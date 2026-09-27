import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs

/-!
# The tangent rows of the lens wiring

`Work.Drive.PushDisc.lensTangentRows`: at each point `γ₂ (sigR x)` of the finger's core arc
(`|x| ≤ 1`) the tangent plane of the finger `Φ₀ ∘ f` is spanned by the `x`-derivative of the
finger's parametrisation `S₂ (·, 0)` and its `v`-frame `V x`, and this plane has dimension `k + 1`.

The proof is a chain of three reductions, each proved once here:

* `lensRangeMfderivEqRangeChartRep`: the range of `mfderiv (Φ₀ ∘ f)` at `y` equals the range of the
  Fréchet derivative of the chart representation `u ↦ Φ₀ (f (c.symm u))` at `c y`.  This is the
  range form of the chain rule `mfderiv g y = D(g ∘ c.symm)(c y) ∘ mfderiv c y` together with the
  surjectivity of the derivative of a smooth chart (`lensSurjMfderivOfIsSmoothChart`; the
  composition `c ∘ c.symm = id` gives a right inverse).
* `lensRangeFderivSplitECompEq`: precomposing with the linear splitting `splitE k` does not change
  the range (the splitting is bijective).
* `lensRangeFderivEqSpanCons`: the range of `fderiv S₂` at `(x,0)` is spanned by the images of the
  basis of `ℝ × ℝ^k` (`lensBasisVec`), which are computed by the two partial derivatives via
  `lensFderivCompInl` / `lensFderivCompInr` and the defining row `hVdef` of the finger's frame.
-/

open scoped Manifold ContDiff
open Set Metric Filter

namespace Work.Drive.PushDisc

noncomputable section

/-! ## Elementary algebra of `ℝ × ℝ^k` -/

/-- The standard basis `eⱼ` of `ℝ^k` sums up to the vector itself. -/
lemma lensSumSmulSingle (k : ℕ) (w : EuclideanSpace ℝ (Fin k)) :
    (∑ j : Fin k, w j • EuclideanSpace.single j (1:ℝ)) = w := by
  have h : WithLp.ofLp (∑ j : Fin k, w j • (EuclideanSpace.single j (1:ℝ))) = WithLp.ofLp w := by
    rw [WithLp.ofLp_sum, WithLp.ofLp]
    ext j
    simp [Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply, Finset.sum_ite_eq]
  exact (WithLp.equiv 2 (Fin k → ℝ)).injective h

/-- The basis `((1,0), (0,e₁), …)` of `ℝ × ℝ^k`, indexed compatibly with `Fin.cons`. -/
def lensBasisVec (k : ℕ) : Fin (k+1) → ℝ × EuclideanSpace ℝ (Fin k) :=
  Fin.cons ((1:ℝ), (0:EuclideanSpace ℝ (Fin k)))
    (fun j : Fin k => ((0:ℝ), EuclideanSpace.single j (1:ℝ)))

@[simp] lemma lensBasisVec_zero (k : ℕ) :
    lensBasisVec k 0 = ((1:ℝ), (0:EuclideanSpace ℝ (Fin k))) := Fin.cons_zero _ _

@[simp] lemma lensBasisVec_succ (k : ℕ) (j : Fin k) :
    lensBasisVec k j.succ = ((0:ℝ), EuclideanSpace.single j (1:ℝ)) := Fin.cons_succ _ _ _

/-- The basis decomposition of a vector of `ℝ × ℝ^k`. -/
lemma lensProdDecomp (k : ℕ) (v : ℝ × EuclideanSpace ℝ (Fin k)) :
    v = v.1 • lensBasisVec k 0 + ∑ j : Fin k, (v.2) j • lensBasisVec k j.succ := by
  have h2 : (∑ j : Fin k, (v.2) j • EuclideanSpace.single j (1:ℝ)) = v.2 :=
    lensSumSmulSingle k v.2
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp only [lensBasisVec_zero, lensBasisVec_succ, Prod.snd_add, Prod.smul_snd, Prod.snd_sum]
    simp
    exact h2.symm

/-- **The range of a linear map out of `ℝ × ℝ^k` is spanned by the images of the basis.** -/
lemma lensRangeEqSpanRangeBasis {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : ℝ × EuclideanSpace ℝ (Fin k) →L[ℝ] G) :
    L.range = Submodule.span ℝ (Set.range (fun i : Fin (k+1) => L (lensBasisVec k i))) := by
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    have hv := lensProdDecomp k v
    rw [hv, map_add, map_smul, map_sum]
    simp only [map_smul]
    have h0 : L (lensBasisVec k 0) ∈
        Submodule.span ℝ (Set.range (fun i : Fin (k+1) => L (lensBasisVec k i))) :=
      Submodule.subset_span ⟨0, rfl⟩
    have hs : ∀ j : Fin k, L (lensBasisVec k j.succ) ∈
        Submodule.span ℝ (Set.range (fun i : Fin (k+1) => L (lensBasisVec k i))) :=
      fun j => Submodule.subset_span ⟨j.succ, rfl⟩
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h0)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hs j))
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩

/-! ## The two partial derivatives -/

/-- The derivative of a two-variable map along the first coordinate. -/
lemma lensFderivCompInl {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {x : ℝ} (hF : DifferentiableAt ℝ F (x, 0)) :
    fderiv ℝ (fun t : ℝ => F (t, 0)) x
      = (fderiv ℝ F (x, 0)).comp (ContinuousLinearMap.inl ℝ ℝ E) := by
  have h1 : HasFDerivAt (fun t : ℝ => (t, (0:E))) (ContinuousLinearMap.inl ℝ ℝ E) x :=
    hasFDerivAt_prodMk_left x (0:E)
  exact (hF.hasFDerivAt.comp x h1).fderiv

/-- The derivative of a two-variable map along the second coordinate. -/
lemma lensFderivCompInr {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {x : ℝ} {w : E} (hF : DifferentiableAt ℝ F (x, w)) :
    fderiv ℝ (fun w' : E => F (x, w')) w
      = (fderiv ℝ F (x, w)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have h1 : HasFDerivAt (fun w' : E => (x, w')) (ContinuousLinearMap.inr ℝ ℝ E) w :=
    hasFDerivAt_prodMk_right x w
  exact (hF.hasFDerivAt.comp w h1).fderiv

/-- **The range of `fderiv S₂ (x,0)` is spanned by the `x`-derivative of the spine `S₂ (·,0)` and
the `v`-frame `V`.** -/
lemma lensRangeFderivEqSpanCons {k : ℕ}
    {S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k}
    (V : Fin k → Work.Drive.Whitney.Mdl k) {x : ℝ}
    (hd : DifferentiableAt ℝ S₂ (x, 0))
    (hV : ∀ (w : EuclideanSpace ℝ (Fin k)),
      (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S₂ (x, w')) 0) w = ∑ j : Fin k, w j • V j) :
    (fderiv ℝ S₂ (x, 0)).range
      = Submodule.span ℝ (Set.range (Fin.cons
          (fderiv ℝ (fun t : ℝ => S₂ (t, (0:EuclideanSpace ℝ (Fin k)))) x 1) V)) := by
  have hβ0 : fderiv ℝ S₂ (x, 0) (lensBasisVec k 0)
      = fderiv ℝ (fun t : ℝ => S₂ (t, (0:EuclideanSpace ℝ (Fin k)))) x 1 := by
    have h2 := lensFderivCompInl (F := S₂) (x := x) hd
    have h3 : fderiv ℝ S₂ (x, 0) (lensBasisVec k 0)
        = (fderiv ℝ (fun t : ℝ => S₂ (t, (0:EuclideanSpace ℝ (Fin k)))) x) 1 := by
      rw [lensBasisVec_zero, h2]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    exact h3
  have hβs : ∀ j : Fin k, fderiv ℝ S₂ (x, 0) (lensBasisVec k j.succ) = V j := by
    intro j
    have h2 := lensFderivCompInr (F := S₂) (x := x) (w := 0) hd
    have h3 : fderiv ℝ S₂ (x, 0) (lensBasisVec k j.succ)
        = (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
            (EuclideanSpace.single j (1:ℝ)) := by
      rw [lensBasisVec_succ, h2]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [h3, hV (EuclideanSpace.single j (1:ℝ))]
    simp [PiLp.single_apply]
  have hfun : (fun i : Fin (k+1) => fderiv ℝ S₂ (x, 0) (lensBasisVec k i))
      = Fin.cons (fderiv ℝ (fun t : ℝ => S₂ (t, (0:EuclideanSpace ℝ (Fin k)))) x 1) V := by
    funext i
    induction i using Fin.cases with
    | zero => exact hβ0
    | succ j => exact hβs j
  rw [lensRangeEqSpanRangeBasis (fderiv ℝ S₂ (x, 0)), hfun]

/-! ## The chart bridge -/

/-- **The manifold derivative of a smooth chart is surjective.** -/
lemma lensSurjMfderivOfIsSmoothChart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : Work.Whitney.IsSmoothChart c) {p : M} (hp : p ∈ c.source) :
    Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c p) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c p :=
    hc.1.contMDiffAt (c.open_source.mem_nhds hp)
  have hsmm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c p) :=
    hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))
  have h1 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c (c.symm (c p)) := by
    rw [c.left_inv hp]; exact hcsm.mdifferentiableAt hne
  have h2 : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c p) :=
    hsmm.mdifferentiableAt hne
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c ∘ c.symm) (c p)
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c (c.symm (c p))).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c p)) :=
    mfderiv_comp (f := c.symm) (x := c p) h1 h2
  rw [c.left_inv hp] at hcomp
  have heq : c ∘ c.symm =ᶠ[nhds (c p)] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hp)] with z hz
    rw [Function.comp_apply, c.right_inv hz]
    rfl
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (ContinuousLinearMap.leftInverse_of_comp hcomp.symm).surjective

/-- **The chart bridge**: the range of `mfderiv g` at `y` is the range of the derivative of the
chart representation `u ↦ g (c.symm u)` at `c y`. -/
lemma lensRangeMfderivEqRangeChartRep {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : M → G} {y : M}
    (hg : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ G) g y)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} (hc : Work.Whitney.IsSmoothChart c)
    (hy : y ∈ c.source) :
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ G) g y).range
      = (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (c.symm u)) (c y)).range := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcsm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y :=
    hc.1.contMDiffAt (c.open_source.mem_nhds hy)
  have hsmm : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y) :=
    hc.2.contMDiffAt (c.open_target.mem_nhds (c.map_source hy))
  have hcy : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c y := hcsm.mdifferentiableAt hne
  have hcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (c y) :=
    hsmm.mdifferentiableAt hne
  have hH : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
      (fun u => g (c.symm u)) (c y) :=
    MDifferentiableAt.comp_of_eq (c y) hg hcs (c.left_inv hy)
  have hcomp := mfderiv_comp (f := c) (x := y) hH hcy
  have heq : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ G) ((fun u : EuclideanSpace ℝ (Fin n) => g (c.symm u)) ∘ c) y
      = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ G) g y := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    simp only [Function.comp_apply]
    rw [c.left_inv hz]
  have hdec : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ G) g y
      = (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => g (c.symm u)) (c y)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c y) := by
    rw [← heq, hcomp, mfderiv_eq_fderiv]
    rfl
  have hsurj := lensSurjMfderivOfIsSmoothChart hc hy
  rw [hdec]
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact ⟨mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c y v, rfl⟩
  · rintro x ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hsurj w
    exact ⟨v, rfl⟩

/-! ## The splitting `splitE k` does not change the range -/

/-- The Fréchet derivative of a function precomposed with the linear splitting `splitE k`. -/
lemma lensFderivSplitEComp {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : EuclideanSpace ℝ (Fin (k+1)) → G} {q : ℝ × EuclideanSpace ℝ (Fin k)}
    (hH : DifferentiableAt ℝ H ((splitE k) q)) :
    fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin k) => H (splitE k q')) q
      = (fderiv ℝ H ((splitE k) q)).comp (splitE k).toContinuousLinearMap := by
  have h1 : HasFDerivAt (fun q' : ℝ × EuclideanSpace ℝ (Fin k) => (splitE k) q')
      (splitE k).toContinuousLinearMap q := (splitE k).toContinuousLinearMap.hasFDerivAt
  exact (hH.hasFDerivAt.comp q h1).fderiv

/-- **Precomposing with `splitE k` does not change the range.** -/
lemma lensRangeFderivSplitECompEq {k : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : EuclideanSpace ℝ (Fin (k+1)) → G} {q : ℝ × EuclideanSpace ℝ (Fin k)}
    (hH : DifferentiableAt ℝ H ((splitE k) q)) :
    (fderiv ℝ (fun q' : ℝ × EuclideanSpace ℝ (Fin k) => H (splitE k q')) q).range
      = (fderiv ℝ H ((splitE k) q)).range := by
  rw [lensFderivSplitEComp hH]
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    exact LinearMap.mem_range.mpr ⟨(splitE k) v, rfl⟩
  · rintro y ⟨w, rfl⟩
    refine LinearMap.mem_range.mpr ⟨(splitE k).symm w, ?_⟩
    show fderiv ℝ H ((splitE k) q) ((splitE k) ((splitE k).symm w))
        = fderiv ℝ H ((splitE k) q) w
    rw [LinearEquiv.apply_symm_apply]

/-! ## The tangent rows -/

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem lensTangentRows {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F) :
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
        (C.γ₂ (Work.Drive.Whitney.sigR x))).range
        = Submodule.span ℝ (Set.range (Fin.cons
            (fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1) (G.V x))))
    ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      Module.finrank ℝ ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
        (C.γ₂ (Work.Drive.Whitney.sigR x))).range) = k + 1)
    ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1 ∈
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
          (C.γ₂ (Work.Drive.Whitney.sigR x))).range) := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have main : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
        (C.γ₂ (Work.Drive.Whitney.sigR x))).range
        = Submodule.span ℝ (Set.range (Fin.cons
            (fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1) (G.V x))))
      ∧ Module.finrank ℝ ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
        (C.γ₂ (Work.Drive.Whitney.sigR x))).range) = k + 1
      ∧ fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1 ∈
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
          (C.γ₂ (Work.Drive.Whitney.sigR x))).range := by
    intro x hx
    -- elementary facts about `x` and the base point of the finger's arc
    have hxabs : |x| ≤ F.X' := by
      have h1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
      linarith [F.hX']
    have hsig : Work.Drive.Whitney.sigR x ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.mem_Icc]
      constructor
      · simp only [Work.Drive.Whitney.sigR]; linarith [hx.1]
      · simp only [Work.Drive.Whitney.sigR]; linarith [hx.2]
    have hmem : C.γ₂ (Work.Drive.Whitney.sigR x) ∈ F.c.source :=
      F.hcarc ⟨Work.Drive.Whitney.sigR x, hsig, rfl⟩
    have hchart : F.c (C.γ₂ (Work.Drive.Whitney.sigR x))
        = splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) := by
      have h := F.harc₂ (Work.Drive.Whitney.sigR x) hsig
      have h2 : (2:ℝ) * Work.Drive.Whitney.sigR x - 1 = x := by
        simp only [Work.Drive.Whitney.sigR]; ring
      rw [h2] at h
      exact h
    -- the finger map is smooth
    have hg_md : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k))
        (fun y : M => T.Φ₀ (C.f y)) (C.γ₂ (Work.Drive.Whitney.sigR x)) :=
      (T.hΦ₀sm.contMDiff.comp C.hf).mdifferentiableAt hne
    -- step 1: the chart bridge
    have hb := lensRangeMfderivEqRangeChartRep (g := fun y : M => T.Φ₀ (C.f y)) hg_md
      F.hcsmooth hmem
    rw [hchart] at hb
    -- step 2: differentiability of the chart representation at `splitE k (x,0)`
    have hHmd : MDifferentiableAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (k + 1))))
        (𝓘(ℝ, Work.Drive.Whitney.Mdl k))
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => T.Φ₀ (C.f (F.c.symm u)))
        (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) := by
      have hcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) F.c.symm
          (F.c (C.γ₂ (Work.Drive.Whitney.sigR x))) :=
        (F.hcsmooth.2.contMDiffAt
          (F.c.open_target.mem_nhds (F.c.map_source hmem))).mdifferentiableAt hne
      have hcomp := MDifferentiableAt.comp_of_eq (F.c (C.γ₂ (Work.Drive.Whitney.sigR x)))
        hg_md hcs (F.c.left_inv hmem)
      rwa [hchart] at hcomp
    have hH : DifferentiableAt ℝ
        (fun u : EuclideanSpace ℝ (Fin (k + 1)) => T.Φ₀ (C.f (F.c.symm u)))
        (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) :=
      mdifferentiableAt_iff_differentiableAt.mp hHmd
    -- step 3: the splitting does not change the range
    have hs := lensRangeFderivSplitECompEq (k := k)
      (H := fun u : EuclideanSpace ℝ (Fin (k + 1)) => T.Φ₀ (C.f (F.c.symm u)))
      (q := (x, (0 : EuclideanSpace ℝ (Fin k)))) hH
    -- step 4: the finger's parametrisation agrees with the chart representation at `(x,0)`
    have hd2 := G.hS₂d (x, (0 : EuclideanSpace ℝ (Fin k))) hxabs (by simpa using F.hr.le)
    -- step 5: the range of `fderiv S₂ (x,0)` in terms of the frame
    have hcore := lensRangeFderivEqSpanCons (S₂ := G.S₂) (V := G.V x) (x := x)
      ((G.hS₂sm.differentiable hne) (x, (0 : EuclideanSpace ℝ (Fin k))))
      (fun w => G.hVdef x w hxabs)
    have hmain : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
        (C.γ₂ (Work.Drive.Whitney.sigR x))).range
        = Submodule.span ℝ (Set.range (Fin.cons
            (fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1)
            (G.V x))) := by
      rw [hb, ← hs, ← hd2]
      exact hcore
    refine ⟨hmain, ?_, ?_⟩
    · -- the dimension row
      have hinj : Function.Injective (fderiv ℝ G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k)))) :=
        G.hS₂imm (x, (0 : EuclideanSpace ℝ (Fin k))) ⟨hxabs, by simpa using F.hr.le⟩
      have h1 : Module.finrank ℝ (fderiv ℝ G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k)))).range
          = Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin k)) :=
        LinearMap.finrank_range_of_inj (by simpa using hinj)
      have h2 : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin k)) = k + 1 := by
        rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace]
        simp
        omega
      have hr : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => T.Φ₀ (C.f y))
          (C.γ₂ (Work.Drive.Whitney.sigR x))).range
          = (fderiv ℝ G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k)))).range := by
        rw [hmain, ← hcore]
      rw [hr]
      exact h1.trans h2
    · -- the membership row
      rw [hmain]
      refine Submodule.subset_span ?_
      exact ⟨0, by simp⟩
  exact ⟨fun x hx => (main x hx).1, fun x hx => (main x hx).2.1, fun x hx => (main x hx).2.2⟩

end

end Work.Drive.PushDisc
