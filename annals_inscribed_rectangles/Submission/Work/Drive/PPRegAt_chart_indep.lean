import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.TParity.Basic

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Chart-independence of the pair regularity `PPRegAt` at a meet

`Work.Drive.PPRegAt E E' V W x` is stated with the **self-centred** chart pair
`(chr (E (ftS x) (ftU x)), chr (E' (ftS x) (ftU x)))`: the surjectivity of the `x`-derivative of
the charted pair map `Work.Drive.ppDiff`, and the surjectivity of its restriction to a coordinate
hyperplane through the point.  The purpose of this file is to show that both conditions are
**independent of the chart pair** used, as long as the two chart pairs `(p, p')` and `(p₀, p₀')`
both contain the four values at `x` — i.e. as long as `x` lies in both chart-residency regions
`Work.Drive.ppRegion p p' E E' V W` and `Work.Drive.ppRegion p₀ p₀' E E' V W`.

The mechanism is the one used for the triple intersection (`TParity/ChartDeriv.lean`): at a meet the
two values of each block **coincide**, so the charted difference map is obtained from a *chart-free*
map by composing, block by block, with the change of coordinates `tangentCoordChange`, which is a
bijection of `ℝ⁴` on the chart region.  Concretely

> `fderiv ℝ (ppDiff p p' E E' V W) x = pUpCLM ∘ (ppA p p' x ∘ ppFree x)`

where

* `ppFree x` is the **chart-free** pair `(dE − dV, dE' − dW)` of the manifold derivatives of the four
  chains at `x` (a map `ℝ⁹ → ℝ⁴ × ℝ⁴`);
* `ppA p p' x = φ_E ⊕ φ_{E'}` is the block-diagonal change of coordinates, a bijection.

Since `pUpCLM` is a bijection as well, the surjectivity of the derivative is equivalent to the
surjectivity of the chart-free `ppFree x` — and *that* does not mention the charts at all.  The same
argument applies verbatim to the restriction of the derivative to a coordinate hyperplane, whose
surjectivity is likewise equivalent to the surjectivity of the restriction of `ppFree x`.

This is what turns the per-piece charted conclusions of the localized Sard argument into the
self-centred `PPRegAt`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PPIndep

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-! ## The chart-free data of the pair map -/

/-- The manifold derivative of the first `2`-chain `z ↦ E (ftS z) (ftU z)` at a point. -/
def ppDE (E : ℝ → Tgt 2 → M) (x : Tgt 9) : Tgt 9 →L[ℝ] Tgt 4 :=
  show Tgt 9 →L[ℝ] Tgt 4 from mfderiv (𝓡 9) (𝓡 4) (fun z : Tgt 9 => E (ftS z) (ftU z)) x

/-- The manifold derivative of the second `2`-chain `z ↦ E' (ftS z) (ftU z)` at a point. -/
def ppDE' (E' : ℝ → Tgt 2 → M) (x : Tgt 9) : Tgt 9 →L[ℝ] Tgt 4 :=
  show Tgt 9 →L[ℝ] Tgt 4 from mfderiv (𝓡 9) (𝓡 4) (fun z : Tgt 9 => E' (ftS z) (ftU z)) x

/-- The manifold derivative of the first `3`-chain `z ↦ V (ftY z)` at a point. -/
def ppDV (V : Tgt 3 → M) (x : Tgt 9) : Tgt 9 →L[ℝ] Tgt 4 :=
  show Tgt 9 →L[ℝ] Tgt 4 from mfderiv (𝓡 9) (𝓡 4) (fun z : Tgt 9 => V (ftY z)) x

/-- The manifold derivative of the second `3`-chain `z ↦ W (ftZ z)` at a point. -/
def ppDW (W : Tgt 3 → M) (x : Tgt 9) : Tgt 9 →L[ℝ] Tgt 4 :=
  show Tgt 9 →L[ℝ] Tgt 4 from mfderiv (𝓡 9) (𝓡 4) (fun z : Tgt 9 => W (ftZ z)) x

/-- **The chart-free pair of block derivatives** at `x`: `(dE − dV, dE' − dW)`. -/
def ppFree (E E' : ℝ → Tgt 2 → M) (V W : Tgt 3 → M) (x : Tgt 9) :
    Tgt 9 →L[ℝ] (Tgt 4 × Tgt 4) :=
  (ppDE E x - ppDV V x).prod (ppDE' E' x - ppDW W x)

/-- The change of coordinates of the tangent space at `a`, from the chart at `a` to the chart at
`p`.  This is the factor by which the charted block of the pair map at a meet is twisted. -/
def ppTc (a p : M) : Tgt 4 →L[ℝ] Tgt 4 :=
  tangentCoordChange (𝓡 4) a p a

/-- The inverse change of coordinates at the point `a`: from the chart at `p` back to the chart at
`a`.  (Note that `ppTcInv a p` is *not* `ppTc p a`: the point whose tangent space is being changed
is `a` in both.) -/
def ppTcInv (a p : M) : Tgt 4 →L[ℝ] Tgt 4 :=
  tangentCoordChange (𝓡 4) p a a

/-- **The block-diagonal chart transition of the pair map**: the change of coordinates of the first
block composed with that of the second block, at the two values of the meet `x`. -/
def ppA (p p' : M) (E E' : ℝ → Tgt 2 → M) (x : Tgt 9) :
    (Tgt 4 × Tgt 4) →L[ℝ] (Tgt 4 × Tgt 4) :=
  (ppTc (E (ftS x) (ftU x)) p).prodMap (ppTc (E' (ftS x) (ftU x)) p')

/-! ## The change of coordinates is a bijection -/

/-- The point `a` lies in the source of the chart at `p` (in the form used by the change of
coordinates). -/
lemma mem_chr_source {a p : M} (ha : a ∈ (chr p).source) : a ∈ (extChartAt (𝓡 4) p).source := by
  rw [extChartAt_source]; exact ha

lemma ppTc_leftInverse {a p : M} (ha : a ∈ (chr p).source) :
    ∀ v : Tgt 4, ppTcInv a p (ppTc a p v) = v := by
  intro v
  exact tangentCoordChange_comp_inv ⟨mem_extChartAt_source a, mem_chr_source ha⟩ v

lemma ppTc_rightInverse {a p : M} (ha : a ∈ (chr p).source) :
    ∀ v : Tgt 4, ppTc a p (ppTcInv a p v) = v := by
  intro v
  exact tangentCoordChange_comp_inv ⟨mem_chr_source ha, mem_extChartAt_source a⟩ v

/-- **The change of coordinates is bijective** as soon as the point lies in the chart's source. -/
lemma ppTc_bijective {a p : M} (ha : a ∈ (chr p).source) : Function.Bijective (ppTc a p) :=
  ⟨fun u v huv => by
      have h := congrArg (ppTcInv a p) huv
      rw [ppTc_leftInverse ha, ppTc_leftInverse ha] at h
      exact h,
    fun w => ⟨ppTcInv a p w, ppTc_rightInverse ha w⟩⟩

/-- The block-diagonal transition is bijective, by bijectivity of each block. -/
lemma bijective_prodMap {f g : Tgt 4 →L[ℝ] Tgt 4} (hf : Function.Bijective f)
    (hg : Function.Bijective g) : Function.Bijective (f.prodMap g) := by
  constructor
  · intro x y h
    have h1 : f x.1 = f y.1 := by simpa using congrArg Prod.fst h
    have h2 : g x.2 = g y.2 := by simpa using congrArg Prod.snd h
    exact Prod.ext (hf.1 h1) (hg.1 h2)
  · intro y
    obtain ⟨x1, hx1⟩ := hf.2 y.1
    obtain ⟨x2, hx2⟩ := hg.2 y.2
    exact ⟨(x1, x2), Prod.ext hx1 hx2⟩

/-- **The block-diagonal chart transition of the pair map is bijective** on the pair region. -/
lemma ppA_bijective (E E' : ℝ → Tgt 2 → M) (V W : Tgt 3 → M) {x : Tgt 9} {p p' : M}
    (hres : x ∈ ppRegion p p' E E' V W) : Function.Bijective (ppA p p' E E' x) :=
  bijective_prodMap (ppTc_bijective hres.1) (ppTc_bijective hres.2.2.1)

/-- The stacking map `ℝ⁴ × ℝ⁴ → ℝ⁸` is bijective. -/
lemma pUpCLM_bijective : Function.Bijective TParity.pUpCLM := by
  refine ⟨fun x y h => ?_, TParity.pUpCLM_surjective⟩
  have hz : TParity.pUpCLM (x - y) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp ((TParity.pUpCLM_eq_zero_iff (x - y)).mp hz)

/-- Surjectivity is invariant under composing on the left with a bijection. -/
lemma surjective_comp_iff_of_bijective {α β γ : Type*} {T : β → γ} (hT : Function.Bijective T)
    (g : α → β) : Function.Surjective (fun a => T (g a)) ↔ Function.Surjective g := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (T y)
    exact ⟨x, hT.1 hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := hT.2 y
    obtain ⟨z, hz⟩ := h x
    exact ⟨z, by show T (g z) = y; rw [hz, hx]⟩

/-! ## The derivative of the charted pair map -/

/-- **The derivative of the charted pair map at a meet is the chart-free derivative, composed with
the block-diagonal chart transition.** -/
theorem hasFDerivAt_ppDiff (E E' : ℝ → Tgt 2 → M) (V W : Tgt 3 → M)
    (hE : ContMDiff (𝓡 9) (𝓡 4) Ctop (fun z : Tgt 9 => E (ftS z) (ftU z)))
    (hE' : ContMDiff (𝓡 9) (𝓡 4) Ctop (fun z : Tgt 9 => E' (ftS z) (ftU z)))
    (hV : ContMDiff (𝓡 9) (𝓡 4) Ctop (fun z : Tgt 9 => V (ftY z)))
    (hW : ContMDiff (𝓡 9) (𝓡 4) Ctop (fun z : Tgt 9 => W (ftZ z)))
    {x : Tgt 9} (hmeet : x ∈ ppMeet E E' V W) {p p' : M}
    (hres : x ∈ ppRegion p p' E E' V W) :
    HasFDerivAt (ppDiff p p' E E' V W)
      (TParity.pUpCLM.comp ((ppA p p' E E' x).comp (ppFree E E' V W x))) x := by
  have hVx : V (ftY x) = E (ftS x) (ftU x) := hmeet.2.1.symm
  have hWx : W (ftZ x) = E' (ftS x) (ftU x) := hmeet.2.2.symm
  -- the two blocks, before the meet identifications
  have h1 : HasFDerivAt (fun y : Tgt 9 => chr p (E (ftS y) (ftU y)))
      ((ppTc (E (ftS x) (ftU x)) p).comp (ppDE E x)) x :=
    fderiv_chart_comp_hasFDerivAt (fun z : Tgt 9 => E (ftS z) (ftU z)) hE p hres.1
  have h2 : HasFDerivAt (fun y : Tgt 9 => chr p (V (ftY y)))
      ((ppTc (V (ftY x)) p).comp (ppDV V x)) x :=
    fderiv_chart_comp_hasFDerivAt (fun z : Tgt 9 => V (ftY z)) hV p hres.2.1
  have h1' : HasFDerivAt (fun y : Tgt 9 => chr p' (E' (ftS y) (ftU y)))
      ((ppTc (E' (ftS x) (ftU x)) p').comp (ppDE' E' x)) x :=
    fderiv_chart_comp_hasFDerivAt (fun z : Tgt 9 => E' (ftS z) (ftU z)) hE' p' hres.2.2.1
  have h2' : HasFDerivAt (fun y : Tgt 9 => chr p' (W (ftZ y)))
      ((ppTc (W (ftZ x)) p').comp (ppDW W x)) x :=
    fderiv_chart_comp_hasFDerivAt (fun z : Tgt 9 => W (ftZ z)) hW p' hres.2.2.2
  -- the block derivatives after the meet identifications
  have hblk1 : HasFDerivAt
      (fun y : Tgt 9 => chr p (E (ftS y) (ftU y)) - chr p (V (ftY y)))
      ((ppTc (E (ftS x) (ftU x)) p).comp (ppDE E x - ppDV V x)) x := by
    have hL : ((ppTc (E (ftS x) (ftU x)) p).comp (ppDE E x))
        - ((ppTc (V (ftY x)) p).comp (ppDV V x))
        = (ppTc (E (ftS x) (ftU x)) p).comp (ppDE E x - ppDV V x) := by
      rw [hVx, ← ContinuousLinearMap.comp_sub]
    exact hL ▸ (h1.sub h2)
  have hblk2 : HasFDerivAt
      (fun y : Tgt 9 => chr p' (E' (ftS y) (ftU y)) - chr p' (W (ftZ y)))
      ((ppTc (E' (ftS x) (ftU x)) p').comp (ppDE' E' x - ppDW W x)) x := by
    have hL : ((ppTc (E' (ftS x) (ftU x)) p').comp (ppDE' E' x))
        - ((ppTc (W (ftZ x)) p').comp (ppDW W x))
        = (ppTc (E' (ftS x) (ftU x)) p').comp (ppDE' E' x - ppDW W x) := by
      rw [hWx, ← ContinuousLinearMap.comp_sub]
    exact hL ▸ (h1'.sub h2')
  -- the pair identity and the pass to the stacked `ℝ⁸`-valued map
  have hpair := TParity.hasFDerivAt_pUp hblk1 hblk2
  have hL : ((ppTc (E (ftS x) (ftU x)) p).comp (ppDE E x - ppDV V x)).prod
      ((ppTc (E' (ftS x) (ftU x)) p').comp (ppDE' E' x - ppDW W x))
      = (ppA p p' E E' x).comp (ppFree E E' V W x) := by
    exact rfl
  rw [hL] at hpair
  have hfun : (fun y : Tgt 9 => TParity.pUp
      ((chr p (E (ftS y) (ftU y))) - (chr p (V (ftY y))))
      ((chr p' (E' (ftS y) (ftU y))) - (chr p' (W (ftZ y)))))
      = ppDiff p p' E E' V W := rfl
  rwa [hfun] at hpair

end PPIndep

/-! ## The target -/

/-- **Chart-independence of the pair regularity at a meet.** -/
theorem PPRegAt_chart_indep
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => E' (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY z)))
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ z)))
    {x : EuclideanSpace ℝ (Fin 9)} (hmeet : x ∈ Work.Drive.ppMeet E E' V W)
    {p p' p₀ p₀' : M} (hres : x ∈ Work.Drive.ppRegion p p' E E' V W)
    (hres₀ : x ∈ Work.Drive.ppRegion p₀ p₀' E E' V W) :
    (Function.Surjective (fderiv ℝ (Work.Drive.ppDiff p p' E E' V W) x) ↔
      Function.Surjective (fderiv ℝ (Work.Drive.ppDiff p₀ p₀' E E' V W) x)) ∧
    (∀ (i : Fin 9) (hi : x i = 0 ∨ x i = 1),
      (Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (Work.Drive.ppDiff p p' E E' V W) x v.1) ↔
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (Work.Drive.ppDiff p₀ p₀' E E' V W) x v.1))) := by
  -- the derivative, in the chart-free form of `PPIndep`
  have hder : ∀ (q q' : M), x ∈ ppRegion q q' E E' V W →
      fderiv ℝ (ppDiff q q' E E' V W) x
        = TParity.pUpCLM.comp ((PPIndep.ppA q q' E E' x).comp (PPIndep.ppFree E E' V W x)) :=
    fun q q' hq => (PPIndep.hasFDerivAt_ppDiff E E' V W hE hE' hV hW hmeet hq).fderiv
  -- the unrestricted clause
  have key : ∀ (q q' : M), (x ∈ ppRegion q q' E E' V W) →
      ((Function.Surjective (fderiv ℝ (ppDiff q q' E E' V W) x)) ↔
      (Function.Surjective (fun v : EuclideanSpace ℝ (Fin 9) =>
        (PPIndep.ppA q q' E E' x) (PPIndep.ppFree E E' V W x v)))) := by
    intro q q' hq
    rw [hder q q' hq]
    exact PPIndep.surjective_comp_iff_of_bijective PPIndep.pUpCLM_bijective _
  -- the hyperplane clause (the face index and the face value are not used)
  have key2 : ∀ (q q' : M), (x ∈ ppRegion q q' E E' V W) → ∀ i : Fin 9,
      ((Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (ppDiff q q' E E' V W) x v.1)) ↔
      (Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          (PPIndep.ppA q q' E E' x) (PPIndep.ppFree E E' V W x v.1)))) := by
    intro q q' hq i
    have hfun : (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
        fderiv ℝ (ppDiff q q' E E' V W) x v.1)
        = fun v => TParity.pUpCLM
            ((PPIndep.ppA q q' E E' x) (PPIndep.ppFree E E' V W x v.1)) := by
      funext v
      rw [hder q q' hq]
      simp only [ContinuousLinearMap.comp_apply]
    rw [hfun]
    exact PPIndep.surjective_comp_iff_of_bijective PPIndep.pUpCLM_bijective _
  refine ⟨?_, fun i _ => ?_⟩
  · rw [key p p' hres, key p₀ p₀' hres₀]
    exact (PPIndep.surjective_comp_iff_of_bijective
        (PPIndep.ppA_bijective E E' V W hres) (PPIndep.ppFree E E' V W x)).trans
      ((PPIndep.surjective_comp_iff_of_bijective
        (PPIndep.ppA_bijective E E' V W hres₀) (PPIndep.ppFree E E' V W x)).symm)
  · rw [key2 p p' hres i, key2 p₀ p₀' hres₀ i]
    exact (PPIndep.surjective_comp_iff_of_bijective
        (PPIndep.ppA_bijective E E' V W hres)
        (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          PPIndep.ppFree E E' V W x v.1)).trans
      ((PPIndep.surjective_comp_iff_of_bijective
        (PPIndep.ppA_bijective E E' V W hres₀)
        (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          PPIndep.ppFree E E' V W x v.1)).symm)

end

end Work.Drive
