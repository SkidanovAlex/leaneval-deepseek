import Mathlib
import Submission.Work.Drive.sepFamDefs

/-!
# Smoothness of the bumped charted difference system of a smooth family

`Work.Drive.SepBumpedSmooth Lf N p γ β` is the statement that the *bumped* charted difference system

`q ↦ (γ q.1 * β q.2) • FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2`

of a family `(Lf, N)` of (loop, chain) pairs is `C^∞` on the whole parameter space
`ℝ^m × ℝ^5`.  This is the standing hypothesis of the parametric-Sard bricks of the separated
germ/parity route (the bump `γ ⊗ β` localizes the system to a product `U ×ˢ V` on which both
values of the family lie in the source of the chart at `p` — a `Work.Drive.SepChartReg`).

The proof is a pointwise case distinction, exactly as in the `(2,3)`-analogue
`Work.Drive.famMeet_contDiff_cutoff`:

* if `β` vanishes near `q₀.2` then the system is *eventually equal to `0`* near `q₀` (a point outside
  the topological support of a function has a neighbourhood on which the function vanishes);
* likewise if `γ` vanishes near `q₀.1`;
* otherwise `(q₀.1, q₀.2) ∈ tsupport γ ×ˢ tsupport β ⊆ U ×ˢ V`, so both values of the family lie in
  the source of the chart at `p`: the charted difference is the sum
  `chr p (famLoop …) - chr p (famChain …)` of two composites of (a) the *jointly* smooth sides of the
  family — `Work.Drive.sep_contMDiff_famLoop_fam`, `Work.Drive.sep_contMDiff_famChain_fam`, both
  obtained from the two halves of `Work.Drive.SepFamSmooth` by composing with the continuous linear
  index selections `FamBox.loopArgCLM` / `FamBox.chainArgCLM` — with (b) the chart `chr p`, which is
  `C^∞` *at every point of its source* (`Work.Drive.sep_contMDiffOn_chr`, from
  `contMDiffOn_extChartAt`), and it remains to multiply by the smooth scalar `γ ⊗ β`.

The only two "library" inputs are thus the pointwise chain rule
(`Work.Drive.sep_contDiffAt_chart_fam`) and the vanishing-outside-the-support lemma.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 2000000

noncomputable section

variable {m : ℕ}

/-! ## The two index selections of the five-box, as continuous linear maps of the *family* -/

/-- The loop index selection `(τ, p) ↦ (τ, mk2 (p 0) (p 1))` of the family parameter
`τ ∈ ℝ^m` and the five-box point `p ∈ ℝ^5`. -/
private def sepLoopArgCLM (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × Amb 4) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ _ _)
    (FamBox.loopArgCLM.comp (ContinuousLinearMap.snd ℝ _ _))

/-- The chain index selection `(τ, p) ↦ (τ, famPt (p 0) (famT3 (p 2) (p 3) (p 4)))`. -/
private def sepChainArgCLM (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × Amb 4) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ _ _)
    (FamBox.chainArgCLM.comp (ContinuousLinearMap.snd ℝ _ _))

private lemma sepLoopArgCLM_apply (m : ℕ) (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    sepLoopArgCLM m q = (q.1, mk2 (q.2 0) (q.2 1)) := by
  simp [sepLoopArgCLM, FamBox.loopArgCLM_apply]

private lemma sepChainArgCLM_apply (m : ℕ) (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    sepChainArgCLM m q = (q.1, famPt (q.2 0) (famT3 (q.2 2) (q.2 3) (q.2 4))) := by
  simp [sepChainArgCLM, FamBox.chainArgCLM_apply]

/-! ## Two elementary inputs -/

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma sep_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X]
    [Zero Y] {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- The chart `chr p` is `C^∞` on its source. -/
private lemma sep_contMDiffOn_chr (p : CappingSpace) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- **The pointwise chain rule**: a jointly smooth charted map, composed with the chart at a point
whose value lies in the source of that chart, is smooth at the point. -/
private lemma sep_contDiffAt_chart_fam
    (f : EuclideanSpace ℝ (Fin m) × Amb 4 → CappingSpace)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop f)
    (p : CappingSpace) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4)
    (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (sep_contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-! ## Joint smoothness of the two sides of the family -/

/-- **The loop side of the family is jointly `C^∞`** in the shift and the five-box variable: the
loop family `q ↦ Lf q.1 (mk2 (q.2 0) (q.2 1))` is the composite of the jointly smooth
`(τ, p) ↦ Lf τ p` (the first half of `Work.Drive.SepFamSmooth`) with the linear index selection
`sepLoopArgCLM`. -/
lemma sep_contMDiff_famLoop_fam
    {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2) := by
  have h' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2) := by
    rw [← modelWithCornersSelf_prod] at h
    rw [chartedSpaceSelf_prod] at h
    exact h
  have hfun : (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2)
      = (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2)
        ∘ ⇑(sepLoopArgCLM m) := by
    funext q
    simp only [Function.comp_apply, sepLoopArgCLM_apply, famLoop]
  rw [hfun]
  exact h'.comp (sepLoopArgCLM m).contMDiff

/-- **The chain side of the family is jointly `C^∞`** in the shift and the five-box variable. -/
lemma sep_contMDiff_famChain_fam
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    (h : ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2) := by
  have h' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2) := by
    rw [← modelWithCornersSelf_prod] at h
    rw [chartedSpaceSelf_prod] at h
    exact h
  have hfun : (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2)
      = (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2)
        ∘ ⇑(sepChainArgCLM m) := by
    funext q
    simp only [Function.comp_apply, sepChainArgCLM_apply, famChain]
  rw [hfun]
  exact h'.comp (sepChainArgCLM m).contMDiff

/-- **Joint smoothness of the charted difference map of the family** at a point at which both
values of the family lie in the source of the chart at `p`. -/
lemma sep_chartDif_joint_contDiffAt
    {Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → CappingSpace}
    (hL : ContMDiff ((𝓡 m).prod (𝓡 2)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => Lf q.1 q.2))
    (hN : ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => N q.1 q.2))
    (p : CappingSpace) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4)
    (hreg : famLoop (Lf q₀.1) q₀.2 ∈ (chr p).source ∧
      famChain (N q₀.1) q₀.2 ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif p (famLoop (Lf q.1)) (famChain (N q.1)) q.2) q₀ := by
  have h1 := sep_contDiffAt_chart_fam
    (f := fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famLoop (Lf q.1) q.2)
    (sep_contMDiff_famLoop_fam hL) p q₀ hreg.1
  have h2 := sep_contDiffAt_chart_fam
    (f := fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => famChain (N q.1) q.2)
    (sep_contMDiff_famChain_fam hN) p q₀ hreg.2
  show ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
    chr p (famLoop (Lf q.1) q.2) - chr p (famChain (N q.1) q.2)) q₀
  exact h1.sub h2

/-! ## The bumped charted difference system is `C^∞` -/

/-- **The bumped charted difference system of a smooth family is `C^∞`.**  The two cut-offs `γ`, `β`
are supported in `U` resp. `V`, and on `U ×ˢ V` both values of the family lie in the source of the
chart at `p`; consequently the system is smooth wherever the bump is non-zero, and it vanishes
identically in a neighbourhood of every point where one of the two cut-offs vanishes. -/
theorem sepCutoffSystemSmooth {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace)
    (hfam : Work.Drive.SepFamSmooth Lf N)
    (p : Work.Drive.CappingSpace) {γ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ) {β : EuclideanSpace ℝ (Fin 5) → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (EuclideanSpace ℝ (Fin 5))}
    (hUV : Work.Drive.SepChartReg Lf N p U V)
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    Work.Drive.SepBumpedSmooth Lf N p γ β := by
  rw [SepBumpedSmooth, contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · -- both cut-offs are non-zero at `q₀`: the chart region hypothesis applies
      have hreg := hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ := sep_chartDif_joint_contDiffAt hfam.1 hfam.2 p q₀ hreg
      have hg : ContDiffAt ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · -- `β` vanishes near `q₀.2`: the system is eventually `0`
      refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (sep_eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · -- `γ` vanishes near `q₀.1`: the system is eventually `0`
    refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (sep_eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]


/-- **The bumped system with an arbitrary smooth reparametrisation of the parameter** — the
`sq`-version `Work.Drive.SepCutoffSystemSmooth` of the main theorem, obtained by composing with the
smooth map `q ↦ (sq q.1, q.2)`.  (Convenience corollary; the main theorem is the `sq = id` case.) -/
theorem sepCutoffSystemSmooth_of_sq {m : ℕ}
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace)
    (hfam : Work.Drive.SepFamSmooth Lf N)
    (p : Work.Drive.CappingSpace) {γ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ) {β : EuclideanSpace ℝ (Fin 5) → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (EuclideanSpace ℝ (Fin 5))}
    (hUV : Work.Drive.SepChartReg Lf N p U V)
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V)
    (sq : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hsq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sq) :
    Work.Drive.SepCutoffSystemSmooth Lf N p γ β sq := by
  rw [SepCutoffSystemSmooth]
  have hbase := sepCutoffSystemSmooth Lf N hfam p hγ hβ hUV hγsupp hβsupp
  rw [SepBumpedSmooth] at hbase
  have hsq2 : ContDiff ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => (sq q.1, q.2)) :=
    (hsq.comp contDiff_fst).prodMk contDiff_snd
  exact hbase.comp hsq2

end

end Work.Drive
