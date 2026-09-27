import Mathlib
import Submission.Work.Drive.sideGermSepDefs
import Submission.Work.Drive.sep_fam_smooth
import Submission.Work.Drive.famMeet_regular_of_good_family
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.sgSweepDefs
import Submission.Work.Drive.loopFam_faceHyp_of_good_family

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Joint smoothness and analytic helpers for the separated germ family

The parity-locality assembly `Work.Drive.sideGerm_parity_eq_of_close_of_separation_of_data`
(`Submission/Work/Drive/sideGerm_parity_eq_of_close_of_separation.lean`) consumes the Sard obligation
`Work.Drive.sep_fam_regular`: for every pair of configurations `A`, `B`, every pair of angle lifts
`tR`, `t'R` and every `ε' > 0` there are shifts `τ₁`, `τ₂` of norm `< ε'` such that the family of the
straight path from `A` to `B` (with the two independent chart shifts) satisfies the regularity clauses
`SepTrans` and `SepFace` of the parity engine.

This file proves it, by the multi-chart parametric Sard `Work.Drive.goodFaceMulti`:

* the family is the straight path in the two chart parameters and the linear path of angle lifts;
* the relevant values (the core loops along the path and the sweep of the plane presentation) are
  compact, and covered by finitely many charts `pch i` with compact sets `C0 i ⊆ interior (C1 i) ⊆
  (chartAt (pch i)).source`;
* for each chart, the *charted difference system* of the two sides of the five-box family, cut off in
  the parameter (γ) and in the box (β), has an **onto parameter-derivative at every zero**
  (`ChartPert`'s surjectivity at every point), which is the hypothesis of `goodFaceMulti`;
* `goodFaceMulti` returns a parameter `τ` for which the `z`-derivative of every system is onto at its
  zeros in `K i` (giving `SepTrans` through the linear-algebra bridge
  `Work.Drive.FamBox.fderiv_chartDif_eq_Lf`), the *face* clause holds (giving the crossing vector `σ`
  of `SepFace`), and no zero lies over the two-face skeletons of the five-box (giving the
  "exactly one face" clause of `SepFace`).

Only the shift of the *loop's* chart is needed: the parameter space is `𝔼^m` (the shift `τ₁`), and
`τ₂ = 0`.  The parameter-derivative of the charted difference is then `∂_{τ₁}` of the loop's charted
value, which is onto by `ChartPert` — the second shift is not needed for the *Sard* (it was needed in
the removed `hdisj`-variant only because there the system was not cut off chart-wise).

Everything here is `sorry`-free and rests on the standard axioms.
-/

namespace Work.Drive

open Manifold Filter Set Pointwise
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {m : ℕ}

/-! ## 1. A uniform smallness lemma for a shifted parameter -/

/-- **The values of a compact parameter set stay in an open set under a small shift.**  If `Ξ` is a
continuous family of self-maps and the compact set `Z` of `(parameter, point)` pairs is mapped by `Ξ`
into the open set `W`, then a small shift `τ` of the parameter keeps the values in `W`.  (The tube
lemma applied to the compact set `Z` and the point `τ = 0`.) -/
theorem sep_shift_mem_nhds {X : Type*} [TopologicalSpace X]
    (Ξ : EuclideanSpace ℝ (Fin m) → X → CappingSpace)
    (hΞ : Continuous (fun q : EuclideanSpace ℝ (Fin m) × X => Ξ q.1 q.2))
    {Z : Set (EuclideanSpace ℝ (Fin m) × X)} (hZ : IsCompact Z) {W : Set CappingSpace}
    (hW : IsOpen W) (hZW : ∀ q ∈ Z, Ξ q.1 q.2 ∈ W) :
    ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin m)), ∀ τ ∈ V, ∀ q ∈ Z, Ξ (q.1 + τ) q.2 ∈ W := by
  have hE : IsOpen {q : (EuclideanSpace ℝ (Fin m) × X) × EuclideanSpace ℝ (Fin m) |
      Ξ (q.1.1 + q.2) q.1.2 ∈ W} := by
    have hcont : Continuous (fun q : (EuclideanSpace ℝ (Fin m) × X) × EuclideanSpace ℝ (Fin m) =>
        Ξ (q.1.1 + q.2) q.1.2) :=
      hΞ.comp (((continuous_fst.fst).add continuous_snd).prodMk continuous_fst.snd)
    exact hcont.isOpen_preimage W hW
  have hsub : Z ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin m))) ⊆
      {q : (EuclideanSpace ℝ (Fin m) × X) × EuclideanSpace ℝ (Fin m) |
        Ξ (q.1.1 + q.2) q.1.2 ∈ W} := by
    rintro ⟨q, τ⟩ ⟨hq, rfl⟩
    simpa using hZW q hq
  obtain ⟨U, V, -, hVo, hZU, h0V, hUV⟩ :=
    generalized_tube_lemma hZ (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin m))))
      hE hsub
  refine ⟨V, hVo.mem_nhds (h0V (Set.mem_singleton 0)), fun τ hτ q hq => ?_⟩
  have hmem : (q, τ) ∈ U ×ˢ V := Set.mk_mem_prod (hZU hq) hτ
  simpa using hUV hmem

/-- **The norm form of `sep_shift_mem_nhds`.** -/
theorem sep_shift_mem_of_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    (Ξ : EuclideanSpace ℝ (Fin m) → X → CappingSpace)
    (hΞ : Continuous (fun q : EuclideanSpace ℝ (Fin m) × X => Ξ q.1 q.2))
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) {S : Set X} (hS : IsCompact S)
    {C W : Set CappingSpace} (hC : IsCompact C) (hW : IsOpen W) (hCW : C ⊆ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p : EuclideanSpace ℝ (Fin m)), p ∈ K → ∀ x ∈ S,
      ∀ (τ : EuclideanSpace ℝ (Fin m)), ‖τ‖ < ε → Ξ p x ∈ C → Ξ (p + τ) x ∈ W := by
  have hZcl : IsClosed ({q : EuclideanSpace ℝ (Fin m) × X | q.1 ∈ K ∧ q.2 ∈ S ∧
      Ξ q.1 q.2 ∈ C}) := by
    have hK' : IsClosed {q : EuclideanSpace ℝ (Fin m) × X | q.1 ∈ K} :=
      hK.isClosed.preimage continuous_fst
    have hS' : IsClosed {q : EuclideanSpace ℝ (Fin m) × X | q.2 ∈ S} :=
      hS.isClosed.preimage continuous_snd
    have hC' : IsClosed {q : EuclideanSpace ℝ (Fin m) × X | Ξ q.1 q.2 ∈ C} :=
      hC.isClosed.preimage hΞ
    have h := hK'.inter (hS'.inter hC')
    simpa only [Set.ofPred_and] using h
  have hZ : IsCompact ({q : EuclideanSpace ℝ (Fin m) × X | q.1 ∈ K ∧ q.2 ∈ S ∧
      Ξ q.1 q.2 ∈ C}) :=
    (hK.prod hS).of_isClosed_subset hZcl (fun q hq => ⟨hq.1, hq.2.1⟩)
  obtain ⟨V, hV, hVsub⟩ := sep_shift_mem_nhds Ξ hΞ hZ hW (fun q hq => hCW hq.2.2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨ε, hε, fun p hp x hx τ hτ hpC => hVsub τ (hball (by
    rw [Metric.mem_ball, dist_zero_right]; exact hτ)) (p, x) ⟨hp, hx, hpC⟩⟩


/-! ## 2. The charted `τ`-derivative of a chart perturbation is onto -/

/-- **The charted parameter-derivative of a chart perturbation is onto**, at every parameter and every
point of the space, whenever the value lies in the chart's source: the composite of the chart (a local
diffeomorphism) with the submersion `t ↦ Ξ t p` (`ChartPert`'s third conjunct) is onto. -/
theorem charted_pert_surj (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (_hQ : IsSmoothChart Q)
    (p : CappingSpace) (x₀ : CappingSpace) (t : EuclideanSpace ℝ (Fin m))
    (hsrc : Ξ t x₀ ∈ (chr p).source) :
    Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀)) t) := by
  set f : EuclideanSpace ℝ (Fin m) → CappingSpace := fun t' => Ξ t' x₀ with hf
  have hsm : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
  have hsrc' : f t ∈ (chr p).source := hsrc
  have hsurj_mf : Function.Surjective (mfderiv (𝓡 m) (𝓡 4) f t) := hΞ.2.2 t x₀
  have hderiv := fderiv_chart_comp f hsm p hsrc'
  have hsrc1 : f t ∈ (extChartAt (𝓡 4) (f t)).source := mem_extChartAt_source (I := 𝓡 4) (f t)
  have hsrc2 : f t ∈ (extChartAt (𝓡 4) p).source := by
    simpa [chr, extChartAt_source] using hsrc'
  have hsurjT : Function.Surjective (tangentCoordChange (𝓡 4) (f t) p (f t)) := by
    intro w
    exact ⟨tangentCoordChange (𝓡 4) p (f t) (f t) w,
      tangentCoordChange_comp_inv (x := p) (y := f t) (z := f t) ⟨hsrc2, hsrc1⟩ w⟩
  intro w
  obtain ⟨v, hv⟩ := hsurj_mf (tangentCoordChange (𝓡 4) p (f t) (f t) w)
  refine ⟨v, ?_⟩
  rw [hderiv]
  show tangentCoordChange (𝓡 4) (f t) p (f t) (mfderiv (𝓡 m) (𝓡 4) f t v) = w
  rw [hv]
  exact tangentCoordChange_comp_inv (x := p) (y := f t) (z := f t) ⟨hsrc2, hsrc1⟩ w

/-- **The same, for the shifted parameter** `τ' ↦ Ξ (c + τ') x₀`. -/
theorem charted_pert_shift_surj (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (p : CappingSpace) (x₀ : CappingSpace) (c t : EuclideanSpace ℝ (Fin m))
    (hsrc : Ξ (c + t) x₀ ∈ (chr p).source) :
    Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) =>
      chr p (Ξ (c + τ') x₀)) t) := by
  have hsm : ContMDiff (𝓡 m) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t' : EuclideanSpace ℝ (Fin m) => Ξ t' x₀) :=
    hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
  have hchart : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p)
      (Ξ (c + t) x₀) :=
    (contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := (⊤ : ℕ∞))).contMDiffAt
      ((chr p).open_source.mem_nhds hsrc)
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀)) (c + t) :=
    contMDiffAt_iff_contDiffAt.mp (hchart.comp (c + t) hsm.contMDiffAt)
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    rw [ne_eq, ← WithTop.coe_zero]
    exact fun h => ENat.top_ne_zero (WithTop.coe_injective h)
  have h2 : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀))
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀)) (c + t)) (c + t) :=
    (hcomp.differentiableAt htop).hasFDerivAt
  have h1 : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin m) => c + τ')
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) t :=
    (hasFDerivAt_id t).const_add c
  have h3 := h2.comp t h1
  have h4 : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) => chr p (Ξ (c + τ') x₀)) t
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀)) (c + t) := by
    have h5 : fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin m) => chr p (Ξ (c + τ') x₀)) t
        = (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' x₀)) (c + t)).comp
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) := h3.fderiv
    simpa using h5
  rw [h4]
  exact charted_pert_surj Ξ Q hΞ hQ p x₀ (c + t) hsrc

/-! ## 3. Joint smoothness of the two sides of the family in the box and the parameter -/

/-- The block map `(q : 𝔼^m × ℝ⁵) ↦ (q.1, mk2 (q.2 0) (q.2 1))` of the loop side. -/
def sepBlkL (m : ℕ) : EuclideanSpace ℝ (Fin m) × Amb 4 →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4))
    (FamBox.loopArgCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)))

lemma sepBlkL_apply (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    sepBlkL m q = (q.1, FamBox.loopArgCLM q.2) := rfl

/-- The block map `(q : 𝔼^m × ℝ⁵) ↦ (q.1, chainArg (q.2))` of the chain side. -/
def sepBlkC (m : ℕ) : EuclideanSpace ℝ (Fin m) × Amb 4 →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4))
    (FamBox.chainArgCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)))

lemma sepBlkC_apply (q : EuclideanSpace ℝ (Fin m) × Amb 4) :
    sepBlkC m q = (q.1, FamBox.chainArgCLM q.2) := rfl

/-- **The loop family on the flat parameter `𝔼²`** is jointly `C^∞` in the shift and the loop
parameter. -/
theorem sep_jointLoopFam2_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓡 4)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        chartLoopFam (sepQfam Ξ Q A B q.1) q.2) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q := hQ
  have hpath : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        sepPathL A B (q.2 0) + q.1) := by
    show ContMDiff _ _ _ (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
      (1 - q.2 0) • A.1 + (q.2 0) • B.1 + q.1)
    exact contMDiff_iff_contDiff.mpr (by fun_prop)
  have hexp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)))
      (𝓘(ℝ, ℂ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => ((q.2 1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
          Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I) :=
      (contDiff_const.mul h1).mul contDiff_const
    exact contMDiff_iff_contDiff.mpr (Complex.contDiff_exp.comp h2)
  have hmain := hΞ.2.1.comp (hpath.prodMk (hQsm.comp hexp))
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, chartLoopFam, sepQfam, coreLoop]

/-- **The loop side of the family on the five-box** is jointly `C^∞`. -/
theorem sep_jointLoopFam_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        famLoop (chartLoopFam (sepQfam Ξ Q A B q.1)) q.2) := by
  have h2 := sep_jointLoopFam2_contMDiff Ξ Q hΞ hQ A B
  have hblk : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (sepBlkL m) := (sepBlkL m).contMDiff
  refine (h2.comp hblk).congr fun q => ?_
  simp only [Function.comp_def, famLoop, sepBlkL_apply, FamBox.loopArgCLM_apply]

/-- **The chain side of the family on the five-box** is jointly `C^∞` in the shift and the box
variable (the shift does not occur: the family sweeps the plane presentation of the *unshifted*
perturbation). -/
theorem sep_jointChainFam_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        famChain (sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B 0)) q.2) := by
  have hchain := sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R 0
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
        sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B 0) q.2) := by
    have hprj : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4)))
        (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) => q.2) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    exact hchain.comp hprj
  have hblk : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (sepBlkC m) := (sepBlkC m).contMDiff
  refine (h2.comp hblk).congr fun q => ?_
  simp only [Function.comp_def, famChain, sepBlkC_apply, FamBox.chainArgCLM_apply]


/-! ## 4. A smooth cut-off on a euclidean space -/

/-- **A smooth cut-off equal to `1` on a compact set and supported in a prescribed open
superset.** -/
lemma sep_exists_cutoff_one_on_of_subset {n : ℕ}
    {K V : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ Ctop f ∧ (∀ x ∈ K, f x = 1) ∧
      tsupport f ⊆ V := by
  classical
  have hpt : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ V := by
    intro x
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.2))
    refine ⟨r / 4, by linarith, ?_⟩
    intro z hz
    apply hrsub
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  choose r hrpos hrsub using hpt
  have hbump : ∀ x : K, ∃ b : ContDiffBump (x : EuclideanSpace ℝ (Fin n)),
      b.rIn = r x ∧ b.rOut = 2 * r x := fun x =>
    ⟨⟨r x, 2 * r x, hrpos x, by linarith [hrpos x]⟩, rfl, rfl⟩
  choose b hb1 hb2 using hbump
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : EuclideanSpace ℝ (Fin n)) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrpos ⟨x, hx⟩)⟩)
  refine ⟨fun y => 1 - ∏ x ∈ s, (1 - b x y), ?_, ?_, ?_⟩
  · have hcont : ContDiff ℝ Ctop
        (fun y : EuclideanSpace ℝ (Fin n) => ∏ x ∈ s, (1 - b x y)) :=
      contDiff_prod (𝕜 := ℝ) (𝔸' := ℝ)
        (fun x _ => contDiff_const.sub (b x).contDiff)
    exact contDiff_const.sub hcont
  · intro y hy
    obtain ⟨x, hxs, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hbx : b x y = 1 := by
      refine (b x).one_of_mem_closedBall ?_
      rw [hb1 x, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hxy)
    have hz : (1 - b x y) = 0 := by rw [hbx]; ring
    show 1 - ∏ x ∈ s, (1 - b x y) = 1
    rw [Finset.prod_eq_zero hxs hz]
    ring
  · have hsupp : Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y)) ⊆
        ⋃ x ∈ s, tsupport (⇑(b x)) := by
      intro y hy
      by_contra hcon
      have h1 : (∏ x ∈ s, (1 - b x y)) = 1 :=
        Finset.prod_eq_one (fun x hx => by
          have hb0 : b x y = 0 := by
            by_contra hne
            exact hcon (Set.mem_iUnion₂.mpr ⟨x, hx, subset_tsupport _ hne⟩)
          rw [hb0]; ring)
      simp only [Function.mem_support, ne_eq] at hy
      exact hy (by rw [h1]; ring)
    have hclosed : IsClosed (⋃ x ∈ s, tsupport (⇑(b x))) :=
      isClosed_biUnion_finset (fun x _ => isClosed_tsupport _)
    calc tsupport (fun y => 1 - ∏ x ∈ s, (1 - b x y))
        = closure (Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y))) := rfl
      _ ⊆ closure (⋃ x ∈ s, tsupport (⇑(b x))) := closure_mono hsupp
      _ = ⋃ x ∈ s, tsupport (⇑(b x)) := hclosed.closure_eq
      _ ⊆ V := by
          rintro z hz
          obtain ⟨x, hxs, hxz⟩ := Set.mem_iUnion₂.mp hz
          exact hrsub x (by rw [(b x).tsupport_eq, hb2 x] at hxz; exact hxz)

/-- **A positive radius below finitely many positive radii.** -/
lemma exists_pos_le_all_fin {r : ℕ} (f : Fin r → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exact ⟨1, one_pos, fun i => absurd i.isLt (by omega)⟩
  · refine ⟨(Finset.univ.image f).min' ⟨f ⟨0, hr⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,
      ?_, fun i => Finset.min'_le _ (f i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    exact Finset.lt_min'_iff _ _ |>.mpr (fun y hy => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hf j)


/-- **A point outside the topological support of `f` has a neighbourhood on which `f` vanishes.** -/
lemma sep_eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **The converse of `Work.Drive.FamBox.chartDif_face_of_kernel`**: surjectivity of the meet
derivative *and* of its restriction to the coordinate hyperplane `{v | v i = 0}` produce a kernel
vector of the difference of derivatives whose `i`-th coordinate does not vanish. -/
lemma sep_exists_sigma_of_faceSurjective {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]
    (p : M) (F G : Amb 4 → M)
    (hF : ContMDiff (𝓡 5) (𝓡 4) Ctop F) (hG : ContMDiff (𝓡 5) (𝓡 4) Ctop G)
    {y : Amb 4} (hy : y ∈ FamBox.chartReg p F G) (heq : F y = G y) {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (FamBox.chartDif p F G) y))
    (hface : Function.Surjective (fun v : {v : Amb 4 // v i = 0} =>
      fderiv ℝ (FamBox.chartDif p F G) y v.1)) :
    ∃ σ : Amb 4, FamBox.Lf F G y σ = 0 ∧ σ i ≠ 0 := by
  set Φ : Amb 4 →L[ℝ] Tgt 4 := fderiv ℝ (FamBox.chartDif p F G) y with hΦ
  refine ⟨Work.Drive.cofactorVec Φ, ?_, ?_⟩
  · have hker : fderiv ℝ (FamBox.chartDif p F G) y (Work.Drive.cofactorVec Φ) = 0 := by
      rw [← hΦ]
      exact Work.Drive.cofactorVec_mem_ker Φ
    have hTeq := FamBox.fderiv_chartDif_eq_Lf p F G hF hG hy heq (Work.Drive.cofactorVec Φ)
    rw [hker] at hTeq
    have hsrc : F y ∈ (extChartAt (𝓡 4) p).source := by
      have h := hy.1
      rwa [chr, ← extChartAt_source (I := 𝓡 4) p] at h
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (F y) p (F y)) :=
      tangentCoordChange_injective (x := F y) (y := p) (z := F y)
        ⟨mem_extChartAt_source (I := 𝓡 4) (F y), hsrc⟩
    refine hinj ?_
    rw [map_zero]
    exact hTeq.symm
  · exact (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero Φ hsurj i).mp hface

/-! ## 5. The Sard regularity of the separated family -/

/-! ## 5. The Sard regularity of the separated family -/



/-! ## The definitions of the separated family and their basic lemmas -/

/-- The plane presentation of the sweep side of the separated family (with the second shift `0`). -/
def sepNc (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    EuclideanSpace ℝ (Fin 4) → CappingSpace :=
  sweepFam c (fun u => 1 - u) (sepPfam Ξ Q tR t'R A B 0)

/-- The loop side of the separated family: the core loops of the shifted charts along the path. -/
def sepLfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) → Amb 4 → CappingSpace :=
  fun τ z => famLoop (chartLoopFam (sepQfam Ξ Q A B τ)) z

/-- The chain side of the separated family (independent of the shift). -/
def sepNfam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    EuclideanSpace ℝ (Fin m) → Amb 4 → CappingSpace :=
  fun _ z => famChain (sepNc Ξ Q c A B tR t'R) z

/-- The cut-off-scaled charted difference system of the separated family in one chart. -/
def sepSys (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (c : ℝ) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (γ : EuclideanSpace ℝ (Fin m) → ℝ) (β : Amb 4 → ℝ) (p : CappingSpace) :
    EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 :=
  fun q => (γ q.1 * β q.2) •
    FamBox.chartDif p (sepLfam Ξ Q A B q.1) (sepNfam Ξ Q c A B tR t'R q.1) q.2

theorem sepLfam_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => sepLfam Ξ Q A B q.1 q.2) := by
  simpa only [sepLfam] using sep_jointLoopFam_contMDiff Ξ Q hΞ hQ A B

theorem sepNfam_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => sepNfam Ξ Q c A B tR t'R q.1 q.2) := by
  simpa only [sepNfam, sepNc] using sep_jointChainFam_contMDiff Ξ Q c hΞ hQ A B tR t'R

/-- The chain side of the separated family is continuous as a function of the box alone. -/
theorem sepNfam_cont (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ) :
    Continuous (fun z : Amb 4 => sepNfam Ξ Q c A B tR t'R 0 z) := by
  show Continuous (fun z : Amb 4 => famChain (sepNc Ξ Q c A B tR t'R) z)
  exact (FamBox.contMDiff_famChain _
    (by simpa only [sepNc] using sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R 0)).continuous

/-- The value formula of the loop side of the separated family. -/
theorem sepLfam_apply (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (τ : EuclideanSpace ℝ (Fin m)) (z : Amb 4) :
    sepLfam Ξ Q A B τ z = Ξ (sepPathL A B (z 0) + τ) (coreLoop Q (z 1)) := by
  simp only [sepLfam, famLoop, chartLoopFam, sepQfam, coreLoop, mk2_apply_zero, mk2_apply_one]

/-- **Joint smoothness of the charted difference of the two sides**, at a point where both values
lie in the chart's source. -/
theorem sep_chartDif_contDiffAt (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (p : CappingSpace) (q : EuclideanSpace ℝ (Fin m) × Amb 4)
    (h1 : sepLfam Ξ Q A B q.1 q.2 ∈ (chr p).source)
    (h2 : sepNfam Ξ Q c A B tR t'R q.1 q.2 ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q' : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      FamBox.chartDif p (sepLfam Ξ Q A B q'.1) (sepNfam Ξ Q c A B tR t'R q'.1) q'.2) q := by
  have hc1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (sepLfam Ξ Q A B q.1 q.2) :=
    (contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)).contMDiffAt
      ((chr p).open_source.mem_nhds h1)
  have hA : ContDiffAt ℝ Ctop (fun q' : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      chr p (sepLfam Ξ Q A B q'.1 q'.2)) q :=
    contMDiffAt_iff_contDiffAt.mp
      (hc1.comp q (sepLfam_contMDiff Ξ Q hΞ hQ A B).contMDiffAt)
  have hc2 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (sepNfam Ξ Q c A B tR t'R q.1 q.2) :=
    (contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)).contMDiffAt
      ((chr p).open_source.mem_nhds h2)
  have hB : ContDiffAt ℝ Ctop (fun q' : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      chr p (sepNfam Ξ Q c A B tR t'R q'.1 q'.2)) q :=
    contMDiffAt_iff_contDiffAt.mp
      (hc2.comp q (sepNfam_contMDiff Ξ Q c hΞ hQ A B tR t'R).contMDiffAt)
  have h := hA.sub hB
  show ContDiffAt ℝ Ctop (fun q' : EuclideanSpace ℝ (Fin m) × Amb 4 =>
    chr p (sepLfam Ξ Q A B q'.1 q'.2) - chr p (sepNfam Ξ Q c A B tR t'R q'.1 q'.2)) q
  exact h

/-- **The parameter-derivative of the system is onto at a zero at which the cut-offs are `1`.** -/
theorem sep_sys_surj (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ Ctop γ)
    {β : Amb 4 → ℝ} (hβ : ContDiff ℝ Ctop β)
    (p : CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (z : Amb 4)
    (hγ1 : γ t = 1) (hβ1 : β z = 1)
    (h1 : sepLfam Ξ Q A B t z ∈ (chr p).source)
    (h2 : sepNfam Ξ Q c A B tR t'R t z ∈ (chr p).source)
    (h0 : sepSys Ξ Q c A B tR t'R γ β p (t, z) = 0) :
    Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
      sepSys Ξ Q c A B tR t'R γ β p (t', z)) t) := by
  have htop : Ctop ≠ 0 := by
    rw [ne_eq, ← WithTop.coe_zero]
    exact fun h => ENat.top_ne_zero (WithTop.coe_injective h)
  -- the charted value of the loop along the shift, and the constant charted value of the chain
  have hsrc : Ξ (sepPathL A B (z 0) + t) (coreLoop Q (z 1)) ∈ (chr p).source := by
    rw [← sepLfam_apply Ξ Q A B t z]
    exact h1
  have hA : Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t) :=
    charted_pert_shift_surj Ξ Q hΞ hQ p (coreLoop Q (z 1)) (sepPathL A B (z 0)) t hsrc
  -- the smoothness of the loop's charted value along the shift
  have hsmLoop : ContDiffAt ℝ Ctop (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t := by
    have hΞt : ContMDiffAt (𝓡 m) (𝓡 4) Ctop (fun t' : EuclideanSpace ℝ (Fin m) =>
        Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1))) t := by
      have h1' : ContMDiffAt (𝓡 m) (𝓡 m) Ctop (fun t' : EuclideanSpace ℝ (Fin m) =>
          sepPathL A B (z 0) + t') t :=
        contMDiffAt_const.add contMDiffAt_id
      have h2' : ContMDiffAt (𝓡 m) (𝓡 4) Ctop (fun t' : EuclideanSpace ℝ (Fin m) =>
          Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1))) t := by
        have h3' : ContMDiff (𝓡 m) (𝓡 4) Ctop (fun t' : EuclideanSpace ℝ (Fin m) =>
            Ξ t' (coreLoop Q (z 1))) :=
          hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
        exact h3'.contMDiffAt.comp t h1'
      exact h2'
    have hch : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p)
        (Ξ (sepPathL A B (z 0) + t) (coreLoop Q (z 1))) :=
      (contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)).contMDiffAt
        ((chr p).open_source.mem_nhds hsrc)
    exact contMDiffAt_iff_contDiffAt.mp (hch.comp t hΞt)
  have hχ0 : FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z = 0 := by
    have h : (γ t * β z) •
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z = 0 := by
      simpa only [sepSys] using h0
    simpa only [hγ1, hβ1, mul_one, one_smul] using h
  -- the function identification
  have hfun1 : (fun t' : EuclideanSpace ℝ (Fin m) =>
        sepSys Ξ Q c A B tR t'R γ β p (t', z))
      = fun t' : EuclideanSpace ℝ (Fin m) => (γ t' * β z) •
          (chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))
            - chr p (sepNfam Ξ Q c A B tR t'R 0 z)) := by
    funext t'
    simp only [sepSys, FamBox.chartDif, sepLfam_apply Ξ Q A B t' z, sepNfam]
  rw [hfun1]
  -- the product rule
  have hγβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z)
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) t) t :=
    ((hγ.contDiffAt.mul contDiffAt_const).differentiableAt htop).hasFDerivAt
  have hloop : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1))))
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t) t :=
    (hsmLoop.differentiableAt htop).hasFDerivAt
  have hloopSub : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
      chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))
        - chr p (sepNfam Ξ Q c A B tR t'R 0 z))
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t) t :=
    hloop.sub_const _
  have hsmul := hγβp.smul hloopSub
  have h5 : (γ t * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t)
      + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) t).smulRight
          (chr p (Ξ (sepPathL A B (z 0) + t) (coreLoop Q (z 1)))
            - chr p (sepNfam Ξ Q c A B tR t'R 0 z))
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t := by
    have hzeq : chr p (Ξ (sepPathL A B (z 0) + t) (coreLoop Q (z 1)))
        - chr p (sepNfam Ξ Q c A B tR t'R 0 z) = 0 := by
      rw [show chr p (Ξ (sepPathL A B (z 0) + t) (coreLoop Q (z 1)))
          - chr p (sepNfam Ξ Q c A B tR t'R 0 z)
          = FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z from rfl]
      exact hχ0
    rw [hγ1, hβ1, mul_one, hzeq]
    simp
  have hderiv : fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => (γ t' * β z) •
      (chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))
        - chr p (sepNfam Ξ Q c A B tR t'R 0 z))) t
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ (sepPathL A B (z 0) + t') (coreLoop Q (z 1)))) t :=
    (h5 ▸ hsmul).fderiv
  rw [hderiv]
  exact hA


/-- The differentiability order `⊤` is positive. -/
theorem sep_ctop_ne_zero : Ctop ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  exact fun h => ENat.top_ne_zero (WithTop.coe_injective h)

/-- **The charted difference has a derivative in the box variable**, at a point where both values lie
in the chart's source. -/
theorem sep_chartDif_hasFDerivAt_z (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (p : CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (z : Amb 4)
    (h1 : sepLfam Ξ Q A B t z ∈ (chr p).source)
    (h2 : sepNfam Ξ Q c A B tR t'R t z ∈ (chr p).source) :
    HasFDerivAt (fun z' : Amb 4 =>
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z')
      (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z) z := by
  have hcd := sep_chartDif_contDiffAt Ξ Q c hΞ hQ A B tR t'R p (t, z) h1 h2
  have hpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (t, z')) z :=
    contDiffAt_const.prodMk contDiffAt_id
  have hslice : ContDiffAt ℝ Ctop (fun z' : Amb 4 =>
      FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z :=
    hcd.comp z hpair
  exact (hslice.differentiableAt sep_ctop_ne_zero).hasFDerivAt

/-- **The box-derivative of the system at a zero with cut-offs `1` is the box-derivative of the
charted difference.** -/
theorem sep_sys_zderiv_eq (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    {γ : EuclideanSpace ℝ (Fin m) → ℝ} {β : Amb 4 → ℝ} (hβ : ContDiff ℝ Ctop β)
    (p : CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (z : Amb 4)
    (hγ1 : γ t = 1) (hβ1 : β z = 1)
    (h1 : sepLfam Ξ Q A B t z ∈ (chr p).source)
    (h2 : sepNfam Ξ Q c A B tR t'R t z ∈ (chr p).source)
    (h0 : sepSys Ξ Q c A B tR t'R γ β p (t, z) = 0) :
    fderiv ℝ (fun z' : Amb 4 => sepSys Ξ Q c A B tR t'R γ β p (t, z')) z
      = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z := by
  have hχ0 : FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z = 0 := by
    have h : (γ t * β z) •
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z = 0 := by
      simpa only [sepSys] using h0
    simpa only [hγ1, hβ1, mul_one, one_smul] using h
  have hχp := sep_chartDif_hasFDerivAt_z Ξ Q c hΞ hQ A B tR t'R p t z h1 h2
  have hβp : HasFDerivAt (fun z' : Amb 4 => γ t * β z')
      (fderiv ℝ (fun z' : Amb 4 => γ t * β z') z) z :=
    ((contDiffAt_const.mul hβ.contDiffAt).differentiableAt sep_ctop_ne_zero).hasFDerivAt
  have hsmul := hβp.smul hχp
  have h5 : (γ t * β z) • (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z)
      + (fderiv ℝ (fun z' : Amb 4 => γ t * β z') z).smulRight
          (FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z)
      = fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z := by
    rw [hγ1, hβ1, mul_one, hχ0]
    simp
  have hgoal : (fun z' : Amb 4 => sepSys Ξ Q c A B tR t'R γ β p (t, z'))
      = fun z' : Amb 4 => (γ t * β z') •
          FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z' := by
    funext z'
    simp only [sepSys]
  rw [hgoal]
  exact (h5 ▸ hsmul).fderiv

/-- **The charted box-derivative onto at a meet gives the intrinsic transversality.** -/
theorem sep_Lf_surj (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (p : CappingSpace) (t : EuclideanSpace ℝ (Fin m)) (z : Amb 4)
    (h1 : sepLfam Ξ Q A B t z ∈ (chr p).source)
    (h2 : sepNfam Ξ Q c A B tR t'R t z ∈ (chr p).source)
    (heq : sepLfam Ξ Q A B t z = sepNfam Ξ Q c A B tR t'R t z)
    (hsurj : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
      FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z') z)) :
    Function.Surjective (FamBox.Lf (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z) := by
  have hFsm : ContMDiff (𝓡 5) (𝓡 4) Ctop (sepLfam Ξ Q A B t) :=
    FamBox.contMDiff_famLoop _ (sep_contMDiff_chartLoopFam Ξ Q hΞ hQ A B t)
  have hGsm : ContMDiff (𝓡 5) (𝓡 4) Ctop (sepNfam Ξ Q c A B tR t'R t) := by
    show ContMDiff (𝓡 5) (𝓡 4) Ctop (famChain (sepNc Ξ Q c A B tR t'R))
    exact FamBox.contMDiff_famChain _
      (by simpa only [sepNc] using sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R 0)
  have hcont : z ∈ FamBox.chartReg p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) := ⟨h1, h2⟩
  have heqfd : fderiv ℝ (FamBox.chartDif p (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t)) z
      = (tangentCoordChange (𝓡 4) (sepLfam Ξ Q A B t z) p (sepLfam Ξ Q A B t z)).comp
          (FamBox.Lf (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z) :=
    ContinuousLinearMap.ext fun v =>
      FamBox.fderiv_chartDif_eq_Lf p _ _ hFsm hGsm hcont heq v
  have hsurjComp : Function.Surjective
      ((tangentCoordChange (𝓡 4) (sepLfam Ξ Q A B t z) p (sepLfam Ξ Q A B t z)).comp
        (FamBox.Lf (sepLfam Ξ Q A B t) (sepNfam Ξ Q c A B tR t'R t) z)) := by
    rw [← heqfd]
    exact hsurj
  have hsrc1 : sepLfam Ξ Q A B t z ∈ (extChartAt (𝓡 4) (sepLfam Ξ Q A B t z)).source :=
    mem_extChartAt_source (I := 𝓡 4) _
  have hsrc2 : sepLfam Ξ Q A B t z ∈ (extChartAt (𝓡 4) p).source := by
    rw [extChartAt_source]
    exact h1
  have hinj : Function.Injective
      (tangentCoordChange (𝓡 4) (sepLfam Ξ Q A B t z) p (sepLfam Ξ Q A B t z)) :=
    tangentCoordChange_injective (x := sepLfam Ξ Q A B t z) (y := p)
      (z := sepLfam Ξ Q A B t z) ⟨hsrc1, hsrc2⟩
  intro w
  obtain ⟨v, hv⟩ := hsurjComp (tangentCoordChange (𝓡 4) (sepLfam Ξ Q A B t z) p
    (sepLfam Ξ Q A B t z) w)
  exact ⟨v, hinj hv⟩



/-- The loop side at a fixed shift, as a map on the five-box. -/
theorem sepLfam_slice_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 5) (𝓡 4) Ctop (sepLfam Ξ Q A B t) :=
  FamBox.contMDiff_famLoop _ (sep_contMDiff_chartLoopFam Ξ Q hΞ hQ A B t)

/-- The chain side at a fixed shift, as a map on the five-box. -/
theorem sepNfam_slice_contMDiff (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 5) (𝓡 4) Ctop (sepNfam Ξ Q c A B tR t'R t) := by
  show ContMDiff (𝓡 5) (𝓡 4) Ctop (famChain (sepNc Ξ Q c A B tR t'R))
  exact FamBox.contMDiff_famChain _
    (by simpa only [sepNc] using sep_contMDiff_sweepFam Ξ Q c hΞ hQ A B tR t'R 0)

end

end Work.Drive
