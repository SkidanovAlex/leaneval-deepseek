import Mathlib
import Submission.Work.MetricSquare.generic_regularization_of_family
import Submission.Work.MetricSquare.generic_regularization_of_family_face_ball
import Submission.Work.Drive.Interfaces
import Submission.Work.Sard.submersion_local_form
import Submission.Work.Sard.weak_interior_empty_open_prod

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# Generic regularization in arbitrary dimension, for a finite family of maps

`Work.MetricSquare.generic_regularization_of_family_face_ball` proves the Sard-type statement that,
for a *single* smooth map `Φ : ℝ^m × ℝ^7 → ℝ^6`, one can find a parameter `p` with `‖p‖ < ε` at
which the `z`-derivative of `Φ (p, ·)` is surjective at every zero inside the unit box, and at every
zero on a face `z i = 0` or `z i = 1` the restriction of that derivative to the coordinate
hyperplane `{v // v i = 0}` is surjective.

Here we prove the statement in *arbitrary* dimension `n` (`z ∈ ℝ^{n+1}`, target `ℝ^n`) and for a
*finite family* `Φ : ι → ℝ^m × ℝ^{n+1} → ℝ^n` simultaneously.  The proof is the same Baire
argument; all the analytic ingredients (`Work.Sard.submersion_local_form`,
`Work.Sard.prod.weakSard_all`, `Work.Sard.prod.isCompact_inter_crit`,
`Work.Sard.wp.interior_eq_empty_iUnion_isClosed`) are already dimension-free, so what has to be
redone is the assembly: the local normal form, the chart dictionary, and the finite family of
auxiliary face maps.
-/

set_option maxHeartbeats 2000000

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter Metric

noncomputable section

namespace Gen

/-- The parameter space `ℝ^m`. -/
abbrev Pm (m : ℕ) : Type := EuclideanSpace ℝ (Fin m)

/-- The auxiliary space of the chart: `ℝ^{m+1}`. -/
abbrev Qm (m : ℕ) : Type := Fin (m + 1) → ℝ

/-! ## The chart lemmas (dimension-free) -/

/-- Differentiating `Φ (e y) = y.1` along the chart gives `DΦ (e y) ∘ De y = fst`. -/
lemma chart_comp_fst {P Z W Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (Φ : P × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (W × Q) (P × Z))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : W × Q → P × Z) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (w : Q) (hw : ((0 : W), w) ∈ e.source) :
    (fderiv ℝ Φ (e ((0 : W), w))).comp
        (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w))
      = ContinuousLinearMap.fst ℝ W Q := by
  have hsource_open : IsOpen e.source := e.open_source
  have hfd_e : HasFDerivAt (e : W × Q → P × Z)
      (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)) ((0 : W), w) :=
    ((he_smooth.contDiffAt (hsource_open.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hfd_Phi : HasFDerivAt Φ (fderiv ℝ Φ (e ((0 : W), w))) (e ((0 : W), w)) :=
    (hΦ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hfd_Phi.comp ((0 : W), w) hfd_e
  have heq : (fun y : W × Q => Φ (e y)) =ᶠ[𝓝 ((0 : W), w)] (fun y => y.1) := by
    filter_upwards [hsource_open.mem_nhds hw] with y hy using he_Phi y hy
  have hfd_fst : HasFDerivAt (fun y : W × Q => y.1)
      (ContinuousLinearMap.fst ℝ W Q) ((0 : W), w) := hasFDerivAt_fst
  have h1 : fderiv ℝ (fun y : W × Q => Φ (e y)) ((0 : W), w)
      = ContinuousLinearMap.fst ℝ W Q := by
    rw [heq.fderiv_eq, hfd_fst.fderiv]
  have h2 : fderiv ℝ (fun y : W × Q => Φ (e y)) ((0 : W), w)
      = (fderiv ℝ Φ (e ((0 : W), w))).comp
          (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)) := hcomp.fderiv
  rw [← h2, h1]

/-- The range of `De 0 ∘ inr` is the kernel of `DΦ (e 0)`. -/
lemma chart_range {P Z W Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (Φ : P × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (W × Q) (P × Z))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : W × Q → P × Z) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : W × Q → P × Z) e.source y))
    (w : Q) (hw : ((0 : W), w) ∈ e.source) :
    (LinearMap.range ((fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)).comp
        (ContinuousLinearMap.inr ℝ W Q) : Q →ₗ[ℝ] (P × Z)))
      = (fderiv ℝ Φ (e ((0 : W), w))).ker := by
  have hsource_open : IsOpen e.source := e.open_source
  have hderiv_eq : fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)
      = fderivWithin ℝ (e : W × Q → P × Z) e.source ((0 : W), w) :=
    (fderivWithin_of_isOpen hsource_open hw).symm
  have hDe_bij : Function.Bijective (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)) := by
    rw [hderiv_eq]; exact he_deriv ((0 : W), w) hw
  have hchain := chart_comp_fst Φ hΦ e he_smooth he_Phi w hw
  refine le_antisymm ?_ ?_
  · rintro v ⟨w', rfl⟩
    show (fderiv ℝ Φ (e ((0 : W), w)))
      ((fderiv ℝ (e : W × Q → P × Z) ((0 : W), w))
        (ContinuousLinearMap.inr ℝ W Q w')) = 0
    have hthis := congrArg (fun (T : (W × Q) →L[ℝ] W) =>
      T (ContinuousLinearMap.inr ℝ W Q w')) hchain
    simpa using hthis
  · intro v hv
    obtain ⟨z', hz'⟩ := hDe_bij.2 v
    have hv0 : (fderiv ℝ Φ (e ((0 : W), w))) v = 0 := hv
    have hfst : z'.1 = 0 := by
      have hthis := congrArg (fun (T : (W × Q) →L[ℝ] W) => T z') hchain
      rw [ContinuousLinearMap.comp_apply, hz', hv0] at hthis
      simpa using hthis.symm
    refine ⟨z'.2, ?_⟩
    have hinr : ContinuousLinearMap.inr ℝ W Q z'.2 = z' := by
      rw [ContinuousLinearMap.inr_apply]
      exact Prod.ext hfst.symm rfl
    show (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w))
      (ContinuousLinearMap.inr ℝ W Q z'.2) = v
    rw [hinr, hz']

/-- The derivative of the parametrised projection `w ↦ (e (0,w)).1`. -/
lemma fderiv_chart_gamma {P Z W Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (Φ : P × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (W × Q) (P × Z))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : W × Q → P × Z) e.source)
    (w : Q) (hw : ((0 : W), w) ∈ e.source) :
    fderiv ℝ (fun w' : Q => (e ((0 : W), w')).1) w
      = (ContinuousLinearMap.fst ℝ P Z).comp
          ((fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)).comp
            (ContinuousLinearMap.inr ℝ W Q)) := by
  have hsource_open : IsOpen e.source := e.open_source
  have hfd_e : HasFDerivAt (e : W × Q → P × Z)
      (fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)) ((0 : W), w) :=
    ((he_smooth.contDiffAt (hsource_open.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt
  have hι : HasFDerivAt (fun w' : Q => ((0 : W), w'))
      (ContinuousLinearMap.inr ℝ W Q) w := by
    simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ W Q)).const_add
      ((0 : W), 0)
  have h1 := hfd_e.comp w hι
  have h2 := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ P Z)).comp w h1
  exact h2.fderiv

/-- The range of the derivative of the parametrised projection is the image of the kernel of the
full derivative under the first projection. -/
lemma chart_range_gamma {P Z W Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (Φ : P × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (W × Q) (P × Z))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : W × Q → P × Z) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : W × Q → P × Z) e.source y))
    (w : Q) (hw : ((0 : W), w) ∈ e.source) :
    Set.range (fderiv ℝ (fun w' : Q => (e ((0 : W), w')).1) w)
      = (ContinuousLinearMap.fst ℝ P Z) ''
          ((fderiv ℝ Φ (e ((0 : W), w))).ker : Set (P × Z)) := by
  have hrange := chart_range Φ hΦ e he_smooth he_Phi he_deriv w hw
  rw [fderiv_chart_gamma Φ hΦ e he_smooth w hw]
  ext v
  constructor
  · rintro ⟨w', rfl⟩
    refine ⟨((fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)).comp
      (ContinuousLinearMap.inr ℝ W Q)) w', ?_, rfl⟩
    rw [← hrange]
    exact ⟨w', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ LinearMap.range ((fderiv ℝ (e : W × Q → P × Z) ((0 : W), w)).comp
        (ContinuousLinearMap.inr ℝ W Q) : Q →ₗ[ℝ] (P × Z)) := by
      rw [hrange]; exact hy
    obtain ⟨w', hw'⟩ := hy'
    exact ⟨w', congrArg (ContinuousLinearMap.fst ℝ P Z) hw'⟩

/-- On the chart, the surjectivity of the derivative of the projection `γ` is equivalent to the
surjectivity of the partial derivative in the coordinate direction. -/
lemma chart_surjective_iff {P Z W Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (Φ : P × Z → W) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (e : OpenPartialHomeomorph (W × Q) (P × Z))
    (he_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : W × Q → P × Z) e.source)
    (he_Phi : ∀ y ∈ e.source, Φ (e y) = y.1)
    (he_deriv : ∀ y ∈ e.source,
      Function.Bijective (fderivWithin ℝ (e : W × Q → P × Z) e.source y))
    (w : Q) (hw : ((0 : W), w) ∈ e.source)
    (hDp : Function.Surjective
      (fderiv ℝ (fun p' : P => Φ (p', (e ((0 : W), w)).2)) (e ((0 : W), w)).1)) :
    Function.Surjective (fderiv ℝ (fun w' : Q => (e ((0 : W), w')).1) w)
      ↔ Function.Surjective
          (fderiv ℝ (fun z' : Z => Φ ((e ((0 : W), w)).1, z')) (e ((0 : W), w)).2) := by
  have hrg := chart_range_gamma Φ hΦ e he_smooth he_Phi he_deriv w hw
  have hker := Work.MetricSquare.fst_image_ker_eq_univ_iff Φ hΦ (e ((0 : W), w)) hDp
  rw [show Function.Surjective (fderiv ℝ (fun w' : Q => (e ((0 : W), w')).1) w)
      ↔ Set.range (fderiv ℝ (fun w' : Q => (e ((0 : W), w')).1) w) = Set.univ
      from Set.range_eq_univ.symm, hrg]
  exact hker

/-! ## The bad parameter sets -/

/-- The set of parameters `p` at which `Ψ (p, ·)` has a zero in the unit box at which the
`z`-derivative fails to be surjective. -/
def badSetGen (m n : ℕ) (Ψ : Pm m × Amb n → Tgt n) : Set (Pm m) :=
  {p | ∃ z ∈ Submission.Drive.unitBox n, Ψ (p, z) = 0 ∧
    ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (p, z')) z)}

/-- **Local structure of the bad set** in arbitrary dimension.  For a point `(p₀,z₀)` in the box at
which `Φ` vanishes and the parameter-derivative is surjective, there is a neighbourhood `U` of
`(p₀,z₀)` and a compact set `A` with empty interior such that every point of `U` which is a *bad*
zero (a zero at which the `z`-derivative fails to be surjective) has its first coordinate in `A`. -/
lemma exists_local_good_gen (m n : ℕ)
    (Φ : Pm m × Amb n → Tgt n) (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (p₀ : Pm m) (z₀ : Amb n) (h0 : Φ (p₀, z₀) = 0)
    (hsurjp : Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z₀)) p₀)) :
    ∃ U : Set (Pm m × Amb n), IsOpen U ∧ (p₀, z₀) ∈ U ∧
      ∃ A : Set (Pm m), IsCompact A ∧ interior A = ∅ ∧
        ∀ (p : Pm m) (z : Amb n), (p, z) ∈ U →
          Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p) →
          Φ (p, z) = 0 →
          ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Φ (p, z')) z) → p ∈ A := by
  classical
  have hfull : Function.Surjective (fderiv ℝ Φ (p₀, z₀)) := by
    intro w
    obtain ⟨v, hv⟩ := hsurjp w
    refine ⟨ContinuousLinearMap.inl ℝ (Pm m) (Amb n) v, ?_⟩
    have h1 : ((fderiv ℝ Φ (p₀, z₀)).comp
        (ContinuousLinearMap.inl ℝ (Pm m) (Amb n))) v
        = (fderiv ℝ (fun p' : Pm m => Φ (p', z₀)) p₀) v := by
      rw [Work.MetricSquare.fd_comp_inl Φ hΦ p₀ z₀]
    simpa using h1.trans hv
  set A0 : (Pm m × Amb n) →L[ℝ] Tgt n := fderiv ℝ Φ (p₀, z₀) with hA0
  set K0 : Submodule ℝ (Pm m × Amb n) := A0.ker with hK0
  obtain ⟨C0, hC0⟩ := K0.exists_isCompl
  have hXdim : Module.finrank ℝ (Pm m × Amb n) = m + (n + 1) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  have hrange : Module.finrank ℝ (LinearMap.range (A0 : (Pm m × Amb n) →ₗ[ℝ] Tgt n)) = n := by
    rw [LinearMap.range_eq_top.mpr hfull, finrank_top, finrank_euclideanSpace_fin]
  have hK0dim : Module.finrank ℝ K0 = m + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((A0 : (Pm m × Amb n) →ₗ[ℝ] Tgt n))
    rw [← hK0] at h
    rw [hrange, hXdim] at h
    omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      (R := ℝ) (M := K0) (M' := Qm m) (by rw [hK0dim]; simp)
  let lam : (Pm m × Amb n) →L[ℝ] Qm m := LinearMap.toContinuousLinearMap
    ((φ : K0 →ₗ[ℝ] Qm m).comp (K0.projectionOnto C0 hC0))
  have hlamker : lam.ker = C0 := by
    change ((φ : K0 →ₗ[ℝ] Qm m).comp (K0.projectionOnto C0 hC0)).ker = C0
    rw [LinearMap.ker_comp]
    have hphi : (φ : K0 →ₗ[ℝ] Qm m).ker = ⊥ := LinearMap.ker_eq_bot.mpr φ.injective
    rw [hphi, Submodule.comap_bot, Submodule.ker_projectionOnto]
  have hlam : Disjoint (fderiv ℝ Φ (p₀, z₀)).ker lam.ker := by
    rw [← hA0, ← hK0, hlamker]
    exact hC0.disjoint
  have hdim : Module.finrank ℝ (Pm m × Amb n) = Module.finrank ℝ (Tgt n) + (m + 1) := by
    rw [hXdim, finrank_euclideanSpace_fin]; omega
  obtain ⟨e, hx0t, he_smooth, he_Phi, he_symm, he_deriv⟩ :=
    Work.Sard.submersion_local_form (m + 1) hdim Φ hΦ (p₀, z₀) hfull lam hlam
  -- the parametrised projection and its critical set
  let γ : Qm m → Pm m := fun w => (e ((0 : Tgt n), w)).1
  let Uγ : Set (Qm m) := {w | ((0 : Tgt n), w) ∈ e.source}
  have hUγ_open : IsOpen Uγ := e.open_source.preimage (by fun_prop)
  have hγ_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ Uγ := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Qm m => ((0 : Tgt n), w)) Uγ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Qm m => e ((0 : Tgt n), w)) Uγ :=
      he_smooth.comp h1 (fun w hw => hw)
    simpa [γ, Function.comp_def] using
      contDiffOn_fst.comp h2 (fun _ _ => Set.mem_univ _)
  have hw₀ : lam (p₀, z₀) ∈ Uγ := by
    have h1 : e.symm (p₀, z₀) ∈ e.source := e.map_target hx0t
    rw [he_symm (p₀, z₀) hx0t, h0] at h1
    exact h1
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp (hUγ_open.mem_nhds hw₀)
  set Kc : Set (Qm m) := Metric.closedBall (lam (p₀, z₀)) (ρ / 2) with hKc
  have hKc_sub : Kc ⊆ Uγ := by
    intro w hw
    refine hρsub ?_
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hw
    linarith [hρpos]
  have hKc_compact : IsCompact Kc := isCompact_closedBall _ _
  have hKc_int : lam (p₀, z₀) ∈ interior Kc := by
    refine interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith [hρpos]))
  set Scrit : Set (Qm m) := {w | ¬ Function.Surjective (fderiv ℝ γ w)} with hScrit
  have hScrit_compact : IsCompact (Kc ∩ Scrit) := by
    rw [hScrit]
    exact Work.Sard.prod.isCompact_inter_crit hUγ_open γ hγ_smooth hKc_compact hKc_sub
  refine ⟨e.target ∩ lam ⁻¹' (interior Kc),
    e.open_target.inter (isOpen_interior.preimage lam.continuous),
    ⟨hx0t, hKc_int⟩, γ '' (Kc ∩ Scrit), ?_, ?_, ?_⟩
  · exact hScrit_compact.image_of_continuousOn
      (hγ_smooth.continuousOn.mono (fun w hw => hKc_sub hw.1))
  · refine le_bot_iff.mp ?_
    have hsub : Kc ∩ Scrit ⊆ Uγ ∩ {w : Qm m |
        ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)} := by
      intro w hw
      refine ⟨hKc_sub hw.1, ?_⟩
      show ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)
      rw [fderivWithin_of_isOpen hUγ_open (hKc_sub hw.1)]
      exact hw.2
    have hws := (Work.Sard.prod.weakSard_all m) (Qm m) (Pm m)
      (by rw [finrank_euclideanSpace_fin])
      (by rw [Module.finrank_fin_fun, finrank_euclideanSpace_fin]) Uγ hUγ_open γ hγ_smooth
    calc interior (γ '' (Kc ∩ Scrit))
        ≤ interior (γ '' (Uγ ∩ {w : Qm m |
            ¬ Function.Surjective (fderivWithin ℝ γ Uγ w)})) :=
          interior_mono (Set.image_mono hsub)
      _ = ∅ := hws
  · intro p z hx hDp hΦz hbad
    have hxt : (p, z) ∈ e.target := hx.1
    have hwK : lam (p, z) ∈ interior Kc := hx.2
    have hsymm : e.symm (p, z) = ((0 : Tgt n), lam (p, z)) := by
      rw [he_symm (p, z) hxt, hΦz]
    have hsource_w : ((0 : Tgt n), lam (p, z)) ∈ e.source := by
      rw [← hsymm]; exact e.map_target hxt
    have hx_eq : e ((0 : Tgt n), lam (p, z)) = (p, z) := by
      rw [← hsymm]; exact e.right_inv hxt
    have hww : (e ((0 : Tgt n), lam (p, z))).1 = p := by rw [hx_eq]
    have hww2 : (e ((0 : Tgt n), lam (p, z))).2 = z := by rw [hx_eq]
    have hDp' : Function.Surjective
        (fderiv ℝ (fun p' : Pm m => Φ (p', (e ((0 : Tgt n), lam (p, z))).2))
          (e ((0 : Tgt n), lam (p, z))).1) := by
      rw [hww, hww2]; exact hDp
    have hiff := chart_surjective_iff Φ hΦ e he_smooth he_Phi he_deriv (lam (p, z)) hsource_w hDp'
    have hbadγ : ¬ Function.Surjective (fderiv ℝ γ (lam (p, z))) := by
      intro hsurj
      have hthis := hiff.mp hsurj
      rw [hww, hww2] at hthis
      exact hbad hthis
    have hp : p = γ (lam (p, z)) := by
      show p = (e ((0 : Tgt n), lam (p, z))).1
      rw [hww]
    rw [hp]
    exact Set.mem_image_of_mem γ ⟨interior_subset hwK, hbadγ⟩

/-- `Work.MetricSquare.bad_interior_empty`, restated for `badSetGen` in arbitrary dimension. -/
lemma interior_badSetGen_eq_empty (m n : ℕ) (Ψ : Pm m × Amb n → Tgt n)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hsurj : ∀ (p : Pm m) (z : Amb n), z ∈ Submission.Drive.unitBox n → Ψ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Ψ (p', z)) p)) :
    interior (badSetGen m n Ψ) = ∅ := by
  classical
  by_contra hne
  set Bad : Set (Pm m) := {p | ∃ z ∈ Submission.Drive.unitBox n, Ψ (p, z) = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (p, z')) z)} with hBad
  obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hp₀)
  have hBsub : Metric.closedBall p₀ (ε / 2) ⊆ Bad := by
    intro p hp
    have hp' : p ∈ Metric.closedBall p₀ (ε / 2) := hp
    refine interior_subset (hεsub ?_)
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hp'
    linarith [hε]
  have hBint : (interior (Metric.closedBall p₀ (ε / 2))).Nonempty :=
    ⟨p₀, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by linarith [hε]))⟩
  -- the compact set of bad points
  set K : Set (Pm m × Amb n) := {x | x.1 ∈ Metric.closedBall p₀ (ε / 2) ∧
      x.2 ∈ Submission.Drive.unitBox n ∧ Ψ x = 0 ∧
      ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (x.1, z')) x.2)} with hK
  have hcont : Continuous (fun x : Pm m × Amb n =>
      (fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))) := by
    have h1 : Continuous (fun T : (Pm m × Amb n) →L[ℝ] Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Amb n) (Pm m × Amb n) (Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Pm m × Amb n) →L[ℝ] Tgt n => ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  have hK_eq : K = ((Metric.closedBall p₀ (ε / 2) ×ˢ Submission.Drive.unitBox n)
      ∩ {x : Pm m × Amb n | Ψ x = 0})
      ∩ {x : Pm m × Amb n | ¬ Function.Surjective
          ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))} := by
    rw [hK]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
    rw [← Work.MetricSquare.fd_comp_inr Ψ hΨ x.1 x.2]
    tauto
  have hKcompact : IsCompact K := by
    rw [hK_eq]
    have hc1 : IsClosed ((Metric.closedBall p₀ (ε / 2) ×ˢ Submission.Drive.unitBox n)
        ∩ {x : Pm m × Amb n | Ψ x = 0}) :=
      ((isCompact_closedBall p₀ (ε / 2)).isClosed.prod (isClosed_unitBox n)).inter
        (isClosed_eq hΨ.continuous continuous_const)
    have hc2 : IsClosed {x : Pm m × Amb n | ¬ Function.Surjective
        ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall p₀ (ε / 2)).prod (isCompact_unitBox n))
      (hc1.inter hc2) (fun x hx => hx.1.1)
  -- the local neighbourhoods
  have hchoice : ∀ x : K, ∃ U : Set (Pm m × Amb n), IsOpen U ∧ (x.1 : Pm m × Amb n) ∈ U ∧
      ∃ A : Set (Pm m), IsCompact A ∧ interior A = ∅ ∧
        (∀ (p : Pm m) (z : Amb n), (p, z) ∈ U →
          Function.Surjective (fderiv ℝ (fun p' : Pm m => Ψ (p', z)) p) →
          Ψ (p, z) = 0 →
          ¬ Function.Surjective (fderiv ℝ (fun z' : Amb n => Ψ (p, z')) z) → p ∈ A) :=
    fun x => exists_local_good_gen m n Ψ hΨ x.1.1 x.1.2 x.2.2.2.1
      (hsurj x.1.1 x.1.2 x.2.2.1 x.2.2.2.1)
  choose U hU using hchoice
  obtain ⟨s, hs⟩ := hKcompact.elim_finite_subcover U (fun x => (hU x).1)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩)
  have hBsub2 : Metric.closedBall p₀ (ε / 2) ⊆ ⋃ y : s, (hU (y : K)).2.2.choose := by
    intro p hp
    have hpBad : p ∈ Bad := hBsub hp
    obtain ⟨z, hzbox, hΨz, hbad⟩ := hpBad
    have hxK : (p, z) ∈ K := ⟨hp, hzbox, hΨz, hbad⟩
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxK)
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hU (y : K)).2.2.choose_spec.2.2 p z hxy
      (hsurj p z hzbox hΨz) hΨz hbad⟩
  -- Baire
  have hclosedA : ∀ y : s, IsClosed ((hU (y : K)).2.2.choose) :=
    fun y => (hU (y : K)).2.2.choose_spec.1.isClosed
  have hemptyA : ∀ y : s, interior ((hU (y : K)).2.2.choose) = ∅ :=
    fun y => (hU (y : K)).2.2.choose_spec.2.1
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hclosedA hemptyA
  have hsubInt : interior (Metric.closedBall p₀ (ε / 2)) ⊆
      interior (⋃ y : s, (hU (y : K)).2.2.choose) := interior_mono hBsub2
  rw [hBaire] at hsubInt
  exact hBint.ne_empty (Set.Subset.antisymm hsubInt (Set.empty_subset _))

/-- **The bad set is a countable union of compact sets.** -/
lemma isCompact_badSetGen_inter_closedBall (m n : ℕ) (Ψ : Pm m × Amb n → Tgt n)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (k : ℕ) :
    IsCompact (badSetGen m n Ψ ∩ Metric.closedBall (0 : Pm m) k) := by
  have hcont : Continuous (fun x : Pm m × Amb n =>
      (fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))) := by
    have h1 : Continuous (fun T : (Pm m × Amb n) →L[ℝ] Tgt n =>
        T.comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))) := by
      have h := (ContinuousLinearMap.compL ℝ (Amb n) (Pm m × Amb n) (Tgt n)).continuous.clm_apply
        (continuous_const : Continuous
          (fun _ : (Pm m × Amb n) →L[ℝ] Tgt n => ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))
      simpa using h
    exact h1.comp (hΨ.continuous_fderiv (by simp))
  set K : Set (Pm m × Amb n) := ((Metric.closedBall (0 : Pm m) k ×ˢ Submission.Drive.unitBox n)
      ∩ {x : Pm m × Amb n | Ψ x = 0})
      ∩ {x : Pm m × Amb n | ¬ Function.Surjective
          ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))} with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    have hc1 : IsClosed ((Metric.closedBall (0 : Pm m) k ×ˢ Submission.Drive.unitBox n)
        ∩ {x : Pm m × Amb n | Ψ x = 0}) :=
      ((isCompact_closedBall (0 : Pm m) k).isClosed.prod (isClosed_unitBox n)).inter
        (isClosed_eq hΨ.continuous continuous_const)
    have hc2 : IsClosed {x : Pm m × Amb n | ¬ Function.Surjective
        ((fderiv ℝ Ψ x).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))} :=
      Work.Sard.prod.isClosed_setOf_not_surjective_clm'.preimage hcont
    exact IsCompact.of_isClosed_subset
      ((isCompact_closedBall (0 : Pm m) k).prod (isCompact_unitBox n))
      (hc1.inter hc2) (fun x hx => hx.1.1)
  have himg : Prod.fst '' K = badSetGen m n Ψ ∩ Metric.closedBall (0 : Pm m) k := by
    rw [hK]
    ext p
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, badSetGen]
    constructor
    · rintro ⟨x, ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩, rfl⟩
      exact ⟨⟨x.2, hx2, hx3, fun hc => hx4 (by rwa [← Work.MetricSquare.fd_comp_inr Ψ hΨ x.1 x.2] at hc)⟩, hx1⟩
    · rintro ⟨⟨z, hz, hz0, hzbad⟩, hp⟩
      exact ⟨(p, z), ⟨⟨⟨hp, hz⟩, hz0⟩, by rwa [Work.MetricSquare.fd_comp_inr Ψ hΨ p z]⟩, rfl⟩
  rw [← himg]
  exact hKcompact.image continuous_fst

/-- The bad set is the union over `k` of its intersections with the closed balls. -/
lemma badSetGen_eq_iUnion_closedBall (m n : ℕ) (Ψ : Pm m × Amb n → Tgt n) :
    badSetGen m n Ψ = ⋃ k : ℕ, badSetGen m n Ψ ∩ Metric.closedBall (0 : Pm m) k := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := exists_nat_ge ‖p‖
    exact Set.mem_iUnion.mpr ⟨k, hp, Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hk)⟩
  · intro hp
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
    exact hk.1

/-! ## The linear projection onto a coordinate hyperplane and the face maps -/

/-- The orthogonal projection of `ℝ^{n+1}` onto the coordinate hyperplane `{v | v i = 0}`. -/
def faceLin {n : ℕ} (i : Fin (n + 1)) : Amb n →L[ℝ] Amb n :=
  ContinuousLinearMap.id ℝ (Amb n) -
    (PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) i).smulRight (EuclideanSpace.single i 1)

/-- `z ↦ z` with the `i`-th coordinate replaced by `c`. -/
def faceMap {n : ℕ} (i : Fin (n + 1)) (c : ℝ) : Amb n → Amb n :=
  fun z => faceLin i z + c • EuclideanSpace.single i 1

lemma faceLin_coord {n : ℕ} (i : Fin (n + 1)) (z : Amb n) (j : Fin (n + 1)) :
    (faceLin i z) j = if j = i then 0 else z j := by
  simp only [faceLin]
  split_ifs with h <;> simp [h]

lemma faceLin_self {n : ℕ} (i : Fin (n + 1)) (z : Amb n) : (faceLin i z) i = 0 := by
  rw [faceLin_coord, if_pos rfl]

lemma faceLin_eq_self_of {n : ℕ} {i : Fin (n + 1)} {z : Amb n} (hz : z i = 0) :
    faceLin i z = z := by
  apply WithLp.ofLp_injective 2
  funext j
  rw [faceLin_coord]
  split_ifs with h
  · rw [h]; exact hz.symm
  · rfl

lemma faceMap_coord {n : ℕ} (i : Fin (n + 1)) (c : ℝ) (z : Amb n) (j : Fin (n + 1)) :
    (faceMap i c z) j = if j = i then c else z j := by
  simp only [faceMap, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, faceLin_coord]
  split_ifs with h <;> ring

lemma faceMap_self {n : ℕ} (i : Fin (n + 1)) (z : Amb n) : faceMap i (z i) z = z := by
  apply WithLp.ofLp_injective 2
  funext j
  rw [faceMap_coord]
  split_ifs with h
  · rw [h]
  · rfl

lemma faceMap_mem_unitBox {n : ℕ} {i : Fin (n + 1)} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {z : Amb n} (hz : z ∈ Submission.Drive.unitBox n) :
    faceMap i c z ∈ Submission.Drive.unitBox n := by
  intro j
  rw [faceMap_coord]
  split_ifs with h
  · exact ⟨hc0, hc1⟩
  · exact hz j

lemma hasFDerivAt_faceMap {n : ℕ} (i : Fin (n + 1)) (c : ℝ) (z : Amb n) :
    HasFDerivAt (faceMap i c) (faceLin i) z := by
  have h : HasFDerivAt (⇑(faceLin i)) (faceLin i) z := ContinuousLinearMap.hasFDerivAt (faceLin i)
  exact h.add_const (c • EuclideanSpace.single i 1)

/-- Surjectivity of `D ∘ faceLin i` is surjectivity of the restriction of `D` to the coordinate
hyperplane `{v | v i = 0}`. -/
lemma surjective_comp_faceLin_iff {n : ℕ} (D : Amb n →L[ℝ] Tgt n) (i : Fin (n + 1)) :
    Function.Surjective (D.comp (faceLin i)) ↔
      Function.Surjective (fun v : {v : Amb n // v i = 0} => D v.1) := by
  constructor
  · intro h w
    obtain ⟨u, hu⟩ := h w
    exact ⟨⟨faceLin i u, faceLin_self i u⟩, hu⟩
  · intro h w
    obtain ⟨v, hv⟩ := h w
    exact ⟨v.1, by rw [ContinuousLinearMap.comp_apply, faceLin_eq_self_of v.2]; exact hv⟩

/-- `Φ` with the `i`-th coordinate of the `z`-variable replaced by `c`. -/
def PhiIc {m n : ℕ} (Φ : Pm m × Amb n → Tgt n) (i : Fin (n + 1)) (c : ℝ) :
    Pm m × Amb n → Tgt n :=
  fun x => Φ (x.1, faceMap i c x.2)

lemma PhiIc_contDiff {m n : ℕ} (Φ : Pm m × Amb n → Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (i : Fin (n + 1)) (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (PhiIc Φ i c) := by
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (faceMap i c) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(faceLin i)) :=
      ContinuousLinearMap.contDiff (faceLin i)
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : Amb n => c • EuclideanSpace.single i (1 : ℝ)) := contDiff_const
    exact h.add hc
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Pm m × Amb n => (x.1, faceMap i c x.2)) :=
    contDiff_fst.prodMk (h2.comp contDiff_snd)
  exact hΦ.comp hpair

/-- The `z`-derivative of `Φ_{i,c}`. -/
lemma fderiv_PhiIc {m n : ℕ} (Φ : Pm m × Amb n → Tgt n)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (i : Fin (n + 1)) (c : ℝ)
    (p : Pm m) (z : Amb n) :
    fderiv ℝ (fun z' : Amb n => PhiIc Φ i c (p, z')) z
      = (fderiv ℝ (fun w : Amb n => Φ (p, w)) (faceMap i c z)).comp (faceLin i) := by
  have hlin : HasFDerivAt (faceMap i c) (faceLin i) z := hasFDerivAt_faceMap i c z
  have hinner : HasFDerivAt (fun w : Amb n => (p, w))
      (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)) (faceMap i c z) := by
    simpa using (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))).const_add
      (p, 0)
  have hd : DifferentiableAt ℝ Φ (p, faceMap i c z) :=
    (hΦ.differentiable (by simp)).differentiableAt
  have hcomp1 : HasFDerivAt (fun w : Amb n => Φ (p, w))
      ((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n)))
      (faceMap i c z) :=
    hd.hasFDerivAt.comp (faceMap i c z) hinner
  have hcomp2 : HasFDerivAt (fun z' : Amb n => PhiIc Φ i c (p, z'))
      (((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))).comp
        (faceLin i)) z :=
    hcomp1.comp z hlin
  have hgoal : fderiv ℝ (fun z' : Amb n => PhiIc Φ i c (p, z')) z
      = ((fderiv ℝ Φ (p, faceMap i c z)).comp (ContinuousLinearMap.inr ℝ (Pm m) (Amb n))).comp
          (faceLin i) := hcomp2.fderiv
  rw [hgoal, Work.MetricSquare.fd_comp_inr Φ hΦ p (faceMap i c z)]

/-- The parameter-derivative of `Φ_{i,c}` is surjective at every zero in the box. -/
lemma PhiIc_hsurj {m n : ℕ} (Φ : Pm m × Amb n → Tgt n) (i : Fin (n + 1)) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsurj : ∀ (p : Pm m) (z : Amb n), z ∈ Submission.Drive.unitBox n → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p)) :
    ∀ (p : Pm m) (z : Amb n), z ∈ Submission.Drive.unitBox n → PhiIc Φ i c (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => PhiIc Φ i c (p', z)) p) := by
  intro p z hz h0
  have hz' : faceMap i c z ∈ Submission.Drive.unitBox n := faceMap_mem_unitBox hc0 hc1 hz
  have h0' : Φ (p, faceMap i c z) = 0 := h0
  have h := hsurj p (faceMap i c z) hz' h0'
  change Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', faceMap i c z)) p)
  exact h

/-! ## The two-valued index -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def cval (b : Bool) : ℝ := if b then 1 else 0

/-- The Bool with value `1` exactly when `x = 1`. -/
def boolOf (x : ℝ) : Bool := if x = 1 then true else false

lemma cval_boolOf {x : ℝ} (h : x = 0 ∨ x = 1) : cval (boolOf x) = x := by
  rcases h with rfl | rfl
  · simp [boolOf, cval]
  · simp [boolOf, cval]

lemma cval_nonneg (b : Bool) : 0 ≤ cval b := by
  cases b <;> simp [cval]

lemma cval_le_one (b : Bool) : cval b ≤ 1 := by
  cases b <;> simp [cval]

/-- The finite family of maps: `Φ` itself and the face maps `Φ_{i,c}`. -/
def mapFam {m n : ℕ} (Φ : Pm m × Amb n → Tgt n) :
    Option (Fin (n + 1) × Bool) → Pm m × Amb n → Tgt n :=
  fun o => Option.elim o Φ (fun jb => PhiIc Φ jb.1 (cval jb.2))

lemma mapFam_none {m n : ℕ} (Φ : Pm m × Amb n → Tgt n) : mapFam Φ none = Φ := rfl

lemma mapFam_some {m n : ℕ} (Φ : Pm m × Amb n → Tgt n) (i : Fin (n + 1)) (b : Bool) :
    mapFam Φ (some (i, b)) = PhiIc Φ i (cval b) := rfl

end Gen

open Gen

/-! ## The main theorem -/

theorem generic_regularization_gen (m n : ℕ) (ι : Type*) [Fintype ι] (ε : ℝ) (hε : 0 < ε)
    (Φ : ι → EuclideanSpace ℝ (Fin m) × Work.Drive.Amb n → Work.Drive.Tgt n)
    (hΦ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ i))
    (hsurj : ∀ (i : ι) (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb n),
      z ∈ Submission.Drive.unitBox n → Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ (i : ι) (z : Work.Drive.Amb n), z ∈ Submission.Drive.unitBox n → Φ i (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z)) ∧
      (∀ (i : ι) (j : Fin (n + 1)) (z : Work.Drive.Amb n), z ∈ Submission.Drive.unitBox n →
        Φ i (p, z) = 0 → (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb n // v j = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb n => Φ i (p, z')) z v.1)) := by
  classical
  have hmap_smooth : ∀ (i : ι) (o : Option (Fin (n + 1) × Bool)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mapFam (Φ i) o) := by
    intro i o
    cases o with
    | none => exact hΦ i
    | some jb =>
      obtain ⟨j, b⟩ := jb
      exact PhiIc_contDiff (Φ i) (hΦ i) j (cval b)
  have hmap_hsurj : ∀ (i : ι) (o : Option (Fin (n + 1) × Bool)),
      ∀ (p : Pm m) (z : Amb n), z ∈ Submission.Drive.unitBox n → mapFam (Φ i) o (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun p' : Pm m => mapFam (Φ i) o (p', z)) p) := by
    intro i o
    cases o with
    | none => exact hsurj i
    | some jb =>
      obtain ⟨j, b⟩ := jb
      exact PhiIc_hsurj (Φ i) j (cval b) (cval_nonneg b) (cval_le_one b) (hsurj i)
  have hSclosed : ∀ k : ι × Option (Fin (n + 1) × Bool) × ℕ,
      IsClosed (badSetGen m n (mapFam (Φ k.1) k.2.1) ∩ Metric.closedBall (0 : Pm m) k.2.2) :=
    fun k => (isCompact_badSetGen_inter_closedBall m n (mapFam (Φ k.1) k.2.1)
      (hmap_smooth k.1 k.2.1) k.2.2).isClosed
  have hSempty : ∀ k : ι × Option (Fin (n + 1) × Bool) × ℕ,
      interior (badSetGen m n (mapFam (Φ k.1) k.2.1) ∩ Metric.closedBall (0 : Pm m) k.2.2) = ∅ :=
    fun k => subset_eq_empty (interior_mono Set.inter_subset_left)
      (interior_badSetGen_eq_empty m n (mapFam (Φ k.1) k.2.1) (hmap_smooth k.1 k.2.1)
        (hmap_hsurj k.1 k.2.1))
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hSclosed hSempty
  have hunion : (⋃ k : ι × Option (Fin (n + 1) × Bool) × ℕ,
        badSetGen m n (mapFam (Φ k.1) k.2.1) ∩ Metric.closedBall (0 : Pm m) k.2.2)
      = ⋃ (i : ι) (o : Option (Fin (n + 1) × Bool)), badSetGen m n (mapFam (Φ i) o) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, badSetGen]
    constructor
    · rintro ⟨k, ⟨z, hz, hz0, hz1⟩, -⟩
      exact ⟨k.1, k.2.1, z, hz, hz0, hz1⟩
    · rintro ⟨i, o, z, hz, hz0, hz1⟩
      obtain ⟨N, hN⟩ := exists_nat_ge ‖p‖
      exact ⟨(i, o, N), ⟨z, hz, hz0, hz1⟩,
        Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hN)⟩
  have hBad : interior (⋃ (i : ι) (o : Option (Fin (n + 1) × Bool)),
      badSetGen m n (mapFam (Φ i) o)) = ∅ := by
    rw [← hunion]; exact hBaire
  obtain ⟨p, hpball, hp⟩ :=
    Work.MetricSquare.exists_norm_lt_notMem_of_interior_eq_empty _ hBad hε
  refine ⟨p, hpball, ?_, ?_⟩
  · intro i z hz h0
    by_contra hbad
    exact hp (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨none, ⟨z, hz, h0, hbad⟩⟩⟩)
  · intro i j z hz h0 hzi
    by_contra hbad
    have hpface : p ∈ badSetGen m n (PhiIc (Φ i) j (z j)) := by
      refine ⟨z, hz, ?_, ?_⟩
      · show PhiIc (Φ i) j (z j) (p, z) = 0
        rw [PhiIc, faceMap_self j z]
        exact h0
      · intro hD
        have hD' : Function.Surjective
            ((fderiv ℝ (fun w : Amb n => Φ i (p, w)) z).comp (faceLin j)) := by
          have h1 := fderiv_PhiIc (Φ i) (hΦ i) j (z j) p z
          rw [faceMap_self j z] at h1
          rw [← h1]
          exact hD
        exact hbad ((surjective_comp_faceLin_iff _ j).mp hD')
    refine hp (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨some (j, boolOf (z j)), ?_⟩⟩)
    have hval : cval (boolOf (z j)) = z j := cval_boolOf hzi
    show p ∈ badSetGen m n (PhiIc (Φ i) j (cval (boolOf (z j))))
    rw [hval]
    exact hpface

end

end Work.Drive
