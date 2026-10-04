import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.EXT.ricAt_eq_sum_frame
import Submission.Work.EXT.exists_isONFrame_head
import Submission.Work.EXT.abs_bilin_le_of_abs_self_le
import Submission.Work.EXT.rmP_pair_symm2
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci bound from a bound on the curvature components

`CurvBound g C` bounds every component `rmFrame g x e i j k l = g(R(eᵢ,eⱼ)e_l, e_k)` of the
curvature of `g` in every `g`-orthonormal frame.  This file shows that this bounds the pointwise
Ricci tensor `ricAt (lcOf g) x u v` by `(finrank ℝ E) * C * ‖u‖ * ‖v‖`, which is what the
continuation/Shi step of the Brendle–Schoen argument needs (it feeds the hypothesis
`|Ric(u,u)| ≤ λ g(u,u)` of `Work.Diff.EXT.metric_equiv_of_ric_bound` with `λ = (finrank ℝ E) * C`).

The mathematical content is

* the trace identity `ricAt (lcOf g) x u v = ∑ j, g (R(e_j,u)v) e_j` in an orthonormal frame
  (`Work.EXT.ricAt_eq_sum_frame`, delegated);
* the diagonal estimate `|ricAt (lcOf g) x w w| ≤ (finrank ℝ E) * C * g(w,w)`, obtained from the
  trace identity in an orthonormal frame whose first vector is `w` (so every summand is a single
  curvature component, bounded by `CurvBound`), plus the bilinearity of `ricAt` in `w` to reduce
  the general case to the unit case;
* symmetry of `Ric` (`Work.EXT.rmP_pair_symm`: `g(R(a,b)d,c) = g(R(c,d)b,a)` for the
  Levi–Civita connection, from Bianchi + the two skew-symmetries) and the polarization
  (numerical-radius) inequality `Work.EXT.abs_bilin_le_of_abs_self_le`.

The trace identity, the bilinearity and the pair symmetry all need the Levi-Civita connection of
`g` to be a *smooth* covariant derivative; that is `Work.EXT.contMDiffCovariantDerivative_lcOf`,
together with Mathlib's torsion-freeness and metric-compatibility of `leviCivitaConnection`, which
are combined below into `LCSmooth I M`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Bilinearity of the pointwise Ricci tensor -/

section Bilin

/-- `ricAt` is additive in its middle slot.  Both sides are rewritten with the trace identity and
the multilinearity of `rmVec` in that slot. -/
theorem ricAt_add_middle_L
    (g : SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞))
    (x : M) (u₁ u₂ v : TangentSpace I x) :
    ricAt (lcOf g) x (u₁ + u₂) v = ricAt (lcOf g) x u₁ v + ricAt (lcOf g) x u₂ v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he (u₁ + u₂) v,
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u₁ v,
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u₂ v,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.rmVec_add_middle (lcOf g) hcov x _ u₁ u₂ v]
  simp only [map_add, add_apply]

/-- `ricAt` is homogeneous in its middle slot. -/
theorem ricAt_smul_middle_L
    (g : SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞))
    (x : M) (c : ℝ) (u v : TangentSpace I x) :
    ricAt (lcOf g) x (c • u) v = c * ricAt (lcOf g) x u v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he (c • u) v,
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.rmVec_smul_middle (lcOf g) hcov x c _ u v]
  simp only [map_smul, smul_apply, smul_eq_mul]

/-- `ricAt` is additive in its last slot. -/
theorem ricAt_add_last_L
    (g : SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞))
    (x : M) (u v₁ v₂ : TangentSpace I x) :
    ricAt (lcOf g) x u (v₁ + v₂) = ricAt (lcOf g) x u v₁ + ricAt (lcOf g) x u v₂ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u (v₁ + v₂),
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u v₁,
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u v₂,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.rmVec_add_right (lcOf g) hcov x _ u v₁ v₂]
  simp only [map_add, add_apply]

/-- `ricAt` is homogeneous in its last slot. -/
theorem ricAt_smul_last_L
    (g : SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞))
    (x : M) (c : ℝ) (u v : TangentSpace I x) :
    ricAt (lcOf g) x u (c • v) = c * ricAt (lcOf g) x u v := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u (c • v),
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.rmVec_smul_right (lcOf g) hcov x c _ u v]
  simp only [map_smul, smul_apply, smul_eq_mul]

end Bilin

/-! ## Symmetry of the pointwise Ricci tensor -/

/-- `Ric` is symmetric: in an orthonormal frame it is the trace `∑ j g(R(e_j,u)v,e_j)`, which the
pair-exchange symmetry `rmP g x a b c d = rmP g x c d a b` turns into `∑ j g(R(e_j,v)u,e_j)`. -/
theorem ricAt_symm_L (hLC : LCSmooth I M) (g : SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (lcOf g) (⊤ : ℕ∞))
    (x : M) (u v : TangentSpace I x) : ricAt (lcOf g) x u v = ricAt (lcOf g) x v u := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  have he : IsONFrame g x (onFrame g x) := Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  rw [Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he u v,
    Work.EXT.ricAt_eq_sum_frame g hcov x (onFrame g x) he v u]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := Work.EXT.rmP_pair_symm2 hLC g x (onFrame g x j) u (onFrame g x j) v
  simpa only [rmP] using h

/-! ## Metric compatibility of the Levi-Civita connection (challenge's form)

Mathlib proves metric compatibility of `leviCivitaConnection` in the form `derivMetricTensor = 0`;
its consequence `IsMetricCompatible.mvfderiv_inner_eq` is *literally* the frozen predicate
`Submission.IsMetricCompatible` of the challenge, so the two are identified here. -/

/-- The Levi-Civita connection of a smooth metric is metric compatible in the frozen sense. -/
theorem isMetricCompatible_lcOf_L (g : SMet I M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
     LeanEval.Geometry.SphereTheorem.IsMetricCompatible (lcOf g)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : IsManifold I 2 M := inferInstance
  intro Y Z hY hZ x v
  have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  have h := (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    |>.mvfderiv_inner_eq (σ := Y) (τ := Z) (Submission.Diff.smoothExt x v) hY' hZ'
  simpa only [Submission.Diff.lcOf, Work.Diff.GE.smoothExt_apply] using h

/-! ## The diagonal (quadratic) bound -/

/-- `|Ric(w,w)| ≤ (finrank ℝ E) * C * g(w,w)`: apply the trace identity in an orthonormal frame
whose first vector is `w/‖w‖` (so every summand is a single component of `CurvBound`) and use
bilinearity of `Ric` to reduce to `g(w,w) = 1`. -/
theorem ricAt_quad_bound_L (hLC : LCSmooth I M) (g : SMet I M) {C : ℝ}
    (hC : 0 ≤ C) (hb : CurvBound g C) (x : M) (w : TangentSpace I x) :
    |ricAt (lcOf g) x w w| ≤ ((Module.finrank ℝ E : ℝ) * C) * g.inner x w w := by
  obtain ⟨hcovne, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcovne
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  by_cases hn : 0 < Module.finrank ℝ E
  · have hunit : ∀ w : TangentSpace I x, g.inner x w w = 1 →
        |ricAt (lcOf g) x w w| ≤ (Module.finrank ℝ E : ℝ) * C := by
      intro w hw
      obtain ⟨e, he, he0⟩ := Work.EXT.exists_isONFrame_head g x hn w hw
      rw [Work.EXT.ricAt_eq_sum_frame g hcov x e he w w]
      have hterm : ∀ j : Fin (Module.finrank ℝ E),
          |g.inner x (rmVec (lcOf g) x (e j) w w) (e j)| ≤ C := by
        intro j
        have h := hb x e he j ⟨0, hn⟩ j ⟨0, hn⟩
        have heq : rmFrame g x e j ⟨0, hn⟩ j ⟨0, hn⟩
            = g.inner x (rmVec (lcOf g) x (e j) w w) (e j) := by
          simp only [rmFrame, he0]
        rwa [heq] at h
      calc |∑ j, g.inner x (rmVec (lcOf g) x (e j) w w) (e j)|
          ≤ ∑ j, |g.inner x (rmVec (lcOf g) x (e j) w w) (e j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (Module.finrank ℝ E), C := Finset.sum_le_sum (fun j _ => hterm j)
        _ = (Module.finrank ℝ E : ℝ) * C := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases eq_or_ne w 0 with hw | hw
    · subst hw
      have h00 : ricAt (lcOf g) x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        have h := ricAt_smul_middle_L g hcov x 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
        simpa using h
      rw [h00, abs_zero]
      simp
    · have hle : 0 ≤ g.inner x w w := by
        have h2 : g.inner x w w = ‖w‖ ^ 2 := by
          rw [show g.inner x w w = Inner.inner ℝ w w from rfl, real_inner_self_eq_norm_sq]
        rw [h2]; positivity
      have hne : g.inner x w w ≠ 0 := by
        intro hzero
        exact hw (inner_self_eq_zero.mp hzero)
      have hpos : 0 < g.inner x w w := lt_of_le_of_ne hle (Ne.symm hne)
      set a : ℝ := Real.sqrt (g.inner x w w) with ha
      have hapos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr hpos
      have hsq : a ^ 2 = g.inner x w w := by rw [ha]; exact Real.sq_sqrt (le_of_lt hpos)
      set w' : TangentSpace I x := a⁻¹ • w with hw'_def
      have hunit_w : g.inner x w' w' = 1 := by
        rw [hw'_def]
        have hrew : g.inner x (a⁻¹ • w) (a⁻¹ • w) = a⁻¹ * (a⁻¹ * g.inner x w w) := by
          simp only [map_smul, smul_apply, smul_eq_mul]
        have hsq2 : a⁻¹ * (a⁻¹ * a ^ 2) = 1 := by field_simp
        rw [hrew, ← hsq]
        exact hsq2
      have h1 := hunit w' hunit_w
      have hw_eq : w = a • w' := by
        rw [hw'_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hapos), one_smul]
      have hscale : ricAt (lcOf g) x w w = a * a * ricAt (lcOf g) x w' w' := by
        rw [hw_eq, ricAt_smul_middle_L g hcov x a _ _, ricAt_smul_last_L g hcov x a _ _]
        ring
      have hww : g.inner x w w = a * a := by rw [← hsq]; ring
      calc |ricAt (lcOf g) x w w|
          = a * a * |ricAt (lcOf g) x w' w'| := by
            rw [hscale, abs_mul, abs_mul, abs_of_pos hapos]
        _ ≤ a * a * ((Module.finrank ℝ E : ℝ) * C) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((Module.finrank ℝ E : ℝ) * C) * g.inner x w w := by
            rw [hww]; ring
  · have hfin : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hsub : Subsingleton (TangentSpace I x) := by
      refine ⟨fun p q => ?_⟩
      have h := (Module.finrank_eq_zero_iff (R := ℝ) (M := E)).mp hfin (p - q)
      obtain ⟨c, hc, hcx⟩ := h
      have hp : p - q = 0 := by
        rcases smul_eq_zero.mp hcx with h0 | h0
        · exact absurd h0 hc
        · exact h0
      exact sub_eq_zero.mp hp
    have hw0 : w = 0 := Subsingleton.elim w 0
    subst hw0
    have h00 : ricAt (lcOf g) x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
      have h := ricAt_smul_middle_L g hcov x 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
      simpa using h
    rw [h00, abs_zero]
    simp [hfin]

/-! ## The bound on `Ric(u,v)` -/

/-- The requested inequality, with the smoothness of the Levi-Civita connection (the contract
`LCSmooth`, equivalently `ContMDiffCovariantDerivative (lcOf g) ∞`) available as a hypothesis.
The diagonal estimate plus symmetry of `Ric` give, by polarization,
`|Ric(u,v)| ≤ (finrank ℝ E) * C * ‖u‖ * ‖v‖`. -/
theorem ric_bound_of_curvBound_of_LCSmooth
    (hLC : LCSmooth I M) {g : SMet I M} {C : ℝ} (hC : 0 ≤ C) (hb : CurvBound g C)
    (x : M) (u v : TangentSpace I x) :
    |ricAt (lcOf g) x u v| ≤
      (Module.finrank ℝ E : ℝ) * C * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  obtain ⟨hcovne, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcovne
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  let B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun p q => ricAt (lcOf g) x p q)
      (fun p₁ p₂ q => ricAt_add_middle_L g hcov x p₁ p₂ q)
      (fun c p q => ricAt_smul_middle_L g hcov x c p q)
      (fun p q₁ q₂ => ricAt_add_last_L g hcov x p q₁ q₂)
      (fun c p q => ricAt_smul_last_L g hcov x c p q)
  have hBsymm : ∀ p q : TangentSpace I x, B p q = B q p := by
    intro p q
    rw [LinearMap.mk₂_apply, LinearMap.mk₂_apply]
    exact ricAt_symm_L hLC g hcov x p q
  have hquad : ∀ w : TangentSpace I x,
      |B w w| ≤ ((Module.finrank ℝ E : ℝ) * C) * ‖w‖ ^ 2 := by
    intro w
    rw [LinearMap.mk₂_apply, ← real_inner_self_eq_norm_sq w]
    exact ricAt_quad_bound_L hLC g hC hb x w
  have hK : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC
  have hmain := Work.EXT.abs_bilin_le_of_abs_self_le B hBsymm hK hquad u v
  rw [LinearMap.mk₂_apply] at hmain
  have hnorm : ∀ p : TangentSpace I x, ‖p‖ = Real.sqrt (g.inner x p p) := by
    intro p
    have h1 : ‖p‖ = Real.sqrt (‖p‖ ^ 2) := (Real.sqrt_sq (norm_nonneg p)).symm
    have h2 : (‖p‖ ^ 2 : ℝ) = g.inner x p p := by
      rw [← real_inner_self_eq_norm_sq p]
      exact Work.Diff.GE.inner_eq_metric (I := I) (M := M) g x p p
    rw [h1, h2]
  rw [hnorm u, hnorm v] at hmain
  calc |ricAt (lcOf g) x u v|
      ≤ ((Module.finrank ℝ E : ℝ) * C) * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := hmain
    _ = (Module.finrank ℝ E : ℝ) * C * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
        ring

/-! ## The requested lemma -/

theorem ric_bound_of_curvBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    {g : Submission.Diff.SMet I M} {C : ℝ} (hC : 0 ≤ C) (hb : Submission.Diff.CurvBound g C)
    (x : M) (u v : TangentSpace I x) :
    abs (Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v) ≤
      (Module.finrank ℝ E : ℝ) * C * Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) :=
  ric_bound_of_curvBound_of_LCSmooth (Work.EXT.lcSmooth_noBoundary (I := I) (M := M)) hC hb x u v

end Work.Diff.EXT
