import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- At a point of a set on which `f` is analytic, the divisor of `f` equals the analytic
vanishing order (as an integer). -/
private lemma divisor_eq_order_aux {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f z) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f z = n := by rw [analyticOrderNatAt, ← hn]; simp
    rw [h2, ← hn]; simp

/-- The primitive character inducing a non-trivial character of level `q` is non-trivial. -/
private lemma primitiveCharacter_ne_one_aux {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h1
  have h := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h
  exact hχ h.symm

/-- **The box contains only finitely many non-trivial zeros of `χ`.**

For a non-principal Dirichlet character `χ` mod `q` and `R > 0`, the set of points `u` of
Heath-Brown's box `InBox q R` at which `χ` has a non-trivial zero (i.e. `zeroMult χ u ≠ 0`) is
finite.  Indeed `zeroMult χ u ≠ 0` forces `Λ(χ*, u) = 0` for the primitive character `χ*`
inducing `χ`, and the zeros of `Λ(χ*, ·)` lie in the open critical strip `0 < Re < 1`
(`zerosInStrip`); combined with the box inequalities `(1 - Re u) log q ≤ R` and
`|Im u| log q ≤ R` (and `log q > 0`, which holds since `χ ≠ 1` forces `q ≥ 2`) this confines
the set to a compact disk.  An analytic function has finite divisor support on a compact set. -/
lemma finite_inBox_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor] {R : ℝ} (hR : 0 < R) :
    ({u : ℂ | Work.LinnikContract.InBox q R u ∧ Work.LinnikContract.zeroMult χ u ≠ 0} : Set ℂ).Finite := by
  -- `q ≥ 2`, hence `log q > 0`
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqne : q ≠ 1 := by
    rintro rfl
    exact hχ (Subsingleton.elim χ (1 : DirichletCharacter ℂ 1))
  have hq2 : 2 ≤ q := by omega
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1R
  -- the primitive character inducing `χ` is non-trivial
  have hψne : χ.primitiveCharacter ≠ (1 : DirichletCharacter ℂ χ.conductor) :=
    primitiveCharacter_ne_one_aux hχ
  have hψprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  -- its completed L-function, analytic everywhere
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ.primitiveCharacter
  let ρ : ℝ := 1 + 2 * (R / Real.log (q : ℝ))
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall (0 : ℂ) ρ) := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hψne).analyticAt z
  -- an analytic function has finite divisor support on a compact set
  have hfin : (Function.support
      (fun u : ℂ => MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) ρ) u)).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset (f := Λ)
        (U := Metric.closedBall (0 : ℂ) ρ) (V := Metric.closedBall (0 : ℂ) ρ)
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) ρ) (le_refl _))
  refine hfin.subset ?_
  intro u hu
  rw [Function.mem_support]
  obtain ⟨hbox, hzm⟩ := hu
  -- `u` is a zero of `Λ`
  have hzm' : analyticOrderNatAt Λ u ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hzm
  have hzero : Λ u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm'
  -- zeros of `Λ` lie in the critical strip
  have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip
    χ.primitiveCharacter hψne hψprim u hzero
  -- box inequalities
  have him : |u.im| ≤ R / Real.log (q : ℝ) := (le_div_iff₀ hlogq).mpr hbox.2
  have hrelow : 1 - R / Real.log (q : ℝ) ≤ u.re := by
    have h := (le_div_iff₀ hlogq).mpr hbox.1
    linarith
  have hRlog : 0 ≤ R / Real.log (q : ℝ) := le_of_lt (div_pos hR hlogq)
  -- `u` lies in the compact disk of radius `ρ`
  have huK : u ∈ Metric.closedBall (0 : ℂ) ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    calc ‖u‖ ≤ |u.re| + |u.im| := norm_le_abs_re_add_abs_im u
      _ ≤ (1 + R / Real.log (q : ℝ)) + R / Real.log (q : ℝ) := by
          refine add_le_add ?_ him
          rw [abs_le]
          exact ⟨by linarith, by linarith⟩
      _ = ρ := by
          rw [show ρ = 1 + 2 * (R / Real.log (q : ℝ)) from rfl]; ring
  -- where the vanishing order is positive, the divisor does not vanish
  rw [divisor_eq_order_aux hAn huK]
  intro h
  exact hzm' (by exact_mod_cast h)

end Work.LinnikAreas
