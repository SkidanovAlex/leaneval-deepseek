import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.contDiff_integral_deriv
import Submission.Work.Diff.Dim2.deriv_eq_smul_rot90
import Submission.Work.Diff.Dim2.exists_cos_sin
import Submission.Work.Diff.Dim2.eq_of_deriv_eq_smul_rot90
import Submission.Work.Diff.Dim2.sign_of_continuous_ne_zero
import Submission.Work.Diff.Dim2.period_shift_exists_int

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

noncomputable section

/-- **The angular velocity of a plane curve** `θ ↦ ⟪J (κ θ), deriv κ θ⟫`, where `J = rot90` is
the quarter turn. -/
def angVel (κ : ℝ → EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ :=
  inner ℝ (rot90 (κ θ)) (deriv κ θ)

/-- The angular velocity in coordinates. -/
lemma angVel_eq_coord (κ : ℝ → EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    angVel κ θ = -(κ θ 1) * deriv κ θ 0 + (κ θ 0) * deriv κ θ 1 := by
  rw [angVel, inner_fin_two, rot90_apply_zero, rot90_apply_one]

lemma angVel_contDiff {κ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (angVel κ) := by
  have h : angVel κ = fun θ => -(κ θ 1) * deriv κ θ 0 + (κ θ 0) * deriv κ θ 1 :=
    funext fun θ => angVel_eq_coord κ θ
  rw [h]
  fun_prop

/-- **The unit circle parametrisation has velocity `J` times its position.** -/
lemma circPt_hasDerivAt (t : ℝ) : HasDerivAt circPt (rot90 (circPt t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      (![-Real.sin t, Real.cos t]) t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
  have h2 : HasDerivAt
      (fun s : ℝ =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![-Real.sin t, Real.cos t] : Fin 2 → ℝ)) t :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).hasFDerivAt.comp_hasDerivAt t h1
  have hval : (EuclideanSpace.equiv (Fin 2) ℝ).symm (![-Real.sin t, Real.cos t] : Fin 2 → ℝ)
      = rot90 (circPt t) := by
    rw [rot90]; congr 1
  rw [hval] at h2
  exact h2

/-- **The core of the degree-one argument.**

Let `ρ : ℝ → ℝ` be continuous and strictly increasing, let `a`, `b : ℝ → ℝ` be the two coordinate
functions of a `2π`-periodic curve with `cos (ρ θ) = a θ`, `sin (ρ θ) = b θ`, and suppose that the
pair `(a, b)` is injective on the fundamental domain `[0, 2π)`.  If `ρ` shifts by `n · 2π` over a
period, then `n = 1`.

Indeed, `n > 0` because `ρ` is strictly increasing, and if `n ≥ 2` the intermediate value theorem
produces `θ₁ ∈ (0, 2π)` with `ρ θ₁ = ρ 0 + 2π`; then `a θ₁ = cos (ρ 0 + 2π) = a 0` and similarly
for `b`, so `θ₁ = 0`, contradiction. -/
theorem shift_int_eq_one {ρ a b : ℝ → ℝ} {n : ℤ}
    (hcont : Continuous ρ) (hmono : StrictMono ρ)
    (hcos : ∀ θ, Real.cos (ρ θ) = a θ) (hsin : ∀ θ, Real.sin (ρ θ) = b θ)
    (hinj : ∀ θ ∈ Set.Ico 0 (2 * Real.pi), ∀ θ' ∈ Set.Ico 0 (2 * Real.pi),
      a θ = a θ' → b θ = b θ' → θ = θ')
    (hshift : ∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + (n : ℝ) * (2 * Real.pi)) :
    n = 1 := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hshift0 : ρ (2 * Real.pi) = ρ 0 + (n : ℝ) * (2 * Real.pi) := by
    simpa using hshift 0
  have hnpos : 0 < n := by
    have h : ρ 0 < ρ (2 * Real.pi) := hmono (by linarith [Real.pi_pos])
    rw [hshift0] at h
    have h' : (0 : ℝ) < (n : ℝ) * (2 * Real.pi) := by linarith
    have h'' : (0 : ℝ) < 2 * Real.pi * (n : ℝ) := by linarith
    have h''' : (0 : ℝ) < (n : ℝ) := pos_of_mul_pos_right h'' h2π.le
    exact_mod_cast h'''
  have hnle : n ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℤ) ≤ n := by omega
      exact_mod_cast this
    have hle : ρ 0 + 2 * Real.pi ≤ ρ (2 * Real.pi) := by
      rw [hshift0]; nlinarith [hn2]
    obtain ⟨θ₁, hθ₁mem, hθ₁⟩ :=
      (intermediate_value_Icc (f := ρ) (a := (0 : ℝ)) (b := 2 * Real.pi)
        (by linarith [Real.pi_pos]) hcont.continuousOn) ⟨by linarith, hle⟩
    have hθ₁lt : θ₁ < 2 * Real.pi := by
      rw [← hmono.lt_iff_lt, hθ₁, hshift0]
      nlinarith [hn2]
    have hθ₁gt : 0 < θ₁ := by
      rw [← hmono.lt_iff_lt, hθ₁]
      linarith
    have ha : a θ₁ = a 0 := by
      rw [← hcos θ₁, ← hcos 0, hθ₁, Real.cos_add_two_pi]
    have hb : b θ₁ = b 0 := by
      rw [← hsin θ₁, ← hsin 0, hθ₁, Real.sin_add_two_pi]
    exact absurd (hinj θ₁ ⟨hθ₁gt.le, hθ₁lt⟩ 0 ⟨le_refl 0, h2π⟩ ha hb) (ne_of_gt hθ₁gt)
  omega

/-- **A monotone angle lift exists as soon as the angular velocity never vanishes.**

This is the main construction: `ψ θ = c₀ + ∫₀^θ ⟪J (κ t), κ' t⟫ dt` (with `c₀` an argument of
`κ 0`) is a smooth angle lift of `κ` — this is the uniqueness claim for the ODE
`w' = ⟪J w, w'⟫ • J w`, satisfied both by `κ` and by `θ ↦ (cos (ψ θ), sin (ψ θ))`.  Its derivative
is the (nowhere zero) angular velocity, so it is strictly monotone; its period shift is an integer
multiple of `2π`, and equals `2π` up to the sign that makes its derivative positive. -/
theorem lift_of_ne_zero
    {κ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hper : ∀ θ, κ (θ + 2 * Real.pi) = κ θ)
    (hunit : ∀ θ, ‖κ θ‖ = 1)
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    (hne : ∀ θ, angVel κ θ ≠ 0) :
    ∃ (s : ℝ) (ρ : ℝ → ℝ), (s = 1 ∨ s = -1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      (∀ θ, 0 < deriv ρ θ) ∧ (∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi) ∧
      (∀ θ, Real.cos (ρ θ) = (κ θ) 0 ∧ Real.sin (ρ θ) = s * (κ θ) 1) := by
  classical
  -- ## The lift `ψ` obtained by integrating the angular velocity
  have hcs0 := exists_cos_sin (κ 0) (hunit 0)
  obtain ⟨c₀, hc₀cos, hc₀sin⟩ := hcs0
  obtain ⟨hφsm, hφderiv⟩ := contDiff_integral_deriv (angVel_contDiff hsm)
  set ψ : ℝ → ℝ := fun θ => (∫ t in 0..θ, angVel κ t) + c₀ with hψdef
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    rw [hψdef]; exact hφsm.add contDiff_const
  have hψderiv : deriv ψ = angVel κ := by
    funext θ
    rw [hψdef, deriv_add_const]
    exact congrFun hφderiv θ
  have hψd : ∀ θ, HasDerivAt ψ (angVel κ θ) θ := fun θ =>
    ((hψsm.differentiable (by simp)).differentiableAt.hasDerivAt).congr_deriv
      (congrFun hψderiv θ)
  -- ## `ψ` is an angle lift of `κ`
  have hcircPt : ∀ t, HasDerivAt circPt (rot90 (circPt t)) t := circPt_hasDerivAt
  have hγd : ∀ θ, HasDerivAt (fun θ => circPt (ψ θ))
      ((angVel κ θ) • rot90 (circPt (ψ θ))) θ :=
    fun θ => (hcircPt (ψ θ)).scomp θ (hψd θ)
  have hκsmul : ∀ θ, deriv κ θ = (angVel κ θ) • rot90 (κ θ) :=
    fun θ => deriv_eq_smul_rot90 hsm hunit θ
  have hκd : ∀ θ, HasDerivAt κ ((angVel κ θ) • rot90 (κ θ)) θ := by
    intro θ
    have hd : HasDerivAt κ (deriv κ θ) θ :=
      (hsm.differentiable (by simp)).differentiableAt.hasDerivAt
    exact hd.congr_deriv (hκsmul θ)
  have hγ0 : (fun θ => circPt (ψ θ)) 0 = κ 0 := by
    show circPt (ψ 0) = κ 0
    have hψ0 : ψ 0 = c₀ := by
      rw [hψdef]; simp
    rw [hψ0]
    refine PiLp.ext fun i => ?_
    fin_cases i
    · simpa using (circPt_zero c₀).trans hc₀cos
    · simpa using (circPt_one c₀).trans hc₀sin
  have heq : (fun θ => circPt (ψ θ)) = κ :=
    eq_of_deriv_eq_smul_rot90 hγd hκd (fun θ => norm_circPt (ψ θ)) hunit hγ0
  have hcs : ∀ θ, Real.cos (ψ θ) = (κ θ) 0 ∧ Real.sin (ψ θ) = (κ θ) 1 := by
    intro θ
    have h := congrFun heq θ
    exact ⟨by rw [← circPt_zero (ψ θ), h], by rw [← circPt_one (ψ θ), h]⟩
  -- ## injectivity of the coordinate pair, in the two signed versions
  have hinj_pos : ∀ θ ∈ Set.Ico 0 (2 * Real.pi), ∀ θ' ∈ Set.Ico 0 (2 * Real.pi),
      (κ θ) 0 = (κ θ') 0 → (κ θ) 1 = (κ θ') 1 → θ = θ' := by
    intro θ hθ θ' hθ' h0 h1
    exact hinj hθ hθ' (PiLp.ext fun i => by fin_cases i <;> assumption)
  have hinj_neg : ∀ θ ∈ Set.Ico 0 (2 * Real.pi), ∀ θ' ∈ Set.Ico 0 (2 * Real.pi),
      (κ θ) 0 = (κ θ') 0 → -((κ θ) 1) = -((κ θ') 1) → θ = θ' := by
    intro θ hθ θ' hθ' h0 h1
    refine hinj hθ hθ' (PiLp.ext fun i => ?_)
    fin_cases i
    · exact h0
    · exact neg_inj.mp h1
  have hper_int : ∃ n : ℤ, ∀ θ, ψ (θ + 2 * Real.pi) = ψ θ + (n : ℝ) * (2 * Real.pi) :=
    period_shift_exists_int hper hψsm.continuous hcs
  rcases sign_of_continuous_ne_zero (angVel_contDiff hsm).continuous hne with hpos | hneg
  · -- ## The angular velocity is positive everywhere: `ρ = ψ`, `s = 1`
    obtain ⟨n, hn⟩ := hper_int
    have hmono : StrictMono ψ :=
      strictMono_of_deriv_pos (fun θ => by rw [hψderiv]; exact hpos θ)
    have hn1 : n = 1 := shift_int_eq_one hψsm.continuous hmono (fun θ => (hcs θ).1)
      (fun θ => (hcs θ).2) hinj_pos hn
    refine ⟨1, ψ, Or.inl rfl, hψsm, fun θ => ?_, fun θ => ?_, fun θ => ?_⟩
    · rw [hψderiv]; exact hpos θ
    · rw [hn θ, hn1]; norm_num
    · exact ⟨(hcs θ).1, by rw [one_mul]; exact (hcs θ).2⟩
  · -- ## The angular velocity is negative everywhere: `ρ = -ψ`, `s = -1`
    have hρsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ => -ψ θ) := hψsm.neg
    have hρderiv : deriv (fun θ => -ψ θ) = fun θ => -(angVel κ θ) := by
      funext θ
      exact ((hψd θ).neg).deriv
    obtain ⟨n, hn⟩ := hper_int
    have hn' : ∀ θ, (fun θ => -ψ θ) (θ + 2 * Real.pi) =
        (fun θ => -ψ θ) θ + ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
      intro θ
      show -(ψ (θ + 2 * Real.pi)) = -ψ θ + ((-n : ℤ) : ℝ) * (2 * Real.pi)
      rw [hn θ]; push_cast; ring
    have hmono : StrictMono (fun θ => -ψ θ) :=
      strictMono_of_deriv_pos (fun θ => by rw [hρderiv]; exact neg_pos.mpr (hneg θ))
    have hcs' : ∀ θ, Real.cos ((fun θ => -ψ θ) θ) = (κ θ) 0 ∧
        Real.sin ((fun θ => -ψ θ) θ) = -((κ θ) 1) := by
      intro θ
      exact ⟨by simpa using (hcs θ).1, by simp [Real.sin_neg, (hcs θ).2]⟩
    have hn1 : -n = 1 := shift_int_eq_one hρsm.continuous hmono (fun θ => (hcs' θ).1)
      (fun θ => (hcs' θ).2) hinj_neg hn'
    refine ⟨-1, fun θ => -ψ θ, Or.inr rfl, hρsm, fun θ => ?_, fun θ => ?_, fun θ => ?_⟩
    · rw [hρderiv]; exact neg_pos.mpr (hneg θ)
    · rw [hn' θ, hn1]; norm_num
    · exact ⟨(hcs' θ).1, by rw [(hcs' θ).2]; ring⟩

/-- **A monotone angle lift of a degree-one circle map.**

Let `κ : ℝ → ℝ²` be `C^∞`, `2π`-periodic, with `‖κ θ‖ = 1`, injective on the fundamental domain
`[0, 2π)`, and with nowhere vanishing angular velocity `⟪J (κ θ), deriv κ θ⟫ ≠ 0` (where
`J = Work.Diff.Dim2.rot90` is the quarter turn).  Then, after possibly reflecting the target
(`s = -1`, i.e. `sin ↦ -sin`), `κ` has a `C^∞` angle lift `ρ` whose derivative is *strictly
positive* and which shifts by exactly `2π` per period.

More precisely there are `s ∈ {1, -1}` and `ρ : ℝ → ℝ` with `ρ` smooth, `deriv ρ θ > 0` everywhere,
`ρ (θ + 2π) = ρ θ + 2π`, and `cos (ρ θ) = (κ θ) 0`, `sin (ρ θ) = s * (κ θ) 1`.

Route: `κ` has a lift `ρ₀` (covering map `ℝ → S¹`, `ℝ` simply connected); the hypothesis
`⟪J (κ θ), deriv κ θ⟫ ≠ 0` says `deriv ρ₀ ≠ 0`, so `ρ₀` is strictly monotone; injectivity of `κ` on
the fundamental domain forces `ρ₀ (θ + 2π) - ρ₀ θ = ± 2π`; in the `+2π` case take `s = 1`,
`ρ = ρ₀`; in the `-2π` case take `s = -1`, `ρ = -ρ₀`. -/
theorem lift_monotone
    {κ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ)
    (hper : ∀ θ, κ (θ + 2 * Real.pi) = κ θ)
    (hunit : ∀ θ, ‖κ θ‖ = 1)
    (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    (hw : ∀ θ, inner ℝ (Work.Diff.Dim2.rot90 (κ θ)) (deriv κ θ) ≠ 0) :
    ∃ (s : ℝ) (ρ : ℝ → ℝ), (s = 1 ∨ s = -1) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧
      (∀ θ, 0 < deriv ρ θ) ∧ (∀ θ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi) ∧
      (∀ θ, Real.cos (ρ θ) = (κ θ) 0 ∧ Real.sin (ρ θ) = s * (κ θ) 1) := by
  exact lift_of_ne_zero hsm hper hunit hinj hw

end

end Work.Diff.Dim2
