import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.Q_sub_norm_le
import Submission.Work.Diff.MP.exists_local_solution_Q
import Submission.Work.Diff.MP.ode_taylor_estimates
import Submission.Work.Diff.MP.ode_push_forward_of_invariant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The growing truncation of an ODE-invariant family

For `ϱ > 0` we construct `Λ > 0`, `ε > 0` with `ε ≤ 1/(2Λ)` and `C' ≥ 0` such that for *every*
family `F` invariant under Hamilton's ODE `R' = Q R` and every `a` with `F a ∩ frobBall ϱ ≠ ∅`:

* the truncated family `truncFam F ϱ Λ a t = F t ∩ frobBall (growRad ϱ Λ (t - a))` is nonempty on
  `[a, a + ε]`, and
* every `S` of the truncated family at time `t` has a successor `S'` of the truncated family at
  time `t + h` within the second order Euler approximation `S + h • Q S`, `h ≤ ε - (t - a)`.

The radius `growRad ϱ Λ s = ϱ / (1 - Λ s)` is the solution of `Υ' = Λ Υ²` with `Υ 0 = ϱ`; since
`|Q R| ≤ 5 n² |R|²` the one-step push-forward of the ODE grows no faster than `Υ`, provided
`Λ ≥ n² L / ϱ` where `L` is the *uniform* bound of `Q` on the Frobenius ball of radius `2ϱ`.

The proof is therefore:

1. `exists_uniform_push_Q`: on the Frobenius ball of radius `R` there is a time `δ > 0` and constants
   `L, C` such that for every `S` in that ball the solution `Ψ` of `Ψ' = Q ∘ Ψ`, `Ψ 0 = S` exists on
   `(-δ, δ)` with `‖Ψ h - S‖ ≤ L h` and `frobDist (Ψ h) (S + h • Q S) ≤ C h²` for `h ∈ [0, δ]`.
   (This is a *uniform* strengthening of `ode_push_forward_of_invariant`, obtained from
   Picard–Lindelöf on a closed ball together with the mean value inequality.)
2. `ode_shift_mem`: `ODEInvariantFamily` applied to the time-shifted curve `s ↦ Ψ (s - t)` gives
   `Ψ h ∈ F (t + h)`.
3. `growRad_add_le`: the arithmetic of the comparison with the super-solution `Υ`.
-/

set_option maxHeartbeats 8000000

open Set Metric
open Submission.Diff.Alg
open scoped NNReal

namespace Work.Diff.MP

/-! ## A strengthened Picard–Lindelöf: the local flow stays in the ball

Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` produces the solution but
does not record that it stays inside the closed ball on which the vector field is controlled.  On
the finite-dimensional side this is what makes the constants uniform in the initial point, so we
prove the strengthened form here (the proof is the one from `Mathlib.Analysis.ODE.PicardLindelof`,
where the ball membership is available internally as `FunSpace.compProj_mem_closedBall`). -/

theorem picard_flow_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    exact α.compProj_mem_closedBall hf.mul_max_le
  · intro t ht
    refine (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem ?_ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- The flow version of the previous lemma. -/
theorem picard_flow_mem_closedBall'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ r,
      α x t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α x t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t := by
  classical
  have H : ∀ x ∈ closedBall x₀ r, ∃ α : ℝ → E, α t₀ = x ∧
      (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
    fun x hx => picard_flow_mem_closedBall hf hx
  choose β hβ using H
  refine ⟨fun x => if hx : x ∈ closedBall x₀ r then β x hx else fun _ => x, ?_⟩
  intro x hx
  simp only [dite_eq_left hx]
  exact hβ x hx

/-! ## The uniform one-step push-forward on a Frobenius ball -/

/-- **Uniform local existence and Taylor estimates for `R' = Q R` on a Frobenius ball.**

For the Frobenius ball of radius `R > 0` there are `δ > 0`, `L ≥ 0`, `C ≥ 0` such that for every
`S` with `frobNorm S ≤ R` there is a solution `Ψ` of `Ψ' = Q (Ψ)` with `Ψ 0 = S`, defined and
differentiable on the open interval `(-δ, δ)`, with `‖Ψ h - S‖ ≤ L h` (the uniform Lipschitz/Sup
bound) and `frobDist (Ψ h) (S + h • Q S) ≤ C h²` (the second-order Euler remainder) for
`h ∈ [0, δ]`. -/
theorem exists_uniform_push_Q (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ δ > 0, ∃ L : ℝ, 0 ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : Curv4 n, frobNorm S ≤ R →
        ∃ Ψ : ℝ → Curv4 n, Ψ 0 = S ∧
          (∀ h ∈ Ioo (-δ) δ, HasDerivAt Ψ (Q (Ψ h)) h) ∧
          (∀ h ∈ Icc 0 δ, ‖Ψ h - S‖ ≤ L * h) ∧
          (∀ h ∈ Icc 0 δ, frobDist (Ψ h) (S + h • Q S) ≤ C * h ^ 2) := by
  have hQ0 : Q (0 : Curv4 n) = 0 := by
    ext i j k l
    simp [Q]
  have hQlip : ∀ x y : Curv4 n,
      ‖Q x - Q y‖ ≤ 5 * (n : ℝ) ^ 2 * (‖x‖ + ‖y‖) * ‖x - y‖ := fun x y => Q_sub_norm_le n x y
  set Lc : ℝ := 5 * (n : ℝ) ^ 2 * (2 * R) ^ 2 + 1 with hLcdef
  set Kc : ℝ := 5 * (n : ℝ) ^ 2 * (2 * R + 2 * R) with hKcdef
  have hLcpos : 0 < Lc := by rw [hLcdef]; positivity
  have hKcnn : 0 ≤ Kc := by rw [hKcdef]; positivity
  set m : ℝ := R / (2 * Lc) with hmdef
  have hmpos : 0 < m := by rw [hmdef]; positivity
  have hQbound : ∀ x : Curv4 n, ‖x‖ ≤ 2 * R → ‖Q x‖ ≤ Lc := by
    intro x hx
    have h2 : ‖Q x - Q 0‖ ≤ 5 * (n : ℝ) ^ 2 * (‖x‖ * ‖x‖) := by
      have h := hQlip x 0
      calc ‖Q x - Q 0‖ ≤ 5 * (n : ℝ) ^ 2 * (‖x‖ + ‖(0 : Curv4 n)‖) * ‖x - 0‖ := h
        _ = 5 * (n : ℝ) ^ 2 * (‖x‖ * ‖x‖) := by rw [norm_zero, add_zero, sub_zero]; ring
    have hxx : ‖x‖ * ‖x‖ ≤ (2 * R) * (2 * R) :=
      mul_le_mul hx hx (norm_nonneg _) (by linarith)
    have h4 : ‖Q x‖ = ‖Q x - Q 0‖ := by rw [hQ0, sub_zero]
    rw [h4]
    calc ‖Q x - Q 0‖ ≤ 5 * (n : ℝ) ^ 2 * (‖x‖ * ‖x‖) := h2
      _ ≤ 5 * (n : ℝ) ^ 2 * ((2 * R) * (2 * R)) := mul_le_mul_of_nonneg_left hxx (by positivity)
      _ ≤ Lc := by rw [hLcdef]; nlinarith
  have hQlipBall : ∀ x y : Curv4 n, ‖x‖ ≤ 2 * R → ‖y‖ ≤ 2 * R →
      ‖Q x - Q y‖ ≤ Kc * ‖x - y‖ := by
    intro x y hx hy
    have h := hQlip x y
    have hxy : ‖x‖ + ‖y‖ ≤ 2 * R + 2 * R := add_le_add hx hy
    have h1 : 5 * (n : ℝ) ^ 2 * (‖x‖ + ‖y‖) ≤ 5 * (n : ℝ) ^ 2 * (2 * R + 2 * R) :=
      mul_le_mul_of_nonneg_left hxy (by positivity)
    calc ‖Q x - Q y‖ ≤ 5 * (n : ℝ) ^ 2 * (‖x‖ + ‖y‖) * ‖x - y‖ := h
      _ ≤ 5 * (n : ℝ) ^ 2 * (2 * R + 2 * R) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = Kc * ‖x - y‖ := by rw [hKcdef]
  -- package the `ℝ≥0` constants
  let A : ℝ≥0 := NNReal.mk (2 * R) (by linarith)
  let Rr : ℝ≥0 := NNReal.mk R hR.le
  let Ln : ℝ≥0 := NNReal.mk Lc hLcpos.le
  let Kn : ℝ≥0 := NNReal.mk Kc hKcnn
  have hAcoe : (A : ℝ) = 2 * R := NNReal.coe_mk _ _
  have hRcoe : (Rr : ℝ) = R := NNReal.coe_mk _ _
  have hLcoe : (Ln : ℝ) = Lc := NNReal.coe_mk _ _
  have hf : IsPicardLindelof (fun _ : ℝ => Q)
      (⟨0, by constructor <;> linarith [hmpos]⟩ : Icc (-m) m) (0 : Curv4 n) A Rr Ln Kn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro x hx y hy
      rw [mem_closedBall, dist_eq_norm, sub_zero, hAcoe] at hx hy
      rw [dist_eq_norm]
      exact hQlipBall x y hx hy
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      rw [mem_closedBall, dist_eq_norm, sub_zero, hAcoe] at hx
      exact hQbound x hx
    · have ht0 : ((⟨0, by constructor <;> linarith [hmpos]⟩ : Icc (-m) m) : ℝ) = 0 := rfl
      rw [hLcoe, hAcoe, hRcoe, ht0, sub_zero, zero_sub, neg_neg, max_self]
      have hLm : Lc * m = R / 2 := by rw [hmdef]; field_simp
      linarith
  obtain ⟨α, hα⟩ := picard_flow_mem_closedBall' hf
  refine ⟨m, hmpos, Lc, hLcpos.le, (n : ℝ) ^ 2 * (Kc * Lc), by positivity, ?_⟩
  intro S hS
  have hSr : S ∈ closedBall (0 : Curv4 n) Rr := by
    rw [mem_closedBall, dist_eq_norm, sub_zero, hRcoe]
    exact le_trans (norm_le_frobNorm S) hS
  obtain ⟨hα0, hαball, hαderiv⟩ := hα S hSr
  have hball : ∀ t ∈ Icc (-m) m, ‖α S t‖ ≤ 2 * R := by
    intro t ht
    have hh := hαball t ht
    rw [mem_closedBall, dist_eq_norm, sub_zero, hAcoe] at hh
    exact hh
  have hα0' : α S 0 = S := by simpa using hα0
  refine ⟨α S, hα0', ?_, ?_, ?_⟩
  · intro h hh
    exact (hαderiv h (Ioo_subset_Icc_self hh)).hasDerivAt (Icc_mem_nhds hh.1 hh.2)
  · intro h hh
    have hsub : Icc (0 : ℝ) h ⊆ Icc (-m) m :=
      fun z hz => ⟨by linarith [hmpos, hz.1], le_trans hz.2 hh.2⟩
    have hderiv : ∀ x ∈ Icc (0 : ℝ) h, HasDerivWithinAt (α S) (Q (α S x)) (Icc (0 : ℝ) h) x :=
      fun x hx => (hαderiv x (hsub hx)).mono hsub
    have hbound : ∀ x ∈ Ico (0 : ℝ) h, ‖Q (α S x)‖ ≤ Lc := by
      intro x hx
      exact hQbound _ (hball x ⟨by linarith [hmpos, hx.1],
        le_of_lt (lt_of_lt_of_le hx.2 hh.2)⟩)
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound h ⟨hh.1, le_rfl⟩
    simpa [hα0', sub_zero] using key
  · intro h hh
    have hsub : Icc (0 : ℝ) h ⊆ Icc (-m) m :=
      fun z hz => ⟨by linarith [hmpos, hz.1], le_trans hz.2 hh.2⟩
    have hderiv : ∀ x ∈ Icc (0 : ℝ) h,
        HasDerivWithinAt (fun u => α S u - u • Q S) (Q (α S x) - Q S) (Icc (0 : ℝ) h) x := by
      intro x hx
      have h1 : HasDerivWithinAt (α S) (Q (α S x)) (Icc (0 : ℝ) h) x :=
        (hαderiv x (hsub hx)).mono hsub
      have h2 : HasDerivWithinAt (fun u : ℝ => u • Q S) (Q S) (Icc (0 : ℝ) h) x := by
        simpa using ((hasDerivAt_id x).smul_const (Q S)).hasDerivWithinAt (s := Icc (0 : ℝ) h)
      exact h1.sub h2
    have hlin : ∀ x ∈ Icc (0 : ℝ) h, ‖α S x - S‖ ≤ Lc * x := by
      intro x hx
      have hsub2 : Icc (0 : ℝ) x ⊆ Icc (-m) m :=
        fun z hz => ⟨by linarith [hmpos, hz.1], le_trans hz.2 (le_trans hx.2 hh.2)⟩
      have hderiv' : ∀ y ∈ Icc (0 : ℝ) x, HasDerivWithinAt (α S) (Q (α S y)) (Icc (0 : ℝ) x) y :=
        fun y hy => (hαderiv y (hsub2 hy)).mono hsub2
      have hbound' : ∀ y ∈ Ico (0 : ℝ) x, ‖Q (α S y)‖ ≤ Lc := by
        intro y hy
        exact hQbound _ (hball y ⟨by linarith [hmpos, hy.1],
          le_of_lt (lt_of_lt_of_le hy.2 (le_trans hx.2 hh.2))⟩)
      have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv' hbound' x ⟨hx.1, le_rfl⟩
      simpa [hα0', sub_zero] using key
    have hbound : ∀ x ∈ Ico (0 : ℝ) h, ‖Q (α S x) - Q S‖ ≤ Kc * (Lc * h) := by
      intro x hx
      have hxle : x ≤ h := le_of_lt hx.2
      have hb1 : ‖α S x‖ ≤ 2 * R := hball x ⟨by linarith [hmpos, hx.1], le_trans hxle hh.2⟩
      have hb2 : ‖S‖ ≤ 2 * R := le_trans (norm_le_frobNorm S) (le_trans hS (by linarith))
      have h1 := hQlipBall _ _ hb1 hb2
      have h2 := hlin x ⟨hx.1, hxle⟩
      calc ‖Q (α S x) - Q S‖ ≤ Kc * ‖α S x - S‖ := h1
        _ ≤ Kc * (Lc * x) := mul_le_mul_of_nonneg_left h2 hKcnn
        _ ≤ Kc * (Lc * h) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxle hLcpos.le) hKcnn
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound h ⟨hh.1, le_rfl⟩
    have key' : ‖(α S h - h • Q S) - (α S 0 - (0 : ℝ) • Q S)‖ ≤ (Kc * (Lc * h)) * h := by
      simpa [sub_zero] using key
    have h3 : ‖α S h - (S + h • Q S)‖ ≤ Kc * Lc * h ^ 2 := by
      have h4 : (α S h - h • Q S) - (α S 0 - (0 : ℝ) • Q S) = α S h - (S + h • Q S) := by
        rw [hα0', zero_smul, sub_zero]
        abel
      rw [← h4]
      calc ‖(α S h - h • Q S) - (α S 0 - (0 : ℝ) • Q S)‖ ≤ (Kc * (Lc * h)) * h := key'
        _ = Kc * Lc * h ^ 2 := by ring
    calc frobDist (α S h) (S + h • Q S) = frobNorm (α S h - (S + h • Q S)) := rfl
      _ ≤ (n : ℝ) ^ 2 * ‖α S h - (S + h • Q S)‖ := frobNorm_le_mul_norm _
      _ ≤ (n : ℝ) ^ 2 * (Kc * Lc * h ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ((n : ℝ) ^ 2 * (Kc * Lc)) * h ^ 2 := by ring

/-! ## The time shift of a local solution -/

/-- A local solution of `R' = Q R` starting at `S ∈ F t` has its time-shifted values in `F`:
`Ψ h ∈ F (t + h)`.  `ODEInvariantFamily` is stated on left-closed intervals, so the shifted curve
`s ↦ Ψ (s - t)` is run up to `t + η` with `h < η < δ`. -/
theorem ode_shift_mem (n : ℕ) (F : ℝ → Set (Curv4 n))
    (hF : ODEInvariantFamily F) (t : ℝ) (S : Curv4 n) (hS : S ∈ F t)
    {δ : ℝ} (hδ : 0 < δ) (Ψ : ℝ → Curv4 n) (hΨ0 : Ψ 0 = S)
    (hΨd : ∀ h ∈ Ioo (-δ) δ, HasDerivAt Ψ (Q (Ψ h)) h)
    {h : ℝ} (hh0 : 0 < h) (hhδ : h < δ) : Ψ h ∈ F (t + h) := by
  set η : ℝ := (h + δ) / 2 with hη
  have hlt : h < η := by rw [hη]; linarith
  have hηδ : η < δ := by rw [hη]; linarith
  have hmem0 : (fun s : ℝ => Ψ (s - t)) t ∈ F t := by simpa [hΨ0] using hS
  have hderiv : ∀ s ∈ Ico t (t + η),
      HasDerivWithinAt (fun s : ℝ => Ψ (s - t)) (Q (Ψ (s - t))) (Ico t (t + η)) s := by
    intro s hs
    have hu : s - t ∈ Ioo (-δ) δ := ⟨by linarith [hs.1], by linarith [hs.2, hηδ]⟩
    have h1 : HasDerivAt Ψ (Q (Ψ (s - t))) (s - t) := hΨd _ hu
    have h2 : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Ico t (t + η)) s :=
      ((hasDerivAt_id s).sub_const t).hasDerivWithinAt
    have h3 := HasDerivAt.scomp_hasDerivWithinAt (x := s) (h := fun s : ℝ => s - t) h1 h2
    rw [one_smul] at h3
    exact h3
  have hres := hF t (t + η) (fun s : ℝ => Ψ (s - t)) hmem0 hderiv
  have hmem : t + h ∈ Ico t (t + η) := ⟨by linarith, by linarith⟩
  have := hres (t + h) hmem
  simpa using this

/-! ## The growth comparison for `growRad` -/

/-- On the domain where the denominator is positive, the truncation radius is at most `2 ϱ`. -/
theorem growRad_le_two (ϱ Λ s : ℝ) (hϱ : 0 < ϱ) (h1 : 0 < 1 - Λ * s) (h2 : Λ * s ≤ 1 / 2) :
    growRad ϱ Λ s ≤ 2 * ϱ := by
  rw [growRad]
  rw [div_le_iff₀ h1]
  nlinarith

/-- The arithmetic of the comparison with the super-solution `Υ s = growRad ϱ Λ s`: if `Λ` dominates
the quadratic constant of `Q` on the truncated ball (`n² L ≤ Λ ϱ`) then one Euler step of the ODE
fits into the next truncation ball. -/
theorem growRad_add_le (n : ℕ) (ϱ L Λ s h : ℝ) (hϱ : 0 < ϱ) (hL : 0 ≤ L) (hΛpos : 0 < Λ)
    (hΛ : (n : ℝ) ^ 2 * L ≤ Λ * ϱ) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (h1 : 0 < 1 - Λ * s) (h2 : 0 < 1 - Λ * (s + h)) :
    growRad ϱ Λ s + (n : ℝ) ^ 2 * (L * h) ≤ growRad ϱ Λ (s + h) := by
  have hden : 0 < (1 - Λ * (s + h)) * (1 - Λ * s) := mul_pos h2 h1
  have ha : 1 - Λ * (s + h) ≤ 1 := by
    nlinarith [mul_nonneg hΛpos.le (by linarith : (0 : ℝ) ≤ s + h)]
  have hb : 1 - Λ * s ≤ 1 := by nlinarith [mul_nonneg hΛpos.le hs]
  have hle1 : (1 - Λ * (s + h)) * (1 - Λ * s) ≤ 1 := by nlinarith [hden, ha, hb]
  have hdiff : growRad ϱ Λ (s + h) - growRad ϱ Λ s
      = ϱ * Λ * h / ((1 - Λ * (s + h)) * (1 - Λ * s)) := by
    rw [growRad, growRad]
    field_simp
    ring
  have hnum : (n : ℝ) ^ 2 * (L * h) ≤ ϱ * Λ * h := by nlinarith [hΛ, hh, hϱ, hΛpos]
  have key : (n : ℝ) ^ 2 * (L * h) ≤ growRad ϱ Λ (s + h) - growRad ϱ Λ s := by
    rw [hdiff, le_div_iff₀ hden]
    have hmul := mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (L * h))
    linarith
  linarith

/-! ## The target -/

theorem trunc_push_growing (n : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (2 * Λ) ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (F : ℝ → Set (Submission.Diff.Alg.Curv4 n)),
        Submission.Diff.Alg.ODEInvariantFamily F → ∀ (a : ℝ),
        (Work.Diff.MP.truncFam F ϱ Λ a a).Nonempty →
        (∀ t ∈ Set.Icc a (a + ε), (Work.Diff.MP.truncFam F ϱ Λ a t).Nonempty) ∧
        (∀ t ∈ Set.Ico a (a + ε), ∀ h : ℝ, 0 < h → h ≤ ε - (t - a) →
          ∀ S ∈ Work.Diff.MP.truncFam F ϱ Λ a t,
            ∃ S' ∈ Work.Diff.MP.truncFam F ϱ Λ a (t + h),
              Work.Diff.MP.frobDist S' (S + h • Submission.Diff.Alg.Q S) ≤ C' * h ^ 2) := by
  have hR2 : 0 < 2 * ϱ := by linarith
  obtain ⟨δ, hδpos, L, hLnn, C, hCnn, hpush⟩ := exists_uniform_push_Q n (2 * ϱ) hR2
  set Λ : ℝ := (n : ℝ) ^ 2 * L / ϱ + 1 with hΛdef
  have hΛpos : 0 < Λ := by rw [hΛdef]; positivity
  have hΛϱ : (n : ℝ) ^ 2 * L ≤ Λ * ϱ := by
    have h1 : Λ * ϱ = (n : ℝ) ^ 2 * L + ϱ := by rw [hΛdef]; field_simp
    linarith
  set ε : ℝ := min (δ / 2) (1 / (2 * Λ)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min (by linarith) (by positivity)
  have hε1 : ε ≤ 1 / (2 * Λ) := by rw [hεdef]; exact min_le_right _ _
  have hεδ : ε ≤ δ / 2 := by rw [hεdef]; exact min_le_left _ _
  have hΛε : Λ * ε ≤ 1 / 2 := by
    have h2 : Λ * ε ≤ Λ * (1 / (2 * Λ)) := mul_le_mul_of_nonneg_left hε1 hΛpos.le
    have h3 : Λ * (1 / (2 * Λ)) = 1 / 2 := by field_simp
    linarith
  refine ⟨Λ, hΛpos, ε, hεpos, hε1, C, hCnn, ?_⟩
  intro F hF a hne
  have hconj2 : ∀ t ∈ Ico a (a + ε), ∀ h : ℝ, 0 < h → h ≤ ε - (t - a) →
      ∀ S ∈ truncFam F ϱ Λ a t,
        ∃ S' ∈ truncFam F ϱ Λ a (t + h),
          frobDist S' (S + h • Q S) ≤ C * h ^ 2 := by
    intro t ht h hh0 hh S hS
    rw [truncFam_eq] at hS
    obtain ⟨hSF, hSball⟩ := hS
    have hSgr : frobNorm S ≤ growRad ϱ Λ (t - a) := hSball
    have hs0 : 0 ≤ t - a := by linarith [ht.1]
    have hse : t - a ≤ ε := by linarith [ht.2]
    have hΛs : Λ * (t - a) ≤ 1 / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hse hΛpos.le) hΛε
    have hden : 0 < 1 - Λ * (t - a) := by linarith
    have hS2R : frobNorm S ≤ 2 * ϱ := le_trans hSgr (growRad_le_two ϱ Λ (t - a) hϱ hden hΛs)
    obtain ⟨Ψ, hΨ0, hΨd, hΨlin, hΨtay⟩ := hpush S hS2R
    have hhδ : h < δ := by linarith [hh, hεδ, hδpos]
    have hmemF : Ψ h ∈ F (t + h) := ode_shift_mem n F hF t S hSF hδpos Ψ hΨ0 hΨd hh0 hhδ
    have hden2 : 0 < 1 - Λ * ((t - a) + h) := by
      have h1 : Λ * ((t - a) + h) ≤ Λ * ε :=
        mul_le_mul_of_nonneg_left (by linarith) hΛpos.le
      linarith
    have hlin2 : frobNorm (Ψ h) ≤ frobNorm S + (n : ℝ) ^ 2 * (L * h) := by
      have h1 := frobNorm_add_le (Ψ h - S) S
      rw [sub_add_cancel] at h1
      have h2 : frobNorm (Ψ h - S) ≤ (n : ℝ) ^ 2 * (L * h) := by
        have h3 := hΨlin h ⟨hh0.le, le_of_lt hhδ⟩
        calc frobNorm (Ψ h - S) ≤ (n : ℝ) ^ 2 * ‖Ψ h - S‖ := frobNorm_le_mul_norm _
          _ ≤ (n : ℝ) ^ 2 * (L * h) := mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith
    have hnorm : frobNorm (Ψ h) ≤ growRad ϱ Λ (t + h - a) := by
      rw [show t + h - a = (t - a) + h by ring]
      have hstep := growRad_add_le n ϱ L Λ (t - a) h hϱ hLnn hΛpos hΛϱ hs0 hh0.le hden hden2
      linarith
    exact ⟨Ψ h, by rw [truncFam_eq]; exact ⟨hmemF, hnorm⟩,
      hΨtay h ⟨hh0.le, le_of_lt hhδ⟩⟩
  refine ⟨?_, hconj2⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hta | hlt
  · rw [← hta]
    exact hne
  · obtain ⟨S0, hS0⟩ := hne
    obtain ⟨S', hS', -⟩ :=
      hconj2 a ⟨le_rfl, by linarith [hεpos]⟩ (t - a) (by linarith) (by linarith [ht.1, ht.2]) S0 hS0
    exact ⟨S', by rwa [show a + (t - a) = t by ring] at hS'⟩

end Work.Diff.MP
