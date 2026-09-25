import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower

namespace Work.BourgainPlan.Maximal

/-- **The lower Rademacher (Khintchine) inequality, averaged over the sign vectors.**

For every finite index type `ι` and every `p ≥ 1` there is `c > 0` with

  `c · (∑_i ‖u i‖²)^{p/2} ≤ (∑_{ε : ι → Bool} ‖∑_i ε_i u i‖^p) / |ι → Bool|`

for every family `u : ι → ℂ` — the "lower" half of Khintchine's inequality, in the normed form in
which the randomisation argument for square functions consumes it: the average over the signs of
`‖Σ_i ε_i u_i‖^p` dominates `(Σ_i ‖u_i‖²)^{p/2}`.

This is an immediate corollary of the already-proved two-stage lower bound
`Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower` (in
`Submission/Work/BourgainPlan/IonescuWainger/rademacher_two_stage_lower.lean`) with the second
index type specialised to `PUnit`: the inner sum over `η : PUnit → Bool` has two terms whose
coefficient is `±1`, so it contributes `2 · ‖Σ_i ε_i u_i‖^p` and the cardinality factor
`|PUnit → Bool| = 2` cancels.  (In `ENNReal`, `2 * (A * 2)⁻¹ = A⁻¹`.) -/
theorem rademacher_lower_finset {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (hp : 1 ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : ι → ℂ),
      ENNReal.ofReal c * (∑ i : ι, ‖u i‖ₑ ^ (2:ℝ)) ^ (p / 2)
        ≤ (∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1 : ℂ) else -1) * u i‖ₑ ^ p) *
            (Fintype.card (ι → Bool) : ENNReal)⁻¹ := by
  obtain ⟨c, hc, h⟩ := Work.BourgainPlan.IonescuWainger.rademacher_two_stage_lower p hp
  refine ⟨c, hc, fun u => ?_⟩
  classical
  -- Specialise the second index type of the two-stage bound to `Unit` and set `a i _ = u i`.
  have key := h (κ := Unit) (fun i (_ : Unit) => u i)
  -- The left-hand side: the inner (single-term) sum over `Unit` contributes nothing new.
  have hL : (∑ i : ι, ∑ t : Unit, ‖(fun i (_ : Unit) => u i) i t‖ₑ ^ (2:ℝ))
      = ∑ i : ι, ‖u i‖ₑ ^ (2:ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_unique]
  -- The right-hand side: for each `ε` the sum over `η : Unit → Bool` has the two terms
  -- `‖Σ_i ε_i u_i‖ₑ ^ p`, so it equals `2 * ‖Σ_i ε_i u_i‖ₑ ^ p`.
  have hR : (∑ ε : ι → Bool, ∑ η : Unit → Bool, ‖∑ i : ι, ∑ t : Unit,
        (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
          * (fun i (_ : Unit) => u i) i t‖ₑ ^ p)
      = 2 * (∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    have hF : ∀ η : Unit → Bool,
        ‖∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t‖ₑ ^ p
          = ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p := by
      intro η
      -- Factor the `±1` coefficient `η ()` out of the whole sum.
      have hsum : (∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t)
          = (if η () then (1:ℂ) else -1) * ∑ i : ι, (if ε i then (1:ℂ) else -1) * u i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_unique]
        ring
      have hnorm : ‖∑ i : ι, ∑ t : Unit, (if ε i then (1:ℂ) else -1) * (if η t then (1:ℂ) else -1)
            * (fun i (_ : Unit) => u i) i t‖
          = ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ := by
        rw [hsum, norm_mul,
          show ‖(if η () then (1:ℂ) else -1)‖ = 1 from by rcases η () <;> simp,
          one_mul]
      rw [← ofReal_norm, ← ofReal_norm, hnorm]
    rw [Finset.sum_congr rfl (fun η _ => hF η), Finset.sum_const, Finset.card_univ]
    rw [show Fintype.card (Unit → Bool) = 2 from by simp [Fintype.card_bool],
      two_nsmul, two_mul]
  have hD : (Fintype.card (Unit → Bool) : ENNReal) = 2 := by
    rw [show Fintype.card (Unit → Bool) = 2 from by simp [Fintype.card_bool]]
    norm_num
  rw [hL, hR, hD] at key
  refine le_trans key (le_of_eq ?_)
  -- Pure `ENNReal` arithmetic: `2 * A * (C * 2)⁻¹ = A * C⁻¹`.
  set A : ENNReal := ∑ ε : ι → Bool, ‖∑ i : ι, (if ε i then (1:ℂ) else -1) * u i‖ₑ ^ p
  set C : ENNReal := (Fintype.card (ι → Bool) : ENNReal)
  rw [ENNReal.mul_inv (Or.inr (by norm_num : (2:ENNReal) ≠ ⊤))
      (Or.inr (by norm_num : (2:ENNReal) ≠ 0))]
  calc (2 * A) * (C⁻¹ * 2⁻¹)
      = (2 * 2⁻¹) * (A * C⁻¹) := by ring
    _ = 1 * (A * C⁻¹) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ = A * C⁻¹ := one_mul _

end Work.BourgainPlan.Maximal
