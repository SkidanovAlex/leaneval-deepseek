import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Work.MotT

/-- In a field of characteristic `≠ 5`, the numeral `5` is nonzero. -/
private lemma five_ne_zero_of_ringChar_ne {K : Type} [Field K] (hk : ringChar K ≠ 5) :
    (5 : K) ≠ 0 := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hz
  · intro h0
    have hdvd : ringChar K ∣ 5 := (ringChar.spec K 5).mp h0
    rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd (ringChar K) hdvd with h1 | h5
    · exact hp.ne_one h1
    · exact hk h5
  · haveI : CharZero K := (CharP.charP_zero_iff_charZero K).mp (ringChar.eq_iff.mp hz)
    norm_num

theorem kpE_invariants (K : Type) [Field K] (hk : ringChar K ≠ 5) (u : K) (hu : u ≠ 0)
    (hw : Work.MotT.kpW K u ≠ 0) (hΔ : Work.MotT.kpDelta K u ≠ 0) :
    (Work.MotT.kpE K u).IsElliptic ∧
      (Work.MotT.kpE K u).Δ = (Work.MotT.kpDelta K u) ^ 5 / (5 ^ 12 * u ^ 19) ∧
      (Work.MotT.kpE K u).c₄ =
        ((u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1) *
          (u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1) *
          (u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1))
          / (625 * u ^ 8) := by
  have h5 : (5 : K) ≠ 0 := five_ne_zero_of_ringChar_ne hk
  have hDelta : (Work.MotT.kpE K u).Δ =
      (Work.MotT.kpDelta K u) ^ 5 / (5 ^ 12 * u ^ 19) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, Work.MotT.kpE_a1, Work.MotT.kpE_a2, Work.MotT.kpE_a3,
      Work.MotT.kpE_a4, Work.MotT.kpE_a6, Work.MotT.kpA1, Work.MotT.kpA2, Work.MotT.kpA3,
      Work.MotT.kpA4, Work.MotT.kpA6,
      show (125 : K) = (5 : K) ^ 3 by norm_num,
      show (625 : K) = (5 : K) ^ 4 by norm_num,
      show (15625 : K) = (5 : K) ^ 6 by norm_num,
      show (1953125 : K) = (5 : K) ^ 9 by norm_num]
    field_simp [h5, hu, hw]
    simp only [Work.MotT.kpW, Work.MotT.kpDelta]
    first | refl_ring1 | ring
  have hc4 : (Work.MotT.kpE K u).c₄ =
      ((u ^ 4 + 3 * u ^ 3 - u ^ 2 - 3 * u + 1) *
          (u ^ 8 + u ^ 7 + 7 * u ^ 6 - 7 * u ^ 5 + 7 * u ^ 3 + 7 * u ^ 2 - u + 1) *
          (u ^ 8 - 4 * u ^ 7 + 7 * u ^ 6 - 2 * u ^ 5 + 15 * u ^ 4 + 2 * u ^ 3 + 7 * u ^ 2 + 4 * u + 1))
          / (625 * u ^ 8) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      Work.MotT.kpE_a1, Work.MotT.kpE_a2, Work.MotT.kpE_a3, Work.MotT.kpE_a4,
      Work.MotT.kpA1, Work.MotT.kpA2, Work.MotT.kpA3, Work.MotT.kpA4,
      show (125 : K) = (5 : K) ^ 3 by norm_num,
      show (625 : K) = (5 : K) ^ 4 by norm_num,
      show (15625 : K) = (5 : K) ^ 6 by norm_num]
    field_simp [h5, hu, hw]
    simp only [Work.MotT.kpW, Work.MotT.kpDelta]
    first | refl_ring1 | ring
  refine ⟨?_, hDelta, hc4⟩
  rw [WeierstrassCurve.isElliptic_iff, hDelta]
  exact isUnit_iff_ne_zero.mpr
    (div_ne_zero (pow_ne_zero 5 hΔ)
      (mul_ne_zero (pow_ne_zero 12 h5) (pow_ne_zero 19 hu)))

end Work.MotT
