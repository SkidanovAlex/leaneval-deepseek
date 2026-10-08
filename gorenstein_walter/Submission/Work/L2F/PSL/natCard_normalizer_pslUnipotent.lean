import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.normalizer_pslUnipotent_card
import Submission.Work.PSL2.Card

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Two elementary facts about `GF(p,k)`

We keep them local (`Main.lean` has public copies, but importing that file would drag in the whole
area, so we redo the two one-liners used here). -/

/-- `5 ≤ p ^ k` forces `k ≠ 0`, hence `GF(p,k)` has `p ^ k` elements (`GaloisField.card`). -/
private lemma card_galois (p k : ℕ) [Fact p.Prime] (hk : 5 ≤ p ^ k) :
    Nat.card (GaloisField p k) = p ^ k :=
  GaloisField.card p k (by rintro rfl; simp at hk)

/-- For an odd prime `p` the field `GF(p,k)` has characteristic `p ≠ 2`, so `2 ≠ 0`. -/
private lemma two_ne_zero_galois (p k : ℕ) [Fact p.Prime] (hp : Odd p) :
    (2 : GaloisField p k) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp2 : p = 2 := le_antisymm hle hge
  obtain ⟨m, hm⟩ := hp
  omega

/-- The normalizer of `pslUnipotent (GF(p,k))` in `PSL(2,GF(p,k))` has order `q(q-1)/2`, `q = p^k`
(`p` an odd prime, `5 ≤ p^k`).  Immediate from `normalizer_pslUnipotent_card`
(`2 * |N(pslUnipotent)| = q(q-1)`) together with the parity of `q`-odd. -/
theorem natCard_normalizer_pslUnipotent {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    Nat.card (Subgroup.normalizer (Work.L2F.pslUnipotent (GaloisField p k) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) =
      p ^ k * (p ^ k - 1) / 2 := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  -- `2 * |N| = q(q-1)` with `q = p^k`
  have h := normalizer_pslUnipotent_card (GaloisField p k) (two_ne_zero_galois p k hp)
  rw [card_galois p k hk] at h
  -- divisibility is automatic: `2 * (q(q-1)/2) = q(q-1)`, and `Nat.eq_div_of_mul_eq_left`
  -- only needs the product equation.
  exact Nat.eq_div_of_mul_eq_left (by norm_num : (2 : ℕ) ≠ 0) (by rw [mul_comm]; exact h)

end Work.L2F.PSL
