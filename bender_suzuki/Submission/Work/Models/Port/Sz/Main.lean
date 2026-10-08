/-
The order of the Suzuki group `Sz(2^(2n+1))`.

Combining the abstract Bruhat assembly (`Submission.Sz.Bruhat`), the existence of the
`(1 + 2^n)`-th root (`Submission.Sz.Root`) and the explicit matrix identity
`Commons.GroupTheory.Suzuki.szW_conj_szU_matrix` (proved in the shared commons), we obtain

* `w * u(a,b) * w ∈ B ∪ B w B` for every root element `u(a,b)`,
* the Bruhat decomposition `SzModel n = B ∪ B w B`,
* the order `|Sz(2^(2n+1))| = q^2 (q - 1) (q^2 + 1)` with `q = 2^(2n+1)`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Bruhat
import Submission.Work.Models.Port.Sz.Root
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szW_conj_szU_matrix

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The Weyl conjugate of a root element lies in `B ∪ B w B`. -/
theorem szWg_conj_szUg_mem (n : ℕ) (a b : SzField n) :
    szWg n * szUg n a b * szWg n ∈ szBwBSet n := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    rw [szUg_zero, mul_one, szWg_mul_self]
    exact Or.inl (szBorel n).one_mem
  · obtain ⟨z, hz0, hz⟩ := sz_exists_root n a b hab
    set c := (a ^ (1 + 2 ^ (n + 1)) + b) / z ^ (1 + 2 ^ n) with hc
    set d := a / z ^ (1 + 2 ^ n) + c ^ (1 + 2 ^ (n + 1)) with hd
    set e := z ^ (1 + 2 ^ n) * d with he
    set f := a * z ^ (2 ^ n) with hf
    have hmatrix := Commons.GroupTheory.Suzuki.szW_conj_szU_matrix n a b z c d e f hz0 hz
      hc.symm hd.symm he.symm hf.symm
    have hGL : szWg n * szUg n a b * szWg n =
        szUg n c d * szWg n * szUg n e f * szTg n (Units.mk0 z hz0) := by
      apply Units.ext
      simpa only [Matrix.GeneralLinearGroup.coe_mul, szWg_coe, szUg_coe, szTg_coe,
        szW, szU, szT, Units.val_mk0] using hmatrix
    rw [hGL]
    exact Or.inr ((mem_szBwB n _).mpr ⟨szUg n c d, Subgroup.mem_sup_left ⟨c, d, rfl⟩,
      szUg n e f * szTg n (Units.mk0 z hz0),
      (szBorel n).mul_mem (Subgroup.mem_sup_left ⟨e, f, rfl⟩)
        (Subgroup.mem_sup_right ⟨Units.mk0 z hz0, rfl⟩), by group⟩)

/-- The Bruhat decomposition for `Sz(2^(2n+1))`: `SzModel n = B ∪ B w B`. -/
theorem szModel_eq_szBwBSubgroup' (n : ℕ) :
    SzModel n = szBwBSubgroup n (fun a b => szWg_conj_szUg_mem n a b) :=
  szModel_eq_szBwBSubgroup n (fun a b => szWg_conj_szUg_mem n a b)

/-- `|Sz(2^(2n+1))| = q^2 (q - 1) (q^2 + 1)` with `q = 2^(2n+1)`. -/
theorem card_szModel_final (n : ℕ) :
    Nat.card (SzModel n) = Nat.card (SzField n) ^ 2 * (Nat.card (SzField n) - 1) *
      (Nat.card (SzField n) ^ 2 + 1) :=
  card_szModel n (fun a b => szWg_conj_szUg_mem n a b)

/-- `|Sz(2^(2n+1))| = 2^(4n+2) * (2^(2n+1) - 1) * (2^(4n+2) + 1)`. -/
theorem card_szModel_final' (n : ℕ) :
    Nat.card (SzModel n) =
      2 ^ (4 * n + 2) * (2 ^ (2 * n + 1) - 1) * (2 ^ (4 * n + 2) + 1) := by
  have hsq : (2 ^ (2 * n + 1)) ^ 2 = 2 ^ (4 * n + 2) := by
    rw [← pow_mul]; congr 1; ring
  rw [card_szModel_final, card_szField, hsq]

/-- `SzModel n = B w B` has index `q^2 + 1` over the Borel subgroup. -/
theorem card_szModel_eq_borel_mul (n : ℕ) :
    Nat.card (SzModel n) = Nat.card (szBorel n) * (Nat.card (SzField n) ^ 2 + 1) := by
  rw [card_szModel_final, card_szBorel]

/-- The Borel subgroup is a proper subgroup of `SzModel n`. -/
theorem szBorel_lt_szModel (n : ℕ) : szBorel n < SzModel n :=
  lt_of_le_of_ne (szBorel_le_szModel n) (fun h => szWg_notMem_szBorel n (h ▸ szWg_mem_szModel n))

/-- `Sz(2^(2n+1))` is one of the three families of the Bender–Suzuki classification. -/
theorem SzModel_isSimpleBenderGroup (n : ℕ) (hn : 1 ≤ n) :
    IsSimpleBenderGroup (SzModel n) :=
  IsSimpleBenderGroup.isSuzuki n hn (MulEquiv.refl _)

end Submission.Sz
