import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Injectivity of the angular eigenvalue `λ_n` on `n ≥ 1`

`eigLam n = 4(n-1)² + 10(n-1)` (`EigBasis.eigLamNat`), so on the index range `n ≥ 1`
it is the strictly increasing quadratic `k ↦ 4k² + 10k` evaluated at `k = n - 1`
(`λ_1 = 0 < λ_2 = 14 < λ_3 = 36 < …`).  Hence `λ_n = λ_m` forces `n = m`, which is what
the assembly needs: the eigenvalues of distinct angular modes are distinct.

The hypothesis `1 ≤ n` is essential: `eigLam 0 = eigLam 1 = 0` (because `0 - 1 = 0` in
`ℕ`), so `eigLam` is not injective on all of `ℕ`.
-/

namespace Work.FTS.EllipticEst.LevelOneAsm

/-- The quadratic `k ↦ 4k² + 10k` is strictly monotone on `ℕ`. -/
theorem strictMono_four_sq_add_ten :
    StrictMono (fun k : ℕ => 4 * k ^ 2 + 10 * k) := by
  apply strictMono_nat_of_lt_succ
  intro k
  nlinarith [Nat.zero_le k]

/-- Iterated form: `4k² + 10k = 4j² + 10j` implies `k = j`. -/
theorem four_sq_add_ten_injective :
    Function.Injective (fun k : ℕ => 4 * k ^ 2 + 10 * k) :=
  strictMono_four_sq_add_ten.injective

/-- `eigLam` is injective on the index range `n ≥ 1`. -/
theorem eigLam_injective_of_one_le {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : Work.FTS.EllipticEst.LevelOneAsm.eigLam n =
      Work.FTS.EllipticEst.LevelOneAsm.eigLam m) :
    n = m := by
  have hnat : eigLamNat n = eigLamNat m := Nat.cast_injective h
  have h3 : n - 1 = m - 1 := four_sq_add_ten_injective hnat
  omega

theorem eigLam_ne_of_ne {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n ≠ m) :
    Work.FTS.EllipticEst.LevelOneAsm.eigLam n ≠ Work.FTS.EllipticEst.LevelOneAsm.eigLam m := by
  intro hc
  exact h (eigLam_injective_of_one_le hn hm hc)

end Work.FTS.EllipticEst.LevelOneAsm
