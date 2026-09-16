import Submission.ZagierHoffmanProof.StepB5
import Submission.Commons.Data.Finset.sum_range_mul_split

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B6: depth-one `S_<d` products (paper (2.4), base case)

For monic polynomials of degree `< d`, splitting pairs by their degrees gives the
depth-(1,1) `S_<d` product recursion:

`S_<d(x)·S_<d(y) = S_<d(x,y) + S_<d(y,x) + Σ_{ℓ<d} S_ℓ(x)·S_ℓ(y)`,

where the last term (the equal-degree diagonal) is expanded later by
`thakur_prod_one` at each level `ℓ` to obtain the full depth-one stuffle.  The proof
uses the level decomposition `S_lt_eq_sum_levels` and the generic prefix-split
`Commons.Data.Finset.sum_range_mul_split`.
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma S_lt_one_mul_one (d : ℕ) (x y : ℕ+) :
    S_lt F 1 (by omega) (fun _ : Fin 1 => x) d * S_lt F 1 (by omega) (fun _ : Fin 1 => y) d =
      S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then x else y) d +
      S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then y else x) d +
      ∑ ℓ ∈ Finset.range d,
        S F 1 (by omega) (fun _ : Fin 1 => x) ℓ * S F 1 (by omega) (fun _ : Fin 1 => y) ℓ := by
  classical
  let 𝔰x : Fin 1 → ℕ+ := fun _ => x
  let 𝔰y : Fin 1 → ℕ+ := fun _ => y
  let 𝔰xy : Fin 2 → ℕ+ := fun j => if (j : ℕ) = 0 then x else y
  let 𝔰yx : Fin 2 → ℕ+ := fun j => if (j : ℕ) = 0 then y else x
  have hrecxy (ℓ : ℕ) : S F 2 (by omega) 𝔰xy ℓ = P F ℓ x * S_lt F 1 (by omega) 𝔰y ℓ := by
    rw [S_d_recursion F 2 (by omega) (by omega) (by omega) 𝔰xy ℓ]
    congr 1
  have hrecyx (ℓ : ℕ) : S F 2 (by omega) 𝔰yx ℓ = P F ℓ y * S_lt F 1 (by omega) 𝔰x ℓ := by
    rw [S_d_recursion F 2 (by omega) (by omega) (by omega) 𝔰yx ℓ]
    congr 1
  have hA : (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ,
        S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m) =
      S_lt F 2 (by omega) 𝔰xy d := by
    calc
      (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m)
          = ∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ * (∑ m ∈ Finset.range ℓ, S F 1 (by omega) 𝔰y m) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact (Finset.mul_sum (s := Finset.range ℓ) (f := fun m : ℕ => S F 1 (by omega) 𝔰y m)
              (a := S F 1 (by omega) 𝔰x ℓ)).symm
      _ = ∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ * S_lt F 1 (by omega) 𝔰y ℓ := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [← S_lt_eq_sum_levels F 1 (by omega) 𝔰y ℓ]
      _ = ∑ ℓ ∈ Finset.range d, S F 2 (by omega) 𝔰xy ℓ := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [S_one_eq_P F ℓ (by omega) 𝔰x]
            exact (hrecxy ℓ).symm
      _ = S_lt F 2 (by omega) 𝔰xy d := by
            rw [S_lt_eq_sum_levels F 2 (by omega) 𝔰xy d]
  have hB : (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m,
        S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m) =
      S_lt F 2 (by omega) 𝔰yx d := by
    calc
      (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m)
          = ∑ m ∈ Finset.range d, S F 1 (by omega) 𝔰y m * (∑ ℓ ∈ Finset.range m, S F 1 (by omega) 𝔰x ℓ) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            ring
      _ = ∑ m ∈ Finset.range d, S F 1 (by omega) 𝔰y m * S_lt F 1 (by omega) 𝔰x m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [← S_lt_eq_sum_levels F 1 (by omega) 𝔰x m]
      _ = ∑ m ∈ Finset.range d, S F 2 (by omega) 𝔰yx m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [S_one_eq_P F m (by omega) 𝔰y]
            exact (hrecyx m).symm
      _ = S_lt F 2 (by omega) 𝔰yx d := by
            rw [S_lt_eq_sum_levels F 2 (by omega) 𝔰yx d]
  calc
    S_lt F 1 (by omega) 𝔰x d * S_lt F 1 (by omega) 𝔰y d
        = (∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ) * (∑ m ∈ Finset.range d, S F 1 (by omega) 𝔰y m) := by
          rw [S_lt_eq_sum_levels F 1 (by omega) 𝔰x d, S_lt_eq_sum_levels F 1 (by omega) 𝔰y d]
    _ = (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m) +
        (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y m) +
        (∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y ℓ) := by
          exact Commons.Data.Finset.sum_range_mul_split (R := RatFunc.CompletionAtInfty F) d
            (fun ℓ => S F 1 (by omega) 𝔰x ℓ) (fun m => S F 1 (by omega) 𝔰y m)
    _ = S_lt F 2 (by omega) 𝔰xy d + S_lt F 2 (by omega) 𝔰yx d +
        (∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y ℓ) := by
          rw [hA, hB]
    _ = S_lt F 2 (by omega) 𝔰xy d + S_lt F 2 (by omega) 𝔰yx d +
        ∑ ℓ ∈ Finset.range d,
          S F 1 (by omega) (fun _ : Fin 1 => x) ℓ * S F 1 (by omega) (fun _ : Fin 1 => y) ℓ := by
          congr 1
    _ = S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then x else y) d +
        S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then y else x) d +
        ∑ ℓ ∈ Finset.range d,
          S F 1 (by omega) (fun _ : Fin 1 => x) ℓ * S F 1 (by omega) (fun _ : Fin 1 => y) ℓ := by
          congr 2
end ZagierHoffmanPositiveChar
