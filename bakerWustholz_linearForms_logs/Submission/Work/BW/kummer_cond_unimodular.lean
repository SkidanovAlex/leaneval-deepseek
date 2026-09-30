import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_prod_zpow_even
import Submission.Work.BW.unimodular_even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The Kummer condition is preserved by a unimodular integral change of basis: if `det U = ±1` then
`fun j => ∏ i, β i ^ (U i j)` satisfies the Kummer condition whenever `β` does. -/
theorem kummer_cond_unimodular {K : Type*} [Field K] {n : ℕ} (β : Fin n → K)
    (hβ : KummerCond β) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    KummerCond (fun j => ∏ i, β i ^ (U i j)) := by
  -- `KummerCond` forces every coordinate to be nonzero (otherwise `0` is a square).
  have hβnz : ∀ i, β i ≠ 0 := by
    intro i hi
    have he : (fun k => if k = i then (1 : Fin 2) else 0) ≠ 0 := by
      intro h
      have h2 : (1 : Fin 2) = 0 := by simpa using congrFun h i
      exact absurd h2 (by decide)
    have hprod :
        (∏ j, β j ^ (((fun k => if k = i then (1 : Fin 2) else 0) j) : ℕ)) = β i := by
      rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
        (fun hi' => absurd (Finset.mem_univ i) hi')]
      simp
    exact (hβ (fun k => if k = i then (1 : Fin 2) else 0) he)
      ⟨0, by rw [hprod, hi]; ring⟩
  intro e he hsq
  -- Rewrite the failing square into a single product with integral exponents.
  have hprod_id : (∏ j, (∏ i, β i ^ (U i j)) ^ (e j : ℕ))
      = ∏ i, β i ^ (∑ j, U i j * (e j : ℤ)) := by
    have hsum : ∀ i : Fin n,
        (∏ j, β i ^ (U i j * (e j : ℤ))) = β i ^ (∑ j, U i j * (e j : ℤ)) := by
      intro i
      induction (Finset.univ : Finset (Fin n)) using Finset.induction with
      | empty => simp
      | insert x s hxs ih =>
          rw [Finset.prod_insert hxs, Finset.sum_insert hxs, ih, zpow_add₀ (hβnz i)]
    calc ∏ j, (∏ i, β i ^ (U i j)) ^ (e j : ℕ)
        = ∏ j, ∏ i, (β i ^ (U i j)) ^ (e j : ℕ) := by
          apply Finset.prod_congr rfl; intro j _; rw [Finset.prod_pow]
      _ = ∏ j, ∏ i, β i ^ (U i j * (e j : ℤ)) := by
          apply Finset.prod_congr rfl; intro j _
          apply Finset.prod_congr rfl; intro i _
          rw [← zpow_natCast (β i ^ U i j) (e j : ℕ), ← zpow_mul]
      _ = ∏ i, ∏ j, β i ^ (U i j * (e j : ℤ)) := Finset.prod_comm
      _ = ∏ i, β i ^ (∑ j, U i j * (e j : ℤ)) := Finset.prod_congr rfl (fun i _ => hsum i)
  rw [hprod_id] at hsq
  -- Generalized Kummer: all exponents are even.
  have heven : ∀ i, (2 : ℤ) ∣ ∑ j, U i j * (e j : ℤ) :=
    kummer_prod_zpow_even β hβnz hβ (fun i => ∑ j, U i j * (e j : ℤ)) hsq
  -- Unimodularity: `U` is invertible mod 2, so `e` itself is even.
  have hxe : ∀ i, (2 : ℤ) ∣ (U.mulVec (fun j => (e j : ℤ))) i := by
    intro i
    rw [Matrix.mulVec_apply_eq_sum]
    exact heven i
  have hx := unimodular_even U hU (fun j => (e j : ℤ)) hxe
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra hcon
    apply he
    funext j
    by_contra hj
    exact hcon ⟨j, hj⟩
  have hj1 : (e j : ℤ) = 1 := by
    have hlt : (e j : ℕ) < 2 := (e j).isLt
    have hne : (e j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext (by simpa using h0))
    have hval : (e j : ℕ) = 1 := by omega
    exact_mod_cast hval
  have hdvd := hx j
  rw [hj1] at hdvd
  exact absurd hdvd (by norm_num)

end Work.BW
