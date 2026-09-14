import Mathlib
import Submission.Commons.FieldTheory.Polynomial.monic_index_ge_card_le

open Polynomial
open UniqueFactorizationMonoid

namespace Commons.FieldTheory.Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The type of monic polynomials of a fixed degree `n` over `F` satisfying the
index condition is finite: a monic polynomial is determined by its coefficients
below the degree. -/
private lemma finite_index_fiber {F : Type*} [Field F] [Fintype F] [DecidableEq F] (k n : ℕ) :
    Finite {f : F[X] // f.Monic ∧ f.natDegree = n ∧
      k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree} := by
  classical
  haveI : Finite (Fin n → F) := inferInstance
  refine Finite.of_injective
    (fun f : {f : F[X] // f.Monic ∧ f.natDegree = n ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree} =>
      (fun i : Fin n => (f : F[X]).coeff (i : ℕ))) ?_
  intro f₁ f₂ h
  apply Subtype.ext
  refine monic_ext f₁.2.1 f₂.2.1 ?_ ?_
  · rw [f₁.2.2.1, f₂.2.2.1]
  · intro i hi
    have hin : i < n := by rw [← f₁.2.2.1]; exact hi
    exact congrFun h ⟨i, hin⟩

theorem index_card_degree_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (N k : ℕ) (hk : k ≤ N) :
    Nat.card {f : F[X] // f.Monic ∧ 1 ≤ f.natDegree ∧ f.natDegree ≤ N ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree}
      ≤ (N + 1) * 2 ^ ((N + 1) ^ 4) * (Fintype.card F) ^ (N - k) := by
  classical
  let T : ℕ → Type _ := fun n => {f : F[X] // f.Monic ∧ f.natDegree = n ∧
      k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree}
  haveI hTfin : ∀ n : ℕ, Finite (T n) := fun n => finite_index_fiber k n
  have hinj : Nat.card {f : F[X] // f.Monic ∧ 1 ≤ f.natDegree ∧ f.natDegree ≤ N ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree}
      ≤ Nat.card (Σ n : Fin (N + 1), T n) := by
    refine Nat.card_le_card_of_injective
      (fun f : {f : F[X] // f.Monic ∧ 1 ≤ f.natDegree ∧ f.natDegree ≤ N ∧
          k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree} =>
        ⟨⟨f.1.natDegree, Nat.lt_succ_of_le f.2.2.2.1⟩, ⟨f.1, f.2.1, rfl, f.2.2.2.2⟩⟩) ?_
    intro f₁ f₂ h
    apply Subtype.ext
    exact congrArg (fun x : Σ n : Fin (N + 1), T n => ((x.2 : T x.1) : F[X])) h
  have hbound : ∀ n : Fin (N + 1), Nat.card (T n) ≤
      2 ^ ((N + 1) ^ 4) * (Fintype.card F) ^ (N - k) := by
    intro n
    by_cases hkn : k ≤ (n : ℕ)
    · have h := monic_index_ge_card_le (F := F) (n : ℕ) k hkn
      have hn : (n : ℕ) ≤ N := Nat.lt_succ_iff.mp n.2
      refine le_trans h ?_
      apply Nat.mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2)
          (pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ (n : ℕ) + 1) (by omega) 4)
      · exact pow_le_pow_right₀
          (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr (⟨(0 : F)⟩ : Nonempty F)))
          (Nat.sub_le_sub_right hn k)
    · haveI : IsEmpty (T n) := by
        refine ⟨fun f => ?_⟩
        have h1 : k ≤ f.1.natDegree := le_trans f.2.2.2 (Nat.sub_le _ _)
        rw [f.2.2.1] at h1
        exact absurd h1 hkn
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
  calc
    Nat.card {f : F[X] // f.Monic ∧ 1 ≤ f.natDegree ∧ f.natDegree ≤ N ∧
        k ≤ f.natDegree - (((normalizedFactors f).toFinset.prod id : F[X])).natDegree}
        ≤ Nat.card (Σ n : Fin (N + 1), T n) := hinj
    _ = ∑ n : Fin (N + 1), Nat.card (T n) := Nat.card_sigma
    _ ≤ ∑ n : Fin (N + 1), 2 ^ ((N + 1) ^ 4) * (Fintype.card F) ^ (N - k) :=
        Finset.sum_le_sum (fun n _ => hbound n)
    _ = (N + 1) * (2 ^ ((N + 1) ^ 4) * (Fintype.card F) ^ (N - k)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    _ = (N + 1) * 2 ^ ((N + 1) ^ 4) * (Fintype.card F) ^ (N - k) := by ring

end

end Commons.FieldTheory.Polynomial
