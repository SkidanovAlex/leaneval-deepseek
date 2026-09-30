import Mathlib
import Submission.Work.BW.monomialDefs
import Submission.Work.BW.exists_finset_card_finrank_linearIndepOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of a monomial basis with bounded exponents

If `β : Fin n → F` generates a number field `F` over `ℚ`, then there are
`d = Module.finrank ℚ F` distinct monomials `∏ i, β i ^ (e j i)` with all exponents
`e j i < d` that are `ℚ`-linearly independent.

The proof has two halves:

* the *unrestricted* monomials `allMono β e` (`e : Fin n → ℕ`) span `F` because the
  subalgebra `ℚ[β]` is a finite-dimensional subalgebra of the field `F`, hence a field,
  hence contains the field `ℚ(β) = F` (`span_allMono_eq_top`);
* every monomial is a `ℚ`-linear combination of monomials with exponents `< d`, because
  each `β i` is algebraic of degree `≤ d` over `ℚ` (`range_allMono_subset_span_bMono`).

From these, finitely many bounded monomials span `F`, and since `F` has dimension `d`,
some `d` of them are linearly independent (`exists_finset_card_finrank_linearIndepOn`).
-/

namespace Work.BW

open scoped BigOperators

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- The monomial `allMono β (Function.update e i v)` is the product of all monomial factors of
`allMono β e` except the `i`-th, times `β i ^ v`. -/
lemma allMono_update (β : Fin n → F) (e : Fin n → ℕ) (i : Fin n) (v : ℕ) :
    allMono β (Function.update e i v)
      = (∏ j ∈ Finset.univ.erase i, β j ^ e j) * (β i) ^ v := by
  rw [allMono, ← Finset.prod_erase_mul Finset.univ
      (fun j => β j ^ (Function.update e i v) j) (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1]
  · rw [Function.update_self]

/-- `allMono β e` is the product of all monomial factors except the `i`-th, times `β i ^ (e i)`. -/
lemma allMono_eq_prod_erase (β : Fin n → F) (e : Fin n → ℕ) (i : Fin n) :
    allMono β e = (∏ j ∈ Finset.univ.erase i, β j ^ e j) * (β i) ^ (e i) := by
  rw [allMono, ← Finset.prod_erase_mul Finset.univ (fun j => β j ^ e j) (Finset.mem_univ i)]

/-- If `β` generates `F` over `ℚ`, the unrestricted monomials span `F`. -/
theorem span_allMono_eq_top (β : Fin n → F)
    (hgen : IntermediateField.adjoin ℚ (Set.range β) = ⊤) :
    Submodule.span ℚ (Set.range (allMono β)) = ⊤ := by
  have hA : Algebra.adjoin ℚ (Set.range β) = ⊤ :=
    IntermediateField.adjoin_eq_top_iff.mp hgen
  have hspan : Submodule.span ℚ (↑(Submonoid.closure (Set.range β)) : Set F) = ⊤ := by
    rw [← Algebra.adjoin_eq_span ℚ (Set.range β), hA, Algebra.top_toSubmodule]
  have hclosure : (↑(Submonoid.closure (Set.range β)) : Set F) ⊆ Set.range (allMono β) := by
    have hle : Submonoid.closure (Set.range β) ≤
        ({ carrier := Set.range (allMono β)
           one_mem' := ⟨0, allMono_zero β⟩
           mul_mem' := by
             rintro _ _ ⟨e, rfl⟩ ⟨e', rfl⟩
             exact ⟨e + e', allMono_add β e e'⟩ } : Submonoid F) :=
      Submonoid.closure_le.mpr (by
        rintro x ⟨i, rfl⟩
        exact ⟨Function.update 0 i 1, allMono_update_zero β i⟩)
    intro x hx
    exact hle hx
  rw [eq_top_iff]
  calc ⊤ = Submodule.span ℚ (↑(Submonoid.closure (Set.range β)) : Set F) := hspan.symm
    _ ≤ Submodule.span ℚ (Set.range (allMono β)) := Submodule.span_mono hclosure

/-- Every monomial is a `ℚ`-linear combination of monomials with all exponents `< finrank ℚ F`. -/
theorem range_allMono_subset_span_bMono (β : Fin n → F) :
    Set.range (allMono β) ⊆ Submodule.span ℚ (Set.range (bMono β)) := by
  classical
  set S : Submodule ℚ F := Submodule.span ℚ (Set.range (bMono β))
  -- Each `β i` satisfies a monic relation of degree `m ≤ finrank ℚ F`.
  have hrel : ∀ i : Fin n, ∃ m : ℕ, 0 < m ∧ m ≤ Module.finrank ℚ F ∧ ∃ c : ℕ → ℚ,
      (β i) ^ m = ∑ k ∈ Finset.range m, c k • (β i) ^ k := by
    intro i
    have hint : IsIntegral ℚ (β i) := Algebra.IsIntegral.isIntegral (β i)
    refine ⟨(minpoly ℚ (β i)).natDegree, minpoly.natDegree_pos hint, minpoly.natDegree_le (β i),
      fun k => -((minpoly ℚ (β i)).coeff k), ?_⟩
    have hmonic : (minpoly ℚ (β i)).Monic := minpoly.monic hint
    have haeval : (Polynomial.aeval (β i)) (minpoly ℚ (β i)) = 0 := minpoly.aeval ℚ (β i)
    rw [Polynomial.aeval_eq_sum_range] at haeval
    rw [Finset.sum_range_succ] at haeval
    rw [hmonic.coeff_natDegree, one_smul] at haeval
    have heq : (β i) ^ (minpoly ℚ (β i)).natDegree
        = -∑ k ∈ Finset.range (minpoly ℚ (β i)).natDegree,
            (minpoly ℚ (β i)).coeff k • (β i) ^ k := by
      rw [add_comm] at haeval
      exact eq_neg_of_add_eq_zero_left haeval
    have heq2 : -∑ k ∈ Finset.range (minpoly ℚ (β i)).natDegree,
          (minpoly ℚ (β i)).coeff k • (β i) ^ k
        = ∑ k ∈ Finset.range (minpoly ℚ (β i)).natDegree,
            (-((minpoly ℚ (β i)).coeff k)) • (β i) ^ k := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [← neg_smul])
    exact heq.trans heq2
  -- Strong induction on the total degree.
  have key : ∀ M, ∀ e : Fin n → ℕ, (∑ i, e i) = M → allMono β e ∈ S := by
    intro M
    refine Nat.strong_induction_on M ?_
    intro N ih e he
    by_cases hbdd : ∀ i, e i < Module.finrank ℚ F
    · have heq : allMono β e = bMono β (fun i => ⟨e i, hbdd i⟩) := rfl
      rw [heq]
      exact Submodule.subset_span ⟨fun i => ⟨e i, hbdd i⟩, rfl⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hbdd
      have hi' : Module.finrank ℚ F ≤ e i := not_lt.mp hi
      obtain ⟨m, hmpos, hmle, c, hc⟩ := hrel i
      have hm : m ≤ e i := le_trans hmle hi'
      have hpow : (β i) ^ (e i)
          = ∑ k ∈ Finset.range m, c k • ((β i) ^ (e i - m) * (β i) ^ k) := by
        calc (β i) ^ (e i)
            = (β i) ^ (e i - m + m) := by rw [Nat.sub_add_cancel hm]
          _ = (β i) ^ (e i - m) * (β i) ^ m := by rw [pow_add]
          _ = (β i) ^ (e i - m) * (∑ k ∈ Finset.range m, c k • (β i) ^ k) := by rw [hc]
          _ = ∑ k ∈ Finset.range m, c k • ((β i) ^ (e i - m) * (β i) ^ k) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun k _ =>
                  (Algebra.mul_smul_comm (c k) ((β i) ^ (e i - m)) ((β i) ^ k)))
      have hidentity : allMono β e
          = ∑ k ∈ Finset.range m, c k • allMono β (Function.update e i (e i - m + k)) := by
        rw [allMono_eq_prod_erase β e i, hpow, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Algebra.mul_smul_comm, ← pow_add, ← allMono_update β e i (e i - m + k)]
      rw [hidentity]
      refine Submodule.sum_mem S (fun k hk => ?_)
      refine Submodule.smul_mem S (c k) ?_
      have hk' : k < m := Finset.mem_range.mp hk
      have hlt : (∑ j, (Function.update e i (e i - m + k)) j) < N := by
        rw [← he]
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
        · rw [Function.update_apply]
          split_ifs with h
          · rw [h]; omega
          · exact le_rfl
        · rw [Function.update_self]; omega
      exact ih (∑ j, (Function.update e i (e i - m + k)) j) hlt _ rfl
  rintro _ ⟨e, rfl⟩
  exact key (∑ i, e i) e rfl

theorem exists_monomial_basis {F : Type*} [Field F] [NumberField F] {n : ℕ} (β : Fin n → F)
    (hgen : IntermediateField.adjoin ℚ (Set.range β) = ⊤) :
    ∃ (m : Fin (Module.finrank ℚ F) → F) (e : Fin (Module.finrank ℚ F) → Fin n → ℕ),
      (∀ j, m j = ∏ i, β i ^ (e j i)) ∧
      (∀ j i, e j i < Module.finrank ℚ F) ∧
      LinearIndependent ℚ m := by
  classical
  have hspan_all : Submodule.span ℚ (Set.range (allMono β)) = ⊤ := span_allMono_eq_top β hgen
  have hsubset : Set.range (allMono β) ⊆ Submodule.span ℚ (Set.range (bMono β)) :=
    range_allMono_subset_span_bMono β
  have htop : Submodule.span ℚ (Set.range (bMono β)) = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = Submodule.span ℚ (Set.range (allMono β)) := hspan_all.symm
      _ ≤ Submodule.span ℚ (Set.range (bMono β)) := (Submodule.span_le).mpr hsubset
  have hfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (bMono β)))
      = Module.finrank ℚ F := by
    rw [htop, finrank_top]
  obtain ⟨s, hcard, hind⟩ := exists_finset_card_finrank_linearIndepOn (K := ℚ) (v := bMono β)
      (n := Module.finrank ℚ F) hfin
  let φ : ↥s ≃ Fin (Module.finrank ℚ F) := Finset.equivFinOfCardEq hcard
  let g : Fin (Module.finrank ℚ F) → (Fin n → Fin (Module.finrank ℚ F)) :=
    fun j => (φ.symm j : Fin n → Fin (Module.finrank ℚ F))
  refine ⟨fun j => bMono β (g j), fun j i => (g j i : ℕ), ?_, ?_, ?_⟩
  · intro j; rfl
  · intro j i; exact (g j i).isLt
  · exact hind.comp φ.symm φ.symm.injective

end Work.BW
