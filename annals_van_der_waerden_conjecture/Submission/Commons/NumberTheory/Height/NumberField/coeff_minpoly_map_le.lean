import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.Height.NumberField

open Polynomial IntermediateField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- Bound on the norm of a product of complex numbers each of norm `≤ B`. -/
lemma norm_multiset_prod_le_pow {t : Multiset ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ t, ‖x‖ ≤ B) : ‖t.prod‖ ≤ B ^ t.card := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
      have ha : ‖a‖ ≤ B := h a (Multiset.mem_cons_self a s)
      have hs : ∀ x ∈ s, ‖x‖ ≤ B := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      calc
        ‖a * s.prod‖ = ‖a‖ * ‖s.prod‖ := norm_mul _ _
        _ ≤ B * B ^ s.card := mul_le_mul ha (ih hs) (norm_nonneg _) hB
        _ = B ^ s.card * B := mul_comm _ _

/-- Bound on the norm of the `k`-th elementary symmetric function of a multiset of
complex numbers each of norm `≤ B`. -/
lemma norm_esymm_le {m : Multiset ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ x ∈ m, ‖x‖ ≤ B) (k : ℕ) :
    ‖m.esymm k‖ ≤ (m.card.choose k : ℝ) * B ^ k := by
  rw [Multiset.esymm]
  refine (norm_multiset_sum_le _).trans ?_
  simp only [Multiset.map_map, Function.comp_apply]
  have key : ∀ x ∈ (m.powersetCard k).map (fun t => ‖t.prod‖), x ≤ B ^ k := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hsub : t ≤ m := (Multiset.mem_powersetCard.mp ht).1
    have hcard : t.card = k := (Multiset.mem_powersetCard.mp ht).2
    rw [← hcard]
    exact norm_multiset_prod_le_pow hB (fun y hy => hm y (Multiset.mem_of_le hsub hy))
  have := Multiset.sum_le_card_nsmul ((m.powersetCard k).map (fun t => ‖t.prod‖)) (B ^ k) key
  rw [Multiset.card_map, Multiset.card_powersetCard, nsmul_eq_mul] at this
  exact this

theorem coeff_minpoly_map_le {K : Type*} [Field K] [NumberField K] (α : K) {B : ℝ}
    (hB : 1 ≤ B) (h : ∀ σ : K →+* ℂ, ‖σ α‖ ≤ B) (s : ℕ) :
    ‖((minpoly ℚ α).map (algebraMap ℚ ℂ)).coeff s‖
      ≤ 2 ^ Module.finrank ℚ K * B ^ Module.finrank ℚ K := by
  classical
  set P : Polynomial ℂ := (minpoly ℚ α).map (algebraMap ℚ ℂ) with hP
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  have hα : IsAlgebraic ℚ α := Algebra.IsAlgebraic.isAlgebraic α
  have hαint : IsIntegral ℚ α := hα.isIntegral
  -- Every complex root of the minimal polynomial is a conjugate of `α`.
  have hroot_bound : ∀ x ∈ P.roots, ‖x‖ ≤ B := by
    intro x hx
    have hx' : x ∈ (minpoly ℚ α).aroots ℂ := by
      rw [hP] at hx
      rwa [← Polynomial.aroots_def (minpoly ℚ α) ℂ] at hx
    letI : Algebra ℚ ↥(ℚ⟮α⟯) := IntermediateField.algebra' (R' := ℚ) (ℚ⟮α⟯)
    haveI : Algebra.IsAlgebraic (↥(ℚ⟮α⟯)) K :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) (A := K) (L := ↥(ℚ⟮α⟯))
    obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ)
      (L := ↥(ℚ⟮α⟯)) (M := ℂ) (E := K)
      ((IntermediateField.algHomAdjoinIntegralEquiv (F := ℚ) (E := K) (K := ℂ) hαint).symm
        ⟨x, hx'⟩)
    have hgen := congrArg (fun f : ↥(ℚ⟮α⟯) →ₐ[ℚ] ℂ =>
      f (IntermediateField.AdjoinSimple.gen ℚ α)) hφ
    dsimp only at hgen
    rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (F := ℚ) (h := hαint)
      (x := ⟨x, hx'⟩)] at hgen
    simp only [AlgHom.domRestrict, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      IntermediateField.AdjoinSimple.algebraMap_gen] at hgen
    simpa [hgen] using h φ.toRingHom
  -- The degree of the minimal polynomial is at most `[K : ℚ]`.
  have hPn : P.natDegree ≤ Module.finrank ℚ K := by
    rw [hP, (minpoly.monic hαint).natDegree_map (algebraMap ℚ ℂ)]
    exact minpoly.natDegree_le α
  by_cases hs : s ≤ P.natDegree
  · have hsplit : P.Splits := IsAlgClosed.splits P
    have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hs
    have hmonic : P.Monic := (minpoly.monic hαint).map (algebraMap ℚ ℂ)
    rw [hcoeff, hmonic.leadingCoeff, one_mul, norm_mul]
    have h1 : ‖(-1 : ℂ) ^ (P.natDegree - s)‖ = 1 := by simp
    rw [h1, one_mul]
    have hesymm := norm_esymm_le hB0 hroot_bound (P.natDegree - s)
    refine hesymm.trans ?_
    rw [IsAlgClosed.card_roots_eq_natDegree]
    have hk_le : P.natDegree - s ≤ Module.finrank ℚ K :=
      le_trans (Nat.sub_le _ _) hPn
    have hchoose : ((P.natDegree.choose (P.natDegree - s) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ Module.finrank ℚ K := by
      have h1' : P.natDegree.choose (P.natDegree - s) ≤ 2 ^ P.natDegree :=
        Nat.choose_le_two_pow _ _
      have h2' : 2 ^ P.natDegree ≤ 2 ^ Module.finrank ℚ K :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hPn
      exact_mod_cast le_trans h1' h2'
    have hBk : B ^ (P.natDegree - s) ≤ B ^ Module.finrank ℚ K := pow_le_pow_right₀ hB hk_le
    calc (P.natDegree.choose (P.natDegree - s) : ℝ) * B ^ (P.natDegree - s)
        ≤ (2 : ℝ) ^ Module.finrank ℚ K * B ^ Module.finrank ℚ K :=
          mul_le_mul hchoose hBk (pow_nonneg hB0 _) (pow_nonneg (by norm_num) _)
      _ = 2 ^ Module.finrank ℚ K * B ^ Module.finrank ℚ K := rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hs)]
    simp only [norm_zero]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hB0 _)

end Commons.NumberTheory.Height.NumberField