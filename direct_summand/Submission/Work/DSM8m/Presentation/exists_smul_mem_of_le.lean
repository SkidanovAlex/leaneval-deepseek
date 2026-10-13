import Mathlib

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.DSM8m.Presentation

/-- In a finite `A`-subalgebra `S` of a field `L`, every nonzero element `α` divides a nonzero
element of `A`: there are `c ≠ 0` in `A` and `y ∈ S` with `y * α = algebraMap A S c`.

The proof uses that `α` is integral over `A`, so `minpoly A α` is a monic polynomial over `A`
killing `α`; its constant term is nonzero, since otherwise dividing by `X` would produce a monic
polynomial of smaller degree still killing `α`. -/
theorem exists_mul_eq_algebraMap_of_finite (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (S : Subalgebra A L) [Module.Finite A S] {α : S} (hα : α ≠ 0) :
    ∃ (c : A) (y : S), c ≠ 0 ∧ y * α = algebraMap A S c := by
  haveI : Nontrivial A :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := L) (by simpa using congrArg (algebraMap A L) h)⟩⟩
  have hint : IsIntegral A α := IsIntegral.of_finite A α
  set p : Polynomial A := minpoly A α with hp
  have hpmonic : p.Monic := minpoly.monic hint
  have hpaeval : Polynomial.aeval α p = 0 := minpoly.aeval A α
  have hcoeff : p.coeff 0 ≠ 0 := by
    intro h0
    have hsplit : p.divX * Polynomial.X = p := by
      have h := Polynomial.divX_mul_X_add p
      rw [h0, Polynomial.C_0, add_zero] at h
      exact h
    have hdivXmonic : p.divX.Monic :=
      Polynomial.Monic.of_mul_monic_right (Polynomial.monic_X : (Polynomial.X : Polynomial A).Monic)
        (by simpa only [hsplit] using hpmonic)
    have haev : Polynomial.aeval α p.divX = 0 := by
      have h : Polynomial.aeval α p.divX * α = 0 := by
        have hh := hpaeval
        rw [← hsplit, map_mul, Polynomial.aeval_X] at hh
        exact hh
      rcases mul_eq_zero.mp h with h1 | h1
      · exact h1
      · exact absurd h1 hα
    have hle : p.degree ≤ (p.divX).degree := by
      have h := minpoly.min A α hdivXmonic haev
      rw [← hp] at h
      exact h
    have hp_ne : p ≠ 0 := hpmonic.ne_zero
    have hdivX_ne : p.divX ≠ 0 := by
      intro h
      refine hp_ne ?_
      have hh := Polynomial.divX_mul_X_add p
      rw [h, zero_mul, h0, Polynomial.C_0, add_zero] at hh
      exact hh.symm
    have hnd : p.natDegree = (p.divX).natDegree + 1 := by
      have h := Polynomial.Monic.natDegree_mul hdivXmonic
        (Polynomial.monic_X : (Polynomial.X : Polynomial A).Monic)
      rw [hsplit] at h
      rwa [Polynomial.natDegree_X] at h
    have hlt : (p.divX).degree < p.degree := by
      rw [Polynomial.degree_eq_natDegree hp_ne, Polynomial.degree_eq_natDegree hdivX_ne, hnd]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _)
    exact absurd hle (not_le.mpr hlt)
  refine ⟨p.coeff 0, -(Polynomial.aeval α p.divX), hcoeff, ?_⟩
  have h : Polynomial.aeval α p.divX * α + algebraMap A S (p.coeff 0) = 0 := by
    have hh := hpaeval
    rw [← Polynomial.divX_mul_X_add p, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      at hh
    exact hh
  rw [neg_mul, neg_eq_iff_add_eq_zero]
  exact h

theorem exists_smul_mem_of_le (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (R S : Subalgebra A L) [Module.Finite A R] [Module.Finite A S] (hSR : S ≤ R)
    (hS : IsFractionRing S L) :
    ∃ c : A, c ≠ 0 ∧ ∀ r : R, ∃ s : S, (r : L) * algebraMap A L c = (s : L) := by
  haveI : IsLocalization (nonZeroDivisors S) L := hS
  -- generators of `R` as an `A`-module
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := R)
  -- write each generator as a fraction of two elements of `S`
  choose x hx using fun i : Fin n => IsLocalization.surj (nonZeroDivisors S) ((g i : R) : L)
  have hxne : ∀ i : Fin n, ((x i).2 : S) ≠ 0 := fun i h => by
    have hmem : ((x i).2 : S) ∈ nonZeroDivisors S := (x i).2.2
    rw [h] at hmem
    exact zero_notMem_nonZeroDivisors hmem
  -- a common denominator in `S` for the generators
  set t : S := ∏ i : Fin n, ((x i).2 : S) with ht
  have ht_ne : t ≠ 0 := by
    rw [ht, Finset.prod_ne_zero_iff]
    intro i _
    exact hxne i
  -- turn the `S`-denominator into an `A`-denominator
  obtain ⟨c, y, hc, hyt⟩ := exists_mul_eq_algebraMap_of_finite A L S ht_ne
  refine ⟨c, hc, fun r => ?_⟩
  have hgen : ∀ i : Fin n, ∃ u : S, (t : L) * ((g i : R) : L) = (u : L) := by
    intro i
    have hsplit : t = (∏ j ∈ Finset.univ.erase i, ((x j).2 : S)) * ((x i).2 : S) := by
      rw [ht]
      simpa using
        (Finset.prod_erase_mul Finset.univ (fun j => ((x j).2 : S)) (Finset.mem_univ i)).symm
    refine ⟨(∏ j ∈ Finset.univ.erase i, ((x j).2 : S)) * ((x i).1 : S), ?_⟩
    have hxi : (((g i : R) : L)) * (((x i).2 : S) : L) = (((x i).1 : S) : L) := hx i
    have hG : (((x i).2 : S) : L) * ((g i : R) : L) = (((x i).1 : S) : L) := by
      rw [mul_comm, hxi]
    rw [hsplit, Subalgebra.coe_mul, Subalgebra.coe_mul, mul_assoc, hG]
  have hR : ∀ r : R, ∃ u : S, (t : L) * ((r : R) : L) = (u : L) := by
    intro r
    have hr : r ∈ Submodule.span A (Set.range g) := by rw [hg]; trivial
    refine Submodule.span_induction (R := A) (M := R)
      (p := fun x _ => ∃ u : S, (t : L) * (x : L) = (u : L)) ?_ ?_ ?_ ?_ hr
    · rintro x ⟨i, rfl⟩
      exact hgen i
    · exact ⟨0, by rw [Subalgebra.coe_zero, mul_zero, Subalgebra.coe_zero]⟩
    · rintro x y _ _ ⟨ux, hux⟩ ⟨uy, huy⟩
      exact ⟨ux + uy, by
        rw [Subalgebra.coe_add, mul_add, hux, huy, Subalgebra.coe_add]⟩
    · rintro a x _ ⟨ux, hux⟩
      refine ⟨a • ux, ?_⟩
      have hx' : (((a • x : R)) : L) = algebraMap A L a * (x : L) := by
        rw [Subalgebra.coe_smul, Algebra.smul_def]
      have hux' : (((a • ux : S)) : L) = algebraMap A L a * (ux : L) := by
        rw [Subalgebra.coe_smul, Algebra.smul_def]
      rw [hx', hux', ← mul_assoc, mul_comm (t : L) (algebraMap A L a), mul_assoc, hux]
  obtain ⟨u, hu⟩ := hR r
  refine ⟨y * u, ?_⟩
  have h1 : (y : L) * (t : L) = algebraMap A L c := by
    have h := congrArg (algebraMap S L) hyt
    rw [map_mul, ← IsScalarTower.algebraMap_apply A S L c] at h
    exact h
  rw [← h1, Subalgebra.coe_mul, ← hu]
  ring

end Work.DSM8m.Presentation
