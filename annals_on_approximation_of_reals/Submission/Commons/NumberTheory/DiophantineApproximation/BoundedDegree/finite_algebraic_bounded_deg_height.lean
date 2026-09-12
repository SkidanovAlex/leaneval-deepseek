import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.DiophantineApproximation.BoundedDegree.minpoly_leading_coeff_eq_one

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open scoped BigOperators
open Polynomial

private lemma num_natAbs_le_mul_num (c : ℚ) (D : ℕ) (hDdiv : c.den ∣ D) (hDpos : 0 < D) :
    c.num.natAbs ≤ (D * c).num.natAbs := by
  let m : ℕ := D / c.den
  have hD : D = c.den * m := by
    dsimp [m]
    rw [Nat.mul_comm, Nat.div_mul_cancel hDdiv]
  have hden_le_D : c.den ≤ D := Nat.le_of_dvd hDpos hDdiv
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.div_pos hden_le_D (Rat.den_pos c)
  have hden_ne : (c.den : ℚ) ≠ 0 := by exact_mod_cast (Rat.den_pos c).ne'
  have hdenc : (c.den : ℚ) * c = (c.num : ℚ) := by
    calc
      (c.den : ℚ) * c = (c.den : ℚ) * ((c.num : ℚ) / (c.den : ℚ)) := by
        rw [Rat.num_div_den c]
      _ = (c.num : ℚ) := mul_div_cancel₀ (a := (c.num : ℚ)) (b := (c.den : ℚ)) hden_ne
  have hEqRat : (D : ℚ) * c = (m : ℚ) * (c.num : ℚ) := by
    calc
      (D : ℚ) * c = (↑(c.den * m) : ℚ) * c := by rw [hD]
      _ = ((c.den : ℚ) * (m : ℚ)) * c := by rw [Nat.cast_mul]
      _ = (m : ℚ) * ((c.den : ℚ) * c) := by ring
      _ = (m : ℚ) * (c.num : ℚ) := by rw [hdenc]
  have hEqRat2 : (D : ℚ) * c = (↑(c.num * (m : ℤ)) : ℚ) := by
    rw [hEqRat]
    norm_num [Int.cast_mul, mul_comm]
  have hnum : (D * c).num = c.num * (m : ℤ) := by
    rw [hEqRat2]
    exact Rat.num_intCast (c.num * (m : ℤ))
  have hna : (D * c).num.natAbs = c.num.natAbs * m := by
    rw [hnum]
    rw [Int.natAbs_mul]
    rw [Int.natAbs_natCast]
  rw [hna]
  rw [mul_comm]
  exact Nat.le_mul_of_pos_left c.num.natAbs (by omega)

private lemma bounded_rat_finite (h : ℕ) : {c : ℚ | c.num.natAbs ≤ h ∧ c.den ≤ h + 1}.Finite := by
  let A : Finset ℤ := Finset.Icc (-(h : ℤ)) (h : ℤ)
  let B : Finset ℕ := Finset.range (h + 2)
  let S : Finset ℚ := (A.product B).image (fun ab : ℤ × ℕ => (ab.1 : ℚ) / (ab.2 : ℕ))
  have hmem_Icc : ∀ a : ℤ, a.natAbs ≤ h → a ∈ Finset.Icc (-(h : ℤ)) (h : ℤ) := by
    intro a ha
    rw [Finset.mem_Icc]
    have h' : (a.natAbs : ℤ) ≤ (h : ℤ) := by exact_mod_cast ha
    constructor
    · calc
        -(h : ℤ) ≤ -|a| := neg_le_neg (by simpa [Int.natCast_natAbs] using h')
        _ ≤ a := neg_abs_le a
    · calc
        a ≤ |a| := le_abs_self a
        _ ≤ (h : ℤ) := by simpa [Int.natCast_natAbs] using h'
  have hsub : {c : ℚ | c.num.natAbs ≤ h ∧ c.den ≤ h + 1} ⊆ (S : Set ℚ) := by
    intro c hc
    rcases hc with ⟨hcn, hcd⟩
    change c ∈ S
    rw [Finset.mem_image]
    refine ⟨(c.num, c.den), ?_, ?_⟩
    · change (c.num, c.den) ∈ A ×ˢ B
      rw [Finset.mem_product]
      constructor
      · exact hmem_Icc c.num hcn
      · change c.den ∈ B
        rw [Finset.mem_range]
        omega
    · exact Rat.num_div_den c
  exact (S.finite_toSet).subset hsub

private lemma minpoly_coeff_mem_bounded (h : ℕ) {α : ℂ} (hα : IsAlgebraic ℚ α)
    (hH : (let p := minpoly ℚ α;
           let D := Multiset.lcm (Multiset.map (fun i : ℕ ↦ (p.coeff i).den) p.support.val);
           Finset.sup p.support (fun i : ℕ ↦ (D * p.coeff i).num.natAbs) : ℕ) ≤ h)
    (i : ℕ) : (minpoly ℚ α).coeff i ∈ {c : ℚ | c.num.natAbs ≤ h ∧ c.den ≤ h + 1} := by
  let p : Polynomial ℚ := minpoly ℚ α
  let D : ℕ := Multiset.lcm (Multiset.map (fun j : ℕ => (p.coeff j).den) p.support.val)
  change p.coeff i ∈ {c : ℚ | c.num.natAbs ≤ h ∧ c.den ≤ h + 1}
  have hH' : (p.support.sup (fun j : ℕ => (D * p.coeff j).num.natAbs) : ℕ) ≤ h := by
    simpa [p, D] using hH
  by_cases hi : i ∈ p.support
  · have hp_ne : p ≠ 0 := (minpoly.monic (IsAlgebraic.isIntegral hα)).ne_zero
    have hmem_dvd : (p.coeff i).den ∣ D := by
      dsimp [D]
      exact Multiset.dvd_lcm (Multiset.mem_map.mpr ⟨i, hi, rfl⟩)
    have hD_ne : D ≠ 0 := by
      dsimp [D]
      exact (Multiset.lcm_ne_zero_iff _).2 (by
        intro hz
        rcases Multiset.mem_map.mp hz with ⟨j, hj, hden⟩
        have hpos : 0 < (p.coeff j).den := Rat.den_pos (p.coeff j)
        omega)
    have hden_le_D : (p.coeff i).den ≤ D := Nat.le_of_dvd (Nat.pos_of_ne_zero hD_ne) hmem_dvd
    have hd_mem : p.natDegree ∈ p.support := by
      rw [Polynomial.mem_support_iff]
      rw [Polynomial.coeff_natDegree]
      exact (Polynomial.leadingCoeff_ne_zero.mpr hp_ne)
    have hD_le_h : D ≤ h := by
      have hterm_le :
          (D * p.coeff p.natDegree).num.natAbs ≤
            p.support.sup (fun j : ℕ => (D * p.coeff j).num.natAbs) :=
        Finset.le_sup (f := fun j : ℕ => (D * p.coeff j).num.natAbs) hd_mem
      have hterm : (D * p.coeff p.natDegree).num.natAbs = D := by
        have hc1 : p.coeff p.natDegree = 1 := by
          simpa [p] using minpoly_leading_coeff_eq_one α hα
        simp [hc1]
      rw [hterm] at hterm_le
      exact le_trans hterm_le hH'
    have hnum_le_h : (p.coeff i).num.natAbs ≤ h := by
      have htermi_le :
          (D * p.coeff i).num.natAbs ≤
            p.support.sup (fun j : ℕ => (D * p.coeff j).num.natAbs) :=
        Finset.le_sup (f := fun j : ℕ => (D * p.coeff j).num.natAbs) hi
      have hnum_le : (p.coeff i).num.natAbs ≤ (D * p.coeff i).num.natAbs :=
        num_natAbs_le_mul_num (p.coeff i) D hmem_dvd (Nat.pos_of_ne_zero hD_ne)
      exact le_trans hnum_le (le_trans htermi_le hH')
    exact ⟨hnum_le_h, by
      have hden_le_h : (p.coeff i).den ≤ h := le_trans hden_le_D hD_le_h
      omega⟩
  · have hzero : p.coeff i = 0 := by
      by_contra h
      exact hi (Polynomial.mem_support_iff.mpr h)
    rw [hzero]
    simp

/-- There are finitely many algebraic numbers of degree at most `n` whose naive height
(the maximum absolute value of the numerators of the coefficients of the minimal
polynomial after clearing denominators) is at most `h`. -/
theorem finite_algebraic_bounded_deg_height (n h : ℕ) :
    {α : ℂ | IsAlgebraic ℚ α ∧ Polynomial.natDegree (minpoly ℚ α) ≤ n ∧
      (let p := minpoly ℚ α;
       let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
       Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) ≤ h}.Finite := by
  let U : Set ℚ := {c : ℚ | c.num.natAbs ≤ h ∧ c.den ≤ h + 1}
  have hU : U.Finite := by
    simpa [U] using (bounded_rat_finite h)
  have hUnion : (⋃ (f : Polynomial ℚ) (_ : f.natDegree ≤ n ∧ ∀ i, f.coeff i ∈ U),
      ((f.map (algebraMap ℚ ℂ)).roots.toFinset : Set ℂ)).Finite := by
    simpa [U] using
      (Polynomial.bUnion_roots_finite (R := ℚ) (S := ℂ) (algebraMap ℚ ℂ) n hU)
  refine hUnion.subset ?_
  intro α hα
  rcases hα with ⟨hαalg, hdeg, hH⟩
  let p : Polynomial ℚ := minpoly ℚ α
  have hcoeffU : ∀ i : ℕ, p.coeff i ∈ U := by
    intro i
    have hi' := minpoly_coeff_mem_bounded h hαalg hH i
    simpa [p, U] using hi'
  refine Set.mem_iUnion.mpr ⟨p, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨hdeg, hcoeffU⟩, ?_⟩
  -- α is a root of p
  have hp_ne : p ≠ 0 := (minpoly.monic (IsAlgebraic.isIntegral hαalg)).ne_zero
  have hroot : α ∈ p.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hp_ne, minpoly.aeval ℚ α⟩
  simpa [Polynomial.rootSet_def, Polynomial.aroots_def] using hroot

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree