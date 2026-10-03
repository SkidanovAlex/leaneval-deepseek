import Mathlib
import Submission.Work.ORFinal.OreField.skewMonoidAlgebra_noZeroDivisors
import Submission.Work.ORFinal.OreField.coeff_mul_finset_sum_single
import Submission.Work.ORFinal.OreField.matrix_kernel_of_card_lt
import Submission.Work.ORFinal.OreField.coeff_finset_sum_single_eq

/-!
# The right Ore condition for a twisted Laurent extension of a division ring

`SkewMonoidAlgebra D (Multiplicative ℤ)` is the twisted Laurent polynomial ring `D[t^{±1}; σ]`
over a division ring `D`.  We prove the right Ore condition: for nonzero `x y` there exist
nonzero `c d` with `x * c = y * d`.

The argument is linear algebra and avoids any division algorithm.  Choose `B` bounding the
exponents of `x` and `y`, and shift both on the left by the monomial `t^B` so that their support
lies in `[0, 2B]`.  Then multiply both by elements supported in `[0, 2B]`: the unknowns are the
`2B+1` coefficients of `c` and the `2B+1` coefficients of `d`, while only `4B+1` coefficient
equations have to be solved, so a nonzero solution exists by `matrix_kernel_of_card_lt`.  The
substitution `c_j = t^j • C_j` absorbs the twist and makes the equations `D`-linear; in the
coefficient of `t^m` the factor `t^m` pans out, which is why the same `m`-indexed matrix works for
all coefficients. -/

namespace Work.ORFinal.OreField

open SkewMonoidAlgebra Multiplicative

section Aux

variable {D : Type*} [DivisionRing D] [MulSemiringAction (Multiplicative ℤ) D]

/-- `g • a = 0 ↔ a = 0` for the action of a group element on a division ring. -/
private lemma smul_eq_zero_iff' (g : Multiplicative ℤ) (a : D) : g • a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, smul_zero]⟩
  have := congrArg (fun z => g⁻¹ • z) h
  rwa [smul_zero, smul_smul, inv_mul_cancel, one_smul] at this

/-- `single (-Bz) 1` is a left inverse of `single Bz 1`. -/
private lemma single_neg_mul_single (Bz : ℤ) :
    SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) *
      SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) = 1 := by
  rw [SkewMonoidAlgebra.single_mul_single]
  rw [show ofAdd (-Bz) * ofAdd Bz = 1 by rw [← ofAdd_add, neg_add_cancel, ofAdd_zero]]
  rw [show (1 : D) * ofAdd (-Bz) • (1 : D) = 1 by rw [smul_one, mul_one]]
  rfl

/-- Coefficients of `single Bz 1 * z` in terms of those of `z`. -/
private lemma shift_coeff (z : SkewMonoidAlgebra D (Multiplicative ℤ)) (Bz : ℤ) (k : ℤ) :
    (SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) * z).coeff (ofAdd k)
      = ofAdd Bz • z.coeff (ofAdd (k - Bz)) := by
  rw [SkewMonoidAlgebra.coeff_single_mul]
  have h1 : (ofAdd Bz)⁻¹ * ofAdd k = ofAdd (k - Bz) := by
    rw [show (ofAdd Bz)⁻¹ = ofAdd (-Bz) from (ofAdd_neg Bz).symm, ← ofAdd_add]
    congr 1
    ring
  rw [h1, one_mul]

/-- Left multiplication by `single Bz 1` is injective. -/
private lemma shift_ne_zero (z : SkewMonoidAlgebra D (Multiplicative ℤ)) (Bz : ℤ) (hz : z ≠ 0) :
    SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) * z ≠ 0 := by
  intro h
  have hz0 : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) *
      (SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) * z) = z := by
    rw [← mul_assoc, single_neg_mul_single, one_mul]
  rw [h, mul_zero] at hz0
  exact hz hz0.symm

end Aux

/-- A common bound for the exponents of two elements of the twisted Laurent polynomial ring. -/
private lemma exists_support_bound {D : Type*} [DivisionRing D]
    [MulSemiringAction (Multiplicative ℤ) D]
    (x y : SkewMonoidAlgebra D (Multiplicative ℤ)) :
    ∃ B : ℕ, (∀ i ∈ x.support, (toAdd i).natAbs ≤ B) ∧
      (∀ i ∈ y.support, (toAdd i).natAbs ≤ B) :=
  ⟨max (x.support.sup fun i => (toAdd i).natAbs)
      (y.support.sup fun i => (toAdd i).natAbs),
   fun _ hi => le_trans (Finset.le_sup (f := fun i => (toAdd i).natAbs) hi) (le_max_left _ _),
   fun _ hi => le_trans (Finset.le_sup (f := fun i => (toAdd i).natAbs) hi) (le_max_right _ _)⟩

theorem skewMonoidAlgebra_ore {D : Type*} [DivisionRing D]
    [MulSemiringAction (Multiplicative ℤ) D]
    (x y : SkewMonoidAlgebra D (Multiplicative ℤ)) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ c d : SkewMonoidAlgebra D (Multiplicative ℤ), c ≠ 0 ∧ d ≠ 0 ∧ x * c = y * d := by
  classical
  obtain ⟨B, hBx, hBy⟩ := exists_support_bound (D := D) x y
  set Bz : ℤ := (B : ℤ) with hBz
  -- vanishing of the coefficients of `x` and `y` outside `[-Bz, Bz]`
  have hxzero : ∀ j : ℤ, ¬ (-Bz ≤ j ∧ j ≤ Bz) → x.coeff (ofAdd j) = 0 := by
    intro j hj
    by_contra hne
    have hmem : ofAdd j ∈ x.support := mem_support_iff.mpr hne
    have hle := hBx (ofAdd j) hmem
    rw [toAdd_ofAdd] at hle
    have hle' : (j.natAbs : ℤ) ≤ Bz := by rw [hBz]; exact_mod_cast hle
    have hup : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    have hdn : -j ≤ (j.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -j); simpa using this
    exact hj ⟨by linarith, by linarith⟩
  have hyzero : ∀ j : ℤ, ¬ (-Bz ≤ j ∧ j ≤ Bz) → y.coeff (ofAdd j) = 0 := by
    intro j hj
    by_contra hne
    have hmem : ofAdd j ∈ y.support := mem_support_iff.mpr hne
    have hle := hBy (ofAdd j) hmem
    rw [toAdd_ofAdd] at hle
    have hle' : (j.natAbs : ℤ) ≤ Bz := by rw [hBz]; exact_mod_cast hle
    have hup : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
    have hdn : -j ≤ (j.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -j); simpa using this
    exact hj ⟨by linarith, by linarith⟩
  -- the shifted elements
  set xb : SkewMonoidAlgebra D (Multiplicative ℤ) :=
    SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) * x with hxb
  set yb : SkewMonoidAlgebra D (Multiplicative ℤ) :=
    SkewMonoidAlgebra.single (ofAdd Bz) (1 : D) * y with hyb
  -- their coefficients vanish outside `[0, 2Bz]`
  have hxbvanish : ∀ k : ℤ, (k < 0 ∨ 2 * Bz < k) → xb.coeff (ofAdd k) = 0 := by
    intro k hk
    rw [hxb, shift_coeff]
    have hv : x.coeff (ofAdd (k - Bz)) = 0 := by
      apply hxzero
      rintro ⟨h1, h2⟩
      rcases hk with hk | hk <;> omega
    rw [hv, smul_zero]
  have hybvanish : ∀ k : ℤ, (k < 0 ∨ 2 * Bz < k) → yb.coeff (ofAdd k) = 0 := by
    intro k hk
    rw [hyb, shift_coeff]
    have hv : y.coeff (ofAdd (k - Bz)) = 0 := by
      apply hyzero
      rintro ⟨h1, h2⟩
      rcases hk with hk | hk <;> omega
    rw [hv, smul_zero]
  have hxbnz : xb ≠ 0 := by rw [hxb]; exact shift_ne_zero x Bz hx
  have hybnz : yb ≠ 0 := by rw [hyb]; exact shift_ne_zero y Bz hy
  -- the linear system
  let ψ : ℕ → ℕ → D := fun n j =>
    if (j : ℕ) < 2 * B + 1 then
      ofAdd (-(n : ℤ)) • xb.coeff (ofAdd ((n : ℤ) - (j : ℤ)))
    else
      -(ofAdd (-(n : ℤ)) • yb.coeff (ofAdd ((n : ℤ) - ((j : ℤ) - ((2 * B + 1 : ℕ) : ℤ)))))
  set Ψ : Matrix (Fin (4 * B + 1)) (Fin ((2 * B + 1) + (2 * B + 1))) D :=
    fun n j => ψ (n : ℕ) (j : ℕ) with hΨ
  have hcard : 4 * B + 1 < (2 * B + 1) + (2 * B + 1) := by omega
  obtain ⟨v, hvne, hvker⟩ := matrix_kernel_of_card_lt hcard Ψ
  have hker : ∀ n : Fin (4 * B + 1), ∑ j, Ψ n j * v j = 0 := by
    intro n
    have := congrFun hvker n
    rwa [Matrix.mulVec_apply, dotProduct] at this
  -- the unknowns
  set C : Fin (2 * B + 1) → D := fun j => v (Fin.castAdd (2 * B + 1) j) with hC
  set Dk : Fin (2 * B + 1) → D := fun j => v (Fin.natAdd (2 * B + 1) j) with hDk
  have hCapply : ∀ j, v (Fin.castAdd (2 * B + 1) j) = C j := fun j => by rw [hC]
  have hDkapply : ∀ j, v (Fin.natAdd (2 * B + 1) j) = Dk j := fun j => by rw [hDk]
  set c : SkewMonoidAlgebra D (Multiplicative ℤ) :=
    ∑ j : Fin (2 * B + 1), SkewMonoidAlgebra.single (ofAdd ((j : ℕ) : ℤ))
      (ofAdd ((j : ℕ) : ℤ) • C j) with hc
  set d : SkewMonoidAlgebra D (Multiplicative ℤ) :=
    ∑ j : Fin (2 * B + 1), SkewMonoidAlgebra.single (ofAdd ((j : ℕ) : ℤ))
      (ofAdd ((j : ℕ) : ℤ) • Dk j) with hd
  -- evaluation of the matrix at the two blocks
  have hΨcast : ∀ (n : Fin (4 * B + 1)) (i : Fin (2 * B + 1)),
      Ψ n (Fin.castAdd (2 * B + 1) i)
        = ofAdd (-((n : ℕ) : ℤ)) • xb.coeff (ofAdd (((n : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by
    intro n i
    show ψ (n : ℕ) ((Fin.castAdd (2 * B + 1) i : Fin _) : ℕ) = _
    rw [Fin.val_castAdd]
    show (if ((i : ℕ) < 2 * B + 1) then _ else _) = _
    rw [if_pos i.isLt]
  have hΨnat : ∀ (n : Fin (4 * B + 1)) (i : Fin (2 * B + 1)),
      Ψ n (Fin.natAdd (2 * B + 1) i)
        = -(ofAdd (-((n : ℕ) : ℤ)) • yb.coeff (ofAdd (((n : ℕ) : ℤ) - ((i : ℕ) : ℤ)))) := by
    intro n i
    show ψ (n : ℕ) ((Fin.natAdd (2 * B + 1) i : Fin _) : ℕ) = _
    rw [Fin.val_natAdd]
    show (if ((2 * B + 1 + (i : ℕ) : ℕ) < 2 * B + 1) then _ else _) = _
    rw [if_neg (by omega)]
    congr 1
    congr 2
    push_cast
    ring
  -- the coefficient identity
  have hkey : xb * c = yb * d := by
    apply SkewMonoidAlgebra.ext
    intro g
    obtain ⟨m, rfl⟩ := ofAdd.surjective g
    have h1 : (xb * c).coeff (ofAdd m)
        = ∑ j : Fin (2 * B + 1),
            xb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • C j) := by
      rw [hc]
      exact coeff_mul_finset_sum_single (2 * B + 1) xb C m
    have h2 : (yb * d).coeff (ofAdd m)
        = ∑ j : Fin (2 * B + 1),
            yb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • Dk j) := by
      rw [hd]
      exact coeff_mul_finset_sum_single (2 * B + 1) yb Dk m
    rw [h1, h2]
    by_cases hm : (0 : ℤ) ≤ m ∧ m ≤ 4 * Bz
    · -- the equations of the linear system apply
      obtain ⟨hm0, hm4⟩ := hm
      have hmnn : m.toNat < 4 * B + 1 := by
        have h2' : m ≤ ((4 * B : ℕ) : ℤ) := by
          rw [hBz] at hm4
          push_cast
          exact hm4
        omega
      set nm : Fin (4 * B + 1) := ⟨m.toNat, hmnn⟩ with hnm
      have hnmval : ((nm : ℕ) : ℤ) = m := by
        simp only [hnm]
        exact Int.toNat_of_nonneg hm0
      have hker' := hker nm
      rw [Fin.sum_univ_add] at hker'
      rw [show (∑ i : Fin (2 * B + 1), Ψ nm (Fin.castAdd (2 * B + 1) i) * v (Fin.castAdd (2 * B + 1) i))
            = ∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • xb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * C i from by
          apply Finset.sum_congr rfl
          intro i _
          rw [hΨcast nm i, hCapply i, hnmval],
          show (∑ i : Fin (2 * B + 1), Ψ nm (Fin.natAdd (2 * B + 1) i) * v (Fin.natAdd (2 * B + 1) i))
            = -∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • yb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * Dk i from by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [hΨnat nm i, hDkapply i, hnmval, neg_mul]] at hker'
      have hEq : (∑ i : Fin (2 * B + 1),
              (ofAdd (-m) • xb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * C i)
            = ∑ i : Fin (2 * B + 1),
              (ofAdd (-m) • yb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * Dk i := by
        have h0 : (∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • xb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * C i)
              - ∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • yb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * Dk i = 0 := by
          rw [sub_eq_add_neg]
          exact hker'
        exact sub_eq_zero.mp h0
      -- apply `ofAdd m •` and identify with the two coefficient sums
      have hSx : (∑ j : Fin (2 * B + 1),
            xb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • C j))
          = ofAdd m • (∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • xb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * C i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [MulSemiringAction.smul_mul, smul_smul,
          show ofAdd m * ofAdd (-m) = 1 by rw [← ofAdd_add, add_neg_cancel, ofAdd_zero],
          one_smul]
      have hSy : (∑ j : Fin (2 * B + 1),
            yb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • Dk j))
          = ofAdd m • (∑ i : Fin (2 * B + 1),
                (ofAdd (-m) • yb.coeff (ofAdd (m - ((i : ℕ) : ℤ)))) * Dk i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [MulSemiringAction.smul_mul, smul_smul,
          show ofAdd m * ofAdd (-m) = 1 by rw [← ofAdd_add, add_neg_cancel, ofAdd_zero],
          one_smul]
      rw [hSx, hSy, hEq]
    · -- no equation is needed: both sums vanish
      have hm' : m < 0 ∨ 4 * Bz < m := by
        rcases lt_or_ge m 0 with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          by_contra hle
          exact hm ⟨h, le_of_not_gt hle⟩
      have hzx : ∑ j : Fin (2 * B + 1),
            xb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • C j) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : ((j : ℕ) : ℤ) ≤ 2 * Bz := by
          have : (j : ℕ) ≤ 2 * B := by omega
          rw [hBz]; exact_mod_cast this
        have hv : xb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) = 0 := by
          apply hxbvanish
          rcases hm' with hm' | hm'
          · left; omega
          · right; omega
        rw [hv, zero_mul]
      have hzy : ∑ j : Fin (2 * B + 1),
            yb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) * (ofAdd m • Dk j) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj : ((j : ℕ) : ℤ) ≤ 2 * Bz := by
          have : (j : ℕ) ≤ 2 * B := by omega
          rw [hBz]; exact_mod_cast this
        have hv : yb.coeff (ofAdd (m - ((j : ℕ) : ℤ))) = 0 := by
          apply hybvanish
          rcases hm' with hm' | hm'
          · left; omega
          · right; omega
        rw [hv, zero_mul]
      rw [hzx, hzy]
  -- conclude
  have hxc : x * c = y * d := by
    have hL : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * xb = x := by
      rw [hxb, ← mul_assoc, single_neg_mul_single, one_mul]
    have hR : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * yb = y := by
      rw [hyb, ← mul_assoc, single_neg_mul_single, one_mul]
    have hkey' : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * (xb * c)
        = SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * (yb * d) := by rw [hkey]
    have hkeys : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * (xb * c) = x * c := by
      rw [← mul_assoc, hL]
    have hkeyd : SkewMonoidAlgebra.single (ofAdd (-Bz)) (1 : D) * (yb * d) = y * d := by
      rw [← mul_assoc, hR]
    rw [hkeys, hkeyd] at hkey'
    exact hkey'
  have hcne : c ≠ 0 := by
    intro hc0
    have hd0 : d = 0 := by
      have : yb * d = 0 := by rw [← hkey, hc0, mul_zero]
      by_contra hdne
      exact skewMonoidAlgebra_noZeroDivisors yb d hybnz hdne this
    have hC0 : ∀ j, C j = 0 := by
      intro j
      have : c.coeff (ofAdd ((j : ℕ) : ℤ)) = 0 := by rw [hc0]; simp
      rw [hc, coeff_finset_sum_single_eq] at this
      exact (smul_eq_zero_iff' _ _).mp this
    have hD0 : ∀ j, Dk j = 0 := by
      intro j
      have : d.coeff (ofAdd ((j : ℕ) : ℤ)) = 0 := by rw [hd0]; simp
      rw [hd, coeff_finset_sum_single_eq] at this
      exact (smul_eq_zero_iff' _ _).mp this
    apply hvne
    funext j
    show v j = 0
    refine Fin.addCases (motive := fun x => v x = 0) ?_ ?_ j
    · intro i
      rw [hCapply i, hC0 i]
    · intro i
      rw [hDkapply i, hD0 i]
  have hdne : d ≠ 0 := by
    intro hd0
    have hc0 : c = 0 := by
      have : xb * c = 0 := by rw [hkey, hd0, mul_zero]
      by_contra hcne
      exact skewMonoidAlgebra_noZeroDivisors xb c hxbnz hcne this
    have hC0 : ∀ j, C j = 0 := by
      intro j
      have : c.coeff (ofAdd ((j : ℕ) : ℤ)) = 0 := by rw [hc0]; simp
      rw [hc, coeff_finset_sum_single_eq] at this
      exact (smul_eq_zero_iff' _ _).mp this
    have hD0 : ∀ j, Dk j = 0 := by
      intro j
      have : d.coeff (ofAdd ((j : ℕ) : ℤ)) = 0 := by rw [hd0]; simp
      rw [hd, coeff_finset_sum_single_eq] at this
      exact (smul_eq_zero_iff' _ _).mp this
    apply hvne
    funext j
    show v j = 0
    refine Fin.addCases (motive := fun x => v x = 0) ?_ ?_ j
    · intro i
      rw [hCapply i, hC0 i]
    · intro i
      rw [hDkapply i, hD0 i]
  exact ⟨c, d, hcne, hdne, hxc⟩

end Work.ORFinal.OreField
