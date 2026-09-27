import Mathlib
import Submission.Work.EKLProd.ProdPlaqueDefs
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLProd.inv_entries_bound

namespace Work.EKLProd

open Matrix

set_option linter.unusedVariables false

noncomputable section

/-- Entrywise bound for a product of two `3 × 3` real matrices: if all entries of `A` are
bounded by `b ≥ 0` and all entries of `B` by `d ≥ 0`, then all entries of `A * B` are bounded
by `3 * (b * d)`. -/
lemma abs_mat_mul_le {A B : Matrix (Fin 3) (Fin 3) ℝ} {b d : ℝ} (hb : 0 ≤ b) (_hd : 0 ≤ d)
    (hA : ∀ i j, |A i j| ≤ b) (hB : ∀ i j, |B i j| ≤ d) (i j : Fin 3) :
    |(A * B) i j| ≤ 3 * (b * d) := by
  rw [Matrix.mul_apply]
  calc |∑ k, A i k * B k j| ≤ ∑ k, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * |B k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, b * d :=
      Finset.sum_le_sum (fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hb)
    _ = 3 * (b * d) := by rw [Fin.sum_univ_three]; ring

/-- Every entry of the inverse of an element of `SL₃(ℝ)` whose entries are bounded by `B ≥ 0`
is bounded by `2 B²`: the inverse is the adjugate, whose entries are `2 × 2` minors. -/
lemma inv_entry_le_of_abs_le {g : Work.EKLContract.SL3} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B) (i j : Fin 3) :
    |((g⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 * B ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  exact abs_adjugate_entry_le hB hg i j

/-- **The two factors of `(t' * u') * t⁻¹` stay in the box of radius `R`.**

Let `τ := hT T U t` be the `T`-coordinate of a point `t` of the closed unit ball `Ucl H 1` (all
entries within `1` of the identity), so that (by `EKLProd/hT_apply_eq_ite`) its entries are bounded
by `2` and those of `τ - t` by `1` — this is the hypothesis `hτ`.  Then for
`t' ∈ V (R/10⁹)`, `u' ∈ V (R/10⁹)` (entries within `R/10⁹` of the identity) the two factors
`t' * τ⁻¹` and `τ * u' * t⁻¹` of the product `(t' * u') * t⁻¹` lie in `V R`, i.e. differ from the
identity by `< R` in every entry (`hineqA`, `hineqB` are the two arithmetic hypotheses produced by
the estimates and are satisfied for `R ≥ 5000`).

Route.  Cramer: the entries of `τ⁻¹` and of `t⁻¹` are bounded by `8` (the inverse is the adjugate
of a matrix with entries `≤ 2`, `Work.EKLProd.abs_adjugate_entry_le`).  Then
`t' * τ⁻¹ - 1 = (t' - 1) * τ⁻¹ + (τ⁻¹ - 1)` gives `hineqA`; and, writing `υ := hU T U t`
(so `τ * υ = t` and `υ⁻¹ * τ⁻¹ = t⁻¹`),
`τ * u' * t⁻¹ = (τ * u' * τ⁻¹) * (τ * υ⁻¹ * τ⁻¹) = (τ * u' * τ⁻¹) * (τ * t⁻¹)` with
`|τ * u' * τ⁻¹ - 1| ≤ 3·2·(R/10⁹)·8` and `|τ * t⁻¹| ≤ 1 + 3·2·(3·8·1·8)`, giving `hineqB`. -/
theorem mul_inv_mem_V_of_hT_bounds {H T U : Subgroup Work.EKLContract.SL3}
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    {t : Work.EKLContract.SL3} (ht : Work.EKLComp.Ucl H 1) {R : ℝ}
    (hineqA : 3 * (8 * (R / (10 : ℝ) ^ 9)) + 9 < R)
    (hineqB : 3 * (1153 * (48 * (R / (10 : ℝ) ^ 9))) + 1152 < R)
    {t' u' : Work.EKLContract.SL3}
    (ht' : t' ∈ Work.EKLContract.V (R / (10 : ℝ) ^ 9))
    (hu' : u' ∈ Work.EKLContract.V (R / (10 : ℝ) ^ 9))
    (hτ : ∀ i j : Fin 3, |(Work.EKLProd.hT T U t) i j| ≤ 2 ∧
      |(Work.EKLProd.hT T U t) i j - t i j| ≤ 1) :
    t' * (Work.EKLProd.hT T U t)⁻¹ ∈ Work.EKLContract.V R ∧
      Work.EKLProd.hT T U t * u' * t⁻¹ ∈ Work.EKLContract.V R := by
  -- `R` is positive (forced by `hineqA`)
  have hRpos : 0 < R := by
    have h10 : (10 : ℝ) ^ 9 ≠ 0 := by norm_num
    have hdiv : R / (10 : ℝ) ^ 9 * (10 : ℝ) ^ 9 = R := div_mul_cancel₀ R h10
    nlinarith [hineqA, hdiv]
  have hc : 0 ≤ R / (10 : ℝ) ^ 9 := div_nonneg (le_of_lt hRpos) (by norm_num)
  have hone : ∀ i j : Fin 3, |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]; split_ifs <;> simp
  -- the `T`-coordinate
  set τ : Work.EKLContract.SL3 := Work.EKLProd.hT T U t with hτdef
  have hτ2 : ∀ i j : Fin 3, |(τ : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := fun i j => by
    rw [hτdef]; exact (hτ i j).1
  have hτt : ∀ i j : Fin 3,
      |(τ : Matrix (Fin 3) (Fin 3) ℝ) i j - (t : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 :=
    fun i j => by rw [hτdef]; exact (hτ i j).2
  -- entries of `t` are bounded by `3` (only `hτ` is available: entries of `t` are one more
  -- than the entries of `τ`)
  have ht3 : ∀ i j : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 3 := by
    intro i j
    have h1 : |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (τ : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [abs_sub_comm]; exact hτt i j
    calc |(t : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |((t : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (τ : Matrix (Fin 3) (Fin 3) ℝ) i j + (τ : Matrix (Fin 3) (Fin 3) ℝ) i j)| := by
          rw [sub_add_cancel]
      _ ≤ |(t : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (τ : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(τ : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          abs_add_le _ _
      _ ≤ 1 + 2 := add_le_add h1 (hτ2 i j)
      _ = 3 := by norm_num
  have hτi8 : ∀ i j : Fin 3,
      |(((τ⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 8 := by
    intro i j
    have h := inv_entry_le_of_abs_le (B := 2) (by norm_num) hτ2 i j
    norm_num at h; exact h
  have hτi9 : ∀ i j : Fin 3,
      |(((τ⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 9 := by
    intro i j
    calc |(((τ⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |(((τ⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_sub _ _
      _ ≤ 8 + 1 := add_le_add (hτi8 i j) (hone i j)
      _ = 9 := by norm_num
  have hti18 : ∀ i j : Fin 3,
      |(((t⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 18 := by
    intro i j
    have h := inv_entry_le_of_abs_le (B := 3) (by norm_num) ht3 i j
    norm_num at h; exact h
  have htc : ∀ i j : Fin 3, |(t' : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R / (10 : ℝ) ^ 9 :=
    fun i j => le_of_lt (ht' i j)
  have huc : ∀ i j : Fin 3, |(u' : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R / (10 : ℝ) ^ 9 :=
    fun i j => le_of_lt (hu' i j)
  constructor
  · -- first factor: `t' * τ⁻¹`
    intro i j
    have hcoe : (((t' * (τ)⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ)
        = (t' : Matrix (Fin 3) (Fin 3) ℝ)
            * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul t' τ⁻¹
    calc |(((t' * (τ)⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |((((t' : Matrix (Fin 3) (Fin 3) ℝ)
              * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) - 1) i j)| := by
            rw [hcoe, Matrix.sub_apply]
      _ = |(((((t' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
              * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
              + ((((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j)| := by
            rw [show (t' : Matrix (Fin 3) (Fin 3) ℝ)
                  * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
                = ((t' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
                  * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
                  + ((((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1)
                from by noncomm_ring]
      _ = |((((t' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
              * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j)
              + (((((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)| := by
            rw [Matrix.add_apply]
      _ ≤ |((((t' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
              * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j)|
            + |(((((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)| :=
            abs_add_le _ _
      _ ≤ 3 * ((R / (10 : ℝ) ^ 9) * 8) + 9 :=
            add_le_add (abs_mat_mul_le hc (by norm_num)
              (fun p q => by rw [Matrix.sub_apply]; exact htc p q) hτi8 i j) (hτi9 i j)
      _ = 3 * (8 * (R / (10 : ℝ) ^ 9)) + 9 := by ring
      _ < R := hineqA
  · -- second factor: `τ * u' * t⁻¹`
    intro i j
    have hττi : (τ : Matrix (Fin 3) (Fin 3) ℝ)
        * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hτiτ : (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * (τ : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have htti : (t : Matrix (Fin 3) (Fin 3) ℝ)
        * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    set P : Matrix (Fin 3) (Fin 3) ℝ :=
      (τ : Matrix (Fin 3) (Fin 3) ℝ) * (u' : Matrix (Fin 3) (Fin 3) ℝ)
        * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) with hPdef
    set Q : Matrix (Fin 3) (Fin 3) ℝ :=
      (τ : Matrix (Fin 3) (Fin 3) ℝ)
        * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) with hQdef
    have hP1 : ∀ p q : Fin 3,
        |((P - 1) p q)| ≤ 3 * (3 * (2 * (R / (10 : ℝ) ^ 9))) * 8 := by
      intro p q
      have hidP : P - 1 = (τ : Matrix (Fin 3) (Fin 3) ℝ)
          * ((u' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
          * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [hPdef, mul_sub, mul_one, sub_mul, hττi]
      rw [hidP]
      have h1 : ∀ p q : Fin 3,
          |((τ : Matrix (Fin 3) (Fin 3) ℝ) * ((u' : Matrix (Fin 3) (Fin 3) ℝ) - 1)) p q|
            ≤ 3 * (2 * (R / (10 : ℝ) ^ 9)) :=
        fun p q => abs_mat_mul_le (by norm_num) hc hτ2
          (fun p q => by rw [Matrix.sub_apply]; exact huc p q) p q
      have h2 := abs_mat_mul_le (b := 3 * (2 * (R / (10 : ℝ) ^ 9))) (d := 8)
        (by nlinarith [hc]) (by norm_num) h1 hτi8 p q
      calc |((τ : Matrix (Fin 3) (Fin 3) ℝ) * ((u' : Matrix (Fin 3) (Fin 3) ℝ) - 1)
              * (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) p q|
          ≤ 3 * ((3 * (2 * (R / (10 : ℝ) ^ 9))) * 8) := h2
        _ = 3 * (3 * (2 * (R / (10 : ℝ) ^ 9))) * 8 := by ring
    have hQ1 : ∀ p q : Fin 3, |((Q - 1) p q)| ≤ 54 := by
      intro p q
      have hidQ : Q - 1 = ((τ : Matrix (Fin 3) (Fin 3) ℝ) - (t : Matrix (Fin 3) (Fin 3) ℝ))
          * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
        rw [hQdef, sub_mul, htti]
      rw [hidQ]
      have hsub : ∀ p q : Fin 3,
          |((τ : Matrix (Fin 3) (Fin 3) ℝ) - (t : Matrix (Fin 3) (Fin 3) ℝ)) p q| ≤ 1 :=
        fun p q => by rw [Matrix.sub_apply]; exact hτt p q
      have h := abs_mat_mul_le (b := 1) (d := 18) (by norm_num) (by norm_num) hsub hti18 p q
      calc |(((τ : Matrix (Fin 3) (Fin 3) ℝ) - (t : Matrix (Fin 3) (Fin 3) ℝ))
            * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) p q|
          ≤ 3 * (1 * 18) := h
        _ = 54 := by norm_num
    have hQb : ∀ p q : Fin 3, |Q p q| ≤ 1 + 54 := by
      intro p q
      have hentry : Q p q = (Q - 1) p q + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q := by
        rw [← Matrix.add_apply, sub_add_cancel]
      calc |Q p q| = |(Q - 1) p q + (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := by rw [hentry]
        _ ≤ |(Q - 1) p q| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) p q| := abs_add_le _ _
        _ ≤ 54 + 1 := add_le_add (hQ1 p q) (hone p q)
        _ = 1 + 54 := by ring
    have hPQ : P * Q = ((τ : Matrix (Fin 3) (Fin 3) ℝ) * (u' : Matrix (Fin 3) (Fin 3) ℝ))
        * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [hPdef, hQdef]
      rw [mul_assoc ((τ : Matrix (Fin 3) (Fin 3) ℝ) * (u' : Matrix (Fin 3) (Fin 3) ℝ))
            (((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
            ((τ : Matrix (Fin 3) (Fin 3) ℝ)
              * (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))]
      rw [← mul_assoc ((((τ⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
            (τ : Matrix (Fin 3) (Fin 3) ℝ)
            (((t⁻¹) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)]
      rw [hτiτ, one_mul]
    have hcoe : (((τ * u' * t⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) = P * Q := by
      rw [hPQ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    calc |(((τ * u' * t⁻¹ : Work.EKLContract.SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |((P * Q - 1) i j)| := by rw [hcoe, Matrix.sub_apply]
      _ = |(((P - 1) * Q + (Q - 1)) i j)| := by
            rw [show P * Q - 1 = (P - 1) * Q + (Q - 1) from by noncomm_ring]
      _ = |(((P - 1) * Q) i j) + ((Q - 1) i j)| := by rw [Matrix.add_apply]
      _ ≤ |(((P - 1) * Q) i j)| + |((Q - 1) i j)| := abs_add_le _ _
      _ ≤ 3 * ((3 * (3 * (2 * (R / (10 : ℝ) ^ 9))) * 8) * (1 + 54)) + 54 :=
            add_le_add (abs_mat_mul_le (b := 3 * (3 * (2 * (R / (10 : ℝ) ^ 9))) * 8)
              (d := 1 + 54) (by nlinarith [hc]) (by norm_num) hP1 hQb i j) (hQ1 i j)
      _ = 23760 * (R / (10 : ℝ) ^ 9) + 54 := by ring
      _ < R := by nlinarith [hineqB, hc]

end

end Work.EKLProd
