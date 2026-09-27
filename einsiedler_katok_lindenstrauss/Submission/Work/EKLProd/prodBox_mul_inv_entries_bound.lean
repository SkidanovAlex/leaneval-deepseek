import Mathlib
import Submission.Work.EKLProd.ProdPlaqueDefs
import Submission.Work.EKLProd.inv_entries_bound

/-!
# Entrywise boundedness of the right translate of the product box

For the tower identity of Pisa Lemma 8.10 one needs that the *right translate*
`(prodBox T U ε) · g₀⁻¹` of the product box `prodBox T U ε = (V ε ∩ T) * (V ε ∩ U)` is
contained in an entrywise box (a compact set of matrices).  This module proves the quantitative
version

`prodBox_mul_inv_entries_bound`:

if `g₀ ∈ prodBox T U ε` and `ε > 0`, then there is `C` with `|u i j| ≤ C` for every
`u ∈ (prodBox T U ε) · g₀⁻¹`.

The proof is a three-fold entrywise product bound.  Writing `a = t v` (`t, v ∈ V ε`) and
`g₀ = t₀ v₀` (`t₀, v₀ ∈ V ε`), we have

`a · g₀⁻¹ = t · (v · v₀⁻¹) · t₀⁻¹`,

each of the three factors is entrywise bounded (elements of `V ε` by `1 + ε`, inverses of
elements of `V ε` by `2 (1 + ε)²`, from `inv_entries_bound`), and an entry of a product of two
`3 × 3` matrices with entrywise bounds `b`, `d` is bounded by `3 b d`.  Chaining gives the
explicit constant `C = 108 (1 + ε)⁶`.
-/


namespace Work.EKLProd

open Work.EKLContract

/-- Entrywise bound for a product of `3 × 3` real matrices: if all entries of `A` are bounded by
`b ≥ 0` and all entries of `B` by `d ≥ 0`, then all entries of `A * B` are bounded by
`3 * (b * d)`. -/
lemma abs_mul_entries_le {A B : SL3} {b d : ℝ} (_hb : 0 ≤ b) (_hd : 0 ≤ d)
    (hA : ∀ i j, |A i j| ≤ b) (hB : ∀ i j, |B i j| ≤ d) (i j : Fin 3) :
    |(A * B) i j| ≤ 3 * (b * d) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  calc |∑ k, (A : Matrix (Fin 3) (Fin 3) ℝ) i k * (B : Matrix (Fin 3) (Fin 3) ℝ) k j|
      ≤ ∑ k, |(A : Matrix (Fin 3) (Fin 3) ℝ) i k * (B : Matrix (Fin 3) (Fin 3) ℝ) k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(A : Matrix (Fin 3) (Fin 3) ℝ) i k| * |(B : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
        simp [abs_mul]
    _ ≤ ∑ k, b * d :=
        Finset.sum_le_sum (fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) _hb)
    _ = 3 * (b * d) := by rw [Fin.sum_univ_three]; ring

/-- Every entry of an element of the displacement neighbourhood `V ε` is bounded by `1 + ε`. -/
lemma abs_entry_le_of_mem_V {ε : ℝ} {u : SL3} (hu : u ∈ V ε) (i j : Fin 3) :
    |u i j| ≤ 1 + ε := by
  have hlt : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε :=
    hu i j
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |u i j| = |((u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
                    + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by rw [sub_add_cancel]
    _ ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ ε + 1 := add_le_add (le_of_lt hlt) hone
    _ = 1 + ε := by ring

/-- Every entry of the inverse of an element of `V ε` is bounded by `2 (1 + ε)²` (the entries of
the inverse are `2 × 2` minors of the adjugate). -/
lemma inv_entry_le {ε : ℝ} (hε : 0 < ε) {u : SL3} (hu : u ∈ V ε) (i j : Fin 3) :
    |(u⁻¹) i j| ≤ 2 * (1 + ε) ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  refine abs_adjugate_entry_le (by linarith) (fun p q => ?_) i j
  exact abs_entry_le_of_mem_V hu p q

/-- Entrywise bound for the normal form `((t * v) * v₀⁻¹) * t₀⁻¹` with `t, v, t₀, v₀ ∈ V ε`. -/
lemma prodBox_pair_bound {ε : ℝ} (hε : 0 < ε) {t v t₀ v₀ : SL3}
    (ht : t ∈ V ε) (hv : v ∈ V ε) (ht₀ : t₀ ∈ V ε) (hv₀ : v₀ ∈ V ε) (i j : Fin 3) :
    |(((t * v) * v₀⁻¹) * t₀⁻¹) i j| ≤ 108 * (1 + ε) ^ 6 := by
  have htv : ∀ i j, |(t * v) i j| ≤ 3 * ((1+ε)*(1+ε)) :=
    fun i j => abs_mul_entries_le (by positivity) (by positivity)
      (fun i j => abs_entry_le_of_mem_V ht i j) (fun i j => abs_entry_le_of_mem_V hv i j) i j
  have hA : ∀ i j, |((t * v) * v₀⁻¹) i j| ≤ 3 * ((3 * ((1+ε)*(1+ε))) * (2*(1+ε)^2)) :=
    fun i j => abs_mul_entries_le (by positivity) (by positivity) htv
      (fun i j => inv_entry_le hε hv₀ i j) i j
  have hfin := abs_mul_entries_le (A := (t*v)*v₀⁻¹) (B := t₀⁻¹) (by positivity) (by positivity) hA
    (fun i j => inv_entry_le hε ht₀ i j) i j
  have heq : 3 * ((3 * ((3 * ((1+ε)*(1+ε))) * (2*(1+ε)^2))) * (2*(1+ε)^2)) = 108 * (1+ε)^6 := by
    ring
  linarith [hfin, heq]

/-- Entrywise bound for `a · g₀⁻¹` with `g₀, a` in the product box. -/
lemma mul_inv_entry_bound {T U : Subgroup SL3} {ε : ℝ} (hε : 0 < ε)
    {g₀ a : SL3} (hg₀ : g₀ ∈ prodBox T U ε) (ha : a ∈ prodBox T U ε) (i j : Fin 3) :
    |(a * g₀⁻¹) i j| ≤ 108 * (1 + ε) ^ 6 := by
  obtain ⟨t₀, ⟨ht₀V, _⟩, v₀, ⟨hv₀V, _⟩, hde₀⟩ := hg₀
  obtain ⟨t, ⟨htV, _⟩, v, ⟨hvV, _⟩, hde⟩ := ha
  have hg0inv : g₀⁻¹ = v₀⁻¹ * t₀⁻¹ := by rw [← hde₀, mul_inv_rev]
  have key := prodBox_pair_bound (ε := ε) hε (t := t) (v := v) (t₀ := t₀) (v₀ := v₀)
    htV hvV ht₀V hv₀V i j
  rw [← hde, hg0inv]
  dsimp only
  rw [← mul_assoc]
  exact key

theorem prodBox_mul_inv_entries_bound {T U : Subgroup Work.EKLContract.SL3} {ε : ℝ} (hε : 0 < ε)
    {g₀ : Work.EKLContract.SL3} (hg₀ : g₀ ∈ Work.EKLProd.prodBox T U ε) :
    ∃ C : ℝ, ∀ u : Work.EKLContract.SL3,
      u ∈ (fun a : Work.EKLContract.SL3 => a * g₀⁻¹) '' Work.EKLProd.prodBox T U ε →
      ∀ i j, |u i j| ≤ C := by
  refine ⟨108 * (1 + ε) ^ 6, ?_⟩
  rintro u ⟨a, ha, rfl⟩ i j
  exact mul_inv_entry_bound hε hg₀ ha i j

end Work.EKLProd
