import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.MDEstimates.eNorm_sub_le
import Submission.Work.HP.MDBasic.finite_sets

/-!
# Lower bound for the number of lattice points in a Euclidean ball

For a sublattice `L ⊆ ℤ^5` of rank `r ≤ 3` and `T ≥ 1`, the number of lattice points of
`L` of Euclidean norm at most `T` is bounded below by a positive constant times the product
`∏_{i=1}^{r} T / λ_i(L)` of the successive minima.

## The argument

Fix `L` of rank `R = rk L` and let `f 0, …, f (R-1)` be the `ℤ`-linearly independent lattice
vectors with `‖f j‖ ≤ λ_{j+1}(L)` supplied by `Work.HP.FM.exists_indep_le_lam` (the successive
minima are attained — Minkowski's greedy construction).  For each index `j` pick

`N j = ⌊T / ((R+1) · λ_{j+1})⌋ + 1`

and look at the box `∏_j {0, …, N j - 1}` of integer coefficient vectors.  The map

`a ↦ Ψ a = ∑_j a_j • f j`

is injective (linear independence), lands in `L` (submodule), and every value at an element of
the box has norm at most `T`:  the `j`-th coefficient is at most `N j - 1 ≤ T/((R+1)λ_{j+1})`,
so `a_j ‖f j‖ ≤ T/(R+1)` and the triangle inequality gives `‖Ψ a‖ ≤ R·T/(R+1) ≤ T`.

Counting the box therefore yields
`#(L ∩ B_T) ≥ ∏_j N j ≥ ∏_j T/((R+1)λ_{j+1}) = (1/(R+1))^R · ∏_j T/λ_{j+1}`.
Since `R ≤ 3` the prefactor is at least `1/64`, which gives the claimed constant.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.Q44Geom

namespace VDC

variable {ι : Type*} [Fintype ι]

/-- Triangle inequality for the Euclidean norm `eNorm` of integer vectors. -/
lemma eNorm_neg (v : ι → ℤ) : Work.HP.eNorm (-v) = Work.HP.eNorm v := by
  simp only [Work.HP.eNorm, Pi.neg_apply]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Int.cast_neg]; ring

lemma eNorm_add_le (v w : ι → ℤ) :
    Work.HP.eNorm (v + w) ≤ Work.HP.eNorm v + Work.HP.eNorm w := by
  have h := Work.HP.MDEstimates.eNorm_sub_le v (-w)
  rw [sub_neg_eq_add, eNorm_neg] at h
  exact h

lemma eNorm_sum_le {κ : Type*} (s : Finset κ) (g : κ → ι → ℤ) :
    Work.HP.eNorm (∑ k ∈ s, g k) ≤ ∑ k ∈ s, Work.HP.eNorm (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Work.HP.eNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc Work.HP.eNorm (g a + ∑ k ∈ s, g k)
        ≤ Work.HP.eNorm (g a) + Work.HP.eNorm (∑ k ∈ s, g k) := eNorm_add_le _ _
      _ ≤ Work.HP.eNorm (g a) + ∑ k ∈ s, Work.HP.eNorm (g k) := add_le_add le_rfl ih

lemma eNorm_smul_int (c : ℤ) (v : ι → ℤ) :
    Work.HP.eNorm (c • v) = |(c : ℝ)| * Work.HP.eNorm v := by
  rw [Work.HP.eNorm, Work.HP.eNorm]
  have hsum : (∑ i, (((c • v) i : ℤ) : ℝ) ^ 2) = (c : ℝ) ^ 2 * ∑ i, ((v i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  rw [hsum, Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq_eq_abs]

/-- **Main lower bound.**  For a sublattice `L ⊆ ℤ^5` and `T ≥ 1`,
`(1/(rk L + 1))^(rk L) · ∏_{i<rk L} T/λ_{i+1} ≤ #(L ∩ B_T)`. -/
theorem ballCount_lower (L : Submodule ℤ (Fin 5 → ℤ)) (T : ℝ) (hT : 1 ≤ T) :
    ((1 : ℝ) / ((Work.HP.rk L : ℝ) + 1) ^ (Work.HP.rk L)) *
        ∏ i ∈ Finset.range (Work.HP.rk L), (T / Work.HP.lam L (i + 1))
      ≤ (({v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
  classical
  set R : ℕ := Work.HP.rk L with hRdef
  obtain ⟨f, hfL, hfLI, hfb⟩ := Work.HP.FM.exists_indep_le_lam L
  let x : Fin R → ℝ := fun j => T / (((R : ℝ) + 1) * Work.HP.lam L (j.1 + 1))
  let N : Fin R → ℕ := fun j => ⌊x j⌋₊ + 1
  let Ψ : ((j : Fin R) → Fin (N j)) → (Fin 5 → ℤ) := fun a => ∑ j, (((a j : ℕ) : ℤ)) • f j
  have hlampos : ∀ j : Fin R, 0 < Work.HP.lam L (j.1 + 1) :=
    fun j => Work.HP.lam_pos L (by omega) (by omega)
  have hxnn : ∀ j : Fin R, 0 ≤ x j := by
    intro j
    have hlam := hlampos j
    simp only [x]; positivity
  have hΨinj : Function.Injective Ψ := by
    intro a a' h
    have hg : (∑ j, (((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ)) • f j) = 0 := by
      have hsub : Ψ a - Ψ a' = ∑ j, (((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ)) • f j := by
        simp only [Ψ]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by rw [← sub_smul])
      rw [← hsub, sub_eq_zero.mpr h]
    have hzero := (Fintype.linearIndependent_iff.mp hfLI)
      (fun j => ((a j : ℕ) : ℤ) - ((a' j : ℕ) : ℤ)) hg
    funext j
    exact Fin.ext (Int.ofNat.inj (sub_eq_zero.mp (hzero j)))
  have hmem : ∀ a : ((j : Fin R) → Fin (N j)), Ψ a ∈ L := by
    intro a
    simp only [Ψ]
    exact Submodule.sum_mem L (fun j _ => Submodule.smul_mem L (((a j : ℕ) : ℤ)) (hfL j))
  have hnorm : ∀ a : ((j : Fin R) → Fin (N j)), Work.HP.eNorm (Ψ a) ≤ T := by
    intro a
    have hstep : ∀ j : Fin R, Work.HP.eNorm (((a j : ℕ) : ℤ) • f j) ≤ T / ((R : ℝ) + 1) := by
      intro j
      have hfloor : ((⌊x j⌋₊ : ℕ) : ℝ) ≤ x j := Nat.floor_le (hxnn j)
      have hNj : (N j : ℝ) = (⌊x j⌋₊ : ℝ) + 1 := by simp only [N]; push_cast; ring
      have haN : (a j : ℕ) ≤ N j - 1 := by have := (a j).2; omega
      have hcast : ((a j : ℕ) : ℝ) ≤ ((N j - 1 : ℕ) : ℝ) := by exact_mod_cast haN
      have hNsub : ((N j - 1 : ℕ) : ℝ) = ((⌊x j⌋₊ : ℕ) : ℝ) := by
        simp only [N, Nat.add_sub_cancel]
      calc Work.HP.eNorm (((a j : ℕ) : ℤ) • f j)
          = ((a j : ℕ) : ℝ) * Work.HP.eNorm (f j) := by
            rw [eNorm_smul_int, abs_of_nonneg (Nat.cast_nonneg _)]
            simp only [Int.cast_natCast]
        _ ≤ ((N j - 1 : ℕ) : ℝ) * Work.HP.eNorm (f j) :=
            mul_le_mul_of_nonneg_right hcast (Work.HP.eNorm_nonneg _)
        _ ≤ ((N j - 1 : ℕ) : ℝ) * Work.HP.lam L (j.1 + 1) :=
            mul_le_mul_of_nonneg_left (hfb j) (Nat.cast_nonneg _)
        _ = ((⌊x j⌋₊ : ℕ) : ℝ) * Work.HP.lam L (j.1 + 1) := by rw [hNsub]
        _ ≤ x j * Work.HP.lam L (j.1 + 1) :=
            mul_le_mul_of_nonneg_right hfloor (hlampos j).le
        _ = T / ((R : ℝ) + 1) := by
            simp only [x]
            rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt (hlampos j))]
    calc Work.HP.eNorm (Ψ a)
        = Work.HP.eNorm (∑ j, (((a j : ℕ) : ℤ)) • f j) := by simp only [Ψ]
      _ ≤ ∑ j, Work.HP.eNorm ((((a j : ℕ) : ℤ)) • f j) := eNorm_sum_le _ _
      _ ≤ ∑ _j : Fin R, (T / ((R : ℝ) + 1)) := Finset.sum_le_sum (fun j _ => hstep j)
      _ = (R : ℝ) * (T / ((R : ℝ) + 1)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ T := by
            have hRpos : 0 < (R : ℝ) + 1 := by positivity
            have h1 : (R : ℝ) / ((R : ℝ) + 1) ≤ 1 := by
              rw [div_le_one hRpos]; linarith
            have h2 : (R : ℝ) * (T / ((R : ℝ) + 1)) = T * ((R : ℝ) / ((R : ℝ) + 1)) := by
              field_simp
            rw [h2]
            calc T * ((R : ℝ) / ((R : ℝ) + 1)) ≤ T * 1 :=
                  mul_le_mul_of_nonneg_left h1 (by linarith)
              _ = T := by ring
  have hsub : Set.range Ψ ⊆ {v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} := by
    rintro v ⟨a, rfl⟩
    exact ⟨hmem a, hnorm a⟩
  have hfin : ({v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).Finite :=
    (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) T).subset (fun v hv => hv.2)
  have hSle : ((Set.range Ψ).ncard : ℝ)
      ≤ (({v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard hsub hfin)
  have hrange : (Set.range Ψ).ncard = ∏ j : Fin R, N j := by
    rw [Set.ncard_range_of_injective hΨinj, Nat.card_eq_fintype_card, Fintype.card_pi]
    simp
  have hprod_le : ∏ j : Fin R, (T / (((R : ℝ) + 1) * Work.HP.lam L (j.1 + 1)))
      ≤ ∏ j : Fin R, (N j : ℝ) := by
    refine Finset.prod_le_prod₀ (fun j _ => by simpa only [x] using hxnn j) (fun j _ => ?_)
    have hlt : x j < (⌊x j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (x j)
    have hNj : (N j : ℝ) = (⌊x j⌋₊ : ℝ) + 1 := by simp only [N]; push_cast; ring
    change x j ≤ (N j : ℝ)
    rw [hNj]; linarith
  have hprod_eq : ∏ j : Fin R, (T / (((R : ℝ) + 1) * Work.HP.lam L (j.1 + 1)))
      = (1 / ((R : ℝ) + 1) ^ R) * ∏ j : Fin R, (T / Work.HP.lam L (j.1 + 1)) := by
    have h1 : ∀ j : Fin R, T / (((R : ℝ) + 1) * Work.HP.lam L (j.1 + 1))
        = (1 / ((R : ℝ) + 1)) * (T / Work.HP.lam L (j.1 + 1)) := by
      intro j
      have hR : ((R : ℝ) + 1) ≠ 0 := by positivity
      have hl : Work.HP.lam L (j.1 + 1) ≠ 0 := ne_of_gt (hlampos j)
      field_simp
    rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, div_pow, one_pow]
  have hkey : (1 / ((R : ℝ) + 1) ^ R) * ∏ j : Fin R, (T / Work.HP.lam L (j.1 + 1))
      ≤ (({v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
    rw [← hprod_eq]
    calc ∏ j : Fin R, (T / (((R : ℝ) + 1) * Work.HP.lam L (j.1 + 1)))
        ≤ ∏ j : Fin R, (N j : ℝ) := hprod_le
      _ = ((∏ j : Fin R, N j : ℕ) : ℝ) := by rw [Nat.cast_prod]
      _ = ((Set.range Ψ).ncard : ℝ) := by rw [hrange]
      _ ≤ _ := hSle
  rw [← Finset.prod_range (fun i => T / Work.HP.lam L (i + 1))] at hkey
  exact hkey

end VDC

theorem vdc_lower : ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), r ≤ 3 → ∀ (L : Submodule ℤ (Fin 5 → ℤ)),
    Work.HP.rk L = r → ∀ T : ℝ, 1 ≤ T →
    c * ∏ i ∈ Finset.range r, (T / Work.HP.lam L (i + 1))
      ≤ (({v : Fin 5 → ℤ | v ∈ L ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ) := by
  refine ⟨1 / 64, by norm_num, ?_⟩
  intro r hr L hrk T hT
  have hmain := VDC.ballCount_lower L T hT
  rw [hrk] at hmain
  have hpow : ((r : ℝ) + 1) ^ r ≤ 64 := by
    have h1 : r + 1 ≤ 4 := by omega
    have h2 : (r + 1) ^ r ≤ 4 ^ 3 := by
      calc (r + 1) ^ r ≤ 4 ^ r := Nat.pow_le_pow_left h1 r
        _ ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr
    have h3 : (((r + 1) ^ r : ℕ) : ℝ) ≤ ((4 ^ 3 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    exact h3
  have hcoef : (1 / 64 : ℝ) ≤ 1 / ((r : ℝ) + 1) ^ r := by
    have hpos : 0 < ((r : ℝ) + 1) ^ r := pow_pos (by positivity) r
    exact one_div_le_one_div_of_le hpos hpow
  have hprod_nonneg : 0 ≤ ∏ i ∈ Finset.range r, (T / Work.HP.lam L (i + 1)) := by
    refine Finset.prod_nonneg (fun i hi => ?_)
    have hi' : i < r := Finset.mem_range.mp hi
    have hl : 0 < Work.HP.lam L (i + 1) := Work.HP.lam_pos L (by omega) (by omega)
    positivity
  calc (1 / 64 : ℝ) * ∏ i ∈ Finset.range r, (T / Work.HP.lam L (i + 1))
      ≤ (1 / ((r : ℝ) + 1) ^ r) * ∏ i ∈ Finset.range r, (T / Work.HP.lam L (i + 1)) :=
        mul_le_mul_of_nonneg_right hcoef hprod_nonneg
    _ ≤ _ := hmain

end Work.Q44Geom
