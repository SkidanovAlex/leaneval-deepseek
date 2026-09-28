import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.DN.SM_ratio_tendsto
import Submission.Work.HP.DN.SM_sandwich

/-!
# N14.  Density of `LocSet(w)`

The statement below is node N14 of `DESIGN.md` (the requested lemma, unchanged), proved here as
the assembly of the `Work.HP.DN` nodes.

## Route (lead's design review `requests/hasse2/DESIGN_REVIEW.md` §2)

The fixed level of the earlier route (`LocSet d n M`, exponents `r_p(M)`) loses `≍ 1/log M` to
the deep `p`-adic failures, so the review replaces it by the uniform exponent `4M`:

* `DN.SM d n M a` = `RealSol d n a ∧ ∀ p ≤ M, p prime → PrimModZero d n a p (4 * M)`;
* **D6** (`DN.SM_ratio_tendsto`): for each fixed `M` the ratio `ratio (SM M)` converges;
* **D9** (`DN.SM_sandwich`): for admissible `w` the ratio `ratio (LocSet (w A))` is eventually
  sandwiched between `ratio (SM M)` and `ratio (SM M) - C (M/4^M + 1/M)`.

This file is the assembly: `SM (M+1) ⊆ SM M`, so the limits `dM M` are antitone and their
infimum is their limit; the upper half of the sandwich gives `limsup ≤ dM M` for every `M`
(hence `limsup ≤ inf_M dM M`), and the lower half gives
`liminf ≥ dM M - C (M/4^M + 1/M)` (hence `liminf ≥ inf_M dM M`).  So the limit exists and equals
`sInf (range dM)`, independently of `w`.
-/

set_option autoImplicit false

noncomputable section

open Filter Finset

namespace Work.HP

/-! ## Elementary facts about the height ball (used by the assembly and by the DN nodes) -/

section Elem
variable {ι : Type*} [Fintype ι]

lemma density_eNorm_nonneg (a : ι → ℤ) : 0 ≤ eNorm a := Real.sqrt_nonneg _

lemma density_sq_coord_le_sum_sq (a : ι → ℤ) (i : ι) :
    ((a i : ℝ)) ^ 2 ≤ ∑ j, ((a j : ℝ)) ^ 2 :=
  Finset.single_le_sum (s := Finset.univ) (f := fun j => ((a j : ℝ)) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

/-- Every coordinate of a vector is bounded by its Euclidean norm. -/
lemma density_abs_coord_le_eNorm (a : ι → ℤ) (i : ι) : |(a i : ℝ)| ≤ eNorm a := by
  rw [eNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (density_sq_coord_le_sum_sq a i)

end Elem

variable (d n : ℕ)

/-- The coordinate box of radius `⌈A⌉₊`, as a finite set of coefficient vectors. -/
def densityBox (A : ℝ) : Finset (Mon d n → ℤ) :=
  Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ))

lemma density_primSet_subset_box (A : ℝ) (P : (Mon d n → ℤ) → Prop) : primSet d n A P ⊆ ↑(densityBox d n A) := by
  intro a ha
  obtain ⟨-, hA, -⟩ := ha
  rw [densityBox, Finset.mem_coe, Fintype.mem_piFinset]
  intro m
  have h1 : |(a m : ℝ)| ≤ A := le_trans (density_abs_coord_le_eNorm a m) hA
  have h2 : |(a m : ℝ)| ≤ (⌈A⌉₊ : ℝ) := h1.trans (Nat.le_ceil A)
  have h3 : ((a m : ℤ) : ℝ) ≤ ((⌈A⌉₊ : ℤ) : ℝ) := (abs_le.mp h2).2
  have h4 : ((-(⌈A⌉₊ : ℤ) : ℤ) : ℝ) ≤ ((a m : ℤ) : ℝ) := by
    push_cast
    linarith [(abs_le.mp h2).1]
  rw [Finset.mem_Icc]
  exact ⟨by exact_mod_cast h4, by exact_mod_cast h3⟩

/-- **Finiteness of the height ball** (node N01, first conjunct). -/
theorem density_primSet_finite (A : ℝ) (P : (Mon d n → ℤ) → Prop) : (primSet d n A P).Finite :=
  (densityBox d n A).finite_toSet.subset (density_primSet_subset_box d n A P)

lemma density_primCount_nonneg (A : ℝ) (P : (Mon d n → ℤ) → Prop) : 0 ≤ primCount d n A P := by
  rw [primCount]; positivity

lemma density_ratio_nonneg (A : ℝ) (P : (Mon d n → ℤ) → Prop) : 0 ≤ ratio d n A P := by
  rw [ratio]; exact div_nonneg (density_primCount_nonneg d n A P) (density_primCount_nonneg d n A _)

lemma density_primSet_mono {A A' : ℝ} {P P' : (Mon d n → ℤ) → Prop} (hA : A ≤ A')
    (hP : ∀ a, P a → P' a) : primSet d n A P ⊆ primSet d n A' P' :=
  fun a ha => ⟨ha.1, ha.2.1.trans hA, hP a ha.2.2⟩

/-- Monotonicity of `ratio` in the predicate: a stronger condition has a smaller ratio. -/
theorem density_ratio_mono {A : ℝ} {P P' : (Mon d n → ℤ) → Prop} (hP : ∀ a, P a → P' a) :
    ratio d n A P ≤ ratio d n A P' := by
  rw [ratio, ratio]
  refine div_le_div_of_nonneg_right ?_ ?_
  · rw [primCount, primCount]
    exact_mod_cast Set.ncard_le_ncard (density_primSet_mono d n le_rfl hP) (density_primSet_finite d n A P')
  · rw [primCount]; positivity

end Work.HP

namespace Work.HP

open Filter

private lemma sq_le_four_pow (M : ℕ) : M ^ 2 ≤ 4 ^ M := by
  calc M ^ 2 ≤ (2 ^ M) ^ 2 := Nat.pow_le_pow_left (le_of_lt (Nat.lt_two_pow_self)) 2
    _ = 4 ^ M := by
        rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        congr 1
        omega

private lemma div_pow_four_le_inv (M : ℕ) (hM : 1 ≤ M) : (M : ℝ) / 4 ^ M ≤ 1 / (M : ℝ) := by
  have h : ((M : ℝ)) ^ 2 ≤ (4 : ℝ) ^ M := by exact_mod_cast sq_le_four_pow M
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [pow_two] using h

private lemma exists_small_mul (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ M : ℕ, 1 ≤ M ∧ C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) < δ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (2 * C / δ))
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := le_trans (le_max_left _ _) (le_of_lt hM)
    exact_mod_cast this
  refine ⟨M, hM1, ?_⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hbound : (M : ℝ) / 4 ^ M + 1 / (M : ℝ) ≤ 2 / (M : ℝ) := by
    have h := div_pow_four_le_inv M hM1
    have h2 : 2 / (M : ℝ) = 1 / (M : ℝ) + 1 / (M : ℝ) := by ring
    linarith
  have hstep : C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) ≤ 2 * C / (M : ℝ) := by
    calc C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) ≤ C * (2 / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound hC.le
      _ = 2 * C / (M : ℝ) := by ring
  refine lt_of_le_of_lt hstep ?_
  have h2C : 2 * C / δ < (M : ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
  rw [div_lt_iff₀ hMpos]
  rw [div_lt_iff₀ hδ] at h2C
  linarith

/-- N14. Density of `LocSet(w)` converges to one limit for every `w → ∞` with `w(A) ≤ A`
(replaces Poonen–Voloch). -/
theorem density (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ L : ℝ, ∀ w : ℝ → ℝ, Tendsto w atTop atTop → (∀ᶠ A in atTop, w A ≤ A) →
      Tendsto (fun A => ratio d n A (LocSet d n (w A))) atTop (nhds L) := by
  classical
  obtain ⟨C, hC, hsw⟩ := DN.SM_sandwich d n hd hn
  choose dM hdM using fun M : ℕ => DN.SM_ratio_tendsto d n hd hn M
  -- the fixed-level limits are antitone in `M`, since `SM (M+1) ⊆ SM M`
  have hanti : ∀ M M' : ℕ, M ≤ M' → dM M' ≤ dM M := by
    intro M M' hMM
    refine le_of_tendsto_of_tendsto (hdM M') (hdM M) (Filter.Eventually.of_forall ?_)
    intro A
    have hpoint : ∀ a : Mon d n → ℤ, DN.SM d n M' a → DN.SM d n M a := by
      intro a ha
      refine ⟨ha.1, fun p hp hpM => ?_⟩
      obtain ⟨x, hx, hdvd⟩ := ha.2 p hp (le_trans hpM hMM)
      exact ⟨x, hx, (pow_dvd_pow _ (by omega : 4 * M ≤ 4 * M')).trans hdvd⟩
    exact density_ratio_mono d n hpoint
  -- every `dM M` is nonnegative, so the range is bounded below
  have hbdd : BddBelow (Set.range dM) := ⟨0, by
    rintro y ⟨M, rfl⟩
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hdM M)
      (Filter.Eventually.of_forall fun A => density_ratio_nonneg d n A _)⟩
  refine ⟨sInf (Set.range dM), ?_⟩
  intro w hw hwA
  set ℓ := sInf (Set.range dM) with hℓ
  have hℓle : ∀ M : ℕ, ℓ ≤ dM M := fun M => csInf_le hbdd (Set.mem_range_self M)
  have hex : ∀ b : ℝ, ℓ < b → ∃ M : ℕ, dM M < b := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    exact absurd (le_csInf (Set.range_nonempty dM) (by rintro y ⟨M, rfl⟩; exact hcon M))
      (not_le.mpr hb)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bound
    intro b hb
    have hδpos : 0 < (ℓ - b) / 2 := by linarith
    obtain ⟨M, hM1, hM2⟩ := exists_small_mul C ((ℓ - b) / 2) hC hδpos
    have hstrict : ℓ - (ℓ - b) / 2 < dM M := by
      have h1 : ℓ ≤ dM M := hℓle M
      linarith
    filter_upwards [hsw M hM1 w hw hwA,
      (hdM M).eventually (eventually_gt_nhds hstrict)] with A hA1 hA2
    have h4 : ratio d n A (DN.SM d n M) - C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) ≤
        ratio d n A (LocSet d n (w A)) := by linarith [hA1.2]
    have h5 : ℓ - (ℓ - b) / 2 < ratio d n A (DN.SM d n M) := hA2
    have h6 : C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) < (ℓ - b) / 2 := hM2
    linarith
  · -- upper bound
    intro b hb
    obtain ⟨M₀, hM₀⟩ := hex b hb
    have hM₀le : dM (max M₀ 1) ≤ dM M₀ := hanti M₀ (max M₀ 1) (le_max_left _ _)
    filter_upwards [hsw (max M₀ 1) (le_max_right _ _) w hw hwA,
      (hdM (max M₀ 1)).eventually (eventually_lt_nhds (lt_of_le_of_lt hM₀le hM₀))] with A hA1 hA2
    exact lt_of_le_of_lt hA1.1 hA2

end Work.HP
