import Mathlib
import Submission.Work.Peluse.Ulower.finalTarget

/-!
# The box-norm power at a singleton direction set dominates a power of the mean

At the degenerate direction set `arithIcc κ 1 = {κ}` the `2^s`-th box-norm power collapses to
the ordinary average of `‖f‖^{2^s}` over the window (`Ulower.uNormPow_singleton_symIcc`), so the
comparison with the mean is Jensen's inequality for the convex function `x ↦ x^{2^s}`:

* for `s = 0` (`2^s = 1`) the two sides are *equal* (`uNormPow 0` is the normalised modulus of
  the total mass, `uNormPow_zero` below);
* for `s ≥ 1`, `mean^{2^s} ≤ (1/|S|) ∑_{x ∈ S} ‖f x‖^{2^s}` because
  `‖∑ f‖ ≤ ∑ ‖f‖` and `(∑ a_i)^n ≤ (#S)^{n-1} ∑ a_i^n` for `n ≥ 1` and `a_i ≥ 0`
  (`sum_pow_le_card_pow_mul_sum_pow`, i.e. `Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`
  transported to a natural exponent).

The constant `1` is admissible in both cases; the sum may be taken over `symIcc N` because
`SupportIn f N` kills everything outside the window.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse

noncomputable section

/-! ## The level-`0` box-norm power -/

/-- The `0`-th box-norm power is the normalised modulus of the total mass. -/
lemma uNormPow_zero (Q S : Finset ℤ) (f : ℤ → ℂ) :
    uNormPow 0 Q S f = ((S.card : ℝ))⁻¹ * ‖∑' x : ℤ, f x‖ := by
  unfold uNormPow boxNormPow boxSumPow prodCubeSum
  simp [Work.Peluse.weight, Work.Peluse.cornerShift]

/-! ## Jensen for nonnegative finite families, with a natural exponent -/

/-- For `1 ≤ n` and `aᵢ ≥ 0`, the `n`-th power of the sum is at most `(#s)^{n-1}` times the
sum of the `n`-th powers (Jensen for the convex function `x ↦ x^n`). -/
lemma sum_pow_le_card_pow_mul_sum_pow {ι : Type*} (s : Finset ι) (f : ι → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ n ≤ (s.card : ℝ) ^ (n - 1) * ∑ i ∈ s, f i ^ n := by
  have hp : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := s) (f := f) (p := (n : ℝ)) hp hf
  have hnn : ((n:ℝ) - 1) = ((n-1:ℕ):ℝ) := by rw [eq_comm, Nat.cast_sub hn, Nat.cast_one]
  have hexp : ((s.card : ℝ)) ^ ((n:ℝ) - 1) = ((s.card : ℝ)) ^ (n - 1) := by
    rw [hnn, Real.rpow_natCast]
  simpa only [Real.rpow_natCast, hexp] using h

/-- `(m⁻¹)^q · m^{q-1} = m⁻¹` for `m > 0` and `q ≥ 1`: the normalisation of the `q`-th power of
the mean against the `q`-th power of the cardinality. -/
lemma inv_pow_mul_pow_sub {m : ℝ} (hm : 0 < m) {q : ℕ} (hq : 1 ≤ q) :
    (m⁻¹) ^ q * m ^ (q - 1) = m⁻¹ := by
  have h : m ^ q = m ^ (q - 1) * m := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  rw [inv_pow, h, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

/-! ## The comparison at level `s ≥ 1` -/

/-- The `2^s`-th power of the normalised mean is at most the `2^s`-th box-norm power at the
singleton direction set `{κ}`, for `s ≥ 1`. -/
lemma meanPow_le_singleton_uNormPow {s : ℕ} (hs : 1 ≤ s) {κ : ℤ} {L : ℕ} {F : ℤ → ℂ}
    (hvan : ∀ x : ℤ, x ∉ symIcc L → F x = 0) :
    (((symIcc L).card : ℝ)⁻¹ * ‖∑' x : ℤ, F x‖) ^ (2 ^ s)
      ≤ uNormPow s ({κ} : Finset ℤ) (symIcc L) F := by
  rw [Ulower.uNormPow_singleton_symIcc (t := s) hs (c := κ) (L := L) (F := F) hvan]
  have hmpos : 0 < ((symIcc L).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩)
  have hq1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hjens : (∑ x ∈ symIcc L, ‖F x‖) ^ (2 ^ s)
      ≤ ((symIcc L).card : ℝ) ^ (2 ^ s - 1) * ∑ x ∈ symIcc L, ‖F x‖ ^ (2 ^ s) :=
    sum_pow_le_card_pow_mul_sum_pow _ _ hq1 (fun x _ => norm_nonneg _)
  have h1 : ((symIcc L).card : ℝ)⁻¹ * ‖∑' x : ℤ, F x‖
      ≤ ((symIcc L).card : ℝ)⁻¹ * ∑ x ∈ symIcc L, ‖F x‖ := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [tsum_eq_sum hvan]
    exact norm_sum_le _ _
  have h2 : (((symIcc L).card : ℝ)⁻¹ * ‖∑' x : ℤ, F x‖) ^ (2 ^ s)
      ≤ (((symIcc L).card : ℝ)⁻¹ * ∑ x ∈ symIcc L, ‖F x‖) ^ (2 ^ s) :=
    pow_le_pow_left₀ (by positivity) h1 _
  refine le_trans h2 ?_
  rw [mul_pow]
  refine le_trans (mul_le_mul_of_nonneg_left hjens (by positivity)) ?_
  rw [← mul_assoc, inv_pow_mul_pow_sub hmpos hq1]

/-! ## The target -/

theorem uNormPowGeMeanPow (s : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (κ : ℤ) (N : ℕ) (f : ℤ → ℂ), SupportIn f N → C * (((symIcc N).card : ℝ)⁻¹ * ‖∑' x : ℤ, f x‖) ^ (2 ^ s) ≤ uNormPow s (arithIcc κ 1) (symIcc N) f := by
  refine ⟨1, one_pos, ?_⟩
  intro κ N f hf
  have hvan : ∀ x : ℤ, x ∉ symIcc N → f x = 0 :=
    fun x hx => hf x (Ulower.lt_natAbs_of_notMem_symIcc hx)
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    rw [uNormPow_zero]
    simp
  · rw [Ulower.arithIcc_one_eq_singleton κ]
    simpa using meanPow_le_singleton_uNormPow hs hvan

end

end Work.Peluse.Prop36SW
