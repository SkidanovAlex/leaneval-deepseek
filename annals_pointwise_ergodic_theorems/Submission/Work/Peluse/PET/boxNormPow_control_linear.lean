import Mathlib
import Submission.Work.Peluse.PET.pet_step
import Submission.Work.Peluse.BoxNorm.prodCubeSum_norm_le
import Submission.Work.Peluse.PET.boxSumPow_last_singleton
import Submission.Work.Peluse.PET.pow_div_le
import Submission.Work.Peluse.PET.gamma_le_nine_beta
import Submission.Work.Peluse.PET.two_mul_boxNormPow_succ_ge

/-!
# Control of the box norm by the linear configuration (Peluse's Lemma 4.10, degenerate direction)

The `(m+1)`-linear average along the linear configuration `(x + c_1 y, …, x + c_m y)` dominates — as
a power of `γ` — the `m`-fold Gowers box norm of the last function `F_m` with the shift sets
`(c_m - c_{i+1})[H]`, `H = ⌊γ' M⌋`.  Note that the last shift set is degenerate
(`arithIcc 0 H = {0}`), so the box norm is really the `(m-1)`-fold box norm of `|F_m|²`.

The proof is the following chain.

* (`norm_lambda_le`, `gamma_le_nine_beta`) All the factors other than `F_m` are `1`-bounded and
  `x ↦ x + c_m y` is a bijection of `ℤ`, so the average is at most `‖F_m‖₁ / N`; combined with
  Cauchy–Schwarz on `symIcc N` this gives `γ / 9 ≤ β`, where
  `β = (∑_{x ∈ symIcc N} ‖F_m x‖²)/|symIcc N|` is the normalised `L²` mass of `F_m`.
* (`boxSumPow_last_singleton`) Since the last shift set is `{0}`, the cube term of the `m`-fold box
  sum collapses pairwise (`starᵏ f · starᵏ⁺¹ f = ‖f‖²`), so
  `boxSumPow m Q S f = boxSumPow (m-1) Q' S (‖f‖²)`.
* (`boxNormPow_iterate_ge`) For a nonnegative real `h` supported in `symIcc N` and shift sets of
  diameter `≤ 2N`, iterating the Cauchy–Schwarz recursion `2 B_t ≥ B_{t-1}²` gives
  `β^{2^t} ≤ 2^{2^t - 1} B_t`.
* (`pow_div_le`) Finally `(γ/1000)^{2^t} ≤ β^{2^t}/2^{2^t-1}`, because `1000` absorbs the factor
  `2` and `γ ≤ 1`.

The requested statement follows with `K = 2^{m-1}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-- The degenerate shift set `arithIcc 0 H` is the singleton `{0}` as soon as `H ≥ 1`. -/
lemma control_linear_arithIcc_zero {H : ℕ} (hH : 1 ≤ H) :
    Work.Peluse.arithIcc (0 : ℤ) H = ({0} : Finset ℤ) := by
  rw [Work.Peluse.arithIcc]
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    ring
  · intro hx
    exact ⟨1, ⟨le_refl 1, hH⟩, by rw [hx]; ring⟩

/-- `arithIcc d H` is nonempty as soon as `H ≥ 1`. -/
lemma control_linear_arithIcc_nonempty {d : ℤ} {H : ℕ} (hH : 1 ≤ H) :
    (Work.Peluse.arithIcc d H).Nonempty := by
  rw [Work.Peluse.arithIcc, Finset.image_nonempty]
  exact ⟨1, by simp [hH]⟩


/-- The box norm of order `0` is the normalised `L¹` mass. -/
private lemma control_linear_boxNormPow_zero {N : ℕ} (Q : Fin 0 → Finset ℤ) (h : ℤ → ℂ)
    (hsupp : Work.Peluse.SupportIn h N) (hreal : ∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) :
    Work.Peluse.boxNormPow 0 Q (Work.Peluse.symIcc N) h
      = (∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) / (((Work.Peluse.symIcc N).card : ℕ) : ℝ) := by
  have hwin : Work.Peluse.BoxNorm.winWindow 0 Q N = Work.Peluse.symIcc N := by
    simp [Work.Peluse.BoxNorm.winWindow, Work.Peluse.symIcc]
  have hsum : (∑ x ∈ Work.Peluse.symIcc N, h x)
      = (((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => hreal x
  have hbox : Work.Peluse.boxSumPow 0 Q (Work.Peluse.symIcc N) h
      = ((Work.Peluse.symIcc N).card : ℂ)⁻¹
        * (((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) : ℝ) : ℂ) := by
    rw [Work.Peluse.boxSumPow,
      Work.Peluse.BoxNorm.prodCubeSum_eq_const_mul_winForm Q (Work.Peluse.symIcc N)
        (fun _ : Fin 0 → Bool => h) (fun _ => hsupp),
      hwin, Work.Peluse.BoxNorm.winForm_zero]
    simp only [Work.Peluse.BoxNorm.cubeConst, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [hsum]
  rw [Work.Peluse.boxNormPow, hbox]
  have hcard : ((Work.Peluse.symIcc N).card : ℂ)
      = ((((Work.Peluse.symIcc N).card : ℕ) : ℝ) : ℂ) := (Complex.ofReal_natCast _).symm
  rw [hcard, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)),
    div_eq_inv_mul, mul_comm]

/-- Iterating the Cauchy--Schwarz recursion `2 B_{t+1} ≥ B_t²` (with `B_t` the `t`-fold box norm
of a nonnegative real function with the first `t` shift sets). -/
private theorem control_linear_iterate_ge {t : ℕ} (Q : Fin t → Finset ℤ) {N : ℕ} (hN : 0 < N)
    (h : ℤ → ℂ) (hQ : ∀ i, (Q i).Nonempty) (hbd : ∀ i a, a ∈ Q i → |a| ≤ (N : ℤ))
    (hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → h x = 0)
    (hreal : ∀ x : ℤ, h x = ((‖h x‖ : ℝ) : ℂ)) :
    ((∑ x ∈ Work.Peluse.symIcc N, ‖h x‖) / (((Work.Peluse.symIcc N).card : ℕ) : ℝ)) ^ (2 ^ t)
      ≤ 2 ^ (2 ^ t - 1) * Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) h := by
  have hsuppIn : Work.Peluse.SupportIn h N := by
    intro x hx
    apply hsupp
    intro hmem
    simp only [Work.Peluse.symIcc, Finset.mem_Icc] at hmem
    have hle : |x| ≤ (N : ℤ) := abs_le.mpr hmem
    have hcast : ((x.natAbs : ℤ)) = |x| := Int.natCast_natAbs x
    have h2 : ((x.natAbs : ℤ)) ≤ (N : ℤ) := by rw [hcast]; exact hle
    have h3 : x.natAbs ≤ N := by exact_mod_cast h2
    omega
  induction t with
  | zero =>
    have h0 := control_linear_boxNormPow_zero (N := N) Q h hsuppIn hreal
    rw [h0]
    norm_num
  | succ t ih =>
    set B : ℝ := Work.Peluse.boxNormPow t (fun i : Fin t => Q i.castSucc)
      (Work.Peluse.symIcc N) h with hB
    set β : ℝ := (∑ x ∈ Work.Peluse.symIcc N, ‖h x‖)
      / (((Work.Peluse.symIcc N).card : ℕ) : ℝ) with hβ
    have hih : β ^ (2 ^ t) ≤ 2 ^ (2 ^ t - 1) * B :=
      ih (fun i : Fin t => Q i.castSucc) (fun i => hQ i.castSucc)
        (fun i a ha => hbd i.castSucc a ha)
    have hstep : B ^ 2 ≤ 2 * Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) h :=
      two_mul_boxNormPow_succ_ge Q hN h hQ (hbd (Fin.last t)) hsupp hreal
    have hβnn : 0 ≤ β := by
      rw [hβ]
      exact div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _)
    have h2nn : ∀ k : ℕ, (0 : ℝ) ≤ 2 ^ k := fun k => pow_nonneg (by norm_num) k
    have hexp : (2 ^ t - 1) * 2 = 2 ^ (t + 1) - 2 := by
      have h1 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    have h1 : β ^ (2 ^ (t + 1)) = (β ^ (2 ^ t)) ^ 2 := by rw [Nat.pow_succ, ← pow_mul]
    have h2 : (β ^ (2 ^ t)) ^ 2 ≤ (2 ^ (2 ^ t - 1) * B) ^ 2 :=
      pow_le_pow_left₀ (pow_nonneg hβnn _) hih 2
    have h3 : (2 ^ (2 ^ t - 1) * B) ^ 2 = 2 ^ ((2 ^ t - 1) * 2) * B ^ 2 := by
      rw [mul_pow, pow_mul]
    have h4 : 2 ^ ((2 ^ t - 1) * 2) * B ^ 2
        ≤ 2 ^ (2 ^ (t + 1) - 2)
            * (2 * Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) h) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left hstep (h2nn _)
    have h5 : 2 ^ (2 ^ (t + 1) - 2)
          * (2 * Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) h)
        = 2 ^ (2 ^ (t + 1) - 1)
          * Work.Peluse.boxNormPow (t + 1) Q (Work.Peluse.symIcc N) h := by
      have hk : 2 ^ (t + 1) - 2 + 1 = 2 ^ (t + 1) - 1 := by
        have h1 : (1 : ℕ) ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
        omega
      rw [← hk, pow_succ]
      ring
    exact le_trans (le_trans (le_of_eq h1) (le_trans h2 (le_of_eq h3)))
      (le_trans h4 (le_of_eq h5))

end

end Work.Peluse.PET
