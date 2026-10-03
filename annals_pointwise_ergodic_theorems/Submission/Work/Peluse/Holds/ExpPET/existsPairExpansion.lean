import Mathlib
import Submission.Work.Peluse.Holds.ExpPET.Expansion
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# From the averaged box norm to one good label pair (the `ExpansionPETShort` brick (B))

`Work.Peluse.Holds.ExpansionPETShort` starts from a lower bound for the average over
`a ∈ [1,M₂]` of the level-`s` box norm of `f` at the direction sets `Q_i(a) = (c·a + b_i)[M₁]`.

This module performs the first half of the expansion step: after

* Jensen (`ExpPET/Jensen.lean`) passes from the box *norm* to the box-norm *power*,
* the box sum is a nonnegative real (`BoxNorm.boxSumPow_eq_boxNormPow`), so
  `boxNormPow = (boxSumPow).re`, and
* `ExpPET.Expansion.boxSumPow_arithIcc_eq` expands each `boxSumPow s (Q(a)) S f` into the
  double sum over the *labels* `(k,k') ∈ ([1,M₁]^s)²` of the cube terms `expCube (Q(a)) k̃ k̃'`,

one may exchange the `a`-sum with the `(k,k')`-sum (Fubini) and read off that the *maximum* over the
`M₁^{2s}` label pairs of the complex number

  `Λ_{k,k'} = ∑_{a ∈ [1,M₂]} ∑'_x expCube (Q(a)) k̃ k̃' f x`

dominates `δ^{2^s}·|S|·M₂`.  **No Markov lemma is needed** — a mean-value argument on the real part
(which is what the nonnegativity of the box sum supplies) already produces one pair, and the PET step
(`PetLinear.linear_boxnorm_control_paper`) consumes a single pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Work.Peluse.Holds.ExpPET

open Work.Peluse

noncomputable section

/-- The cardinality of the label set `(i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}` is `M₁ ^ s`.
(Stated with `Finset.univ.card` because `Fintype.card` at this type does not elaborate in
declaration statements.) -/
lemma card_labels (s M₁ : ℕ) :
    (Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁})).card = M₁ ^ s := by
  rw [Finset.card_univ, Fintype.card_fun]
  have h1 : Fintype.card (Fin s) = s := Fintype.card_fin s
  rw [h1]
  congr 1
  rw [Fintype.card_coe, Nat.card_Icc]
  omega

/-- The reciprocal of the label normalisation `(M₁⁻¹)^s` squared is `(M₁^s)^2`. -/
lemma inv_labelNorm (s M₁ : ℕ) :
    (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹ = (((M₁ : ℝ)) ^ s) ^ 2 := by
  rw [inv_pow, inv_pow, inv_inv]

/-- **Mean-value extraction**: a family of reals whose *average* dominates `θ` has an element `≥ θ`. -/
lemma exists_le_of_le_card_mul {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → ℝ) {θ : ℝ}
    (h : θ * (((Finset.univ : Finset ι).card : ℕ) : ℝ) ≤ ∑ i, y i) : ∃ i, θ ≤ y i := by
  by_contra hc
  push_neg at hc
  have h2 : ∑ i, y i < ∑ _i : ι, θ :=
    Finset.sum_lt_sum (fun i _ => le_of_lt (hc i))
      ⟨Classical.arbitrary ι, Finset.mem_univ _, hc _⟩
  have h3 : ∑ _i : ι, θ = (((Finset.univ : Finset ι).card : ℕ) : ℝ) * θ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h3] at h2
  nlinarith [h]

/-- **The expansion + Fubini + mean-value brick.** -/
theorem exists_pair_expansion {s M₁ M₂ : ℕ} (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (c : ℤ)
    (b : Fin s → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) {δ : ℝ} (hδ : 0 < δ) (hfin : FinSuppZ f)
    (hbox : δ ^ (2 ^ s) ≤ ((M₂ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
        boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f) :
    ∃ k k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
      δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ) ≤
        ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
  classical
  -- (0) the box sum is a nonnegative real
  have hreal : ∀ a ∈ Finset.Icc 1 M₂,
      boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f
        = ((boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f : ℝ) : ℂ) :=
    fun a _ => BoxNorm.boxSumPow_eq_boxNormPow hs hfin
  have hreal' : ∀ a ∈ Finset.Icc 1 M₂,
      boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f
        = (boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f).re := by
    intro a ha
    rw [hreal a ha, Complex.ofReal_re]
  have hnorm : (∑ a ∈ Finset.Icc 1 M₂,
        boxNormPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f)
      = (∑ a ∈ Finset.Icc 1 M₂,
          boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f).re := by
    rw [Finset.sum_congr rfl hreal']
    simp only [← Complex.coe_reAddGroupHom]
    exact (map_sum Complex.reAddGroupHom
      (fun a : ℕ => boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f)
      (Finset.Icc 1 M₂)).symm
  -- (1) the expansion of the box sum at the arithmetic-progression direction sets
  have hexp : ∀ a : ℕ,
      boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f
        = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
            * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                  ∑' x : ℤ, expCube (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)) :=
    fun a => boxSumPow_arithIcc_eq hM₁ (fun i : Fin s => c * (a : ℤ) + b i) S f
  -- (2) Fubini
  have hsum : (∑ a ∈ Finset.Icc 1 M₂,
        boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f)
      = ((S.card : ℂ))⁻¹ * ((∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2
          * (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
                ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                  expCube (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x)) := by
    rw [Finset.sum_congr rfl (fun a _ => hexp a), ← Finset.mul_sum]
    congr 1
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm (s := Finset.Icc 1 M₂)
      (t := (Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁})))]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Finset.sum_comm (s := Finset.Icc 1 M₂)
      (t := (Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁})))
  -- the label sum, as a single complex number
  set T : ℂ := (∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
      ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
          expCube (fun i : Fin s => c * (a : ℤ) + b i)
            (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x) with hT
  -- (3) the constants are real
  have hre1 : ((S.card : ℂ))⁻¹ = ((((S.card : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_inv (S.card : ℝ)).symm
  have hK : (∏ i : Fin s, (((M₁ : ℂ))⁻¹)) ^ 2 = ((((((M₁ : ℝ))⁻¹) ^ s) ^ 2 : ℝ) : ℂ) := by
    have h1 : (∏ i : Fin s, (((M₁ : ℂ))⁻¹)) = (((((M₁ : ℝ))⁻¹) ^ s : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_fin]
      rw [show (M₁ : ℂ) = (((M₁ : ℝ)) : ℂ) from (Complex.ofReal_natCast M₁).symm,
        ← Complex.ofReal_inv, ← Complex.ofReal_pow]
    rw [h1, ← Complex.ofReal_pow]
  have hreT : (∑ a ∈ Finset.Icc 1 M₂,
        boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f).re
      = ((S.card : ℝ))⁻¹ * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2) * T.re := by
    rw [hsum, hre1, hK]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  -- (4) positivity of the ingredients
  have hM1r : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁
  have hM2r : (0 : ℝ) < (M₂ : ℝ) := by exact_mod_cast hM₂
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · exfalso
      have h0 : ((S.card : ℂ))⁻¹ = 0 := by rw [h]; simp
      have h6 : (∑ a ∈ Finset.Icc 1 M₂,
          boxSumPow s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) S f) = 0 := by
        rw [hsum, h0, zero_mul]
      rw [hnorm, h6, Complex.zero_re, mul_zero] at hbox
      have hpos : 0 < δ ^ (2 ^ s) := pow_pos hδ _
      linarith
    · exact_mod_cast h
  have hp : (0 : ℝ) < ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 := by positivity
  -- (5) the lower bound for the real part of the label sum
  have hTlow : δ ^ (2 ^ s) * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)
      ≤ T.re := by
    have h1 := hbox
    rw [hnorm, hreT] at h1
    have h3 := mul_le_mul_of_nonneg_right h1
      (by positivity : (0 : ℝ) ≤ (M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹)
    have hM2ne : (M₂ : ℝ) ≠ 0 := ne_of_gt hM2r
    have hSne : (S.card : ℝ) ≠ 0 := ne_of_gt hSpos
    have hpne : ((((M₁ : ℝ))⁻¹) ^ s) ^ 2 ≠ 0 := ne_of_gt hp
    have h4 : ((M₂ : ℝ))⁻¹ * (((S.card : ℝ))⁻¹ * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2) * T.re)
          * ((M₂ : ℝ) * (S.card : ℝ) * (((((M₁ : ℝ))⁻¹) ^ s) ^ 2)⁻¹) = T.re := by
      field_simp
    rw [h4] at h3
    exact h3
  -- (6) the norm of the label sum dominates its real part
  have hnormT : T.re
      ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
    refine le_trans (Complex.re_le_norm T) ?_
    rw [hT]
    calc ‖∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖
        ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
              ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                  expCube (fun i : Fin s => c * (a : ℤ) + b i)
                    (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ :=
          Finset.sum_le_sum fun k _ => norm_sum_le _ _
  -- (7) the mean-value extraction
  have hcardR : ((((Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}))).card : ℕ) : ℝ)
      = ((M₁ : ℝ)) ^ s := by
    rw [card_labels s M₁, Nat.cast_pow]
  have hmain : δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ) * ((M₁ : ℝ)) ^ s
        * ((M₁ : ℝ)) ^ s
      ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
    have hv := inv_labelNorm s M₁
    rw [hv] at hTlow
    refine le_trans ?_ hnormT
    calc δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ) * ((M₁ : ℝ)) ^ s * ((M₁ : ℝ)) ^ s
        = δ ^ (2 ^ s) * ((M₂ : ℝ) * (S.card : ℝ) * (((M₁ : ℝ)) ^ s) ^ 2) := by ring
      _ ≤ T.re := hTlow
  haveI : Nonempty ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}) :=
    ⟨fun _ => ⟨1, by rw [Finset.mem_Icc]; exact ⟨le_rfl, hM₁⟩⟩⟩
  have h4 : δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ) * ((M₁ : ℝ)) ^ s
        * ((((Finset.univ : Finset ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}))).card : ℕ) : ℝ)
      ≤ ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
            ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
                expCube (fun i : Fin s => c * (a : ℤ) + b i)
                  (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖ := by
    rw [hcardR]
    exact hmain
  obtain ⟨k, hk⟩ := exists_le_of_le_card_mul
    (fun k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁} =>
      ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
            expCube (fun i : Fin s => c * (a : ℤ) + b i)
              (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖)
    (θ := δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ) * ((M₁ : ℝ)) ^ s) h4
  obtain ⟨k', hk'⟩ := exists_le_of_le_card_mul
    (fun k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁} =>
      ‖∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
          expCube (fun i : Fin s => c * (a : ℤ) + b i)
            (fun i => ((k i).1 : ℤ)) (fun i => ((k' i).1 : ℤ)) f x‖)
    (θ := δ ^ (2 ^ s) * (S.card : ℝ) * (M₂ : ℝ))
    (by rw [hcardR]; exact hk)
  exact ⟨k, k', hk'⟩

end

end Work.Peluse.Holds.ExpPET
