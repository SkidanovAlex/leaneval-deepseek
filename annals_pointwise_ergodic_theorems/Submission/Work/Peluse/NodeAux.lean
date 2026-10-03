import Mathlib
import Submission.Work.Peluse.Pairing.boxSumPow_star
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions
import Submission.Work.Peluse.Concat.arithIcc_shrink_ge_two
import Submission.Work.Peluse.Pairing.cs_dualFn_step
import Submission.Work.Peluse.PET.pet_step
import Submission.Work.Peluse.UControl.arith_final

/-!
# Shared interface facts of the `U`-control area

These are the elementary `U`-norm/`LambdaZ` interface lemmas that several files of the area need
(they used to live in `Submission/Work/Peluse/ucontrol_of_concat.lean`); keeping them in their own
module lets `Submission/Work/Peluse/PaperRoute/ucontrolPaper_of_piecePet.lean` import them *without*
importing the node `Work.Peluse.ucontrol_of_concat` (which would be a cycle once the node consumes
the paper route's `PeluseUControlPaper`).

* `boxNormPow_star` / `uNormPow_star`: conjugation invariance;
* `norm_dualFn_le_one`, `dualFn_supportIn_dSup`: the dual function's sup-norm and support;
* `le_dSup`, `LambdaZ_scale`: enlarging the `x`-range;
* `arithIcc_neg`, `boxNormPow_symIcc_ratio`, `boxSumPow_eq_inv_mul_common`, `uNormPow_arithIcc_neg`,
  `uNormPow_arithIcc_shrink`, `uNormPow_direction_bridge`: the direction-set bookkeeping;
* `lc_natAbs_mul_pow_le_polySup`, `polySup_le_sum_coeff_mul_pow`,
  `leadingCoeff_ne_zero_of_two_le_natDegree`, `one_le_leadingCoeff_natAbs`: coefficient arithmetic.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-- Convergence of `∑' x, star (f x)` is not needed: the box sum of `star ∘ f` is the conjugate of
that of `f` (`Work.Peluse.Pairing.boxSumPow_star`), so the box-norm powers agree. -/
theorem boxNormPow_star {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow t Q S (fun x => star (f x)) = boxNormPow t Q S f := by
  rw [boxNormPow, boxNormPow, Pairing.boxSumPow_star, norm_star]

/-- Conjugation invariance of the uniformity norm: `‖conj ∘ f‖_{U^s} = ‖f‖_{U^s}`. -/
theorem uNormPow_star {s : ℕ} (Q : Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    uNormPow s Q S (fun x => star (f x)) = uNormPow s Q S f :=
  boxNormPow_star (fun _ : Fin s => Q) S f

/-- The dual function is `1`-bounded whenever its two slots are (used by `boxNormPow_le_one` to
reduce the box norm of `F₂` to the `sup`-norm bound). -/
theorem norm_dualFn_le_one {N : ℕ} (hN : 0 < N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h₀ : ∀ x, ‖f₀ x‖ ≤ 1) (h₁ : ∀ x, ‖f₁ x‖ ≤ 1) :
    ∀ x, ‖dualFn N P f₀ f₁ x‖ ≤ 1 := by
  intro x
  rw [dualFn, norm_mul]
  have hNc : ‖((N : ℂ))⁻¹‖ = ((N : ℝ))⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  rw [hNc]
  have h1 : ‖∑ y ∈ Finset.Icc 1 N,
      f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ ≤ (N : ℝ) := by
    calc ‖∑ y ∈ Finset.Icc 1 N,
          f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖
        ≤ ∑ y ∈ Finset.Icc 1 N,
            ‖f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _y ∈ Finset.Icc 1 N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul]
          exact mul_le_one₀ (h₀ _) (norm_nonneg _) (h₁ _)
      _ = (N : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
          simp
  calc ((N : ℝ))⁻¹ * _ ≤ ((N : ℝ))⁻¹ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by
        have h : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hN
        field_simp

/-! ## Interface facts for the scale and direction bookkeeping of the assembly -/

/-- The support parameter `dSup P N₀ N = N₀ + polySup P N` dominates `N₀`. -/
theorem le_dSup (P : Polynomial ℤ) (N₀ N : ℕ) : N₀ ≤ dSup P N₀ N :=
  Nat.le_add_right _ _

/-- Rescaling the `x`-range of `LambdaZ`: the `x`-sum is over all of `ℤ`, so only the normalising
factor `((N₀ : ℂ) * (N : ℂ))⁻¹` changes.  Used by the assembly to enlarge the support parameter of
the `x`-range from `N₀` to `dSup P N₀ N` (`dualFn` is supported on the larger box). -/
theorem LambdaZ_scale (P : Polynomial ℤ) (N₀ N₀' N : ℕ) (hN₀ : (N₀ : ℂ) ≠ 0)
    (f₀ f₁ f₂ : ℤ → ℂ) :
    LambdaZ N₀' N P f₀ f₁ f₂ = ((N₀ : ℂ) * ((N₀' : ℂ))⁻¹) * LambdaZ N₀ N P f₀ f₁ f₂ := by
  have h : ((N₀' : ℂ) * (N : ℂ))⁻¹
      = ((N₀ : ℂ) * ((N₀' : ℂ))⁻¹) * (((N₀ : ℂ) * (N : ℂ))⁻¹) := by
    rw [mul_inv_rev, mul_inv_rev]
    field_simp
    try ring_nf
  simp only [LambdaZ]
  rw [h, mul_assoc]

/-- The direction set `c[D]` is the reflection of `(-c)[D]`: used to reduce the sign of
`P.leadingCoeff` (which may be negative) to the positive case, where
`Work.Peluse.Concat.arithIcc_shrink_ge_two` applies.  Together with
`Work.Peluse.Pairing.boxSumPow_neg_directions` this gives
`boxNormPow t (arithIcc c D) (symIcc N) f = boxNormPow t (arithIcc (-c) D) (symIcc N) (f ∘ neg)` for
every `c ≠ 0`. -/
theorem arithIcc_neg (c : ℤ) (D : ℕ) : arithIcc c D = (arithIcc (-c) D).image Neg.neg := by
  rw [arithIcc, arithIcc, Finset.image_image]
  congr 1
  funext n
  simp

/-- The box sum is `|S|⁻¹` times a factor independent of the ambient set `S` (the sums over `x` and
over the shift tuples do not involve `S`). -/
theorem boxSumPow_eq_inv_mul_common {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    ∃ A : ℂ, ∀ S : Finset ℤ, boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A := by
  refine ⟨(∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)), ?_⟩
  intro S
  simp only [boxSumPow, prodCubeSum_eq]
  ring

/-- Changing the ambient set `S` rescales the box-norm power by the ratio of the cardinalities.
This is the step that lets the assembly move between the support box `symIcc N₀` of the PET/§5
chapters and the support box `symIcc (dSup P N₀ N)` of `PeluseUControl`. -/
theorem boxNormPow_symIcc_ratio {t : ℕ} (Q : Fin t → Finset ℤ) (N N' : ℕ) (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc N') f
      = (((symIcc N).card : ℕ) : ℝ) / (((symIcc N').card : ℕ) : ℝ) *
          boxNormPow t Q (symIcc N) f := by
  obtain ⟨A, hA⟩ := boxSumPow_eq_inv_mul_common Q f
  have h1 : boxSumPow t Q (symIcc N') f = (((symIcc N').card : ℂ))⁻¹ * A := hA _
  have h2 : boxSumPow t Q (symIcc N) f = (((symIcc N).card : ℂ))⁻¹ * A := hA _
  rw [boxNormPow, boxNormPow, h1, h2, norm_mul, norm_mul, norm_inv, norm_inv,
    Complex.norm_natCast, Complex.norm_natCast]
  have hmem' : (0 : ℤ) ∈ symIcc N' := by simp [symIcc]
  have hmem : (0 : ℤ) ∈ symIcc N := by simp [symIcc]
  have ha : (((symIcc N').card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem'⟩))
  have hb : (((symIcc N).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem⟩))
  field_simp
  try ring

/-- Reflection of the directions keeps the uniformity-norm power.  Combined with
`Work.Peluse.Concat.arithIcc_shrink_ge_two` this reduces the sign of `lc P` to the positive case. -/
theorem uNormPow_arithIcc_neg (s : ℕ) (c : ℤ) (L N : ℕ) (f : ℤ → ℂ) :
    uNormPow s (arithIcc c L) (symIcc N) f
      = uNormPow s (arithIcc (-c) L) (symIcc N) (fun x : ℤ => f (-x)) := by
  have hfun : (fun _ : Fin s => arithIcc c L)
      = fun _ : Fin s => (arithIcc (-c) L).image (fun z : ℤ => -z) := by
    funext i
    exact arithIcc_neg c L
  simp only [uNormPow, boxNormPow]
  rw [hfun, Pairing.boxSumPow_neg_directions]

/-- **Monotonicity of the uniformity-norm power in the direction length** (`s ≥ 2`): shrinking
`c[L]` to `c[L']` (`L' ≤ L`) can only increase the box norm, so a lower bound at a *long* direction
set implies one at every shorter set.  This is the useful direction of
`Work.Peluse.Concat.arithIcc_shrink_ge_two`, and is the reason why, in
`Work.Peluse.UControl.Theorem37Chapter`, it suffices to prove the conclusion at the *maximal*
admissible length `⌊δ^K N₀ / C⌋`: the hypothesis `C L ≤ δ^K N₀` bounds all admissible `L` by it. -/
theorem uNormPow_arithIcc_shrink {s : ℕ} (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ), 0 < c → ∀ (L' L N : ℕ), 1 ≤ L' → L' ≤ L →
      ∀ (f : ℤ → ℂ), SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      C * uNormPow s (arithIcc c L) (symIcc N) f ≤ uNormPow s (arithIcc c L') (symIcc N) f := by
  obtain ⟨C, hC, H⟩ := Concat.arithIcc_shrink_ge_two (t := s) hs
  refine ⟨C, hC, fun c hc L' L N hL' hLL f hfs hb => ?_⟩
  simpa only [uNormPow] using H c hc L' L hL' hLL f hfs hb


/-- **The direction-coefficient bridge** (step 4 of `NOTES_ucontrol_of_concat_SESSION2.md` §5).

Peluse's §§4-6 produce a lower bound for the box-norm power of `f` at the direction set
`((deg P)! · lc P)[L]`, while `Work.Peluse.PeluseUControl` demands `(lc P)[D]`.  The two sets are
dilation-related and the two comparisons

* `Work.Peluse.BoxNormDilation.dilated_directions_ge`
  (`‖f‖_{□^t_{(mc)[L]}} ≼ ‖f‖_{□^t_{c[mL]}}`, `t ≥ 2`, `m ≥ 2`) and
* `Work.Peluse.Concat.arithIcc_shrink_ge_two`
  (`‖f‖_{□^t_{c[L]}} ≼ ‖f‖_{□^t_{c[L']}}`, `2 ≤ t`, `L' ≤ L`, `c > 0`)

compose to give the bridge, for every `D ≤ m·L`; the sign of `c` is handled by
`uNormPow_arithIcc_neg`.  Both comparisons are *false* at `t = 1`, which is why `2 ≤ s` is
required (see §3 of the notes). -/
theorem uNormPow_direction_bridge {s : ℕ} (hs : 2 ≤ s) (m : ℕ) (hm : 2 ≤ m) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (c : ℤ) (hc : c ≠ 0) (L D N : ℕ) (f : ℤ → ℂ),
      1 ≤ L → 1 ≤ D → D ≤ m * L → (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      κ * uNormPow s (arithIcc (m * c) L) (symIcc N) f
        ≤ uNormPow s (arithIcc c D) (symIcc N) f := by
  obtain ⟨C₁, hC₁, hdil⟩ := BoxNormDilation.dilated_directions_ge hs m hm
  obtain ⟨C₂, hC₂, hshr⟩ := Concat.arithIcc_shrink_ge_two (t := s) hs
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  have key : ∀ (c' : ℤ), 0 < c' → ∀ (L D N : ℕ) (f : ℤ → ℂ),
      1 ≤ L → 1 ≤ D → D ≤ m * L → (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      (C₁ * C₂) * uNormPow s (arithIcc (m * c') L) (symIcc N) f
        ≤ uNormPow s (arithIcc c' D) (symIcc N) f := by
    intro c' hc' L D N f hL hD hDm hf hsupp
    have h1 := hdil c' L N f (ne_of_gt hc') hL hf hsupp
    have h2 := hshr c' hc' D (m * L) hD hDm (f := f) hsupp hf
    calc (C₁ * C₂) * uNormPow s (arithIcc (m * c') L) (symIcc N) f
        = C₂ * (C₁ * uNormPow s (arithIcc (m * c') L) (symIcc N) f) := by ring
      _ ≤ C₂ * uNormPow s (arithIcc c' (m * L)) (symIcc N) f :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hC₂)
      _ ≤ uNormPow s (arithIcc c' D) (symIcc N) f := h2
  intro c hc L D N f hL hD hDm hf hsupp
  by_cases hlt : c < 0
  · have hcpos : 0 < -c := by omega
    have hf' : ∀ x : ℤ, ‖(fun x : ℤ => f (-x)) x‖ ≤ 1 := fun x => hf (-x)
    have hsupp' : SupportIn (fun x : ℤ => f (-x)) N := by
      intro x hx
      exact hsupp (-x) (by simpa using hx)
    have h := key (-c) hcpos L D N (fun x : ℤ => f (-x)) hL hD hDm hf' hsupp'
    rw [show m * (-c) = -(m * c) by ring] at h
    rw [uNormPow_arithIcc_neg s (m * c) L N f, uNormPow_arithIcc_neg s c D N f]
    exact h
  · by_cases heq : c = 0
    · exact absurd heq hc
    · have hgt : 0 < c := by omega
      exact key c hgt L D N f hL hD hDm hf hsupp

/-- The support of the dual function in the symmetric box `[-dSup P N₀ N, dSup P N₀ N]` used by
`PeluseUControl` (a reproof of `Work.Peluse.Tools.dualFn_supportIn` with the `M ≤ N` hypothesis
dropped, in the shape needed by the assembly). -/
theorem dualFn_supportIn_dSup {N₀ N : ℕ} (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h₀ : SupportIn f₀ N₀) :
    SupportIn (dualFn N P f₀ f₁) (dSup P N₀ N) := by
  intro x hx
  rw [dSup] at hx
  simp only [dualFn]
  rw [Finset.sum_eq_zero (fun y hy => ?_), mul_zero]
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  have hkey : (N₀ : ℤ) < |x - P.eval ((y : ℕ) : ℤ)| := by
    have hS : |P.eval ((y : ℕ) : ℤ)| ≤ ((polySup P N : ℕ) : ℤ) :=
      Tools.eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy2)
    have hx' : (N₀ : ℤ) + ((polySup P N : ℕ) : ℤ) < |x| := by
      rw [← Int.natCast_natAbs x]
      exact_mod_cast hx
    have := abs_sub_abs_le_abs_sub x (P.eval ((y : ℕ) : ℤ))
    linarith
  have hnat : N₀ < (x - P.eval ((y : ℕ) : ℤ)).natAbs := by
    have hcast : (N₀ : ℤ) < (((x - P.eval ((y : ℕ) : ℤ)).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hkey
    exact_mod_cast hcast
  rw [h₀ _ hnat, zero_mul]

/-! ## Elementary arithmetic facts about `polySup`

These are the two comparisons between `polySup P N` and `N ^ P.natDegree` that the assembly needs:
`polySup` dominates its leading term, and is dominated by the sum of the absolute values of the
coefficients times the leading power (for `N ≥ 1`). -/

/-- `polySup P N` dominates its leading term `|lc P| * N ^ deg P`. -/
theorem lc_natAbs_mul_pow_le_polySup (P : Polynomial ℤ) (N : ℕ) :
    P.leadingCoeff.natAbs * N ^ P.natDegree ≤ polySup P N := by
  rw [polySup]
  have hmem : P.natDegree ∈ Finset.range (P.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  calc P.leadingCoeff.natAbs * N ^ P.natDegree
      = (P.coeff P.natDegree).natAbs * N ^ P.natDegree := by rw [Polynomial.coeff_natDegree]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs * N ^ i :=
        Finset.single_le_sum (f := fun i => (P.coeff i).natAbs * N ^ i)
          (fun i _ => Nat.zero_le _) hmem

/-- For `N ≥ 1`, `polySup P N` is at most the sum of the absolute values of the coefficients times
`N ^ deg P`. -/
theorem polySup_le_sum_coeff_mul_pow (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) :
    polySup P N
      ≤ (∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs) * N ^ P.natDegree := by
  rw [polySup, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN hi')

/-- The leading coefficient of a polynomial of degree `≥ 2` is nonzero. -/
theorem leadingCoeff_ne_zero_of_two_le_natDegree {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    P.leadingCoeff ≠ 0 := by
  intro h
  have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
  rw [hP] at hd
  simp at hd

/-- The absolute value of the leading coefficient of a polynomial of degree `≥ 2` is at least `1`. -/
theorem one_le_leadingCoeff_natAbs {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) :
    1 ≤ P.leadingCoeff.natAbs :=
  Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (leadingCoeff_ne_zero_of_two_le_natDegree hd))

end

end Work.Peluse
