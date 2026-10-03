/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Peluse.U2Inv.u2inv_boxSum_eq_triple
import Submission.Work.Peluse.U2Inv.u2inv_gW_eq_triple
import Submission.Work.Peluse.U2Inv.u2inv_gW_eq_fourier
import Submission.Work.Peluse.U2Inv.u2inv_sum_dft_nu
import Submission.Work.Peluse.U2Inv.u2inv_TT_eq
import Submission.Work.Peluse.U2Inv.u2inv_TT_bound

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Peluse's `U²`-inverse theorem (Lemma 2.4 of the paper)

This module proves `Work.Peluse.PeluseU2Inverse`:

if `f : ℤ → ℂ` is `1`-bounded and supported in `[-L,L]`, and its `U²` box norm at scale
`[δ'L]` is at least `δ`, then `f` correlates with a character:
`|∑_x f x · exp (2π i β x)| ≥ (δδ')²` for some `β ∈ ℝ`.

The proof is the classical one (Peluse, Lemma 2.4; Tao's notes on the `U²` inverse theorem):

* the interval box sum is a `μ_m`-weighted average of the difference operators `Δ_{a,b} f`
  (`U2Inv/Defs.T3`), and a support hypothesis makes its `x`-sum an interval sum;
* that sum is transported to the cyclic group `ZMod (4L+1)`, where the discrete Fourier transform
  turns it into a sum of the "twisted `U²` quantities" `TT`;
* Fourier inversion in the two shift variables bounds `gW` by the maximum of `TT` times
  `‖dft ν‖_{ℓ¹}² = (N/m)²`;
* the classical `U²` argument (Cauchy–Schwarz in the frequency variable) then bounds `TT` by
  `η²‖F‖₂²/N³`, where `η` is the largest Fourier coefficient of the transported function;
* combining, `η ≥ m δ²`, and `m ≥ 1` because `m = 0` would make the box sum vanish.

The six computational pieces are proved in the separate modules
`U2Inv/u2inv_boxSum_eq_triple`, `U2Inv/u2inv_gW_eq_triple`, `U2Inv/u2inv_gW_eq_fourier`,
`U2Inv/u2inv_sum_dft_nu`, `U2Inv/u2inv_TT_eq`, `U2Inv/u2inv_TT_bound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-! ## Elementary properties of the transported function `pF` -/

/-- The coercion `ℤ → ZMod (Gmod L)` is injective on `symIcc L`. -/
lemma u2inv_abs_sub_lt_gmod {L : ℕ} {a b : ℤ} (ha : a ∈ symIcc L) (hb : b ∈ symIcc L) :
    |a - b| < (Gmod L : ℤ) := by
  obtain ⟨ha1, ha2⟩ := mem_symIcc_iff.mp ha
  obtain ⟨hb1, hb2⟩ := mem_symIcc_iff.mp hb
  have h4 : |a - b| ≤ 2 * (L : ℤ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have h5 : (2 * (L : ℤ)) < (Gmod L : ℤ) := by simp [Gmod]; omega
  linarith

lemma u2inv_intCast_injOn_symIcc {L : ℕ} {a b : ℤ} (ha : a ∈ symIcc L) (hb : b ∈ symIcc L)
    (h : (a : ZMod (Gmod L)) = (b : ZMod (Gmod L))) : a = b := by
  have hmod : a ≡ b [ZMOD (Gmod L)] := (ZMod.intCast_eq_intCast_iff a b (Gmod L)).mp h
  obtain ⟨k, hk⟩ := hmod.dvd
  have hN : (0:ℤ) < (Gmod L : ℤ) := by simp [Gmod]
  have habs : |b - a| < (Gmod L : ℤ) := by
    rw [abs_sub_comm]; exact u2inv_abs_sub_lt_gmod ha hb
  rw [hk, abs_mul, abs_of_pos hN] at habs
  have hk1 : |k| < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [abs_nonneg k]
  have hk0 : k = 0 := by
    rw [abs_lt] at hk1
    omega
  have h2 := hk
  rw [hk0, mul_zero] at h2
  omega

/-- `pF` restricted to the image of `symIcc L` is `f`. -/
lemma u2inv_pF_apply {L : ℕ} {f : ℤ → ℂ} {a : ℤ} (ha : a ∈ symIcc L) :
    pF L f (a : ZMod (Gmod L)) = f a := by
  unfold pF
  rw [show (∑ b ∈ symIcc L, (if (b : ZMod (Gmod L)) = (a : ZMod (Gmod L)) then f b else 0))
        = ∑ b ∈ symIcc L, (if b = a then f b else 0) from
      Finset.sum_congr rfl (fun b hb => by
        have hiff : ((b : ZMod (Gmod L)) = (a : ZMod (Gmod L))) ↔ b = a :=
          ⟨fun h => u2inv_intCast_injOn_symIcc hb ha h, fun h => by rw [h]⟩
        rw [if_congr hiff rfl rfl])]
  rw [Finset.sum_ite_eq' (symIcc L) a f, if_pos ha]

/-- A sum over `ℤ` of a function vanishing off `symIcc L` is the corresponding finite sum. -/
lemma u2inv_tsum_eq_sum_symIcc (L : ℕ) (φ : ℤ → ℂ) (hφ : ∀ x : ℤ, L < x.natAbs → φ x = 0) :
    (∑' x : ℤ, φ x) = ∑ x ∈ symIcc L, φ x := by
  rw [tsum_eq_sum (s := symIcc L)]
  intro x hx
  apply hφ
  by_contra hcon
  exact hx (mem_symIcc_iff.mpr (by
    constructor <;> (push_neg at hcon; omega)))

/-- The discrete Fourier transform of `pF L f` is the character sum over the interval. -/
lemma u2inv_dft_pF_eq (L : ℕ) (f : ℤ → ℂ) (k : ZMod (Gmod L)) :
    ZMod.dft (pF L f) k
      = ∑ a ∈ symIcc L, f a * ZMod.stdAddChar (-((a : ZMod (Gmod L)) * k)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [show (∑ j : ZMod (Gmod L), ZMod.stdAddChar (-(j * k)) * pF L f j)
      = ∑ j : ZMod (Gmod L), ∑ a ∈ symIcc L,
          ZMod.stdAddChar (-(j * k)) * (if (a : ZMod (Gmod L)) = j then f a else 0) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pF, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [show (∑ j : ZMod (Gmod L),
        ZMod.stdAddChar (-(j * k)) * (if (a : ZMod (Gmod L)) = j then f a else 0))
      = ∑ j : ZMod (Gmod L),
          (if (a : ZMod (Gmod L)) = j then f a * ZMod.stdAddChar (-(j * k)) else 0) from by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases h : (a : ZMod (Gmod L)) = j
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; simp]
  rw [Finset.sum_ite_eq]
  simp

/-- The `ℓ²`-mass of the transported function, with the exact normalisation used below. -/
lemma u2inv_sum_normSq_pF_le (L : ℕ) (f : ℤ → ℂ) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ∑ z : ZMod (Gmod L), ‖pF L f z‖ ^ 2 ≤ ((symIcc L).card : ℝ) := by
  have hzero : ∀ z : ZMod (Gmod L),
      z ∉ (symIcc L).image (fun a : ℤ => (a : ZMod (Gmod L))) → pF L f z = 0 := by
    intro z hz
    unfold pF
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [if_neg]
    intro hcontra
    exact hz (Finset.mem_image.mpr ⟨a, ha, hcontra⟩)
  have h1 : ∑ z : ZMod (Gmod L), ‖pF L f z‖ ^ 2
      = ∑ z ∈ (symIcc L).image (fun a : ℤ => (a : ZMod (Gmod L))), ‖pF L f z‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rw [hzero x hx, norm_zero]
    norm_num
  rw [h1, Finset.sum_image]
  · have h2 : ∀ a ∈ symIcc L, ‖pF L f (a : ZMod (Gmod L))‖ ^ 2 ≤ 1 := by
      intro a ha
      rw [u2inv_pF_apply ha]
      nlinarith [norm_nonneg (f a), hf a]
    calc ∑ a ∈ symIcc L, ‖pF L f (a : ZMod (Gmod L))‖ ^ 2
        ≤ ∑ a ∈ symIcc L, (1:ℝ) := Finset.sum_le_sum h2
      _ = ((symIcc L).card : ℝ) := by simp
  · intro a ha b hb h
    exact u2inv_intCast_injOn_symIcc ha hb h

/-- **The assembly step.**  The six computational pieces (all proved in the sibling modules of
`U2Inv/`) imply Peluse's `U²`-inverse theorem. -/
theorem u2inv_u2inverse_of_pieces
    (hbox : ∀ (L m : ℕ) (f : ℤ → ℂ), SupportIn f L →
      boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f
        = ((symIcc L).card : ℂ)⁻¹ * T3 L m f)
    (hgW : ∀ (L m : ℕ) (f : ℤ → ℂ), SupportIn f L → m ≤ L →
      gW L m f = (((Gmod L : ℂ)) ^ 3)⁻¹ * T3 L m f)
    (hfour : ∀ (L m : ℕ) (f : ℤ → ℂ), gW L m f = (((Gmod L : ℂ)) ^ 2)⁻¹ *
      ∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
        ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f))
    (hsum : ∀ (L m : ℕ), 1 ≤ m → m ≤ Gmod L →
      ∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖ = (Gmod L : ℝ) / (m : ℝ))
    (hTT : ∀ (L : ℕ) (k₁ k₂ : ZMod (Gmod L)) (F : ZMod (Gmod L) → ℂ),
      TT L k₁ k₂ F = (((Gmod L : ℂ)) ^ 4)⁻¹ *
        ∑ ξ : ZMod (Gmod L), ZMod.dft F (ξ + k₁ + k₂) * star (ZMod.dft F (ξ + k₁)) *
          star (ZMod.dft F (ξ + k₂)) * ZMod.dft F ξ)
    (hbound : ∀ (L : ℕ) (k₁ k₂ : ZMod (Gmod L)) (F : ZMod (Gmod L) → ℂ) (η : ℝ),
      (∀ ξ : ZMod (Gmod L), ‖ZMod.dft F ξ‖ ≤ η) → 0 ≤ η →
      ‖TT L k₁ k₂ F‖ ≤ η ^ 2 * (∑ x : ZMod (Gmod L), ‖F x‖ ^ 2) /
        ((Gmod L : ℝ) ^ 3)) :
    SharpU2Inverse := by
  refine ⟨1/2, by norm_num, 2, by norm_num, ?_⟩
  intro L δ δ' f hL hδ0 hδ1 hδ'0 hδ'1 hf hbdd hnorm
  let m : ℕ := (⌊δ' * (L : ℝ)⌋).toNat
  have hnorm' : δ ≤ uNorm 2 (arithIcc 1 m) (symIcc L) f := hnorm
  -- ### Step 1: the box-sum bound `δ⁴ ≤ ‖boxSumPow …‖`
  have hB4 : δ ^ 4 ≤ ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖ := by
    have hu0 : (0:ℝ) ≤ uNormPow 2 (arithIcc 1 m) (symIcc L) f := norm_nonneg _
    have h1 : δ ≤ (uNormPow 2 (arithIcc 1 m) (symIcc L) f) ^ (1 / ((2:ℝ)^2)) := hnorm'
    have h2 : δ ^ 4 ≤ ((uNormPow 2 (arithIcc 1 m) (symIcc L) f) ^ (1 / ((2:ℝ)^2))) ^ 4 :=
      pow_le_pow_left₀ (le_of_lt hδ0) h1 4
    have h3 : ((uNormPow 2 (arithIcc 1 m) (symIcc L) f) ^ (1 / ((2:ℝ)^2))) ^ 4
        = uNormPow 2 (arithIcc 1 m) (symIcc L) f := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0,
        show (1 / ((2:ℝ) ^ 2)) * ((4:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
    rw [h3] at h2
    exact h2
  -- ### Step 2: `m ≥ 1`
  have hm1 : 1 ≤ m := by
    by_contra hc
    push_neg at hc
    have hm0 : m = 0 := by omega
    have hB0' : boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 0) (symIcc L) f = 0 := by
      have hI : arithIcc 1 0 = (∅ : Finset ℤ) := by simp [arithIcc]
      rw [hI, boxSumPow, prodCubeSum]
      simp
    have hu0 : uNorm 2 (arithIcc 1 0) (symIcc L) f = 0 := by
      rw [uNorm, uNormPow, boxNormPow, hB0', norm_zero]
      exact Real.zero_rpow (by norm_num : (1 / ((2:ℝ)^2)) ≠ 0)
    have h2 : δ ≤ uNorm 2 (arithIcc 1 0) (symIcc L) f := by
      rw [hm0] at hnorm'
      exact hnorm'
    rw [hu0] at h2
    linarith
  -- ### Step 3: `m ≤ L`
  have hmL : m ≤ L := by
    have h1 : (m : ℤ) ≤ (L : ℤ) := by
      have h2 : (m : ℤ) = ⌊δ' * (L : ℝ)⌋ := by
        dsimp only [m]
        exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
      rw [h2]
      calc ⌊δ' * (L : ℝ)⌋ ≤ ⌊((L : ℝ))⌋ := Int.floor_mono (by nlinarith)
        _ = (L : ℤ) := Int.floor_natCast L
    exact_mod_cast h1
  have hmN : m ≤ Gmod L := by simp only [Gmod]; omega
  -- ### Notation
  have hmpos : (0:ℝ) < (m:ℝ) := by
    have h : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    linarith
  have hNpos : (0:ℝ) < (Gmod L : ℝ) := by
    have h : (0:ℕ) < Gmod L := by simp [Gmod]
    exact_mod_cast h
  have hcpos : (0:ℝ) < ((symIcc L).card : ℝ) := by rw [card_symIcc]; positivity
  -- ### Step 4: `T3` and `gW` in terms of the box sum
  have hT3 : T3 L m f
      = ((symIcc L).card : ℂ) * boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f := by
    have h := hbox L m f hf
    have hc : ((symIcc L).card : ℂ) ≠ 0 := by
      rw [card_symIcc]
      exact_mod_cast (by omega : 2 * L + 1 ≠ 0)
    rw [h, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hF2 : ‖gW L m f‖ * ((Gmod L : ℝ)^3)
      = ((symIcc L).card : ℝ) * ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖ := by
    have hN3 : ((Gmod L : ℝ)^3) ≠ 0 := by positivity
    have h1 : ‖gW L m f‖ = ((Gmod L : ℝ)^3)⁻¹ * ‖T3 L m f‖ := by
      rw [hgW L m f hf hmL, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    have h2 : ‖T3 L m f‖
        = ((symIcc L).card : ℝ) * ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖ := by
      rw [hT3, norm_mul, Complex.norm_natCast]
    rw [h1, h2]
    have h3 : ((Gmod L : ℝ)^3)⁻¹ * (((symIcc L).card : ℝ) *
          ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖) * ((Gmod L : ℝ)^3)
        = (((Gmod L : ℝ)^3)⁻¹ * ((Gmod L : ℝ)^3)) *
          (((symIcc L).card : ℝ) *
            ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖) := by ring
    rw [h3, inv_mul_cancel₀ hN3, one_mul]
  -- ### Step 5: the maximisers
  obtain ⟨k0, hk0⟩ : ∃ k0 : ZMod (Gmod L),
      ∀ ξ : ZMod (Gmod L), ‖ZMod.dft (pF L f) ξ‖ ≤ ‖ZMod.dft (pF L f) k0‖ := by
    obtain ⟨k0, _, hk0⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod (Gmod L)))
      (fun ξ => ‖ZMod.dft (pF L f) ξ‖) ⟨0, Finset.mem_univ 0⟩
    exact ⟨k0, fun ξ => hk0 ξ (Finset.mem_univ ξ)⟩
  obtain ⟨p, hp⟩ : ∃ p : ZMod (Gmod L) × ZMod (Gmod L),
      ∀ q : ZMod (Gmod L) × ZMod (Gmod L),
        ‖TT L q.1 q.2 (pF L f)‖ ≤ ‖TT L p.1 p.2 (pF L f)‖ := by
    obtain ⟨p, _, hp⟩ := Finset.exists_max_image
      (Finset.univ : Finset (ZMod (Gmod L) × ZMod (Gmod L)))
      (fun q => ‖TT L q.1 q.2 (pF L f)‖) ⟨(0, 0), Finset.mem_univ _⟩
    exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
  set η : ℝ := ‖ZMod.dft (pF L f) k0‖ with hη
  set Tmax : ℝ := ‖TT L p.1 p.2 (pF L f)‖ with hTmax
  -- ### Step 6: `Tmax * N³ ≤ η² * card`
  have hF4 : Tmax * ((Gmod L : ℝ)^3) ≤ η ^ 2 * ((symIcc L).card : ℝ) := by
    have hη0 : 0 ≤ η := by rw [hη]; positivity
    have hb := hbound L p.1 p.2 (pF L f) η (fun ξ => by rw [hη]; exact hk0 ξ) hη0
    have hmass := u2inv_sum_normSq_pF_le L f hbdd
    have hN3 : (0:ℝ) < ((Gmod L : ℝ)^3) := by positivity
    rw [le_div_iff₀ hN3] at hb
    rw [hTmax]
    calc ‖TT L p.1 p.2 (pF L f)‖ * ((Gmod L : ℝ)^3)
        ≤ η ^ 2 * (∑ x : ZMod (Gmod L), ‖pF L f x‖ ^ 2) := hb
      _ ≤ η ^ 2 * ((symIcc L).card : ℝ) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
  -- ### Step 7: `‖gW‖ * m² ≤ Tmax`
  have hF3 : ‖gW L m f‖ * (m:ℝ) ^ 2 ≤ Tmax := by
    have hsumdft := hsum L m hm1 hmN
    have hfour' := hfour L m f
    have hinner : ‖∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
          ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)‖
        ≤ (∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖) ^ 2 * Tmax := by
      calc ‖∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
              ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)‖
          ≤ ∑ k₁ : ZMod (Gmod L), ‖∑ k₂ : ZMod (Gmod L),
              ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
              ‖ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)‖ :=
            Finset.sum_le_sum (fun k₁ _ => norm_sum_le _ _)
        _ = ∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
              ‖ZMod.dft (nu L m) k₁‖ * ‖ZMod.dft (nu L m) k₂‖ * ‖TT L k₁ k₂ (pF L f)‖ := by
            simp [norm_mul]
        _ ≤ ∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
              ‖ZMod.dft (nu L m) k₁‖ * ‖ZMod.dft (nu L m) k₂‖ * Tmax := by
            refine Finset.sum_le_sum (fun k₁ _ => Finset.sum_le_sum (fun k₂ _ => ?_))
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hTmax]
            exact hp (k₁, k₂)
        _ = ((∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖) *
              (∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖)) * Tmax := by
            have hsq : ((∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖) *
                (∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖))
                = ∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
                    ‖ZMod.dft (nu L m) k₁‖ * ‖ZMod.dft (nu L m) k₂‖ := by
              rw [Finset.sum_mul_sum]
            rw [hsq, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun k₁ _ => ?_)
            rw [Finset.sum_mul]
        _ = (∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖) ^ 2 * Tmax := by rw [sq]
    have h1 : ‖gW L m f‖ ≤ Tmax / (m:ℝ) ^ 2 := by
      have hm0 : (m:ℝ) ≠ 0 := ne_of_gt hmpos
      have hN0 : (Gmod L : ℝ) ≠ 0 := ne_of_gt hNpos
      calc ‖gW L m f‖
          = ((Gmod L : ℝ) ^ 2)⁻¹ * ‖∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
              ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)‖ := by
            rw [hfour', norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        _ ≤ ((Gmod L : ℝ) ^ 2)⁻¹ *
              ((∑ k : ZMod (Gmod L), ‖ZMod.dft (nu L m) k‖) ^ 2 * Tmax) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = Tmax / (m:ℝ) ^ 2 := by
            rw [hsumdft]
            field_simp
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ) ^ 2)] at h1
    exact h1
  -- ### Step 8: the numerical conclusion `η ≥ m δ²`
  have hmain : δ ^ 4 * (m:ℝ) ^ 2 ≤ η ^ 2 := by
    have h1 : ((symIcc L).card : ℝ) * δ ^ 4 * (m:ℝ) ^ 2
        ≤ Tmax * ((Gmod L : ℝ) ^ 3) := by
      calc ((symIcc L).card : ℝ) * δ ^ 4 * (m:ℝ) ^ 2
          ≤ ((symIcc L).card : ℝ) *
              ‖boxSumPow 2 (fun _ : Fin 2 => arithIcc 1 m) (symIcc L) f‖ * (m:ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB4 hcpos.le) (sq_nonneg (m:ℝ))
        _ = ‖gW L m f‖ * ((Gmod L : ℝ) ^ 3) * (m:ℝ) ^ 2 := by rw [hF2]
        _ = ‖gW L m f‖ * (m:ℝ) ^ 2 * ((Gmod L : ℝ) ^ 3) := by ring
        _ ≤ Tmax * ((Gmod L : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right hF3 (by positivity)
    have h2 : ((symIcc L).card : ℝ) * δ ^ 4 * (m:ℝ) ^ 2 ≤ η ^ 2 * ((symIcc L).card : ℝ) :=
      le_trans h1 hF4
    refine le_of_mul_le_mul_right ?_ hcpos
    calc (δ ^ 4 * (m:ℝ) ^ 2) * ((symIcc L).card : ℝ)
        = ((symIcc L).card : ℝ) * δ ^ 4 * (m:ℝ) ^ 2 := by ring
      _ ≤ η ^ 2 * ((symIcc L).card : ℝ) := h2
  have h5 : (m:ℝ) * δ ^ 2 ≤ η := by
    have h4 : ((m:ℝ) * δ ^ 2) ^ 2 ≤ η ^ 2 := by
      have h4' : ((m:ℝ) * δ ^ 2) ^ 2 = δ ^ 4 * (m:ℝ) ^ 2 := by ring
      rw [h4']
      exact hmain
    have h6 : (0:ℝ) ≤ (m:ℝ) * δ ^ 2 := by positivity
    have h7 : Real.sqrt (((m:ℝ) * δ ^ 2) ^ 2) ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq h6, Real.sqrt_sq (by positivity : (0:ℝ) ≤ η)] at h7
  have h6 : δ ^ 2 ≤ (m:ℝ) * δ ^ 2 := by
    have hmm : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    nlinarith [sq_nonneg δ]
  -- ### Step 9: the character sum
  let β : ℝ := -(k0.val : ℝ) / (Gmod L : ℝ)
  have hβval : β = -(k0.val : ℝ) / (Gmod L : ℝ) := rfl
  have hchar : ∀ a : ℤ,
      Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (a : ℂ))
        = ZMod.stdAddChar (-((a : ZMod (Gmod L)) * k0)) := by
    intro a
    have harg : 2 * Real.pi * Complex.I * (β : ℂ) * (a : ℂ)
        = 2 * Real.pi * Complex.I * ((↑(-(a * (k0.val : ℤ))) : ℂ)) / (Gmod L : ℂ) := by
      rw [hβval]
      push_cast
      field_simp
    rw [harg, ← ZMod.stdAddChar_coe (-(a * (k0.val : ℤ)))]
    congr 1
    rw [Int.cast_neg, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val k0]
  have hsum_eq : (∑' x : ℤ, f x * Complex.exp (2 * Real.pi * Complex.I * (β : ℂ) * (x : ℂ)))
      = ZMod.dft (pF L f) k0 := by
    rw [u2inv_tsum_eq_sum_symIcc L _
      (fun x hx => by rw [hf x hx, zero_mul])]
    rw [u2inv_dft_pF_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hchar a]
  -- ### Step 10: the factor `L` against `m`
  have hfloor_ge : (1:ℤ) ≤ ⌊δ' * (L : ℝ)⌋ := by
    have h : ((m : ℤ)) = ⌊δ' * (L : ℝ)⌋ := by
      dsimp only [m]
      exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
    rw [← h]
    exact_mod_cast hm1
  have hm_ge : δ' * (L : ℝ) ≤ 2 * (m : ℝ) := by
    by_cases h : δ' * (L : ℝ) ≤ 2
    · have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      linarith
    · have hlt : δ' * (L : ℝ) < (⌊δ' * (L : ℝ)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hm_eq : (m:ℝ) = (⌊δ' * (L : ℝ)⌋ : ℝ) := by
        have h2 : ((m : ℤ)) = ⌊δ' * (L : ℝ)⌋ := by
          dsimp only [m]
          exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
        exact_mod_cast h2
      rw [hm_eq]
      linarith
  have harith : (1/2:ℝ) * (δ * δ') ^ 2 * (L : ℝ) ≤ (m:ℝ) * δ ^ 2 := by
    have h1 : (δ') ^ 2 * (L:ℝ) ≤ 2 * (m:ℝ) := by
      have h2 : (δ') ^ 2 * (L:ℝ) = δ' * (δ' * (L:ℝ)) := by ring
      rw [h2]
      calc δ' * (δ' * (L:ℝ)) ≤ 1 * (2 * (m:ℝ)) :=
            mul_le_mul hδ'1 hm_ge (by positivity) (by norm_num)
        _ = 2 * (m:ℝ) := by ring
    have h3 : (1/2:ℝ) * (δ * δ') ^ 2 * (L : ℝ) = δ^2 * ((δ') ^ 2 * (L:ℝ)) / 2 := by ring
    rw [h3]
    have h4 : ((δ') ^ 2 * (L:ℝ)) / 2 ≤ (m:ℝ) := by linarith
    calc δ^2 * ((δ') ^ 2 * (L:ℝ)) / 2 = δ^2 * (((δ') ^ 2 * (L:ℝ)) / 2) := by ring
      _ ≤ δ^2 * (m:ℝ) := mul_le_mul_of_nonneg_left h4 (sq_nonneg δ)
      _ = (m:ℝ) * δ ^ 2 := by ring
  refine ⟨β, ?_⟩
  rw [hsum_eq]
  calc (1/2:ℝ) * (δ * δ') ^ 2 * (L : ℝ) ≤ (m:ℝ) * δ ^ 2 := harith
    _ ≤ η := h5
    _ = ‖ZMod.dft (pF L f) k0‖ := hη

end

end Work.Peluse.U2Inv

namespace Work.Peluse

/-- **Peluse's `U²`-inverse theorem in the form used by Area A2** (`Work.Peluse.PeluseU2Inverse`),
assembled from the six computational pieces of `U2Inv/`.  In fact the constant `C'` can be taken
to be `1` and `K = 2` (see `Work.Peluse.U2Inv.u2inv_u2inverse_of_pieces`). -/
theorem u2inverse : Work.Peluse.PeluseU2Inverse := by
  obtain ⟨C', hC', K, hK, hbody⟩ := Work.Peluse.U2Inv.u2inv_u2inverse_of_pieces
    Work.Peluse.U2Inv.u2inv_boxSum_eq_triple
    Work.Peluse.U2Inv.u2inv_gW_eq_triple
    Work.Peluse.U2Inv.u2inv_gW_eq_fourier
    Work.Peluse.U2Inv.u2inv_sum_dft_nu
    Work.Peluse.U2Inv.u2inv_TT_eq
    Work.Peluse.U2Inv.u2inv_TT_bound
  exact ⟨C', hC', K, hK, hbody⟩

end Work.Peluse
