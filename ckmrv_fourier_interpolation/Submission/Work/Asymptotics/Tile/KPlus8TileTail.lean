/-
# The `K_+^{(8)}` tail on the cusp-`±1` tiles

For `w ∈ E = KEpsilon`, `n = ±1` and `z = i t` with `t ≥ 2 Im (S • w) + 1`, the kernel
`K_+^{(8)}(n+w, z)` differs from its cusp-`i∞` model `𝒢_+^{(8)}(n+w, z)` by
`O((scale w)^N (1+t)^M e^{π Im(Sw) - πt})`, i.e. `TB π 1` of `tileTB`.

The proof is the algebra of `Compact.KPlus8_sub_Gplus8_decomp`,
`K_+^{(8)} - 𝒢_+^{(8)} = tailC⁻¹ (Φ₁ + Φ₂ + Φ₃)`, together with

* the tile `τ`-atom bounds of `tileTB` (`TB.E4`, `TB.E6`, `TB.phi0`, `TB.phi2`, `TB.j`,
  `TB.invDelta`, `TB.E14`),
* the `z`-atom bounds on the contour `z = i t` (`ZC`), and
* the tile divisor lower bound `1/16 ≤ ‖Δ(z)(j(n+w) - j z)‖`, obtained from
  `funnel_divisor_lower` applied at `S • w ∈ 𝔽` and the `S`-invariance of `j`.

Every term is `(τ-atom) × (z-atom)` with `a ≤ (2b-1)π`, so `TB.absorb_gen` finishes.
-/
import Mathlib
import Submission.Work.Asymptotics.Tile.tileTB
import Submission.Work.Asymptotics.Tile.KMinusTileTail
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.funnel_divisor_lower

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics

noncomputable section

/-! ## Transport of a `TB` bound along an equality valid on the tiles -/

lemma TB.congr_tile {a b : ℝ} {F G : ℍ → ℤ → ℍ → ℂ} (h : TB a b F)
    (hFG : ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ), (n = 1 ∨ n = -1) → w ∈ KEpsilon →
      (z : ℂ) = (t : ℂ) * Complex.I → 2 * (ModularGroup.S • w).im + 1 ≤ t →
      F w n z = G w n z) : TB a b G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun w n z t hn hw hz ht => by
    rw [← hFG w n z t hn hw hz ht]
    exact hb w n z t hn hw hz ht⟩

/-! ## The tile divisor lower bound -/

lemma ktl8_tile_divisor_lower (w : ℍ) (hw : w ∈ KEpsilon) (z : ℍ) (t : ℝ)
    (hz : (z : ℂ) = (t : ℝ) * Complex.I) (ht : 2 * (ModularGroup.S • w).im + 1 ≤ t)
    (n : ℤ) (hn : n = 1 ∨ n = -1) :
    (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)‖ := by
  have hτF : Funnel (ModularGroup.S • w) := ⟨S_smul_mem_DomainD hw.1, hw.2⟩
  have hht : (ModularGroup.S • w).im + 1 ≤ t := by linarith [hw.2]
  have h := funnel_divisor_lower (ModularGroup.S • w) z t hτF hht hz
  have hj : jInvariantFun (ModularGroup.S • w) = jInvariantFun ((n : ℝ) +ᵥ w) := by
    rw [KernelFacts.jInvariantFun_S_smul, ktl_jInvariantFun_vadd_int n hn w]
  rwa [hj] at h

/-- The reciprocal divisor is uniformly bounded on the tiles. -/
lemma TB.ktl8_invdivisor :
    TB 0 0 (fun w n z =>
      (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) := by
  refine ⟨16, 0, 0, by norm_num, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have h := ktl8_tile_divisor_lower w hw z t hz ht n hn
  have hpos : 0 < ‖DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z)‖ :=
    lt_of_lt_of_le (by norm_num) h
  have hinv : ‖(DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹‖ ≤ 16 := by
    rw [norm_inv]
    rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 16)]
    have h16 : ((16 : ℝ))⁻¹ = 1 / 16 := by norm_num
    rw [h16]
    exact h
  have hexp : Real.exp (0 * (ModularGroup.S • w).im - 0 * Real.pi * t) = 1 := by
    rw [show (0 : ℝ) * (ModularGroup.S • w).im - 0 * Real.pi * t = 0 from by ring,
      Real.exp_zero]
  rw [hexp]
  simpa using hinv

/-! ## The `z`-atoms on the contour -/

lemma ZC.ktl8_z : ZC 1 0 (fun z : ℍ => (z : ℂ)) := by
  refine ⟨1, one_pos, fun z t ht hz => ?_⟩
  rw [ktl_norm_coe ht hz, Real.rpow_one,
    show (0 : ℝ) * Real.pi * t = 0 from by ring, neg_zero, Real.exp_zero]
  simp only [mul_one, one_mul]
  linarith

lemma ZC.ktl8_zsq : ZC 2 0 (fun z : ℍ => (z : ℂ) ^ 2) :=
  ZC.congr ((ZC.ktl8_z.mul ZC.ktl8_z).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by ring)

lemma ZC.ktl8_E2sub1 : ZC 0 2 (fun z : ℍ => E2Fun z - 1) :=
  (ZC.of_isBigOq E2_minus_one).mono (le_refl 0) (by norm_num)

lemma ZC.ktl8_E2 : ZC 0 0 (fun z : ℍ => E2Fun z) :=
  (ZC.of_isBigOq E2Fun_bdd).mono (le_refl 0) (by norm_num)
lemma ZC.ktl8_E4 : ZC 0 0 (fun z : ℍ => E4Fun z) :=
  (ZC.of_isBigOq E4Fun_bdd).mono (le_refl 0) (by norm_num)
lemma ZC.ktl8_E6 : ZC 0 0 (fun z : ℍ => E6Fun z) :=
  (ZC.of_isBigOq E6Fun_bdd).mono (le_refl 0) (by norm_num)
lemma ZC.ktl8_E4sub1 : ZC 0 2 (fun z : ℍ => E4Fun z - 1) :=
  (ZC.of_isBigOq E4_minus_one).mono (le_refl 0) (by norm_num)
lemma ZC.ktl8_E6sub1 : ZC 0 2 (fun z : ℍ => E6Fun z - 1) :=
  (ZC.of_isBigOq E6_minus_one).mono (le_refl 0) (by norm_num)

lemma ZC.ktl8_E8 : ZC 0 0 (fun z : ℍ => E8Fun z) :=
  ZC.congr ((ZC.ktl8_E4.mul ZC.ktl8_E4).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by simp only [E8Fun, pow_two])

lemma ZC.ktl8_E10 : ZC 0 0 (fun z : ℍ => E10Fun z) :=
  ZC.congr ((ZC.ktl8_E4.mul ZC.ktl8_E6).mono (m' := 0) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by simp only [E10Fun])

lemma ZC.ktl8_Delta : ZC 0 2 (fun z : ℍ => DeltaFun z) := by
  have h : IsBigOq (fun τ : ℍ => DeltaFun τ) 1 :=
    ((Work.Asymptotics.DeltaFun_isBigOq.add Work.Asymptotics.qParamFun_isBigOq).mono
      (by norm_num)).congr (fun τ => by ring)
  exact (ZC.of_isBigOq h).mono (le_refl 0) (by norm_num)

lemma ZC.ktl8_oneAE2 : ZC 0 0 (fun z : ℍ => 1 + E2Fun z) :=
  ((ZC.const 0 le_rfl (1 : ℂ)).add ZC.ktl8_E2).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)

lemma ZC.ktl8_E4add1 : ZC 0 0 (fun z : ℍ => E4Fun z + 1) :=
  (ZC.ktl8_E4.add (ZC.const 0 le_rfl (1 : ℂ))).mono (m' := 0) (n' := 0)
    (by norm_num) (by norm_num)

/-- `G(z) = z E₂(z) - 6i/π` grows at most linearly on the contour. -/
lemma ZC.ktl8_Gt : ZC 1 0 (fun z : ℍ => TildeFacts.Gt z) := by
  obtain ⟨C, hC, hb⟩ := E2Fun_bdd
  refine ⟨C + 6 / Real.pi + 1, by positivity, fun z t ht hz => ?_⟩
  have hzt : ‖(z : ℂ)‖ = t := ktl_norm_coe ht hz
  have hzim : z.im = t := ktl_im_of_contour hz
  have h1 : ‖E2Fun z‖ ≤ C := by
    have h := hb z (by rw [hzim]; exact ht)
    simpa using h
  have hgt : ‖TildeFacts.Gt z‖ ≤ C * t + 6 / Real.pi := by
    rw [TildeFacts.Gt]
    have h2 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, show ‖(6 : ℂ)‖ = 6 by norm_num, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    refine le_trans (norm_sub_le _ _) ?_
    rw [h2, norm_mul, hzt]
    have h3 : t * ‖E2Fun z‖ ≤ t * C := mul_le_mul_of_nonneg_left h1 (by linarith)
    linarith
  rw [Real.rpow_one, show (0 : ℝ) * Real.pi * t = 0 from by ring, neg_zero, Real.exp_zero]
  simp only [mul_one]
  refine le_trans hgt ?_
  have hq : (0 : ℝ) ≤ 6 / Real.pi := by positivity
  have h1 : C * t ≤ C * (1 + t) := mul_le_mul_of_nonneg_left (by linarith) hC.le
  have h2 : 6 / Real.pi ≤ (6 / Real.pi) * (1 + t) := by
    calc 6 / Real.pi = (6 / Real.pi) * 1 := by ring
      _ ≤ (6 / Real.pi) * (1 + t) := mul_le_mul_of_nonneg_left (by linarith) hq
  calc C * t + 6 / Real.pi
      ≤ C * (1 + t) + (6 / Real.pi) * (1 + t) := by linarith
    _ = (C + 6 / Real.pi) * (1 + t) := by ring
    _ ≤ (C + 6 / Real.pi + 1) * (1 + t) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith

lemma ZC.ktl8_phit1 : ZC 2 0 (fun z : ℍ => phitVec z 1) :=
  ZC.congr ((ZC.ktl8_z.mul ZC.ktl8_Gt).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num))
    (fun z => (TildeFacts.phitVec_one z).symm)

lemma ZC.ktl8_phit2 : ZC 2 0 (fun z : ℍ => phitVec z 2) :=
  ZC.congr ((ZC.ktl8_Gt.mul ZC.ktl8_Gt).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num))
    (fun z => by rw [← pow_two]; exact (TildeFacts.phitVec_two z).symm)

lemma ZC.ktl8_E8sub : ZC 0 2 (fun z : ℍ => E8Fun z - E4Fun z ^ 3) :=
  ZC.congr (((ZC.ktl8_E4.mul ZC.ktl8_E4).mul ZC.ktl8_E4sub1).mono (m' := 0) (n' := 2)
      (by norm_num) (by norm_num)).neg
    (fun z => by simp only [E8Fun]; ring)

lemma ZC.ktl8_E10sub : ZC 0 2 (fun z : ℍ => E10Fun z - E4Fun z ^ 3) :=
  ZC.congr ((ZC.ktl8_E4.mul
      (ZC.ktl8_E6sub1.sub ((ZC.ktl8_E4sub1.mul ZC.ktl8_E4add1).mono (m' := 0) (n' := 2)
        (by norm_num) (by norm_num)))).mono (m' := 0) (n' := 2) (by norm_num) (by norm_num))
    (fun z => by simp only [E10Fun]; ring)

/-! ## `τ`-atoms in the exact shapes needed -/

lemma TB.ktl8_tau :
    TB 0 0 (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ)) :=
  TB.phiNeg2.congr (fun w n z => by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring)

lemma TB.ktl8_tauE6 :
    TB 0 0 (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
  (TB.mul TB.ktl8_tau TB.E6).mono (by norm_num) (by norm_num)

lemma TB.ktl8_twoPhi0E4 :
    TB 0 0 (fun w n _ => 2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) := by
  have h : TB 0 0 (fun w n _ => 2 * (Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TB.const_mul 2 (TB.mul TB.phi0 TB.E4)).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by ring)

lemma TB.ktl8_tauE6j :
    TB (2 * Real.pi) 0
      (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  (TB.mul TB.ktl8_tauE6 TB.j).mono (by linarith [Real.pi_pos]) (by norm_num)

lemma TB.ktl8_twoPhi0E4j :
    TB (2 * Real.pi) 0
      (fun w n _ => 2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  (TB.mul TB.ktl8_twoPhi0E4 TB.j).mono (by linarith [Real.pi_pos]) (by norm_num)

/-! ## `Φ₁` -/

lemma TB.ktl8_PhiMain :
    TB Real.pi 1 (fun w n z => Compact.PhiMain ((n : ℝ) +ᵥ w) z) := by
  have hzC : ZC 2 0 (fun z : ℍ =>
      -((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)) := by
    have h1 : ZC 2 0 (fun z : ℍ => (z : ℂ) ^ 2 * (1 + E2Fun z)) :=
      (ZC.ktl8_zsq.mul ZC.ktl8_oneAE2).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num)
    have h2 : ZC 1 0 (fun z : ℍ => 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)) :=
      (((ZC.const 0 le_rfl (12 * Complex.I / (Real.pi : ℂ))).mul ZC.ktl8_z).mono
        (m' := 1) (n' := 0) (by norm_num) (by norm_num)).congr (fun z => by ring)
    exact ((h1.neg.add h2).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num)).congr
      (fun z => by ring)
  have h1 : TB 0 0 (fun w n z =>
      (-((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
        * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
    ((TB.mul_ZC (by norm_num) hzC TB.ktl8_tauE6).mono (by norm_num) (by norm_num)).congr
      (fun w n z => by ring)
  have h2 : TB 0 0 (fun w n z => (z : ℂ) ^ 2
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    ((TB.mul_ZC (by norm_num) ZC.ktl8_zsq TB.ktl8_twoPhi0E4).mono (by norm_num)
      (by norm_num)).congr (fun w n z => by ring)
  have hbr : TB 0 0 (fun w n z =>
      (-((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
          * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
        + (z : ℂ) ^ 2 * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    TB.add h1 h2
  refine ((TB.mul_ZC (by norm_num) ZC.ktl8_E2sub1 hbr).absorb_gen (by norm_num)
    (by nlinarith [Real.pi_pos])).congr_tile (fun w n z t hn hw hz ht => ?_)
  simp only [Compact.PhiMain]
  ring

/-! ## `Φ₂` -/

lemma TB.ktl8_PhiDiv :
    TB Real.pi 1 (fun w n z => Compact.PhiDiv ((n : ℝ) +ᵥ w) z) := by
  have hZC : ZC 2 2 (fun z : ℍ => DeltaFun z * (z : ℂ) ^ 2) :=
    (ZC.ktl8_Delta.mul ZC.ktl8_zsq).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hTB : TB (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
        * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹) :=
    ((TB.mul (TB.mul TB.phi2 TB.E14) TB.invDelta).mono (by linarith [Real.pi_pos])
      (by norm_num)).congr (fun w n z => by ring)
  have hprod : TB (2 * Real.pi) 2
      (fun w n z => (DeltaFun z * (z : ℂ) ^ 2)
        * (Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
            * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹)) :=
    (TB.mul_ZC (by norm_num) hZC hTB).mono (le_refl _) (by norm_num)
  have hboth : TB (2 * Real.pi) 2
      (fun w n z => (DeltaFun z * (z : ℂ) ^ 2)
        * (Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
            * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹)
        * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) :=
    (TB.mul hprod TB.ktl8_invdivisor).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine ((hboth.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_))
  have hDτ : DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := ClassicalFacts.DeltaFun_ne_zero _
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hd := ktl8_tile_divisor_lower w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  simp only [Compact.PhiDiv, div_eq_mul_inv]
  field_simp

/-! ## `Φ₃` -/

lemma TB.ktl8_PhiCorr :
    TB Real.pi 1 (fun w n z => Compact.PhiCorr ((n : ℝ) +ᵥ w) z) := by
  have hZ8 : ZC 2 2 (fun z : ℍ => phitVec z 2 * (E8Fun z - E4Fun z ^ 3)) :=
    (ZC.ktl8_phit2.mul ZC.ktl8_E8sub).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ10 : ZC 2 2 (fun z : ℍ => phitVec z 1 * (E10Fun z - E4Fun z ^ 3)) :=
    (ZC.ktl8_phit1.mul ZC.ktl8_E10sub).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ8b : ZC 2 2 (fun z : ℍ => phitVec z 2 * DeltaFun z) :=
    (ZC.ktl8_phit2.mul ZC.ktl8_Delta).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ10b : ZC 2 2 (fun z : ℍ => phitVec z 1 * DeltaFun z) :=
    (ZC.ktl8_phit1.mul ZC.ktl8_Delta).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hN1a : TB 0 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
    ((TB.mul_ZC (by norm_num) hZ8 TB.ktl8_tauE6).mono (le_refl 0) (by norm_num)).congr
      (fun w n z => by ring)
  have hN1b : TB (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * DeltaFun z)
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    ((TB.mul_ZC (by norm_num) hZ8b TB.ktl8_tauE6j).mono (le_refl _) (by norm_num)).congr
      (fun w n z => by ring)
  have hN2a : TB 0 2 (fun w n z => (phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    ((TB.mul_ZC (by norm_num) hZ10 TB.ktl8_twoPhi0E4).mono (le_refl 0) (by norm_num)).congr
      (fun w n z => by ring)
  have hN2b : TB (2 * Real.pi) 2 (fun w n z => (phitVec z 1 * DeltaFun z)
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w))) :=
    ((TB.mul_ZC (by norm_num) hZ10b TB.ktl8_twoPhi0E4j).mono (le_refl _) (by norm_num)).congr
      (fun w n z => by ring)
  have hN1 : TB (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    TB.add (hN1a.mono (by linarith [Real.pi_pos]) (le_refl 2)) hN1b
  have hN2 : TB (2 * Real.pi) 2 (fun w n z => (phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
      + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
          * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w))) :=
    TB.add (hN2a.mono (by linarith [Real.pi_pos]) (le_refl 2)) hN2b
  have hnum : TB (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)
      - ((phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
          * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
        + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
            * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w)))) :=
    TB.sub hN1 hN2
  have hres : TB (2 * Real.pi) 2 (fun w n z => ((phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)
      - ((phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
          * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
        + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
            * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w))))
      * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) :=
    (TB.mul hnum TB.ktl8_invdivisor).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine ((hres.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_))
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hd := ktl8_tile_divisor_lower w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  simp only [Compact.PhiCorr, div_eq_mul_inv]
  field_simp

/-! ## The main theorem, `d = 8` -/

theorem KPlus8TileTail :
    TB Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 8 ((n : ℝ) +ᵥ w) z) := by
  have hsum : TB Real.pi 1 (fun w n z =>
      Compact.PhiMain ((n : ℝ) +ᵥ w) z + Compact.PhiDiv ((n : ℝ) +ᵥ w) z
        + Compact.PhiCorr ((n : ℝ) +ᵥ w) z) :=
    TB.add (TB.add TB.ktl8_PhiMain TB.ktl8_PhiDiv) TB.ktl8_PhiCorr
  refine (TB.const_mul (Compact.tailC)⁻¹ hsum).congr_tile (fun w n z t hn hw hz ht => ?_)
  have hG : Compact.Gplus 8 ((n : ℝ) +ᵥ w) z = Compact.Gplus8 ((n : ℝ) +ᵥ w) z := by
    rw [Compact.Gplus]; simp
  have hd := ktl8_tile_divisor_lower w hw z t hz ht n hn
  have hne : jInvariantFun ((n : ℝ) +ᵥ w) ≠ jInvariantFun z := by
    intro h0
    rw [h0, sub_self, mul_zero, norm_zero] at hd
    norm_num at hd
  rw [hG]
  exact (Compact.KPlus8_sub_Gplus8_decomp ((n : ℝ) +ᵥ w) z hne).symm

end

end Work.Asymptotics.Tile
