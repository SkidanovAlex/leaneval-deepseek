import Mathlib
import Submission.Work.Asymptotics.Tile.SharpTB
import Submission.Work.Asymptotics.Tile.KPlus8TileTail
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.funnel_divisor_lower

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold
open Work.Kernels Work.Asymptotics
open Work.Asymptotics.EtailE

noncomputable section

/-- The reciprocal divisor is uniformly bounded on the tiles. -/
lemma TBS.ktl8_invdivisor :
    TBS 0 0 (fun w n z =>
      (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) := by
  refine ⟨16, 0, 0, by norm_num, le_refl 0, le_refl 0, fun w n z t hn hw hz ht => ?_⟩
  have h := tileDivisorLowerSharp w hw z t hz ht n hn
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

lemma TBS.ktl8_tau :
    TBS 0 0 (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ)) :=
  TBS.phiNeg2.congr (fun w n z => by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring)

lemma TBS.ktl8_tauE6 :
    TBS 0 0 (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
  (TBS.mul TBS.ktl8_tau TBS.E6).mono (by norm_num) (by norm_num)

lemma TBS.ktl8_twoPhi0E4 :
    TBS 0 0 (fun w n _ => 2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)) := by
  have h : TBS 0 0 (fun w n _ => 2 * (Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
      * E4Fun ((n : ℝ) +ᵥ w))) :=
    (TBS.const_mul 2 (TBS.mul TBS.phi0 TBS.E4)).mono (by norm_num) (by norm_num)
  exact h.congr (fun w n z => by ring)

lemma TBS.ktl8_tauE6j :
    TBS (2 * Real.pi) 0
      (fun w n _ => ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  (TBS.mul TBS.ktl8_tauE6 TBS.j).mono (by linarith [Real.pi_pos]) (by norm_num)

lemma TBS.ktl8_twoPhi0E4j :
    TBS (2 * Real.pi) 0
      (fun w n _ => 2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w)) :=
  (TBS.mul TBS.ktl8_twoPhi0E4 TBS.j).mono (by linarith [Real.pi_pos]) (by norm_num)

/-! ## `Φ₁` -/

lemma TBS.ktl8_PhiMain :
    TBS Real.pi 1 (fun w n z => Compact.PhiMain ((n : ℝ) +ᵥ w) z) := by
  have hzC : ZC 2 0 (fun z : ℍ =>
      -((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)) := by
    have h1 : ZC 2 0 (fun z : ℍ => (z : ℂ) ^ 2 * (1 + E2Fun z)) :=
      (ZC.ktl8_zsq.mul ZC.ktl8_oneAE2).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num)
    have h2 : ZC 1 0 (fun z : ℍ => 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)) :=
      (((ZC.const 0 le_rfl (12 * Complex.I / (Real.pi : ℂ))).mul ZC.ktl8_z).mono
        (m' := 1) (n' := 0) (by norm_num) (by norm_num)).congr (fun z => by ring)
    exact ((h1.neg.add h2).mono (m' := 2) (n' := 0) (by norm_num) (by norm_num)).congr
      (fun z => by ring)
  have h1 : TBS 0 0 (fun w n z =>
      (-((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
        * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
    ((TBS.mul_ZC (by norm_num) hzC TBS.ktl8_tauE6).mono (by norm_num) (by norm_num)).congr
      (fun w n z => by ring)
  have h2 : TBS 0 0 (fun w n z => (z : ℂ) ^ 2
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    ((TBS.mul_ZC (by norm_num) ZC.ktl8_zsq TBS.ktl8_twoPhi0E4).mono (by norm_num)
      (by norm_num)).congr (fun w n z => by ring)
  have hbr : TBS 0 0 (fun w n z =>
      (-((z : ℂ) ^ 2 * (1 + E2Fun z)) + 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ))
          * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
        + (z : ℂ) ^ 2 * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    TBS.add h1 h2
  refine ((TBS.mul_ZC (by norm_num) ZC.ktl8_E2sub1 hbr).absorb_gen (by norm_num)
    (by nlinarith [Real.pi_pos])).congr_tile (fun w n z t hn hw hz ht => ?_)
  simp only [Compact.PhiMain]
  ring

/-! ## `Φ₂` -/

lemma TBS.ktl8_PhiDiv :
    TBS Real.pi 1 (fun w n z => Compact.PhiDiv ((n : ℝ) +ᵥ w) z) := by
  have hZC : ZC 2 2 (fun z : ℍ => DeltaFun z * (z : ℂ) ^ 2) :=
    (ZC.ktl8_Delta.mul ZC.ktl8_zsq).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hTB : TBS (2 * Real.pi) 0
      (fun w n _ => Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
        * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹) :=
    ((TBS.mul (TBS.mul TBS.phi2 TBS.E14) TBS.invDelta).mono (by linarith [Real.pi_pos])
      (by norm_num)).congr (fun w n z => by ring)
  have hprod : TBS (2 * Real.pi) 2
      (fun w n z => (DeltaFun z * (z : ℂ) ^ 2)
        * (Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
            * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹)) :=
    (TBS.mul_ZC (by norm_num) hZC hTB).mono (le_refl _) (by norm_num)
  have hboth : TBS (2 * Real.pi) 2
      (fun w n z => (DeltaFun z * (z : ℂ) ^ 2)
        * (Work.Kernels.phi2 ((n : ℝ) +ᵥ w) * E14Fun ((n : ℝ) +ᵥ w)
            * (DeltaFun ((n : ℝ) +ᵥ w))⁻¹)
        * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) :=
    (TBS.mul hprod TBS.ktl8_invdivisor).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine ((hboth.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_))
  have hDτ : DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := ClassicalFacts.DeltaFun_ne_zero _
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hd := tileDivisorLowerSharp w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  simp only [Compact.PhiDiv, div_eq_mul_inv]
  field_simp

/-! ## `Φ₃` -/

lemma TBS.ktl8_PhiCorr :
    TBS Real.pi 1 (fun w n z => Compact.PhiCorr ((n : ℝ) +ᵥ w) z) := by
  have hZ8 : ZC 2 2 (fun z : ℍ => phitVec z 2 * (E8Fun z - E4Fun z ^ 3)) :=
    (ZC.ktl8_phit2.mul ZC.ktl8_E8sub).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ10 : ZC 2 2 (fun z : ℍ => phitVec z 1 * (E10Fun z - E4Fun z ^ 3)) :=
    (ZC.ktl8_phit1.mul ZC.ktl8_E10sub).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ8b : ZC 2 2 (fun z : ℍ => phitVec z 2 * DeltaFun z) :=
    (ZC.ktl8_phit2.mul ZC.ktl8_Delta).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hZ10b : ZC 2 2 (fun z : ℍ => phitVec z 1 * DeltaFun z) :=
    (ZC.ktl8_phit1.mul ZC.ktl8_Delta).mono (m' := 2) (n' := 2) (by norm_num) (by norm_num)
  have hN1a : TBS 0 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)) :=
    ((TBS.mul_ZC (by norm_num) hZ8 TBS.ktl8_tauE6).mono (le_refl 0) (by norm_num)).congr
      (fun w n z => by ring)
  have hN1b : TBS (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * DeltaFun z)
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    ((TBS.mul_ZC (by norm_num) hZ8b TBS.ktl8_tauE6j).mono (le_refl _) (by norm_num)).congr
      (fun w n z => by ring)
  have hN2a : TBS 0 2 (fun w n z => (phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))) :=
    ((TBS.mul_ZC (by norm_num) hZ10 TBS.ktl8_twoPhi0E4).mono (le_refl 0) (by norm_num)).congr
      (fun w n z => by ring)
  have hN2b : TBS (2 * Real.pi) 2 (fun w n z => (phitVec z 1 * DeltaFun z)
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
        * jInvariantFun ((n : ℝ) +ᵥ w))) :=
    ((TBS.mul_ZC (by norm_num) hZ10b TBS.ktl8_twoPhi0E4j).mono (le_refl _) (by norm_num)).congr
      (fun w n z => by ring)
  have hN1 : TBS (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)) :=
    TBS.add (hN1a.mono (by linarith [Real.pi_pos]) (le_refl 2)) hN1b
  have hN2 : TBS (2 * Real.pi) 2 (fun w n z => (phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
      * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
      + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
          * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w))) :=
    TBS.add (hN2a.mono (by linarith [Real.pi_pos]) (le_refl 2)) hN2b
  have hnum : TBS (2 * Real.pi) 2 (fun w n z => (phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)
      - ((phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
          * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
        + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
            * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w)))) :=
    TBS.sub hN1 hN2
  have hres : TBS (2 * Real.pi) 2 (fun w n z => ((phitVec z 2 * (E8Fun z - E4Fun z ^ 3))
      * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
      + (phitVec z 2 * DeltaFun z) * ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) * E6Fun ((n : ℝ) +ᵥ w)
          * jInvariantFun ((n : ℝ) +ᵥ w)
      - ((phitVec z 1 * (E10Fun z - E4Fun z ^ 3))
          * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w))
        + (phitVec z 1 * DeltaFun z) * (2 * Work.Kernels.phi0 ((n : ℝ) +ᵥ w)
            * E4Fun ((n : ℝ) +ᵥ w) * jInvariantFun ((n : ℝ) +ᵥ w))))
      * (DeltaFun z * (jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z))⁻¹) :=
    (TBS.mul hnum TBS.ktl8_invdivisor).mono (by linarith [Real.pi_pos]) (by norm_num)
  refine ((hres.absorb_gen (by norm_num) (by nlinarith [Real.pi_pos])).congr_tile
    (fun w n z t hn hw hz ht => ?_))
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hd := tileDivisorLowerSharp w hw z t hz ht n hn
  have hJ : jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hd
    norm_num at hd
  simp only [Compact.PhiCorr, div_eq_mul_inv]
  field_simp

theorem TBS8TileTail :
    TBS Real.pi 1
      (fun (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) =>
        Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 8 ((n : ℝ) +ᵥ w) z) := by
  have hsum : TBS Real.pi 1 (fun w n z =>
      Compact.PhiMain ((n : ℝ) +ᵥ w) z + Compact.PhiDiv ((n : ℝ) +ᵥ w) z
        + Compact.PhiCorr ((n : ℝ) +ᵥ w) z) :=
    TBS.add (TBS.add TBS.ktl8_PhiMain TBS.ktl8_PhiDiv) TBS.ktl8_PhiCorr
  refine (TBS.const_mul (Compact.tailC)⁻¹ hsum).congr_tile (fun w n z t hn hw hz ht => ?_)
  have hG : Compact.Gplus 8 ((n : ℝ) +ᵥ w) z = Compact.Gplus8 ((n : ℝ) +ᵥ w) z := by
    rw [Compact.Gplus]; simp
  have hd := tileDivisorLowerSharp w hw z t hz ht n hn
  have hne : jInvariantFun ((n : ℝ) +ᵥ w) ≠ jInvariantFun z := by
    intro h0
    rw [h0, sub_self, mul_zero, norm_zero] at hd
    norm_num at hd
  rw [hG]
  exact (Compact.KPlus8_sub_Gplus8_decomp ((n : ℝ) +ᵥ w) z hne).symm


end

end Work.Asymptotics.Tile
