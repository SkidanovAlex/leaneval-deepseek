import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea6Road.TauCoreOfTauHeart
import Submission.Work.FIArea6.S16CleanSum_eq_Tsum
import Submission.Work.FIArea6.S16FcoefSum
import Submission.Work.FIArea6Road.TauHeartFserEqQ
import Submission.Work.FIArea6Road.TauHeartFcoefMass
import Submission.Work.FIArea6Road.TauHeartFcoefTailSub
import Submission.Work.FIArea6Road.TauHeartArith
import Submission.Work.FIArea6Road.TauHeartDefs
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6Road.TailFreqLBound
import Submission.Work.FIArea6Road.TailLogNStep
import Submission.Work.FIArea6V.CleanVDefs
import Submission.Work.FIArea6V.cleanBoxTermSum_eq_freqSum
import Submission.Work.FIArea6V.cleanTerm_eq_zero_of_axis_near
import Submission.Work.FIArea6V.S16CleanTailArithSmallTheta
import Submission.Work.FIArea6V.S16CleanTailArithLargeTheta

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The clean §16 core from the §16 heart** (the clean-lane analogue of
`Work.FIArea6Road.TauCoreOfTauHeart`).

The clean §16 box sum `Σ_{z ∈ boxN} [IsPrimary ∧ NoSmallPrimes]·q(arg z − φ)·p(|z|²)·μ·γ·χ·(z/|z|)^j`
of *FI* Lemma 16.2 is Fourier-expanded in the angular variable,
`Σ_z q(β_z)g(z) = Σ'_ℓ q̂(ℓ)e^{−iℓφ}Tsum Pa χ (j+ℓ) p` (`cleanBoxTermSum_eq_freqSum`, valid for
`−π ≤ φ ≤ π − 2πθ`), split at the frequency cutoff `L = freqL Pa`, and dominated by the heart
`S16TsumHeart` on the retained modes and by the trivial mass bound `‖Tsum‖ ≤ 4·winTauSq Pa` on the
tail (two arithmetic lemmas according to whether `θ` is below or above
`exp(−√log N/4)(log N)^3`).  When `φ` lies outside `[−π, π − 2πθ]` the sector is within `2πθ` of a
real axis, and the axis-free hypothesis on the polar box forces every summand to vanish
(`cleanTerm_eq_zero_of_axis_near`). -/
theorem S16CleanCoreTwoA_of_heart (hf : Work.FIArea6.S16TsumHeart) :
    Work.FIArea6V.S16CleanCoreTwoA := by
  intro ε hε hε4
  obtain ⟨c0, C0, x0, hc0, hC0, hx0, hH⟩ := hf ε hε hε4
  obtain ⟨xv, hxv, hvsep⟩ := Work.FIArea6Road.TauHeartArith.2.2
  obtain ⟨CT1, xT1, hCT1, hxT1, hTA1⟩ := S16CleanTailArithSmallTheta
  obtain ⟨CT2, xT2, hCT2, hxT2, hTA2⟩ := S16CleanTailArithLargeTheta
  refine ⟨min c0 ((4 : ℝ) ^ ε / 4), 100000000 * C0 + (CT1 + CT2),
    max x0 (max xv (max xT1 (max xT2 3))), ?_, ?_, ?_, ?_⟩
  · exact lt_min hc0 (div_pos (Real.rpow_pos_of_pos (by norm_num) ε) (by norm_num))
  · have h1 : (0 : ℝ) < 100000000 * C0 := by positivity
    linarith
  · exact lt_of_lt_of_le hx0 (le_max_left _ _)
  · intro Pa hx φ ν d j chi q p hax hν hνε hd1 hdd hj hχi hqC hpC hq0 hq1 hqsupp hqder
      hp0 hp1 hpsupp hpder
    classical
    have hx0' : x0 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
    have hxv' : xv ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_max_left xv (max xT1 (max xT2 3)))
        (le_max_right x0 (max xv (max xT1 (max xT2 3))))) hx
    have hxT1' : xT1 ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_trans (le_max_left xT1 (max xT2 3))
        (le_max_right xv (max xT1 (max xT2 3))))
        (le_max_right x0 (max xv (max xT1 (max xT2 3))))) hx
    have hxT2' : xT2 ≤ (Pa.x : ℝ) :=
      le_trans (le_trans (le_trans (le_trans (le_max_left xT2 3) (le_max_right xT1 (max xT2 3)))
        (le_max_right xv (max xT1 (max xT2 3))))
        (le_max_right x0 (max xv (max xT1 (max xT2 3))))) hx
    have hsep : 2 * Real.pi * Real.sqrt 2 * Pa.θ ≤ Pa.ϑ := hvsep Pa hxv'
    have hθle1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
    have hθlt : Pa.θ < 1 := Work.FIArea6Road.TauHeartArith.1 Pa
    have hη4 : Pa.η ≤ 1 / 4 := Work.FIArea6Road.TauHeartArith.2.1 Pa
    have hθ0 : (0 : ℝ) < Pa.θ := Pa.hθ0
    have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one hN1
    have hlogN0 : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg hN1
    have hlogN6 : (0 : ℝ) ≤ (Real.log Pa.N) ^ (6 : ℕ) := pow_nonneg hlogN0 _
    have hdpos : (0 : ℝ) < ((4 * d : ℕ) : ℝ) := by
      have : (0 : ℕ) < 4 * d := by omega
      exact_mod_cast this
    have h4d1 : (1 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 4 * d)
    have h4d4 : (4 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 ≤ 4 * d)
    have hd2 : ∀ α : ℝ, |iteratedDeriv 2 q α| ≤ 1048576 / Pa.θ ^ 2 := by
      intro α
      have h := hqder 2 le_rfl α
      have hcm : Work.FITop4.cMoll 2 = (1048576 : ℝ) := by
        rw [Work.FITop4.cMoll]; norm_num
      rw [hcm] at h
      have hpow : Pa.θ ^ (-(2 : ℝ)) = (Pa.θ ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hθ0)]
        norm_num
      rw [div_eq_mul_inv, ← hpow]
      exact h
    have hχ1 : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hχi.1.2.2.1
    have hpabs : ∀ u : ℝ, |p u| ≤ 1 := fun u => abs_le.mpr ⟨by linarith [hp0 u], hp1 u⟩
    rw [← boxTermSumClean_eq Pa φ j chi q p]
    set c : ℝ := min c0 ((4 : ℝ) ^ ε / 4) with hcdef
    have hcpos : 0 < c :=
      lt_min hc0 (div_pos (Real.rpow_pos_of_pos (by norm_num) ε) (by norm_num))
    have hcle : c ≤ c0 := min_le_left _ _
    have hc4 : c ≤ (4 : ℝ) ^ ε / 4 := min_le_right _ _
    set E1 : ℝ := Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
      with hE1def
    set E2 : ℝ := Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))) with hE2def
    have hE1pos : 0 < E1 := by rw [hE1def]; exact Real.exp_pos _
    have hE2pos : 0 < E2 := by rw [hE2def]; exact Real.exp_pos _
    set Mh : ℝ := C0 * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
      with hMhdef
    have hMh0 : 0 ≤ Mh := by
      rw [hMhdef]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC0)
        (add_nonneg (le_of_lt hE1pos) (le_of_lt hE2pos))) (le_of_lt hdpos)) hN0) hlogN6
    -- `ηc(4d)^{-ε} ≤ 1/4`
    have h4e : (4 : ℝ) ^ ε * (4 : ℝ) ^ (-ε) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4), add_neg_cancel, Real.rpow_zero]
    have hmono : ((4 * d : ℕ) : ℝ) ^ (-ε) ≤ (4 : ℝ) ^ (-ε) := by
      have h1 : (4 : ℝ) ^ ε ≤ ((4 * d : ℕ) : ℝ) ^ ε :=
        Real.rpow_le_rpow (by norm_num) h4d4 (le_of_lt hε)
      have h2 : ((4 * d : ℕ) : ℝ) ^ (-ε) = (((4 * d : ℕ) : ℝ) ^ ε)⁻¹ :=
        Real.rpow_neg (le_of_lt hdpos) ε
      have h3 : (4 : ℝ) ^ (-ε) = ((4 : ℝ) ^ ε)⁻¹ := Real.rpow_neg (by norm_num) ε
      rw [h2, h3]
      exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) ε) h1
    have hkey : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) ≤ 1 / 4 := by
      have h2 : Pa.η * c ≤ (1 / 4) * ((4 : ℝ) ^ ε / 4) := by
        calc Pa.η * c ≤ (1 / 4) * c := mul_le_mul_of_nonneg_right hη4 (le_of_lt hcpos)
          _ ≤ (1 / 4) * ((4 : ℝ) ^ ε / 4) := mul_le_mul_of_nonneg_left hc4 (by norm_num)
      have h3 : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε)
          ≤ ((1 / 4) * ((4 : ℝ) ^ ε / 4)) * (4 : ℝ) ^ (-ε) :=
        mul_le_mul h2 hmono (Real.rpow_nonneg (le_of_lt hdpos) _)
          (mul_nonneg (by norm_num) (div_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) ε))
            (by norm_num)))
      have h4 : ((1 / 4) * ((4 : ℝ) ^ ε / 4)) * (4 : ℝ) ^ (-ε) = 1 / 16 := by
        calc ((1 / 4) * ((4 : ℝ) ^ ε / 4)) * (4 : ℝ) ^ (-ε)
            = (1 / 16) * ((4 : ℝ) ^ ε * (4 : ℝ) ^ (-ε)) := by ring
          _ = 1 / 16 := by rw [h4e]; norm_num
      rw [h4] at h3
      linarith [h3]
    have hE1low : Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) ≤ E1 := by
      rw [hE1def, Real.exp_le_exp]
      have hs := Real.sqrt_nonneg (Real.log Pa.N)
      have h1 : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)
          ≤ (1 / 4) * Real.sqrt (Real.log Pa.N) := mul_le_mul_of_nonneg_right hkey hs
      have h2 : (1 / 4) * Real.sqrt (Real.log Pa.N) = Real.sqrt (Real.log Pa.N) / 4 := by ring
      linarith [h1, h2.le, h2.ge]
    -- the heart at the reduced constant
    have hheart : ∀ m : ℤ, |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) →
        ‖Work.FIArea6Hecke.Tsum Pa chi m p‖ ≤ Mh := by
      intro m hm
      have h0 := hH Pa hx0' ν d m chi p hν hνε hd1 hdd hm hχi hpC hp0 hp1 hpsupp hpder
      have hE1le : Real.exp (-(Pa.η * c0 * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
          ≤ E1 := by
        rw [hE1def, Real.exp_le_exp]
        have h4d : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) ^ (-ε) := Real.rpow_nonneg (le_of_lt hdpos) _
        have hs : (0 : ℝ) ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_nonneg _
        have h1 : Pa.η * c ≤ Pa.η * c0 := mul_le_mul_of_nonneg_left hcle (le_of_lt Pa.hη)
        have h2 : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) ≤ Pa.η * c0 * ((4 * d : ℕ) : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right h1 h4d
        have h3 : Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)
            ≤ Pa.η * c0 * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N) :=
          mul_le_mul_of_nonneg_right h2 hs
        linarith [h3]
      rw [hMhdef]
      refine le_trans h0 ?_
      have h1 : C0 * (Real.exp (-(Pa.η * c0 * ((4 * d : ℕ) : ℝ) ^ (-ε)
            * Real.sqrt (Real.log Pa.N)))
          + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))) ≤ C0 * (E1 + E2) := by
        rw [hE2def]
        exact mul_le_mul_of_nonneg_left (add_le_add hE1le le_rfl) (le_of_lt hC0)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 (le_of_lt hdpos)) hN0) hlogN6
    -- case analysis on `φ`
    by_cases hφnc : φ ≤ Real.pi - 2 * Real.pi * Pa.θ
    · by_cases hφlo : -Real.pi ≤ φ
      · -- good case: the sector sum is the Fourier–Hecke series
        have hEq := cleanBoxTermSum_eq_freqSum Pa φ j chi q p hqC hq0 hq1 hqsupp hd2 hpsupp hθlt
          hφlo hφnc
        rw [hEq]
        set F : ℤ → ℂ := fun ℓ => Work.FIArea5.S16.fcoef q ℓ *
            Complex.exp (-((ℓ : ℂ) * Complex.I * (φ : ℂ)))
            * Work.FIArea6Hecke.Tsum Pa chi (j + ℓ) p with hFdef
        set L : ℕ := Work.FIArea6Hecke.freqL Pa with hLdef
        set sf : Finset ℤ := Finset.Icc (-(L : ℤ)) (L : ℤ) with hsdef
        have hL1 : 1 ≤ L := by
          rw [hLdef, Work.FIArea6Hecke.freqL]
          refine Nat.le_floor ?_
          push_cast
          exact Real.one_le_exp (Real.sqrt_nonneg _)
        have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < L)
        have hLexp : ((L : ℤ) : ℝ) ≤ Real.exp (Real.sqrt (Real.log Pa.N)) := by
          rw [hLdef, Work.FIArea6Hecke.freqL]
          push_cast
          exact Nat.floor_le (Real.exp_nonneg _)
        have hWnn : (0 : ℝ) ≤ 4 * winTauSq Pa := by
          have hw : (0 : ℝ) ≤ winTauSq Pa := by
            unfold winTauSq
            exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
          linarith
        have hTsum_le : ∀ m : ℤ, ‖Work.FIArea6Hecke.Tsum Pa chi m p‖ ≤ 4 * winTauSq Pa :=
          fun m => Work.FIArea6Road.norm_Tsum_le_suppWindow Pa chi m p hχ1 hpabs hpsupp
        have hFsumm : Summable F := by
          refine Summable.of_norm_bounded
            (g := fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖ * (4 * winTauSq Pa))
            ((Work.FIArea6Road.summable_norm_fcoef q hθ0 hθle1 hqC hq0 hq1 hqsupp hd2).mul_right _)
            (fun ℓ => ?_)
          simp only [hFdef, norm_mul, Work.FIArea6Road.norm_exp_neg_int_mul_I, mul_one, one_mul]
          exact mul_le_mul_of_nonneg_left (hTsum_le (j + ℓ)) (norm_nonneg _)
        rw [(Summable.sum_add_tsum_compl (s := sf) hFsumm).symm]
        refine le_trans (norm_add_le _ _) ?_
        -- main term
        have hmain : ‖∑ ℓ ∈ sf, F ℓ‖ ≤ 100000000 * Mh := by
          refine le_trans (norm_sum_le _ _) ?_
          have h1 : ∀ ℓ ∈ sf, ‖F ℓ‖ ≤ ‖Work.FIArea5.S16.fcoef q ℓ‖ * Mh := by
            intro ℓ hℓ
            rw [hsdef, Finset.mem_Icc] at hℓ
            have hℓabs : |((ℓ : ℝ))| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) := by
              rw [abs_le]
              constructor
              · have h := hℓ.1
                have h2 : -(((L : ℤ)) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
                linarith [h2, hLexp]
              · have h := hℓ.2
                have h2 : ((ℓ : ℤ) : ℝ) ≤ ((L : ℤ) : ℝ) := by exact_mod_cast h
                linarith [h2, hLexp]
            have hm : |(((j + ℓ : ℤ)) : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) := by
              have h3 : ((j + ℓ : ℤ) : ℝ) = (j : ℝ) + (ℓ : ℝ) := by push_cast; ring
              rw [h3]
              have h4 := abs_add_le (j : ℝ) (ℓ : ℝ)
              have h5 : |(j : ℝ)| ≤ 3 * Real.exp (Real.sqrt (Real.log Pa.N)) := hj
              linarith
            simp only [hFdef, norm_mul, Work.FIArea6Road.norm_exp_neg_int_mul_I, mul_one, one_mul]
            exact mul_le_mul_of_nonneg_left (hheart (j + ℓ) hm) (norm_nonneg _)
          calc ∑ ℓ ∈ sf, ‖F ℓ‖ ≤ ∑ ℓ ∈ sf, ‖Work.FIArea5.S16.fcoef q ℓ‖ * Mh :=
                Finset.sum_le_sum h1
            _ = (∑ ℓ ∈ sf, ‖Work.FIArea5.S16.fcoef q ℓ‖) * Mh := by rw [Finset.sum_mul]
            _ ≤ 100000000 * Mh := by
                refine mul_le_mul_of_nonneg_right ?_ hMh0
                rw [hsdef, hLdef]
                exact Work.FIArea6.S16FcoefSum hθ0 hθle1 hqC hq0 hq1 hqsupp hd2
                  (Work.FIArea6Hecke.freqL Pa)
        -- tail
        have hbound1 : ‖∑' (ℓ : ↥((sf : Set ℤ))ᶜ), F (ℓ : ℤ)‖
            ≤ (4 * winTauSq Pa) * (∑' (ℓ : ↥((sf : Set ℤ))ᶜ),
                ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖) := by
          have h1 : ∀ ℓ : ↥((sf : Set ℤ))ᶜ, ‖F (ℓ : ℤ)‖
              ≤ ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖ * (4 * winTauSq Pa) := by
            intro ℓ
            simp only [hFdef, norm_mul, Work.FIArea6Road.norm_exp_neg_int_mul_I, mul_one, one_mul]
            exact mul_le_mul_of_nonneg_left (hTsum_le (j + (ℓ : ℤ))) (norm_nonneg _)
          refine le_trans (norm_tsum_le_tsum_norm (hFsumm.subtype _ |>.norm)) ?_
          calc ∑' (ℓ : ↥((sf : Set ℤ))ᶜ), ‖F (ℓ : ℤ)‖
              ≤ ∑' (ℓ : ↥((sf : Set ℤ))ᶜ), ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖
                  * (4 * winTauSq Pa) :=
                Summable.tsum_le_tsum h1 ((hFsumm.subtype _).norm)
                  (((Work.FIArea6Road.summable_norm_fcoef q hθ0 hθle1 hqC hq0 hq1 hqsupp
                    hd2).subtype _).mul_right _)
            _ = (∑' (ℓ : ↥((sf : Set ℤ))ᶜ), ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖)
                  * (4 * winTauSq Pa) := tsum_mul_right
            _ = (4 * winTauSq Pa) * (∑' (ℓ : ↥((sf : Set ℤ))ᶜ),
                  ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖) := by ring
        have htail : ‖∑' (ℓ : ↥((sf : Set ℤ))ᶜ), F (ℓ : ℤ)‖
            ≤ (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
              * (Real.log Pa.N) ^ (6 : ℕ) := by
          by_cases hθsmall : Pa.θ ≤ Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
              * (Real.log Pa.N) ^ (3 : ℕ)
          · have hcoef1 : (∑' (ℓ : ↥((sf : Set ℤ))ᶜ), ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖)
                ≤ 10000000 :=
              le_trans (Summable.tsum_subtype_le (fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖)
                ((sf : Set ℤ))ᶜ (fun _ => norm_nonneg _)
                (Work.FIArea6Road.summable_norm_fcoef q hθ0 hθle1 hqC hq0 hq1 hqsupp hd2))
                (Work.FIArea6Road.TauHeartFcoefMass q hθ0 hθle1 hqC hq0 hq1 hqsupp hd2)
            have hstep1 : (4 * winTauSq Pa) * (∑' (ℓ : ↥((sf : Set ℤ))ᶜ),
                  ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖) ≤ 10000000 * (4 * winTauSq Pa) := by
              calc (4 * winTauSq Pa) * (∑' (ℓ : ↥((sf : Set ℤ))ᶜ),
                      ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖)
                  ≤ (4 * winTauSq Pa) * 10000000 := mul_le_mul_of_nonneg_left hcoef1 hWnn
                _ = 10000000 * (4 * winTauSq Pa) := by ring
            have hscale : CT1 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                  * (Real.log Pa.N) ^ (6 : ℕ)
                ≤ (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                  * (Real.log Pa.N) ^ (6 : ℕ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith [hCT2.le]) (Real.exp_nonneg _)) hN0) hlogN6
            exact le_trans (le_trans hbound1 hstep1) (le_trans (hTA1 Pa hxT1' hθsmall) hscale)
          · have hθlarge : Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * (Real.log Pa.N) ^ (3 : ℕ)
                ≤ Pa.θ := le_of_lt (not_le.mp hθsmall)
            have hcoef2 : (∑' (ℓ : ↥((sf : Set ℤ))ᶜ), ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖)
                ≤ 20000000 / (Real.pi * Pa.θ * (L : ℝ)) := by
              rw [hsdef] at *
              exact Work.FIArea6Road.TauHeartFcoefTailSub q hθ0 hθle1 hqC hq0 hq1 hqsupp hd2 L hL1
            have hstep2 : (4 * winTauSq Pa) * (∑' (ℓ : ↥((sf : Set ℤ))ᶜ),
                  ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖)
                ≤ (4 * winTauSq Pa) * (20000000 / (Real.pi * Pa.θ * (L : ℝ))) :=
              mul_le_mul_of_nonneg_left hcoef2 hWnn
            have hscale : CT2 * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                  * (Real.log Pa.N) ^ (6 : ℕ)
                ≤ (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                  * (Real.log Pa.N) ^ (6 : ℕ) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith [hCT1.le]) (Real.exp_nonneg _)) hN0) hlogN6
            exact le_trans (le_trans hbound1 hstep2) (le_trans (hTA2 Pa hxT2' hθlarge) hscale)
        -- assembly for the good case
        have hM : 100000000 * Mh ≤ 100000000 * C0 * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
            * (Real.log Pa.N) ^ (6 : ℕ) :=
          le_of_eq (by rw [hMhdef]; ring)
        have hT2 : (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
              * (Real.log Pa.N) ^ (6 : ℕ)
            ≤ (CT1 + CT2) * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
              * (Real.log Pa.N) ^ (6 : ℕ) := by
          have h1 : Real.exp (-(Real.sqrt (Real.log Pa.N) / 4))
              ≤ (E1 + E2) * ((4 * d : ℕ) : ℝ) := by
            have h2 : E1 ≤ E1 + E2 := le_add_of_nonneg_right (le_of_lt hE2pos)
            have h3 : E1 + E2 ≤ (E1 + E2) * ((4 * d : ℕ) : ℝ) := by
              have h5 : (0 : ℝ) ≤ E1 + E2 := by linarith [hE1pos, hE2pos]
              simpa using mul_le_mul_of_nonneg_left h4d1 h5
            linarith [hE1low, h2, h3]
          calc (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ)
              ≤ (CT1 + CT2) * ((E1 + E2) * ((4 * d : ℕ) : ℝ)) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h1 (by positivity)) hN0) hlogN6
            _ = (CT1 + CT2) * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ) := by ring
        refine le_trans (add_le_add hmain htail) ?_
        calc 100000000 * Mh
              + (CT1 + CT2) * Real.exp (-(Real.sqrt (Real.log Pa.N) / 4)) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ)
            ≤ 100000000 * C0 * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ)
              + (CT1 + CT2) * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ) := add_le_add hM hT2
          _ = (100000000 * C0 + (CT1 + CT2)) * (E1 + E2) * ((4 * d : ℕ) : ℝ) * Pa.N
                * (Real.log Pa.N) ^ (6 : ℕ) := by ring
      · -- `φ < −π`: the sector is within `2πθ` of the negative real axis
        push_neg at hφlo
        have hzero : boxTermSumClean Pa φ j chi q p = 0 := by
          unfold boxTermSumClean
          refine Finset.sum_eq_zero (fun z _ => ?_)
          by_cases hc : SuppClean Pa z
          · rw [if_pos hc]
            by_cases hq : q (Complex.arg z.toComplex - φ) = 0
            · simp [Work.FIArea6Road.s16Term, hq]
            · by_cases hp : p (Work.FIPlan.gnorm z) = 0
              · simp [Work.FIArea6Road.s16Term, hp]
              · have hβ := hqsupp _ hq
                exact cleanTerm_eq_zero_of_axis_near Pa φ j chi q p hax hqC hqsupp hpsupp hsep hθle1
                  hc.1 (Work.FIArea6Road.abs_sin_le_of_near_neg_pi (Complex.neg_pi_lt_arg _)
                    (by linarith [hβ.2]))
          · rw [if_neg hc]
        rw [hzero, norm_zero]
        have hfin : (0 : ℝ) ≤ (100000000 * C0 + (CT1 + CT2)) * (E1 + E2) * ((4 * d : ℕ) : ℝ)
            * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
          rw [hE1def, hE2def]
          have h1 : (0 : ℝ) < 100000000 * C0 + (CT1 + CT2) := by linarith [hC0, hCT1, hCT2]
          positivity
        linarith
    · -- `π − 2πθ < φ`: the sector is within `2πθ` of the positive real axis
      push_neg at hφnc
      have hzero : boxTermSumClean Pa φ j chi q p = 0 := by
        unfold boxTermSumClean
        refine Finset.sum_eq_zero (fun z _ => ?_)
        by_cases hc : SuppClean Pa z
        · rw [if_pos hc]
          by_cases hq : q (Complex.arg z.toComplex - φ) = 0
          · simp [Work.FIArea6Road.s16Term, hq]
          · by_cases hp : p (Work.FIPlan.gnorm z) = 0
            · simp [Work.FIArea6Road.s16Term, hp]
            · have hβ := hqsupp _ hq
              exact cleanTerm_eq_zero_of_axis_near Pa φ j chi q p hax hqC hqsupp hpsupp hsep hθle1
                hc.1 (Work.FIArea6Road.abs_sin_le_of_near_pi (by linarith [hβ.1])
                  (Complex.arg_le_pi _) (by linarith [hφnc]))
        · rw [if_neg hc]
      rw [hzero, norm_zero]
      have hfin : (0 : ℝ) ≤ (100000000 * C0 + (CT1 + CT2)) * (E1 + E2) * ((4 * d : ℕ) : ℝ)
          * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
        rw [hE1def, hE2def]
        have h1 : (0 : ℝ) < 100000000 * C0 + (CT1 + CT2) := by linarith [hC0, hCT1, hCT2]
        positivity
      linarith

end

end Work.FIArea6V
