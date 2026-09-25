import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Fleet.chainMeanValueFamily
import Submission.Work.NN.Core.Fleet.supInterpLp
import Submission.Work.NN.Core.Fleet.moserIterateLimit
import Submission.Work.NN.Core.Fleet.selfImprove

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff Topology

namespace Work.NN.Core.Lev2

open Work.NN.Core.Fleet

private abbrev Pd {n : ℕ} (r : Fin n → ℝ) : Set (Work.NN.Core.Cn n) :=
  Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) r

/-- **Moser self-improvement (Lipschitz `u`).**  The statement is character-for-character
`Work.NN.Core.Lev.selfImproveLip`, whose proof in `Submission/Work/NN/Core/Lev/lipChain.lean` can be
copied verbatim (that file does not build at the moment only because of its unrelated import
`lipMoserBoostC`, so copy the text into this file, do not import `lipChain`).  The proof needs
`Work.NN.Core.Fleet.supInterpLp.supInterpLp`,
`Work.NN.Core.Fleet.moserIterateLimit.moserIterateLimit`, the `lamFamily` facts of
`Fleet/chainMeanValueFamily` and `Work.CR.Flat.polydisc_mono`; all of these are sorry-free. -/
theorem selfImproveLipCopy {n : ℕ} (hn : 0 < n) {σ ρ ρstar : Fin n → ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hσρstar : ∀ j, σ j < ρstar j) (hρstarρ : ∀ j, ρstar j < ρ j)
    {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : NNReal} (u : Work.NN.Core.Cn n → ℂ),
      LipschitzOnWith K u (Work.CR.Flat.polydisc 0 ρ) →
      (∀ (j : ℕ) (z : Work.NN.Core.Cn n),
        z ∈ Work.CR.Flat.polydisc 0 (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^j)) →
        ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal (A * B^j) *
          MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (2 * (n:ℝ) - 1)))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0
              (fun i => σ i + (ρstar i - σ i) * (1 - (1/2:ℝ)^(j+1)))))) →
      ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
        ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) := by
  have hσle : ∀ i, σ i ≤ ρstar i := fun i => le_of_lt (hσρstar i)
  have hn1 : 1 ≤ n := hn
  set k : ℕ := 2*n - 1 with hkdef
  have hk1 : 1 ≤ k := by rw [hkdef]; omega
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk1)
  have hkcast : ((k:ℝ)) = 2*(n:ℝ) - 1 := by
    rw [hkdef]
    have h1 : (1:ℕ) ≤ 2*n := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  set r : ℝ := 1 - 1/(k:ℝ) with hrdef
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    have : 0 < 1/(k:ℝ) := one_div_pos.mpr hkpos
    have : 1/(k:ℝ) ≤ 1 := by
      rw [div_le_one hkpos]; exact_mod_cast hk1
    linarith
  have hr1 : r < 1 := by
    rw [hrdef]
    have : 0 < 1/(k:ℝ) := one_div_pos.mpr hkpos
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨A^k * B^(r*(k:ℝ)^2), ?_, ?_⟩
  · have h1 : 0 < A^k := pow_pos hA k
    have h2 : 0 < B^(r*(k:ℝ)^2) := Real.rpow_pos_of_pos hBpos _
    exact mul_pos h1 h2
  · intro K u hLip hfam
    have hmeasρ : AEStronglyMeasurable u (volume.restrict (Pd ρ)) :=
      hLip.continuousOn.aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc (0:Cn n) ρ).measurableSet
    let M : ℕ → ENNReal := fun j => ⨆ z : Pd (lamFamily σ ρstar j), ENNReal.ofReal ‖u (z:Cn n)‖
    have hMpoint : ∀ j (z : Cn n) (hz : z ∈ Pd (lamFamily σ ρstar j)),
        ENNReal.ofReal ‖u z‖ ≤ M j := by
      intro j z hz
      exact le_iSup (fun z : Pd (lamFamily σ ρstar j) => ENNReal.ofReal ‖u (z:Cn n)‖) ⟨z, hz⟩
    have hexp : ENNReal.ofReal (2 * (2 * (n:ℝ) - 1)) = ENNReal.ofReal (2 * (k:ℝ)) := by
      congr 1
      rw [hkcast]
    set Q : ENNReal := eLpNorm u 2 (volume.restrict (Pd ρ)) with hQsub
    have hr' : ((k:ℝ) - 1)/(k:ℝ) = r := by
      rw [hrdef]; field_simp
    have hrec : ∀ j, M j ≤ ENNReal.ofReal (A * B^j) * Q ^ (1/(k:ℝ)) * (M (j+1))^r := by
      intro j
      have h1 : M j ≤ ENNReal.ofReal (A * B^j) *
          eLpNorm u (ENNReal.ofReal (2*(k:ℝ)))
            (volume.restrict (Pd (lamFamily σ ρstar (j+1)))) := by
        apply iSup_le
        intro z
        have hz : (z : Cn n) ∈ Pd (lamFamily σ ρstar j) := z.2
        have hhz := hfam j (z : Cn n) hz
        rw [hexp] at hhz
        exact hhz
      have hST : Pd (lamFamily σ ρstar (j+1)) ⊆ Pd ρ :=
        Work.CR.Flat.polydisc_mono
          (fun i => le_of_lt (lt_trans (lamFamily_lt_ρstar hσρstar (j+1) i) (hρstarρ i)))
      have h2 : eLpNorm u (ENNReal.ofReal (2*(k:ℝ)))
            (volume.restrict (Pd (lamFamily σ ρstar (j+1))))
          ≤ (M (j+1)) ^ (((k:ℝ)-1)/(k:ℝ)) * Q ^ (1/(k:ℝ)) := by
        have hmain := supInterpLp (μ := volume) (S := Pd (lamFamily σ ρstar (j+1))) (T := Pd ρ)
          (u := u) hk1 (fun z hz => hMpoint (j+1) z hz) hST hmeasρ
        simpa [Q] using hmain
      calc M j ≤ ENNReal.ofReal (A * B^j) *
            eLpNorm u (ENNReal.ofReal (2*(k:ℝ))) (volume.restrict (Pd (lamFamily σ ρstar (j+1)))) := h1
        _ ≤ ENNReal.ofReal (A * B^j) * ((M (j+1)) ^ (((k:ℝ)-1)/(k:ℝ)) * Q ^ (1/(k:ℝ))) :=
              mul_le_mul' le_rfl h2
        _ = ENNReal.ofReal (A * B^j) * Q ^ (1/(k:ℝ)) * (M (j+1))^r := by rw [hr']; ring
    obtain ⟨K, hKpos, hMK⟩ : ∃ K : ℝ, 0 < K ∧ ∀ j, M j ≤ ENNReal.ofReal K := by
      have hcd_compact : IsCompact {z : Cn n | ∀ i, ‖z i‖ ≤ ρstar i} := by
        have h1 : {z : Cn n | ∀ i, ‖z i‖ ≤ ρstar i}
            = Set.univ.pi (fun i : Fin n => Metric.closedBall (0:ℂ) (ρstar i)) := by
          ext z
          simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Metric.mem_closedBall,
            dist_eq_norm, sub_zero]
        rw [h1]
        exact isCompact_univ_pi (fun i => isCompact_closedBall (0:ℂ) (ρstar i))
      have hcd_sub : {z : Cn n | ∀ i, ‖z i‖ ≤ ρstar i} ⊆ Pd ρ := by
        intro z hz
        rw [Work.CR.Flat.mem_polydisc]
        intro i
        simp only [Pi.zero_apply, sub_zero]
        exact lt_of_le_of_lt (hz i) (hρstarρ i)
      have hcont : ContinuousOn u {z : Cn n | ∀ i, ‖z i‖ ≤ ρstar i} :=
        hLip.continuousOn.mono hcd_sub
      obtain ⟨C₀, hC₀⟩ := hcd_compact.exists_bound_of_continuousOn hcont
      refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
      intro j
      apply iSup_le
      intro z
      have hzcd : (z : Cn n) ∈ {z : Cn n | ∀ i, ‖z i‖ ≤ ρstar i} := by
        intro i
        have hh : ‖(z:Cn n) i‖ < lamFamily σ ρstar j i := by
          simpa [Pi.zero_apply] using z.2 i
        exact le_trans (le_of_lt hh) (lamFamily_le_ρstar hσle j i)
      have := hC₀ (z : Cn n) hzcd
      exact ENNReal.ofReal_le_ofReal (le_trans this (le_max_left _ _))
    -- main case analysis
    intro z hz
    by_cases hQtop : Q = ⊤
    · rw [hQtop, ENNReal.mul_top]
      · exact le_top
      · exact (ENNReal.ofReal_pos.mpr (by
          have h1 : 0 < A^k := pow_pos hA k
          have h2 : 0 < B^(r*(k:ℝ)^2) := Real.rpow_pos_of_pos hBpos _
          exact mul_pos h1 h2)).ne'
    · by_cases hM0 : M 0 = 0
      · have hz' : z ∈ Pd (lamFamily σ ρstar 0) := by simpa [lamFamily] using hz
        have := hMpoint 0 z hz'
        rw [hM0] at this
        exact le_trans this zero_le
      · have hM0pos : 0 < M 0 := pos_iff_ne_zero.mpr hM0
        have hMne : ∀ j, M j ≠ ⊤ := fun j =>
          ne_of_lt (lt_of_le_of_lt (hMK j) ENNReal.ofReal_lt_top)
        have hMmono : ∀ j, M 0 ≤ M j := by
          intro j
          apply iSup_le
          intro zz
          have hz' : (zz : Cn n) ∈ Pd (lamFamily σ ρstar j) :=
            Work.CR.Flat.polydisc_mono (fun i => lamFamily_mono hσle (Nat.zero_le j) i) zz.2
          exact hMpoint j (zz : Cn n) hz'
        have hQ0 : Q ≠ 0 := by
          intro hQ0eq
          have h := hrec 0
          rw [hQ0eq, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hkpos)] at h
          simp at h
          exact hM0 h
        set q : ℝ := Q.toReal with hqdef
        have hqpos : 0 < q := by
          rw [hqdef]; exact ENNReal.toReal_pos hQ0 hQtop
        set mm : ℕ → ℝ := fun j => (M j).toReal with hmmdef
        have hmmpos : ∀ j, 0 < mm j := by
          intro j
          have h1 : 0 < (M 0).toReal := ENNReal.toReal_pos hM0 (hMne 0)
          have h2 : (M 0).toReal ≤ (M j).toReal := ENNReal.toReal_mono (hMne j) (hMmono j)
          exact lt_of_lt_of_le h1 h2
        have hmmK : ∀ j, mm j ≤ K := by
          intro j
          have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMK j)
          rw [ENNReal.toReal_ofReal hKpos.le] at h
          exact h
        have hABnn : ∀ j, (0:ℝ) ≤ A * B^j := fun j =>
          mul_nonneg hA.le (pow_nonneg (le_trans zero_le_one hB) j)
        have hrecR : ∀ j, mm j ≤ A * B^j * q^(1/(k:ℝ)) * (mm (j+1))^r := by
          intro j
          have hCjne : ENNReal.ofReal (A * B^j) * Q ^ (1/(k:ℝ)) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hkpos)) hQtop).ne
          have hne : ENNReal.ofReal (A * B^j) * Q ^ (1/(k:ℝ)) * (M (j+1))^r ≠ ⊤ :=
            ENNReal.mul_ne_top hCjne
              (ENNReal.rpow_lt_top_of_nonneg hr0 (hMne (j+1))).ne
          have h := ENNReal.toReal_mono hne (hrec j)
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hABnn j),
              ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h
          exact h
        have hfin : mm 0 ≤ A^k * B^(r * (k:ℝ)^2) * q :=
          moserIterateLimit hr0 hr1 hmmpos hKpos hmmK hA hBpos hqpos hk1 hrdef hrecR
        have hM0le : M 0 ≤ ENNReal.ofReal (A^k * B^(r*(k:ℝ)^2)) * Q := by
          have h1 : ENNReal.ofReal (mm 0) = M 0 := ENNReal.ofReal_toReal (hMne 0)
          rw [← h1]
          calc ENNReal.ofReal (mm 0) ≤ ENNReal.ofReal (A^k * B^(r*(k:ℝ)^2) * q) :=
                ENNReal.ofReal_le_ofReal hfin
            _ = ENNReal.ofReal (A^k * B^(r*(k:ℝ)^2)) * ENNReal.ofReal q :=
                ENNReal.ofReal_mul (by positivity)
            _ = ENNReal.ofReal (A^k * B^(r*(k:ℝ)^2)) * Q := by
                congr 1
                exact ENNReal.ofReal_toReal hQtop
        have hz' : z ∈ Pd (lamFamily σ ρstar 0) := by simpa [lamFamily] using hz
        exact le_trans (hMpoint 0 z hz') hM0le



end Work.NN.Core.Lev2
