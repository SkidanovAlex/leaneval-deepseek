import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.regBaseAssembly
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.bijective_fderiv_sqDisk_foldBox
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.cutTransport
import Submission.Work.Drive.collapse_polar_dictionary
import Submission.Work.Drive.pairOneDataT6
import Submission.Work.Drive.diskPlane_mfderiv
import Submission.Work.Drive.collarZeroInterior

/-!
# The `s = 1` pair datum of the transport `T6` at the design's chains

*(H3 lane; the last analytic input of the per-block wrapper
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` (`Drive/blockT6Wrapper.lean`, H4).)*

See `PAIRONEDATA_PLAN.md` and `PAIRONEDATA_INTERIORITY_DEFECT.md` for the design.  The statement is the
*interior* version: the consumer `Work.Drive.hregBase_design_chains` applies `hpair` only at collar
meets carrying `Work.Drive.CollarInterior`, and on the faces of the parameter square
`PairOneData` is **false** (the fold direction of `sqDisk ∘ foldBox` is killed by both plane blocks, so
clause (i) fails).  The remaining inputs are the two `GoodLoopChain`s of `T6GenAt` at the core and
diameter meets, the collar data, and the seam clause of the chart.
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The core/diameter meet identification of an `s = 1` collar meet of the design's pair.** -/
theorem exists_meetData_of_ppMeet
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₁ c₂ : ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δc : ℝ} (hδc : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun t => 1 - t) P₁)) :
    ∀ x ∈ ppMeet (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 →
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) 1 ∧
        (t, ftY x) ∈ coreMeet Q c₁ P₁ ∧
        (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂) ∧
        PolarDict β Q (ftU x) t σ ∧
        (∀ a : EuclideanSpace ℝ (Fin 2),
          mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a = 0 →
          ∃ μ : ℝ, mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a = μ • cdFoldDisk (ftU x)) ∧
        (1 - 2 * σ) • colCirclePt t = cdFoldDisk (ftU x) ∧
        (1 - 2 * σ) ≠ 0 ∧ cdFoldDisk (ftU x) ≠ 0 := by
  intro x hx hs
  have hQsm : IsSmoothChart Q := hQ
  -- ### 1. the box coordinates of the two sweeps and of the plane parameter
  have hY2 : ftY x ∈ Submission.Drive.unitBox 2 := by
    intro i
    have h := hx.1 ⟨3 + i.val, by omega⟩
    simpa [ftY, WithLp.ofLp_toLp] using h
  have hZ2 : ftZ x ∈ Submission.Drive.unitBox 2 := by
    intro i
    have h := hx.1 ⟨6 + i.val, by omega⟩
    simpa [ftZ, WithLp.ofLp_toLp] using h
  have hVeq : colPlane β Q 1 (ftU x) = clampedSweep c₁ (fun t => 1 - t) P₁ (ftY x) := by
    have h := hx.2.1
    rwa [hs] at h
  have hWeq : diskPlane Q (ftU x) = clampedSweep c₂ (fun t => 1 - t) P₂ (ftZ x) := hx.2.2
  -- ### 2. the cut point of the honest plane, and the collar
  have hcutmem : diskPtFun (ftU x) ∈ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂) := by
    refine ⟨?_, ?_⟩
    · have h1 : cplxOf (diskPtFun (ftU x)) = cdFoldDisk (ftU x) := by
        rw [diskPtFun_apply, cplxOf_cplxOfInv]; rfl
      rw [h1]
      exact norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
    · refine ⟨ftZ x, hZ2, ?_⟩
      rw [← hWeq, diskPlane_eq_Q_cplxOf_diskPtFun]
  have hcol : δc < ‖cdFoldDisk (ftU x)‖ := by
    have h1 : ¬ (‖cplxOf (diskPtFun (ftU x))‖ ≤ δc) := fun hh => hδcut _ hh hcutmem
    have h2 : cplxOf (diskPtFun (ftU x)) = cdFoldDisk (ftU x) := by
      rw [diskPtFun_apply, cplxOf_cplxOfInv]; rfl
    rw [h2] at h1
    exact lt_of_not_ge h1
  have hz_ne : cdFoldDisk (ftU x) ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt hδc hcol)
  have hzle : ‖cdFoldDisk (ftU x)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
  -- ### 3. the polar parametrisation of the disk point
  obtain ⟨τ, hτ, t, ht_mem, σ, hσ_mem, ht, hσt⟩ := exists_colParam hz_ne hzle
  -- ### 4. the core meet
  have hcoreVal : coreLoop Q t = clampedSweep c₁ (fun t => 1 - t) P₁ (ftY x) := by
    have hpl : colPlane β Q 1 (ftU x) = Q (polarNorm (cdFoldDisk (ftU x))) := by
      rw [colPlane_eq_cdFoldDisk, Function.comp_apply]
      exact colPlane_one_of_collar hδc hβδ Q (ftU x) (le_of_lt hcol)
    rcases ht with ht | ht
    · rw [ht, coreLoop_eq_col, hτ]
      exact hpl.symm.trans hVeq
    · rw [ht, coreLoop_add_one hQseam τ, coreLoop_eq_col, hτ]
      exact hpl.symm.trans hVeq
  have hcoreMeet : (t, ftY x) ∈ coreMeet Q c₁ P₁ := ⟨ht_mem, hY2, hcoreVal⟩
  obtain ⟨hLinf, hLne, hVinj⟩ := loopChain_rank_data hcore hcoreMeet
  -- ### 5. the diameter meet
  have hdiamVal : diamLoop Q t σ = clampedSweep c₂ (fun t => 1 - t) P₂ (ftZ x) := by
    simpa [diamLoop_eq', hσt, diskPlane_eq_cdFoldDisk, Function.comp_def] using hWeq
  have hdiamMeet : (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun t => 1 - t) P₂) :=
    ⟨hσ_mem, hZ2, hdiamVal⟩
  -- ### 6. the polar dictionary at the polar parameter
  have hcoreτ : CoreImmersiveAt Q τ := by
    rcases ht with ht | ht
    · rw [← ht]; exact hLne
    · have h2 : CoreImmersiveAt Q (τ + 1) := by rw [← ht]; exact hLne
      intro h0
      refine h2 (clm_eq_zero_of_one _ ?_)
      show (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) (τ + 1)) 1 = 0
      rw [mfderiv_coreLoop_add_one hQsm hQseam τ]
      rw [h0]
      rfl
  have hpd : PolarDict β Q (ftU x) t σ :=
    polarDict_of_data hδc hβδ hQsm hQseam hcol hτ hcoreτ ht hσt
  -- ### 7. the kernel clause: the collapsed plane's differential kills exactly the radial directions
  have hCne : chartDerivC Q (polarNorm (cdFoldDisk (ftU x)))
      (Complex.I * polarNorm (cdFoldDisk (ftU x))) ≠ 0 := by
    intro h0
    have h1 : (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) τ) 1 = 0 := by
      rw [mfderiv_coreLoop_chartDeriv hQsm τ, hτ, chartDerivC_smul, h0, smul_zero]
    exact hcoreτ (clm_eq_zero_of_one _ h1)
  have hker : ∀ a : EuclideanSpace ℝ (Fin 2),
      mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a = 0 →
      ∃ μ : ℝ, mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a = μ • cdFoldDisk (ftU x) := by
    intro a ha
    have hA : (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x)) a
        = chartDerivC Q (polarNorm (cdFoldDisk (ftU x)))
            (fderiv ℝ polarNorm (cdFoldDisk (ftU x))
              (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a)) :=
      mfderiv_colPlane_one_chartDeriv hδc hβδ hQsm (ftU x) hcol a
    have hmem := fderiv_polarNorm_mem_span hz_ne
      (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c = 0 := by
      have h2 : c • chartDerivC Q (polarNorm (cdFoldDisk (ftU x)))
          (Complex.I * polarNorm (cdFoldDisk (ftU x))) = 0 := by
        have h3 := ha
        rw [hA, ← hc, chartDerivC_smul] at h3
        exact h3
      rcases smul_eq_zero.mp h2 with h4 | h4
      · exact h4
      · exact absurd h4 hCne
    have hzero : fderiv ℝ polarNorm (cdFoldDisk (ftU x))
        (mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a) = 0 := by
      rw [← hc, hc0, zero_smul]
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp
      ((fderiv_polarNorm_eq_zero_iff hz_ne _).mp hzero)
    exact ⟨μ, hμ.symm⟩
  have hbase : (1 - 2 * σ) • colCirclePt t = cdFoldDisk (ftU x) := by
    rw [Complex.real_smul]; push_cast; exact hσt
  have hcne : (1 - 2 * σ) ≠ 0 := by
    intro h0
    exact hz_ne (by rw [← hbase, h0, zero_smul])
  exact ⟨t, ht_mem, σ, hσ_mem, hcoreMeet, hdiamMeet, hpd, hker, hbase, hcne, hz_ne⟩

/-- **The `s = 1` pair datum of the transport at the design's chains** (the H3 obligation of
`NOTES_LEAD_hodd_blockT6.md` §4.1(2)), in the *interior* form the consumer uses. -/
theorem pairOneData_of_T6GenAt
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₁ c₂ : ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    {δc : ℝ} (hδc : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hdiam : ∀ q ∈ coreMeet Q c₁ P₁,
      GoodLoopChain (diamLoop Q q.1) (clampedSweep c₂ (fun t => 1 - t) P₂)) :
    ∀ x ∈ ppMeet (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 → (∀ i : Fin 2, ftU x i ∈ Set.Ioo (0 : ℝ) 1) →
      PairOneData (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x := by
  intro x hx hs hu
  have hQsm : IsSmoothChart Q := hQ
  obtain ⟨t, ht_mem, σ, hσ_mem, hcoreMeet, hdiamMeet, hpd, hker, hbase, hcne, hz_ne⟩ :=
    exists_meetData_of_ppMeet β Q P₁ P₂ c₁ c₂ hQ hQseam hδc hβδ hδcut hcore x hx hs
  have hdiamGL : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun t => 1 - t) P₂) :=
    hdiam (t, ftY x) hcoreMeet
  obtain ⟨hLinf, hLne, hVinj⟩ := loopChain_rank_data hcore hcoreMeet
  obtain ⟨hDlinf, hDlne, hWinj⟩ := loopChain_rank_data hdiamGL hdiamMeet
  -- ### 8. the non-vanishing of the diameter direction
  have hMw : chartDerivC Q (cdFoldDisk (ftU x)) (colCirclePt t) ≠ 0 := by
    intro h0
    have h1 : (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ) 1 = 0 := by
      rw [mfderiv_diamLoop_chartDeriv' hQsm t σ, hbase, chartDerivC_smul, h0, smul_zero]
    exact hDlne (clm_eq_zero_of_one _ h1)
  have hMz : chartDerivC Q (cdFoldDisk (ftU x)) (cdFoldDisk (ftU x)) ≠ 0 := by
    intro h0
    have h1 : chartDerivC Q (cdFoldDisk (ftU x)) ((1 - 2 * σ) • colCirclePt t) = 0 := by
      rw [hbase]; exact h0
    rw [chartDerivC_smul] at h1
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact hcne h2
    · exact hMw h2
  -- ### 9. the three clauses of `PairOneData`
  refine ⟨?_, hVinj, hWinj⟩
  intro a hinV hinW
  obtain ⟨c, hc⟩ := hpd.1 a
  have hAin : (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x)) a
      ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap := by
    rw [hc]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  have hA0 : (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x)) a = 0 := by
    have hmem : (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x)) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap ⊓
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep c₁ (fun r => 1 - r) P₁) (ftY x)).toLinearMap :=
      ⟨hAin, hinV⟩
    rw [hLinf, Submodule.mem_bot] at hmem
    exact hmem
  obtain ⟨μ, hμ⟩ := hker a hA0
  have hBval : (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)) a
      = μ • chartDerivC Q (cdFoldDisk (ftU x)) (cdFoldDisk (ftU x)) := by
    rw [mfderiv_diskPlane_chartDeriv hQsm (ftU x) a, hμ, chartDerivC_smul]
  have hB0 : (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)) a = 0 := by
    have hBim : (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap :=
      hpd.2 a hA0
    have hmem : (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap ⊓
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep c₂ (fun r => 1 - r) P₂) (ftZ x)).toLinearMap :=
      ⟨hBim, hinW⟩
    rw [hDlinf, Submodule.mem_bot] at hmem
    exact hmem
  have hμ0 : μ = 0 := by
    have h2 : μ • chartDerivC Q (cdFoldDisk (ftU x)) (cdFoldDisk (ftU x)) = 0 := by
      rw [← hBval]; exact hB0
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 hMz
  have hdZ0 : mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) cdFoldDisk (ftU x) a = 0 := by
    rw [hμ0, zero_smul] at hμ
    exact hμ
  have hdZ0' : (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) (ftU x)) a = 0 := by
    rw [show (fun y : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox y)) = cdFoldDisk from rfl]
    exact hdZ0
  exact inj_mfderiv_sqDisk_foldBox (ftU x) (hu 0) (hu 1) (by rw [hdZ0', map_zero])
/-! ## 4. The collar interiority at the `s = 1` end -/

/-- **The `s = 0` slice of the `9`-box**: the point with the family parameter set to `0`. -/
def ppZeroS (x : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 9) :=
  WithLp.toLp 2 (fun i : Fin 9 => if i = 0 then 0 else x i)

lemma ppZeroS_ftS (x : EuclideanSpace ℝ (Fin 9)) : ftS (ppZeroS x) = 0 := by
  simp only [ftS, ppZeroS, WithLp.ofLp_toLp]
  simp

lemma ppZeroS_ftU (x : EuclideanSpace ℝ (Fin 9)) : ftU (ppZeroS x) = ftU x := by
  ext i
  simp only [ftU, ppZeroS, WithLp.ofLp_toLp]
  rw [if_neg (by intro h; have h2 := congrArg Fin.val h; simp at h2)]

lemma ppZeroS_ftY (x : EuclideanSpace ℝ (Fin 9)) : ftY (ppZeroS x) = ftY x := by
  ext i
  simp only [ftY, ppZeroS, WithLp.ofLp_toLp]
  rw [if_neg (by intro h; have h2 := congrArg Fin.val h; simp at h2)]

lemma ppZeroS_ftZ (x : EuclideanSpace ℝ (Fin 9)) : ftZ (ppZeroS x) = ftZ x := by
  ext i
  simp only [ftZ, ppZeroS, WithLp.ofLp_toLp]
  rw [if_neg (by intro h; have h2 := congrArg Fin.val h; simp at h2)]

lemma ppZeroS_mem_unitBox (x : EuclideanSpace ℝ (Fin 9))
    (hx : x ∈ Submission.Drive.unitBox 8) : ppZeroS x ∈ Submission.Drive.unitBox 8 := by
  intro i
  simp only [ppZeroS, WithLp.ofLp_toLp]
  by_cases h : i = 0
  · rw [if_pos h]
    exact ⟨le_rfl, zero_le_one⟩
  · rw [if_neg h]
    exact hx i

lemma onSeam2_foldBox_of_coord_eq_zero {u : EuclideanSpace ℝ (Fin 2)} {i : Fin 2}
    (h : u i = 0) : onSeam2 (foldBox u) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact Or.inl (by rw [foldBox_apply_zero, h, foldFun_zero])
  · exact Or.inr (Or.inr (Or.inl (by rw [foldBox_apply_one, h, foldFun_zero])))

lemma onSeam2_foldBox_of_coord_eq_one {u : EuclideanSpace ℝ (Fin 2)} {i : Fin 2}
    (h : u i = 1) : onSeam2 (foldBox u) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · exact Or.inr (Or.inl (by rw [foldBox_apply_zero, h, foldFun_one]))
  · exact Or.inr (Or.inr (Or.inr (by rw [foldBox_apply_one, h, foldFun_one])))

/-- **The collar interiority at the `s = 1` end** (`collarInterior_one`, the second half of the
`hint` datum of `Work.Drive.hregBase_design_chains`, `NOTES_LEAD_hodd_blockT6.md` §4.1(2)).

Two ingredients, one per family of coordinates.

* The **sweep** parameters are strictly interior by the interiority clause of the two
  `GoodLoopChain`s at the core and diameter meets (`Work.Drive.exists_meetData_of_ppMeet`).
* The **plane** parameter: if the disk point `sqDisk (foldBox (ftU x))` is strictly inside the disk
  then `ftU x` is off the seam of the square.  If it lies on the unit circle then the collapsed
  plane at `s = 1` *is* the honest plane there (`Work.Drive.colPlane_of_norm_one`, for which
  `β 1 = 1` is needed), so the `s = 0` slice `ppZeroS x` is again a meet of the pair, and the
  `s = 0` argument `Work.Drive.collarInterior_zero_of_meet3Hyp` (the `Meet3Hyp` face clause at the
  triple point) gives the full interiority — a contradiction with the seam hypothesis. -/
theorem collarInterior_one
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hβ1 : β 1 = 1)
    {δc : ℝ} (hδc : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hdiam : ∀ q ∈ coreMeet Q c₁ P₁,
      GoodLoopChain (diamLoop Q q.1) (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hD : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] k))) :
    ∀ x ∈ ppMeet (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 → CollarInterior x := by
  intro x hx hs
  have hboxU : ftU x ∈ Submission.Drive.unitBox 1 := by
    intro j
    have h := hx.1 ⟨1 + j.val, by omega⟩
    simpa [ftU, WithLp.ofLp_toLp] using h
  have hρle : ‖cdFoldDisk (ftU x)‖ ≤ 1 := norm_sqDisk_le_one _ (foldBox_mem_unitBox _)
  by_cases hlt : ‖cdFoldDisk (ftU x)‖ < 1
  · -- the disk point is strictly inside the disk: the plane parameter is off the seam
    have hu : ∀ i : Fin 2, ftU x i ∈ Set.Ioo (0 : ℝ) 1 := by
      intro i
      have hseam_of_zero : ftU x i = 0 → False := by
        intro hzero
        have hseam : onSeam2 (foldBox (ftU x)) := onSeam2_foldBox_of_coord_eq_zero hzero
        have h1 : ‖sqDisk (foldBox (ftU x))‖ = 1 :=
          (norm_sqDisk_eq_one_iff (foldBox (ftU x)) (foldBox_mem_unitBox _)).mpr hseam
        rw [show ‖cdFoldDisk (ftU x)‖ = ‖sqDisk (foldBox (ftU x))‖ from rfl, h1] at hlt
        exact lt_irrefl _ hlt
      have hseam_of_one : ftU x i = 1 → False := by
        intro hone
        have hseam : onSeam2 (foldBox (ftU x)) := onSeam2_foldBox_of_coord_eq_one hone
        have h1 : ‖sqDisk (foldBox (ftU x))‖ = 1 :=
          (norm_sqDisk_eq_one_iff (foldBox (ftU x)) (foldBox_mem_unitBox _)).mpr hseam
        rw [show ‖cdFoldDisk (ftU x)‖ = ‖sqDisk (foldBox (ftU x))‖ from rfl, h1] at hlt
        exact lt_irrefl _ hlt
      exact ⟨lt_of_le_of_ne (hboxU i).1 (fun h => hseam_of_zero h.symm),
        lt_of_le_of_ne (hboxU i).2 (fun h => hseam_of_one h)⟩
    obtain ⟨t, ht_mem, σ, hσ_mem, hcoreMeet, hdiamMeet, -⟩ :=
      exists_meetData_of_ppMeet β Q P₁ P₂ c₁ c₂ hQ hQseam hδc hβδ hδcut hcore x hx hs
    exact ⟨hu, (hcore.2.1 (t, ftY x) hcoreMeet).2,
      ((hdiam (t, ftY x) hcoreMeet).2.1 (σ, ftZ x) hdiamMeet).2⟩
  · -- the disk point is on the unit circle: the `s = 0` slice of the meet is a triple point
    have hρ1 : ‖cdFoldDisk (ftU x)‖ = 1 := le_antisymm hρle (le_of_not_gt hlt)
    have hEq0 : colPlane β Q 0 (ftU x) = colPlane β Q 1 (ftU x) := by
      have h1 : colMap β 1 (cdFoldDisk (ftU x)) = cdFoldDisk (ftU x) :=
        colMap_of_norm_one hβ1 1 (cdFoldDisk (ftU x)) hρ1
      rw [colPlane_zero, colPlane_eq_cdFoldDisk, Function.comp_apply, h1]
      rfl
    have hVeq : colPlane β Q 1 (ftU x) = clampedSweep c₁ (fun t => 1 - t) P₁ (ftY x) := by
      have h := hx.2.1
      rwa [hs] at h
    have hWeq : diskPlane Q (ftU x) = clampedSweep c₂ (fun t => 1 - t) P₂ (ftZ x) := hx.2.2
    have hx' : ppZeroS x ∈ ppMeet (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) := by
      refine ⟨ppZeroS_mem_unitBox x hx.1, ?_, ?_⟩
      · show colPlane β Q (ftS (ppZeroS x)) (ftU (ppZeroS x)) = _
        rw [ppZeroS_ftS, ppZeroS_ftU, hEq0, hVeq, ppZeroS_ftY]
      · show diskPlane Q (ftU (ppZeroS x))
          = clampedSweep c₂ (fun t => 1 - t) P₂ (ftZ (ppZeroS x))
        rw [ppZeroS_ftU, hWeq, ppZeroS_ftZ]
    have hci := collarInterior_zero_of_meet3Hyp (M := CappingSpace) hD ?_ ?_ ?_ ?_ hx' (ppZeroS_ftS x)
    · simpa [CollarInterior, ppZeroS_ftU, ppZeroS_ftY, ppZeroS_ftZ] using hci
    · intro u
      show colPlane β Q 0 u = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
      rw [colPlane_zero, Matrix.cons_val_zero,
        clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
      exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
    · intro u
      show (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 0 u
        = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
          (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
      rw [Matrix.cons_val_zero,
        clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
      exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
    · intro y; rfl
    · intro z; rfl

/-! ## 5. The combined form consumed by the transport wrapper -/

/-- **The two `s = 1` data of the collar regularity at once** — the `CollarInterior` and the
`PairOneData` datum of `Work.Drive.hregBase_design_chains` at an `s = 1` meet, from the design's
`Meet3Hyp` and the box-restricted bundle.  This is the shape in which
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` (`Drive/blockT6Wrapper.lean`) consumes
them. -/
theorem collarInterior_and_pairOneData_of_T6GenAt
    (β : ℝ → ℝ) (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hβ1 : β 1 = 1)
    {δc : ℝ} (hδc : 0 ≤ δc) (hβδ : ∀ t : ℝ, δc ^ 2 ≤ t → β t = Real.sqrt t)
    (hδcut : ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
      x ∉ diskCut Q (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun t => 1 - t) P₁))
    (hdiam : ∀ q ∈ coreMeet Q c₁ P₁,
      GoodLoopChain (diamLoop Q q.1) (clampedSweep c₂ (fun t => 1 - t) P₂))
    (hD : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] k))) :
    ∀ x ∈ ppMeet (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 →
      CollarInterior x ∧
        PairOneData (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
          (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x := by
  intro x hx hs
  have hci := collarInterior_one β Q P₁ P₂ c₀ c₁ c₂ hQ hQseam hβ1 hδc hβδ hδcut hcore hdiam hD
    x hx hs
  exact ⟨hci, pairOneData_of_T6GenAt β Q P₁ P₂ c₁ c₂ hQ hQseam hδc hβδ hδcut hcore hdiam
    x hx hs hci.1⟩

end

end Work.Drive
