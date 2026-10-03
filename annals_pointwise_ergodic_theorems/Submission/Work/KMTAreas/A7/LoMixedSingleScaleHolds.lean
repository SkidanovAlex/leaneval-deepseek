/-
# The band-restricted single-scale §6 estimate of the mixed range (Area A7, `…Holds`)

Target: `Work.KMTAreas.A7.LoMixedSingleScaleStatement P p₁ p₂`
(`Submission/Work/KMTAreas/A7/LoMixedDefs.lean`): on the guard *and* on the band `loBandCond`
(which makes the repaired window's `m_*` equal to `1` on the support of the bumps) the
model-approximation error `mainPartTuple − loMixedTuple` is bounded per scale by
`K(Λ)·2^{C·max(2^{ρL},L)}·⌊a n⌋⁻¹·‖f‖_{p₁}‖g‖_{p₂}`, and `0` off that set.

This is Krause--Mirek--Tao, Ann. of Math. 195 (3) 2022, Proposition `mod-approx` (§6) at the
arithmetic heights `(0,l₂)`, for the **repaired** model window `loMixedU ρ P.natDegree l₂ k₁ k₂`
(the paper's free constant `C₂`, chosen large enough to separate the fibres of `diffFreqs ρ l₂`;
the pinned window `uScale ρ L` made this statement *false*: see `NOTES_LoMixedLeft.md` §6 and
`NOTES_A7_smallKernelMass_le.md` §6).

Route: on the gate, `mainPartTuple − loMixedTuple = bilinOp (coeff2 symD) f g` — the concrete
column is `bilinOp (coeff2 symC)` (`loMainPart_eq_bilinOp_symC`), the model column is
`bilinOp (coeff2 symMWin)` (`Work.KMTPlan.A6.loMixedOpEqBilinOp`), and the two kernels differ by
the §6 error symbol `coeff2 symD` (`coeff2_sub_of_meas_bdd` + the collapse
`lpSymC_sub_symMWin_eq_symD`, whose non-aliasing hypothesis at the repaired window is the theorem
`LpNonAliasAtWindow`) — so the `ℓ^p` bound follows from `BilinOpLp` and the `ℓ¹(ℤ²)` mass bound
`LpSymDMassBound` of the §6 crux (`crude-mult`(ii)).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpMixedModelSymbol
import Submission.Work.KMTAreas.A7.LpSymMwCollapse
import Submission.Work.KMTAreas.A7.LpSymDMass
import Submission.Work.KMTAreas.A7.LpNonAliasAtWindow
import Submission.Work.KMTAreas.A7.LpSymMWinBounds

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract

noncomputable section

/-! ## The degenerate cases -/

/-- With `f = 0` the concrete column vanishes. -/
theorem lpss_mainPartTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a 0 g 0 l₂ k₁ k₂ n x = 0 := by
  simp only [mainPartTuple]
  split_ifs with h
  · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
    simp [Work.KMTAreas.A7.iwConv_zero_right]
  · rfl

/-- With `g = 0` the concrete column vanishes. -/
theorem lpss_mainPartTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a f 0 0 l₂ k₁ k₂ n x = 0 := by
  simp only [mainPartTuple]
  split_ifs with h
  · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
    simp [Work.KMTAreas.A7.iwConv_zero_right]
  · rfl

/-- With `f = 0` the model column vanishes. -/
theorem lpss_loMixedTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    loMixedTuple ρ P C₀ a 0 g l₂ k₁ k₂ n x = 0 := by
  simp only [loMixedTuple]
  split_ifs with h
  · simp only [loMixedOp, smallBtwist, Tm]
    simp [Work.KMTAreas.A7.iwConv_zero_right]
  · rfl

/-- With `g = 0` the model column vanishes. -/
theorem lpss_loMixedTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    loMixedTuple ρ P C₀ a f 0 l₂ k₁ k₂ n x = 0 := by
  simp only [loMixedTuple]
  split_ifs with h
  · simp only [loMixedOp, smallBtwist, Tm]
    simp [Work.KMTAreas.A7.iwConv_zero_right]
  · rfl

/-! ## The main theorem -/

theorem LoMixedSingleScaleHolds (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    Work.KMTAreas.A7.LoMixedSingleScaleStatement P p₁ p₂ := by
  intro C₀ hC₀
  obtain ⟨ρB, hρBz, hB⟩ := LpSymDMassBound P hdeg
  refine ⟨min ρB (1 / 8), lt_min hρBz (by norm_num), ?_⟩
  intro ρ hρ hρle
  have hρB : ρ ≤ ρB := le_trans hρle (min_le_left _ _)
  have hρ8 : ρ ≤ 1 / 8 := le_trans hρle (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := by linarith
  obtain ⟨D, C, hDpos, hC1, hmass⟩ := hB ρ hρ hρB
  have hDnn : (0 : ℝ) ≤ D := le_of_lt hDpos
  let K : NNReal → NNReal := fun _ => Real.toNNReal D
  have hKval : ∀ Λ : NNReal, (K Λ : ENNReal) = ENNReal.ofReal D := fun Λ =>
    ENNReal.ofNNReal_toNNReal D
  refine ⟨C, le_trans zero_le_one hC1, K, ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hl₂ n
  set N : ℕ := Nat.floor (a n) with hNdef
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
    exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h1).ne'
  have hWpos : (0 : ℝ) < smallScaleWeight C ρ 0 l₂ k₁ k₂ := by
    rw [smallScaleWeight]; positivity
  have hWnn : (0 : ℝ) ≤ smallScaleWeight C ρ 0 l₂ k₁ k₂ := le_of_lt hWpos
  have hNinvnn : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
  have hKpos : (0 : ENNReal) < (K Λ : ENNReal) := by
    rw [hKval Λ]
    exact ENNReal.ofReal_pos.mpr hDpos
  have hWposE : (0 : ENNReal) < ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂) :=
    ENNReal.ofReal_pos.mpr hWpos
  have hFposE : (0 : ENNReal) < ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hRpos : (0 : ENNReal) < (K Λ : ENNReal)
      * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂) * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) :=
    ENNReal.mul_pos (ne_of_gt (ENNReal.mul_pos (ne_of_gt hKpos) (ne_of_gt hWposE)))
      (ne_of_gt hFposE)
  have hRne : ((K Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂)
      * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹)) ≠ 0 := ne_of_gt hRpos
  have hRfin : ((K Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂)
      * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
  -- the budget of the estimate
  set W : ENNReal := (K Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂)
    * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) with hWdef
  by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
  · -- `f = 0`
    have hfzero : f = 0 := by
      have hae : f =ᵐ[MeasureTheory.Measure.count] 0 :=
        (MeasureTheory.eLpNorm_eq_zero_iff
          (ne_of_gt (lt_trans zero_lt_one hp₁))).mp hf0
      funext x
      by_contra hx
      have hnull : MeasureTheory.Measure.count {y : ℤ | ¬ (f y = 0)} = 0 :=
        MeasureTheory.ae_iff.mp hae
      have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | ¬ (f y = 0)} := by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hx
      have hle : MeasureTheory.Measure.count ({x} : Set ℤ)
          ≤ MeasureTheory.Measure.count {y : ℤ | ¬ (f y = 0)} :=
        MeasureTheory.measure_mono hsub
      rw [hnull] at hle
      simp only [MeasureTheory.Measure.count_singleton, le_zero_iff, one_ne_zero] at hle
    subst hfzero
    have hzero : (fun x : ℤ =>
        (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
            mainPartTuple ρ P C₀ a 0 g 0 l₂ k₁ k₂ n x
              - loMixedTuple ρ P C₀ a 0 g l₂ k₁ k₂ n x
          else 0)) = 0 := by
      funext x
      by_cases hc : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
      · rw [if_pos hc]
        simp only [lpss_mainPartTuple_zero_left, lpss_loMixedTuple_zero_left, sub_zero]
        rfl
      · rw [if_neg hc]
        rfl
    rw [hzero, MeasureTheory.eLpNorm_zero]
    exact bot_le
  · by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
    · -- `g = 0`
      have hgzero : g = 0 := by
        have hae : g =ᵐ[MeasureTheory.Measure.count] 0 :=
          (MeasureTheory.eLpNorm_eq_zero_iff
            (ne_of_gt (lt_trans zero_lt_one hp₂))).mp hg0
        funext x
        by_contra hx
        have hnull : MeasureTheory.Measure.count {y : ℤ | ¬ (g y = 0)} = 0 :=
          MeasureTheory.ae_iff.mp hae
        have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | ¬ (g y = 0)} := by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]; exact hx
        have hle : MeasureTheory.Measure.count ({x} : Set ℤ)
            ≤ MeasureTheory.Measure.count {y : ℤ | ¬ (g y = 0)} :=
          MeasureTheory.measure_mono hsub
        rw [hnull] at hle
        simp only [MeasureTheory.Measure.count_singleton, le_zero_iff, one_ne_zero] at hle
      subst hgzero
      have hzero : (fun x : ℤ =>
          (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n
              ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
              mainPartTuple ρ P C₀ a f 0 0 l₂ k₁ k₂ n x
                - loMixedTuple ρ P C₀ a f 0 l₂ k₁ k₂ n x
            else 0)) = 0 := by
        funext x
        by_cases hc : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
            ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
        · rw [if_pos hc]
          simp only [lpss_mainPartTuple_zero_right, lpss_loMixedTuple_zero_right, sub_zero]
          rfl
        · rw [if_neg hc]
          rfl
      rw [hzero, MeasureTheory.eLpNorm_zero]
      exact bot_le
    · by_cases hft : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤
      · rw [hft]
        refine le_top.trans (le_of_eq ?_)
        rw [ENNReal.mul_top hRne, ENNReal.top_mul hg0]
      · by_cases hgt : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
        · rw [hgt]
          rw [ENNReal.mul_top (ne_of_gt (ENNReal.mul_pos hRne hf0))]
          exact le_top
        · -- the main case: `f, g` are `ℓ^p`, hence bounded
          have hMf : MemLp f p₁ MeasureTheory.Measure.count :=
            (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hft))
          have hMg : MemLp g p₂ MeasureTheory.Measure.count :=
            (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgt))
          have hbf : Work.KMTAreas.A5.BoundedZ f :=
            Work.KMTAreas.A5.boundedZ_of_memLp hp₁ hMf
          have hbg : Work.KMTAreas.A5.BoundedZ g :=
            Work.KMTAreas.A5.boundedZ_of_memLp hp₂ hMg
          by_cases hcond : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
              ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
          · -- the §6 model comparison on the gate
            have hguard : loGuard ρ C₀ a 0 l₂ k₁ k₂ n := hcond.1
            have hband : loBandCond ρ P l₂ k₁ k₂ N := by rw [hNdef]; exact hcond.2
            have hC2 : max k₁ k₂ + 2 * loMixedU ρ P.natDegree l₂ k₁ k₂ + 1
                ≤ (logN N).toNat := by
              rw [loBandCond] at hband
              omega
            have hC2mass' : max k₁ k₂
                  + 2 * uScale ρ (max (max 0 l₂) (max k₁ k₂)) + 1
                ≤ (logN N).toNat := by
              have hle := uScale_le_loMixedU ρ P.natDegree l₂ k₁ k₂
              omega
            have hC2mass : max k₁ k₂
                  + 2 * uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) + 1
                ≤ (logN N).toNat := by
              simpa [Work.KMTPlan.A6.lcL] using hC2mass'
            have hu1 : 1 ≤ loMixedU ρ P.natDegree l₂ k₁ k₂ :=
              le_trans (Work.KMTPlan.A6.symp_one_le_uScale ρ hρ.le _)
                (uScale_le_loMixedU ρ P.natDegree l₂ k₁ k₂)
            have hNA1 : NonAliasing (-(2 * (loMixedU ρ P.natDegree l₂ k₁ k₂ : ℤ)))
                (diffFreqs ρ 0) := loNonAliasingDiffFreqsZero ρ hu1
            have hNA2 : NonAliasing
                (-((P.natDegree : ℤ) * 2 * (loMixedU ρ P.natDegree l₂ k₁ k₂ : ℤ)))
                (diffFreqs ρ l₂) := LpNonAliasAtWindow ρ P.natDegree hρ hρ8 hdeg l₂ k₁ k₂
            -- the collapse of the two symbols
            have hcollapse : ∀ x y : ℝ,
                Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂ x y
                  - symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂ x y
                  = Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂ x y := by
              intro x y
              exact Work.KMTPlan.A6.lpSymC_sub_symMWin_eq_symD ρ hρ hρ1 P N l₂ k₁ k₂ x y
                (le_trans (by norm_num) hdeg) hN1 (by simpa using hC2) hNA1 hNA2
            -- measurability and boundedness of the two symbols
            have hmC : Measurable (fun z : ℝ × ℝ =>
                Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂ z.1 z.2) :=
              Work.KMTPlan.A6.measurable_symC ρ P N 0 l₂ k₁ k₂
            have hmM : Measurable (fun z : ℝ × ℝ =>
                symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂ z.1 z.2) :=
              lp_measurable_symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂
            obtain ⟨C₁, hC₁⟩ := Work.KMTPlan.A6.exists_bound_symC ρ hρ hρ1 P N 0 l₂ k₁ k₂
            obtain ⟨C₂, hC₂⟩ :=
              lp_exists_bound_symMWin ρ hρ hρ1 P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂
            -- the kernel identity
            have hker : ∀ u v : ℤ,
                Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂) u v
                  - Work.KMTPlan.A6.coeff2
                      (symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂) u v
                  = Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) u v := by
              intro u v
              rw [Work.KMTPlan.A6.coeff2_sub_of_meas_bdd
                (Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂)
                (symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂) u v C₁ C₂
                hmC hC₁ hmM hC₂]
              exact Work.KMTPlan.A6.coeff2_congr (fun x y => hcollapse x y) u v
            have hkerM : ∀ u v : ℤ,
                Work.KMTPlan.A6.coeff2
                    (symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂) u v
                  = Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂) u v
                    - Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) u v := by
              intro u v
              have h := hker u v
              rw [sub_eq_iff_eq_add'] at h
              rw [eq_sub_iff_add_eq]
              exact h.symm
            have hsumC : Summable (fun q : ℤ × ℤ =>
                ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symC ρ P N 0 l₂ k₁ k₂) q.1 q.2‖) :=
              (Work.KMTPlan.A6.symC_symM_summable ρ hρ hρ1 P N 0 l₂ k₁ k₂).1
            obtain ⟨hsumD, hmassD⟩ := hmass N l₂ k₁ k₂ hl₂ hN1 hC2mass
            have hsumM : Summable (fun q : ℤ × ℤ =>
                ‖Work.KMTPlan.A6.coeff2
                  (symMWin ρ P (loMixedU ρ P.natDegree l₂ k₁ k₂) N 0 l₂ k₁ k₂) q.1 q.2‖) := by
              refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
                (hsumC.add hsumD)
              rw [hkerM q.1 q.2]
              exact norm_sub_le _ _
            -- the operator identity on the gate
            have hpt : ∀ x : ℤ, mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
                = bilinOp (fun u v => Work.KMTPlan.A6.coeff2
                    (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) u v) f g x := by
              intro x
              rw [loMainPart_eq_bilinOp_symC ρ hρ hρ1 P C₀ a f g l₂ k₁ k₂ n x hbf hbg hguard,
                Work.KMTPlan.A6.loMixedOpEqBilinOp ρ hρ hρ1 P C₀ a f g l₂ k₁ k₂ n x
                  hbf hbg hguard,
                Work.KMTPlan.A6.bilinOp_sub_kernel hsumC hsumM hbf.choose_spec hbg.choose_spec x]
              congr 1
              funext u v
              exact hker u v
            have hfun : (fun x : ℤ => (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n
                  ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                  mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                    - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
                else 0))
                = fun x : ℤ => bilinOp (fun u v => Work.KMTPlan.A6.coeff2
                    (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) u v) f g x := by
              funext x
              rw [if_pos hcond]
              exact hpt x
            rw [hfun]
            have hbil := BilinOpLp (K := fun u v => Work.KMTPlan.A6.coeff2
                  (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) u v)
                (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (p₁ := p₁) (p₂ := p₂)
                (by rw [inv_inv]) (ENNReal.one_le_inv.mpr hsum) hsumD f g
            refine hbil.trans ?_
            have hWle : ENNReal.ofReal (∑' q : ℤ × ℤ,
                  ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) q.1 q.2‖)
                ≤ (K Λ : ENNReal) * ENNReal.ofReal (smallScaleWeight C ρ 0 l₂ k₁ k₂)
                  * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) := by
              have h1 : ENNReal.ofReal (∑' q : ℤ × ℤ,
                    ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) q.1 q.2‖)
                  ≤ ENNReal.ofReal (D * smallScaleWeight C ρ 0 l₂ k₁ k₂
                      * ((N : ℕ) : ℝ)⁻¹) :=
                ENNReal.ofReal_le_ofReal hmassD
              refine h1.trans (le_of_eq ?_)
              rw [hKval Λ,
                ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ D * smallScaleWeight C ρ 0 l₂ k₁ k₂),
                ENNReal.ofReal_mul hDnn]
            exact mul_le_mul' (mul_le_mul' hWle le_rfl) le_rfl
          · -- off the gate the function vanishes
            have hzero : (fun x : ℤ =>
                (if loGuard ρ C₀ a 0 l₂ k₁ k₂ n
                    ∧ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                    mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                      - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
                  else 0)) = 0 := by
              funext x
              rw [if_neg hcond]
              rfl
            rw [hzero, MeasureTheory.eLpNorm_zero]
            exact bot_le

end

end Work.KMTAreas.A7
