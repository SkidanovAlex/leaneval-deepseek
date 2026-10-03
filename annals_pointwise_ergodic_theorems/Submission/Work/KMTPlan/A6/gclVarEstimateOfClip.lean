import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceLowpassG
import Submission.Port.Aesm

set_option maxHeartbeats 6000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7 Work.KMTAreas.A7Hi

/-- The `Gcl`-carrier bound of §3 from the clipped low-pass variational estimate, supplied directly
as the hypothesis `hLowClipIn` (the conclusion of
`Work.KMTAreas.A7Hi.lacunaryBumpLowpassClipBoundG`).

This is the assembly `Work.KMTPlan.A6.gclVarEstimateExplicitOfLow` with its low-pass input
`hLowpass` replaced by the *clip bound* it is used through: the only place that assembly consumes
`hLowpass` is `hLowClip` (`Work.KMTAreas.A7Hi.lacunaryBumpLowpassClipBoundG`), and every other
input of the assembly (`lacunaryBumpFareyPartBoundG`, `lacunaryBumpFareyDiffPartBoundG`,
`lacunaryBumpBadPartBoundG`) is a proved theorem of the tree. -/
theorem gclVarEstimateOfClip (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hLowClipIn : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
        (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Λ : NNReal) (hΛ : 1 < Λ)
        (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ CρcLow : ℝ, 0 < CρcLow ∧ ∃ Clow : ℝ, 0 < Clow ∧
        ∀ (Cρc : ℝ), CρcLow ≤ Cρc →
          ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
            (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (g : ℤ → ℂ),
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                  Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
                then Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) g x else 0))
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (3 * Clow * (1 + (l₂ : ℝ)) ^ 2) *
                MeasureTheory.eLpNorm g p MeasureTheory.Measure.count) :
    Work.KMTPlan.A6.GclBound P := by
  have hdeg : 2 ≤ P.natDegree := hd
  have hBadPart : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
      (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
      (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
        (f : ℤ → ℂ) (Bf : ℝ) (hBf : ∀ m : ℤ, ‖f m‖ ≤ Bf),
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
            then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop
    exact Work.KMTAreas.A7Hi.lacunaryBumpBadPartBoundG P P.natDegree hd le_rfl ρ hρ hρ1 C₀
      hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop
  intro C₀ hC₀ r hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr.le
  refine ⟨4, by norm_num, ?_⟩
  intro ρ hρ hρ1 hρC
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  intro p hp hptop
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  have hsub : ∀ u w : ℕ → ℂ,
      variationalNorm r (u - w)
        ≤ variationalNorm r u
          + variationalNorm r w := by
    intro u w
    rw [sub_eq_add_neg]
    refine (variationalNorm_add_le hr1 u (-w)).trans ?_
    have h2 : variationalNorm r (-w)
        = variationalNorm r w := by
      have h3 : (-1 : ℂ) • w = -w := by funext n; simp
      rw [← h3, variationalNorm_smul (r := r) hr1 (-1 : ℂ) w]
      simp
    rw [h2]
  have key : ∀ Λ : NNReal, ∃ c : NNReal,
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
          ≤ (c : ENNReal) * ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro Λ
    by_cases hΛ : 1 < Λ
    · obtain ⟨CρcF, hCρcF3, KF, hKFpos, hF⟩ :=
        lacunaryBumpFareyPartBoundG P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p hp hptop
      obtain ⟨CρcD, hCρcD3, KD, hKDpos, hD⟩ :=
        lacunaryBumpFareyDiffPartBoundG P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p hp hptop
      obtain ⟨Cρlow, hCρlowpos, Clow, hClowpos, hLow⟩ := hLowClipIn ρ hρ hρ1 C₀ hC₀ hρC Λ hΛ r hr p hp hptop
      obtain ⟨CbadF, hCbadFpos, hBadF⟩ :=
        hBadPart ρ hρ hρ1 C₀ hC₀ hρC CρcF hCρcF3 Λ hΛ r hr p hp hptop
      set Cρc₀ : ℝ := max CρcD Cρlow with hCρc₀def
      have h3₀ : 3 ≤ Cρc₀ := le_trans hCρcD3 (le_max_left _ _)
      have hDC₀ : CρcD ≤ Cρc₀ := le_max_left _ _
      have hLC₀ : Cρlow ≤ Cρc₀ := le_max_right _ _
      obtain ⟨Cbad0, hCbad0pos, hBad0⟩ :=
        hBadPart ρ hρ hρ1 C₀ hC₀ hρC Cρc₀ h3₀ Λ hΛ r hr p hp hptop
      set Ktot : ℝ := max 1 (max (2 * (KF : ℝ) + CbadF)
        (6 * (KD : ℝ) + 6 * (Clow : ℝ) + Cbad0)) with hKtotdef
      have hKtot1 : (1 : ℝ) ≤ Ktot := le_max_left _ _
      have hKtotF : 2 * (KF : ℝ) + CbadF ≤ Ktot :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      have hKtotD : 6 * (KD : ℝ) + 6 * (Clow : ℝ) + Cbad0 ≤ Ktot :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have hKtotpos : (0 : ℝ) < Ktot := lt_of_lt_of_le zero_lt_one hKtot1
      refine ⟨ENNReal.toNNReal (ENNReal.ofReal Ktot + 1), ?_⟩
      intro a l₁ l₂ k₁ k₂ t f hΛ' ha ha1 ht
      have hmain : MeasureTheory.eLpNorm (fun x : ℤ =>
            variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Ktot * ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        by_cases hl₂0 : l₂ = 0
        · subst hl₂0
          have hz : Gcl ρ P C₀ a l₁ 0 k₁ k₂ t f = 0 := by
            funext n
            simp only [Gcl]
            by_cases hc : core ρ C₀ l₁ 0 k₁ k₂ a n
            · rw [if_pos hc]
              exact Work.KMTAreas.A7Hi.Tex_zero_level ρ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
            · simp [hc]
          have h0 : variationalNorm r (0 : ℕ → ℂ) = 0 := by
            have h := variationalNorm_smul (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
            rw [zero_smul, enorm_zero, zero_mul] at h
            exact h
          have hz0 : (fun x : ℤ => variationalNorm r
              (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x)) = (0 : ℤ → ℝ≥0∞) := by
            funext x
            have h1 : (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x) = (0 : ℕ → ℂ) := by
              funext n; simp
            rw [h1]
            exact h0
          rw [hz, hz0, MeasureTheory.eLpNorm_zero]
          exact bot_le
        · have hl₂ : 1 ≤ l₂ := Nat.one_le_iff_ne_zero.mpr hl₂0
          rcases Nat.eq_zero_or_pos k₂ with hk₂0 | hk₂pos
          · subst hk₂0
            set D1 : ℕ → ℤ → ℂ := fun n x => Tle ρ l₂ (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) f x
              with hD1def
            set D2 : ℕ → ℤ → ℂ := fun n x => Tle ρ (l₂ - 1) (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) f x
              with hD2def
            set Alp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hAlpdef
            set Adp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hAdpdef
            set A : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f x else 0 with hAdef
            set Bp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey Cρc₀ ρ l₂ 0 a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f x else 0 with hBpdef
            set L1 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hL1def
            set L2 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ (l₂ - 1) (varphitildeN P.natDegree (Nat.floor (a n)) 0) f x else 0 with hL2def
            set M1 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hM1def
            set M2 : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
              then Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x else 0 with hM2def
            have hsplit : Gcl ρ P C₀ a l₁ l₂ k₁ 0 t f = A + Bp := by
              funext n x
              simp only [Gcl, hAdef, hBpdef, Pi.add_apply]
              by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a n
              · by_cases hF : Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hc, if_pos ⟨hc, hF⟩, if_neg (fun h => h.2 hF)]
                  simp
                · rw [if_pos hc, if_neg (fun h => hF h.2), if_pos ⟨hc, hF⟩]
                  simp
              · rw [if_neg hc, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
                simp
            by_cases hfin : ∃ Bf : ℝ, ∀ m : ℤ, ‖f m‖ ≤ Bf
            · obtain ⟨Bf, hBf⟩ := hfin
              have hXteL : ∀ n : ℕ, Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                  = Tle ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                    - Tle ρ (l₂ - 1) (varphitildeN P.natDegree (Nat.floor (a n)) 0) f := by
                intro n
                exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂
                  (adm_of_bump (contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0)
                    (hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0))
                  (adm_of_bump (contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0)
                    (hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0)) hBf
              have hXteD : ∀ n : ℕ, Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f
                  = Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f
                    - Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f := by
                intro n
                have hfun : (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ)
                    = (fun ξ : ℝ => varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ
                        * (ee (PevalR P ((Nat.floor (a n) : ℝ) * t) * ξ) - 1)) := by
                  funext ξ
                  rw [show varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      = varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ
                        * ee (PevalR P ((Nat.floor (a n) : ℝ) * t) * ξ) from rfl]
                  ring
                rw [hfun]
                refine Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂ ?_ ?_ hBf
                · exact adm_of_bump ((contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul
                      ((contDiff_ee_const_mul 2 (PevalR P ((Nat.floor (a n) : ℝ) * t))).sub contDiff_const))
                    ((hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul_right)
                · exact adm_of_bump ((contDiff_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul
                      ((contDiff_ee_const_mul 2 (PevalR P ((Nat.floor (a n) : ℝ) * t))).sub contDiff_const))
                    ((hasCompactSupport_varphitildeN P.natDegree (Nat.floor (a n)) 0).mul_right)
              have hXf : ∀ n : ℕ, Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) f
                  = Tex ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) 0) f
                    + Tex ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                      - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f :=
                fun n => Tex_varphitildeNt_split_of_bounded P P.natDegree ρ l₂ (Nat.floor (a n)) t hBf
              have hbp : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Bp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal Cbad0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hBpdef]
                exact hBad0 a ha ha1 l₁ l₂ k₁ 0 t ht f Bf hBf
              have hD1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => D1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hD1def]
                exact hD l₂ l₁ l₂ k₁ 0 le_rfl t ht a ha ha1 f
              have hD2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => D2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hD2def]
                exact hD (l₂ - 1) l₁ l₂ k₁ 0 (Nat.pred_le _) t ht a ha ha1 f
              have hL1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => L1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * Clow * (1 + (l₂ : ℝ)) ^ 2) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hL1def]
                exact hLow Cρc₀ hLC₀ a ha ha1 l₂ l₁ l₂ k₁ 0 le_rfl f
              have hL2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => L2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * Clow * (1 + (l₂ : ℝ)) ^ 2) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hL2def]
                exact hLow Cρc₀ hLC₀ a ha ha1 (l₂ - 1) l₁ l₂ k₁ 0 (Nat.pred_le _) f
              have hD1val : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ 0 a n → Farey CρcD ρ l₂ 0 a n →
                  ∀ x : ℤ, D1 n x = Tle ρ l₂ (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x := by
                intro n hc hF x
                simp only [hD1def, Tle_ite,
                  if_pos (show core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
                    from ⟨hc, hF⟩)]
              have hD2val : ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ 0 a n → Farey CρcD ρ l₂ 0 a n →
                  ∀ x : ℤ, D2 n x = Tle ρ (l₂ - 1) (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                    - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) f x := by
                intro n hc hF x
                simp only [hD2def, Tle_ite,
                  if_pos (show core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n
                    from ⟨hc, hF⟩)]
              have hM1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M1 n x)) p MeasureTheory.Measure.count
                  ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
                      variationalNorm r (fun n : ℕ => D1 n x))
                        p MeasureTheory.Measure.count := by
                by_cases hS : ∃ n, core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · obtain ⟨m, hm⟩ := Work.KMTAreas.A7Hi.core_and_farey_iff_le_G (monotone_of_lacunary hΛ ha ha1) hS
                  refine Work.KMTAreas.A7Hi.eLpNorm_variationalNorm_clip_le hr1 p m D1 M1 ?_ ?_
                  · intro n hn
                    funext x
                    simp only [hM1def, Pi.zero_apply,
                      if_neg (fun hcon => absurd ((hm n).mp hcon) (not_le.mpr hn))]
                  · intro n hn
                    have hcn := (hm n).mpr hn
                    funext x
                    simp only [hM1def, if_pos hcn]
                    exact (hD1val n hcn.1 (Work.KMTAreas.A7Hi.farey_mono_const hDC₀ hcn.2) x).symm
                · have hz : M1 = 0 := by
                    funext n x
                    simp only [hM1def, Pi.zero_apply, if_neg (fun hcon => hS ⟨n, hcon⟩)]
                  rw [hz]
                  have hz2 : (fun x : ℤ => variationalNorm r (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x))
                      = (fun x : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
                    funext x
                    congr 1
                  rw [hz2, Work.KMTAreas.A7Hi.eLpNorm_variationalNorm_zero hr1 p]
                  exact bot_le
              have hM1d : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M1 n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                refine hM1b.trans ?_
                refine (mul_le_mul_of_nonneg_left hD1b (show (0 : ℝ≥0∞) ≤ 3 by norm_num)).trans (le_of_eq ?_)
                rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← mul_assoc,
                  ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
                  show (3 : ℝ) * (KD * (1 + (l₂ : ℝ))) = 3 * KD * (1 + (l₂ : ℝ)) by ring]
              have hM2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M2 n x)) p MeasureTheory.Measure.count
                  ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
                      variationalNorm r (fun n : ℕ => D2 n x))
                        p MeasureTheory.Measure.count := by
                by_cases hS : ∃ n, core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · obtain ⟨m, hm⟩ := Work.KMTAreas.A7Hi.core_and_farey_iff_le_G (monotone_of_lacunary hΛ ha ha1) hS
                  refine Work.KMTAreas.A7Hi.eLpNorm_variationalNorm_clip_le hr1 p m D2 M2 ?_ ?_
                  · intro n hn
                    funext x
                    simp only [hM2def, Pi.zero_apply,
                      if_neg (fun hcon => absurd ((hm n).mp hcon) (not_le.mpr hn))]
                  · intro n hn
                    have hcn := (hm n).mpr hn
                    funext x
                    simp only [hM2def, if_pos hcn]
                    exact (hD2val n hcn.1 (Work.KMTAreas.A7Hi.farey_mono_const hDC₀ hcn.2) x).symm
                · have hz : M2 = 0 := by
                    funext n x
                    simp only [hM2def, Pi.zero_apply, if_neg (fun hcon => hS ⟨n, hcon⟩)]
                  rw [hz]
                  have hz2 : (fun x : ℤ => variationalNorm r (fun n : ℕ => (0 : ℕ → ℤ → ℂ) n x))
                      = (fun x : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
                    funext x
                    congr 1
                  rw [hz2, Work.KMTAreas.A7Hi.eLpNorm_variationalNorm_zero hr1 p]
                  exact bot_le
              have hAleq : Alp = L1 - L2 := by
                funext n x
                simp only [hAlpdef, hL1def, hL2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXteL n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hMpeq : Adp = M1 - M2 := by
                funext n x
                simp only [hAdpdef, hM1def, hM2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXteD n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hM2d : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => M2 n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (3 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                refine hM2b.trans ?_
                refine (mul_le_mul_of_nonneg_left hD2b (show (0 : ℝ≥0∞) ≤ 3 by norm_num)).trans (le_of_eq ?_)
                rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← mul_assoc,
                  ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
                  show (3 : ℝ) * (KD * (1 + (l₂ : ℝ))) = 3 * KD * (1 + (l₂ : ℝ)) by ring]
              have hAadd : A = Alp + Adp := by
                funext n x
                simp only [hAdef, hAlpdef, hAdpdef, Pi.add_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc₀ ρ l₂ 0 a n
                · rw [if_pos hcn, if_pos hcn, if_pos hcn]
                  exact congrFun (hXf n) x
                · rw [if_neg hcn, if_neg hcn, if_neg hcn]
                  simp
              have hAlpB : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Alp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAleq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => L1 n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => L2 n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hL1b hL2b).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hAdpB : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Adp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hMpeq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => M1 n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => M2 n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hM1d hM2d).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
                    show 3 * (KD : ℝ) * (1 + (l₂ : ℝ)) + 3 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      = 6 * (KD : ℝ) * (1 + (l₂ : ℝ)) by ring]
              have hAb : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => A n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAadd]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => Alp n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => Adp n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact variationalNorm_add_le hr1 _ _
                · refine (add_le_add hAlpB hAdpB).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hstep : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r
                      (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ 0 t f n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                        + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2)
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
                    + ENNReal.ofReal Cbad0 * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hsplit]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => A n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => Bp n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  have h1 : (fun n : ℕ => (A + Bp) n x)
                      = (fun n : ℕ => A n x) + (fun n : ℕ => Bp n x) := by
                    funext n; simp
                  rw [h1]
                  exact variationalNorm_add_le hr1 _ _
                · exact add_le_add hAb hbp
              refine hstep.trans ?_
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              rw [← ENNReal.ofReal_mul (le_of_lt hKtotpos)]
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              · have hlw1 : (1 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  Work.KMTAreas.A7Hi.assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ 0
                have hlw0 : (0 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 := le_trans zero_le_one hlw1
                have h1 : 6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                    ≤ 6 * (KD : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  mul_le_mul_of_nonneg_left (Work.KMTAreas.A7Hi.one_add_le_lossWeight hρ0 l₁ l₂ k₁ 0) (by positivity)
                have h2 : 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2
                    ≤ 6 * (Clow : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ 0 :=
                  mul_le_mul_of_nonneg_left (Work.KMTAreas.A7Hi.lossWeight_four_ge_sq hρ0 l₁ l₂ k₁ 0) (by positivity)
                have h4 : Cbad0 ≤ Cbad0 * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
                  nlinarith [hCbad0pos, hlw1]
                have h5 : 6 * (KD : ℝ) * (1 + (l₂ : ℝ))
                      + 6 * (Clow : ℝ) * (1 + (l₂ : ℝ)) ^ 2 + Cbad0
                    ≤ Ktot * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
                  nlinarith [h1, h2, h4, hKtotD, hlw0]
                exact h5
            · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
                by_contra hne
                exact hfin (eLpNorm_finite_bounded p hp1 f (lt_top_iff_ne_top.mpr hne))
              have hKne : ENNReal.ofReal Ktot ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr hKtotpos
              have hlwne : ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ 0) ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one
                  (Work.KMTAreas.A7Hi.assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ 0))
              rw [htop, ENNReal.mul_top (mul_ne_zero hKne hlwne)]
              exact le_top
          · set A : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0 with hAdef
            set Bp : ℕ → ℤ → ℂ := fun n x =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcF ρ l₂ k₂ a n
              then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f x else 0 with hBpdef
            set G1 : ℕ → ℤ → ℂ := fun n x => Tle ρ l₂ (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) f x with hG1def
            set G2 : ℕ → ℤ → ℂ := fun n x => Tle ρ (l₂ - 1) (fun ξ : ℝ =>
              if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
              then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) f x with hG2def
            have hsplit : Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f = A + Bp := by
              funext n x
              simp only [Gcl, hAdef, hBpdef, Pi.add_apply]
              by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
              · by_cases hF : Farey CρcF ρ l₂ k₂ a n
                · rw [if_pos hc, if_pos ⟨hc, hF⟩, if_neg (fun h => h.2 hF)]
                  simp
                · rw [if_pos hc, if_neg (fun h => hF h.2), if_pos ⟨hc, hF⟩]
                  simp
              · rw [if_neg hc, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]
                simp
            by_cases hfin : ∃ Bf : ℝ, ∀ m : ℤ, ‖f m‖ ≤ Bf
            · obtain ⟨Bf, hBf⟩ := hfin
              have hXte : ∀ n : ℕ, Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
                  = Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f
                    - Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) f := by
                intro n
                exact Tex_eq_Tle_sub_of_bounded ρ hρ hρ1 hl₂
                  (adm_of_bump (Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
                    (Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t))
                  (adm_of_bump (Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
                    (Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)) hBf
              have hbpF : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => Bp n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal CbadF * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hBpdef]
                exact hBadF a ha ha1 l₁ l₂ k₁ k₂ t ht f Bf hBf
              have hG1b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => G1 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KF * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hG1def]
                exact hF k₂ hk₂pos l₂ l₁ l₂ k₁ le_rfl t ht a ha ha1 f
              have hG2b : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => G2 n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (KF * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))) *
                      MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hG2def]
                exact hF k₂ hk₂pos (l₂ - 1) l₁ l₂ k₁ (Nat.pred_le _) t ht a ha ha1 f
              have hAeq : A = G1 - G2 := by
                funext n x
                simp only [hAdef, hG1def, hG2def, Pi.sub_apply]
                by_cases hcn : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n
                · rw [if_pos hcn]
                  have e1 := congrFun (Tle_ite ρ l₂
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_pos hcn] at e1
                  have e2 := congrFun (Tle_ite ρ (l₂ - 1)
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_pos hcn] at e2
                  rw [e1, e2]
                  exact congrFun (hXte n) x
                · rw [if_neg hcn]
                  have e1 := congrFun (Tle_ite ρ l₂
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_neg hcn] at e1
                  have e2 := congrFun (Tle_ite ρ (l₂ - 1)
                    (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcF ρ l₂ k₂ a n)
                    (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := f)) x
                  rw [if_neg hcn] at e2
                  rw [e1, e2]
                  simp
              have hAb : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r (fun n : ℕ => A n x))
                    p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)))
                      * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hAeq]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => G1 n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => G2 n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  exact hsub _ _
                · refine (add_le_add hG1b hG2b).trans (le_of_eq ?_)
                  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
                  congr 2
                  ring
              have hstep : MeasureTheory.eLpNorm (fun x : ℤ =>
                    variationalNorm r
                      (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t f n x)) p MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)))
                        * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count
                    + ENNReal.ofReal CbadF * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
                rw [hsplit]
                refine (eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)).trans
                  ((eLpNorm_add_le (f := (fun x : ℤ => variationalNorm r (fun n : ℕ => A n x))) (g := (fun x : ℤ => variationalNorm r (fun n : ℕ => Bp n x)))
                    hp1).trans ?_)
                · rw [enorm_eq_self, enorm_eq_self]
                  have h1 : (fun n : ℕ => (A + Bp) n x)
                      = (fun n : ℕ => A n x) + (fun n : ℕ => Bp n x) := by
                    funext n; simp
                  rw [h1]
                  exact variationalNorm_add_le hr1 _ _
                · exact add_le_add hAb hbpF
              refine hstep.trans ?_
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              rw [← ENNReal.ofReal_mul (le_of_lt hKtotpos)]
              refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
              · have hlw1 : (1 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
                  Work.KMTAreas.A7Hi.assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ k₂
                have hlw0 : (0 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := le_trans zero_le_one hlw1
                have h1 : 2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ))
                    ≤ 2 * (KF : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [Work.KMTAreas.A7Hi.lossWeight_four_ge_mul hρ0 l₁ l₂ k₁ k₂, hKFpos]
                have h4 : CbadF ≤ CbadF * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [hCbadFpos, hlw1]
                have h5 : 2 * (KF : ℝ) * (1 + (l₂ : ℝ)) * (1 + (k₂ : ℝ)) + CbadF
                    ≤ Ktot * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
                  nlinarith [h1, h4, hKtotF, hlw0]
                exact h5
            · have htop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
                by_contra hne
                exact hfin (eLpNorm_finite_bounded p hp1 f (lt_top_iff_ne_top.mpr hne))
              have hKne : ENNReal.ofReal Ktot ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr hKtotpos
              have hlwne : ENNReal.ofReal (lossWeight 4 ρ l₁ l₂ k₁ k₂) ≠ 0 :=
                ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one
                  (Work.KMTAreas.A7Hi.assembly_one_le_lossWeight (by norm_num) hρ0 l₁ l₂ k₁ k₂))
              rw [htop, ENNReal.mul_top (mul_ne_zero hKne hlwne)]
              exact le_top

      refine hmain.trans ?_
      have hcoe : ((ENNReal.toNNReal (ENNReal.ofReal Ktot + 1) : NNReal) : ENNReal)
          = ENNReal.ofReal Ktot + 1 := ENNReal.coe_toNNReal (by
            simp only [ne_eq, ENNReal.add_eq_top, not_or]
            exact ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
      rw [hcoe]
      exact mul_le_mul' (mul_le_mul' (le_add_right le_rfl) le_rfl) le_rfl
    · exact ⟨1, fun a l₁ l₂ k₁ k₂ t f hΛ' _ _ _ => absurd hΛ' hΛ⟩
  refine ⟨fun Λ => Classical.choose (key Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht
  exact Classical.choose_spec (key Λ) a l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht
end

end Work.KMTPlan.A6
