import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.interior_zeroSet_projection_empty
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- For every positive real `t` there is `k` with `1 / (k + 1) ≤ t`. -/
lemma exists_div_succ_le {t : ℝ} (ht : 0 < t) : ∃ k : ℕ, (1:ℝ)/(k+1) ≤ t := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / t)
  refine ⟨k, ?_⟩
  have h1 : (1:ℝ) ≤ (k : ℝ) * t := by
    have h := mul_le_mul_of_nonneg_right hk ht.le
    rwa [div_mul_cancel₀ 1 (ne_of_gt ht)] at h
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (k : ℝ) + 1)]
  nlinarith

/-- **Endpoint-tangent transversality is generic.**  Every smooth knot admits an
arbitrarily `C¹`-close smooth knot `r'` at which no chord of a collinear triple of
distinct points is tangent at one of its own endpoints. -/
theorem exists_close_endpointTangentsOffChord {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r' ∧
      (∀ a b m : ℝ, a ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        b ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        m ∈ Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period →
        LeanEval.KnotTheory.Quadrisecant.collinearityValue r' a b m = 0 →
        (r' a - r' b ≠ 0 ∧ r' a - r' m ≠ 0 ∧ r' m - r' b ≠ 0) →
        LeanEval.KnotTheory.Quadrisecant.EndpointTangentsOffChord r' a b m) ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧
        ‖LeanEval.KnotTheory.Quadrisecant.velocity r' t -
          LeanEval.KnotTheory.Quadrisecant.velocity r t‖ < ε := by
  obtain ⟨ε₀, hε₀pos, hsm⟩ := smallCorrectionKnot hr
  set Kc : ℝ := max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1 with hKc
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r₀ : ℝ := min (ε / (72 * Kc)) (ε₀ / (72 * Kc)) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (by positivity) (by positivity)
  have hr₀leε : r₀ ≤ ε / (72 * Kc) := min_le_left _ _
  have hr₀le₀ : r₀ ≤ ε₀ / (72 * Kc) := min_le_right _ _
  have hKcr₀ : Kc * r₀ ≤ ε₀ / 72 := by
    have h1 : Kc * r₀ ≤ Kc * (ε₀ / (72 * Kc)) := mul_le_mul_of_nonneg_left hr₀le₀ hKcpos.le
    have h2 : Kc * (ε₀ / (72 * Kc)) = ε₀ / 72 := by field_simp
    rw [h2] at h1; exact h1
  have hKcr₀ε : Kc * r₀ ≤ ε / 72 := by
    have h1 : Kc * r₀ ≤ Kc * (ε / (72 * Kc)) := mul_le_mul_of_nonneg_left hr₀leε hKcpos.le
    have h2 : Kc * (ε / (72 * Kc)) = ε / 72 := by field_simp
    rw [h2] at h1; exact h1
  have hbound : ∀ c ∈ Kv r₀, ‖eCoeff c‖ ≤ Kc * r₀ := by
    intro c hc
    have hcn : ‖c‖ ≤ r₀ := by
      rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc; exact hc
    have hop : ‖eCoeff c‖ ≤ ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ :=
      ContinuousLinearMap.le_opNorm (eCoeff : Coeff →L[ℝ] (Fin 9 → Space)) c
    have hkey : ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ ≤ Kc * r₀ :=
      mul_le_mul (le_max_left _ _) hcn (norm_nonneg c)
        (le_trans (norm_nonneg _) (le_max_left _ _))
    linarith
  have hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c) := by
    intro c hc
    refine isSmoothKnot_pertV hr hε₀pos hsm (lt_of_le_of_lt (hbound c hc) ?_)
    linarith [hKcr₀, hε₀pos]
  have hper : ∀ c : Coeff, Function.Periodic (pertV r c) (2 * Real.pi) :=
    fun c => pertV_periodic hr c
  set M : ℝ := speedBound r hr r₀ with hM
  let L : ℕ → ℝ := fun k => M / deltaN r hr.smooth r₀ hr₀pos.le hS hper k
  set Xsel : Fin 3 → (Cfg → ℝ) := ![cfgA, cfgB, cfgM] with hXsel
  have hXsel0 : Xsel 0 = cfgA := by simp [hXsel]
  have hXsel1 : Xsel 1 = cfgB := by simp [hXsel]
  have hXsel2 : Xsel 2 = cfgM := by simp [hXsel]
  -- the bad sets
  let bad : (ℕ × Fin 3) → Set Coeff := fun i => {c : Coeff | c ∈ Kv r₀ ∧
      ∃ w ∈ Kn i.1 (L i.1), PsiGen r (Xsel i.2) (c, w) = 0}
  have hXc_of : ∀ i : ℕ × Fin 3, Xsel i.2 = cfgA ∨ Xsel i.2 = cfgB ∨ Xsel i.2 = cfgM := by
    rintro ⟨k, s⟩
    fin_cases s
    · exact Or.inl hXsel0
    · exact Or.inr (Or.inl hXsel1)
    · exact Or.inr (Or.inr hXsel2)
  -- each bad set has empty interior
  have hbad : ∀ i : ℕ × Fin 3, interior (bad i) = ∅ := by
    rintro ⟨k, s⟩
    have hXc := hXc_of (k, s)
    have hcont : ContDiff ℝ ⊤ (Xsel s) := by
      rcases hXc with h | h | h
      · rw [h]; exact contDiff_cfgA
      · rw [h]; exact contDiff_cfgB
      · rw [h]; exact contDiff_cfgM
    have hfin : Module.finrank ℝ Cfg < Module.finrank ℝ Tgt := by
      rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; norm_num
    refine interior_zeroSet_projection_empty hfin (contDiff_PsiGen hr.smooth hcont)
      (isCompact_Kv r₀) (isCompact_Kn k (L k)) ?_
    intro p hp hp0
    have hpc : p.1 ∈ Kv r₀ := hp.1
    have hpw : p.2 ∈ Kn k (L k) := hp.2
    have hspec := Kn_spec k (L k) hpw
    have heq : eTgt (pertVelV r p.1 (Xsel s p.2) -
        cfgLam p.2 • (pertV r p.1 (cfgA p.2) - pertV r p.1 (cfgB p.2)),
        pertVelV r p.1 (Xsel s p.2) -
        cfgMu p.2 • (pertV r p.1 (cfgA p.2) - pertV r p.1 (cfgM p.2))) = 0 := by
      rw [← eT1_add_eT2]
      exact hp0
    obtain ⟨hu, hv⟩ := eTgt_eq_zero_iff.mp heq
    have hlam : cfgLam p.2 ≠ 0 := by
      intro h
      have hreg := (hS p.1 hpc).regular (Xsel s p.2)
      rw [velocity_pertV hr.smooth p.1 (Xsel s p.2)] at hreg
      rw [h, zero_smul, sub_zero] at hu
      exact hreg hu
    have hmu : cfgMu p.2 ≠ 0 := by
      intro h
      have hreg := (hS p.1 hpc).regular (Xsel s p.2)
      rw [velocity_pertV hr.smooth p.1 (Xsel s p.2)] at hreg
      rw [h, zero_smul, sub_zero] at hv
      exact hreg hv
    exact ⟨PsiDeriv (Xsel s) p.2,
      surjective_PsiDeriv hXc hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.1
        (lt_of_lt_of_le (by positivity) hspec.2.2.2.2.2.1)
        (lt_of_lt_of_le (by positivity) hspec.2.2.2.2.2.2.1)
        (lt_of_lt_of_le (by positivity) hspec.2.2.2.2.2.2.2) hlam hmu,
      hasFDerivAt_PsiGen_slice r (Xsel s) p.1 p.2⟩
  -- the bad sets are closed
  have hclosed : ∀ i : ℕ × Fin 3, IsClosed (bad i) := by
    rintro ⟨k, s⟩
    have hXc := hXc_of (k, s)
    have hcont : ContDiff ℝ ⊤ (Xsel s) := by
      rcases hXc with h | h | h
      · rw [h]; exact contDiff_cfgA
      · rw [h]; exact contDiff_cfgB
      · rw [h]; exact contDiff_cfgM
    have hcomp : IsCompact ((Kv r₀ ×ˢ Kn k (L k)) ∩ (PsiGen r (Xsel s)) ⁻¹' {0}) :=
      ((isCompact_Kv r₀).prod (isCompact_Kn k (L k))).inter_right
        (isClosed_singleton.preimage (contDiff_PsiGen hr.smooth hcont).continuous)
    have himg : Prod.fst '' ((Kv r₀ ×ˢ Kn k (L k)) ∩ (PsiGen r (Xsel s)) ⁻¹' {0}) = bad (k, s) := by
      ext c
      constructor
      · rintro ⟨p, ⟨hp, hp0⟩, rfl⟩
        exact ⟨hp.1, p.2, hp.2, hp0⟩
      · rintro ⟨hc, w, hw, h0⟩
        exact ⟨(c, w), ⟨⟨hc, hw⟩, h0⟩, rfl⟩
    rw [← himg]
    exact (hcomp.image continuous_fst).isClosed
  -- Baire
  have hUne : (interior (Kv r₀)).Nonempty := by
    have hball : Metric.ball (0 : Coeff) r₀ ⊆ interior (Kv r₀) := by
      rw [Kv]
      exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
    exact ⟨0, hball (Metric.mem_ball_self hr₀pos)⟩
  have hHopen : ∀ i : ℕ × Fin 3, IsOpen ((bad i)ᶜ) := fun i => (hclosed i).isOpen_compl
  have hHdense : ∀ i : ℕ × Fin 3, Dense ((bad i)ᶜ) := fun i =>
    interior_eq_empty_iff_dense_compl.mp (hbad i)
  have hBaire : Dense (⋂ i : ℕ × Fin 3, (bad i)ᶜ) := dense_iInter_of_isOpen hHopen hHdense
  obtain ⟨c, hcmem, hcU⟩ := hBaire.exists_mem_open isOpen_interior hUne
  have hcKv : c ∈ Kv r₀ := interior_subset hcU
  refine ⟨pertV r c, hS c hcKv, ?_, ?_⟩
  · intro a b m ha hb hm hcol hdist
    have hZ1 : pertV r c a - pertV r c b ≠ 0 := hdist.1
    have hZ2 : pertV r c a - pertV r c m ≠ 0 := hdist.2.1
    have hZ3 : pertV r c b - pertV r c m ≠ 0 := by
      intro h
      exact hdist.2.2 (by rw [sub_eq_zero] at h ⊢; exact h.symm)
    obtain ⟨ρ, hρ⟩ := (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
      (pertV r c a - pertV r c b) (pertV r c a - pertV r c m)).mp hcol |>.resolve_left hZ1
    have hρ0 : ρ ≠ 0 := by
      intro h; rw [h, zero_smul] at hρ; exact hZ2 hρ
    have haIcc : a ∈ Set.Icc 0 (2 * Real.pi) := ⟨ha.1, by simpa [period] using ha.2.le⟩
    have hbIcc : b ∈ Set.Icc 0 (2 * Real.pi) := ⟨hb.1, by simpa [period] using hb.2.le⟩
    have hmIcc : m ∈ Set.Icc 0 (2 * Real.pi) := ⟨hm.1, by simpa [period] using hm.2.le⟩
    have ha2 : a < 2 * Real.pi := by simpa [period] using ha.2
    have hb2 : b < 2 * Real.pi := by simpa [period] using hb.2
    have hm2 : m < 2 * Real.pi := by simpa [period] using hm.2
    have hab : a ≠ b := fun h => hZ1 (by rw [h, sub_self])
    have ham : a ≠ m := fun h => hZ2 (by rw [h, sub_self])
    have hbm : b ≠ m := fun h => hZ3 (by rw [h, sub_self])
    have hcsep1 : 0 < csep a b := by
      have hlt : |a - b| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨by linarith [haIcc.1, hb2], by linarith [ha2, hbIcc.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hab)) (sub_pos.mpr hlt)
    have hcsep2 : 0 < csep a m := by
      have hlt : |a - m| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨by linarith [haIcc.1, hm2], by linarith [ha2, hmIcc.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr ham)) (sub_pos.mpr hlt)
    have hcsep3 : 0 < csep b m := by
      have hlt : |b - m| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨by linarith [hbIcc.1, hm2], by linarith [hb2, hmIcc.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hbm)) (sub_pos.mpr hlt)
    obtain ⟨k, hk⟩ := exists_div_succ_le (lt_min (lt_min hcsep1 hcsep2) hcsep3)
    have hk1 : (1:ℝ)/(k+1) ≤ csep a b :=
      hk.trans (le_trans (min_le_left _ _) (min_le_left _ _))
    have hk2 : (1:ℝ)/(k+1) ≤ csep a m :=
      hk.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have hk3 : (1:ℝ)/(k+1) ≤ csep b m := hk.trans (min_le_right _ _)
    have hq : (a, (b, m)) ∈ tripleSet k := ⟨haIcc, hbIcc, hmIcc, hk1, hk2, hk3⟩
    have hdelpos : 0 < deltaN r hr.smooth r₀ hr₀pos.le hS hper k :=
      deltaN_pos hr.smooth hr₀pos.le (hS := hS) (hper := hper) k
    have hdel1 : deltaN r hr.smooth r₀ hr₀pos.le hS hper k ≤
        ‖pertV r c a - pertV r c b‖ :=
      (deltaN_le hr.smooth hr₀pos.le (hS := hS) (hper := hper) k hcKv a b m hq).1
    have hdel2 : deltaN r hr.smooth r₀ hr₀pos.le hS hper k ≤
        ‖pertV r c a - pertV r c m‖ :=
      (deltaN_le hr.smooth hr₀pos.le (hS := hS) (hper := hper) k hcKv a b m hq).2
    have slot : ∀ (X : Cfg → ℝ) (x : ℝ) (hXc : X = cfgA ∨ X = cfgB ∨ X = cfgM),
        ((X = cfgA ∧ x = a) ∨ (X = cfgB ∧ x = b) ∨ (X = cfgM ∧ x = m)) →
        cross3 (pertV r c a - pertV r c b) (velocity (pertV r c) x) ≠ 0 := by
      intro X x hXc hx hcross
      have hxIcc : x ∈ Set.Icc 0 (2 * Real.pi) := by
        rcases hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact haIcc
        · exact hbIcc
        · exact hmIcc
      obtain ⟨lam, hlam⟩ := (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
        (pertV r c a - pertV r c b) (velocity (pertV r c) x)).mp hcross |>.resolve_left hZ1
      have hsp : ‖velocity (pertV r c) x‖ ≤ M := by
        rw [hM, velocity_pertV hr.smooth c x]
        exact speedBound_spec hr r₀ c hcKv x hxIcc
      have hZ1norm : 0 < ‖pertV r c a - pertV r c b‖ := norm_pos_iff.mpr hZ1
      have hlambound : |lam| ≤ L k := by
        have heqv : ‖velocity (pertV r c) x‖ = |lam| * ‖pertV r c a - pertV r c b‖ := by
          rw [hlam, norm_smul, Real.norm_eq_abs]
        have h1 : |lam| * deltaN r hr.smooth r₀ hr₀pos.le hS hper k ≤ M :=
          calc |lam| * deltaN r hr.smooth r₀ hr₀pos.le hS hper k
              ≤ |lam| * ‖pertV r c a - pertV r c b‖ :=
                mul_le_mul_of_nonneg_left hdel1 (abs_nonneg lam)
            _ = ‖velocity (pertV r c) x‖ := heqv.symm
            _ ≤ M := hsp
        rw [show L k = M / deltaN r hr.smooth r₀ hr₀pos.le hS hper k from rfl,
          le_div_iff₀ hdelpos]
        exact h1
      have hcross2 : cross3 (pertV r c a - pertV r c m) (velocity (pertV r c) x) = 0 := by
        rw [hρ, cross3_smul_left, hcross, smul_zero]
      obtain ⟨mu, hmu⟩ := (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
        (pertV r c a - pertV r c m) (velocity (pertV r c) x)).mp hcross2 |>.resolve_left hZ2
      have hZ2norm : 0 < ‖pertV r c a - pertV r c m‖ := norm_pos_iff.mpr hZ2
      have hmubound : |mu| ≤ L k := by
        have heqv : ‖velocity (pertV r c) x‖ = |mu| * ‖pertV r c a - pertV r c m‖ := by
          rw [hmu, norm_smul, Real.norm_eq_abs]
        have h1 : |mu| * deltaN r hr.smooth r₀ hr₀pos.le hS hper k ≤ M :=
          calc |mu| * deltaN r hr.smooth r₀ hr₀pos.le hS hper k
              ≤ |mu| * ‖pertV r c a - pertV r c m‖ :=
                mul_le_mul_of_nonneg_left hdel2 (abs_nonneg mu)
            _ = ‖velocity (pertV r c) x‖ := heqv.symm
            _ ≤ M := hsp
        rw [show L k = M / deltaN r hr.smooth r₀ hr₀pos.le hS hper k from rfl,
          le_div_iff₀ hdelpos]
        exact h1
      have hwKn : mkCfg lam mu a b m ∈ Kn k (L k) :=
        mem_Kn_mkCfg hlambound hmubound haIcc hbIcc hmIcc hk1 hk2 hk3
      have hXw : X (mkCfg lam mu a b m) = x := by
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, cfgA_mkCfg]
        · rw [h1, h2, cfgB_mkCfg]
        · rw [h1, h2, cfgM_mkCfg]
      have hz : PsiGen r X (c, mkCfg lam mu a b m) = 0 := by
        simp only [PsiGen]
        rw [eT1_add_eT2, eTgt_eq_zero_iff]
        refine ⟨?_, ?_⟩
        · rw [cfgLam_mkCfg, cfgA_mkCfg, cfgB_mkCfg, hXw, ← velocity_pertV hr.smooth c x,
            hlam, sub_self]
        · rw [cfgMu_mkCfg, cfgA_mkCfg, cfgM_mkCfg, hXw, ← velocity_pertV hr.smooth c x,
            hmu, sub_self]
      have hss : ∃ s : Fin 3, Xsel s = X := by
        rcases hXc with h | h | h
        · exact ⟨0, by rw [h, hXsel0]⟩
        · exact ⟨1, by rw [h, hXsel1]⟩
        · exact ⟨2, by rw [h, hXsel2]⟩
      obtain ⟨s, hs⟩ := hss
      have hH := Set.mem_iInter.mp hcmem (k, s)
      change c ∉ ({c' : Coeff | c' ∈ Kv r₀ ∧ ∃ w ∈ Kn k (L k),
        PsiGen r (Xsel s) (c', w) = 0}) at hH
      rw [hs] at hH
      exact hH ⟨hcKv, _, hwKn, hz⟩
    have keyA : cross3 (pertV r c a - pertV r c b) (velocity (pertV r c) a) ≠ 0 :=
      slot cfgA a (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩)
    have keyB : cross3 (pertV r c a - pertV r c b) (velocity (pertV r c) b) ≠ 0 :=
      slot cfgB b (Or.inr (Or.inl rfl)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have keyM : cross3 (pertV r c a - pertV r c b) (velocity (pertV r c) m) ≠ 0 :=
      slot cfgM m (Or.inr (Or.inr rfl)) (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have hZ3eq : pertV r c b - pertV r c m = (ρ - 1) • (pertV r c a - pertV r c b) := by
      have h1 : pertV r c b - pertV r c m
          = -(pertV r c a - pertV r c b) + (pertV r c a - pertV r c m) := by abel
      rw [h1, hρ, sub_smul, one_smul]
      abel
    have hρ1 : ρ - 1 ≠ 0 := by
      intro h
      exact hZ3 (by rw [hZ3eq, h, zero_smul])
    refine ⟨keyA, keyB, ?_, ?_, ?_, ?_⟩
    · rw [hρ, cross3_smul_left]; exact smul_ne_zero hρ0 keyA
    · rw [hρ, cross3_smul_left]; exact smul_ne_zero hρ0 keyM
    · rw [hZ3eq, cross3_smul_left]; exact smul_ne_zero hρ1 keyB
    · rw [hZ3eq, cross3_smul_left]; exact smul_ne_zero hρ1 keyM
  · intro t
    have hb1 : ‖eCoeff c‖ ≤ Kc * r₀ := hbound c hcKv
    constructor
    · have hdiff : ‖pertV r c t - r t‖ = ‖perturbCorr (eCoeff c) t‖ := by
        simp [pertV, perturb]
      rw [hdiff]
      have hle := norm_perturbCorr_le (eCoeff c) t
      have hnn := norm_nonneg (perturbCorr (eCoeff c) t)
      nlinarith [hKcr₀ε, hε, hle, hb1, hnn]
    · have hdiff : velocity (pertV r c) t - velocity r t = perturbVelCorr (eCoeff c) t := by
        rw [velocity_pertV hr.smooth c t, pertVelV, perturbVel]; abel
      rw [hdiff]
      have hle := norm_perturbVelCorr_le (eCoeff c) t
      have hnn := norm_nonneg (perturbVelCorr (eCoeff c) t)
      nlinarith [hKcr₀ε, hε, hle, hb1, hnn]

end

end Work.Drive
