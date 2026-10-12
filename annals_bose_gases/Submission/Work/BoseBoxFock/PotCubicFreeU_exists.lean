import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.chAimg_bound
import Submission.Work.BoseBoxFock.PCFU.chAslot_le
import Submission.Work.BoseBoxFock.PCFU.chBimg_piece
import Submission.Work.BoseBoxFock.PCFU.chBslot_le
import Submission.Work.BoseBoxFock.PCFU.chCimg_le
import Submission.Work.BoseBoxFock.PCFU.chCslot_le
import Submission.Work.BoseBoxFock.PCFU.chDslot_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **The condensate pin determines `c`.**

The node's context carries *three* pinning hypotheses on the condensate mode
(`e 0 =ᵐ c·θ`, the `θ`-pairing `∫ conj(e 0)·θ = ℓ^{3/2}`, and `c̄c = ℓ⁻³`), and they are
redundant: the first two already force `c = (√(ℓ³))⁻¹ = ℓ^{-3/2}` (the pin `∫ conj(e 0)·θ`
evaluated at `e 0 = c·θ` reads `c̄ℓ³ = ℓ^{3/2}`).  Consequently
`pinCond v μ c = pinTheta v μ N 0 = e_0`, the *normalised* condensate of the box basis
`e_a = ℓ^{-3/2}θ_a`; this is the normalisation every dictionary computation needs (it fixes the
`c`-dependence of the mode side of `potCubic`, and hence the absolute constant in any matching
against `q3lowWord`). -/
theorem pinC_eq_inv_sqrt {v : ℝ³ → ℝ} {μ : ℝ} {c : ℂ} {e0 : ℝ³ → ℂ}
    (hpin0 : e0 =ᵐ[MeasureTheory.volume]
      fun x => c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
    (hθp : (∫ z : ℝ³, star (e0 z) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) z)
      = (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)) :
    c = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) := by
  classical
  set ℓ := ellH v μ with hℓdef
  have hℓ : 0 < ℓ := ellH_pos v μ
  -- (1) the `θ`-normalisation `∫ θ² = ℓ³`
  have hθind : (fun z : ℝ³ => Work.BoseK15.corpusBox.thetaFun ℓ z)
      = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℂ)) := by
    funext z
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
      simp [Work.BoseB4.BoxData.thetaFun_apply, hz]
  have hsq : (∫ z : ℝ³,
        Work.BoseK15.corpusBox.thetaFun ℓ z * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = ((ℓ ^ 3 : ℝ) : ℂ) := by
    have hfun : (fun z : ℝ³ =>
          Work.BoseK15.corpusBox.thetaFun ℓ z * Work.BoseK15.corpusBox.thetaFun ℓ z)
        = (fun z : ℝ³ => Work.BoseK15.corpusBox.thetaFun ℓ z) := by
      funext z
      by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
        simp [Work.BoseB4.BoxData.thetaFun_apply, hz]
    rw [hfun, hθind,
      MeasureTheory.integral_indicator (Work.BoseK15.corpusBox.boxL_measurableSet ℓ),
      MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Work.BoseK15.corpusBox.volume_boxL_toReal hℓ,
      RCLike.real_smul_eq_coe_mul, mul_one]
    rfl
  -- (2) the pinned integral, rewritten through the a.e. pin
  have hae : (fun z : ℝ³ => star (e0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      =ᵐ[MeasureTheory.volume]
        (fun z : ℝ³ => star c * (Work.BoseK15.corpusBox.thetaFun ℓ z
          * Work.BoseK15.corpusBox.thetaFun ℓ z)) := by
    refine hpin0.mono (fun z hz => ?_)
    show star (e0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z
      = star c * (Work.BoseK15.corpusBox.thetaFun ℓ z
          * Work.BoseK15.corpusBox.thetaFun ℓ z)
    rw [hz]
    by_cases hz' : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;>
      simp [Work.BoseB4.BoxData.thetaFun_apply, hz']
  have h2 : (∫ z : ℝ³, star (e0 z) * Work.BoseK15.corpusBox.thetaFun ℓ z)
      = star c * ((ℓ ^ 3 : ℝ) : ℂ) := by
    have hcst : (∫ z : ℝ³, star c * (Work.BoseK15.corpusBox.thetaFun ℓ z
          * Work.BoseK15.corpusBox.thetaFun ℓ z))
        = star c * (∫ z : ℝ³, Work.BoseK15.corpusBox.thetaFun ℓ z
          * Work.BoseK15.corpusBox.thetaFun ℓ z) :=
      MeasureTheory.integral_const_mul (star c)
        (fun z : ℝ³ => Work.BoseK15.corpusBox.thetaFun ℓ z
          * Work.BoseK15.corpusBox.thetaFun ℓ z)
    rw [MeasureTheory.integral_congr_ae hae, hcst, hsq]
  -- (3) cancel the non-zero factor `ℓ³`
  have h3 : (((ℓ ^ 3 : ℝ)) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (pow_pos hℓ 3)
  have hsqrtne : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (pow_pos hℓ 3))
  have hcast : ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹
      = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ) := by
    have hsq3 : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 :=
      Real.mul_self_sqrt (show (0 : ℝ) ≤ ℓ ^ 3 by positivity)
    have hreal : Real.sqrt (ℓ ^ 3) * (ℓ ^ 3)⁻¹ = (Real.sqrt (ℓ ^ 3))⁻¹ := by
      field_simp
      rw [sq]
      exact hsq3
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hreal]
  have hsqrt_rpow : (((ℓ ^ (3 / 2 : ℝ) : ℝ)) : ℂ) = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) := by
    have : ℓ ^ (3 / 2 : ℝ) = Real.sqrt (ℓ ^ 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ℓ 3, ← Real.rpow_mul (le_of_lt hℓ)]
      norm_num
    rw [this]
  have hstar : star c = (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ) := by
    have h := h2.symm.trans hθp
    rw [hsqrt_rpow] at h
    have hkey : star c = ((Real.sqrt (ℓ ^ 3) : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := by
      rw [← h, mul_assoc, mul_inv_cancel₀ h3, mul_one]
    rw [hkey, hcast]
  -- (4) `c` is the conjugate of `star c`, and `star` fixes the real value
  have hc : c = star (star c) := (star_star c).symm
  rw [hc, hstar]
  simp

/-- **The small-diluteness regime of the slot estimates**: for `ε₀` small enough, every admissible
`μ` has a box large enough to contain the support of `v` (`R ≤ ℓ·chiR0`) and to satisfy the
no-aliasing regime `2R ≤ ℓ` of the face-layer estimates.  Both are eventual properties of
`μ → 0⁺` (`Work.BoseBox.sideAt_large`) compatible with `Adm`'s diluteness clause `μ(a v)³ ≤ ε₀`. -/
theorem exists_regime (v : ℝ³ → ℝ) (hav : 0 < BoseGases.a v) {R : ℝ} (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 2 * R ≤ ellH v μ := by
  have hchi : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have h1 : ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * Submission.BoseGases.chiR0 :=
    Work.BoseBox.sideAt_large hav R _ hchi
  have h2 : ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      2 * R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) := by
    have h := Work.BoseBox.sideAt_large hav (2 * R) 1 one_pos
    simpa using h
  rw [eventually_nhdsWithin_iff] at h1 h2
  obtain ⟨δ₁, hδ₁, h1'⟩ := (Metric.eventually_nhds_iff).mp h1
  obtain ⟨δ₂, hδ₂, h2'⟩ := (Metric.eventually_nhds_iff).mp h2
  refine ⟨min δ₁ δ₂ * (BoseGases.a v) ^ 3 / 2, by positivity, ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have hμa : μ * (BoseGases.a v) ^ 3 ≤ min δ₁ δ₂ * (BoseGases.a v) ^ 3 / 2 := hAdm.2.1
  have hμδ : μ < min δ₁ δ₂ := by
    have hA : 0 < (BoseGases.a v) ^ 3 := pow_pos hav 3
    have hμa' : μ * (BoseGases.a v) ^ 3 ≤ (min δ₁ δ₂ / 2) * (BoseGases.a v) ^ 3 := by
      nlinarith [hμa]
    have hle : μ ≤ min δ₁ δ₂ / 2 := le_of_mul_le_mul_right hμa' hA
    have hpos2 : 0 < min δ₁ δ₂ / 2 := by linarith [hδ₁, hδ₂]
    linarith
  have hμlt1 : μ < δ₁ := lt_of_lt_of_le hμδ (min_le_left _ _)
  have hμlt2 : μ < δ₂ := lt_of_lt_of_le hμδ (min_le_right _ _)
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hside]
  have hdist1 : dist μ (0 : ℝ) < δ₁ := by rw [Real.dist_eq, sub_zero, abs_of_pos hμ]; exact hμlt1
  have hdist2 : dist μ (0 : ℝ) < δ₂ := by rw [Real.dist_eq, sub_zero, abs_of_pos hμ]; exact hμlt2
  refine ⟨?_, ?_⟩
  · rw [hℓeq]
    exact h1' hdist1 (Set.mem_Ioi.mpr hμ)
  · rw [hℓeq]
    exact h2' hdist2 (Set.mem_Ioi.mpr hμ)

/-- **The slot bound of the cubic dictionary** (condition (SLOT)).  By the PROVED dictionary
theorem `PCFU.lhs_re_eq_q3lowWord_add_slot` the target `FRK.PotCubicFreeU` is *exactly* this
statement: the dictionary evaluates the honest cubic row as `q3lowWord` plus `2ℓ⁻³·Re` of the
total slot `chSlotSum`, so all the analytic content of the node is in this single inequality. -/
noncomputable def ChSlotBound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  (∀ μ : ℝ, ⌈chNThresh v μ⌉₊ ≤ Nmin μ) ∧
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          2 * (ellH v μ) ^ (-3 : ℤ)
              * (PCFU.chSlotSum v h fc fu μ (HM μ).N
                  (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))).re
            ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ

/-- **(B8) the plumbing of the node**: `ChSlotBound` implies the target `FRK.PotCubicFreeU`,
by the PROVED dictionary theorem `PCFU.lhs_re_eq_q3lowWord_add_slot`.  All of the label
bookkeeping (`hsub` from the guarded `kmomLab` additivity, `hN` from the `N`-threshold,
`hc` from the PROVED `pinC_eq_inv_sqrt`) is discharged here. -/
theorem potCubicFreeU_of_chSlotBound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ)
    (hcsb : ChSlotBound v h fc fu R J Nmin ε₀ C) :
    Work.BoseBoxFock.FRK.PotCubicFreeU v h fc fu R J Nmin ε₀ C := by
  obtain ⟨hNthresh, hslot⟩ := hcsb
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec e hemeas hbdd hsupp horth hint hemem hpin hKp
    hLp hθp T_NH hTNH
  have hμ : 0 < μ := hAdm.1
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hside]
  have hℓpos : 0 < ellH v μ := ellH_pos v μ
  -- `chNThresh v μ ≤ N`
  have hNreal : chNThresh v μ ≤ ((HM μ).N : ℝ) := by
    have h1 : chNThresh v μ ≤ ((⌈chNThresh v μ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (⌈chNThresh v μ⌉₊ : ℕ) ≤ (HM μ).N := le_trans (hNthresh μ) (hMono μ)
    have h3 : (((⌈chNThresh v μ⌉₊ : ℕ) : ℝ)) ≤ (((HM μ).N : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  -- the small parameters
  have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d :=
    paramsAt_d_pos_of_sideAt_pos hside
  have hApos : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹ * ellH v μ :=
    mul_pos (inv_pos.mpr (mul_pos (pow_pos hd 2) hℓpos)) hℓpos
  -- the threshold in the `sideAt` spelling, normalised
  have hNnorm : 4 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
          / (2 * Real.pi)) + 2 ≤ ((HM μ).N : ℝ) := by
    have h := hNreal
    unfold chNThresh at h
    rw [hℓeq] at h
    have hr : 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi) + 2
        = 4 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi)) + 2 := by ring
    rwa [hr] at h
  have hXnn : 0 ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
        / (2 * Real.pi) := by positivity
  -- the `hN` of the guarded label arithmetic
  have hNhalf : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹ * ellH v μ
      / (2 * Real.pi) ≤ ((HM μ).N : ℝ) / 2 := by
    rw [hℓeq]
    have hr : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi)
        = 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi)) := by ring
    rw [hr]
    linarith
  have hN1 : 1 ≤ (HM μ).N := by
    have h2 : (2 : ℝ) ≤ chNThresh v μ := by
      unfold chNThresh
      have h0 : 0 ≤ 4 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2 * ellH v μ)⁻¹ * ellH v μ
          / (2 * Real.pi) := by positivity
      linarith
    have : (1 : ℝ) ≤ ((HM μ).N : ℝ) := by linarith
    exact_mod_cast this
  -- the dictionary's `hN`
  have hNd : 2 * PCFU.chKappa v μ * ellH v μ / (2 * Real.pi) ≤ ((HM μ).N : ℝ) := by
    rw [PCFU.chKappa, hℓeq]
    have hr : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi)
        = 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
            / (2 * Real.pi)) := by ring
    rw [hr]
    linarith
  -- the dictionary's `hκ`
  have hκ : 0 < PCFU.chKappa v μ := by
    rw [PCFU.chKappa]
    exact inv_pos.mpr (mul_pos (pow_pos hd 2) hside)
  -- the guarded label additivity
  have hsub : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
      fLh v fc μ (HM μ).N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        W1h v h μ fu (HM μ).N k ≠ 0 →
        kmomLab (ellH v μ) (HM μ).N (s - k)
          = kmomLab (ellH v μ) (HM μ).N s - kmomLab (ellH v μ) (HM μ).N k :=
    fun s _ hs k _ hk => kmomLab_sub_of_support v h fc fu μ (HM μ).N hside hNhalf hN1 hs hk
  -- the condensate pin
  obtain ⟨hc0, hconj, hpin0⟩ := hpin
  have hpin0' : e 0 =ᵐ[MeasureTheory.volume]
      fun x => hc0 * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x := by
    rw [hℓeq]; exact hpin0
  have hθp' : (∫ z : ℝ³, star (e 0 z) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) z)
      = (((ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hℓeq]; exact hθp
  have hc : hc0 = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) := pinC_eq_inv_sqrt hpin0' hθp'
  -- the dictionary theorem
  have hdict := PCFU.lhs_re_eq_q3lowWord_add_slot (n := n) v h hvrad fc fu HM μ hside hsub hκ hNd Φ
    hc0 e hemeas hbdd hsupp horth hemem hpin0 hKp hLp T_NH hTNH hc
  -- the slot bound
  have hsl := hslot HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec
  -- rewrite the dictionary to the `sideAt` spelling and finish
  rw [hℓeq] at hdict hsl
  simp only [PCFU.chKappa] at hdict
  rw [hdict]
  linarith [hsl]

/-- **The per-pair slot bound** — the analytic content of (SLOT).  For every admissible state and
every ordered pair of distinct slots, both alias slots are bounded (in absolute value) by
`A μ · normB`.  All of §1 of the session-16 FINDING goes into this `Prop`; the arithmetic and the
`n(n−1)` assembly are in `chSlotBound_of_perPair`. -/
noncomputable def PerPairSlotBound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ : ℝ) (A : ℝ → ℝ) : Prop :=
  (∀ μ : ℝ, ⌈chNThresh v μ⌉₊ ≤ Nmin μ) ∧
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          ∀ (i j : Fin n), i ≠ j →
            ‖PCFU.chSlotAB v h fc fu μ (HM μ).N i j
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
              ≤ A μ * Work.BoseBoxFix.normB v μ n Φ ∧
            ‖PCFU.chSlotCD v h fc fu μ (HM μ).N i j
                (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
              ≤ A μ * Work.BoseBoxFix.normB v μ n Φ

/-- Local abbreviation: the box restriction of a state at the `μ`-dependent box side. -/
private noncomputable def boxR (v : ℝ³ → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℝ :=
  boxRestrictR (ellH v μ) Φ

/-- **The assembly**: the per-pair slot bound plus the arithmetic gives (SLOT).  The two pair sums
are bounded by `#(pairSet n) = n(n−1)` times the per-pair bound (no `PermInvariant` hypothesis is
needed), and `n(n−1) ≤ n² ≤ 4μ²ℓ⁶` by `n ≤ 2μℓ³`. -/
theorem chSlotBound_of_perPair {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < BoseGases.a v)
    {fc fu : Work.BoseBoxFix.LowCut} {R J : ℝ} {Nmin : ℝ → ℕ} {ε₀ C : ℝ} {A : ℝ → ℝ}
    (hA0 : ∀ μ : ℝ, 0 ≤ A μ)
    (hpair : PerPairSlotBound v h fc fu R J Nmin ε₀ A)
    (harith : ∀ μ : ℝ, 0 < μ →
      2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A μ)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C) :
    ChSlotBound v h fc fu R J Nmin ε₀ C := by
  obtain ⟨hNth, hpair'⟩ := hpair
  refine ⟨hNth, ?_⟩
  intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec
  have hμ : 0 < μ := hAdm.1
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hside]
  have hℓpos : 0 < ellH v μ := ellH_pos v μ
  have hnormBnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => by positivity)
  have hKnn : 0 ≤ A μ * Work.BoseBoxFix.normB v μ n Φ := mul_nonneg (hA0 μ) hnormBnn
  -- the per-pair bounds, at every ordered pair of distinct slots
  have hpp : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
          ≤ A μ * Work.BoseBoxFix.normB v μ n Φ ∧
        ‖PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
          ≤ A μ * Work.BoseBoxFix.normB v μ n Φ := by
    intro p hp
    rw [Submission.BoseGases.pairSet, Finset.mem_filter] at hp
    exact hpair' HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec p.1 p.2 hp.2
  -- the norm of `ℓ^{-3}`
  have hzpow : ‖((ellH v μ : ℂ)) ^ (-3 : ℤ)‖ = (ellH v μ) ^ (-3 : ℤ) := by
    rw [norm_zpow]
    have hreal : ‖((ellH v μ : ℝ) : ℂ)‖ = ellH v μ := by
      have h1 : ‖((ellH v μ : ℝ) : ℂ)‖ ^ 2 = (ellH v μ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      nlinarith [norm_nonneg ((ellH v μ : ℝ) : ℂ), hℓpos]
    rw [hreal]
  -- the cardinality of the pair set
  have hcardR : (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
      = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [PCFU.pairSet_card_nat n]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · rw [Nat.cast_mul, Nat.cast_sub h0, Nat.cast_one]
  have hKdef : (A μ * Work.BoseBoxFix.normB v μ n Φ) = (A μ * Work.BoseBoxFix.normB v μ n Φ) := rfl
  -- the two pair sums
  have hsAB : ‖∑ p ∈ Submission.BoseGases.pairSet n,
        PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
      ≤ (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
          * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
          PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet n,
            (A μ * Work.BoseBoxFix.normB v μ n Φ) :=
          Finset.sum_le_sum (fun p hp => (hpp p hp).1)
      _ = (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
            * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsCD : ‖∑ p ∈ Submission.BoseGases.pairSet n,
        PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
      ≤ (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
          * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
          PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet n,
            (A μ * Work.BoseBoxFix.normB v μ n Φ) :=
          Finset.sum_le_sum (fun p hp => (hpp p hp).2)
      _ = (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
            * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the total slot
  have hsum : ‖PCFU.chSlotSum v h fc fu μ (HM μ).N (boxR v μ Φ)‖
      ≤ ((n : ℝ) * ((n : ℝ) - 1)) * (1 + (ellH v μ) ^ (-3 : ℤ))
          * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by
    rw [PCFU.chSlotSum]
    calc ‖(∑ p ∈ Submission.BoseGases.pairSet n,
              PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ))
            + ((ellH v μ : ℂ)) ^ (-3 : ℤ) * (∑ p ∈ Submission.BoseGases.pairSet n,
              PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ))‖
        ≤ ‖∑ p ∈ Submission.BoseGases.pairSet n,
              PCFU.chSlotAB v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ)‖
            + ‖((ellH v μ : ℂ)) ^ (-3 : ℤ) * (∑ p ∈ Submission.BoseGases.pairSet n,
              PCFU.chSlotCD v h fc fu μ (HM μ).N p.1 p.2 (boxR v μ Φ))‖ := norm_add_le _ _
      _ ≤ (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
              * (A μ * Work.BoseBoxFix.normB v μ n Φ)
            + (ellH v μ) ^ (-3 : ℤ)
              * ((((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
                * (A μ * Work.BoseBoxFix.normB v μ n Φ)) := by
          rw [norm_mul, hzpow]
          exact add_le_add hsAB (mul_le_mul_of_nonneg_left hsCD (zpow_pos hℓpos _).le)
      _ = (((Submission.BoseGases.pairSet n).card : ℕ) : ℝ)
            * (1 + (ellH v μ) ^ (-3 : ℤ)) * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by ring
      _ = ((n : ℝ) * ((n : ℝ) - 1)) * (1 + (ellH v μ) ^ (-3 : ℤ))
            * (A μ * Work.BoseBoxFix.normB v μ n Φ) := by rw [hcardR]
  -- the arithmetic
  have hcard : ((n : ℝ) * ((n : ℝ) - 1)) ≤ 4 * μ ^ 2 * (ellH v μ) ^ 6 := by
    have hnge : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h2 : (n : ℝ) ^ 2 ≤ (2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3) ^ 2 :=
      pow_le_pow_left₀ hnge hn 2
    rw [← hℓeq] at h2
    nlinarith [h1, h2]
  have hmain : 2 * (ellH v μ) ^ (-3 : ℤ)
      * ‖PCFU.chSlotSum v h fc fu μ (HM μ).N (boxR v μ Φ)‖
      ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
    have hstep : 2 * (ellH v μ) ^ (-3 : ℤ)
        * ‖PCFU.chSlotSum v h fc fu μ (HM μ).N (boxR v μ Φ)‖
        ≤ 2 * (ellH v μ) ^ (-3 : ℤ)
          * ((4 * μ ^ 2 * (ellH v μ) ^ 6) * (1 + (ellH v μ) ^ (-3 : ℤ))
            * (A μ * Work.BoseBoxFix.normB v μ n Φ)) := by
      have h1' : (0 : ℝ) ≤ 1 + (ellH v μ) ^ (-3 : ℤ) := by positivity
      have h2' : ((n : ℝ) * ((n : ℝ) - 1)) * (1 + (ellH v μ) ^ (-3 : ℤ))
          * (A μ * Work.BoseBoxFix.normB v μ n Φ)
          ≤ (4 * μ ^ 2 * (ellH v μ) ^ 6) * (1 + (ellH v μ) ^ (-3 : ℤ))
            * (A μ * Work.BoseBoxFix.normB v μ n Φ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard h1') hKnn
      exact le_trans (mul_le_mul_of_nonneg_left hsum (by positivity))
        (mul_le_mul_of_nonneg_left h2' (by positivity))
    have h5 : (2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A μ))
        * Work.BoseBoxFix.normB v μ n Φ
        ≤ ((1 / 2) * Work.BoseFixR.errKafz v R μ C) * Work.BoseBoxFix.normB v μ n Φ :=
      mul_le_mul_of_nonneg_right (harith μ hμ) hnormBnn
    exact le_trans (le_trans hstep (le_of_eq (by ring : 2 * (ellH v μ) ^ (-3 : ℤ)
        * ((4 * μ ^ 2 * (ellH v μ) ^ 6) * (1 + (ellH v μ) ^ (-3 : ℤ))
          * (A μ * Work.BoseBoxFix.normB v μ n Φ))
        = (2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A μ))
          * Work.BoseBoxFix.normB v μ n Φ))) h5
  exact le_trans (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)) hmain

/-! ## The final assembly: the two per-slot halves close the node

The whole remaining mathematics of the node sits in `PerPairSlotBound` (the per-pair alias-slot
estimate, session 16 §6).  It is split into two independent halves — the `(A)/(B)` pair
(`chSlotAB`) and the `(C)/(D)` pair (`chSlotCD`) — each of which produces

* a constant `A : ℝ → ℝ` with its *own* `N`-threshold `T : ℝ → ℝ`,
* the budget `2ℓ⁻³·(4μ²ℓ⁶(1+ℓ⁻³)·A μ) ≤ ¼·μ·a v` (so that the two budgets sum to `½·μ·a v`),

and nothing else.  This section contains the (short) assembly: it is independent of the two halves'
proofs, so the node is closed as soon as they land. -/

/-- **The per-slot half statement**: the shape of the two delegated halves `PCFU.perPairAB_le`
(`slot = chSlotAB`) and `PCFU.perPairCD_le` (`slot = chSlotCD`) — a constant `A`, an extra
`N`-threshold `T : ℝ → ℝ`, the budget `¼ μ (a v)` and the per-pair bound. -/
private noncomputable def PerPairHalf (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J ε₀ : ℝ)
    (slot : ∀ (n : ℕ) (μ : ℝ) (N : ℕ) (i j : Fin n), (Submission.BoseGases.X n → ℝ) → ℂ) :
    Prop :=
  ∃ (A T : ℝ → ℝ), (∀ μ : ℝ, 0 ≤ A μ) ∧ (∀ μ : ℝ, 0 ≤ T μ) ∧
    (∀ μ : ℝ, 0 < μ →
      2 * (ellH v μ) ^ (-3 : ℤ)
        * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A μ)
        ≤ (1 / 4) * (μ * BoseGases.a v)) ∧
    (∀ (Nmin : ℝ → ℕ), (∀ μ : ℝ, ⌈chNThresh v μ⌉₊ ≤ Nmin μ) →
      (∀ μ : ℝ, ⌈T μ⌉₊ ≤ Nmin μ) →
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ) →
      ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
            ∀ (i j : Fin n), i ≠ j →
              ‖slot n μ (HM μ).N i j
                  (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
                ≤ A μ * Work.BoseBoxFix.normB v μ n Φ)

/-- **The assembly of (SLOT) from the two per-slot halves** (session 16 §9).  With the two
budgets summing to `½ μ (a v) ≤ ½ errKafz v R μ 1` (`errKafz_ge`) and the two `N`-thresholds
folded into one `Nmin`, the halves give `PerPairSlotBound` for `A = A₁ + A₂`, hence (SLOT) with
`C = 1` by the PROVED `chSlotBound_of_perPair`. -/
private theorem chSlotBound_of_halves {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J ε₀ : ℝ} (hav : 0 < BoseGases.a v)
    (hreg : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ)
    (hAB : PerPairHalf v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chSlotAB v h fc fu μ N i j Θ))
    (hCD : PerPairHalf v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chSlotCD v h fc fu μ N i j Θ)) :
    ∃ (Nmin : ℝ → ℕ) (C : ℝ), 0 ≤ C ∧ ChSlotBound v h fc fu R J Nmin ε₀ C := by
  obtain ⟨A₁, T₁, hA₁, hT₁, hb₁, hd₁⟩ := hAB
  obtain ⟨A₂, T₂, hA₂, hT₂, hb₂, hd₂⟩ := hCD
  refine ⟨fun μ => max ⌈chNThresh v μ⌉₊ (max ⌈T₁ μ⌉₊ ⌈T₂ μ⌉₊), 1, zero_le_one, ?_⟩
  refine chSlotBound_of_perPair hav (A := fun μ => A₁ μ + A₂ μ)
    (fun μ => add_nonneg (hA₁ μ) (hA₂ μ)) ?_ ?_
  · refine ⟨fun μ => le_max_left _ _, ?_⟩
    intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have hth₁ : ∀ μ : ℝ, ⌈T₁ μ⌉₊ ≤ max ⌈chNThresh v μ⌉₊ (max ⌈T₁ μ⌉₊ ⌈T₂ μ⌉₊) :=
      fun μ => le_trans (le_max_left _ _) (le_max_right _ _)
    have hth₂ : ∀ μ : ℝ, ⌈T₂ μ⌉₊ ≤ max ⌈chNThresh v μ⌉₊ (max ⌈T₁ μ⌉₊ ⌈T₂ μ⌉₊) :=
      fun μ => le_trans (le_max_right _ _) (le_max_right _ _)
    have h1 := hd₁ (fun μ => max ⌈chNThresh v μ⌉₊ (max ⌈T₁ μ⌉₊ ⌈T₂ μ⌉₊))
      (fun μ => le_max_left _ _) hth₁ hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have h2 := hd₂ (fun μ => max ⌈chNThresh v μ⌉₊ (max ⌈T₁ μ⌉₊ ⌈T₂ μ⌉₊))
      (fun μ => le_max_left _ _) hth₂ hreg HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have hnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg (fun x => by positivity)
    exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right (by linarith [hA₂ μ]) hnn),
      le_trans h2 (mul_le_mul_of_nonneg_right (by linarith [hA₁ μ]) hnn)⟩
  · intro μ hμ
    have hsum : 2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * (A₁ μ + A₂ μ))
        = 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₁ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₂ μ) := by
      ring
    have herr : μ * BoseGases.a v ≤ Work.BoseFixR.errKafz v R μ 1 := by
      have h := Work.BoseBoxFock.errKafz_ge (v := v) (R := R) (μ := μ) (C := 1) hμ hav
        (zero_le_one : (0 : ℝ) ≤ 1)
      simpa using h
    rw [hsum]
    have h1 := hb₁ μ hμ
    have h2 := hb₂ μ hμ
    linarith

/-- **The assembly of (SLOT) from the eight channel pieces.**  Each piece `i` comes with its own
`Kᵢ > 0`, its constant `Aᵢ` and its `N`-threshold `Tᵢ`.  Taking

* `Nmin μ := ⌈chNThresh v μ⌉₊ + Σᵢ Tᵢ μ` (a sum, so every threshold is dominated),
* `A μ := Σᵢ Aᵢ μ`,
* `C := 2·(Σᵢ Kᵢ) + 1` (so that `½·errKafz v R μ C ≥ (Σᵢ Kᵢ)·μ·(a v) ≥ Σᵢ budgetᵢ`,
  by `errKafz_ge`),

the triangle inequality through `chSlotAB = (chAslot + chAimg) − (chBslot + chBimg)` and
`chSlotCD = −(chCslot + chCimg) + (chDslot + chDimg)` gives `PerPairSlotBound`, and the PROVED
`chSlotBound_of_perPair` gives (SLOT). -/
private theorem chSlotBound_of_pieces {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R J ε₀ : ℝ} (hav : 0 < BoseGases.a v)
    (hreg : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ)
    (hA : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chAslot v h fc fu μ N i j Θ))
    (hAi : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chAimg v h fc fu μ N i j Θ))
    (hB : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chBslot v h fc fu μ N i j Θ))
    (hBi : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chBimg v h fc fu μ N i j Θ))
    (hC : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chCslot v h fc fu μ N i j Θ))
    (hCi : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chCimg v h fc fu μ N i j Θ))
    (hD : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chDslot v h fc fu μ N i j Θ))
    (hDi : SlotPiece v h fc fu R J ε₀ (fun n μ N i j Θ => PCFU.chDimg v h fc fu μ N i j Θ)) :
    ∃ (Nmin : ℝ → ℕ) (C : ℝ), 0 ≤ C ∧ ChSlotBound v h fc fu R J Nmin ε₀ C := by
  obtain ⟨K₁, hK₁, A₁, T₁, hA₁0, hb₁, hd₁⟩ := hA
  obtain ⟨K₂, hK₂, A₂, T₂, hA₂0, hb₂, hd₂⟩ := hAi
  obtain ⟨K₃, hK₃, A₃, T₃, hA₃0, hb₃, hd₃⟩ := hB
  obtain ⟨K₄, hK₄, A₄, T₄, hA₄0, hb₄, hd₄⟩ := hBi
  obtain ⟨K₅, hK₅, A₅, T₅, hA₅0, hb₅, hd₅⟩ := hC
  obtain ⟨K₆, hK₆, A₆, T₆, hA₆0, hb₆, hd₆⟩ := hCi
  obtain ⟨K₇, hK₇, A₇, T₇, hA₇0, hb₇, hd₇⟩ := hD
  obtain ⟨K₈, hK₈, A₈, T₈, hA₈0, hb₈, hd₈⟩ := hDi
  refine ⟨fun μ => ⌈chNThresh v μ⌉₊
      + (T₁ μ + T₂ μ + T₃ μ + T₄ μ + T₅ μ + T₆ μ + T₇ μ + T₈ μ),
    2 * (K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈) + 1, ?_, ?_⟩
  · have h0 : 0 < K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈ := by linarith
    linarith
  refine chSlotBound_of_perPair hav
    (A := fun μ => A₁ μ + A₂ μ + A₃ μ + A₄ μ + A₅ μ + A₆ μ + A₇ μ + A₈ μ) ?_ ?_ ?_
  · intro μ
    have h1 := hA₁0 μ; have h2 := hA₂0 μ; have h3 := hA₃0 μ; have h4 := hA₄0 μ
    have h5 := hA₅0 μ; have h6 := hA₆0 μ; have h7 := hA₇0 μ; have h8 := hA₈0 μ
    linarith
  · refine ⟨fun μ => ?_, ?_⟩
    · dsimp only
      omega
    intro HM hMono μ hAdm hJ n Φ hn hnorm hlowB hspec i j hij
    have hnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := le_of_lt hnorm
    have hp1 := hd₁ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp2 := hd₂ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp3 := hd₃ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp4 := hd₄ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp5 := hd₅ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp6 := hd₆ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp7 := hd₇ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hp8 := hd₈ _ (fun μ => by omega) (fun μ => by omega) hreg HM hMono μ hAdm hJ n Φ hn
      hnorm hlowB hspec i j hij
    have hA50 := hA₅0 μ; have hA60 := hA₆0 μ; have hA70 := hA₇0 μ; have hA80 := hA₈0 μ
    constructor
    · rw [PCFU.chSlotAB]
      refine le_trans (norm_sub_le _ _) ?_
      have h12 : ‖PCFU.chAslot v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + PCFU.chAimg v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ (A₁ μ + A₂ μ) * Work.BoseBoxFix.normB v μ n Φ :=
        le_trans (norm_add_le _ _) (by nlinarith [hp1, hp2, hnn])
      have h34 : ‖PCFU.chBslot v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + PCFU.chBimg v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ (A₃ μ + A₄ μ) * Work.BoseBoxFix.normB v μ n Φ :=
        le_trans (norm_add_le _ _) (by nlinarith [hp3, hp4, hnn])
      nlinarith [h12, h34, hnn, hA50, hA60, hA70, hA80]
    · rw [PCFU.chSlotCD]
      refine le_trans (norm_add_le _ _) ?_
      have h56 : ‖-(PCFU.chCslot v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + PCFU.chCimg v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)))‖
          ≤ (A₅ μ + A₆ μ) * Work.BoseBoxFix.normB v μ n Φ :=
        le_trans (le_of_eq (norm_neg _))
          (le_trans (norm_add_le _ _) (by linarith [hp5, hp6, hnn]))
      have h78 : ‖PCFU.chDslot v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
          + PCFU.chDimg v h fc fu μ (HM μ).N i j
            (boxRestrictR (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ (A₇ μ + A₈ μ) * Work.BoseBoxFix.normB v μ n Φ :=
        le_trans (norm_add_le _ _) (by nlinarith [hp7, hp8, hnn])
      nlinarith [h56, h78, hnn, hA₁0 μ, hA₂0 μ, hA₃0 μ, hA₄0 μ]
  · intro μ hμ
    have hsum : 2 * (ellH v μ) ^ (-3 : ℤ)
          * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ))
            * (A₁ μ + A₂ μ + A₃ μ + A₄ μ + A₅ μ + A₆ μ + A₇ μ + A₈ μ))
        = 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₁ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₂ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₃ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₄ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₅ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₆ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₇ μ)
          + 2 * (ellH v μ) ^ (-3 : ℤ)
            * (4 * μ ^ 2 * (ellH v μ) ^ 6 * (1 + (ellH v μ) ^ (-3 : ℤ)) * A₈ μ) := by
      ring
    have hKsum : 0 < K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈ := by linarith
    have herr : (K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈) * (μ * BoseGases.a v)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ
            (2 * (K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈) + 1) := by
      have h := Work.BoseBoxFock.errKafz_ge (v := v) (R := R) (μ := μ)
        (C := 2 * (K₁ + K₂ + K₃ + K₄ + K₅ + K₆ + K₇ + K₈) + 1) hμ hav (by linarith)
      nlinarith [h]
    rw [hsum]
    have h1 := hb₁ μ hμ; have h2 := hb₂ μ hμ; have h3 := hb₃ μ hμ; have h4 := hb₄ μ hμ
    have h5 := hb₅ μ hμ; have h6 := hb₆ μ hμ; have h7 := hb₇ μ hμ; have h8 := hb₈ μ hμ
    linarith

/-- **The node from the eight channel pieces** — the whole remaining assembly.  The regime `ε₀` is
*taken from* `exists_regime` (this is the reason the pieces carry the regime hypothesis
`∀μ, Adm v ε₀ μ → R ≤ ℓ·chiR0 ∧ 2R ≤ ℓ` in the body of `SlotPieceBound`: at a *free* `ε₀` the alias
slots are genuinely not small — `t = μ(a v)³ = 1` is admissible for `ε₀ ≥ 1` and there the face
layer of `χ` is unavailable; see `PCFU/FINDING_perPairCD_le_FALSE.md` §2 and
`PCFU/FINDING_perPairAB_le_regime.md`). -/
private theorem potCubicFreeU_of_pieces (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ)
    (hA : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chAslot v h fc fu μ N i j Θ))
    (hAi : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chAimg v h fc fu μ N i j Θ))
    (hB : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chBslot v h fc fu μ N i j Θ))
    (hBi : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chBimg v h fc fu μ N i j Θ))
    (hC : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chCslot v h fc fu μ N i j Θ))
    (hCi : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chCimg v h fc fu μ N i j Θ))
    (hD : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chDslot v h fc fu μ N i j Θ))
    (hDi : ∀ ε₀ : ℝ, SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => PCFU.chDimg v h fc fu μ N i j Θ)) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FRK.PotCubicFreeU v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, hε₀, hreg₂⟩ := exists_regime v hav (by linarith : (0 : ℝ) < 2 * R)
  have hreg : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ := by
    intro μ hAdm
    obtain ⟨h1, h2⟩ := hreg₂ μ hAdm
    exact ⟨by linarith [h1], by linarith [h2]⟩
  obtain ⟨Nmin, C, hC0, hcsb⟩ := chSlotBound_of_pieces hav hreg
    (hA ε₀) (hAi ε₀) (hB ε₀) (hBi ε₀) (hC ε₀) (hCi ε₀) (hD ε₀) (hDi ε₀)
  exact ⟨Nmin, ε₀, C, hε₀, hC0,
    potCubicFreeU_of_chSlotBound v h hvrad hav fc fu R J Nmin ε₀ C hcsb⟩

/-- **The node from the two per-slot halves** — the coarser of the two assemblies.  Each half is
stated uniformly in `ε₀` with the regime hypothesis; the regime `ε₀` is taken from
`exists_regime`. -/
private theorem potCubicFreeU_of_halves (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ)
    (hAB : ∀ ε₀ : ℝ, (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ) →
      PerPairHalf v h fc fu R J ε₀
        (fun n μ N i j Θ => PCFU.chSlotAB v h fc fu μ N i j Θ))
    (hCD : ∀ ε₀ : ℝ, (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ) →
      PerPairHalf v h fc fu R J ε₀
        (fun n μ N i j Θ => PCFU.chSlotCD v h fc fu μ N i j Θ)) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FRK.PotCubicFreeU v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, hε₀, hreg₂⟩ := exists_regime v hav (by linarith : (0 : ℝ) < 2 * R)
  have hreg : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ ellH v μ * Submission.BoseGases.chiR0 ∧ 4 * R ≤ ellH v μ := by
    intro μ hAdm
    obtain ⟨h1, h2⟩ := hreg₂ μ hAdm
    exact ⟨by linarith [h1], by linarith [h2]⟩
  obtain ⟨Nmin, C, hC0, hcsb⟩ := chSlotBound_of_halves hav hreg (hAB ε₀ hreg) (hCD ε₀ hreg)
  exact ⟨Nmin, ε₀, C, hε₀, hC0,
    potCubicFreeU_of_chSlotBound v h hvrad hav fc fu R J Nmin ε₀ C hcsb⟩

theorem PotCubicFreeU_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      Work.BoseBoxFock.FRK.PotCubicFreeU v h fc fu R J Nmin ε₀ C := by
  exact potCubicFreeU_of_pieces v h hvrad hR hav fc fu J
    (PCFU.chAslot_le v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chAimg_bound v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chBslot_le v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chBimg_piece v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chCslot_le v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chCimg_le v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chDslot_le v h hv hv1 hvrad hR hv_supp hav fc fu J)
    (PCFU.chDimg_le v h hv hv1 hvrad hR hv_supp hav fc fu J)

end Work.BoseBoxFock
