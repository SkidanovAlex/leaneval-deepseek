import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.FRK.lowBandSqrt_exists
import Submission.Work.BoseBoxFock.FRK.zeroCellArith
import Submission.Work.BoseBoxFock.FRK.zeroCellRow_le
import Submission.Work.BoseBoxFock.FRK.zeroCellSX_le
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.rowZeroSmall
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.potCubicZeroCell_exists` — the zero cell (`k = 0`) of the cubic row

The design `sources/boseDCF/bose_deadrow_cubicfree.md` §B3 and its review `_REVIEW.md` B2/B3:
the "all `k`" dictionary `PotCubicFreeU` differs from FS's cubic term by the single lattice term
`k = 0`, `T₀ = ℓ⁻³Ŵ₁(0)Σ_s f_L(s) a₀†ã_s†a(q₀)a(q_s)`, which FS's `excited = univ.erase 0`
drops.  This file proves `potCubicZeroCell_exists`: for every `γ > 0` the row
`potCubic(excited) − potCubic(univ) = −(k = 0 term)` is dominated by the γ-fraction of the
low-band gap, `γ ℓ⁻² n₊`, uniformly in the state and the honest mode family.

The chain (all in the honest box vocabulary of `BoseBoxFock/FRK/cubicZeroDefs.lean`):

* `zeroCellRow_le` — the row split `potCubic(univ) = potCubic(excited) + potCubic({0})` plus the
  atom expansion, the per-pair bound and the weighted Cauchy–Schwarz:
  `row ≤ 2 ℓ⁻³ √(Σ_s |f_L s||Ŵ₁(0)|‖a_{f s}a_{f 0}Θ‖²) √(Σ_s |f_L s||Ŵ₁(0)|‖a_{g s}a_{e vec 0}Θ‖²)`;
* `zeroCellSX_le` — `Σ_s‖a_{f s}a_{f 0}Θ‖² ≤ C_B² ⟨Θ, Q²Θ⟩` with `Q = dΓ(boxT0)` the
  excited-particle number and `C_B = 48/π` the χ-frame constant (`honestChiFrame`);
* `lowBandCondSumAux` — `Σ_s‖a_{g s}a_{e vec 0}Θ‖² ≤ n ⟨Θ,QΘ⟩` (the θ-frame is Bessel with
  constant `1`, `gramOrthFrame`);
* `re_boxSlotSum_boxT0_le_cnPlusC` + `cnPlusC_boxRestrictC_eq_cnPlus` — `⟨Θ,QΘ⟩ ≤ n₊`;
* `windowCGAux` — `⟨Θ,Q²Θ⟩ ≤ 𝓜 n₊` (the spectral window `SpectralNPlusLe`);
* `zeroCellArith` — `a v · ℓ⁻¹ √(2μℓ³𝓜) ≤ √2 (μ(a v)³)^{1/9}`;
* and the final comparison `2 C₁ (48/π) a v ℓ⁻¹ √(n𝓜) ≤ γ`, which holds because
  `√(n𝓜) ≤ √(2μℓ³𝓜)` (`n ≤ 2μℓ³`) and `t ↦ t^{1/9}` is small at the diluteness `t ≤ ε₀`.

`C := 0` is enough: the `½ errKafz` allowance is never used.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.FRK

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The main theorem (assembly). -/
theorem potCubicZeroCell_exists (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (Nmin : ℝ → ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ Work.BoseBoxFock.FRK.PotCubicZeroCell v h fc fu R J Nmin ε₀ C γ := by
  obtain ⟨ε₁, C_W, hε₁, hC_W, hEnv⟩ := envFacts_uniform v h hv hv1 hvrad hR hv_supp hav fc fu
  set C₁ : ℝ := max C_W 1 with hC1def
  have hC1nn : 0 ≤ C₁ := le_trans zero_le_one (le_max_right _ _)
  have hC1pos : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCWC1 : C_W ≤ C₁ := le_max_left _ _
  set K : ℝ := 2 * C₁ * (48 / Real.pi) * Real.sqrt 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKnn : 0 ≤ K := hKpos.le
  refine ⟨min ε₁ (min 1 ((γ / (2 * K)) ^ (9 : ℕ))), 0, lt_min hε₁ (lt_min one_pos ?_),
    le_refl 0, ?_⟩
  · exact pow_pos (div_pos hγ (mul_pos two_pos hKpos)) 9
  intro HM hNmin μ
  set ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v) with hℓdef
  set E : Work.BoseB7.Q3Env (Lab (HM μ).N) := (HonestBoxFam v h fc fu HM μ).E with hEdef
  intro hAdm hJ n Φ hn hnorm hlow hspec e hmeas hbdd hsupp horth hint hmem hpin hqvec htheta
    h0pin T_NH hTNH
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < BoseGases.a v := hav
  have hAnn1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have htγ : μ * (BoseGases.a v) ^ 3 ≤ (γ / (2 * K)) ^ (9 : ℕ) :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hEllpos, hEllEq, hMuEq, hμℓ3, hellinv, hMle, hW1le, _hW1ωle, _hW1ω0nn, _hW1ω0le,
    _hW1ω0eq, _hcHCF, _hW1par, _hW1ωpar, _htaupar, _hchipar⟩ :=
    hEnv HM μ hAnn1
  rw [← hℓdef] at hEllEq
  have hℓpos : 0 < ℓ := by rw [← hEllEq]; exact hEllpos
  have hℓnn : 0 ≤ ℓ := hℓpos.le
  have hEℓpos : 0 < E.ell := by rw [hEllEq]; exact hℓpos
  have hW10 : |E.W1 0| ≤ C₁ * BoseGases.a v :=
    le_trans (hW1le 0) (mul_le_mul_of_nonneg_right hCWC1 ha.le)
  have hW10nn : 0 ≤ |E.W1 0| := abs_nonneg _
  have hC1a : 0 ≤ C₁ * BoseGases.a v := mul_nonneg hC1nn ha.le
  have hcnPlusnn : 0 ≤ Submission.BoseGases.cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ) :=
    cnPlus_nonneg' ℓ _
  have herr : Work.BoseFixR.errKafz v R μ 0 = 0 := by
    simp only [Work.BoseFixR.errKafz, zero_mul]
  rcases le_or_gt n 1 with hn1 | hn2
  · -- ## degenerate case `n ≤ 1`
    have hΘm : Measurable (boxRestrictC ℓ (Φ : Submission.BoseGases.X n → ℝ)) :=
      boxRestrictC_measurable ℓ Φ.contDiff.continuous
    have hΘb : ∃ C : ℝ, ∀ x, ‖boxRestrictC ℓ (Φ : Submission.BoseGases.X n → ℝ) x‖ ≤ C :=
      (boxRestrictC_norm_bound hℓpos Φ.contDiff.continuous).imp (fun C hC => hC.2)
    have hz1 := Work.BoseBoxFock.PotCubicLowBandAux.potCubic_eq_zero_of_le_one
      (m := (HM μ).m) (n := n) (Mode := Lab (HM μ).N) (ℓ := ℓ) (e := e)
      hmeas hbdd hsupp horth (HM μ).f (HM μ).g (Work.BoseB7.excited (Lab (HM μ).N))
      E (boxRestrictC ℓ (Φ : Submission.BoseGases.X n → ℝ)) hΘm hΘb hn1
    have hz2 := Work.BoseBoxFock.PotCubicLowBandAux.potCubic_eq_zero_of_le_one
      (m := (HM μ).m) (n := n) (Mode := Lab (HM μ).N) (ℓ := ℓ) (e := e)
      hmeas hbdd hsupp horth (HM μ).f (HM μ).g (Finset.univ : Finset (Lab (HM μ).N))
      E (boxRestrictC ℓ (Φ : Submission.BoseGases.X n → ℝ)) hΘm hΘb hn1
    have hL : (∫ x : Submission.BoseGases.X n, star (boxRestrictC ℓ Φ.toFun x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Work.BoseB7.excited (Lab (HM μ).N)) E (boxRestrictC ℓ Φ.toFun) x).re
        - (∫ x : Submission.BoseGases.X n, star (boxRestrictC ℓ Φ.toFun x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Finset.univ : Finset (Lab (HM μ).N)) E (boxRestrictC ℓ Φ.toFun) x).re = 0 := by
      rw [hz1, hz2]
      simp only [sub_self]
    have hR : (0:ℝ) ≤ γ * (ℓ ^ (-2 : ℤ) *
          Submission.BoseGases.cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ))
        + 1 / 2 * Work.BoseFixR.errKafz v R μ 0 * Work.BoseBoxFix.normB v μ n Φ := by
      simp only [herr, mul_zero, zero_mul, add_zero]
      exact mul_nonneg hγ.le (mul_nonneg (zpow_nonneg hℓnn _) hcnPlusnn)
    exact le_trans (le_of_eq hL) hR
  · -- ## main case `2 ≤ n`
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 2 := ⟨n - 2, by omega⟩
    have hnR : ((d : ℝ) + 2) ≤ 2 * μ * ℓ ^ 3 := by
      have h2 := hn; push_cast at h2; exact h2
    set Θ : Work.BoseDict.Xn (d + 2) → ℂ :=
      boxRestrictC ℓ (Φ : Submission.BoseGases.X (d + 2) → ℝ) with hΘdef
    have hΦc : Continuous (Φ : Submission.BoseGases.X (d + 2) → ℝ) := Φ.contDiff.continuous
    have hΘm : Measurable Θ := boxRestrictC_measurable ℓ hΦc
    have hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C :=
      (boxRestrictC_norm_bound hℓpos hΦc).imp (fun C hC => hC.2)
    have hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox (d + 2) ℓ :=
      boxRestrictC_support_subset ℓ _
    have hΘsuppPow : Function.support Θ ⊆ Work.MB.boxPow (d + 2) ℓ := by
      rw [Work.BoseBoxFock.FRK.boxPow_eq_abox (d + 2) hℓpos]; exact hΘsupp
    have hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 2))) (x : Submission.BoseGases.X (d + 2)),
        Θ (x ∘ σ) = Θ x := boxRestrictC_symm ℓ _ Φ.symm
    set 𝓜 : ℝ := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ with h𝓜def
    have h𝓜1 : 1 ≤ 𝓜 := by
      rw [h𝓜def]; exact Work.BoseBoxFock.PotCubicLowBandAux.bigMAdmGeOne hav hμ ht1
    have h𝓜nn : 0 ≤ 𝓜 := le_trans zero_le_one h𝓜1
    set NP : ℝ := Submission.BoseGases.cnPlus ℓ (Φ : Submission.BoseGases.X (d + 2) → ℝ)
      with hNPdef
    have hNPnn : 0 ≤ NP := hcnPlusnn
    set SX : ℝ := ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |E.fL s| * |E.W1 0| *
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
            (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
            (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re with hSXdef
    set SY : ℝ := ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |E.fL s| * |E.W1 0| *
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re with hSYdef
    set V : ℝ := (Work.BoseDict.cIPn (d + 2) Θ
      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m) Θ)).re with hVdef
    set V2 : ℝ := (Work.BoseDict.cIPn (d + 2) Θ
      (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m)
        (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.boxT0 (HM μ).m) Θ))).re with hV2def
    have hrow : (∫ x : Submission.BoseGases.X (d + 2), star (Θ x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Work.BoseB7.excited (Lab (HM μ).N)) E Θ x).re
        - (∫ x : Submission.BoseGases.X (d + 2), star (Θ x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Finset.univ : Finset (Lab (HM μ).N)) E Θ x).re
        ≤ 2 * (ℓ ^ (-(3 : ℝ))) * Real.sqrt SX * Real.sqrt SY := by
      have hh := zeroCellRow_le (m := (HM μ).m) (d := d) (Mode := Lab (HM μ).N)
        (ℓ := ℓ) (e := e) hℓpos hmeas hbdd hsupp horth hmem (HM μ).f (HM μ).g E hEℓpos
        hΘm hΘb hΘsuppPow hΘsym
      rw [hEllEq] at hh
      rw [hSXdef, hSYdef]
      exact hh
    have hSXraw := zeroCellSX_le (m := (HM μ).m) (d := d) (Mode := Lab (HM μ).N)
      (ℓ := ℓ) (e := e) hmeas hbdd hsupp horth hmem (HM μ).f (48 / Real.pi) (by positivity)
      (honestChiFrame h fc fu HM μ) (HM μ).hf0 hΘm hΘb hΘsuppPow hΘsym
    have hV2le : V2 ≤ 𝓜 * NP := by
      have hw := Work.BoseBoxFock.PotCubicLowBandAux.windowCGAux (m := (HM μ).m)
        (n := d + 2) (ℓ := ℓ) (𝓜 := 𝓜) hℓpos h𝓜nn hmeas hbdd hsupp horth hmem
        hpin Φ.contDiff (by simpa only [Work.BoseBox.SpectralNPlusLe] using hspec)
      rw [Work.BoseBoxFock.cnPlusC_boxRestrictC_eq_cnPlus hℓpos
          (Φ : Submission.BoseGases.X (d + 2) → ℝ)] at hw
      exact hw
    have hVle : V ≤ NP := by
      have h1 := Work.BoseBoxFock.re_boxSlotSum_boxT0_le_cnPlusC (m := (HM μ).m) (n := d + 2)
        (ℓ := ℓ) (e := e) hℓpos hmeas hbdd hsupp horth hint hpin hΘm hΘb hΘsupp
      rw [show Work.BoseBoxFock.cnPlusC ℓ Θ = Submission.BoseGases.cnPlus ℓ
          (Φ : Submission.BoseGases.X (d + 2) → ℝ) from
        Work.BoseBoxFock.cnPlusC_boxRestrictC_eq_cnPlus hℓpos
          (Φ : Submission.BoseGases.X (d + 2) → ℝ)] at h1
      have h2 : V = ∫ x in Submission.BoseGases.abox (d + 2) ℓ,
          (star (Θ x) * Work.BoseDict.boxSlotSum e
            (Work.BoseBoxFock.boxT0 (HM μ).m) Θ x).re := by
        rw [hVdef]
        exact Work.BoseBoxFock.FRK.cIPn_boxT0_re_eq_setIntegral (m := (HM μ).m) (n := d + 2)
          (ℓ := ℓ) (e := e) hℓpos hmeas hbdd hsupp hΘm hΘb hΘsupp
      rw [h2]
      exact h1
    have hSXle : SX ≤ C₁ * BoseGases.a v * ((48 / Real.pi) ^ 2 * 𝓜 * NP) := by
      have hterm : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re
            ≤ |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re := by
        intro s _
        have h1 : |E.fL s| ≤ 1 := honestFam_fL_abs_le_one h fc fu HM μ s
        have h3 : 0 ≤ (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
              (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
              (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re :=
          Work.BoseBoxFock.FRK.cIPn_self_re_nonneg _
        calc |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re
            ≤ 1 * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hW10nn) h3
          _ = |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re := by ring
      have hSXnn : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re :=
        Finset.sum_nonneg (fun s _ => Work.BoseBoxFock.FRK.cIPn_self_re_nonneg _)
      calc SX ≤ ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |E.W1 0| *
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re := by
            rw [hSXdef]; exact Finset.sum_le_sum hterm
        _ = |E.W1 0| * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).f s) d
                (Work.BoseDict.boxAnnOf e ((HM μ).f 0) (d + 1) Θ))).re := by
            rw [Finset.mul_sum]
        _ ≤ (C₁ * BoseGases.a v) * ((48 / Real.pi) ^ 2 * V2) := by
            refine mul_le_mul hW10 hSXraw hSXnn hC1a
        _ ≤ (C₁ * BoseGases.a v) * ((48 / Real.pi) ^ 2 * (𝓜 * NP)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC1a
            exact mul_le_mul_of_nonneg_left hV2le (by positivity)
        _ = C₁ * BoseGases.a v * ((48 / Real.pi) ^ 2 * 𝓜 * NP) := by ring
    have horthG : ∀ s t : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)},
        Work.BoseB4.gram ((HM μ).g s.1) ((HM μ).g t.1) = if s = t then (1 : ℝ) else 0 := by
      intro s t
      have hs : s.1 ≠ 0 := (mem_excited_iff s.1).mp s.2
      have ht : t.1 ≠ 0 := (mem_excited_iff t.1).mp t.2
      rw [(HM μ).hg s.1 t.1 hs ht]
      by_cases hst : s.1 = t.1
      · rw [if_pos hst, if_pos (Subtype.ext hst)]
      · rw [if_neg hst, if_neg (fun hh => hst (congrArg Subtype.val hh))]
    have hframeG : ∀ w : Fin (HM μ).m → ℝ,
        ∑ s : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)},
          (Work.BoseB4.gram ((HM μ).g s.1) w) ^ 2 ≤ 1 * ∑ l : Fin (HM μ).m, (w l) ^ 2 :=
      fun w => by
        simpa using gramOrthFrame (fun s : {s : Lab (HM μ).N //
          s ∈ Work.BoseB7.excited (Lab (HM μ).N)} => (HM μ).g s.1) horthG w
    have hSUsub : (∑ s : {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)},
        (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e ((HM μ).g s.1) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e ((HM μ).g s.1) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re)
        ≤ 1 * ((d : ℝ) + 2) * V :=
      Work.BoseBoxFock.PotCubicLowBandAux.lowBandCondSumAux (m := (HM μ).m) (n := d) (ℓ := ℓ)
        (e := e) hℓpos hmeas hbdd hsupp horth
        (ι := {s : Lab (HM μ).N // s ∈ Work.BoseB7.excited (Lab (HM μ).N)})
        (g := fun s => (HM μ).g s.1) (C_θ := 1) zero_le_one hframeG
        (fun s => (HM μ).hg0 s.1 ((mem_excited_iff s.1).mp s.2))
        hΘm hΘb hΘsuppPow hΘsym
    have hSUle : (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re)
        ≤ ((d : ℝ) + 2) * V := by
      rw [sum_excited_eq_sum_subtype (Mode := Lab (HM μ).N)
        (fun s => (Work.BoseDict.cIPn d
          (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
          (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
            (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re)]
      linarith [hSUsub]
    have hSYle : SY ≤ C₁ * BoseGases.a v * (1 * ((d : ℝ) + 2) * NP) := by
      have hterm : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re
            ≤ |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re := by
        intro s _
        have h1 : |E.fL s| ≤ 1 := honestFam_fL_abs_le_one h fc fu HM μ s
        have h3 : 0 ≤ (Work.BoseDict.cIPn d
            (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
            (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
              (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re :=
          Work.BoseBoxFock.FRK.cIPn_self_re_nonneg _
        calc |E.fL s| * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re
            ≤ 1 * |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hW10nn) h3
          _ = |E.W1 0| * (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re := by
              ring
      have hSYnn : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re :=
        Finset.sum_nonneg (fun s _ => Work.BoseBoxFock.FRK.cIPn_self_re_nonneg _)
      calc SY ≤ ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N), |E.W1 0| *
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re := by
            rw [hSYdef]; exact Finset.sum_le_sum hterm
        _ = |E.W1 0| * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            (Work.BoseDict.cIPn d
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))
              (Work.BoseDict.boxAnnOf e ((HM μ).g s) d
                (Work.BoseDict.boxAnnOf e (Work.BoseB4.evec (HM μ).m 0) (d + 1) Θ))).re := by
            rw [Finset.mul_sum]
        _ ≤ (C₁ * BoseGases.a v) * (1 * ((d : ℝ) + 2) * V) := by
            refine mul_le_mul hW10 ?_ hSYnn hC1a
            simpa using hSUle
        _ ≤ (C₁ * BoseGases.a v) * (1 * ((d : ℝ) + 2) * NP) := by
            have h1 : (1 * ((d:ℝ) + 2) * V) ≤ (1 * ((d:ℝ) + 2) * NP) := by
              have h2 : (0:ℝ) ≤ 1 * ((d:ℝ) + 2) := by positivity
              exact mul_le_mul_of_nonneg_left hVle h2
            exact mul_le_mul_of_nonneg_left h1 hC1a
    have hprod : Real.sqrt SX * Real.sqrt SY
        ≤ C₁ * BoseGases.a v * (48 / Real.pi) * Real.sqrt (𝓜 * ((d : ℝ) + 2)) * NP := by
      have hh := sqrt_prod_le (A := C₁ * BoseGases.a v) (B := 48 / Real.pi) (C := 1)
        (Z₁ := 𝓜) (Z₂ := ((d : ℝ) + 2)) (V := NP) (SX := SX) (SY := SY)
        hC1a (by positivity) zero_le_one h𝓜nn (by positivity) hNPnn hSXle hSYle
      rw [Real.sqrt_one, mul_one] at hh
      exact hh
    have hℓinv : ℓ ^ (-(3 : ℝ)) = ℓ ^ (-2 : ℤ) * ℓ⁻¹ := by
      have h3 : ℓ ^ (-(3:ℝ)) = (ℓ^3)⁻¹ := by
        rw [Real.rpow_neg (x := ℓ) hℓnn (3:ℝ)]
        rw [show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
      have h2 : ℓ ^ (-2 : ℤ) = (ℓ^2)⁻¹ := by
        rw [show (-2:ℤ) = -((2:ℕ):ℤ) from rfl, zpow_neg, zpow_natCast]
      rw [h3, h2, ← mul_inv]
      rfl
    have hzpos : 0 < ℓ ^ (-2 : ℤ) := zpow_pos hℓpos _
    have hs𝓜 : Real.sqrt (𝓜 * ((d : ℝ) + 2)) ≤ Real.sqrt (2 * μ * ℓ ^ 3 * 𝓜) := by
      apply Real.sqrt_le_sqrt
      calc 𝓜 * ((d : ℝ) + 2) ≤ 𝓜 * (2 * μ * ℓ ^ 3) :=
            mul_le_mul_of_nonneg_left hnR h𝓜nn
        _ = 2 * μ * ℓ ^ 3 * 𝓜 := by ring
    have htle : (μ * (BoseGases.a v) ^ 3) ^ (1/9 : ℝ) ≤ γ / (2 * K) := by
      have h1 : (μ * (BoseGases.a v) ^ 3) ^ (1/9 : ℝ)
          ≤ ((γ / (2 * K)) ^ (9:ℕ)) ^ (1/9 : ℝ) := by
        refine Real.rpow_le_rpow (mul_pos hμ (pow_pos ha 3)).le ?_ (by norm_num)
        exact htγ
      have h2 : ((γ / (2 * K)) ^ (9:ℕ)) ^ (1/9 : ℝ) = γ / (2 * K) := by
        rw [← Real.rpow_natCast (γ / (2*K)) 9,
          ← Real.rpow_mul (by positivity : (0:ℝ) ≤ γ/(2*K))]
        norm_num
      linarith [h1, h2.le, h2.ge]
    have harith := zeroCellArith (μ := μ) (a := BoseGases.a v) hμ ha ht1
    have hKt : K * (μ * (BoseGases.a v) ^ 3) ^ (1/9 : ℝ) ≤ γ/2 := by
      have h1 : K * (μ * (BoseGases.a v) ^ 3) ^ (1/9 : ℝ) ≤ K * (γ / (2 * K)) :=
        mul_le_mul_of_nonneg_left htle hKnn
      have h2 : K * (γ / (2 * K)) = γ / 2 := by field_simp
      linarith [h1, h2.le, h2.ge]
    have hfin : 2 * C₁ * (48 / Real.pi) *
        (BoseGases.a v * ℓ⁻¹ * Real.sqrt (𝓜 * ((d:ℝ)+2))) ≤ γ := by
      have h1 : BoseGases.a v * ℓ⁻¹ * Real.sqrt (𝓜 * ((d:ℝ)+2))
          ≤ Real.sqrt 2 * (μ * (BoseGases.a v)^3) ^ (1/9:ℝ) :=
        (mul_le_mul_of_nonneg_left hs𝓜 (by positivity)).trans harith
      have h2 : 2 * C₁ * (48 / Real.pi) *
            (Real.sqrt 2 * (μ*(BoseGases.a v)^3)^(1/9:ℝ))
          = K * (μ*(BoseGases.a v)^3)^(1/9:ℝ) := by
        rw [hKdef]; ring
      calc 2 * C₁ * (48 / Real.pi) * (BoseGases.a v * ℓ⁻¹ * Real.sqrt (𝓜 * ((d:ℝ)+2)))
          ≤ 2 * C₁ * (48 / Real.pi) *
              (Real.sqrt 2 * (μ*(BoseGases.a v)^3)^(1/9:ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = K * (μ*(BoseGases.a v)^3)^(1/9:ℝ) := h2
        _ ≤ γ/2 := hKt
        _ ≤ γ := by linarith [hγ]
    have hcoef : 2 * (ℓ ^ (-(3 : ℝ))) * (C₁ * BoseGases.a v * (48 / Real.pi) *
          Real.sqrt (𝓜 * ((d:ℝ)+2))) ≤ γ * ℓ ^ (-2 : ℤ) := by
      have e : 2 * (ℓ^(-(3:ℝ))) * (C₁ * BoseGases.a v * (48/Real.pi) *
            Real.sqrt (𝓜 * ((d:ℝ)+2)))
          = (2 * C₁ * (48/Real.pi) * (BoseGases.a v * ℓ⁻¹ * Real.sqrt (𝓜 * ((d:ℝ)+2))))
            * ℓ ^ (-2 : ℤ) := by
        rw [hℓinv]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hfin hzpos.le
    have htarget : 2 * (ℓ ^ (-(3 : ℝ))) * Real.sqrt SX * Real.sqrt SY
        ≤ γ * (ℓ ^ (-2 : ℤ) * NP) := by
      have e1 : 2 * (ℓ ^ (-(3 : ℝ))) * Real.sqrt SX * Real.sqrt SY
          ≤ 2 * (ℓ ^ (-(3 : ℝ))) * (C₁ * BoseGases.a v * (48 / Real.pi) *
              Real.sqrt (𝓜 * ((d:ℝ)+2)) * NP) := by
        have h2 := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ 2 * ℓ^(-(3:ℝ)))
        calc 2 * (ℓ ^ (-(3 : ℝ))) * Real.sqrt SX * Real.sqrt SY
            = 2 * (ℓ ^ (-(3 : ℝ))) * (Real.sqrt SX * Real.sqrt SY) := by ring
          _ ≤ 2 * (ℓ ^ (-(3 : ℝ))) * (C₁ * BoseGases.a v * (48 / Real.pi) *
              Real.sqrt (𝓜 * ((d:ℝ)+2)) * NP) := h2
      refine e1.trans ?_
      calc 2 * (ℓ ^ (-(3 : ℝ))) * (C₁ * BoseGases.a v * (48 / Real.pi) *
              Real.sqrt (𝓜 * ((d:ℝ)+2)) * NP)
          = (2 * (ℓ ^ (-(3 : ℝ))) * (C₁ * BoseGases.a v * (48 / Real.pi) *
              Real.sqrt (𝓜 * ((d:ℝ)+2)))) * NP := by ring
        _ ≤ (γ * ℓ ^ (-2 : ℤ)) * NP := mul_le_mul_of_nonneg_right hcoef hNPnn
        _ = γ * (ℓ ^ (-2 : ℤ) * NP) := by ring
    have hz : (0:ℝ) ≤ 1 / 2 * Work.BoseFixR.errKafz v R μ 0 *
        Work.BoseBoxFix.normB v μ (d + 2) Φ := by
      rw [herr]
      simp
    change (∫ x : Submission.BoseGases.X (d + 2), star (Θ x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Work.BoseB7.excited (Lab (HM μ).N)) E Θ x).re
        - (∫ x : Submission.BoseGases.X (d + 2), star (Θ x) *
          potCubic (fun T => Work.BoseDict.boxSlotSum e T) (HM μ).f (HM μ).g
            (Finset.univ : Finset (Lab (HM μ).N)) E Θ x).re
        ≤ γ * (ℓ ^ (-2 : ℤ) * NP)
          + 1 / 2 * Work.BoseFixR.errKafz v R μ 0 * Work.BoseBoxFix.normB v μ (d + 2) Φ
    exact (hrow.trans htarget).trans (le_add_of_nonneg_right hz)

