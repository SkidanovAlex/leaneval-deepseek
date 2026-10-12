import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KzAllC2
import Submission.Work.BoseBoxFock.SymAllC
import Submission.Work.BoseBoxFock.symC_floor_honest2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.SymCAllC` — the `symC` floor for the corrected operator `KzOpCAll`

`symC_floor_honest2` (`symC_floor_honest2.lean`) proves the pointwise floor of FS `thm:Kafz`
with the *uncorrected* `KzOpC`:
`(⨅_ρ valFS ρ − err(z))‖Φ(z)‖² ≤ Re Σ_i z^{p_i}z̄^{q_i}⟪Φ(z), KvecHon i Φ(z)⟫`.
Here the same floor is proved with the χ-label-`0` row included, i.e. with `KzOpCAll` and the
globally minimised `⨅_ρ valFSAll ρ`.  This is the input the corrected model theorem
(`model_kafz_all`) consumes.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

variable {m : ℕ} [NeZero m]

theorem symC_floor_honest2All (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ C Kw : ℝ) (hμ : 0 < μ) (hC : 0 ≤ C) (hKw : 0 ≤ Kw)
    (hM0 : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
    (henv : Work.BoseBoxFock.EnvFactsAt v h fc fu HM μ C)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ 48 / Real.pi)
    (hχ2 : (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k ^ 2) ≤ 1)
    (hBes : ∀ x : Work.BoseB4.cfock (Work.BoseB4.Excited (HM μ).m),
        (inner ℂ x (Work.BoseBoxFock.nPlusChi (m := (HM μ).m) (HM μ).f x)).re
          ≤ (48 / Real.pi) * (inner ℂ x (Work.BoseBoxFock.nPlusC (m := (HM μ).m) x)).re)
    (n : ℕ) (hn : (n : ℝ) ≤ 2 * μ * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
    (Ψ : Work.BoseB4.RealFock (HM μ).m)
    (hWin : Work.BoseBoxFock.ExcWindow
      (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ) n Ψ) :
    ∀ z : ℂ,
      ((⨅ (ρ : {ρ : ℝ // 0 ≤ ρ}),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ.1)
          - (4 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
             + 4 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                 * (|(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0|
                     * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                         (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                   + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
                     * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                         (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
                 * ‖z‖
             + (|2 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                     (8 * Real.pi * BoseGases.a v) + μ * (8 * Real.pi * BoseGases.a v)|
                 + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                   * (2 * C * BoseGases.a v
                       + |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
                           + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                   * ((48 / Real.pi) * (Work.BoseBox.bigM
                       (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))))
        * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
      ≤ (∑ i ∈ Finset.range 25,
          z ^ (Work.BoseBoxFock.pvecF i) * (starRingEnd ℂ z) ^ (Work.BoseBoxFock.qvecF i) *
            inner ℂ (Work.BoseB4.Phi (Work.BoseB4.split Ψ) z)
              (Work.BoseBoxFock.KvecHon v h fc fu HM μ i
                (Work.BoseB4.Phi (Work.BoseB4.split Ψ) z))).re := by
  intro z
  let u : ℂ := if z = 0 then 1 else z / ((‖z‖ : ℝ) : ℂ)
  have hudef : u = if z = 0 then 1 else z / ((‖z‖ : ℝ) : ℂ) := rfl
  have hzu : z = ((‖z‖ : ℝ) : ℂ) * u := by
    rw [hudef]
    by_cases hz : z = 0
    · rw [if_pos hz, hz, norm_zero, Complex.ofReal_zero, zero_mul]
    · rw [if_neg hz]
      have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hz
      rw [← mul_div_assoc, mul_div_cancel_left₀ z h0]
  have hu : u * starRingEnd ℂ u = 1 := by
    rw [hudef]
    by_cases hz : z = 0
    · rw [if_pos hz]; simp
    · rw [if_neg hz]
      have hns : Complex.normSq (z / ((‖z‖ : ℝ) : ℂ)) = 1 := by
        rw [Complex.normSq_div, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
        field_simp
      rw [Complex.mul_conj, hns, Complex.ofReal_one]
  have henv0 := henv
  obtain ⟨hell, hell_eq, hmu_eq, -, -, -, hW1le, hWωle, hω0, -, hωval, hcH, hW1par, hWωpar,
    hτpar, hχpar⟩ := henv0
  obtain ⟨f, hf, hfdeg⟩ := phi_split_toCFock (m := (HM μ).m) hWin z
  have hdegvz : ∀ β ∈ ((toCFock (Excited (HM μ).m)).symm (Phi (split Ψ) z)).support,
      Finsupp.degree β ≤ ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
        (BoseGases.a v) μ⌋₊ := by
    intro β hβ
    rw [hf] at hβ
    simp only [LinearEquiv.symm_apply_apply] at hβ
    exact hfdeg β hβ
  have hKvz : (inner ℂ (Phi (split Ψ) z)
        (nPlusC (m := (HM μ).m) (Phi (split Ψ) z))).re
      ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        * ‖Phi (split Ψ) z‖ ^ 2 := by
    have h2 := inner_nPlusC_toCFock_le (m := (HM μ).m)
      ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ⌋₊ f hfdeg
    rw [← hf] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (Nat.floor_le hM0) (sq_nonneg _))
  let w : cfock (Excited (HM μ).m) := gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z)
  have hwdef : w = gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z) := rfl
  have hdegw : ∀ β ∈ ((toCFock (Excited (HM μ).m)).symm w).support,
      Finsupp.degree β ≤ ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
        (BoseGases.a v) μ⌋₊ :=
    degree_gaugeC_le u _ (Phi (split Ψ) z) hdegvz
  have hwnorm : ‖w‖ ^ 2 = ‖Phi (split Ψ) z‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) w,
      norm_sq_eq_re_inner (𝕜 := ℂ) (Phi (split Ψ) z)]
    exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z) (Phi (split Ψ) z))
  have hKplus : (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
      ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ
        * ‖w‖ ^ 2 := by
    have hgap : (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
        = (inner ℂ (Phi (split Ψ) z)
            (nPlusC (m := (HM μ).m) (Phi (split Ψ) z))).re := by
      rw [hwdef, ← gaugeC_nPlusC (m := (HM μ).m) u hu (Phi (split Ψ) z)]
      exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z)
        (nPlusC (m := (HM μ).m) (Phi (split Ψ) z)))
    rw [hgap, hwnorm]
    exact hKvz
  have hKc : (inner ℂ w (nPlusChi (m := (HM μ).m) (HM μ).f w)).re
      ≤ ((48 / Real.pi) * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
          (BoseGases.a v) μ) * ‖w‖ ^ 2 := by
    have h1 := hBes w
    have h2 : (48 / Real.pi) * (inner ℂ w (nPlusC (m := (HM μ).m) w)).re
        ≤ (48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
            (BoseGases.a v) μ * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hKplus (by positivity)
    refine le_trans h1 ?_
    rw [mul_assoc]
    exact h2
  have hsym : (inner ℂ (Phi (split Ψ) z)
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z (Phi (split Ψ) z))).re
      = (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re := by
    have h1 : gaugeC (Excited (HM μ).m) u
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
          (((‖z‖ : ℝ) : ℂ) * u) (Phi (split Ψ) z))
        = symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖
          (gaugeC (Excited (HM μ).m) u (Phi (split Ψ) z)) :=
      gaugeC_symC _ _ _ _ _ _ _ u hu (gaugeC_BNHHon v h fc fu HM μ u hu) _
    rw [← hzu] at h1
    rw [hwdef, ← h1]
    exact congrArg Complex.re (gaugeC_inner_iso u hu (Phi (split Ψ) z)
      (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z
        (Phi (split Ψ) z))).symm
  have hsum : (inner ℂ (Phi (split Ψ) z)
        (symC (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) z (Phi (split Ψ) z))).re
      = (∑ i ∈ Finset.range 25, z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i) *
          inner ℂ (Phi (split Ψ) z)
            (KvecHon v h fc fu HM μ i (Phi (split Ψ) z))).re := by
    congr 1
    simp only [symC, KvecHon]
    rw [LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right]
  have hρ : 0 ≤ ‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 :=
    div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hell) 3)
  obtain ⟨x, y, hxre, hyre, hxdeg, hydeg, hwxy, hwnormxy, -⟩ :=
    KzOpC_split_re_im v h fc fu HM μ
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
      ⌊Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ⌋₊
      w hdegw
  have hquadAll : (inner ℂ w (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
        (8 * Real.pi * BoseGases.a v)
        (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w)).re
      = (inner ℂ x (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) x)).re
        + (inner ℂ y (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) y)).re := by
    rw [hwxy]
    exact quadForm_re_split_of_isRealMap _
      (KzOpCAll_real (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
        (8 * Real.pi * BoseGases.a v) (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
        (isRealMap_BNHHon v h fc fu HM μ)) x y hxre hyre
  have hdecx := eigen_decomp_of_degree (HonestBoxFam v h fc fu HM μ).E.bigM x hxdeg
  have hdecy := eigen_decomp_of_degree (HonestBoxFam v h fc fu HM μ).E.bigM y hydeg
  have hflx : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖x‖ ^ 2
      ≤ (inner ℂ x (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) x)).re :=
    KzOpCAll_floor_window v h hv hvrad hR hv_supp hav fc fu HM μ C Kw (48 / Real.pi)
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) hμ hC hρ hKw (by positivity)
      henv hWω hχb x hxre hdecx
  have hfly : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖y‖ ^ 2
      ≤ (inner ℂ y (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) y)).re :=
    KzOpCAll_floor_window v h hv hvrad hR hv_supp hav fc fu HM μ C Kw (48 / Real.pi)
      (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) hμ hC hρ hKw (by positivity)
      henv hWω hχb y hyre hdecy
  have hfloor : (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖w‖ ^ 2
      ≤ (inner ℂ w (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
          (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w)).re := by
    rw [hwnormxy, hquadAll]
    linarith [hflx, hfly]
  have hWsup : ∀ k : Lab (HM μ).N,
      |(HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k|
        ≤ 2 * C * BoseGases.a v := by
    intro k
    calc |(HonestBoxFam v h fc fu HM μ).E.W1 k + (HonestBoxFam v h fc fu HM μ).E.W1omega k|
        ≤ |(HonestBoxFam v h fc fu HM μ).E.W1 k|
          + |(HonestBoxFam v h fc fu HM μ).E.W1omega k| := abs_add_le _ _
      _ ≤ C * BoseGases.a v + C * BoseGases.a v := add_le_add (hW1le k) (hWωle k)
      _ = 2 * C * BoseGases.a v := by ring
  have hdisc : ∀ r : ℝ, 0 ≤ r →
      symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) r
        - KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v) (r ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)
      = ((r ^ 2 : ℝ) : ℂ) • D2FAll (HM μ).f (HonestBoxFam v h fc fu HM μ).E
          (8 * Real.pi * BoseGases.a v)
        + ((r : ℝ) : ℂ) • D1F (HM μ).f (HM μ).g (HonestBoxFam v h fc fu HM μ).E
        + D0F (HM μ).f (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) :=
    fun r hr => symDiscrepAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
      ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
      (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
      (8 * Real.pi * BoseGases.a v) hell rfl hτpar hχpar hW1par hWωpar hωval r hr
  have hSym := symR_floor_genAll (f := (HM μ).f) (g := (HM μ).g) (BNH := BNHHon v h fc fu HM μ)
    (PHs := (HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
    (F := (HonestBoxFam v h fc fu HM μ).F) (E := (HonestBoxFam v h fc fu HM μ).E)
    (gHat0 := 8 * Real.pi * BoseGases.a v) (hℓ := hell) (hPH := rfl) (hcH := hcH)
    (hω0 := hω0) (hφ := (HM μ).hf0)
    (hgonb := fun s hs t ht => (HM μ).hg s t (Finset.mem_erase.mp hs).1
      (Finset.mem_erase.mp ht).1)
    (hdisc := hdisc)
    (K := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
    (Kc := (48 / Real.pi) * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ)
    (Kχb := 48 / Real.pi) (Wsup := 2 * C * BoseGases.a v) (hK0 := hM0)
    (hKc0 := mul_nonneg (by positivity) hM0) (hKχb0 := by positivity) (hWsup := hWsup)
    (hχ2 := hχ2) (hχ2b := hχb)
  have hSymr := hSym ‖z‖ (norm_nonneg z) w hKc hKplus
  have hsplit : (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
        ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
        (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re
      = (inner ℂ w (KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w)).re
        + (inner ℂ w (((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
              ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
              (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖)
            - KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
              (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
              (8 * Real.pi * BoseGases.a v)
              (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w)).re := by
    have h2 : symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w
        = KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3) w
          + ((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
                (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖
              - KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
                (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
                (8 * Real.pi * BoseGases.a v)
                (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w) := by
      rw [LinearMap.sub_apply]
      abel
    rw [h2, inner_add_right, Complex.add_re]
  have hforms :
      4 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * Work.BoseBoxFock.cHCF (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                    (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
      = 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * i3F (HonestBoxFam v h fc fu HM μ).E
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM
                      (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + (HonestBoxFam v h fc fu HM μ).E.mu * (8 * Real.pi * BoseGases.a v)|
              + i3F (HonestBoxFam v h fc fu HM μ).E
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM
                    (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))) := by
    rw [show i3F (HonestBoxFam v h fc fu HM μ).E
        = (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) from rfl, hmu_eq]
  have hkey : ((⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) - (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2
      ≤ (inner ℂ w (symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
          ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
          (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖ w)).re := by
    rw [hsplit]
    have h2 : -((4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2 ≤ (inner ℂ w (((symR (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            ((HonestBoxFam v h fc fu HM μ).F.PHset (HonestBoxFam v h fc fu HM μ).E)
            (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) ‖z‖)
          - KzOpCAll (HM μ).f (HM μ).g (BNHHon v h fc fu HM μ)
            (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).E
            (8 * Real.pi * BoseGases.a v)
            (‖z‖ ^ 2 / (HonestBoxFam v h fc fu HM μ).E.ell ^ 3)) w)).re := by
      have h1 := hSymr
      dsimp only [Work.BoseBoxFock.i3F] at h1
      rw [hmu_eq] at h1
      exact h1
    have hsum2 := add_le_add hfloor h2
    have hL : ((⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) - (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2
        = (⨅ (ρ' : {ρ : ℝ // 0 ≤ ρ}),
        (HonestBoxFam v h fc fu HM μ).valFSAll ρ'.1) * ‖w‖ ^ 2 + (-(4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) * ‖z‖ ^ 2
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)))
              * ‖z‖
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v)
                + μ * (8 * Real.pi * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ))))) * ‖w‖ ^ 2 := by ring
    rw [hL]
    exact hsum2
  rw [← hwnorm, ← hsum, hsym]
  exact hkey

end Work.BoseBoxFock
