import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.Rep9.principalBoundAmended
import Submission.Work.ZeroFreeTables.OffAxis.HBLemma9_1_engine_H_cplx
import Submission.Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH
import Submission.Work.ZeroFreeTables.OffAxis.zetaZeroFreeStripH
import Submission.Work.ZeroFreeTables.OffAxis.HB91H.zetaZeroInvSq_wide
import Submission.Work.ZeroFreeTables.Engine6.principalSigmaDiff_gen

open DirichletCharacter Complex Set Filter
open scoped Topology BigOperators

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-!
# `Work.ZeroFreeTables.OffAxis.RectRepPrincipal`

The **wide principal bound** of the height-`H` repeated-zero `P₃` engine: the height-`3H` form of
`Rep9.principalBoundAmended` (whose `|Im s| ≤ 4` is not enough for the diagonal argument, whose
points `σ + 2iγ`, `σ + 3iγ` have heights `2H`, `3H`).

## Proof

Exactly the proof of `Rep9.principalBoundM_of_bounds` (i.e. of the engine
`HB95PrincipalEngine.principalEngine6`), with the two height constants `5` and `4` replaced by a
single parameter `T`:

* the `ζ`-corrector `-ζ'/ζ - 1/(s-1)`, together with its first two derivatives, is bounded in real
  part by a constant `C₁` on the closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}` — by compactness,
  since the corrector agrees there with `-logDeriv ((s-1)ζ(s))`, the logarithmic derivative of a
  nowhere-zero analytic function (`zetaCorrector_three_boundsT` below);
* the mod-`q` correction is `Engine6.principalSigmaDiff_gen`, whose bound does not involve the
  height at all;
* the absorption of the two corrections into `α·e` is `Rep9.shiftAbsorb`.

The target is then the case `T = 3H`, `L = log q`.
-/

/-! ## The general-height `ζ`-corrector bound -/

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}`. -/
private def zetaRectT (T : ℝ) : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| ≤ T}

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}` is compact. -/
private lemma isCompact_zetaRectT (T : ℝ) : IsCompact (zetaRectT T) := by
  have h : zetaRectT T = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
      '' (Set.Icc 1 2 ×ˢ Set.Icc (-T) T) := by
    ext s
    constructor
    · intro ⟨h1, h2, h3⟩
      refine ⟨(s.re, s.im), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [abs_le] at h3; exact ⟨h3.1, h3.2⟩
      · simp
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · simpa using hp1
      · simpa using hp2
      · simp only [ofReal_re, ofReal_im, add_im, mul_I_im, zero_add]
        exact abs_le.mpr ⟨hp3, hp4⟩
  rw [h]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- The extension `z ↦ (z-1)ζ(z)` of `ζ` does not vanish for `Re z ≥ 1` (no restriction on
`Im z`): the only delicate point is `z = 1`, where the extension takes the value `1`, and
`riemannZeta_ne_zero_of_one_le_re` handles the rest. -/
private lemma zetaExtPole_ne_zero_of_one_le_re (s : ℂ) (h1 : 1 ≤ s.re) :
    Work.ZeroFreeTables.P9.zetaExtPole s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · subst h
    simp [Work.ZeroFreeTables.P9.zetaExtPole, Work.ZeroFreeTables.P9.psiExtPole, Gammaℝ_one]
  · rw [Work.ZeroFreeTables.P9.zetaExtPole_eq s (by rintro rfl; norm_num at h1) h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (riemannZeta_ne_zero_of_one_le_re h1)

/-- The closed rectangle `{1 ≤ Re s ≤ 2, |Im s| ≤ T}` sits inside the open set `zetaExtU` on which
`zetaExtPole` is analytic and nonzero. -/
private lemma zetaRectT_subset_zetaExtU (T : ℝ) : zetaRectT T ⊆ Work.ZeroFreeTables.P9.zetaExtU := by
  intro z hz
  have hz' : 1 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T := hz
  refine ⟨?_, zetaExtPole_ne_zero_of_one_le_re z hz'.1⟩
  intro h0
  have hre : z.re = 0 := by rw [h0]; simp
  linarith [hz'.1]

/-- **The `ζ`-corrector bound at an arbitrary height.**  The corrector
`zetaCorrector s = -ζ'/ζ(s) - 1/(s-1)` and its first two derivatives are bounded (in real part, in
absolute value) on the rectangle `1 < Re s ≤ 2`, `|Im s| ≤ T`.  On that rectangle
`zetaCorrector = -logDeriv zetaExtPole`, the logarithmic derivative of the nowhere-zero analytic
function `zetaExtPole` on `zetaExtU ⊇ {1 ≤ Re s ≤ 2, |Im s| ≤ T}`, so
`logDeriv_iteratedDeriv_re_bdd` applies to the compact rectangle. -/
private theorem zetaCorrector_three_boundsT (T : ℝ) (_hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ T →
      |(Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C ∧
      |(iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re| ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.ZeroFreeTables.P9.logDeriv_iteratedDeriv_re_bdd
    Work.ZeroFreeTables.P9.zetaExtPole Work.ZeroFreeTables.P9.zetaExtU (zetaRectT T)
    Work.ZeroFreeTables.P9.isOpen_zetaExtU (isCompact_zetaRectT T) (zetaRectT_subset_zetaExtU T)
    Work.ZeroFreeTables.P9.analyticOn_zetaExtPole_of_U
    Work.ZeroFreeTables.P9.zetaExtPole_ne_zero_on_U
  refine ⟨C₁, hC₁pos, ?_⟩
  intro s hs1 hs2 hs3
  have hs : s ∈ zetaRectT T := ⟨le_of_lt hs1, hs2, hs3⟩
  obtain ⟨h0, h1, h2⟩ := hC₁ s hs
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  obtain ⟨h2l, h2r⟩ := abs_le.mp h2
  have heq : Work.ZeroFreeTables.Rep9.zetaCorrector =ᶠ[𝓝 s]
      fun z => -logDeriv Work.ZeroFreeTables.P9.zetaExtPole z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1] with z hz
    rw [Work.ZeroFreeTables.Rep9.zetaCorrector,
      Work.ZeroFreeTables.P9.logDeriv_zetaExtPole_eq z hz, one_div]
    ring
  have hd0 : (Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((logDeriv Work.ZeroFreeTables.P9.zetaExtPole s).re) := by
    have h := heq.iteratedDeriv_eq 0
    simp only [iteratedDeriv_zero] at h
    simpa using congrArg Complex.re h
  have hd1 : (iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((iteratedDeriv 1 (logDeriv Work.ZeroFreeTables.P9.zetaExtPole) s).re) := by
    have h := heq.iteratedDeriv_eq 1
    simp only [iteratedDeriv_fun_neg] at h
    simpa using congrArg Complex.re h
  have hd2 : (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      = -((iteratedDeriv 2 (logDeriv Work.ZeroFreeTables.P9.zetaExtPole) s).re) := by
    have h := heq.iteratedDeriv_eq 2
    simp only [iteratedDeriv_fun_neg] at h
    simpa using congrArg Complex.re h
  refine ⟨?_, ?_, ?_⟩
  · rw [hd0, abs_le]
    exact ⟨by linarith, by linarith⟩
  · rw [hd1, abs_le]
    exact ⟨by linarith, by linarith⟩
  · rw [hd2, abs_le]
    exact ⟨by linarith, by linarith⟩

/-! ## The principal engine at arbitrary height -/

/-- **The principal-character `P₃` engine at arbitrary height `T`.** -/
private theorem principalEngineWide {a e M T : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M)
    (_hT : 0 ≤ T) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q : ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M → ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ T →
        Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
  obtain ⟨C₁, hC₁pos, hZ⟩ := zetaCorrector_three_boundsT T _hT
  obtain ⟨C₂, hC₂pos, hD⟩ :=
    Work.ZeroFreeTables.Engine6.principalSigmaDiff_gen (a := a) (M := M) ha hM
  obtain ⟨L₀, _hL₀one, hL₀⟩ :=
    Work.ZeroFreeTables.Rep9.shiftAbsorb (a := a) (M := M) (e := e) ha hM he hC₁pos hC₂pos
  refine ⟨max (max L₀ a) 1, le_max_right _ _, ?_⟩
  intro q _inst L lam₁ hL hlogq hlam0 hlamM s hsre hsim
  have hL₀le : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have haL : a ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have h1L : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one h1L
  have hs1 : 1 < s.re := by rw [hsre]; exact lt_add_of_pos_right 1 (div_pos ha hLpos)
  have hs2 : s.re ≤ 2 := by
    rw [hsre]
    have hle : a / L ≤ 1 := by rw [div_le_one hLpos]; exact haL
    linarith
  have hαnn : 0 ≤ a + lam₁ := by linarith
  have hαM : a + lam₁ ≤ a + M := by linarith
  have hy : 0 ≤ (a + lam₁) / L := div_nonneg hαnn hLpos.le
  -- ## the reduction at `q = 1`
  have hred : Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁
      = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * (Work.ZeroFreeTables.Rep9.zetaCorrector s).re
        - ((a + lam₁) / L) ^ 2
          * (iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3
          * (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re := by
    rw [Work.ZeroFreeTables.Rep9.SigmaP3L_principal_eq_pole_add_corrector (q := 1)
        (L := L) (a := a) (lam₁ := lam₁) (s := s) hs1,
      Work.ZeroFreeTables.Rep9.principalCorrector_one_eq_zetaCorrector_fun]
  -- ## the bounds for the three corrector terms
  obtain ⟨hZ0, hZ1, hZ2⟩ := hZ s hs1 hs2 hsim
  have hcorr : ((a + lam₁) / L) * (Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      + (1 / 3) * ((a + lam₁) / L) ^ 3
        * (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
      ≤ ((a + lam₁) / L) * C₁ * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
    have hb0 : (Work.ZeroFreeTables.Rep9.zetaCorrector s).re ≤ C₁ :=
      le_trans (le_abs_self _) hZ0
    have hb1 : -(iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re ≤ C₁ :=
      le_trans (neg_le_abs _) hZ1
    have hb2 : (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re ≤ C₁ :=
      le_trans (le_abs_self _) hZ2
    have h2 : 0 ≤ ((a + lam₁) / L) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ ((a + lam₁) / L) ^ 3 := pow_nonneg hy 3
    have e1 : ((a + lam₁) / L) * (Work.ZeroFreeTables.Rep9.zetaCorrector s).re
        ≤ ((a + lam₁) / L) * C₁ := mul_le_mul_of_nonneg_left hb0 hy
    have e2 : ((a + lam₁) / L) ^ 2 * (-(iteratedDeriv 1
          Work.ZeroFreeTables.Rep9.zetaCorrector s).re) ≤ ((a + lam₁) / L) ^ 2 * C₁ :=
      mul_le_mul_of_nonneg_left hb1 h2
    have e3 : ((a + lam₁) / L) ^ 3
        * (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
        ≤ ((a + lam₁) / L) ^ 3 * C₁ := mul_le_mul_of_nonneg_left hb2 h3
    nlinarith [e1, e2, e3, hy, h2, h3, hC₁pos]
  -- ## the mod-`q` correction
  have hdiff : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁
      ≤ ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
    have h := hD (q := q) hLpos hlogq hlam0 hlamM s hsre
    have hsq : Real.sqrt (Real.log (q : ℝ)) ≤ Real.sqrt L := Real.sqrt_le_sqrt hlogq
    have hfac : 0 ≤ ((a + lam₁) / L) * C₂ := mul_nonneg hy hC₂pos.le
    have hfac2 : 0 ≤ 1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2 := by positivity
    have hstep : ((a + lam₁) / L) * C₂ * (1 + Real.sqrt (Real.log (q : ℝ)))
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2)
        ≤ ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      have h1 : 1 + Real.sqrt (Real.log (q : ℝ)) ≤ 1 + Real.sqrt L := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hfac) hfac2
    have habs := le_abs_self (Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁)
    linarith [habs, h, hstep]
  -- ## absorption
  have hkey := hL₀ hL₀le (x := a + lam₁) hαnn hαM
  calc Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by linarith [hdiff]
    _ = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + (((a + lam₁) / L) * (Work.ZeroFreeTables.Rep9.zetaCorrector s).re
          - ((a + lam₁) / L) ^ 2
            * (iteratedDeriv 1 Work.ZeroFreeTables.Rep9.zetaCorrector s).re
          + (1 / 3) * ((a + lam₁) / L) ^ 3
            * (iteratedDeriv 2 Work.ZeroFreeTables.Rep9.zetaCorrector s).re)
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      rw [hred]; ring
    _ ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * C₁ * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2)
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      linarith [hcorr]
    _ ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
      linarith [hkey]

/-! ## The target at `T = 3H`, `L = log q` -/

theorem RectRepPrincipal {a e M H : ℝ} (ha : 0 < a) (he : 0 < e) (hM : 0 ≤ M) (hH1 : 1 ≤ H) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] {lam₁ : ℝ}, 0 ≤ lam₁ → lam₁ ≤ M →
      H ≤ Real.log (q : ℝ) →
      ∀ s : ℂ, s.re = 1 + a / Real.log (q : ℝ) → |s.im| ≤ 3 * H →
        Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * ((Real.log (q : ℝ) : ℝ) : ℂ)))).re
              + (a + lam₁) * e := by
  have hT : 0 ≤ 3 * H := by linarith
  obtain ⟨L₀, _hL₀one, hmain⟩ :=
    principalEngineWide (a := a) (e := e) (M := M) (T := 3 * H) ha he hM hT
  refine ⟨⌈Real.exp (max L₀ 1)⌉₊ + 2, ?_⟩
  intro q hq _inst lam₁ hlam0 hlamM _hHlog s hsre hsim
  have hle : Real.exp (max L₀ 1) ≤ (q : ℝ) := by
    have hceil : Real.exp (max L₀ 1) ≤ ((⌈Real.exp (max L₀ 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hmono : ((⌈Real.exp (max L₀ 1)⌉₊ : ℕ) : ℝ)
        ≤ ((⌈Real.exp (max L₀ 1)⌉₊ + 2 : ℕ) : ℝ) := by push_cast; norm_num
    have hq' : ((⌈Real.exp (max L₀ 1)⌉₊ + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hlog : max L₀ 1 ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (max L₀ 1)) hle
    rwa [Real.log_exp] at h
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlog
  exact hmain (q := q) (L := Real.log (q : ℝ)) (lam₁ := lam₁) hL₀le le_rfl hlam0 hlamM s hsre hsim

end Work.ZeroFreeTables.OffAxis
