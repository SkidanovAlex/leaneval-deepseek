/-
# `mslot_le_winf` — the mixed slots of the `𝒲^{4,∞}`-priced product rule (open quadrant)

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the *open* quadrant) and of class
`𝒲^{4,∞}` (`Work.Spaces.WlInfMem α 4 f`), and for a `SmoothOpen` `g` of class `ℋ⁴`
(`Work.Spaces.HkMem α 4 g`) whose *radial* slots are dominated by the mean-term estimate

`(D_z^d g(z,θ)·w(z))² ≤ CB·(w(z)² ∫_σ (D_z^d g(z,σ))² + (γ-1)⁻¹ Aang α g d z)`   (`d ≤ 3`),

every *mixed* slot of the product `f·g` (weighted as in `HkIntegrand`) is dominated pointwise by
the majorant `GmajW`:

`(D_z^J D_θ^I (f·g)(z,θ)·W)² ≤ C·|f|²_{𝒲^{4,∞}}·GmajW α g z θ`,  `1 ≤ I`, `I+J ≤ 4`.

This is the open-quadrant instance of `Work.FTS.H2.WPQ.m_term_le_smoothQuad` (whose `g`-side
hypothesis is the angular-Hardy bound `(D_z^d g·w)² ≤ 100/(γ-1) Aang α g d z`): here the open
class has no vanishing of the `g`-slices at `θ = 0, π/2`, so the `g`-side is priced by the
mean-term estimate above (`Work.FTS.OpenPkg.ProdOpen.sob_theta_mean`) and the majorant is
`GmajW` (the `ℋ⁴`-integrand of `g` plus `(HgInt + (γ-1)⁻¹ ∑_{d<4} Aang d)·TW`) instead of
`GmajQ` (where the angular block carries no `sin(2θ)^{-γ}`).

The proof is the same as in the Hardy case:

* Leibniz for the two-operator calculus in the open class
  (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`);
* Cauchy–Schwarz on the resulting double sum
  (`Finset.sq_sum_le_card_mul_sum_sq`) with the binomial bounds
  `Work.Spaces.choose_sq_le_256`;
* in each summand, if `a < I` at least one `θ`-derivative falls on `g`, so the `g`-block is a
  single mixed slot, bounded by `HkIntegrand α 4 g` (`Work.Spaces.sq_le_HkIntegrand_mixed`);
  the `f`-block is bounded by `𝒲^{4,∞}` (`Work.FTS.OpenPkg.DzIter_le_WlInf_open`,
  `Work.FTS.OpenPkg.Mixed_le_WlInf_open`);
* if `a = I` all `θ`-derivatives fall on `f`: the `f`-block then carries exactly the angular
  factor `(α + sin2θ)² sin(2θ)^{2α/5}` (which produces the `TW` of the majorant), while the
  `g`-block is the *radial* slot `D_z^{J-b} g`, which is where the mean-term hypothesis is
  consumed.

-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WProdWin.Basic
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.H2.WPQ.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WProdWin

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular and weight algebra -/

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·W)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]
  ring

/-! ## The `g`-side step: the mean-term hypothesis produces the `TW`-block of `GmajW` -/

private theorem mslot_gside_le {α CB : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgm : Work.Spaces.HkMem α 4 g)
    (hCB : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    {d : ℕ} (hd : d ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ max CB 1 * GmajW α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  -- the mean-term block is nonnegative
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α g d z))
  have hg1 : (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ max CB 1 * ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  -- the mean term and the single `Aang` term are both dominated by `HgInt`/`∑Aang`
  have hmem : d ∈ Finset.range 4 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α g d' z) hmem
  have hw : (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2) ≤ HgInt α g z :=
    w_sq_mul_slice_le_HgInt hgm (by omega) hz
  have hXle : (Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt α g z + (Work.Spaces.gam α - 1)⁻¹
          * ∑ d' ∈ Finset.range 4, Work.FTS.H2.WPQ.Aang α g d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  -- `(D_z^d g · W)² · (α+sin2θ)²sin(2θ)^{2α/5} = (D_z^d g · w)² · TW`
  rw [mul_Wt_sq hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) = TW α θ := by
    rw [TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2 * TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ
      ≤ GmajW α g z θ := by
    simp only [GmajW]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 4 g z θ))
  calc (max CB 1 * ((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) * TW α θ
      = max CB 1 * (((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) := by ring
    _ ≤ max CB 1 * GmajW α g z θ := mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

theorem mslot_le_winf (CB : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      (∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 f) ^ 2
            * Work.FTS.OpenPkg.WProdWin.GmajW α g z θ := by
  have hCpos : (0 : ℝ) < 2 * 10 ^ 12 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 12 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 12 * (1 + max CB 1), hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm hCB I J hI hIJ z θ hz hθ0 hθ1
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
    inv_nonneg.mpr (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hGnn : 0 ≤ GmajW α g z θ := GmajW_nonneg hα g hθI
  have hTWnn : 0 ≤ TW α θ := TW_nonneg hα.le hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hHkG : Work.Spaces.HkIntegrand α 4 g z θ ≤ GmajW α g z θ := HkIntegrand_le_GmajW hα g hθI
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hKper_nn : (0 : ℝ) ≤ 65536 * 40000 * (1 + max CB 1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hJ4 : J ≤ 4 := by omega
  have hI4 : I ≤ 4 := by omega
  have hA2nn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I f g hf hg z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
        * GmajW α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul (Work.Spaces.choose_sq_le_256 I a (by omega) hI4)
              (Work.Spaces.choose_sq_le_256 J b (by omega) hJ4) (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on `g`
      have hIa : 1 ≤ I - a := by omega
      have hma : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ 40000 * (Work.Spaces.WlInf α 4 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
            Work.FTS.OpenPkg.DzIter_le_WlInf_open (α := α) (f := f) (b := b) (z := z) (θ := θ)
              hf hfm (by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 := Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2 ≤ 40000 * (Work.Spaces.WlInf α 4 f) ^ 2
          nlinarith [h1, sq_nonneg (100 * Work.Spaces.WlInf α 4 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := f) (a := a) (b := b)
            (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (100 * (Work.Spaces.WlInf α 4 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ = 40000 * (Work.Spaces.WlInf α 4 f) ^ 2 := by ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (40000 * (Work.Spaces.WlInf α 4 f) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ :=
              mul_le_mul_of_nonneg_left hmg (by nlinarith [hWsq])
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
              * Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
            rw [show 65536 * ((40000 * (Work.Spaces.WlInf α 4 f) ^ 2)
                  * Work.Spaces.HkIntegrand α 4 g z θ)
                = (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2
                  * Work.Spaces.HkIntegrand α 4 g z θ) from by ring]
            calc (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2
                  * Work.Spaces.HkIntegrand α 4 g z θ)
                ≤ (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hCBB0]) (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ := by ring
    · -- all `θ`-derivatives fall on `f`: the mean-term hypothesis is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b ≤ 3 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have h := Work.FTS.OpenPkg.Mixed_le_WlInf_open (α := α) (f := f) (a := a) (b := b)
          (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
        calc (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 4 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hT : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        have he : Work.Spaces.mixed (J - b) (I - a) g = Work.Spaces.DzIter (J - b) g := by
          rw [hsub, Work.Spaces.mixed_zero_right]
        rw [he]
      have hgside : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ max CB 1 * GmajW α g z θ :=
        mslot_gside_le (α := α) (CB := CB) (g := g) (d := J - b) hα hgm hCB hdJ hz hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hT]
          _ ≤ ((100 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1 * GmajW α g z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
            rw [show 65536 * ((100 * Work.Spaces.WlInf α 4 f) ^ 2 * (max CB 1) * GmajW α g z θ)
                = (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ) from by ring]
            have hAB : (65536 * 10000 * (max CB 1) : ℝ)
                ≤ 65536 * 40000 * (1 + max CB 1) := by nlinarith [hCBB0]
            calc (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ)
                ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 4 f) ^ 2
                    * GmajW α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) ≤ 4 := by exact_mod_cast hI4
    have h2 : (J : ℝ) ≤ 4 := by exact_mod_cast hJ4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
                * GmajW α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ) := by rw [hsumconst]; ring
    _ ≤ 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
            * GmajW α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ ≤ (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ := by
        rw [show 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ)
            = (625 * (65536 * 40000 * (1 + max CB 1))) * ((Work.Spaces.WlInf α 4 f) ^ 2
              * GmajW α g z θ) from by ring]
        have hle : 625 * (65536 * 40000 * (1 + max CB 1)) ≤ 2 * 10 ^ 12 * (1 + max CB 1) := by
          nlinarith [hCBB0]
        calc (625 * (65536 * 40000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ)
            ≤ (2 * 10 ^ 12 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 4 f) ^ 2 * GmajW α g z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 4 f) ^ 2
                * GmajW α g z θ := by ring

end Work.FTS.OpenPkg.WProdWin
