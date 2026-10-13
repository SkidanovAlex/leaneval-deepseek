import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.H2.WPQ.DzIter_Wt_sq_le_Aang_Rho
import Submission.Work.H2.WPQ.HkIntegrand_le_GmajQ
import Submission.Work.H2.WPQ.hardy_term_le_GmajQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.WPQ

open scoped Real

set_option maxHeartbeats 0

/-- `0 ≤ sin(2θ)` on the open quadrant. -/
private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) := (Work.FTS.H2.WPQ.sin_two_pos_of_Ioo hθ).le

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

/-- The weight algebra `sin(2θ)^{2α/5} · sin(2θ)^{-γ} = sin(2θ)^{2α/5-γ}` on the open
quadrant. -/
private theorem psi2_mul_rho {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.WPQ.sin_two_pos_of_Ioo hθ
  rw [mul_assoc, ← Real.rpow_add hs]
  congr 1

/-- **The mixed summand of the product rule, in the interior class.**  For `0 < α ≤ 1`, `f`, `g`
smooth on the open quadrant, `f ∈ 𝒲^{4,∞}`, and given the angular sup bound
`(D_z^d g · w)² ≤ 100/(γ-1) Aang α g d z` for `d ≤ 3` (`hardy_slice_Aang`), every mixed summand
of `HkIntegrand α 4 (f·g)` is bounded pointwise by the majorant `GmajQ`
(`Work.FTS.H2.WPQ.GmajQ`, which is the `ℋ⁴`-integrand of `g` plus the angular-Hardy
contribution):

`(D_z^J D_θ^I (f·g) · W)² ≤ 10^12 |f|_𝒲² · GmajQ α g`,  for `1 ≤ I`, `I + J ≤ 4`, `z > 0`.

Interior counterpart of `Work.Spaces.m_term_le` (hypotheses `SmoothInt`/`SmoothNbhd` there).  The
Leibniz rule for the mixed operator on the open quadrant is
`Work.FTS.H2.WPQ.mixed_mul_eq_smoothQuad` (in `Submission.Work.FTS.H2.WPQ.Leibniz`); for the
`f`-side use `Work.FTS.H2.WPQ.Mixed_le_WlInf`/`DzIter_le_WlInf` (in `WPQ.Interior`), for the
`g`-side (when at least one `θ`-derivative falls on `f`) use
`Work.Spaces.sq_le_HkIntegrand_mixed`, and in the remaining case `a = I ≥ 1` the `g`-block is
`D_z^{J-b} g` with no `θ`-derivative, which is handled by the hypothesis on `D_z^d g` together
with the weight algebra `Wt² = w² sin(2θ)^{-γ}` — this is exactly the step that needs the
angular sup bound.  Cauchy–Schwarz on the double sum (`sq_sum_le_card_mul_sum_sq`) with the
binomial bounds `Work.Spaces.choose_sq_le_256` (in `Submission/Work/Spaces/WProductRule.lean`)
gives the constant `10^12`; `Work.Spaces.m_term_le` is a good template for the whole argument. -/
theorem m_term_le_smoothQuad {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hfm : Work.Spaces.WlInfMem α 4 f)
    (hhardy : ∀ d ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g d z)
    {I J : ℕ} (hI : 1 ≤ I) (hIJ : I + J ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hzpos : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ := by
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hfm
  have hW2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTFnn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
    Work.FTS.H2.WPQ.theta_factor_nonneg hθI
  have hGnn : 0 ≤ Work.FTS.H2.WPQ.GmajQ α g z θ :=
    Work.FTS.H2.WPQ.GmajQ_nonneg hα g hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  -- the `ℋ⁴`-integrand is dominated by the majorant
  have hHkG : Work.Spaces.HkIntegrand α 4 g z θ ≤ Work.FTS.H2.WPQ.GmajQ α g z θ :=
    HkIntegrand_le_GmajQ hα hθI
  -- a single Hardy term is dominated by the majorant
  have hGd : ∀ d ≤ 3, (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      ≤ Work.FTS.H2.WPQ.GmajQ α g z θ :=
    fun d hd => hardy_term_le_GmajQ hα hθI hd
  -- Leibniz
  have heq := Work.FTS.H2.WPQ.mixed_mul_eq_smoothQuad J I f g hf hg
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq z hz θ hθ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ 1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
        * Work.FTS.H2.WPQ.GmajQ α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hI4 : I ≤ 4 := by omega
    have hJ4 : J ≤ 4 := by omega
    have hJb : J - b ≤ 3 := by omega
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 I a (by omega) hI4
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 J b (by omega) hJ4
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
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
          ≤ 5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 15 * Work.Spaces.WlInf α 4 f :=
            Work.FTS.H2.WPQ.DzIter_le_WlInf (b := b) (z := z) (θ := θ) hf hfm
              (show b ≤ 4 by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (15 * Work.Spaces.WlInf α 4 f) ^ 2 :=
            Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ 5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2
          nlinarith [h1, sq_nonneg (15 * Work.Spaces.WlInf α 4 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := Work.FTS.H2.WPQ.Mixed_le_WlInf (a := a) (b := b) (z := z) (θ := θ) hα hf
            hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (15 * (Work.Spaces.WlInf α 4 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (15 * Work.Spaces.WlInf α 4 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (15 * Work.Spaces.WlInf α 4 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ ≤ 5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2 := by
                nlinarith [sq_nonneg (15 * Work.Spaces.WlInf α 4 f)]
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2) * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2)
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2)
                * Work.Spaces.HkIntegrand α 4 g z θ :=
              mul_le_mul_of_nonneg_left hmg (mul_nonneg (by norm_num) (sq_nonneg _))
      have hA' : (0 : ℝ) ≤ (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ :=
        mul_nonneg hW2 hHknn
      have hB' : (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ :=
        mul_le_mul_of_nonneg_left hHkG hW2
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((5 * (15 * Work.Spaces.WlInf α 4 f) ^ 2)
              * Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ := by
            nlinarith [hA', hB', sq_nonneg (Work.Spaces.WlInf α 4 f)]
    · -- all `θ`-derivatives fall on `f`: the Hardy bound is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (15 * Work.Spaces.WlInf α 4 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        rw [hac]
        have h := Work.FTS.H2.WPQ.Mixed_le_WlInf (a := I) (b := b) (z := z) (θ := θ) hα hf
          hfm hI (by omega) hz hθ
        calc (Work.Spaces.mixed b I f z θ) ^ 2
            ≤ (15 * (Work.Spaces.WlInf α 4 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (15 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [hsub, Work.Spaces.mixed_zero_right]
        exact DzIter_Wt_sq_le_Aang_Rho hα hhardy hJb hz hzpos hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ ((15 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * ((100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ ((15 * Work.Spaces.WlInf α 4 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ ≤ ((15 * Work.Spaces.WlInf α 4 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
                * ((100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
              mul_le_mul_of_nonneg_left hmg
                (mul_nonneg (sq_nonneg _)
                  (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_Ioo hθ) _)))
      have hRy : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = (α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := psi2_mul_rho hθ
      have hfac : (65536 : ℝ) * ((15 * Work.Spaces.WlInf α 4 f) ^ 2
              * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * ((100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = 1474560000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * ((Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g (J - b) z
                * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
        rw [show (65536 : ℝ) * ((15 * Work.Spaces.WlInf α 4 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
              * ((100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
            = 1474560000 * ((Work.Spaces.WlInf α 4 f) ^ 2
                * (Work.FTS.H2.WPQ.Aang α g (J - b) z * ((Work.Spaces.gam α - 1)⁻¹
                  * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))) from by ring]
        rw [hRy]
        ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
                * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((15 * Work.Spaces.WlInf α 4 f) ^ 2
              * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * ((100 / (Work.Spaces.gam α - 1)) * Work.FTS.H2.WPQ.Aang α g (J - b) z
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ = 1474560000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * ((Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g (J - b) z
                * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := hfac
        _ ≤ 1474560000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.FTS.H2.WPQ.GmajQ α g z θ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGd (J - b) hJb) hW2)
              (by norm_num)
        _ ≤ 1500000000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.FTS.H2.WPQ.GmajQ α g z θ) :=
            mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hW2 hGnn)
        _ = 1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
              * Work.FTS.H2.WPQ.GmajQ α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) ≤ 4 := by exact_mod_cast (by omega : I ≤ 4)
    have h2 : (J : ℝ) ≤ 4 := by exact_mod_cast (by omega : J ≤ 4)
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * Work.FTS.H2.WPQ.GmajQ α g z θ) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.FTS.H2.WPQ.GmajQ α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  rw [hYsplit]
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
              (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
                * Work.FTS.H2.WPQ.GmajQ α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * Work.FTS.H2.WPQ.GmajQ α g z θ) := by
        rw [hsumconst]; ring_nf
    _ ≤ 625 * (1500000000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.FTS.H2.WPQ.GmajQ α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ = 937500000000 * ((Work.Spaces.WlInf α 4 f) ^ 2
          * Work.FTS.H2.WPQ.GmajQ α g z θ) := by ring
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.FTS.H2.WPQ.GmajQ α g z θ := by
        rw [show (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 4 f) ^ 2
              * Work.FTS.H2.WPQ.GmajQ α g z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 4 f) ^ 2
                * Work.FTS.H2.WPQ.GmajQ α g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hW2 hGnn)

end Work.H2.WPQ
