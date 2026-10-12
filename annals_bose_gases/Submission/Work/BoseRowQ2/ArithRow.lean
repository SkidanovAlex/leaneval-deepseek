import ChallengeDeps
import Submission.Work.BoseRowQ2.HonParams
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.ArithRow` — the arithmetic row of FS l.3253–3257, proved

FS choose `ε ∝ ε_T^{-1}(d K_ℓ)²` (l.3257).  Writing it as a function of the
parameters alone,

    fsEps c μ = c · (paramsAt μ (a v)).eT⁻¹ · ((paramsAt μ (a v)).d · (paramsAt μ (a v)).Kl)²,

the companion inequality of l.3253–3257,

    `2 ρ Ŵ₁ω(0) (Cχ / ε) ≤ (b/800) ε_T (dℓ)⁻²`,

is *equivalent* to the purely absolute condition `2ρŴ₁ω(0)Cχ ≤ (b/800)c(μ a v)`:
the `ε_T`, `d` and `K_ℓ` factors cancel symbolically, using only
`K_ℓ²/ℓ² = μa` (`honE_ell_eq`).  This is the sense in which the corpus's `b/400`
reserve is not tight; the numerical outcome is `ρ ≤ 3μ/2`, `Ŵ₁ω(0) ≤ 16πa v`
(`Work.BoseGateFS.honE_W1omega0`, proved) and
`c = 800·(3/2)·16π·(96/π)/b = 58982400`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- FS's `ε ∝ ε_T^{-1}(dK_ℓ)²` at the parameters of `μ`, as a function of `μ` alone. -/
def fsEps (v : EuclideanSpace ℝ (Fin 3) → ℝ) (c : ℝ) (μ : ℝ) : ℝ :=
  c * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)⁻¹
    * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl) ^ 2

/-- **The arithmetic row of FS l.3253–3257, at FS's own `ε` and `Cχ = 96/π`.**

`ArithAt` holds at `ε := fsEps 58982400 μ`, provided the honest row
`Ŵ₁ω(0) ≤ 16π a v` (supplied by `Work.BoseGateFS.honE_W1omega0` at the honest
data).  With `ρ ≤ 3μ/2` the conclusion is an *equality*-tight constant
comparison, so the corpus's `b/400` reserve is sufficient with room to spare. -/
theorem RowArith_at_fsEps {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (Ng : ℝ → ℕ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hW : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ∧ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 ≤ 16 * Real.pi * _root_.BoseGases.a v) :
    RowArith (h := h) (fc := fc) (fu := fu) R εg Ng (96 / Real.pi) (fsEps v 58982400) := by
  intro _hεg1 HM _hNg μ hμ hε ρ hρ
  rw [ArithAt]
  have ht : 0 < μ * _root_.BoseGases.a v ^ 3 := mul_pos hμ (pow_pos hav 3)
  have hμa : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  have heTpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).eT := by
    rw [honE_eT_eq' v h fc fu HM μ]; exact Real.rpow_pos_of_pos ht _
  have hdpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).d := by
    rw [honE_d_eq v h fc fu HM μ]; exact Real.rpow_pos_of_pos ht _
  have hKlpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).Kl := by
    rw [honE_Kl_eq v h fc fu HM μ]; exact Real.rpow_pos_of_pos ht _
  have hellpos : 0 < (Work.BoseRowsFS.honE v h fc fu HM μ).ell := by
    rw [Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav]
    exact Work.BoseBoxFock.ellH_pos v μ
  have hεpos : 0 < fsEps v 58982400 μ := by
    rw [fsEps]
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr heTpos))
      (pow_pos (mul_pos hdpos hKlpos) 2)
  -- the parameter spellings agree definitionally
  have hPT : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      = (Work.BoseRowsFS.honE v h fc fu HM μ).eT := rfl
  have hPD : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = (Work.BoseRowsFS.honE v h fc fu HM μ).d := rfl
  have hPK : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = (Work.BoseRowsFS.honE v h fc fu HM μ).Kl := rfl
  have heTne : (Work.BoseRowsFS.honE v h fc fu HM μ).eT ≠ 0 := ne_of_gt heTpos
  have hdne : (Work.BoseRowsFS.honE v h fc fu HM μ).d ≠ 0 := ne_of_gt hdpos
  have hKlne : (Work.BoseRowsFS.honE v h fc fu HM μ).Kl ≠ 0 := ne_of_gt hKlpos
  have hellne : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ≠ 0 := ne_of_gt hellpos
  have hμane : μ * _root_.BoseGases.a v ≠ 0 := ne_of_gt hμa
  -- the box side: `ℓ² = K_ℓ² / (μa)`
  have hhalf : ((μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))) ^ 2
      = (μ * _root_.BoseGases.a v)⁻¹ := by
    rw [sq, ← Real.rpow_add hμa,
      show (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have hell2 : (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ 2
      = (Work.BoseRowsFS.honE v h fc fu HM μ).Kl ^ 2 / (μ * _root_.BoseGases.a v) := by
    rw [honE_ell_eq v h fc fu HM hμ hav, honE_Kl_eq v h fc fu HM μ, mul_pow, hhalf,
      inv_eq_one_div]
    ring
  -- the box side as it appears in `(d ℓ)^{-2}`
  have hdelli : ((Work.BoseRowsFS.honE v h fc fu HM μ).d
        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
      = ((Work.BoseRowsFS.honE v h fc fu HM μ).d ^ 2
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).Kl ^ 2
              / (μ * _root_.BoseGases.a v)))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt (mul_pos hdpos hellpos)), Real.rpow_two, mul_pow, hell2]
  -- the cancellation identity
  have hkey : ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).eT
        * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
        * fsEps v 58982400 μ
      = ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800) * 58982400
        * (μ * _root_.BoseGases.a v) := by
    rw [fsEps, hPT, hPD, hPK, hdelli]
    field_simp
  -- the absolute constant comparison
  have hnum : 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (96 / Real.pi)
      ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800) * 58982400
        * (μ * _root_.BoseGases.a v) := by
    obtain ⟨hW0, hW'⟩ := hW HM μ hμ hε
    have h1 : ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ≤ (3 * μ / 2) * (16 * Real.pi * _root_.BoseGases.a v) :=
      mul_le_mul hρ.2.2 hW' hW0 (by positivity)
    have h2 : 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        ≤ 48 * Real.pi * (μ * _root_.BoseGases.a v) := by
      nlinarith [h1, hμa, Real.pi_pos]
    rw [Work.BoseRowsFS.honE_b]
    have hpos96 : (0 : ℝ) < 96 / Real.pi := by positivity
    have hstep := mul_le_mul_of_nonneg_right h2 (le_of_lt hpos96)
    have h96 : (48 * Real.pi * (μ * _root_.BoseGases.a v)) * (96 / Real.pi)
        = 4608 * (μ * _root_.BoseGases.a v) := by
      field_simp
      ring
    have hrhs : ((1 : ℝ) / 16 / 800) * 58982400 * (μ * _root_.BoseGases.a v)
        = 4608 * (μ * _root_.BoseGases.a v) := by norm_num
    linarith [hstep, h96, hrhs]
  have hgoal : 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (96 / Real.pi)
      ≤ (((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).eT
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
        * fsEps v 58982400 μ := by
    rw [hkey]
    exact hnum
  rw [show 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (96 / Real.pi / fsEps v 58982400 μ)
      = (2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (96 / Real.pi))
        / fsEps v 58982400 μ from by ring]
  rw [div_le_iff₀ hεpos]
  exact hgoal

end Work.BoseRowQ2
