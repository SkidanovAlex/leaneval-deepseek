/-
# ZeroFreeTables/OffAxis/RectRepOrder3Case

**HB Lemma 9.1 at a repeated zero, order-3 case (`χ₁² ≠ 1`, `χ₁³ = 1`), at rectangle
height `H`.**

For `a, K, ε > 0`, `H ≥ 1` and `W ≥ 3H + 1` there is `q₀` such that for `q ≥ q₀`, a level-`q`
character `χ₁` with `χ₁² ≠ 1`, `χ₁³ = 1`, a pair `(χ₁, ρ₁)` with `IsMinWideAt H W χ₁ ρ₁`, a
**multiple** zero (`2 ≤ zeroMult χ₁ ρ₁`) and the side condition `cond913 λ₁ λ₁ a K`, HB's
inequality `ineq913 λ₁ λ₁ a K ε` holds.

## The argument

This is the height-`H` form of `Rep9.order3_case_prim` (`Rep9/Assembly.lean`), with the
replacements of the piece map (`OffAxis/NOTE_RectRep_pieces.md`):

* `IsMin1WideAt 10` ↦ `IsMinWideAt H W` (plus `3H + 1 ≤ W`), `IsZ χ ρ` ↦ the three consequences
  `χ ≠ 1`, `|Im ρ| ≤ H`, `0 ≤ lamOf q ρ`;
* `Rep9.pointBound` ↦ `OffAxis.pointBoundH` at height `3H` (the four points `σ`, `σ + iγ`,
  `σ + 2iγ`, `σ + 3iγ` have height `≤ 3H`); this forces the threshold `3H ≤ log q`, met by
  enlarging `q₀`;
* `Rep9.principalBoundAmended` ↦ `OffAxis.RectRepPrincipal` (the wide principal bound, valid
  for `|Im s| ≤ 3H`);
* `Rep9.nearSum_bounds.1` ↦ `Rep9.nearSumDoubleH`, `Rep9.nearSum_bounds.2` ↦ `RectRepNearSum`;
* `Rep9.combination_diag` ↦ `RectRepComb`, `Rep9.order3_extraM` ↦ `RectRepOrder3`;
* the endgame `Rep9.ineq913_diag_of_derived_poly` is used verbatim.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectRepOrder3
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPrincipal
import Submission.Work.ZeroFreeTables.OffAxis.RepHMisc
import Submission.Work.ZeroFreeTables.OffAxis.RepHNear
import Submission.Work.ZeroFreeTables.OffAxis.RectRepNearSum
import Submission.Work.ZeroFreeTables.OffAxis.RectRepComb
import Submission.Work.ZeroFreeTables.Rep9.Assembly
import Submission.Work.ZeroFreeTables.Rep9.P3_div_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.OffAxis


open Work.ZeroFreeTables Work.LinnikContract

/-- The imaginary part of `x + iγ` (with `x`, `γ` real). -/
private lemma imRepAddI (x γ : ℝ) :
    ((((x : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I).im) = γ := by
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

/-- The real part of `x + iγ` (with `x`, `γ` real). -/
private lemma reRepAddI (x γ : ℝ) :
    ((((x : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * Complex.I).re) = x := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

theorem RectRepOrder3Case {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 = 1 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  -- ## the constants (transcribed from `Rep9.order3_case_prim`)
  set S : ℝ := K^2 + 3*K + 3/2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (min (1/(768*K)) (1/12)) (min (29*a*S/(768*K)) (a*S/(24*K))) with hedef
  have hepos : 0 < e := by
    rw [hedef]
    exact lt_min (lt_min (by positivity) (by norm_num))
      (lt_min (by positivity) (by positivity))
  have heA : e ≤ min (1/(768*K)) (1/12) := min_le_left _ _
  have heB : e ≤ min (29*a*S/(768*K)) (a*S/(24*K)) := min_le_right _ _
  have he1 : e ≤ 1/(768*K) := le_trans heA (min_le_left _ _)
  have he12 : e ≤ 1/12 := le_trans heA (min_le_right _ _)
  have he3 : e ≤ a*S/(24*K) := le_trans heB (min_le_right _ _)
  set e0 : ℝ := e * S / (2*(K^2+K+1/2)) with he0def
  have he0pos : 0 < e0 := by rw [he0def]; positivity
  have he0le : e0 ≤ 3*e/2 := by
    rw [he0def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K^2+K+1/2))]
    have h1 : K^2 + 3*K + 3/2 ≤ 3*(K^2+K+1/2) := by nlinarith only [sq_nonneg K, hK]
    have h2 : e * (K^2 + 3*K + 3/2) ≤ e * (3*(K^2+K+1/2)) :=
      mul_le_mul_of_nonneg_left h1 hepos.le
    have h3 : (3*e/2) * (2*(K^2+K+1/2)) = e * (3*(K^2+K+1/2)) := by ring
    rw [hSdef]
    linarith only [h2, h3.le, h3.ge]
  have he0quarter : e0 ≤ 1/4 + e := by linarith only [he0le, he12]
  -- polynomial forms of the size conditions on `e`, `e0`
  have he1' : 768*K*e ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left he1 (by positivity : (0:ℝ) ≤ 768*K)
    have h2 : (768*K)*(1/(768*K)) = 1 := by
      field_simp
    linarith only [h, h2.le, h2.ge]
  have h768 : 768*K*e*S ≤ S := by
    have h := mul_le_mul_of_nonneg_right he1' hSpos.le
    simpa using h
  have he0v : (K^2+K+1/2)*e0 = e*S/2 := by
    rw [he0def]; field_simp
  have he0les : e0 ≤ e*S := by
    have hA0 : (1:ℝ)/2 ≤ K^2+K+1/2 := by nlinarith only [sq_nonneg K, hK]
    have hnn : 0 ≤ e*S := mul_nonneg hepos.le hSpos.le
    have h1 : (e*S)*1 ≤ (e*S)*(2*(K^2+K+1/2)) :=
      mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 2*(K^2+K+1/2)) hnn
    rw [he0def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(K^2+K+1/2))]
    linarith only [h1]
  have h84 : 84*K*e*S ≤ S/2 := by
    have h1 : 84*K*e*S = (84/768)*(768*K*e*S) := by ring
    have h2 : (84/768)*(768*K*e*S) ≤ (84/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (84/768)*S ≤ (1/2:ℝ)*S :=
      mul_le_mul_of_nonneg_right (by norm_num) hSpos.le
    have h4 : (1/2:ℝ)*S = S/2 := by ring
    linarith only [h1.le, h1.ge, h2, h3, h4.le, h4.ge]
  have hSge : (3:ℝ)/2 ≤ S := by rw [hSdef]; nlinarith only [sq_nonneg K, hK.le]
  set ex : ℝ := e/(4*a*S) with hexdef
  have hexle : ex ≤ 1/(96*K) := by
    have h := div_le_div_of_nonneg_right he3 (by positivity : (0:ℝ) ≤ 4*a*S)
    have h3 : (a*S/(24*K))/(4*a*S) = 1/(96*K) := by
      field_simp; ring
    linarith only [h, h3.le, h3.ge]
  have hexSp : 48*K*(ex*S) ≤ S/2 := by
    have h := mul_le_mul_of_nonneg_right hexle hSpos.le
    have h4 : 48*K*(ex*S) ≤ 48*K*((1/(96*K))*S) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 48*K*((1/(96*K))*S) = S/2 := by
      field_simp; ring
    linarith only [h4, h2.le, h2.ge]
  set CN : ℝ := (K^2+K+1/2)*e0 + (S - 1/4)*(1/4+e) + (1/4)*e0 with hCNdef
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (le_of_lt ha) (by linarith only [Work.ZeroFreeTables.Rep9.Kond_pos hK])
  -- ## the analytic inputs, at heights `3H` and `H`
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ := pointBoundH (a := a) (e := e) (M := M) (H := 3 * H) ha hepos hMnn
  obtain ⟨q₀p, hprinc⟩ := RectRepPrincipal (a := a) (e := e0) (M := M) (H := H) ha he0pos hMnn hH1
  obtain ⟨q₀x, hextra⟩ := RectRepOrder3 (a := a) (δ := δ) (e := e) (M := M)
    ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max q₀b q₀p) (max (max q₀x (max (Nat.ceil (Real.exp (max (M/δ) 10)))
      (Nat.ceil (Real.exp (3 * H))))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3eq hcond
  have hqb : q₀b ≤ q := by omega
  have hqp : q₀p ≤ q := by omega
  have hqx : q₀x ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hceMd : Nat.ceil (Real.exp (max (M/δ) 10)) ≤ q := by omega
  have hce3H : Nat.ceil (Real.exp (3 * H)) ≤ q := by omega
  have hLnb : Real.exp (max (M/δ) 10) ≤ (q : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceMd)
  have hMδ : M/δ ≤ Real.log (q : ℝ) := by
    calc M/δ ≤ max (M/δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * Real.log (q : ℝ) := by
    have h' : M/δ ≤ Real.log (q : ℝ) := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith only [h']
  have h3H : 3 * H ≤ Real.log (q : ℝ) := by
    have hexp : Real.exp (3 * H) ≤ (q : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hce3H)
    calc 3 * H = Real.log (Real.exp (3 * H)) := (Real.log_exp _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  -- ## basic facts about the pair
  have hW2 : H + 2 ≤ W := by linarith only [hH1, hHW]
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := hmin.1
  have hlam0 : 0 ≤ lamOf q ρ₁ := IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
    rw [div_le_iff₀ hLpos]
    exact le_trans hlamM hMlt
  have hcube : ((a + lamOf q ρ₁) / a) ^ 3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith
  have hale : a ≤ al := by rw [hal]; linarith
  have hnumA : ((a + lamOf q ρ₁ : ℝ) : ℂ) = (al : ℂ) := by rw [← hal]
  have hnumB : ((a : ℂ) + ((lamOf q ρ₁ : ℝ) : ℂ)) = (al : ℂ) := by
    rw [← Complex.ofReal_add, ← hal]
  set σ : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) with hσ
  set P0 : ℝ := P3R (al/a) with hP0def
  set Φa : ℝ := (P3 ((al:ℂ) / ((a:ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I))).re
    with hΦadef
  set Φ2 : ℝ := (P3 ((al:ℂ) / ((al:ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I))).re
    with hΦ2def
  set Wv : ℝ := P3NearSumL q (Real.log (q:ℝ)) (χ₁^2)
    (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ with hWdef
  have hcomb := RectRepComb (χ₁ := χ₁) (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K) (H := H)
    hq2 ha hK hγ hlam0 hχ1ne
  have hσeq : (((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) = σ := by rw [hσ]
  have hcomb' := hcomb
  rw [hσeq] at hcomb'
  have hσre : σ.re = 1 + a / Real.log (q:ℝ) := by rw [hσ]; exact Complex.ofReal_re _
  have hσim : |σ.im| ≤ 3 * H := by
    rw [hσ]; simp only [Complex.ofReal_im, abs_zero]; linarith only [hH1]
  -- ## (0) the principal character at `σ`
  have hb0 : SigmaP3L q (Real.log (q:ℝ)) (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P0 + al*e0 := by
    have h := hprinc q hqp (lam₁ := lamOf q ρ₁) hlam0 hlamM hHlog σ hσre hσim
    have hz : (a + lamOf q ρ₁) / ((σ - 1) * ((Real.log (q:ℝ) : ℝ) : ℂ)) = ((al/a : ℝ) : ℂ) := by
      have hnum : ((a + lamOf q ρ₁ : ℝ) : ℂ) = (((a : ℝ) : ℂ) + ((lamOf q ρ₁ : ℝ) : ℂ)) := by
        push_cast; ring
      rw [← hnum]
      have hσ1 : σ - 1 = (((a / Real.log (q:ℝ) : ℝ)) : ℂ) := by
        have hcast : ((1 + a / Real.log (q:ℝ) : ℝ) : ℂ) - 1
            = (((1 + a / Real.log (q:ℝ)) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * ((Real.log (q:ℝ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hLpos)
      rw [hσ2, ← Complex.ofReal_div, hal]
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * ((Real.log (q:ℝ) : ℝ) : ℂ)))).re = P0 := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal, hP0def] using h
  -- ## (1) `χ₁` at `σ + iγ`: the multiple zero gives `−2 P₃(1)`
  have hb1 : SigmaP3L q (Real.log (q:ℝ)) χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al*(1/4 + e) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q:ℝ) := by
      rw [hσ]; exact reRepAddI _ _
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have hsi : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im = ρ₁.im := by
        rw [hσ]; exact imRepAddI _ _
      rw [hsi]; linarith only [hγ, hH1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM h3H
      (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have h3 : (2:ℝ) * P3R 1 ≤ P3NearSumL q (Real.log (q:ℝ)) χ₁
        (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin hW2 hmult
        ha hδ0 hδ1 hδlam
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
      rw [hs] at h
      exact h
    linarith only [h1, h3]
  -- ## (2) `χ₁²` at `σ + 2iγ` (with the near sum `Wv` kept)
  have hb2 : SigmaP3L q (Real.log (q:ℝ)) (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I)
      a (lamOf q ρ₁) ≤ -Wv + al*(1/4 + e) := by
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q:ℝ) := by
      rw [hσ]; exact reRepAddI _ _
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have hsi : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 2 * ρ₁.im := by
        rw [hσ]; exact imRepAddI _ _
      rw [hsi, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith only [hγ, hH1]
    have h1 := hpb q hqb (χ₁^2) (fun hcon => hχ2 hcon) hlam0 hlamM h3H
      (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
    rw [hs] at h1
    simpa [hWdef] using h1
  have hWnn : 0 ≤ Wv := by
    have hre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q:ℝ) := by
      rw [hσ]; exact reRepAddI _ _
    have him : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have hsi : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 2 * ρ₁.im := by
        rw [hσ]; exact imRepAddI _ _
      rw [hsi, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith only [hγ, hH1]
    have h := RectRepNearSum (q := q) χ₁ (χ₁^2) ρ₁ hq2 hmin hHW (fun hcon => hχ2 hcon)
      hlam0 ha hδ0 hδ1 (s := σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) hre him
    simpa [hWdef] using h
  -- ## (3) `χ₁³ = 1` at `σ + 3iγ` (principal)
  have hb3 : SigmaP3L q (Real.log (q:ℝ)) (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I)
      a (lamOf q ρ₁) ≤ Φa + al*e0 := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a / Real.log (q:ℝ) := by
      rw [hσ]; exact reRepAddI _ _
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have hsi : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 3 * ρ₁.im := by
        rw [hσ]; exact imRepAddI _ _
      rw [hsi, abs_mul, show |(3:ℝ)| = 3 by norm_num]
      linarith only [hγ]
    have h := hprinc q hqp (lam₁ := lamOf q ρ₁) hlam0 hlamM hHlog
      (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have hz : (P3 ((a + lamOf q ρ₁) / (((σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1)
        * ((Real.log (q:ℝ) : ℝ) : ℂ)))).re = Φa := by
      have harg : (a + lamOf q ρ₁) / (((σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1)
          * ((Real.log (q:ℝ) : ℝ) : ℂ))
          = (al:ℂ) / ((a:ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I) := by
        have hσ3 : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
            = (((a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
          rw [hσ]; push_cast; ring
        have hL3 : (((((a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I)
            * ((Real.log (q:ℝ) : ℝ) : ℂ))
            = ((a : ℂ) + (((3 * ρ₁.im * Real.log (q:ℝ) : ℝ)) : ℂ) * Complex.I) := by
          rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a (ne_of_gt hLpos)]
          rw [show ((3 * ρ₁.im : ℝ) : ℂ) * Complex.I * ((Real.log (q:ℝ) : ℝ) : ℂ)
              = (((3 * ρ₁.im * Real.log (q:ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
        rw [hσ3, hL3, hnumB]
      rw [harg, hΦadef]
    rw [hz] at h
    simpa [hal, hχ3eq] using h
  by_cases hnear : ‖(1 : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ### NEAR branch: `2·Φ(α,α,μ) ≤ Wv` dominates the pole term `Φ(α,a,μ)`
    have hxk := (hextra q hqx χ₁ ρ₁ hmin hHW hmult hχ3eq hδlam hlamM).1 hnear
    have hxs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2 * ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ]
    have hxz : ((a : ℂ) + ((lamOf q ρ₁ : ℝ) : ℂ)) / (((a : ℂ) + ((lamOf q ρ₁ : ℝ) : ℂ))
        + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((al:ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [hnumB]
    have hxk' : 2 * Φ2 ≤ Wv := by
      rw [hxs, hxz] at hxk
      simpa [hWdef, hΦ2def] using hxk
    have hΦ2nn : 0 ≤ Φ2 := by
      rw [hΦ2def]
      exact Work.ZeroFreeTables.P9.PhiG_nonneg (x := al) (y := al)
        (t := 3 * ρ₁.im * Real.log (q:ℝ)) halpos le_rfl
    have hdiv := Work.ZeroFreeTables.Rep9.P3_div_le (x := al) (y := a)
      (t := 3 * ρ₁.im * Real.log (q:ℝ)) ha hale
    have hΦale : Φa ≤ (al/a)^3 * Φ2 := by simpa [hΦadef, hΦ2def] using hdiv
    have hpair : (1/4) * Φa ≤ (K + 1/2) * Wv := by
      have hKd : Kond K ≤ 4*K := min_le_right _ _
      have h4 : (1/4)*(al/a)^3 ≤ 2*(K+1/2) := by nlinarith only [hcube, hKd, hK]
      have h2 : (1/4) * Φa ≤ (1/4) * ((al/a)^3 * Φ2) :=
        mul_le_mul_of_nonneg_left hΦale (by norm_num)
      have h3 : (1/4) * ((al/a)^3 * Φ2) = ((1/4)*(al/a)^3) * Φ2 := by ring
      have h5 : ((1/4)*(al/a)^3) * Φ2 ≤ (2*(K+1/2)) * Φ2 :=
        mul_le_mul_of_nonneg_right h4 hΦ2nn
      have h7 : (K+1/2)*(2*Φ2) ≤ (K+1/2)*Wv :=
        mul_le_mul_of_nonneg_left hxk' (by linarith)
      have h8 : (2*(K+1/2))*Φ2 = (K+1/2)*(2*Φ2) := by ring
      linarith only [h2, h3, h5, h7, h8]
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/4+e))
          + (K+1/2)*(-Wv + al*(1/4+e)) + (1/4)*(Φa + al*e0)
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
            + ((1/4)*Φa - (K+1/2)*Wv) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
          + ((1/4)*Φa - (K+1/2)*Wv) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      linarith only [hlow, hpair]
    have hcp : CN*(48*K) ≤ 12*K*S + S/2 := by
      have h1 : CN*(48*K) = 48*K*(K^2+K+1/2)*e0 + 48*K*((S-1/4)*(1/4+e))
          + 12*K*e0 := by rw [hCNdef]; ring
      have h2 : 48*K*(K^2+K+1/2)*e0 = 24*K*e*S := by
        linear_combination (48*K) * he0v
      have h3 : 12*K*e0 ≤ 12*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0les (show (0:ℝ) ≤ 12*K by positivity)
        have h' : (12:ℝ)*K*(e*S) = 12*K*e*S := by ring
        linarith only [h, h'.le, h'.ge]
      have h4 : 48*K*((S-1/4)*(1/4+e)) = 12*K*S + 48*K*e*S - 3*K - 12*K*e := by ring
      have h5 : (0:ℝ) ≤ 3*K + 12*K*e := by positivity
      have h6 : 24*K*e*S + (12*K*S + 48*K*e*S - 3*K - 12*K*e) + 12*K*e*S
          ≤ 12*K*S + 84*K*e*S := by linarith only [h5]
      have h7 : 12*K*S + 84*K*e*S ≤ 12*K*S + S/2 := by linarith only [h84]
      linarith only [h1.le, h1.ge, h2.le, h2.ge, h3, h4.le, h4.ge, h6, h7]
    have hcp' : CN*(48*K) ≤ (12*K+1)*S := by
      have h8 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [hcp, h8.le, h8.ge, hSpos.le]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K) (C := CN)
      (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcp' hD
  · -- ### FAR branch: `Φ(α,a,μ) ≤ e`, absorbed by the extra error `ex`
    have hfar := (hextra q hqx χ₁ ρ₁ hmin hHW hmult hχ3eq hδlam hlamM).2 hnear
    have hxz : ((a : ℂ) + ((lamOf q ρ₁ : ℝ) : ℂ)) / ((a:ℂ)
        + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((a:ℂ) + ((3 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [hnumB]
    have hfar' : Φa ≤ e := by
      rw [hxz] at hfar
      simpa [hΦadef] using hfar
    have hexb : e/4 ≤ al*(ex*S) := by
      have h1 : al*(ex*S) = al*e/(4*a) := by
        rw [hexdef]
        field_simp
      have h2 : a*e/(4*a) = e/4 := by
        field_simp
      have h3 : a*e/(4*a) ≤ al*e/(4*a) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hale hepos.le) (by positivity)
      rw [h1, ← h2]
      exact h3
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*(CN + ex*S) := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/4+e))
          + (K+1/2)*(-Wv + al*(1/4+e)) + (1/4)*(Φa + al*e0)
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
            + ((1/4)*Φa - (K+1/2)*Wv) := by
        rw [hCNdef]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*CN
          + ((1/4)*Φa - (K+1/2)*Wv) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      have hdrop : (1/4)*Φa - (K+1/2)*Wv ≤ (1/4)*e := by
        have hW2' : (0:ℝ) ≤ (K+1/2)*Wv := mul_nonneg (by linarith) hWnn
        linarith only [hfar', hW2']
      have hsum2 : al*(CN + ex*S) = al*CN + al*(ex*S) := by ring
      rw [hsum2]
      linarith only [hlow, hdrop, hexb]
    have hcf : (CN + ex*S)*(48*K) ≤ (12*K+1)*S := by
      have hcp : CN*(48*K) ≤ 12*K*S + S/2 := by
        have h1 : CN*(48*K) = 48*K*(K^2+K+1/2)*e0 + 48*K*((S-1/4)*(1/4+e))
            + 12*K*e0 := by rw [hCNdef]; ring
        have h2 : 48*K*(K^2+K+1/2)*e0 = 24*K*e*S := by
          linear_combination (48*K) * he0v
        have h3 : 12*K*e0 ≤ 12*K*e*S := by
          have h := mul_le_mul_of_nonneg_left he0les (show (0:ℝ) ≤ 12*K by positivity)
          have h' : (12:ℝ)*K*(e*S) = 12*K*e*S := by ring
          linarith only [h, h'.le, h'.ge]
        have h4 : 48*K*((S-1/4)*(1/4+e)) = 12*K*S + 48*K*e*S - 3*K - 12*K*e := by ring
        have h5 : (0:ℝ) ≤ 3*K + 12*K*e := by positivity
        have h6 : 24*K*e*S + (12*K*S + 48*K*e*S - 3*K - 12*K*e) + 12*K*e*S
            ≤ 12*K*S + 84*K*e*S := by linarith only [h5]
        have h7 : 12*K*S + 84*K*e*S ≤ 12*K*S + S/2 := by linarith only [h84]
        linarith only [h1.le, h1.ge, h2.le, h2.ge, h3, h4.le, h4.ge, h6, h7]
      have h1 : (CN + ex*S)*(48*K) = CN*(48*K) + 48*K*(ex*S) := by ring
      have h2 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [h1.le, h1.ge, hcp, hexSp, h2.le, h2.ge]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K)
      (C := CN + ex*S) (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcf hD

end Work.ZeroFreeTables.OffAxis