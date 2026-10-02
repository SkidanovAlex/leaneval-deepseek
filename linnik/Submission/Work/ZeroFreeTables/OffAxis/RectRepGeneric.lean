/-
# ZeroFreeTables/OffAxis/RectRepGeneric

The **generic case** (`χ₁² ≠ 1`, `χ₁³ ≠ 1`) of HB Lemma 9.1 at a multiple zero, at rectangle
height `H`: the height-parametric form of `Rep9.Assembly.generic_case_prim`.

With `L = log q`, `λ = lamOf q ρ₁`, `γ = Im ρ₁`, `α = a + λ`, `σ = 1 + a/L`, the four points of
HB's diagonal (9.1) combination are `σ`, `σ+iγ`, `σ+2iγ`, `σ+3iγ`, all of height `≤ 3H`.  The
per-point bounds are

* `σ`: the principal-character pole bound `Rep9.principalBoundAmended`;
* `σ+iγ`: the wide point bound `pointBoundWide` together with the double-zero near sum
  `Rep9.nearSumDoubleH` (`P3NearSumL ≥ 2 P₃(1)`);
* `σ+2iγ`, `σ+3iγ`: `pointBoundWide` with the near sums dropped by `RectRepNearSum`
  (`P3NearSumL ≥ 0`),

and the assembly is `RectRepDiag` (the diagonal §9 endgame at height `H`).

The constants are `M = a (Kond K + 1)` (the bound on `λ` from `cond913`), error `1/200` for each
of the four point bounds, and `c = 1/6 + 1/200`; the side condition
`c ≤ 1/6 + (K²+K+1−K·Kond K)/(12K)` holds because `K + 1/4 ≤ K²+K+1−K·Kond K`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPoint
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDiag
import Submission.Work.ZeroFreeTables.OffAxis.RectRepNearSum
import Submission.Work.ZeroFreeTables.OffAxis.RepHNear
import Submission.Work.ZeroFreeTables.Rep9.principalBoundAmended
import Submission.Work.ZeroFreeTables.Rep9.Assembly

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

/-- **The generic case of HB Lemma 9.1 at a repeated zero, at height `H`** (`χ₁² ≠ 1`,
`χ₁³ ≠ 1`). -/
theorem rectRepGeneric {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 3 ≠ 1 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (le_of_lt ha) (by linarith only [Work.ZeroFreeTables.Rep9.Kond_pos hK, hK])
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ :=
    pointBoundWide (a := a) (e := 1/200) (M := M) (H := H) ha (by norm_num) hMnn hH1
  obtain ⟨L₀p, hprinc⟩ :=
    Work.ZeroFreeTables.Rep9.principalBoundAmended (a := a) (e := 1/200) (M := M) ha
      (by norm_num)
  refine ⟨max (max q₀b (Nat.ceil (Real.exp L₀p)))
      (max (Nat.ceil (Real.exp (max (M/δ) 10))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hqb : q₀b ≤ q := by omega
  have hLp : L₀p ≤ L := by
    have hce : Nat.ceil (Real.exp L₀p) ≤ q := by omega
    have hexp : Real.exp L₀p ≤ (q:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hce)
    rw [hLdef]
    calc L₀p = Real.log (Real.exp L₀p) := (Real.log_exp L₀p).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hexp
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  have hLnb : Real.exp (max (M/δ) 10) ≤ (q:ℝ) := by
    have h2 : (Nat.ceil (Real.exp (max (M/δ) 10)) : ℝ) ≤ (q:ℝ) :=
      by exact_mod_cast (by omega : Nat.ceil (Real.exp (max (M/δ) 10)) ≤ q)
    exact le_trans (Nat.le_ceil _) h2
  have hMδ : M/δ ≤ L := by
    rw [hLdef]
    calc M/δ ≤ max (M/δ) 10 := le_max_left _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  have hMlt : M ≤ δ * L := by
    have h' : M/δ ≤ L := hMδ
    rw [div_le_iff₀ hδ0] at h'
    linarith only [h']
  have h10 : (10:ℝ) ≤ L := by
    rw [hLdef]
    calc (10:ℝ) ≤ max (M/δ) 10 := le_max_right _ _
      _ = Real.log (Real.exp (max (M/δ) 10)) := (Real.log_exp _).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos _) hLnb
  -- facts about the pair
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.OffAxis.IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / L ≤ δ := by
    rw [div_le_iff₀ hLpos]; exact le_trans hlamM hMlt
  have hγ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := Work.ZeroFreeTables.OffAxis.IsMinWideAt.ne_one hmin
  have hcube : ((a + lamOf q ρ₁)/a)^3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith only [ha, hlam0]
  set σ : ℂ := ((1 + a / L : ℝ) : ℂ) with hσ
  -- (0) the principal character at `σ`
  have hS0 : SigmaP3L q L (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P3R (al/a) + al * (1/200) := by
    have hσre : σ.re = 1 + a/L := by rw [hσ]; simp
    have hσim : |σ.im| ≤ 4 := by rw [hσ]; simp
    have h := hprinc (L := L) (lam₁ := lamOf q ρ₁) hLp (le_of_eq hLdef.symm) hlam0 hlamM
      σ hσre hσim
    have hz : (a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)) = ((al/a : ℝ) : ℂ) := by
      have hσ1 : σ - 1 = (((a/L : ℝ)) : ℂ) := by
        have hcast : ((1 + a/L : ℝ) : ℂ) - 1 = (((1 + a/L) - 1 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
        rw [hσ, hcast]
        congr 1
        ring
      have hσ2 : (σ - 1) * (L : ℂ) = ((a : ℝ) : ℂ) := by
        rw [hσ1, ← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ a (ne_of_gt hLpos)
      rw [hσ2, ← Complex.ofReal_add, ← Complex.ofReal_div, hal]
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)))).re = P3R (al/a) := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal] using h
  -- (1) `χ₁` at `σ + iγ`: the double zero gives `−2 P₃(1)`
  have hS1 : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al * (1/6 + 1/200) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      rw [hσ]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, zero_add]
      linarith only [hγ, hH1, hδ0, hδ1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM hHlog _ hsre hsim
    have h3 : (2:ℝ) * P3R 1 ≤ P3NearSumL q L χ₁
        (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin
        (by linarith only [hH1, hHW]) hmult ha hδ0 hδ1 hδlam
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- (2) `χ₁²` at `σ + 2iγ`
  have hS2 : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ al * (1/6 + 1/200) := by
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 2 * ρ₁.im := by rw [hσ]; simp
      rw [him, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith only [hγ, hH1, hδ0, hδ1]
    have h1 := hpb q hqb (χ₁^2) (fun hcon => hχ2 hcon) hlam0 hlamM hHlog _ hsre hsim
    have h3 : (0:ℝ) ≤ P3NearSumL q L (χ₁^2)
        (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := RectRepNearSum (q := q) χ₁ (χ₁^2) ρ₁ hq2 hmin hHW (fun hcon => hχ2 hcon)
        hlam0 ha hδ0 hδ1 (s := σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((2*ρ₁.im : ℝ)) : ℂ) * Complex.I)
          = σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- (3) `χ₁³` at `σ + 3iγ`
  have hS3 : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ al * (1/6 + 1/200) := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 3 * ρ₁.im := by rw [hσ]; simp
      rw [him, abs_mul, show |(3:ℝ)| = 3 by norm_num]
      linarith only [hγ, hH1]
    have h1 := hpb q hqb (χ₁^3) (fun hcon => hχ3 hcon) hlam0 hlamM hHlog _ hsre hsim
    have h3 : (0:ℝ) ≤ P3NearSumL q L (χ₁^3)
        (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ := by
      have h := RectRepNearSum (q := q) χ₁ (χ₁^3) ρ₁ hq2 hmin hHW (fun hcon => hχ3 hcon)
        hlam0 ha hδ0 hδ1 (s := σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
          = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      exact h
    linarith only [h1, h3, inst]
  -- the endgame
  set c : ℝ := 1/6 + (K^2 + K + 1 - K * Kond K) / (12*K) with hcdef
  have hc : c ≤ 1/6 + (K^2 + K + 1 - K * Kond K) / (12*K) := le_rfl
  have he : (K^2 + K + 1/2) * (1/200:ℝ) + (K^2 + 2*K + 3/4) * (1/6 + 1/200)
        + (K + 1/2) * (1/6 + 1/200) + (1/4) * (1/6 + 1/200)
      ≤ c * (K^2 + 3*K + 3/2) := by
    have hsl := Work.ZeroFreeTables.Rep9.slack_ge_Kquarter hK
    have hLHS : (K^2 + K + 1/2) * (1/200:ℝ) + (K^2 + 2*K + 3/4) * (1/6 + 1/200)
        + (K + 1/2) * (1/6 + 1/200) + (1/4) * (1/6 + 1/200)
        = (K^2 + 3*K + 3/2)/6 + (K+1)^2/100 := by ring
    have hRHS : c * (K^2 + 3*K + 3/2)
        = (K^2 + 3*K + 3/2)/6
          + (K^2 + K + 1 - K * Kond K) * (K^2 + 3*K + 3/2) / (12*K) := by
      first | (rw [hcdef]; field_simp; ring) | (rw [hcdef]; field_simp)
    rw [hLHS, hRHS]
    have hkey : (K+1)^2/100 ≤ (K^2 + K + 1 - K * Kond K) * (K^2 + 3*K + 3/2) / (12*K) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 12*K)]
      have hSnn : 0 ≤ K^2 + 3*K + 3/2 := by positivity
      have h2 : (K + 1/4) * (K^2 + 3*K + 3/2)
          ≤ (K^2 + K + 1 - K * Kond K) * (K^2 + 3*K + 3/2) :=
        mul_le_mul_of_nonneg_right hsl hSnn
      nlinarith only [h2, sq_nonneg K, hK.le, hK, hδ0, hδ1]
    linarith only [hkey]
  exact RectRepDiag χ₁ ρ₁ hq2 ha hK hε hχ1ne hγ hlam0 hcond hc hS0 hS1 hS2 hS3 he

end Work.ZeroFreeTables.OffAxis
