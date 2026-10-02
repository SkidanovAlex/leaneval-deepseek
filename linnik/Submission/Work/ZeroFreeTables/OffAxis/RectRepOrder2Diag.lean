/-
# ZeroFreeTables/OffAxis/RectRepOrder2Diag

**HB Lemma 9.1 at a multiple zero, order-2 case (`χ₁² = 1`, `ρ₁` non-real), at height `H`.**

This is `Rep9.Assembly.order2_case_prim` carried over to the rectangle-height numbering
`IsMinWideAt H W` with `3H + 1 ≤ W`, using the four-point diagonal `RectRepComb`/`RectRepDiag`:

* `σ = 1 + a/L`, `L = log q`, `λ = lamOf q ρ₁`, `α = a + λ`, `γ = Im ρ₁`, `μ = 2γL`;
* `σ`: the wide principal bound `RectRepPrincipal`, pole term `P0 = P₃^ℝ(α/a)`;
* `σ+iγ` (`χ₁`, multiple zero): the wide point bound `pointBoundWide`, near sum `W1` kept, and
  `2P₃(1) ≤ W1` by `Rep9.nearSumDoubleH`;
* `σ+2iγ` (`χ₁² = 1`, principal): `RectRepPrincipal`, pole term `Ψ = Re P₃(α/(a+iμ))`.
  *near* branch (`‖1+iγ−ρ̄₁‖ ≤ δ`, `RectRepCaseCNear`): `W1 ≥ 2P₃(1) + 2Φ₂`
  (`Φ₂ = Re P₃(α/(α+iμ))`) and `Ψ ≤ (α/a)³Φ₂ ≤ (Kond K+1)Φ₂` (`P3_div_le`), so the pole term is
  dominated using `(K+½)(Kond K+1) ≤ 2(K²+2K+3/4)` (`A2_mul_Kond_le`);
  *far* branch (`RectRepCaseCFar`): `Ψ ≤ e`, absorbed by the extra error `ex·S`;
* `σ+3iγ` (`χ₁³ = χ₁`, non-principal): `pointBoundWide` with the near sum `W3 ≥ 0` dropped
  (`RectRepNearSum`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDefs
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPoint
import Submission.Work.ZeroFreeTables.OffAxis.RectRepPrincipal
import Submission.Work.ZeroFreeTables.OffAxis.RectRepComb
import Submission.Work.ZeroFreeTables.OffAxis.RectRepDiag
import Submission.Work.ZeroFreeTables.OffAxis.RectRepNearSum
import Submission.Work.ZeroFreeTables.OffAxis.RectRepCaseCNear
import Submission.Work.ZeroFreeTables.OffAxis.RectRepCaseCFar
import Submission.Work.ZeroFreeTables.OffAxis.RepHNear
import Submission.Work.ZeroFreeTables.Rep9.P3_div_le
import Submission.Work.ZeroFreeTables.Rep9.Assembly
import Submission.Work.ZeroFreeTables.Rep9.principalBoundAmended

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables Work.LinnikContract

theorem RectRepOrder2Diag {a K ε H W : ℝ} (ha : 0 < a) (hK : 0 < K) (hε : 0 < ε)
    (hH1 : 1 ≤ H) (hHW : 3 * H + 1 ≤ W) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) → Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  set S : ℝ := K^2 + 3*K + 3/2 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  set e : ℝ := min (min (1/(768*K)) (1/12))
      (min (29*a*S/(768*K)) (a*S/(96*K*(K+1/2)))) with hedef
  have hepos : 0 < e := by
    rw [hedef]
    exact lt_min (lt_min (by positivity) (by norm_num))
      (lt_min (by positivity) (by positivity))
  have heA : e ≤ min (1/(768*K)) (1/12) := min_le_left _ _
  have heB : e ≤ min (29*a*S/(768*K)) (a*S/(96*K*(K+1/2))) := min_le_right _ _
  have he1 : e ≤ 1/(768*K) := le_trans heA (min_le_left _ _)
  have he12 : e ≤ 1/12 := le_trans heA (min_le_right _ _)
  have he4 : e ≤ a*S/(96*K*(K+1/2)) := le_trans heB (min_le_right _ _)
  set e0 : ℝ := e * S / (2*(K^2+K+1/2)) with he0def
  have he0pos : 0 < e0 := by rw [he0def]; positivity
  have he1' : 768*K*e ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left he1 (by positivity : (0:ℝ) ≤ 768*K)
    have h2 : (768*K)*(1/(768*K)) = 1 := by field_simp
    linarith [h, h2.le, h2.ge]
  have h768 : 768*K*e*S ≤ S := by
    have h := mul_le_mul_of_nonneg_right he1' hSpos.le
    simpa using h
  have h24 : 24*K*e*S ≤ S/32 := by
    have h1 : 24*K*e*S = (24/768)*(768*K*e*S) := by ring
    have h2 : (24/768)*(768*K*e*S) ≤ (24/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (24/768)*S = S/32 := by ring
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  have h48 : 48*K*e*S ≤ S/16 := by
    have h1 : 48*K*e*S = (48/768)*(768*K*e*S) := by ring
    have h2 : (48/768)*(768*K*e*S) ≤ (48/768)*S :=
      mul_le_mul_of_nonneg_left h768 (by norm_num)
    have h3 : (48/768)*S = S/16 := by ring
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  have he0v : (K^2+K+1/2)*e0 = e*S/2 := by
    first | (rw [he0def]; field_simp; ring) | (rw [he0def]; field_simp)
  have hA2e0 : (K+1/2)*e0 ≤ e*S := by
    have hK1 : K + 1/2 ≤ 2*(K^2+K+1/2) := by nlinarith [sq_nonneg K, hK]
    have h1 : (K+1/2)*e0 ≤ (2*(K^2+K+1/2))*e0 :=
      mul_le_mul_of_nonneg_right hK1 he0pos.le
    have h2 : (2*(K^2+K+1/2))*e0 = e*S := by linarith [he0v]
    linarith [h1, h2.le, h2.ge]
  have hA1e : 48*K*((K^2+2*K+3/4)*e) ≤ (K^2+2*K+3/4)/16 := by
    have h := mul_le_mul_of_nonneg_left he1' (by positivity : (0:ℝ) ≤ K^2+2*K+3/4)
    have h2 : 48*K*((K^2+2*K+3/4)*e) = ((K^2+2*K+3/4)*(768*K*e))/16 := by ring
    linarith [h, h2.le, h2.ge]
  have h12e : 12*K*e ≤ 1/64 := by
    have h1 : 12*K*e = (12/768)*(768*K*e) := by ring
    have h2 : (12/768)*(768*K*e) ≤ (12/768)*1 :=
      mul_le_mul_of_nonneg_left he1' (by norm_num)
    have h3 : (12/768)*1 = 1/64 := by norm_num
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  set ex : ℝ := (K+1/2)*e/(a*S) with hexdef
  have hexle : ex ≤ 1/(96*K) := by
    rw [hexdef, div_le_iff₀ (by positivity : (0:ℝ) < a*S)]
    have h1 : (K+1/2)*e ≤ (K+1/2)*(a*S/(96*K*(K+1/2))) :=
      mul_le_mul_of_nonneg_left he4 (by linarith)
    have h2 : (K+1/2)*(a*S/(96*K*(K+1/2))) = (1/(96*K))*(a*S) := by
      first | (field_simp; ring) | field_simp
    linarith [h1, h2.le, h2.ge]
  have hexSp : 48*K*(ex*S) ≤ S/2 := by
    have h := mul_le_mul_of_nonneg_right hexle hSpos.le
    have h4 : 48*K*(ex*S) ≤ 48*K*((1/(96*K))*S) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 48*K*((1/(96*K))*S) = S/2 := by
      first | (field_simp; ring) | field_simp
    linarith [h4, h2.le, h2.ge]
  set C2 : ℝ := (K^2+K+1/2)*e0 + (K^2+2*K+3/4)*(1/6+e) + (K+1/2)*e0
      + (1/4)*(1/6+e) with hC2def
  set M : ℝ := a * (Kond K + 1) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (le_of_lt ha) (by linarith [Work.ZeroFreeTables.Rep9.Kond_pos hK])
  obtain ⟨q₀b, δ, hδ0, hδ1, hpb⟩ :=
    pointBoundWide (a := a) (e := e) (M := M) (H := H) ha hepos hMnn hH1
  obtain ⟨q₀p, hprinc⟩ :=
    RectRepPrincipal (a := a) (e := e0) (M := M) (H := H) ha he0pos hMnn hH1
  obtain ⟨q₀c, hnearC⟩ := RectRepCaseCNear (a := a) (δ := δ) ha hδ0 hδ1
  obtain ⟨q₀f, hfarC⟩ := RectRepCaseCFar (a := a) (δ := δ) (e := e) (M := M)
    ha hδ0 hδ1 hepos hMnn
  refine ⟨max (max (max q₀b q₀c) q₀f) (max (max q₀p
      (Nat.ceil (Real.exp (max (M/δ) 10)))) 3 + 1), ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hmult hsq him hcond
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hqb : q₀b ≤ q := by omega
  have hqc : q₀c ≤ q := by omega
  have hqf : q₀f ≤ q := by omega
  have hqp : q₀p ≤ q := by omega
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
    linarith [h']
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.ZeroFreeTables.OffAxis.IsMinWideAt.lam_nonneg hmin
  have hlamM : lamOf q ρ₁ ≤ M := by
    rw [hMdef]
    exact Work.ZeroFreeTables.Rep9.lam_le_of_cond913 ha hK hlam0 hcond
  have hδlam : lamOf q ρ₁ / L ≤ δ := by
    rw [div_le_iff₀ hLpos]; exact le_trans hlamM hMlt
  have hγH : |ρ₁.im| ≤ H := hmin.2.2.1
  have hχ1ne : χ₁ ≠ 1 := Work.ZeroFreeTables.OffAxis.IsMinWideAt.ne_one hmin
  have hcube : ((a + lamOf q ρ₁)/a)^3 ≤ Kond K + 1 :=
    Work.ZeroFreeTables.Rep9.cond913_cube_le ha hlam0 hcond
  have hχ3ne : χ₁^3 ≠ 1 := by
    intro hcon
    exact hχ1ne (by
      have h2 : χ₁^3 = χ₁^2 * χ₁ := by
        rw [show (3:ℕ) = 2+1 from rfl, pow_succ]
      rw [h2, hsq, one_mul] at hcon
      exact hcon)
  set al : ℝ := a + lamOf q ρ₁ with hal
  have halpos : 0 < al := by rw [hal]; linarith
  have hale : a ≤ al := by rw [hal]; linarith
  set σ : ℂ := ((1 + a / L : ℝ) : ℂ) with hσ
  set μ : ℝ := 2 * ρ₁.im * L with hμ
  set P0 : ℝ := P3R (al/a) with hP0def
  set Ψ : ℝ := (P3 ((al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I))).re with hΨdef
  set Φ2 : ℝ := (P3 ((al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I))).re with hΦ2def
  set W1 : ℝ := P3NearSumL q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ
    with hW1def
  set W3 : ℝ := P3NearSumL q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁) δ
    with hW3def
  have hcomb := RectRepComb (q := q) χ₁ (a := a) (lam₁ := lamOf q ρ₁) (γ := ρ₁.im) (K := K)
    (H := H) hq2 ha hK hγH hlam0 hχ1ne
  have hσeq : (((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) = σ := by rw [hσ, hLdef]
  have hcomb' := hcomb
  rw [hσeq] at hcomb'
  have hσre : σ.re = 1 + a/L := by rw [hσ]; simp
  have hσim : |σ.im| ≤ 4 := by rw [hσ]; simp
  -- (0) principal character at σ
  have hb0 : SigmaP3L q L (1 : DirichletCharacter ℂ q) σ a (lamOf q ρ₁)
      ≤ P0 + al*e0 := by
    have h := hprinc q hqp hlam0 hlamM hHlog σ hσre (by
      rw [hσ]; simp only [Complex.ofReal_im, abs_zero]; linarith [hH1])
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
    have hP : (P3 ((a + lamOf q ρ₁) / ((σ - 1) * (L : ℂ)))).re = P0 := by
      rw [hz]; exact Work.ZeroFreeTables.Rep9.P3_ofReal_re (al/a)
    rw [hP] at h
    simpa [hal, hP0def] using h
  -- (1) χ₁ at σ + iγ  (near sum `W1`)
  have hb1w : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W1 + al*(1/6 + e) := by
    have hsre : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I).im = ρ₁.im := by rw [hσ]; simp
      rw [him]; linarith [hγH, hH1]
    have h1 := hpb q hqb χ₁ hχ1ne hlam0 hlamM hHlog _ hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h1
    simpa [hW1def] using h1
  have hb1 : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -(2 * P3R 1) + al*(1/6 + e) := by
    have h3 : (2:ℝ) * P3R 1 ≤ W1 := by
      have h := Work.ZeroFreeTables.Rep9.nearSumDoubleH (q := q) χ₁ ρ₁ hq2 hmin
        (by linarith only [hH1, hHW]) hmult ha hδ0 hδ1 hδlam
      have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
          = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
      rw [hs] at h
      simpa [hW1def] using h
    linarith [hb1w, h3]
  -- (2) χ₁² = 1 at σ + 2iγ  (principal, pole at distance `a + iμ`)
  have hb2 : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ Ψ + al*e0 := by
    rw [hsq]
    have hsre : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 2 * ρ₁.im := by rw [hσ]; simp
      rw [him, abs_mul, show |(2:ℝ)| = 2 by norm_num]
      linarith [hγH, hH1]
    have h := hprinc q hqp hlam0 hlamM hHlog (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre hsim
    have hz : (a + lamOf q ρ₁) / (((σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1) * (L : ℂ))
        = (al : ℂ) / ((a : ℂ) + ((μ : ℝ) : ℂ) * Complex.I) := by
      have hσ2' : (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) - 1
          = (((a / L : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I := by
        rw [hσ]; push_cast; ring
      have hL2 : (((((a / L : ℝ)) : ℂ) + ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I) * (L : ℂ))
          = ((a : ℂ) + (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I) := by
        rw [add_mul, ← Complex.ofReal_mul, div_mul_cancel₀ a (ne_of_gt hLpos)]
        rw [show ((2 * ρ₁.im : ℝ) : ℂ) * Complex.I * (L : ℂ)
            = (((2 * ρ₁.im * L : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [hσ2', hL2, hμ, hal, ← Complex.ofReal_add]
    rw [hz] at h
    simpa [hal, hΨdef] using h
  -- (3) χ₁³ = χ₁ at σ + 3iγ  (near sum `W3`)
  have hb3 : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
      ≤ -W3 + al*(1/6 + e) := by
    have hsre : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 3 * ρ₁.im := by rw [hσ]; simp
      rw [him, abs_mul, show |(3:ℝ)| = 3 by norm_num]
      linarith [hγH, hH1]
    have h1 := hpb q hqb (χ₁^3) (fun hcon => hχ3ne hcon) hlam0 hlamM hHlog _ hsre hsim
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h1
    simpa [hW3def] using h1
  have hW3nn : 0 ≤ W3 := by
    have hsre3 : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).re = 1 + a/L := by rw [hσ]; simp
    have hsim3 : |(σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im| ≤ 3 * H := by
      have him : (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I).im = 3 * ρ₁.im := by rw [hσ]; simp
      rw [him, abs_mul, show |(3:ℝ)| = 3 by norm_num]
      linarith [hγH, hH1]
    have h := RectRepNearSum (q := q) χ₁ (χ₁^3) ρ₁ hq2 hmin hHW (fun hcon => hχ3ne hcon)
      hlam0 ha hδ0 hδ1 (s := σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) hsre3 hsim3
    have hs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + (((3*ρ₁.im : ℝ)) : ℂ) * Complex.I)
        = σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    rw [hs] at h
    simpa [hW3def] using h
  by_cases hnear : ‖(1 : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₁‖ ≤ δ
  · -- ### NEAR branch: the conjugate zero dominates `Σ(σ+iγ,χ₁)`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hnc := hnearC q hqc χ₁ ρ₁ (H := H) (W := W) hmin hHW hmult hsq him hδlam' hnear
    have hxs : ((((1 + a / Real.log (q:ℝ) : ℝ)) : ℂ) + ((ρ₁.im : ℝ) : ℂ) * Complex.I)
        = σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I := by rw [hσ, hLdef]
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / (((↑a : ℂ) + ↑(lamOf q ρ₁))
        + ((2 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((al:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hnc' : (2:ℝ) * P3R 1 + 2 * Φ2 ≤ W1 := by
      rw [hxs, hxz] at hnc
      simpa [hW1def, hΦ2def] using hnc
    have hb1' : SigmaP3L q L χ₁ (σ + ((ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ -(2 * P3R 1) - 2 * Φ2 + al*(1/6 + e) := by linarith [hb1w, hnc']
    have hΦ2nn : 0 ≤ Φ2 := by
      rw [hΦ2def]
      exact Work.ZeroFreeTables.P9.PhiG_nonneg (x := al) (y := al) (t := μ) halpos le_rfl
    have hΨle : Ψ ≤ (al/a)^3 * Φ2 := by
      exact (by simpa [hΨdef, hΦ2def] using
        Work.ZeroFreeTables.Rep9.P3_div_le (x := al) (y := a) (t := μ) ha hale)
    have hpair : (K+1/2)*Ψ ≤ 2*(K^2+2*K+3/4)*Φ2 := by
      have hKd : (K+1/2)*(Kond K+1) ≤ 2*(K^2+2*K+3/4) :=
        Work.ZeroFreeTables.Rep9.A2_mul_Kond_le hK
      have h1 : (K+1/2)*((al/a)^3) ≤ (K+1/2)*(Kond K+1) :=
        mul_le_mul_of_nonneg_left hcube (by linarith)
      calc (K+1/2)*Ψ ≤ (K+1/2)*((al/a)^3 * Φ2) :=
            mul_le_mul_of_nonneg_left hΨle (by linarith)
        _ = ((K+1/2)*((al/a)^3)) * Φ2 := by ring
        _ ≤ ((K+1/2)*(Kond K+1)) * Φ2 := mul_le_mul_of_nonneg_right h1 hΦ2nn
        _ ≤ (2*(K^2+2*K+3/4)) * Φ2 := mul_le_mul_of_nonneg_right hKd hΦ2nn
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1' hA1
      have i2 := mul_le_mul_of_nonneg_left hb2 hA2
      have i3 := mul_le_mul_of_nonneg_left hb3 hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0)
          + (K^2+2*K+3/4)*(-(2*P3R 1) - 2*Φ2 + al*(1/6+e))
          + (K+1/2)*(Ψ + al*e0) + (1/4)*(-W3 + al*(1/6+e))
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2
            + ((K+1/2)*Ψ - 2*(K^2+2*K+3/4)*Φ2 - (1/4)*W3) := by
        rw [hC2def]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2
          + ((K+1/2)*Ψ - 2*(K^2+2*K+3/4)*Φ2 - (1/4)*W3) := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      linarith only [hlow, hpair, hW3nn]
    have hcp : C2*(48*K) ≤ 12*K*S + S/2 := by
      have h2 : 48*K*((K^2+K+1/2)*e0) = 24*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0v.le (show (0:ℝ) ≤ 48*K by positivity)
        have h' := mul_le_mul_of_nonneg_left he0v.ge (show (0:ℝ) ≤ 48*K by positivity)
        linarith only [h, h']
      have h3 : 48*K*((K^2+2*K+3/4)*(1/6+e))
          = 8*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e) := by ring
      have h4 : 48*K*((K+1/2)*e0) ≤ 48*K*(e*S) :=
        mul_le_mul_of_nonneg_left hA2e0 (by positivity)
      have h5 : 48*K*((1/4)*(1/6+e)) = 2*K + 12*K*e := by ring
      have hslack : 3*S/32 + (K^2+2*K+3/4)/16 + 1/64
          + (8*K*(K^2+2*K+3/4) + 2*K) ≤ 12*K*S + S/2 := by
        rw [hSdef]
        nlinarith only [sq_nonneg K, hK.le, mul_nonneg hK.le (sq_nonneg K)]
      have hexp : C2*(48*K) = 48*K*((K^2+K+1/2)*e0) + 48*K*((K^2+2*K+3/4)*(1/6+e))
          + 48*K*((K+1/2)*e0) + 48*K*((1/4)*(1/6+e)) := by rw [hC2def]; ring
      rw [hexp]
      linarith only [h2, h3, h4, h5, h24, h48, hA1e, h12e, hslack]
    have hcp' : C2*(48*K) ≤ (12*K+1)*S := by
      have h8 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [hcp, h8.le, h8.ge, hSpos.le]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K) (C := C2)
      (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcp' hD
  · -- ### FAR branch: the pole term `Ψ ≤ e` is absorbed by the extra error `ex`
    have hδlam' : lamOf q ρ₁ / Real.log (q:ℝ) ≤ δ := by rw [← hLdef]; exact hδlam
    have hfar := hfarC q hqf χ₁ ρ₁ hlam0 hlamM him hnear
    have hxz : ((↑a : ℂ) + ↑(lamOf q ρ₁)) / ((↑a : ℂ)
        + ((2 * ρ₁.im * Real.log (q:ℝ) : ℝ) : ℂ) * Complex.I)
        = (al:ℂ)/((a:ℂ) + (μ:ℂ) * Complex.I) := by
      rw [hμ, ← hLdef, hal, ← Complex.ofReal_add]
    have hfar' : Ψ ≤ e := by
      rw [hxz] at hfar
      simpa [hΨdef] using hfar
    have hb2' : SigmaP3L q L (χ₁^2) (σ + ((2*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ e + al*e0 := by linarith [hb2, hfar']
    have hb3' : SigmaP3L q L (χ₁^3) (σ + ((3*ρ₁.im : ℝ) : ℂ) * Complex.I) a (lamOf q ρ₁)
        ≤ 0 + al*(1/6 + e) := by linarith [hb3, hW3nn]
    have hexb : (K+1/2)*e ≤ al*(ex*S) := by
      have h1 : al*(ex*S) = al*(K+1/2)*e/a := by
        rw [hexdef]
        first | (field_simp; ring) | field_simp | ring_nf
      have h3a : a*(K+1/2)*e ≤ al*(K+1/2)*e := by
        have h := mul_le_mul_of_nonneg_right hale (show (0:ℝ) ≤ K+1/2 by linarith)
        have h'' := mul_le_mul_of_nonneg_right h hepos.le
        linarith [h'']
      have h3 : a*(K+1/2)*e/a ≤ al*(K+1/2)*e/a :=
        div_le_div_of_nonneg_right h3a ha.le
      have h2 : a*(K+1/2)*e/a = (K+1/2)*e := by
        first | (field_simp; ring) | field_simp
      rw [h1, ← h2]
      exact h3
    have hD : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*(C2 + ex*S) := by
      have hA0 : (0:ℝ) ≤ K^2+K+1/2 := by positivity
      have hA1 : (0:ℝ) ≤ K^2+2*K+3/4 := by positivity
      have hA2 : (0:ℝ) ≤ K+1/2 := by linarith
      have hA3 : (0:ℝ) ≤ 1/4 := by norm_num
      have i0 := mul_le_mul_of_nonneg_left hb0 hA0
      have i1 := mul_le_mul_of_nonneg_left hb1 hA1
      have i2 := mul_le_mul_of_nonneg_left hb2' hA2
      have i3 := mul_le_mul_of_nonneg_left hb3' hA3
      have hsum : (K^2+K+1/2)*(P0 + al*e0) + (K^2+2*K+3/4)*(-(2*P3R 1) + al*(1/6+e))
          + (K+1/2)*(e + al*e0) + (1/4)*(0 + al*(1/6+e))
          = (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 + (K+1/2)*e := by
        rw [hC2def]; ring
      have hlow : 0 ≤ (K^2+K+1/2)*P0 - (2*K^2+4*K+3/2)*P3R 1 + al*C2 + (K+1/2)*e := by
        linarith only [hcomb', i0, i1, i2, i3, hsum.le, hsum.ge]
      have hsum2 : al*(C2 + ex*S) = al*C2 + al*(ex*S) := by ring
      rw [hsum2]
      linarith only [hlow, hexb]
    have hcp : C2*(48*K) ≤ 12*K*S + S/2 := by
      have h2 : 48*K*((K^2+K+1/2)*e0) = 24*K*e*S := by
        have h := mul_le_mul_of_nonneg_left he0v.le (show (0:ℝ) ≤ 48*K by positivity)
        have h' := mul_le_mul_of_nonneg_left he0v.ge (show (0:ℝ) ≤ 48*K by positivity)
        linarith only [h, h']
      have h3 : 48*K*((K^2+2*K+3/4)*(1/6+e))
          = 8*K*(K^2+2*K+3/4) + 48*K*((K^2+2*K+3/4)*e) := by ring
      have h4 : 48*K*((K+1/2)*e0) ≤ 48*K*(e*S) :=
        mul_le_mul_of_nonneg_left hA2e0 (by positivity)
      have h5 : 48*K*((1/4)*(1/6+e)) = 2*K + 12*K*e := by ring
      have hslack : 3*S/32 + (K^2+2*K+3/4)/16 + 1/64
          + (8*K*(K^2+2*K+3/4) + 2*K) ≤ 12*K*S + S/2 := by
        rw [hSdef]
        nlinarith only [sq_nonneg K, hK.le, mul_nonneg hK.le (sq_nonneg K)]
      have hexp : C2*(48*K) = 48*K*((K^2+K+1/2)*e0) + 48*K*((K^2+2*K+3/4)*(1/6+e))
          + 48*K*((K+1/2)*e0) + 48*K*((1/4)*(1/6+e)) := by rw [hC2def]; ring
      rw [hexp]
      linarith only [h2, h3, h4, h5, h24, h48, hA1e, h12e, hslack]
    have hcf : (C2 + ex*S)*(48*K) ≤ (12*K+1)*S := by
      have h1 : (C2 + ex*S)*(48*K) = C2*(48*K) + 48*K*(ex*S) := by ring
      have h2 : (12*K+1)*S = 12*K*S + S := by ring
      linarith only [h1.le, h1.ge, hcp, hexSp, h2.le, h2.ge]
    exact Work.ZeroFreeTables.Rep9.ineq913_diag_of_derived_poly (a := a) (K := K)
      (C := C2 + ex*S) (ε := ε) (lam := lamOf q ρ₁) ha hK hε hlam0 hcube hcf hD

end Work.ZeroFreeTables.OffAxis
