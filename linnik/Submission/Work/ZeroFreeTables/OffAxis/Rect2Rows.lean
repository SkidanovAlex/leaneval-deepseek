/-
# ZeroFreeTables/OffAxis — `Rect2Rows`

The four row reductions of the height-`L` HB Lemma 9.4 (`OffAxis/RectLam2`).  Each takes the
corresponding height-`L` engine *as an explicit hypothesis* (the interfaces `Engine62`,
`Engine93`, `Engine92` below, which are the conclusions of `hbLemma6_2_engine_H`,
`hbLemma9_3_engine_H`, `hbLemma9_2_engine_H` after the supplies have been plugged in); the
assembly `OffAxis/RectLam2` instantiates them.

* `rowSmall` — HB Lemma 6.2 with the unconditional `ψ = 3·(1/6) = 1/2`
  (`HB94.L52supply16`) on the region `λ₁ ≤ 0.348`, `λ₂ ≤ 0.701` (`certA_348_701`);
* `row62C3` — HB §9's `(C3)` case, `ψ = 3·(1/8) = 3/8`, supplied by `χ ^ 60 = 1`
  (`HB94.L52supply_pow`), on the Table 10 row `(0.702, 0.702)` (`table10_62_cert`);
* `row93` — HB Lemma 9.3 (the reversed-role Table 9) on the row `(0.702, 0.702)`
  (`table10_93_cert`);
* `row92` — HB Lemma 9.2 (Table 9) on the row `(0.704, 0.704)` (`P9F.rowcontra_0704_0704`),
  whose values dominate Table 10's `(0.702, 0.702)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.Rect2Cert
import Submission.Work.ZeroFreeTables.table10_62_cert
import Submission.Work.ZeroFreeTables.table10_93_cert
import Submission.Work.ZeroFreeTables.P9F.table9_top
import Submission.Work.ZeroFreeTables.P9F.table9_rows
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- The conclusion of `hbLemma6_2_engine_H` (at a fixed `q`), with the four supplies plugged
in as explicit `L52Hyp` hypotheses. -/
def Engine62 {q : ℕ} [NeZero q] (c δ H W : ℝ) (T : Work.ZeroFreeTables.TestFn) : Prop :=
  ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
    [NeZero χ₁.conductor] [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor]
    [NeZero (χ₁ * χ₂⁻¹).conductor],
    Commons.NumberTheory.Linnik.L52Hyp χ₁ c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp χ₂ c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) c (1/1000000) δ →
    IsMinWideAt H W χ₁ ρ₁ →
    zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → |ρ₂.im| ≤ H → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
    lamOf q ρ₁ ≤ 1 → lamOf q ρ₂ ≤ 1 →
    0 ≤ T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁)
        + T.f 0 * (3 * (c + 1/1000000))

/-- The conclusion of `hbLemma9_3_engine_H` (at a fixed `q`), with the `1/6` supply as an
explicit hypothesis. -/
def Engine93 {q : ℕ} [NeZero q] (δ H W : ℝ) (T : Work.ZeroFreeTables.TestFn) (k : ℝ) : Prop :=
  ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
    (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) →
    IsMinWideAt H W χ₁ ρ₁ →
    zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → |ρ₂.im| ≤ H → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
    χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
    lamOf q ρ₁ ≤ 1 → lamOf q ρ₂ ≤ 1 →
    0 ≤ (k ^ 2 + 1/2) * (T.F (-(lamOf q ρ₁)) - T.F 0) - 2 * k * T.F (lamOf q ρ₂ - lamOf q ρ₁)
        + T.f 0 * ((k ^ 2 + 4 * k + 3/2) * ((1:ℝ)/6 + 1/1000000))

/-- The conclusion of `hbLemma9_2_engine_H` (at a fixed `q`) in the `La`-normal form used by the
Table 9 certificates. -/
def Engine92 {q : ℕ} [NeZero q] (δ H W θ lam : ℝ) (k : ℝ) : Prop :=
  ∀ (χ₁ χj : DirichletCharacter ℂ q) (ρ₁ ρj : ℂ),
    (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) →
    IsMinWideAt H W χ₁ ρ₁ →
    zeroMult χj ρj ≠ 0 → χj ≠ 1 → |ρj.im| ≤ H →
    χj ≠ χ₁ → χj ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χj → χ₁ ^ 2 ≠ χj⁻¹ →
    lamOf q ρ₁ ≤ 2 → lamOf q ρj ≤ 2 → 2 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) →
    0 ≤ (k ^ 2 + 1/2) * (P9F.La θ lam (lamOf q ρ₁) - P9F.La θ lam (lamOf q ρ₁ - lamOf q ρj))
        - 2 * k * P9F.La θ lam 0
        + tf71f θ lam 0 * ((k ^ 2 + 4 * k + 3/2) * ((1:ℝ)/6 + 1/1000000))

/-! ## The small-`λ₁` route (`c = 1/6`) -/

theorem rowSmall {q : ℕ} [NeZero q] {δ H W : ℝ}
    (hE : Engine62 (q := q) ((1:ℝ)/6) δ H W (Work.ZeroFreeTables.tf72T (17/20) (by norm_num)))
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hzm₂ : zeroMult χ₂ ρ₂ ≠ 0) (hχ₂ : χ₂ ≠ 1)
    (hγ₂ : |ρ₂.im| ≤ H) (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hle1 : lamOf q ρ₁ ≤ 348/1000) (hle2 : lamOf q ρ₂ ≤ 701/1000)
    (hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂)
    (hL52 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) : False := by
  haveI i1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI i2 : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI i3 : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI i4 : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  have hneA : χ₁ * χ₂ ≠ 1 := fun h => hne2 (eq_inv_of_mul_eq_one_right h)
  have hneB : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hne1 ((mul_inv_eq_one.mp h).symm)
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ (hL52 χ₁ hmin.1) (hL52 χ₂ hχ₂)
    (hL52 (χ₁ * χ₂) hneA) (hL52 (χ₁ * χ₂⁻¹) hneB)
    hmin hzm₂ hχ₂ hγ₂ hne1 hne2 (by linarith) (by linarith)
  exact absurd hcore (not_le.mpr (certA_348_701 (lamOf q ρ₁) (lamOf q ρ₂) hle1 hlam12 hle2))

/-! ## The `(C3)` route (`c = 1/8`, `χ ^ 60 = 1`) -/

theorem row62C3 {q : ℕ} [NeZero q] {δ H W lam : ℝ} (hl : 0 < lam)
    (hE : Engine62 (q := q) ((1:ℝ)/8) δ H W (Work.ZeroFreeTables.tf72T lam hl))
    (hcert : ∀ u v : ℝ, u ≤ 702/1000 → u ≤ v → v ≤ 702/1000 →
      (Work.ZeroFreeTables.tf72T lam hl).F (-u) - (Work.ZeroFreeTables.tf72T lam hl).F 0
        - (Work.ZeroFreeTables.tf72T lam hl).F (v - u)
        + (Work.ZeroFreeTables.tf72T lam hl).f 0 * (3 * ((1:ℝ)/8 + 1/1000000)) < 0)
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ} [NeZero χ₁.conductor]
    [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₁ * χ₂⁻¹).conductor]
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hzm₂ : zeroMult χ₂ ρ₂ ≠ 0) (hχ₂ : χ₂ ≠ 1)
    (hγ₂ : |ρ₂.im| ≤ H) (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hl1 : lamOf q ρ₁ ≤ 702/1000) (hl2 : lamOf q ρ₂ ≤ 702/1000)
    (hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂)
    (hL52₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ ((1:ℝ)/8) (1/1000000) δ)
    (hL52₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ ((1:ℝ)/8) (1/1000000) δ)
    (hL52A : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) ((1:ℝ)/8) (1/1000000) δ)
    (hL52B : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) ((1:ℝ)/8) (1/1000000) δ) : False := by
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ hL52₁ hL52₂ hL52A hL52B hmin hzm₂ hχ₂ hγ₂ hne1 hne2
    (by linarith) (by linarith)
  exact absurd hcore (not_le.mpr (hcert (lamOf q ρ₁) (lamOf q ρ₂) hl1 hlam12 hl2))

/-! ## The Lemma 9.3 route -/

theorem row93 {q : ℕ} [NeZero q] {δ H W lam k : ℝ} (hl : 0 < lam) (hk : 0 ≤ k)
    (hE : Engine93 (q := q) δ H W (Work.ZeroFreeTables.tf72T lam hl) k)
    (hcert : ∀ u v : ℝ, 348/1000 ≤ u → u ≤ 702/1000 → u ≤ v → v ≤ 702/1000 →
      (k ^ 2 + 1/2) * ((Work.ZeroFreeTables.tf72T lam hl).F (-u)
          - (Work.ZeroFreeTables.tf72T lam hl).F 0)
        - 2 * k * (Work.ZeroFreeTables.tf72T lam hl).F (v - u)
        + (Work.ZeroFreeTables.tf72T lam hl).f 0
            * ((k ^ 2 + 4 * k + 3/2) * ((1:ℝ)/6 + 1/1000000)) < 0)
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hzm₂ : zeroMult χ₂ ρ₂ ≠ 0) (hχ₂ : χ₂ ≠ 1)
    (hγ₂ : |ρ₂.im| ≤ H) (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (h348 : 348/1000 ≤ lamOf q ρ₁) (hl1 : lamOf q ρ₁ ≤ 702/1000)
    (hl2 : lamOf q ρ₂ ≤ 702/1000) (hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂)
    (hcsq : χ₂ ^ 2 ≠ 1) (hcsq1 : χ₂ ^ 2 ≠ χ₁) (hcsq2 : χ₂ ^ 2 ≠ χ₁⁻¹)
    (hL52 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) : False := by
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ hL52 hmin hzm₂ hχ₂ hγ₂ hne1 hne2 hcsq hcsq1 hcsq2
    (by linarith) (by linarith)
  exact absurd hcore (not_le.mpr (hcert (lamOf q ρ₁) (lamOf q ρ₂) h348 hl1 hlam12 hl2))

/-! ## The Lemma 9.2 route -/

theorem row92 {q : ℕ} [NeZero q] {δ H W θ lam : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam)
    (hE : Engine92 (q := q) δ H W θ lam (107/125))
    (hcert : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ (88/125 : ℝ) → laj ≤ (88/125 : ℝ) →
      0 ≤ ((107/125 : ℝ) ^ 2 + 1/2) * (P9F.La θ lam la1 - P9F.La θ lam (la1 - laj))
        - 2 * (107/125 : ℝ) * P9F.La θ lam 0
        + tf71f θ lam 0 * (2762098309/2929687500 : ℝ) → False)
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt H W χ₁ ρ₁) (hzm₂ : zeroMult χ₂ ρ₂ ≠ 0) (hχ₂ : χ₂ ≠ 1)
    (hγ₂ : |ρ₂.im| ≤ H) (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hsq : χ₁ ^ 2 ≠ 1) (hsq1 : χ₁ ^ 2 ≠ χ₂) (hsq2 : χ₁ ^ 2 ≠ χ₂⁻¹)
    (h0le : 0 ≤ lamOf q ρ₁) (hle1 : lamOf q ρ₁ ≤ 88/125) (hle2 : lamOf q ρ₂ ≤ 88/125)
    (hL52 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (hsqrt : 2 ≤ Real.sqrt (Real.log (Real.log (q:ℝ)))) : False := by
  have h2₁ : lamOf q ρ₁ ≤ 2 := by linarith
  have h2₂ : lamOf q ρ₂ ≤ 2 := by linarith
  have hE' := hE χ₁ χ₂ ρ₁ ρ₂ hL52 hmin hzm₂ hχ₂ hγ₂ hne1 hne2 hsq hsq1 hsq2 h2₁ h2₂ hsqrt
  have hsl : ((107/125 : ℝ) ^ 2 + 4 * (107/125 : ℝ) + 3/2) * ((1:ℝ)/6 + 1/1000000)
      ≤ (2762098309/2929687500 : ℝ) := by norm_num
  have hf0 : 0 ≤ tf71f θ lam 0 := tf71f_nonneg θ lam hθ0 hθπ hlam 0
  exact hcert h0le hle1 hle2 (by
    have := hE'
    linarith [this, mul_nonneg hf0 (sub_nonneg.mpr hsl)])

end Work.ZeroFreeTables.OffAxis
