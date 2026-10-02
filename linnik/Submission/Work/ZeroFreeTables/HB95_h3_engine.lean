/-
# ZeroFreeTables/HB95_h3_engine — the analytic engine of HB Lemma 9.5, `h = 3`

With `a = 26/10`, `P₃(X) = X + X² + (2/3)X³` (`P3R`), `σ = 1 + a/L` (`L = log q`), the five
points `s_j = σ + i·j·γ` (`γ = Im ρ₁`) and the Chebyshev expansion of (9.15)

`(3+10cos θ)²(9+10cos θ)² = 14379 + 24480cos θ + 14900cos 2θ + 6000cos 3θ + 1250cos 4θ`,

the pointwise positivity (9.16) for a *cubic* character (`χ₁³ = 1`, so `χ₁^k` cycles
`1, χ₁, χ₁², 1, χ₁`) gives

`0 ≤ 14379Σ(σ,χ₀) + 24480Σ(σ+iγ,χ₁) + 14900Σ(σ+2iγ,χ₁²) + 6000Σ(σ+3iγ,χ₀) + 1250Σ(σ+4iγ,χ₁)`

(`HB95h3.pointwise`), and the per-point bounds of HB §8.2 turn this into

`0 ≤ 14379·P₃(α/a) − 24480·P₃(1) + 40630·α·(1/8+ε)`,  `α = a + λ₁`,

once the `T`-bracket is shown to be non-positive.  The three non-principal points keep the
window zeros at the exact distance `α + iT` (`T = 3γL`):

* `s₁ = σ+iγ` with `χ₁` keeps `ρ₁` (`(s₁-ρ₁)L = α`),
* `s₂ = σ+2iγ` with `χ₁² = χ̄₁` keeps `ρ̄₁` (`(s₂-ρ̄₁)L = α + iT`),
* `s₄ = σ+4iγ` with `χ₁` keeps `ρ₁` (`(s₄-ρ₁)L = α + iT`),

so the bracket is `−14900·m·P₃(α/(α+iT)) − 1250·m·P₃(α/(α+iT)) + 6000·P₃(α/(a+iT)) ≤ 0` by
`HB95h3.h3_Tstep` (the side condition (9.17) at `a = 2.6`).  The two principal points `σ` and
`σ+3iγ` are handled by `HB95h2.principalBound`, and the `1/8` inputs by HB Lemma 3.1 at
`φ = 1/4` for characters of order `≤ 3` (`logDerivEighth3`).

This is the `h = 3` companion of `Work.ZeroFreeTables.HB95_h2_engine`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB95_h2_engine
import Submission.Work.ZeroFreeTables.HB95h3.pointwise
import Submission.Work.ZeroFreeTables.HB95h3.Tstep
import Submission.Work.ZeroFreeTables.HB95h3.h3_Tbracket
import Submission.Work.ZeroFreeTables.HB95h3.hBnum3
import Submission.Work.ZeroFreeTables.HB94.lemma3_1_free_pow
import Submission.Work.ZeroFreeTables.HB94.hbound_quarter_pow_h
import Submission.Work.LinnikAreas.area1

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Order-`3` bookkeeping -/

theorem h3_pow_three {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : orderOf χ = 3) :
    χ ^ 3 = 1 :=
  h ▸ pow_orderOf_eq_one χ

theorem h3_sq_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : orderOf χ = 3) :
    χ ^ 2 ≠ 1 := by
  intro h2
  have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [h] at hdvd
  omega

theorem h3_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : orderOf χ = 3) :
    χ⁻¹ = χ ^ 2 := by
  have h3 : χ ^ 3 = 1 := h3_pow_three χ h
  have h2 : χ ^ 2 * χ = 1 := by rw [← pow_succ]; exact h3
  exact inv_eq_of_mul_eq_one_left h2

theorem h3_order_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : orderOf χ = 3) :
    orderOf (χ ^ 2) = 3 := by
  have h3 : χ ^ 3 = 1 := h3_pow_three χ h
  have h6 : (χ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, h3, one_pow]
  have hdvd : orderOf (χ ^ 2) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h6
  have hne : orderOf (χ ^ 2) ≠ 1 :=
    fun h1 => h3_sq_ne_one χ h (orderOf_eq_one_iff.mp h1)
  rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf (χ ^ 2)) hdvd with h1 | h1
  · exact absurd h1 hne
  · exact h1

/-- A complex conjugation of a zero of `χ₁` (of order `3`) is a zero of `χ₁² = χ₁⁻¹` with the
same multiplicity. -/
theorem zeroMult_sq_conj {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (h : orderOf χ₁ = 3) :
    Work.LinnikContract.zeroMult (χ₁ ^ 2) ((starRingEnd ℂ) ρ₁)
      = Work.LinnikContract.zeroMult χ₁ ρ₁ := by
  rw [← h3_inv χ₁ h]
  exact Work.A7.zeroMult_conj_inv χ₁ ρ₁

/-- The conductor of a character of a non-zero modulus is positive, as a real number. -/
theorem conductor_cast_pos' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (0 : ℝ) < ((χ.conductor : ℕ) : ℝ) :=
  Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)

/-- The modulus of a non-principal character is at least `3`. -/
theorem three_le_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    3 ≤ χ.conductor := by
  by_contra hc
  push_neg at hc
  exact hχ (Work.LinnikAreas.eq_one_of_conductor_le_two χ (by omega))

/-- **HB Lemma 3.1 at `φ = 1/4` for characters of order `≤ 3`, threshold exposed.**  This is
`Work.ZeroFreeTables.HB95h3.logDerivEighth` with the modulus threshold `N₀` replaced by its
value `3` (its proof fixes `N₀ = 3`); the engine needs the threshold as a hypothesis, since it
cannot be read off the existential. -/
theorem logDerivEighth3 {e : ℝ} (he : 0 < e) :
    ∃ L₀ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
        (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hord : orderOf χ ≤ 3) {L : ℝ},
        3 ≤ N → L₀ ≤ L → Real.log (N : ℝ) ≤ L →
          LogDerivHyp χ δ L (1 / 8 + e) := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.ZeroFreeTables.HB94.lemma3_1_free_pow 6 (φ := (1 : ℝ) / 4) (by norm_num) he
      (Work.ZeroFreeTables.hbound_quarter_pow_h 6 (by norm_num))
  refine ⟨L₀, δ, hδ0, hδ1, ?_⟩
  intro N _inst χ hχ hprim hord L hN hL hlogN
  have h6 : χ ^ 6 = 1 := by
    have hdvd : orderOf χ ∣ 6 := by
      have hpos : 0 < orderOf χ := orderOf_pos χ
      interval_cases orderOf χ <;> norm_num
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hN3 : 3 ≤ N := hN
  have hL0 : 0 ≤ L :=
    le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) hlogN
  intro s hs1 hs2 hs3
  have key := hmain hN3 χ hχ hprim h6 hL hlogN s hs1 hs2 (le_trans hs3 (by linarith only [hL0]))
  have hc : (1 : ℝ) / 4 / 2 + e = 1 / 8 + e := by norm_num
  rw [hc] at key
  simpa only [LogDerivHyp, InvNearSum, pdiv] using key

/-- **The analytic engine of HB Lemma 9.5 for `h = 3`.**  For every `ε > 0` and all large `q`,
a cubic `χ₁` with a minimal zero `ρ₁` of `λ₁ ≤ 348/1000` satisfies the `P₃` inequality (★)
of HB (9.16):

`0 ≤ 14379·P₃(α/a) − 24480·P₃(1) + 40630·α·(1/8 + ε)`,  `a = 26/10`, `α = a + λ₁`. -/
theorem HB95_h3_engine :
    ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → orderOf χ₁ = 3 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348 : ℝ) / 1000 →
        0 ≤ 14379 * Work.ZeroFreeTables.P3R
              (((26 : ℝ) / 10 + Work.LinnikContract.lamOf q ρ₁) / ((26 : ℝ) / 10))
          - 24480 * Work.ZeroFreeTables.P3R 1
          + 40630 * ((26 : ℝ) / 10 + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε) := by
  intro ε hε
  -- ## the analytic inputs
  obtain ⟨L₀_log, δ, hδ0, hδ1, hlog⟩ := logDerivEighth3 (e := ε / 16) (by positivity)
  obtain ⟨L₀_m, hm⟩ := HB95h2.masterP3kept (a := (26 : ℝ) / 10) (δ := δ) (c := 1 / 8 + ε / 16)
      (e := ε / 16) (M := 1) (by norm_num) hδ0 hδ1 (by positivity)
  obtain ⟨L₀_i, hi⟩ := HB95h2.imprimCorr (a := (26 : ℝ) / 10) (e := ε / 16) (M := 1)
      (by norm_num) (by positivity)
  obtain ⟨L₀_p, hp⟩ := HB95h2.principalBound (a := (26 : ℝ) / 10) (e := ε / 16) (M := 1)
      (by norm_num) (by positivity)
  -- ## the threshold
  set Y : ℝ := max 64 (max (1000 / (δ ^ 2 * ε)) (1000 / δ ^ 2)) with hYdef
  set Z : ℝ := max (8 / δ) Y with hZdef
  set Lreq : ℝ := max (max L₀_log (max L₀_m (max L₀_i L₀_p))) Z with hLreqdef
  refine ⟨Nat.ceil (Real.exp Lreq) + 10, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm1 hord hle
  haveI : NeZero q := hqne
  have hq1 : 1 < q := by
    have h1 : Nat.ceil (Real.exp Lreq) + 10 ≤ q := hq
    omega
  have hexp : Real.exp Lreq ≤ (q : ℝ) := by
    have h1 : Real.exp Lreq ≤ (Nat.ceil (Real.exp Lreq) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp Lreq) + 10 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    push_cast at h2
    linarith only [hδ0, hδ1, h1, h2]
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLge : Lreq ≤ L := by
    rw [hLdef, ← Real.log_exp Lreq]
    exact Real.log_le_log (Real.exp_pos Lreq) hexp
  have hZL : Z ≤ L := le_trans (le_max_right (max L₀_log (max L₀_m (max L₀_i L₀_p))) Z) hLge
  have hYL : Y ≤ L := le_trans (le_max_right (8 / δ) Y) hZL
  have h8δ : 8 / δ ≤ L := le_trans (le_max_left (8 / δ) Y) hZL
  have h64 : (64 : ℝ) ≤ L :=
    le_trans (le_max_left (64:ℝ) (max (1000 / (δ ^ 2 * ε)) (1000 / δ ^ 2))) hYL
  have hLε : 1000 / (δ ^ 2 * ε) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right (64:ℝ) _)) hYL
  have hLδ : 1000 / δ ^ 2 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right (64:ℝ) _)) hYL
  have hL0log : L₀_log ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hL0m : L₀_m ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_left _ _)) hLge
  have hL0i : L₀_i ≤ L :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)) hLge
  have hL0p : L₀_p ≤ L :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)) hLge
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  -- ## facts about the pair
  have hZisZ : IsZ χ₁ ρ₁ := isMin1_isZ hm1.1
  have hχ1ne : χ₁ ≠ 1 := isZ_ne_one hZisZ
  have hzm : zeroMult χ₁ ρ₁ ≠ 0 := hZisZ.2.1
  have hγ1 : |ρ₁.im| ≤ 1 := hZisZ.2.2
  have hq2 : 2 ≤ q := two_le_of_ne_one χ₁ hχ1ne
  have hlam0 : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZisZ
  have hlam1 : lamOf q ρ₁ ≤ 1 := by linarith only [hδ0, hδ1, hle]
  have hlamval : lamOf q ρ₁ = (1 - ρ₁.re) * L := by rw [hLdef]; rfl
  -- ## order bookkeeping
  have h3one : χ₁ ^ 3 = 1 := h3_pow_three χ₁ hord
  have hχ2ne : χ₁ ^ 2 ≠ 1 := h3_sq_ne_one χ₁ hord
  have hord2 : orderOf (χ₁ ^ 2) = 3 := h3_order_sq χ₁ hord
  haveI hNne : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχs_ne : χ₁.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ₁ hχ1ne
  have hχs_prim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hordprim1 : orderOf (χ₁.primitiveCharacter) = 3 := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord]
  haveI hN2ne : NeZero (χ₁ ^ 2).conductor := ⟨(χ₁ ^ 2).conductor_ne_zero⟩
  have hχ2s_ne : (χ₁ ^ 2).primitiveCharacter ≠ 1 := primitiveCharacter_ne_one (χ₁ ^ 2) hχ2ne
  have hχ2s_prim : ((χ₁ ^ 2).primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 2)
  have hordprim2 : orderOf ((χ₁ ^ 2).primitiveCharacter) = 3 := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter, hord2]
  have hcond1 : 3 ≤ χ₁.conductor := three_le_conductor χ₁ hχ1ne
  have hcond2 : 3 ≤ (χ₁ ^ 2).conductor := three_le_conductor (χ₁ ^ 2) hχ2ne
  have hNq : χ₁.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ₁.conductor_dvd_level
  have hlogN : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (conductor_cast_pos' χ₁) (by exact_mod_cast hNq)
  have hN2q : (χ₁ ^ 2).conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (χ₁ ^ 2).conductor_dvd_level
  have hlogN2 : Real.log (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (conductor_cast_pos' (χ₁ ^ 2)) (by exact_mod_cast hN2q)
  have hzm_eq : ∀ u : ℂ, zeroMult χ₁ u = zeroMult χ₁.primitiveCharacter u := by
    intro u
    rw [show zeroMult χ₁.primitiveCharacter u
        = analyticOrderNatAt (DirichletCharacter.completedLFunction (χ₁.primitiveCharacter)) u from
      Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
        (χ₁.primitiveCharacter) hχs_prim u]
    rfl
  have hzm2_eq : ∀ u : ℂ, zeroMult (χ₁ ^ 2) u = zeroMult ((χ₁ ^ 2).primitiveCharacter) u := by
    intro u
    rw [show zeroMult ((χ₁ ^ 2).primitiveCharacter) u
        = analyticOrderNatAt
            (DirichletCharacter.completedLFunction ((χ₁ ^ 2).primitiveCharacter)) u from
      Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
        ((χ₁ ^ 2).primitiveCharacter) hχ2s_prim u]
    rfl
  -- ## the notation
  set A : ℝ := (26 : ℝ) / 10 with hAdef
  set α : ℝ := A + lamOf q ρ₁ with hαdef
  set γ : ℝ := ρ₁.im with hγdef
  set T : ℝ := 3 * γ * L with hTdef
  set σ : ℝ := 1 + A / L with hσdef
  set s₁ : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hs₁def
  set s₂ : ℂ := (σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I with hs₂def
  set s₃ : ℂ := (σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I with hs₃def
  set s₄ : ℂ := (σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I with hs₄def
  set S : Finset ℂ := {ρ₁} with hSdef
  set S' : Finset ℂ := {starRingEnd ℂ ρ₁} with hS'def
  have hApos : 0 < A := by rw [hAdef]; norm_num
  have hαpos : 0 < α := by rw [hαdef, hAdef]; linarith only [hδ0, hδ1, hlam0]
  have hαle4 : α ≤ 4 := by rw [hαdef, hAdef]; linarith only [hδ0, hδ1, hle]
  have hσgt : 1 < σ := by
    rw [hσdef]
    have h : 0 < A / L := div_pos hApos hLpos
    linarith only [h]
  have hLne : L ≠ 0 := hLpos.ne'
  have hLℂ : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLne
  have hAlL : A / L ≤ δ / 2 := by
    rw [div_le_iff₀ hLpos]
    have h1 : (δ / 2) * (8 / δ) = 4 := by field_simp <;> ring
    have h2 : (4:ℝ) ≤ (δ / 2) * L := by
      have h3 := mul_le_mul_of_nonneg_left h8δ (by positivity : (0:ℝ) ≤ δ / 2)
      linarith only [h3, h1]
    have h4 : A ≤ 4 := by rw [hAdef]; norm_num
    linarith only [h2, h4, hδ0, hδ1]
  -- ## the denominators
  have hρrepr : ((ρ₁.re : ℂ)) + (ρ₁.im : ℂ) * Complex.I = ρ₁ := Complex.re_add_im ρ₁
  have d0 : ((σ : ℂ) - 1) * (L : ℂ) = ((A : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
    rw [hσdef]
    push_cast
    field_simp
    ring
  have d1 : (s₁ - ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
    rw [hs₁def, ← hρrepr, hσdef, hγdef, hαdef, hlamval]
    push_cast
    field_simp
    ring
  have d2 : (s₂ - starRingEnd ℂ ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₂def, hσdef, hγdef, hαdef, hTdef, hlamval]
    rw [starRingEnd_eq]
    push_cast
    field_simp
    ring
  have d3 : (s₃ - 1) * (L : ℂ) = ((A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₃def, hσdef, hγdef, hTdef]
    push_cast
    field_simp
    ring
  have d4 : (s₄ - ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₄def, ← hρrepr, hσdef, hγdef, hαdef, hTdef, hlamval]
    push_cast
    field_simp
    ring
  -- ## the pointwise inequality (HB (9.16))
  have hpt := HB95h3.pointwise (q := q) χ₁ h3one (a := A) (lam₁ := lamOf q ρ₁)
      (σ := σ) (γ := γ) (le_of_lt hαpos) hσgt hq2
  simp only [← hs₁def, ← hs₂def, ← hs₃def, ← hs₄def] at hpt
  rw [← hLdef] at hpt
  -- ## the real/im parts of the five points
  have hγabs : |γ| ≤ 1 := by rw [hγdef]; exact hγ1
  have hre1 : s₁.re = 1 + A / L := by rw [hs₁def]; simp [hσdef]
  have him1 : |s₁.im| ≤ 4 := by
    have h : s₁.im = γ := by rw [hs₁def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre2 : s₂.re = 1 + A / L := by rw [hs₂def]; simp [hσdef]
  have him2 : |s₂.im| ≤ 4 := by
    have h : s₂.im = 2 * γ := by rw [hs₂def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre3 : s₃.re = 1 + A / L := by rw [hs₃def]; simp [hσdef]
  have him3 : |s₃.im| ≤ 4 := by
    have h : s₃.im = 3 * γ := by rw [hs₃def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre4 : s₄.re = 1 + A / L := by rw [hs₄def]; simp [hσdef]
  have him4 : |s₄.im| ≤ 4 := by
    have h : s₄.im = 4 * γ := by rw [hs₄def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs]
  have hre0 : ((σ : ℂ)).re = 1 + A / L := by simp [hσdef]
  have him0 : |((σ : ℂ)).im| ≤ 4 := by simp
  -- ## the principal-character bounds at `σ` and `σ+3iγ`
  have hp0 := hp (L := L) (lam₁ := lamOf q ρ₁) hL0p (le_of_eq hLdef.symm) hlam0 hlam1
      (s := (σ : ℂ)) hre0 him0
  have hp3 := hp (L := L) (lam₁ := lamOf q ρ₁) hL0p (le_of_eq hLdef.symm) hlam0 hlam1
      (s := s₃) hre3 him3
  have hpack : ((↑A + ↑(lamOf q ρ₁)) : ℂ) = (((A + lamOf q ρ₁ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_add]
  have e0 : (P3 ((↑A + ↑(lamOf q ρ₁)) / (((σ : ℂ) - 1) * (L : ℂ)))).re = P3R (α / A) := by
    rw [hpack, reP3_eq_P3AB (x := A + lamOf q ρ₁) (y := A) (t := 0) d0,
      Table4.P3AB_zero, ← hαdef]
  have e3 : (P3 ((↑A + ↑(lamOf q ρ₁)) / ((s₃ - 1) * (L : ℂ)))).re = Table4.P3AB α A T := by
    rw [hpack, reP3_eq_P3AB (x := A + lamOf q ρ₁) (y := A) (t := T) d3, ← hαdef]
  have hb0 : SigmaP3L q L 1 (σ : ℂ) A (lamOf q ρ₁)
      ≤ P3R (α / A) + (A + lamOf q ρ₁) * (ε / 16) := by
    rw [← e0]; exact hp0
  have hb3 : SigmaP3L q L 1 s₃ A (lamOf q ρ₁)
      ≤ Table4.P3AB α A T + (A + lamOf q ρ₁) * (ε / 16) := by
    rw [← e3]; exact hp3
  have hρ₁re_lt : ρ₁.re < 1 := by
    have hz : DirichletCharacter.completedLFunction (χ₁.primitiveCharacter) ρ₁ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (by simpa [Work.LinnikContract.zeroMult] using hzm)
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip (χ₁.primitiveCharacter)
      hχs_ne hχs_prim hz).2
  -- ## the `1/8` inputs
  have hlog1 : LogDerivHyp χ₁.primitiveCharacter δ L (1 / 8 + ε / 16) :=
    hlog χ₁.primitiveCharacter hχs_ne hχs_prim (by rw [hordprim1])
      (L := L) hcond1 hL0log hlogN
  have hlog2 : LogDerivHyp ((χ₁ ^ 2).primitiveCharacter) δ L (1 / 8 + ε / 16) :=
    hlog ((χ₁ ^ 2).primitiveCharacter) hχ2s_ne hχ2s_prim (by rw [hordprim2])
      (L := L) hcond2 hL0log hlogN2
  -- ## the imprimitivity corrections
  have hi1 := hi (χ := χ₁) hχ1ne (L := L) (lam₁ := lamOf q ρ₁)
      hL0i (le_of_eq hLdef.symm) hlam0 hlam1 (s := s₁) hre1 him1
  have hi2 := hi (χ := χ₁ ^ 2) hχ2ne (L := L) (lam₁ := lamOf q ρ₁)
      hL0i (le_of_eq hLdef.symm) hlam0 hlam1 (s := s₂) hre2 him2
  have hi4 := hi (χ := χ₁) hχ1ne (L := L) (lam₁ := lamOf q ρ₁)
      hL0i (le_of_eq hLdef.symm) hlam0 hlam1 (s := s₄) hre4 him4
  -- ## the multiplicity
  set m : ℝ := (zeroMult χ₁ ρ₁ : ℝ) with hmdef
  have hm_ge1 : 1 ≤ m := by
    rw [hmdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzm
  have hconj_re : (starRingEnd ℂ ρ₁).re = ρ₁.re := by simp
  have hconj_lt : (starRingEnd ℂ ρ₁).re < 1 := by rw [hconj_re]; exact hρ₁re_lt
  have hzm_p1 : (zeroMult (χ₁.primitiveCharacter) ρ₁ : ℝ) ≤ m := by
    rw [← hzm_eq ρ₁, ← hmdef]
  have hzm_p2 : (zeroMult ((χ₁ ^ 2).primitiveCharacter) (starRingEnd ℂ ρ₁) : ℝ) ≤ m := by
    rw [← hzm2_eq (starRingEnd ℂ ρ₁), zeroMult_sq_conj χ₁ ρ₁ hord, ← hmdef]
  -- ## the master bounds at the three non-principal points
  have hmin1 : ∀ v : ℂ, zeroMult (χ₁.primitiveCharacter) v ≠ 0 →
      (v ∈ S ∨ ‖(1 : ℂ) + (s₁.im : ℂ) * Complex.I - v‖ ≤ δ) →
      lamOf q ρ₁ ≤ (1 - v.re) * L := by
    intro v hv hcase
    have himv : |v.im| ≤ 10 := by
      rcases hcase with hvS | hvwin
      · rw [hSdef, Finset.mem_singleton] at hvS
        rw [hvS, ← hγdef]
        rw [abs_le] at hγabs ⊢
        constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
      · have h2 : |s₁.im - v.im| ≤ 1 := by
          have h3 : |((1 : ℂ) + (s₁.im : ℂ) * Complex.I - v).im| ≤ 1 :=
            le_trans (Complex.abs_im_le_norm _) (le_trans hvwin (by linarith only [hδ1]))
          simpa using h3
        have h4 : |s₁.im| ≤ 1 := by
          have h : s₁.im = γ := by rw [hs₁def]; simp
          rw [h]; exact hγabs
        rw [abs_le] at h2 h4 ⊢
        constructor <;> linarith only [h2.1, h2.2, h4.1, h4.2, hδ1, hσdef, hσgt, hAlL, h2, h4]
    have hv' : zeroMult χ₁ v ≠ 0 := by rw [hzm_eq v]; exact hv
    have hmin' := hm1.2 χ₁ v hχ1ne hv' himv
    simpa [Work.LinnikContract.lamOf, hLdef] using hmin'
  have hmin2 : ∀ v : ℂ, zeroMult ((χ₁ ^ 2).primitiveCharacter) v ≠ 0 →
      (v ∈ S' ∨ ‖(1 : ℂ) + (s₂.im : ℂ) * Complex.I - v‖ ≤ δ) →
      lamOf q ρ₁ ≤ (1 - v.re) * L := by
    intro v hv hcase
    have himv : |v.im| ≤ 10 := by
      rcases hcase with hvS | hvwin
      · rw [hS'def, Finset.mem_singleton] at hvS
        rw [hvS, Complex.conj_im, abs_neg, ← hγdef]
        rw [abs_le] at hγabs ⊢
        constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
      · have h2 : |s₂.im - v.im| ≤ 1 := by
          have h3 : |((1 : ℂ) + (s₂.im : ℂ) * Complex.I - v).im| ≤ 1 :=
            le_trans (Complex.abs_im_le_norm _) (le_trans hvwin (by linarith only [hδ1]))
          simpa using h3
        have h4 : |s₂.im| ≤ 2 := by
          have h : s₂.im = 2 * γ := by rw [hs₂def]; simp
          rw [h]; rw [abs_le] at hγabs ⊢
          constructor <;> linarith only [hγabs.1, hγabs.2, hγabs]
        rw [abs_le] at h2 h4 ⊢
        constructor <;> linarith only [h2.1, h2.2, h4.1, h4.2, hδ1, hσdef, hσgt, hAlL, h2, h4]
    have hv' : zeroMult (χ₁ ^ 2) v ≠ 0 := by rw [hzm2_eq v]; exact hv
    have hmin' := hm1.2 (χ₁ ^ 2) v hχ2ne hv' himv
    simpa [Work.LinnikContract.lamOf, hLdef] using hmin'
  have hmin4 : ∀ v : ℂ, zeroMult (χ₁.primitiveCharacter) v ≠ 0 →
      (v ∈ S ∨ ‖(1 : ℂ) + (s₄.im : ℂ) * Complex.I - v‖ ≤ δ) →
      lamOf q ρ₁ ≤ (1 - v.re) * L := by
    intro v hv hcase
    have himv : |v.im| ≤ 10 := by
      rcases hcase with hvS | hvwin
      · rw [hSdef, Finset.mem_singleton] at hvS
        rw [hvS, ← hγdef]
        rw [abs_le] at hγabs ⊢
        constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
      · have h2 : |s₄.im - v.im| ≤ 1 := by
          have h3 : |((1 : ℂ) + (s₄.im : ℂ) * Complex.I - v).im| ≤ 1 :=
            le_trans (Complex.abs_im_le_norm _) (le_trans hvwin (by linarith only [hδ1]))
          simpa using h3
        have h4 : |s₄.im| ≤ 4 := by
          have h : s₄.im = 4 * γ := by rw [hs₄def]; simp
          rw [h]; rw [abs_le] at hγabs ⊢
          constructor <;> linarith only [hγabs.1, hγabs.2, hγabs]
        rw [abs_le] at h2 h4 ⊢
        constructor <;> linarith only [h2.1, h2.2, h4.1, h4.2, hδ1, hσdef, hσgt, hAlL, h2, h4]
    have hv' : zeroMult χ₁ v ≠ 0 := by rw [hzm_eq v]; exact hv
    have hmin' := hm1.2 χ₁ v hχ1ne hv' himv
    simpa [Work.LinnikContract.lamOf, hLdef] using hmin'
  have hm1' := hm (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim (L := L)
      (lam₁ := lamOf q ρ₁) hL0m hlogN hlam0 hlam1 hlog1 S s₁ hre1 him1
  have hm2' := hm (χ := (χ₁ ^ 2).primitiveCharacter) hχ2s_ne hχ2s_prim (L := L)
      (lam₁ := lamOf q ρ₁) hL0m hlogN2 hlam0 hlam1 hlog2 S' s₂ hre2 him2
  have hm4' := hm (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim (L := L)
      (lam₁ := lamOf q ρ₁) hL0m hlogN hlam0 hlam1 hlog1 S s₄ hre4 him4
  -- ## the kept extractions
  have hK1 := HB95h2.keptExtractW (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim
      (a := A) (lam₁ := lamOf q ρ₁) (L := L) (δ := δ) (s := s₁) (S := S)
      hLpos hApos hlam0 hδ0 hre1 hmin1
  have hK2 := HB95h2.keptExtractW (χ := (χ₁ ^ 2).primitiveCharacter) hχ2s_ne hχ2s_prim
      (a := A) (lam₁ := lamOf q ρ₁) (L := L) (δ := δ) (s := s₂) (S := S')
      hLpos hApos hlam0 hδ0 hre2 hmin2
  have hK4 := HB95h2.keptExtractW (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim
      (a := A) (lam₁ := lamOf q ρ₁) (L := L) (δ := δ) (s := s₄) (S := S)
      hLpos hApos hlam0 hδ0 hre4 hmin4
  -- ## the evaluations of the kept sums
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hSsum1 : (∑ u ∈ S, (zeroMult (χ₁.primitiveCharacter) u : ℝ)
      * (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₁ - u) * (L : ℂ)))).re) = m * P3R 1 := by
    rw [hSdef, Finset.sum_singleton]
    have h1 : (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₁ - ρ₁) * (L : ℂ)))).re = P3R 1 := by
      rw [reP3_eq_P3AB (x := A + lamOf q ρ₁) (y := α) (t := 0) d1, ← hαdef,
        Table4.P3AB_zero, div_self hαne]
    rw [h1, ← hzm_eq ρ₁, ← hmdef]
  have hSsum2 : (∑ u ∈ S', (zeroMult ((χ₁ ^ 2).primitiveCharacter) u : ℝ)
      * (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₂ - u) * (L : ℂ)))).re)
      = m * Table4.P3AB α α T := by
    rw [hS'def, Finset.sum_singleton]
    have h1 : (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₂ - starRingEnd ℂ ρ₁) * (L : ℂ)))).re
        = Table4.P3AB α α T := by
      rw [reP3_eq_P3AB (x := A + lamOf q ρ₁) (y := α) (t := T) d2, ← hαdef]
    rw [h1, ← hzm2_eq (starRingEnd ℂ ρ₁), zeroMult_sq_conj χ₁ ρ₁ hord, ← hmdef]
  have hSsum4 : (∑ u ∈ S, (zeroMult (χ₁.primitiveCharacter) u : ℝ)
      * (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₄ - u) * (L : ℂ)))).re)
      = m * Table4.P3AB α α T := by
    rw [hSdef, Finset.sum_singleton]
    have h1 : (P3 (((A + lamOf q ρ₁ : ℝ) : ℂ) / ((s₄ - ρ₁) * (L : ℂ)))).re
        = Table4.P3AB α α T := by
      rw [reP3_eq_P3AB (x := A + lamOf q ρ₁) (y := α) (t := T) d4, ← hαdef]
    rw [h1, ← hzm_eq ρ₁, ← hmdef]
  have hP1 : P3R 1 = 8 / 3 := by norm_num [P3R]
  have hK1b : m * ((8 : ℝ) / 3) ≤ Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter)
      s₁ A (lamOf q ρ₁) δ S := by
    rw [← hP1, ← hSsum1]; exact hK1
  have hK2b : m * Table4.P3AB α α T ≤ Table4.keptP3Sum (χ₁ ^ 2).conductor L
      ((χ₁ ^ 2).primitiveCharacter) s₂ A (lamOf q ρ₁) δ S' := by
    rw [← hSsum2]; exact hK2
  have hK4b : m * Table4.P3AB α α T ≤ Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter)
      s₄ A (lamOf q ρ₁) δ S := by
    rw [← hSsum4]; exact hK4
  -- ## the pointwise bounds at the three non-principal points
  have hb1 : SigmaP3L q L χ₁ s₁ A (lamOf q ρ₁)
      ≤ - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (lamOf q ρ₁) δ S
        + (A + lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)
        + (A + lamOf q ρ₁) * (ε / 16)
        + ((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₁ δ u)
            * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re))) := by
    linarith only [hi1, hm1', this, hNne]
  have hb2 : SigmaP3L q L (χ₁ ^ 2) s₂ A (lamOf q ρ₁)
      ≤ - Table4.keptP3Sum (χ₁ ^ 2).conductor L ((χ₁ ^ 2).primitiveCharacter) s₂ A
            (lamOf q ρ₁) δ S'
        + (A + lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)
        + (A + lamOf q ρ₁) * (ε / 16)
        + ((A + lamOf q ρ₁) / L) * (∑ u ∈ S', (1 - P9.nearInd s₂ δ u)
            * ((zeroMult ((χ₁ ^ 2).primitiveCharacter) u : ℝ) * ((1 / (s₂ - u)).re))) := by
    linarith only [hi2, hm2', this, hN2ne]
  have hb4 : SigmaP3L q L χ₁ s₄ A (lamOf q ρ₁)
      ≤ - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₄ A (lamOf q ρ₁) δ S
        + (A + lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)
        + (A + lamOf q ρ₁) * (ε / 16)
        + ((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₄ δ u)
            * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₄ - u)).re))) := by
    linarith only [hi4, hm4', this, hNne]
  -- ## the error (far-zero) terms
  have hExbound : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s u : ℂ),
      s.re = 1 + A / L → |s.im| ≤ 4 →
      (zeroMult χ u : ℝ) ≤ m → u.re < 1 →
      ((A + lamOf q ρ₁) / L) * ((1 - P9.nearInd s δ u)
        * ((zeroMult χ u : ℝ) * ((1 / (s - u)).re)))
        ≤ ((A + lamOf q ρ₁) / L) * (16 * m / δ ^ 2) := by
    intro N _inst χ s u hsre hsim hzmle hure
    apply mul_le_mul_of_nonneg_left _
      (div_nonneg (le_of_lt hαpos) hLpos.le)
    by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
    · rw [P9.nearInd_eq_ite, if_pos hnear]
      simp only [sub_self, zero_mul]
      exact div_nonneg (by linarith only [hm_ge1]) (by positivity)
    · rw [P9.nearInd_eq_ite, if_neg hnear, sub_zero, one_mul]
      have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hnear
      have hrec := re_inv_le_of_far hδ0 hδ1.le hApos hLpos hAlL hsre hure hfar
      have hzm0 : (0 : ℝ) ≤ (zeroMult χ u : ℝ) := by positivity
      have h1 : (zeroMult χ u : ℝ) * ((1 / (s - u)).re)
          ≤ (zeroMult χ u : ℝ) * (8 / δ ^ 2) :=
        mul_le_mul_of_nonneg_left hrec hzm0
      have h2 : (zeroMult χ u : ℝ) * (8 / δ ^ 2) ≤ m * (8 / δ ^ 2) :=
        mul_le_mul_of_nonneg_right hzmle (by positivity)
      have h3 : m * (8 / δ ^ 2) ≤ 16 * m / δ ^ 2 := by
        rw [show m * (8 / δ ^ 2) = (m * 8) / δ ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [hm_ge1]
      linarith only [h1, h2, h3, _inst]
  have hEx1 : ((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₁ δ u)
        * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))
      ≤ ((A + lamOf q ρ₁) / L) * (16 * m / δ ^ 2) := by
    rw [hSdef, Finset.sum_singleton]
    exact hExbound (χ₁.primitiveCharacter) s₁ ρ₁ hre1 him1 hzm_p1 hρ₁re_lt
  have hEx2 : ((A + lamOf q ρ₁) / L) * (∑ u ∈ S', (1 - P9.nearInd s₂ δ u)
        * ((zeroMult ((χ₁ ^ 2).primitiveCharacter) u : ℝ) * ((1 / (s₂ - u)).re)))
      ≤ ((A + lamOf q ρ₁) / L) * (16 * m / δ ^ 2) := by
    rw [hS'def, Finset.sum_singleton]
    exact hExbound ((χ₁ ^ 2).primitiveCharacter) s₂ (starRingEnd ℂ ρ₁) hre2 him2 hzm_p2 hconj_lt
  have hEx4 : ((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₄ δ u)
        * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₄ - u)).re)))
      ≤ ((A + lamOf q ρ₁) / L) * (16 * m / δ ^ 2) := by
    rw [hSdef, Finset.sum_singleton]
    exact hExbound (χ₁.primitiveCharacter) s₄ ρ₁ hre4 him4 hzm_p1 hρ₁re_lt
  have hδ2L : 1000 ≤ δ ^ 2 * L := by
    have h := (div_le_iff₀ (show (0:ℝ) < δ ^ 2 by positivity)).mp hLδ
    rw [mul_comm L (δ ^ 2)] at h
    exact h
  have hδ2εL : 1000 ≤ δ ^ 2 * ε * L := by
    have h := (div_le_iff₀ (show (0:ℝ) < δ ^ 2 * ε by positivity)).mp hLε
    rw [mul_comm L (δ ^ 2 * ε)] at h
    exact h
  have hExComb : 24480 * (((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₁ δ u)
        * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re))))
      + 14900 * (((A + lamOf q ρ₁) / L) * (∑ u ∈ S', (1 - P9.nearInd s₂ δ u)
        * ((zeroMult ((χ₁ ^ 2).primitiveCharacter) u : ℝ) * ((1 / (s₂ - u)).re))))
      + 1250 * (((A + lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - P9.nearInd s₄ δ u)
        * ((zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₄ - u)).re))))
      ≤ 65280 * (m - 1) + 31738 * (A + lamOf q ρ₁) * ε :=
    HB95h3.hBnum3 hαpos hLpos hδ0 hε hαle4 hm_ge1 ⟨_, hmdef⟩ hEx1 hEx2 hEx4 hδ2L hδ2εL
  -- ## the `T`-bracket
  have hTbr := HB95h3.h3_Tbracket (lam := lamOf q ρ₁) (T := T) (m := m)
      hlam0 hle hm_ge1 hK1b hK2b hK4b
  rw [← hAdef, ← hαdef] at hTbr
  -- ## the assembly
  have t0 := mul_le_mul_of_nonneg_left hb0 (show (0:ℝ) ≤ 14379 by norm_num)
  have t1 := mul_le_mul_of_nonneg_left hb1 (show (0:ℝ) ≤ 24480 by norm_num)
  have t2 := mul_le_mul_of_nonneg_left hb2 (show (0:ℝ) ≤ 14900 by norm_num)
  have t3 := mul_le_mul_of_nonneg_left hb3 (show (0:ℝ) ≤ 6000 by norm_num)
  have t4 := mul_le_mul_of_nonneg_left hb4 (show (0:ℝ) ≤ 1250 by norm_num)
  have hraw := le_trans hpt
    (add_le_add (add_le_add (add_le_add (add_le_add t0 t1) t2) t3) t4)
  have hkey : 0 ≤ 14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3))
      + 40630 * ((A + lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16))
      + 61009 * ((A + lamOf q ρ₁) * (ε / 16))
      + (65280 * (m - 1) + 31738 * (A + lamOf q ρ₁) * ε) := by
    linarith only [hraw, hTbr, hExComb, hNne, hN2ne]
  rw [← hαdef] at hkey
  have hgoal : 0 ≤ 14379 * P3R (α / A) - 24480 * P3R 1 + 40630 * α * (1 / 8 + ε) := by
    rw [hP1]
    have hαε : 0 ≤ α * ε := mul_nonneg hαpos.le hε.le
    linarith only [hkey, hαε]
  exact hgoal

end Work.ZeroFreeTables
