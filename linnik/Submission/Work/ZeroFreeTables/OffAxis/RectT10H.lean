/-
# ZeroFreeTables/OffAxis — `RectT10H`

**HB Table 10 (`λ₂` in the complex case) at rectangle height `L`**, in the form the off-axis
assembly consumes it: for `L ≥ 1` there is `q₀` such that for `q ≥ q₀` and a pair
`(χ₁, ρ₁)` carrying the height-`L` numbering `IsRectMin L χ₁ ρ₁` with `1 < |ρ₁.im|` and
`λ₁ ≥ 0.348`, every row `p` of `hbTable10` with `λ₁ ≤ p.1` satisfies `Lam2BoundH L χ₁ p.2`:
every zero of height `≤ L` of a character `χ ∉ {χ₁, χ₁⁻¹}` has `λ ≥ p.2`.

The mathematical content is HB's Lemma 9.4 (Table 10 via Lemma 9.3, with HB Lemma 6.2 for
small orders) run at rectangle height `L`; the on-axis proof is
`Submission/Work/ZeroFreeTables/HBLemma9_4_proof.lean` with its `HB94/rowcontra*` components,
and the height-`L` engines are `OffAxis/hbLemma{9_2,9_3,6_2}_engine_H`.  The three routes for
the second zero `ρ₂` (of a character `χ₂ ∉ {χ₁, χ₁⁻¹}` at height `≤ L`, `λ₂ ≤ p.2`) are, with
`hA := χ₁² ∈ {1,χ₂,χ₂⁻¹}` and `hB := χ₂² ∈ {1,χ₁,χ₁⁻¹}`:

* `¬hA`: HB Lemma 9.2 (Table 9), the certificates `P9F.rowcontra_*`, dispatched over the twenty
  rows of `hbTable10` in `row92_all_H`;
* `hA`, `¬hB`: HB Lemma 9.3 (`table10_93_cert`), in `row93_all_H`;
* `hA`, `hB`: the `(C3)` case, HB Lemma 6.2 with `ψ = 3/8` (`χ₁^60 = χ₂^60 = 1`,
  `table10_62_cert`), in `row62_all_H`.

Since `q₀` may depend on `L`, the large-`q` threshold absorbs the hypotheses `L ≤ Real.log q`
and `2 ≤ √(log log q)` that the engines need.  The hypothesis `λ₁ ≥ 0.348` (HB Lemma 9.5 at
rectangle height) removes the small-`λ₁` routes of the on-axis proof (`λ₁ < 0.348` is the case
covered there by HB Theorem 1 + Table 7 and by Lemma 6.2 with `ψ = 1/2`), and it also removes
the first row `(0.34, 0.929)` of Table 10, whose first coordinate is below `0.348`.

Every ingredient is `sorry`-free.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Tables
import Submission.Work.ZeroFreeTables.OffAxis.RectLam2
import Submission.Work.ZeroFreeTables.HBLemma9_4_proof

namespace Work.ZeroFreeTables.OffAxis

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract
open Work.ZeroFreeTables

/-! ## The three height-`L` engines as interfaces

Each is the conclusion of the corresponding `OffAxis.hbLemma*_engine_H` at `H = L`, `W = 10 * L`,
`ε = 1/1000000`, with the `c` of the route. -/

/-- The conclusion of `hbLemma6_2_engine_H` at `H = L`, `W = 10 * L`. -/
def Eng62H {q : ℕ} [NeZero q] (T : TestFn) (c δ L : ℝ) : Prop :=
  ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
    [NeZero χ₁.conductor] [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor]
    [NeZero (χ₁ * χ₂⁻¹).conductor],
    L ≤ Real.log (q : ℝ) →
    Commons.NumberTheory.Linnik.L52Hyp χ₁ c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp χ₂ c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c (1/1000000) δ →
    Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) c (1/1000000) δ →
    IsMinWideAt L (10 * L) χ₁ ρ₁ →
    zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → |ρ₂.im| ≤ L →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
    lamOf q ρ₁ ≤ 1 → lamOf q ρ₂ ≤ 1 →
    0 ≤ T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁)
        + T.f 0 * (3 * (c + 1/1000000))

/-- The conclusion of `hbLemma9_3_engine_H` at `H = L`, `W = 10 * L`, `c = 1/6`. -/
def Eng93H {q : ℕ} [NeZero q] (T : TestFn) (k δ L : ℝ) : Prop :=
  ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
    (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) →
    L ≤ Real.log (q : ℝ) →
    IsMinWideAt L (10 * L) χ₁ ρ₁ →
    zeroMult χ₂ ρ₂ ≠ 0 → χ₂ ≠ 1 → |ρ₂.im| ≤ L →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
    lamOf q ρ₁ ≤ 1 → lamOf q ρ₂ ≤ 1 →
    0 ≤ (k ^ 2 + 1 / 2) * (T.F (-(lamOf q ρ₁)) - T.F 0) -
          2 * k * T.F (lamOf q ρ₂ - lamOf q ρ₁) +
          T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000))

/-- The conclusion of `hbLemma9_2_engine_H` at `H = L`, `W = 10 * L`, `c = 1/6`. -/
def Eng92H {q : ℕ} [NeZero q] (T : TestFn) (k δ L : ℝ) : Prop :=
  ∀ (χ₁ χj : DirichletCharacter ℂ q) (ρ₁ ρj : ℂ),
    (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ) →
    L ≤ Real.log (q : ℝ) →
    IsMinWideAt L (10 * L) χ₁ ρ₁ →
    zeroMult χj ρj ≠ 0 → χj ≠ 1 → |ρj.im| ≤ L →
    χj ≠ χ₁ → χj ≠ χ₁⁻¹ → χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χj → χ₁ ^ 2 ≠ χj⁻¹ →
    lamOf q ρ₁ ≤ 2 → lamOf q ρj ≤ 2 →
    2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
    0 ≤ (k ^ 2 + 1 / 2) * (T.F (-(lamOf q ρ₁)) - T.F (lamOf q ρj - lamOf q ρ₁)) -
          2 * k * T.F 0 +
          T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000))

/-! ## Threshold bookkeeping -/

/-- `q ≥ ⌈exp L⌉ + 1` forces `L ≤ log q`. -/
theorem rectT10H_le_log_of_ceil_exp_le {q N : ℕ} {L : ℝ} (hN : Nat.ceil (Real.exp L) + 1 ≤ N)
    (hq : N ≤ q) : L ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp L ≤ (q : ℝ) := by
    have h2 : Real.exp L ≤ ((Nat.ceil (Real.exp L) : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (Real.exp L) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans hN hq)
    push_cast at h3
    linarith
  have h := Real.log_le_log (Real.exp_pos L) h1
  rwa [Real.log_exp] at h

/-- `q ≥ ⌈exp (exp 4)⌉ + 1` forces `4 ≤ log log q`. -/
theorem four_le_loglog_of_ceil_exp_exp_le {q N : ℕ}
    (hN : Nat.ceil (Real.exp (Real.exp 4)) + 1 ≤ N) (hq : N ≤ q) :
    (4:ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
  have h1 : Real.exp (Real.exp 4) ≤ (q : ℝ) := by
    have h2 : Real.exp (Real.exp 4) ≤ ((Nat.ceil (Real.exp (Real.exp 4)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h3 : ((Nat.ceil (Real.exp (Real.exp 4)) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (le_trans hN hq)
    push_cast at h3
    linarith
  have h4 : Real.exp 4 ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 4)) h1
    rwa [Real.log_exp] at h
  have h5 : Real.log (Real.exp 4) ≤ Real.log (Real.log (q : ℝ)) :=
    Real.log_le_log (Real.exp_pos 4) h4
  rwa [Real.log_exp] at h5

theorem two_le_sqrt_loglog {q : ℕ} (h : (4:ℝ) ≤ Real.log (Real.log (q : ℝ))) :
    2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
  have h' := Real.sqrt_le_sqrt h
  rwa [show Real.sqrt 4 = 2 by norm_num] at h'

/-! ## Instantiating the three engines -/

theorem eng92_of_engine {δ L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L)
    (θ lam k : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k) :
    ∃ qE : ℕ, ∀ q : ℕ, qE ≤ q → ∀ [NeZero q],
      Eng92H (q := q) (tf71T θ lam hθ0 hθπ hlam) k δ L := by
  have hH0 : (0:ℝ) ≤ L := by linarith
  have h3L : 3 * L + δ ≤ 10 * L := by linarith
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine_H (tf71T θ lam hθ0 hθπ hlam) k ((1:ℝ)/6) (1/1000000)
    δ L (10 * L) hk (by norm_num) hδ0 hδ1 hH0 h3L
  refine ⟨qE, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂
  exact hqE q hq χ₁ χ₂ ρ₁ ρ₂

theorem eng93_of_engine {δ L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L)
    {T : TestFn} {k : ℝ} (hk : 0 ≤ k) :
    ∃ qE : ℕ, ∀ q : ℕ, qE ≤ q → ∀ [NeZero q], Eng93H (q := q) T k δ L := by
  have hH0 : (0:ℝ) ≤ L := by linarith
  have h3L : 3 * L + δ ≤ 10 * L := by linarith
  obtain ⟨qE, hqE⟩ := hbLemma9_3_engine_H T k ((1:ℝ)/6) (1/1000000) δ L (10 * L)
    hk (by norm_num) hδ0 hδ1 hH0 h3L
  refine ⟨qE, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂
  exact hqE q hq χ₁ χ₂ ρ₁ ρ₂

theorem eng62_of_engine {δ L : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L)
    {T : TestFn} {c : ℝ} (hc : 0 < c) :
    ∃ qE : ℕ, ∀ q : ℕ, qE ≤ q → ∀ [NeZero q], Eng62H (q := q) T c δ L := by
  have hH0 : (0:ℝ) ≤ L := by linarith
  have h3L : 3 * L + δ ≤ 10 * L := by linarith
  obtain ⟨qE, hqE⟩ := hbLemma6_2_engine_H T c (1/1000000) δ L (10 * L)
    (by norm_num) hδ0 hδ1 hH0 h3L
  refine ⟨qE, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ _i1 _i2 _i3 _i4
  exact hqE q hq χ₁ χ₂ ρ₁ ρ₂

/-! ## The three certificate steps, at a fixed `q` -/

/-- **The HB Lemma 9.2 step at height `L`.**  Given the height-`L` engine and a Table-9
certificate (in the form of the `P9F.rowcontra_*` lemmas, i.e. in terms of `P9F.La` and
`tf71f`), a pair of zeros `ρ₁` (the rectangle minimiser) and `ρ₂` (of a character
`χ₂ ∉ {χ₁, χ₁⁻¹}` with `χ₁² ∉ {1, χ₂, χ₂⁻¹}`), with `λ₁ ≥ 0.348`, `λ₁ ≤ a`, `λ₂ ≤ c`, is
impossible. -/
theorem row92_at {q : ℕ} [NeZero q] {δ L : ℝ} {θ lam k slack a c : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k)
    (ha2 : a ≤ 2) (hc2 : c ≤ 2)
    (hsl : (k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000) ≤ slack)
    (hcert : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1 / 2) * (P9F.La θ lam la1 - P9F.La θ lam (la1 - laj)) -
          2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack → False)
    (hE : Eng92H (q := q) (tf71T θ lam hθ0 hθπ hlam) k δ L)
    (hL52 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (hlogq : L ≤ Real.log (q : ℝ))
    (hsqrt : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))))
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt L (10 * L) χ₁ ρ₁) (hZ2 : IsZAt L χ₂ ρ₂)
    (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hsq : χ₁ ^ 2 ≠ 1) (hsq1 : χ₁ ^ 2 ≠ χ₂) (hsq2 : χ₁ ^ 2 ≠ χ₂⁻¹)
    (h0le : 0 ≤ lamOf q ρ₁) (hle1 : lamOf q ρ₁ ≤ a) (hle2 : lamOf q ρ₂ ≤ c) : False := by
  have h21 : lamOf q ρ₁ ≤ 2 := le_trans hle1 ha2
  have h22 : lamOf q ρ₂ ≤ 2 := le_trans hle2 hc2
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ hL52 hlogq hmin hZ2.2.1 hZ2.1 hZ2.2.2 hne1 hne2 hsq hsq1 hsq2
    h21 h22 hsqrt
  rw [P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (-(lamOf q ρ₁)),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam (lamOf q ρ₂ - lamOf q ρ₁),
      P9F.tf71T_F_eq_La θ lam hθ0 hθπ hlam 0] at hcore
  simp only [neg_neg, neg_sub, neg_zero, tf71T] at hcore
  have hf0 : 0 ≤ tf71f θ lam 0 := tf71f_nonneg θ lam hθ0 hθπ hlam 0
  exact hcert h0le hle1 hle2 (by linarith [hcore, mul_nonneg hf0 (sub_nonneg.mpr hsl)])

/-- **The HB Lemma 9.3 step at height `L`.** -/
theorem row93_at {q : ℕ} [NeZero q] {δ L a b lam k : ℝ} (hl : 0 < lam)
    (hE : Eng93H (q := q) (tf72T lam hl) k δ L)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hcert : ∀ u v : ℝ, 348/1000 ≤ u → u ≤ a → u ≤ v → v ≤ b →
      (k ^ 2 + 1 / 2) * ((tf72T lam hl).F (-u) - (tf72T lam hl).F 0) -
        2 * k * (tf72T lam hl).F (v - u) + (tf72T lam hl).f 0 *
          ((k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000)) < 0)
    (hL52 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (hlogq : L ≤ Real.log (q : ℝ)) (hL : 1 ≤ L)
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt L (10 * L) χ₁ ρ₁) (hZ2 : IsZAt L χ₂ ρ₂)
    (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hcsq : χ₂ ^ 2 ≠ 1) (hcsq1 : χ₂ ^ 2 ≠ χ₁) (hcsq2 : χ₂ ^ 2 ≠ χ₁⁻¹)
    (h348 : 348/1000 ≤ lamOf q ρ₁) (hle1 : lamOf q ρ₁ ≤ a) (hle2 : lamOf q ρ₂ ≤ b) : False := by
  have h1 : lamOf q ρ₁ ≤ 1 := le_trans hle1 ha1
  have h2 : lamOf q ρ₂ ≤ 1 := le_trans hle2 hb1
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hmin.2.2.2 χ₂ ρ₂ hZ2.1 hZ2.2.1 (le_trans hZ2.2.2 (by linarith))
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ hL52 hlogq hmin hZ2.2.1 hZ2.1 hZ2.2.2 hne1 hne2 hcsq hcsq1 hcsq2 h1 h2
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) h348 hle1 hlam12 hle2
  linarith only [hcore, hneg]

/-- **The `(C3)` step at height `L`** (HB Lemma 6.2 with `ψ = 3/8`): both relations
`χ₁² ∈ {1, χ₂, χ₂⁻¹}` and `χ₂² ∈ {1, χ₁, χ₁⁻¹}` hold, so `χ₁⁶⁰ = χ₂⁶⁰ = 1`. -/
theorem row62_at {q : ℕ} [NeZero q] {δ L a b lam : ℝ} (hl : 0 < lam)
    (hE : Eng62H (q := q) (tf72T lam hl) ((1:ℝ)/8) δ L)
    (hL8 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ ^ 60 = 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    (hlogq : L ≤ Real.log (q : ℝ)) (hL : 1 ≤ L)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hcert : ∀ u v : ℝ, u ≤ a → u ≤ v → v ≤ b →
      (tf72T lam hl).F (-u) - (tf72T lam hl).F 0 - (tf72T lam hl).F (v - u)
        + (tf72T lam hl).f 0 * (3 * ((1:ℝ)/8 + 1/1000000)) < 0)
    {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hmin : IsMinWideAt L (10 * L) χ₁ ρ₁) (hZ2 : IsZAt L χ₂ ρ₂)
    (hne1 : χ₂ ≠ χ₁) (hne2 : χ₂ ≠ χ₁⁻¹)
    (hA : χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹)
    (hB : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹)
    (ha : lamOf q ρ₁ ≤ a) (hb : lamOf q ρ₂ ≤ b) : False := by
  haveI i1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI i2 : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI i3 : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI i4 : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  obtain ⟨ha60, hb60⟩ := pow60_of_relations hA hB
  have hA60 : (χ₁ * χ₂) ^ 60 = 1 := by rw [mul_pow, ha60, hb60, one_mul]
  have hB60 : (χ₁ * χ₂⁻¹) ^ 60 = 1 := by rw [mul_pow, ha60, inv_pow, hb60, one_mul, inv_one]
  have hneA : χ₁ * χ₂ ≠ 1 := fun h => hne2 (eq_inv_of_mul_eq_one_right h)
  have hneB : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hne1 ((mul_inv_eq_one.mp h).symm)
  have h1 : lamOf q ρ₁ ≤ 1 := le_trans ha ha1
  have h2 : lamOf q ρ₂ ≤ 1 := le_trans hb hb1
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ :=
    hmin.2.2.2 χ₂ ρ₂ hZ2.1 hZ2.2.1 (le_trans hZ2.2.2 (by linarith))
  have hcore := hE χ₁ χ₂ ρ₁ ρ₂ hlogq (hL8 χ₁ hmin.1 ha60) (hL8 χ₂ hZ2.1 hb60)
    (hL8 (χ₁ * χ₂) hneA hA60) (hL8 (χ₁ * χ₂⁻¹) hneB hB60)
    hmin hZ2.2.1 hZ2.1 hZ2.2.2 hne1 hne2 h1 h2
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) ha hlam12 hb
  linarith only [hcore, hneg]

/-! ## The three routes, with their large-`q` thresholds -/

/-- **The HB Lemma 9.2 route for one row**: from the Table-9 certificate at `(a, c)` (region
`[0, a] × (-∞, c]`), a threshold `N` beyond which no pair with `λ₁ ∈ [0.348, a]`, `λ₂ ≤ c` and
`χ₁² ∉ {1, χ₂, χ₂⁻¹}` exists. -/
theorem row92_row (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (L : ℝ) (hL : 1 ≤ L)
    {θ lam k slack a c : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2) (hlam : 0 < lam) (hk : 0 ≤ k)
    (ha2 : a ≤ 2) (hc2 : c ≤ 2)
    (hsl : (k ^ 2 + 4 * k + 3 / 2) * ((1:ℝ)/6 + 1/1000000) ≤ slack)
    (hcert : ∀ {la1 laj : ℝ}, 0 ≤ la1 → la1 ≤ a → laj ≤ c →
      0 ≤ (k ^ 2 + 1 / 2) * (P9F.La θ lam la1 - P9F.La θ lam (la1 - laj)) -
          2 * k * P9F.La θ lam 0 + tf71f θ lam 0 * slack → False) :
    ∃ N : ℕ, q₀ ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
      348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ a → lamOf q ρ₂ ≤ c → False := by
  obtain ⟨qE, hqE⟩ := eng92_of_engine hδ0 hδ1 hL θ lam k hθ0 hθπ hlam hk
  refine ⟨max (max q₀ qE) (max (Nat.ceil (Real.exp L) + 1) (Nat.ceil (Real.exp (Real.exp 4)) + 1)),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
  have hq₀ : q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqE' : qE ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hK1 : Nat.ceil (Real.exp L) + 1 ≤ q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hK2 : Nat.ceil (Real.exp (Real.exp 4)) + 1 ≤ q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  exact row92_at hθ0 hθπ hlam hk ha2 hc2 hsl hcert (hqE q hqE')
    (fun χ _ hχ => hL52 q hq₀ χ hχ) (rectT10H_le_log_of_ceil_exp_le hK1 le_rfl)
    (two_le_sqrt_loglog (four_le_loglog_of_ceil_exp_exp_le hK2 le_rfl))
    hmin hZ2 hne1 hne2 hsq hsq1 hsq2 (by linarith) hle1 hle2

/-- **HB Lemma 9.2 (Table 9) at height `L`, all twenty rows of Table 10.** -/
theorem row92_all_H (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (L : ℝ) (hL : 1 ≤ L) :
    ∀ p ∈ tableR hbTable10,
      ∃ N : ℕ, q₀ ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
        (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
        IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
        χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
        χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ →
        348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  intro p hp
  simp only [tableR, hbTable10, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    | h14 | h15 | h16 | h17 | h18 | h19
  · subst h0
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (21/500:ℝ)) (k := (407/500:ℝ)) (slack := (338664717947/375000000000:ℝ))
      (a := (9/25:ℝ)) (c := (123/100:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_036_123 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h1
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (21/500:ℝ)) (k := (407/500:ℝ)) (slack := (338664717947/375000000000:ℝ))
      (a := (9/25:ℝ)) (c := (123/100:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_036_123 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h2
    have hθ0 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 24)
      (lam := (9/200:ℝ)) (k := (817/1000:ℝ)) (slack := (1358882154467/1500000000000:ℝ))
      (a := (19/50:ℝ)) (c := (1181/1000:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_038_1181 P9F.arctan24_bounds.1
        P9F.arctan24_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h3
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (11/250:ℝ)) (k := (41/50:ℝ)) (slack := (3407774843/3750000000:ℝ))
      (a := (2/5:ℝ)) (c := (227/200:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_04_1135 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h4
    have hθ0 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (24:ℝ)) = (24/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 24)
      (lam := (23/500:ℝ)) (k := (411/500:ℝ)) (slack := (113827579921/125000000000:ℝ))
      (a := (21/50:ℝ)) (c := (547/500:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_042_1094 P9F.arctan24_bounds.1
        P9F.arctan24_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h5
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (23/500:ℝ)) (k := (33/40:ℝ)) (slack := (730755329/800000000:ℝ))
      (a := (11/25:ℝ)) (c := (211/200:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_044_1055 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h6
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (23/500:ℝ)) (k := (207/250:ℝ)) (slack := (28633458849/31250000000:ℝ))
      (a := (23/50:ℝ)) (c := (509/500:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_046_1018 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h7
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (47/1000:ℝ)) (k := (104/125:ℝ)) (slack := (21563532323/23437500000:ℝ))
      (a := (12/25:ℝ)) (c := (123/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_048_0984 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h8
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (6/125:ℝ)) (k := (417/500:ℝ)) (slack := (115241590889/125000000000:ℝ))
      (a := (1/2:ℝ)) (c := (119/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_05_0952 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h9
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (6/125:ℝ)) (k := (209/250:ℝ)) (slack := (28869460681/31250000000:ℝ))
      (a := (13/25:ℝ)) (c := (461/500:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_052_0922 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h10
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (6/125:ℝ)) (k := (419/500:ℝ)) (slack := (347142783683/375000000000:ℝ))
      (a := (27/50:ℝ)) (c := (893/1000:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_054_0893 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h11
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (49/1000:ℝ)) (k := (21/25:ℝ)) (slack := (72469279/78125000:ℝ))
      (a := (14/25:ℝ)) (c := (433/500:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_056_0866 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h12
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (1/20:ℝ)) (k := (421/500:ℝ)) (slack := (116187598241/125000000000:ℝ))
      (a := (29/50:ℝ)) (c := (21/25:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_058_084 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h13
    have hθ0 : 0 < Real.arctan (15:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (15:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (15:ℝ)) = (15/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 15)
      (lam := (41/500:ℝ)) (k := (211/250:ℝ)) (slack := (87318387563/93750000000:ℝ))
      (a := (3/5:ℝ)) (c := (102/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_06_0816 P9F.arctan15_bounds.1
        P9F.arctan15_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h14
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (1/20:ℝ)) (k := (847/1000:ℝ)) (slack := (1401362484227/1500000000000:ℝ))
      (a := (31/50:ℝ)) (c := (99/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_062_0792 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h15
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (51/1000:ℝ)) (k := (849/1000:ℝ)) (slack := (468070168801/500000000000:ℝ))
      (a := (16/25:ℝ)) (c := (77/100:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_064_077 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h16
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (13/250:ℝ)) (k := (213/250:ℝ)) (slack := (29343464369/31250000000:ℝ))
      (a := (33/50:ℝ)) (c := (187/250:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_066_0748 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h17
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (13/250:ℝ)) (k := (427/500:ℝ)) (slack := (117611609329/125000000000:ℝ))
      (a := (17/25:ℝ)) (c := (91/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_068_0728 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h18
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (13/250:ℝ)) (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ))
      (a := (7/10:ℝ)) (c := (177/250:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_07_0708 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)
  · subst h19
    have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
    have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    have htan : Real.tan (Real.arctan (25:ℝ)) = (25/1:ℝ) := by rw [Real.tan_arctan]; norm_num
    obtain ⟨N, hNge, hN⟩ := row92_row q₀ δ hδ0 hδ1 hL52 L hL (θ := Real.arctan 25)
      (lam := (13/250:ℝ)) (k := (107/125:ℝ)) (slack := (2762098309/2929687500:ℝ))
      (a := (88/125:ℝ)) (c := (88/125:ℝ)) hθ0 hθπ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun {la1 laj} h1 h2 h3 h4 => P9F.rowcontra_0704_0704 P9F.arctan25_bounds.1
        P9F.arctan25_bounds.2 htan h1 h2 h3 h4)
    refine ⟨N, hNge, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 hle1 hle2
    exact hN q hq χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hsq hsq1 hsq2 h348 (by linarith) (by linarith)

/-- **HB Lemma 9.3 at height `L` for the rows of Table 10 with `p.1 ≥ 0.36`**: the certificate
`table10_93_cert` fed to the height-`L` engine. -/
theorem row93_all_H (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (L : ℝ) (hL : 1 ≤ L) :
    ∀ p ∈ tableR hbTable10, (36/100 : ℝ) ≤ p.1 →
      ∃ N : ℕ, q₀ ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
        (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
        IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
        χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
        χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
        348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  intro p hp hp36
  obtain ⟨lam, k, hl, hk, hcert⟩ := table10_93_cert p hp hp36
  have hp1 : p.1 ≤ 1 := (HB94.tableR_hbTable10_le_one_aux hp).1
  have hp2 : p.2 ≤ 1 := (HB94.tableR_hbTable10_le_one_aux hp).2
  obtain ⟨qE, hqE⟩ := eng93_of_engine (δ := δ) (L := L) hδ0 hδ1 hL (T := tf72T lam hl) hk
  refine ⟨max (max q₀ qE) (Nat.ceil (Real.exp L) + 1),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hcsq hcsq1 hcsq2 h348 hle1 hle2
  have hq₀ : q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqE' : qE ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hK1 : Nat.ceil (Real.exp L) + 1 ≤ q := le_trans (le_max_right _ _) hq
  exact row93_at hl (hqE q hqE') hp1 hp2 hcert (fun χ _ hχ => hL52 q hq₀ χ hχ)
    (rectT10H_le_log_of_ceil_exp_le hK1 le_rfl) hL hmin hZ2 hne1 hne2 hcsq hcsq1 hcsq2 h348 hle1 hle2

/-- **The `(C3)` route at height `L` for the rows of Table 10 with `p.1 ≥ 0.36`**: HB Lemma 6.2
with `ψ = 3/8` and the certificate `table10_62_cert`. -/
theorem row62_all_H (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL8 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 60 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    (L : ℝ) (hL : 1 ≤ L) :
    ∀ p ∈ tableR hbTable10, (36/100 : ℝ) ≤ p.1 →
      ∃ N : ℕ, q₀ ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
        (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
        IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
        χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
        (χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹) →
        (χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹) →
        348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  intro p hp _
  obtain ⟨lam, hl, hcert⟩ := table10_62_cert p hp
  have hp1 : p.1 ≤ 1 := (HB94.tableR_hbTable10_le_one_aux hp).1
  have hp2 : p.2 ≤ 1 := (HB94.tableR_hbTable10_le_one_aux hp).2
  obtain ⟨qE, hqE⟩ := eng62_of_engine (δ := δ) (L := L) hδ0 hδ1 hL
    (T := tf72T lam hl) (c := (1:ℝ)/8) (by norm_num)
  refine ⟨max (max q₀ qE) (Nat.ceil (Real.exp L) + 1),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hA hB h348 hle1 hle2
  have hq₀ : q₀ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqE' : qE ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hK1 : Nat.ceil (Real.exp L) + 1 ≤ q := le_trans (le_max_right _ _) hq
  exact row62_at hl (hqE q hqE') (fun χ _ hχ hpow => hL8 q hq₀ χ hχ hpow)
    (rectT10H_le_log_of_ceil_exp_le hK1 le_rfl) hL hp1 hp2 hcert hmin hZ2 hne1 hne2 hA hB
    (by linarith) (by linarith)

/-! ## The assembly -/

theorem RectT10H : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ →
      ∀ p ∈ Work.ZeroFreeTables.tableR Work.ZeroFreeTables.hbTable10,
        Work.LinnikContract.lamOf q ρ₁ ≤ p.1 →
        Work.ZeroFreeTables.Lam2BoundH L χ₁ p.2 := by
  intro L hL
  -- the two log-derivative supplies, at a common `δ`
  obtain ⟨δ₁, hδ₁0, hδ₁1, q₁₆, h16⟩ := HB94.L52supply16
  obtain ⟨δ₂, hδ₂0, hδ₂1, q₆₀, h60⟩ := HB94.L52supply_pow
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδ0 : 0 < δ := lt_min hδ₁0 hδ₂0
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) hδ₁1
  set Q : ℕ := max q₁₆ q₆₀ with hQdef
  have hL6 : ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ := by
    intro q hq _inst χ _instc hχ
    exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_left _ _)
      (h16 q (le_trans (le_max_left _ _) hq) χ hχ)
  have hL8 : ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 60 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ := by
    intro q hq _inst χ _instc hχ hpow
    exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_right _ _)
      (h60 q (le_trans (le_max_right _ _) hq) χ hχ hpow)
  -- the three routes, and the case analysis, for every row of Table 10
  have hrow : ∀ p ∈ (tableR hbTable10).toFinset,
      ∃ N : ℕ, Q ≤ N ∧ ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
        (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
        IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
        χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → 348/1000 ≤ lamOf q ρ₁ →
        lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
    intro p hpS
    have hp : p ∈ tableR hbTable10 := List.mem_toFinset.mp hpS
    obtain ⟨N92, hN92ge, h92⟩ := row92_all_H Q δ hδ0 hδ1 hL6 L hL p hp
    by_cases hp34 : p.1 < 348/1000
    · refine ⟨N92, hN92ge, ?_⟩
      intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 h348 hle1 hle2
      linarith
    · push_neg at hp34
      have hp36 : (36/100 : ℝ) ≤ p.1 := by
        rcases table10_p1_cases hp with h | h
        · linarith
        · exact h
      obtain ⟨N93, hN93ge, h93⟩ := row93_all_H Q δ hδ0 hδ1 hL6 L hL p hp hp36
      obtain ⟨N62, hN62ge, h62⟩ := row62_all_H Q δ hδ0 hδ1 hL8 L hL p hp hp36
      refine ⟨max (max N92 N93) N62, ?_, ?_⟩
      · omega
      · intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 h348 hle1 hle2
        have hq92 : N92 ≤ q := by omega
        have hq93 : N93 ≤ q := by omega
        have hq62 : N62 ≤ q := by omega
        by_cases hA : χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹
        · by_cases hB : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹
          · exact h62 q hq62 χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hA hB h348 hle1 hle2
          · push_neg at hB
            exact h93 q hq93 χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hB.1 hB.2.1 hB.2.2 h348 hle1 hle2
        · push_neg at hA
          exact h92 q hq92 χ₁ χ₂ ρ₁ ρ₂ hmin hZ2 hne1 hne2 hA.1 hA.2.1 hA.2.2 h348 hle1 hle2
  -- a single deadline for all rows
  obtain ⟨N, hN⟩ := exists_uniform_deadline (tableR hbTable10).toFinset
    (fun p n => Q ≤ n ∧ ∀ q : ℕ, n ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMinWideAt L (10 * L) χ₁ ρ₁ → IsZAt L χ₂ ρ₂ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → 348/1000 ≤ lamOf q ρ₁ →
      lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False)
    (fun p n m hnm h => ⟨le_trans h.1 hnm, fun q hq => h.2 q (le_trans hnm hq)⟩) hrow
  refine ⟨N, ?_⟩
  intro q hq _inst χ₁ ρ₁ hR him h348 p hp hle1
  obtain ⟨hNQ, hNp⟩ := hN p (List.mem_toFinset.mpr hp)
  have hqQ : Q ≤ q := le_trans hNQ hq
  have hmin : IsMinWideAt L (10 * L) χ₁ ρ₁ :=
    ⟨hR.1.1, hR.1.2.1, hR.1.2.2, fun χ u hχ hzm him => hR.2 χ u ⟨hχ, hzm, him⟩⟩
  intro χ ρ hZ hχ1 hχ2
  by_contra hcon
  push_neg at hcon
  exact hNp q hq χ₁ χ ρ₁ ρ hmin hZ hχ1 hχ2 h348 hle1 (le_of_lt hcon)

end

end Work.ZeroFreeTables.OffAxis
