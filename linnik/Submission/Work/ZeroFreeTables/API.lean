/-
# ZeroFreeTables — API.lean

Basic interface of the predicates `IsZ`, `IsMin1`, `Lam0Bound`, `Lam2Bound`,
`Lam3Bound` (frozen in `Submission.Work.LinnikContract.Defs`) together with the
`Z1`–`Z5` components and `ZeroFreeCert` of `Submission.Work.ZeroFreeTables.Defs`.

Everything here is a projection, a monotonicity statement or a combination of two
bounds; it is the glue that AREA 7 (`Assembly`) and any consumer of AREA 3 needs.
-/
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.LinnikContract2.API

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Projections of `IsZ` and `IsMin1` -/

@[simp] theorem isZ_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : χ ≠ 1 := h.1

@[simp] theorem isZ_mult_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : zeroMult χ ρ ≠ 0 := h.2.1

@[simp] theorem isZ_im_le_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZ χ ρ) : |ρ.im| ≤ 1 := h.2.2

theorem isMin1_isZ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) : IsZ χ₁ ρ₁ := h.1

/-- `ρ₁` has *minimal* `λ`: every zero in the working region has `λ ≥ λ₁`
(`λ(ρ) = (1 - Re ρ) log q`, so the zero of largest real part has the least `λ`; HB's
`λ₁` is by definition this minimum). -/
theorem isMin1_lam_le {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hZ : IsZ χ ρ) :
    lamOf q ρ₁ ≤ lamOf q ρ := by
  have h := h.2
  exact h χ ρ hZ

theorem isMin1_lam_le_chi {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) {ρ : ℂ} (hZ : IsZ χ₁ ρ) : lamOf q ρ₁ ≤ lamOf q ρ :=
  isMin1_lam_le h hZ

/-- `IsMin1` propagates to any zero of `χ₁` with no larger `λ`. -/
theorem isMin1_trans_le {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ₁' : ℂ}
    (h : IsMin1 χ₁ ρ₁) (hZ : IsZ χ₁ ρ₁') (hle : lamOf q ρ₁' ≤ lamOf q ρ₁) :
    IsMin1 χ₁ ρ₁' :=
  ⟨hZ, fun χ ρ hρχ => hle.trans (isMin1_lam_le h hρχ)⟩

/-- If *some* zero `ρ` of `χ₁` is in the working region, then `λ₁ ≤ λ(ρ)`. -/
theorem isMin1_le_of_isZ {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1 χ₁ ρ₁) {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hZ : IsZ χ ρ) : lamOf q ρ₁ ≤ lamOf q ρ := isMin1_lam_le h hZ

/-! ## Monotonicity in the constant -/

theorem lam0Bound_mono {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c c' : ℝ}
    (h : Lam0Bound χ₁ ρ₁ c) (hc : c' ≤ c) : Lam0Bound χ₁ ρ₁ c' := by
  have h1 := h.1
  have h2 := h.2
  exact ⟨fun hm => hc.trans (h1 hm), fun ρ hZ hne hconj => hc.trans (h2 ρ hZ hne hconj)⟩

theorem lam2Bound_mono {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c c' : ℝ}
    (h : Lam2Bound χ₁ c) (hc : c' ≤ c) : Lam2Bound χ₁ c' := by
  intro χ ρ hZ h1 h2
  exact hc.trans (h χ ρ hZ h1 h2)

theorem lam3Bound_mono {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c c' : ℝ}
    (h : Lam3Bound χ₁ c) (hc : c' ≤ c) : Lam3Bound χ₁ c' := by
  obtain ⟨χ₂, hχ₂⟩ := h
  exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => hc.trans (hχ₂ χ ρ hZ h1 h2 h3 h4)⟩

/-! ## Projections and combinations of the bounds -/

/-- `Lam0Bound` at an explicit zero of `χ₁`. -/
theorem lam0Bound_apply {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ : ℂ} {c : ℝ}
    (h : Lam0Bound χ₁ ρ₁ c) (hZ : IsZ χ₁ ρ) (hne : ρ ≠ ρ₁)
    (hconj : χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) : c ≤ lamOf q ρ := by
  have h := h.2
  exact h ρ hZ hne hconj

/-- `Lam0Bound` at `ρ₁` itself, when `ρ₁` is a multiple zero. -/
theorem lam0Bound_self {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ}
    (h : Lam0Bound χ₁ ρ₁ c) (hm : 2 ≤ zeroMult χ₁ ρ₁) : c ≤ lamOf q ρ₁ := h.1 hm

/-- `Lam2Bound` at an explicit zero. -/
theorem lam2Bound_apply {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c : ℝ}
    (h : Lam2Bound χ₁ c) {χ : DirichletCharacter ℂ q} {ρ : ℂ} (hZ : IsZ χ ρ)
    (h1 : χ ≠ χ₁) (h2 : χ ≠ χ₁⁻¹) : c ≤ lamOf q ρ := h χ ρ hZ h1 h2

/-- The excluded pair of a `Lam3Bound`, exposed. -/
theorem lam3Bound_elim {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c : ℝ}
    (h : Lam3Bound χ₁ c) : ∃ χ₂ : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → c ≤ lamOf q ρ := h

/-- HB Lemma 9.4: `λ₂` bounds apply to `λ₃`'s excluded pair as well.  For every
character `χ ≠ χ₁^{±1}` we have `λ^{(χ)} ≥ min c₂ c₃`, where `c₂` comes from
`Lam2Bound` and `c₃` is the companion bound of `Lam3Bound`. -/
theorem le_min_of_lam2_lam3 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c₂ c₃ : ℝ}
    (h2 : Lam2Bound χ₁ c₂) (h3 : Lam3Bound χ₁ c₃) :
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
      min c₂ c₃ ≤ lamOf q ρ := by
  obtain ⟨χ₂, hχ₂⟩ := h3
  intro χ ρ hZ h1 h2ne
  by_cases h3' : χ = χ₂
  · rw [h3'] at hZ h1 h2ne
    exact le_trans (min_le_left _ _) (h2 χ₂ ρ hZ h1 h2ne)
  by_cases h4' : χ = χ₂⁻¹
  · rw [h4'] at hZ h1 h2ne
    exact le_trans (min_le_left _ _) (h2 χ₂⁻¹ ρ hZ h1 h2ne)
  exact le_trans (min_le_right _ _) (hχ₂ χ ρ hZ h1 h2ne h3' h4')

/-- `Lam2Bound` implies `Lam3Bound` (take `χ₂ = χ₁`). -/
theorem lam2Bound_to_lam3Bound {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c : ℝ}
    (h : Lam2Bound χ₁ c) : Lam3Bound χ₁ c :=
  ⟨χ₁, fun χ ρ hZ h1 h2 _ _ => h χ ρ hZ h1 h2⟩

/-- The pair of `Lam3Bound` may be discarded at the cost of the minimum of the two bounds. -/
theorem lam2Bound_of_lam2_lam3 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {c₂ c₃ : ℝ}
    (h2 : Lam2Bound χ₁ c₂) (h3 : Lam3Bound χ₁ c₃) : Lam2Bound χ₁ (min c₂ c₃) :=
  le_min_of_lam2_lam3 h2 h3

/-! ## Unpacking `ZeroFreeCert` -/

theorem zeroFreeCert_z1 (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁ := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hm => (hq q hq' χ₁ ρ₁ hm).1⟩

theorem zeroFreeCert_z2 (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z2 χ₁ ρ₁ := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hm => (hq q hq' χ₁ ρ₁ hm).2.1⟩

theorem zeroFreeCert_z3 (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z3 χ₁ ρ₁ := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hm => (hq q hq' χ₁ ρ₁ hm).2.2.1⟩

theorem zeroFreeCert_z4 (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z4 χ₁ ρ₁ := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hm => (hq q hq' χ₁ ρ₁ hm).2.2.2.1⟩

theorem zeroFreeCert_z5 (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → Z5 χ₁ ρ₁ lamS := by
  intro lamS hS
  obtain ⟨q₀, hq⟩ := h lamS hS
  exact ⟨q₀, fun q hq' _ χ₁ ρ₁ hm => (hq q hq' χ₁ ρ₁ hm).2.2.2.2⟩

theorem zeroFreeCert_z4' (h : ZeroFreeCert) : ∀ lamS : ℝ, 0 < lamS →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ∀ r ∈ rows15, r.1 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ r.2.1 →
        Lam0Bound χ₁ ρ₁ r.2.2.1 ∧ Lam2Bound χ₁ r.2.2.2.1 ∧ Lam3Bound χ₁ r.2.2.2.2 :=
  zeroFreeCert_z4 h

/-! ## Assembling `ZeroFreeCert` from the five conditions -/

/-- **`HBNumbering696` (round-1 bridge; the audit's corrected form).**  When `λ₁ < 0.696`, the
height-10 minimiser is HB's §6 numbered zero, so the local engine's clause
`λ₁ ≤ λ(u)` holds for every zero `u` of the rectangle (6.1), i.e. every zero with
`|Im u| ≤ 𝓛`.  No `|Im ρ₁| ≤ 1` is assumed, so the round-2 wide minimiser satisfies the
hypothesis as well.

This replaces the refuted `HBWideMin` (which failed on `λ₁ ∈ (0.702, 0.856]` and had no `q₀`):
with a height-10 hypothesis plus `λ₁ < 0.696`, `χ₁` must be (a power of) HB's numbered
character — Lemma 9.4 gives `λ ≥ 0.702` for every character outside `χ*^{±1}`, so a second
zero of `χ*` at height `≤ 10` would force `λ₁ ≥ 0.696` by Table 8/4 (strict, by certificate).
A prover needs that plus HB Lemma 6.1 (the zero-free strip `𝓛 < |t| ≤ 10𝓛`); the audit
(`ENGINE_AUDIT_LEAD.md` §3.7) records it as TRUE by that route.

Round 2 drops this bridge entirely: `LinnikContract2.IsMin1` already gives the wide
clause, so nothing in the round-2 interface asks for it. -/
def HBNumbering696 : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    χ₁ ≠ 1 → zeroMult χ₁ ρ₁ ≠ 0 → |ρ₁.im| ≤ 10 →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
      lamOf q ρ₁ ≤ lamOf q u) →
    lamOf q ρ₁ < 696/1000 →
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → zeroMult χ u ≠ 0 →
      |u.im| ≤ Real.log q → lamOf q ρ₁ ≤ lamOf q u

theorem zeroFreeCert_of (h1 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z1 χ₁ ρ₁)
    (h2 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z2 χ₁ ρ₁)
    (h3 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z3 χ₁ ρ₁)
    (h4 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z4 χ₁ ρ₁)
    (h5 : ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1WideAt 10 χ₁ ρ₁ → Z5 χ₁ ρ₁ lamS) : ZeroFreeCert := by
  intro lamS hS
  obtain ⟨Q1, hQ1⟩ := h1 lamS hS
  obtain ⟨Q2, hQ2⟩ := h2 lamS hS
  obtain ⟨Q3, hQ3⟩ := h3 lamS hS
  obtain ⟨Q4, hQ4⟩ := h4 lamS hS
  obtain ⟨Q5, hQ5⟩ := h5 lamS hS
  refine ⟨max (max (max (max Q1 Q2) Q3) Q4) Q5, ?_⟩
  intro q hq _ χ₁ ρ₁ hm
  have hQ1' : Q1 ≤ q := by have := hq; simp only [max_le_iff] at this; omega
  have hQ2' : Q2 ≤ q := by have := hq; simp only [max_le_iff] at this; omega
  have hQ3' : Q3 ≤ q := by have := hq; simp only [max_le_iff] at this; omega
  have hQ4' : Q4 ≤ q := by have := hq; simp only [max_le_iff] at this; omega
  have hQ5' : Q5 ≤ q := by have := hq; simp only [max_le_iff] at this; omega
  exact ⟨hQ1 q hQ1' χ₁ ρ₁ hm, hQ2 q hQ2' χ₁ ρ₁ hm, hQ3 q hQ3' χ₁ ρ₁ hm,
    hQ4 q hQ4' χ₁ ρ₁ hm, hQ5 q hQ5' χ₁ ρ₁ hm⟩

theorem area3_of_zeroFreeCert {Area1 : Prop} (h : ZeroFreeCert) : Area3 Area1 := fun _ => h


/-- **HB's setting for the exceptional zero** ((6.1), (6.2)): `ρ₁` is the zero of
*minimal* `λ` among the non-principal zeros of **all** characters in the rectangle
`|Im| ≤ 𝓛` (`𝓛 = log q`), not only among the zeros of the working region `|Im| ≤ 1`.

The `P₃` engine (HB Lemma 9.1 and its §6/§10 companions) needs this stronger
minimality: the derivation drops the zero terms with `Re P₃(α/((s-u)𝓛)) ≥ 0`, and
by condition (4.11) that is exactly `λ₁ ≤ λ(u)` for every zero `u` in the window
`|Im u| ≤ 3 + δ` used by (9.1).  `IsMin1` alone (working region `|Im| ≤ 1`) leaves
zeros with `1 < |Im u| ≤ 3 + δ` unconstrained, and their terms cannot be dropped.
A delegated prover isolated this; see `dev/README.md`. -/
def IsMin1Wide {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsMin1 χ₁ ρ₁ ∧ ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 → zeroMult χ u ≠ 0 →
    |u.im| ≤ Real.log q → lamOf q ρ₁ ≤ lamOf q u

theorem IsMin1Wide.isMin1 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1Wide χ₁ ρ₁) : IsMin1 χ₁ ρ₁ := h.1

/-- `IsMin1Wide` is `IsMin1WideAt` at height `𝓛 = log q`. -/
theorem isMin1WideAt_log_iff {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1WideAt (Real.log q) χ₁ ρ₁ ↔ IsMin1Wide χ₁ ρ₁ := Iff.rfl

/-- Minimality at a larger height is a stronger hypothesis. -/
theorem IsMin1WideAt.mono {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    {H H' : ℝ} (hHH' : H ≤ H') (h : IsMin1WideAt H' χ₁ ρ₁) : IsMin1WideAt H χ₁ ρ₁ :=
  ⟨h.1, fun χ u hχ hu hH => h.2 χ u hχ hu (le_trans hH hHH')⟩

/-- A wider minimality gives the engine's hypothesis `IsMin1Wide` whenever the
working window `𝓛 = log q` fits below it. -/
theorem IsMin1Wide_of_isMin1WideAt {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    {H : ℝ} (hH : Real.log q ≤ H) (h : IsMin1WideAt H χ₁ ρ₁) : IsMin1Wide χ₁ ρ₁ :=
  (isMin1WideAt_log_iff).mp (IsMin1WideAt.mono hH h)

/-- Minimality at height `log q ≥ 10` gives the height-10 form used by the engine
`Prop`s (this is the direction a consumer holding `IsMin1Wide` needs). -/
theorem IsMin1Wide.toIsMin1WideAt10 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1Wide χ₁ ρ₁) (h10 : 10 ≤ Real.log q) : IsMin1WideAt 10 χ₁ ρ₁ :=
  IsMin1WideAt.mono h10 h

/-- The *second* conjunct of `Lam0Bound`: every other zero of `χ₁` (and, when `χ₁`
is real, everything except `conj ρ₁`) has `λ ≥ c`.  The multiplicity case
`ρ₀ = ρ₁` is the separate first conjunct of `Lam0Bound`. -/
def Lam0BoundOther {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (c : ℝ) : Prop :=
  ∀ ρ : ℂ, IsZ χ₁ ρ → ρ ≠ ρ₁ → (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) → c ≤ lamOf q ρ

/-- `Lam0Bound` is the multiplicity case together with `Lam0BoundOther`. -/
theorem lam0Bound_iff {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ} :
    Lam0Bound χ₁ ρ₁ c ↔ (2 ≤ zeroMult χ₁ ρ₁ → c ≤ lamOf q ρ₁) ∧ Lam0BoundOther χ₁ ρ₁ c :=
  Iff.rfl

theorem Lam0BoundOther.mono' {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c c' : ℝ}
    (h : Lam0BoundOther χ₁ ρ₁ c) (hc : c' ≤ c) : Lam0BoundOther χ₁ ρ₁ c' :=
  fun ρ hZ hne hconj => hc.trans (h ρ hZ hne hconj)

theorem Lam0BoundOther.apply {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ : ℂ} {c : ℝ}
    (h : Lam0BoundOther χ₁ ρ₁ c) (hZ : IsZ χ₁ ρ) (hne : ρ ≠ ρ₁)
    (hconj : χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) : c ≤ lamOf q ρ := h ρ hZ hne hconj

/-- `Lam0Bound` from its two parts. -/
theorem lam0Bound_of_parts {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ}
    (h1 : 2 ≤ zeroMult χ₁ ρ₁ → c ≤ lamOf q ρ₁) (h2 : Lam0BoundOther χ₁ ρ₁ c) :
    Lam0Bound χ₁ ρ₁ c := ⟨h1, h2⟩

/-- **The round-2 adapter.**  `LinnikContract2.IsMin1` (the wide minimiser at height `50`) gives
the height-10 predicate of this area for every *on-axis* pair (`|Im ρ₁| ≤ 1`): the narrow
component is round 2's `IsMin1.parts`, and the height-10 clause is `IsMin1.window`.
Off-axis pairs are covered by `HBOffAxis`. -/
theorem IsMin1WideAt_of_isMin1 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hm : LinnikContract2.IsMin1 χ₁ ρ₁) (hZ : Work.LinnikContract.IsZ χ₁ ρ₁) :
    IsMin1WideAt 10 χ₁ ρ₁ := by
  refine ⟨?_, ?_⟩
  · exact LinnikContract2.IsMin1.toRound1Shape hm hZ
  · intro χ u hχ hu him
    exact hm.le_lamOf (LinnikContract2.isZH_mono (by norm_num) ⟨hχ, hu, him⟩)

end Work.ZeroFreeTables
