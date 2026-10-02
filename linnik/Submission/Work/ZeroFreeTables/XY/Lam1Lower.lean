import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.ZeroFreeTables.XY.P3PhiLe
import Submission.Work.ZeroFreeTables.XY.P3ReDecay2
import Submission.Work.ZeroFreeTables.XY.ArgIdentities
import Submission.Work.ZeroFreeTables.XY.NearNorm
import Submission.Work.ZeroFreeTables.XY.NearP3sumExtract2
import Submission.Work.ZeroFreeTables.XY.NearP3sumExtractTwo2
import Submission.Work.ZeroFreeTables.XY.NearP3sumNonneg2
import Submission.Work.ZeroFreeTables.XY.Z2Small
import Submission.Work.ZeroFreeTables.XY.Z4Small
import Submission.Work.ZeroFreeTables.XY.ChenSumNonneg2
import Submission.Work.ZeroFreeTables.XY.PrimitiveSigmaEngine
import Submission.Work.ZeroFreeTables.XY.ImprimitiveSigmaReduce
import Submission.Work.ZeroFreeTables.XY.PrincipalSigmaBoundD
import Submission.Work.ZeroFreeTables.Table4.HB83_base

/-!
# `Work.ZeroFreeTables.XY.Lam1Lower`

The `h = 2` case of Heath-Brown's Lemma 9.5:  for a **real** character `χ₁` (`χ₁ ^ 2 = 1`)
whose minimal zero `ρ₁` in the strip `|Im| ≤ 10` is **not real**, `λ₁ ≥ 518/1000`.

The proof is Heath-Brown's §9 computation: the pointwise Chen-type inequality
`0 ≤ (3+10cos θ)² (9+10cos θ)²` expanded as
`14379 + 24480 cos θ + 14900 cos 2θ + 6000 cos 3θ + 1250 cos 4θ`, evaluated at the five
points `σ + n i γ₁` (`σ = 1 + a/𝓛`, `a = 17/5`) of the `P₃`-functional `Σ(s,χ)`; the bounds
`Σ ≤ -Σ_{near} Re P₃(α/((s-u)𝓛)) + (a+λ₁)(φ/2+ε)` (HB (9.2)–(9.7), with `φ(χ₁) = 1/4`
since `χ₁` has order `2`) together with the comparison identities of `P3Bounds` turn it into
`0 ≤ 14379 P₃((a+λ₁)/a) - 24480 P₃(1) + 3810 (a + λ₁)` up to `o(1)`, which forces
`λ₁ ≥ 0.518` (`lam1_numeric`).
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.ZeroFreeTables.XY

open Work.ZeroFreeTables

/-! ## The numerical core -/

/-- `F(λ) = 14379 P₃((17/5+λ)/(17/5)) - 24480 P₃(1) + 3810 (17/5 + λ)` as a polynomial. -/
theorem F_eq_poly (lam : ℝ) :
    14379 * P3R ((17/5 + lam)/(17/5)) - 24480 * P3R 1 + 3810 * (17/5 + lam)
      = (1198250/4913) * lam^3 + (1078425/289) * lam^2 + (424245/17) * lam - 13982 := by
  unfold Work.ZeroFreeTables.P3R
  field_simp
  ring

/-- The polynomial of `F_eq_poly`. -/
def Fpoly (x : ℝ) : ℝ :=
  (1198250/4913) * x^3 + (1078425/289) * x^2 + (424245/17) * x - 13982

theorem Fpoly_mono {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 518/1000) : Fpoly x ≤ Fpoly (518/1000) := by
  have hfac : Fpoly (518/1000) - Fpoly x
      = (518/1000 - x) * ((1198250/4913) * ((518/1000)^2 + (518/1000)*x + x^2)
          + (1078425/289) * (518/1000 + x) + (424245/17)) := by
    unfold Fpoly; ring
  have hbracket : 0 ≤ (1198250/4913) * ((518/1000)^2 + (518/1000)*x + x^2)
      + (1078425/289) * (518/1000 + x) + (424245/17) := by positivity
  nlinarith [hfac, hbracket, h0, h1]

theorem Fpoly_518_lt : Fpoly (518/1000) < -18 := by unfold Fpoly; norm_num

/-- The numeric core of `Lam1Lower`. -/
theorem lam1_numeric (lam : ℝ)
    (h : 0 ≤ 14379 * P3R ((17/5 + lam)/(17/5)) - 24480 * P3R 1 + 3810 * (17/5 + lam)) :
    518/1000 ≤ lam := by
  rw [F_eq_poly] at h
  have hGval : Fpoly (518/1000) < 0 := by
    have := Fpoly_518_lt; linarith
  have hquad : ∀ x : ℝ, 0 < (1198250/4913) * x^2 + (1078425/289) * x + (424245/17) := by
    intro x
    nlinarith [sq_nonneg (x + (1078425/289) / (2 * (1198250/4913)))]
  by_contra hcon
  push_neg at hcon
  rcases lt_or_ge lam 0 with hlam | hlam
  · have hneg : Fpoly lam < Fpoly 0 := by
      have hfac : Fpoly lam - Fpoly 0
          = lam * ((1198250/4913) * lam^2 + (1078425/289) * lam + (424245/17)) := by
        unfold Fpoly; ring
      have := hquad lam
      nlinarith [hfac, hlam]
    have h0 : Fpoly 0 = -13982 := by unfold Fpoly; norm_num
    rw [h0] at hneg
    change 0 ≤ Fpoly lam at h
    linarith [h, hneg]
  · have hmono : Fpoly lam ≤ Fpoly (518/1000) := Fpoly_mono hlam (le_of_lt hcon)
    change 0 ≤ Fpoly lam at h
    linarith [h, hmono, hGval]

/-! ## Elementary `P₃` facts -/

theorem P3_ofReal (x : ℝ) : (P3 ((x:ℝ):ℂ)).re = P3R x := by
  have : P3 ((x:ℝ):ℂ) = (((P3R x : ℝ)) : ℂ) := by
    unfold Work.ZeroFreeTables.P3 Work.ZeroFreeTables.P3R
    push_cast
    ring
  rw [this, Complex.ofReal_re]

/-- `Re P₃(β/(β+iu)) ≥ 0`. -/
theorem P3_re_self_nonneg {β u : ℝ} (hβ : 0 < β) :
    0 ≤ (P3 ((β:ℂ)/((β:ℂ) + (u:ℂ)*Complex.I))).re := by
  have hβne : (β:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hβ)
  have h1 : 1 ≤ (((β:ℂ) + (u:ℂ)*Complex.I)/(β:ℂ)).re := by
    rw [Complex.div_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.normSq_apply]
    rw [div_self (by positivity : β*β ≠ 0), zero_div, add_zero]
  have h2 := P3_inv_re_nonneg (((β:ℂ) + (u:ℂ)*Complex.I)/(β:ℂ)) h1
  have h3 : (((β:ℂ) + (u:ℂ)*Complex.I)/(β:ℂ))⁻¹ = (β:ℂ)/((β:ℂ) + (u:ℂ)*Complex.I) := by
    rw [inv_div]
  rwa [h3] at h2

/-- `P₃(x/x) = P₃(1)`. -/
theorem P3_div_self {x : ℝ} (hx : x ≠ 0) :
    (P3 (((x:ℝ):ℂ)/((x:ℝ):ℂ))).re = P3R 1 := by
  rw [div_self (by exact_mod_cast hx)]
  exact P3_ofReal 1

theorem P3R_one_pos : 0 < P3R 1 := by unfold Work.ZeroFreeTables.P3R; norm_num

/-! ## The level/conductor transfer of the near-zero sums

`zeroMult χ u` is the multiplicity of `u` as a zero of the completed `L`-function of the
*primitive* character `χ.primitiveCharacter`.  Hence `nearP3sum` is insensitive to passing from
`χ` (at level `q`) to `χ.primitiveCharacter` (at level `χ.conductor`), which is what lets the
engine (proved for primitive characters) be applied at the conductor while the final bound is
stated at the level `q`. -/

private lemma completedLFunction_changeLevel_of_eq {n m : ℕ} [NeZero n] [NeZero m]
    (h : n = m) (ψ : DirichletCharacter ℂ n) :
    (fun s => DirichletCharacter.completedLFunction (N := n) ψ s)
      = fun s => DirichletCharacter.completedLFunction (N := m)
          (DirichletCharacter.changeLevel (dvd_of_eq h) ψ) s := by
  cases h
  rw [Subsingleton.elim (dvd_of_eq rfl) (dvd_refl n), DirichletCharacter.changeLevel_self]

private lemma changeLevel_conductor_primitiveCharacter {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (h : χ.conductor = n) :
    DirichletCharacter.changeLevel (dvd_of_eq h) χ.primitiveCharacter = χ := by
  rw [Subsingleton.elim (dvd_of_eq h) χ.conductor_dvd_level,
    DirichletCharacter.changeLevel_primitiveCharacter]

/-- For a *primitive* character the completed `L`-function of its primitive part is itself. -/
theorem completedLFunction_primitiveCharacter_self {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (hprim : χ.IsPrimitive) [NeZero χ.conductor] :
    DirichletCharacter.completedLFunction χ.primitiveCharacter
      = DirichletCharacter.completedLFunction χ := by
  have hc : χ.conductor = n := hprim
  have h1 := completedLFunction_changeLevel_of_eq hc χ.primitiveCharacter
  have h2 : (fun s => DirichletCharacter.completedLFunction (N := n)
        (DirichletCharacter.changeLevel (dvd_of_eq hc) χ.primitiveCharacter) s)
      = fun s => DirichletCharacter.completedLFunction (N := n) χ s := by
    rw [changeLevel_conductor_primitiveCharacter χ hc]
  exact h1.trans h2

/-- `zeroMult` is unchanged when passing to the primitive character. -/
theorem zeroMult_primitiveCharacter_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (u : ℂ) :
    Work.LinnikContract.zeroMult χ.primitiveCharacter u = Work.LinnikContract.zeroMult χ u := by
  haveI : NeZero (χ.primitiveCharacter).conductor :=
    ⟨(χ.primitiveCharacter).conductor_ne_zero⟩
  simp only [Work.LinnikContract.zeroMult]
  rw [completedLFunction_primitiveCharacter_self χ.primitiveCharacter
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)]

/-- `nearP3sum` is unchanged when passing from the level `q` to the conductor. -/
theorem nearP3sum_primitiveCharacter_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {L a lam δ : ℝ} (s : ℂ) :
    Work.ZeroFreeTables.P9.nearP3sum χ.conductor L χ.primitiveCharacter s a lam δ
      = Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ := by
  haveI : NeZero (χ.primitiveCharacter).conductor :=
    ⟨(χ.primitiveCharacter).conductor_ne_zero⟩
  simp only [Work.ZeroFreeTables.P9.nearP3sum, Work.LinnikContract.zeroMult,
    completedLFunction_primitiveCharacter_self χ.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)]

/-! ## The main assembly

The analytic inputs are proved in sibling modules; they are hypotheses here so that the
assembly can be checked independently of them. -/

theorem main_assembly
    (hP : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ 518 / 1000 → s.re = 1 + (17 / 5) / Real.log q → |s.im| ≤ 4 →
      SigmaP3L q (Real.log q) (1 : DirichletCharacter ℂ q) s (17 / 5) lam₁
        ≤ (P3 (((((17 : ℝ) / 5) + lam₁) : ℂ)
              / ((s - 1) * ((Real.log q : ℝ) : ℂ)))).re + 1 / 100000)
    (hS : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ 518 / 1000 → s.re = 1 + (17 / 5) / Real.log q → |s.im| ≤ 3 →
      SigmaP3L q (Real.log q) χ s (17 / 5) lam₁
        ≤ - Work.ZeroFreeTables.P9.nearP3sum q (Real.log q) χ s (17 / 5) lam₁ δ
          + (((17 : ℝ) / 5) + lam₁) * (1 / 8 + 1 / 100000))
    (hChen : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 →
      ∀ {σ γ a lam L : ℝ}, 0 < L → 1 < σ → 0 < a + lam →
      0 ≤ 14379 * SigmaP3L q L 1 ((σ : ℂ)) a lam
        + 24480 * SigmaP3L q L χ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam
        + 14900 * SigmaP3L q L 1 ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) a lam
        + 6000 * SigmaP3L q L χ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam
        + 1250 * SigmaP3L q L 1 ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) a lam)
    (hCmp : ∀ (α β c : ℝ), 0 < α → 0 < β → β ≤ α →
      (P3 ((α : ℂ) / ((β : ℂ) + (c : ℂ) * Complex.I))).re
        ≤ (α / β) ^ 3 * (P3 ((α : ℂ) / ((α : ℂ) + (c : ℂ) * Complex.I))).re)
    (hDecay : ∀ {a α u : ℝ}, 0 < a → a ≤ α → α ≤ |u| →
      |(P3 ((α : ℂ) / ((a : ℂ) + (u : ℂ) * Complex.I))).re| ≤ 5 * α ^ 2 / u ^ 2)
    (hArg : ∀ {σ L a lam γ : ℝ}, σ = 1 + a/L → L ≠ 0 → ∀ {ρ : ℂ}, ρ.re = 1 - lam/L → ρ.im = γ →
      ((((σ:ℂ) + (γ:ℂ)*Complex.I) - ρ) * ((L:ℝ):ℂ) = ((a+lam:ℝ):ℂ))
      ∧ ((((σ:ℂ) + (γ:ℂ)*Complex.I) - starRingEnd ℂ ρ) * ((L:ℝ):ℂ)
          = ((a+lam:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
      ∧ ((((σ:ℂ) + 3*(γ:ℂ)*Complex.I) - ρ) * ((L:ℝ):ℂ)
          = ((a+lam:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
      ∧ ((((σ:ℂ) + 3*(γ:ℂ)*Complex.I) - starRingEnd ℂ ρ) * ((L:ℝ):ℂ)
          = ((a+lam:ℝ):ℂ) + (((4*γ*L:ℝ)):ℂ)*Complex.I)
      ∧ ((((σ:ℂ)) - 1) * ((L:ℝ):ℂ) = ((a:ℝ):ℂ))
      ∧ ((((σ:ℂ) + 2*(γ:ℂ)*Complex.I) - 1) * ((L:ℝ):ℂ)
          = ((a:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
      ∧ ((((σ:ℂ) + 4*(γ:ℂ)*Complex.I) - 1) * ((L:ℝ):ℂ)
          = ((a:ℝ):ℂ) + (((4*γ*L:ℝ)):ℂ)*Complex.I))
    (hNorm : ∀ {L lam γ δ : ℝ}, 0 < δ → ∀ {ρ : ℂ}, ρ.re = 1 - lam/L → ρ.im = γ →
      ((‖(1:ℂ) + (γ:ℂ)*Complex.I - ρ‖ ≤ δ) ↔ ((lam/L)^2 ≤ δ^2))
      ∧ ((‖(1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - ρ‖ ≤ δ) ↔ ((lam/L)^2 + (2*γ)^2 ≤ δ^2))
      ∧ ((‖(1:ℂ) + (γ:ℂ)*Complex.I - starRingEnd ℂ ρ‖ ≤ δ) ↔ ((lam/L)^2 + (2*γ)^2 ≤ δ^2))
      ∧ ((‖(1:ℂ) + ((3*γ:ℝ):ℂ)*Complex.I - starRingEnd ℂ ρ‖ ≤ δ) ↔ ((lam/L)^2 + (4*γ)^2 ≤ δ^2)))
    (hExt1 : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {L a lam δ : ℝ}, 0 < L → 0 < a → 0 < δ → 0 < a + lam →
      ∀ {s u : ℂ}, (∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
          ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L) →
        s.re = 1 + a / L → Work.LinnikContract.zeroMult χ u ≠ 0 →
        ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ →
        (Work.LinnikContract.zeroMult χ u : ℝ)
          * (P3 (((a + lam : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ)
    (hExt2 : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      {L a lam δ : ℝ}, 0 < L → 0 < a → 0 < δ → 0 < a + lam →
      ∀ {s u₁ u₂ : ℂ}, (∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
          ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L) →
        s.re = 1 + a / L →
        Work.LinnikContract.zeroMult χ u₁ ≠ 0 →
        Work.LinnikContract.zeroMult χ u₂ ≠ 0 → u₁ ≠ u₂ →
        ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u₁‖ ≤ δ →
        ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u₂‖ ≤ δ →
        (Work.LinnikContract.zeroMult χ u₁ : ℝ)
            * (P3 (((a + lam : ℝ) : ℂ) / ((s - u₁) * (L : ℂ)))).re
          + (Work.LinnikContract.zeroMult χ u₂ : ℝ)
            * (P3 (((a + lam : ℝ) : ℂ) / ((s - u₂) * (L : ℂ)))).re
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ)
    (hNnn : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {L a lam δ : ℝ},
      0 < L → 0 < a → 0 < δ → 0 < a + lam → ∀ {s : ℂ},
      (∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
          ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L) →
      s.re = 1 + a / L → 0 ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ)
    (hZ2s : ∀ {a α δ L γ : ℝ}, 0 < a → a ≤ α → α ≤ 3918/1000 → 0 < δ → 0 < L →
      10000 ≤ δ * L → δ / 3 ≤ |γ| →
      14900 * (P3 ((α:ℂ) / ((a:ℂ) + (((2*γ*L:ℝ)):ℂ) * Complex.I))).re ≤ 1)
    (hZ4s : ∀ {a α δ L γ : ℝ}, 0 < a → a ≤ α → α ≤ 3918/1000 → 0 < δ → 0 < L →
      10000 ≤ δ * L → δ / 5 ≤ |γ| →
      1250 * (P3 ((α:ℂ) / ((a:ℂ) + (((4*γ*L:ℝ)):ℂ) * Complex.I))).re ≤ 1)
    : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      518/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨Q1, hQ1⟩ := hP
  obtain ⟨δ, hδpos, hδlt1, Q2, hQ2⟩ := hS
  refine ⟨max (max Q1 Q2) (max (Nat.ceil (Real.exp (10000 / δ)) + 1) 3), ?_⟩
  intro q hq _inst χ₁ ρ₁ hm hsq him
  have hq1 : Q1 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.1.1
  have hq2 : Q2 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.1.2
  have hqA : Nat.ceil (Real.exp (10000 / δ)) + 1 ≤ q := by
    have h := hq; simp only [max_le_iff] at h; exact h.2.1
  have hq3 : 3 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.2.2
  have hq1' : 1 < q := by omega
  have hLpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq1')
  have hLbig : 10000 / δ ≤ Real.log (q:ℝ) := by
    have h1 : Real.exp (10000 / δ) ≤ ((Nat.ceil (Real.exp (10000 / δ)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (10000 / δ)) : ℕ) : ℝ) ≤ (q : ℝ) := by
      have h3 : Nat.ceil (Real.exp (10000 / δ)) ≤ q := by omega
      exact_mod_cast h3
    have h3 : Real.exp (10000 / δ) ≤ (q : ℝ) := le_trans h1 h2
    have h4 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h4
  by_contra hcon
  push_neg at hcon
  have hχne : χ₁ ≠ 1 := hm.1.1.1
  have hmult : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  have hγle : |ρ₁.im| ≤ 1 := hm.1.1.2.2
  set L : ℝ := Real.log (q:ℝ) with hLdef
  set a : ℝ := 17/5 with hadef
  set lam : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlamdef
  set γ : ℝ := ρ₁.im with hγdef
  set σ : ℝ := 1 + a/L with hσdef
  set α : ℝ := a + lam with hαdef
  have hLpos' : 0 < L := by rw [hLdef]; exact hLpos
  have hLne : L ≠ 0 := ne_of_gt hLpos'
  have hane : a ≠ 0 := by rw [hadef]; norm_num
  have hapos : 0 < a := by rw [hadef]; norm_num
  have hLbig' : 10000 / δ ≤ L := by rw [hLdef]; exact hLbig
  have hlamlt : lam < 518/1000 := by rw [hlamdef]; exact hcon
  have hlamle : lam ≤ 518/1000 := le_of_lt hlamlt
  have hρre : ρ₁.re = 1 - lam/L := by
    rw [hlamdef, hLdef, Work.LinnikContract.lamOf]
    have hLne2 : Real.log (q:ℝ) ≠ 0 := ne_of_gt hLpos
    field_simp
    ring
  have hρim : ρ₁.im = γ := by rw [hγdef]
  have hγab : |γ| ≤ 1 := by rw [hγdef]; exact hγle
  have hγne : γ ≠ 0 := by rw [hγdef]; exact him
  have hρlt1 : ρ₁.re < 1 := by
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hprim : χ₁.primitiveCharacter ≠ 1 := by
      intro h1
      have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ₁
      rw [h1, DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level] at h2
      exact hχne h2.symm
    have hz := apply_eq_zero_of_analyticOrderNatAt_ne_zero hmult
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hprim
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hz).2
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef, Work.LinnikContract.lamOf]
    have hq1r : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    nlinarith only [hρlt1, Real.log_nonneg hq1r]
  have hαpos : 0 < α := by rw [hαdef]; linarith
  have hαapos : 0 < a + lam := by rw [← hαdef]; exact hαpos
  have hσ1 : 1 < σ := by
    rw [hσdef]; have : 0 < a/L := div_pos hapos hLpos'; linarith
  have hLsmall : lam / L ≤ δ / 2 := by
    have h1 : lam / L ≤ (518/1000) / L := by
      rw [div_le_div_iff₀ hLpos' hLpos']; nlinarith only [hlamle, hLpos']
    have h2 : (518/1000) / L ≤ (518/1000) / (10000/δ) := by
      rw [div_le_div_iff₀ hLpos' (by positivity : (0:ℝ) < 10000/δ)]
      nlinarith only [hLbig']
    have h3 : (518/1000) / (10000/δ) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 10000/δ)]
      have h5 : (δ/2) * (10000/δ) = 5000 := by field_simp; ring
      rw [h5]; norm_num
    linarith
  have hLsmall' : lam / L ≤ δ := le_trans hLsmall (by linarith [hδpos])
  have hαle : α ≤ 3918/1000 := by rw [hαdef, hadef]; linarith
  -- minimality
  have hmin1 : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ₁ u' ≠ 0 → |u'.im| ≤ 10 →
      lam ≤ (1 - u'.re) * L := by
    intro u' hu' him'
    have h := hm.2 χ₁ u' hχne hu' him'
    simpa [hlamdef, hLdef, Work.LinnikContract.lamOf] using h
  -- conjugate-zero facts
  have hmultc : Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) ≠ 0 := by
    rw [Work.A7.zeroMult_conj_sq_one χ₁ hsq ρ₁]; exact hmult
  have hγcle : |(starRingEnd ℂ ρ₁).im| ≤ 10 := by
    rw [Complex.conj_im]; rw [abs_neg]; linarith [hγab]
  have hρ₁conj_ne : (starRingEnd ℂ ρ₁) ≠ ρ₁ := by
    intro h
    have h1 := congrArg Complex.im h
    rw [Complex.conj_im] at h1
    have h2 : γ = 0 := by rw [hγdef]; linarith
    exact hγne h2
  -- the five points
  have hpoint : 0 ≤ 14379 * SigmaP3L q L 1 ((σ : ℂ)) a lam
      + 24480 * SigmaP3L q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam
      + 14900 * SigmaP3L q L 1 ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) a lam
      + 6000 * SigmaP3L q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam
      + 1250 * SigmaP3L q L 1 ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) a lam :=
    hChen q χ₁ hsq (σ := σ) (γ := γ) (a := a) (lam := lam) (L := L) hLpos' hσ1 hαapos
  -- the argument identities
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ :=
    hArg (σ := σ) (L := L) (a := a) (lam := lam) (γ := γ) hσdef hLne (ρ := ρ₁) hρre hρim
  -- imaginary part bounds
  have him0 : |(((σ : ℂ))).im| ≤ 4 := by simp
  have him1 : |(((σ : ℂ) + (γ : ℂ) * Complex.I)).im| ≤ 3 := by
    have h : (((σ : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
    rw [h]; linarith [hγab]
  have him2 : |(((σ : ℂ) + 2 * (γ : ℂ) * Complex.I)).im| ≤ 4 := by
    have h : (((σ : ℂ) + 2 * (γ : ℂ) * Complex.I)).im = 2 * γ := by simp
    rw [h, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hγab]
  have him3 : |(((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).im| ≤ 3 := by
    have h : (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).im = 3 * γ := by simp
    rw [h, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    linarith [hγab]
  have him4 : |(((σ : ℂ) + 4 * (γ : ℂ) * Complex.I)).im| ≤ 4 := by
    have h : (((σ : ℂ) + 4 * (γ : ℂ) * Complex.I)).im = 4 * γ := by simp
    rw [h, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    linarith [hγab]
  have hre0 : (((σ : ℂ))).re = 1 + (17 / 5) / Real.log q := by
    have h : (((σ : ℂ))).re = σ := by simp
    rw [h, hσdef, hadef, hLdef]
  have hre1 : (((σ : ℂ) + (γ : ℂ) * Complex.I)).re = 1 + (17 / 5) / Real.log q := by
    have h : (((σ : ℂ) + (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef, hadef, hLdef]
  have hre2 : (((σ : ℂ) + 2 * (γ : ℂ) * Complex.I)).re = 1 + (17 / 5) / Real.log q := by
    have h : (((σ : ℂ) + 2 * (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef, hadef, hLdef]
  have hre3 : (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).re = 1 + (17 / 5) / Real.log q := by
    have h : (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef, hadef, hLdef]
  have hre4 : (((σ : ℂ) + 4 * (γ : ℂ) * Complex.I)).re = 1 + (17 / 5) / Real.log q := by
    have h : (((σ : ℂ) + 4 * (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef, hadef, hLdef]
  -- the five sum bounds
  have b0 := hQ1 q hq1 lam ((σ : ℂ)) hlam0 hlamle hre0 him0
  have b1 := hQ2 q hq2 χ₁ hχne hsq lam ((σ : ℂ) + (γ : ℂ) * Complex.I) hlam0 hlamle hre1 him1
  have b2 := hQ1 q hq1 lam ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) hlam0 hlamle hre2 him2
  have b3 := hQ2 q hq2 χ₁ hχne hsq lam ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) hlam0 hlamle hre3 him3
  have b4 := hQ1 q hq1 lam ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) hlam0 hlamle hre4 him4
  -- rewrite the arguments of the principal bounds
  have harg0 : ((((((17 : ℝ) / 5) + lam) : ℂ)
        / ((((σ : ℂ)) - 1) * (((Real.log (q:ℝ) : ℝ)) : ℂ))))
      = ((α/a : ℝ) : ℂ) := by
    rw [ha5, show ((α/a : ℝ) : ℂ) = ((α:ℂ)) / ((a:ℂ)) from Complex.ofReal_div α a]
    congr 1
    rw [hαdef, hadef]
    push_cast
    ring
  have harg2 : ((((((17 : ℝ) / 5) + lam) : ℂ)
        / ((((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) - 1) * (((Real.log (q:ℝ) : ℝ)) : ℂ))))
      = (((α : ℂ)) / (((a : ℂ)) + (((2*γ*L:ℝ)):ℂ)*Complex.I)) := by
    rw [ha6]
    congr 1
    rw [hαdef, hadef]
    push_cast
    ring
  have harg4 : ((((((17 : ℝ) / 5) + lam) : ℂ)
        / ((((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) - 1) * (((Real.log (q:ℝ) : ℝ)) : ℂ))))
      = (((α : ℂ)) / (((a : ℂ)) + (((4*γ*L:ℝ)):ℂ)*Complex.I)) := by
    rw [ha7]
    congr 1
    rw [hαdef, hadef]
    push_cast
    ring
  rw [harg0, P3_ofReal (α/a)] at b0
  rw [harg2] at b2
  rw [harg4] at b4
  -- define the values
  set Z2 : ℝ := (P3 (((α:ℂ)) / (((a:ℂ)) + (((2*γ*L:ℝ)):ℂ)*Complex.I))).re with hZ2def
  set Z4 : ℝ := (P3 (((α:ℂ)) / (((a:ℂ)) + (((4*γ*L:ℝ)):ℂ)*Complex.I))).re with hZ4def
  set W2 : ℝ := (P3 (((α:ℂ)) / (((α:ℂ)) + (((2*γ*L:ℝ)):ℂ)*Complex.I))).re with hW2def
  set W4 : ℝ := (P3 (((α:ℂ)) / (((α:ℂ)) + (((4*γ*L:ℝ)):ℂ)*Complex.I))).re with hW4def
  have hW2nn : 0 ≤ W2 := by rw [hW2def]; exact P3_re_self_nonneg hαpos
  have hW4nn : 0 ≤ W4 := by rw [hW4def]; exact P3_re_self_nonneg hαpos
  -- the comparison bounds
  have hZ2cmp : 14900 * Z2 ≤ 30480 * W2 := by
    have h := hCmp α a (2*γ*L) hαpos hapos (by rw [hαdef]; linarith)
    have h32 : (α/a)^3 ≤ 30480/14900 := by
      have h4 : α/a ≤ 3918/3400 := by
        rw [div_le_div_iff₀ hapos (by norm_num : (0:ℝ) < 3400), hadef]; nlinarith only [hαle]
      have h5 : 0 ≤ α/a := by positivity
      nlinarith only [h4, h5, sq_nonneg (α/a), pow_le_pow_left₀ h5 h4 3]
    rw [hZ2def, hW2def]
    nlinarith only [h, h32, hW2nn]
  have hZ4cmp : 1250 * Z4 ≤ 6000 * W4 := by
    have h := hCmp α a (4*γ*L) hαpos hapos (by rw [hαdef]; linarith)
    have h32 : (α/a)^3 ≤ 6000/1250 := by
      have h4 : α/a ≤ 3918/3400 := by
        rw [div_le_div_iff₀ hapos (by norm_num : (0:ℝ) < 3400), hadef]; nlinarith only [hαle]
      have h5 : 0 ≤ α/a := by positivity
      nlinarith only [h4, h5, sq_nonneg (α/a), pow_le_pow_left₀ h5 h4 3]
    rw [hZ4def, hW4def]
    nlinarith only [h, h32, hW4nn]
  -- the near norms
  obtain ⟨hn1, hn2, hn3, hn4⟩ :=
    hNorm (L := L) (lam := lam) (γ := γ) (δ := δ) hδpos (ρ := ρ₁) hρre hρim
  -- ## The three-case analysis
  --
  -- `A = [(lam/L)^2 + (2*γ)^2 ≤ δ^2]` (⟺ `ρ̄₁` is in the window at `s₁ = σ+iγ`, by `hn3`),
  -- `B = [(lam/L)^2 + (4*γ)^2 ≤ δ^2]` (⟺ `ρ̄₁` is in the window at `s₃ = σ+3iγ`, by `hn4`),
  -- and `B ⟹ A`.  `ρ₁` is always in the window at `s₁` (by `hn1`, using `hLsmall`).
  have haα : a ≤ α := by rw [hαdef]; linarith [hlam0]
  have hαne : a + lam ≠ 0 := ne_of_gt hαapos
  have hδL : 10000 ≤ δ * L := by
    have h := mul_le_mul_of_nonneg_left hLbig' (le_of_lt hδpos)
    have h2 : δ * (10000 / δ) = 10000 := by field_simp
    linarith [h, h2]
  -- minimality in the "window" form required by the extraction lemmas
  have hminWin : ∀ (c : ℝ), |c| ≤ 9 → ∀ u' : ℂ, Work.LinnikContract.zeroMult χ₁ u' ≠ 0 →
      ‖(1 : ℂ) + (c : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L := by
    intro c hc u' hu' hnear
    refine hmin1 u' hu' ?_
    have h1 : |c - u'.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (c : ℂ) * Complex.I - u')
      have him : ((1 : ℂ) + (c : ℂ) * Complex.I - u').im = c - u'.im := by simp
      rw [him] at h
      exact h.trans hnear
    have h2 : |u'.im| ≤ |c| + |c - u'.im| := by
      calc |u'.im| = |c - (c - u'.im)| := by congr 1; ring
        _ ≤ |c| + |c - u'.im| := abs_sub _ _
    linarith [h1, h2, hc, hδlt1]
  have hminW1 : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ₁ u' ≠ 0 →
      ‖(1 : ℂ) + (((σ : ℂ) + (γ : ℂ) * Complex.I).im : ℂ) * Complex.I - u'‖ ≤ δ →
      lam ≤ (1 - u'.re) * L := by
    intro u' hu' hnear
    refine hminWin γ (by linarith [hγab]) u' hu' ?_
    simpa using hnear
  have hminW3 : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ₁ u' ≠ 0 →
      ‖(1 : ℂ) + (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I).im : ℂ) * Complex.I - u'‖ ≤ δ →
      lam ≤ (1 - u'.re) * L := by
    intro u' hu' hnear
    refine hminWin (3 * γ) ?_ u' hu' ?_
    · rw [abs_mul]
      have h3 : |(3 : ℝ)| = 3 := abs_of_nonneg (by norm_num)
      rw [h3]
      linarith [hγab]
    · simpa using hnear
  have hsre1 : (((σ : ℂ) + (γ : ℂ) * Complex.I)).re = 1 + a / L := by
    have h : (((σ : ℂ) + (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef]
  have hsre3 : (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).re = 1 + a / L := by
    have h : (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I)).re = σ := by simp
    rw [h, hσdef]
  -- the near/near conditions and the multiplicity lower bounds
  have hbA : (lam / L) ^ 2 ≤ δ ^ 2 := by
    have h1 : 0 ≤ lam / L := div_nonneg hlam0 (le_of_lt hLpos')
    have h2 : lam / L ≤ δ / 2 := hLsmall
    nlinarith only [h1, h2, hδpos]
  have hL2 : (lam / L) ^ 2 ≤ δ ^ 2 / 4 := by
    have h1 : 0 ≤ lam / L := div_nonneg hlam0 (le_of_lt hLpos')
    have h2 : lam / L ≤ δ / 2 := hLsmall
    nlinarith only [h1, h2, hδpos]
  have hnear1ρ : ‖(1 : ℂ) + (((σ : ℂ) + (γ : ℂ) * Complex.I).im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
    simpa using hn1.mpr hbA
  have hz1 : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) := by
    have h1 : 1 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ := Nat.one_le_iff_ne_zero.mpr hmult
    exact_mod_cast h1
  have hzc : (1 : ℝ) ≤ (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) := by
    have h1 : 1 ≤ Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) :=
      Nat.one_le_iff_ne_zero.mpr hmultc
    exact_mod_cast h1
  -- the five bounds, restated in the abbreviations of this file
  have hb0' : SigmaP3L q L 1 ((σ : ℂ)) a lam ≤ P3R (α / a) + 1 / 100000 := b0
  have hb1' : SigmaP3L q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam
      ≤ - Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ
        + α * (1 / 8 + 1 / 100000) := b1
  have hb2' : SigmaP3L q L 1 ((σ : ℂ) + 2 * (γ : ℂ) * Complex.I) a lam ≤ Z2 + 1 / 100000 := b2
  have hb3' : SigmaP3L q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam
      ≤ - Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ
        + α * (1 / 8 + 1 / 100000) := b3
  have hb4' : SigmaP3L q L 1 ((σ : ℂ) + 4 * (γ : ℂ) * Complex.I) a lam ≤ Z4 + 1 / 100000 := b4
  -- the final bookkeeping: `Fpoly lam = 14379 P₃(α/a) - 24480 P₃(1) + 3810 α`
  have hfp : Fpoly lam = 14379 * P3R (α / a) - 24480 * P3R 1 + 3810 * α := by
    have h1 := F_eq_poly lam
    simp only [Fpoly, hαdef, hadef] at h1 ⊢
    exact h1.symm
  have hfinish : ∀ x : ℝ, -7 / 2 ≤ x → Fpoly lam = x → False := by
    intro x hx hfx
    have h1 : Fpoly lam ≤ Fpoly (518 / 1000) := Fpoly_mono hlam0 hlamle
    rw [← hfx] at hx
    linarith [hx, h1, Fpoly_518_lt]
  -- the single-term extraction at `s₁` (used in the case `¬A`)
  have hP1leN1 : P3R 1 ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ := by
    have h2 := hExt1 (q := q) χ₁ (L := L) (a := a) (lam := lam) (δ := δ) hLpos' hapos hδpos
      hαapos (s := (σ : ℂ) + (γ : ℂ) * Complex.I) hminW1 hsre1 hmult hnear1ρ
    rw [ha1, P3_div_self hαne] at h2
    have h3 : P3R 1 ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * P3R 1 := by
      simpa using mul_le_mul_of_nonneg_right hz1 (le_of_lt P3R_one_pos)
    linarith [h2, h3]
  by_cases hA : (lam / L) ^ 2 + (2 * γ) ^ 2 ≤ δ ^ 2
  · by_cases hB : (lam / L) ^ 2 + (4 * γ) ^ 2 ≤ δ ^ 2
    · -- ## Case `A ∧ B`
      have hnear1ρc : ‖(1 : ℂ) + (((σ : ℂ) + (γ : ℂ) * Complex.I).im : ℂ) * Complex.I
          - starRingEnd ℂ ρ₁‖ ≤ δ := by
        simpa using hn3.mpr hA
      have hnear3ρ : ‖(1 : ℂ) + (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I).im : ℂ) * Complex.I
          - ρ₁‖ ≤ δ := by
        simpa using hn2.mpr hA
      have hnear3ρc : ‖(1 : ℂ) + (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I).im : ℂ) * Complex.I
          - starRingEnd ℂ ρ₁‖ ≤ δ := by
        simpa using hn4.mpr hB
      have hPW1 : P3R 1 + W2
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ := by
        have h2 := hExt2 (q := q) χ₁ (L := L) (a := a) (lam := lam) (δ := δ) hLpos' hapos hδpos
          hαapos (s := (σ : ℂ) + (γ : ℂ) * Complex.I) (u₁ := ρ₁) (u₂ := starRingEnd ℂ ρ₁)
          hminW1 hsre1 hmult hmultc (Ne.symm hρ₁conj_ne) hnear1ρ hnear1ρc
        rw [ha1, ha2, P3_div_self hαne] at h2
        have h2' : (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * P3R 1
            + (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W2
            ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ := h2
        have h3 : P3R 1 ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * P3R 1 := by
          simpa using mul_le_mul_of_nonneg_right hz1 (le_of_lt P3R_one_pos)
        have h4 : W2 ≤ (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W2 := by
          simpa using mul_le_mul_of_nonneg_right hzc hW2nn
        linarith [h2', h3, h4]
      have hW2W4 : W2 + W4
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ := by
        have h2 := hExt2 (q := q) χ₁ (L := L) (a := a) (lam := lam) (δ := δ) hLpos' hapos hδpos
          hαapos (s := (σ : ℂ) + 3 * (γ : ℂ) * Complex.I) (u₁ := ρ₁) (u₂ := starRingEnd ℂ ρ₁)
          hminW3 hsre3 hmult hmultc (Ne.symm hρ₁conj_ne) hnear3ρ hnear3ρc
        rw [ha3, ha4] at h2
        have h2' : (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * W2
            + (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W4
            ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ := h2
        have h3 : W2 ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * W2 := by
          simpa using mul_le_mul_of_nonneg_right hz1 hW2nn
        have h4 : W4 ≤ (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W4 := by
          simpa using mul_le_mul_of_nonneg_right hzc hW4nn
        linarith [h2', h3, h4]
      have hstep : 0 ≤ 14379 * P3R (α / a) - 24480 * P3R 1
          + 30480 * α * (1 / 8 + 1 / 100000) + 30529 * (1 / 100000) := by
        linarith [hpoint, hb0', hb1', hb2', hb3', hb4', hPW1, hW2W4, hZ2cmp, hZ4cmp]
      have hkey : -7 / 2 ≤ 14379 * P3R (α / a) - 24480 * P3R 1 + 3810 * α := by
        nlinarith only [hstep, hαle]
      exact hfinish _ hkey hfp
    · -- ## Case `A ∧ ¬B`
      have hnear1ρc : ‖(1 : ℂ) + (((σ : ℂ) + (γ : ℂ) * Complex.I).im : ℂ) * Complex.I
          - starRingEnd ℂ ρ₁‖ ≤ δ := by
        simpa using hn3.mpr hA
      have hnear3ρ : ‖(1 : ℂ) + (((σ : ℂ) + 3 * (γ : ℂ) * Complex.I).im : ℂ) * Complex.I
          - ρ₁‖ ≤ δ := by
        simpa using hn2.mpr hA
      have hPW1 : P3R 1 + W2
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ := by
        have h2 := hExt2 (q := q) χ₁ (L := L) (a := a) (lam := lam) (δ := δ) hLpos' hapos hδpos
          hαapos (s := (σ : ℂ) + (γ : ℂ) * Complex.I) (u₁ := ρ₁) (u₂ := starRingEnd ℂ ρ₁)
          hminW1 hsre1 hmult hmultc (Ne.symm hρ₁conj_ne) hnear1ρ hnear1ρc
        rw [ha1, ha2, P3_div_self hαne] at h2
        have h2' : (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * P3R 1
            + (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W2
            ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + (γ : ℂ) * Complex.I) a lam δ := h2
        have h3 : P3R 1 ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * P3R 1 := by
          simpa using mul_le_mul_of_nonneg_right hz1 (le_of_lt P3R_one_pos)
        have h4 : W2 ≤ (Work.LinnikContract.zeroMult χ₁ (starRingEnd ℂ ρ₁) : ℝ) * W2 := by
          simpa using mul_le_mul_of_nonneg_right hzc hW2nn
        linarith [h2', h3, h4]
      have hW2leN3 : W2
          ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ := by
        have h2 := hExt1 (q := q) χ₁ (L := L) (a := a) (lam := lam) (δ := δ) hLpos' hapos hδpos
          hαapos (s := (σ : ℂ) + 3 * (γ : ℂ) * Complex.I) hminW3 hsre3 hmult hnear3ρ
        rw [ha3] at h2
        have h2' : (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * W2
            ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ := h2
        have h3 : W2 ≤ (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) * W2 := by
          simpa using mul_le_mul_of_nonneg_right hz1 hW2nn
        linarith [h2', h3]
      have hγ5 : δ / 5 ≤ |γ| := by
        have hgt : δ ^ 2 < (lam / L) ^ 2 + (4 * γ) ^ 2 := not_le.mp hB
        have hsq : (δ / 5) ^ 2 ≤ |γ| ^ 2 := by
          rw [sq_abs γ]
          nlinarith only [hL2, hgt, hδpos]
        have h3nn : 0 ≤ δ / 5 := by positivity
        have h4 : |δ / 5| ≤ |γ| := by simpa using sq_le_sq.mp hsq
        simpa [abs_of_nonneg h3nn] using h4
      have hZ4sm : 1250 * Z4 ≤ 1 := hZ4s hapos haα hαle hδpos hLpos' hδL hγ5
      have hstep : 0 ≤ 14379 * P3R (α / a) - 24480 * P3R 1
          + 30480 * α * (1 / 8 + 1 / 100000) + 30529 * (1 / 100000) + 1 := by
        linarith [hpoint, hb0', hb1', hb2', hb3', hb4', hPW1, hW2leN3, hZ2cmp, hZ4sm, hW2nn]
      have hkey : -7 / 2 ≤ 14379 * P3R (α / a) - 24480 * P3R 1 + 3810 * α := by
        nlinarith only [hstep, hαle]
      exact hfinish _ hkey hfp
  · -- ## Case `¬A`
    have hγ3 : δ / 3 ≤ |γ| := by
      have hgt : δ ^ 2 < (lam / L) ^ 2 + (2 * γ) ^ 2 := not_le.mp hA
      have hsq : (δ / 3) ^ 2 ≤ |γ| ^ 2 := by
        rw [sq_abs γ]
        nlinarith only [hL2, hgt, hδpos]
      have h3nn : 0 ≤ δ / 3 := by positivity
      have h4 : |δ / 3| ≤ |γ| := by simpa using sq_le_sq.mp hsq
      simpa [abs_of_nonneg h3nn] using h4
    have hZ2sm : 14900 * Z2 ≤ 1 := hZ2s hapos haα hαle hδpos hLpos' hδL hγ3
    have hγ5 : δ / 5 ≤ |γ| := le_trans (by linarith [hδpos]) hγ3
    have hZ4sm : 1250 * Z4 ≤ 1 := hZ4s hapos haα hαle hδpos hLpos' hδL hγ5
    have hN3nn : 0 ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ₁ ((σ : ℂ) + 3 * (γ : ℂ) * Complex.I) a lam δ :=
      hNnn χ₁ hLpos' hapos hδpos hαapos hminW3 hsre3
    have hstep : 0 ≤ 14379 * P3R (α / a) - 24480 * P3R 1
        + 30480 * α * (1 / 8 + 1 / 100000) + 30529 * (1 / 100000) + 2 := by
      linarith [hpoint, hb0', hb1', hb2', hb3', hb4', hP1leN1, hN3nn, hZ2sm, hZ4sm]
    have hkey : -7 / 2 ≤ 14379 * P3R (α / a) - 24480 * P3R 1 + 3810 * α := by
      nlinarith only [hstep, hαle]
    exact hfinish _ hkey hfp

/-- The required statement: the `h = 2` case of Heath-Brown's Lemma 9.5.  Obtained from
`main_assembly` by supplying its twelve inputs: the principal-character bound
(`PrincipalSigmaBoundD`), the Σ-bound for real characters (HB Lemma 3.1 at `φ = 1/4` —
`Table4.logDerivHyp_eighth` — fed into the §8.2 engine `PrimitiveSigmaEngine` for the primitive
character and corrected by `ImprimitiveSigmaReduce`), the pointwise Chen inequality
(`ChenSumNonneg2`), and the elementary `P₃` comparisons and near-sum extractions. -/
theorem Lam1Lower : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
    518/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  -- ## the principal-character bound
  obtain ⟨qP, hPraw⟩ := PrincipalSigmaBoundD (M := 518 / 1000) (ε := 1 / 1000000)
    (by norm_num) (by norm_num)
  have hP : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ 518 / 1000 → s.re = 1 + (17 / 5) / Real.log q → |s.im| ≤ 4 →
      Work.ZeroFreeTables.SigmaP3L q (Real.log q) (1 : DirichletCharacter ℂ q) s (17 / 5) lam₁
        ≤ (Work.ZeroFreeTables.P3 (((((17 : ℝ) / 5) + lam₁) : ℂ)
              / ((s - 1) * ((Real.log q : ℝ) : ℂ)))).re + 1 / 100000 := by
    refine ⟨qP, ?_⟩
    intro q hq _inst lam₁ s h0 h1 hre him
    have h2 := hPraw q hq lam₁ s h0 h1 hre him
    have h3 : ((17 : ℝ) / 5 + lam₁) * (1 / 1000000) ≤ 1 / 100000 := by nlinarith [h1]
    linarith
  -- ## HB Lemma 3.1 at `φ = 1/4`, the §8.2 engine, and the imprimitive correction
  obtain ⟨Lp, δ, hδ0, hδ1, hLD⟩ :=
    Work.ZeroFreeTables.Table4.logDerivHyp_eighth (e := 1 / 400000) (by norm_num)
  obtain ⟨Le, hE⟩ := PrimitiveSigmaEngine (a := 17 / 5) (δ := δ) (c := 1 / 8 + 1 / 400000)
    (e := 1 / 400000) (by norm_num) hδ0 hδ1 (by norm_num) (by norm_num)
  obtain ⟨Li, hI⟩ := ImprimitiveSigmaReduce (a := 17 / 5) (e := 1 / 400000)
    (by norm_num) (by norm_num)
  have hS : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → χ ^ 2 = 1 → ∀ (lam₁ : ℝ) (s : ℂ),
      0 ≤ lam₁ → lam₁ ≤ 518 / 1000 → s.re = 1 + (17 / 5) / Real.log q → |s.im| ≤ 3 →
      Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s (17 / 5) lam₁
        ≤ - Work.ZeroFreeTables.P9.nearP3sum q (Real.log q) χ s (17 / 5) lam₁ δ
          + (((17 : ℝ) / 5) + lam₁) * (1 / 8 + 1 / 100000) := by
    refine ⟨δ, hδ0, hδ1, ⌈Real.exp (max (max Lp Le) Li)⌉₊ + 1, ?_⟩
    intro q hq _inst χ hχ hreal lam₁ s hlam0 hlamle hsre hsim
    haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    -- `log q` is beyond all the thresholds
    have hexp : Real.exp (max (max Lp Le) Li) ≤ (q : ℝ) := by
      have h1 : Real.exp (max (max Lp Le) Li)
          ≤ ((⌈Real.exp (max (max Lp Le) Li)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp (max (max Lp Le) Li)⌉₊ : ℕ) : ℝ)
          ≤ ((⌈Real.exp (max (max Lp Le) Li)⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h3 : ((⌈Real.exp (max (max Lp Le) Li)⌉₊ + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hq
      linarith
    have hLbig : max (max Lp Le) Li ≤ Real.log (q : ℝ) := by
      rw [← Real.log_exp (max (max Lp Le) Li)]
      exact Real.log_le_log (Real.exp_pos _) hexp
    have hLp' : Lp ≤ Real.log (q : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLbig
    have hLe' : Le ≤ Real.log (q : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLbig
    have hLi' : Li ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hLbig
    -- HB Lemma 3.1 for the primitive character
    have hχ' : χ.primitiveCharacter ≠ 1 := by
      intro h1
      apply hχ
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
      exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
    have hχ'2 : χ.primitiveCharacter ^ 2 = 1 := by
      have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
          (χ.primitiveCharacter ^ 2) = 1 := by
        rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, hreal]
      exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
        (by rw [hmap, DirichletCharacter.changeLevel_one])
    have hconle : ((χ.conductor : ℕ) : ℝ) ≤ (q : ℝ) := by
      have hpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      exact_mod_cast (Nat.le_of_dvd hpos χ.conductor_dvd_level)
    have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)) hconle
    have hLDq : Work.ZeroFreeTables.LogDerivHyp χ.primitiveCharacter δ (Real.log (q : ℝ))
        (1 / 8 + 1 / 400000) :=
      hLD χ.primitiveCharacter hχ' (DirichletCharacter.primitiveCharacter_isPrimitive χ)
        hχ'2 hLp' hlogN
    -- the engine for the primitive character
    have heng : Work.ZeroFreeTables.SigmaP3L χ.conductor (Real.log (q : ℝ)) χ.primitiveCharacter
          s (17 / 5) lam₁
        ≤ - Work.ZeroFreeTables.P9.nearP3sum χ.conductor (Real.log (q : ℝ)) χ.primitiveCharacter
              s (17 / 5) lam₁ δ + (17 / 5 + lam₁) * (1 / 8 + 1 / 400000 + 1 / 400000) := by
      have h := hE (L := Real.log (q : ℝ)) χ.primitiveCharacter hχ'
        (DirichletCharacter.primitiveCharacter_isPrimitive χ) hLe' hlogN hlam0
        (le_trans hlamle (by norm_num)) hLDq s hsre hsim
      have hc : (17 / 5 + lam₁) * (1 / 8 + 1 / 400000 + 1 / 400000)
          = (17 / 5 + lam₁) * (1 / 8 + 1 / 400000) + (17 / 5 + lam₁) * (1 / 400000) := by ring
      linarith [h, hc]
    -- the imprimitive correction
    have himp : Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s (17 / 5) lam₁
        ≤ Work.ZeroFreeTables.SigmaP3L χ.conductor (Real.log (q : ℝ)) χ.primitiveCharacter
            s (17 / 5) lam₁ + (17 / 5 + lam₁) * (1 / 400000) := by
      have h := hI (L := Real.log (q : ℝ)) χ hχ hreal hLi' le_rfl hlam0
        (le_trans hlamle (by norm_num)) s hsre hsim
      simpa using h
    -- the near sums agree at the level and at the conductor
    have hnear : Work.ZeroFreeTables.P9.nearP3sum χ.conductor (Real.log (q : ℝ))
          χ.primitiveCharacter s (17 / 5) lam₁ δ
        = Work.ZeroFreeTables.P9.nearP3sum q (Real.log (q : ℝ)) χ s (17 / 5) lam₁ δ := by
      simpa using nearP3sum_primitiveCharacter_eq (q := q) χ (L := Real.log (q : ℝ))
        (a := 17 / 5) (lam := lam₁) (δ := δ) s
    have hε : (1 / 8 + 1 / 400000 + 1 / 400000 + 1 / 400000 : ℝ) ≤ 1 / 8 + 1 / 100000 := by
      norm_num
    have hcoef : (0 : ℝ) ≤ 17 / 5 + lam₁ := by linarith
    have hmul : (17 / 5 + lam₁) * (1 / 8 + 1 / 400000 + 1 / 400000 + 1 / 400000)
        ≤ (17 / 5 + lam₁) * (1 / 8 + 1 / 100000) :=
      mul_le_mul_of_nonneg_left hε hcoef
    calc Work.ZeroFreeTables.SigmaP3L q (Real.log q) χ s (17 / 5) lam₁
        ≤ Work.ZeroFreeTables.SigmaP3L χ.conductor (Real.log (q : ℝ)) χ.primitiveCharacter
            s (17 / 5) lam₁ + (17 / 5 + lam₁) * (1 / 400000) := himp
      _ ≤ - Work.ZeroFreeTables.P9.nearP3sum χ.conductor (Real.log (q : ℝ)) χ.primitiveCharacter
              s (17 / 5) lam₁ δ
            + (17 / 5 + lam₁) * (1 / 8 + 1 / 400000 + 1 / 400000 + 1 / 400000) := by
          linarith [heng]
      _ = - Work.ZeroFreeTables.P9.nearP3sum q (Real.log (q : ℝ)) χ s (17 / 5) lam₁ δ
            + (17 / 5 + lam₁) * (1 / 8 + 1 / 400000 + 1 / 400000 + 1 / 400000) := by rw [hnear]
      _ ≤ - Work.ZeroFreeTables.P9.nearP3sum q (Real.log (q : ℝ)) χ s (17 / 5) lam₁ δ
            + (((17 : ℝ) / 5) + lam₁) * (1 / 8 + 1 / 100000) := by linarith [hmul]
  exact main_assembly hP hS ChenSumNonneg2 P3PhiLe P3ReDecay2 ArgIdentities NearNorm
    NearP3sumExtract2 NearP3sumExtractTwo2 NearP3sumNonneg2 Z2Small Z4Small

end Work.ZeroFreeTables.XY
