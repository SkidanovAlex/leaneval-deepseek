import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Interfaces between the stages of `build_quadruples`

The scaling-down step (MRT Fourier, Prop. 3.1; MRTTZ Prop. 3.4) produces, from a phase family
at scale `(X, H)`, a phase family at scale `(X/a, H/a)` in which each new interval is hit by
`≫ π₀(a)` rescaled old intervals whose phase is `PolyRel`-related to the new one. `incPairs` is
the set of those incidences.

The prime range `[a, b]` produced by a scaling-down step is always *narrow* (`5 b ≤ 7 a`), and the
new length is exactly `H/a`; this is what makes the two chained scalings fit the exact conventions
of `QuadData` (`EdgeGeom` wants primes in `[P₁, 2P₁]`, `rel` wants moduli in `[P₂/2, P₂]`).
-/

open Classical
open Polynomial Finset Real Complex MeasureTheory
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-- The pairs `(x,p)` consisting of a left endpoint `x` of the source family (of intervals of
length `H`), `p` a prime in `[a, b]`, such that the rescaled interval `[x/p, x/p + H/p]` lies
within `R` of `x'` and the rescaled phase `(1/p)_* φ_x` is `PolyRel k C 1`-related to `pol'` on
`[x', x' + L']`. -/
noncomputable def incPairs (k : ℕ) (C : ℝ) (src : Finset ℝ) (a b H R L' : ℝ)
    (pol : ℝ → ℝ[X]) (pol' : ℝ[X]) (x' : ℝ) : Finset (ℝ × ℕ) :=
  (src ×ˢ primesIn a b).filter (fun q =>
    |q.1 / (q.2 : ℝ) - x'| ≤ R ∧
      PolyRel k C 1 (q.1 / (q.2 : ℝ)) (H / (q.2 : ℝ)) (dil (q.2 : ℝ) (pol q.1)) x' L' pol')

/-- A phase family can be weakened to a smaller constant. -/
def PhaseFamily.weaken {k : ℕ} {f : ℕ → ℂ} {c c' X H : ℝ} (F : PhaseFamily k f c X H)
    (h : c' ≤ c) (hXH : 0 ≤ X / H) (hH : 0 ≤ H) : PhaseFamily k f c' X H :=
  ⟨F.fam, F.pol, F.isFam,
    le_trans (mul_le_mul_of_nonneg_right h hXH) F.card_ge, F.deg,
    fun x hx => le_trans (mul_le_mul_of_nonneg_right h hH) (F.corr_ge x hx)⟩

/-- `PhaseFamily` transferred along equalities of the two scale parameters. -/
def PhaseFamily.congr {k : ℕ} {f : ℕ → ℂ} {c X L X' L' : ℝ} (hX : X = X') (hL : L = L')
    (F : PhaseFamily k f c X L) : PhaseFamily k f c X' L' :=
  hL ▸ hX ▸ F

/-- `PolyRel` is monotone in its constant. -/
lemma PolyRel_mono {k : ℕ} {C C' δ : ℝ} {x₁ L₁ x₂ L₂ : ℝ} {P₁ P₂ : ℝ[X]}
    (h : PolyRel k C δ x₁ L₁ P₁ x₂ L₂ P₂) (hC : C ≤ C') (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    PolyRel k C' δ x₁ L₁ P₁ x₂ L₂ P₂ := by
  obtain ⟨h1, h2, h3, ε, γ, hdegε, hdegγ, hP, hε, hγ⟩ := h
  refine ⟨le_trans h1 (mul_le_mul_of_nonneg_right hC hL₂),
    le_trans h2 (mul_le_mul_of_nonneg_right hC hL₁),
    le_trans h3 (mul_le_mul_of_nonneg_right hC hL₁),
    ε, γ, hdegε, hdegγ, hP, fun t ht => le_trans (hε t ht) hC, hγ⟩

end Work.BMF
