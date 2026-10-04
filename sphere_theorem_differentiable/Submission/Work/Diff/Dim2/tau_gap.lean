import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

-- NOTE for the prover.  `f := rdist p`, `g := rdist q`, `τ` is the crossing time of `{f = a}` for
-- the flow `Φ 0 ·` of `V` (cf. `Work.Diff.Dim2.tau`).  With `w := Φ 0 (-(τ x)) x` one has
-- `Φ 0 (τ x) w = x` by the flow law `hΦself` + `phi_flow_add` (`Submission.GSFlow`), and
-- `f w = a` (`hτa`), so `hflow_lip` gives `|f x - a| ≤ τ x` (`hflow_lip` at `y := w`,
-- `s := τ x`, `s' := 0`).
-- Conjunct 1: `τ x > 0` and `hτval` (valid since `f x ≤ a ≤ 3a/2`) rule out `f x ≤ a` (which would
-- give `τ x = f x - a ≤ 0`); hence `f x > a`, and `f x ≤ a + τ x < a + 1`, so
-- `g x ≥ D - f x > D - a - 1 > 3γ/2 + e` by `hD`.
-- Conjunct 2: `f x ≥ D - g x ≥ D - 3γ/2 - e > 3a/2`, so `hτhalf` gives `τ x ≥ a/2 > 0`; then
-- `τ x ≥ f x - a ≥ D - 3γ/2 - e - a > 1` by `hD`.
-- (The companion `Work.Diff.Dim2.flow_lip_f` derives `hflow_lip` from `‖V‖ ≤ 1`.)
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

theorem tau_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p q : M} {D a γ e : ℝ} (ha : 0 < a) (hγ : 0 < γ) (he : 0 < e)
    (hD : 1 + a + 3 * γ / 2 + e < D)
    (htri : ∀ y : M, D ≤ Work.Diff.C.rdist (I := I) (M := M) p y +
      Work.Diff.C.rdist (I := I) (M := M) q y)
    {Φ : ℝ → ℝ → M → M}
    (hΦself : ∀ s x, Φ s s x = x)
    (hflow_lip : ∀ y : M, ∀ s s' : ℝ,
      |Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s y)
        - Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s' y)| ≤ |s - s'|)
    {τ : M → ℝ}
    (hτval : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 →
      τ x = Work.Diff.C.rdist (I := I) (M := M) p x - a)
    (hτhalf : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      3 * a / 2 ≤ Work.Diff.C.rdist (I := I) (M := M) p x → a / 2 ≤ τ x)
    (hτa : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ x)) x) = a) :
    (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → 0 < τ x → τ x < 1 →
      a < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        3 * γ / 2 + e < Work.Diff.C.rdist (I := I) (M := M) q x) ∧
    (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 + e → 1 < τ x) := by
  -- ## The key Lipschitz inequality  `|f x - a| ≤ |τ x|`
  --
  -- Note that one does *not* need the flow law `Φ 0 a (Φ 0 b y) = Φ 0 (a+b) y` here (`phi_flow_add`
  -- needs `hVsm`/`hΦderiv`, which are not hypotheses of this statement): applying `hflow_lip` at the
  -- *same* base point `y := x`, with `s := -(τ x)` and `s' := 0`, uses `Φ 0 0 x = x` (`hΦself 0 x`)
  -- on the right and `hτa` on the left.
  have hkey : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      |Work.Diff.C.rdist (I := I) (M := M) p x - a| ≤ |τ x| := by
    intro x h1 h2
    have h := hflow_lip x (-(τ x)) 0
    rw [hτa x h1 h2, hΦself 0 x] at h
    rw [sub_zero, abs_neg] at h
    rwa [abs_sub_comm] at h
  constructor
  · -- ## Conjunct 1: `a < f x` and `3γ/2 + e < g x`
    intro x h1 h2 hτpos hτlt
    have hineq := hkey x h1 h2
    have hτabs : |τ x| = τ x := abs_of_pos hτpos
    have hfx_lt : Work.Diff.C.rdist (I := I) (M := M) p x < a + 1 := by
      have hle := le_abs_self (Work.Diff.C.rdist (I := I) (M := M) p x - a)
      linarith
    have hgt : a < Work.Diff.C.rdist (I := I) (M := M) p x := by
      by_contra hcon
      have hcon' : Work.Diff.C.rdist (I := I) (M := M) p x ≤ a := le_of_not_gt hcon
      have h3 : Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 := by linarith
      have hval := hτval x h1 h3
      linarith
    refine ⟨hgt, ?_⟩
    have htri' := htri x
    linarith
  · -- ## Conjunct 2: `1 < τ x`
    intro x h1 h2 hg
    have hfx : 1 + a < Work.Diff.C.rdist (I := I) (M := M) p x := by
      have htri' := htri x
      linarith
    by_cases hle : Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2
    · -- `f x ≤ 3a/2`: `hτval` gives `τ x = f x - a > 1` directly
      have hval := hτval x h1 hle
      linarith
    · -- `3a/2 < f x`: `hτhalf` gives `τ x > 0`, and then `|f x - a| ≤ |τ x|` gives `τ x > 1`
      have hlt : 3 * a / 2 < Work.Diff.C.rdist (I := I) (M := M) p x := lt_of_not_ge hle
      have hhalf := hτhalf x h1 h2 hlt.le
      have hineq := hkey x h1 h2
      have hτpos : 0 < τ x := by linarith
      have hτabs : |τ x| = τ x := abs_of_pos hτpos
      have hfa : 0 < Work.Diff.C.rdist (I := I) (M := M) p x - a := by linarith
      have hfin : |Work.Diff.C.rdist (I := I) (M := M) p x - a|
          = Work.Diff.C.rdist (I := I) (M := M) p x - a := abs_of_pos hfa
      linarith

end Work.Diff.Dim2
