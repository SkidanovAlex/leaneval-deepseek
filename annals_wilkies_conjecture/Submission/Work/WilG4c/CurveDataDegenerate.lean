import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.DegJetLeOne
import Submission.Work.WilG4c.ExistsNearmaxBox

namespace Work.WilG4c

/-- **The degenerate (`β = 0`) branch of `CurveData` (BNZ §5.4, Fix F1 of the lead's audit
`sources/wilkiesG4/wilkies_g4_REVIEW.md` §2.3).**

`CurveData k p n r F` asserts, for each member `(i,l)`, the existence of a finite exceptional
set `B` and of near-maximising curves `γ` off `B`.  In the assembly (`CurveDataPullC`) the family
is a pullback `pullX F α β` along the affine `x`-chart `t ↦ α l + β l · t`, and the pullback of
the exceptional set is `{(t - α l)/β l}`, which needs `β l ≠ 0`.  With the corrected chart rule
`Work.WilG4a.F1AffineW` a chart may be degenerate (`β l = 0`), and then
`pullX F α β i l t = F i l (pt (α l) (Fin.tail t))` is *independent of the distinguished
coordinate* `t 0`.

This statement covers exactly that case: for a fixed member `i`, a fixed parameter `l` and a
degenerate chart (with `α ∈ I`), the multi-curve data holds with the **empty** exceptional set.
Consequently the `β = 0` branch of `CurveDataPullC` is a direct application of this result (both
conditions are pointwise in `l`, and the two chart components are functions of `l`).

Construction (audit §2.3; the reviewers corrected the naive sketch — `γ m v x` may depend on `x`):
take `B = ∅` and, for each `(m,v)` and each `x`, a point `γ m v x` of the cube at which the `m`-th
directional derivative of the slice `F i l (α, ·)` in the direction `v` (with the distinguished
direction removed when `v` contains it — then both sides of the first clause vanish) is at least
half of its supremum over the cube.
* `Work.WilkG4c.YBound F r` bounds every jet of the slice `F i l (α, ·)` on the cube by `1`, so the
  supremum is `≤ 1` and a near-supremum point exists; if the `C^m`-locus is empty both clauses are
  vacuous.
* The second clause is `‖·‖ ≤ 1 ≤ exp 1 * (r * (1 + n * exp 1))^m`, using `hr : 1 ≤ r` for `m ≥ 1`
  and `Real.exp 1 ≥ 1` for `m = 0`.-/
theorem CurveDataDegenerate {k p n r : ℕ} (hr : 1 ≤ r) (F : Work.WilkG4c.Family k p (n + 1))
    (hY : Work.WilkG4c.YBound F r) (i : Fin k) (l : Fin p → ℝ) (α : ℝ)
    (hα : α ∈ Work.WilkG4c.I) :
    ∃ γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ,
      (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
        x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
            (Work.WilkG4c.pt x y) →
        |iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
            (Work.WilkG4c.pt x y) (fun t => Pi.single (v t) 1)| ≤
          2 * |iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
                (Work.WilkG4c.curveFun (γ m v) x) (fun t => Pi.single (v t) 1)|) ∧
      (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
        x ∈ Work.WilkG4c.I → y ∈ WilkiesDesign.openCube n →
        ContDiffAt ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
            (Work.WilkG4c.pt x y) →
        |iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
            (Work.WilkG4c.curveFun (γ m v) x) (fun t => Pi.single (v t) 1)| ≤
          Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
  classical
  -- The two abbreviations of the proof: the jet `D` of the degenerate pullback in the
  -- directions `Pi.single (v t) 1`, and the right-hand side `K` of the jet bound.
  let D : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → (Fin n → ℝ) → ℝ :=
    fun m v x y => iteratedFDeriv ℝ m (Work.WilkG4c.pullX F (fun _ => α) (fun _ => (0 : ℝ)) i l)
      (Work.WilkG4c.pt x y) (fun t => Pi.single (v t) 1)
  let K : ℕ → ℝ := fun m => Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m
  -- `K m ≥ 1` for every `m`: `r ≥ 1`, `1 + n exp 1 ≥ 1` and `exp 1 ≥ 1`.
  have hKone : ∀ m : ℕ, 1 ≤ K m := by
    intro m
    show (1 : ℝ) ≤ Real.exp 1 * ((r : ℝ) * (1 + (n : ℝ) * Real.exp 1)) ^ m
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hn1 : (1 : ℝ) ≤ 1 + (n : ℝ) * Real.exp 1 := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) * Real.exp 1 :=
        mul_nonneg (Nat.cast_nonneg n) (Real.exp_nonneg 1)
      linarith
    have hbase : (1 : ℝ) ≤ (r : ℝ) * (1 + (n : ℝ) * Real.exp 1) := by
      have h := mul_le_mul hr' hn1 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ (r : ℝ))
      simpa using h
    have hp : (1 : ℝ) ≤ ((r : ℝ) * (1 + (n : ℝ) * Real.exp 1)) ^ m := one_le_pow₀ hbase
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h := mul_le_mul he hp (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ Real.exp 1)
    simpa using h
  -- The curve: a `2`-approximate maximiser of `|D m v x|` over the points of the cube at which
  -- `|D m v x| ≤ K m`, with an arbitrary default when there is no such point (then both clauses
  -- are vacuous, since every `C^m`-point of the cube *is* such a point, by `DegJetLeOne`).
  let γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ := fun m v x =>
    if h : ∃ yc : Fin n → ℝ, (∀ i, yc i ∈ Set.Ioo (0 : ℝ) 1) ∧ |D m v x yc| ≤ K m ∧
        ∀ y' : Fin n → ℝ, (∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1) → |D m v x y'| ≤ K m →
          |D m v x y'| ≤ 2 * |D m v x yc|
    then h.choose else fun _ => (1 / 2 : ℝ)
  refine ⟨γ, ?_, ?_⟩
  · -- First clause: near-maximality of `γ m v x`.
    intro m v x y hm hxI hy hcd
    have hjet : |D m v x y| ≤ 1 := by
      simp only [D]
      exact DegJetLeOne hY i l α hα m hm v x y hy hcd
    have hyU : |D m v x y| ≤ K m := le_trans hjet (hKone m)
    have hex := ExistsNearmaxBox (D m v x) (K m) y hy hyU
    have hγ : γ m v x = hex.choose := dif_pos hex
    have hmax : |D m v x y| ≤ 2 * |D m v x (γ m v x)| := by
      rw [hγ]
      exact hex.choose_spec.2.2 y hy hyU
    simpa only [D, Work.WilkG4c.curveFun] using hmax
  · -- Second clause: the jet bound at the curve point.
    intro m v x y hm hxI hy hcd
    have hjet : |D m v x y| ≤ 1 := by
      simp only [D]
      exact DegJetLeOne hY i l α hα m hm v x y hy hcd
    have hyU : |D m v x y| ≤ K m := le_trans hjet (hKone m)
    have hex := ExistsNearmaxBox (D m v x) (K m) y hy hyU
    have hγ : γ m v x = hex.choose := dif_pos hex
    have hb : |D m v x (γ m v x)| ≤ K m := by
      rw [hγ]
      exact hex.choose_spec.2.1
    simpa only [D, Work.WilkG4c.curveFun, K] using hb

end Work.WilG4c
