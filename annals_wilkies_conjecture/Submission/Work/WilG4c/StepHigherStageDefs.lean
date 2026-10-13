/-
  WilG4c / `StepHigherStageDefs` — the shared vocabulary of the §5.4 assembly: the interface
  `StepStage` of the estimate (d)+(e), the multi-curve data `CurveData`, and the composed chart
  `subdivChart = chartPt α β ∘ subdivMap N s ∘ ψ`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.Engine

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The interface of the estimate (d)+(e) -/

/-- **The multi-curve data of BNZ §5.4** for one family `F` of cube dimension `n+1`: for every
member `(i,l)` there is a finite exceptional set `B` of `x`-coordinates, off which the curves
`γ m v : ℝ → ℝ^n` are near-maximising (up to the factor `2`) for the `m`-th directional
derivative in the direction list `v`, and off which along the curves the derivatives are
bounded by `e (r (1 + n e))^m` (BNZ Lemma 22).

Both conditions are required only off `B`: at a bad `x` the derivative of `F i l` at the curve
point is a junk value of `iteratedFDeriv`, so nothing can be demanded there, and the pointwise
bound is recovered at those finitely many coordinates by continuity
(`Work.WilkG4c.pt_jet_le_multi_bad_offB`).  This is verbatim the hypothesis of
`Work.WilkG4c.pullback_pylipdef_multi_badB` (whose conclusion is that the diagonal subdivision
of `F` satisfies `PYLipDef`). -/
def CurveData (k p n r : ℕ) (F : Family k p (n + 1)) : Prop :=
  ∀ (i : Fin k) (l : Fin p → ℝ), ∃ B : Finset ℝ,
    ∃ γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ,
      (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
        x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
        ContDiffAt ℝ m (F i l) (pt x y) →
        |iteratedFDeriv ℝ m (F i l) (pt x y) (fun t => Pi.single (v t) 1)| ≤
          2 * |iteratedFDeriv ℝ m (F i l) (curveFun (γ m v) x)
                (fun t => Pi.single (v t) 1)|) ∧
      (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
        x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
        ContDiffAt ℝ m (F i l) (pt x y) →
        |iteratedFDeriv ℝ m (F i l) (curveFun (γ m v) x) (fun t => Pi.single (v t) 1)| ≤
          Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)

/-- **The stage hypothesis of BNZ §5.4** (the output of the tuple construction, Corollary 5.5
and the inductive computation, i.e. items (d)+(e) of the plan).  For every family satisfying
`PYLip` with `Ω`-bounded graphs and values in `(0,1)`, there is a finite family `Φ₁` of affine
`x`-charts `(α,β)` such that

* the coordinate graphs of `α,β` are `Ω`-bounded with format `a₁` and degree `eval ![D,r] b₁`
  (`a₁` is independent of `D,r`);
* the charts map the interval into itself: `0 < β l`, `0 ≤ α l`, `α l + β l ≤ 1`;
* the charts cover the `x`-interval `I` up to `ε/2`;
* each pullback `pullX F α β` carries the multi-curve data `CurveData` of the estimate;
* the number of charts is bounded by a polynomial in `D,r,k,-log ε`. -/
def StepStage (S : SOMin) (p n : ℕ) : Prop :=
  ∀ (F0 : ℕ), ∃ (a₁ : ℕ) (b₁ : MvPolynomial (Fin 2) ℕ) (c₁ : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 1 ≤ r → 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Family k p (n + 1)),
        PYLip p n r k F → (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        ValuesIn01 Λ F →
        ∃ Φ₁ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
          (Φ₁.card : ℝ) ≤
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c₁ ∧
          (∀ cb ∈ Φ₁,
            graphOf cb.1 ∈ S.Ω a₁ (MvPolynomial.eval ![D, r] b₁) (p + 1) ∧
            graphOf cb.2 ∈ S.Ω a₁ (MvPolynomial.eval ![D, r] b₁) (p + 1) ∧
            ∀ l : Fin p → ℝ, 0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1) ∧
          (∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ Φ₁, ∃ t ∈ I,
            |cb.1 l + cb.2 l * t - x| < ε / 2) ∧
          (∀ cb ∈ Φ₁, CurveData k p n r (pullX F cb.1 cb.2))

/-! ## 3. The composed chart `chartPt ∘ subdivMap ∘ ψ` -/

/-- The chart obtained by composing the affine `x`-chart `chartPt α β` (`(l,z) ↦ (α l + β l z 0,
tail z)`) with the diagonal subdivision `subdivMap N s` and the cube chart `ψ`:
`subdivChart α β s ψ l t = chartPt α β l (subdivMap N s (ψ l t))`. -/
def subdivChart {p n N : ℕ} (α β : (Fin p → ℝ) → ℝ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (ψ : ChartTuple p (n + 1)) : ChartTuple p (n + 1) :=
  fun j l t => chartPt α β l (subdivMap N s (fun k => ψ k l t)) j

@[simp] theorem subdivChart_apply {p n N : ℕ} (α β : (Fin p → ℝ) → ℝ)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (ψ : ChartTuple p (n + 1))
    (j : Fin (n + 1)) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    subdivChart α β s ψ j l t = chartPt α β l (subdivMap N s (fun k => ψ k l t)) j := rfl

/-- The defining identity of the composed chart, in point form: for a family member `F i`,
the value of `F` at the composed chart point is the value of the pullback family at the
subdivided chart point.  This is what makes the `PYLipDef` chieck of the subdivided pullback
(`Work.WilkG4c.pullback_pylipdef_multi_bad`) transfer verbatim to the chart composites of the
original family. -/
theorem fam_comp_subdivChart {k p n N : ℕ} (F : Family k p (n + 1))
    (α β : (Fin p → ℝ) → ℝ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (ψ : ChartTuple p (n + 1)) (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    F i l (fun j => subdivChart α β s ψ j l t) =
      (fun i l u => pullX F α β i l (subdivMap N s u)) i l (fun j => ψ j l t) := by
  simp only [subdivChart_apply]
  rw [pullX_eq]

/-- The composed chart maps the open cube into itself whenever the affine chart does (on the
given parameter) and `ψ` does. -/
theorem subdivChart_mem_openCube {p n N : ℕ} (hN : 1 ≤ N) {α β : (Fin p → ℝ) → ℝ}
    {l : Fin p → ℝ} (hβ : 0 < β l) (hα : 0 ≤ α l) (hαβ : α l + β l ≤ 1)
    {s : Fin (n + 1) → Fin (3 * (N - 1) + 1)} {ψ : ChartTuple p (n + 1)}
    (hψ : ∀ t ∈ openCube (n + 1), (fun j => ψ j l t) ∈ openCube (n + 1)) :
    ∀ t ∈ openCube (n + 1), (fun j => subdivChart α β s ψ j l t) ∈ openCube (n + 1) := by
  intro t ht
  have h1 : subdivMap N s (fun k => ψ k l t) ∈ openCube (n + 1) :=
    subdivMap_mem_openCube hN s (hψ t ht)
  exact chartPt_mem_openCube hα hβ hαβ h1


/-! ## 4. `pt`, the cube, and the distance of two points with the same tail -/

/-- `pt t y` lies in the open cube exactly when `t ∈ I` and `y` does. -/
theorem pt_mem_openCube {n : ℕ} {t : ℝ} {y : Fin n → ℝ} :
    pt t y ∈ openCube (n + 1) ↔ t ∈ I ∧ y ∈ openCube n := by
  constructor
  · intro h
    exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨h1, h2⟩ j
    induction j using Fin.cases with
    | zero =>
        have h1' : (0 : ℝ) < t ∧ t < 1 := h1
        simpa only [pt_zero, Set.mem_Ioo] using h1'
    | succ j => simpa only [pt_succ, Set.mem_Ioo] using h2 j

/-- The chart point of `pt t y` is `pt (α l + β l · t) y`. -/
theorem chartPt_pt {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ) (t : ℝ) (y : Fin n → ℝ) :
    chartPt α β l (pt t y) = pt (α l + β l * t) y := by
  funext j
  induction j using Fin.cases with
  | zero => simp [chartPt_zero, pt_zero]
  | succ j => simp [chartPt_succ, pt_succ]

/-- Two points of `ℝ^{n+1}` with the same tail are at distance at most the distance of their
first coordinates. -/
theorem dist_le_of_tail_eq {n : ℕ} {x x' : Fin (n + 1) → ℝ} (h : Fin.tail x' = Fin.tail x) :
    dist x' x ≤ |x' 0 - x 0| := by
  refine (dist_pi_le_iff (abs_nonneg _)).mpr fun j => ?_
  induction j using Fin.cases with
  | zero => simp [Real.dist_eq]
  | succ j =>
      have hh : x' j.succ = x j.succ := congrFun h j
      rw [hh]
      simp


end Work.WilkG4c
