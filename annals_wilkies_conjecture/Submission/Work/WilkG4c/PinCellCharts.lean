import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilkG4c.TailPullbackNorm
import Submission.Work.WilkG4c.FamGraphConstPtMem
import Submission.Work.WilkG4c.FamGraphTailMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-!
# Pinned-slice charts (`Work.WilkG4c.PinCellCharts`)

The `§5.3` assembly has to cover the *pinned* part of the cube: points `x ∈ (0,1)^{n+1}` whose
distinguished coordinate `x 0` equals a definable function `pt l` of the parameters (the fibre of
a "pin" cell of a cell decomposition refining the bad curve).  At such a point the family is
literally a family in the remaining `n` coordinates, so the F-lemma at level `n` (the induction
hypothesis `ih`) covers it.

Concretely, let `G i l u = F i l (Fin.cons (pt l) u)` be the sliced family and let `Ψ` be the
`Finset` of charts of the `n`-cube produced by `ih p` for `G`.  For each `ψ ∈ Ψ` put

* `nextChart pt ψ 0 l t = pt l` (the pinned coordinate),
* `nextChart pt ψ j.succ l t = ψ j l (Fin.tail t)`.

Then `Φ := Ψ.image (nextChart pt)` has the required cardinality bound, satisfies `ChartsOK`, and
covers every pinned point: given `x` with `x 0 = pt l`, the cover of `Fin.tail x` by `Ψ` gives
`ψ, s` with `|G i l (ψ· l s) - G i l (Fin.tail x)| < ε`, and `t = Fin.cons (1/2) s` realises the
same point as `nextChart pt ψ l t`.

The two analytic/`Ω` inputs are the separate lemmas `TailPullbackNorm` (the composite only
depends on `Fin.tail t`, and `Fin.tail` is a linear map of norm `≤ 1`),
`FamGraphConstPtMem` and `FamGraphTailMem` (the `Ω`-bookkeeping of the two families of
coordinates, via `Work.WilG5.coordPre_mem`).
-/

/-- The chart attached to a chart `ψ` of the `n`-cube: coordinate `0` is pinned at `pt`,
the remaining coordinates are `ψ` composed with `Fin.tail`. -/
def nextChart {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (ψ : ChartTuple p n) : ChartTuple p (n + 1) :=
  fun j => Fin.cases (fun (l : Fin p → ℝ) (_ : Fin (n + 1) → ℝ) => pt l)
    (fun (j' : Fin n) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => ψ j' l (Fin.tail t)) j

@[simp] theorem nextChart_zero {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (ψ : ChartTuple p n)
    (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) : nextChart pt ψ 0 l t = pt l := by
  simp [nextChart]

@[simp] theorem nextChart_succ {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (ψ : ChartTuple p n)
    (j : Fin n) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    nextChart pt ψ j.succ l t = ψ j l (Fin.tail t) := by
  simp [nextChart]

/-- The coordinates of `nextChart pt ψ l t` are `pt l` followed by the `ψ`-coordinates of
`Fin.tail t`. -/
theorem nextChart_cons {p n : ℕ} (pt : (Fin p → ℝ) → ℝ) (ψ : ChartTuple p n)
    (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    (fun j => nextChart pt ψ j l t) = Fin.cons (pt l) (fun j => ψ j l (Fin.tail t)) := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp

/-- `Fin.cons` respects the open cube. -/
theorem cons_mem_openCube {n : ℕ} {c : ℝ} {u : Fin n → ℝ} (hc : c ∈ I)
    (hu : u ∈ openCube n) : Fin.cons c u ∈ openCube (n + 1) := by
  intro j
  induction j using Fin.cases with
  | zero => exact hc
  | succ j => exact hu j

/-- Evaluation of the degree polynomial produced by the assembly. -/
theorem eval_pin_b (b₁ : MvPolynomial (Fin 2) ℕ) (D r c : ℕ) :
    MvPolynomial.eval ![D, r] (b₁ + MvPolynomial.X 0 + MvPolynomial.C c)
      = MvPolynomial.eval ![D, r] b₁ + D + c := by
  simp [MvPolynomial.eval_add, MvPolynomial.eval_X]

theorem PinCellCharts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (n p : ℕ) (hn : 1 ≤ n) (ih : ∀ q, WilkiesDesign.CG.FLem S q n) :
    ∀ (F0 A0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
        (pt : (Fin p → ℝ) → ℝ),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        (WilkiesDesign.graphOf pt ∈ S.Ω A0 D (p + 1)) →
        (∀ l ∈ Λ, pt l ∈ Work.WilkG4c.I) →
        (∀ i, WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin n → ℝ) =>
            F i l (Fin.cons (pt l) u)) ∈ S.Ω F0 D (p + n + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          Work.WilkG4c.ChartsOK S a (MvPolynomial.eval ![D, r] b) r Λ F Φ ∧
          (∀ l ∈ Λ, ∀ x ∈ WilkiesDesign.openCube (n + 1), x 0 = pt l →
            ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube (n + 1),
              ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε) := by
  intro F0 A0
  obtain ⟨a₁, b₁, c₁, H₁⟩ := ih p F0
  refine ⟨max (A0 + 64 * ((p + (n + 1) + 1) + (p + 1)) + 64)
      (a₁ + 64 * ((p + (n + 1) + 1) + (p + n + 1)) + 64),
    b₁ + MvPolynomial.X 0 + MvPolynomial.C
      (32 * ((p + (n + 1) + 1) + (p + 1)) + 32
        + (32 * ((p + (n + 1) + 1) + (p + n + 1)) + 32)), c₁, ?_⟩
  intro D r k ε hε hε1 Λ F pt hF hpt hptI hG hval
  obtain ⟨Ψ, hΨcard, hΨok, hΨcov⟩ :=
    H₁ D r k ε hε hε1 Λ (fun i l u => F i l (Fin.cons (pt l) u)) hG
      (fun i l hl u hu => hval i l hl (Fin.cons (pt l) u) (cons_mem_openCube (hptI l hl) hu))
  refine ⟨Ψ.image (nextChart pt), ?_, ?_, ?_⟩
  · -- cardinality: the number of charts does not increase
    have hcard := Finset.card_image_le (s := Ψ) (f := nextChart pt)
    calc ((Ψ.image (nextChart pt)).card : ℝ) ≤ (Ψ.card : ℝ) := by exact_mod_cast hcard
      _ ≤ _ := hΨcard
  · -- the per-chart conditions of `ChartsOK`
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hφ
    have hψ' := hΨok ψ hψ
    refine ⟨?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero =>
        have hfun : nextChart pt ψ 0 = (fun (l : Fin p → ℝ) (_ : Fin (n + 1) → ℝ) => pt l) := by
          funext l t; rw [nextChart_zero]
        rw [hfun]
        refine Omega_mono_le S (le_max_left _ _) ?_ (FamGraphConstPtMem (S := S) hpt)
        rw [eval_pin_b]
        omega
      | succ j =>
        have hfun : nextChart pt ψ j.succ
            = (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) => ψ j l (Fin.tail t)) := by
          funext l t; rw [nextChart_succ]
        rw [hfun]
        refine Omega_mono_le S (le_max_right _ _) ?_ (FamGraphTailMem (S := S) (hψ'.1 j))
        rw [eval_pin_b]
        omega
    · intro l hl
      refine ⟨?_, ?_⟩
      · -- the chart maps the cube into the cube
        intro t ht
        rw [nextChart_cons]
        intro j
        induction j using Fin.cases with
        | zero => simpa [I] using hptI l hl
        | succ j => exact (hψ'.2 l hl).1 (Fin.tail t) (fun i => ht i.succ) j
      · -- the composites are `C^r` with unit norms, because they only depend on `Fin.tail t`
        intro i
        have hsm : ContDiffOn ℝ r
            (fun u : Fin n → ℝ => F i l (Fin.cons (pt l) (fun j => ψ j l u)))
            (openCube n) := ((hψ'.2 l hl).2 i).1
        have hnrm : ∀ m, m ≤ r → ∀ u ∈ openCube n,
            ‖iteratedFDeriv ℝ m (fun u : Fin n → ℝ =>
              F i l (Fin.cons (pt l) (fun j => ψ j l u))) u‖ ≤ 1 :=
          ((hψ'.2 l hl).2 i).2
        have hTP := TailPullbackNorm
          (f := fun u : Fin n → ℝ => F i l (Fin.cons (pt l) (fun j => ψ j l u))) hsm hnrm
        refine ⟨?_, ?_⟩
        · have hgoal : (fun t : Fin (n + 1) → ℝ => F i l (fun j => nextChart pt ψ j l t))
              = (fun t : Fin (n + 1) → ℝ =>
                  F i l (Fin.cons (pt l) (fun j => ψ j l (Fin.tail t)))) := by
            funext t; rw [nextChart_cons]
          rw [hgoal]
          exact hTP.1
        · intro m hm t ht
          have hgoal : (fun t : Fin (n + 1) → ℝ => F i l (fun j => nextChart pt ψ j l t))
              = (fun t : Fin (n + 1) → ℝ =>
                  F i l (Fin.cons (pt l) (fun j => ψ j l (Fin.tail t)))) := by
            funext t; rw [nextChart_cons]
          rw [hgoal]
          exact hTP.2 m hm t ht
  · -- the cover of the pinned slice
    intro l hl x hx hx0
    have htail : Fin.tail x ∈ openCube n := fun j => hx j.succ
    obtain ⟨ψ, hψ, s, hs, hcov⟩ := hΨcov l hl (Fin.tail x) htail
    refine ⟨nextChart pt ψ, Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩, Fin.cons (1 / 2) s, ?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => show (1 / 2 : ℝ) ∈ Set.Ioo 0 1; norm_num
      | succ j => simpa using hs j
    · intro i
      have hfun1 : (fun j => nextChart pt ψ j l (Fin.cons (1 / 2) s))
          = Fin.cons (pt l) (fun j => ψ j l s) := by
        rw [nextChart_cons]
        simp
      have hx' : Fin.cons (pt l) (Fin.tail x) = x := by
        rw [← hx0]; exact Fin.cons_self_tail x
      rw [hfun1, ← hx']
      exact hcov i

end Work.WilkG4c
