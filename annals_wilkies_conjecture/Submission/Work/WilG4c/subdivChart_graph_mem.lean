import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4c.FamGraphPolyComb
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.PolyCombBasic
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.famGraph_pullX
import Submission.Work.WilG4c.sliceGraph_mem_gen
import Submission.Work.WilG4c.ChartRescaleMem

/-!
## `Work.WilkG4c.subdivChart_graph_mem`

`Ω`-membership of the composed chart `subdivChart α β s ψ = chartPt α β ∘ subdivMap N s ∘ ψ`
of BNZ §5.4 (the "diagonal subdivision" of the chart supplied by Corollary 19).

The statement is that the format of `famGraph (subdivChart α β s ψ j)` is bounded by
`a₁ + a₂ + A` and its degree by `C * (B₁ + B₂) + C`, where `A, C` depend only on `S`, `p`, `n` --
in particular not on `N`, nor on the subdivision index `s`, nor on the two input formats/degrees
individually (`α` and `β` share the pair `(a₁, B₁)`, only their *sum* with `(a₂, B₂)` matters).

The proof is a two-step composition, each step a single use of one input bound (so that the
format cost is the *sum* of the two formats, `a₁ + a₂`, and not any multiple of either):

* the *outer* chart `outerChart α β j = (l,w) ↦ chartPt α β l w j` is the affine `x`-chart
  reading the first coordinate, `w ↦ pt (α l + β l · w 0) (Fin.tail w)`, followed by the `j`-th
  coordinate projection; `famGraph_pullX` composes the coordinate projection (a hyperplane,
  format `p+(n+1)+1`, degree `1`) with the affine chart, which costs `+a₁` in format and
  `+2*B₁` in degree -- *one* use of the pair `(a₁, B₁)`, uniformly in `j` (`outerChart_mem`);
* the *inner* chart `innerChart N s ψ k = (l,t) ↦ subdivMap N s (ψ·l t) k` is, coordinate by
  coordinate, the affine rescaling `subdivBase N s k + (ψ k l t)/N` of the input chart; the
  value-rescaling lemma `ChartRescaleMem` costs `+a₂` in format and `+2` in degree
  (`innerChart_mem`);
* the two are composed by `famGraph_comp_single`, whose format cost `F₀ + F₁ + a` is the *sum*
  of the two formats and whose degree cost `D₀ + (p + (n+1)) * D₁ + c` is linear with the fixed
  coefficient `p + (n+1)`.

Finally the numeric bookkeeping: `A := Kout + Ain + ca` absorbs the three additive constants
and `C := 2 + (p + (n+1)) * Cin + Kout + cc + 1` dominates the coefficient `2` of `B₁`, the
coefficient `(p + (n+1)) * Cin` of `B₂` and the additive constant `Kout + (p+(n+1))*Cin + cc`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-! The auxiliary lemmas of `subdivChart_graph_mem`, gathered in their own namespace so that
the shared library never sees an accidental clash of common names (`outerChart`, `innerChart`,
`famGraph_coord_mem`, ...). -/

namespace SubdivChartGraph

/-! ## 1. The outer chart: the affine `x`-chart read in the `j`-th coordinate -/

/-- The outer chart of the subdivision: `(l,w) ↦ chartPt α β l w j`. -/
def outerChart {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (j : Fin (n + 1)) :
    (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ :=
  fun l w => chartPt α β l w j

/-- The graph of the coordinate projection `(l,w) ↦ w j` is a hyperplane in `ℝ^{p+(n+1)+1}`. -/
theorem famGraph_coord_mem (S : WilkiesDesign.SOMin) (p n : ℕ) (j : Fin (n + 1)) :
    WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) => w j) ∈
      S.Ω (p + (n + 1) + 1) 1 (p + (n + 1) + 1) := by
  have h := graphOf_coord_mem (S := S) (Fin.natAdd p j)
  simpa only [WilkiesDesign.CG.famGraph, WilkiesDesign.graphOf] using h

/-- **The outer chart is `Ω`-definable with one use of the pair `(a₁, B₁)`.** -/
theorem outerChart_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K : ℕ, ∀ (a₁ B₁ : ℕ) (α β : (Fin p → ℝ) → ℝ),
      WilkiesDesign.graphOf α ∈ S.Ω a₁ B₁ (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω a₁ B₁ (p + 1) →
      ∀ j : Fin (n + 1),
        WilkiesDesign.CG.famGraph (outerChart α β j) ∈
          S.Ω (a₁ + K) (2 * B₁ + K) (p + (n + 1) + 1) := by
  obtain ⟨K₀, hK₀⟩ := Work.WilG4c.famGraph_pullX S p n
  refine ⟨K₀ + (p + (n + 1) + 1) + 1, ?_⟩
  intro a₁ B₁ α β hα hβ j
  have hco := famGraph_coord_mem S p n j
  have hmain : WilkiesDesign.CG.famGraph (outerChart α β j) ∈
      S.Ω ((p + (n + 1) + 1) + a₁ + K₀) (1 + 2 * B₁ + K₀) (p + (n + 1) + 1) :=
    hK₀ a₁ B₁ (p + (n + 1) + 1) 1 α β
      (fun (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) => w j) hα hβ hco
  exact Omega.mono hmain (by omega) (by omega)

/-! ## 2. The inner chart: the diagonal subdivision as a value-rescaling -/

/-- The inner chart of the subdivision: the `k`-th coordinate of `subdivMap N s (ψ·)`. -/
def innerChart {p n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (ψ : ChartTuple p (n + 1)) (k : Fin (n + 1)) :
    (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ :=
  fun l t => subdivMap N s (fun k' => ψ k' l t) k

/-- The inner chart is the affine rescaling `subdivBase N s k + (ψ k l t)/N` of the input
chart (valid for every `N`, including `N = 0`, where both sides vanish). -/
theorem innerChart_eq {p n : ℕ} (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
    (ψ : ChartTuple p (n + 1)) (k : Fin (n + 1)) :
    innerChart N s ψ k = (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
      subdivBase N s k + ψ k l t / (N : ℝ)) := by
  funext l t
  simp only [innerChart, subdivMap_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    div_eq_inv_mul]

/-- **The inner chart is `Ω`-definable with one use of the pair `(a₂, B₂)`.** -/
theorem innerChart_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ A C : ℕ, ∀ (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (a₂ B₂ : ℕ)
      (ψ : ChartTuple p (n + 1)),
      (∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω a₂ B₂ (p + (n + 1) + 1)) →
      ∀ k : Fin (n + 1), WilkiesDesign.CG.famGraph (innerChart N s ψ k) ∈
        S.Ω (a₂ + A) (C * B₂ + C) (p + (n + 1) + 1) := by
  obtain ⟨K₀, hK₀⟩ := Work.WilG4c.ChartRescaleMem S p n
  refine ⟨K₀, 2, ?_⟩
  intro N s a₂ B₂ ψ hψ k
  have h := hK₀ N (subdivBase N s k) a₂ B₂ (ψ k) (hψ k)
  rw [innerChart_eq N s ψ k]
  exact Omega.mono h le_rfl (by omega)

/-! ## 3. The composite -/

/-- `subdivChart` is the composite of the outer and inner charts. -/
theorem subdivChart_eq_comp {p n N : ℕ} (α β : (Fin p → ℝ) → ℝ)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (ψ : ChartTuple p (n + 1)) (j : Fin (n + 1)) :
    subdivChart α β s ψ j =
      (fun (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
        outerChart α β j l (fun k => innerChart N s ψ k l t)) := by
  funext l t
  simp only [subdivChart_apply, outerChart, innerChart]

end SubdivChartGraph

open SubdivChartGraph

theorem subdivChart_graph_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ A C : ℕ, ∀ (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
      (α β : (Fin p → ℝ) → ℝ) (ψ : Work.WilkG4c.ChartTuple p (n + 1)) (a₁ a₂ B₁ B₂ : ℕ),
      WilkiesDesign.graphOf α ∈ S.Ω a₁ B₁ (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω a₁ B₁ (p + 1) →
      (∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω a₂ B₂ (p + (n + 1) + 1)) →
      ∀ j, WilkiesDesign.CG.famGraph (Work.WilkG4c.subdivChart α β s ψ j) ∈
        S.Ω (a₁ + a₂ + A) (C * (B₁ + B₂) + C) (p + (n + 1) + 1) := by
  obtain ⟨Kout, hOut⟩ := SubdivChartGraph.outerChart_mem S p n
  obtain ⟨Ain, Cin, hIn⟩ := SubdivChartGraph.innerChart_mem S p n
  obtain ⟨ca, cc, hcomp⟩ := Work.WilkG4c.famGraph_comp_single S p (n + 1)
  refine ⟨Kout + Ain + ca, 2 + (p + (n + 1)) * Cin + Kout + cc + 1, ?_⟩
  intro N s α β ψ a₁ a₂ B₁ B₂ hα hβ hψ j
  -- the outer chart
  have hout : WilkiesDesign.CG.famGraph (SubdivChartGraph.outerChart α β j) ∈
      S.Ω (a₁ + Kout) (2 * B₁ + Kout) (p + (n + 1) + 1) :=
    hOut a₁ B₁ α β hα hβ j
  -- the inner chart
  have hin : ∀ k : Fin (n + 1), WilkiesDesign.CG.famGraph (SubdivChartGraph.innerChart N s ψ k) ∈
      S.Ω (a₂ + Ain) (Cin * B₂ + Cin) (p + (n + 1) + 1) :=
    fun k => hIn N s a₂ B₂ ψ hψ k
  -- compose
  have hmain := hcomp (a₁ + Kout) (a₂ + Ain) (2 * B₁ + Kout) (Cin * B₂ + Cin)
    (SubdivChartGraph.outerChart α β j) (SubdivChartGraph.innerChart N s ψ) hout hin
  rw [SubdivChartGraph.subdivChart_eq_comp α β s ψ j]
  refine Omega.mono hmain ?_ ?_
  · show (a₁ + Kout) + (a₂ + Ain) + ca ≤ a₁ + a₂ + (Kout + Ain + ca)
    omega
  · -- degree bookkeeping
    show (2 * B₁ + Kout) + (p + (n + 1)) * (Cin * B₂ + Cin) + cc ≤
      (2 + (p + (n + 1)) * Cin + Kout + cc + 1) * (B₁ + B₂) +
        (2 + (p + (n + 1)) * Cin + Kout + cc + 1)
    have hXle : (p + (n + 1)) * Cin ≤ 2 + (p + (n + 1)) * Cin + Kout + cc + 1 := by omega
    have h2le : 2 ≤ 2 + (p + (n + 1)) * Cin + Kout + cc + 1 := by omega
    have hC1 : 2 * B₁ ≤ (2 + (p + (n + 1)) * Cin + Kout + cc + 1) * B₁ :=
      Nat.mul_le_mul_right B₁ h2le
    have hC2 : ((p + (n + 1)) * Cin) * B₂ ≤
        (2 + (p + (n + 1)) * Cin + Kout + cc + 1) * B₂ :=
      Nat.mul_le_mul_right B₂ hXle
    have hC3 : Kout + (p + (n + 1)) * Cin + cc ≤
        2 + (p + (n + 1)) * Cin + Kout + cc + 1 := by omega
    rw [Nat.mul_add (p + (n + 1)) (Cin * B₂) Cin,
      ← Nat.mul_assoc (p + (n + 1)) Cin B₂,
      Nat.mul_add (2 + (p + (n + 1)) * Cin + Kout + cc + 1) B₁ B₂]
    omega

end Work.WilkG4c

/-! ## The same statement under the directory's namespace spelling

The area directory is `Submission/Work/WilG4c`, and several files of the area (e.g.
`famGraph_linX.lean`, `famGraph_pullX.lean`, `ChartRescaleMem.lean`, and the statements of the
sibling lemmas in the same directory) use the namespace spelling `Work.WilG4c` derived from that
path, while the module's original statement lived under `Work.WilkG4c`.  We expose the
*identical* statement under the directory's spelling as well, as a one-line wrapper, exactly as
`Submission/Work/WilG4c/FamGraphRescale.lean` does. -/

namespace Work.WilG4c

/-- `subdivChart_graph_mem` in the directory's namespace spelling; identical to
`Work.WilkG4c.subdivChart_graph_mem`. -/
theorem subdivChart_graph_mem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ A C : ℕ, ∀ (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1))
      (α β : (Fin p → ℝ) → ℝ) (ψ : Work.WilkG4c.ChartTuple p (n + 1)) (a₁ a₂ B₁ B₂ : ℕ),
      WilkiesDesign.graphOf α ∈ S.Ω a₁ B₁ (p + 1) →
      WilkiesDesign.graphOf β ∈ S.Ω a₁ B₁ (p + 1) →
      (∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω a₂ B₂ (p + (n + 1) + 1)) →
      ∀ j, WilkiesDesign.CG.famGraph (Work.WilkG4c.subdivChart α β s ψ j) ∈
        S.Ω (a₁ + a₂ + A) (C * (B₁ + B₂) + C) (p + (n + 1) + 1) :=
  Work.WilkG4c.subdivChart_graph_mem S p n

end Work.WilG4c
