import Mathlib
import ChallengeDeps
import Submission.LocalCurve
import Submission.TorusCharts
import Submission.TorusChartGraph

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology Matrix
open Commons.Analysis.Calculus.FDeriv
open Commons.LinearAlgebra.LinearIndependent
set_option maxHeartbeats 800000

/-!
# Layer A (xi) — instantiating the graph arc at the `(A,B)` general-position triples

`RealGraphArc` (`TorusChartGraph.lean`) packages the implicit-function graph
data of the local trisecant arc.  This module **instantiates** it: at a
collinear off-diagonal triple `(a,b,m)` whose `a`- and `b`-hinge partials are
the independent rank-two witness pair, the three `LocalCurve.lean` split
instances give explicit split homeomorphisms — for the pair `(A,B)` the
split is `splitAB : (x, (y₁,y₂)) ↦ (y₁, (y₂, x))` (graph over the `m`
coordinate, second factor the `(a,b)`-plane).  The theorem
`realGraphArc_AB` runs the product-domain implicit function theorem
(`Commons.Analysis.Calculus.Implicit.implicitFunction_graph`) with the
pair-reduced map `red = pairReduced r a b m 0 1` (whose second-factor partial
derivative is the invertible Gram matrix of the independent pair), selects a
small `x`-interval `(a₁,b₁) ∋ u.1 = m` on which the graph
`γ(x) = splitAB (x, ψ(x))` lies in the collinear off-diagonal zero set and
inside the `ψ`-covering neighbourhood `W`, and fills the `RealGraphArc`
record field by field.  The graph-coordinate / no-re-entry lemmas of
`TorusChartGraph.lean` (`graph_coordinate`, `coord_along_t`,
`trace_eq_zeroSet_of_box`, `arcHomeo`, `arc_closed_embedding`) then apply to
every such instance.

(The `(A,M)` and `(B,M)` witness pairs are routine variations with the other
two split maps; they will be added as the next instances.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

theorem exists_realGraphArc_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    Nonempty (RealGraphArc r) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAB
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAB
  let u : ℝ × (ℝ × ℝ) := (m, (a, b))
  let red : RealParamTriple → ℝ × ℝ := pairReduced r a b m (0 : Fin 3) (1 : Fin 3)
  have hColl : collinearityMap r p = 0 := by
    dsimp [p]
    exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAB]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (1 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (1 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAB_contDiff le_top)
  -- the partial derivative along the second factor is the Gram matrix
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  have hcdR : DifferentiableAt ℝ red (a, (b, m)) :=
    (ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top).differentiable_one (a, (b, m))
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
        fun s : ℝ => red (a + s, (b, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (0 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a + s, (b, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3)) =
        (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
          inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  have hcol2 : D (0, 1) = (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
      inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
        fun s : ℝ => red (a, (b + s, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b + s, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (1 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a, (b + s, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3)) =
        (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
          inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  -- invertibility of the partial derivative: Gram determinant is nonzero
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialB r a b m);
        inner ℝ (collPartialB r a b m) (collPartialA r a b m),
        inner ℝ (collPartialB r a b m) (collPartialB r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D) (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialB r a b m))
      (c₂₁ := inner ℝ (collPartialB r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialB r a b m);
              inner ℝ (collPartialB r a b m) (collPartialA r a b m),
              inner ℝ (collPartialB r a b m) (collPartialB r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  -- identification of the zero sets
  have hidentAB : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (1 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentAB with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.2.2, z.1)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.2, z.1)) :=
      (Continuous.snd continuous_snd).prodMk continuous_fst
    exact hc1.prodMk hc2
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitAB := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.2.2, z.1)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.2, z.1)) :=
      (Continuous.snd continuous_snd).prodMk continuous_fst
    exact hc1.prodMk hc2
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitAB (x, ψ x)) = 0 ∧ splitAB (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitAB z) = 0 → splitAB z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitAB z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitAB, unSplitAB, hAcont, unSplitAB_continuous, unSplitAB_splitAB,
    splitAB_unSplitAB, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩⟩
theorem exists_realGraphArc_AB_splitting {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    ∃ d : RealGraphArc r, d.B = unSplitAB ∧ d.A = splitAB ∧ d.u = (m, (a, b)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAB
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAB
  let u : ℝ × (ℝ × ℝ) := (m, (a, b))
  let red : RealParamTriple → ℝ × ℝ := pairReduced r a b m (0 : Fin 3) (1 : Fin 3)
  have hColl : collinearityMap r p = 0 := by
    dsimp [p]
    exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAB]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (1 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (1 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAB_contDiff le_top)
  -- the partial derivative along the second factor is the Gram matrix
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  have hcdR : DifferentiableAt ℝ red (a, (b, m)) :=
    (ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (1 : Fin 3)) le_top).differentiable_one (a, (b, m))
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
        fun s : ℝ => red (a + s, (b, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (0 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a + s, (b, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (0 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (0 : Fin 3)) =
        (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
          inner ℝ (collPartialA r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (0 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  have hcol2 : D (0, 1) = (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
      inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
    dsimp [D]
    have hline : HasDerivAt (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 :=
      fderiv_along_axis_eq_deriv (H := red ∘ A) (p := u) (e := ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) hcdAat
    have hpath : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
        fun s : ℝ => red (a, (b + s, m)) := by
      funext s
      change red (A ((m, (a, b)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b + s, m))
      congr 1
      dsimp [A, u, splitAB]
      simp
    have hg' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ (red ∘ A) u) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) 0 := by
      rw [hpath] at hline
      exact hline
    have hlineR : HasDerivAt (fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 :=
      fderiv_along_axis_eq_deriv (H := red) (p := (a, (b, m))) (e := axisVec (1 : Fin 3)) hcdR
    have hpathR : (fun s : ℝ => red (a, (b + s, m))) = fun s : ℝ => red ((a, (b, m)) + s • axisVec (1 : Fin 3)) := by
      funext s
      congr 1
      dsimp [axisVec]
      ext <;> simp
    have hlineR' : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
        ((fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3))) 0 := by
      rw [← hpathR] at hlineR
      exact hlineR
    have huniq := HasDerivAt.unique hlineR' hg'
    have hcol : (fderiv ℝ red (a, (b, m))) (axisVec (1 : Fin 3)) =
        (inner ℝ (collPartialB r a b m) (collPartialA r a b m),
          inner ℝ (collPartialB r a b m) (collPartialB r a b m)) := by
      dsimp [red]
      simpa [collPartial_eq_A, collPartial_eq_B] using
        (fderiv_pairReduced_axis h a b m (1 : Fin 3) (0 : Fin 3) (1 : Fin 3))
    rw [hcol] at huniq
    simpa [ContinuousLinearMap.comp_apply] using huniq.symm
  -- invertibility of the partial derivative: Gram determinant is nonzero
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialB r a b m);
        inner ℝ (collPartialB r a b m) (collPartialA r a b m),
        inner ℝ (collPartialB r a b m) (collPartialB r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D) (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialB r a b m))
      (c₂₁ := inner ℝ (collPartialB r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialB r a b m);
              inner ℝ (collPartialB r a b m) (collPartialA r a b m),
              inner ℝ (collPartialB r a b m) (collPartialB r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialB r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  -- identification of the zero sets
  have hidentAB : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (1 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentAB with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.2.2, z.1)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.2, z.1)) :=
      (Continuous.snd continuous_snd).prodMk continuous_fst
    exact hc1.prodMk hc2
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitAB := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.2.2, z.1)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.2, z.1)) :=
      (Continuous.snd continuous_snd).prodMk continuous_fst
    exact hc1.prodMk hc2
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitAB (x, ψ x)) = 0 ∧ splitAB (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitAB z) = 0 → splitAB z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitAB z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitAB, unSplitAB, hAcont, unSplitAB_continuous, unSplitAB_splitAB,
    splitAB_unSplitAB, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩, And.intro rfl (And.intro rfl rfl)⟩


/-- **The `(A,B)` graph-arc instance**: at a collinear off-diagonal triple
whose `a`- and `b`-hinge partials are independent, the local trisecant arc
carries graph coordinates (`RealGraphArc`) — graph over the `m`-coordinate
with split `splitAB` and implicit function `ψ`. -/
noncomputable def realGraphArc_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    RealGraphArc r :=
  Classical.choice (exists_realGraphArc_AB h a b m hΦ hZ hW0 hmb hLI)
theorem exists_realGraphArc_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    Nonempty (RealGraphArc r) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAM
  let u : ℝ × (ℝ × ℝ) := (b, (a, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q := rfl
  have hp0 : (a, (b, m)) = (a, (b, m)) := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a + s, (b, m)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
      (inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a + s, (b, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a + s, (b, m))) (col := (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialA r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentAM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentAM with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.1, z.2.2)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.2)) :=
      continuous_fst.prodMk (Continuous.snd continuous_snd)
    exact hc1.prodMk hc2
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitAM := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.1, z.2.2)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.2)) :=
      continuous_fst.prodMk (Continuous.snd continuous_snd)
    exact hc1.prodMk hc2
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitAM (x, ψ x)) = 0 ∧ splitAM (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitAM z) = 0 → splitAM z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitAM z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitAM, unSplitAM, hAcont, unSplitAM_continuous, unSplitAM_splitAM,
    splitAM_unSplitAM, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩⟩
theorem exists_realGraphArc_AM_splitting {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    ∃ d : RealGraphArc r, d.B = unSplitAM ∧ d.A = splitAM ∧ d.u = (b, (a, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitAM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitAM
  let u : ℝ × (ℝ × ℝ) := (b, (a, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitAM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (0 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q := rfl
  have hp0 : (a, (b, m)) = (a, (b, m)) := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (0 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (0 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitAM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a + s, (b, m)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a + s, (b, m))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a + s, (b, m)))
      (inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (0 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (0 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a + s, (b, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
      inner ℝ (collPartialA r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a + s, (b, m))) (col := (inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((b, (a, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitAM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (0 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (0 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
        inner ℝ (collPartialA r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialA r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialA r a b m) (collPartialA r a b m))
      (c₁₂ := inner ℝ (collPartialA r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialA r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialA r a b m) (collPartialA r a b m),
              inner ℝ (collPartialA r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialA r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialA r a b m) (collPartialA r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialA r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialA r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentAM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (0 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentAM with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.1, z.2.2)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.2)) :=
      continuous_fst.prodMk (Continuous.snd continuous_snd)
    exact hc1.prodMk hc2
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitAM := by
    change Continuous (fun z : ℝ × (ℝ × ℝ) => (z.2.1, (z.1, z.2.2)))
    have hc1 : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.1) := Continuous.fst continuous_snd
    have hc2 : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.2)) :=
      continuous_fst.prodMk (Continuous.snd continuous_snd)
    exact hc1.prodMk hc2
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitAM (x, ψ x)) = 0 ∧ splitAM (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitAM z) = 0 → splitAM z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitAM z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitAM, unSplitAM, hAcont, unSplitAM_continuous, unSplitAM_splitAM,
    splitAM_unSplitAM, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩, And.intro rfl (And.intro rfl rfl)⟩


/-- **The `(A,M)` graph-arc instance**: at a collinear off-diagonal triple
whose `a`- and `m`-hinge partials are independent, the local trisecant arc
carries graph coordinates (`RealGraphArc`) — graph over the `b`-coordinate
with split `splitAM` and implicit function `ψ`. -/
noncomputable def realGraphArc_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    RealGraphArc r :=
  Classical.choice (exists_realGraphArc_AM h a b m hΦ hZ hW0 hmb hLI)
theorem exists_realGraphArc_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    Nonempty (RealGraphArc r) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitBM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitBM
  let u : ℝ × (ℝ × ℝ) := (a, (b, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitBM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (1 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (1 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitBM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a, (b + s, m)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a, (b + s, m))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
      (inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b + s, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
      inner ℝ (collPartialB r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a, (b + s, m))) (col := (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (c₁₂ := inner ℝ (collPartialB r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialB r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
              inner ℝ (collPartialB r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialB r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentBM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (1 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentBM with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    exact continuous_id
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitBM := by
    exact continuous_id
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitBM (x, ψ x)) = 0 ∧ splitBM (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitBM z) = 0 → splitBM z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitBM z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitBM, unSplitBM, hAcont, unSplitBM_continuous, unSplitBM_splitBM,
    splitBM_unSplitBM, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩⟩
theorem exists_realGraphArc_BM_splitting {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    ∃ d : RealGraphArc r, d.B = unSplitBM ∧ d.A = splitBM ∧ d.u = (a, (b, m)) := by
  let p : RealParamTriple := (a, (b, m))
  let A : ℝ × (ℝ × ℝ) → RealParamTriple := splitBM
  let B : RealParamTriple → ℝ × (ℝ × ℝ) := unSplitBM
  let u : ℝ × (ℝ × ℝ) := (a, (b, m))
  let red : RealParamTriple → ℝ × ℝ := fun q => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q
  have hColl : collinearityMap r p = 0 := by dsimp [p]; exact hΦ
  have hOff : p ∈ RealOffDiagonalTriples r := by
    dsimp [p, RealOffDiagonalTriples]
    exact ⟨hZ, hW0, hmb⟩
  have hu : A u = p := by
    dsimp [A, u, p, splitBM]
  have hred0 : red p = (0, 0) := by
    dsimp [red, p]
    exact pairReduced_base_zero a b m (1 : Fin 3) (2 : Fin 3) hΦ
  have hredColl : ∀ q : RealParamTriple, collinearityMap r q = 0 → red q = (0, 0) := by
    intro q hq
    dsimp [red]
    simp [pairReduced, hq]
  have hred : red = fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q := rfl
  have hCdA : ContDiff ℝ 1 (red ∘ A) := by
    dsimp [red, A]
    have hc : ContDiff ℝ 1 (fun q : RealParamTriple => pairReduced r a b m (1 : Fin 3) (2 : Fin 3) q) :=
      ContDiff.of_le (contDiff_pairReduced h a b m (1 : Fin 3) (2 : Fin 3)) le_top
    exact ContDiff.comp hc (ContDiff.of_le splitBM_contDiff le_top)
  have hcdAat : DifferentiableAt ℝ (red ∘ A) u := hCdA.differentiable_one u
  let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (fderiv ℝ (red ∘ A) u) ∘L .inr ℝ ℝ (ℝ × ℝ)
  have hpath1 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun s : ℝ => red (a, (b + s, m)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) = red (a, (b + s, m))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd1 : HasDerivAt (fun s : ℝ => red (a, (b + s, m)))
      (inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (1 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (1 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b + s, m))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol1 : D (1, 0) = (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
      inner ℝ (collPartialB r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((1 : ℝ), (0 : ℝ)))
      (path := fun s : ℝ => (a, (b + s, m))) (col := (inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m))) hcdAat hpath1
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd1)
    simpa using hc
  have hpath2 : (fun s : ℝ => (red ∘ A) (u + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun s : ℝ => red (a, (b, m + s)) := by
    funext s
    change red (A ((a, (b, m)) + s • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) = red (a, (b, m + s))
    congr 1
    dsimp [A, u, splitBM]
    simp
  have hd2 : HasDerivAt (fun s : ℝ => red (a, (b, m + s)))
      (inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (1 : Fin 3)),
        inner ℝ (collPartial r a b m (2 : Fin 3)) (collPartial r a b m (2 : Fin 3))) 0 := by
    exact axis_path_col h a b m (1 : Fin 3) (2 : Fin 3) (2 : Fin 3) red hred (a, (b, m)) rfl
      (fun s : ℝ => (a, (b, m + s))) (by funext s; dsimp [axisVec]; ext <;> ring)
  have hcol2 : D (0, 1) = (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
      inner ℝ (collPartialM r a b m) (collPartialM r a b m)) := by
    dsimp [D]
    have hc := split_col_helper (red := red) (A := A) (u := u) (d := ((0 : ℝ), (1 : ℝ)))
      (path := fun s : ℝ => (a, (b, m + s))) (col := (inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m))) hcdAat hpath2
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hd2)
    simpa using hc
  have hgram : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
        inner ℝ (collPartialB r a b m) (collPartialM r a b m);
        inner ℝ (collPartialM r a b m) (collPartialB r a b m),
        inner ℝ (collPartialM r a b m) (collPartialM r a b m)]) ≠ 0 := by
    exact Commons.Analysis.InnerProductSpace.gram_det_ne_zero_of_linearIndependent hLI
  have if₂ : D.IsInvertible := by
    exact Commons.Analysis.Normed.isInvertible_of_det_columns (D := D)
      (c₁₁ := inner ℝ (collPartialB r a b m) (collPartialB r a b m))
      (c₁₂ := inner ℝ (collPartialB r a b m) (collPartialM r a b m))
      (c₂₁ := inner ℝ (collPartialM r a b m) (collPartialB r a b m))
      (c₂₂ := inner ℝ (collPartialM r a b m) (collPartialM r a b m))
      (hc₁ := hcol1) (hc₂ := hcol2) (hdet := by
        have hEq : (Matrix.det !![inner ℝ (collPartialB r a b m) (collPartialB r a b m),
              inner ℝ (collPartialB r a b m) (collPartialM r a b m);
              inner ℝ (collPartialM r a b m) (collPartialB r a b m),
              inner ℝ (collPartialM r a b m) (collPartialM r a b m)])
            = (inner ℝ (collPartialB r a b m) (collPartialB r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialM r a b m)) -
              (inner ℝ (collPartialB r a b m) (collPartialM r a b m)) *
                (inner ℝ (collPartialM r a b m) (collPartialB r a b m)) := by
          rw [Matrix.det_fin_two_of]
        rw [← hEq]
        exact hgram)
  have hidentBM : ∃ U : Set RealParamTriple, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, red q = (0, 0) → collinearityMap r q = 0 := by
    simpa [red] using (identification_pairReduced_zero h a b m (1 : Fin 3) (2 : Fin 3) hΦ hZ
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLI))
  -- identify the zero sets (red = 0 ⟺ collinear) near the triple
  rcases hidentBM with ⟨Uid, hUido, hUidp, hUid⟩
  -- ψ from the product-domain implicit function theorem
  rcases Commons.Analysis.Calculus.Implicit.implicitFunction_graph
    (u := u) (f := red ∘ A)
    (cdf := ContDiff.contDiffAt (n := 1) hCdA)
    (h0 := by
      change red (A u) = (0, 0)
      rw [hu]
      exact hred0)
    (if₂ := if₂) with ⟨ψ, hψu, hψV, hcover⟩
  rcases hψV with ⟨V, hVV, hψcd, hψval⟩
  -- the covering neighbourhood W (open) on which the zero set is the graph
  have hWex : ∃ W : Set (ℝ × (ℝ × ℝ)), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, (red ∘ A) v = (0, 0) → ψ v.1 = v.2 := by
    rcases hcover.exists_mem with ⟨W₀, hW₀u, hW₀⟩
    rcases mem_nhds_iff.mp hW₀u with ⟨W, hWsub, hWopen, hWu⟩
    refine ⟨W, hWopen, hWu, ?_⟩
    intro v hv
    exact hW₀ v (hWsub hv)
  rcases hWex with ⟨W, hWopen, hWu, hW⟩
  -- ψ is C¹ at u.1 (hence continuous) since V is a neighbourhood of u.1
  have hψcdAt : ContDiffAt ℝ 1 ψ u.1 := ContDiffOn.contDiffAt hψcd hVV
  have hψcontAt : ContinuousAt ψ u.1 := hψcdAt.continuousAt
  have hpairAt : ContinuousAt (fun x : ℝ => (x, ψ x)) u.1 := continuousAt_id.prodMk hψcontAt
  -- the good set G = Uid ∩ offdiag ∋ p0
  have hOffo : IsOpen (RealOffDiagonalTriples r) := isOpen_RealOffDiagonalTriples h
  let G : Set RealParamTriple := Uid ∩ RealOffDiagonalTriples r
  have hGo : IsOpen G := hUido.inter hOffo
  have hGp : p ∈ G := ⟨hUidp, hOff⟩
  -- the x-neighbourhood where everything is good
  have hWmem : {x : ℝ | (x, ψ x) ∈ W} ∈ 𝓝 u.1 := by
    have hm : (u.1, ψ u.1) ∈ W := by
      simpa [hψu] using hWu
    exact hpairAt.preimage_mem_nhds (hWopen.mem_nhds hm)
  have hAcont0 : Continuous A := by
    dsimp [A]
    exact continuous_id
  have hpathAt : ContinuousAt (fun x : ℝ => A (x, ψ x)) u.1 :=
    (hAcont0.continuousAt.comp hpairAt)
  have hGmem : {x : ℝ | A (x, ψ x) ∈ G} ∈ 𝓝 u.1 := by
    have hg : A u ∈ G := by
      simpa [hu] using hGp
    exact hpathAt.preimage_mem_nhds (hGo.mem_nhds (by simpa [hψu] using hg))
  have hUx : (V ∩ {x : ℝ | (x, ψ x) ∈ W} ∩ {x : ℝ | A (x, ψ x) ∈ G}) ∈ 𝓝 u.1 :=
    Filter.inter_mem (Filter.inter_mem hVV hWmem) hGmem
  rcases exists_Ioo_subset_of_mem_nhds hUx with ⟨a1, b1, ha1, hb1, hab1⟩
  -- continuity of the split map
  have hAcont : Continuous splitBM := by
    exact continuous_id
  -- ψ is C¹ on the selected x-interval
  have hψC1b : ContDiffOn ℝ 1 ψ (Set.Ioo a1 b1) := by
    refine hψcd.mono ?_
    intro x hx
    exact (hab1 hx).left.left
  -- the graph over (a1,b1) is a collinear off-diagonal zero of Φ
  have hgraph_goodb : ∀ x ∈ Set.Ioo a1 b1,
      collinearityMap r (splitBM (x, ψ x)) = 0 ∧ splitBM (x, ψ x) ∈ RealOffDiagonalTriples r := by
    intro x hx
    have hxU := hab1 hx
    have hxV : x ∈ V := hxU.left.left
    have hxG : A (x, ψ x) ∈ G := hxU.right
    have hredψ : red (A (x, ψ x)) = (0, 0) := hψval x hxV
    constructor
    · exact hUid (A (x, ψ x)) hxG.1 hredψ
    · exact hxG.2
  -- the graph lies inside W on (a1,b1)
  have hgraphWb : ∀ x ∈ Set.Ioo a1 b1, (x, ψ x) ∈ W := by
    intro x hx
    exact (hab1 hx).left.right
  -- covering: every zero in the x-slice over W sits on the graph
  have hcoverb : ∀ z : ℝ × (ℝ × ℝ), z.1 ∈ Set.Ioo a1 b1 → z ∈ W →
      collinearityMap r (splitBM z) = 0 → splitBM z ∈ RealOffDiagonalTriples r →
      ψ z.1 = z.2 := by
    intro z hz1 hzW hcoll hoff
    exact hW z hzW (hredColl (splitBM z) hcoll)
  -- assemble the RealGraphArc record (graph over (a1,b1), neighbourhood W)
  exact ⟨⟨splitBM, unSplitBM, hAcont, unSplitBM_continuous, unSplitBM_splitBM,
    splitBM_unSplitBM, u, ψ, hψu, a1, b1, ha1, hb1, hψC1b, hgraph_goodb, W, hWopen,
    hWu, hgraphWb, hcoverb⟩, And.intro rfl (And.intro rfl rfl)⟩


/-- **The `(B,M)` graph-arc instance**: at a collinear off-diagonal triple
whose `b`- and `m`-hinge partials are independent, the local trisecant arc
carries graph coordinates (`RealGraphArc`) — graph over the `a`-coordinate
with the identity split `splitBM` and implicit function `ψ`. -/
noncomputable def realGraphArc_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    RealGraphArc r :=
  Classical.choice (exists_realGraphArc_BM h a b m hΦ hZ hW0 hmb hLI)
