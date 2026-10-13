/-
  WilG4c / `StepHigherAsm` — the *assembly* half of BNZ §5.4 (`Work.WilkG4c.StepHigher`).

  ## What is assembled here

  `Work.WilkG4c.StepHigher` reduces `FLemP (PYLipDef)` to `FLemP (PYLip)`.  The construction
  (BNZ §5.4) has three parts:

  * **(d)+(e) the estimate**: from the tuple of near-maximising curves and the surrogates,
    BNZ's Corollary 5.5 (`h1`) produces affine `x`-charts `x = α l + β l · t`, and the
    inductive computation along the curves (the engine `Work.WilkG4c.curve_bound`,
    `Work.WilkG4c.tnorm_curve_system_w`) plus BNZ Lemma 4.1 (`Work.WilkG4c.TnormRescale`)
    shows that for every chart the *pullback* `pullX F α β`, subdivided into the cubes of
    side `1/N` (`subdivN n r`), satisfies `PYLipDef`.
  * **(f) the assembly** (this file): apply `hP2` (i.e. `FLemP (PYLipDef)`) to each subdivided
    pullback, obtaining charts `ψ` of the rescaled cube, and compose them back along
    `Φ_η ∘ subdiv ∘ ψ`; the `Ω`-boundedness of the composite's coordinate graphs, the
    cardinality bound and the `ε`-cover are assembled here.

  The interface `StepStage` (in `StepHigherStageDefs`) isolates (d)+(e) as a *hypothesis*: it is
  exactly "for every chart `(α,β)` of the `h1`-output, the pullback `pullX F α β` has the
  multi-curve data that `Work.WilkG4c.pullback_pylipdef_multi_bad` consumes".

  ## Contents

  * `famGraph_subdivMap_mem` — the `Ω`-graph of the subdivided pullback (from `FamGraphRescale`).
  * `valuesIn01_subdivMap` — the subdivided pullback has values in `(0,1)`.
  * `subdivMap_interior_cover` — every point of the open cube lies in the image of some
    subdivision chart (`Work.WilkG4c.subdivMap`), with a point of the open cube as preimage.
  * `FLemP_of_stage` — **the assembly**: `StepStage → FLemP (PYLipDef) → FLemP (PYLip)`.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4c.Pullback
import Submission.Work.WilG4c.pullX_YBound
import Submission.Work.WilG4c.pullX_lip
import Submission.Work.WilG4c.pullback_pylipdef_multi_bad
import Submission.Work.WilG4c.famGraph_pullX
import Submission.Work.WilG4c.FamGraphRescale
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.Norm
import Submission.Work.WilG4c.subdivChart_graph_mem
import Submission.Work.WilG4c.polyCountEval_comp4

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 2. The subdivided pullback: `Ω`-graphs and values -/

/-- The subdivision chart `subdivMap N s` is a diagonal rescaling: `z ↦ q + z/N` with
`q = subdivBase N s` a *constant* vector.  Hence `FamGraphRescale` applies verbatim and the
graph of the subdivided family is `Ω`-bounded with the format raised by a constant and the
degree by `2`. -/
theorem famGraph_subdivMap_mem (S : SOMin) (p n : ℕ) :
    ∃ K₁ : ℕ, ∀ (N : ℕ) (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) (F0 D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      famGraph (fun l z => f l (subdivMap N s z)) ∈
        S.Ω (F0 + K₁) (D + 2) (p + (n + 1) + 1) := by
  obtain ⟨K₁, hK⟩ := FamGraphRescale S p n
  refine ⟨K₁, ?_⟩
  intro N s F0 D f hf
  have hfam : (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
        f l (fun j => subdivBase N s j + z j / (N : ℝ)))
      = (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) => f l (subdivMap N s z)) := by
    funext l z
    congr 1
    funext j
    rw [subdivMap_eq]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  rw [← hfam]
  exact hK N (subdivBase N s) F0 D f hf

/-- The subdivided pullback still takes values in `(0,1)` on `Λ`: the subdivision chart maps
the open cube strictly into itself (`Work.WilkG4c.subdivMap_mem_openCube`). -/
theorem valuesIn01_subdivMap {k p n N : ℕ} (hN : 1 ≤ N)
    (s : Fin (n + 1) → Fin (3 * (N - 1) + 1)) {Λ : Set (Fin p → ℝ)}
    {F : Family k p (n + 1)} (h : ValuesIn01 Λ F) :
    ValuesIn01 Λ (fun i l z => F i l (subdivMap N s z)) := by
  intro i l hl z hz
  exact h i l hl (subdivMap N s z) (subdivMap_mem_openCube hN s hz)

/-! ## 4. The `ε`-cover of the assembly -/

/-- **The `ε`-cover of the assembly.**  Suppose the affine charts `Φ₁` cover the `x`-interval `I`
up to `ε/2` (`hdom`), the family is `1`-Lipschitz, and for every chart `(α,β) ∈ Φ₁` and every
subdivision index `s` the chart family `Ψ αβ s` covers the *image* of the subdivided pullback
up to `ε/2`.  Then the composed charts `subdivChart α β s ψ` cover the cube up to `ε`.

This is the covering argument of BNZ §5.4 (spelled out in the plan, §12.3): the `x`-coordinate
is moved to the affine chart point (cost `ε/2` by Lipschitzness), the resulting point of the
pullback's cube lies in the image of a subdivision chart (`subdivMap_covers`), and the
`hP2`-cover of the subdivided pullback supplies the last `ε/2`. -/
theorem covers_subdivChart {k p n N : ℕ} (hN : 1 ≤ N) {Λ : Set (Fin p → ℝ)}
    {F : Family k p (n + 1)} {ε : ℝ} (hLip : LipOnCube F 1)
    {Φ₁ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))}
    (hαβ : ∀ cb ∈ Φ₁, ∀ l, 0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1)
    (hdom : ∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ Φ₁, ∃ t ∈ I, |cb.1 l + cb.2 l * t - x| < ε / 2)
    {Ψ : (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)) → (Fin (n + 1) → Fin (3 * (N - 1) + 1)) →
      Finset (ChartTuple p (n + 1))}
    (hcov : ∀ cb ∈ Φ₁, ∀ s, Covers Λ
      (fun i l t => pullX F cb.1 cb.2 i l (subdivMap N s t)) (Ψ cb s) (ε / 2)) :
    Covers Λ F (Φ₁.biUnion (fun cb => Finset.univ.biUnion (fun s =>
      (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)))) ε := by
  intro l hl x hx
  -- the `x`-coordinate is covered by an affine chart
  obtain ⟨hx0, hx1⟩ := hx 0
  obtain ⟨cb, hcb, t₀, ht₀, hclose⟩ := hdom l hl (x 0) ⟨hx0, hx1⟩
  obtain ⟨hβ, hα, hαβl⟩ := hαβ cb hcb l
  -- the point of the pullback's cube and its chart point
  have hpt : pt t₀ (Fin.tail x) ∈ openCube (n + 1) :=
    pt_mem_openCube.mpr ⟨ht₀, fun j => hx j.succ⟩
  have hx' : chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)) ∈ openCube (n + 1) :=
    chartPt_mem_openCube hα hβ hαβl hpt
  have hdist : dist (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) x < ε / 2 := by
    have htail : Fin.tail (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) = Fin.tail x := by
      rw [chartPt_pt]
      exact tail_pt t₀ (Fin.tail x)
    refine lt_of_le_of_lt (dist_le_of_tail_eq htail) ?_
    rw [chartPt_pt, pt_zero]
    exact hclose
  -- the subdivision cover at that point
  obtain ⟨s, u, hu, hsu⟩ := subdivMap_covers hN hpt
  -- the `hP2`-cover of the subdivided pullback
  obtain ⟨ψ, hψ, t, ht, hbound⟩ := hcov cb hcb s l hl u hu
  refine ⟨subdivChart cb.1 cb.2 s ψ, ?_, t, ht, fun i => ?_⟩
  · refine Finset.mem_biUnion.mpr ⟨cb, hcb, Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ s, Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩⟩⟩
  · have h1 : |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t)
        - F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)))| < ε / 2 := by
      have h := hbound i
      simp only [pullX_apply] at h
      rw [hsu] at h
      exact h
    have h2 : |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x| ≤ ε / 2 := by
      calc |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x|
          ≤ 1 * dist (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) x := hLip i l _ x hx' hx
        _ ≤ ε / 2 := by rw [one_mul]; exact le_of_lt hdist
    calc |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t) - F i l x|
        ≤ |F i l (fun j => subdivChart cb.1 cb.2 s ψ j l t)
            - F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x)))|
          + |F i l (chartPt cb.1 cb.2 l (pt t₀ (Fin.tail x))) - F i l x| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1 h2
      _ = ε := by ring

end Work.WilkG4c
