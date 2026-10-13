/-
  `WilG4a/CD/sliceContDiffAt_mem` — the pointwise *fibre*-`C^j` locus of a `p`-parameter family.

  ## Statement (frozen; requested by the agent working on `WilG4a/cellDecomp_exists`)

  For a family `f : (Fin p → ℝ) → ℝ → ℝ` whose graph is `Ω F0 D (p+2)`-definable in a sharply
  o-minimal structure with sharp derivatives, the set

    `W_j(f) := {z : Fin (p+1) → ℝ | ContDiffAt ℝ j (fun x => f (Fin.init z) x) (z (Fin.last p))}`

  of points at which the *slice* `x ↦ f l x` is `C^j` at `x`, is `Ω a (b.eval ![D,j]) (p+1)`
  for a format `a` and a polynomial `b` depending only on `p` and `F0`.

  ## Why it is needed

  `CellDecomp` (`WilG4a/f1affine1_defs.lean`) requires cells on which the slices are `C^{r+1}`
  with constant-signed derivatives on the fibre, or degenerate.  A cell decomposition compatible
  only with the *joint* bad loci does not suffice: the bad cells must be separated by the *fibre*
  bad loci, i.e. the complements of the `W_j`, and the decomposition must be uniform in the order
  `r` — hence the format `a` must be independent of `j`.

  ## The difficulty, and how it is resolved

  `S.SharpDeriv` is a statement about the **joint** `C^j` locus (`Cells.derivGraphSet_mem`): its
  domain is `interior {x | ContDiffAt ℝ j (famFun f) x}` and its value is `iteratedFDeriv ℝ j`.
  The joint `C^j` locus is contained in the fibre locus `W_j`, and is genuinely *smaller*; on the
  difference (`badLocus f j`) the joint condition alone says nothing.  Every "order-recursion"
  route (the junk recursion `W_{j+1}(f) = W_1(f) ∩ W_j(∂_x f)`, delegated here as
  `Work.WilG4a.CD.slice_junk_recursion`, or the `ε`-`δ` transcription of `C^j`-at-a-point) produces
  a format that grows with the *order*, not the requested uniform one.

  The uniformity in `j` is instead obtained by recursing on the *parameter dimension* (bounded by
  `p`, hence a constant) while the order `j` is handled by `SharpDeriv`'s own uniformity in the
  order.  The key notions, all in sibling modules, are:

  * the **fibre germ** `Work.WilG4a.CD.fibGerm f j`: the set of `(l,x)` whose *punctured* fibre
    neighbourhood `{t ≠ x}` lies in the interior of the joint `C^j` locus.  It is `Ω`-definable
    with a format independent of `j` (`fibGerm_mem`: the extra atoms `ρ > 0`, `t ≠ x`,
    `(t-x)² < ρ²` cost only constants).  On it, and only on it, the *fibre* condition can be
    checked against limits of the *joint* `x`-derivatives along the punctured fibre
    (`fibDerivSet_eq_fibMainSet_on_germ`).
  * The cylindrical decomposition of `ℝ^{p+1}` refining `badLocus f j` (`cellDecomp_germ`) is such
    that over every cell whose base has non-empty interior the germ holds everywhere
    (the bad locus has empty interior, being the complement of the open joint `C^j` locus, so its
    vertical fibres over a thick base are finite, and a finite fibre minus a point is a punctured
    neighbourhood); the cells over a *thin* base are then reparametrised (`thinCellParam`) and the
    family pulled back along the tube (`graphFam_param_mem`, using `subst_mem` and
    `shiftFamGraph_mem`), exhibiting it as a family with `k < p` parameters to which the induction
    hypothesis applies (`fibDerivSet_lift`).
  * Consequently the graph of the `j`-th **fibre** derivative

      `G_j(f) = {(l,x,y) : the slice at (l,x) is C^j there and y = its j-th derivative}`

    is `Ω a (b.eval ![D,j]) (p+2)` with `a` uniform in `j` and degree `poly(D,j)`
    (`Work.WilG4a.CD.fibDerivGraph_mem`).

  The frozen statement is the projection of `G_j(f)`; that one-line step is formalised here
  (`target_eq_proj` and `sliceContDiffAt_mem_of_fibDerivGraph`).

  ## Supporting lemmas proved in this directory

  * `Work.WilG4a.CD.sliceContDiffAt_one_mem` — the `j = 1` case, from the `ε`-`δ` (first-order)
    characterisation of `C^1` (`WilG4a.sliceDerivCont_mem`).
  * `Work.WilG4a.CD.slice_junk_recursion` — the junk recursion, the honest but non-uniform route.
  * `Work.WilG4a.CD.sliceContDiffAt_junk_iff` — `C^j`-ness `=` continuity `+` continuity of the
    junk `i`-th derivatives, `1 ≤ i ≤ j` (again `j`-dependent, but a useful rewriting lemma).
  * `Work.WilG4a.CD.badLoci_cellDecomp` — a cell decomposition compatible with
    `badLocus f 0, …, badLocus f j` simultaneously, with format uniform in `j`.
  * `Work.WilG4a.CD.shiftFamGraph_mem` — the graph of `(l,t) ↦ f l (g l + t)` is `Ω`-definable
    with a controlled format.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.slice_contDiffAt
import Submission.Work.WilG4a.CD.fibDerivGraph_mem

namespace Work.WilG4a.CD

open WilkiesDesign WilkiesConjecture Work.WilG4a

/-! ## The graph of the `j`-th fibre derivative -/

/-- The graph of the `j`-th derivative of the slices of `f`, over the points at which the slice
is `C^j`: the coordinates are the `p` parameters, then `x`, then the value of the derivative. -/
def fibDerivGraph {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) : Set (Fin (p + 2) → ℝ) :=
  {w | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p)) ∧
    w (Fin.last (p + 1)) =
      iteratedDeriv j (fun x : ℝ => f (Fin.init (Fin.init w)) x) ((Fin.init w) (Fin.last p))}

/-- **The target set is the projection of the fibre-derivative graph.**  This is the only step
that the frozen statement needs on top of the fibre-derivative graph. -/
theorem target_eq_proj {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    {z : Fin (p + 1) → ℝ | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p))}
      = projLast (fibDerivGraph f j) := by
  ext z
  constructor
  · intro hz
    refine ⟨iteratedDeriv j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p)), ?_⟩
    simp only [fibDerivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact ⟨by simpa using hz, trivial⟩
  · rintro ⟨y, hy⟩
    simp only [fibDerivGraph, Set.mem_ofPred_eq, projLast, Fin.init_snoc, Fin.snoc_last] at hy
    simpa using hy.1

/-! ## The "good cell" direction -/

/-- A set contained in the interior of the joint `C^j` locus of `famFun f` is contained in the
fibre `C^j` locus: the joint condition implies the slice condition.  (This is the direction that
`WilG4a/cellDecomp_exists` gets for free; it uses `Work.WilG4a.slice_contDiffAt`.) -/
theorem subset_target_of_subset_smooth {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ)
    {Y : Set (Fin (p + 1) → ℝ)} (hY : Y ⊆ smoothLocus f j) :
    Y ⊆ {z : Fin (p + 1) → ℝ | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p))} := by
  intro z hz
  have hz' : z ∈ smoothLocus f j := hY hz
  have h : Fin.snoc (Fin.init z) (z (Fin.last p)) ∈ smoothLocus f j := by
    rwa [Fin.snoc_init_self]
  have h2 := slice_contDiffAt p (famFun f) j (Fin.init z) (z (Fin.last p)) h
  simpa [famFun_apply] using h2

/-! ## Assembly -/

/-- **The frozen statement follows from the fibre-derivative graph with one projection.** -/
theorem sliceContDiffAt_mem_of_fibDerivGraph (S : WilkiesDesign.SOMin) (F0 p : ℕ)
    (h : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        fibDerivGraph f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 2)) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        {z : Fin (p + 1) → ℝ | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p))} ∈
          S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  obtain ⟨a, b, hb⟩ := h
  refine ⟨a + 1, b, ?_⟩
  intro D j f hf
  rw [target_eq_proj f j]
  exact S.proj (hb D j hf)

/-- **The fibre `C^j` locus of a `p`-parameter family is `Ω`-definable with a format uniform in
the order `j`.**  (The frozen statement.)  This is the projection of the delegated
fibre-derivative-graph statement `Work.WilG4a.CD.fibDerivGraph_mem`. -/
theorem sliceContDiffAt_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        {z : Fin (p + 1) → ℝ | ContDiffAt ℝ j (fun x : ℝ => f (Fin.init z) x) (z (Fin.last p))} ∈
          S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  refine sliceContDiffAt_mem_of_fibDerivGraph S F0 p ?_
  obtain ⟨a, b, hb⟩ := fibDerivGraph_mem S hcd hder p F0
  exact ⟨a, b, fun D j f hf => hb D j hf⟩

end Work.WilG4a.CD
