import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.twoLetter_F2_generation
import Submission.Work.ORBassSerre.Interface
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.OROneRel.coset_lev
import Submission.Work.OROneRel.cosetGraphDist
import Submission.Work.OROneRel.arrowULift
import Submission.Work.OROneRel.isTree_arrowULift
import Submission.Work.OROneRel.exists_arrowULift_graphAction
import Submission.Work.OROneRel.band_cosetGraph_isTree

/-!
# The `F₂`-tree of the two-letter band: reduction to the coset tree of `(winRho.range, tlLowTau)`

The target `Work.OROneRel.winRhoRange_tree` asks, for the two-letter band data, for an `F₂`-tree
(`F₂ = FreeGroup (Fin 2)`) on which the subgroup `H = (winRho Wt c 0 (p*q)).range` is the
stabiliser of a vertex `v` and in which some edge joins `v` to `tlLowTau⁻¹ • v`.

This file records the *reduction* of that target to the single tree statement about the **coset
graph of the pair `(H, tlLowTau)`** (`Work.OROneRel.GradedHNN.Coset H t`: vertices the left cosets
`F₂ ⧸ H`, edges `{gH, gHt}`), together with the elementary facts that make the reduction work:

* `cohom_winRho_of`, `cohom_eq_one_of_mem_winRho_range`: every element of `H` has weight `0`
  (the loop class `W i * x * (W (i + c x))⁻¹` is killed by `cohom c` when `W` is a gauge);
* `stabilizer_baseC_eq`: the stabiliser of the base vertex `H` of the coset graph is `H`;
* `actsWithoutInversions_coset`: the coset graph has **no inversions**: an inversion would force
  `2 * χ(g) = 0` while the adjacency forces the levels to differ by exactly one.

The remaining obligation is exactly Linton's one-dimensional splitting statement for the band graph
of the two-petal rose (`Work.OROneRel.NOTES_twoLetterBandComparison_injective.md`, §13): the coset
graph of `(H, tlLowTau)` is a tree, i.e. `F₂` is the HNN extension of `H` with stable letter
`tlLowTau` over the gate `H ⊓ tlLowTau⁻¹ H tlLowTau`.
-/

namespace Work.OROneRel

open Quiver

/-! ## Elements of `winRho.range` have weight zero -/

/-- The loop class of an edge of the window is killed by the weight: if `Wt` is a gauge, the class
`Wt i * x * (Wt (i + c x))⁻¹` has weight `i + c x - (i + c x) = 0`. -/
theorem cohom_winRho_of {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) (e : winBeta Wt c lo hi) :
    cohom c (winRho Wt c lo hi (FreeGroup.of e)) = 1 := by
  rw [winRho_of, coverClassAt, gaugeMap_of]
  rw [map_mul, map_mul, map_inv, hcoh, hcoh, cohom_of, ← ofAdd_add, ← ofAdd_neg, ← ofAdd_add,
    add_neg_cancel]
  rfl

/-- **Every element of `winRho.range` has weight zero.** -/
theorem cohom_eq_one_of_mem_winRho_range {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (hcoh : ∀ i : ℤ, cohom c (Wt i) = Multiplicative.ofAdd i) {g : FreeGroup α}
    (hg : g ∈ (winRho Wt c lo hi).range) : cohom c g = 1 := by
  obtain ⟨x, rfl⟩ := hg
  induction x using FreeGroup.induction_on with
  | one => simp
  | of e => exact cohom_winRho_of Wt c lo hi hcoh e
  | inv_of e ih =>
      show cohom c (winRho Wt c lo hi (FreeGroup.of e)⁻¹) = 1
      rw [map_inv, map_inv]
      exact inv_eq_one.mpr ih
  | mul x y hx hy =>
      show cohom c (winRho Wt c lo hi (x * y)) = 1
      rw [map_mul, map_mul]
      rw [hx, hy, one_mul]

/-! ## The stabiliser of the base vertex of the coset graph -/

/-- The stabiliser of the base vertex `H` of the coset graph of the pair `(H, t)` is `H` itself. -/
theorem stabilizer_baseC_eq {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    MulAction.stabilizer G (GradedHNN.baseC H t) = H := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [GradedHNN.smul_cmk, mul_one] at h
    have h' : g⁻¹ * (1 : G) ∈ H := (GradedHNN.cmk_eq_iff H t).mp h
    have h2 : g⁻¹ ∈ H := by simpa using h'
    simpa using H.inv_mem h2
  · intro hg
    have h1 : g • GradedHNN.baseC H t = GradedHNN.cmk H t g := by
      rw [GradedHNN.smul_cmk, mul_one]
    rw [h1]
    exact (GradedHNN.cmk_eq_iff H t).mpr (by simpa using hg)

/-! ## The coset graph of `(H, t)` has no inversions -/

/-- **The coset graph of `(H, t)` has no inversions**, as soon as `H` is killed by a weight map
`φbar` with `φbar t` of weight one: an inversion `g • e = e.reverse` forces both `g • x = y` and
`g • y = x`, hence `χ(g) = -χ(g)` while `χ(y) - χ(x) = χ(g)`, contradicting that adjacent vertices
differ in level by exactly one. -/
theorem actsWithoutInversions_coset {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (φbar : G →* Multiplicative ℤ) (hH : ∀ h : H, φbar (h : G) = 1)
    (ht : φbar t = Multiplicative.ofAdd 1) :
    Work.ORBassSerre.ActsWithoutInversions G (GradedHNN.Coset H t) := by
  intro g e he
  obtain ⟨x, y, f⟩ := e
  have h1 : g • x = y := by
    have h := congrArg Quiver.Total.left he
    rw [Work.ORBassSerre.GraphAction.smul_left, Quiver.Total.reverse_mk] at h
    simpa using h
  have h2 : g • y = x := by
    have h := congrArg Quiver.Total.right he
    rw [Work.ORBassSerre.GraphAction.smul_right, Quiver.Total.reverse_mk] at h
    simpa using h
  have hle : |GradedHNN.lev H t φbar hH y - GradedHNN.lev H t φbar hH x| = 1 :=
    GradedHNN.abs_lev_adj H t φbar hH ht f
  have e1 : GradedHNN.lev H t φbar hH y
      = (φbar g).toAdd + GradedHNN.lev H t φbar hH x := by
    rw [← h1, GradedHNN.lev_smul]
  have e2 : GradedHNN.lev H t φbar hH x
      = (φbar g).toAdd + GradedHNN.lev H t φbar hH y := by
    rw [← h2, GradedHNN.lev_smul]
  have hzero : GradedHNN.lev H t φbar hH y - GradedHNN.lev H t φbar hH x = 0 := by linarith
  rw [hzero] at hle
  simp at hle

/-! ## The reduction: the target from the tree-ness of the coset graph of `(H₀, τ)`

The coset graph `GradedHNN.Coset H t` of a pair `(H, t)` has vertices the left cosets `G ⧸ H` and
edges the pairs `{gH, gtH}`.  Take `G = F₂ = FreeGroup (Fin 2)`, `H = H₀ =
(winRho Wt (tlW p q) 0 (p*q)).range` and `t = τ = tlLowTau p q hp hq hcop`.  Then

* the stabiliser of the base vertex is `H₀` (`stabilizer_baseC_eq`),
* the action is without inversions (`actsWithoutInversions_coset`, using
  `cohom_eq_one_of_mem_winRho_range` and `tlLowTau_cohom`),
* and the fundamental edge `edgeArrowC H τ : baseC ⟶ τ⁻¹ • baseC` satisfies
  `τ • (τ⁻¹ • baseC) = baseC`.

So the tree-ness of that coset graph -- the one remaining mathematical input, the "one-dimensional
splitting" of Linton, *One-relator hierarchies*, arXiv:2202.11324 (Proposition `splitting`) -- yields
the target, with `V` the arrow-`ULift` of the coset graph: the target's existential quantifies over
an arbitrary universe for the *arrows*, so the lift is needed, and `isTree_arrowULift` /
`exists_arrowULift_graphAction` transport the tree structure and the action along it. -/

/-- **Connectivity of the band coset graph.**  For the two-letter band data the coset graph of
`(H₀, τ)` is connected, since `F₂ = ⟨H₀, τ⟩` (`twoLetter_F2_generation`); this is the connectivity
half of the tree statement. -/
theorem cosetBand_connected (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    ∀ x y : GradedHNN.Coset
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop), Nonempty (Quiver.Path x y) :=
  GradedHNN.connected_coset _ _
    (twoLetter_F2_generation p q hp hq hcop Wt hW0 hcoh hwin htree)

/-- **The target from the tree-ness of the band coset graph.** -/
theorem winRhoRange_tree_of_cosetTree (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hT : Work.ORBassSerre.IsTree (GradedHNN.Coset
      (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range
      (Work.OROneRel.tlLowTau p q hp hq hcop))) :
    ∃ (V : Type) (_ : Quiver V) (_ : Quiver.HasInvolutiveReverse V)
      (_ : MulAction (FreeGroup (Fin 2)) V)
      (_ : Work.ORBassSerre.GraphAction (FreeGroup (Fin 2)) V) (v z : V) (e : v ⟶ z),
      Work.ORBassSerre.IsTree V ∧ Work.ORBassSerre.ActsWithoutInversions (FreeGroup (Fin 2)) V ∧
      MulAction.stabilizer (FreeGroup (Fin 2)) v =
        (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range ∧
      (Work.OROneRel.tlLowTau p q hp hq hcop) • z = v := by
  classical
  set H : Subgroup (FreeGroup (Fin 2)) :=
    (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range with hHdef
  set τ : FreeGroup (Fin 2) := Work.OROneRel.tlLowTau p q hp hq hcop with hτdef
  have hφH : ∀ h : H, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (h : FreeGroup (Fin 2)) = 1 :=
    fun h => cohom_eq_one_of_mem_winRho_range Wt (Work.OROneRel.tlW p q) 0
      ((p : ℤ) * (q : ℤ)) hcoh h.2
  have hφτ : Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1 := by
    rw [hτdef]; exact tlLowTau_cohom p q hp hq hcop
  have hT' : @Work.ORBassSerre.IsTree (GradedHNN.Coset H τ)
      (Work.OROneRel.arrowULiftQuiver (GradedHNN.Coset H τ) (GradedHNN.instQuiverCoset H τ))
      (Work.OROneRel.arrowULiftHasInvolutiveReverse (GradedHNN.Coset H τ)
        (GradedHNN.instQuiverCoset H τ) (GradedHNN.instHasInvolutiveReverseCoset H τ)) :=
    isTree_arrowULift (V := GradedHNN.Coset H τ) (Q := GradedHNN.instQuiverCoset H τ)
      (GradedHNN.instHasInvolutiveReverseCoset H τ) hT
  have hninv : @Work.ORBassSerre.ActsWithoutInversions (FreeGroup (Fin 2)) (GradedHNN.Coset H τ)
      FreeGroup.instGroup (GradedHNN.instQuiverCoset H τ) (GradedHNN.instHasReverseCoset H τ)
      (inferInstance : MulAction (FreeGroup (Fin 2)) (GradedHNN.Coset H τ))
      (GradedHNN.instGraphActionCoset H τ) :=
    actsWithoutInversions_coset H τ (Work.OROneRel.cohom (Work.OROneRel.tlW p q)) hφH hφτ
  have hA'' := Work.OROneRel.actsWithoutInversions_arrowULift (Q := GradedHNN.instQuiverCoset H τ)
      (M := (inferInstance : MulAction (FreeGroup (Fin 2)) (GradedHNN.Coset H τ)))
      (HR := GradedHNN.instHasReverseCoset H τ) (GA := GradedHNN.instGraphActionCoset H τ) hninv
  refine ⟨GradedHNN.Coset H τ,
    Work.OROneRel.arrowULiftQuiver (GradedHNN.Coset H τ) (GradedHNN.instQuiverCoset H τ),
    Work.OROneRel.arrowULiftHasInvolutiveReverse (GradedHNN.Coset H τ)
      (GradedHNN.instQuiverCoset H τ) (GradedHNN.instHasInvolutiveReverseCoset H τ),
    (inferInstance : MulAction (FreeGroup (Fin 2)) (GradedHNN.Coset H τ)),
    Work.OROneRel.arrowULiftGraphAction (Q := GradedHNN.instQuiverCoset H τ)
      (M := (inferInstance : MulAction (FreeGroup (Fin 2)) (GradedHNN.Coset H τ)))
      (HR := GradedHNN.instHasReverseCoset H τ) (GA := GradedHNN.instGraphActionCoset H τ),
    GradedHNN.baseC H τ, τ⁻¹ • GradedHNN.baseC H τ,
    Work.OROneRel.arrowULiftUp (GradedHNN.edgeArrowC H τ), hT', hA'', ?_, ?_⟩
  · exact stabilizer_baseC_eq H τ
  · show τ • (τ⁻¹ • GradedHNN.baseC H τ) = GradedHNN.baseC H τ
    rw [smul_smul, mul_inv_cancel, one_smul]

theorem winRhoRange_tree (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1) (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i) (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)), Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) → ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)), Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) : ∃ (V : Type) (_ : Quiver V) (_ : Quiver.HasInvolutiveReverse V) (_ : MulAction (FreeGroup (Fin 2)) V) (_ : Work.ORBassSerre.GraphAction (FreeGroup (Fin 2)) V) (v z : V) (e : v ⟶ z), Work.ORBassSerre.IsTree V ∧ Work.ORBassSerre.ActsWithoutInversions (FreeGroup (Fin 2)) V ∧ MulAction.stabilizer (FreeGroup (Fin 2)) v = (Work.OROneRel.winRho Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))).range ∧ (Work.OROneRel.tlLowTau p q hp hq hcop) • z = v :=
  Work.OROneRel.winRhoRange_tree_of_cosetTree p q hp hq hcop Wt hW0 hcoh hwin htree
    (Work.OROneRel.band_cosetGraph_isTree p q hp hq hcop Wt hW0 hcoh hwin htree)

end Work.OROneRel
