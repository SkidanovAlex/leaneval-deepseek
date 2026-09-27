import Mathlib
import Submission.Work.OneDim.PlanarModel
import Submission.Work.OneDim.PlanarProps
import Submission.Work.Embedding.Proper

/-!
# Assembly of the planar embedding from the per-component classification (`n = 1`)

Given the classification of connected smooth one-manifolds (each connected component is
diffeomorphic to `ℝ` or to the circle), we assemble a smooth embedding `M → ℝ²` with injective
derivative:

* the connected components are open, pairwise disjoint, and (by second countability) countably
  many: the `j`-th component is placed in the `j`-th "slot" of the plane;
* the `j`-th non-compact component is placed on the horizontal line `{p | p 1 = j + 1/2}` using a
  parametrisation by `ℝ`, and the `j`-th compact component on the circle of radius `1/4` centred
  at `(j, 0)`;
* the assembled map is a smooth injective immersion with proper slot assignment, hence a closed
  embedding.
-/

open scoped Manifold ContDiff
open Topology Set Function

namespace Work.OneDim

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The hypothesis of the theorem: every nonempty preconnected open set of `M` is diffeomorphic
either to `ℝ` or to the unit circle. -/
abbrev AsmHyp (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M] : Prop :=
  ∀ (C : TopologicalSpace.Opens M), (C : Set M).Nonempty → IsPreconnected (C : Set M) →
    (Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ C ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
      Nonempty (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle C ((⊤ : ℕ∞) : WithTop ℕ∞)))

/-- The connected component of `x`, as an open subset of `M`. -/
def compOpen (x : M) : TopologicalSpace.Opens M :=
  ⟨connectedComponent x, by
    haveI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) M
    exact isOpen_connectedComponent⟩

theorem mem_compOpen_self (x : M) : x ∈ compOpen x := mem_connectedComponent

theorem isPreconnected_compOpen (x : M) : IsPreconnected (compOpen x : Set M) :=
  isPreconnected_connectedComponent

theorem compOpen_nonempty (x : M) : (compOpen x : Set M).Nonempty :=
  ⟨x, mem_compOpen_self x⟩

theorem isOpen_connectedComponent' (x : M) : IsOpen (connectedComponent x) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) M
  exact isOpen_connectedComponent

theorem denseRange_exists_mem_open {p : ℕ → M} (hp : DenseRange p) {U : Set M}
    (hU : IsOpen U) (hne : U.Nonempty) : ∃ n, p n ∈ U :=
  hp.exists_mem_open hU hne

/-- Auxiliary: `Nat.find` depends only on the predicate. -/
theorem Nat.find_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ∃ n, p n) (hq : ∃ n, q n)
    (h : ∀ n, p n ↔ q n) : Nat.find hp = Nat.find hq := by
  refine le_antisymm (Nat.find_min' hp ((h _).mpr (Nat.find_spec hq)))
    (Nat.find_min' hq ((h _).mp (Nat.find_spec hp)))

/-- The canonical index of the connected component of `x`: the least `n` with `p n` in it. -/
def slot (p : ℕ → M) (hp : DenseRange p) (x : M) : ℕ :=
  @Nat.find (fun n => p n ∈ connectedComponent x)
    (Classical.decPred (fun n => p n ∈ connectedComponent x))
    (denseRange_exists_mem_open hp (isOpen_connectedComponent' x) (compOpen_nonempty x))

theorem slot_spec (p : ℕ → M) (hp : DenseRange p) (x : M) :
    p (slot p hp x) ∈ connectedComponent x := by
  rw [slot]
  exact @Nat.find_spec (fun n => p n ∈ connectedComponent x)
    (Classical.decPred (fun n => p n ∈ connectedComponent x)) _

theorem slot_congr (p : ℕ → M) (hp : DenseRange p) {x y : M}
    (hxy : connectedComponent x = connectedComponent y) : slot p hp x = slot p hp y := by
  classical
  rw [slot, slot]
  refine Nat.find_congr' _ _ fun n => ?_
  rw [hxy]

theorem slot_eq_of_mem (p : ℕ → M) (hp : DenseRange p) {j : ℕ} {y : M}
    (hy : y ∈ compOpen (p j)) : slot p hp y = slot p hp (p j) :=
  slot_congr p hp (connectedComponent_eq (x := p j) (y := y) hy).symm

theorem slot_mem (p : ℕ → M) (hp : DenseRange p) (x : M) : x ∈ compOpen (p (slot p hp x)) := by
  have h := slot_spec p hp x
  have hc : connectedComponent x = connectedComponent (p (slot p hp x)) :=
    connectedComponent_eq h
  change x ∈ connectedComponent (p (slot p hp x))
  rw [← hc]
  exact mem_connectedComponent

theorem slot_idem (p : ℕ → M) (hp : DenseRange p) (x : M) :
    slot p hp (p (slot p hp x)) = slot p hp x := by
  refine slot_congr p hp ?_
  exact (connectedComponent_eq (slot_spec p hp x)).symm

/-- The canonical index of the component of `p j`. -/
def cIdx (p : ℕ → M) (hp : DenseRange p) (j : ℕ) : ℕ := slot p hp (p j)

theorem cIdx_idem (p : ℕ → M) (hp : DenseRange p) (j : ℕ) :
    cIdx p hp (cIdx p hp j) = cIdx p hp j := slot_idem p hp (p j)

theorem cIdx_mem (p : ℕ → M) (hp : DenseRange p) (j : ℕ) : p j ∈ compOpen (p (cIdx p hp j)) := by
  have h := slot_spec p hp (p j)
  have hc : connectedComponent (p (slot p hp (p j))) = connectedComponent (p j) :=
    (connectedComponent_eq h).symm
  change p j ∈ connectedComponent (p (slot p hp (p j)))
  rw [hc]
  exact mem_connectedComponent

theorem slot_eq_cIdx (p : ℕ → M) (hp : DenseRange p) {j : ℕ} {y : M}
    (hy : y ∈ compOpen (p (cIdx p hp j))) : slot p hp y = cIdx p hp j := by
  have h1 : slot p hp y = slot p hp (p (cIdx p hp j)) := slot_eq_of_mem p hp hy
  rw [h1]
  show cIdx p hp (cIdx p hp j) = cIdx p hp j
  exact cIdx_idem p hp j

/-- The model data of the connected component of `y`: a diffeomorphism from `ℝ` or from the
unit circle onto the component. -/
def compData (h : AsmHyp M) (y : M) : PlanarPlaceData (compOpen y) := by
  classical
  exact if h1 : Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ (compOpen y)
      ((⊤ : ℕ∞) : WithTop ℕ∞)) then Sum.inl (Classical.choice h1)
    else Sum.inr (Classical.choice ((Or.resolve_left
      (h (compOpen y) (compOpen_nonempty y) (isPreconnected_compOpen y)) h1)))

/-- The assembled map. -/
def assemble (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) (x : M) :
    EuclideanSpace ℝ (Fin 2) :=
  planarPlace (slot p hp x) (compData h (p (slot p hp x))) ⟨x, slot_mem p hp x⟩

theorem assemble_apply_of_slot_eq (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p)
    {x : M} {j : ℕ} (hj : slot p hp x = j) (hmem : x ∈ compOpen (p j)) :
    assemble h p hp x = planarPlace j (compData h (p j)) ⟨x, hmem⟩ := by
  subst hj
  rw [assemble]

/-- On the `j`-th canonical component, the assembled map agrees with the model placement. -/
theorem assemble_eq_place (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) (j : ℕ)
    (y : compOpen (p (cIdx p hp j))) :
    assemble h p hp (y : M)
      = planarPlace (cIdx p hp j) (compData h (p (cIdx p hp j))) y := by
  have hj : slot p hp (y : M) = cIdx p hp j := slot_eq_cIdx p hp y.2
  rw [assemble_apply_of_slot_eq h p hp hj y.2]

/-- The canonical components cover `M`. -/
theorem iUnion_cIdx_compOpen (p : ℕ → M) (hp : DenseRange p) :
    (⋃ j, (compOpen (p (cIdx p hp j)) : Set M)) = univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine Set.mem_iUnion.mpr ⟨slot p hp x, ?_⟩
    have h1 : cIdx p hp (slot p hp x) = slot p hp x := slot_idem p hp x
    rw [h1]
    exact slot_mem p hp x

/-- The assembled map is `C^∞`: it agrees with a smooth model placement on each canonical
component. -/
theorem contMDiff_assemble (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (assemble h p hp) := by
  refine contMDiff_of_contMDiffOn_iUnion_of_isOpen
    (s := fun j : ℕ => (compOpen (p (cIdx p hp j)) : Set M)) ?_ ?_ ?_
  · intro j
    have hpiece : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : compOpen (p (cIdx p hp j)) =>
          planarPlace (cIdx p hp j) (compData h (p (cIdx p hp j))) y) :=
      planarPlace_contMDiff (cIdx p hp j) (compData h (p (cIdx p hp j)))
    have hsub : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : compOpen (p (cIdx p hp j)) => assemble h p hp (y : M)) :=
      hpiece.congr (fun y => assemble_eq_place h p hp j y)
    intro x hx
    exact (contMDiffAt_subtype_iff.mp (hsub ⟨x, hx⟩)).contMDiffWithinAt
  · intro j
    exact (compOpen (p (cIdx p hp j))).2
  · exact iUnion_cIdx_compOpen p hp

/-- **The derivative of the inclusion of an open subset is the identity.**  The written function
in charts is the identity: the chart of the open subset at `y` is the restriction of the ambient
chart at `y`, so composing with the inverse chart gives the identity. -/
theorem mfderiv_subtypeVal_eq_one {U : TopologicalSpace.Opens M} (y : U) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) (Subtype.val : U → M) y
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 1)) := by
  have hwritten : writtenInExtChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) y (Subtype.val : U → M)
      =ᶠ[𝓝 ((extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) y) y)] id := by
    have htarget : (chartAt (EuclideanSpace ℝ (Fin 1)) y) y
        ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) y).target :=
      (chartAt (EuclideanSpace ℝ (Fin 1)) y).map_source
        (mem_chart_source (EuclideanSpace ℝ (Fin 1)) y)
    filter_upwards [IsOpen.mem_nhds (chartAt (EuclideanSpace ℝ (Fin 1)) y).open_target htarget]
      with u hu
    simp only [writtenInExtChartAt, Function.comp_apply, id_eq, extChartAt_coe,
      extChartAt_coe_symm, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm]
    have hval : (Subtype.val ((chartAt (EuclideanSpace ℝ (Fin 1)) y).symm u) : M)
        = (chartAt (EuclideanSpace ℝ (Fin 1)) (y : M)).symm u := by
      have h1 := OpenPartialHomeomorph.subtypeRestr_symm_apply
        (e := chartAt (EuclideanSpace ℝ (Fin 1)) (y : M)) (U := U) ⟨y⟩
        (show u ∈ (((chartAt (EuclideanSpace ℝ (Fin 1)) (y : M))).subtypeRestr ⟨y⟩).target
          from hu)
      simpa only [TopologicalSpace.Opens.chartAt_eq, Function.comp_apply] using h1
    rw [hval]
    exact (chartAt (EuclideanSpace ℝ (Fin 1)) (y : M)).right_inv
      (OpenPartialHomeomorph.subtypeRestr_target_subset
        (e := chartAt (EuclideanSpace ℝ (Fin 1)) (y : M)) ⟨y⟩ hu)
  have hrange : range (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) = univ := by
    ext x
    simp
  have hwritten' : writtenInExtChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) y (Subtype.val : U → M)
      =ᶠ[𝓝[univ] ((extChartAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) y) y)] id := by
    rw [nhdsWithin_univ]
    exact hwritten
  refine HasMFDerivAt.mfderiv ⟨continuous_subtype_val.continuousAt, ?_⟩
  rw [hrange]
  exact (Filter.EventuallyEq.hasFDerivWithinAt_iff hwritten' hwritten.self_of_nhds).mpr
    (hasFDerivWithinAt_id _ _)

/-- The derivative of the inclusion of an open subset is injective. -/
theorem mfderiv_subtypeVal_injective {U : TopologicalSpace.Opens M} (y : U) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) (Subtype.val : U → M) y) := by
  rw [mfderiv_subtypeVal_eq_one y]
  exact fun a b hab => hab

/-- **Injectivity of the assembled map.** The slot index of a point is determined by the image:
the second coordinate is `j + 1/2 ≥ 1/2` on a line slot and has absolute value `≤ 1/4` on a
circle slot, while two distinct circle slots are centred more than `1/2` apart. -/
theorem injective_assemble (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) :
    Function.Injective (assemble h p hp) := by
  intro x y hxy
  have hjeq : planarPlace (slot p hp x) (compData h (p (slot p hp x))) ⟨x, slot_mem p hp x⟩
      = planarPlace (slot p hp y) (compData h (p (slot p hp y))) ⟨y, slot_mem p hp y⟩ := by
    rw [← assemble_apply_of_slot_eq h p hp rfl (slot_mem p hp x),
      ← assemble_apply_of_slot_eq h p hp rfl (slot_mem p hp y)]
    exact hxy
  have hj : slot p hp x = slot p hp y :=
    planarPlace_slot_eq (slot p hp x) (slot p hp y) (compData h (p (slot p hp x)))
      (compData h (p (slot p hp y))) ⟨x, slot_mem p hp x⟩ ⟨y, slot_mem p hp y⟩ hjeq
  have hxW : x ∈ compOpen (p (cIdx p hp (slot p hp x))) := by
    rw [cIdx, slot_idem p hp x]
    exact slot_mem p hp x
  have hyW : y ∈ compOpen (p (cIdx p hp (slot p hp x))) := by
    have h1 : cIdx p hp (slot p hp x) = slot p hp y := by
      rw [cIdx, slot_idem p hp x]
      exact hj
    rw [h1]
    exact slot_mem p hp y
  have hinjW : Function.Injective (fun z : compOpen (p (cIdx p hp (slot p hp x))) =>
      assemble h p hp (z : M)) := by
    intro a b hab
    dsimp only at hab
    rw [assemble_eq_place h p hp (slot p hp x) a,
      assemble_eq_place h p hp (slot p hp x) b] at hab
    exact planarPlace_injective (cIdx p hp (slot p hp x))
      (compData h (p (cIdx p hp (slot p hp x)))) hab
  have hfin : (⟨x, hxW⟩ : compOpen (p (cIdx p hp (slot p hp x)))) = ⟨y, hyW⟩ :=
    hinjW (by simpa using hxy)
  exact Subtype.ext_iff.mp hfin

/-- The `j`-th slot piece of the preimage of a set. -/
def slotPiece (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (j : ℕ) : Set M :=
  Subtype.val '' {y : compOpen (p (cIdx p hp j)) | assemble h p hp (y : M) ∈ K}

theorem isCompact_slotPiece (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (j : ℕ) :
    IsCompact (slotPiece h p hp K j) := by
  have hT : IsCompact ({y : compOpen (p (cIdx p hp j)) | assemble h p hp (y : M) ∈ K}) := by
    have hpre : {y : compOpen (p (cIdx p hp j)) | assemble h p hp (y : M) ∈ K}
        = (planarPlace (cIdx p hp j) (compData h (p (cIdx p hp j)))) ⁻¹' K := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact iff_of_eq (congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z ∈ K)
        (assemble_eq_place h p hp j y))
    rw [hpre]
    exact (planarPlace_isProperMap (cIdx p hp j)
      (compData h (p (cIdx p hp j)))).isCompact_preimage hK
  exact hT.image continuous_subtype_val

/-- **The assembled map is proper.** The preimage of a compact set is a finite union of compact
slot pieces: a point of the preimage of a ball of radius `R` has slot index at most `R + 1/2`. -/
theorem isProperMap_assemble (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) :
    IsProperMap (assemble h p hp) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(contMDiff_assemble h p hp).continuous, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set N := Nat.ceil (R + 1 / 2) with hN
  have hcover : assemble h p hp ⁻¹' K = ⋃ k : Fin (N + 1), slotPiece h p hp K k.val := by
    ext x
    constructor
    · intro hx
      have hb : (slot p hp x : ℝ) ≤ R + 1 / 2 := by
        have h1 : (slot p hp x : ℝ) ≤ ‖assemble h p hp x‖ + 1 / 2 := by
          simpa [assemble] using natCast_le_norm_planarPlace (slot p hp x)
            (compData h (p (slot p hp x))) ⟨x, slot_mem p hp x⟩
        have h2 : ‖assemble h p hp x‖ ≤ R := hR _ hx
        linarith
      have hNx : slot p hp x ≤ N := by
        rw [hN]
        exact_mod_cast hb.trans (Nat.le_ceil (R + 1 / 2))
      refine Set.mem_iUnion.mpr ⟨⟨slot p hp x, Nat.lt_succ_of_le hNx⟩, ?_⟩
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      have h1 : cIdx p hp (slot p hp x) = slot p hp x := slot_idem p hp x
      rw [h1]
      exact slot_mem p hp x
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, rfl⟩ := hk
      exact hy
  rw [hcover]
  exact isCompact_iUnion fun k => isCompact_slotPiece h p hp hK k.val

/-- **The assembled map is an immersion.** On the canonical component of `x` it agrees with the
model placement (whose derivative is injective), and the inclusion of that open component has
derivative the identity map. -/
theorem mfderiv_assemble_injective (h : AsmHyp M) (p : ℕ → M) (hp : DenseRange p) (x : M) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (assemble h p hp) x) := by
  set j := slot p hp x with hj
  have hxe : x ∈ compOpen (p (cIdx p hp j)) := by
    rw [hj]
    have h1 : cIdx p hp (slot p hp x) = slot p hp x := slot_idem p hp x
    rw [h1]
    exact slot_mem p hp x
  have hinj_local : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (fun y : compOpen (p (cIdx p hp j)) => assemble h p hp (y : M)) ⟨x, hxe⟩) := by
    rw [mfderiv_congr (show (fun y : compOpen (p (cIdx p hp j)) => assemble h p hp (y : M))
      = (planarPlace (cIdx p hp j) (compData h (p (cIdx p hp j))))
      from funext fun y => assemble_eq_place h p hp j y)]
    exact planarPlace_mfderiv_injective (cIdx p hp j)
      (compData h (p (cIdx p hp j))) ⟨x, hxe⟩
  have hgMD : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (assemble h p hp) x :=
    (contMDiff_assemble h p hp).mdifferentiableAt (by simp)
  have hfMD : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (Subtype.val : compOpen (p (cIdx p hp j)) → M)
      (⟨x, hxe⟩ : compOpen (p (cIdx p hp j))) :=
    (contMDiff_subtype_val (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mdifferentiableAt (by simp)
  have hchain2 := mfderiv_comp (f := (Subtype.val : compOpen (p (cIdx p hp j)) → M))
    (g := assemble h p hp) ⟨x, hxe⟩ hgMD hfMD
  have hAB : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (assemble h p hp) x
      ∘L mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (Subtype.val : compOpen (p (cIdx p hp j)) → M) ⟨x, hxe⟩) := by
    rw [← hchain2]
    exact hinj_local
  have hBsurj : Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (Subtype.val : compOpen (p (cIdx p hp j)) → M) ⟨x, hxe⟩) := by
    rw [mfderiv_subtypeVal_eq_one ⟨x, hxe⟩]
    exact fun y => ⟨y, rfl⟩
  intro a b hab
  obtain ⟨a', rfl⟩ := hBsurj a
  obtain ⟨b', rfl⟩ := hBsurj b
  have h1 : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (assemble h p hp) x
      ∘L mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (Subtype.val : compOpen (p (cIdx p hp j)) → M) ⟨x, hxe⟩) a'
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (assemble h p hp) x
        ∘L mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (Subtype.val : compOpen (p (cIdx p hp j)) → M) ⟨x, hxe⟩) b' := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact hab
  exact congrArg (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    (Subtype.val : compOpen (p (cIdx p hp j)) → M) ⟨x, hxe⟩) (hAB h1)

end

/-- **Assembly of the planar embedding from the per-component classification.**

Given the classification of connected smooth 1-manifolds (each connected component is
diffeomorphic to `ℝ` or to `Circle`), every Hausdorff second countable smooth 1-manifold admits a
smooth embedding into `ℝ²` with injective derivative.

The proof is a disjoint-union assembly: the (countably many, pairwise disjoint, open) connected
components are embedded separately; the `k`-th non-compact component is placed on the line
`{p | p 1 = k + 1/2}` with a proper parametrisation, and the `k`-th compact component on a small
circle of radius `1/4` centred at `(k, 0)`.  The assembled map is injective, immersive and proper
(the slots escape to infinity), hence a closed embedding. -/
theorem assembly_of_components {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (h : ∀ (C : TopologicalSpace.Opens M), (C : Set M).Nonempty → IsPreconnected (C : Set M) →
      (Nonempty (Diffeomorph (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ℝ C ((⊤ : ℕ∞) : WithTop ℕ∞)) ∨
        Nonempty (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle C
          ((⊤ : ℕ∞) : WithTop ℕ∞)))) :
    ∃ e : M → EuclideanSpace ℝ (Fin 2),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) e ∧
      Topology.IsEmbedding e ∧
      ∀ x : M, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) e x) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    haveI : Subsingleton M := ⟨ fun a _ => isEmptyElim a⟩
    refine ⟨fun x => isEmptyElim x, ?_, ?_, ?_⟩
    · exact fun x => isEmptyElim x
    · exact IsEmbedding.of_subsingleton _
    · exact fun x => isEmptyElim x
  · haveI : Nonempty M := hM
    exact ⟨assemble h (TopologicalSpace.denseSeq M) (TopologicalSpace.denseRange_denseSeq M),
      contMDiff_assemble h _ _,
      Work.Embedding.isEmbedding_of_isProperMap_injective
        (isProperMap_assemble h _ _) (injective_assemble h _ _),
      mfderiv_assemble_injective h _ _⟩

end Work.OneDim
