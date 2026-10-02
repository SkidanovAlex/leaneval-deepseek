import Mathlib
import Submission.Work.Thom.Glue
import Submission.Work.Thom.EucCube
import Submission.Work.Cohomology.subsingleton_relCohomology_of_open_subset
import Submission.Work.Thom.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The vanishing of the relative cohomology of a bundle piece, from the Euclidean model

Let `Z` be a real bundle of rank `n` over a base `B`, presented by gluing data
(`Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι`), and let `W ⊆ Z.baseSet i` be a
set contained in a single chart `i`.  Then the relative cohomology of the piece of the Thom pair
over `W`,
`Work.Thom.PieceCoh Z W m = H^m(X|_W, X|_W ∖ 0)`, vanishes below the rank:

`Work.Thom.subsingleton_PieceCoh_of_euclidean` deduces this from the Euclidean model
`H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for `m < n`, which is the hypothesis `hEuc`.

The mathematical content is that on the chart `i` the bundle is trivial: the local trivialisation
`Z.localTriv i`, restricted to the piece over `W`, is a homeomorphism of pairs
`(X|_W, X|_W∖0) ≅ (W × ℝⁿ, W × (ℝⁿ∖0))`
(`Work.Thom.pieceChartHomeo`), and relative cohomology is invariant under a homeomorphism of pairs
(`Work.Cohomology.relCohomology_homeomorph_pairs`).  Note that the model space of the hypothesis is
`Fin n → ℝ` (with the product topology), so the fibre `EuclideanSpace ℝ (Fin n)= PiLp 2 (Fin n → ℝ)`
is transported by `PiLp.homeomorph`.
-/

open Work.TangentClasses

namespace Work.Thom

open Bundle

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- The transition function of `Z` from the preferred chart at `x` to a chart `i` containing `x`
is injective: a fibre coordinate vanishes in the chart `i` exactly when it vanishes in the
preferred chart at the base point. -/
theorem coordChange_indexAt_eq_zero_iff' (Z : RealBundle B F ι) (i : ι)
    (x : B) (hx : x ∈ Z.baseSet i) (v : F) :
    Z.coordChange (Z.indexAt x) i x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : Z.coordChange (Z.indexAt x) (Z.indexAt x) x v = v :=
      Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) v
    have h2 := Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x
      ⟨⟨Z.mem_baseSet_at x, hx⟩, Z.mem_baseSet_at x⟩ v
    rw [h1] at h2
    rw [h, map_zero] at h2
    exact h2.symm
  · intro h; rw [h, map_zero]

/-- **The chart homeomorphism of the piece over `W ⊆ Z.baseSet i`**, together with the
zero-complement condition: for a set `W` contained in the chart `i`, the local trivialisation
`Z.localTriv i` restricted to `W` is a homeomorphism
`↥(Z.proj ⁻¹' W) ≃ₜ (↥W × F)`, and it carries the complement of the zero section onto the
punctured product `{q | q.2 ≠ 0}`. -/
noncomputable def pieceChartHomeo (Z : RealBundle B F ι) (i : ι) {W : Set B}
    (hW : W ⊆ Z.baseSet i) :
    { e : ↥(Z.proj ⁻¹' W) ≃ₜ (↥W × F) //
      ∀ z : ↥(Z.proj ⁻¹' W), ((z : Z.TotalSpace) ∈ zeroComplement Z ↔ (e z).2 ≠ 0) } := by
  classical
  -- the auxiliary nonemptiness needed by `Trivialization.restrictPreimage'` (it is used only for
  -- the junk value of the inverse; `⟨x, 0⟩` always lies over `x`).
  haveI hne : Nonempty (↥W → F → ↥(Z.proj ⁻¹' W)) :=
    ⟨fun x _ => ⟨(⟨x.1, 0⟩ : Z.TotalSpace),
      show Z.proj (⟨x.1, 0⟩ : Z.TotalSpace) ∈ W from x.2⟩⟩
  have hbase : ((Z.localTriv i).restrictPreimage' W).baseSet = Set.univ := by
    rw [Trivialization.restrictPreimage'_baseSet]
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact hW x.2
  have hsrc : ((Z.localTriv i).restrictPreimage' W).source = Set.univ := by
    rw [Trivialization.source_eq, hbase, Set.preimage_univ]
  have htgt : ((Z.localTriv i).restrictPreimage' W).target = Set.univ := by
    rw [Trivialization.target_eq, hbase, Set.univ_prod_univ]
  refine ⟨((Z.localTriv i).restrictPreimage' W).toOpenPartialHomeomorph
    |>.toHomeomorphOfSourceEqUnivTargetEqUniv hsrc htgt, ?_⟩
  intro z
  have hz2 : (((Z.localTriv i).restrictPreimage' W).toOpenPartialHomeomorph
      |>.toHomeomorphOfSourceEqUnivTargetEqUniv hsrc htgt z).2
      = ((Z.localTriv i) (z : Z.TotalSpace)).2 := by
    rw [OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_apply,
      Trivialization.coe_coe]
    exact congrArg Prod.snd (Trivialization.restrictPreimage'_apply (Z.localTriv i) W z)
  rw [hz2, VectorBundleCore.localTriv_apply, mem_zeroComplement]
  show ((show F from (z : Z.TotalSpace).2) ≠ 0) ↔
    (Z.coordChange (Z.indexAt (z : Z.TotalSpace).1) i (z : Z.TotalSpace).1
      ((show F from (z : Z.TotalSpace).2))) ≠ 0
  exact (coordChange_indexAt_eq_zero_iff' Z i (z : Z.TotalSpace).1 (hW z.2)
    ((show F from (z : Z.TotalSpace).2))).not.symm

/-- **Vanishing of the relative cohomology of a bundle piece below the rank, from the Euclidean
model.**  If `H^m(W × ℝⁿ, W × (ℝⁿ∖0)) = 0` for every space `W` and every `m < n` (`hEuc`), then
for every real bundle `Z` of rank `n` and every `W` contained in a single chart of `Z`, the
relative cohomology `Work.Thom.PieceCoh Z W m` vanishes for `m < n`. -/
theorem subsingleton_PieceCoh_of_euclidean
    (hEuc : ∀ (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ), m < n →
      Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × (Fin n → ℝ)))
        {p : W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0}).homology m))
    {B : Type} [TopologicalSpace B] (n : ℕ) (ι : Type) [Inhabited ι]
    (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin n)) ι) (i : ι)
    {W : Set B} (hW : W ⊆ Z.baseSet i) {m : ℕ} (hm : m < n) :
    Subsingleton (Work.Thom.PieceCoh Z W m) := by
  -- the pair homeomorphism `(X|_W, X|_W∖0) ≅ (↥W × ℝⁿ, ↥W × (ℝⁿ∖0))`
  obtain ⟨hW1, hW2⟩ := pieceChartHomeo Z i hW
  let e2 : ↥W × EuclideanSpace ℝ (Fin n) ≃ₜ ↥W × (Fin n → ℝ) :=
    Homeomorph.prodCongr (Homeomorph.refl ↥W) (PiLp.homeomorph 2 (fun _ : Fin n => ℝ))
  let e : ↥(Z.proj ⁻¹' W) ≃ₜ ↥W × (Fin n → ℝ) := hW1.trans e2
  have hiff : ∀ z : ↥(Z.proj ⁻¹' W),
      z ∈ {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z} ↔
        e z ∈ {p : ↥W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0} := by
    intro z
    simp only [Set.mem_ofPred_eq]
    rw [hW2 z]
    have hthis : (e z).2 = (hW1 z).2.ofLp := rfl
    rw [hthis]
    exact (WithLp.ofLp_eq_zero (p := 2) (V := Fin n → ℝ)).symm.not
  -- relative cohomology is invariant under the homeomorphism of pairs
  obtain ⟨iso⟩ := Work.Cohomology.relCohomology_homeomorph_pairs
    {y : ↥(Z.proj ⁻¹' W) | (y : Z.TotalSpace) ∈ zeroComplement Z}
    {p : ↥W × (Fin n → ℝ) | (p.2 : Fin n → ℝ) ≠ 0} e hiff m
  exact Work.Cohomology.subsingleton_of_iso iso.symm (hEuc n ↥W m hm)

end

end Work.Thom
