import Mathlib
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# The "closed ball bundle" of a real bundle over a compact base is compact

Let `Z` be a real vector bundle (in the gluing-data model `Work.TangentClasses.RealBundle`, i.e.
Mathlib's `VectorBundleCore ℝ B F ι`) over a compact Hausdorff base `B`, with model fibre `F` a
finite-dimensional real normed space.  The total space is `Z.TotalSpace = Σ x, Z.Fiber x` with
`Z.Fiber x = F` definitionally, and the *fibrewise norm* is `Work.Thom.fibreNorm Z ⟨x,v⟩ = ‖v‖`.

**Main result.** If the fibrewise norm is continuous (`hcont`), then for every `M : ℝ` the set

`{p : Z.TotalSpace | fibreNorm Z p ≤ M}`

— the "closed ball bundle of radius `M`" — is compact.  This is the compactness input for the
one-point compactification / Thom space of `Z` (`Submission/Work/ThomBordism/CanonThomAux.lean`),
where it is used in the form `hM : ∀ M, IsCompact {p | fibreNorm Z p ≤ M}`.

## Proof

Cover `B` by finitely many trivialisations `Z.baseSet i` (`i ∈ s`) and shrink, using normality of the
compact Hausdorff base (`exists_subset_iUnion_closed_subset`), to a finite cover by **closed** sets
`v i ⊆ Z.baseSet i`.  Then

`{fibreNorm ≤ M} = ⋃ i, Φ i '' {z : ↥(v i) × F | fibreNorm Z (Φ i z) ≤ M}`,

where `Φ i (x, w) = ⟨x, (Z.localTriv i).symm x w⟩` is the inverse trivialisation, which is continuous
by `Bundle.Trivialization.continuousOn_symm`.  Each piece is a closed subset of the compact set
`↥(v i) × closedBall 0 (M / c i)`:

* closedness is `hcont` (the fibrewise norm composed with the continuous `Φ i`);
* boundedness is the only substance.  Writing a fibre vector as `w = ‖w‖ • u` with `‖u‖ = 1`,
  homogeneity of `Φ i` (`fibreNorm_trivPoint_smul`) reduces the bound to a *positive* lower bound `c`
  for `fibreNorm` on the compact set `↥(v i) × sphere 0 1`.  Such a `c` exists because the function
  is continuous and does not vanish there: `u ≠ 0` and the coordinate change
  `Z.localTriv i`'s fibre coordinate is injective (`fibCoord_ne_zero`).
-/

namespace Work.ThomBordism

open Work.TangentClasses

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {ι : Type}

/-! ## The inverse trivialisation as a map `↥v × F → Z.TotalSpace` -/

/-- The inverse trivialisation `Z.localTriv i`, as a point of the total space:
`(x, w) ↦ ⟨x, (Z.localTriv i).symm x w⟩`. -/
private def trivPoint (Z : RealBundle B F ι) (i : ι) (x : B) (w : F) : Z.TotalSpace :=
  ⟨x, (Z.localTriv i).symm x w⟩

/-- The fibre coordinate of `Z.localTriv i` at `x`, in the *model* fibre `F` (the fibre
`Z.Fiber x` is only reducibly equal to `F`, which type class search does not unfold, so it is useful
to have this `F`-valued version). -/
private def fibCoord (Z : RealBundle B F ι) (i : ι) (x : B) (w : F) : F :=
  (Z.coordChange i (Z.indexAt x) x) w

/-- The fibrewise norm of the inverse trivialisation, read with the `Z.Fiber x → F` coercion. -/
private theorem fibreNorm_trivPoint_coe (Z : RealBundle B F ι) (i : ι) (x : B) (w : F) :
    Work.Thom.fibreNorm Z (trivPoint Z i x w) =
      ‖(show F from (Z.localTriv i).symm x w)‖ := rfl

/-- The fibrewise norm of the inverse trivialisation, in the `F`-valued coordinate `fibCoord`. -/
private theorem fibreNorm_trivPoint (Z : RealBundle B F ι) (i : ι) (x : B) (w : F)
    (hx : x ∈ Z.baseSet i) :
    Work.Thom.fibreNorm Z (trivPoint Z i x w) = ‖fibCoord Z i x w‖ := by
  rw [fibreNorm_trivPoint_coe, fibCoord]
  rw [VectorBundleCore.localTriv_symm_apply Z i hx]

/-- The inverse trivialisation is continuous, in the form needed here: as a map `↥v × F → Z`. -/
private theorem continuous_trivPoint (Z : RealBundle B F ι) {i : ι} {v : Set B}
    (hv : v ⊆ Z.baseSet i) : Continuous (fun z : (↥v) × F => trivPoint Z i (z.1 : B) z.2) := by
  have hc1 : Continuous (fun z : (↥v) × F => (z.1 : B)) :=
    continuous_subtype_val.comp continuous_fst
  have hc2 : Continuous (fun z : (↥v) × F => z.2) := continuous_snd
  have h := (Z.localTriv i).continuousOn_symm.comp_continuous (hc1.prodMk hc2)
    (fun z : (↥v) × F => ⟨hv z.1.2, Set.mem_univ _⟩)
  simpa only [Function.comp_def, trivPoint] using h

/-- The coordinate change of a bundle is injective on the overlap of two charts: it is inverse to
the coordinate change in the other direction (the cocycle, `VectorBundleCore.coordChange_comp`). -/
private theorem coordChange_injective (Z : RealBundle B F ι) {i j : ι} {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) : Function.Injective (Z.coordChange i j x) := by
  intro a b hab
  have h1 := Z.coordChange_comp i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩ a
  have h2 := Z.coordChange_comp i j i x ⟨⟨hx.1, hx.2⟩, hx.1⟩ b
  rw [Z.coordChange_self i x hx.1] at h1 h2
  rw [hab] at h1
  exact h1.symm.trans h2

/-- The inverse trivialisation does not vanish on a nonzero vector. -/
private theorem fibCoord_ne_zero (Z : RealBundle B F ι) (i : ι) {x : B} (hx : x ∈ Z.baseSet i)
    {w : F} (hw : w ≠ 0) : fibCoord Z i x w ≠ 0 := by
  intro h
  have h' : (Z.coordChange i (Z.indexAt x) x) w = 0 := by simpa only [fibCoord] using h
  exact hw (coordChange_injective Z ⟨hx, Z.mem_baseSet_at x⟩ (by rw [h', map_zero]))

/-- Homogeneity of the fibre coordinate. -/
private theorem fibCoord_smul (Z : RealBundle B F ι) (i : ι) (x : B) (c : ℝ) (w : F) :
    fibCoord Z i x (c • w) = c • fibCoord Z i x w := map_smul _ c w

/-- Homogeneity of the fibrewise norm in the inverse trivialisation. -/
private theorem fibreNorm_trivPoint_smul (Z : RealBundle B F ι) (i : ι) (x : B)
    (hx : x ∈ Z.baseSet i) (c : ℝ) (w : F) :
    Work.Thom.fibreNorm Z (trivPoint Z i x (c • w)) =
      |c| * Work.Thom.fibreNorm Z (trivPoint Z i x w) := by
  rw [fibreNorm_trivPoint Z i x (c • w) hx, fibreNorm_trivPoint Z i x w hx, fibCoord_smul,
    norm_smul, Real.norm_eq_abs]

/-! ## Boundedness over a chart -/

/-- **The essential estimate.**  If a positive `c` bounds the fibrewise norm from below on the unit
sphere of the chart `i` over `v`, then the fibre coordinates of the ball of radius `M` over `v` are
bounded by `max (M / c) 0`. -/
private theorem norm_le_radius_of_bound (Z : RealBundle B F ι) {i : ι} {v : Set B}
    (hv : v ⊆ Z.baseSet i) {c : ℝ} (hc : 0 < c)
    (hb : ∀ z : (↥v) × F, ‖z.2‖ = 1 →
      c ≤ Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2))
    {M : ℝ} {z : (↥v) × F}
    (hz : Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2) ≤ M) :
    ‖z.2‖ ≤ max (M / c) 0 := by
  by_cases hz0 : z.2 = 0
  · rw [hz0, norm_zero]
    exact le_max_right _ _
  · have hnormpos : 0 < ‖z.2‖ := norm_pos_iff.mpr hz0
    have hsp : ‖(‖z.2‖⁻¹ • z.2 : F)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z.2),
        inv_mul_cancel₀ (ne_of_gt hnormpos)]
    have hcl := hb (⟨z.1, ‖z.2‖⁻¹ • z.2⟩ : (↥v) × F) hsp
    rw [fibreNorm_trivPoint Z i (z.1 : B) (‖z.2‖⁻¹ • z.2) (hv z.1.2), fibCoord_smul, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z.2)] at hcl
    rw [← fibreNorm_trivPoint Z i (z.1 : B) z.2 (hv z.1.2)] at hcl
    have hmul : ‖z.2‖ * c ≤ M := by
      have h2 : ‖z.2‖ * c ≤
          (‖z.2‖⁻¹ * Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2)) * ‖z.2‖ := by
        rw [mul_comm ‖z.2‖ c]
        exact mul_le_mul_of_nonneg_right hcl (norm_nonneg _)
      have h3 : (‖z.2‖⁻¹ * Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2)) * ‖z.2‖
          = Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2) := by
        rw [mul_assoc, mul_comm _ ‖z.2‖, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnormpos),
          one_mul]
      rw [h3] at h2
      linarith
    exact le_trans ((le_div_iff₀ hc).mpr hmul) (le_max_left _ _)

/-! ## The pieces -/

/-- The piece of `{fibreNorm ≤ M}` lying over `v`, read through the trivialisation `i`. -/
private def pieceSet (Z : RealBundle B F ι) (M : ℝ) (v : Set B) (i : ι) : Set Z.TotalSpace :=
  (fun z : (↥v) × F => trivPoint Z i (z.1 : B) z.2) ''
    {z : (↥v) × F | Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2) ≤ M}

/-- Each piece is compact: it is the continuous image of a closed subset of the compact set
`↥v × closedBall 0 (max (M / c) 0)`. -/
private theorem isCompact_pieceSet (Z : RealBundle B F ι) {v : Set B} (hvclosed : IsClosed v)
    {i : ι} (hv : v ⊆ Z.baseSet i) {c : ℝ} (hc : 0 < c)
    (hb : ∀ z : (↥v) × F, ‖z.2‖ = 1 →
      c ≤ Work.Thom.fibreNorm Z (trivPoint Z i (z.1 : B) z.2))
    (hcont : Continuous (Work.Thom.fibreNorm Z)) (M : ℝ) :
    IsCompact (pieceSet Z M v i) := by
  have hvcomp : IsCompact v :=
    IsCompact.of_isClosed_subset isCompact_univ hvclosed (Set.subset_univ _)
  have hcpt : CompactSpace ↥v := isCompact_iff_compactSpace.mp hvcomp
  rw [pieceSet]
  refine IsCompact.image_of_continuousOn ?_ ((continuous_trivPoint Z hv).continuousOn)
  refine IsCompact.of_isClosed_subset
    (s := (Set.univ : Set ↥v) ×ˢ Metric.closedBall (0 : F) (max (M / c) 0)) ?_ ?_ ?_
  · exact isCompact_univ.prod (isCompact_closedBall (0 : F) (max (M / c) 0))
  · exact isClosed_le (hcont.comp (continuous_trivPoint Z hv)) continuous_const
  · intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_radius_of_bound Z hv hc hb hz

/-! ## The theorem -/

theorem isCompact_fibreNorm_le {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (hcont : Continuous (Work.Thom.fibreNorm Z))
    (M : ℝ) : IsCompact {p : Z.TotalSpace | Work.Thom.fibreNorm Z p ≤ M} := by
  classical
  obtain ⟨s, hs⟩ := (isCompact_univ (X := B)).elim_finite_subcover Z.baseSet
    (fun i => Z.isOpen_baseSet i)
    (fun x _ => Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  have huo : ∀ i : {i // i ∈ s}, IsOpen (Z.baseSet i.1) := fun i => Z.isOpen_baseSet i.1
  have hus : (Set.univ : Set B) ⊆ ⋃ i : {i // i ∈ s}, Z.baseSet i.1 := by
    intro x _
    obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, his⟩, hxi⟩
  have huf : ∀ x ∈ (Set.univ : Set B), {i : {i // i ∈ s} | x ∈ Z.baseSet i.1}.Finite :=
    fun x _ => Set.toFinite _
  obtain ⟨v, hvuniv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset (isClosed_univ (X := B)) huo huf hus
  -- a positive lower bound for the fibrewise norm on the unit sphere of each chart
  have hbound : ∀ i : {i // i ∈ s}, ∃ c : ℝ, 0 < c ∧
      ∀ z : (↥(v i)) × F, ‖z.2‖ = 1 →
        c ≤ Work.Thom.fibreNorm Z (trivPoint Z i.1 (z.1 : B) z.2) := by
    intro i
    have hvci : (v i) ⊆ Z.baseSet i.1 := hvsub i
    have hcpt_i : CompactSpace ↥(v i) := isCompact_iff_compactSpace.mp
      (IsCompact.of_isClosed_subset isCompact_univ (hvclosed i) (Set.subset_univ _))
    have hK : IsCompact ((Set.univ : Set ↥(v i)) ×ˢ Metric.sphere (0 : F) 1) :=
      isCompact_univ.prod (isCompact_sphere (0 : F) 1)
    have hcont_i : ContinuousOn (fun z : (↥(v i)) × F =>
        Work.Thom.fibreNorm Z (trivPoint Z i.1 (z.1 : B) z.2))
        ((Set.univ : Set ↥(v i)) ×ˢ Metric.sphere (0 : F) 1) :=
      (hcont.comp (continuous_trivPoint Z hvci)).continuousOn.mono (Set.subset_univ _)
    have hpos : ∀ z ∈ (Set.univ : Set ↥(v i)) ×ˢ Metric.sphere (0 : F) 1,
        0 < Work.Thom.fibreNorm Z (trivPoint Z i.1 (z.1 : B) z.2) := by
      intro z hz
      have hz2 : ‖z.2‖ = 1 := by
        have h := hz.2
        rwa [Metric.mem_sphere, dist_zero_right] at h
      have hz2nz : z.2 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz2
        norm_num at hz2
      rw [fibreNorm_trivPoint Z i.1 (z.1 : B) z.2 (hvci z.1.2)]
      exact norm_pos_iff.mpr (fibCoord_ne_zero Z i.1 (hvci z.1.2) hz2nz)
    obtain ⟨c, hcpos, hcb⟩ := hK.exists_forall_le' hcont_i hpos
    exact ⟨c, hcpos, fun z hz =>
      hcb z ⟨Set.mem_univ _, by rwa [Metric.mem_sphere, dist_zero_right]⟩⟩
  choose c hcpos hcbound using hbound
  have hcover : {p : Z.TotalSpace | Work.Thom.fibreNorm Z p ≤ M} =
      ⋃ i : {i // i ∈ s}, pieceSet Z M (v i) i.1 := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hvuniv (Set.mem_univ p.1))
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [pieceSet]
      refine ⟨(⟨p.1, hi⟩, ((Z.localTriv i.1) p).2), ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        rw [fibreNorm_trivPoint_coe]
        have hsymm : (Z.localTriv i.1).symm p.1 ((Z.localTriv i.1) p).2 = p.2 :=
          (Z.localTriv i.1).symm_proj_apply p (hvsub i hi)
        rw [hsymm]
        exact hp
      · show trivPoint Z i.1 (⟨p.1, hi⟩ : ↥(v i)) ((Z.localTriv i.1) p).2 = p
        rw [trivPoint]
        have hsymm : (Z.localTriv i.1).symm p.1 ((Z.localTriv i.1) p).2 = p.2 :=
          (Z.localTriv i.1).symm_proj_apply p (hvsub i hi)
        rw [hsymm]
    · intro hp
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      rw [pieceSet] at hpi
      obtain ⟨z, hz, hzp⟩ := hpi
      rw [← hzp]
      exact hz
  rw [hcover]
  exact isCompact_iUnion (fun i => isCompact_pieceSet Z (hvclosed i) (hvsub i) (hcpos i)
    (hcbound i) hcont M)

end

end Work.ThomBordism
