import Mathlib
import Submission.Work.Gen.puncturedSlabs
import Submission.Work.Gen.tubeOfHomogeneous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Work.Gen

open Work.TangentClasses Work.Thom
open scoped Topology

noncomputable section

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι]

/-- The chart model of the weighted fibrewise norm `ν` over the chart `Z.baseSet i`: on the
product `Z.baseSet i × F` it is `(x, v) ↦ ν ⟨x, Z.coordChange i (indexAt x) x v⟩`. -/
noncomputable def slabKTubeNu (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι) :
    (Z.baseSet i) × F → ℝ :=
  fun p => slabNu Z φ (((Z.localTriv i).preimageHomeomorph (Z.baseSet_at i).le).symm p).val

theorem slabKTubeNu_apply (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι)
    (b : Z.baseSet i) (v : F) :
    slabKTubeNu Z φ i (b, v) =
      slabNu Z φ (⟨(b : B), Z.coordChange i (Z.indexAt (b : B)) (b : B) v⟩ : Z.TotalSpace) := by
  unfold slabKTubeNu
  rw [Bundle.Trivialization.preimageHomeomorph_symm_apply]
  rfl

theorem slabKTubeNu_continuous (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι)
    (hcont : Continuous (slabNu Z φ)) : Continuous (slabKTubeNu Z φ i) := by
  unfold slabKTubeNu
  exact hcont.comp (continuous_subtype_val.comp
    (Bundle.Trivialization.preimageHomeomorph (Z.localTriv i) (Z.baseSet_at i).le).continuous_symm)

theorem slabKTubeNu_smul (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι)
    (b : Z.baseSet i) (c : ℝ) (v : F) :
    slabKTubeNu Z φ i (b, c • v) = |c| * slabKTubeNu Z φ i (b, v) := by
  rw [slabKTubeNu_apply, slabKTubeNu_apply, map_smul, slabNu_smul]

theorem slabKTubeNu_nonneg (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι)
    (hnn : ∀ i b, 0 ≤ φ i b) (p : (Z.baseSet i) × F) : 0 ≤ slabKTubeNu Z φ i p := by
  obtain ⟨b, v⟩ := p
  rw [slabKTubeNu_apply]
  exact slabNu_nonneg Z φ hnn _

/-- Injectivity of the change-of-chart map, used to read off the vanishing of the fibre
coordinate. -/
theorem coordChange_injective (Z : RealBundle B F ι) (i : ι) (b : B) (hb : b ∈ Z.baseSet i) :
    Function.Injective (Z.coordChange i (Z.indexAt b) b) := by
  intro u w h
  have hx : b ∈ Z.baseSet i ∩ Z.baseSet (Z.indexAt b) ∩ Z.baseSet i :=
    ⟨⟨hb, Z.mem_baseSet_at b⟩, hb⟩
  have eu : Z.coordChange (Z.indexAt b) i b (Z.coordChange i (Z.indexAt b) b u) = u := by
    rw [Z.coordChange_comp i (Z.indexAt b) i b hx u, Z.coordChange_self i b hb u]
  have ew : Z.coordChange (Z.indexAt b) i b (Z.coordChange i (Z.indexAt b) b w) = w := by
    rw [Z.coordChange_comp i (Z.indexAt b) i b hx w, Z.coordChange_self i b hb w]
  rw [← eu, ← ew, h]

theorem slabKTubeNu_eq_zero (Z : RealBundle B F ι) (φ : ι → C(B, ℝ)) (i : ι)
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (hnn : ∀ i b, 0 ≤ φ i b)
    (hpos : ∀ b, 0 < ∑ i, φ i b) (b : Z.baseSet i) (v : F)
    (h : slabKTubeNu Z φ i (b, v) = 0) : v = 0 := by
  rw [slabKTubeNu_apply] at h
  have h1 : ((Z.coordChange i (Z.indexAt (b : B)) (b : B)) v : F) = 0 := by
    have h2 : slabVec Z (⟨(b : B), Z.coordChange i (Z.indexAt (b : B)) (b : B) v⟩ :
        Z.TotalSpace) = 0 := (slabNu_eq_zero_iff Z φ hφ hnn hpos _).mp h
    simpa [slabVec] using h2
  exact coordChange_injective Z i (b : B) b.2 (by rw [h1, map_zero])


/-- **The tube property for the dyadic slabs.**  Given an open set `P` of the punctured total space
containing the slab piece over `b`, there is a neighbourhood `W ∋ b` with `π ⁻¹' W ∩ slabK j ⊆ P`.

This is the tube property for the compact fibre piece of a slab, transported through the chart at `b`.

Route.  Fix `i₀` with `φ i₀ b ≠ 0` (exists since `∑ i, φ i b > 0`); then `b ∈ Z.baseSet i₀` by `hφ`.
Let `Φ := (Z.localTriv i₀).preimageHomeomorph (s := Z.baseSet i₀) subset_rfl :
  Z.proj ⁻¹' Z.baseSet i₀ ≃ₜ Z.baseSet i₀ × F` be the chart (continuous in both directions), and let
`g := fun (x, v) => slabNu Z φ (Φ.symm (x, v))`, continuous on `Z.baseSet i₀ × F` by `hcont`.  Write
`P̃` for the chart image of `P`.  Then:
* at `x = b`, `g (b, ·)` vanishes only at `v = 0` (`slabNu_eq_zero_iff`), so
  `S := {v : 2^j ≤ g (b,v) ≤ 2^(j+1)}` is a compact subset of the open set `P̃`; Mathlib's tube result
  `generalized_tube_lemma` gives open `N ∋ b` and `L ⊇ S` with `N × L ⊆ P̃`;
* `g` is homogeneous in `v` (`slabNu_smul`: `g (x, c • v) = |c| * g (x, v)`) and positive off `0`, so
  on the compact unit sphere `{v : ‖v‖ = 1}` the function `g (b, ·)` is bounded below by some `δ > 0`;
  by continuity of `g` and the tube result, `g (x, v) ≥ δ/2` for `x` near `b` and `‖v‖ = 1`, whence
  `{v : g (x,v) ≤ 2^(j+1)} ⊆ closedBall 0 (2^(j+1) / (δ/2))` for such `x`;
* on that bounded ball, `g (x, ·)` is uniformly close to `g (b, ·)` for `x` near `b` (continuity of `g`
  plus the tube result), which gives `{v : g (x,v) ∈ [2^j, 2^(j+1)]} ⊆ L` for `x` close to `b`.
Combining, a small neighbourhood `W` of `b` works. -/
theorem slabK_tube {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [ProperSpace F] {ι : Type*} [Fintype ι] (Z : Work.TangentClasses.RealBundle B F ι)
    (φ : ι → ContinuousMap B ℝ) (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i)
    (hcont : Continuous (Work.Gen.slabNu Z φ))
    (hnn : ∀ i b, 0 ≤ φ i b) (hpos : ∀ b, 0 < ∑ i, φ i b)
    (j : ℤ) (b : B) (P : Set (Work.Gen.Punct Z))
    (hP : IsOpen P) (hsub : Work.Gen.slabK Z φ j ∩ Work.Gen.punctProj Z ⁻¹' {b} ⊆ P) :
    ∃ W ∈ nhds b, Work.Gen.punctProj Z ⁻¹' W ∩ Work.Gen.slabK Z φ j ⊆ P := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < φ i b := by
    by_contra hc
    push Not at hc
    have hsum : ∑ i, φ i b = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hc i) (hnn i b)
    have := hpos b
    rw [hsum] at this
    exact lt_irrefl 0 this
  have hb₀ : b ∈ Z.baseSet i₀ :=
    hφ i₀ (subset_tsupport (φ i₀) (Function.mem_support.mpr hi₀.ne'))
  -- the chart at `b`
  let Φ : (Z.proj ⁻¹' Z.baseSet i₀) ≃ₜ (Z.baseSet i₀) × F :=
    (Z.localTriv i₀).preimageHomeomorph (Z.baseSet_at i₀).le
  let Ψ : (Z.baseSet i₀) × F → Z.TotalSpace := fun p => (Φ.symm p).val
  -- an open set of the total space cutting out `P`
  obtain ⟨Uo, hUo, hUoeq⟩ :=
    (isOpen_induced_iff (f := (Subtype.val : Punct Z → Z.TotalSpace)) (s := P)).mp hP
  have hmem : ∀ y : Punct Z, y ∈ P ↔ (y : Z.TotalSpace) ∈ Uo := by
    intro y; rw [← hUoeq]; rfl
  let Pc : Set ((Z.baseSet i₀) × F) := Ψ ⁻¹' Uo
  have hPcopen : IsOpen Pc :=
    hUo.preimage (continuous_subtype_val.comp Φ.continuous_symm)
  -- the slab piece over `b` maps into `Pc`
  have hPcsub : ∀ v : F, (2:ℝ)^j ≤ slabKTubeNu Z φ i₀ (⟨b, hb₀⟩, v) →
      slabKTubeNu Z φ i₀ (⟨b, hb₀⟩, v) ≤ (2:ℝ)^(j+1) →
      (⟨b, hb₀⟩, v) ∈ Pc := by
    intro v hv1 hv2
    have hposj : (0:ℝ) < (2:ℝ)^j := zpow_pos (by norm_num) j
    have hg0 : slabKTubeNu Z φ i₀ (⟨b, hb₀⟩, (0:F)) = 0 := by
      have h := slabKTubeNu_smul Z φ i₀ (⟨b, hb₀⟩) (0:ℝ) v
      simpa using h
    have hvnz : v ≠ 0 := by
      intro hv; rw [hv, hg0] at hv1; linarith
    have hval : Ψ (⟨b, hb₀⟩, v) =
        (⟨b, Z.coordChange i₀ (Z.indexAt b) b v⟩ : Z.TotalSpace) := by
      show (((Z.localTriv i₀).preimageHomeomorph (Z.baseSet_at i₀).le).symm (⟨b, hb₀⟩, v)).val
        = (⟨b, Z.coordChange i₀ (Z.indexAt b) b v⟩ : Z.TotalSpace)
      rw [Bundle.Trivialization.preimageHomeomorph_symm_apply]
      rfl
    have hz : Ψ (⟨b, hb₀⟩, v) ∈ zeroComplement Z := by
      rw [mem_zeroComplement, hval]
      show ((Z.coordChange i₀ (Z.indexAt b) b) v : F) ≠ 0
      intro hc
      exact hvnz (coordChange_injective Z i₀ b hb₀ (by rw [hc, map_zero]))
    let y : Punct Z := ⟨Ψ (⟨b, hb₀⟩, v), hz⟩
    have hy : y ∈ P := by
      apply hsub
      refine ⟨?_, ?_⟩
      · rw [mem_slabK]
        have hgl : slabNu Z φ (Ψ (⟨b, hb₀⟩, v)) = slabKTubeNu Z φ i₀ (⟨b, hb₀⟩, v) := rfl
        rw [hgl]
        exact ⟨hv1, hv2⟩
      · rw [Set.mem_preimage, Set.mem_singleton_iff]
        show Z.proj (Ψ (⟨b, hb₀⟩, v)) = b
        rw [hval]
    rw [hmem] at hy
    exact hy
  -- the tube step (the analytic content)
  obtain ⟨U, hU, hUtube⟩ :=
    tubeOfHomogeneous (A := Z.baseSet i₀) (F := F) (slabKTubeNu Z φ i₀)
      (slabKTubeNu_continuous Z φ i₀ hcont) (slabKTubeNu_smul Z φ i₀)
      (fun x v => slabKTubeNu_nonneg Z φ i₀ hnn (x, v))
      (fun x v h => slabKTubeNu_eq_zero Z φ i₀ hφ hnn hpos x v h)
      (lo := (2:ℝ)^j) (hi := (2:ℝ)^(j+1)) (zpow_pos (by norm_num) j) (⟨b, hb₀⟩) hPcopen hPcsub
  refine ⟨Subtype.val '' U, ?_, ?_⟩
  · have hmap : Filter.map (Subtype.val : (Z.baseSet i₀) → B) (𝓝 (⟨b, hb₀⟩)) = 𝓝 b :=
      IsOpenMap.map_nhds_eq (Z.isOpen_baseSet i₀).isOpenMap_subtype_val
        continuous_subtype_val.continuousAt
    rw [← hmap, Filter.mem_map]
    exact Filter.mem_of_superset hU (fun x hx => ⟨x, hx, rfl⟩)
  · intro y hy
    obtain ⟨hyW, hyK⟩ := hy
    rw [Set.mem_preimage] at hyW
    rw [mem_slabK] at hyK
    obtain ⟨x₀, hx₀U, hx₀eq⟩ := hyW
    have hy1 : (punctProj Z y) ∈ Z.baseSet i₀ := hx₀eq ▸ x₀.2
    let x' : Z.baseSet i₀ := ⟨(y : Z.TotalSpace).1, hy1⟩
    let yc : Z.proj ⁻¹' Z.baseSet i₀ := ⟨(y : Z.TotalSpace), hy1⟩
    have hx'eq : x' = x₀ := Subtype.ext hx₀eq.symm
    have hx'U : x' ∈ U := by rw [hx'eq]; exact hx₀U
    let v : F := (Z.localTriv i₀ (y : Z.TotalSpace)).2
    have hΦy : Φ yc = (x', v) := by
      rw [Bundle.Trivialization.preimageHomeomorph_apply]
    have hsymm : Φ.symm (x', v) = yc := by
      rw [← hΦy]; exact Φ.symm_apply_apply yc
    have hPsi : Ψ (x', v) = (y : Z.TotalSpace) := congrArg Subtype.val hsymm
    have hgval : slabKTubeNu Z φ i₀ (x', v) = slabNu Z φ (y : Z.TotalSpace) := by
      show slabNu Z φ (Ψ (x', v)) = slabNu Z φ (y : Z.TotalSpace)
      rw [hPsi]
    have hmemP : (x', v) ∈ Pc := by
      refine hUtube x' hx'U v ?_ ?_
      · rw [hgval]; exact hyK.1
      · rw [hgval]; exact hyK.2
    have hyUo : (y : Z.TotalSpace) ∈ Uo := by
      have : Ψ (x', v) ∈ Uo := hmemP
      rwa [hPsi] at this
    exact (hmem y).mpr hyUo

end

end Work.Gen
