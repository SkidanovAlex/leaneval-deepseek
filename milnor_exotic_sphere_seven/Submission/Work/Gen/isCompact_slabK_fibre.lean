import Mathlib
import Submission.Work.Gen.puncturedSlabs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Gen

/-- **The fibre piece of a slab is compact.**  This is the fibre input of the paracompactness
argument for the punctured total space `Work.Gen.Punct Z` of a real bundle over a base.

Route: pick `i₀` with `0 < φ i₀ b` (exists since `∑ i, φ i b > 0` and all terms are non-negative);
`hφ` gives `b ∈ Z.baseSet i₀`.  On the fibre over `b`, read in the chart `Z.localTriv i₀`, the
function `ν` is `v ↦ ∑ i, φ i b * ‖Z.coordChange (Z.indexAt b) i b v‖` (`Work.Gen.slabNu_mk`), and the
`i₀`-term dominates `φ i₀ b * ‖v‖` times the inverse norm of the linear equivalence
`Z.coordChange (Z.indexAt b) i₀ b`; hence the piece `{2^j ≤ ν ≤ 2^(j+1)}` is closed (continuity of
`ν`, e.g. `Work.Gen.slabNu_mk` + `Z.continuousOn_coordChange`) and bounded in the model fibre, so
compact by `[ProperSpace F]`.  Transport along the chart homeomorphism
`(Z.localTriv i₀).preimageHomeomorph` (or `Trivialization.preimageSingletonHomeomorph`) to the
subspace `Work.Gen.Punct Z`. -/
theorem isCompact_slabK_fibre {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [ProperSpace F] {ι : Type*} [Fintype ι] (Z : Work.TangentClasses.RealBundle B F ι)
    (φ : ι → ContinuousMap B ℝ) (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i)
    (hnn : ∀ i b, 0 ≤ φ i b) (hpos : ∀ b, 0 < ∑ i, φ i b)
    (hcont : Continuous (Work.Gen.slabNu Z φ)) (j : ℤ) (b : B) :
    IsCompact (Work.Gen.slabK Z φ j ∩ Work.Gen.punctProj Z ⁻¹' {b}) := by
  -- Step 0: some weight at `b` is positive, so `b` lies in the corresponding chart set.
  have hex : ∃ i, 0 < φ i b := by
    by_contra h
    push Not at h
    have hle : ∑ i, φ i b ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith [hpos b]
  obtain ⟨i₀, hi₀⟩ := hex
  have hb : b ∈ Z.baseSet i₀ :=
    hφ i₀ (subset_tsupport (φ i₀) (Function.mem_support.mpr (ne_of_gt hi₀)))
  -- Step 1: the chart at `b` and the inverse-chart parametrisation of the fibre over `b`.
  let e := Z.localTriv i₀
  let h : ↥(Z.proj ⁻¹' {b}) ≃ₜ F := e.preimageSingletonHomeomorph hb
  let sec : F → Z.TotalSpace := fun v => (h.symm v : Z.TotalSpace)
  have hsec_cont : Continuous sec := continuous_subtype_val.comp h.symm.continuous
  have hsec_proj : ∀ v, Z.proj (sec v) = b := fun v => (h.symm v).2
  have hsec_chart : ∀ v, (e (sec v)).2 = v := fun v => h.apply_symm_apply v
  have hsec_inv : ∀ x : ↥(Z.proj ⁻¹' {b}),
      sec ((e (x : Z.TotalSpace)).2) = (x : Z.TotalSpace) := by
    intro x
    show Subtype.val (h.symm (h x)) = Subtype.val x
    rw [h.symm_apply_apply]
  -- Step 2: the piece of the model fibre sitting over `b`.
  set C : Set F := {v | (2:ℝ)^j ≤ slabNu Z φ (sec v) ∧ slabNu Z φ (sec v) ≤ (2:ℝ)^(j+1)}
    with hCdef
  have hcontsec : Continuous fun v : F => slabNu Z φ (sec v) := hcont.comp hsec_cont
  have hCclosed : IsClosed C := by
    rw [hCdef]
    exact (isClosed_le continuous_const hcontsec).inter (isClosed_le hcontsec continuous_const)
  -- the `i₀`-term of `ν` dominates `φ i₀ b * ‖v‖`
  have hterm : ∀ v, φ i₀ b * ‖v‖ ≤ slabNu Z φ (sec v) := by
    intro v
    have h1 : φ i₀ b * ‖(e (sec v)).2‖ ≤ slabNu Z φ (sec v) := by
      have h2 := Finset.single_le_sum (f := fun i => φ i (sec v).1 * ‖(Z.localTriv i (sec v)).2‖)
        (fun i _ => mul_nonneg (hnn i (sec v).1) (norm_nonneg _)) (Finset.mem_univ i₀)
      simpa only [slabNu, hsec_proj v, e] using h2
    rwa [hsec_chart v] at h1
  have hbound : ∀ v ∈ C, ‖v‖ ≤ (2:ℝ)^(j+1) / φ i₀ b := by
    intro v hv
    rw [hCdef] at hv
    have h3 := hterm v
    have h4 := hv.2
    rw [le_div_iff₀ hi₀]
    linarith
  have hCcomp : IsCompact C := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : F) ((2:ℝ)^(j+1) / φ i₀ b))
      hCclosed ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound v hv
  -- Step 3: the chart identifies the piece over `b` with the piece of the model fibre.
  have himg : sec '' C = Subtype.val '' (slabK Z φ j ∩ punctProj Z ⁻¹' {b}) := by
    ext p
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [hCdef] at hv
      have hmem : sec v ∈ Work.Thom.zeroComplement Z := by
        have hν : 0 < slabNu Z φ (sec v) := lt_of_lt_of_le (zpow_pos (by norm_num) j) hv.1
        exact (slabVec_ne_zero_iff Z (sec v)).mp ((slabNu_pos Z φ hφ hnn hpos (sec v)).mp hν)
      refine ⟨⟨sec v, hmem⟩, ⟨?_, ?_⟩, rfl⟩
      · exact hv
      · exact hsec_proj v
    · rintro ⟨x, hx, rfl⟩
      have hx2 : Z.proj (x : Z.TotalSpace) = b := hx.2
      have hw : sec ((e (x : Z.TotalSpace)).2) = (x : Z.TotalSpace) :=
        hsec_inv ⟨(x : Z.TotalSpace), by simpa using hx2⟩
      refine ⟨(e (x : Z.TotalSpace)).2, ?_, hw⟩
      simp only [hCdef, Set.mem_ofPred_eq]
      rw [hw]
      exact hx.1
  have hsub : IsCompact (Subtype.val '' (slabK Z φ j ∩ punctProj Z ⁻¹' {b})) := by
    rw [← himg]
    exact hCcomp.image hsec_cont
  exact Subtype.isCompact_iff.mpr hsub

end Work.Gen
