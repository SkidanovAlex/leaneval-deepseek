import Mathlib
import Submission.Work.Horn.germF0_base

namespace Work.Horn

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-!
# `Work.Horn.Dg_pieces` — the two pieces of the horn domain `D_g`

For an `𝓕₀`-germ `f₀` with §4.1 data `d` and a nonempty immediate basin `B`, let
`BuOf d B`, `BlOf d B` be the two components of `B̃ = φ₀⁻¹(B) ∩ Dφ` (through `±i(η₀+1)`).
The domain of the pushed-down horn map is `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)`.  We record its decomposition
into the two open pieces

* `U = {0} ∪ π(B̃ᵘ)`  — the "upper" piece, which is open, **bounded** and preconnected, and
* `V = π(B̃ˡ)`        — the "lower" piece, which is open and disjoint from `U`,

together with the "no component crosses over" property: a preconnected subset of `D_g` meeting `U`
is entirely contained in `U`.

Boundedness of `U` is the substantive point: `B̃ᵘ ⊇ {η₀ < Im w}` and `B̃ˡ ⊇ {Im w < -η₀}`, and
`B̃ᵘ ∩ B̃ˡ = ∅` (Prop. 5.3), so `Im w ≥ -η₀` on `B̃ᵘ` and hence `‖π w‖ = e^{-2π Im w} ≤ e^{2πη₀}`.
-/

/-- `{0} ∪ π '' Bu` is open whenever `Bu` is open and contains the upper half plane
`{η < Im w}`: the image of that half plane is the punctured disc of radius `e^{-2πη}`, so it fills
in the missing point `0`. -/
theorem isOpen_insert_piExp_of_upper {Bu : Set ℂ} {η : ℝ} (hBuO : IsOpen Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    IsOpen (insert 0 (MandelDim.piExp '' Bu)) := by
  have hpi : IsOpen (MandelDim.piExp '' Bu) := Work.Repel.isOpen_piExp_image hBuO
  rw [isOpen_iff_mem_nhds]
  rintro ζ (rfl | hζ)
  · refine Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-(2 * Real.pi * η)))) ?_
    intro ξ hξ
    rcases eq_or_ne ξ 0 with rfl | hξne
    · exact Or.inl rfl
    · refine Or.inr ⟨Complex.log ξ / (2 * ↑Real.pi * Complex.I), hup ?_, ?_⟩
      · show η < (Complex.log ξ / (2 * ↑Real.pi * Complex.I)).im
        rw [Work.Repel.im_log_div_two_pi_I]
        have hlt : ‖ξ‖ < Real.exp (-(2 * Real.pi * η)) := by
          simpa [dist_eq_norm] using hξ
        have hlog : Real.log ‖ξ‖ < -(2 * Real.pi * η) :=
          (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hξne)).mpr hlt
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
        nlinarith [Real.pi_pos]
      · exact MandelDim.piExp_log_div ξ hξne
  · exact Filter.mem_of_superset (hpi.mem_nhds hζ) (Set.subset_insert _ _)

/-- `0` is in the closure of `π '' Bu` when `Bu` contains the upper half plane `{η < Im w}`:
`π '' {η < Im w}` is the punctured disc of radius `e^{-2πη}`, whose closure contains `0`. -/
theorem zero_mem_closure_piExp_of_upper {Bu : Set ℂ} {η : ℝ}
    (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    (0 : ℂ) ∈ closure (MandelDim.piExp '' Bu) := by
  have hsub : Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * η))) \ {0} ⊆
      MandelDim.piExp '' Bu := by
    intro ξ hξ
    obtain ⟨hξball, hξ0⟩ := hξ
    have hξne : ξ ≠ 0 := by simpa using hξ0
    refine ⟨Complex.log ξ / (2 * ↑Real.pi * Complex.I), hup ?_, ?_⟩
    · show η < (Complex.log ξ / (2 * ↑Real.pi * Complex.I)).im
      rw [Work.Repel.im_log_div_two_pi_I]
      have hlt : ‖ξ‖ < Real.exp (-(2 * Real.pi * η)) := by
        simpa [dist_eq_norm] using hξball
      have hlog : Real.log ‖ξ‖ < -(2 * Real.pi * η) :=
        (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hξne)).mpr hlt
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    · exact MandelDim.piExp_log_div ξ hξne
  have h0 : (0 : ℂ) ∈
      closure (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * η))) \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set c : ℝ := min ε (Real.exp (-(2 * Real.pi * η))) / 2 with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hcnorm : ‖(c : ℂ)‖ = c := by rw [norm_ofReal_coe, abs_of_pos hcpos]
    refine ⟨(c : ℂ), ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hcnorm]
      rw [hc]; have := min_le_right ε (Real.exp (-(2 * Real.pi * η))); linarith
    · intro h
      exact hcpos.ne' (Complex.ofReal_eq_zero.mp (Set.mem_singleton_iff.mp h))
    · rw [dist_eq_norm, zero_sub, norm_neg, hcnorm]
      rw [hc]; have := min_le_left ε (Real.exp (-(2 * Real.pi * η))); linarith
  exact closure_mono hsub h0

/-- `{0} ∪ π '' Bu` is preconnected whenever `Bu` is preconnected and contains the upper half
plane `{η < Im w}` (the inserted point `0` lies in the closure of the image). -/
theorem isPreconnected_insert_piExp {Bu : Set ℂ} {η : ℝ} (hBuC : IsPreconnected Bu)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    IsPreconnected (insert 0 (MandelDim.piExp '' Bu)) := by
  have hcont : Continuous MandelDim.piExp := by
    unfold MandelDim.piExp; continuity
  have h1 : IsPreconnected (MandelDim.piExp '' Bu) := hBuC.image _ hcont.continuousOn
  have h0 : (0 : ℂ) ∈ closure (MandelDim.piExp '' Bu) :=
    zero_mem_closure_piExp_of_upper hup
  refine h1.subset_closure (Set.subset_insert _ _) ?_
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz'
  · exact h0
  · exact subset_closure hz'

theorem Dg_pieces {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) :
    IsOpen (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
    Bornology.IsBounded (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
    IsPreconnected (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
    insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) =
      insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) ∪
        MandelDim.piExp '' (MandelDim.BlOf d B) ∧
    Disjoint (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)))
      (MandelDim.piExp '' (MandelDim.BlOf d B)) ∧
    (∀ C : Set ℂ, IsPreconnected C →
      C ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) →
      (C ∩ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty →
      C ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) := by
  -- the given immediate basin carries the `𝓕₀`-setup, so `Prop 5.3` applies to `BuOf`, `BlOf`
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, hBuT, _, hup, hlo, _⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
  obtain ⟨-, -, hdisj⟩ :=
    Work.HornSC.horn_sc Work.HornTopo.horn_topo Work.BasinSC.basin_sc
      Work.PlanarSC.planar_inter_sc f₀ D₀ B c d hsetup
  set U : Set ℂ := insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) with hU
  set V : Set ℂ := MandelDim.piExp '' (MandelDim.BlOf d B) with hV
  have hUopen : IsOpen U := hU.symm ▸ isOpen_insert_piExp_of_upper hBuO hup
  have hVopen : IsOpen V := hV.symm ▸ Work.Repel.isOpen_piExp_image hBlO
  have hUconn : IsPreconnected U :=
    hU.symm ▸ isPreconnected_insert_piExp isPreconnected_connectedComponentIn hup
  -- `BuOf ⊆ {Im ≥ -η₀}`: otherwise it would meet `BlOf ⊇ {Im < -η₀}`, contradicting Prop. 5.3
  have him : ∀ w ∈ MandelDim.BuOf d B, -d.η₀ ≤ w.im := by
    intro w hw
    by_contra h
    push_neg at h
    exact (Set.disjoint_left.mp hdisj) hw (hlo h)
  have hnorm : ∀ ζ ∈ MandelDim.piExp '' (MandelDim.BuOf d B),
      ‖ζ‖ ≤ Real.exp (2 * Real.pi * d.η₀) := by
    rintro ζ ⟨w, hw, rfl⟩
    rw [piExp_norm]
    apply Real.exp_le_exp.mpr
    have := him w hw
    nlinarith [Real.pi_pos]
  have hUbdd : Bornology.IsBounded U := by
    rw [hU]
    refine (Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := Real.exp (2 * Real.pi * d.η₀))).subset ?_
    intro ζ hζ
    rcases Set.mem_insert_iff.mp hζ with rfl | hζ'
    · rw [Metric.mem_closedBall, dist_self]; positivity
    · rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using hnorm ζ hζ'
  have hUV : U ∪ V = insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
    rw [hU, hV, Set.image_union]
    ext ζ
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  have hdisjUV : Disjoint (MandelDim.piExp '' (MandelDim.BuOf d B))
      (MandelDim.piExp '' (MandelDim.BlOf d B)) := by
    refine Set.disjoint_left.mpr fun ζ hζu hζl => ?_
    obtain ⟨w₁, hw₁, rfl⟩ := hζu
    obtain ⟨w₂, hw₂, hweq⟩ := hζl
    obtain ⟨k, hk⟩ := MandelDim.piExp_eq_iff.mp hweq
    have hmem : w₂ ∈ MandelDim.BuOf d B := by
      rw [hk]
      exact MandelDim.IsTInvariant.add_int hBuT hw₁ k
    exact (Set.disjoint_left.mp hdisj) hmem hw₂
  have hUVdisj : Disjoint U V := by
    rw [hU, hV]
    refine Set.disjoint_left.mpr fun ζ hζU hζV => ?_
    rcases Set.mem_insert_iff.mp hζU with rfl | hζu
    · obtain ⟨w, -, hw⟩ := hζV
      exact MandelDim.piExp_ne_zero w hw
    · exact (Set.disjoint_left.mp hdisjUV) hζu hζV
  refine ⟨hUopen, hUbdd, hUconn, hUV.symm, hUVdisj, ?_⟩
  intro C hC hsub hne
  have hsub' : C ⊆ U ∪ V := by rw [hUV]; exact hsub
  have hdisjC : C ∩ (U ∩ V) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hUVdisj, Set.inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hC U V hUopen hVopen hsub' hdisjC) with
    hCU | hCV
  · exact hCU
  · exfalso
    obtain ⟨z, hzC, hzU⟩ := hne
    exact (Set.disjoint_left.mp hUVdisj) hzU (hCV hzC)

end

end Work.Horn
