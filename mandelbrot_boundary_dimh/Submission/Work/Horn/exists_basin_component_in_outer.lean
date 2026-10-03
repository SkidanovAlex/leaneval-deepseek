import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion
import Submission.Work.Horn.flower_q_component_nz
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.E_surjOn_ends
import Submission.Work.Horn.cov_of_parts
import Submission.Work.HornPhi.horn_phi
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.pushdown_differentiableOn_punctured
import Submission.Work.Horn.pushdown_germ_not_id

/-!
# `Work.Horn.exists_basin_component_in_outer`

Shishikura's parabolic implosion for `f₀ ∈ 𝓕₀`: for the pushed-down horn map
`g = pushdown Ẽ_{f₀}` on `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)` the parabolic basin of `0` has a component in
the **outer** (lower) piece `π '' B̃ˡ` — the piece on which `g` is asymptotically the contraction
`ζ ↦ π cl · ζ`, `|π cl| = exp (-2π Im cl) < 1`.

The point of the construction is that it uses only *proved* Prop. 5.3 material (the covering
property of `E` on each horn, `cov_of_parts`, hence its surjectivity off the critical-value lattice
`Φ c + ℤ`, `E_surjOn_ends`): the parabolic basin of `g` contains a whole petal `V` of the Leau–Fatou
flower of `g` at `0` (`flower_q_component_nz`), and *every* preimage under `g` of a basin point is
again a basin point (`Work.HornTopo.mem_basin_of_image_mem`, backward invariance of the basin).
Since `E : B̃ˡ → ℂ` is onto `ℂ ∖ (Φ c + ℤ)`, every lift `y` of a petal point off the lattice has a
preimage `w ∈ B̃ˡ`, and `π w` is the required outer basin point.

The lower-end hypothesis `hcl`/`hclpos` is not needed in this route (it is the input of
`Horn/pushdown_lower_end_linear_growth`, kept here for the caller's use); the outer component is
produced by the covering property instead.
-/

open scoped Topology

namespace Work.Horn

set_option maxHeartbeats 2000000

open MandelDim Set Filter Topology

noncomputable section

/-- A nonempty open subset of `ℂ` contains a point different from any prescribed point. -/
lemma exists_mem_ne_of_isOpen {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) (p : ℂ) :
    ∃ y ∈ U, y ≠ p := by
  obtain ⟨x, hx⟩ := hne
  rcases eq_or_ne x p with rfl | hxp
  · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨x + (((r / 2 : ℝ)) : ℂ), hrU ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : x + (((r / 2 : ℝ)) : ℂ) - x = (((r / 2 : ℝ)) : ℂ) := by ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
      linarith
    · intro h
      have h2 : (((r / 2 : ℝ)) : ℂ) = 0 := by
        have h3 := congrArg (fun z : ℂ => z - x) h
        simpa [sub_self] using h3
      have h4 : r / 2 = 0 := Complex.ofReal_eq_zero.mp h2
      linarith
  · exact ⟨x, hx, hxp⟩

theorem exists_basin_component_in_outer {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {cl : ℂ} (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl))
    (hclpos : 0 < cl.im) :
    ∃ C : Set ℂ, C.Nonempty ∧ IsPreconnected C ∧
      C ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
      C ⊆ MandelDim.piExp '' Bl := by
  classical
  -- ## 0. the `𝓕₀`-setup, and `Bu`, `Bl` are the canonical components `BuOf`, `BlOf`
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, hsub₀⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBu_eq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBl_eq : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hBu_eq' : MandelDim.BuOf d B = Bu := hBu_eq.symm
  have hBl_eq' : MandelDim.BlOf d B = Bl := hBl_eq.symm
  -- ## 1. the domain `D_g`, the map `g` and its elementary properties
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0 : (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := Set.mem_insert _ _
  have hfix : MandelDim.pushdown d.E 0 = 0 := MandelDim.pushdown_zero d.E
  have hd1 : deriv (MandelDim.pushdown d.E) 0 = 1 := MandelDim.deriv_pushdown_E d
  -- ## 2. the Leau–Fatou expansion of `g` at `0`
  have hρ : 0 < Real.exp (-(2 * Real.pi * d.η₀)) := Real.exp_pos _
  -- `g` is holomorphic on the ball of radius `exp (-2πη₀)`: on the punctured ball this is
  -- `pushdown_differentiableOn_punctured`, and at `0` it is `pushdown_hasDerivAt_zero`
  have hgball : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * d.η₀)))) := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact (pushdown_hasDerivAt_zero f₀ D₀ d).differentiableAt.differentiableWithinAt
    · have hnhds : Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * d.η₀))) \ {0} ∈ 𝓝 z :=
        (Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl).mem_nhds
          ⟨hz, by simpa using hz0⟩
      exact (((pushdown_differentiableOn_punctured f₀ D₀ d) z ⟨hz, hz0⟩).differentiableAt
        hnhds).differentiableWithinAt
  have hnz : ¬ (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ) :=
    pushdown_not_eventually_id d hsetup
  obtain ⟨q, hq, a, ha, hgerm⟩ := germ_expansion hρ hgball hfix hd1 hnz
  -- ## 3. the flower of `g` on `D_g`
  have hopen : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      ∀ U ∈ nhds z, MandelDim.pushdown d.E '' U ∈ nhds (MandelDim.pushdown d.E z) := by
    have hset : insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) =
        insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
      rw [hBu_eq, hBl_eq]
    rw [hset]
    exact hopen_Dg hF0 d hB hBne
  obtain ⟨V, hV1, hV0, hVmap, hVdisj, hVcl, hVinj, hVcapture, hVreach, hVindex⟩ :=
    flower_q_component_nz hDg h0 hg hq ha hfix hopen hgerm
  -- ## 4. a point of a petal, off the critical-value lattice `Φ c + ℤ`
  set i : Fin q := ⟨0, by omega⟩ with hi
  have hVi_open : IsOpen (V i) := (hV1 i).1
  have hVi_ne : (V i).Nonempty := (hV1 i).2.1.nonempty
  have hVi_sub : V i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := (hV1 i).2.2
  obtain ⟨v, hvV, hvne⟩ := exists_mem_ne_of_isOpen hVi_open hVi_ne (MandelDim.piExp (d.Φ c))
  have hv0 : v ≠ 0 := fun h0 => hV0 i (h0 ▸ hvV)
  -- ## 5. the lift `y` of `v`, and surjectivity of `E` on the lower horn
  set y : ℂ := Complex.log v / (2 * Real.pi * Complex.I) with hydef
  have hpiy : MandelDim.piExp y = v := Work.Horn.MandelDim.piExp_log_div v hv0
  have hyoff : ∀ k : ℤ, y ≠ d.Φ c + k := by
    intro k hk
    refine hvne ?_
    rw [← hpiy, hk, Work.Horn.MandelDim.piExp_add_intCast]
  have hcov := cov_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi
    Work.HornVarphi.horn_varphi hornSC f₀ D₀ B c d hsetup
  obtain ⟨w, hwBlOf, hwE⟩ :=
    (E_surjOn_ends Work.HornTopo.horn_topo d hsetup hcov).2 y hyoff
  have hwBl : w ∈ Bl := hBl_eq' ▸ hwBlOf
  -- ## 6. `g (π w) = v`
  have hTl : MandelDim.IsTInvariant (MandelDim.BlOf d B) := fun u => by
    rw [hBl_eq']
    exact hBlT u
  have hEl : ∀ u ∈ MandelDim.BlOf d B, u + 1 ∈ MandelDim.BlOf d B →
      d.E (u + 1) = d.E u + 1 := fun u hu _ =>
    Work.Horn.MandelDim.ParabData.E_add_one d
      (hsub₀ (Set.mem_union_right _ (hBl_eq' ▸ hu)))
      (hsub₀ (Set.mem_union_right _ (hBl_eq' ▸ (hTl u).mp hu)))
  have hgpi : MandelDim.pushdown d.E (MandelDim.piExp w) = MandelDim.piExp (d.E w) :=
    Work.Horn.MandelDim.pushdown_piExp hTl hEl hwBlOf
  have hgv : MandelDim.pushdown d.E (MandelDim.piExp w) = v := by
    rw [hgpi, hwE, hpiy]
  -- ## 7. `v` is in the basin of `g`, hence so is `π w` (backward invariance)
  have hvbasin : v ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
    refine hVreach v (hVi_sub hvV) ⟨0, ?_, ?_⟩
    · intro k hk
      omega
    · simpa using (Set.mem_iUnion.mpr ⟨i, hvV⟩ : v ∈ ⋃ j, V j)
  have hpiw_mem : MandelDim.piExp w ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
    Set.mem_insert_iff.mpr (Or.inr ⟨w, Set.mem_union_right _ hwBl, rfl⟩)
  have hbasin : MandelDim.piExp w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.HornTopo.mem_basin_of_image_mem hDg hg hpiw_mem (by rw [hgv]; exact hvbasin)
  -- ## 8. the witness
  exact ⟨{MandelDim.piExp w}, ⟨MandelDim.piExp w, rfl⟩, isPreconnected_singleton,
    (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact hbasin),
    (fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      exact ⟨w, hwBl, hz.symm⟩)⟩

end

end Work.Horn
