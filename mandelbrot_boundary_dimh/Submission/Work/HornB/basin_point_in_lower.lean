import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.assembly
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.HornTopo.horn_topo
import Submission.Work.HornPhi.horn_phi
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.Horn.E_surjOn_ends
import Submission.Work.Horn.exists_basin_component_in_outer

namespace Work.HornB

/-- Any non-empty parabolic basin of the pushed-down horn map contains a point of the "outer"
(lower-end) piece `π '' Bl`.

The argument does not use the dynamics of the basin beyond its non-emptiness: since the basin is
open (`Work.Horn.isOpen_parabolicBasin`) it contains a point `v` different from the single
critical-value point `π (Φ c)`; the lifted horn map `E` is a covering on the lower horn
(`Work.Horn.cov_of_parts`) off the critical lattice `Φ c + ℤ`, hence surjective there
(`Work.Horn.E_surjOn_ends`), so a lift `y` of `v` has a preimage `w ∈ Bl`; `π` intertwines `E`
with `pushdown d.E` (`Work.Horn.MandelDim.pushdown_piExp`), so `g (π w) = v` is a basin point and
the backward invariance of the basin (`Work.HornTopo.mem_basin_of_image_mem`) puts `π w` in the
basin.  Finally `π (log v/(2πi)) = v`, so `v ≠ 0` as soon as `0 ∉ basin`
(`Work.Horn.zero_not_mem_basin_pushdown`). -/
theorem basin_point_in_lower {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hne : (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))).Nonempty) :
    ∃ ζ ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      ζ ∈ MandelDim.piExp '' Bl := by
  classical
  -- ## 0. the `𝓕₀`-setup, and `Bl` is the canonical component `BlOf d B`
  obtain ⟨c, hsetup⟩ := Work.Horn.isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, -, hBlT, -, hlo₀, hsub₀⟩ :=
    Work.Horn.horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBl_eq : Bl = MandelDim.BlOf d B := Work.Horn.Bl_eq_BlOf d hBl hlo hlo₀
  -- ## 1. a basin point `v` different from the critical-value point `π (Φ c)`
  have hBopen : IsOpen (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :=
    Work.Horn.isOpen_parabolicBasin _ _
  obtain ⟨v, hvbasin, hvne⟩ :=
    Work.Horn.exists_mem_ne_of_isOpen hBopen hne (MandelDim.piExp (d.Φ c))
  have hv0 : v ≠ 0 := fun h =>
    Work.Horn.zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo (h ▸ hvbasin)
  -- ## 2. `v` lifted off the critical-value lattice
  have hlog : MandelDim.piExp (Complex.log v / (2 * (Real.pi : ℂ) * Complex.I)) = v :=
    Work.Horn.MandelDim.piExp_log_div v hv0
  have hyoff : ∀ k : ℤ,
      Complex.log v / (2 * (Real.pi : ℂ) * Complex.I) ≠ d.Φ c + k := by
    intro k hk
    refine hvne ?_
    rw [← hlog, hk, Work.Horn.MandelDim.piExp_add_intCast]
  -- ## 3. surjectivity of `E` on the lower horn off that lattice
  have hcov := Work.Horn.cov_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi
    Work.HornVarphi.horn_varphi Work.Horn.hornSC f₀ D₀ B c d hsetup
  obtain ⟨-, hsurjL⟩ := Work.Horn.E_surjOn_ends Work.HornTopo.horn_topo d hsetup hcov
  obtain ⟨w, hwBlOf, hwE⟩ := hsurjL _ hyoff
  have hwBl : w ∈ Bl := by rw [hBl_eq]; exact hwBlOf
  -- ## 4. `g (π w) = v`
  have hTl : MandelDim.IsTInvariant (MandelDim.BlOf d B) := fun u => by
    rw [← hBl_eq]; exact hBlT u
  have hEl : ∀ u ∈ MandelDim.BlOf d B, u + 1 ∈ MandelDim.BlOf d B →
      d.E (u + 1) = d.E u + 1 := fun u hu _ =>
    Work.Horn.MandelDim.ParabData.E_add_one d
      (hsub₀ (Set.mem_union_right _ (hBl_eq.symm ▸ hu)))
      (hsub₀ (Set.mem_union_right _ (hBl_eq.symm ▸ (hTl u).mp hu)))
  have hgpi : MandelDim.pushdown d.E (MandelDim.piExp w) = MandelDim.piExp (d.E w) :=
    Work.Horn.MandelDim.pushdown_piExp hTl hEl hwBlOf
  have hgv : MandelDim.pushdown d.E (MandelDim.piExp w) = v := by
    rw [hgpi, hwE, hlog]
  -- ## 5. `π w` is a basin point (backward invariance)
  have hpiwD : MandelDim.piExp w ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
    Set.mem_insert_iff.mpr (Or.inr ⟨w, Set.mem_union_right _ hwBl, rfl⟩)
  have hDg_open : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.isOpen_insert_piExp hBuO hBlO hup hlo
  have hg_holo : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hbasin : MandelDim.piExp w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.HornTopo.mem_basin_of_image_mem hDg_open hg_holo hpiwD (by rw [hgv]; exact hvbasin)
  exact ⟨MandelDim.piExp w, hbasin, w, hwBl, rfl⟩

end Work.HornB
