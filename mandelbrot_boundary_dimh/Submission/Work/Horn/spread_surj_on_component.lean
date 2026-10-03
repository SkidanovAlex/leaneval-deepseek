import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.basin_components_infinite
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.PetalImLocal.image_eq_self_of_isPreconnected

open Set Filter Topology
open scoped Topology

namespace Work.Horn

/-!
# `Work.Horn.spread_surj_on_component`

Surjectivity of the pushed-down horn map `g = pushdown d.E` on a component `B' i` of its parabolic
basin `P = ParabolicBasin g D_g`, `D_g = {0} ∪ π '' (Bu ∪ Bl)`:

    B' i ⊆ g '' B' i.

The proof is the classical one for a holomorphic self-map of a component of its own basin which is
*proper*:

* `B' i` is an open, preconnected, nonempty component of the open set `P` (`T`-invariance of the
  hyperbolic structure is irrelevant here: only the component structure and the local behaviour of
  `g` at `0` are used), maximal among preconnected subsets of `P`;
* `g '' B' i ⊆ B' i` (`hmap`) and `g` is *proper* relative to `B' i` (`hprop`);
* properness makes `g '' B' i` closed inside `B' i`
  (`Work.Horn.PetalImLocal.mem_image_of_mem_closure`, using the maximality of the component);
* `g` is *open* at every point of `D_g` (`Work.Horn.hopen_Dg`: `g` is nowhere locally constant,
  from `g'(0) = 1` at `0` and from the two end asymptotics of the lifted horn map), hence
  `g '' B' i` is open inside `B' i`;
* a nonempty subset of the *preconnected* `B' i` which is both open and closed is everything.

The only subtlety is the verification that `g` is not constant on `B' i` (needed for the open
mapping theorem): since `g` is open at every point of the nonempty open set `B' i`, a constant value
`c` on `B' i` would make the singleton `{c}` a neighbourhood of `c` — impossible in `ℂ`.
-/

/-- A singleton is not a neighbourhood of its point in `ℂ` (no point of `ℂ` is isolated). -/
theorem singleton_not_mem_nhds_complex (a : ℂ) : ¬ ({a} : Set ℂ) ∈ 𝓝 a := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  have hrew : a + (ε : ℂ) / 2 - a = (ε : ℂ) / 2 := by ring
  have hmem : a + (ε : ℂ) / 2 ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, dist_eq_norm, hrew, norm_ofReal_div_two ε hε.le]
    linarith
  have h1 : a + (ε : ℂ) / 2 = a := Set.mem_singleton_iff.mp (hball hmem)
  have h2 : (ε : ℂ) / 2 = 0 := by
    have h1' : a + (ε : ℂ) / 2 = a + 0 := by rw [add_zero]; exact h1
    exact add_left_cancel h1'
  have h3 : ((ε : ℂ) / 2).re = 0 := by rw [h2, Complex.zero_re]
  have h4 : ε / 2 = 0 := by simpa using h3
  linarith

theorem spread_surj_on_component {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {q : ℕ} {B' : Fin q → Set ℂ}
    (hcomp : ∀ i, ∃ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      B' i = connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z)
    (hmap : ∀ i, Set.MapsTo (MandelDim.pushdown d.E) (B' i) (B' i))
    (hprop : ∀ (i : Fin q) (L : Set ℂ), L ⊆ B' i → IsCompact L →
      IsCompact (B' i ∩ (MandelDim.pushdown d.E) ⁻¹' L)) :
    ∀ i, B' i ⊆ MandelDim.pushdown d.E '' B' i := by
  obtain ⟨hBuO, hBlO, -, -, hup₀, hlo₀, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBu_eq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBl_eq : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  -- the parabolic basin of `g` is open
  have hPopen : IsOpen (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :=
    (basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo).1
  have hPsubDg : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆
      insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
    ImmBasins.parabolicBasin_subset_D
  -- `g` is open at every point of its domain (the domain is the canonical `D_g`)
  have hE : insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) =
      insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
    rw [hBu_eq, hBl_eq]
  have hopenDg : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      ∀ U ∈ 𝓝 z, MandelDim.pushdown d.E '' U ∈ 𝓝 (MandelDim.pushdown d.E z) := by
    intro z hz
    rw [hE] at hz
    exact hopen_Dg hF0 d hB hBne z hz
  intro i
  obtain ⟨z₀, hz₀P, hB'i⟩ := hcomp i
  have hz₀B : z₀ ∈ B' i := by rw [hB'i]; exact mem_connectedComponentIn hz₀P
  have hBi_sub : B' i ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
    rw [hB'i]; exact connectedComponentIn_subset _ _
  have hBi_open : IsOpen (B' i) := by
    rw [hB'i]; exact hPopen.connectedComponentIn
  have hBi_pre : IsPreconnected (B' i) := by
    rw [hB'i]; exact isPreconnected_connectedComponentIn
  -- maximality of the component among preconnected subsets of the basin
  have hmax : ∀ s : Set ℂ, IsPreconnected s →
      s ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) →
      (B' i ∩ s).Nonempty → s ⊆ B' i := by
    intro s hs hsF hmeet
    obtain ⟨y, hyB, hys⟩ := hmeet
    rw [hB'i] at hyB ⊢
    rw [connectedComponentIn_eq hyB]
    exact IsPreconnected.subset_connectedComponentIn hs hys hsF
  -- `g` is not constant on the component: otherwise a singleton would be a neighbourhood
  have hnconst : ¬ ∃ c : ℂ, ∀ z ∈ B' i, MandelDim.pushdown d.E z = c := by
    rintro ⟨c, hc⟩
    have hconst : ∀ᶠ w in 𝓝 z₀, MandelDim.pushdown d.E w = MandelDim.pushdown d.E z₀ := by
      filter_upwards [hBi_open.mem_nhds hz₀B] with w hw
      rw [hc w hw, hc z₀ hz₀B]
    have him : MandelDim.pushdown d.E ''
        {w : ℂ | MandelDim.pushdown d.E w = MandelDim.pushdown d.E z₀} ∈
        𝓝 (MandelDim.pushdown d.E z₀) :=
      hopenDg z₀ (hPsubDg (hBi_sub hz₀B))
        {w : ℂ | MandelDim.pushdown d.E w = MandelDim.pushdown d.E z₀} hconst
    have hsing : MandelDim.pushdown d.E ''
        {w : ℂ | MandelDim.pushdown d.E w = MandelDim.pushdown d.E z₀} =
        {MandelDim.pushdown d.E z₀} := by
      ext v
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        exact ⟨z₀, rfl, hv.symm⟩
    rw [hsing] at him
    exact singleton_not_mem_nhds_complex _ him
  intro x hx
  have heq : MandelDim.pushdown d.E '' B' i = B' i :=
    PetalImLocal.image_eq_self_of_isPreconnected (B := B' i) hDg hg hBi_sub hmax
      (hprop i) ⟨z₀, hz₀B⟩ hBi_open hBi_pre (hmap i) hnconst
  rw [heq]
  exact hx

end Work.Horn
