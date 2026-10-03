import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.E_not_locally_const
import Submission.Work.Horn.pushdown_not_locally_const
import Submission.Work.Horn.locally_open_of_not_locally_const

/-!
# `Work.Horn.basin_basic_Dg`

`Work.Horn.MandelDim.basin_basic` (`Submission/Work/Horn/basin.lean`) proves the three elementary
facts about the parabolic basin of a map `f` on a domain `D`

* `ParabolicBasin f D` is open,
* it is forward invariant (`f z ∈ ParabolicBasin f D` for `z` in it),
* it is backward invariant inside `D` (`f z ∈ ParabolicBasin f D` and `z ∈ D` imply `z` in it),

but it takes the *local openness* of `f` at the points of `D` as a hypothesis.  That hypothesis is
supplied there by `MandelDim.basin_open_map`, which needs `D` **preconnected**.  For the
pushed-down horn map `g = pushdown d.E` on

`D_g = {0} ∪ π '' (Bu ∪ Bl)`

preconnectedness is *false* in the canonical situation (`Work.Horn.not_preconnected_Dg`: the upper
and lower pieces `{0} ∪ π '' Bu` and `π '' Bl` are disjoint nonempty open sets), so the hypothesis
`hconn` of `Work.Horn.pushdown_basin_basic` is uninstantiable and that route is broken.

This file re-routes the argument: preconnectedness of `D_g` is **not** needed, only the *pointwise*
fact that `g` is nowhere locally constant on `D_g`.  Indeed, by
`Work.Horn.locally_open_of_not_locally_const`, a holomorphic function which is not locally constant
at `z` is locally open at `z`, and that is the only thing `basin_basic` uses preconnectedness for.

Nowhere-local-constancy of `g` comes from the two ends of the cylinder:

* at `z = 0`, from `g'(0) = 1` (`Work.Horn.MandelDim.deriv_pushdown_E`), i.e. Shishikura's
  normalisation (4.1.5);
* at `z = π w` with `w ∈ Bu ∪ Bl`, from `Work.Horn.E_not_locally_const` (the lifted horn map `E`
  is nowhere locally constant on `Bu ∪ Bl`: analytic continuation along the component of `d.DE`
  through `w` would carry a local constancy to the ends of the cylinder, where `E w - w → 0`
  resp. `E w - w → cl`) transported through `π` by
  `Work.Horn.pushdown_not_locally_const`.

Nothing about the *connectedness* of the domain enters, so the statement holds for the canonical
(disconnected) `D_g`.
-/

open MandelDim Set Metric Filter Topology
open scoped Topology

namespace Work.Horn

noncomputable section

theorem basin_basic_Dg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    IsOpen (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      Set.MapsTo (MandelDim.pushdown d.E)
        (MandelDim.ParabolicBasin (MandelDim.pushdown d.E) (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
        (MandelDim.ParabolicBasin (MandelDim.pushdown d.E) (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      (∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
        MandelDim.pushdown d.E z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) →
        z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) := by
  -- the cylinder domain `D_g` is open, `g = pushdown d.E` is holomorphic on it, and
  -- `Bu ∪ Bl` is `T`-invariant with `E` equivariant on it
  obtain ⟨hBuO, hBlO, hBuT, hBlT, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hGholo : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := by
    intro u
    simp only [Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mp h)
      · exact Or.inr ((hBlT u).mp h)
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mpr h)
      · exact Or.inr ((hBlT u).mpr h)
  have heq : ∀ u ∈ Bu ∪ Bl, u + 1 ∈ Bu ∪ Bl → d.E (u + 1) = d.E u + 1 :=
    fun u hu _ => MandelDim.ParabData.E_add_one d (hsub hu) (hsub ((hT u).mp hu))
  have hDEo : IsOpen d.DE :=
    d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open (isOpen_parabolicBasin f₀ D₀)
  -- `g` is locally open at every point of its domain: it is holomorphic there and nowhere
  -- locally constant
  have hopen : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)), ∀ U ∈ 𝓝 z,
      MandelDim.pushdown d.E '' U ∈ 𝓝 (MandelDim.pushdown d.E z) := by
    intro z hz U hU
    refine locally_open_of_not_locally_const hDg hGholo hz ?_ U hU
    rcases Set.mem_insert_iff.mp hz with rfl | hz'
    · -- the germ at `0`, where `g'(0) = 1`
      intro hloc
      have hEq : (fun _ : ℂ => MandelDim.pushdown d.E 0) =ᶠ[𝓝 (0 : ℂ)]
          (MandelDim.pushdown d.E) := by
        filter_upwards [hloc] with ζ hζ using hζ.symm
      have hz0 : deriv (MandelDim.pushdown d.E) 0 = 0 := by
        rw [← hEq.deriv_eq]
        simp
      rw [Work.Horn.MandelDim.deriv_pushdown_E d] at hz0
      exact one_ne_zero hz0
    · -- the points of `π '' (Bu ∪ Bl)`, by descent from the lifted horn map
      obtain ⟨w, hw, rfl⟩ := hz'
      have hcont : ContinuousAt d.E w :=
        (Work.Horn.differentiableOn_E d).continuousOn.continuousAt (hDEo.mem_nhds (hsub hw))
      exact pushdown_not_locally_const hT heq hw ((hBuO.union hBlO).mem_nhds hw) hcont
        (E_not_locally_const d hBu hBl hsub hup hlo w hw)
  exact MandelDim.basin_basic hDg hGholo hopen

end

end Work.Horn
