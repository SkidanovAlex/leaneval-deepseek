import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.fiber_infinite_in_basin
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.HornB.components_infinite_abstract
import Submission.Work.HornB.exists_injective_component_family
import Submission.Work.HornB.basin_point_in_lower

/-!
# `Work.Horn.basin_components_infinite` — the parabolic basin of `g = pushdown d.E` has
infinitely many components

For `f₀ ∈ 𝓕₀` with §4.1 data `d : ParabData f₀ D₀`, an immediate basin `B`, the two end components
`Bu, Bl` of `φ₀⁻¹(B) ∩ Dφ` and `D_g = {0} ∪ π '' (Bu ∪ Bl)`, the parabolic basin
`P = ParabolicBasin (pushdown d.E) D_g` of the pushed-down horn map has **infinitely many**
connected components, i.e. there is an injective family of maximal preconnected subsets of `P`
(that is the requested statement).

## The argument

Everything is routed through the abstract counting lemma
`Work.HornB.components_infinite_abstract`, whose hypotheses are met as follows.

* `P` is open (`Work.Horn.basin_basic_Dg`) and `g`-invariant, `P ⊆ D_g`, and `g` is continuous on
  `P` (holomorphy of `g` on the open `D_g`, `Work.Horn.pushdown_g_holo`).
* The fibre of `g` over every nonzero point of `P` inside `P` is infinite
  (`Work.Horn.pushdown_fiber_infinite_in_basin`, Prop. 5.3's infinite degree).
* The components `B' i` of `P` carrying the Leau–Fatou petals of `g` at `0` are `g`-invariant, and
  every `P`-orbit enters one of them (`Work.Horn.petal_components_upper_local`, the flower theorem
  `Work.Horn.flower_q_component_nz` + `Work.Horn.petal_spread_component`).
* `P` also has a point in the *lower* piece `π '' Bl` (`Work.HornB.basin_point_in_lower`, from the
  infinite fibres of `E` on `Bl` together with backward invariance of the basin), so the component
  of that point is a component of `P` different from every `B' i`: the `B' i` lie in the bounded
  *upper* piece `{0} ∪ π '' BuOf`, the lower piece is disjoint from it (`Work.Horn.Dg_pieces`).

The abstract lemma then turns the "σ is a surjective self-map of the component set, hence a
bijection when the component set is finite" argument into `¬ ∃ s : Finset (Set ℂ), …`, and
`Work.HornB.exists_injective_component_family` converts that into the injective family required.
-/

namespace Work.Horn

open Set Filter Topology

noncomputable section

theorem basin_components_infinite (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (η : ℝ) (Bu Bl : Set ℂ)
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hne : (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))).Nonempty) :
    ∃ f : ℕ → Set ℂ,
      Function.Injective f ∧
      (∀ k : ℕ, f k ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      (∀ k : ℕ, IsPreconnected (f k)) ∧
      (∀ (k : ℕ) (C : Set ℂ), IsPreconnected C →
        C ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) →
        (f k ∩ C).Nonempty → C ⊆ f k) := by
  classical
  have hBne : B.Nonempty := hB.2.1.nonempty
  -- ## 0. Structural facts: the two components are the canonical ones, `D_g` is open, `g` is
  -- holomorphic there
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, hsub₀⟩ :=
    Work.Horn.horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBu_eq : Bu = MandelDim.BuOf d B := Work.Horn.Bu_eq_BuOf d hBu hup hup₀
  have hBl_eq : Bl = MandelDim.BlOf d B := Work.Horn.Bl_eq_BlOf d hBl hlo hlo₀
  have hDgopen : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.isOpen_insert_piExp hBuO hBlO hup hlo
  have hgholo : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  -- ## 1. The basin: open, invariant, contained in `D_g`, and with infinite fibres over its
  -- nonzero points
  obtain ⟨hPopen, hPmap, hPback⟩ := Work.Horn.basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  have hPsub : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hmap, -⟩ := hz
    exact hmap 0 (mem_of_mem_nhds hU)
  have hPconn : ContinuousOn (MandelDim.pushdown d.E)
      (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) := hgholo.continuousOn.mono hPsub
  have hfiber : ∀ w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))), w ≠ 0 →
      ((MandelDim.pushdown d.E) ⁻¹' {w} ∩ MandelDim.ParabolicBasin
        (MandelDim.pushdown d.E) (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))).Infinite :=
    fun w hw hw0 =>
      Work.Horn.pushdown_fiber_infinite_in_basin hF0 d hB hBne hBu hBl hsub hup hlo hw0 hw
  -- ## 2. The petal components: `g`-invariant components of `P` in the upper piece which capture
  -- every basin orbit
  obtain ⟨q, B', hB'sub, hB'comp, hB'inv, hB'reach, hB'U⟩ :=
    petal_components_upper_local hF0 d hB hBne hBu hBl hsub hup hlo
  -- ## 3. A basin point in the lower piece `π '' Bl`
  obtain ⟨ζ, hζP, hζV⟩ :=
    Work.HornB.basin_point_in_lower hF0 d hB hBne hBu hBl hsub hup hlo hne
  -- ## 4. The two pieces of `D_g` are disjoint, so the component of `ζ` is not a petal component
  obtain ⟨hUopen, hUbdd, hUconn, hUVeq, hUVdisj, hcross⟩ := Work.Horn.Dg_pieces hF0 d hB hBne
  have hζV' : ζ ∈ MandelDim.piExp '' (MandelDim.BlOf d B) := by rwa [hBl_eq] at hζV
  have hC1ne : ∀ i : Fin q,
      connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ζ ≠ B' i := by
    intro i hEq
    have hζB : ζ ∈ B' i := by
      rw [← hEq]
      exact mem_connectedComponentIn hζP
    exact (Set.disjoint_left.mp hUVdisj) (hB'U i hζB) hζV'
  -- ## 5. The counting lemma and the conversion into an injective family
  have hnotfinite : ¬ ∃ s : Finset (Set ℂ),
      ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
        connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z ∈ s :=
    Work.HornB.components_infinite_abstract hPopen hPconn hPmap hfiber B'
      hB'comp hB'inv hB'reach
      ⟨connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ζ,
        ⟨ζ, hζP, rfl⟩, hC1ne⟩
  exact Work.HornB.exists_injective_component_family hnotfinite

end

end Work.Horn
