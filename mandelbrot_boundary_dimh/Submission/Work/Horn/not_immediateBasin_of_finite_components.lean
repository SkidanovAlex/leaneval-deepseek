import Mathlib
import Submission.Work.Horn.fiber_infinite_in_basin
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.pushdown_not_locally_const
import Submission.Work.Horn.E_not_locally_const
import Submission.Work.Horn.pushdown_basin_surj
import Submission.Work.Horn.not_immediateBasin_of_connected
import Submission.Work.HornFC.nonzero_mem_component
import Submission.Work.HornFC.componentMap_wd
import Submission.Work.HornFC.finite_inter_preimage_singleton

/-!
# `Work.Horn.not_immediateBasin_of_finite_components`

**If the parabolic basin of the pushed-down horn map `g = pushdown d.E` on its horn domain
`D_g = {0} ∪ π '' (Bu ∪ Bl)` has finitely many connected components and the fibre of `g` inside the
basin over every nonzero basin point is infinite, then `g` has no immediate basin at all** (in the
sense of `MandelDim.IsImmediateBasin`, which demands *properness* of `g : B → B`).

This generalises `Work.Horn.not_immediateBasin_of_connected` (the case "the basin is
preconnected", where the unique component is `B'` itself) to the case of *finitely many*
components, which is the situation the paper's Lemma 5.2/5.4 produces (`q` petals ⟹ `q`
components).

## The mechanism

The proofs of `Work.Horn.basin_basic_Dg` give that the basin `P` is open, forward invariant and
backward invariant inside `D_g`; `Work.Horn.pushdown_fiber_infinite_in_basin` gives that the fibre
of `g` over every nonzero `w ∈ P` inside `P` is infinite.

The new ingredient is the induced map **σ on the finite set `Ω` of components of `P`**: it sends a
component `C` to the component containing `g '' C` (well defined because `g '' C` is preconnected,
`g` being continuous and `C` connected — `Work.HornFC.componentMap_wd`).  Two observations:

* **σ is surjective.**  For a component `C` pick a nonzero point `v ∈ C` (possible since `C` is
  open, hence nonempty and not `{0}`; `Work.HornFC.nonzero_mem_component`).  The fibre over `v`
  inside `P` being infinite is in particular nonempty, so there is `ζ ∈ P` with `g ζ = v`; the
  component of `ζ` is then mapped by σ to the component of `v`, i.e. to `C`.
* **A self-map of a finite set that is surjective is injective** (`Finite.injective_iff_surjective`).

Consequently every component has a *unique* predecessor under σ.  In particular, if `B'` is a
component of `P` with `g '' B' ⊆ B'` (so that σ fixes `B'`), then σ's unique predecessor of `B'` is
`B'` itself, i.e. **every preimage in `P` of a point of `B'` already lies in `B'`**.  But then for a
nonzero `w ∈ B'` the fibre `g ⁻¹' {w} ∩ P` (infinite) is contained in `B'`, hence equals
`B' ∩ g ⁻¹' {w}`, which `IsImmediateBasin`'s properness clause forces to be compact.  A compact
subset of the domain of the holomorphic, nowhere-locally-constant `g` meets a fibre only finitely
often (`Work.HornFC.finite_inter_preimage_singleton`), a contradiction.

Along the way the following three library lemmas (proved in `Submission/Work/HornFC/`) are used:
`Work.HornFC.nonzero_mem_component`, `Work.HornFC.componentMap_wd`,
`Work.HornFC.finite_inter_preimage_singleton`.
-/

namespace Work.Horn

open Set Metric Filter

noncomputable section

/-- A choice of point of a nonempty subset of `ℂ` (`0` for the empty set).  Only used through
`Work.Horn.pick_mem`; its advantage over `Exists.choose` is that the term `pick C` does not depend
on a *proof* that `C` is a component, so it can be rewritten with without dependency problems. -/
def pick (C : Set ℂ) : ℂ := by
  classical
  exact if h : C.Nonempty then h.choose else 0

theorem pick_mem {C : Set ℂ} (hC : C.Nonempty) : pick C ∈ C := by
  rw [pick, dite_eq_left hC]
  exact hC.choose_spec

/-- **The abstract content of `Work.Horn.not_immediateBasin_of_finite_components`.**

Let `g` be holomorphic on an open set `D`, nowhere locally constant on `D`, and such that

* the parabolic basin `P = MandelDim.ParabolicBasin g D` is open and `g`-invariant,
* `P ⊆ D`,
* the fibre of `g` inside `P` over every nonzero point of `P` is infinite,
* `P` has only finitely many connected components.

Then `g` has no immediate basin on `D`. -/
theorem not_immediateBasin_of_finite_components_general {g : ℂ → ℂ} {D : Set ℂ}
    (hDopen : IsOpen D)
    (hgholo : DifferentiableOn ℂ g D)
    (hgnlc : ∀ z ∈ D, ¬ Filter.Eventually (fun u => g u = g z) (nhds z))
    (hPopen : IsOpen (MandelDim.ParabolicBasin g D))
    (hPmap : Set.MapsTo g (MandelDim.ParabolicBasin g D) (MandelDim.ParabolicBasin g D))
    (hfiber : ∀ w ∈ MandelDim.ParabolicBasin g D, w ≠ 0 →
      (g ⁻¹' {w} ∩ MandelDim.ParabolicBasin g D).Infinite)
    (hPsub : MandelDim.ParabolicBasin g D ⊆ D)
    (hfin : ∃ s : Finset (Set ℂ), ∀ z ∈ MandelDim.ParabolicBasin g D,
      connectedComponentIn (MandelDim.ParabolicBasin g D) z ∈ s) :
    ¬ ∃ B' : Set ℂ, MandelDim.IsImmediateBasin g D B' := by
  rintro ⟨B', hB'⟩
  classical
  let P : Set ℂ := MandelDim.ParabolicBasin g D
  obtain ⟨s, hs⟩ := hfin
  -- the set of connected components of the basin
  set Ω : Set (Set ℂ) := {C | ∃ z ∈ P, C = connectedComponentIn P z} with hΩdef
  have hΩfin : Ω.Finite := (s.finite_toSet).subset (fun C hC => by
    obtain ⟨z, hz, rfl⟩ := hC
    exact hs z hz)
  haveI : Fintype Ω := hΩfin.fintype
  have hpoint : ∀ (C : Set ℂ), C ∈ Ω → pick C ∈ C := fun C hC => by
    obtain ⟨z, hzP, hCeq⟩ := hC
    have hne : C.Nonempty := ⟨z, by rw [hCeq]; exact mem_connectedComponentIn hzP⟩
    exact pick_mem hne
  have hnonzero : ∀ C ∈ Ω, ∃ w ∈ C, w ≠ 0 := fun C hC => by
    obtain ⟨z, hz, rfl⟩ := hC
    exact Work.HornFC.nonzero_mem_component hPopen hz
  have hcont : ContinuousOn g P := (hgholo.mono hPsub).continuousOn
  -- `g` sends each component of `P` into a single component of `P`
  have hCmap : ∀ C ∈ Ω, ∀ z ∈ C, ∀ z' ∈ C,
      connectedComponentIn P (g z) = connectedComponentIn P (g z') :=
    fun C hC z hz z' hz' => Work.HornFC.componentMap_wd hPopen hcont hPmap hC hz hz'
  have hCmem : ∀ C ∈ Ω, ∀ z ∈ C, connectedComponentIn P (g z) ∈ Ω := fun C hC z hz => by
    obtain ⟨z₀, hz₀, hCeq⟩ := hC
    have hz' : z ∈ connectedComponentIn P z₀ := hCeq ▸ hz
    exact ⟨g z, hPmap (connectedComponentIn_subset P z₀ hz'), rfl⟩
  -- the induced map on components
  let σ : Ω → Ω := fun C => ⟨connectedComponentIn P (g (pick C.1)),
    hCmem C.1 C.2 (pick C.1) (hpoint C.1 C.2)⟩
  have hσ_val : ∀ (C : Ω) {z : ℂ} (hz : z ∈ C.1),
      (σ C).1 = connectedComponentIn P (g z) :=
    fun C z hz => hCmap C.1 C.2 (pick C.1) (hpoint C.1 C.2) z hz
  -- σ is surjective: the component of a preimage of a point of `C` maps to `C`
  have hσsurj : Function.Surjective σ := by
    rintro ⟨C', hC'Ω⟩
    obtain ⟨z, hzP, rfl⟩ := hC'Ω
    obtain ⟨v, hvC', hv0⟩ := hnonzero (connectedComponentIn P z) ⟨z, hzP, rfl⟩
    have hvP : v ∈ P := connectedComponentIn_subset P z hvC'
    obtain ⟨ζ, hζg, hζP⟩ := (hfiber v hvP hv0).nonempty
    have hζg' : g ζ = v := Set.mem_singleton_iff.mp hζg
    refine ⟨⟨connectedComponentIn P ζ, ⟨ζ, hζP, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hσ_val ⟨connectedComponentIn P ζ, ⟨ζ, hζP, rfl⟩⟩ (mem_connectedComponentIn hζP), hζg']
    exact (connectedComponentIn_eq hvC').symm
  -- hence σ is a bijection of the finite set of components of the basin
  have hσinj : Function.Injective σ := Finite.injective_iff_surjective.mpr hσsurj
  -- `B'` is a connected component of the basin
  have hB'sub : B' ⊆ P := by
    rw [show P = MandelDim.ParabolicBasin g D from rfl]
    exact hB'.2.2.1
  have hB'pre : IsPreconnected B' := hB'.2.1.isPreconnected
  have hB'comp : ∀ z ∈ B', B' = connectedComponentIn P z := by
    intro z hz
    refine le_antisymm (hB'pre.subset_connectedComponentIn hz hB'sub) ?_
    exact hB'.2.2.2.1 (connectedComponentIn P z) isPreconnected_connectedComponentIn
      (connectedComponentIn_subset P z) ⟨z, hz, mem_connectedComponentIn (hB'sub hz)⟩
  have hB'Ω : B' ∈ Ω := by
    obtain ⟨b, hb⟩ := hB'.2.1.nonempty
    exact ⟨b, hB'sub hb, hB'comp b hb⟩
  obtain ⟨b, hbB'⟩ := hB'.2.1.nonempty
  have hbP : b ∈ P := hB'sub hbB'
  have hB'comp_b : B' = connectedComponentIn P b := hB'comp b hbB'
  have hB'pt : pick B' ∈ B' := hpoint B' hB'Ω
  -- `σ` fixes `B'`, because `g` maps `B'` into itself
  have hσB' : σ ⟨B', hB'Ω⟩ = ⟨B', hB'Ω⟩ := by
    apply Subtype.ext
    rw [hσ_val ⟨B', hB'Ω⟩ hB'pt]
    have hmem : g (pick B') ∈ connectedComponentIn P b :=
      hB'comp_b ▸ (hB'.2.2.2.2.1 hB'pt)
    exact (connectedComponentIn_eq hmem).symm.trans hB'comp_b.symm
  -- injectivity of σ: every preimage in the basin of a point of `B'` lies in `B'`
  have hpre : ∀ z ∈ P, g z ∈ B' → z ∈ B' := by
    intro z hzP hgzB'
    have hCz : σ ⟨connectedComponentIn P z, ⟨z, hzP, rfl⟩⟩ = ⟨B', hB'Ω⟩ := by
      apply Subtype.ext
      rw [hσ_val ⟨connectedComponentIn P z, ⟨z, hzP, rfl⟩⟩ (mem_connectedComponentIn hzP)]
      have hmem : g z ∈ connectedComponentIn P b := hB'comp_b ▸ hgzB'
      exact (connectedComponentIn_eq hmem).symm.trans hB'comp_b.symm
    have hinj := hσinj (hCz.trans hσB'.symm)
    have hset : connectedComponentIn P z = B' := by
      have h2 := congrArg (fun X : Ω => X.1) hinj
      simpa using h2
    exact hset ▸ mem_connectedComponentIn hzP
  -- the infinite fibre over a nonzero point of `B'` is contained in `B'`, hence compact
  obtain ⟨w, hwB', hw0⟩ := hnonzero B' hB'Ω
  have hwP : w ∈ P := hB'sub hwB'
  have hinf : (g ⁻¹' {w} ∩ P).Infinite := hfiber w hwP hw0
  have hEq : g ⁻¹' {w} ∩ P = B' ∩ g ⁻¹' {w} := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      have hgz : g z = w := Set.mem_singleton_iff.mp hz1
      exact ⟨hpre z hz2 (hgz.symm ▸ hwB'), hz1⟩
    · rintro ⟨hz1, hz2⟩
      exact ⟨hz2, hB'sub hz1⟩
  have hcomp : IsCompact (B' ∩ g ⁻¹' {w}) :=
    hB'.2.2.2.2.2.2 {w} (by rw [Set.singleton_subset_iff]; exact hwB') isCompact_singleton
  have hfin' : (B' ∩ g ⁻¹' {w}).Finite := by
    have h0 := Work.HornFC.finite_inter_preimage_singleton hDopen hgholo hgnlc
      (K := B' ∩ g ⁻¹' {w}) hcomp (fun z hz => hPsub (hB'sub hz.1)) (w := w)
    rwa [Set.inter_eq_left.mpr Set.inter_subset_right] at h0
  exact hfin'.not_infinite (hEq ▸ hinf)

theorem not_immediateBasin_of_finite_components {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hV : ∃ w : ℂ, w ≠ 0 ∧ w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
    (hfin : ∃ s : Finset (Set ℂ), ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z ∈ s) :
    ¬ ∃ B' : Set ℂ, MandelDim.IsImmediateBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) B' := by
  obtain ⟨hPopen, hPmap, -⟩ := basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDopen : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hPsub : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hiter, -⟩ := hz
    simpa using hiter 0 (mem_of_mem_nhds hU)
  exact not_immediateBasin_of_finite_components_general hDopen
    (pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo)
    (pushdown_not_locally_const_Dg hF0 d hB hBne hBu hBl hsub hup hlo)
    hPopen hPmap
    (fun w hw hw0 => pushdown_fiber_infinite_in_basin hF0 d hB hBne hBu hBl hsub hup hlo hw0 hw)
    hPsub hfin

end

end Work.Horn
