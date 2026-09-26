import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# The slicing datum at a sphere homeomorphic to the round sphere

Given a homeomorphism `φ : RoundSphere ≃ₜ S` of the round unit sphere onto a set `S ⊆ ℝ³`, a
transversality witness `TransverseSphere standard S` (the finite family of curves of `S ∩ F`,
`F = standard.carrier`) and the Jordan–Schoenflies theorem on the round sphere with standard
position of finitely many pairwise disjoint curves (`JordanSchoenfliesSphere`, see
`Work.Topology.Classical.Defs`), we obtain a slicing datum `SliceData standard S`.

The argument is a transport of the Jordan–Schoenflies datum along the homeomorphism `φ`:

* the curves `c i` of `S` are pulled back to Jordan curves `g i = φ⁻¹ ∘ c i` on the round sphere;
* Jordan–Schoenflies bounds embedded discs `e i` in the round sphere with `∂ e i = g i`, whose
  interiors are open in the sphere, and supplies the nesting rank;
* pushing the discs forward along `φ` gives embedded discs in `S` bounded by `c i`, whose
  interiors are open in `S` (`φ` is a homeomorphism), and the same rank witnesses the nesting.

Notice that no hypothesis that `S` is an embedded sphere is needed: the homeomorphism `φ` itself
is the only structural input about `S`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk
open Work.Topology.SphereSlicing

namespace Work.Topology.Classical

set_option linter.style.haveILetI false in
theorem sliceData_standard_of_homeomorph (S : Set LeanEval.KnotTheory.PardonDistortion.R3)
    (φ : Work.Topology.Classical.RoundSphere ≃ₜ S)
    (hT : Work.Topology.SphereSlicing.TransverseSphere Work.CoreTopology.standard S)
    (h : Work.Topology.Classical.JordanSchoenfliesSphere) :
    Nonempty (Work.Topology.SphereSlicing.SliceData Work.CoreTopology.standard S) := by
  classical
  obtain ⟨ι, hfin, c, hsimple, hdisj, hmem, hcover⟩ := hT
  haveI : Fintype ι := hfin
  -- The pulled-back curves on the round sphere.
  let G : ι → ℝ → ↥RoundSphere := fun i t => φ.symm ⟨c i t, hmem i t⟩
  let g : ι → ℝ → R3 := fun i t => (G i t : R3)
  -- They are Jordan curves on the round sphere ...
  have hjc : ∀ i, IsJordanCurveRound (g i) := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t; exact (G i t).2
    · exact continuous_subtype_val.comp
        ((map_continuous φ.symm).comp ((c i).cont.subtype_mk (hmem i)))
    · intro t
      apply congrArg Subtype.val
      apply congrArg φ.symm
      apply Subtype.ext
      exact (c i).periodic t
    · intro t ht t' ht' hh
      apply hsimple i ht ht'
      have h2 : φ (G i t) = φ (G i t') := congrArg φ (Subtype.ext hh)
      have h3 : φ (G i t) = ⟨(c i).γ t, hmem i t⟩ := by
        simp only [G]; exact φ.apply_symm_apply _
      have h4 : φ (G i t') = ⟨(c i).γ t', hmem i t'⟩ := by
        simp only [G]; exact φ.apply_symm_apply _
      rw [h3, h4] at h2
      exact Subtype.ext_iff.mp h2
  -- ... and pairwise disjoint, since `φ` (and hence `φ.symm`) is injective.
  have hgdisj : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨t, rfl⟩ ⟨t', ht'⟩
    have hSS : (⟨(c i).γ t, hmem i t⟩ : ↥S) = ⟨(c j).γ t', hmem j t'⟩ := by
      have h2 : φ (G j t') = φ (G i t) := congrArg φ (Subtype.ext ht')
      have h3 : φ (G i t) = ⟨(c i).γ t, hmem i t⟩ := by
        simp only [G]; exact φ.apply_symm_apply _
      have h4 : φ (G j t') = ⟨(c j).γ t', hmem j t'⟩ := by
        simp only [G]; exact φ.apply_symm_apply _
      rw [h3, h4] at h2
      exact h2.symm
    have hcc : (c i).γ t = (c j).γ t' := Subtype.ext_iff.mp hSS
    exact Set.disjoint_left.mp (hdisj hij) (Set.mem_range_self t) ⟨t', hcc.symm⟩
  obtain ⟨e, e', rank, heinj, _he'inj, hebnd, _he'bnd, hemem, _he'mem, heopen, _he'open,
    _hecov, _heint, hrank⟩ := h ι g hjc hgdisj
  -- The discs in the round sphere, as points of the subtype.
  let E : ι → Disc → ↥RoundSphere := fun i z => ⟨e i z, hemem i z⟩
  -- Their images under `φ` are embedded discs in `S`.
  let disc : ι → C(Disc, R3) := fun i =>
    { toFun := fun z => (φ (E i z) : R3)
      continuous_toFun := continuous_subtype_val.comp
        ((map_continuous φ).comp ((e i).continuous_toFun.subtype_mk (hemem i))) }
  refine ⟨{
    ι := ι
    fintype := hfin
    c := c
    simple := hsimple
    disjoint := hdisj
    mem := hmem
    covers_pt := hcover
    disc := disc
    disc_inj := ?_
    disc_boundary := ?_
    disc_mem := ?_
    open_interior := ?_
    rank := rank
    inside := ?_ }⟩
  · -- injectivity of the pushed-forward disc
    intro i z z' hzz'
    have h1 : φ (E i z) = φ (E i z') := by
      apply Subtype.ext
      exact hzz'
    have h2 : E i z = E i z' := φ.injective h1
    have h3 : e i z = e i z' := congrArg Subtype.val h2
    exact heinj i h3
  · -- the boundary of the pushed-forward disc is the given curve
    intro i θ
    have h1 : E i (circlePoint θ) = G i θ := by
      apply Subtype.ext
      exact hebnd i θ
    change (φ (E i (circlePoint θ)) : R3) = (c i).γ θ
    rw [h1]
    have h2 : φ (G i θ) = ⟨(c i).γ θ, hmem i θ⟩ := by
      simp only [G]; exact φ.apply_symm_apply _
    exact congrArg Subtype.val h2
  · -- the disc lies in `S`
    intro i z
    exact (φ (E i z)).2
  · -- the interior of the disc is open in `S`, being the image under `φ` of an open set
    intro i
    have hset : φ '' {x : ↥RoundSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z = (x : R3)}
        = {x : ↥S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z = (x : R3)} := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, hyz⟩, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (φ (E i z) : R3) = (φ y : R3)
        have : E i z = y := Subtype.ext hyz
        rw [this]
      · rintro ⟨z, hz, hzx⟩
        refine ⟨E i z, ⟨z, hz, rfl⟩, ?_⟩
        apply Subtype.ext
        exact hzx
    rw [← hset]
    exact φ.isOpenMap _ (heopen i)
  · -- the nesting rank: a curve meeting the interior of the disc of `i` has smaller rank
    intro i j hcon
    apply hrank i j
    obtain ⟨z, hz, hmem'⟩ := hcon
    obtain ⟨t, ht⟩ := hmem'
    refine ⟨z, hz, ?_⟩
    refine ⟨t, ?_⟩
    show (G j t : R3) = (E i z : R3)
    have hφ : φ (E i z) = ⟨(c j).γ t, hmem j t⟩ := Subtype.ext ht.symm
    have key : E i z = φ.symm ⟨(c j).γ t, hmem j t⟩ := by
      calc E i z = φ.symm (φ (E i z)) := (φ.symm_apply_apply (E i z)).symm
        _ = φ.symm ⟨(c j).γ t, hmem j t⟩ := by rw [hφ]
    rw [key]

end Work.Topology.Classical
