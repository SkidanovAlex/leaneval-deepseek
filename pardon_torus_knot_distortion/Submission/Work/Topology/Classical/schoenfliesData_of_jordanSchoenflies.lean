import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# The Jordan–Schoenflies datum on a set homeomorphic to the round sphere

`JordanSchoenfliesSphere` (`Work.Topology.Classical.Defs`) is stated on the *round* unit sphere
`RoundSphere = Metric.sphere 0 1`.  This file is the transport of its conclusion to an arbitrary
set `A ⊆ ℝ³` equipped with a homeomorphism `φ : RoundSphere ≃ₜ A`: given pairwise disjoint Jordan
curves `c i` on `A`, the curves `G i = φ⁻¹ ∘ c i` are Jordan curves on the round sphere, and the
Jordan–Schoenflies discs and nesting rank attached to them are pushed forward along `φ`.

The result is exactly the packaged structure `SchoenfliesData A ι c`, which is what the rest of
the chapter (`Work.Topology.Classical.sliceData_standard_of_homeomorph`,
`Work.Topology.Classical.sliceInput_standard_of_jordanSchoenflies`) consumes.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

set_option linter.style.haveILetI false in
theorem schoenfliesData_of_jordanSchoenflies
    (h : Work.Topology.Classical.JordanSchoenfliesSphere)
    {A : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (φ : Work.Topology.Classical.RoundSphere ≃ₜ A)
    {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hc : ∀ i : ι, Work.Topology.Classical.IsJordanCurveOn A (c i))
    (hdisj : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) :
    Nonempty (Work.Topology.Classical.SchoenfliesData A ι c) := by
  classical
  -- the curves as maps into the subtypes, and their pull-back to the round sphere
  have hcA : ∀ i t, c i t ∈ A := fun i => (hc i).1
  have hccont : ∀ i, Continuous (c i) := fun i => (hc i).2.1
  have hcper : ∀ i, Function.Periodic (c i) (2 * Real.pi) := fun i => (hc i).2.2.1
  have hcinj : ∀ i, Set.InjOn (c i) (Set.Ico 0 (2 * Real.pi)) := fun i => (hc i).2.2.2
  let C : ι → ℝ → ↥A := fun i t => ⟨c i t, hcA i t⟩
  let G : ι → ℝ → ↥RoundSphere := fun i t => φ.symm (C i t)
  let g : ι → ℝ → R3 := fun i t => (G i t : R3)
  have hφG : ∀ i t, φ (G i t) = C i t := fun i t => φ.apply_symm_apply (C i t)
  have hCcont : ∀ i, Continuous (C i) := fun i => (hccont i).subtype_mk (hcA i)
  have hGper : ∀ i, Function.Periodic (G i) (2 * Real.pi) := by
    intro i t
    apply congrArg φ.symm
    apply Subtype.ext
    exact hcper i t
  -- the pulled-back curves are Jordan curves on the round sphere
  have hjc : ∀ i, IsJordanCurveRound (g i) := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t; exact (G i t).2
    · exact continuous_subtype_val.comp
        ((map_continuous φ.symm).comp (hCcont i))
    · exact fun t => congrArg Subtype.val (hGper i t)
    · intro t ht t' ht' hh
      apply hcinj i ht ht'
      have h2 : φ (G i t) = φ (G i t') := congrArg φ (Subtype.ext hh)
      rw [hφG i t, hφG i t'] at h2
      exact Subtype.ext_iff.mp h2
  -- ... and pairwise disjoint, since `φ` (and hence `φ.symm`) is injective
  have hgdisj : Pairwise fun i j => Disjoint (Set.range (g i)) (Set.range (g j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨t, rfl⟩ ⟨t', ht'⟩
    have hSS : C i t = C j t' := by
      rw [← hφG i t, ← hφG j t']
      exact (congrArg φ (Subtype.ext ht')).symm
    have hcc : c i t = c j t' := congrArg Subtype.val hSS
    exact Set.disjoint_left.mp (hdisj hij) (Set.mem_range_self t) ⟨t', hcc.symm⟩
  obtain ⟨e, e', rank, heinj, he'inj, hebnd, he'bnd, hemem, he'mem, heopen, he'open,
    hecov, heint, hrank⟩ := h ι g hjc hgdisj
  -- the discs of the round sphere, as maps into the subtype
  let E : ι → Disc → ↥RoundSphere := fun i z => ⟨e i z, hemem i z⟩
  let E' : ι → Disc → ↥RoundSphere := fun i z => ⟨e' i z, he'mem i z⟩
  -- their push-forwards along `φ`
  let disc : ι → C(Disc, R3) := fun i =>
    { toFun := fun z => (φ (E i z) : R3)
      continuous_toFun := continuous_subtype_val.comp
        ((map_continuous φ).comp ((e i).continuous_toFun.subtype_mk (hemem i))) }
  let disc' : ι → C(Disc, R3) := fun i =>
    { toFun := fun z => (φ (E' i z) : R3)
      continuous_toFun := continuous_subtype_val.comp
        ((map_continuous φ).comp ((e' i).continuous_toFun.subtype_mk (he'mem i))) }
  refine ⟨{
    e := disc
    e' := disc'
    rank := rank
    inj := ?_
    inj' := ?_
    boundary := ?_
    boundary' := ?_
    mem := ?_
    mem' := ?_
    open_interior := ?_
    open_interior' := ?_
    cover := ?_
    meet := ?_
    nested := ?_ }⟩
  · -- injectivity of the pushed-forward disc
    intro i z z' hzz'
    have h1 : φ (E i z) = φ (E i z') := Subtype.ext hzz'
    have h2 : E i z = E i z' := φ.injective h1
    exact heinj i (congrArg Subtype.val h2)
  · -- injectivity of the other pushed-forward disc
    intro i z z' hzz'
    have h1 : φ (E' i z) = φ (E' i z') := Subtype.ext hzz'
    have h2 : E' i z = E' i z' := φ.injective h1
    exact he'inj i (congrArg Subtype.val h2)
  · -- the boundary of the pushed-forward disc is the given curve
    intro i θ
    have h1 : E i (circlePoint θ) = G i θ := by
      apply Subtype.ext
      exact hebnd i θ
    change (φ (E i (circlePoint θ)) : R3) = c i θ
    rw [h1]
    exact congrArg Subtype.val (hφG i θ)
  · -- likewise for the other disc
    intro i θ
    have h1 : E' i (circlePoint θ) = G i θ := by
      apply Subtype.ext
      exact he'bnd i θ
    change (φ (E' i (circlePoint θ)) : R3) = c i θ
    rw [h1]
    exact congrArg Subtype.val (hφG i θ)
  · -- the disc lies in `A`
    intro i z
    exact (φ (E i z)).2
  · -- likewise for the other disc
    intro i z
    exact (φ (E' i z)).2
  · -- the interior of the disc is open in `A`, being the image under `φ` of an open set
    intro i
    have hset : φ '' {x : ↥RoundSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z = (x : R3)}
        = {x : ↥A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z = (x : R3)} := by
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
  · -- likewise for the other side
    intro i
    have hset : φ '' {x : ↥RoundSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e' i z = (x : R3)}
        = {x : ↥A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc' i z = (x : R3)} := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, hyz⟩, rfl⟩
        refine ⟨z, hz, ?_⟩
        change (φ (E' i z) : R3) = (φ y : R3)
        have : E' i z = y := Subtype.ext hyz
        rw [this]
      · rintro ⟨z, hz, hzx⟩
        refine ⟨E' i z, ⟨z, hz, rfl⟩, ?_⟩
        apply Subtype.ext
        exact hzx
    rw [← hset]
    exact φ.isOpenMap _ (he'open i)
  · -- the two pushed-forward discs cover `A`
    intro i
    ext y
    constructor
    · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · exact (φ (E i z)).2
      · exact (φ (E' i z)).2
    · intro hy
      obtain ⟨w, hw⟩ := φ.surjective ⟨y, hy⟩
      have hwmem : (w : R3) ∈ Set.range (e i) ∪ Set.range (e' i) := by
        rw [hecov i]; exact w.2
      rcases hwmem with ⟨z, hz⟩ | ⟨z, hz⟩
      · left
        refine ⟨z, ?_⟩
        change (φ (E i z) : R3) = y
        have hzw : E i z = w := Subtype.ext hz
        rw [hzw]
        exact congrArg Subtype.val hw
      · right
        refine ⟨z, ?_⟩
        change (φ (E' i z) : R3) = y
        have hzw : E' i z = w := Subtype.ext hz
        rw [hzw]
        exact congrArg Subtype.val hw
  · -- the two pushed-forward discs meet exactly in the curve
    intro i
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      rcases hy1 with ⟨z, rfl⟩
      rcases hy2 with ⟨z', hz'⟩
      have hEq : E' i z' = E i z := by
        apply φ.injective
        apply Subtype.ext
        exact hz'
      have he : e i z ∈ Set.range (e i) ∩ Set.range (e' i) :=
        ⟨⟨z, rfl⟩, ⟨z', (congrArg Subtype.val hEq)⟩⟩
      rw [heint i] at he
      obtain ⟨t, ht⟩ := he
      refine ⟨t, ?_⟩
      have hEG : E i z = G i t := Subtype.ext ht.symm
      show c i t = (φ (E i z) : R3)
      rw [hEG]
      exact (congrArg Subtype.val (hφG i t)).symm
    · rintro ⟨t, rfl⟩
      have hGt : (G i t : R3) ∈ Set.range (e i) ∩ Set.range (e' i) := by
        rw [heint i]; exact ⟨t, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨z, hz⟩ := hGt.1
        refine ⟨z, ?_⟩
        show (φ (E i z) : R3) = c i t
        have hEG : E i z = G i t := Subtype.ext hz
        rw [hEG]
        exact congrArg Subtype.val (hφG i t)
      · obtain ⟨z, hz⟩ := hGt.2
        refine ⟨z, ?_⟩
        show (φ (E' i z) : R3) = c i t
        have hEG : E' i z = G i t := Subtype.ext hz
        rw [hEG]
        exact congrArg Subtype.val (hφG i t)
  · -- the nesting rank: a curve meeting the interior of the disc of `i` has smaller rank
    intro i j hcon
    apply hrank i j
    obtain ⟨z, hz, hmem'⟩ := hcon
    obtain ⟨t, ht⟩ := hmem'
    refine ⟨z, hz, ?_⟩
    refine ⟨t, ?_⟩
    have h1 : C j t = φ (E i z) := Subtype.ext ht
    have h2 : G j t = E i z := by
      change φ.symm (C j t) = E i z
      rw [h1, φ.symm_apply_apply]
    exact congrArg Subtype.val h2

end

end Work.Topology.Classical
