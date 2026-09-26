import Mathlib
import Submission.Work.EpsW.arcsWallFamily
import Submission.Work.EpsW.countsWd
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.exists_finite_component_decomposition
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_of_forall
import Submission.Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle
import Submission.Work.Smooth.JordanSeparationCutting.isLocallyArc_of_periodic_injOn
import Submission.Work.BoxShrink.closure_sliceRegion_subset
import Submission.Work.CoreTopology.isClosed_carrier
import Submission.Work.EpsW.localEuclidean_range_of_periodic_injOn
import Submission.Work.EpsW.exists_isOpen_localModel_periodic
import Submission.Work.EpsW.localArc_gluedPair
import Submission.Work.EpsW.localEuclidean_image_Ioo
import Submission.Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
import Submission.Work.EpsW.exists_isOpen_localModel_arc

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.Smooth.OneManifold

namespace Work.EpsW

noncomputable section

/-- The level coordinate `y ↦ y (σ 2)` of the box data. -/
def lvl (σ : Equiv.Perm (Fin 3)) (y : R3) : ℝ := y (σ 2)

/-- The `x`-th parameter of the unit interval: `x : Fin 2` is the parameter `0` or `1`. -/
def arcPar (x : Fin 2) : Work.Smooth.Plane.ArcInterval :=
  ⟨(x : ℕ), by
    have hx : (x : ℕ) < 2 := x.isLt
    constructor
    · positivity
    · exact_mod_cast Nat.le_of_lt_succ hx⟩

/-- The endpoint index of a parameter which is `0` or `1`. -/
def arcIdx (y : Work.Smooth.Plane.ArcInterval) : Fin 2 := if (y : ℝ) = 0 then 0 else 1

/-- The endpoint map of a family of arcs, indexed by `Fin n × Fin 2`. -/
def endpt {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)) : Fin n × Fin 2 → R3 :=
  fun p => a p.1 (arcPar p.2)

@[simp] theorem endpt_apply {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3))
    (p : Fin n × Fin 2) : endpt a p = a p.1 (arcPar p.2) := rfl

@[simp] theorem arcPar_zero : arcPar 0 = (⟨0, by norm_num⟩ : Work.Smooth.Plane.ArcInterval) := by
  ext; simp [arcPar]

@[simp] theorem arcPar_one : arcPar 1 = (⟨1, by norm_num⟩ : Work.Smooth.Plane.ArcInterval) := by
  ext; simp [arcPar]

theorem arcPar_inj : Function.Injective arcPar := by
  intro x y h
  have h' : (x : ℕ) = (y : ℕ) := by
    have := congrArg (fun z : Work.Smooth.Plane.ArcInterval => (z : ℝ)) h
    simpa [arcPar] using this
  exact Fin.ext h'

theorem arcIdx_spec {y : Work.Smooth.Plane.ArcInterval} (hy : (y : ℝ) = 0 ∨ (y : ℝ) = 1) :
    arcPar (arcIdx y) = y := by
  rcases hy with hy | hy
  · have h1 : arcIdx y = 0 := by simp [arcIdx, hy]
    rw [h1]; ext; simp [arcPar, hy]
  · have h1 : arcIdx y = 1 := by simp [arcIdx, hy]
    rw [h1]; ext; simp [arcPar, hy]

/-- The sphere trace `Γ = F ∩ ∂PBox s c σ`. -/
abbrev Gset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Set R3 := P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s

/-- The slice `Σ = F ∩ D`. -/
abbrev Sigset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 := Work.BoxShrink.Core.sliceRegion P s c σ u

/-- The trace of the upper half-box wall on the surface. -/
abbrev Wset (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 := P.carrier ∩ wall s c σ u

/-- The parameter `0` of the unit interval. -/
abbrev pZero : Work.Smooth.Plane.ArcInterval := ⟨0, by norm_num⟩

/-- The parameter `1` of the unit interval. -/
abbrev pOne : Work.Smooth.Plane.ArcInterval := ⟨1, by norm_num⟩

/-- The `0`-endpoint of an arc of the family. -/
abbrev arcEnd0 {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)) (j : Fin n) : R3 :=
  a j pZero

/-- The `1`-endpoint of an arc of the family. -/
abbrev arcEnd1 {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)) (j : Fin n) : R3 :=
  a j pOne

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The sphere trace is the union of the curves of the slicing -/

theorem Gset_subset_iUnion
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)) :
    Gset P s c σ ⊆ ⋃ i : Sl.ι, Set.range (Sl.c i).γ := by
  rintro x ⟨hxc, hxs⟩
  obtain ⟨i, hi⟩ := Sl.covers (Work.InnermostDisk.constCurve P x hxc) (fun _ => hxs)
  exact Set.mem_iUnion.mpr ⟨i, hi ⟨0, rfl⟩⟩

theorem iUnion_subset_Gset
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)) :
    (⋃ i : Sl.ι, Set.range (Sl.c i).γ) ⊆ Gset P s c σ := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨t, rfl⟩ := hi
  exact ⟨(Sl.c i).mem t, Sl.mem i t⟩

theorem Gset_eq_iUnion
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)) :
    Gset P s c σ = ⋃ i : Sl.ι, Set.range (Sl.c i).γ :=
  Set.Subset.antisymm (Gset_subset_iUnion Sl) (iUnion_subset_Gset Sl)

/-! ## The endpoints of the arcs lie on the equator -/

theorem endpt_mem_closures {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hhend : ∀ j : Fin n,
      arcEnd0 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s ∧
        arcEnd1 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s)
    (p : Fin n × Fin 2) : endpt a p ∈ Gset P s c σ ∧ lvl σ (endpt a p) = c (σ 2) + u := by
  obtain ⟨j, x⟩ := p
  have hmem : endpt a (j, x) ∈ closure (Sigset P s c σ u) := ha j (arcPar x)
  have hcar : endpt a (j, x) ∈ P.carrier :=
    ((Work.CoreTopology.isClosed_carrier P).closure_subset_iff).mpr
      (fun z hz => hz.1.1) hmem
  have hplane : lvl σ (endpt a (j, x)) = c (σ 2) + u :=
    (Work.BoxShrink.isClosed_cutPlane c σ u).closure_subset_iff.mpr (fun z hz => hz.2) hmem
  have hsph : endpt a (j, x) ∈ Work.BoxShrink.Core.sphereSet c σ s := by
    rcases (show x = 0 ∨ x = 1 by omega) with h | h
    · have hx : arcPar x = pZero := by rw [h]; exact arcPar_zero
      show a j (arcPar x) ∈ Work.BoxShrink.Core.sphereSet c σ s
      rw [hx]
      exact (hhend j).1
    · have hx : arcPar x = pOne := by rw [h]; exact arcPar_one
      show a j (arcPar x) ∈ Work.BoxShrink.Core.sphereSet c σ s
      rw [hx]
      exact (hhend j).2
  exact ⟨⟨hcar, hsph⟩, hplane⟩

/-- The endpoints of the arcs are exactly the equator points, as a set. -/
theorem range_endpt_eq_equator {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hhend : ∀ j : Fin n,
      arcEnd0 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s ∧
        arcEnd1 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s)
    (heq : ∀ q ∈ P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s ∩
        Work.BoxShrink.Core.cutPlane c σ u,
      ∃ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        ((x : ℝ) = 0 ∨ (x : ℝ) = 1) ∧ a j x = q) :
    Set.range (endpt a) = Gset P s c σ ∩ Work.BoxShrink.Core.cutPlane c σ u := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, rfl⟩
    exact endpt_mem_closures ha hhend p
  · rintro x ⟨hxG, hxpl⟩
    obtain ⟨j, y, hy, hyx⟩ := heq x ⟨⟨hxG.1, hxG.2⟩, hxpl⟩
    refine ⟨(j, arcIdx y), ?_⟩
    rw [endpt_apply, arcIdx_spec hy, hyx]

theorem endpt_injective {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) :
    Function.Injective (endpt a) := by
  rintro ⟨j, x⟩ ⟨j', x'⟩ hp
  simp only [endpt_apply] at hp
  by_cases hjj : j = j'
  · subst hjj
    have hxx : x = x' := arcPar_inj (hinj j hp)
    simp [hxx]
  · exfalso
    have hmem : a j (arcPar x) ∈ Set.range (a j) ∩ Set.range (a j') :=
      ⟨⟨arcPar x, rfl⟩, ⟨arcPar x', hp.symm⟩⟩
    exact (Set.disjoint_left.mp (hdisj hjj)) hmem.1 hmem.2

/-! ## The trace of the wall -/

theorem Wset_eq :
    Wset P s c σ u =
      (Gset P s c σ ∩ {y : R3 | c (σ 2) + u ≤ lvl σ y}) ∪ Sigset P s c σ u := by
  rw [Wset, wall, Gset, Sigset, Work.BoxShrink.Core.sliceRegion_eq_carrier_inter_cutDisc]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, lvl,
    Work.BoxShrink.Core.mem_sphereSet, Work.BoxShrink.Core.mem_cutDisc]
  constructor
  · rintro ⟨hyc, hyw | hyw⟩
    · exact Or.inl ⟨⟨hyc, hyw.1⟩, hyw.2⟩
    · exact Or.inr ⟨hyc, hyw⟩
  · rintro (⟨⟨hyc, hys⟩, hyu⟩ | ⟨hyc, hyw⟩)
    · exact ⟨hyc, Or.inl ⟨hys, hyu⟩⟩
    · exact ⟨hyc, Or.inr hyw⟩

/-! ## Compactness and closedness of the wall trace -/

theorem isClosed_sphereSet :
    IsClosed (Work.BoxShrink.Core.sphereSet c σ s) := by
  rw [show Work.BoxShrink.Core.sphereSet c σ s =
      {y : R3 | Submission.boxNorm c σ y = s} from rfl]
  exact isClosed_eq (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const

theorem isCompact_carrier (P : Work.CoreTopology.ParamTorus) : IsCompact P.carrier := by
  have hK : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcarrier : P.carrier =
      (fun p : ℝ × ℝ => P.psi p.1 p.2) ''
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    apply Set.Subset.antisymm
    · rintro X ⟨⟨x, y⟩, rfl⟩
      exact ⟨(Work.CoreTopology.redParam x, Work.CoreTopology.redParam y),
        ⟨⟨Work.CoreTopology.redParam_mem x, Work.CoreTopology.redParam_mem y⟩,
          Work.CoreTopology.psi_redParam P x y⟩⟩
    · rintro X ⟨⟨x, y⟩, _, rfl⟩
      exact ⟨(x, y), rfl⟩
  rw [hcarrier]
  exact hK.image P.cont

/-- The sphere trace is closed. -/
theorem isClosed_Gset : IsClosed (Gset P s c σ) :=
  (Work.CoreTopology.isClosed_carrier P).inter isClosed_sphereSet

/-- The trace of the wall is closed: the only points of the closure of the slice which are not in
the slice are equator points, which are already in the sphere trace. -/
theorem isClosed_Wset : IsClosed (Wset P s c σ u) := by
  rw [Wset_eq]
  have hG : IsClosed (Gset P s c σ ∩ {y : R3 | c (σ 2) + u ≤ lvl σ y}) :=
    isClosed_Gset.inter
      (isClosed_le continuous_const (Work.Topology.SphereSlicing.continuous_coordR3 (σ 2)))
  refine isClosed_of_closure_subset ?_
  rw [closure_union, hG.closure_eq]
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · rcases Work.BoxShrink.closure_sliceRegion_subset P s c σ u hz with h | h
    · exact Or.inr h
    · refine Or.inl ⟨⟨?_, (Work.BoxShrink.Core.mem_sphereSet).mpr h.1⟩, ?_⟩
      · exact ((Work.CoreTopology.isClosed_carrier P).closure_subset_iff).mpr
          (fun w hw => hw.1.1) hz
      · show c (σ 2) + u ≤ lvl σ z
        rw [lvl, h.2]

theorem isCompact_Wset : IsCompact (Wset P s c σ u) :=
  (isCompact_carrier P).of_isClosed_subset isClosed_Wset (fun _ hy => hy.1)

/-! ## Elementary consequences of the arc hypotheses -/

/-- The membership criterion for the slice. -/
theorem mem_Sigset {y : R3} :
    y ∈ Sigset P s c σ u ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧ lvl σ y = c (σ 2) + u := by
  simp [Sigset, lvl, Work.BoxShrink.Core.mem_sliceRegion]

/-- The curves of the slicing other than a given one. -/
abbrev otherCurves (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s))
    (i₀ : Sl.ι) : Set R3 :=
  ⋃ i : {i : Sl.ι // i ≠ i₀}, Set.range (Sl.c i.1).γ

theorem mem_otherCurves {Sl : Work.InnermostDisk.SphereSlicing P
      (Work.BoxShrink.Core.sphereSet c σ s)} {i₀ : Sl.ι} {z : R3} :
    z ∈ otherCurves Sl i₀ ↔ ∃ i : {i : Sl.ι // i ≠ i₀}, z ∈ Set.range (Sl.c i.1).γ := by
  simp [otherCurves]

/-- The arcs of the family other than a given one. -/
abbrev otherArcs {n : ℕ} (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)) (j₀ : Fin n) : Set R3 :=
  ⋃ j : {j : Fin n // j ≠ j₀}, Set.range (a j.1)

theorem mem_otherArcs {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)} {j₀ : Fin n}
    {z : R3} :
    z ∈ otherArcs a j₀ ↔ ∃ j : {j : Fin n // j ≠ j₀}, z ∈ Set.range (a j.1) := by
  simp [otherArcs]

/-- An interior point of an arc of the family is not on the box sphere. -/
theorem not_mem_sphereSet_of_interior {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (hint : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1))
    {j : Fin n} {x : Work.Smooth.Plane.ArcInterval} (h0 : (x : ℝ) ≠ 0) (h1 : (x : ℝ) ≠ 1) :
    a j x ∉ Work.BoxShrink.Core.sphereSet c σ s := by
  intro h
  rcases hint j x h with h' | h'
  · exact h0 h'
  · exact h1 h'

/-- An interior point of an arc of the family lies in the slice. -/
theorem mem_Sigset_of_interior {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hint : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1))
    {j : Fin n} {x : Work.Smooth.Plane.ArcInterval} (h0 : (x : ℝ) ≠ 0) (h1 : (x : ℝ) ≠ 1) :
    a j x ∈ Sigset P s c σ u := by
  by_contra hcon
  have h2 : a j x ∈ closure (Work.BoxShrink.Core.sliceRegion P s c σ u) \
      Work.BoxShrink.Core.sliceRegion P s c σ u := ⟨ha j x, hcon⟩
  rcases Work.BoxShrink.closure_sliceRegion_subset P s c σ u h2.1 with h | h
  · exact absurd h hcon
  · exact not_mem_sphereSet_of_interior hint h0 h1 ((Work.BoxShrink.Core.mem_sphereSet).mpr h.1)

/-- The interior points of an arc: the range without the two endpoints is the image of `(0,1)`. -/
theorem range_sdiff_endpoints {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (j : Fin n) (hinj : Function.Injective (a j)) :
    Set.range (a j) \ ({arcEnd0 a j, arcEnd1 a j} : Set R3) =
      a j '' {x : Work.Smooth.Plane.ArcInterval | (x : ℝ) ∈ Set.Ioo 0 1} := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x, rfl⟩, hz⟩
    have hx0 : (x : ℝ) ≠ 0 := fun h => hz (Or.inl (congrArg (a j) (Subtype.ext h)))
    have hx1 : (x : ℝ) ≠ 1 := fun h => hz (Or.inr (congrArg (a j) (Subtype.ext h)))
    exact ⟨x, ⟨lt_of_le_of_ne x.2.1 (Ne.symm hx0), lt_of_le_of_ne x.2.2 hx1⟩, rfl⟩
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      have h' := congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ)) (hinj h)
      simp at h'
      exact absurd h' (ne_of_gt hx.1)
    · intro h
      have h' := congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ)) (hinj h)
      simp at h'
      exact absurd h' (ne_of_lt hx.2)

/-- The trace of a locally Euclidean set on an open set is locally Euclidean. -/
theorem IsLocallyEuclidean.inter_isOpen {Z S : Set R3} (h : IsLocallyEuclidean Z)
    (hS : IsOpen S) : IsLocallyEuclidean (S ∩ Z) :=
  h.of_isOpenIn Set.inter_subset_right (by
    show IsOpen ((Subtype.val ⁻¹' (S ∩ Z)) : Set Z)
    rw [show (Subtype.val ⁻¹' (S ∩ Z) : Set Z) = Subtype.val ⁻¹' S from by
      ext z; exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩]
    exact hS.preimage continuous_subtype_val)

/-! ## The local models -/

/-- **A point of the sphere trace above the level `u`.**  Locally the wall trace is the sphere
trace, which is locally an arc because the curve of the slicing is a `2π`-periodic injective
parametrisation of a circle. -/
theorem localModel_trace
    (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)) {y : R3}
    (hy : y ∈ Gset P s c σ) (hyu : c (σ 2) + u < lvl σ y) :
    ∃ O : Set R3, IsOpen O ∧ y ∈ O ∧
      IsLocallyEuclidean
        (O ∩ (Gset P s c σ ∩ {z : R3 | c (σ 2) + u < lvl σ z})) := by
  classical
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (Gset_subset_iUnion Sl hy)
  have hAclosed : IsClosed (otherCurves Sl i₀) := by
    rw [otherCurves]
    exact isClosed_iUnion_of_finite fun i =>
      Work.InnermostDisk.isClosed_range_closedCurve (Sl.c i.1)
  have hOopen : IsOpen ((otherCurves Sl i₀)ᶜ ∩ {z : R3 | c (σ 2) + u < lvl σ z}) :=
    hAclosed.isOpen_compl.inter
      (isOpen_lt continuous_const (Work.Topology.SphereSlicing.continuous_coordR3 (σ 2)))
  have hyO : y ∈ (otherCurves Sl i₀)ᶜ ∩ {z : R3 | c (σ 2) + u < lvl σ z} := by
    refine ⟨?_, hyu⟩
    intro h
    obtain ⟨i, hi⟩ := mem_otherCurves.mp h
    have : i.1 = i₀ := by
      by_contra hne
      exact (Set.disjoint_left.mp (Sl.disjoint hne)) hi hi₀
    exact i.2 this
  refine ⟨(otherCurves Sl i₀)ᶜ ∩ {z : R3 | c (σ 2) + u < lvl σ z}, hOopen, hyO, ?_⟩
  have hEq : ((otherCurves Sl i₀)ᶜ ∩ {z : R3 | c (σ 2) + u < lvl σ z}) ∩
        (Gset P s c σ ∩ {z : R3 | c (σ 2) + u < lvl σ z}) =
      ((otherCurves Sl i₀)ᶜ ∩ {z : R3 | c (σ 2) + u < lvl σ z}) ∩ Set.range (Sl.c i₀).γ := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨hzA, hzu⟩, hzG, -⟩
      have hzun : z ∈ ⋃ i : Sl.ι, Set.range (Sl.c i).γ := Gset_subset_iUnion Sl hzG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzun
      have hii : i = i₀ := by
        by_contra hne
        exact hzA (mem_otherCurves.mpr ⟨⟨i, hne⟩, hi⟩)
      exact ⟨⟨hzA, hzu⟩, hii ▸ hi⟩
    · rintro z ⟨⟨hzA, hzu⟩, hzi⟩
      exact ⟨⟨hzA, hzu⟩, iUnion_subset_Gset Sl (Set.mem_iUnion.mpr ⟨i₀, hzi⟩), hzu⟩
  rw [hEq]
  exact IsLocallyEuclidean.inter_isOpen
    (localEuclidean_range_of_periodic_injOn (Sl.c i₀).cont (Sl.c i₀).periodic (Sl.simple i₀))
    hOopen

/-- **A point of the slice.**  Locally the wall trace is the slice, which near an interior point of
a slice arc is the image of an open interval under the injective arc parametrisation. -/
theorem localModel_slice {n : ℕ} {a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)}
    (hinj : ∀ j : Fin n, Function.Injective (a j))
    (ha : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ closure (Sigset P s c σ u))
    (hdisj : Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j')))
    (hcover : closure (Sigset P s c σ u) ⊆ ⋃ j, Set.range (a j))
    (hint : ∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
      a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1))
    (hhend : ∀ j : Fin n,
      arcEnd0 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s ∧
        arcEnd1 a j ∈
          Work.BoxShrink.Core.sphereSet c σ s)
    {y : R3} (hy : y ∈ Sigset P s c σ u) :
    ∃ O : Set R3, IsOpen O ∧ y ∈ O ∧ IsLocallyEuclidean (O ∩ Sigset P s c σ u) := by
  classical
  obtain ⟨j₀, x₀, hx₀⟩ : ∃ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval), a j x = y := by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (subset_closure hy))
    obtain ⟨x, hx⟩ := hj
    exact ⟨j, x, hx⟩
  have hnlt : Submission.boxNorm c σ y < s :=
    (Submission.mem_PBox_iff s c σ y).mp (mem_Sigset.mp hy).2.1
  have hx₀ne : (x₀ : ℝ) ≠ 0 ∧ (x₀ : ℝ) ≠ 1 := by
    constructor
    · intro h
      have hx : x₀ = pZero := Subtype.ext h
      have h1 : y ∈ Work.BoxShrink.Core.sphereSet c σ s := by
        rw [← hx₀, hx]
        exact (hhend j₀).1
      rw [Work.BoxShrink.Core.mem_sphereSet] at h1
      exact absurd h1 (ne_of_lt hnlt)
    · intro h
      have hx : x₀ = pOne := Subtype.ext h
      have h1 : y ∈ Work.BoxShrink.Core.sphereSet c σ s := by
        rw [← hx₀, hx]
        exact (hhend j₀).2
      rw [Work.BoxShrink.Core.mem_sphereSet] at h1
      exact absurd h1 (ne_of_lt hnlt)
  have hBclosed : IsClosed (otherArcs a j₀) := by
    rw [otherArcs]
    exact isClosed_iUnion_of_finite fun j => (isCompact_range (a j.1).continuous).isClosed
  have hOopen : IsOpen ((otherArcs a j₀)ᶜ ∩ {z : R3 | Submission.boxNorm c σ z < s} ∩
      {arcEnd0 a j₀}ᶜ ∩
      {arcEnd1 a j₀}ᶜ) :=
    ((hBclosed.isOpen_compl.inter
        (isOpen_lt (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const)).inter
      isClosed_singleton.isOpen_compl).inter isClosed_singleton.isOpen_compl
  have hyO : y ∈ (otherArcs a j₀)ᶜ ∩ {z : R3 | Submission.boxNorm c σ z < s} ∩
      {arcEnd0 a j₀}ᶜ ∩
      {arcEnd1 a j₀}ᶜ := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rintro h
      obtain ⟨w, hw⟩ := mem_otherArcs.mp h
      exact (Set.disjoint_left.mp (hdisj w.2)) hw ⟨x₀, hx₀⟩
    · exact hnlt
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hx : x₀ = (⟨0, by norm_num⟩ : Work.Smooth.Plane.ArcInterval) := (hinj j₀) (hx₀.trans h)
      exact hx₀ne.1 (by simpa using congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ)) hx)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have hx : x₀ = (⟨1, by norm_num⟩ : Work.Smooth.Plane.ArcInterval) := (hinj j₀) (hx₀.trans h)
      exact hx₀ne.2 (by simpa using congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ)) hx)
  refine ⟨_, hOopen, hyO, ?_⟩
  have hEq : ((otherArcs a j₀)ᶜ ∩ {z : R3 | Submission.boxNorm c σ z < s} ∩
        {arcEnd0 a j₀}ᶜ ∩
        {arcEnd1 a j₀}ᶜ) ∩ Sigset P s c σ u =
      a j₀ '' {x : Work.Smooth.Plane.ArcInterval | (x : ℝ) ∈ Set.Ioo 0 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨⟨⟨hzB, hzO⟩, hz0⟩, hz1⟩, hzSig⟩
      have hzrange : z ∈ Set.range (a j₀) := by
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover (subset_closure hzSig))
        have hjj : j = j₀ := by
          by_contra hne
          exact hzB (mem_otherArcs.mpr ⟨⟨j, hne⟩, hj⟩)
        subst hjj
        exact hj
      have hznot : z ∉ ({arcEnd0 a j₀, arcEnd1 a j₀} : Set R3) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hz0, hz1⟩
      exact (range_sdiff_endpoints j₀ (hinj j₀)) ▸ ⟨hzrange, hznot⟩
    · rintro z ⟨x, hx, rfl⟩
      have hSig : a j₀ x ∈ Sigset P s c σ u :=
        mem_Sigset_of_interior ha hint (ne_of_gt hx.1) (ne_of_lt hx.2)
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hSig⟩
      · rintro h
        obtain ⟨w, hw⟩ := mem_otherArcs.mp h
        exact (Set.disjoint_left.mp (hdisj w.2)) hw ⟨x, rfl⟩
      · exact (Submission.mem_PBox_iff s c σ (a j₀ x)).mp (mem_Sigset.mp hSig).2.1
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        exact (ne_of_gt hx.1) (congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ))
          ((hinj j₀) h))
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        exact (ne_of_lt hx.2) (congrArg (fun t : Work.Smooth.Plane.ArcInterval => (t : ℝ))
          ((hinj j₀) h))
  rw [hEq]
  exact localEuclidean_image_Ioo (hinj j₀)

/-! ## Periodic curves: parameters, injectivity, and isolated level crossings -/

/-- The reduction of a parameter to the interval `[0, 2π)` does not change the value of a
`2π`-periodic curve. -/
theorem gamma_fract_mul {γ : ℝ → R3} (hper : Function.Periodic γ (2 * Real.pi)) (s : ℝ) :
    γ (2 * Real.pi * Int.fract (s / (2 * Real.pi))) = γ s := by
  have h := Int.floor_add_fract (s / (2 * Real.pi))
  have hs : s = 2 * Real.pi * Int.fract (s / (2 * Real.pi)) +
      (⌊s / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) := by
    have h2 : 2 * Real.pi * ((⌊s / (2 * Real.pi)⌋ : ℝ) +
        Int.fract (s / (2 * Real.pi))) = s := by
      rw [h]; field_simp
    conv_lhs => rw [← h2]
    ring
  conv_rhs => rw [hs]
  exact ((hper.int_mul ⌊s / (2 * Real.pi)⌋)
    (2 * Real.pi * Int.fract (s / (2 * Real.pi)))).symm

/-- Equal fractional parts modulo `2π` differ by an integral multiple of `2π`. -/
theorem sub_eq_int_mul_of_fract_eq {t t' : ℝ}
    (h : Int.fract (t / (2 * Real.pi)) = Int.fract (t' / (2 * Real.pi))) :
    ∃ k : ℤ, t - t' = k * (2 * Real.pi) := by
  have h2pi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have h3 : t = 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℝ) +
      Int.fract (t / (2 * Real.pi))) := by
    have h := Int.floor_add_fract (t / (2 * Real.pi))
    have h2 : 2 * Real.pi * ((⌊t / (2 * Real.pi)⌋ : ℝ) +
        Int.fract (t / (2 * Real.pi))) = t := by
      rw [h]; field_simp
    exact h2.symm
  have h4 : t' = 2 * Real.pi * ((⌊t' / (2 * Real.pi)⌋ : ℝ) +
      Int.fract (t' / (2 * Real.pi))) := by
    have h' := Int.floor_add_fract (t' / (2 * Real.pi))
    have h2 : 2 * Real.pi * ((⌊t' / (2 * Real.pi)⌋ : ℝ) +
        Int.fract (t' / (2 * Real.pi))) = t' := by
      rw [h']; field_simp
    exact h2.symm
  refine ⟨⌊t / (2 * Real.pi)⌋ - ⌊t' / (2 * Real.pi)⌋, ?_⟩
  have hdiff : t - t' = 2 * Real.pi *
      ((⌊t / (2 * Real.pi)⌋ : ℝ) - (⌊t' / (2 * Real.pi)⌋ : ℝ)) := by
    conv_lhs => rw [h3, h4]
    rw [h]
    ring
  have hcast : (((⌊t / (2 * Real.pi)⌋ - ⌊t' / (2 * Real.pi)⌋ : ℤ) : ℝ)) =
      (⌊t / (2 * Real.pi)⌋ : ℝ) - (⌊t' / (2 * Real.pi)⌋ : ℝ) := by
    push_cast; ring
  rw [hcast]
  linarith

/-- Two parameters of a `2π`-periodic injective closed curve giving the same point differ by a
multiple of `2π`. -/
theorem eq_add_int_mul_of_periodic {γ : ℝ → R3} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {t t' : ℝ} (h : γ t = γ t') :
    ∃ k : ℤ, t = t' + k * (2 * Real.pi) := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfr : Int.fract (t / (2 * Real.pi)) = Int.fract (t' / (2 * Real.pi)) := by
    have hm1 : 2 * Real.pi * Int.fract (t / (2 * Real.pi)) ∈ Set.Ico 0 (2 * Real.pi) := by
      refine ⟨?_, ?_⟩
      · positivity
      · have h1 := Int.fract_lt_one (t / (2 * Real.pi))
        calc 2 * Real.pi * Int.fract (t / (2 * Real.pi)) < 2 * Real.pi * 1 :=
              mul_lt_mul_of_pos_left h1 h2pi
          _ = 2 * Real.pi := mul_one _
    have hm2 : 2 * Real.pi * Int.fract (t' / (2 * Real.pi)) ∈ Set.Ico 0 (2 * Real.pi) := by
      refine ⟨?_, ?_⟩
      · positivity
      · have h1 := Int.fract_lt_one (t' / (2 * Real.pi))
        calc 2 * Real.pi * Int.fract (t' / (2 * Real.pi)) < 2 * Real.pi * 1 :=
              mul_lt_mul_of_pos_left h1 h2pi
          _ = 2 * Real.pi := mul_one _
    have heq : 2 * Real.pi * Int.fract (t / (2 * Real.pi)) =
        2 * Real.pi * Int.fract (t' / (2 * Real.pi)) :=
      hinj hm1 hm2 (by rw [gamma_fract_mul hper t, gamma_fract_mul hper t', h])
    nlinarith
  obtain ⟨k, hk⟩ := sub_eq_int_mul_of_fract_eq hfr
  refine ⟨k, ?_⟩
  linarith

/-- A `2π`-periodic curve injective on a fundamental period is injective on any interval of length
at most `2π`. -/
theorem eq_of_abs_sub_lt {γ : ℝ → R3} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {t t' : ℝ}
    (h : |t - t'| < 2 * Real.pi) (heq : γ t = γ t') : t = t' := by
  obtain ⟨k, hk⟩ := eq_add_int_mul_of_periodic hper hinj heq
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmul : (k : ℝ) * (2 * Real.pi) = t - t' := by linarith
  have habs : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    have h' : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by rw [hmul]; exact h
    rwa [abs_mul, abs_of_pos h2pi] at h'
  have hk0 : k = 0 := by
    have h1 : |(k : ℝ)| < 1 := by nlinarith
    rw [abs_lt] at h1
    have h2 : (-1 : ℤ) < k := by exact_mod_cast h1.1
    have h3 : k < (1 : ℤ) := by exact_mod_cast h1.2
    omega
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- **The level crossings of a periodic injective curve are isolated.**  If `Z` is the level set
`{t | L (γ t) = a}` of a function along a `2π`-periodic injective curve, and only finitely many
parameters in a fundamental period are in `Z`, then every point of `Z` is isolated in `Z`. -/
theorem exists_isolated_levelSet {γ : ℝ → R3} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) (L : R3 → ℝ) (a t₀ : ℝ)
    (hfin : ({t : ℝ | L (γ t) = a} ∩ Set.Ico 0 (2 * Real.pi)).Finite)
    (ht₀ : L (γ t₀) = a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, L (γ t) = a → |t - t₀| < δ → t = t₀ := by
  classical
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlocfin : ({t : ℝ | L (γ t) = a} ∩ Set.Ioo (t₀ - Real.pi) (t₀ + Real.pi)).Finite := by
    refine Set.Finite.of_injOn (f := fun t : ℝ => 2 * Real.pi * Int.fract (t / (2 * Real.pi)))
      (t := {t : ℝ | L (γ t) = a} ∩ Set.Ico 0 (2 * Real.pi)) ?_ ?_ hfin
    · intro t ht
      refine ⟨?_, ?_⟩
      · show L (γ (2 * Real.pi * Int.fract (t / (2 * Real.pi)))) = a
        rw [gamma_fract_mul hper t]
        exact ht.1
      · refine ⟨?_, ?_⟩
        · positivity
        · have h1 := Int.fract_lt_one (t / (2 * Real.pi))
          calc 2 * Real.pi * Int.fract (t / (2 * Real.pi)) < 2 * Real.pi * 1 :=
                mul_lt_mul_of_pos_left h1 h2pi
            _ = 2 * Real.pi := mul_one _
    · intro t ht t' ht' h
      have hfr : Int.fract (t / (2 * Real.pi)) = Int.fract (t' / (2 * Real.pi)) := by
        have := h; nlinarith
      obtain ⟨k, hk⟩ := sub_eq_int_mul_of_fract_eq hfr
      have hlt : |t - t'| < 2 * Real.pi := by
        rw [abs_lt]
        constructor <;> linarith [ht.2.1, ht.2.2, ht'.2.1, ht'.2.2]
      rw [hk, abs_mul, abs_of_pos h2pi] at hlt
      have hk0 : k = 0 := by
        have h1 : |(k : ℝ)| < 1 := by nlinarith
        rw [abs_lt] at h1
        have h2 : (-1 : ℤ) < k := by exact_mod_cast h1.1
        have h3 : k < (1 : ℤ) := by exact_mod_cast h1.2
        omega
      rw [hk0] at hk
      push_cast at hk
      linarith
  set S : Finset ℝ := (hlocfin.toFinset).filter (fun t => t ≠ t₀) with hS
  set D : Finset ℝ := S.image (fun t => |t - t₀|) with hD
  have hDlt : ∀ d ∈ D, d < Real.pi := by
    intro d hd
    rw [hD] at hd
    obtain ⟨t, htS, ht⟩ := Finset.mem_image.mp hd
    have htmem : t ∈ {t : ℝ | L (γ t) = a} ∩ Set.Ioo (t₀ - Real.pi) (t₀ + Real.pi) :=
      (hlocfin.mem_toFinset).mp (Finset.mem_filter.mp htS).1
    have h2 : t ∈ Set.Ioo (t₀ - Real.pi) (t₀ + Real.pi) := htmem.2
    rw [Set.mem_Ioo] at h2
    rw [← ht, abs_lt]
    constructor <;> linarith [h2.1, h2.2]
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    rw [hD] at hd
    obtain ⟨t, htS, ht⟩ := Finset.mem_image.mp hd
    have htne : t ≠ t₀ := (Finset.mem_filter.mp htS).2
    rw [← ht]
    exact abs_pos.mpr (sub_ne_zero.mpr htne)
  by_cases hDne : D.Nonempty
  · refine ⟨D.min' hDne, ?_, ?_⟩
    · have hminmem := Finset.min'_mem D hDne
      linarith [hDpos (D.min' hDne) hminmem]
    · intro t htZ hlt
      by_contra hne
      have hltπ : D.min' hDne < Real.pi := hDlt (D.min' hDne) (Finset.min'_mem D hDne)
      have htIoo : t ∈ Set.Ioo (t₀ - Real.pi) (t₀ + Real.pi) := by
        have hlt' : |t - t₀| < Real.pi := by linarith
        rw [abs_lt] at hlt'
        rw [Set.mem_Ioo]
        exact ⟨by linarith [hlt'.1], by linarith [hlt'.2]⟩
      have hdmem : |t - t₀| ∈ D := by
        rw [hD]
        refine Finset.mem_image.mpr ⟨t, ?_, rfl⟩
        rw [hS]
        exact Finset.mem_filter.mpr ⟨(hlocfin.mem_toFinset).mpr ⟨htZ, htIoo⟩, hne⟩
      have hmin : D.min' hDne ≤ |t - t₀| := Finset.min'_le D _ hdmem
      linarith
  · refine ⟨Real.pi / 2, ?_, ?_⟩
    · positivity
    · intro t htZ hlt
      by_contra hne
      have htIoo : t ∈ Set.Ioo (t₀ - Real.pi) (t₀ + Real.pi) := by
        have hlt' : |t - t₀| < Real.pi / 2 := hlt
        rw [abs_lt] at hlt'
        rw [Set.mem_Ioo]
        exact ⟨by linarith [hlt'.1], by linarith [hlt'.2]⟩
      have hdmem : |t - t₀| ∈ D := by
        rw [hD]
        refine Finset.mem_image.mpr ⟨t, ?_, rfl⟩
        rw [hS]
        exact Finset.mem_filter.mpr ⟨(hlocfin.mem_toFinset).mpr ⟨htZ, htIoo⟩, hne⟩
      exact hDne ⟨_, hdmem⟩


/-!
## The remaining local model: a plan for `Work.EpsW.localModel_endpoint`

The one local model not proved in this file is the neighbourhood of an *equator point*
`e = endpt a p`.  The ingredients, in the order in which they are used:

1. **`e` is a point of `Gset` with `lvl σ e = c (σ 2) + u`** (`endpt_mem_closures`), so it lies on
   a sphere-trace curve: `obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (Gset_subset_iUnion Sl heG)`, and
   by `gamma_fract_mul` one may take the parameter `t₀ ∈ Set.Ico 0 (2 * Real.pi)` of `e`, i.e.
   `(Sl.c i₀).γ t₀ = e`.

2. **The level crossings of the curve `Sl.c i₀` are exactly the equator points.**  For
   `t ∈ {t | lvl σ ((Sl.c i₀).γ t) = c (σ 2) + u} ∩ Set.Ico 0 (2 * Real.pi)` the point
   `(Sl.c i₀).γ t` lies in `Gset` and in the cutting plane, hence — by `heq` — in
   `Set.range (endpt a)`, which is finite (`Set.finite_range`), and `(Sl.c i₀).γ` is injective on
   `Set.Ico 0 (2 * Real.pi)` (`Sl.simple i₀`).  So `Set.Finite.of_injOn` gives the finiteness
   hypothesis of `exists_isolated_levelSet`, which produces `δ₁ > 0` such that
   `∀ t, lvl σ ((Sl.c i₀).γ t) = c (σ 2) + u → |t - t₀| < δ₁ → t = t₀`.
   Put `δ := δ₁ / 2`.

3. **The up side.**  Since there are no crossings in `(t₀ - δ₁, t₀ + δ₁)` other than `t₀`, the
   level `lvl σ ∘ (Sl.c i₀).γ` has constant sign on each of the two halves; the sign is constant on
   an interval without zeros (`sign_constant_of_no_zero`, using `intermediate_value_Icc`).  The two
   signs are opposite: `hcross i₀ t₀ _` provides points of level `> c (σ 2) + u` and
   `< c (σ 2) + u` within `δ` of `t₀`, and they cannot lie on the same side of `t₀` (a sign change
   on one side would produce a crossing).  So with `d := if upRight then δ else -δ` the map
   `f s := (Sl.c i₀).γ (t₀ + (1 - s) * d)` is an injective arc ending at `e` whose image is exactly
   the *up* half of the trace (level `≥ c (σ 2) + u`, with equality only at `e`).

4. **The slice half.**  With `e = a p.1 (arcPar p.2)` the map
   `g s := a p.1 (if (p.2 : ℕ) = 0 then s / 2 else 1 - s / 2)` is an injective arc starting at `e`;
   `range g` is the half of the slice arc `a p.1` from `e`.  Note `Set.range f ∩ Set.range g = {e}`:
   `range f ⊆ Gset`, `range g ⊆ Set.range (a p.1)`, and `Set.range (a p.1) ∩ Gset ⊆ {arcEnd0 a p.1,
   arcEnd1 a p.1}` by `hint`; the other endpoint is not in `range f`, since it would then be an
   equator point at distance `< δ₁` from `t₀`.

5. **`Work.EpsW.localArc_gluedPair`** applied to `f`, `g` (with `f 1 = g 0 = e`) gives an open
   `O' ∋ e` with `IsLocallyEuclidean (O' ∩ (Set.range f ∪ Set.range g))`.

6. **The avoidances.**  Take `O` to be the intersection of `O'` with
   `(otherArcs a p.1)ᶜ`, `(otherCurves Sl i₀)ᶜ`,
   the open set of `exists_isOpen_localModel_periodic` for `(Sl.c i₀).γ` at `t₀` with radius `δ`,
   the open set of `exists_isOpen_localModel_arc` for `a p.1` at `arcPar p.2`, and the complement of
   the `1`-side of `Curve`/`Arc`, to prove `O ∩ Wset P s c σ u = O ∩ (Set.range f ∪ Set.range g)`
   using `Wset_eq`; the conclusion follows from `IsLocallyEuclidean.inter_isOpen`.
-/

end

end Work.EpsW
