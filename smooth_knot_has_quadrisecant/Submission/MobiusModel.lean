import Mathlib
import Submission.ChordModel

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The quotient chord model `MobiusModel = ChordData / flip`

`ChordData = {q : Circle × ℝ | q.2 ∈ (-1,1)}` with the flip
`chordFlip (n,d) = (-n,-d)` describes the same chord twice.  This module
quotients by the flip orbit and proves that the slide of `ChordModel.lean`
descends to a **deformation retraction of the model Möbius band onto its core
circle**:

    MobiusCoreRetract :
      ∃ ρ : MobiusModel × Icc 0 1 → MobiusModel, Continuous ρ ∧
        ρ (c, 0) = c ∧ ρ (c, 1) ∈ range mobiusCore ∧ ρ (mobiusCore n, t) = mobiusCore n

where `mobiusCore n = [(n, 0)]` is the class of the diameter
`{z : ℂ | z·n = 0}` (chords through the origin).  The core is a circle:
`mobiusCore n = mobiusCore m ↔ n = m ∨ n = -m` (the antipodal identification
of the normal direction).

Structure (mirroring `Submission/SecantSpace.lean`): the flip-orbit setoid
`chordSetoid` with class API; the quotient map
`mobiusMk : ChordData → MobiusModel` is an *open quotient map*
(`isOpenQuotientMap_mobiusMk`: the saturation `U ∪ chordFlip '' U` of an open
set is open, since the flip is a continuous involution), so
`IsOpenQuotientMap.prodMap` makes `ChordData × I → MobiusModel × I` a quotient
map and `IsOpenQuotientMap.continuous_comp_iff` descends the continuity of
the representative-level slide `chordSlideAt` to `mobiusSlide`.  The endpoint
and fixed-point properties are then read off `ChordModel`'s representative
lemmas.  -/

/-- Two chord data are equivalent when they describe the same chord: equal,
or flipped. -/
def chordRel (q q' : ChordData) : Prop := q = q' ∨ chordFlip q = q'

lemma chordRel_refl (q : ChordData) : chordRel q q := Or.inl rfl

lemma chordRel_symm {q q' : ChordData} (h : chordRel q q') : chordRel q' q := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [← h]
    exact chordFlip_chordFlip q

lemma chordRel_trans {q q' q'' : ChordData} (h : chordRel q q') (h' : chordRel q' q'') :
    chordRel q q'' := by
  rcases h with h | h
  · rcases h' with h' | h'
    · exact Or.inl (h.trans h')
    · right
      rw [h]
      exact h'
  · rcases h' with h' | h'
    · right
      rw [← h']
      exact h
    · left
      calc q = chordFlip (chordFlip q) := (chordFlip_chordFlip q).symm
        _ = chordFlip q' := congrArg chordFlip h
        _ = q'' := h'

/-- The flip-orbit equivalence relation on chord data. -/
instance chordSetoid : Setoid ChordData where
  r := chordRel
  iseqv := ⟨chordRel_refl, @chordRel_symm, @chordRel_trans⟩

/-- The model open Möbius band: chords of the unit circle, up to the two
ordered descriptions `(n,d)` and `(-n,-d)` of the same chord. -/
abbrev MobiusModel := Quotient chordSetoid

/-- The quotient map from chord data to the model Möbius band. -/
abbrev mobiusMk (q : ChordData) : MobiusModel := ⟦q⟧

/-- Two chord data represent the same chord iff they are equal or flipped. -/
lemma mobiusMk_eq_iff (q q' : ChordData) :
    mobiusMk q = mobiusMk q' ↔ chordRel q q' := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Flipping a chord description does not change the chord. -/
@[simp]
lemma mobiusMk_flip (q : ChordData) : mobiusMk (chordFlip q) = mobiusMk q := by
  unfold mobiusMk
  exact Quotient.sound (Or.inr (chordFlip_chordFlip q))

/-- The quotient map is continuous. -/
lemma continuous_mobiusMk : Continuous mobiusMk := by
  exact continuous_quot_mk

/-- The preimage of the image of a set of chord data under the quotient map is
its flip-saturation. -/
lemma mobiusMk_preimage_image (U : Set ChordData) :
    mobiusMk ⁻¹' (mobiusMk '' U) = U ∪ chordFlip '' U := by
  ext q
  constructor
  · rintro ⟨u, hu, hqu⟩
    have hrel := (mobiusMk_eq_iff q u).mp hqu.symm
    rcases hrel with hrel | hrel
    · left
      simpa [hrel] using hu
    · right
      refine ⟨u, hu, ?_⟩
      have h1 : chordFlip u = q := by simpa using congrArg chordFlip hrel.symm
      exact h1
  · rintro (hq | hq)
    · exact ⟨q, hq, rfl⟩
    · rcases hq with ⟨u, hu, hqu⟩
      exact ⟨u, hu, by
        rw [← hqu]
        exact (mobiusMk_flip u).symm⟩

/-- The image of a set of chord data under the flip is its preimage (the flip
is an involution). -/
lemma chordFlip_image_eq_preimage (U : Set ChordData) :
    chordFlip '' U = chordFlip ⁻¹' U := by
  ext q
  constructor
  · rintro ⟨u, hu, hqu⟩
    have this : chordFlip q = u := by
      calc chordFlip q = chordFlip (chordFlip u) := by rw [hqu]
        _ = u := chordFlip_chordFlip u
    simpa [this] using hu
  · intro hq
    refine ⟨chordFlip q, ?_, ?_⟩
    · simpa using hq
    · simp

/-- The flip-quotient map onto `MobiusModel` is an open map. -/
lemma isOpenMap_mobiusMk : IsOpenMap mobiusMk := by
  intro U hU
  have hpre : IsOpen (mobiusMk ⁻¹' (mobiusMk '' U)) := by
    rw [mobiusMk_preimage_image]
    have hflip : IsOpen (chordFlip '' U) := by
      simpa [chordFlip_image_eq_preimage] using (hU.preimage continuous_chordFlip)
    exact hU.union hflip
  change @IsOpen MobiusModel
    (TopologicalSpace.coinduced (Quotient.mk' : ChordData → MobiusModel) inferInstance)
    (mobiusMk '' U)
  exact hpre

/-- The flip-quotient map is an open quotient map. -/
lemma isOpenQuotientMap_mobiusMk : IsOpenQuotientMap mobiusMk where
  surjective := by
    intro c
    refine Quotient.inductionOn c ?_
    intro q
    exact ⟨q, rfl⟩
  continuous := continuous_mobiusMk
  isOpenMap := isOpenMap_mobiusMk

/-- The diameter chord data with normal `n` (the model core circle). -/
abbrev coreChord (n : Circle) : ChordData :=
  ⟨(n, 0), by change (-1 : ℝ) < (0 : ℝ) ∧ (0 : ℝ) < 1; norm_num⟩

/-- The model core circle: chords through the origin (diameters), as
classes. -/
abbrev mobiusCore (n : Circle) : MobiusModel := mobiusMk (coreChord n)

/-- Flipping the normal negates the core point, but the class is unchanged
(a diameter has no orientation). -/
lemma mobiusCore_neg (n : Circle) : mobiusCore (-n) = mobiusCore n := by
  apply Quotient.sound
  right
  -- chordFlip (coreChord n) = coreChord (-n)
  apply Subtype.ext
  ext <;> simp [chordFlip, chordDataFlip]

/-- Two diameters determine the same chord exactly when their normals agree
up to sign. -/
lemma chordRel_coreChord_iff (n m : Circle) :
    chordRel (coreChord n) (coreChord m) ↔ n = m ∨ n = -m := by
  constructor
  · intro h
    rcases h with h | h
    · left
      exact congrArg (fun q : ChordData => q.1.1) h
    · right
      have hf : (chordFlip (coreChord n)).1.1 = m :=
        congrArg (fun q : ChordData => q.1.1) h
      have hn : -n = m := by simpa [chordFlip, chordDataFlip] using hf
      have hm : n = -m := by
        have hneg := congrArg (fun x : Circle => -x) hn
        simpa using hneg
      exact hm
  · intro h
    rcases h with h | h
    · left
      exact congrArg coreChord h
    · right
      -- chordFlip (coreChord n) = coreChord m
      apply Subtype.ext
      ext <;> simp [chordFlip, chordDataFlip, h]

/-- Two diameters determine the same chord exactly when their normals agree
up to sign (class form). -/
lemma mobiusCore_eq_iff (n m : Circle) :
    mobiusCore n = mobiusCore m ↔ n = m ∨ n = -m := by
  change mobiusMk (coreChord n) = mobiusMk (coreChord m) ↔ n = m ∨ n = -m
  constructor
  · intro h
    exact (chordRel_coreChord_iff n m).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((chordRel_coreChord_iff n m).mpr h)

/-- The slide at a fixed time, descended to the model: `[(n, d)] ↦
[(n, (1-t)·d)]`. -/
abbrev mobiusSlideSection (t : Set.Icc (0 : ℝ) 1) (c : MobiusModel) : MobiusModel :=
  Quotient.lift (fun q : ChordData => mobiusMk (chordSlideAt t q)) (by
    intro q q' hrel
    rcases hrel with hrel | hrel
    · rw [hrel]
    · have hs : chordSlideAt t q' = chordFlip (chordSlideAt t q) := by
        rw [← hrel, chordSlideAt_flip]
      rw [hs]
      exact (mobiusMk_flip (chordSlideAt t q)).symm) c

/-- Sliding a chord toward the parallel diameter at time `t` (descended to
the model). -/
abbrev mobiusSlide (c : MobiusModel) (t : Set.Icc (0 : ℝ) 1) : MobiusModel :=
  mobiusSlideSection t c

/-- The representative-level slide computes on classes. -/
@[simp]
lemma mobiusSlide_mk (q : ChordData) (t : Set.Icc (0 : ℝ) 1) :
    mobiusSlide (⟦q⟧ : MobiusModel) t = (⟦chordSlideAt t q⟧ : MobiusModel) := by
  rfl

/-- The representative-level slide is continuous jointly in the chord data
and the time. -/
lemma continuous_chordSlideAt_prod : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
    chordSlideAt z.2 z.1) := by
  have hz1 : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      (z.1 : RawChordData)) := continuous_subtype_val.comp continuous_fst
  have hfst : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      ((z.1 : RawChordData).1 : Circle)) :=
    (continuous_fst : Continuous (fun r : RawChordData => r.1)).comp hz1
  have hsnd : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      ((z.1 : RawChordData).2 : ℝ)) :=
    (continuous_snd : Continuous (fun r : RawChordData => r.2)).comp hz1
  have htm : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hcst : Continuous (fun _ : ChordData × Set.Icc (0 : ℝ) 1 => (1 : ℝ)) := continuous_const
  have hsub' : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 => (1 : ℝ) - (z.2 : ℝ)) :=
    hcst.sub htm
  have hmul : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      (1 - (z.2 : ℝ)) * ((z.1 : RawChordData).2 : ℝ)) := hsub'.mul hsnd
  have hraw : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      ((z.1 : RawChordData).1, (1 - (z.2 : ℝ)) * (z.1 : RawChordData).2)) :=
    hfst.prodMk hmul
  have hsubtype : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      (⟨((z.1 : RawChordData).1, (1 - (z.2 : ℝ)) * (z.1 : RawChordData).2),
        offset_slide_mem_Ioo z.2.2.1 z.2.2.2 z.1.2⟩ : ChordData)) := by
    exact Continuous.subtype_mk (f := fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
        ((z.1 : RawChordData).1, (1 - (z.2 : ℝ)) * (z.1 : RawChordData).2))
      (p := fun w : RawChordData => w.2 ∈ Set.Ioo (-1) 1) hraw
      (by intro z; exact offset_slide_mem_Ioo z.2.2.1 z.2.2.2 z.1.2)
  -- the goal function is pointwise this subtype-valued function
  have heq : (fun z : ChordData × Set.Icc (0 : ℝ) 1 => chordSlideAt z.2 z.1) =
      (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
        (⟨((z.1 : RawChordData).1, (1 - (z.2 : ℝ)) * (z.1 : RawChordData).2),
          offset_slide_mem_Ioo z.2.2.1 z.2.2.2 z.1.2⟩ : ChordData)) := by
    funext z
    rfl
  simpa [heq] using hsubtype

/-- The descended slide is continuous jointly in the class and the time. -/
lemma continuous_mobiusSlide : Continuous (fun z : MobiusModel × Set.Icc (0 : ℝ) 1 =>
    mobiusSlide z.1 z.2) := by
  have hQ : IsOpenQuotientMap (Prod.map mobiusMk (id : Set.Icc (0 : ℝ) 1 →
      Set.Icc (0 : ℝ) 1)) := by
    exact IsOpenQuotientMap.prodMap isOpenQuotientMap_mobiusMk IsOpenQuotientMap.id
  have hrep : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
      mobiusSlide (mobiusMk z.1) z.2) := by
    have hcls : Continuous (fun z : ChordData × Set.Icc (0 : ℝ) 1 =>
        mobiusMk (chordSlideAt z.2 z.1)) :=
      continuous_mobiusMk.comp continuous_chordSlideAt_prod
    have heq : (fun z : ChordData × Set.Icc (0 : ℝ) 1 => mobiusSlide (mobiusMk z.1) z.2) =
        (fun z : ChordData × Set.Icc (0 : ℝ) 1 => mobiusMk (chordSlideAt z.2 z.1)) := by
      funext z
      rw [mobiusSlide_mk]
    rwa [heq]
  exact (IsOpenQuotientMap.continuous_comp_iff hQ
    (g := fun z : MobiusModel × Set.Icc (0 : ℝ) 1 => mobiusSlide z.1 z.2)).mp hrep

/-- At time `0` the slide is the identity on the model. -/
lemma mobiusSlide_zero (c : MobiusModel) :
    mobiusSlide c ⟨(0 : ℝ), by norm_num⟩ = c := by
  refine Quotient.inductionOn c ?_
  intro q
  rw [mobiusSlide_mk]
  congr 1
  exact chordSlideAt_zero q

/-- At time `1` the slide lands on the core circle of diameters. -/
lemma mobiusSlide_one_mem_core (c : MobiusModel) :
    ∃ n : Circle, mobiusSlide c ⟨(1 : ℝ), by norm_num⟩ = mobiusCore n := by
  refine Quotient.inductionOn c ?_
  intro q
  refine ⟨q.1.1, ?_⟩
  have hsub : chordSlideAt ⟨(1 : ℝ), by norm_num⟩ q = coreChord q.1.1 := by
    apply Subtype.ext
    change ((q.1 : RawChordData).1, (1 - 1) * (q.1 : RawChordData).2) =
      (q.1.1, (0 : ℝ))
    ext <;> simp
  rw [mobiusSlide_mk, hsub]

/-- A diameter is fixed throughout the slide. -/
lemma mobiusSlide_core_fixed (n : Circle) (t : Set.Icc (0 : ℝ) 1) :
    mobiusSlide (mobiusCore n) t = mobiusCore n := by
  rw [mobiusSlide_mk]
  congr 1
  exact chordSlideAt_fixed_on_core t n (coreChord n) rfl

/-- **The model Möbius band deformation-retracts onto its core circle** (the
slide `mobiusSlide`, descended from `chordSlideAt`). -/
def MobiusCoreRetract : Prop :=
  ∃ ρ : MobiusModel × Set.Icc (0 : ℝ) 1 → MobiusModel,
    Continuous ρ ∧
    (∀ c : MobiusModel, ρ (c, ⟨(0 : ℝ), by norm_num⟩) = c) ∧
    (∀ c : MobiusModel, ∃ n : Circle, ρ (c, ⟨(1 : ℝ), by norm_num⟩) = mobiusCore n) ∧
    (∀ (n : Circle) (t : Set.Icc (0 : ℝ) 1), ρ (mobiusCore n, t) = mobiusCore n)

/-- The deformation retraction is witnessed by `mobiusSlide`. -/
lemma mobius_core_retract : MobiusCoreRetract := by
  refine ⟨fun z => mobiusSlide z.1 z.2, continuous_mobiusSlide, ?_, ?_, ?_⟩
  · intro c
    exact mobiusSlide_zero c
  · intro c
    exact mobiusSlide_one_mem_core c
  · intro n t
    exact mobiusSlide_core_fixed n t

end LeanEval.KnotTheory.Quadrisecant
