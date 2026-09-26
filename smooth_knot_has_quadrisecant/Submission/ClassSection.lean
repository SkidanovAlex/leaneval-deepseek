import Mathlib
import ChallengeDeps
import Submission.SecantSpace

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Milestone-2 step (iii), assembly item (a) — the sheet local section of
the chord-class double cover of the open band

The open Möbius band of secants is double-covered by the ordered pairs of
distinct parameters:

    mobiusCover : OrderedPairs → OpenMobius ,   (a, b) ↦ class of {a, b},

a free `ZMod 2`-swap quotient (`SecantSpace.lean`), hence (`SecantSpace`)
a covering map and, in particular, a local homeomorphism.  The open-map
half of the local 1-manifold structure of the trisecant locus `O`
(`TrisecantTransverse.lean` header) is proved by the *canonical-section
argument*: near a strict class `c₀ = mobiusCover (a₀,b₀) ∈ O`, every class
of `O` in a neighbourhood of `c₀` has a unique strict representative whose
chord lies on a fixed sheet — the ordered representative with first
endpoint near `a₀` and second near `b₀` — and the middle point depends
continuously on the class.  This module supplies item (a), the band-side
*sheet local section* on which that argument rests:

1. **`mobiusCover` is a local homeomorphism** (`mobiusCover_isLocalHomeomorph`,
   `exists_sheet_at`): each ordered pair `p₀` lies in the source of an open
   partial homeomorphism `e` of `OrderedPairs` onto `OpenMobius` agreeing
   with `mobiusCover` everywhere.  Bundled as `MobiusSheet p₀` (an open
   source `S ∋ p₀`, an open target `T ∋ mobiusCover p₀`, and the
   homeomorphism `φ : S ≃ₜ T` extending `mobiusCover`), whose existence is
   `MobiusSheet.nonempty`.  The canonical continuous **section**
   `MobiusSheet.sec c = (φ.symm ⟨c,·⟩).1 : T → OrderedPairs` satisfies
   `mobiusCover (sec c) = c` (right inverse, `sec_comp`), `sec (mobiusCover p)
   = p` for `p ∈ S` (left inverse, `sec_eq_of_source`, so the section is
   fixed at the base pair: `sec_base`), and is continuous
   (`secContinuous`, `secContinuousMap`).

2. **The classical sheet over an endpoint box** (`chordBox Ua Ub`): for
   disjoint open circle neighbourhoods `Ua ∋ a₀`, `Ub ∋ b₀` of the two
   endpoints, the box of ordered chords with first endpoint in `Ua` and
   second in `Ub` is open (`isOpen_chordBox`), `mobiusCover` is injective
   on it (`mobiusCover_injOn_chordBox` — the two ordered representatives of
   one class can never both lie in the box, since the swapped one would put
   a single circle point inside both disjoint neighbourhoods), its image is
   open in the band (`isOpen_chordBox_image`), and the restriction is a
   homeomorphism onto that image (`chordBoxHomeo`).  This is the *sheet*
   that keeps the two endpoints on their prescribed sides of the chord —
   the ordered representative over which strict trisecant data with chords
   near `(a₀,b₀)` are canonically lifted in assembly items (b)/(c).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-! ## 1. The double cover of the band is a local homeomorphism -/

/-- **The double cover is a local homeomorphism**: `mobiusCover` is a
covering map (`SecantSpace.isCoveringMap_mobiusCover`), and a covering map
is locally a homeomorphism. -/
lemma mobiusCover_isLocalHomeomorph : IsLocalHomeomorph mobiusCover := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact (IsCoveringMap.isCoveringMapOn isCoveringMap_mobiusCover).isLocalHomeomorphOn

/-- **A sheet through an ordered pair.**  Each ordered pair `p₀` of distinct
parameters lies in the source of an open partial homeomorphism `e` of
`OrderedPairs` onto `OpenMobius` whose function agrees with `mobiusCover`
everywhere: `e.source` is an open neighbourhood of `p₀`, `e.target` is an
open neighbourhood of `mobiusCover p₀` in the band, and `e.symm` restricts
to a continuous section of the double cover over `e.target`. -/
theorem exists_sheet_at {p₀ : OrderedPairs} :
    ∃ e : OpenPartialHomeomorph OrderedPairs OpenMobius,
      p₀ ∈ e.source ∧ mobiusCover = e := by
  exact mobiusCover_isLocalHomeomorph p₀

/-- **A bundled sheet of the double cover through `p₀`**: an open source
neighbourhood `S ∋ p₀` in the ordered pairs, an open target neighbourhood
`T ∋ mobiusCover p₀` in the band, and a homeomorphism `φ : S ≃ₜ T` that
extends `mobiusCover` (agreement on the source). -/
structure MobiusSheet (p₀ : OrderedPairs) where
  S : Set OrderedPairs
  T : Set OpenMobius
  φ : {p : OrderedPairs // p ∈ S} ≃ₜ {c : OpenMobius // c ∈ T}
  S_open : IsOpen S
  T_open : IsOpen T
  p₀_mem : p₀ ∈ S
  class_mem : mobiusCover p₀ ∈ T
  /-- the sheet homeo extends the covering map on its source -/
  agrees : ∀ x : {p : OrderedPairs // p ∈ S}, ((φ x : OpenMobius) = mobiusCover x.1)

open OpenPartialHomeomorph in
/-- Build a bundled sheet from the partial homeomorphism supplied by the
local-homeomorphism structure of the covering map. -/
def MobiusSheet.ofPartialHomeo (p₀ : OrderedPairs)
    (e : OpenPartialHomeomorph OrderedPairs OpenMobius)
    (hxe : p₀ ∈ e.source) (hfe : mobiusCover = e) : MobiusSheet p₀ :=
  { S := e.source,
    T := e.target,
    φ := e.toHomeomorphSourceTarget,
    S_open := e.open_source,
    T_open := e.open_target,
    p₀_mem := hxe,
    class_mem := by
      have h_eq : mobiusCover p₀ = e p₀ := congr_fun hfe p₀
      rw [h_eq]
      exact e.map_source hxe,
    agrees := by
      intro x
      have hx : (e.toHomeomorphSourceTarget x : OpenMobius) = e x.1 := by simp
      rw [hx]
      exact (congr_fun hfe x.1).symm }

namespace MobiusSheet

/-- Every ordered pair of distinct parameters carries a sheet of the double
cover (the local homeomorphism structure of the covering map, bundled). -/
theorem nonempty (p₀ : OrderedPairs) : Nonempty (MobiusSheet p₀) := by
  rcases exists_sheet_at (p₀ := p₀) with ⟨e, hxe, hfe⟩
  exact ⟨MobiusSheet.ofPartialHomeo p₀ e hxe hfe⟩

variable {p₀ : OrderedPairs}

/-- The sheet homeo sends the base pair to the base class (it extends
`mobiusCover`, which sends `p₀` to `mobiusCover p₀`). -/
lemma φ_base (sh : MobiusSheet p₀) :
    sh.φ ⟨p₀, sh.p₀_mem⟩ = ⟨mobiusCover p₀, sh.class_mem⟩ := by
  apply Subtype.ext
  exact sh.agrees ⟨p₀, sh.p₀_mem⟩

/-- **The canonical section of the double cover over the sheet target**:
`sh.sec c` is the unique ordered pair on the sheet `S` lying over the class
`c ∈ T`. -/
def sec (sh : MobiusSheet p₀) (c : OpenMobius) (hc : c ∈ sh.T) : OrderedPairs :=
  ((sh.φ.symm ⟨c, hc⟩ : {p : OrderedPairs // p ∈ sh.S}) : OrderedPairs)

/-- The section lands in the sheet source. -/
lemma sec_mem_source (sh : MobiusSheet p₀) (c : OpenMobius) (hc : c ∈ sh.T) :
    sh.sec c hc ∈ sh.S :=
  (sh.φ.symm ⟨c, hc⟩).2

/-- **The section is a right inverse of the covering map**: the ordered
pair chosen over `c` has class `c` exactly. -/
lemma sec_comp (sh : MobiusSheet p₀) (c : OpenMobius) (hc : c ∈ sh.T) :
    mobiusCover (sh.sec c hc) = c := by
  let x : {p : OrderedPairs // p ∈ sh.S} := sh.φ.symm ⟨c, hc⟩
  have hφ : (sh.φ x : OpenMobius) = mobiusCover x.1 := sh.agrees x
  calc
    mobiusCover (sh.sec c hc) = mobiusCover x.1 := by simp [sec, x]
    _ = (sh.φ x : OpenMobius) := hφ.symm
    _ = c := by
      have hsub : sh.φ x = ⟨c, hc⟩ := sh.φ.apply_symm_apply ⟨c, hc⟩
      exact congrArg Subtype.val hsub

/-- **The section is fixed on the base class**: over the class of the base
ordered pair the section returns exactly that pair (the sheet is chosen
through `p₀`). -/
lemma sec_base (sh : MobiusSheet p₀) :
    sh.sec (mobiusCover p₀) sh.class_mem = p₀ := by
  unfold sec
  have hφb : sh.φ ⟨p₀, sh.p₀_mem⟩ = ⟨mobiusCover p₀, sh.class_mem⟩ := sh.φ_base
  have hb : sh.φ.symm ⟨mobiusCover p₀, sh.class_mem⟩ = ⟨p₀, sh.p₀_mem⟩ := by
    rw [← hφb]
    exact sh.φ.symm_apply_apply ⟨p₀, sh.p₀_mem⟩
  exact congrArg Subtype.val hb

/-- The class of a source point lies in the target of the sheet (the sheet
homeo extends `mobiusCover`, whose value at `p` is the class of `p`). -/
lemma class_mem_of_source (sh : MobiusSheet p₀) {p : OrderedPairs} (hp : p ∈ sh.S) :
    mobiusCover p ∈ sh.T := by
  have hφT : (sh.φ ⟨p, hp⟩ : OpenMobius) ∈ sh.T := (sh.φ ⟨p, hp⟩).2
  rw [sh.agrees ⟨p, hp⟩] at hφT
  exact hφT

/-- **The section inverts the covering map on the sheet source**: for an
ordered pair `p` on the sheet, the section over its class returns `p`
itself (the left-inverse property, as values of `OrderedPairs`). -/
lemma sec_eq_of_source (sh : MobiusSheet p₀) {p : OrderedPairs} (hp : p ∈ sh.S) :
    sh.sec (mobiusCover p) (sh.class_mem_of_source hp) = p := by
  unfold sec
  have hφx : sh.φ ⟨p, hp⟩ = ⟨mobiusCover p, sh.class_mem_of_source hp⟩ := by
    apply Subtype.ext
    exact sh.agrees ⟨p, hp⟩
  have hback : sh.φ.symm ⟨mobiusCover p, sh.class_mem_of_source hp⟩ = ⟨p, hp⟩ := by
    rw [← hφx]
    exact sh.φ.symm_apply_apply ⟨p, hp⟩
  exact congrArg Subtype.val hback

/-- The section is continuous (as a map from the target subtype into the
ordered pairs): it is the composition of the homeo inverse with the
inclusion of the source. -/
theorem secContinuous (sh : MobiusSheet p₀) :
    Continuous (fun x : {c : OpenMobius // c ∈ sh.T} => sh.sec x.1 x.2) := by
  have h1 : Continuous (fun x : {c : OpenMobius // c ∈ sh.T} =>
      (sh.φ.symm x : {p : OrderedPairs // p ∈ sh.S})) := (sh.φ.symm).continuous
  have h2 : Continuous (fun x : {c : OpenMobius // c ∈ sh.T} =>
      ((sh.φ.symm x : {p : OrderedPairs // p ∈ sh.S}) : OrderedPairs)) :=
    continuous_subtype_val.comp h1
  simpa [sec] using h2

/-- The section, bundled as a continuous map from the target subtype into
the ordered pairs. -/
noncomputable def secContinuousMap (sh : MobiusSheet p₀) :
    C({c : OpenMobius // c ∈ sh.T}, OrderedPairs) :=
  ⟨fun x => sh.sec x.1 x.2, sh.secContinuous⟩

/-- The continuous section is a right inverse of the covering map, at the
level of values: for every class in the target, the class of the section
value is the class itself. -/
lemma secContinuousMap_comp (sh : MobiusSheet p₀) :
    ∀ x : {c : OpenMobius // c ∈ sh.T}, mobiusCover ((sh.secContinuousMap) x) = x.1 := by
  intro x
  exact sh.sec_comp x.1 x.2

end MobiusSheet

/-! ## 2. The sheet over an endpoint box (disjoint circle neighbourhoods) -/

/-- An ordered-chord box: ordered pairs whose first endpoint lies in `Ua`
and whose second endpoint lies in `Ub`. -/
def chordBox (Ua Ub : Set (AddCircle period)) : Set OrderedPairs :=
  {p | p.1.1 ∈ Ua ∧ p.1.2 ∈ Ub}

/-- A chord box is open when both endpoint neighbourhoods are open (it is
the preimage of the open product `Ua × Ub` under the continuous map
`p ↦ (p.1.1, p.1.2)`). -/
lemma isOpen_chordBox {Ua Ub : Set (AddCircle period)} (hUa : IsOpen Ua) (hUb : IsOpen Ub) :
    IsOpen (chordBox Ua Ub) := by
  let val : OrderedPairs → AddCircle period × AddCircle period := Subtype.val
  have hcont : Continuous val := continuous_subtype_val
  have hset : chordBox Ua Ub = val ⁻¹' (Ua ×ˢ Ub) := by
    ext p
    simp [chordBox, val]
  rw [hset]
  exact (hUa.prod hUb).preimage hcont

/-- The box contains an ordered pair whose endpoints lie in the two
neighbourhoods. -/
lemma mem_chordBox {Ua Ub : Set (AddCircle period)} {a b : AddCircle period}
    (ha : a ∈ Ua) (hb : b ∈ Ub) (hab : a ≠ b) :
    (⟨(a, b), hab⟩ : OrderedPairs) ∈ chordBox Ua Ub := by
  simp [chordBox, ha, hb]

/-- **`mobiusCover` is injective on a chord box with disjoint endpoint
neighbourhoods**: two ordered pairs in the box with equal classes are equal
(the fibre of the double cover is `{p, swapOrdered p}` and the swapped
representative of a box point would place a single circle point inside both
disjoint neighbourhoods). -/
lemma mobiusCover_injOn_chordBox {Ua Ub : Set (AddCircle period)}
    (hdis : Disjoint Ua Ub) : Set.InjOn mobiusCover (chordBox Ua Ub) := by
  intro p hp q hq hpq
  have hfib := mobiusCover_fiber p
  have hq' : q ∈ ({p, swapOrdered p} : Set OrderedPairs) := by
    rw [← hfib]
    exact hpq.symm
  simp at hq'
  rcases hq' with hEq | hsw
  · exact hEq.symm
  · exfalso
    have h1 : q.1.1 ∈ Ua := hq.1
    have h2 : q.1.1 ∈ Ub := by
      have hfst : q.1.1 = p.1.2 := by
        have hc := congrArg (fun z : OrderedPairs => z.1.1) hsw
        simpa [swapOrdered] using hc
      rw [hfst]
      exact hp.2
    exact (Set.disjoint_left.mp hdis) h1 h2

/-- The image of a chord box under the double cover is open in the band
(`mobiusCover` is an open map). -/
lemma isOpen_chordBox_image {Ua Ub : Set (AddCircle period)} (hUa : IsOpen Ua) (hUb : IsOpen Ub) :
    IsOpen (mobiusCover '' chordBox Ua Ub) :=
  isOpenMap_mobiusCover (chordBox Ua Ub) (isOpen_chordBox hUa hUb)

/-- The class of an ordered pair of the box lies in the image of the box. -/
lemma class_mem_chordBox_image {Ua Ub : Set (AddCircle period)} {p : OrderedPairs}
    (hp : p ∈ chordBox Ua Ub) : mobiusCover p ∈ mobiusCover '' chordBox Ua Ub :=
  ⟨p, hp, rfl⟩

/-- **The sheet homeomorphism of the box**: for disjoint open endpoint
neighbourhoods, `mobiusCover` restricts to a homeomorphism from the chord
box onto its image in the band.  The restriction is continuous
(composition of continuous maps), injective (`mobiusCover_injOn_chordBox`),
surjective onto its image by definition, and open — an open subset of the
box is open in `OrderedPairs` (the box is open), its image is open in the
band (`isOpenMap_mobiusCover`), and since the image of the box is open in
the band, openness in the image subspace is witnessed by openness of the
value-image (`chordBoxHomeo`'s proof records this as `hopen`). -/
noncomputable def chordBoxHomeo {Ua Ub : Set (AddCircle period)}
    (hUa : IsOpen Ua) (hUb : IsOpen Ub) (hdis : Disjoint Ua Ub) :
    {p : OrderedPairs // p ∈ chordBox Ua Ub} ≃ₜ
      {c : OpenMobius // c ∈ mobiusCover '' chordBox Ua Ub} := by
  let B : Set OrderedPairs := chordBox Ua Ub
  let V : Set OpenMobius := mobiusCover '' B
  let f : {p : OrderedPairs // p ∈ B} → {c : OpenMobius // c ∈ V} := fun x =>
    ⟨mobiusCover x.1, class_mem_chordBox_image (Ua := Ua) (Ub := Ub) x.2⟩
  have hB_open : IsOpen B := isOpen_chordBox hUa hUb
  have hV_open : IsOpen V := isOpen_chordBox_image (Ua := Ua) (Ub := Ub) hUa hUb
  have hcont : Continuous f := by
    dsimp [f]
    exact Continuous.subtype_mk (continuous_mobiusCover.comp continuous_subtype_val)
      (fun x : {p : OrderedPairs // p ∈ B} => class_mem_chordBox_image (Ua := Ua) (Ub := Ub) x.2)
  have hsurj : Function.Surjective f := by
    rintro ⟨c, ⟨p, hp, hc⟩⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    exact hc
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact mobiusCover_injOn_chordBox (Ua := Ua) (Ub := Ub) hdis (x₁ := x.1) (x₂ := y.1) x.2 y.2
      (congrArg (fun z : {c : OpenMobius // c ∈ V} => (z : OpenMobius)) hxy)
  have hopen : IsOpenMap f := by
    intro U hU
    have hU_open : IsOpen ((Subtype.val : {p : OrderedPairs // p ∈ B} → OrderedPairs) '' U) := by
      exact hB_open.isOpenMap_subtype_val U hU
    have himg_open : IsOpen (mobiusCover '' ((Subtype.val : {p : OrderedPairs // p ∈ B} → OrderedPairs) '' U)) :=
      isOpenMap_mobiusCover _ hU_open
    have hval_eq : (Subtype.val : {c : OpenMobius // c ∈ V} → OpenMobius) '' (f '' U) =
        mobiusCover '' ((Subtype.val : {p : OrderedPairs // p ∈ B} → OrderedPairs) '' U) := by
      ext c
      constructor
      · rintro ⟨z, ⟨x, hxU, hz⟩, rfl⟩
        refine ⟨x.1, ⟨x, hxU, rfl⟩, ?_⟩
        simpa using congrArg Subtype.val hz
      · rintro ⟨p, ⟨x, hxU, rfl⟩, rfl⟩
        refine ⟨f x, ⟨x, hxU, rfl⟩, ?_⟩
        rfl
    have hiff : IsOpen (f '' U) ↔
        IsOpen ((Subtype.val : {c : OpenMobius // c ∈ V} → OpenMobius) '' (f '' U)) := by
      constructor
      · intro hs
        exact hV_open.isOpenMap_subtype_val (f '' U) hs
      · intro hs
        have hpre : IsOpen ((Subtype.val : {c : OpenMobius // c ∈ V} → OpenMobius) ⁻¹'
            ((Subtype.val : {c : OpenMobius // c ∈ V} → OpenMobius) '' (f '' U))) :=
          hs.preimage continuous_subtype_val
        simpa [Subtype.val_injective.preimage_image] using hpre
    rw [hiff, hval_eq]
    exact himg_open
  exact (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen

/-- The box sheet homeo extends `mobiusCover` on the box: the value of the
homeo is the class of the ordered pair. -/
lemma chordBoxHomeo_apply {Ua Ub : Set (AddCircle period)} (hUa : IsOpen Ua) (hUb : IsOpen Ub)
    (hdis : Disjoint Ua Ub) (x : {p : OrderedPairs // p ∈ chordBox Ua Ub}) :
    ((chordBoxHomeo hUa hUb hdis x : {c : OpenMobius // c ∈ mobiusCover '' chordBox Ua Ub}) :
      OpenMobius) = mobiusCover x.1 := by
  rfl

/-- Disjoint open neighbourhoods exist for two distinct points of the
parameter circle (the circle is Hausdorff). -/
lemma exists_disjoint_open_nhds {a b : AddCircle period} (hab : a ≠ b) :
    ∃ Ua Ub : Set (AddCircle period),
      IsOpen Ua ∧ IsOpen Ub ∧ a ∈ Ua ∧ b ∈ Ub ∧ Disjoint Ua Ub :=
  t2_separation (x := a) (y := b) hab

/-- **Disjoint endpoint neighbourhoods of an ordered pair**: for an ordered
pair `p₀ = (a₀, b₀)` of distinct parameters, disjoint open neighbourhoods
`Ua ∋ a₀`, `Ub ∋ b₀` exist, so `chordBoxHomeo` makes the box a sheet over
an open neighbourhood of the class `mobiusCover p₀`. -/
theorem exists_box_sheet (p₀ : OrderedPairs) :
    ∃ (Ua Ub : Set (AddCircle period)),
      IsOpen Ua ∧ IsOpen Ub ∧ p₀.1.1 ∈ Ua ∧ p₀.1.2 ∈ Ub ∧ Disjoint Ua Ub := by
  rcases exists_disjoint_open_nhds p₀.2 with ⟨Ua, Ub, hUa, hUb, ha, hb, hdis⟩
  exact ⟨Ua, Ub, hUa, hUb, ha, hb, hdis⟩

end LeanEval.KnotTheory.Quadrisecant
