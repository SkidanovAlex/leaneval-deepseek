import Mathlib
import Submission.Work.OROneRel.coverRootDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.rhoC_injective_range

namespace Work.OROneRel

universe u

variable {α : Type u}


/-! ## Auxiliary lemmas for `coverClass_injective`

The two inputs of the main proof are

* `signed_lift_injective_aux`: in a free group, a family of signed free generators with at most one
  sign per generator is free; this is the step that turns a *set of decorated letters*
  `S ⊆ (α × ℤ) × Bool` (with no edge used in both directions) into a free family of symbols;
* `coverClass_eq_coverPhi` and `coverPhi_injective`: for the letter-weight gauge `W i = of t ^ i` the
  loop class of the symbol `(x, i, ±)` is `coverPhi (of (x,i))^{±1}` for the Magnus map
  `coverPhi : F ({x // x ≠ t} × ℤ) →* F α`, `(x,i) ↦ t ^ i * x * t ^ (-(i + c x))`, which is
  injective by `rhoC_injective_range`.

The main theorem is then `rfl`-level assembly: the class map factors as an injective map on the
symbols followed by the injective map `coverPhi`. -/

/-- The candidate retraction of the signed-generator map: `of (q x)` is sent to the signed symbol
`x^{±1}` prescribed by `b`, and every generator not in the range of `q` is sent to `1`.  It is well
defined (and a genuine homomorphism) because `q` is injective. -/
noncomputable def signedRetractFun {X Y : Type*} (q : X → Y) (b : X → Bool) (y : Y) :
    FreeGroup X := by
  classical
  exact dite (∃ x : X, q x = y)
    (fun h => if b (Classical.choose h) then FreeGroup.of (Classical.choose h)
      else (FreeGroup.of (Classical.choose h))⁻¹)
    (fun _ => 1)

/-- The retraction of `FreeGroup.lift (fun x => of (q x)^{b x})`. -/
noncomputable def signedRetract {X Y : Type*} (q : X → Y) (b : X → Bool) :
    FreeGroup Y →* FreeGroup X :=
  FreeGroup.lift (signedRetractFun q b)

/-- **A signed family of free generators of a free group is free.**  If `q : X → Y` is injective and
`b : X → Bool` prescribes, for every `x`, whether the generator `of (q x)` is used or its inverse,
then the induced map on free groups is injective. -/
lemma signed_lift_injective_aux {X Y : Type*} (q : X → Y) (b : X → Bool)
    (hq : Function.Injective q) :
    Function.Injective
      (FreeGroup.lift fun x : X =>
        if b x then FreeGroup.of (q x) else (FreeGroup.of (q x))⁻¹) := by
  classical
  have hψq : ∀ x : X, signedRetractFun q b (q x)
      = (if b x then FreeGroup.of x else (FreeGroup.of x)⁻¹) := by
    intro x
    have hex : ∃ x' : X, q x' = q x := ⟨x, rfl⟩
    have h2 : Classical.choose hex = x := hq (Classical.choose_spec hex)
    rw [signedRetractFun, dif_pos hex, h2]
  have hψe : ∀ x : X, signedRetract q b
      (if b x then FreeGroup.of (q x) else (FreeGroup.of (q x))⁻¹) = FreeGroup.of x := by
    intro x
    by_cases hb : b x = true
    · rw [if_pos hb, signedRetract, FreeGroup.lift_apply_of, hψq x, if_pos hb]
    · rw [if_neg hb, map_inv, signedRetract, FreeGroup.lift_apply_of, hψq x, if_neg hb]
      simp
  have hcomp : (signedRetract q b).comp (FreeGroup.lift fun x : X =>
        if b x then FreeGroup.of (q x) else (FreeGroup.of (q x))⁻¹)
      = MonoidHom.id (FreeGroup X) := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, FreeGroup.lift_apply_of]
    exact hψe x
  have key : ∀ w : FreeGroup X,
      FreeGroup.lift (fun x : X =>
        if b x then FreeGroup.of (q x) else (FreeGroup.of (q x))⁻¹) w = 1 → w = 1 := by
    intro w hw
    have h := DFunLike.congr_fun hcomp w
    rw [MonoidHom.comp_apply, MonoidHom.id_apply] at h
    rw [← h, hw, map_one]
  intro w w' hww'
  have h1 : FreeGroup.lift (fun x : X =>
      if b x then FreeGroup.of (q x) else (FreeGroup.of (q x))⁻¹) (w * w'⁻¹) = 1 := by
    rw [map_mul, map_inv, hww', mul_inv_cancel]
  have h2 := key (w * w'⁻¹) h1
  have h3 : w = w * w'⁻¹ * w' := by group
  rw [h3, h2, one_mul]

/-! ## The injective class map of the `ℤ`-cover -/

/-- The class map of the `ℤ`-cover, restricted to the generators `x ≠ t`: the Magnus map
`rhoC (of t) c : (x,i) ↦ t ^ i * x * t ^ (-i - c x)` composed with the inclusion of the generators
`x ≠ t`. -/
noncomputable def coverPhi (t : α) (c : α → ℤ) :
    FreeGroup ({x : α // x ≠ t} × ℤ) →* FreeGroup α :=
  (rhoC (FreeGroup.of t) c).comp
    (FreeGroup.map fun p : {x : α // x ≠ t} × ℤ => ((p.1 : α), p.2))

/-- `coverPhi` is injective (the restricted Magnus embedding, `rhoC_injective_range`). -/
lemma coverPhi_injective (t : α) (c : α → ℤ) (hc : c t = 1) :
    Function.Injective (coverPhi t c) :=
  (rhoC_injective_range t c hc).1

/-- The value of `coverPhi` on a generator. -/
lemma coverPhi_of (t : α) (c : α → ℤ) (x : {x : α // x ≠ t}) (i : ℤ) :
    coverPhi t c (FreeGroup.of (x, i)) =
      FreeGroup.of t ^ i * FreeGroup.of (x : α) * FreeGroup.of t ^ (-(i + c (x : α))) := by
  have h : -i - c (x : α) = -(i + c (x : α)) := by ring
  rw [coverPhi, MonoidHom.comp_apply, FreeGroup.map.of, rhoC_of, h]

/-- The loop class of a decorated letter under the letter-weight gauge `W i = of t ^ i`. -/
lemma coverClass_eq_coverPhi (t : α) (c : α → ℤ) (x : α) (hx : x ≠ t) (i : ℤ) (b : Bool) :
    coverClass (fun j : ℤ => FreeGroup.of t ^ j) c ((x, i), b) =
      (if b then coverPhi t c (FreeGroup.of ((⟨x, hx⟩ : {x : α // x ≠ t}), i))
        else (coverPhi t c (FreeGroup.of ((⟨x, hx⟩ : {x : α // x ≠ t}), i)))⁻¹) := by
  rcases b with _ | _
  · simp only [Bool.false_eq_true, if_false]
    rw [coverClass, gauge_letter]
    simp only [coverSrc, coverTgt, coverLetter, Bool.false_eq_true, if_false]
    rw [coverPhi_of t c ⟨x, hx⟩ i]
    group
  · simp only [if_true]
    rw [coverClass, gauge_letter]
    simp only [coverSrc, coverTgt, coverLetter, if_true]
    rw [coverPhi_of t c ⟨x, hx⟩ i]
    group

/-- **The loop classes of the ℤ-cover, letter-weight gauge, are independent.**

Let `t : α` with `c t = 1`, and let `S` be a set of *decorated letters* of the ℤ-cover of the
presentation complex of `⟨α | u⟩` (an element of `S` is a pair `(p, sign)` with `p = (x, i)` a
generator together with the level `i`).  Assume

* `hS` : no decorated letter has `x = t` (these are exactly the letters whose loop class is trivial), and
* `hclash` : no (undirected) edge of the cover is used in both directions, i.e. `(x,i)` never occurs
  in `S` both with `true` and with `false`.

Then the map `FreeGroup S →* FreeGroup α` sending a decorated letter to its *loop class* is
injective.  Equivalently (the reviewer's reading): the family
`{t^i · x · t ^ (-(i + c x)) : (x,i) ∈ T}` is a free basis of the subgroup it generates, and the
statement follows since the signed symbols are `±`-copies of those basis elements.
Suggested route: the ℤ-cover of the rose with the `t`-edges as a spanning tree shows that the
signed loop classes are a subset (up to inversion) of a free basis of the kernel of the weight map;
the reduction `Φ : x ↦ x · t ^ (c x)` (an automorphism of `F α` fixing `t`) also reduces the
general `c` to the case `c x = 0` for `x ≠ t`, where the assertion is that the conjugates
`t ^ i · x · t ^ (-i)` of the free-factor generators are independent. -/
theorem coverClass_injective {α : Type u} [DecidableEq α] (t : α) (c : α → ℤ) (hct : c t = 1)
    (S : Set ((α × ℤ) × Bool)) (hS : ∀ p ∈ S, p.1.1 ≠ t)
    (hclash : ∀ (x : α) (i : ℤ), ((x, i), true) ∈ S → ((x, i), false) ∈ S → False) :
    Function.Injective
      (FreeGroup.lift (fun p : S =>
        Work.OROneRel.coverClass (fun i : ℤ => FreeGroup.of t ^ i) c p.1)) := by
  classical
  -- The decorated letter `p` forgets its sign; `hclash` makes this forgetful map injective.
  let q : S → ({x : α // x ≠ t} × ℤ) := fun p => (⟨p.1.1.1, hS p.1 p.2⟩, p.1.1.2)
  have hq : Function.Injective q := by
    rintro ⟨⟨⟨x, i⟩, b⟩, hp⟩ ⟨⟨⟨x', i'⟩, b'⟩, hp'⟩ heq
    dsimp only [q] at heq
    have hx : x = x' :=
      congrArg (fun z : {y : α // y ≠ t} => (z : α)) (congrArg Prod.fst heq)
    have hi : i = i' := congrArg (fun z : {y : α // y ≠ t} × ℤ => z.2) heq
    have hb : b = b' := by
      cases b <;> cases b'
      · rfl
      · exfalso
        rw [← hx, ← hi] at hp'
        exact hclash x i hp' hp
      · exfalso
        rw [hx, hi] at hp
        exact hclash x' i' hp hp'
      · rfl
    exact Subtype.ext (Prod.ext (Prod.ext hx hi) hb)
  -- The map on the symbols: a decorated letter is sent to the matching signed generator.
  let Ψ : FreeGroup S →* FreeGroup ({x : α // x ≠ t} × ℤ) :=
    FreeGroup.lift fun p : S => if p.1.2 then FreeGroup.of (q p) else (FreeGroup.of (q p))⁻¹
  have hΨ : Function.Injective Ψ := signed_lift_injective_aux q (fun p => p.1.2) hq
  have hΦ : Function.Injective (coverPhi t c) := coverPhi_injective t c hct
  -- The class map is the composite of the two injective maps.
  have key : (FreeGroup.lift (fun p : S =>
        Work.OROneRel.coverClass (fun i : ℤ => FreeGroup.of t ^ i) c p.1))
      = (coverPhi t c).comp Ψ := by
    refine FreeGroup.ext_hom _ _ (fun p => ?_)
    obtain ⟨⟨⟨x, i⟩, b⟩, hp⟩ := p
    -- On the generator `p = ((x,i),b)` the class map is the class of the letter, and `Ψ` sends it
    -- to the signed symbol `(x,i)^{±1}`.
    simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, Ψ, q]
    by_cases hb : b = true
    · rw [if_pos hb, coverClass_eq_coverPhi t c x (hS ((x, i), b) hp) i b, if_pos hb]
    · rw [if_neg hb, coverClass_eq_coverPhi t c x (hS ((x, i), b) hp) i b, if_neg hb, map_inv]
  rw [key]
  exact hΦ.comp hΨ

end Work.OROneRel
