/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `isEpic_starClosureCod`: the epic criterion at the `∗`-regular closure

## Status of the requested statement (2026-10-02)

The statement

`Work.ORDivLoc.Closure.isEpic_starClosureCod` — `IsEpic (starClosureCod E φK H)` for an *arbitrary*
coefficient field `K` and embedding `φK : K →+* ℂ` —

is **false as written** (it is therefore **not** stated in this file): the epicity of
`starClosureCod E φK H` needs a `∗`-compatibility of the *scalar* part of the coefficient field
which the statement does not assume.

What the proof of [JZLA20, Proposition 2.7] (= the "if" direction, [Jaikin, *The base change in the
Atiyah and the Lück approximation conjectures*, GAFA 29 (2019), Proposition 6.1]) actually uses is
that the source carries a `∗`-structure with respect to which the structure map is a
`∗`-homomorphism.  Concretely, take `g h : V →+* Q` with the same restriction to `K[↥H]`, let
`E = {v | g v = h v}` be their equalizer, and let `P = {v ∈ E | star v ∈ E}`.  Then `P` is a
subring of `V` containing the image and closed under relative inverses of its self-adjoint
elements (this is `map_relativeInverse_eq_of_selfAdjoint`), so
`starRegularClosure_le_of_isRelativeInverse_selfAdjoint` gives `V ⊆ P ⊆ E` **provided
`star '' φ(K[↥H]) ⊆ E`**, i.e. provided the star of every element of the image of `φ'` is a ring
expression in the image.  For the generators of `K[↥H]` this means

* `star (genU E h) = genU E h⁻¹` for `h : ↥H` — true by `ι_star` and `GroupAlgebraStar`, and
* `star (algebraMap K E.U k) = algebraMap K E.U (σ k)` for an anti-automorphism `σ` of `K` —
  true only when `φK(K) ⊆ ℂ` is closed under complex conjugation (with the canonical
  `Work.ORBridgeLinnell.kAlgebra E φK` this is `conj (φK k) ∈ φK(K)`).

The paper is in the second situation (`K ⊆ ℂ` closed under conjugation), but the statement here
quantifies over an arbitrary field `K`, an arbitrary `φK : K →+* ℂ` and an arbitrary
`[Algebra K E.U]`, with no compatibility between the `K`-algebra structure and the involution of
`E.U`; the extraction `Work.ORVonNeumann.StarRegularEnvelope` does not impose one either.

### Counterexample (outline)

* `E` = the envelope of the trivial group (`Work.ORVonNeumann.Examples.punitEnvelopeAux`):
  `U = ULift ℂ` with `star = conjugation`, `ι = trivialAug`; `H = ⊥`.
* `K = ℚ(α)` for a non-real root `α ∈ ℂ` of the irreducible cubic `X³ - 2`, `φK : K ↪ ℂ` the
  inclusion, `[Algebra K E.U] = Work.ORBridgeLinnell.kAlgebra E φK`.
* Then `K[↥⊥] ≃ K`, `toUK (single 1 k) = k • 1 = algebraMap K E.U k`, and
  `starClosureOfSubgroup E φK ⊥` is the smallest `∗`-closed subfield of `ℂ` containing `φK(K)`,
  namely `V = ℚ(α, ᾱ)`; up to the identification `K[↥⊥] ≃ K`, `starClosureCod E φK ⊥` is the
  inclusion `K ↪ V`.
* `ᾱ ∉ K`: otherwise `K ∋ ᾱ`, hence also `∛2 = -(α + ᾱ) ∈ K` and `ω = α/∛2 ∈ K` (`α = ω·∛2` is a
  non-real cube root of `2`), so `ℚ(ω, ∛2) ⊆ K` and `6 ∣ [K : ℚ]`, while `[K : ℚ] = 3` because
  `X³ - 2` is irreducible over `ℚ` (Eisenstein at `2`) — contradiction.
* Hence `V/K` is a non-trivial *normal* extension (it is the splitting field of `X³ - 2` over `K`,
  of degree `6/3 = 2`), so there is a non-identity `τ ∈ Gal(V/K)` fixing `K` pointwise; `id` and
  `τ` are distinct ring homomorphisms `V → V` with the same restriction to the image of
  `starClosureCod E φK ⊥`, which is therefore **not** epic.

(Equivalently one may use the cubic `X³ + X + 1` and the Galois-order argument: if `ᾱ ∈ ℚ(α)` then
`ℚ(α)` contains all three roots, is the splitting field of an irreducible cubic, hence Galois of
degree `3`, while complex conjugation would then be an automorphism of order `2` — so `2 ∣ 3`.)

The corrected statement — with the precise hypothesis the proof needs — is proved below as
`isEpic_codRestrict_starRegularClosure_of_star_mem`; instantiated at `φ = (toUK E φK H).toRingHom`
it gives `IsEpic (starClosureCod E φK H)` as soon as the star of every element of the image of
`toUK` is a ring expression in the image (in particular when `K` is a `∗`-field and
`K[↥H] → U(G)` is a `∗`-homomorphism, as in [JZLA20], or, concretely, whenever
`∀ k : K, star (algebraMap K E.U k) = algebraMap K E.U k` holds together with
`∀ h : ↥H, star (genU E h) = genU E h⁻¹`).
-/
import Mathlib
import Submission.Work.ORDivLoc.Basic
import Submission.Work.ORDivLoc.Vocabulary
import Submission.Work.ORHughesFree.StarRegular.relativeInverse_mem_starRegularClosure
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le_of_isRelativeInverse_selfAdjoint
import Submission.Work.ORHughesFree.NaturalExtension.isEpic_of_starRegularClosure
import Submission.Work.ORHughesFree.NaturalExtension.relativeInverse_selfAdjoint

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDivLoc.Closure

universe u

open Work.ORHughesFree

/-- **The epic criterion of [JZLA20, Proposition 2.7] with the exact hypothesis the proof needs.**

Let `φ : S →+* U` be a ring homomorphism into a `∗`-regular ring `U` and let

`V = R(φ(S), U) = starRegularClosure (starSubringClosure (Set.range φ))`

be the `∗`-regular closure of the image of `φ`.  If **the star of every element of the image is a
ring expression in the image**, i.e.

`hstar : ∀ s : S, star (φ s) ∈ Subring.closure (Set.range φ)`,

then the corestriction `S →+* V` of `φ` is epic (right cancellable).

The proof is the equalizer argument of `map_relativeInverse_eq_of_selfAdjoint`: for
`g h : V →+* Q` agreeing on the image of `φ`, the set `A` on which `g` and `h` agree contains
`φ(S)` and, by `hstar`, also `star '' φ(S)`; hence the `∗`-subring closure of the image lies in
`A`, and the star-closed part `P ⊆ A` is closed under relative inverses of its self-adjoint
elements, so `starRegularClosure_le_of_isRelativeInverse_selfAdjoint` gives
`V ⊆ P ⊆ A`, i.e. `g = h`. -/
theorem isEpic_codRestrict_starRegularClosure_of_star_mem {S U : Type u} [Ring S] [Ring U]
    [StarRing U] [IsStarRegular U] (φ : S →+* U)
    (hstar : ∀ s : S, star (φ s) ∈ Subring.closure (Set.range φ)) :
    IsEpic (φ.codRestrict
      (starRegularClosure (starSubringClosure (Set.range φ))).toSubring
      (fun s => subset_starRegularClosure _
        (subset_starSubringClosure _ ⟨s, rfl⟩))) := by
  intro Q _ g h hgh
  let V : StarSubring U := starRegularClosure (starSubringClosure (Set.range φ))
  let ψ : S →+* ↥V := φ.codRestrict V.toSubring
    (fun s => subset_starRegularClosure _ (subset_starSubringClosure _ ⟨s, rfl⟩))
  letI hStarV : StarRing ↥V :=
    { star := fun a => ⟨star (a : U), V.star_mem' a.2⟩
      star_involutive := fun a => Subtype.ext (by
        show star (star (a : U)) = (a : U)
        rw [star_star])
      star_mul := fun a b => Subtype.ext (by
        show star ((a : U) * (b : U)) = star (b : U) * star (a : U)
        rw [star_mul])
      star_add := fun a b => Subtype.ext (by
        show star ((a : U) + (b : U)) = star (a : U) + star (b : U)
        rw [star_add]) }
  have hgψ : ∀ s : S, g (ψ s) = h (ψ s) := fun s => RingHom.congr_fun hgh s
  have hclV : (Subring.closure (Set.range φ) : Set U) ⊆ (V : Set U) := by
    refine Subring.closure_le.mpr ?_
    rintro x ⟨s, rfl⟩
    exact subset_starRegularClosure _ (subset_starSubringClosure _ (Set.mem_range_self s))
  -- ## the part `A ⊆ V` on which `g` and `h` agree
  let A : Subring U :=
    { carrier := {x | x ∈ (V : Set U) ∧
        ∀ hx : x ∈ (V : Set U), g (⟨x, hx⟩ : ↥V) = h ⟨x, hx⟩}
      zero_mem' := ⟨V.toSubring.zero_mem, fun hx => by
        rw [show (⟨0, hx⟩ : ↥V) = 0 from Subtype.ext (by simp)]
        simp⟩
      one_mem' := ⟨V.toSubring.one_mem, fun hx => by
        rw [show (⟨1, hx⟩ : ↥V) = 1 from Subtype.ext (by simp)]
        simp⟩
      add_mem' := by
        rintro x y hx hy
        exact ⟨V.toSubring.add_mem hx.1 hy.1, fun hxy => by
          rw [show (⟨x + y, hxy⟩ : ↥V) = ⟨x, hx.1⟩ + ⟨y, hy.1⟩ from Subtype.ext rfl,
            map_add, map_add, hx.2 _, hy.2 _]⟩
      neg_mem' := by
        rintro x hx
        exact ⟨V.toSubring.neg_mem hx.1, fun hx' => by
          rw [show (⟨-x, hx'⟩ : ↥V) = -⟨x, hx.1⟩ from Subtype.ext rfl,
            map_neg, map_neg, hx.2 _]⟩
      mul_mem' := by
        rintro x y hx hy
        exact ⟨V.toSubring.mul_mem hx.1 hy.1, fun hxy => by
          rw [show (⟨x * y, hxy⟩ : ↥V) = ⟨x, hx.1⟩ * ⟨y, hy.1⟩ from Subtype.ext rfl,
            map_mul, map_mul, hx.2 _, hy.2 _]⟩ }
  have hrangeA : (Set.range φ) ⊆ (A : Set U) := by
    rintro x ⟨s, rfl⟩
    exact ⟨subset_starRegularClosure _
      (subset_starSubringClosure _ (Set.mem_range_self s)), fun hx => by
        rw [show (⟨φ s, hx⟩ : ↥V) = ψ s from Subtype.ext rfl]
        exact hgψ s⟩
  have hclA : (Subring.closure (Set.range φ) : Set U) ⊆ (A : Set U) :=
    Subring.closure_le.mpr hrangeA
  -- ## the part of `V` whose star lies in `A`
  let Astar : Subring U :=
    { carrier := {x | star x ∈ (V : Set U) ∧
        ∀ hx : star x ∈ (V : Set U), g (⟨star x, hx⟩ : ↥V) = h ⟨star x, hx⟩}
      zero_mem' := ⟨V.star_mem' V.toSubring.zero_mem, fun hx => by
        rw [show (⟨star (0 : U), hx⟩ : ↥V) = 0 from Subtype.ext (by simp)]
        simp⟩
      one_mem' := ⟨V.star_mem' V.toSubring.one_mem, fun hx => by
        rw [show (⟨star (1 : U), hx⟩ : ↥V) = 1 from Subtype.ext (by simp)]
        simp⟩
      add_mem' := by
        rintro x y hx hy
        refine ⟨?_, fun hxy => ?_⟩
        · rw [star_add]
          exact V.toSubring.add_mem hx.1 hy.1
        · have e : (⟨star (x + y), hxy⟩ : ↥V) =
              ⟨star x, hx.1⟩ + ⟨star y, hy.1⟩ := by
            apply Subtype.ext
            show star (x + y) = star x + star y
            rw [star_add]
          calc g (⟨star (x + y), hxy⟩ : ↥V)
              = g (⟨star x, hx.1⟩ + ⟨star y, hy.1⟩ : ↥V) := congrArg g e
            _ = h (⟨star x, hx.1⟩ + ⟨star y, hy.1⟩ : ↥V) := by
                rw [map_add, map_add, hx.2 _, hy.2 _]
            _ = h (⟨star (x + y), hxy⟩ : ↥V) := (congrArg h e).symm
      neg_mem' := by
        rintro x hx
        refine ⟨?_, fun hx' => ?_⟩
        · rw [star_neg]
          exact V.toSubring.neg_mem hx.1
        · have e : (⟨star (-x), hx'⟩ : ↥V) = -⟨star x, hx.1⟩ := by
            apply Subtype.ext
            show star (-x) = -star x
            rw [star_neg]
          calc g (⟨star (-x), hx'⟩ : ↥V)
              = g (-⟨star x, hx.1⟩ : ↥V) := congrArg g e
            _ = h (-⟨star x, hx.1⟩ : ↥V) := by rw [map_neg, map_neg, hx.2 _]
            _ = h (⟨star (-x), hx'⟩ : ↥V) := (congrArg h e).symm
      mul_mem' := by
        rintro x y hx hy
        refine ⟨?_, fun hxy => ?_⟩
        · rw [star_mul]
          exact V.toSubring.mul_mem hy.1 hx.1
        · have e : (⟨star (x * y), hxy⟩ : ↥V) =
              ⟨star y, hy.1⟩ * ⟨star x, hx.1⟩ := by
            apply Subtype.ext
            show star (x * y) = star y * star x
            rw [star_mul]
          calc g (⟨star (x * y), hxy⟩ : ↥V)
              = g (⟨star y, hy.1⟩ * ⟨star x, hx.1⟩ : ↥V) := congrArg g e
            _ = h (⟨star y, hy.1⟩ * ⟨star x, hx.1⟩ : ↥V) := by
                rw [map_mul, map_mul, hy.2 _, hx.2 _]
            _ = h (⟨star (x * y), hxy⟩ : ↥V) := (congrArg h e).symm }
  -- ## the star-closed part `P`
  let P : Subring U := A ⊓ Astar
  have hPmem : ∀ x : U, x ∈ (P : Set U) ↔ x ∈ (A : Set U) ∧ x ∈ (Astar : Set U) :=
    fun x => Subring.mem_inf
  have hrangeP : (Set.range φ) ⊆ (P : Set U) := by
    rintro x ⟨s, rfl⟩
    rw [hPmem]
    exact ⟨hrangeA ⟨s, rfl⟩, hclV (hstar s), hclA (hstar s) |>.2⟩
  have hPstar : ∀ x : U, x ∈ (P : Set U) → star x ∈ (P : Set U) := by
    intro x hx
    rw [hPmem] at hx ⊢
    refine ⟨⟨hx.2.1, fun h => hx.2.2 h⟩, ?_, ?_⟩
    · rw [star_star]
      exact hx.1.1
    · intro h
      rw [show (⟨star (star x), h⟩ : ↥V) = ⟨x, hx.1.1⟩ from Subtype.ext (by simp)]
      exact hx.1.2 hx.1.1
  have hE : ∀ x : U, x ∈ (P : Set U) → star x = x → ∀ y : U, IsRelativeInverse x y →
      y ∈ (P : Set U) := by
    intro x hxP hxs y hy
    rw [hPmem] at hxP ⊢
    obtain ⟨hxV, hxagr⟩ := hxP.1
    obtain ⟨hxSV, hxSagr⟩ := hxP.2
    have hyV : y ∈ (V : Set U) :=
      StarRegular.relativeInverse_mem_starRegularClosure hxV hy
    have hxadj : star (⟨x, hxV⟩ : ↥V) = ⟨x, hxV⟩ := by
      apply Subtype.ext
      show star x = x
      exact hxs
    have hrel : IsRelativeInverse (⟨x, hxV⟩ : ↥V) (⟨y, hyV⟩ : ↥V) :=
      ⟨by apply Subtype.ext; show x * y * x = x; exact hy.left,
        by apply Subtype.ext; show y * x * y = y; exact hy.right,
        by apply Subtype.ext; show star (x * y) = x * y; exact hy.star_left,
        by apply Subtype.ext; show star (y * x) = y * x; exact hy.star_right⟩
    have hagr : g (⟨x, hxV⟩ : ↥V) = h ⟨x, hxV⟩ := hxagr hxV
    have hyagr : g (⟨y, hyV⟩ : ↥V) = h ⟨y, hyV⟩ :=
      NaturalExtension.map_relativeInverse_eq_of_selfAdjoint g h hxadj hrel hagr
    have hys : star y = y :=
      NaturalExtension.star_eq_self_of_isRelativeInverse_selfAdjoint hxs hy
    exact ⟨⟨hyV, fun h => hyagr⟩, by rw [hys]; exact hyV, fun h => by
      rw [show (⟨star y, h⟩ : ↥V) = ⟨y, hyV⟩ from Subtype.ext hys]
      exact hyagr⟩
  have hRE : ((starSubringClosure (Set.range φ) : StarSubring U) : Set U) ⊆ (P : Set U) :=
    starSubringClosure_le (T := ⟨P, fun hx => hPstar _ hx⟩) hrangeP
  have hsub : ((starRegularClosure (starSubringClosure (Set.range φ)) : StarSubring U) : Set U) ⊆
      (P : Set U) :=
    StarRegular.starRegularClosure_le_of_isRelativeInverse_selfAdjoint
      (starSubringClosure (Set.range φ)) P hRE hE
  refine RingHom.ext fun v => ?_
  have hvP : (v : U) ∈ (P : Set U) := hsub v.2
  rw [hPmem] at hvP
  exact hvP.1.2 v.2

/-- **The corrected form of `isEpic_starClosureCod`**, in the vocabulary in which the node N6
route needs it: `IsEpic (starClosureCod E φK H)` holds as soon as the star of every element of the
image of `toUK E φK H` is a ring expression in that image.

This is `isEpic_codRestrict_starRegularClosure_of_star_mem` applied to
`φ = (toUK E φK H).toRingHom`: `starClosureCod E φK H` is `φ` with its codomain restricted to
`starRegularClosure (starSubringClosure (Set.range φ))`, i.e. to
`starClosureOfSubgroup E φK H`.

The hypothesis is the one that the paper gets for free: for `K ⊆ ℂ` closed under complex
conjugation and the canonical `kAlgebra E φK`, `K[↥H] → U(G)` is a `∗`-homomorphism for the star
`∑ k_h · h ↦ ∑ conj (k_h) · h⁻¹` on `K[↥H]`, hence `star (toUK x) = toUK (star x) ∈ Set.range toUK`.
(For `h ∈ ↥H`, `star (genU E h) = genU E h⁻¹` always holds, by `ι_star` and the involution of
`ℂ[G]`; only the scalars can fail, and the counterexample in the module docstring shows that
without this hypothesis the statement is false.) -/
theorem isEpic_starClosureCod_of_star_mem {K : Type} [Field K] {G : Type} [Group G]
    (E : Work.ORVonNeumann.StarRegularEnvelope G) (φK : K →+* ℂ) [Algebra K E.U] (H : Subgroup G)
    (hstar : ∀ x : MonoidAlgebra K ↥H,
      star (Work.ORBridgeLinnell.toUK E φK H x) ∈
        Subring.closure (Set.range (Work.ORBridgeLinnell.toUK E φK H))) :
    Work.ORHughesFree.IsEpic (Work.ORDivLoc.starClosureCod E φK H) :=
  isEpic_codRestrict_starRegularClosure_of_star_mem
    (Work.ORBridgeLinnell.toUK E φK H).toRingHom hstar

end Work.ORDivLoc.Closure
