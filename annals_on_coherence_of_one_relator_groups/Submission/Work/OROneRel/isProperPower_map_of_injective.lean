/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".

# `IsProperPower` under an injective relabelling of the generators

Being a proper power in a free group is *intrinsic* under an injective map of the generating
sets: an element `x ∈ F(γ)` is a proper power `v ^ k` (`k ≥ 2`) if and only if its image under
`FreeGroup.map f : F(γ) →* F(δ)` is one, for `f : γ → δ` injective.

The forward implication is formal and needs nothing: `FreeGroup.map f` is a homomorphism, so it
sends `v ^ k` to `(FreeGroup.map f v) ^ k`.

The backward implication is the interesting one, and it needs that `f` is injective on generators.
The point is that although `FreeGroup.map f` is *not* surjective, it always admits a
**retraction** as soon as `f` is injective: the image of `f` consists of free generators, so
sending each generator in the image back to its (unique) preimage and every other generator to `1`
extends to a homomorphism `F(δ) →* F(γ)` by `FreeGroup.lift`.  Concretely, with

`g d = if ∃ b, f b = d then of b.choose else 1`

the composite `FreeGroup.lift g ∘ FreeGroup.map f` fixes every generator, hence is the identity
(this is `hsplit` below, proved by the induction principle of the free group).  Applying this
retraction to a witness `FreeGroup.map f x = u ^ k` produces a witness `x = (FreeGroup.lift g u) ^ k`
in `F(γ)`, which is exactly `IsProperPower x`.

Note that injectivity of `f` (rather than mere injectivity of `FreeGroup.map f`) is what is used:
it is the source of the retraction, and it is necessary — e.g. with the two-element generating set
`γ = {a, b}` mapping onto the single generator `δ = {c}` the statement fails for `x = a * b⁻¹`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u v

theorem isProperPower_map_of_injective {γ : Type u} {δ : Type v} {f : γ → δ}
    (hf : Function.Injective f) (x : FreeGroup γ) :
    Work.OROneRel.IsProperPower (FreeGroup.map f x) ↔ Work.OROneRel.IsProperPower x := by
  classical
  constructor
  · -- `IsProperPower` against the graph of `f`: extract a root with the retraction of `map f`.
    rintro ⟨u, k, hk, hxk⟩
    let g : δ → FreeGroup γ :=
      fun d => if h : ∃ b : γ, f b = d then FreeGroup.of h.choose else 1
    -- `g` inverts `f` on the generators lying in the image of `f`.
    have hg : ∀ b : γ, g (f b) = FreeGroup.of b := by
      intro b
      have hb : ∃ b' : γ, f b' = f b := ⟨b, rfl⟩
      show dite (∃ b' : γ, f b' = f b) (fun h => FreeGroup.of h.choose) (fun _ => 1) =
        FreeGroup.of b
      rw [dif_pos hb]
      exact congrArg FreeGroup.of (hf (Exists.choose_spec hb))
    -- hence `FreeGroup.lift g` is a retraction of `FreeGroup.map f`.
    have hsplit : ∀ y : FreeGroup γ, FreeGroup.lift g (FreeGroup.map f y) = y := by
      intro y
      induction y using FreeGroup.induction_on with
      | one => simp
      | of b => rw [FreeGroup.map.of, FreeGroup.lift_apply_of]; exact hg b
      | inv_of b ih => rw [map_inv, map_inv, ih]
      | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
    refine ⟨FreeGroup.lift g u, k, hk, ?_⟩
    have h1 := congrArg (FreeGroup.lift g) hxk
    rw [map_pow] at h1
    rw [hsplit x] at h1
    exact h1
  · rintro ⟨u, k, hk, hxk⟩
    exact ⟨FreeGroup.map f u, k, hk, by rw [hxk, map_pow]⟩

end Work.OROneRel
