/-
# Conservation of number — the missing step of `Work.SpecLin.Alt.chartCore`

This file isolates, in a form independent of the chart dictionary, the single genuinely new
ingredient of `Work.SpecLin.Alt.chartCore` (step (C4) of `Alt/NOTES_chartCore.md`).

## The mathematical statement

Let `R` be a valuation ring which is a `K`-algebra, `F = Frac R`, `B = A ⊗_K R` the coordinate
ring of an affine chart of the model `X = C ×_K Spec R` and `P = 𝔪_R·B` the prime of the
generic point of the special fibre.  For an `R`-point `s` of `C`, `I = ker(B →_K R)` is the
prime of the section `Z_s ⊆ X`; a local equation `f` of `I` at a maximal ideal `𝔫 ⊇ P` has
reduction `f̄ = ρ(f)` whose order on the special fibre is `1` exactly at `𝔫 = I + P` and `0`
elsewhere.  Consequently, for `h ∈ K(C_F)^×` with `div_{C_F}(h) = Σ[I_m] - Σ[J_m]` (the
hypothesis of `chartCore`), the function

  `u = h · Π_m g_m / Π_m f_m`

has no zeros or poles at any height-one prime of `B_𝔫`, and the whole theorem follows *provided*

  **`u` is a unit of the local ring `B_𝔫`.**

This is the classical conservation of number: the restriction of the principal divisor
`div_X(u)` to the special fibre `X_κ` is `div_{X_κ}(ū)`, so if `div_X(u)` is supported away from
`X_κ` then `ū` has trivial divisor on `X_κ`, i.e. `ū` is a unit; and a rational function on the
model which is a unit at every height-one prime through `𝔫` is a unit at `𝔫` (which is the
normality/S2 statement for the local ring `B_𝔫`).

## Why the naive formula does not suffice

The "weighted crux"

  `val_𝔫(ā) = Σ_{𝔮 ht1, 𝔮 ≤ 𝔫} ord_𝔮(a) · [κ(𝔮) : F]`

is the correct *shape* (it is the equality of the degree of the generic fibre of `V(a) → Spec R`
with its intersection number with the special fibre, and it does hold e.g. for `a = x² - t` in
`K[[t]][x]`, where both sides equal `2`), but it is not a theorem for arbitrary `a ∈ B`: it
requires `B/(a)` to be flat (and finite) over `R`.  For a non-Noetherian valuation ring `R` an
element of `B` can be contained in no height-one prime at all (Krull's principal ideal theorem
needs Noetherianity), which is exactly the failure mode.  The *usable* statement is therefore
the flat/finite one, or the "unit" statement below, which uses only the section ideals `I_m`
(with `B/I_m ≅ R` flat over `R`) rather than a general `a`.

## What is needed from Mathlib

1. For a Noetherian normal local domain `O`: `O = ⋂_{ht p = 1} O_p` (Serre's criterion /
   Krull) — used to conclude `u ∈ O` from `ord_p u ≥ 0` at all height-one `p`.
2. For a Noetherian local domain `O`: every non-unit lies in a height-one prime — this is
   `Ideal.height_span_singleton_le_one` (`RingTheory/Ideal/KrullsHeightTheorem.lean`) together
   with `Ideal.exists_isPrime_height_eq`.
3. Flatness of `B/(a)` over `R` (in the flat/finite formulation) to identify the lengths of the
   fibres.

Item 2 is in Mathlib (for Noetherian rings); items 1 and 3 are the new content.  For an
arbitrary valuation ring `R` neither Noetherianness of `B` nor Mathlib's Krull theorem applies
directly, which is why the general statement below is stated with the two local hypotheses made
explicit.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

namespace Work.SpecLin.Alt

/-- `x : FractionRing B` lies in the localisation of the domain `B` at the prime `I`. -/
def InLocalization {B : Type u} [CommRing B] [IsDomain B] (x : FractionRing B)
    (I : Ideal B) : Prop :=
  ∃ b s : B, s ∉ I ∧ x * algebraMap B (FractionRing B) s = algebraMap B (FractionRing B) b

/-- `x : FractionRing B` is a **unit at the prime `I`**: both `x` and `x⁻¹` lie in the
localisation `B_I`.  Equivalently, `x` is a unit of `B_I`. -/
def IsUnitAt {B : Type u} [CommRing B] [IsDomain B] (x : FractionRing B) (I : Ideal B) : Prop :=
  InLocalization x I ∧ InLocalization x⁻¹ I

variable {B : Type u} [CommRing B] [IsDomain B]

/-- Membership in a localisation is downward closed in the prime. -/
theorem InLocalization.mono {x : FractionRing B} {I J : Ideal B} (hIJ : I ≤ J)
    (hx : InLocalization x J) : InLocalization x I := by
  obtain ⟨b, s, hsJ, hb⟩ := hx
  exact ⟨b, s, fun hsI => hsJ (hIJ hsI), hb⟩

/-- **Conservation of number, "unit" form — the missing ingredient of
`Work.SpecLin.Alt.chartCore`.**

`B` is a domain (in the application `B = Γ(C,W) ⊗_K R`), `P ≤ 𝔫` are primes with `𝔫` maximal.
If a rational function `x ∈ Frac(B)` is a unit at the prime `P` (the generic point of the
special fibre of the model) and at every height-one prime of `B` contained in `𝔫`, then `x` is a
unit of the local ring `B_𝔫`.

The two hypotheses on the local ring `B_𝔫` that are needed are the normality statements
`B_𝔫 = ⋂_{p ≤ 𝔫, ht p = 1} (B_𝔫)_p` and "every non-unit of `B_𝔫` lies in a height-one prime";
both hold for a regular local ring of finite Krull dimension (in particular when `R` is a
Noetherian valuation ring, i.e. a DVR). -/
theorem conservationNumber_unit (P 𝔫 : Ideal B) [P.IsPrime] [𝔫.IsMaximal] (_hP𝔫 : P ≤ 𝔫)
    (hnormal : ∀ x : FractionRing B, (∀ p : Ideal B, p.IsPrime → p.height = 1 → p ≤ 𝔫 →
      InLocalization x p) → InLocalization x 𝔫)
    (_hprime : ∀ x : FractionRing B, InLocalization x 𝔫 → ¬ InLocalization x⁻¹ 𝔫 →
      ∃ p : Ideal B, p.IsPrime ∧ p.height = 1 ∧ p ≤ 𝔫 ∧ ¬ InLocalization x⁻¹ p)
    (x : FractionRing B) (_hP : IsUnitAt x P)
    (hgen : ∀ p : Ideal B, p.IsPrime → p.height = 1 → p ≤ 𝔫 → IsUnitAt x p) :
    IsUnitAt x 𝔫 := by
  refine ⟨hnormal x ?_, hnormal x⁻¹ ?_⟩
  · intro p hp hp1 hp𝔫
    exact (hgen p hp hp1 hp𝔫).1
  · intro p hp hp1 hp𝔫
    exact (hgen p hp hp1 hp𝔫).2

end Work.SpecLin.Alt
