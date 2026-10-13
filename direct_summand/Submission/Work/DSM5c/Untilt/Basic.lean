import Mathlib

/-!
# DSM5c / PB3 — the untilt of a perfect ring: vocabulary

Node **PB3** of the M5c design (`sources/dsmap/direct_summand_mix_design.md` §3): the *untilt
functor* `R ↦ W(R)/ξ` on perfect, `ϖ`-adically complete, `ϖ`-torsion-free rings, used to build the
perfectoid charts `D_S` of `area_M5c` as untilts of the completed perfections of the tilted charts.

Mathlib's `Mathlib/RingTheory/WittVector/Complete.lean` already contains the two facts that make
this node tractable, for `k` a perfect ring of characteristic `p`:

* `WittVector.eq_zero_of_p_mul_eq_zero` — `𝕎 k` is `p`-torsion free;
* `WittVector.quotientPEquiv : 𝕎 k ⧸ (p) ≃+* k` (with `WittVector.ker_constantCoeff`,
  `WittVector.mem_span_p_iff_coeff_zero_eq_zero`).

This file sets up the vocabulary: the element `ξ` and the ring `untilt`.  Following the design (and
the conventions of this workspace, where the pseudo-uniformizer of a `PerfectoidData p W` satisfies
`ϖ 0 ^ p = p * unit`), the input of the untilt is the *tilt-side* element `w` with `p = ♯ w = [w]`;
then

  `ξ := [w] - p`  in `𝕎 R`,  `untilt R w := 𝕎 R ⧸ (ξ)`,

and `♯(w) = p` holds *by construction* in `untilt R w`, while the pseudo-uniformizer of the untilt
is the image of `[w ^ (1/p)]` (whose `p`-th power is `[w] = p`).  With
`constantCoeff = coeff 0 : 𝕎 R →+* R` one has `constantCoeff ξ = w` (`Work.DSM5c.constantCoeff_xi`),
so the mod-`p` reduction of the untilt is

  `(untilt R w) ⧸ (p) ≅ R ⧸ (w)`,

which is exactly the mod-`p` comparison used by the M5c transport (cf.
`DSMap.Mix.perfectoid_modp_tilt`: `C ⧸ (p) ≅ C♭ ⧸ (ϖ♭) ^ p`, here in the form `R ⧸ (w)` with
`w = (ϖ♭) ^ p`).

## Warning (a trap worth recording)

With the naive choice `ξ := [ϖ♭] - p` (using the pseudo-uniformizer `ϖ♭` of `R` itself instead of
`w` with `p = ♯w`) the mod-`p` reduction is `R ⧸ (ϖ♭)`, *not* `R ⧸ ((ϖ♭) ^ p)`: the two differ
already for `R = 𝔽_p[x ^ (1/p^∞)]`, `C = ℤ_p[x ^ (1/p^∞)]^`, where the correct answer is
`𝔽_p[x ^ (1/p^∞)] ⧸ (x ^ p)`.  Hence the exponent `p` in the definition above is essential.

## What remains (see `Submission/Work/DSM5c/NOTES.md` §5)

`untilt R w` is `p`-torsion free, `p`-adically complete, has `PerfectoidData p` (with
`ϖ := ♯(w ^ (1/p))`), has tilt `≅ R` (via `PerfectionMap`/`Perfection.equiv`), is natural in `R`
and commutes with finite products; the mod-`p` comparison above, the chart-level comparison and the
dévissage `p ↦ p^m` then complete the M5c transport.  None of these is in this file yet.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.DSM5c

universe a

open WittVector

/-- **PB3, the element `ξ`**: for a ring `R` and `w ∈ R` playing the role of "`p` in the tilt"
(i.e. `p = ♯ w` in the untilt to be built), `ξ := [w] - p` in the ring of Witt vectors `𝕎 R`.

Kept as an `abbrev` so that the instances of `untilt` below are found without explicit instance
declarations. -/
noncomputable abbrev xi (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] (w : R) :
    WittVector p R :=
  WittVector.teichmuller p w - (p : WittVector p R)

/-- **PB3, the untilt ring**: `untilt R w := 𝕎 R ⧸ (ξ)`.  It is the ring that receives the tilt `R`
via `♯`; see `NOTES.md` §5 for what remains to be proved about it (torsion-freeness, `p`-adic
completeness, the `PerfectoidData` structure, the tilt identification and naturality). -/
noncomputable abbrev untilt (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] (w : R) :
    Type a :=
  WittVector p R ⧸ Ideal.span {xi p R w}

variable {p : ℕ} [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]

/-- The defining property of `ξ`: its `0`-th coefficient (equivalently, its image under the ring
homomorphism `constantCoeff : 𝕎 R →+* R`) is `w`.  This is what makes the mod-`p` reduction of the
untilt equal to `R ⧸ (w)`. -/
@[simp] theorem constantCoeff_xi (w : R) :
    WittVector.constantCoeff (xi p R w) = w := by
  rw [xi, map_sub, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have h : (p : WittVector p R) ∈ RingHom.ker (WittVector.constantCoeff (p := p) (R := R)) := by
    rw [WittVector.ker_constantCoeff]
    exact Ideal.mem_span_singleton_self _
  simp only [RingHom.mem_ker] at h
  rw [h, sub_zero]

namespace Untilt

/-- The structure map `𝕎 R → untilt R w`. -/
noncomputable def mk (w : R) : WittVector p R →+* untilt p R w :=
  Ideal.Quotient.mk _

/-- `ξ` vanishes in the untilt. -/
@[simp] theorem mk_xi (w : R) : mk (p := p) (R := R) w (xi p R w) = 0 := by
  rw [mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- **`p = ♯ w` in the untilt** (`♯` being the Teichmüller map): the image of `p` is the image of
`[w]`.  This is the relation that makes the untilt a "perfectoid-shaped" ring: the
pseudo-uniformizer is the image of `[w ^ (1/p)]` and its `p`-th power is `p`. -/
theorem mk_p_eq_mk_teichmuller (w : R) :
    mk (p := p) (R := R) w (p : WittVector p R) =
      mk (p := p) (R := R) w (WittVector.teichmuller p w) := by
  have h : mk (p := p) (R := R) w (xi p R w) = 0 := mk_xi (p := p) (R := R) w
  simp only [xi, map_sub, sub_eq_zero] at h
  exact h.symm

end Untilt

end Work.DSM5c
