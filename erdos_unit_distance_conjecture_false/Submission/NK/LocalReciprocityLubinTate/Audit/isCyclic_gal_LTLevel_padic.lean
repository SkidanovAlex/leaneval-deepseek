import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Audit.PadicInstance
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units

/-!
# The Galois group of a `p`-adic Lubin–Tate level is cyclic (for odd `p`)

For an odd prime `p`, a uniformiser `π` of `𝒪[ℚ_[p]]` (an irreducible element of the ring of
integers) and `n ≥ 1`, the `n`-th Lubin–Tate level `K_n = ℚ_[p](Λ_n)` has **cyclic** Galois group
over `ℚ_[p]`:

`Gal(K_n/ℚ_[p]) ≃ (𝒪[ℚ_[p]]/𝔪^n)ˣ ≅ (ℤ/p^n)ˣ`.

The Lubin–Tate reciprocity isomorphism at level `n`
(`NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units`, Milne, *CFT*,
Theorem I.3.6 (b)) identifies the Galois group with the group of units of the truncated ring of
integers `𝒪[F]/𝔪^n`.  For `F = ℚ_[p]` this ring is `ℤ_[p]/p^nℤ_[p] ≅ ℤ/p^nℤ`: the reduction
`PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)` has kernel `span {p^n} = 𝔪^n` and is surjective
(every residue class comes from an integer).  The unit group of `ℤ/p^nℤ` is cyclic for odd `p`
(`ZMod.isCyclic_units_of_prime_pow`), which gives the claim.

The hypothesis `2 < p` is essential: for `p = 2` the group `(ℤ/2^nℤ)ˣ ≅ {±1} × (cyclic)` is not
cyclic for `n ≥ 3`.

## Main results

* `NK.LocalReciprocityLubinTate.Audit.ker_toZModPow_eq_maximalIdeal_pow`,
  `...toZModPow_surjective`;
* `NK.LocalReciprocityLubinTate.Audit.isCyclic_units_quot_maximalIdeal_pow_padic`;
* `NK.LocalReciprocityLubinTate.Audit.isCyclic_gal_LTLevel_padic`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Audit

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- **The kernel of `PadicInt.toZModPow n` is the `n`-th power of the maximal ideal of `ℤ_[p]`.**

Mathlib's `PadicInt.ker_toZModPow` states the kernel as `span {p^n}`; since `p` generates the
maximal ideal (`PadicInt.maximalIdeal_eq_span_p`) and `span {x^n} = span {x}^n`
(`Ideal.span_singleton_pow`), this is `𝔪^n`. -/
lemma ker_toZModPow_eq_maximalIdeal_pow (n : ℕ) :
    RingHom.ker (PadicInt.toZModPow (p := p) n) = (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
  rw [PadicInt.ker_toZModPow, ← Ideal.span_singleton_pow, ← PadicInt.maximalIdeal_eq_span_p]

/-- **`PadicInt.toZModPow n` is surjective**: every class in `ℤ/p^nℤ` is represented by an integer,
and `ℤ` maps to `ℤ_[p]` compatibly with `toZModPow` (both composites `ℤ →+* ℤ/p^nℤ` are ring
homomorphisms out of `ℤ`, hence equal). -/
lemma toZModPow_surjective (n : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) n) := by
  intro y
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p ^ n) y
  refine ⟨(k : ℤ_[p]), ?_⟩
  have hcomp : ((PadicInt.toZModPow (p := p) n).comp (Int.castRingHom ℤ_[p]))
      = (Int.castRingHom (ZMod (p ^ n))) := RingHom.ext_int _ _
  have hk' : PadicInt.toZModPow (p := p) n (k : ℤ_[p]) = (k : ZMod (p ^ n)) :=
    RingHom.congr_fun hcomp k
  rw [hk', hk]

/-- **The units of `𝒪[ℚ_[p]]/𝔪^n` are cyclic for odd `p`.**

The composite `𝒪[ℚ_[p]] ≃+* ℤ_[p] →+* ℤ/p^nℤ` (the ring of integers of `ℚ_[p]` is `ℤ_[p]`,
`Audit.padicIntegerEquiv`) is surjective with kernel `𝔪^n`, so it induces a ring isomorphism
`𝒪[ℚ_[p]]/𝔪^n ≃+* ℤ/p^nℤ`.  Transporting `ZMod.isCyclic_units_of_prime_pow` along it gives the
result. -/
theorem isCyclic_units_quot_maximalIdeal_pow_padic (hp2 : 2 < p) (n : ℕ) :
    IsCyclic ((↥(ValuativeRel.valuation ℚ_[p]).integer ⧸
      (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation ℚ_[p]).integer) ^ n)ˣ) := by
  have hp : p.Prime := Fact.out
  let O := ↥(ValuativeRel.valuation ℚ_[p]).integer
  let e : O ≃+* ℤ_[p] := padicIntegerEquiv p
  let φ : O →+* ZMod (p ^ n) := (PadicInt.toZModPow (p := p) n).comp (e : O →+* ℤ_[p])
  -- the isomorphism intertwines the two maximal ideals
  have hmapO : Ideal.map (e : O →+* ℤ_[p]) ((IsLocalRing.maximalIdeal O) ^ n)
      = (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    rw [Ideal.map_pow (f := (e : O →+* ℤ_[p])) (IsLocalRing.maximalIdeal O) n,
      IsLocalRing.map_maximalIdeal_of_surjective (e : O →+* ℤ_[p]) e.surjective]
  have hcomap : Ideal.comap (e : O →+* ℤ_[p]) ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n)
      = (IsLocalRing.maximalIdeal O) ^ n := by
    rw [← hmapO]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [Ideal.mem_comap,
        Ideal.mem_map_iff_of_surjective (f := (e : O →+* ℤ_[p])) (RingEquiv.surjective e)] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [RingEquiv.injective e hyx] at hy
    · rw [Ideal.mem_comap,
        Ideal.mem_map_iff_of_surjective (f := (e : O →+* ℤ_[p])) (RingEquiv.surjective e)]
      exact ⟨x, hx, rfl⟩
  have hkerφ : RingHom.ker φ
      = Ideal.comap (e : O →+* ℤ_[p]) ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, ← ker_toZModPow_eq_maximalIdeal_pow p n,
      RingHom.mem_ker]
    rfl
  have hker : RingHom.ker φ = (IsLocalRing.maximalIdeal O) ^ n := by
    rw [hkerφ, hcomap]
  have hsurj : Function.Surjective φ :=
    (toZModPow_surjective p n).comp (RingEquiv.surjective e)
  -- the ring isomorphism `𝒪[ℚ_[p]]/𝔪^n ≃+* ℤ/p^nℤ`
  have hiso : O ⧸ (IsLocalRing.maximalIdeal O) ^ n ≃+* ZMod (p ^ n) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hcyc : IsCyclic (ZMod (p ^ n))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp (by omega) n
  exact (Units.mapEquiv hiso.toMulEquiv).isCyclic.mpr hcyc

/-- **The Galois group of the `n`-th `p`-adic Lubin–Tate level is cyclic** for odd `p`.

This is the Lubin–Tate reciprocity isomorphism `Gal(K_n/ℚ_[p]) ≃* (𝒪[ℚ_[p]]/𝔪^n)ˣ`
(`NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units`) combined with
`isCyclic_units_quot_maximalIdeal_pow_padic`. -/
theorem isCyclic_gal_LTLevel_padic (p : ℕ) [Fact p.Prime] (hp2 : 2 < p) (n : ℕ) (hn : 1 ≤ n)
    (π : ↥(ValuativeRel.valuation ℚ_[p]).integer) (hπ : Irreducible π) :
    IsCyclic (↥(NK.LocalReciprocityLubinTate.LTLevel ℚ_[p] (π : ℚ_[p])
      (NK.LocalReciprocityLubinTate.residueCard ℚ_[p]) n) ≃ₐ[ℚ_[p]]
      ↥(NK.LocalReciprocityLubinTate.LTLevel ℚ_[p] (π : ℚ_[p])
      (NK.LocalReciprocityLubinTate.residueCard ℚ_[p]) n)) := by
  obtain ⟨w⟩ :=
    NK.LocalReciprocityLubinTate.LubinTate.nonempty_autLTLevel_mulEquiv_units
      (F := ℚ_[p]) π hπ n hn
  exact w.isCyclic.mpr (isCyclic_units_quot_maximalIdeal_pow_padic p hp2 n)

end

end NK.LocalReciprocityLubinTate.Audit
