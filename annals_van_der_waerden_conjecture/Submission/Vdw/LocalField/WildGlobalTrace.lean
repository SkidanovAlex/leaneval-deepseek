import Mathlib
import Submission.Vdw.LocalField.TeichQuotTrace
import Submission.Vdw.LocalField.WildWitnessReduction
import Submission.Vdw.LocalField.WildTrace
import Submission.Vdw.WildBound
import Submission.Vdw.TameExponent

open scoped NumberField WithZero Valued
open IsDedekindDomain
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# WildGlobalTrace — the global transport of the local wild-witness trace

This module closes the **S1 gate** (`hwild`, the per-prime wild different bound
`m_P ≤ e_P − 1 + e_P·v_p(e_P)`; the hypothesis of the proved
`WildBound.discrVal_le_wild`), which had been reduced over Sessions 118–133 to a
*witness with nonzero quotient trace*.

The local side (Sessions 129–133, `WildGenerator` + `TeichQuotTrace`) produces
the Teichmüller-lift class `mk (teich p P α)` in the local quotient
`kpInt ⧸ (p^n)` whose trace over `QpInt ⧸ (p^n)` is nonzero at the critical
level `n = v_p(e) + 1`.  What remained was to transport this to a statement
about the GLOBAL quotient `𝓞 K ⧸ P^(e·n)` over `ℤ/(p^n)` — this module.

Contents:

* `baseIso` — the base-ring identification
  `ℤ/(p^n) ≃+* ℤ_[p]/(p^n)` (through `ZMod (p^n)`, `Int.quotientSpanNatEquivZMod`
  and `PadicInt.toZModPow`, and the ring of integers of the `ℚ_p`-completion);
* `subsingleton_quotientIntRingHom` — there is at most ONE ring hom
  `ℤ ⧸ I →+* S` (`ℤ` is the initial ring, and `ℤ ⧸ I` is a quotient of `ℤ`);
  consequently the compatibility hypothesis of
  `Algebra.trace_eq_of_equiv_equiv` is *automatic* for base ring `ℤ ⧸ I`;
* `globalLocalIsoMapped` — `𝓞 K ⧸ P^(e·n) ≃+* kpInt ⧸ (p^n)·kpInt` in the
  `Ideal.map`-spelling of the local algebra structure;
* **`exists_trace_ne_zero_global`** — the transported witness: there is
  `z : 𝓞 K` whose class in `𝓞 K ⧸ P^(e·n)` has nonzero `ℤ/(p^n)`-trace;
* **`wild_different_count_le`** — the per-prime wild different bound, for ALL
  primes (no case distinction, no tameness hypothesis);
* `discrVal_le_wild_unconditional` — the unconditional small-prime cap
  `v_p(|disc K|) ≤ [K:ℚ]·(1 + ⌊log_p [K:ℚ]⌋)`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **The base-ring identification** `ℤ/(p^n) ≃+* QpInt p ⧸ (p^n)`: through
`ZMod (p^n)`, the `p`-adic integers (surjecting onto `ZMod (p^n)` with kernel
`(p^n)`), and the identification `QpInt p ≃+* ℤ_[p]` of the ring of integers of
the completion with the standard `p`-adic integers. -/
noncomputable def baseIso (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    (ℤ ⧸ pPowIdeal p n) ≃+*
      (QpInt p ⧸ Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))) := by
  have h1 : (ℤ ⧸ pPowIdeal p n) ≃+* ZMod (p ^ n) :=
    Int.quotientSpanNatEquivZMod (p ^ n)
  have h2 : ZMod (p ^ n) ≃+*
      (PadicInt p ⧸ Ideal.span ({((p : PadicInt p) ^ n)} : Set (PadicInt p))) :=
    (RingHom.quotientKerEquivOfSurjective
        (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n))).symm.trans
      (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow (p := p) n))
  have hIJ : Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p)) =
      (Ideal.span ({((p : PadicInt p) ^ n)} : Set (PadicInt p))).map
        (((qpPadicIntEquiv p).symm : PadicInt p ≃+* QpInt p) : PadicInt p →+* QpInt p) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    simp
  have h3 : (PadicInt p ⧸ Ideal.span ({((p : PadicInt p) ^ n)} : Set (PadicInt p))) ≃+*
      (QpInt p ⧸ Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))) :=
    Ideal.quotientEquiv _ _ ((qpPadicIntEquiv p).symm) hIJ
  exact h1.trans (h2.trans h3)

/-- **At most one ring hom out of `ℤ ⧸ I`**: two ring homs `ℤ ⧸ I →+* S` have
the same composite with the (surjective) quotient map `ℤ → ℤ ⧸ I`, and any two
ring homs `ℤ →+* S` agree (`RingHom.ext_int`). -/
lemma subsingleton_quotientIntRingHom (I : Ideal ℤ) (S : Type*) [Ring S] :
    Subsingleton (ℤ ⧸ I →+* S) := by
  refine ⟨fun f g => ?_⟩
  have h : f.comp (Ideal.Quotient.mk I) = g.comp (Ideal.Quotient.mk I) := RingHom.ext_int _ _
  exact RingHom.ext fun x => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrFun (congrArg (fun (φ : ℤ →+* S) => (φ : ℤ → S)) h) z

/-- The global↔local quotient identification `𝓞 K ⧸ P^(e·n) ≃+* kpInt ⧸ (p^n)`,
in the `Ideal.map`-spelling of the local algebra structure (so that the
`QpInt ⧸ (p^n)`-algebra structure on the target is the canonical quotient
algebra structure). -/
noncomputable def globalLocalIsoMapped (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (n : ℕ) :
    ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)) ≃+*
      (kpInt p P ⧸ (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))).map
        (algebraMap (QpInt p) (kpInt p P))) :=
  (globalLocal_quotientIso p P n).trans (Ideal.quotEquivOfEq (by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]))

/-- **Global witness with nonzero quotient trace** (the transport of the local
`teich_quotTrace_ne_zero` to the global quotient over `ℤ/(p^n)`, at the
critical level `n = v_p(e) + 1`). -/
theorem exists_trace_ne_zero_global (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hn : n = padicValNat p (P.ramificationIdx ℤ) + 1) :
    ∃ z : 𝓞 K, Algebra.trace (ℤ ⧸ pPowIdeal p n) ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
      (Ideal.Quotient.mk _ z) ≠ 0 := by
  obtain ⟨α, hα, hgen, htr⟩ := kap_gen_trace_ne_zero (p := p) (P := P)
  have hloc := teich_quotTrace_ne_zero (p := p) (P := P) n hn hα hgen htr
  let e₂ := globalLocalIsoMapped p P n
  have he : RingHom.comp
        (algebraMap (QpInt p ⧸ Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p)))
          (kpInt p P ⧸ (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))).map
            (algebraMap (QpInt p) (kpInt p P))))
        ((baseIso p n) : (ℤ ⧸ pPowIdeal p n) →+*
          (QpInt p ⧸ Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))))
      = RingHom.comp (e₂ : ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n)) →+*
          (kpInt p P ⧸ (Ideal.span ({((p ^ n : ℕ) : QpInt p)} : Set (QpInt p))).map
            (algebraMap (QpInt p) (kpInt p P))))
        (algebraMap (ℤ ⧸ pPowIdeal p n) ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))) :=
    (subsingleton_quotientIntRingHom (pPowIdeal p n) _).allEq _ _
  have htr_eq := Algebra.trace_eq_of_equiv_equiv (baseIso p n) e₂ he
    (e₂.symm (Ideal.Quotient.mk _ (teich p P α)))
  have hne : Algebra.trace (ℤ ⧸ pPowIdeal p n) ((𝓞 K) ⧸ P ^ (P.ramificationIdx ℤ * n))
      (e₂.symm (Ideal.Quotient.mk _ (teich p P α))) ≠ 0 := by
    rw [htr_eq, RingEquiv.apply_symm_apply]
    intro h0
    exact hloc ((baseIso p n).symm.injective (by rw [h0, map_zero]))
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e₂.symm (Ideal.Quotient.mk _ (teich p P α)))
  exact ⟨z, by rw [hz]; exact hne⟩

/-- **THE S1 GATE**: the per-prime wild different bound
`m_P ≤ e_P − 1 + e_P·v_p(e_P)`, for EVERY maximal prime `P` of `𝓞 K` over `p`
(no tameness or residue-degree hypothesis — the trace witness above covers the
wild cases uniformly). -/
theorem wild_different_count_le (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤
      P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  haveI : P.LiesOver (Commons.NumberTheory.NumberField.TameDifferent.p₀ p) :=
    (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
  obtain ⟨Q, hsup, hspl⟩ :=
    Commons.NumberTheory.NumberField.TameDifferent.p₀_map_eq_pow_mul (K := K) p P
  set n := padicValNat p (P.ramificationIdx ℤ) + 1 with hn_def
  have hnpos : 0 < n := by omega
  have htrace := exists_trace_ne_zero_global p P n hn_def
  obtain ⟨y, hyQ, hytr⟩ :=
    exists_wild_witness_of_nonzero_trace p P Q hsup hspl n hnpos htrace
  exact wild_count_le_of_wild_witness p P Q hsup hspl y hyQ hytr

/-- **Unconditional small-prime cap**: for every prime `p` and every number
field `K`, `v_p(|disc K|) ≤ [K:ℚ]·(1 + ⌊log_p [K:ℚ]⌋)` — the S1 output
(`WildBound.discrVal_le_wild` with the per-prime bound now unconditional). -/
theorem discrVal_le_wild_unconditional (p : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p (NumberField.discr K).natAbs ≤
      Module.finrank ℚ K + Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) :=
  Submission.Vdw.discrVal_le_wild (K := K) p (fun P hmax hlies => by
    haveI := hmax
    haveI := hlies
    exact wild_different_count_le (K := K) p P)

end

end Submission.Vdw.LocalField
