import Mathlib
import Submission.Vdw.LocalField.KapTrace
import Submission.Vdw.LocalField.TowerDegree
import Submission.Commons.FieldTheory.Finite.exists_generator_trace_ne_zero

/-!
# WildGenerator — the `p | f` wild witness generator (S1 gate, case `p | f ∧ p | e`)

The remaining open input of the S1 gate (`hwild`, the per-prime wild different
bound `m_P ≤ e_P − 1 + e_P·v_p(e_P)`) is the case `p | f ∧ p | e`, where
`f = P.inertiaDeg ℤ`, `e = P.ramificationIdx ℤ`.  `SinglePrimeWitness`
disposes of the case `p ∤ f` with the element `z = 1`; there the trace over
`𝓞K ⧸ P^(e(k+1))` is `e·f` with `v_p(e·f) = v_p(e) = k`.

For `p | f` the element `1` has trace `e·f` with `v_p(e·f) ≥ k+1`, so a
genuinely new element is needed.  The construction is:

* `ζ = teich p P α` for a **generator** `α` of the residue field units
  `κ^×` whose residue trace `Tr_{κ/𝔽_p}(α)` is nonzero;
* `Tr_{W/ℚ_p}(ζ) = -(g.nextCoeff)` (`TraceResidue.tr_zeta_int`), an integral
  element whose mod-`p` reduction is `Tr_{κ/𝔽_p}(α)`
  (`KapTrace.kap_trace_eq_reduction`) — hence a **unit** of `ℤ_[p]`;
* `Tr_{K_P/ℚ_p}(ζ) = e • Tr_{W/ℚ_p}(ζ)` (`TowerDegree.localTraceIdentity`),
  of exact `p`-adic order `v_p(e) = k`.

The present module supplies the ingredients of that construction that are
independent of the (long) global-trace bookkeeping:

* `Commons.FieldTheory.Finite.exists_generator_trace_ne_zero` (fleet commons)
  — a finite field has a multiplicative generator with nonzero trace
  (the counting fact `φ(p^f−1) > p^{f−1} − 1 + #(proper subfields)`-flavoured;
  verified by direct computation for many `f`);
* `kap_gen_trace_ne_zero` — the same statement instantiated at the residue
  field `κ = kap p P` of the completion, in the exact `hgen` form used by the
  Teichmüller machinery;
* `ker_qpReductionHom` — the kernel of the reduction `QpInt p →+* ZMod p` is
  the maximal ideal (`= (p)`), so a nonzero reduction detects a unit;
* `qpInt_natCast_unit_of_not_dvd` — a natural number prime to `p` is a unit of
  `QpInt`;
* `teich_nextCoeff_isUnit` — for such an `α`, the integral trace
  representative `-(g.nextCoeff)` is a **unit** of `QpInt`;
* `teich_localTrace_eq` — the local trace of `ζ` is `e • (-(g.nextCoeff))`;
* `pow_mul_unit_not_mem_pow`, `natCast_mul_unit_not_mem_pow` — `p^v · (unit)`
  is not divisible by `p^(v+1)` (the exactness of the `p`-adic order);
* `teich_localTrace_not_dvd` — **the local trace of `ζ` has exact `p`-adic
  order `v_p(e)`**: `e·(-(g.nextCoeff)) ∉ (p^{v_p(e)+1})` in `QpInt`.

Together these pin down `Tr_{K_P/ℚ_p}(ζ)` as an element of exact `p`-adic
order `k = v_p(e)`, i.e. `≡ u·τ·p^k (mod p^{k+1})` with `u = e/p^k` and
`τ = Tr_{κ/𝔽_p}(α) ≠ 0` — the level-`k` trace congruence recorded as the
remaining input of the `p | f ∧ p | e` wild witness (Roadmap Session-131/132,
and the Session-133 block for this module).  The global step
(`𝓞K`-approximation of `ζ`, the CRT lift into `Q^(k+1)`, and the
local↔global integer trace congruence) is the next chapter; the reduction
machinery (`WildWitnessReduction.exists_wild_witness_of_nonzero_trace`) is
already in place and consumes exactly such a nonzero quotient trace.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

open scoped NumberField WithZero Valued
open Classical IsLocalRing
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Submission.Vdw.LocalField
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]


/-- kernel of the QpInt → ZMod p reduction. -/
theorem ker_qpReductionHom (p : ℕ) [Fact (Nat.Prime p)] (t : QpInt p) :
    qpReductionHom p t = 0 ↔ t ∈ IsLocalRing.maximalIdeal (QpInt p) := by
  have key : ∀ x : PadicInt p, PadicInt.toZMod x = 0 ↔
      x ∈ IsLocalRing.maximalIdeal (PadicInt p) := by
    intro x
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  have hunit : ∀ x : QpInt p, (x ∈ IsLocalRing.maximalIdeal (QpInt p)) ↔
      (qpPadicIntEquiv p x ∈ IsLocalRing.maximalIdeal (PadicInt p)) := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
    rw [mem_nonunits_iff, mem_nonunits_iff]
    constructor
    · intro h hu
      have hx : IsUnit x := by
        have h' := hu.map ((qpPadicIntEquiv p).symm).toRingHom
        simpa using h'
      exact h hx
    · intro h hu
      have hx : IsUnit (qpPadicIntEquiv p x) := hu.map (qpPadicIntEquiv p).toRingHom
      exact h hx
  rw [show qpReductionHom p t = PadicInt.toZMod (qpPadicIntEquiv p t) from rfl]
  rw [key (qpPadicIntEquiv p t), ← hunit t]

/-- `p ≠ 0` in QpInt (it is not a field). -/
theorem p_ne_zero_qpInt (p : ℕ) [Fact (Nat.Prime p)] : (p : QpInt p) ≠ 0 := by
  intro h
  have hm : IsLocalRing.maximalIdeal (QpInt p) = Ideal.span ({(p : QpInt p)} : Set (QpInt p)) :=
    qpIntMaximalIdeal_eq_span_p p
  have hbot : IsLocalRing.maximalIdeal (QpInt p) = ⊥ := by
    rw [hm, h, Ideal.span_singleton_eq_bot]
  exact IsDiscreteValuationRing.not_a_field (QpInt p) hbot

/-- a natural number not divisible by p is a unit of QpInt. -/
theorem qpInt_natCast_unit_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (u : ℕ) (hu : ¬ p ∣ u) :
    IsUnit ((u : QpInt p)) := by
  have hnotmem : ¬ ((u : QpInt p) ∈ IsLocalRing.maximalIdeal (QpInt p)) := by
    rw [← ker_qpReductionHom p]
    intro h0
    apply hu
    have hunf : qpReductionHom p ((u : QpInt p)) = ((u : ZMod p)) := by
      exact map_natCast (qpReductionHom p) u
    rw [hunf] at h0
    exact (ZMod.natCast_eq_zero_iff u p).mp h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hnotmem
  exact not_not.mp hnotmem

/-- The κ-generator whose residue trace is nonzero. -/
theorem kap_gen_trace_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ∃ α : kap p P, ∃ hα : α ≠ 0,
      orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1 ∧
      Algebra.trace (ZMod p) (kap p P) α ≠ 0 := by
  haveI : Fintype (kap p P) := Fintype.ofFinite _
  obtain ⟨x, hord, htr⟩ :=
    Commons.FieldTheory.Finite.exists_generator_trace_ne_zero (F := kap p P) p
  have hx0 : (x : kap p P) ≠ 0 := Units.ne_zero x
  refine ⟨(x : kap p P), hx0, ?_, htr⟩
  have hmk : Units.mk0 (x : kap p P) hx0 = x := Units.ext rfl
  rw [hmk, hord, Fintype.card_eq_nat_card, kap_card]

/-- The integral trace representative `-(g.nextCoeff)` of the Teichmüller
generator is a unit of QpInt when the residue trace is nonzero. -/
theorem teich_nextCoeff_isUnit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (htr : Algebra.trace (ZMod p) (kap p P) α ≠ 0) :
    IsUnit (-(teichMinpolyInt p P α).nextCoeff : QpInt p) := by
  have hred := kap_trace_eq_reduction p P hα hgen
  rw [hred] at htr
  have hnotmem : ¬ ((-(teichMinpolyInt p P α).nextCoeff : QpInt p) ∈
      IsLocalRing.maximalIdeal (QpInt p)) := by
    rw [← ker_qpReductionHom p (t := (-(teichMinpolyInt p P α).nextCoeff : QpInt p))]
    exact htr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hnotmem
  exact not_not.mp hnotmem

/-- the local trace of the Teichmüller generator. -/
theorem teich_localTrace_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (Algebra.trace (QpAdic p) (kpAdic p P))
        (algebraMap (Wk p P α) (kpAdic p P) (zetaW p P α))
      = P.ramificationIdx ℤ •
          ((-(teichMinpolyInt p P α).nextCoeff : QpInt p) : QpAdic p) := by
  rw [localTraceIdentity p P hα hgen (zetaW p P α), tr_zeta_int p P α hα]
  congr 1

/-- `p^v · s` with `s` a unit is not divisible by `p^(v+1)`. -/
theorem pow_mul_unit_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)] (v : ℕ) (s : QpInt p)
    (hs : IsUnit s) :
    ((p : QpInt p) ^ v * s) ∉
      Ideal.span ({((p ^ (v + 1) : ℕ) : QpInt p)} : Set (QpInt p)) := by
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hdiv : ((p ^ (v + 1) : ℕ) : QpInt p) = (p : QpInt p) ^ v * (p : QpInt p) := by
    rw [pow_succ]
    norm_num
  rw [hdiv] at hc
  have hpv : (p : QpInt p) ^ v ≠ 0 := pow_ne_zero _ (p_ne_zero_qpInt p)
  have hs_eq : s = (p : QpInt p) * c := by
    have h1 : (p : QpInt p) ^ v * s = (p : QpInt p) ^ v * ((p : QpInt p) * c) := by
      rw [hc, mul_assoc]
    exact mul_left_cancel₀ hpv h1
  have hmem_m : s ∈ IsLocalRing.maximalIdeal (QpInt p) := by
    rw [qpIntMaximalIdeal_eq_span_p p, Ideal.mem_span_singleton]
    exact ⟨c, hs_eq⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem_m
  exact hmem_m hs

/-- the exact `p`-adic order of `e·t` for a unit `t` and `e ≠ 0`. -/
theorem natCast_mul_unit_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)] (e : ℕ) (he : e ≠ 0)
    {t : QpInt p} (ht : IsUnit t) :
    ((e : QpInt p) * t) ∉
      Ideal.span ({((p ^ (padicValNat p e + 1) : ℕ) : QpInt p)} : Set (QpInt p)) := by
  set v := padicValNat p e with hv
  have hdv : p ^ v ∣ e := (padicValNat_dvd_iff_le he).mpr le_rfl
  set w := e / p ^ v with hwdef
  have hfac : p ^ v * w = e := Nat.mul_div_cancel' hdv
  have hw : ¬ p ∣ w := by
    intro hpd
    obtain ⟨w', hw'⟩ := hpd
    have : p ^ (v + 1) ∣ e := by
      rw [← hfac, hw', pow_succ]
      exact ⟨w', by ring⟩
    exact pow_succ_padicValNat_not_dvd he this
  have hcast : ((e : QpInt p) * t) = (p : QpInt p) ^ v * ((w : QpInt p) * t) := by
    rw [← hfac, Nat.cast_mul]
    push_cast
    ring
  rw [hcast]
  exact pow_mul_unit_not_mem_pow p v ((w : QpInt p) * t) ((qpInt_natCast_unit_of_not_dvd p w hw).mul ht)

/-- **the local trace of the Teichmüller generator at the exact `p`-adic level**:
for a generator `α` of the residue field units whose residue trace is nonzero,
the number `e·(-g.nextCoeff)` (the local trace of `ζ = teich α` over `ℚ_p`,
up to the coercions) is not divisible by `p^{v_p(e)+1}`. -/
theorem teich_localTrace_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (htr : Algebra.trace (ZMod p) (kap p P) α ≠ 0) :
    ((P.ramificationIdx ℤ : QpInt p) * (-(teichMinpolyInt p P α).nextCoeff : QpInt p)) ∉
      Ideal.span ({((p ^ (padicValNat p (P.ramificationIdx ℤ) + 1) : ℕ) : QpInt p)} :
        Set (QpInt p)) := by
  exact natCast_mul_unit_not_mem_pow p (P.ramificationIdx ℤ)
    (ne_of_gt (Ideal.ramificationIdx_pos P ℤ)) (teich_nextCoeff_isUnit p P hα hgen htr)

end
end Submission.Vdw.LocalField
