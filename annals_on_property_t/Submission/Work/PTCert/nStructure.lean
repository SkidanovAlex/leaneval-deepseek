import Mathlib
import Submission.Work.PTCert.Glue3

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects of the rank-5 certificate: EI, fE,
actE, actN, repE, nuE, Pmat, …, and the semantic Props ESem/TabSem/NSem/RowSem/GroupSem/OrbLabSem/
ClassSem/KleinSem = plain meanings of the kernel checks) and `Glue3.lean` (the Props of the
mathematical steps). READ BOTH FIRST, and `NOTES_LEAD_glue.md` (workspace root) for the whole chain.
Hypotheses of the form `CodeFacts`, `ConjActFacts`, `ActCSound`, `BitsBridge`, `OrbitDecomp`,
`KleinLevel`, `FourierTransport`, `LdlChainSound`, `WhtSound` are GlueDefs Props proved in parallel by
other agents; `ESem`… are data facts proved by kernel checks. Use them as given; do not re-prove them.
Already-proved theorems you may use directly: `Work.PTCert.avgMatInvariant`, `rowFormula`,
`twistedFourierCriterion`, `psdOfBlock`, `psdSignedPerm`, `labelPrinciple`, `avgPrinciple`, `gramSOS`,
`avgGram`, `ldlScaledPrinciple`, `letterAction`, `modelSound`, `sigmaGroupFacts` (+ namespace
SigmaFacts: signAut_mul, signAut_inv, sigAut_mul, sigAut_inv, mem_SigmaSet_iff, ...), `permCheckKSound`.
NEVER unfold the big data definitions (`eAll`, `eM`, …) or try `decide` on them: all data facts come
through the Sem hypotheses. Do not change Glue*.lean. If the statement is false, `declare_false`
with the concrete reason (and say which hypothesis is missing).
Unfold repE/nuE/toEI/repEI. For x : EI (x.1 ∈ eAll): NSem gives 1 ≤ em x, t := (em x - 1)/32 < 611 and
actC cmT (ntab sc) (rp t) = x.1 with sc = (em x - 1) % 32; NSem.2 gives rp t ∈ eAll and em (rp t) = 32 t + 1.
Then: actN (nuE x) (repE x) = x via ActSetup's last clause (actN (zOfSc sc) acts by actC (ntab sc)) and
Subtype.ext. repE (repE x) = repE x: em (rp t) = 32 t + 1 ⇒ (em (rp t) - 1)/32 = t. repE (actN a x) = repE x:
write a = zOfSc sc' (BitsBridge surjectivity), actN a x = actN (a + nuE x) (repE x) (ActSetup composition),
= ⟨actC cmT (ntab sc'') (rp t), _⟩ for the code sc'' of a + nuE x, and NSem.3.
-/

set_option linter.unusedVariables false

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-! ### Small consequences of `NSem` used to build `NStructure` -/

private lemma eS_mem_eAll {z : ℕ} (hz : z ∈ eS) : z ∈ eAll := by
  rw [eS, List.mem_toFinset] at hz; exact hz

private lemma eAll_mem_eS {z : ℕ} (hz : z ∈ eAll) : z ∈ eS := by
  rw [eS, List.mem_toFinset]; exact hz

private lemma div_lt_611 (hN : NSem) {z : ℕ} (hz : z ∈ eS) : (em z - 1) / 32 < 611 :=
  (hN.1 z (eS_mem_eAll hz)).2.1

private lemma nu_act (hN : NSem) {z : ℕ} (hz : z ∈ eS) :
    actC cmT (ntab ((em z - 1) % 32)) (rp ((em z - 1) / 32)) = z :=
  (hN.1 z (eS_mem_eAll hz)).2.2

private lemma rp_mem (hN : NSem) {t : ℕ} (ht : t < 611) : rp t ∈ eS :=
  eAll_mem_eS (hN.2.1 t ht).1

private lemma em_rp (hN : NSem) {t : ℕ} (ht : t < 611) : em (rp t) = 32 * t + 1 :=
  (hN.2.1 t ht).2

private lemma div_act (hN : NSem) {t : ℕ} (ht : t < 611) {sc : ℕ} (hsc : sc < 32) :
    (em (actC cmT (ntab sc) (rp t)) - 1) / 32 = t :=
  hN.2.2 t ht sc hsc

private lemma toEI_val {z : ℕ} (hz : z ∈ eS) (x : EI) : (toEI z x).1 = z := by
  unfold toEI
  rw [dif_pos hz]

private lemma repE_val (hN : NSem) (x : EI) : (repE x).1 = rp ((em x.1 - 1) / 32) := by
  unfold repE
  exact toEI_val (rp_mem hN (div_lt_611 hN x.2)) x

private lemma repEI_val (hN : NSem) (t : ℕ) (ht : t < 611) (x : EI) : (repEI t x).1 = rp t := by
  unfold repEI
  exact toEI_val (rp_mem hN ht) x

private lemma div32 (t : ℕ) : (32 * t + 1 - 1) / 32 = t := by
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num : 0 < 32)]

theorem nStructure (hA : ActSetup) (hBB : BitsBridge) (hE : ESem) (hN : NSem) (hT : TabSem) :
    NStructure := by
  -- the composition law and the table clause of `ActSetup`
  have hmul : ∀ (a b : Fin 5 → ZMod 2) (x : EI), actN (a + b) x = actN a (actN b x) :=
    hA.2.2.2.2.2.2.2.2.1
  have hlast : ∀ sc < 32, ∀ x : EI, (actN (zOfSc sc) x).1 = actC cmT (ntab sc) x.1 :=
    hA.2.2.2.2.2.2.2.2.2.2.2
  -- (1) `nuE x` brings `repE x` back to `x`
  have h1 : ∀ x : EI, actN (nuE x) (repE x) = x := by
    intro x
    apply Subtype.ext
    have hsc : (em x.1 - 1) % 32 < 32 := Nat.mod_lt _ (by norm_num)
    have hrep : (repE x).1 = rp ((em x.1 - 1) / 32) := repE_val hN x
    change (actN (zOfSc ((em x.1 - 1) % 32)) (repE x)).1 = x.1
    rw [hlast _ hsc (repE x), hrep, nu_act hN x.2]
  -- (2) representatives are idempotent
  have h2 : ∀ x : EI, repE (repE x) = repE x := by
    intro x
    apply Subtype.ext
    have hlt : (em x.1 - 1) / 32 < 611 := div_lt_611 hN x.2
    have hrep : (repE x).1 = rp ((em x.1 - 1) / 32) := repE_val hN x
    have hem : em ((repE x).1) = 32 * ((em x.1 - 1) / 32) + 1 := by
      rw [hrep]; exact em_rp hN hlt
    have hdiv : (em (repE x).1 - 1) / 32 = (em x.1 - 1) / 32 := by
      rw [hem]; exact div32 _
    rw [repE_val hN (repE x), hdiv, hrep]
  -- (3) representatives are `actN`-invariant
  have h3 : ∀ (a : Fin 5 → ZMod 2) (x : EI), repE (actN a x) = repE x := by
    intro a x
    obtain ⟨sc', hsc'lt, hsc'eq⟩ := hBB.2.1 5 (a + nuE x)
    have hsc'32 : sc' < 32 := by omega
    have hlt : (em x.1 - 1) / 32 < 611 := div_lt_611 hN x.2
    have hrep : (repE x).1 = rp ((em x.1 - 1) / 32) := repE_val hN x
    have hac : actN (a + nuE x) (repE x) = actN a x := by
      rw [hmul a (nuE x) (repE x), h1 x]
    have hval : (actN a x).1 = actC cmT (ntab sc') (rp ((em x.1 - 1) / 32)) := by
      rw [← hac, ← hsc'eq]
      rw [hlast _ hsc'32 (repE x), hrep]
    have hem : (em (actN a x).1 - 1) / 32 = (em x.1 - 1) / 32 := by
      rw [hval]; exact div_act hN hlt hsc'32
    apply Subtype.ext
    rw [repE_val hN (actN a x), hem, hrep]
  -- (4) the representatives `rp t` are codes
  have h4 : ∀ t < 611, rp t ∈ eS := fun t ht => rp_mem hN ht
  -- (5) the row index of `x` and its representative
  have h5 : ∀ x : EI, (em x.1 - 1) / 32 < 611 ∧ (repE x).1 = rp ((em x.1 - 1) / 32) :=
    fun x => ⟨div_lt_611 hN x.2, repE_val hN x⟩
  -- (6) `repEI t` is a fixed point, with code `rp t`
  have h6 : ∀ t < 611, ∀ x : EI, repE (repEI t x) = repEI t x ∧ (repEI t x).1 = rp t := by
    intro t ht x
    have hval : (repEI t x).1 = rp t := repEI_val hN t ht x
    have hem : em ((repEI t x).1) = 32 * t + 1 := by rw [hval]; exact em_rp hN ht
    have hdiv : (em (repEI t x).1 - 1) / 32 = t := by rw [hem]; exact div32 t
    refine ⟨?_, hval⟩
    apply Subtype.ext
    rw [repE_val hN (repEI t x), hdiv, hval]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.PTCert
