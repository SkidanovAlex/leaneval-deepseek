/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The "no exponent sum zero" case of the Magnus--Moldavanskii hierarchy

`Work.OROneRel.hasMMHierarchy_of_subst`: if `r` is cyclically reduced, `x ≠ t` are two letters of `r`
and `eps x r ≠ 0`, then `⟨α | r⟩` admits a Magnus--Moldavanskii hierarchy (in the embedding form
`HasMMHierarchy.embed`) *provided* the hierarchy is known for every strictly shorter relator.

This is Magnus's *embedding* trick.  Put `p := eps x r`, `q := eps t r` and let
`ψ := subst t x p q` (`t ↦ t ^ p`, `x ↦ x * t ^ (-q)`, all other generators fixed); write
`W := ψ r` and `s := cyclicReduction W`.  Then

* `eps t W = p * eps t r - q * eps x r = 0`, and `eps t` is invariant under cyclic reduction;
* `nonTLetters t s ≤ nonTLetters t W = nonTLetters t (Psi r t x r) ≤ nonTLetters t r < relatorNorm r`,
  so every relator of the next level found below is shorter than `r`;
* `subst t x p q` induces an *injective* map `⟨α | r⟩ →* ⟨α | W⟩` (this is
  `substHom_injective_of_ne_zero`, from the Tietze identification
  `⟨α | W⟩ ≅ ⟨α | r⟩ ∗_{t^n = s^{pn}} ⟨s⟩` of `subst_pushout_equiv` and the Freiheitssatz), which
  composes with the isomorphism `⟨α | W⟩ ≅ ⟨α | s⟩` of conjugate relators to an *embedding*
  `ι : ⟨α | r⟩ ↪ ⟨α | s⟩`.

The hierarchy of `r` is then obtained by `HasMMHierarchy.embed` along `ι`, once `s` has a hierarchy:

* if `t` occurs in `s`, the exponent-sum-zero Magnus step at `s` (`hasMMVertexData_of_expsum_zero`)
  exhibits `⟨α | s⟩` as an HNN extension of `⟨β | mmW t s⟩` with `relatorNorm (mmW t s) ≤
  nonTLetters t s < relatorNorm r`, so `s` inherits a hierarchy from the induction hypothesis through
  the `step` constructor;
* if `t` does not occur in `s`, then `relatorNorm s = nonTLetters t s < relatorNorm r` and the
  induction hypothesis applies to `s` directly.
-/

import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.NoZeroDefs
import Submission.Work.OROneRel.psiSubstDefs
import Submission.Work.OROneRel.nonTLetters_Psi_le
import Submission.Work.OROneRel.nonTLetters_lt_norm
import Submission.Work.OROneRel.nonTLetters_cyclicReduction_le
import Submission.Work.OROneRel.relatorNorm_mmW_le_nt
import Submission.Work.OROneRel.sigma_cyclicReduction
import Submission.Work.OROneRel.mmVertexDataDefs
import Submission.Work.OROneRel.MMAssembly
import Submission.Work.OROneRel.hasMMVertexData_of_expsum_zero
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.subst_pushout_equiv
import Submission.Work.OROneRel.relatorLetters_eq_empty_iff
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate
import Submission.Work.OROneRel.eps_eq_toAdd_sigma
import Submission.Work.OROneRel.amPhi_true_injective
import Submission.Work.OROneRel.amPhi_false_injective

set_option linter.style.haveILetI false

namespace Work.OROneRel

universe u

/-! ## Auxiliary word-combinatorics lemmas about the substitution -/

/-- The substitution `subst t x (eps x r) (eps t r)` of `HNNStep` coincides with the
Magnus/Putman substitution `Psi r t x`: both send `t ↦ t ^ (eps x r) = t ^ (σ_x r)`, `x ↦ x t ^ (-q)`
with `q = eps t r = σ_t r`, and fix every other generator. -/
theorem subst_eq_Psi {α : Type u} (r : FreeGroup α) (t x : α) :
    subst t x (eps x r) (eps t r) = Psi r t x := by
  classical
  have hfun : substFun t x (eps x r) (eps t r) = PsiFun r t x := by
    funext a
    simp only [substFun, PsiFun, eps_eq_toAdd_sigma]
  rw [show subst t x (eps x r) (eps t r) = FreeGroup.lift (substFun t x (eps x r) (eps t r))
      from rfl,
    show Psi r t x = FreeGroup.lift (PsiFun r t x) from rfl, hfun]

/-- The substitution `subst t x (eps x r) (eps t r)` does not increase the number of letters
different from `t`. -/
theorem nonTLetters_subst_le {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t) :
    nonTLetters t (subst t x (eps x r) (eps t r) r) ≤ nonTLetters t r := by
  classical
  have h1 : subst t x (eps x r) (eps t r) r = Psi r t x r :=
    congrArg (fun f : FreeGroup α →* FreeGroup α => f r) (subst_eq_Psi r t x)
  rw [h1]
  exact nonTLetters_Psi_le r t x hxt

/-- The substituted relator has vanishing exponent sum in `t`. -/
theorem eps_subst_self {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t) :
    eps t (subst t x (eps x r) (eps t r) r) = 0 := by
  rw [eps_subst_t hxt]
  ring

/-- If `t` does not occur in `r`, then every letter of `r` is different from `t`, so the norm of `r`
is the number of non-`t` letters. -/
theorem relatorNorm_le_nonTLetters_of_notMem {α : Type u} (s : FreeGroup α) (t : α)
    (h : t ∉ relatorLetters s) : relatorNorm s ≤ nonTLetters t s := by
  classical
  by_contra hcon
  have hlt : (FreeGroup.toWord s).countP (fun p : α × Bool => decide (p.1 ≠ t)) <
      (FreeGroup.toWord s).length := by
    simpa only [nonTLetters, relatorNorm, FreeGroup.norm, not_le] using hcon
  obtain ⟨a, ha, hp⟩ := List.countP_lt_length_iff.mp hlt
  have hat : a.1 = t := not_not.mp (of_decide_eq_false hp)
  refine h ⟨a.2, ?_⟩
  rw [show (t, a.2) = a from Prod.ext hat.symm rfl]
  exact ha

/-- **Injectivity of the substitution on the one-relator groups.**  The Magnus/Putman substitution
`ψ = subst t x p q` with `p ≠ 0` induces an injective map `⟨α | r⟩ →* ⟨α | ψ r⟩` as soon as `r` is
cyclically reduced and involves a letter `x ≠ t`.

The map factors through the amalgam `⟨α | r⟩ ∗_{t^n = s^{pn}} ⟨s⟩ ≅ ⟨α | ψ r⟩`
(`subst_pushout_equiv`), in which `⟨α | r⟩` is the first factor: the inclusion of the first factor is
injective by `Monoid.PushoutI.of_injective`, whose two hypotheses are the injectivity of the two
amalgamation maps `n ↦ (mk t)^n` (the Freiheitssatz, `amPhi_true_injective`) and `n ↦ s ^ (p n)`
(`p ≠ 0`, `amPhi_false_injective`). -/
theorem substHom_injective_of_ne_zero {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t)
    (hcyc : IsCyclicallyReducedRelator r) (hx : x ∈ relatorLetters r) {p q : ℤ} (hp : p ≠ 0) :
    Function.Injective (substHom r t x p q) := by
  obtain ⟨E, hE⟩ := subst_pushout_equiv r hxt p q
  have hφ : ∀ i : Bool, Function.Injective (amPhi r t p i) := by
    intro i
    cases i
    · exact amPhi_false_injective r t hp
    · exact amPhi_true_injective r hxt hcyc hx p
  intro g₁ g₂ h
  refine Monoid.PushoutI.of_injective hφ true ?_
  rw [← hE g₁, ← hE g₂, h]

/-! ## The main statement -/

theorem hasMMHierarchy_of_subst {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (hpx : Work.OROneRel.eps x r ≠ 0)
    (IH : ∀ {β : Type u} (s : FreeGroup β), Work.OROneRel.relatorNorm s <
        Work.OROneRel.relatorNorm r →
      (Work.OROneRel.IsTerminalRelator s ∨
        (Work.OROneRel.IsCyclicallyReducedRelator s ∧ s ≠ 1)) → HasMMHierarchy β s) :
    HasMMHierarchy α r := by
  classical
  -- the substituted relator `W = ψ r` and its cyclic reduction `s`
  set W : FreeGroup α := subst t x (eps x r) (eps t r) r with hW
  set s : FreeGroup α := cyclicReduction W with hs
  have hs_cyc : IsCyclicallyReducedRelator s := isCyclicallyReducedRelator_cyclicReduction W
  -- the letter count bookkeeping
  have hntW : nonTLetters t W ≤ nonTLetters t r := by
    rw [hW]
    exact nonTLetters_subst_le r hxt
  have hnts : nonTLetters t s ≤ nonTLetters t W := by
    rw [hs]
    exact nonTLetters_cyclicReduction_le W t
  have hntr : nonTLetters t r < relatorNorm r := nonTLetters_lt_norm r t ht
  -- the embedding `⟨α | r⟩ ↪ ⟨α | s⟩`
  have hsubst_inj : Function.Injective (substHom r t x (eps x r) (eps t r)) :=
    substHom_injective_of_ne_zero r hxt hcyc hx hpx
  have hiso : Nonempty (PresentedGroup ({W} : Set (FreeGroup α)) ≃*
      PresentedGroup ({cyclicReduction W} : Set (FreeGroup α))) :=
    presentedGroup_conj_iso (isConj_comm.mp (isConj_iff.mpr
      ⟨cyclicConjugator W, cyclicConjugator_mul_cyclicReduction_mul_inv W⟩))
  obtain ⟨eiso⟩ := hiso
  set ι : PresentedGroup ({r} : Set (FreeGroup α)) →* PresentedGroup ({s} : Set (FreeGroup α)) :=
    eiso.toMonoidHom.comp (substHom r t x (eps x r) (eps t r)) with hι
  have hι_inj : Function.Injective ι := eiso.injective.comp hsubst_inj
  by_cases hts : t ∈ relatorLetters s
  · -- **Case A**: `t` occurs in `s`; the exponent-sum-zero step at `s` has a short vertex
    have hs1 : s ≠ 1 := by
      intro h1
      have h0 : relatorLetters s = ∅ := (relatorLetters_eq_empty_iff s).mpr h1
      rw [h0] at hts
      exact hts
    have heps_s : eps t s = 0 := by
      rw [eps_eq_toAdd_sigma, hs, sigma_cyclicReduction W t, hW,
        ← eps_eq_toAdd_sigma t (subst t x (eps x r) (eps t r) r)]
      exact eps_subst_self r hxt
    obtain ⟨hgood, A, B, hA, hB, φ, ⟨eHNN⟩⟩ :=
      hasMMVertexData_of_expsum_zero (r := s) (t := t) hs_cyc hs1 hts heps_s
    -- the vertex relator is shorter than `s`, so the step constructor applies at `s`
    have hlt_s : relatorNorm (mmW t s) < relatorNorm s := mmW_relatorNorm_lt hts
    -- ... and it is also shorter than the original `r`, so the induction hypothesis applies
    have hlt_r : relatorNorm (mmW t s) < relatorNorm r := by
      letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
      have h1 : relatorNorm (mmW t s) ≤ nt t s.toWord := relatorNorm_mmW_le_nt t s
      have h2 : nt t s.toWord = nonTLetters t s := (nonTLetters_eq_nt t s).symm
      omega
    exact HasMMHierarchy.embed r s
      (HasMMHierarchy.step s (mmW t s) hlt_s (IH (mmW t s) hlt_r hgood) A B hA hB φ eHNN)
      ι hι_inj
  · -- **Case B**: `t` does not occur in `s`, which is therefore shorter than `r`
    have hle : relatorNorm s ≤ nonTLetters t s := relatorNorm_le_nonTLetters_of_notMem s t hts
    have hlt : relatorNorm s < relatorNorm r :=
      lt_of_le_of_lt (le_trans hle (le_trans hnts hntW)) hntr
    have hgood : IsTerminalRelator s ∨ (IsCyclicallyReducedRelator s ∧ s ≠ 1) := by
      by_cases h1 : s = 1
      · exact Or.inl (by rw [h1]; exact Or.inl rfl)
      · exact Or.inr ⟨hs_cyc, h1⟩
    exact HasMMHierarchy.embed r s (IH s hlt hgood) ι hι_inj

end Work.OROneRel
