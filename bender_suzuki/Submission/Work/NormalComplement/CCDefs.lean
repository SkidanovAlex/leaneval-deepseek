/-
# NormalComplement: the hypothesis of the Corollary of Peterfalvi I Ch. III §1 Lemma 2

This module contains the definition `Work.NormalComplement.ControlHyp` — the hypothesis of the
Corollary of Lemma 2 (p.174) — together with a few elementary lemmas about `piPrimeCoreSub` used
by the proof of `Work.NormalComplement.controlCorollary`.

The Corollary reads: let `E ≤ W` be finite, `π` the set of prime divisors of `|E|`, and assume `E`
solvable and that for every `p ∈ π` and every `p`-subgroup `U ≠ 1` of `E`

`N_W(U) = O_{π'}(C_W(U)) · N_E(U)`  (this is `ControlHyp E W`).

Then `E` is a Hall subgroup of `W` and has a normal complement in `W`.
-/
import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.pcontrol_criterion
import Submission.Work.NormalComplement.pcontrol_transfer
import Submission.Work.NormalComplement.primes_of_abelianization
import Submission.Work.NormalComplement.isSylowIn_of_sylowIn_normalizer
import Submission.Work.NormalComplement.commutator_subgroupOf_eq_commutator
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Grun.Main
import Submission.Work.LocalPrelim.regular_sylow_fusion

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type*} [Group G]

/-- The hypothesis of the Corollary of Peterfalvi I Ch. III §1 Lemma 2 (p.174): for every prime
`p ∈ π` (`π` the set of prime divisors of `|E|`) and every `p`-subgroup `U ≠ 1` of `E`,
`N_W(U) = O_{π'}(C_W(U)) · N_E(U)`. -/
def ControlHyp (E W : Subgroup G) : Prop :=
  ∀ (p : ℕ) (U : Subgroup G), p.Prime → p ∣ Nat.card E → U ≤ E → U ≠ ⊥ → IsPGroup p U →
    W ⊓ Subgroup.normalizer (U : Set G) =
      piPrimeCoreSub {q | q ∣ Nat.card E} (W ⊓ Subgroup.centralizer (U : Set G)) ⊔
        (E ⊓ Subgroup.normalizer (U : Set G))

/-- `piPrimeCoreSub π X ≤ X`. -/
lemma piPrimeCoreSub_le (π : Set ℕ) (X : Subgroup G) : piPrimeCoreSub π X ≤ X :=
  Subgroup.map_subtype_le _

/-- `O_{π'}(X)` is normal in `X`: it is the image of the (normal, indeed characteristic)
subgroup `O_{π'}(↥X)` of `↥X`. -/
lemma piPrimeCoreSub_le_normalizer (π : Set ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (piPrimeCoreSub π X : Set G) := by
  haveI hnrm : (Work.Fitting.piCore (fun q => q ∉ π) ↥X).Normal :=
    Work.Fitting.normal_sSup (fun N hN => hN.1)
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, hnrm.conj_mem k hk ⟨x, hx⟩, ?_⟩
  simp [MulAut.conj_apply]

/-- If `p ∈ π` then `O_{π'}(X) ≤ O_{p'}(X)`: a normal `π'`-subgroup is in particular a normal
`p'`-subgroup. -/
lemma piPrimeCoreSub_le_pPrimeCoreSub {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hπ : p ∈ π)
    (X : Subgroup G) : piPrimeCoreSub π X ≤ pPrimeCoreSub p X := by
  show (Work.Fitting.piCore (fun q => q ∉ π) ↥X).map X.subtype ≤
    (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  exact Subgroup.map_mono (Work.Fitting.piCore_mono (fun q hq hqp => hq (hqp ▸ hπ)))

/-- The order of `O_{π'}(X)` has no prime divisor in `π`. -/
lemma not_dvd_card_piPrimeCoreSub {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hπ : p ∈ π)
    (X : Subgroup G) [Finite G] : ¬ p ∣ Nat.card ↥(piPrimeCoreSub π X) := by
  have hcard : Nat.card ↥(piPrimeCoreSub π X) =
      Nat.card ↥(Work.Fitting.piCore (fun q => q ∉ π) ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hpi := Work.Fitting.piCore_isPiNat ↥X (fun q => q ∉ π)
  rw [hcard]
  exact fun hd => hpi p hp hd hπ

end Work.NormalComplement
