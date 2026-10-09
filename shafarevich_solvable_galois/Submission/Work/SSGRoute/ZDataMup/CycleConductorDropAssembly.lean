import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conductor drop at a cycle, from the two halves of Lang's Theorem 2

This module isolates the **assembly** of the conductor-drop statement at an *ideal modulus* (a
cycle `Work.SSGRoute.ZDataMup.Cycle`, `CycleDefs.lean`) from the two inputs that the classical
proof of Lang, *Algebraic Number Theory*, Chapter X §2 (Childress, *Class Field Theory*, Chapter 5
§2) supplies:

* `hA` (Childress's Proposition 2.2, the crux, proved via Artin's lemma): every fractional ideal
  coprime to the cycle `c` whose Artin symbol is trivial lies in `P(c)·𝔑(c)`;
* `hB` (the idèle–ideal dictionary plus the universal norm index inequality): the index of
  `P(c)·𝔑(c)` in `I(c)` is at least `[L:K]`.

For the two statements see `NOTE_conductorDrop_obstruction.md`; the point of the *cycle* (rather
than natural-number) formulation is that the support of a cycle need not be saturated above the
rational primes, so that the cycle may be supported *exactly* on the ramified primes — which is
what the conductor drop needs and what no natural-number modulus can express
(`Work.SSGRoute.ZDataMup.Cycle.localGlobalMap_productFormula_of_cycleDrop`).

The assembly is a verbatim translation of
`NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_span_eq_one_of_kernelLe_of_relIndex`: for that `c`
one has `ker(ψ) ⊓ I(c) ⊆ P(c)·𝔑(c)` by `hA`, while `[I(c) : ker(ψ) ⊓ I(c)] = |Gal(L/K)| = [L:K]`
(by `hsurj`) and `[I(c) : P(c)·𝔑(c)] ≥ [L:K]` (by `hB`); hence the two subgroups are equal and
every element of the principal ray is killed by `ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal

namespace Cycle

variable {K : Type} [Field K] [NumberField K]

/-- **The fractional ideals coprime to a cycle, as a subgroup of `Frac K`.**  This is the
`FracCoprime`-presentation of `Cycle.idealCoprimeGroup c` (`CycleDefs.lean`); it is the group `I(c)`
in which the index inequality of the conductor drop is phrased. -/
def coprimeGroup (c : Cycle K) : Subgroup (Frac K) where
  carrier := {A | c.FracCoprime A}
  one_mem' := by
    intro 𝔭 _
    rw [Units.val_one, FractionalIdeal.count_one K 𝔭]
  mul_mem' := by
    intro A B hA hB 𝔭 h𝔭
    rw [Units.val_mul, FractionalIdeal.count_mul K 𝔭 A.ne_zero B.ne_zero, hA 𝔭 h𝔭, hB 𝔭 h𝔭,
      add_zero]
  inv_mem' := by
    intro A hA 𝔭 h𝔭
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K 𝔭, hA 𝔭 h𝔭, neg_zero]

@[simp] theorem mem_coprimeGroup {c : Cycle K} {A : Frac K} :
    A ∈ c.coprimeGroup ↔ c.FracCoprime A := Iff.rfl

end Cycle

namespace Cycle

variable {K : Type} [Field K] [NumberField K]
variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- **The conductor drop at a cycle, from the two halves of Lang's Theorem 2.**  Let `L/K` be a
finite Galois extension of number fields with commutative Galois group, `c` a cycle of `K` and `cL`
a cycle of `L`; suppose that

* the principal ray and the norm group lie in `I(c)` (`hPNI`, the companion of the index
  inequality);
* the Artin symbol is surjective on the fractional ideals coprime to `c` (`hsurj`);
* `ker ψ ⊓ I(c) ⊆ P(c)·𝔑(c)` (`hA`, the crux — Artin's lemma / Childress's Proposition 2.2);
* `[L:K] ≤ [I(c) : P(c)·𝔑(c)]` (`hB`, the idèle–ideal dictionary and the norm index inequality).

Then the Artin symbol kills the principal ideal of every `b` with `c.CongrOne b`.  In particular,
if `c` is supported exactly on the primes ramified in `L/K` and `cL` is the base change of `c`, the
Artin symbol of every such `b` is trivial — the classical "the conductor is supported on the
ramified primes" (Neukirch, *ANT*, V.6.1; Lang, *ANT*, X §4). -/
theorem conductorDrop_of_kernelLe_of_index
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (c : Cycle K) (cL : Cycle L) (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hPNI : c.principalRay ⊔ c.normRay K L cL ≤ c.coprimeGroup)
    (hsurj : ∀ σ : L ≃ₐ[K] L, ∃ A : Frac K,
      c.FracCoprime A ∧ artinSymFracHom (K := K) (L := L) hcomm A = σ)
    (hA : ∀ A : Frac K, c.FracCoprime A →
      artinSymFracHom (K := K) (L := L) hcomm A = 1 →
      A ∈ c.principalRay ⊔ c.normRay K L cL)
    (hB : Module.finrank K L ≤
      (c.principalRay ⊔ c.normRay K L cL).relIndex c.coprimeGroup) :
    ∀ b : Kˣ, c.CongrOne b →
      artinSymFracHom (K := K) (L := L) hcomm (spanUnit b) = 1 := by
  classical
  let f : Frac K →* (L ≃ₐ[K] L) := artinSymFracHom hcomm
  let I : Subgroup (Frac K) := c.coprimeGroup
  let PN : Subgroup (Frac K) := c.principalRay ⊔ c.normRay K L cL
  let J : Subgroup (Frac K) := f.ker ⊓ I
  -- ## the kernel of the Artin symbol on `I(c)` is contained in `P(c)·𝔑(c)`
  have hJPN : J ≤ PN := by
    intro A hA'
    obtain ⟨hker, hI⟩ := Subgroup.mem_inf.mp hA'
    exact hA A (mem_coprimeGroup.mp hI) (MonoidHom.mem_ker.mp hker)
  -- ## the Artin symbol is surjective on `I(c)`
  have hmap : I.map f = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨A, hAcop, hAσ⟩ := hsurj σ
    exact Subgroup.mem_map.mpr ⟨A, hAcop, hAσ⟩
  have hcardI : f.ker.relIndex I = Nat.card (L ≃ₐ[K] L) := by
    rw [Subgroup.relIndex_ker I f, hmap]
    exact Nat.card_congr (Subgroup.topEquiv (G := L ≃ₐ[K] L)).toEquiv
  -- ## hence `[I(c) : ker ψ ⊓ I(c)] = [L : K]`
  have hJrelI : J.relIndex I = Module.finrank K L := by
    rw [show J.relIndex I = f.ker.relIndex I from Subgroup.inf_relIndex_right f.ker I, hcardI,
      IsGalois.card_aut_eq_finrank K L]
  have hJI_ne : J.relIndex I ≠ 0 := by
    rw [hJrelI]
    exact (Module.finrank_pos (R := K) (M := L)).ne'
  -- ## `[I(c) : P(c)·𝔑(c)] = [L : K]` as well, so the two subgroups coincide
  have hPNrelI : PN.relIndex I = Module.finrank K L := by
    refine le_antisymm ?_ hB
    rw [← hJrelI]
    exact Subgroup.relIndex_le_of_le_left hJPN hJI_ne
  have hJrelPN : J.relIndex PN = 1 := by
    have h' : J.relIndex PN * PN.relIndex I = 1 * PN.relIndex I := by
      rw [Subgroup.relIndex_mul_relIndex J PN I hJPN hPNI, hJrelI, hPNrelI, one_mul]
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero (by rw [hPNrelI, ← hJrelI]; exact hJI_ne)) h'
  have hPNJ : PN ≤ J := Subgroup.relIndex_eq_one.mp hJrelPN
  -- ## consequently the principal ray is killed
  intro b hb
  have hmemP : spanUnit b ∈ PN := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, hb, rfl⟩)
  have hker : spanUnit b ∈ f.ker := Subgroup.mem_inf.mp (hPNJ hmemP) |>.1
  exact MonoidHom.mem_ker.mp hker

end Cycle

end Work.SSGRoute.ZDataMup
