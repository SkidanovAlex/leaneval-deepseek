import Mathlib
import Submission.Work.SSGRoute.ZDataMup.CycleDefs
import Submission.Work.SSGRoute.ZDataMup.CycleIdele
import Submission.Work.SSGRoute.ZDataMup.CycleCongr
import Submission.Work.SSGRoute.ZDataMup.LT_CyclePort
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conductor drop at a cycle, from the index inequality

The statement proved here is the *index form* of the conductor drop at an ideal modulus (a
`Work.SSGRoute.ZDataMup.Cycle`): given that

* `P(c)·𝔑(c)` has index at least `[L:K]` in `I(c)` (`hIdx`), and
* every element of `I(c)` killed by the Artin symbol lies in `P(c)·𝔑(c)` (`hKr`),

the Artin symbol kills the principal ideal of every `b` with `b ≡ 1 mod c`.

The interest of this form is that neither the surjectivity of the Artin symbol on `I(c)` nor the
containment `P(c)·𝔑(c) ≤ I(c)` is assumed: from `hIdx` and `hKr` alone one gets
`ker ψ ⊓ I(c) = P(c)·𝔑(c)`, and since `P(c) ≤ P(c)·𝔑(c)`, every principal ideal in the ray lies
in the kernel.

## Implementation note

The commutativity hypothesis of the Artin symbol is read off from `[IsCyclic (L ≃ₐ[K] L)]`
through the *scoped* instance `IsMulCommutative.instCommMagma` (cyclic groups are commutative,
`IsCyclic.isMulCommutative`); hence `open scoped IsMulCommutative` below, which is what makes the
literally-written term `fun a b => mul_comm a b` elaborate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.CFTLib.ArtinReciprocityIdeal

theorem CycleConductorDropOfIndex
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (c : Work.SSGRoute.ZDataMup.Cycle K) (cL : Work.SSGRoute.ZDataMup.Cycle L)
    (hlev : ∀ 𝔭 ∈ c.supp, 1 ≤ c.lev 𝔭)
    (hIdx : Module.finrank K L ≤
      (c.principalRay ⊔ c.normRay K L cL).relIndex c.idealCoprimeGroup)
    (hKr : ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      c.FracCoprime A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => mul_comm a b) A = 1 →
      A ∈ c.principalRay ⊔ c.normRay K L cL) :
    ∀ b : Kˣ, c.CongrOne b →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => mul_comm a b)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          ((b : Kˣ) : K)) = 1 := by
  classical
  intro b hb
  -- the Artin symbol as a homomorphism `Frac K →* Gal(L/K)`
  let f : NK.CFTLib.ArtinReciprocityIdeal.Frac K →* (L ≃ₐ[K] L) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L)
      (fun a b : L ≃ₐ[K] L => mul_comm a b)
  let I : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) := c.idealCoprimeGroup
  let PN : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) :=
    c.principalRay ⊔ c.normRay K L cL
  let PNI : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) := PN ⊓ I
  let J : Subgroup (NK.CFTLib.ArtinReciprocityIdeal.Frac K) := f.ker ⊓ I
  -- ## the crux `hKr`, in group form: `ker ψ ⊓ I(c) ≤ P(c)·𝔑(c)`
  have hJPNI : J ≤ PNI := by
    intro A hA
    obtain ⟨hAker, hAI⟩ := Subgroup.mem_inf.mp hA
    refine Subgroup.mem_inf.mpr ⟨?_, hAI⟩
    have hcop : c.FracCoprime A := Cycle.idealCoprimeGroup_le_Icoprime c hAI
    have hsym : NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => mul_comm a b) A = 1 := by
      have h := MonoidHom.mem_ker.mp hAker
      rw [show f A = NK.CFTLib.Arl.artinSym (K := K) (L := L)
          (fun a b : L ≃ₐ[K] L => mul_comm a b) A from rfl] at h
      exact h
    exact hKr A hcop hsym
  -- ## `[I(c) : ker ψ ⊓ I(c)] ≤ [L:K]`, with no surjectivity hypothesis
  have hcardI : f.ker.relIndex I ≤ Module.finrank K L := by
    rw [Subgroup.relIndex_ker I f, ← IsGalois.card_aut_eq_finrank K L]
    exact Subgroup.card_le_card_group (Subgroup.map f I)
  have hJrelI : J.relIndex I ≤ Module.finrank K L := by
    rw [show J.relIndex I = f.ker.relIndex I from Subgroup.inf_relIndex_right f.ker I]
    exact hcardI
  have hJI_ne : J.relIndex I ≠ 0 := by
    rw [show J.relIndex I = f.ker.relIndex I from Subgroup.inf_relIndex_right f.ker I,
      Subgroup.relIndex_ker I f]
    exact Nat.card_ne_zero.mpr ⟨⟨⟨1, Subgroup.one_mem _⟩⟩, inferInstance⟩
  -- ## `[I(c) : P(c)·𝔑(c)] ≤ [L:K]` as well, hence the two subgroups coincide
  have hPNrelI : PN.relIndex I = Module.finrank K L := by
    refine le_antisymm ?_ hIdx
    rw [← Subgroup.inf_relIndex_right PN I]
    exact le_trans (Subgroup.relIndex_le_of_le_left hJPNI hJI_ne) hJrelI
  have hPNIrelI_eq : PNI.relIndex I = Module.finrank K L :=
    (Subgroup.inf_relIndex_right PN I).trans hPNrelI
  have hJrelI_eq : J.relIndex I = Module.finrank K L := by
    refine le_antisymm hJrelI ?_
    rw [← hPNIrelI_eq]
    exact Subgroup.relIndex_le_of_le_left hJPNI hJI_ne
  have hPpos : 0 < PNI.relIndex I := by
    rw [hPNIrelI_eq]
    exact Module.finrank_pos
  have hJrelPNI : J.relIndex PNI = 1 := by
    have h2 : J.relIndex PNI * PNI.relIndex I = 1 * PNI.relIndex I := by
      rw [Subgroup.relIndex_mul_relIndex J PNI I hJPNI inf_le_right, hJrelI_eq, one_mul,
        ← hPNIrelI_eq]
    exact Nat.eq_of_mul_eq_mul_right hPpos h2
  have hPNIJ : PNI ≤ J := Subgroup.relIndex_eq_one.mp hJrelPNI
  -- ## consequently the principal ray is killed
  have hPIf : c.principalRay ⊓ I ≤ f.ker :=
    le_trans (le_inf (le_trans inf_le_left le_sup_left) inf_le_right)
      (le_trans hPNIJ inf_le_left)
  have hspanP : NK.CFTLib.ArtinReciprocityIdeal.spanUnit b ∈ c.principalRay :=
    Subgroup.subset_closure ⟨b, hb, rfl⟩
  have hspanI : NK.CFTLib.ArtinReciprocityIdeal.spanUnit b ∈ I :=
    Cycle.principalRay_le_idealCoprimeGroup c hlev hspanP
  have hmem : NK.CFTLib.ArtinReciprocityIdeal.spanUnit b ∈ f.ker := hPIf ⟨hspanP, hspanI⟩
  have hkerf : f (NK.CFTLib.ArtinReciprocityIdeal.spanUnit b) = 1 :=
    MonoidHom.mem_ker.mp hmem
  rw [show f (NK.CFTLib.ArtinReciprocityIdeal.spanUnit b) =
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => mul_comm a b)
        (NK.CFTLib.ArtinReciprocityIdeal.spanUnit b) from rfl] at hkerf
  rw [NK.CFTLib.ArtinReciprocityIdeal.coe_spanUnit] at hkerf
  exact hkerf

end Work.SSGRoute.ZDataMup
