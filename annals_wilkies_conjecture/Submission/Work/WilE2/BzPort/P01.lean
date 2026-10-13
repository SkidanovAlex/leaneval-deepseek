/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Order.WellQuasiOrder.exists_finset_subset_forall_le` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

theorem ringKrullDim_mvPoly_fin_card {K : Type*} [Field K] {k : Nat} :
    ringKrullDim (MvPolynomial (Fin k) K) = (k : WithBot ENat) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

-- ==== from Submission.Commons.Order.WellQuasiOrder.exists_finset_subset_forall_le ====
section

namespace Commons.Order.WellQuasiOrder

open Set

/-- In a well-quasi-ordered preorder, every subset `S` admits a finite subset `A ⊆ S`
whose down-closure contains `S`: every `s ∈ S` is above some `a ∈ A`. -/
theorem exists_finset_subset_forall_le {α : Type*} [Preorder α] [WellQuasiOrderedLE α]
    (S : Set α) : ∃ A : Finset α, (∀ a ∈ A, a ∈ S) ∧ ∀ s ∈ S, ∃ a ∈ A, a ≤ s := by
  classical
  have : WellQuasiOrderedLE (Antisymmetrization α (· ≤ ·)) :=
    Monotone.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
      (f := toAntisymmetrization (α := α) (· ≤ ·)) (toAntisymmetrization_mono (α := α))
      (fun b => ⟨ofAntisymmetrization (α := α) (· ≤ ·) b,
        toAntisymmetrization_ofAntisymmetrization (α := α) (r := (· ≤ ·)) b⟩)
  let T : Set (Antisymmetrization α (· ≤ ·)) := toAntisymmetrization (α := α) (· ≤ ·) '' S
  have hT : T.IsPWO := isPWO_of_wellQuasiOrderedLE T
  let M : Set (Antisymmetrization α (· ≤ ·)) := {m | Minimal (· ∈ T) m}
  have hanti : IsAntichain (· ≤ ·) M := by
    intro m hm m' hm' hne hle
    exact hne (le_antisymm hle (hm'.2 hm.1 hle))
  have hfin : M.Finite := hanti.finite_of_wellQuasiOrdered wellQuasiOrdered_le
  have hrep : ∀ m, m ∈ M →
      ∃ a ∈ S, toAntisymmetrization (α := α) (· ≤ ·) a = m := fun m hm => hm.1
  let A : Finset α := hfin.toFinset.attach.image
    (fun m => Classical.choose (hrep m.1 (hfin.mem_toFinset.mp m.2)))
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Classical.choose_spec (hrep m.1 (hfin.mem_toFinset.mp m.2))).1
  · intro s hs
    obtain ⟨m, hle, hm⟩ := hT.exists_le_minimal
      (show toAntisymmetrization (α := α) (· ≤ ·) s ∈ T from Set.mem_image_of_mem _ hs)
    have hmM : m ∈ M := hm
    refine ⟨Classical.choose (hrep m hmM), ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨⟨m, hfin.mem_toFinset.mpr hmM⟩, Finset.mem_attach _ _, ?_⟩
      rfl
    · have hqa : toAntisymmetrization (α := α) (· ≤ ·)
          (Classical.choose (hrep m hmM)) = m := (Classical.choose_spec (hrep m hmM)).2
      have h1 : toAntisymmetrization (α := α) (· ≤ ·) (Classical.choose (hrep m hmM)) ≤
          toAntisymmetrization (α := α) (· ≤ ·) s := by rw [hqa]; exact hle
      exact toAntisymmetrization_le_toAntisymmetrization_iff.mp h1

end Commons.Order.WellQuasiOrder
end


