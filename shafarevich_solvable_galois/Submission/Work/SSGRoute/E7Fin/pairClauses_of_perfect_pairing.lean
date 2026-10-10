import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H1Pair.Clauses
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

/-- The clause bundle `H1Pair.PairClauses` for the pairing on locally constant cocycles induced by
a pairing `B` on the two local `H¹`-spaces: bilinearity and the coboundary clause are inherited
from the `𝔽_p`-linearity of `B` together with `toClass_add`/`toClass_eq_zero_iff`, and perfectness
on each side is `hndL`/`hndR` together with `toClass_surjective`. -/
theorem pairClauses_of_perfect_pairing
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (B : Work.SSGRoute.H1loc p k Ω K M H →ₗ[ZMod p]
      Work.SSGRoute.H1loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (hndL : ∀ x : Work.SSGRoute.H1loc p k Ω K M H, (∀ y, B x y = 0) → x = 0)
    (hndR : ∀ y : Work.SSGRoute.H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H, (∀ x, B x y = 0) → y = 0) :
    Work.SSGRoute.H1Pair.PairClauses p K T M
      (fun a b => B (Work.SSGRoute.toClass p k Ω K M H a)
        (Work.SSGRoute.toClass p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H b)) H := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- additivity in the first variable
    intro a a' b ha ha' _
    have haC : a ∈ lcCocycles p k Ω K M H := (mem_lcCocycles p k Ω K M H a).mpr ha
    have ha'C : a' ∈ lcCocycles p k Ω K M H := (mem_lcCocycles p k Ω K M H a').mpr ha'
    show B (toClass p k Ω K M H (a + a'))
        (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b)
      = B (toClass p k Ω K M H a) (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b)
        + B (toClass p k Ω K M H a') (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b)
    simp only [toClass_add p k Ω K M H haC ha'C, map_add, LinearMap.add_apply]
  · -- additivity in the second variable
    intro a b b' _ hb hb'
    have hbC : b ∈ lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H :=
      (mem_lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b).mpr hb
    have hb'C : b' ∈ lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H :=
      (mem_lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b').mpr hb'
    show B (toClass p k Ω K M H a) (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H (b + b'))
      = B (toClass p k Ω K M H a) (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b)
        + B (toClass p k Ω K M H a) (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b')
    simp only [toClass_add p k Ω K (DualMod p (M ⊗[ZMod p] T)) H hbC hb'C, map_add]
  · -- vanishing on coboundaries
    intro a b ha hb hcob
    have haC : a ∈ lcCocycles p k Ω K M H := (mem_lcCocycles p k Ω K M H a).mpr ha
    have hbC : b ∈ lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H :=
      (mem_lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b).mpr hb
    show B (toClass p k Ω K M H a) (toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b) = 0
    rcases hcob with h | h
    · have h0 : toClass p k Ω K M H a = 0 :=
        (toClass_eq_zero_iff p k Ω K M H haC).mpr ((mem_coboundaries p k Ω K M H a).mpr h)
      rw [h0]; simp
    · have h0 : toClass p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b = 0 :=
        (toClass_eq_zero_iff p k Ω K (DualMod p (M ⊗[ZMod p] T)) H hbC).mpr
          ((mem_coboundaries p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b).mpr h)
      rw [h0]; simp
  · -- perfectness on the left
    intro a ha hall
    have haC : a ∈ lcCocycles p k Ω K M H := (mem_lcCocycles p k Ω K M H a).mpr ha
    refine (mem_coboundaries p k Ω K M H a).mp ?_
    rw [← (toClass_eq_zero_iff p k Ω K M H haC)]
    apply hndL
    intro y
    obtain ⟨g, hg, hgy⟩ := toClass_surjective p k Ω K (DualMod p (M ⊗[ZMod p] T)) H y
    rw [← hgy]
    exact hall g ((mem_lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H g).mp hg)
  · -- perfectness on the right
    intro b hb hall
    have hbC : b ∈ lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H :=
      (mem_lcCocycles p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b).mpr hb
    refine (mem_coboundaries p k Ω K (DualMod p (M ⊗[ZMod p] T)) H b).mp ?_
    rw [← (toClass_eq_zero_iff p k Ω K (DualMod p (M ⊗[ZMod p] T)) H hbC)]
    apply hndR
    intro x
    obtain ⟨g, hg, hgx⟩ := toClass_surjective p k Ω K M H x
    rw [← hgx]
    exact hall g ((mem_lcCocycles p k Ω K M H g).mp hg)

end Work.SSGRoute.E7Fin
