/-
Copyright: the martinet_totally_real_towers team.

# The connecting homomorphisms of the long exact sequence

For a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules we define the connecting
maps `δ⁰ : H⁰(G,C) → H¹(G,A)` and `δ¹ : H¹(G,C) → H²(G,A)` of the long exact sequence, by the
classical formulas on representatives.

The exactness statements live in `Submission.Work.ConCohomology.LongExact`.
-/

import Submission.Work.ConCohomology.GaloisUnits
import Submission.Work.ConCohomology.isCocycle1_delta0Fun
import Submission.Work.ConCohomology.isLocallyConstant_delta1Fun
import Submission.Work.ConCohomology.isCocycle2_delta1Fun
import Submission.Work.ConCohomology.exists_cochain_delta1Fun_add_coboundary

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section Connecting

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

variable (S : CoeffSES G A B C)

lemma isLocallyConstant_delta0Fun (c : C) : IsLocallyConstant (S.delta0Fun c) :=
  ((IsDiscreteGModule.isLocallyConstant_smul (G := G) (S.sect c)).sub
    (IsLocallyConstant.const (S.sect c))).comp S.invFun

/-- The `1`-cocycle `σ ↦ f⁻¹(σ·s - s)` attached to an invariant element `c` of `C`, where `s` is
a lift of `c`. -/
noncomputable def delta0Cocycle (c : H0 G C) : Z1 G A :=
  ⟨⟨S.delta0Fun (c : C), isLocallyConstant_delta0Fun S _⟩,
    mem_Z1.mpr (isCocycle1_delta0Fun S (c : C) c.2)⟩

/-- The connecting map `δ⁰ : H⁰(G,C) → H¹(G,A)`. -/
noncomputable def connecting0 : H0 G C → H1 G A :=
  fun c => H1.mk (delta0Cocycle S c)

@[simp] lemma connecting0_apply (c : H0 G C) :
    connecting0 S c = H1.mk (delta0Cocycle S c) := rfl

@[simp] lemma delta0Cocycle_coe (c : H0 G C) :
    ((delta0Cocycle S c : Z1 G A) : Cochain1 G A) =
      ⟨S.delta0Fun (c : C), isLocallyConstant_delta0Fun S _⟩ := rfl

/-- The connecting map `δ¹ : H¹(G,C) → H²(G,A)`, on the level of cocycles. -/
noncomputable def connectingZ1 (z : Z1 G C) : Z2 G A :=
  ⟨⟨S.delta1Fun (z : G → C), isLocallyConstant_delta1Fun S z⟩,
    mem_Z2.mpr (isCocycle2_delta1Fun S _ (mem_Z1.mp z.2))⟩

@[simp] lemma connectingZ1_coe (z : Z1 G C) :
    ((connectingZ1 S z : Z2 G A) : Cochain2 G A) =
      ⟨S.delta1Fun (z : G → C), isLocallyConstant_delta1Fun S z⟩ := rfl

lemma connecting1_aux (z w : Z1 G C) (h : (QuotientAddGroup.leftRel (B1' G C)) z w) :
    H2.mk (connectingZ1 S z) = H2.mk (connectingZ1 S w) := by
  have hab : -z + w ∈ B1' G C := by
    rw [← QuotientAddGroup.leftRel_apply]
    exact h
  rw [mem_B1'] at hab
  obtain ⟨γ, hγ⟩ := hab
  have hγ' : (w : G → C) = fun σ => (z : G → C) σ + d0Fun (G := G) γ σ := by
    funext σ
    have hσ := DFunLike.congr_fun hγ σ
    simp only [d0Hom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg, LocallyConstant.coe_add,
      LocallyConstant.coe_neg, Pi.add_apply, Pi.neg_apply] at hσ
    rw [d0Fun_apply, hσ]
    abel
  obtain ⟨u, hu⟩ := exists_cochain_delta1Fun_add_coboundary S z (mem_Z1.mp z.2) γ
  have hu' : S.delta1Fun ((w : Z1 G C) : G → C) - S.delta1Fun ((z : Z1 G C) : G → C) =
      d1Fun (G := G) u := by
    rw [hγ']
    exact hu
  have h1 : ((connectingZ1 S w - connectingZ1 S z : Z2 G A) : Cochain2 G A) = d1Hom G A u := by
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    have hp := congrFun hu' (σ, τ)
    simp only [Pi.sub_apply, d1Fun_apply] at hp
    change S.delta1Fun ((w : Z1 G C) : G → C) (σ, τ) -
      S.delta1Fun ((z : Z1 G C) : G → C) (σ, τ) = σ • u τ - u (σ * τ) + u σ
    exact hp
  have hmem : (connectingZ1 S w - connectingZ1 S z) ∈ B2' G A := by
    rw [mem_B2']
    exact ⟨u, h1.symm⟩
  exact ((H2.mk_eq_mk_iff _ _).mpr hmem).symm

/-- The connecting map `δ¹ : H¹(G,C) → H²(G,A)`. -/
noncomputable def connecting1 : H1 G C → H2 G A :=
  Quotient.lift (fun z : Z1 G C => H2.mk (connectingZ1 S z)) (fun z w h => connecting1_aux S z w h)

lemma connecting1_mk (z : Z1 G C) :
    connecting1 S (H1.mk z) = H2.mk (connectingZ1 S z) :=
  Quotient.lift_mk (fun z : Z1 G C => H2.mk (connectingZ1 S z))
    (fun z w h => connecting1_aux S z w h) z

end Connecting

end Work.ConCohomology
