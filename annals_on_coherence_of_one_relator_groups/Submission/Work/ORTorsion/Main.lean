/-
# Node N8: Lemma 5.1′ (the torsion crux)

The main theorem `Work.ORTorsion.torsionFree_tensor`: for a one-relator group `G = ⟨X | u ^ l⟩`
with `K` of characteristic zero and `β ∈ K[G]` whose support maps injectively into
`G ⧸ ⟨⟨u⟩⟩`, the diagonal action of `β` on `V ⊗[K] S` (`S = D(⊤)`) is injective.

The proof is the strong induction of L6 of `N8_TORSION_LEAD.md`.
-/
import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Basic
import Submission.Work.ORTorsion.Base.card_support_single_mul
import Submission.Work.ORTorsion.Base.injective_of_card_one
import Submission.Work.ORTorsion.Base.injective_single_smul
import Submission.Work.ORTorsion.Base.mem_support_single_mul
import Submission.Work.ORTorsion.Denom.exists_mem_R_of_killed
import Submission.Work.ORTorsion.Descent.injective_of_injective_DH
import Submission.Work.ORTorsion.Equiv.incl_top_of_DN
import Submission.Work.ORTorsion.GroupOps.fg_closure_finset
import Submission.Work.ORTorsion.GroupOps.surjective_of_locallyIndicable_quotient
import Submission.Work.ORTorsion.LeadingTerm.exists_degree_killed
import Submission.Work.ORTorsion.Support.card_support_mapToG
import Submission.Work.ORTorsion.Support.closure_support_eq_top
import Submission.Work.ORTorsion.Support.degCoeff_support_card_lt
import Submission.Work.ORTorsion.Support.exists_deg_ne_zero
import Submission.Work.ORTorsion.Support.exists_mapToG_eq
import Submission.Work.ORTorsion.Support.injOn_degCoeff
import Submission.Work.ORTorsion.Support.mem_support_mapToG
import Submission.Work.ORTorsion.Support.sum_coeff_smul_single

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped TensorProduct

namespace Work.ORTorsion

open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-- **Lemma 5.1′** (Jaikin-Zapirain--Linton).  Let `L` be the torsion setting of a one-relator
group `G = ⟨X | u ^ l⟩` with root `L.u`, and let `β ∈ K[G]` be nonzero with the images of its
support in `G ⧸ ⟨⟨u⟩⟩` pairwise distinct.  Then the diagonal action of `β` on `V ⊗[K] D(⊤)` is
injective. -/
theorem torsionFree_tensor (L : TorsionData K G U) (V : Type*) [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (β : MonoidAlgebra K G)
    (hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u})) β.coeff.support)
    (hβ0 : β ≠ 0) :
    Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) => β • m) := by
  classical
  have main : ∀ (n : ℕ) (β : MonoidAlgebra K G), β ≠ 0 →
      Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u})) β.coeff.support →
      β.coeff.support.card ≤ n →
      Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) => β • m) := by
    intro n
    induction n with
    | zero =>
      intro β hβ0 _ hcard
      have h0 : β = 0 := by
        rw [← MonoidAlgebra.coeff_eq_zero]
        exact Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact absurd h0 hβ0
    | succ n ih =>
      intro β hβ0 hβ hcard
      by_cases hone : β.coeff.support.card = 1
      · exact Work.ORTorsion.Base.injective_of_card_one L β hone
      · -- normalise: replace `β` by `single g⁻¹ 1 * β` so that `1` lies in the support
        have hnonempty : β.coeff.support.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          exact hβ0 (MonoidAlgebra.coeff_eq_zero.mp (Finsupp.support_eq_empty.mp hempty))
        obtain ⟨g, hg⟩ := hnonempty
        set β' : MonoidAlgebra K G := MonoidAlgebra.single g⁻¹ (1 : K) * β with hβ'def
        have hβeq : β = MonoidAlgebra.single g (1 : K) * β' := by
          rw [hβ'def, ← mul_assoc, MonoidAlgebra.single_mul_single, mul_inv_cancel, mul_one]
          rw [show (MonoidAlgebra.single (1 : G) (1 : K) : MonoidAlgebra K G) = 1 from rfl,
            one_mul]
        have hcard' : β'.coeff.support.card = β.coeff.support.card :=
          Work.ORTorsion.Base.card_support_single_mul g⁻¹ β
        have h1' : (1 : G) ∈ β'.coeff.support := by
          rw [hβ'def, Work.ORTorsion.Base.mem_support_single_mul]
          simpa using hg
        have hβ'0 : β' ≠ 0 := by
          intro hzero
          rw [hβeq, hzero, mul_zero] at hβ0
          exact hβ0 rfl
        have hβ'inj : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
            β'.coeff.support := by
          intro a ha b hb hab
          rw [hβ'def] at ha hb
          have ha' : g * a ∈ β.coeff.support := by
            simpa using (Work.ORTorsion.Base.mem_support_single_mul g⁻¹ β a).mp ha
          have hb' : g * b ∈ β.coeff.support := by
            simpa using (Work.ORTorsion.Base.mem_support_single_mul g⁻¹ β b).mp hb
          have h2 : g * a = g * b := hβ ha' hb' (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hab])
          exact mul_left_cancel h2
        -- the induction step for the normalised element
        have hstep : Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) => β' • m) := by
          set H : Subgroup G := Subgroup.closure ((β'.coeff.support : Finset G) : Set G) with hHdef
          have hsuppH : ∀ g ∈ β'.coeff.support, g ∈ H :=
            fun g hg => Subgroup.subset_closure hg
          obtain ⟨x, hx⟩ := Work.ORTorsion.Support.exists_mapToG_eq β' hsuppH
          have hx0 : x ≠ 0 := by
            intro hzero
            rw [hzero, map_zero] at hx
            exact hβ'0 hx.symm
          have hx1 : (1 : H) ∈ x.coeff.support := by
            rw [← Work.ORTorsion.Support.mem_support_mapToG x 1, hx]
            exact h1'
          have hgen : Subgroup.closure ((x.coeff.support : Finset H) : Set H) = ⊤ :=
            Work.ORTorsion.Support.closure_support_eq_top x (by rw [hx])
          have hFG : H.FG := Work.ORTorsion.GroupOps.fg_closure_finset β'.coeff.support
          have hgc : ∃ g ∈ β'.coeff.support, g ≠ 1 := by
            have hc0 : β'.coeff.support.card ≠ 0 := Finset.card_ne_zero_of_mem h1'
            have hc2 : 2 ≤ β'.coeff.support.card := by
              rw [hcard']; omega
            by_contra hcon
            push_neg at hcon
            have hsub : β'.coeff.support ⊆ {1} := fun g hg => by
              simp [hcon g hg]
            have hle : β'.coeff.support.card ≤ 1 := by
              rw [Finset.card_le_one]
              intro a ha b hb
              rw [show a = 1 from Finset.mem_singleton.mp (hsub ha),
                show b = 1 from Finset.mem_singleton.mp (hsub hb)]
            omega
          have hne : H.map (QuotientGroup.mk' (Subgroup.normalClosure {L.u})) ≠ ⊥ := by
            obtain ⟨g₀, hg₀, hg₀1⟩ := hgc
            intro hbot
            have hmem : QuotientGroup.mk g₀ ∈ H.map (QuotientGroup.mk' (Subgroup.normalClosure {L.u})) :=
              ⟨g₀, hsuppH g₀ hg₀, rfl⟩
            rw [hbot] at hmem
            simp only [Subgroup.mem_bot] at hmem
            refine hg₀1 (hβ'inj hg₀ h1' ?_)
            rw [hmem]
            simp
          obtain ⟨φ, hφ⟩ := Work.ORTorsion.GroupOps.surjective_of_locallyIndicable_quotient
            (Subgroup.normalClosure {L.u}) L.quotient_locallyIndicable H hFG hne
          set Lb : LaurentBase K U G L.gen L.D H φ := L.laurent H φ hφ with hLbdef
          have hinjDH : Function.Injective (fun m : V ⊗[K] ↥(L.D H) => x • m) := by
            intro m m' hmm
            by_contra hne'
            have hne'' : m - m' ≠ 0 := fun h => hne' (sub_eq_zero.mp h)
            have hxm : x • (m - m') = 0 := by
              rw [smul_sub]
              exact sub_eq_zero.mpr hmm
            obtain ⟨m₂, hm₂, hxm₂⟩ := Work.ORTorsion.Denom.exists_mem_R_of_killed L Lb x (m - m') hne'' hxm
            obtain ⟨b, z, hb, hz, hz0⟩ :=
              Work.ORTorsion.LeadingTerm.exists_degree_killed L Lb x hx0 m₂ hm₂ hxm₂
            have hdegne : ∃ h ∈ x.coeff.support, deg φ h ≠ b := by
              rcases eq_or_ne b 0 with hb0 | hb0
              · subst hb0
                exact Work.ORTorsion.Support.exists_deg_ne_zero φ hφ x hx1 hgen
              · exact ⟨1, hx1, by simpa [deg] using Ne.symm hb0⟩
            have hcardlt := Work.ORTorsion.Support.degCoeff_support_card_lt L Lb x b hdegne
            set γ : MonoidAlgebra K G := mapToG Lb.N (LaurentBase.degCoeff Lb b x) with hγdef
            have hγ0 : γ ≠ 0 := by
              intro hzγ
              have hne : (LaurentBase.degCoeff Lb b x).coeff.support.Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro hE
                exact hb (MonoidAlgebra.coeff_eq_zero.mp (Finsupp.support_eq_empty.mp hE))
              obtain ⟨h, hh⟩ := hne
              have hmem : (h : G) ∈ γ.coeff.support := by
                rw [hγdef, Work.ORTorsion.Support.mem_support_mapToG]
                exact hh
              rw [hzγ] at hmem
              simp at hmem
            have hγinj : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
                γ.coeff.support := by
              rw [hγdef]
              exact Work.ORTorsion.Support.injOn_degCoeff L Lb x b (by rw [hx]; exact hβ'inj)
            have hγcard : γ.coeff.support.card ≤ n := by
              rw [hγdef, Work.ORTorsion.Support.card_support_mapToG]
              have hxc : x.coeff.support.card = β'.coeff.support.card := by
                rw [← Work.ORTorsion.Support.card_support_mapToG x, hx]
              omega
            have ihγ := ih γ hγ0 hγinj hγcard
            have hzincl : (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
                (Subalgebra.inclusion (L.D_mono (le_top : Lb.N ≤ ⊤))).toLinearMap) z ≠ 0 :=
              fun h => hz (Work.ORTorsion.incl_injective (L.D_mono (le_top : Lb.N ≤ ⊤)) h)
            refine hzincl (ihγ ?_)
            change γ • (TensorProduct.map LinearMap.id
                (Subalgebra.inclusion (L.D_mono (le_top : Lb.N ≤ ⊤))).toLinearMap z)
              = γ • (0 : V ⊗[K] ↥(L.D ⊤))
            rw [hγdef, ← Work.ORTorsion.Equiv.incl_top_of_DN L (LaurentBase.degCoeff Lb b x) z,
              hz0]
            simp
          rw [← hx]
          exact Work.ORTorsion.Descent.injective_of_injective_DH L H x hinjDH
        -- transfer back from the normalised element
        intro m m' hmm
        have h1 : (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • (β' • m)
            = (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K G) • (β' • m') := by
          rw [TorsionData.instDiagTopSmul_mul (L := L) V
                (MonoidAlgebra.single g (1 : K)) β' m,
              TorsionData.instDiagTopSmul_mul (L := L) V
                (MonoidAlgebra.single g (1 : K)) β' m',
              ← hβeq]
          exact hmm
        exact hstep (Work.ORTorsion.Base.injective_single_smul L g h1)
  exact main β.coeff.support.card β hβ0 hβ le_rfl

end Work.ORTorsion
