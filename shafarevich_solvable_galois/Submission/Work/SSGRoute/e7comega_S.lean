import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.e7comega_lift
import Submission.Work.SSGRoute.classLocIncl_injective_clean
import Submission.Work.SSGRoute.E7cOmega.eq_of_extLoc_eq_of_orbitSupported
import Submission.Work.SSGRoute.E7cOmega.exists_transversal_mem_of_mulAction
import Submission.Work.SSGRoute.e9c_phiAt_eq_zero_of_local
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.local_duality_ext_realization_of_detection
import Submission.Work.SSGRoute.iInter_nonempty_of_directed_finite
import Submission.Work.SSGRoute.ext_units_single_place
import Submission.Work.SSGRoute.ext_idele_shapiro
import Submission.Work.SSGRoute.lam_local_determination
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.extH_classesK_two_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7cΩ: the realisation-set machinery, self-contained

This module collects, in the namespace `Work.SSGRoute.SSG`, copies of the ingredients of the
E7cΩ assembly that would otherwise have to be imported from modules which (a) import the target
`Submission.Work.SSGRoute.local_phi_realization_in` (so that importing them from the target would
be circular: `E7cOmega/phiAt_eq_of_extLoc_eq.lean`) or (b) import the currently unbuildable
`Submission.Work.SSGRoute.ext_sha2_bridge` (`e7comega_core.lean`).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.SSG

open CategoryTheory SSGRoute.PTExt

noncomputable section
theorem extLoc_sub_local {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : NK.GlobalCFT.Place K)
    (a b : Abelian.Ext M (idelesK k K) r) :
    extLoc (k := k) (K := K) u (a - b)
      = extLoc (k := k) (K := K) u a - extLoc (k := k) (K := K) u b := by
  have hneg : extLoc (k := k) (K := K) u (-b) = -extLoc (k := k) (K := K) u b := by
    have h := extLoc_add (k := k) (K := K) u (-b) b
    rw [neg_add_cancel, extLoc_zero (k := k) (K := K) u] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [sub_eq_add_neg, extLoc_add, hneg, sub_eq_add_neg]

/-- **Equality of orbit-supported idèle `H²`-classes from their equalisation at a single place.**

Two classes `q, q' ∈ H²(Gal(L/k), 𝕀_L)` whose localisations vanish at every place outside the
`Gal(L/k)`-orbit of `r`, and which have the same `r`-localisation, are equal: the difference
`q - q'` localises to `0` at `r`, hence — by conjugation (`e9c_extLoc_conj_zero`) — at every place
of the orbit, and it vanishes outside the orbit by hypothesis, so the idèle localisation is
injective (`extIdele_localisation_injective`) and `q - q' = 0`. -/
theorem eq_of_extLoc_eq_of_orbitSupported {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (q q' : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2)
    (hq : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v q = 0)
    (hq' : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • r ≠ v) →
      SSGRoute.PTExt.extLoc (k := k) (K := L) v q' = 0)
    (h : SSGRoute.PTExt.extLoc (k := k) (K := L) r q
        = SSGRoute.PTExt.extLoc (k := k) (K := L) r q') : q = q' := by
  have key : q - q' = 0 := by
    refine Work.SSGRoute.extIdele_localisation_injective k L (q - q') ?_
    intro v
    rw [Work.SSGRoute.extRes_eq_extHRestrict
      (D := SSGRoute.PTExt.decompK (k := k) (K := L) v) (q - q')]
    change SSGRoute.PTExt.extLoc (k := k) (K := L) v (q - q') = 0
    by_cases hv : ∃ σ : L ≃ₐ[k] L, σ • r = v
    · obtain ⟨σ, rfl⟩ := hv
      have h0 : SSGRoute.PTExt.extLoc (k := k) (K := L) r (q - q') = 0 := by
        rw [extLoc_sub_local, h, sub_self]
      exact Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := L) (q - q') σ r h0
    · have hv' : ∀ σ : L ≃ₐ[k] L, σ • r ≠ v := fun σ hσ => hv ⟨σ, hσ⟩
      rw [extLoc_sub_local, hq v hv', hq' v hv', sub_self]
  exact sub_eq_zero.mp key


/-! ## `Ext`-calculus helpers -/

/-- `extRes` is compatible with negation (additivity together with `extRes_zero`). -/
theorem extRes_neg {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0, 0, 0} Coeff G} {n : ℕ} (x : Abelian.Ext X Y n) :
    extRes f (-x) = -extRes f x := by
  have key : extRes f (-x) + extRes f x = 0 := by
    rw [add_comm, ← extRes_add, add_neg_cancel, extRes_zero]
  exact eq_neg_of_add_eq_zero_left key

/-- Pushing a subtracted class through `extRes` followed by a degree-`0` coefficient map is the
subtraction of the pushed classes. -/
theorem extRes_comp_mk0_sub {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H}
    (ι : Rep.res f Y ⟶ B) {r : ℕ} (x x' : Abelian.Ext X Y r) :
    (extRes f (x - x')).comp (Abelian.Ext.mk₀ ι) (add_zero r)
      = (extRes f x).comp (Abelian.Ext.mk₀ ι) (add_zero r)
        - (extRes f x').comp (Abelian.Ext.mk₀ ι) (add_zero r) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, extRes_add, extRes_neg,
    Abelian.Ext.add_comp, Abelian.Ext.neg_comp]

/-- Localisation of the idèle-pushed class is compatible with subtraction. -/
theorem extLoc_push_sub {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep Coeff (K ≃ₐ[k] K)} (w : NK.GlobalCFT.Place L)
    (y y' : Abelian.Ext M (idelesK k K) 1) :
    extLoc (k := k) (K := L) w
        ((extRes (galRes k K L) (y - y')).comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1))
      = extLoc (k := k) (K := L) w
          ((extRes (galRes k K L) y).comp
            (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1))
        - extLoc (k := k) (K := L) w
          ((extRes (galRes k K L) y').comp
            (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)) := by
  rw [extRes_comp_mk0_sub (galRes k K L) (Work.SSGRoute.idleRepMap k K L) y y',
    extLoc_sub_local]

/-! ## The main statement

The pairing `phiAt (extToClasses ·) h'` of an idèle class only depends on the localisation of the
class at the `Gal(K/k)`-orbit of `w`, provided the class vanishes off that orbit.  Indeed the
difference `z - z'` is supported on the orbit (it vanishes off it by hypothesis and at `w` by `h`),
so the idèle-pushed difference localises to `0` at every place of `L`; the localisation of the
pairing value is the Yoneda product of the localisations, hence is `0` everywhere, and injectivity
of idèle localisation on `H²` (E2) finishes. -/

theorem phiAt_eq_of_extLoc_eq {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} [Finite M] (w : NK.GlobalCFT.Place K)
    (z z' : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) 1)
    (hz : ∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) →
      SSGRoute.PTExt.extLoc (k := k) (K := K) u z = 0)
    (hz' : ∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) →
      SSGRoute.PTExt.extLoc (k := k) (K := K) u z' = 0)
    (h : SSGRoute.PTExt.extLoc (k := k) (K := K) w z
        = SSGRoute.PTExt.extLoc (k := k) (K := K) w z')
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h' : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1) :
    SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) (SSGRoute.PTExt.extToClasses z) h'
      = SSGRoute.PTExt.phiAt (k := k) (K := K) (L := L) (SSGRoute.PTExt.extToClasses z') h' := by
  -- Step 1: rewrite both sides through the idèle-level pairing.
  rw [Work.SSGRoute.phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := L) M z h',
    Work.SSGRoute.phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := L) M z' h']
  -- It suffices to prove the idèle-valued pairing classes equal.
  have hkey : levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h'
      = levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z' h' := by
    rw [← sub_eq_zero]
    apply Work.SSGRoute.extIdele_localisation_injective (k := k) (L := L)
    intro v
    rw [Work.SSGRoute.extRes_eq_extHRestrict (D := decompK (k := k) (K := L) v)]
    change extLoc (k := k) (K := L) v
      (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h'
        - levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z' h') = 0
    -- A place `u` of `K` below `v`.
    obtain ⟨u, hu⟩ :=
      NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) v
    -- `z - z'` vanishes locally at `u`: off the orbit by hypothesis, on the orbit by conjugacy.
    have hloc : extLoc (k := k) (K := K) u (z - z') = 0 := by
      by_cases hu_orb : ∃ σ : K ≃ₐ[k] K, σ • w = u
      · obtain ⟨σ, hσ⟩ := hu_orb
        have hw0 : extLoc (k := k) (K := K) w (z - z') = 0 := by
          rw [extLoc_sub_local (k := k) (K := K) w z z', h, sub_self]
        rw [← hσ]
        exact Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := K) (z - z') σ w hw0
      · have hu' : ∀ σ : K ≃ₐ[k] K, σ • w ≠ u := fun σ hσ => hu_orb ⟨σ, hσ⟩
        rw [extLoc_sub_local (k := k) (K := K) u z z', hz u hu', hz' u hu', sub_self]
    -- The pushed class localises to `0` at `v`.
    have hpushzero : extLoc (k := k) (K := L) v
        ((extRes (galRes k K L) (z - z')).comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)) = 0 :=
      Work.SSGRoute.e9c_transport_zero (z - z') u v hu hloc
    -- Hence the localisations of the two pushed classes agree at `v`.
    have hLz : extLoc (k := k) (K := L) v
          ((extRes (galRes k K L) z).comp
            (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1))
        = extLoc (k := k) (K := L) v
          ((extRes (galRes k K L) z').comp
            (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)) := by
      rw [← sub_eq_zero, ← extLoc_push_sub (k := k) (K := K) (L := L) v z z']
      exact hpushzero
    -- Localisation of the idèle-valued pairing classes, and their agreement.
    have hsub : extLoc (k := k) (K := L) v
          (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h'
            - levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z' h')
        = extLoc (k := k) (K := L) v
            (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h')
          - extLoc (k := k) (K := L) v
            (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z' h') :=
      extLoc_sub_local (k := k) (K := L) v _ _
    have h1 : extLoc (k := k) (K := L) v
          (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z h')
        = yonedaPair (extLoc (k := k) (K := L) v
              ((extRes (galRes k K L) z).comp
                (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)))
            (extHRestrict (decompK (k := k) (K := L) v) h') :=
      Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := L) M z h' v
    have h2 : extLoc (k := k) (K := L) v
          (levelPair (galRes k K L) (Work.SSGRoute.idleRepMap k K L) z' h')
        = yonedaPair (extLoc (k := k) (K := L) v
              ((extRes (galRes k K L) z').comp
                (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)))
            (extHRestrict (decompK (k := k) (K := L) v) h') :=
      Work.SSGRoute.extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := L) M z' h' v
    have hpair : yonedaPair (extLoc (k := k) (K := L) v
              ((extRes (galRes k K L) z).comp
                (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)))
            (extHRestrict (decompK (k := k) (K := L) v) h')
        = yonedaPair (extLoc (k := k) (K := L) v
              ((extRes (galRes k K L) z').comp
                (Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k K L)) (add_zero 1)))
            (extHRestrict (decompK (k := k) (K := L) v) h') :=
      congrArg (fun t => yonedaPair t (extHRestrict (decompK (k := k) (K := L) v) h')) hLz
    rw [hsub, sub_eq_zero]
    exact h1.trans (hpair.trans h2.symm)
  rw [hkey]

/-! ## Classes supported off the orbit of a place -/

/-- **A class of `H²(Gal(L/k), 𝕀_L)` supported off the orbit of `u`**: its localisation vanishes at
every place of `L` outside the `Gal(L/k)`-orbit of `u`. -/
def SupportedOff (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L] (u : NK.GlobalCFT.Place L)
    (q : extH (idelesK k L) 2) : Prop :=
  ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • u ≠ v) →
    extLoc (k := k) (K := L) v q = 0

theorem SupportedOff.sub {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] {u : NK.GlobalCFT.Place L}
    {q₁ q₂ : extH (idelesK k L) 2} (h₁ : SupportedOff k L u q₁)
    (h₂ : SupportedOff k L u q₂) : SupportedOff k L u (q₁ - q₂) := by
  intro v hv
  rw [extLoc_sub_local, h₁ v hv, h₂ v hv, sub_self]

theorem SupportedOff.zero (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (u : NK.GlobalCFT.Place L) :
    SupportedOff k L u 0 := by
  intro v _
  rw [extLoc_zero]

/-- **Injectivity of the one-orbit localisation, in `extToClasses` form.** -/
theorem SupportedOff.extLoc_eq_zero {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {u : NK.GlobalCFT.Place L} {q : extH (idelesK k L) 2} (h : SupportedOff k L u q)
    (h0 : extToClasses q = 0) : extLoc (k := k) (K := L) u q = 0 :=
  classLocIncl_injective_clean k L u q h h0

/-! ## The orbit-supported lift of a `p`-torsion class -/

/-- **The chosen orbit-supported lift of a `p`-torsion class of `H²(Gal(L/k), C_L)`.** -/
noncomputable def classLift (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : extH (classesK k L) 2) (hx : p • x = 0) : extH (idelesK k L) 2 :=
  (classLocLift_ptorsion_clean p k L w₀ hp x hx).choose

theorem classLift_ptorsion (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : extH (classesK k L) 2) (hx : p • x = 0) :
    p • classLift p k L w₀ hp x hx = 0 :=
  (classLocLift_ptorsion_clean p k L w₀ hp x hx).choose_spec.1

theorem classLift_supported (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : extH (classesK k L) 2) (hx : p • x = 0) :
    SupportedOff k L w₀ (classLift p k L w₀ hp x hx) :=
  (classLocLift_ptorsion_clean p k L w₀ hp x hx).choose_spec.2.1

theorem classLift_extToClasses (p : ℕ) [Fact p.Prime] (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w₀))
    (x : extH (classesK k L) 2) (hx : p • x = 0) :
    extToClasses (classLift p k L w₀ hp x hx) = x :=
  (classLocLift_ptorsion_clean p k L w₀ hp x hx).choose_spec.2.2

/-! ## The canonical local Brauer functional -/

theorem localBrauerFunctional_add (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {A : Type} [AddCommGroup A] (u : NK.GlobalCFT.Place L)
    (ν : A →+ extH (classesK k L) 2) (Q : A → extH (idelesK k L) 2)
    (hQsup : ∀ a : A, SupportedOff k L u (Q a))
    (hQcl : ∀ a : A, extToClasses (Q a) = ν a) (a b : A) :
    extLoc (k := k) (K := L) u (Q (a + b))
      = extLoc (k := k) (K := L) u (Q a) + extLoc (k := k) (K := L) u (Q b) := by
  have h1 : extLoc (k := k) (K := L) u (Q (a + b) - Q a - Q b) = 0 :=
    (((hQsup (a + b)).sub (hQsup a)).sub (hQsup b)).extLoc_eq_zero (by
      rw [extToClasses_sub, extToClasses_sub, hQcl (a + b), hQcl a, hQcl b, map_add,
        add_sub_cancel_left, sub_self])
  rw [extLoc_sub_local, extLoc_sub_local] at h1
  have h2 := sub_eq_zero.mp h1
  exact (sub_eq_iff_eq_add.mp h2).trans (add_comm _ _)

theorem localBrauerFunctional_zero (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {A : Type} [AddCommGroup A] (u : NK.GlobalCFT.Place L)
    (ν : A →+ extH (classesK k L) 2) (Q : A → extH (idelesK k L) 2)
    (hQsup : ∀ a : A, SupportedOff k L u (Q a))
    (hQcl : ∀ a : A, extToClasses (Q a) = ν a) :
    extLoc (k := k) (K := L) u (Q 0) = 0 :=
  (hQsup 0).extLoc_eq_zero (by rw [hQcl 0, map_zero])

/-- **The canonical local Brauer functional.** -/
noncomputable def localBrauerFunctional (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {A : Type} [AddCommGroup A] (u : NK.GlobalCFT.Place L)
    (ν : A →+ extH (classesK k L) 2) (Q : A → extH (idelesK k L) 2)
    (hQsup : ∀ a : A, SupportedOff k L u (Q a))
    (hQcl : ∀ a : A, extToClasses (Q a) = ν a) :
    A →+ extH (localUnitsK (k := k) (K := L) u) 2 :=
  AddMonoidHom.mk' (fun a => extLoc (k := k) (K := L) u (Q a))
    (fun a b => localBrauerFunctional_add k L u ν Q hQsup hQcl a b)

theorem localBrauerFunctional_apply (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {A : Type} [AddCommGroup A] (u : NK.GlobalCFT.Place L)
    (ν : A →+ extH (classesK k L) 2) (Q : A → extH (idelesK k L) 2)
    (hQsup : ∀ a : A, SupportedOff k L u (Q a))
    (hQcl : ∀ a : A, extToClasses (Q a) = ν a) (a : A) :
    localBrauerFunctional k L u ν Q hQsup hQcl a = extLoc (k := k) (K := L) u (Q a) := rfl

theorem localBrauerFunctional_congr (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {A : Type} [AddCommGroup A] (u : NK.GlobalCFT.Place L)
    (ν : A →+ extH (classesK k L) 2) (Q₁ Q₂ : A → extH (idelesK k L) 2)
    (h₁sup : ∀ a : A, SupportedOff k L u (Q₁ a))
    (h₁cl : ∀ a : A, extToClasses (Q₁ a) = ν a)
    (h₂sup : ∀ a : A, SupportedOff k L u (Q₂ a))
    (h₂cl : ∀ a : A, extToClasses (Q₂ a) = ν a) :
    localBrauerFunctional k L u ν Q₁ h₁sup h₁cl
      = localBrauerFunctional k L u ν Q₂ h₂sup h₂cl := by
  ext a
  rw [localBrauerFunctional_apply, localBrauerFunctional_apply]
  have h := ((h₁sup a).sub (h₂sup a)).extLoc_eq_zero (by
    rw [extToClasses_sub, h₁cl a, h₂cl a, sub_self])
  rw [extLoc_sub_local] at h
  exact sub_eq_zero.mp h

/-! ## Realisation of a functional by the level pairing -/

/-- **`y` realises `lam` by the level pairing** at the level data `(f, ι)`. -/
def RealisesLevel {G H : Type} [Group G] [Group H] (f : H →* G)
    {M : Rep.{0, 0, 0} Coeff G} {A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H}
    (ι : Rep.res f A ⟶ B) (y : Abelian.Ext.{0} M A 1)
    (lam : extH (Rep.res f M) 1 →+ extH B 2) : Prop :=
  ∀ h : extH (Rep.res f M) 1, levelPair f ι y h = lam h

/-- **E7b(ii): realisation of `p`-torsion functionals.** -/
theorem exists_realisesLevel (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (lam : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1
      →+ extH (NK.HassePrinciple.localUnitsRep k L w') 2)
    (hlam : ∀ h, p • lam h = 0) :
    ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      RealisesLevel f ι y lam :=
  local_duality_ext_realization_of_detection p k K M hM w L w' hw' f hf ι hι hp
    (fun h hne => local_duality_ext_detect_h p k K ζ hζ M hM w L w' hw' f hf ι hι hp h hne)
    lam hlam

/-! ## The orbit-supported class with prescribed localisation -/

/-- **The orbit-supported lift of a local class.**  For a finite `Gal(K/k)`-module `M`, a place `w`
of `K` and a local class `a ∈ Ext^r_{D_w}(M, K_wˣ)`, there is an idèle class
`z ∈ Ext^r_{Gal(K/k)}(M, 𝕀_K)` whose `w`-component is `a` and whose `u`-component vanishes at
every place `u` outside the `Gal(K/k)`-orbit of `w` (idèle Shapiro, `Work.SSGRoute.ext_idele_shapiro`
clause (iii), applied to a transversal containing `w`). -/
theorem exists_orbitSupported_extLoc_gen {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (r : ℕ) (w : NK.GlobalCFT.Place K)
    (a : Abelian.Ext (Rep.res (decompK (k := k) (K := K) w).subtype M)
      (localUnitsK (k := k) w) r) :
    ∃ z : Abelian.Ext M (idelesK k K) r, extLoc (k := k) (K := K) w z = a ∧
      ∀ v : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ v) →
        extLoc (k := k) (K := K) v z = 0 := by
  classical
  obtain ⟨R, hrR, hR⟩ := E7cOmega.exists_transversal_mem_of_mulAction (K ≃ₐ[k] K)
    (NK.GlobalCFT.Place K) w
  let b : ∀ v : R, Abelian.Ext (Rep.res (decompK (k := k) (K := K) v.1).subtype M)
      (localUnitsK (k := k) v.1) r :=
    fun v => if h : v.1 = w then h.symm ▸ a else 0
  have hb_w : b ⟨w, hrR⟩ = a := by
    show (if h : (⟨w, hrR⟩ : R).1 = w then h.symm ▸ a else 0) = a
    rw [dif_pos (rfl : (⟨w, hrR⟩ : R).1 = w)]
  have hb_fin : {v : R | ¬ IsUnramifiedExt (k := k) (K := K) v.1 (b v)}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton (⟨w, hrR⟩ : R)) ?_
    intro v hv
    by_contra hne
    refine hv ?_
    have hvr : v.1 ≠ w := fun h => hne (Subtype.ext h)
    have hb0 : b v = 0 := by
      show (if h : v.1 = w then h.symm ▸ a else 0) = 0
      rw [dif_neg hvr]
    rw [hb0]
    exact ⟨0, by simp⟩
  obtain ⟨q, hq⟩ := (ext_idele_shapiro k K M r R hR).2.2 b hb_fin
  refine ⟨q, ?_, ?_⟩
  · rw [hq ⟨w, hrR⟩, hb_w]
  · intro v hv
    obtain ⟨v', ⟨σ, hσ⟩, -⟩ := hR v
    have hv'r : v'.1 ≠ w := by
      intro h
      have hσv : σ • v = w := hσ.trans h
      have hv1 : σ⁻¹ • w = v := by rw [← hσv]; simp
      exact hv σ⁻¹ hv1
    have hb0 : b v' = 0 := by
      show (if h : v'.1 = w then h.symm ▸ a else 0) = 0
      rw [dif_neg hv'r]
    have hzero : extLoc (k := k) (K := K) v'.1 q = 0 := by
      rw [hq v', hb0]
    have hconj := Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := K) q σ⁻¹ v'.1 hzero
    have hv1 : σ⁻¹ • v'.1 = v := by
      calc σ⁻¹ • v'.1 = σ⁻¹ • (σ • v) := by rw [← hσ]
        _ = v := by simp
    rw [hv1] at hconj
    exact hconj

end

end Work.SSGRoute.SSG
