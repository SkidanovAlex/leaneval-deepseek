import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.two_torsion_lift_odd
import Submission.Work.SSGRoute.local_factorisation
import Submission.Work.SSGRoute.local_clause_conj_transfer
import Submission.Work.SSGRoute.kerSuccCocycle_transport_mem_Z2
import Submission.Work.SSGRoute.exists_localCocycle
import Submission.Work.SSGRoute.exists_shapiro_packaging
import Submission.Work.SSGRoute.ramifiedPlaces_finite
import Submission.Work.SSGRoute.isT1Place_of_isConjPlace
import Submission.Work.SSGRoute.ShapiroNaturalDefs
import Submission.Work.SSGRoute.two_torsion_lift_two
import Submission.Work.SSGRoute.shapiro_packaging_natural
import Submission.Work.SSGRoute.two_torsion_bridge
import Submission.Work.SSGRoute.involutions_eq_one_or_conjugate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `stage_local_shrinking` (Schmidt–Wingberg, Step 1a of Theorem 15) — file plan and helpers

This file must prove `Work.SSGRoute.stage_local_shrinking` (statement at the bottom, unchanged).
The mathematical content is Step 1a of the proof of Theorem 15 of *Šafarevič's theorem on solvable
groups as Galois groups* (A. Schmidt and K. Wingberg, arXiv:math/9809211, §5, pp. 21–23): given a
Scholz solution `φ : G_ℚ →* Γ_m(τ)` at a large level `m`, one finds a surjective `G`-operator map
`Φ : F(m) ⇢ F(n)` such that

* (A) for every place `A` with `IsT1Place p K A` the group extension `Γ_n(τ+1) ↠ Γ_n(τ)` splits
  over the image of `(flowGroupMap Φ) ∘ φ` on `decomp ℚ A`, with a splitting killing the kernel;
* (B) the same over `⟨c⟩` for every involution `c ∈ G_ℚ`.

## The two independent halves

**(A) Places.**  For `A ∈ T¹` the Scholz condition (i) makes `φ|_{D_A}` factor through the
restriction map (`φ̄_A : D_A(K/ℚ) →* Γ_m(τ)`), so the level-`m` local class
`c_A ∈ H²(D_A(K/ℚ), E(m,τ))` (pullback of the extension class of `flowGroupSucc`) is defined.
Killing all the (Shapiro-induced) classes with Proposition 6
(`Work.CohomologicalShrinking.exists_shrinking_H2_tate`, which needs `Prop5Data p G i j`) gives
`Φ`; naturality of the section cocycle (`kerSuccCocycle_naturality`) plus the splitting criterion
(`exists_lift_iff_kerSuccCocycle`) then give the local splitting, first for one place per conjugacy
class (a finite set, `SSGRoute.ramifiedPlaces_finite`) and then, by `G`-equivariance, for all
places of `T¹`.

**(B) Involutions.**  This clause is obtained by the *same* shrinking argument, with the cyclic
subgroup `⟨res c₀⟩` of a chosen nontrivial involution added to the family of local subgroups of
`T`: `shapiro_packaging_natural` packages the local classes *and* the transported section cocycle of
`⟨res c₀⟩` into the single module `T = shapiroT p G (Option ↥S') H'`, so that one application of
`exists_shrinking_H2_tate` (Proposition 6) kills everything at once.  `level_n_of_cocycle_killed_ssg`
then converts the vanishing of the involution class into a lift of `Ψ = (flowGroupMap Φ) ∘ φ` over
`⟨res c₀⟩`, which is pulled back to `⟨c₀⟩`, and — since all nontrivial involutions of `G_ℚ` are
conjugate (`involutions_eq_one_or_conjugate`) — transferred to every other involution of `G_ℚ` by
`involution_clause_conj_transfer_ssg`.  The degenerate branch (no involution outside
`K.fixingSubgroup`) is `involution_clause_of_mem_fixingSubgroup_ssg`.

## Status (complete)

The target theorem is *proved* in this file from the library, **free of `sorryAx`**
(`#print axioms Work.SSGRoute.stage_local_shrinking` = `[propext, Classical.choice, Quot.sound]`).
Clause (A) is also available standalone as `clause_A_of_prop5Data_exists`; its proof uses

  * the factorization `φ|_{D_A} = φ̄_A ∘ res` (`local_factorisation`),
  * the local class `κ_A ∈ Z²(D_A(K/ℚ), E(m,τ))` (`localKappa`, `localKappa_mem_Z2`),
  * the Shapiro packaging with *naturality in the coefficients* (`shapiro_packaging_natural`, which
    is why the module `T = shapiroT p G ι H` is fixed before the level `m` is chosen),
  * the naturality of the kernel identification (`kerIso_naturality`) and of the section cocycle
    (`kerSuccCocycle_naturality`) to deduce the level-`n` local splitting from the killed class,
  * the splitting criterion (`exists_lift_iff_kerSuccCocycle`) and the conjugacy transfer
    (`local_clause_all_places`, `local_clause_conj_transfer`).

The helpers `level_n_of_cocycle_killed_ssg`, `exists_zpowersHom_of_orderOf_dvd_ssg`,
`kerSuccCocycle_kerIso_mem_Z2_ssg`, `exists_conj_transfer_lift_ssg`,
`involution_clause_conj_transfer_ssg` and `involution_clause_of_mem_fixingSubgroup_ssg` carry the
clause-(B) machinery.  They are declared with the suffix `_ssg` so that they do not clash with the
declarations of the same content in the sibling modules
`stage_local_shrinking_cohomological.lean`, `involution_clause_conj_transfer.lean` and
`involution_clause_of_mem_fixingSubgroup.lean`, which build on this module (the route coded there is
identical).  The older group-theoretic route through the `2`-torsion lifting
(`two_torsion_lift_of_halves`, `involution_clause_of_two_torsion`) is retained above but is *not*
used by the final theorem: the "every anti-fixed element is a `δ`-difference" family it rests on is
refuted at `(8,8)` (`gradedStep_j_ge_two.lean`), whereas the cohomological route needs no such input.
-/

open scoped Pointwise
open scoped TensorProduct

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-! ## `K.fixingSubgroup` versus the kernel of the restriction

Stated in a clean generic context (`IntermediateField` carries several non-definitionally-equal
`Algebra` instance paths — see `Submission/NOTES.md`); instantiate with `@`-application. -/

theorem restrictNormalHom_eq_one_iff_mem_fixingSubgroup {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] (K : IntermediateField F Ω) [Normal F K] (σ : Ω ≃ₐ[F] Ω) :
    (AlgEquiv.restrictNormalHom K σ = 1) ↔ σ ∈ K.fixingSubgroup := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]

/-- **Clause (B) of `stage_local_shrinking`.**  If `φ` is a Scholz solution at level `m` and every
`2`-torsion element of `Γ_n(τ)` whose `G`-component is nontrivial lifts to a `2`-torsion element of
`Γ_n(τ+1)` (`htors`, the statement of `Work.SSGRoute.flowGroup_two_torsion_lift`), then for every
involution `c ∈ G_ℚ` the projection `Γ_n(τ+1) ↠ Γ_n(τ)` splits over `⟨c⟩`, with a splitting that
kills the kernel, for the pushed solution `Ψ = (flowGroupMap Φ) ∘ φ`. -/
theorem involution_clause_of_two_torsion (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j m n : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (htors : ∀ γ : flowGroup p (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot p (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      ∃ l : ↥(Subgroup.zpowers c) →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        (∀ σ : ↥(Subgroup.zpowers c),
          SSGRoute.LiftsFlowAt (l σ) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
        (∀ σ : ↥(Subgroup.zpowers c),
          (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l σ = 1) := by
  intro c hc
  set Ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ with hΨdef
  by_cases hfix : c ∈ K.fixingSubgroup
  · -- `φ c = 1`, hence `Ψ` is trivial on `⟨c⟩` and so is `l`
    have hφc : φ c = 1 := hφ.2.2.1 c hc hfix
    have hΨc : Ψ c = 1 := by simp [hΨdef, hφc]
    refine ⟨1, ?_, ?_⟩
    · intro σ
      have hσ1 : Ψ (σ : SSGRoute.GalQ) = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
        rw [← hk, map_zpow, hΨc, one_zpow]
      rw [hσ1]
      exact (liftsFlowAt_iff_flowGroupSucc p K n i j 1 1).mpr (map_one _)
    · intro σ _
      exact MonoidHom.one_apply σ
  · -- `res c ≠ 1`; use the `2`-torsion lift
    have hres_ne : AlgEquiv.restrictNormalHom K c ≠ 1 := by
      intro h1
      exact hfix ((@restrictNormalHom_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _
        K ‹Normal ℚ K› c).mp h1)
    have hδ : flowQuot p (K ≃ₐ[ℚ] K) n i j (Ψ c) ≠ 1 := by
      intro h1
      apply hres_ne
      rw [hΨdef, MonoidHom.comp_apply, flowQuot_flowGroupMap,
        show flowQuot p (K ≃ₐ[ℚ] K) m i j (φ c) = AlgEquiv.restrictNormalHom K c from
          hφ.1.2.2 c] at h1
      exact h1
    have hΨ2 : Ψ c ^ 2 = 1 := by rw [← map_pow, hc, map_one]
    obtain ⟨y, hylift, hy2⟩ := htors (Ψ c) hΨ2 hδ
    have hsucc : flowGroupSucc p (K ≃ₐ[ℚ] K) n i j y = Ψ c :=
      (liftsFlowAt_iff_flowGroupSucc p K n i j y (Ψ c)).mp hylift
    -- the cyclic hom `⟨c⟩ →* Γ_n(τ+1)`, `c ↦ y`
    have hcne : c ≠ 1 := fun h => hfix (h ▸ K.fixingSubgroup.one_mem)
    have hordc : orderOf c = 2 := orderOf_eq_prime hc hcne
    let π : Multiplicative ℤ →* ↥(Subgroup.zpowers c) :=
      { toFun := fun t => ⟨c ^ (Multiplicative.toAdd t), by
          rw [Subgroup.mem_zpowers_iff]
          exact ⟨Multiplicative.toAdd t, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp [zpow_add] }
    have hπsurj : Function.Surjective π := by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
      refine ⟨Multiplicative.ofAdd k, Subtype.ext ?_⟩
      show c ^ (Multiplicative.toAdd (Multiplicative.ofAdd k)) = (x : SSGRoute.GalQ)
      rw [toAdd_ofAdd]
      exact hk
    have hker : π.ker ≤ (zpowersHom (flowGroup p (K ≃ₐ[ℚ] K) n
        (tauSucc i j).1 (tauSucc i j).2) y).ker := by
      intro t ht
      rw [MonoidHom.mem_ker] at ht ⊢
      have ht' : c ^ (Multiplicative.toAdd t) = 1 := by
        have := congrArg (fun x : ↥(Subgroup.zpowers c) => (x : SSGRoute.GalQ)) ht
        simpa [π] using this
      have h2 : (2 : ℤ) ∣ Multiplicative.toAdd t := by
        have h1 : ((orderOf c : ℕ) : ℤ) ∣ Multiplicative.toAdd t :=
          orderOf_dvd_iff_zpow_eq_one.mpr ht'
        rwa [hordc] at h1
      have hord : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
      have hcast : ((orderOf y : ℕ) : ℤ) ∣ (2 : ℤ) := by exact_mod_cast hord
      rw [zpowersHom_apply]
      exact orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hcast h2)
    let l : ↥(Subgroup.zpowers c) →*
        flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
      (QuotientGroup.lift π.ker (zpowersHom (flowGroup p (K ≃ₐ[ℚ] K) n
          (tauSucc i j).1 (tauSucc i j).2) y) hker).comp
        (QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj).symm.toMonoidHom
    have hcomp : (QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj)
        (QuotientGroup.mk (Multiplicative.ofAdd (1 : ℤ)))
          = ⟨c, Subgroup.mem_zpowers c⟩ := by
      show (QuotientGroup.kerLift π) (QuotientGroup.mk (Multiplicative.ofAdd (1 : ℤ))) = _
      rw [QuotientGroup.kerLift_mk]
      apply Subtype.ext
      show c ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ))) = c
      rw [toAdd_ofAdd, zpow_one]
    have hsymm : (QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj).symm
        ⟨c, Subgroup.mem_zpowers c⟩ = QuotientGroup.mk (Multiplicative.ofAdd (1 : ℤ)) := by
      rw [← hcomp, MulEquiv.symm_apply_apply]
    have hly : l ⟨c, Subgroup.mem_zpowers c⟩ = y := by
      show (QuotientGroup.lift π.ker (zpowersHom (flowGroup p (K ≃ₐ[ℚ] K) n
          (tauSucc i j).1 (tauSucc i j).2) y) hker)
          ((QuotientGroup.quotientKerEquivOfSurjective (φ := π) hπsurj).symm
            ⟨c, Subgroup.mem_zpowers c⟩) = y
      rw [hsymm, QuotientGroup.lift_mk', zpowersHom_apply, toAdd_ofAdd, zpow_one]
    refine ⟨l, ?_, ?_⟩
    · intro σ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hΨσ : Ψ (σ : SSGRoute.GalQ) = (Ψ c) ^ k := by
        rw [show (σ : SSGRoute.GalQ) = c ^ k from hk.symm]
        exact map_zpow Ψ c k
      have hlσ : l σ = y ^ k := by rw [hσ, map_zpow, hly]
      rw [hΨσ, hlσ]
      exact (liftsFlowAt_iff_flowGroupSucc p K n i j (y ^ k) ((Ψ c) ^ k)).mpr
        ((map_zpow (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) y k).trans (by rw [hsucc]))
    · intro σ hσ1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hΨσ : Ψ (σ : SSGRoute.GalQ) = (Ψ c) ^ k := by
        rw [show (σ : SSGRoute.GalQ) = c ^ k from hk.symm]
        exact map_zpow Ψ c k
      have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hlσ : l σ = y ^ k := by rw [hσ, map_zpow, hly]
      rw [hlσ]
      have hk1 : (Ψ c) ^ k = 1 := by
        rw [← hσ1, hΨσ]
      have hdvd : ((orderOf (Ψ c) : ℕ) : ℤ) ∣ k := by
        apply orderOf_dvd_iff_zpow_eq_one.mpr
        exact hk1
      have hΨord : orderOf (Ψ c) = 2 := by
        refine orderOf_eq_prime hΨ2 ?_
        intro h0
        exact hδ (by rw [h0, map_one])
      rw [hΨord] at hdvd
      have hord : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
      have hcast : ((orderOf y : ℕ) : ℤ) ∣ (2 : ℤ) := by exact_mod_cast hord
      exact orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hcast hdvd)

/-! ## Recovered lemmas (lost to a concurrent revert of this file; re-added verbatim) -/

theorem cocycleIdentity_congr {H G M : Type*} [Group H] [Group G] [AddCommGroup M]
    [DistribMulAction G M] {f g : H →* G} (hfg : ∀ h, f h = g h) (c : H × H → M) :
    (∀ a b e : H, c (a * b, e) + c (a, b) = f a • c (b, e) + c (a, b * e)) ↔
      (∀ a b e : H, c (a * b, e) + c (a, b) = g a • c (b, e) + c (a, b * e)) := by
  constructor
  · intro h a b e
    rw [← hfg a]
    exact h a b e
  · intro h a b e
    rw [hfg a]
    exact h a b e

theorem flowGroupSucc_ker_comm (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    ∀ a b : ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker, a * b = b * a :=
  fun a b => (flowGroupSucc_ker_isMulCommutative p G m i j).is_comm.comm a b

theorem two_torsion_lift_of_halves (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (htwo : ∀ γ : flowGroup 2 (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot 2 (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1) :
    ∀ γ : flowGroup p (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot p (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  intro γ hγ hδ
  by_cases hp : p = 2
  · subst hp
    exact htwo γ hγ hδ
  · exact two_torsion_lift_odd p hp K n i j hj hji γ hγ hδ

theorem local_clause_of_splitting (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j n : ℕ)
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (A : ValuationSubring SSGRoute.QBar)
    (lam : ↥((SSGRoute.decomp ℚ A).map ρ) →*
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hlam : ∀ h : ↥((SSGRoute.decomp ℚ A).map ρ),
      flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (lam h) = (h : flowGroup p (K ≃ₐ[ℚ] K) n i j)) :
    ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) n
        (tauSucc i j).1 (tauSucc i j).2,
      (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (ρ σ)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), ρ σ = 1 → l σ = 1) := by
  refine ⟨lam.comp (MonoidHom.codRestrict (ρ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A)))
    ((SSGRoute.decomp ℚ A).map ρ) fun σ => Subgroup.mem_map_of_mem ρ σ.2), ?_, ?_⟩
  · intro σ
    exact (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr
      (hlam ⟨ρ σ, Subgroup.mem_map_of_mem ρ σ.2⟩)
  · intro σ hσ
    have hmk : (⟨ρ σ, Subgroup.mem_map_of_mem ρ σ.2⟩ : ↥((SSGRoute.decomp ℚ A).map ρ)) = 1 :=
      Subtype.ext hσ
    show lam ⟨ρ σ, _⟩ = 1
    rw [hmk, map_one]

theorem local_clause_all_places (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j n : ℕ)
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hS : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨ SSGRoute.IsRamifiedIn ℚ K B) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (hrep : ∀ A ∈ S, ∃ l : ↥(SSGRoute.decomp ℚ A) →*
        flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l x) (ρ x)) ∧
      (∀ x : ↥(SSGRoute.decomp ℚ A), ρ x = 1 → l x = 1)) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →*
        flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l x) (ρ x)) ∧
      (∀ x : ↥(SSGRoute.decomp ℚ A), ρ x = 1 → l x = 1) := by
  intro A hA
  obtain ⟨hfin, hram⟩ := hA
  obtain ⟨A₀, hA₀S, hconj⟩ := hS A hfin hram
  obtain ⟨σ, hσ⟩ := hconj
  have hAB : ∀ x : SSGRoute.QBar, x ∈ A ↔ ∃ y : SSGRoute.QBar, y ∈ A₀ ∧ x = σ y := by
    intro x
    rw [← hσ, ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, h.symm⟩
  exact local_clause_conj_transfer p K i j n ρ A₀ A σ hAB (hrep A₀ hA₀S)

theorem exists_representatives (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] :
    ∃ S : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B) ∧
      ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (SSGRoute.IsRamifiedIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B := by
  exact @Work.SSGRoute.ramifiedPlaces_finite p ‹Fact p.Prime› K ‹FiniteDimensional ℚ K›
    (IsGalois.mk : IsGalois ℚ K)

/-- Step 2 of the chase: the factored local map `φA` on `H_A`, chosen from
`Work.SSGRoute.local_factorisation`. -/
noncomputable def localPhi (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A) :
    ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) →*
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j :=
  Classical.choose (local_factorisation p K i j m φ hφ A hA)

/-- The two defining properties of `localPhi` (step 2). -/
theorem localPhi_spec (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A) :
    (∀ σ : ↥(SSGRoute.decomp ℚ A),
        localPhi p K i j m φ hφ A hA
          ⟨AlgEquiv.restrictNormalHom K (σ : SSGRoute.GalQ),
            Subgroup.mem_map_of_mem (AlgEquiv.restrictNormalHom K) σ.2⟩
          = φ (σ : SSGRoute.GalQ)) ∧
      (∀ h : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)),
        Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m i j
          (localPhi p K i j m φ hφ A hA h) = (h : K ≃ₐ[ℚ] K)) :=
  Classical.choose_spec (local_factorisation p K i j m φ hφ A hA)

/-- Step 3, first piece: the equivariant identification of the kernel of `flowGroupSucc` with the
graded piece `E p G m i j`.  It is taken as the explicit inverse of the canonical identification
`succKerIso : E(m,τ) ≃* ker (flowGroupSucc p G m i j)` (first isomorphism theorem); using the
explicit identification (rather than the choice behind `exists_kerSuccAddEquiv_equivariant`) is what
makes its *naturality in the rank* available below. -/
noncomputable def kerIso (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m : ℕ) :
    Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker ≃+
      Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j :=
  (succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm

/-- `kerIso` computed on `Additive.ofMul`. -/
theorem kerIso_ofMul (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m : ℕ)
    (x : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker) :
    kerIso p K i j m (Additive.ofMul x)
      = Additive.ofMul ((succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x) := rfl

/-- `kerIso` is equivariant for the conjugation action of `G` on the kernel (through the canonical
lifts `⟨1,g⟩`) and the graded action on `E(m,τ)`. -/
theorem kerIso_equivariant_ofMul (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m : ℕ)
    (g : K ≃ₐ[ℚ] K) (x : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker) :
    kerIso p K i j m (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
        (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
        (SemidirectProduct.mk 1 g : flowGroup p (K ≃ₐ[ℚ] K) m
          (tauSucc i j).1 (tauSucc i j).2) x))
      = g • kerIso p K i j m (Additive.ofMul x) := by
  rw [kerIso_ofMul, kerIso_ofMul]
  have h := succKerIso_smul p (K ≃ₐ[ℚ] K) m i j g
    ((succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (succKerIso p (K ≃ₐ[ℚ] K) m i j).symm
      (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
        (SemidirectProduct.mk 1 g : flowGroup p (K ≃ₐ[ℚ] K) m
          (tauSucc i j).1 (tauSucc i j).2) x)
      = g • (succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x := by
    have h3 := congrArg (succKerIso p (K ≃ₐ[ℚ] K) m i j).symm h
    rw [MulEquiv.symm_apply_apply] at h3
    exact h3.symm
  rw [h2]
  exact (smul_additive_apply p (K ≃ₐ[ℚ] K) m i j g _).symm

/-- `kerIso` is equivariant (additive form, the shape used by `exists_localCocycle`). -/
theorem kerIso_equivariant (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m : ℕ) :
    ∀ (g : K ≃ₐ[ℚ] K) (x : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker),
      kerIso p K i j m (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
        (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
        (SemidirectProduct.mk 1 g : flowGroup p (K ≃ₐ[ℚ] K) m
          (tauSucc i j).1 (tauSucc i j).2) (Additive.toMul x)))
        = g • kerIso p K i j m x :=
  fun g x => kerIso_equivariant_ofMul p K i j m g (Additive.toMul x)

/-- **Naturality of the kernel identification in the rank**: `kerIso` intertwines the map induced by
an operator map on the kernels with the map induced on the graded pieces. -/
theorem kerIso_naturality (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m n : ℕ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (x : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker) :
    kerIso p K i j n (Additive.ofMul (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ x))
      = gradedMapLin p Φ.toHom Φ.surjective i j (kerIso p K i j m (Additive.ofMul x)) := by
  have h := succKerIso_naturality p (K ≃ₐ[ℚ] K) i j Φ
    ((succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (succKerIso p (K ≃ₐ[ℚ] K) n i j).symm
      (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ x)
      = gradedMapMul p Φ.toHom Φ.surjective i j
          ((succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x) := by
    have h3 := congrArg (succKerIso p (K ≃ₐ[ℚ] K) n i j).symm h
    rw [MulEquiv.symm_apply_apply] at h3
    exact h3
  rw [kerIso_ofMul, kerIso_ofMul, gradedMapLin_apply]
  show Additive.ofMul ((succKerIso p (K ≃ₐ[ℚ] K) n i j).symm
      (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ x))
    = Additive.ofMul (gradedMapMul p Φ.toHom Φ.surjective i j
        ((succKerIso p (K ≃ₐ[ℚ] K) m i j).symm x))
  rw [h2]

/-- The action of an arbitrary element of `Γ(τ+1)` on the kernel, computed through `kerIso`: it is
the graded action of its `G`-component. -/
theorem kerIso_conjKernelMul (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) (i j m : ℕ)
    (y : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (x : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker) :
    kerIso p K i j m (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
        (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j) y x))
      = (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j y).right • kerIso p K i j m (Additive.ofMul x) := by
  have hy : (⟨y.left, y.right⟩ : flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2) = y := rfl
  rw [← hy, kerSucc_conj_eq_mk_one p (K ≃ₐ[ℚ] K) i j m y.left y.right x]
  have hright : (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (⟨y.left, y.right⟩ : flowGroup p
      (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)).right = y.right := rfl
  rw [hright]
  exact kerIso_equivariant_ofMul p K i j m y.right x

/-! ## Transport of coboundaries

Two elementary facts used by the assembly: an equivariant additive bijection of coefficient modules
carries `2`-coboundaries to `2`-coboundaries (and back), and the restriction of a `2`-coboundary
to a subgroup is a `2`-coboundary. -/

/-- An equivariant additive bijection carries `2`-coboundaries to `2`-coboundaries, and back. -/
theorem mem_B2_mapCochain2_iff {H : Type*} [Group H] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] [DistribMulAction H A] [DistribMulAction H B]
    (φ : A →+ B) (hφ : ∀ (h : H) (a : A), φ (h • a) = h • φ a)
    (hbij : Function.Bijective φ) (c : H × H → A) :
    c ∈ Work.GroupCohomology.B2 H A ↔
      Work.GroupCohomology.mapCochain2 H φ c ∈ Work.GroupCohomology.B2 H B := by
  constructor
  · exact Work.GroupCohomology.mapCochain2_mem_B2 H φ hφ
  · intro hc
    rw [Work.GroupCohomology.mem_B2_iff] at hc ⊢
    obtain ⟨f, hf⟩ := hc
    let e : A ≃+ B := AddEquiv.ofBijective φ hbij
    let ψ : B →+ A := e.symm.toAddMonoidHom
    have hψφ : ∀ b : B, φ (ψ b) = b := fun b => e.apply_symm_apply b
    have hφψ : ∀ a : A, ψ (φ a) = a := fun a => e.symm_apply_apply a
    have hψeq : ∀ (h : H) (b : B), ψ (h • b) = h • ψ b := by
      intro h b
      apply hbij.1
      rw [hφ, hψφ, hψφ]
    refine ⟨ψ ∘ f, ?_⟩
    funext q
    obtain ⟨σ, τ⟩ := q
    simp only [Work.GroupCohomology.d1_apply, Function.comp_apply]
    have hh := congrFun hf (σ, τ)
    simp only [Work.GroupCohomology.d1_apply, Work.GroupCohomology.mapCochain2_apply] at hh
    rw [← hψeq σ (f τ), ← hφψ (c (σ, τ)), ← hh]
    simp only [map_add, map_sub]

/-- The restriction of a `2`-coboundary to a subgroup is a `2`-coboundary (for the coefficient
module structure induced by the inclusion). -/
theorem mem_B2_restrict {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    (Hc : Subgroup G) [DistribMulAction ↥Hc A]
    (hact : ∀ (σ : ↥Hc) (a : A), σ • a = (σ : G) • a)
    (c : G × G → A) (hc : c ∈ Work.GroupCohomology.B2 G A) :
    (fun q : ↥Hc × ↥Hc => c (q.1, q.2)) ∈ Work.GroupCohomology.B2 ↥Hc A := by
  rw [Work.GroupCohomology.mem_B2_iff] at hc ⊢
  obtain ⟨f, hf⟩ := hc
  refine ⟨fun σ : ↥Hc => f σ, ?_⟩
  funext q
  obtain ⟨σ, τ⟩ := q
  simp only [Work.GroupCohomology.d1_apply]
  rw [hact σ (f τ), ← hf]
  rfl

/-- Step 3, second piece: the local class `κ_A`, the transport of the section cocycle of
`flowGroupSucc` along the factored local map `localPhi` and the kernel identification `kerIso`. -/
noncomputable def localKappa (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A) :
    ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) ×
      ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)) →
        Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j :=
  fun x => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j
    (localPhi p K i j m φ hφ A hA)
    (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) x.1 x.2)

/-- Step 3, conclusion: `κ_A` is a `2`-cocycle.  One application of `exists_localCocycle` to
`localPhi` and the lift conjunct of `localPhi_spec`. -/
theorem localKappa_mem_Z2 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A) :
    (letI : DistribMulAction ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K))
        (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j) :=
      DistribMulAction.compHom _ (Subgroup.subtype _)
     localKappa p K i j m φ hφ A hA
       ∈ Work.GroupCohomology.Z2 _
         (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)) :=
  exists_localCocycle p K i j m A (localPhi p K i j m φ hφ A hA)
    (localPhi_spec p K i j m φ hφ A hA).2
    (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j)
    (kerIso p K i j m) (kerIso_equivariant p K i j m)

/-- The vanishing of the class of a `2`-cocycle under an operator map is exactly the statement that
the transported cocycle is a `2`-coboundary. -/
theorem h2Map_eq_zero_iff_B2 (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j m n : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (Φ : OperatorMap G m n)
    (c : Work.GroupCohomology.Z2 G (E p G m i j ⊗[ZMod p] T))
    (h : Φ.h2Map p G T (Work.GroupCohomology.H2π G (E p G m i j ⊗[ZMod p] T) c) = 0) :
    Work.GroupCohomology.mapCochain2 G ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
      (c : G × G → E p G m i j ⊗[ZMod p] T)
      ∈ Work.GroupCohomology.B2 G (E p G n i j ⊗[ZMod p] T) := by
  have hmain : Φ.h2Map p G T (Work.GroupCohomology.H2π G (E p G m i j ⊗[ZMod p] T) c)
      = Work.GroupCohomology.H2π G (E p G n i j ⊗[ZMod p] T)
          (Work.GroupCohomology.mapZ2 G ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
            (fun g z => rTensor_equiv p (G := G)
              (f := gradedMapLin p Φ.toHom Φ.surjective i j)
              (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
              g z) c) := by
    rw [show Φ.h2Map p G T (Work.GroupCohomology.H2π G (E p G m i j ⊗[ZMod p] T) c)
        = Work.GroupCohomology.mapH2 G
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
            (fun g z => rTensor_equiv p (G := G)
              (f := gradedMapLin p Φ.toHom Φ.surjective i j)
              (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
              g z) (Work.GroupCohomology.H2π G (E p G m i j ⊗[ZMod p] T) c) from rfl]
    exact Work.GroupCohomology.mapH2_H2π G _ _ c
  have h1 : Work.GroupCohomology.H2π G (E p G n i j ⊗[ZMod p] T)
      (Work.GroupCohomology.mapZ2 G ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
        (fun g z => rTensor_equiv p (G := G)
          (f := gradedMapLin p Φ.toHom Φ.surjective i j)
          (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
          g z) c) = 0 := by
    rw [← hmain]
    exact h
  rw [Work.GroupCohomology.H2pi_eq_zero_iff] at h1
  exact h1

theorem local_level_n_of_class_killed (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j m n : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[ℚ] K) T]
    [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ev : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) m i j)
    (C : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) → E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T)
    (hCval : ∀ h h' : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)),
      ev (C ((h : K ≃ₐ[ℚ] K), (h' : K ≃ₐ[ℚ] K)))
        = localKappa p K i j m φ hφ A hA (h, h'))
    (hkill : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) C
      ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T))
    (hev : ∀ (h : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)))
        (z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T),
      ev ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • ev z)
    (evθ : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j)
    (hevθ : ∀ (h : ↥((SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)))
        (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
      evθ ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • evθ z)
    (hnat : ∀ z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T,
      evθ ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T z)
        = gradedMapLin p Φ.toHom Φ.surjective i j (ev z)) :
    ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) n
        (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥(SSGRoute.decomp ℚ A),
        SSGRoute.LiftsFlowAt (l x) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x)) ∧
      (∀ x : ↥(SSGRoute.decomp ℚ A),
        (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x) = 1 → l x = 1) := by
  classical
  let Δ : Subgroup (K ≃ₐ[ℚ] K) := (SSGRoute.decomp ℚ A).map (AlgEquiv.restrictNormalHom K)
  let θ : E p (K ≃ₐ[ℚ] K) m i j →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j :=
    gradedMapLin p Φ.toHom Φ.surjective i j
  let ρ : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) m i j := localPhi p K i j m φ hφ A hA
  let ρn : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ
  let κ : ↥Δ × ↥Δ → E p (K ≃ₐ[ℚ] K) m i j := localKappa p K i j m φ hφ A hA
  let s : flowGroup p (K ≃ₐ[ℚ] K) m i j →
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) m i j
  let s' : flowGroup p (K ≃ₐ[ℚ] K) n i j →
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) n i j
  have hs : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j
  have hs' : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j
  have h1s : s 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j
  have h1s' : s' 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) n i j
  have hρ : ∀ σ : ↥Δ, ρn σ = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (ρ σ) := fun σ => rfl
  -- the flow quotient of `ρn` is the subgroup inclusion
  have hflow : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ) = (σ : K ≃ₐ[ℚ] K) := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) n i j
      (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (localPhi p K i j m φ hφ A hA σ)) = (σ : K ≃ₐ[ℚ] K)
    rw [flowQuot_flowGroupMap]
    exact (localPhi_spec p K i j m φ hφ A hA).2 σ
  -- the Δ-module structures on the coefficient modules (via the subgroup inclusion)
  letI instT : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instTn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEm : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  -- (A) `θ ∘ κ` is a `2`-coboundary on `Δ`
  have hAB2 : (fun q : ↥Δ × ↥Δ => θ (κ q))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hres : (fun q : ↥Δ × ↥Δ => θ.rTensor T (C (q.1, q.2)))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
      mem_B2_restrict (Hc := Δ) (hact := fun σ z => rfl) (c := fun q : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) => θ.rTensor T (C q)) hkill
    let evθa : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →+ E p (K ≃ₐ[ℚ] K) n i j := evθ
    have hevθ' : ∀ (σ : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
        evθa (σ • z) = σ • evθa z := fun σ z => hevθ σ z
    have hpush : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
      Work.GroupCohomology.mapCochain2_mem_B2 ↥Δ evθa hevθ' hres
    have hfun : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        = fun q : ↥Δ × ↥Δ => θ (κ q) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      rw [hnat (C ((σ : K ≃ₐ[ℚ] K), (τ : K ≃ₐ[ℚ] K))), hCval σ τ]
    rw [hfun] at hpush
    exact hpush
  -- (B) the naturality of the section cocycle: the level-`n` cocycle over `Δ` is cohomologous to
  -- `θ ∘ κ`
  let δ : ↥Δ → E p (K ≃ₐ[ℚ] K) n i j := fun σ => kerIso p K i j n (Additive.ofMul
    (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρ s s' hs hs' σ))
  have hker : (fun q : ↥Δ × ↥Δ => kerIso p K i j n
      (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hd1 : Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := ⟨δ, rfl⟩
    have hdiff := sub_mem hAB2 hd1
    have heq : (fun q : ↥Δ × ↥Δ => θ (κ q))
        - Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        = fun q : ↥Δ × ↥Δ => kerIso p K i j n
            (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      have hnat' := kerSuccCocycle_naturality p (K ≃ₐ[ℚ] K) m n i j Φ ρ ρn hρ s hs s' hs' σ τ
      have h1 := congrArg (kerIso p K i j n) hnat'
      simp only [map_add, map_sub] at h1
      show θ (κ (σ, τ)) - (σ • δ τ - δ (σ * τ) + δ σ)
        = kerIso p K i j n (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' σ τ)
      rw [h1]
      -- simplify the three `kerIso` images of the correction cochain and the first term
      have hκeq : kerIso p K i j n (Additive.ofMul
            (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ
              (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)))
          = θ (κ (σ, τ)) := by
        rw [kerIso_naturality p K i j m n Φ (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)]
        show gradedMapLin p Φ.toHom Φ.surjective i j
            (kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ))
          = gradedMapLin p Φ.toHom Φ.surjective i j (κ (σ, τ))
        rfl
      have hconj : kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
            (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn σ))
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρ s s' hs hs' τ)))
          = σ • δ τ := by
        rw [kerIso_conjKernelMul]
        show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn σ))).right • δ τ = σ • δ τ
        rw [hs' (ρn σ)]
        show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ)) • δ τ = σ • δ τ
        rw [hflow σ]
        show (σ : K ≃ₐ[ℚ] K) • δ τ = (σ : K ≃ₐ[ℚ] K) • δ τ
        rfl
      have hlast : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρ s s' hs hs' (σ * τ))) = δ (σ * τ) := rfl
      have hlast2 : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρ s s' hs hs' σ)) = δ σ := rfl
      rw [hκeq, hconj, hlast, hlast2]
    rw [heq] at hdiff
    exact hdiff
  -- (C) transfer to the kernel coefficients and apply the splitting criterion
  letI : CommGroup ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) with
      mul_comm := flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j }
  letI : DistribMulAction (flowGroup p (K ≃ₐ[ℚ] K) n i j)
      (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)
  letI : DistribMulAction ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    DistribMulAction.compHom _ ρn
  have hkerK : (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)
      ∈ Work.GroupCohomology.B2 ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) := by
    have hφeq : ∀ (h : ↥Δ) (a : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker),
        kerIso p K i j n (h • a) = h • kerIso p K i j n a := by
      intro h a
      show kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn h)) (Additive.toMul a)))
        = (h : K ≃ₐ[ℚ] K) • kerIso p K i j n (Additive.ofMul (Additive.toMul a))
      rw [kerIso_conjKernelMul]
      show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn h))).right
          • kerIso p K i j n (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hs' (ρn h)]
      show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn h)) • kerIso p K i j n
          (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hflow h]
    have hbij : Function.Bijective (kerIso p K i j n).toAddMonoidHom :=
      (kerIso p K i j n).bijective
    exact (mem_B2_mapCochain2_iff (kerIso p K i j n).toAddMonoidHom hφeq hbij
      (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)).mpr hker
  -- the splitting criterion gives the lift over `Δ`
  obtain ⟨ψ, hψ⟩ := (exists_lift_iff_kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)).mpr hkerK
  -- the restriction `D_A →* D_A(K/ℚ)` and `l := ψ ∘ res`
  let resD : ↥(SSGRoute.decomp ℚ A) →* ↥Δ :=
    { toFun := fun x => ⟨(AlgEquiv.restrictNormalHom K) (x : SSGRoute.GalQ),
        Subgroup.mem_map_of_mem (AlgEquiv.restrictNormalHom K) x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp }
  have hresD : ∀ x : ↥(SSGRoute.decomp ℚ A),
      resD x = ⟨(AlgEquiv.restrictNormalHom K) (x : SSGRoute.GalQ),
        Subgroup.mem_map_of_mem (AlgEquiv.restrictNormalHom K) x.2⟩ := fun x => rfl
  refine ⟨ψ.comp resD, ?_, ?_⟩
  · intro x
    refine (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr ?_
    show flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (ψ (resD x)) = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φ x)
    have h2 := DFunLike.congr_fun hψ (resD x)
    simp only [MonoidHom.comp_apply] at h2
    rw [h2]
    show flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (localPhi p K i j m φ hφ A hA (resD x))
      = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φ x)
    rw [hresD x, (localPhi_spec p K i j m φ hφ A hA).1 x]
  · intro x hx
    have hres_eq : flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (localPhi p K i j m φ hφ A hA (resD x)) = 1 := by
      rw [hresD x, (localPhi_spec p K i j m φ hφ A hA).1 x]
      exact hx
    have hy1 : resD x = 1 := by
      apply Subtype.ext
      have h := hflow (resD x)
      have hρn1 : ρn (resD x) = 1 := by
        show flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (localPhi p K i j m φ hφ A hA (resD x)) = 1
        exact hres_eq
      rw [hρn1] at h
      simpa using h.symm
    show ψ (resD x) = 1
    rw [hy1, map_one]



theorem clause_A_of_prop5Data_exists (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n)
    (D : Work.CohomologicalShrinking.Prop5Data p (K ≃ₐ[ℚ] K) i j) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j,
        SSGRoute.IsScholzSolution p K m i j φ →
        ∃ Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n,
          ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
            ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 →
                  l σ = 1) := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  obtain ⟨S, hSfin, hSdisj, hShit⟩ := exists_representatives (p := p) K
  let S' : Finset (ValuationSubring SSGRoute.QBar) := S.filter (fun A => SSGRoute.IsT1Place p K A)
  let Hsub : ↥S' → Subgroup (K ≃ₐ[ℚ] K) :=
    fun A => (SSGRoute.decomp ℚ A.1).map (AlgEquiv.restrictNormalHom K)
  let T : Type _ := shapiroT p (K ≃ₐ[ℚ] K) ↥S' Hsub
  obtain ⟨m₀, hm₀n, hm₀⟩ := exists_shrinking_H2_tate p (K ≃ₐ[ℚ] K) hj D T (Fintype.card ↥S') hn
  refine ⟨m₀, hm₀n, ?_⟩
  intro m hm φ hφ
  let κ : ∀ A : ↥S', ↥(Hsub A) × ↥(Hsub A) → E p (K ≃ₐ[ℚ] K) m i j :=
    fun A => localKappa p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
  have hκ : ∀ A : ↥S', (letI : DistribMulAction ↥(Hsub A) (E p (K ≃ₐ[ℚ] K) m i j) :=
      DistribMulAction.compHom _ (Subgroup.subtype _)
      κ A ∈ Work.GroupCohomology.Z2 (↥(Hsub A)) (E p (K ≃ₐ[ℚ] K) m i j)) :=
    fun A => localKappa_mem_Z2 p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
  obtain ⟨ev, hev, C, hC, hCval, hnat⟩ :=
    shapiro_packaging_natural p (K ≃ₐ[ℚ] K) ↥S' Hsub (E p (K ≃ₐ[ℚ] K) m i j) κ hκ
  let clsA : ↥S' → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
      (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
    fun A => Work.GroupCohomology.H2π (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T)
      ⟨C A, hC A⟩
  let cls : Fin (Fintype.card ↥S') → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
      (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
    fun k => clsA ((Fintype.equivFin ↥S').symm k)
  obtain ⟨Φ, hΦ⟩ := hm₀ m hm cls
  refine ⟨Φ, ?_⟩
  have hrep : ∀ A ∈ S', ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥(SSGRoute.decomp ℚ A),
        SSGRoute.LiftsFlowAt (l x) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x)) ∧
      (∀ x : ↥(SSGRoute.decomp ℚ A),
        (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x) = 1 → l x = 1) := by
    intro A hAS'
    have hA : SSGRoute.IsT1Place p K A := (Finset.mem_filter.mp hAS').2
    have h0 : Φ.h2Map p (K ≃ₐ[ℚ] K) T (clsA ⟨A, hAS'⟩) = 0 := by
      have := hΦ (Fintype.equivFin ↥S' ⟨A, hAS'⟩)
      rwa [show cls (Fintype.equivFin ↥S' ⟨A, hAS'⟩) = clsA ⟨A, hAS'⟩ from by
        simp only [cls, Equiv.symm_apply_apply]] at this
    have hkill := h2Map_eq_zero_iff_B2 (p := p) (G := K ≃ₐ[ℚ] K) (i := i) (j := j)
      (m := m) (n := n) (T := T) Φ ⟨C ⟨A, hAS'⟩, hC ⟨A, hAS'⟩⟩ h0
    obtain ⟨evθ, hevθ, hnatval⟩ := hnat (E p (K ≃ₐ[ℚ] K) n i j)
      (gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
    exact local_level_n_of_class_killed p K i j m n T A hA φ hφ Φ (ev ⟨A, hAS'⟩) (C ⟨A, hAS'⟩)
      (fun h h' => hCval ⟨A, hAS'⟩ h h') hkill (hev ⟨A, hAS'⟩) (evθ ⟨A, hAS'⟩) (hevθ ⟨A, hAS'⟩)
      (fun z => hnatval ⟨A, hAS'⟩ z)
  refine local_clause_all_places p K i j n ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) S' ?_ hrep
  intro B hBfin hBram
  obtain ⟨A, hAS, hconj⟩ := hShit B hBfin hBram.symm
  refine ⟨A, Finset.mem_filter.mpr ⟨hAS, ?_⟩, hconj⟩
  exact isT1Place_of_isConjPlace p K (A₀ := B) (A := A)
    (isConjPlace_symm (k := ℚ) hconj) ⟨hBfin, hBram⟩


/-! ## Auxiliary lemmas for the cohomological assembly of clause (B)

Clause (B) is obtained by the *same* Shapiro/Proposition-6 shrinking as clause (A), with the chosen
involution's cyclic subgroup added to the family of local subgroups.  (The group-theoretic route
through `two_torsion_lift_two` is avoided: the "every anti-fixed element is a `δ`-difference"
family behind it is refuted at `(8,8)`.)  These auxiliary lemmas are declared with the suffix
`_ssg` so that they do not clash with the declarations of the same content in
`Submission/Work/SSGRoute/stage_local_shrinking_cohomological.lean`,
`involution_clause_of_mem_fixingSubgroup.lean` and `involution_clause_conj_transfer.lean`, which
build on this module. -/

/-- **The level-`n` splitting criterion over an arbitrary subgroup.**  This is
`Work.SSGRoute.local_level_n_of_class_killed` with the place `A` (and `localPhi`, `localKappa`)
replaced by an arbitrary subgroup `Δ ≤ Gal(K/ℚ)` and a homomorphism `ρ` lifting the inclusion. -/
theorem level_n_of_cocycle_killed_ssg (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j m n : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[ℚ] K) T]
    [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    (Δ : Subgroup (K ≃ₐ[ℚ] K))
    (ρ : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hρ : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K))
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ev : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) m i j)
    (C : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) → E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T)
    (hCval : ∀ h h' : ↥Δ,
      ev (C ((h : K ≃ₐ[ℚ] K), (h' : K ≃ₐ[ℚ] K)))
        = kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
            (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
            (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) h h'))
    (hkill : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) C
      ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T))
    (hev : ∀ (h : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T),
      ev ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • ev z)
    (evθ : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j)
    (hevθ : ∀ (h : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
      evθ ((h : K ≃ₐ[ℚ] K) • z) = (h : K ≃ₐ[ℚ] K) • evθ z)
    (hnat : ∀ z : E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T,
      evθ ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T z)
        = gradedMapLin p Φ.toHom Φ.surjective i j (ev z)) :
    ∃ l : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      (∀ x : ↥Δ, SSGRoute.LiftsFlowAt (l x)
        (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ) x)) ∧
      (∀ x : ↥Δ, (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ) x) = 1 → l x = 1) := by
  classical
  let θ : E p (K ≃ₐ[ℚ] K) m i j →ₗ[ZMod p] E p (K ≃ₐ[ℚ] K) n i j :=
    gradedMapLin p Φ.toHom Φ.surjective i j
  let ρn : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ
  let s : flowGroup p (K ≃ₐ[ℚ] K) m i j →
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) m i j
  let s' : flowGroup p (K ≃ₐ[ℚ] K) n i j →
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    flowGroupSection p (K ≃ₐ[ℚ] K) n i j
  have hs : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j
  have hs' : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j
  have h1s : s 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j
  have h1s' : s' 1 = 1 := flowGroupSection_one p (K ≃ₐ[ℚ] K) n i j
  let κ : ↥Δ × ↥Δ → E p (K ≃ₐ[ℚ] K) m i j :=
    fun q => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ s hs q.1 q.2)
  have hρn : ∀ σ : ↥Δ, ρn σ = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (ρ σ) := fun σ => rfl
  -- the flow quotient of `ρn` is the subgroup inclusion
  have hflow : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ) = (σ : K ≃ₐ[ℚ] K) := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) n i j
      (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (ρ σ)) = (σ : K ≃ₐ[ℚ] K)
    rw [flowQuot_flowGroupMap]
    exact hρ σ
  -- the Δ-module structures on the coefficient modules (via the subgroup inclusion)
  letI instT : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instTn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEm : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  letI instEn : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  -- (A) `θ ∘ κ` is a `2`-coboundary on `Δ`
  have hAB2 : (fun q : ↥Δ × ↥Δ => θ (κ q))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hres : (fun q : ↥Δ × ↥Δ => θ.rTensor T (C (q.1, q.2)))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
      mem_B2_restrict (Hc := Δ) (hact := fun σ z => rfl) (c := fun q : (K ≃ₐ[ℚ] K) × (K ≃ₐ[ℚ] K) => θ.rTensor T (C q)) hkill
    let evθa : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T →+ E p (K ≃ₐ[ℚ] K) n i j := evθ
    have hevθ' : ∀ (σ : ↥Δ) (z : E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T),
        evθa (σ • z) = σ • evθa z := fun σ z => hevθ σ z
    have hpush : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) :=
      Work.GroupCohomology.mapCochain2_mem_B2 ↥Δ evθa hevθ' hres
    have hfun : (fun q : ↥Δ × ↥Δ => evθ (θ.rTensor T (C (q.1, q.2))))
        = fun q : ↥Δ × ↥Δ => θ (κ q) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      rw [hnat (C ((σ : K ≃ₐ[ℚ] K), (τ : K ≃ₐ[ℚ] K))), hCval σ τ]
    rw [hfun] at hpush
    exact hpush
  -- (B) the naturality of the section cocycle: the level-`n` cocycle over `Δ` is cohomologous to
  -- `θ ∘ κ`
  let δ : ↥Δ → E p (K ≃ₐ[ℚ] K) n i j := fun σ => kerIso p K i j n (Additive.ofMul
    (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' σ))
  have hker : (fun q : ↥Δ × ↥Δ => kerIso p K i j n
      (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2))
      ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := by
    have hd1 : Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        ∈ Work.GroupCohomology.B2 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) := ⟨δ, rfl⟩
    have hdiff := sub_mem hAB2 hd1
    have heq : (fun q : ↥Δ × ↥Δ => θ (κ q))
        - Work.GroupCohomology.d1 ↥Δ (E p (K ≃ₐ[ℚ] K) n i j) δ
        = fun q : ↥Δ × ↥Δ => kerIso p K i j n
            (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2) := by
      funext q
      obtain ⟨σ, τ⟩ := q
      have hnat' := kerSuccCocycle_naturality p (K ≃ₐ[ℚ] K) m n i j Φ ρ ρn hρn s hs s' hs' σ τ
      have h1 := congrArg (kerIso p K i j n) hnat'
      simp only [map_add, map_sub] at h1
      show θ (κ (σ, τ)) - (σ • δ τ - δ (σ * τ) + δ σ)
        = kerIso p K i j n (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' σ τ)
      rw [h1]
      -- simplify the three `kerIso` images of the correction cochain and the first term
      have hκeq : kerIso p K i j n (Additive.ofMul
            (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ
              (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)))
          = θ (κ (σ, τ)) := by
        rw [kerIso_naturality p K i j m n Φ (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ)]
        show gradedMapLin p Φ.toHom Φ.surjective i j
            (kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ s hs σ τ))
          = gradedMapLin p Φ.toHom Φ.surjective i j (κ (σ, τ))
        rfl
      have hconj : kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
            (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn σ))
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' τ)))
          = σ • δ τ := by
        rw [kerIso_conjKernelMul]
        show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn σ))).right • δ τ = σ • δ τ
        rw [hs' (ρn σ)]
        show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn σ)) • δ τ = σ • δ τ
        rw [hflow σ]
        show (σ : K ≃ₐ[ℚ] K) • δ τ = (σ : K ≃ₐ[ℚ] K) • δ τ
        rfl
      have hlast : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' (σ * τ))) = δ (σ * τ) := rfl
      have hlast2 : kerIso p K i j n (Additive.ofMul
            (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ ρ ρn hρn s s' hs hs' σ)) = δ σ := rfl
      rw [hκeq, hconj, hlast, hlast2]
    rw [heq] at hdiff
    exact hdiff
  -- (C) transfer to the kernel coefficients and apply the splitting criterion
  letI : CommGroup ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) with
      mul_comm := flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j }
  letI : DistribMulAction (flowGroup p (K ≃ₐ[ℚ] K) n i j)
      (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)
  letI : DistribMulAction ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) :=
    DistribMulAction.compHom _ ρn
  have hkerK : (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)
      ∈ Work.GroupCohomology.B2 ↥Δ (Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker) := by
    have hφeq : ∀ (h : ↥Δ) (a : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker),
        kerIso p K i j n (h • a) = h • kerIso p K i j n a := by
      intro h a
      show kerIso p K i j n (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (ρn h)) (Additive.toMul a)))
        = (h : K ≃ₐ[ℚ] K) • kerIso p K i j n (Additive.ofMul (Additive.toMul a))
      rw [kerIso_conjKernelMul]
      show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' (ρn h))).right
          • kerIso p K i j n (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hs' (ρn h)]
      show (flowQuot p (K ≃ₐ[ℚ] K) n i j (ρn h)) • kerIso p K i j n
          (Additive.ofMul (Additive.toMul a)) = (h : K ≃ₐ[ℚ] K) • _
      rw [hflow h]
    have hbij : Function.Bijective (kerIso p K i j n).toAddMonoidHom :=
      (kerIso p K i j n).bijective
    exact (mem_B2_mapCochain2_iff (kerIso p K i j n).toAddMonoidHom hφeq hbij
      (fun q : ↥Δ × ↥Δ => kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' q.1 q.2)).mpr hker
  -- the splitting criterion gives the lift over `Δ`
  obtain ⟨ψ, hψ⟩ := (exists_lift_iff_kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j ρn s' hs' h1s'
      (flowGroupSucc_ker_comm p (K ≃ₐ[ℚ] K) n i j)).mpr hkerK
  refine ⟨ψ, ?_, ?_⟩
  · intro x
    exact (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr (DFunLike.congr_fun hψ x)
  · intro x hx
    have hx1 : x = 1 := by
      apply Subtype.ext
      have h := hflow x
      rw [hx, map_one] at h
      exact h.symm
    show ψ x = 1
    rw [hx1, map_one]

/-- The homomorphism out of the cyclic subgroup generated by `g` sending `g` to `x`, when
`orderOf x` divides `orderOf g`. -/
theorem exists_zpowersHom_of_orderOf_dvd_ssg {G H : Type*} [Group G] [Group H] (g : G) (x : H)
    (hx : orderOf x ∣ orderOf g) :
    ∃ ρ : ↥(Subgroup.zpowers g) →* H, ρ ⟨g, Subgroup.mem_zpowers g⟩ = x := by
  have hgen : ∀ y : ↥(Subgroup.zpowers g),
      y ∈ Subgroup.zpowers (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hk⟩
  have hdvd : orderOf x ∣ orderOf (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) := by
    rw [Subgroup.orderOf_mk]
    exact hx
  exact ⟨monoidHomOfForallMemZpowers hgen hdvd, monoidHomOfForallMemZpowers_apply_gen hgen hdvd⟩

/-- The transported section cocycle of an arbitrary subgroup `Δ ≤ Gal(K/ℚ)` (equipped with a
homomorphism `ρ : ↥Δ →* Γ_m(τ)` lifting the inclusion) is a `2`-cocycle with values in `E(m,τ)`.
This is `Work.SSGRoute.exists_localCocycle` with the decomposition group of a place replaced by an
arbitrary subgroup. -/
theorem kerSuccCocycle_kerIso_mem_Z2_ssg (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (Δ : Subgroup (K ≃ₐ[ℚ] K))
    (ρ : ↥Δ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hρ : ∀ σ : ↥Δ, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K)) :
    (letI : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
        DistribMulAction.compHom _ (Subgroup.subtype Δ)
     (fun x : ↥Δ × ↥Δ => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
        (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
        (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) x.1 x.2))
       ∈ Work.GroupCohomology.Z2 ↥Δ (E p (K ≃ₐ[ℚ] K) m i j)) := by
  letI : DistribMulAction ↥Δ (E p (K ≃ₐ[ℚ] K) m i j) :=
    DistribMulAction.compHom _ (Subgroup.subtype Δ)
  have hcomm : ∀ a b : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker, a * b = b * a :=
    fun a b => (flowGroupSucc_ker_isMulCommutative p (K ≃ₐ[ℚ] K) m i j).is_comm.comm a b
  have hmain := kerSuccCocycle_transport_mem_Z2 (p := p) (G := K ≃ₐ[ℚ] K) m i j
    (H := ↥Δ) ρ (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j) hcomm
    (kerIso p K i j m) (kerIso_equivariant p K i j m)
  have hψ : (flowQuot p (K ≃ₐ[ℚ] K) m i j).comp ρ = (Subgroup.subtype Δ : ↥Δ →* K ≃ₐ[ℚ] K) :=
    MonoidHom.ext (fun h => hρ h)
  have hact : DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j)
        ((flowQuot p (K ≃ₐ[ℚ] K) m i j).comp ρ)
      = DistribMulAction.compHom (E p (K ≃ₐ[ℚ] K) m i j) (Subgroup.subtype Δ) :=
    congrArg _ hψ
  rw [hact] at hmain
  exact hmain

/-- **Group-theoretic core of the conjugacy transfer.**  Let `ρ : G →* Γ`, `π : N →* Γ`, let
`c₀, c` be involutions of `G` conjugate by `g`, and let `l₀` lift `ρ` over `⟨c₀⟩`.  If `ρ c ≠ 1`
and `w ∈ N` lifts `ρ g`, then conjugating `l₀ ⟨c₀, ·⟩` by `w` gives a homomorphism `⟨c⟩ →* N`
which still lifts `ρ` and which kills `ker ρ`. -/
private theorem exists_conj_transfer_lift_ssg {G Γ N : Type*} [Group G] [Group Γ] [Group N]
    (ρ : G →* Γ) (π : N →* Γ)
    (c₀ c g : G) (hc₀ : c₀ ^ 2 = 1) (hc : c ^ 2 = 1) (hg : c = g * c₀ * g⁻¹)
    (hne : ρ c ≠ 1) (w : N) (hw : π w = ρ g)
    (l₀ : ↥(Subgroup.zpowers c₀) →* N) (hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀), π (l₀ σ) = ρ σ) :
    ∃ l : ↥(Subgroup.zpowers c) →* N,
      (∀ σ : ↥(Subgroup.zpowers c), π (l σ) = ρ σ) ∧
      (∀ σ : ↥(Subgroup.zpowers c), ρ σ = 1 → l σ = 1) := by
  -- the conjugated element `y = w * l₀ ⟨c₀, ·⟩ * w⁻¹`
  set a : N := l₀ ⟨c₀, Subgroup.mem_zpowers c₀⟩ with ha
  set y : N := w * a * w⁻¹ with hy
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow]
    have h2 : (⟨c₀, Subgroup.mem_zpowers c₀⟩ : ↥(Subgroup.zpowers c₀)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hc₀
    rw [h2, map_one]
  have hyconj : y = MulAut.conj w a := by rw [hy, MulAut.conj_apply]
  have hy2 : y ^ 2 = 1 := by rw [hyconj, ← map_pow, ha2, map_one]
  -- `y` lies over `ρ c`
  have hπy : π y = ρ c := by
    rw [hy, map_mul, map_mul, map_inv, hw, ha, hl₀ ⟨c₀, Subgroup.mem_zpowers c₀⟩]
    rw [← map_inv, ← map_mul, ← map_mul, ← hg]
  -- order bookkeeping
  have hcne : c ≠ 1 := fun h => hne (by rw [h, map_one])
  have hordc : orderOf c = 2 := orderOf_eq_prime (p := 2) hc hcne
  have hρc2 : (ρ c) ^ 2 = 1 := by rw [← map_pow, hc, map_one]
  have hρcord : orderOf (ρ c) = 2 := orderOf_eq_prime (p := 2) hρc2 hne
  have hyord : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  -- `⟨c, ·⟩` generates `⟨c⟩`
  have hgen : ∀ x : ↥(Subgroup.zpowers c),
      x ∈ Subgroup.zpowers (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hk⟩
  have hgdvd : orderOf y ∣ orderOf (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) := by
    rw [Subgroup.orderOf_mk, hordc]
    exact hyord
  -- the homomorphism `⟨c⟩ →* N` determined by `c ↦ y`
  let l : ↥(Subgroup.zpowers c) →* N := monoidHomOfForallMemZpowers hgen hgdvd
  have hl_c : l ⟨c, Subgroup.mem_zpowers c⟩ = y := monoidHomOfForallMemZpowers_apply_gen hgen hgdvd
  refine ⟨l, ?_, ?_⟩
  · intro σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
    have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    calc π (l σ) = π (l ((⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k)) := by
          rw [hσ]
      _ = π ((l ⟨c, Subgroup.mem_zpowers c⟩) ^ k) := by rw [map_zpow]
      _ = (π (l ⟨c, Subgroup.mem_zpowers c⟩)) ^ k := by rw [map_zpow]
      _ = (ρ c) ^ k := by rw [hl_c, hπy]
      _ = ρ (c ^ k) := (map_zpow ρ c k).symm
      _ = ρ σ := by rw [hk]
  · intro σ hσ1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
    have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    have hρk : (ρ c) ^ k = 1 := by
      rw [← map_zpow, hk]
      exact hσ1
    have hk_dvd : ((orderOf (ρ c) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hρk
    rw [hρcord] at hk_dvd
    have hcast : ((orderOf y : ℕ) : ℤ) ∣ (2 : ℤ) := by exact_mod_cast hyord
    have hlσ : l σ = y ^ k := by rw [hσ, map_zpow, hl_c]
    rw [hlσ]
    exact orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hcast hk_dvd)

/-- **Transfer of a clause-(B) lift along conjugacy.**
See `Work.SSGRoute.involution_clause_conj_transfer` for the full explanation; this is the copy
carried by the present module (so that `stage_local_shrinking` can use it without an import
cycle). -/
theorem involution_clause_conj_transfer_ssg (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (c₀ c g : SSGRoute.GalQ) (hc₀ : c₀ ^ 2 = 1) (hc : c ^ 2 = 1)
    (hg : c = g * c₀ * g⁻¹)
    (hne : (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) ≠ 1)
    (l₀ : ↥(Subgroup.zpowers c₀) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀),
      SSGRoute.LiftsFlowAt (l₀ σ) (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) :
    ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      (∀ σ : ↥(Subgroup.zpowers c),
        SSGRoute.LiftsFlowAt (l σ)
          (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
      (∀ σ : ↥(Subgroup.zpowers c),
        (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l σ = 1) := by
  classical
  obtain ⟨l, hl, hkill⟩ :=
    exists_conj_transfer_lift_ssg
      (ρ := (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ)
      (π := flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
      (hc₀ := hc₀) (hc := hc) (hg := hg) (hne := hne)
      (w := flowGroupSection p (K ≃ₐ[ℚ] K) n i j
        (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) g))
      (hw := flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j _)
      (l₀ := l₀)
      (hl₀ := fun σ => (SSGRoute.liftsFlowAt_iff_flowGroupSucc p K n i j (l₀ σ) _).mp (hl₀ σ))
  exact ⟨l,
    fun σ => (SSGRoute.liftsFlowAt_iff_flowGroupSucc p K n i j (l σ) _).mpr (hl σ),
    fun σ hσ => hkill σ hσ⟩

/-- **Clause (B) in the degenerate case.**  If every involution `c ∈ G_ℚ` lies in
`K.fixingSubgroup`, then Scholz condition (ii) gives `φ c = 1`, hence the pushed solution is trivial
on `⟨c⟩` and `l := 1` is a kernel-killing splitting. -/
theorem involution_clause_of_mem_fixingSubgroup_ssg (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (hfix : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(Subgroup.zpowers c),
          SSGRoute.LiftsFlowAt (l σ)
            (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
        (∀ σ : ↥(Subgroup.zpowers c),
          (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l σ = 1) := by
  intro c hc
  -- the pushed solution `Ψ`
  set Ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ with hΨdef
  -- Scholz condition (ii): `c ∈ K.fixingSubgroup` gives `φ c = 1`
  have hφc : φ c = 1 := hφ.2.2.1 c hc (hfix c hc)
  have hΨc : Ψ c = 1 := by simp [hΨdef, hφc]
  -- `l := 1` is a kernel-killing splitting
  refine ⟨1, ?_, ?_⟩
  · intro σ
    have hσ1 : Ψ (σ : SSGRoute.GalQ) = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      rw [← hk, map_zpow, hΨc, one_zpow]
    rw [hσ1]
    exact (liftsFlowAt_iff_flowGroupSucc p K n i j 1 1).mpr (map_one _)
  · intro σ _
    exact MonoidHom.one_apply σ

theorem stage_local_shrinking (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j,
        SSGRoute.IsScholzSolution p K m i j φ →
        ∃ Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n,
          (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
            ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l σ = 1)) ∧
          (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
            ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(Subgroup.zpowers c),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(Subgroup.zpowers c),
                ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l σ = 1)) := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  obtain ⟨D⟩ := prop5Data_exists p (K ≃ₐ[ℚ] K) i j hj hji
  by_cases hmain : ∃ c₀ : SSGRoute.GalQ, c₀ ^ 2 = 1 ∧ c₀ ∉ K.fixingSubgroup
  · obtain ⟨c₀, hc₀sq, hc₀fix⟩ := hmain
    have hc₀res : AlgEquiv.restrictNormalHom K c₀ ≠ 1 := by
      intro h1
      exact hc₀fix ((@restrictNormalHom_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _
        K ‹Normal ℚ K› c₀).mp h1)
    have hc₀ne : c₀ ≠ 1 := by
      intro h1
      exact hc₀fix (h1 ▸ K.fixingSubgroup.one_mem)
    have hordσ : orderOf (AlgEquiv.restrictNormalHom K c₀) = 2 := by
      refine orderOf_eq_prime ?_ hc₀res
      rw [← map_pow, hc₀sq, map_one]
    obtain ⟨S, hSfin, hSdisj, hShit⟩ := exists_representatives (p := p) K
    let S' : Finset (ValuationSubring SSGRoute.QBar) :=
      S.filter (fun A => SSGRoute.IsT1Place p K A)
    let Hinv : Subgroup (K ≃ₐ[ℚ] K) := Subgroup.zpowers (AlgEquiv.restrictNormalHom K c₀)
    let ι' : Type _ := Option ↥S'
    let H' : ι' → Subgroup (K ≃ₐ[ℚ] K) := fun a => match a with
      | some A => (SSGRoute.decomp ℚ A.1).map (AlgEquiv.restrictNormalHom K)
      | none => Hinv
    let T : Type _ := shapiroT p (K ≃ₐ[ℚ] K) ι' H'
    obtain ⟨m₀, hm₀n, hm₀⟩ :=
      exists_shrinking_H2_tate p (K ≃ₐ[ℚ] K) hj D T (Fintype.card ι') hn
    refine ⟨m₀, hm₀n, ?_⟩
    intro m hm φ hφ
    -- the homomorphism `ρ : ↥⟨res c₀⟩ →* Γ_m(τ)` sending the generator to `φ c₀`
    have hφc₀dvd : orderOf (φ c₀) ∣ orderOf (AlgEquiv.restrictNormalHom K c₀) := by
      rw [hordσ]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hc₀sq, map_one])
    obtain ⟨ρ, hρgen⟩ :=
      exists_zpowersHom_of_orderOf_dvd_ssg (AlgEquiv.restrictNormalHom K c₀) (φ c₀) hφc₀dvd
    have hρ : ∀ σ : ↥Hinv, flowQuot p (K ≃ₐ[ℚ] K) m i j (ρ σ) = (σ : K ≃ₐ[ℚ] K) := by
      intro σ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hσeq : σ = (⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩ : ↥Hinv) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hcoe : ((σ : K ≃ₐ[ℚ] K)) = (AlgEquiv.restrictNormalHom K c₀) ^ k := by
        rw [hσeq]
        exact map_zpow (Subgroup.subtype Hinv) _ k
      rw [hcoe]
      have hρpow : ρ σ = (φ c₀) ^ k := by rw [hσeq, map_zpow, hρgen]
      rw [hρpow, map_zpow]
      rw [show flowQuot p (K ≃ₐ[ℚ] K) m i j (φ c₀) = AlgEquiv.restrictNormalHom K c₀ from
        hφ.1.2.2 c₀]
    -- the packaged family of `2`-cocycles
    let κ : ∀ a : ι', ↥(H' a) × ↥(H' a) → E p (K ≃ₐ[ℚ] K) m i j := fun a => match a with
      | some A => localKappa p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
      | none => fun q => kerIso p K i j m (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j ρ
          (flowGroupSection p (K ≃ₐ[ℚ] K) m i j)
          (flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j) q.1 q.2)
    have hκ : ∀ a : ι',
        (letI : DistribMulAction ↥(H' a) (E p (K ≃ₐ[ℚ] K) m i j) :=
          DistribMulAction.compHom _ (Subgroup.subtype _)
         κ a ∈ Work.GroupCohomology.Z2 (↥(H' a)) (E p (K ≃ₐ[ℚ] K) m i j)) := by
      intro a
      cases a with
      | some A => exact localKappa_mem_Z2 p K i j m φ hφ A.1 (Finset.mem_filter.mp A.2).2
      | none => exact kerSuccCocycle_kerIso_mem_Z2_ssg p K i j m Hinv ρ hρ
    obtain ⟨ev, hev, C, hC, hCval, hnat⟩ :=
      shapiro_packaging_natural p (K ≃ₐ[ℚ] K) ι' H' (E p (K ≃ₐ[ℚ] K) m i j) κ hκ
    let clsA : ι' → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
      fun a => Work.GroupCohomology.H2π (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) ⟨C a, hC a⟩
    let cls : Fin (Fintype.card ι') → Work.GroupCohomology.H2 (K ≃ₐ[ℚ] K)
        (E p (K ≃ₐ[ℚ] K) m i j ⊗[ZMod p] T) :=
      fun k => clsA ((Fintype.equivFin ι').symm k)
    obtain ⟨Φ, hΦ⟩ := hm₀ m hm cls
    have hclsA_eval : ∀ a : ι', cls (Fintype.equivFin ι' a) = clsA a := by
      intro a
      simp only [cls, Equiv.symm_apply_apply]
    -- the involution data: the naturality at level `n` and the built-in evaluation maps
    obtain ⟨evθ0, hevθ0, hnat0⟩ := hnat (E p (K ≃ₐ[ℚ] K) n i j)
      (gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
    have hkill0 : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (C none)
        ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
      h2Map_eq_zero_iff_B2 (p := p) (G := K ≃ₐ[ℚ] K) (i := i) (j := j) (m := m) (n := n)
        (T := T) Φ ⟨C none, hC none⟩ (by
          have hh := hΦ (Fintype.equivFin ι' none)
          rwa [hclsA_eval none] at hh)
    obtain ⟨lσ, hlσlift, hlσker⟩ := level_n_of_cocycle_killed_ssg p K i j m n T Hinv ρ hρ Φ
      (ev none) (C none) (fun h h' => hCval none h h') hkill0 (hev none)
      (evθ0 none) (hevθ0 none) (fun z => hnat0 none z)
    -- the lift over `⟨c₀⟩`
    have hσ₀z : ((⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩ : ↥Hinv) ^ 2) = 1 := by
      apply Subtype.ext
      show (AlgEquiv.restrictNormalHom K c₀) ^ 2 = (1 : K ≃ₐ[ℚ] K)
      rw [← map_pow, hc₀sq, map_one]
    have hx2 : (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) ^ 2 = 1 := by
      rw [← map_pow, hσ₀z, map_one]
    have hc₀order : orderOf c₀ = 2 := orderOf_eq_prime hc₀sq hc₀ne
    have hdvd : orderOf (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
        ∣ orderOf c₀ := by
      rw [hc₀order]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx2
    obtain ⟨l₀, hl₀gen⟩ := exists_zpowersHom_of_orderOf_dvd_ssg c₀
      (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) hdvd
    have hρval : (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)
          (ρ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
        = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φ c₀) :=
      congrArg (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) hρgen
    have hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀),
        SSGRoute.LiftsFlowAt (l₀ σ)
            (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) ∧
        ((((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l₀ σ = 1) := by
      intro σ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      have hσeq : σ = (⟨c₀, Subgroup.mem_zpowers c₀⟩ : ↥(Subgroup.zpowers c₀)) ^ k :=
        Subtype.ext (by simpa using hk.symm)
      have hσcoe : (σ : SSGRoute.GalQ) = c₀ ^ k := by
        rw [hσeq]
        exact map_zpow (Subgroup.subtype (Subgroup.zpowers c₀)) _ k
      have hl₀val : l₀ σ
          = (lσ ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩) ^ k := by
        rw [hσeq, map_zpow, hl₀gen]
      have hΨval : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)
          = ((((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp ρ)
              ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)) ^ k := by
        rw [hσcoe, MonoidHom.comp_apply, map_zpow φ c₀ k,
          map_zpow (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φ c₀) k, ← hρval,
          MonoidHom.comp_apply]
      constructor
      · refine (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mpr ?_
        rw [hl₀val, hΨval, map_zpow]
        congr 1
        exact (liftsFlowAt_iff_flowGroupSucc p K n i j _ _).mp
          (hlσlift ⟨AlgEquiv.restrictNormalHom K c₀, Subgroup.mem_zpowers _⟩)
      · intro hσ1
        rw [hl₀val, ← map_zpow]
        refine hlσker _ ?_
        rw [map_zpow]
        rw [← hΨval]
        exact hσ1
    refine ⟨Φ, ?_, ?_⟩
    · -- clause (A)
      have hrep : ∀ A ∈ S', ∃ l : ↥(SSGRoute.decomp ℚ A) →*
          flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
          (∀ x : ↥(SSGRoute.decomp ℚ A),
            SSGRoute.LiftsFlowAt (l x) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x)) ∧
          (∀ x : ↥(SSGRoute.decomp ℚ A),
            (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) x) = 1 → l x = 1) := by
        intro A hAS'
        have hA : SSGRoute.IsT1Place p K A := (Finset.mem_filter.mp hAS').2
        obtain ⟨evθ, hevθ, hnatval⟩ := hnat (E p (K ≃ₐ[ℚ] K) n i j)
          (gradedMapLin p Φ.toHom Φ.surjective i j)
          (fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x)
        have hkillA : Work.GroupCohomology.mapCochain2 (K ≃ₐ[ℚ] K)
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (C (some ⟨A, hAS'⟩))
            ∈ Work.GroupCohomology.B2 (K ≃ₐ[ℚ] K)
                (E p (K ≃ₐ[ℚ] K) n i j ⊗[ZMod p] T) :=
          h2Map_eq_zero_iff_B2 (p := p) (G := K ≃ₐ[ℚ] K) (i := i) (j := j) (m := m) (n := n)
            (T := T) Φ ⟨C (some ⟨A, hAS'⟩), hC (some ⟨A, hAS'⟩)⟩ (by
              have hh := hΦ (Fintype.equivFin ι' (some ⟨A, hAS'⟩))
              rwa [hclsA_eval (some ⟨A, hAS'⟩)] at hh)
        exact local_level_n_of_class_killed p K i j m n T A hA φ hφ Φ
          (ev (some ⟨A, hAS'⟩)) (C (some ⟨A, hAS'⟩))
          (fun h h' => hCval (some ⟨A, hAS'⟩) h h') hkillA (hev (some ⟨A, hAS'⟩))
          (evθ (some ⟨A, hAS'⟩)) (hevθ (some ⟨A, hAS'⟩)) (fun z => hnatval (some ⟨A, hAS'⟩) z)
      refine local_clause_all_places p K i j n ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) S' ?_ hrep
      intro B hBfin hBram
      obtain ⟨A, hAS, hconj⟩ := hShit B hBfin hBram.symm
      refine ⟨A, Finset.mem_filter.mpr ⟨hAS, ?_⟩, hconj⟩
      exact isT1Place_of_isConjPlace p K (A₀ := B) (A := A)
        (isConjPlace_symm (k := ℚ) hconj) ⟨hBfin, hBram⟩
    · -- clause (B)
      intro c hc
      by_cases hcfix : c ∈ K.fixingSubgroup
      · -- `c` acts trivially: the pushed solution is trivial on `⟨c⟩`
        have hφc : φ c = 1 := hφ.2.2.1 c hc hcfix
        refine ⟨1, ?_, ?_⟩
        · intro σ
          have hσ1 : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) (σ : SSGRoute.GalQ)) = 1 := by
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
            have h1 : (σ : SSGRoute.GalQ) = c ^ k := hk.symm
            rw [h1, MonoidHom.comp_apply, map_zpow φ c k, hφc, one_zpow, map_one]
          rw [hσ1]
          exact (liftsFlowAt_iff_flowGroupSucc p K n i j 1 1).mpr (map_one _)
        · intro σ _
          exact MonoidHom.one_apply σ
      · -- `c` is a non-trivial involution: transfer along conjugacy from `c₀`
        have hcne : c ≠ 1 := fun h1 => hcfix (h1 ▸ K.fixingSubgroup.one_mem)
        rcases involutions_eq_one_or_conjugate c₀ c hc₀sq hc with h1 | h2 | ⟨g, hg⟩
        · exact absurd h1 hc₀ne
        · exact absurd h2 hcne
        · have hres : AlgEquiv.restrictNormalHom K c ≠ 1 := by
            intro h1
            exact hcfix ((@restrictNormalHom_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _
              K ‹Normal ℚ K› c).mp h1)
          have hΨne : (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) ≠ 1 := by
            intro h1
            refine hres ?_
            rw [← hφ.1.2.2 c]
            rw [show flowQuot p (K ≃ₐ[ℚ] K) m i j (φ c)
                = flowQuot p (K ≃ₐ[ℚ] K) n i j
                    (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) from by
              rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]]
            rw [h1, map_one]
          exact involution_clause_conj_transfer_ssg p K i j m n φ Φ c₀ c g hc₀sq hc hg hΨne l₀
            (fun σ => (hl₀ σ).1)
  · -- no involution of `G_ℚ` lies outside `K.fixingSubgroup`: clause (B) is trivial
    push_neg at hmain
    obtain ⟨m₀, hm₀n, hm₀⟩ := clause_A_of_prop5Data_exists p K i j hj hji hμ n hn D
    refine ⟨m₀, hm₀n, ?_⟩
    intro m hm φ hφ
    obtain ⟨Φ, hA⟩ := hm₀ m hm φ hφ
    exact ⟨Φ, hA, involution_clause_of_mem_fixingSubgroup_ssg p K i j m n φ hφ Φ hmain⟩

end Work.SSGRoute
