/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.RankTheoryDeep.CharModule
import Submission.NK.RankTheoryDeep.PlacesOverEll

/-!
# Vocabulary for the idèle-side rank lower bound

Definitions and elementary facts shared by the proof of
`NK.NUV2.ideleDualRank_lowerBound` and the lemmas delegated for it:

* `NK.NUV2.isOpen_integralIdeles` — the integral idèles form an open subgroup of `𝕀 K`;
* `NK.NUV2.projLocal` — the projection `∏_v 𝒪_vˣ →* 𝒪_qˣ` at a finite place, continuous;
* `NK.NUV2.testIdle` / `NK.NUV2.testIdleA` — the idèle which is `g` at `q` and `1` elsewhere;
* `NK.NUV2.pushForward` / `NK.NUV2.Phi` — the `ℤ_2`-linear map from the product of the local
  character modules into the character module of the integral idèles, and its injectivity;
* `NK.NUV2.unitsToIntegral` — the diagonal embedding of the global units into the integral
  idèles, and `NK.NUV2.restrictUnits` — its transpose.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct nonZeroDivisors

namespace NK.NUV2

open NK.GlobalCFT NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ## The integral idèles are open -/

/-- **The group of integral idèles is open** in the idèle group (the restricted product topology
has the product of the local unit groups as a basic open set). -/
theorem isOpen_integralIdeles :
    IsOpen ((Idele.integralIdeles K : Subgroup (Idele K)) : Set (Idele K)) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : Place K => (Place.localField K v)ˣ)
    (A := fun v : Place K => (Place.localUnits K v : Set ((Place.localField K v)ˣ)))
    (fun v => Place.isOpen_localUnits v) (p := fun v => v.IsFinite)
  rw [show ((Idele.integralIdeles K : Subgroup (Idele K)) : Set (Idele K))
      = {f : Idele K | ∀ v, v.IsFinite → f v ∈ (Place.localUnits K v : Set _)} from by
    ext x
    simp only [SetLike.mem_coe, Idele.mem_integralIdeles, Set.mem_setOf_eq]]
  exact h

/-! ## The projection to the local units -/

/-- **The projection `∏_v 𝒪_vˣ →* 𝒪_qˣ`** at a finite place `q`. -/
noncomputable def projLocal (q : HeightOneSpectrum (𝓞 K)) :
    ↥(Idele.integralIdeles K) →* ↥(Place.localUnits K (Place.ofFinite q)) :=
  MonoidHom.codRestrict
    ((Idele.eval (Place.ofFinite q)).comp (Idele.integralIdeles K).subtype)
    (Place.localUnits K (Place.ofFinite q))
    (fun x => x.2 _ (Place.isFinite_ofFinite q))

@[simp] theorem projLocal_coe (q : HeightOneSpectrum (𝓞 K))
    (x : ↥(Idele.integralIdeles K)) :
    ((projLocal q x : ↥(Place.localUnits K (Place.ofFinite q))) :
      (Place.localField K (Place.ofFinite q))ˣ) = (x : Idele K) (Place.ofFinite q) := rfl

/-- The projection to the local units is continuous. -/
theorem continuous_projLocal (q : HeightOneSpectrum (𝓞 K)) :
    Continuous (projLocal (K := K) q) := by
  refine Continuous.subtype_mk ?_ _
  exact (RestrictedProduct.continuous_eval (Place.ofFinite q)).comp continuous_subtype_val

/-! ## Test idèles -/

/-- **The idèle which is `g` at the finite place `q` and `1` everywhere else.** -/
noncomputable def testIdle (q : HeightOneSpectrum (𝓞 K))
    (g : ↥(Place.localUnits K (Place.ofFinite q))) : Idele K := by
  classical
  exact ⟨Function.update (fun _ => 1) (Place.ofFinite q)
      (g : (Place.localField K (Place.ofFinite q))ˣ), by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (Place.ofFinite q)).subset ?_
    intro v hv
    by_contra hv'
    exact hv (by rw [Function.update_of_ne (by simpa using hv')]; exact Subgroup.one_mem _)⟩

theorem testIdle_apply_self (q : HeightOneSpectrum (𝓞 K))
    (g : ↥(Place.localUnits K (Place.ofFinite q))) :
    testIdle q g (Place.ofFinite q) = (g : (Place.localField K (Place.ofFinite q))ˣ) := by
  classical
  change Function.update (β := fun v => (Place.localField K v)ˣ) (fun _ => 1) (Place.ofFinite q)
    (g : (Place.localField K (Place.ofFinite q))ˣ) (Place.ofFinite q) = _
  exact Function.update_self _ _ _

theorem testIdle_apply_ne {q q' : HeightOneSpectrum (𝓞 K)} (h : q' ≠ q)
    (g : ↥(Place.localUnits K (Place.ofFinite q))) : testIdle q g (Place.ofFinite q') = 1 := by
  classical
  change Function.update (β := fun v => (Place.localField K v)ˣ) (fun _ => 1) (Place.ofFinite q)
    (g : (Place.localField K (Place.ofFinite q))ˣ) (Place.ofFinite q') = _
  exact Function.update_of_ne (fun hc => h (Place.ofFinite_inj.mp hc)) _ _

theorem testIdle_mem (q : HeightOneSpectrum (𝓞 K))
    (g : ↥(Place.localUnits K (Place.ofFinite q))) : testIdle q g ∈ Idele.integralIdeles K := by
  classical
  rw [Idele.mem_integralIdeles]
  intro v hv
  rw [Place.isFinite_iff] at hv
  obtain ⟨q', rfl⟩ := hv
  by_cases hq : q' = q
  · subst hq; rw [testIdle_apply_self]; exact g.2
  · rw [testIdle_apply_ne hq]; exact Subgroup.one_mem _

/-- The test idèle, as an element of the integral idèles. -/
noncomputable def testIdleA (q : HeightOneSpectrum (𝓞 K))
    (g : ↥(Place.localUnits K (Place.ofFinite q))) : ↥(Idele.integralIdeles K) :=
  ⟨testIdle q g, testIdle_mem q g⟩

@[simp] theorem projLocal_testIdleA (q : HeightOneSpectrum (𝓞 K))
    (g : ↥(Place.localUnits K (Place.ofFinite q))) : projLocal q (testIdleA q g) = g := by
  apply Subtype.ext
  rw [projLocal_coe, testIdleA, testIdle_apply_self]

theorem projLocal_testIdleA_ne {q q' : HeightOneSpectrum (𝓞 K)} (h : q' ≠ q)
    (g : ↥(Place.localUnits K (Place.ofFinite q))) :
    projLocal q' (testIdleA q g) = 1 := by
  apply Subtype.ext
  rw [projLocal_coe, testIdleA, testIdle_apply_ne h]
  rfl

section SumEval

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Evaluating a finite sum of continuous characters at a point. -/
theorem Dual_sum_apply {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → NK.Reconstruct.Dual G ℓ) (x : Additive G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  have h1 : ((∑ i ∈ s, f i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ)
      = ∑ i ∈ s, ((f i) : Additive G →+ PadicInt ℓ) :=
    map_sum (AddSubgroup.subtype _) f s
  have h2 : ((∑ i ∈ s, f i : NK.Reconstruct.Dual G ℓ) : Additive G →+ PadicInt ℓ) x
      = (∑ i ∈ s, ((f i) : Additive G →+ PadicInt ℓ)) x := by rw [h1]
  rw [h2]
  exact map_sum (AddMonoidHom.eval x) (fun i => ((f i) : Additive G →+ PadicInt ℓ)) s

end SumEval

/-! ## The adjoint pair: pushing local characters into the integral idèles -/

/-- **Pushforward of a character of the local units `𝒪_qˣ` to the integral idèles.** -/
noncomputable def pushForward (q : HeightOneSpectrum (𝓞 K)) :
    NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q)) 2 →ₗ[PadicInt 2]
      NK.Reconstruct.Dual ↥(Idele.integralIdeles K) 2 where
  toFun ψ := NK.Reconstruct.dualMap 2 (projLocal q) (continuous_projLocal q) ψ
  map_add' ψ ψ' := NK.Reconstruct.dualMap_add 2 (projLocal q) (continuous_projLocal q) ψ ψ'
  map_smul' a ψ := NK.RankTheoryDeep.dualMap_smul (ℓ := 2) (projLocal q) (continuous_projLocal q) a ψ

@[simp] theorem pushForward_apply (q : HeightOneSpectrum (𝓞 K))
    (ψ : NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q)) 2)
    (x : ↥(Idele.integralIdeles K)) :
    pushForward q ψ (Additive.ofMul x) = ψ (Additive.ofMul (projLocal q x)) := by
  show NK.Reconstruct.dualMap 2 (projLocal q) (continuous_projLocal q) ψ (Additive.ofMul x) = _
  rw [NK.Reconstruct.dualMap_apply]
  rfl

/-- Evaluating a pushed-forward character at the test idèle of its own place. -/
theorem pushForward_testIdleA_self (q : HeightOneSpectrum (𝓞 K))
    (ψ : NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q)) 2)
    (g : ↥(Place.localUnits K (Place.ofFinite q))) :
    pushForward (K := K) q ψ (Additive.ofMul (testIdleA q g)) = ψ (Additive.ofMul g) := by
  rw [pushForward_apply, projLocal_testIdleA]

/-- Evaluating a pushed-forward character at a test idèle of a different place. -/
theorem pushForward_testIdleA_ne {q q' : HeightOneSpectrum (𝓞 K)} (h : q' ≠ q)
    (ψ : NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q')) 2)
    (g : ↥(Place.localUnits K (Place.ofFinite q))) :
    pushForward (K := K) q' ψ (Additive.ofMul (testIdleA q g)) = 0 := by
  rw [pushForward_apply, projLocal_testIdleA_ne h]
  have h0 : Additive.ofMul (1 : ↥(Place.localUnits K (Place.ofFinite q'))) = 0 := rfl
  rw [h0]
  exact map_zero (ψ : Additive ↥(Place.localUnits K (Place.ofFinite q')) →+ PadicInt 2)

/-- **The combined map** from the product of the local character modules over a finite set of
places into the character module of the integral idèles. -/
noncomputable def Phi (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((q : {q // q ∈ S}) → NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q)) 2)
      →ₗ[PadicInt 2] NK.Reconstruct.Dual ↥(Idele.integralIdeles K) 2 where
  toFun ψ := ∑ q : {q // q ∈ S}, pushForward (K := K) q.val (ψ q)
  map_add' ψ ψ' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Pi.add_apply]
    exact (pushForward (K := K) q.val).map_add (ψ q) (ψ' q)
  map_smul' a ψ := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (pushForward (K := K) q.val).map_smul a (ψ q)

/-- **The combined map is injective**: a local character is recovered by evaluating at the test
idèle supported at its place. -/
theorem Phi_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (Phi (K := K) S) := by
  classical
  intro ψ ψ' h
  funext q
  ext g
  have h1 : (Phi (K := K) S ψ) (Additive.ofMul (testIdleA q.val g))
      = (Phi (K := K) S ψ') (Additive.ofMul (testIdleA q.val g)) := by rw [h]
  have heval : ∀ (φ : (q' : {q' // q' ∈ S}) →
        NK.Reconstruct.Dual ↥(Place.localUnits K (Place.ofFinite q'.val)) 2),
      (Phi (K := K) S φ) (Additive.ofMul (testIdleA q.val g)) = φ q (Additive.ofMul g) := by
    intro φ
    have hsum : (Phi (K := K) S φ) (Additive.ofMul (testIdleA q.val g))
        = ∑ q' : {q' // q' ∈ S},
            pushForward (K := K) q'.val (φ q') (Additive.ofMul (testIdleA q.val g)) := by
      rw [Phi, LinearMap.coe_mk, AddHom.coe_mk]
      simpa using Dual_sum_apply (G := ↥(Idele.integralIdeles K)) (ℓ := 2)
        (s := (Finset.univ : Finset {q' // q' ∈ S}))
        (fun q' => pushForward (K := K) q'.val (φ q'))
        (Additive.ofMul (testIdleA q.val g))
    rw [hsum]
    refine (Finset.sum_eq_single (s := (Finset.univ : Finset {q' // q' ∈ S}))
      (f := fun q' : {q' // q' ∈ S} => pushForward (K := K) q'.val (φ q')
        (Additive.ofMul (testIdleA q.val g)))
      (M := PadicInt 2) q ?_ ?_).trans ?_
    · intro q' _ hq'
      exact pushForward_testIdleA_ne (q := q.val) (q' := q'.val)
        (fun hc => hq' (Subtype.ext hc)) (φ q') g
    · intro hq
      exact absurd (Finset.mem_univ q) hq
    · exact pushForward_testIdleA_self q.val (φ q) g
  rw [heval ψ, heval ψ'] at h1
  exact h1

/-! ## The global units inside the integral idèles -/

/-- **The diagonal embedding of the global units into the integral idèles.** -/
noncomputable def unitsToIntegral (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ →* ↥(Idele.integralIdeles K) :=
  MonoidHom.codRestrict
    ((Idele.principalIdele K).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom))
    (Idele.integralIdeles K)
    (fun u => by
      rw [← Idele.idealOf_eq_one_iff, MonoidHom.comp_apply, Idele.idealOf_principalIdele]
      rw [← FractionalIdeal.spanSingleton_one (S := (𝓞 K)⁰) (R := 𝓞 K) (P := K),
        FractionalIdeal.spanSingleton_eq_spanSingleton]
      refine ⟨u⁻¹, ?_⟩
      rw [Units.smul_def, Algebra.smul_def]
      simp [Units.coe_map])

@[simp] theorem unitsToIntegral_coe (u : (𝓞 K)ˣ) :
    ((unitsToIntegral K u : ↥(Idele.integralIdeles K)) : Idele K)
      = Idele.principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := rfl

/-- **The transpose of `unitsToIntegral`**: restriction of a character of the integral idèles to
the global units. -/
noncomputable def restrictUnits :
    NK.Reconstruct.Dual ↥(Idele.integralIdeles K) 2 →ₗ[PadicInt 2]
      (Additive ((𝓞 K)ˣ) →+ PadicInt 2) where
  toFun ψ := (ψ : Additive ↥(Idele.integralIdeles K) →+ PadicInt 2).comp
    (MonoidHom.toAdditive (unitsToIntegral K))
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp] theorem restrictUnits_apply (ψ : NK.Reconstruct.Dual ↥(Idele.integralIdeles K) 2)
    (u : (𝓞 K)ˣ) :
    restrictUnits ψ (Additive.ofMul u) = ψ (Additive.ofMul (unitsToIntegral K u)) := rfl

end NK.NUV2
