import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E9c.Unram
import Submission.Work.SSGRoute.e9c_transport_zero
import Submission.Work.SSGRoute.e9c_transport_unram
import Submission.Work.SSGRoute.e9c_unram_pairing
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.e9c_phiAt_eq_zero_of_local
import Submission.Work.SSGRoute.exists_finset_unramifiedPlaces
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Helper constructions for the E9c assembly -/

/-- The place of the base field below a place of a finite extension. -/
noncomputable def e9cUnder {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (w : Place L) : Place K :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

theorem e9cUnder_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (w : Place L) :
    Place.LiesOver w (e9cUnder (K := K) w) :=
  Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

theorem e9cUnder_eq_of_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    e9cUnder (K := K) w = v :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (e9cUnder_liesOver (K := K) w) h

/-- **The good finite `Gal(K/k)`-stable set of places.** -/
theorem e9c_exists_good_T (k : Type) [Field k] [NumberField k] (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] [FiniteDimensional K L] (S : Finset (Place K)) :
    ∃ T : Set (Place K), T.Finite ∧
      (∀ (σ : K ≃ₐ[k] K) ⦃u : Place K⦄, u ∈ T → σ • u ∈ T) ∧
      (∀ u : Place K, u ∈ (S : Set (Place K)) → u ∈ T) ∧
      (∀ w : Place L, (∀ u : Place K, u ∈ T → ¬ Place.LiesOver w u) →
        ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)),
          w = Place.ofFinite q ∧ q.asIdeal.LiesOver Q.asIdeal ∧
            q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) := by
  classical
  obtain ⟨Texc, hTexc⟩ := exists_finset_unramifiedPlaces k L
  let T₀ : Set (Place K) := (S : Set (Place K)) ∪ {u : Place K | ∃ w ∈ Texc,
    e9cUnder (K := K) w = u}
  have hT₀fin : T₀.Finite := by
    refine Set.Finite.union (S.finite_toSet) ?_
    refine (Texc.finite_toSet.image (fun w => e9cUnder (K := K) w)).subset ?_
    rintro u ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  obtain ⟨G, hGfin, hGsub⟩ :=
    NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K) T₀ hT₀fin
  refine ⟨G.carrier, hGfin, fun σ u hu => G.smul_mem' σ hu, fun u hu => hGsub (Or.inl hu), ?_⟩
  intro w hw
  have hwT : e9cUnder (K := K) w ∉ G.carrier := fun hmem =>
    hw _ hmem (e9cUnder_liesOver (K := K) w)
  have hwnot : w ∉ Texc := by
    intro hmem
    exact hwT (hGsub (Or.inr ⟨w, hmem, rfl⟩))
  exact hTexc w hwnot

/-- A choice of a representative of the orbit of a place. -/
noncomputable def e9cRep {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (R : Set (Place K))
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) : R :=
  Classical.choose (hR u)

theorem e9cRep_spec {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] {R : Set (Place K)}
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) :
    ∃ σ : K ≃ₐ[k] K, σ • u = (e9cRep R hR u).1 :=
  (Classical.choose_spec (hR u)).1

theorem e9cRep_eq_of_exists {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] {R : Set (Place K)}
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) (v : R)
    (h : ∃ σ : K ≃ₐ[k] K, σ • v.1 = u) : v = e9cRep R hR u := by
  obtain ⟨σ, hσ⟩ := h
  have h2 : ∃ τ : K ≃ₐ[k] K, τ • u = v.1 := ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩
  exact (Classical.choose_spec (hR u)).2 v h2

/-! ## The assembly -/

/-- `extLoc` is additive over a `Finset` sum. -/
theorem extLoc_sum' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K) {ι : Type}
    (s : Finset ι) (f : ι → Abelian.Ext M (idelesRepP k K) r) :
    extLoc (k := k) (K := K) u (∑ i ∈ s, f i)
      = ∑ i ∈ s, extLoc (k := k) (K := K) u (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [extLoc_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, extLoc_add, ih]

/-- `extLoc` of a difference. -/
theorem extLoc_sub' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K)
    (a b : Abelian.Ext M (idelesRepP k K) r) :
    extLoc (k := k) (K := K) u (a - b)
      = extLoc (k := k) (K := K) u a - extLoc (k := k) (K := K) u b := by
  have hneg : extLoc (k := k) (K := K) u (-b) = -extLoc (k := k) (K := K) u b := by
    have h := extLoc_add (k := k) (K := K) u (-b) b
    rw [neg_add_cancel, extLoc_zero (k := k) (K := K) u] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [sub_eq_add_neg, extLoc_add, hneg, sub_eq_add_neg]

/-- `IsUnramifiedExt` of the zero class. -/
theorem isUnramifiedExt_zero' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K) :
    IsUnramifiedExt (k := k) (K := K) u
      (0 : Abelian.Ext (Rep.res (decompK (k := k) u).subtype M) (localUnitsK (k := k) u) r) :=
  ⟨0, by rw [Abelian.Ext.zero_comp]⟩


/-- `phiAt` of the zero class. -/
theorem phiAt_zero' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)}
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L)
      (0 : Abelian.Ext M (classesRepP k K) 1) h = 0 := by
  rw [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero]

/-- **E9c, the assembly.**  Same statement as `Work.SSGRoute.e9_glue_phiAt`. -/
theorem e9_glue_phiAt_assembly (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSarch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S)
    (hSram : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S →
        ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (zv : R → Abelian.Ext M (idelesK k K) 1)
    (hsupp : ∀ (v : R) (u : NK.GlobalCFT.Place K), (∀ σ : K ≃ₐ[k] K, σ • v.1 ≠ u) →
      extLoc u (zv v) = 0)
    (hunr : ∀ v : R, v.1 ∉ S → IsUnramifiedExt v.1 (extLoc v.1 (zv v)))
    (z : Abelian.Ext M (idelesK k K) 1) (hz : ∀ v : R, extLoc v.1 z = extLoc v.1 (zv v)) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1),
      (Function.support (fun v : R => phiAt (k := k) (K := K) (L := L)
          (extToClasses (zv v)) h)).Finite ∧
      phiAt (k := k) (K := K) (L := L) (extToClasses z) h =
        ∑ᶠ v : R, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
  classical
  intro L _instNF _instFD _instGal h
  -- the good finite Galois-stable set of places
  obtain ⟨T, hTfin, hTsmul, hST, hram⟩ := e9c_exists_good_T k K L S
  have hRfin : {v : R | v.1 ∈ T}.Finite :=
    hTfin.preimage (f := fun v : R => v.1) (fun a _ b _ hab => Subtype.eq hab)
  let V : Finset R := hRfin.toFinset
  have hVmem : ∀ v : R, v ∈ V ↔ v.1 ∈ T := fun v => Set.Finite.mem_toFinset hRfin
  let W : Abelian.Ext M (idelesRepP k K) 1 := ∑ v ∈ V, zv v
  let y : Abelian.Ext M (idelesRepP k K) 1 := z - W
  -- the sums over `V` have a single (resp. no) surviving term
  have hsum_rep : ∀ u : Place K, u ∈ T →
      ∑ v ∈ V, extLoc (k := k) (K := K) u (zv v)
        = extLoc (k := k) (K := K) u (zv (e9cRep R hR u)) := by
    intro u hu
    refine Finset.sum_eq_single (e9cRep R hR u) ?_ ?_
    · intro v _ hvne
      exact hsupp v u (fun σ hσ => hvne (e9cRep_eq_of_exists hR u v ⟨σ, hσ⟩))
    · intro hnot
      have hmem : (e9cRep R hR u).1 ∈ T := by
        obtain ⟨σ, hσ⟩ := e9cRep_spec (R := R) hR u
        rw [← hσ]
        exact hTsmul σ hu
      exact absurd ((hVmem _).mpr hmem) hnot
  have hsum_zero : ∀ u : Place K, u ∉ T →
      ∑ v ∈ V, extLoc (k := k) (K := K) u (zv v) = 0 := by
    intro u hu
    refine Finset.sum_eq_zero (fun v hv => ?_)
    exact hsupp v u (fun σ hσ => hu (by
      have hσu : σ • v.1 ∈ T := hTsmul σ ((hVmem v).mp hv)
      rwa [hσ] at hσu))
  -- the conjugacy: the components of `z` and of its orbit pieces agree
  have hconj : ∀ u : Place K,
      extLoc (k := k) (K := K) u z
        = extLoc (k := k) (K := K) u (zv (e9cRep R hR u)) := by
    intro u
    obtain ⟨σ, hσ⟩ := e9cRep_spec (R := R) hR u
    have h0 : extLoc (k := k) (K := K) (e9cRep R hR u).1 (z - zv (e9cRep R hR u)) = 0 := by
      rw [extLoc_sub', hz (e9cRep R hR u), sub_self]
    have h1 : extLoc (k := k) (K := K) u (z - zv (e9cRep R hR u)) = 0 := by
      have h2 := e9c_extLoc_conj_zero (k := k) (K := K)
        (z := z - zv (e9cRep R hR u)) (σ := σ⁻¹) (v := (e9cRep R hR u).1) h0
      rwa [show σ⁻¹ • (e9cRep R hR u).1 = u from by rw [← hσ, inv_smul_smul]] at h2
    rw [extLoc_sub'] at h1
    exact sub_eq_zero.mp h1
  -- y vanishes on `T`
  have hTz_y : ∀ u ∈ T, extLoc (k := k) (K := K) u y = 0 := by
    intro u hu
    change extLoc (k := k) (K := K) u (z - W) = 0
    rw [extLoc_sub', extLoc_sum' u V (fun v => zv v), hsum_rep u hu, hconj u, sub_self]
  -- y is unramified everywhere
  have hy_unram : ∀ u : Place K,
      IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u y) := by
    refine isUnramifiedExt_of_components_unramified M 1 R hR y ?_
    intro v
    change IsUnramifiedExt (k := k) (K := K) v.1 (extLoc (k := k) (K := K) v.1 (z - W))
    by_cases hvT : v.1 ∈ T
    · rw [extLoc_sub', extLoc_sum' v.1 V (fun v' => zv v'), hsum_rep v.1 hvT, hconj v.1,
        sub_self]
      exact isUnramifiedExt_zero' v.1
    · rw [extLoc_sub', extLoc_sum' v.1 V (fun v' => zv v'), hsum_zero v.1 hvT, hz v,
        sub_zero]
      exact hunr v (fun hmem => hvT (hST v.1 hmem))
  -- the global value of `y` vanishes
  have hy0 : phiAt (k := k) (K := K) (L := L) (extToClasses y) h = 0 :=
    e9c_phiAt_eq_zero_of_local L M h T y hTz_y (fun u _ => hy_unram u) hram
  -- the orbit pieces with `v ∉ T` are globally unramified, hence have vanishing value
  have hzv_unram : ∀ v : R, v.1 ∉ T → ∀ u : Place K,
      IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u (zv v)) := by
    intro v hvT
    refine isUnramifiedExt_of_components_unramified M 1 R hR (zv v) ?_
    intro v'
    by_cases hvv : v' = v
    · rw [hvv]
      exact hunr v (fun hmem => hvT (hST v.1 hmem))
    · have hzero : extLoc (k := k) (K := K) v'.1 (zv v) = 0 :=
        hsupp v v'.1 (fun σ hσ => hvv (((e9cRep_eq_of_exists hR v'.1 v ⟨σ, hσ⟩).trans
          (e9cRep_eq_of_exists hR v'.1 v' ⟨1, by simp⟩).symm).symm))
      rw [hzero]
      exact isUnramifiedExt_zero' v'.1
  have hFv0 : ∀ v : R, v.1 ∉ T →
      phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h = 0 := by
    intro v hvT
    refine e9c_phiAt_eq_zero_of_local L M h T (zv v) ?_ (fun u _ => hzv_unram v hvT u) hram
    intro u hu
    exact hsupp v u (fun σ hσ => hvT (by
      have hσu : σ⁻¹ • u ∈ T := hTsmul σ⁻¹ hu
      rwa [← hσ, inv_smul_smul] at hσu))
  -- the value of `W` is the sum of the values of the orbit pieces
  have hWval : phiAt (k := k) (K := K) (L := L) (extToClasses W) h
      = ∑ v ∈ V, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
    have hmap : ∀ s : Finset R,
        phiAt (k := k) (K := K) (L := L) (extToClasses (∑ v ∈ s, zv v)) h
          = ∑ v ∈ s, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
      intro s
      induction s using Finset.induction with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty, extToClasses_zero]
          exact phiAt_zero' L h
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, extToClasses_add, phiAt_add, ih]
    exact hmap V
  -- additivity in the class
  have hzy : phiAt (k := k) (K := K) (L := L) (extToClasses z) h
      = phiAt (k := k) (K := K) (L := L) (extToClasses W) h
        + phiAt (k := k) (K := K) (L := L) (extToClasses y) h := by
    rw [← show W + y = z from by change W + (z - W) = z; abel, extToClasses_add, phiAt_add]
  constructor
  · refine hRfin.subset ?_
    intro v hv
    by_contra hvT
    exact hv (hFv0 v (fun h => hvT h))
  · rw [hzy, hy0, add_zero, hWval]
    refine (finsum_eq_finsetSum_of_support_subset (s := V)
      (fun v : R => phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h) ?_).symm
    intro v hv
    by_contra hvT
    exact hv (hFv0 v (fun h => hvT (Finset.mem_coe.mpr ((hVmem v).mpr h))))

end Work.SSGRoute
