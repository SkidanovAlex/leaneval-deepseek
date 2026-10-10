import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e9_caseB_descent
import Submission.Work.SSGRoute.e9_witness_of_classGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField
open CategoryTheory SSGRoute.PTExt

/-- **Case B of the finite-`S` continuity, in the form that does not mention the maximal
unramified abelian extension.**  This is the statement of `e9_caseB_descent` with the pair
`(H, hH, hW)` replaced by the single hypothesis `hW` about the witness set `W`: the conclusion that
the restriction of `h` to `N = ker(galRes : Gal(L/k) → Gal(K/k))` vanishes follows directly, because
the only use of `H` in that proof was to embed the extension `E = L^ker` into a fixed field so that
`hW` could be applied to it — with the witnesses stated for all abelian unramified `E/K` rather than
only those embedding into `H`, the argument applies `hW` to `E = L^ker` directly.  (In the proof of
`e9_caseB_descent`, `hEab` must be bound with `haveI := hEab` before applying the wide `hW`, whose
abelianness hypothesis is a typeclass argument.) -/
theorem e9_caseB_descent_wide (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M]
    (W : Finset (NK.GlobalCFT.Place K))
    (hW : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
        [IsGalois K E] [IsMulCommutative (E ≃ₐ[K] E)],
        differentIdeal (𝓞 K) (𝓞 E) = ⊤ → IsUnramifiedAtInfinitePlaces K E →
        Module.finrank K E ≠ 1 →
        ∃ (v : NK.GlobalCFT.Place K) (Wp : NK.GlobalCFT.Place E),
          v ∈ W ∧ NK.GlobalCFT.Place.LiesOver Wp v ∧
            MulAction.stabilizer (E ≃ₐ[K] E) Wp ≠ ⊥)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M) 1)
    (hunr : ∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      IsUnramifiedClassAt q' h)
    (harch : ∀ w' : NK.GlobalCFT.Place L,
      (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        w' ≠ NK.GlobalCFT.Place.ofFinite q') →
        extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0)
    (htriv : ∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ W, NK.GlobalCFT.Place.LiesOver w' v) →
      extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) :
    extHRestrict (galRes k K L).ker h = 0 := by
  classical
  -- ## Step 0: the cocycle representative
  obtain ⟨z, hz⟩ : ∃ z : ↥(groupCohomology.cocycles₁ (Rep.res (galRes k K L) M)),
      (groupCohomology.H1π (Rep.res (galRes k K L) M)).hom z =
        (eCoh 1 (L ≃ₐ[k] L) (Rep.res (galRes k K L) M)).symm h :=
    groupCohomology.H1_induction_on
      ((eCoh 1 (L ≃ₐ[k] L) (Rep.res (galRes k K L) M)).symm h) (fun w => ⟨w, rfl⟩)
  have hrepr : h = eCoh 1 (L ≃ₐ[k] L) (Rep.res (galRes k K L) M)
      ((groupCohomology.H1π (Rep.res (galRes k K L) M)).hom z) := by
    rw [hz, AddEquiv.apply_symm_apply]
  -- ## Step 1: the cocycle criterion at every subgroup
  have hcrit : ∀ D : Subgroup (L ≃ₐ[k] L),
      extHRestrict D h = 0 ↔ ∃ m : ↥(Rep.res (galRes k K L) M),
        ∀ d ∈ D, (z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M)) d
          = (Rep.res (galRes k K L) M).ρ d m - m := by
    intro D
    rw [hrepr]
    exact e9_caseB_cocycle (Rep.res (galRes k K L) M) D z
  -- ## Step 2: the action of `ker (galRes)` on the coefficients is trivial
  have hNtriv : ∀ (n : L ≃ₐ[k] L), n ∈ (galRes k K L).ker →
      ∀ m : ↥(Rep.res (galRes k K L) M), (Rep.res (galRes k K L) M).ρ n m = m := by
    intro n hn m
    show (M.ρ (galRes k K L n)) m = m
    rw [MonoidHom.mem_ker.mp hn, map_one]
    rfl
  -- ## Step 3: if the restriction to `N` vanished, the cocycle would vanish on `N`
  by_contra hN
  have hex : ∃ n ∈ (galRes k K L).ker,
      (z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M)) n ≠ 0 := by
    by_contra h
    push_neg at h
    exact hN ((hcrit _).mpr ⟨0, fun d hd => by
      rw [h d hd, hNtriv d hd 0, sub_self]⟩)
  -- ## Step 4: the subgroup of `Gal(L/K)` on which the cocycle vanishes
  let φ : (L ≃ₐ[K] L) →* Multiplicative ↥(Rep.res (galRes k K L) M) :=
    { toFun := fun σ => Multiplicative.ofAdd
        ((z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M))
          (AlgEquiv.restrictScalars k σ))
      map_one' := by
        show Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _) (AlgEquiv.restrictScalars k 1)) = 1
        rw [show AlgEquiv.restrictScalars k (1 : L ≃ₐ[K] L) = 1 from rfl]
        rw [groupCohomology.cocycles₁_map_one]
        rfl
      map_mul' := by
        intro σ τ
        have hι : AlgEquiv.restrictScalars k (σ * τ) =
            AlgEquiv.restrictScalars k σ * AlgEquiv.restrictScalars k τ := by
          apply AlgEquiv.ext
          intro x
          rfl
        have hker : AlgEquiv.restrictScalars k σ ∈ (galRes k K L).ker :=
          E9CaseB.restrictScalars_mem_ker σ
        have hc := (groupCohomology.mem_cocycles₁_iff
          (z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M))).mp z.2
          (AlgEquiv.restrictScalars k σ) (AlgEquiv.restrictScalars k τ)
        have h2 : (Rep.res (galRes k K L) M).ρ (AlgEquiv.restrictScalars k σ)
            ((z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M))
              (AlgEquiv.restrictScalars k τ))
            = (z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M))
              (AlgEquiv.restrictScalars k τ) :=
          hNtriv _ hker _
        show Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _)
            (AlgEquiv.restrictScalars k (σ * τ)))
          = Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _) (AlgEquiv.restrictScalars k σ))
            * Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _) (AlgEquiv.restrictScalars k τ))
        rw [hι, hc, h2]
        rw [add_comm]
        rfl }
  let E : IntermediateField K L := IntermediateField.fixedField φ.ker
  have hEfix : E.fixingSubgroup = φ.ker := IntermediateField.fixingSubgroup_fixedField φ.ker
  -- ## Step 5: `φ` is nontrivial
  have hφ_ne : ∃ σ : L ≃ₐ[K] L, φ σ ≠ 1 := by
    obtain ⟨n, hn, hnz⟩ := hex
    obtain ⟨σ, hσ⟩ := E9CaseB.exists_restrictScalars_eq_of_mem_ker hn
    refine ⟨σ, fun h1 => hnz ?_⟩
    have h2 : Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _)
        (AlgEquiv.restrictScalars k σ)) = 1 := h1
    have h3 := congrArg Multiplicative.toAdd h2
    simpa [hσ] using h3
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  -- ## Step 6: `E/K` is abelian and nontrivial
  obtain ⟨hEab, hEfin⟩ := e9_caseB_abelian φ hφ_ne
  -- ## Step 7: the containments
  have hinertia : ∀ (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L)),
      Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal ≤ E.fixingSubgroup := by
    intro q' σ hσ
    rw [hEfix]
    have hI : IsInertiaAt q' (AlgEquiv.restrictScalars k σ) :=
      E9CaseB.isInertiaAt_restrictScalars q' hσ
    have hD : extHRestrict (Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal) h = 0 :=
      hunr q' _ (fun τ hτ => (E9CaseB.isInertiaAt_iff_mem_inertia q' τ).mpr hτ)
    obtain ⟨m, hm⟩ := (hcrit _).mp hD
    have hmem : AlgEquiv.restrictScalars k σ ∈ Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal :=
      (E9CaseB.isInertiaAt_iff_mem_inertia q' _).mp hI
    have h1 := hm _ hmem
    rw [hNtriv _ (E9CaseB.restrictScalars_mem_ker σ) m, sub_self] at h1
    show σ ∈ φ.ker
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _) (AlgEquiv.restrictScalars k σ)) = 1
    rw [h1]
    rfl
  have hstab : ∀ u : NumberField.InfinitePlace L,
      MulAction.stabilizer (L ≃ₐ[K] L) u ≤ E.fixingSubgroup := by
    intro u σ hσ
    rw [hEfix]
    have hσu : (σ : L ≃ₐ[K] L) • u = u := MulAction.mem_stabilizer_iff.mp hσ
    have hD : extHRestrict
        (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)) h = 0 :=
      harch _ (fun q' h => absurd h (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite u q'))
    obtain ⟨m, hm⟩ := (hcrit _).mp hD
    have hmem : AlgEquiv.restrictScalars k σ ∈
        MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u) := by
      rw [MulAction.mem_stabilizer_iff]
      rw [E9CaseB.restrictScalars_smul_place, NK.GlobalCFT.Place.smul_ofInfinite, hσu]
    have h1 := hm _ hmem
    rw [hNtriv _ (E9CaseB.restrictScalars_mem_ker σ) m, sub_self] at h1
    show σ ∈ φ.ker
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _) (AlgEquiv.restrictScalars k σ)) = 1
    rw [h1]
    rfl
  -- ## Step 8: `E/K` is unramified everywhere
  have hunrfin : differentIdeal (𝓞 K) (𝓞 ↥E) = ⊤ :=
    e9_caseB_unramified_finite E hinertia
  have hunrarch : IsUnramifiedAtInfinitePlaces K ↥E := e9_caseB_unramified_arch E hstab
  -- ## Step 9: the wide `hW` applied directly to `E = L^ker`
  haveI := hEab
  obtain ⟨v, Wp, hvW, hWp, hWpstab⟩ := hW ↥E hunrfin hunrarch hEfin
  -- ## Step 10: the witness `Wp` is a finite place
  cases Wp with
  | inl Wp' =>
      exfalso
      have hstab_eq : MulAction.stabilizer (↥E ≃ₐ[K] ↥E)
          (NK.GlobalCFT.Place.ofInfinite Wp') =
          MulAction.stabilizer (↥E ≃ₐ[K] ↥E) Wp' := by
        ext σ
        rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
        rw [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
      have hbot : MulAction.stabilizer (↥E ≃ₐ[K] ↥E) (NK.GlobalCFT.Place.ofInfinite Wp') = ⊥ := by
        rw [hstab_eq]
        exact (NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot (k := K) (K := ↥E)
          (w := Wp')).mp (NumberField.InfinitePlace.isUnramified (k := K) (K := ↥E) Wp')
      exact hWpstab hbot
  | inr Wp' =>
      have hvfin : NK.GlobalCFT.Place.IsFinite v :=
        (NK.GlobalCFT.Place.isFinite_of_liesOver hWp).mp (NK.GlobalCFT.Place.isFinite_ofFinite Wp')
      obtain ⟨Q, hQ⟩ : ∃ Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          v = NK.GlobalCFT.Place.ofFinite Q := NK.GlobalCFT.Place.isFinite_iff.mp hvfin
      subst hQ
      have hWplies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite Wp')
          (NK.GlobalCFT.Place.ofFinite Q) := hWp
      rw [NK.GlobalCFT.Place.liesOver_iff] at hWplies
      have hWp'lies : Wp'.asIdeal.LiesOver Q.asIdeal := by
        rcases hWplies with ⟨w', v', hw, _, _⟩ | ⟨q₀, Q₀, hw, hv, h⟩
        · exact absurd hw Sum.inr_ne_inl
        · rw [NK.GlobalCFT.Place.ofFinite_inj] at hw hv
          subst hw
          subst hv
          exact h
      obtain ⟨q', hq'⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
        (K := ↥E) (L := L) Wp'
      have hq'P : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Wp') := NK.GlobalCFT.Place.liesOver_ofFinite hq'
      let f : MulAction.stabilizer (L ≃ₐ[K] L) (NK.GlobalCFT.Place.ofFinite q') →*
          decompK (k := K) (K := ↥E) (NK.GlobalCFT.Place.ofFinite Wp') :=
        { toFun := fun τ => ⟨AlgEquiv.restrictNormalHom ↥E (τ : L ≃ₐ[K] L), by
            rw [MulAction.mem_stabilizer_iff]
            have hl := NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := ↥E) (L := L)
              (τ : L ≃ₐ[K] L) (AlgEquiv.restrictNormalHom ↥E (τ : L ≃ₐ[K] L))
              (fun y => AlgEquiv.restrictNormal_commutes (τ : L ≃ₐ[K] L) ↥E y) hq'P
            rw [MulAction.mem_stabilizer_iff.mp τ.2] at hl
            exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hl hq'P⟩
          map_one' := by
            apply Subtype.ext
            exact map_one _
          map_mul' := by
            intro a b
            apply Subtype.ext
            exact map_mul _ _ _ }
      have hf : ∀ σ, ((f σ : decompK (k := K) (K := ↥E)
          (NK.GlobalCFT.Place.ofFinite Wp')) : ↥E ≃ₐ[K] ↥E) =
          galRes K ↥E L (σ : L ≃ₐ[K] L) := fun σ => rfl
      obtain ⟨s, hs, hsne⟩ : ∃ s : ↥E ≃ₐ[K] ↥E,
          s ∈ MulAction.stabilizer (↥E ≃ₐ[K] ↥E) (NK.GlobalCFT.Place.ofFinite Wp') ∧
            s ≠ 1 := by
        by_contra h
        apply hWpstab
        rw [Subgroup.eq_bot_iff_forall]
        intro s hs
        by_contra hs1
        exact h ⟨s, hs, hs1⟩
      obtain ⟨τ, hτ⟩ := decompK_restrict_surjective K ↥E (NK.GlobalCFT.Place.ofFinite Wp') L
        (NK.GlobalCFT.Place.ofFinite q') hq'P f hf ⟨s, hs⟩
      have hτmem : (τ : L ≃ₐ[K] L) ∈ MulAction.stabilizer (L ≃ₐ[K] L)
          (NK.GlobalCFT.Place.ofFinite q') := τ.2
      have hτs : AlgEquiv.restrictNormalHom ↥E (τ : L ≃ₐ[K] L) = s := by
        have := congrArg Subtype.val hτ
        simpa [f] using this
      have hτnot : (τ : L ≃ₐ[K] L) ∉ φ.ker := by
        intro hmem
        have h1 : (τ : L ≃ₐ[K] L) ∈ E.fixingSubgroup := by
          rw [hEfix]; exact hmem
        have h2 : AlgEquiv.restrictNormalHom ↥E (τ : L ≃ₐ[K] L) = 1 := by
          have h1' : (τ : L ≃ₐ[K] L) ∈ (AlgEquiv.restrictNormalHom ↥E).ker := by
            rw [IntermediateField.restrictNormalHom_ker (E := E)]
            exact h1
          exact MonoidHom.mem_ker.mp h1'
        rw [hτs] at h2
        exact hsne h2
      have hzτ : (z : (L ≃ₐ[k] L) → ↥(Rep.res (galRes k K L) M))
          (AlgEquiv.restrictScalars k (τ : L ≃ₐ[K] L)) ≠ 0 := by
        intro hz0
        apply hτnot
        rw [MonoidHom.mem_ker]
        show Multiplicative.ofAdd ((z : (L ≃ₐ[k] L) → _)
          (AlgEquiv.restrictScalars k (τ : L ≃ₐ[K] L))) = 1
        rw [hz0]
        rfl
      haveI hIL1 : q'.asIdeal.LiesOver Wp'.asIdeal := hq'
      haveI hIL2 : Wp'.asIdeal.LiesOver Q.asIdeal := hWp'lies
      have hlies' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Q) :=
        NK.GlobalCFT.Place.liesOver_ofFinite
          (Ideal.LiesOver.trans q'.asIdeal Wp'.asIdeal Q.asIdeal)
      have htriv' : extHRestrict
          (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q')) h = 0 :=
        htriv _ ⟨NK.GlobalCFT.Place.ofFinite Q, hvW, hlies'⟩
      obtain ⟨m, hm⟩ := (hcrit _).mp htriv'
      have hmem : AlgEquiv.restrictScalars k (τ : L ≃ₐ[K] L) ∈
          MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') :=
        E9CaseB.restrictScalars_mem_stabilizer hτmem
      have h1 := hm _ hmem
      rw [hNtriv _ (E9CaseB.restrictScalars_mem_ker (τ : L ≃ₐ[K] L)) m, sub_self] at h1
      exact hzτ h1

end Work.SSGRoute
