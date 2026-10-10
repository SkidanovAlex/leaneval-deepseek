import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e9_caseB_abelian
import Submission.Work.SSGRoute.e9_caseB_cocycle
import Submission.Work.SSGRoute.e9_caseB_unramified_arch
import Submission.Work.SSGRoute.e9_caseB_unramified_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField
open CategoryTheory SSGRoute.PTExt

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace E9CaseB

/-! ## Auxiliary lemmas comparing the two levels `Gal(L/k)` and `Gal(L/K)` -/

section Aux

variable {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional k K] [IsGalois k K]

/-- The `k`-algebra automorphism underlying a `K`-algebra automorphism lies in the kernel of the
restriction map `Gal(L/k) →* Gal(K/k)`. -/
lemma restrictScalars_mem_ker (σ : L ≃ₐ[K] L) :
    AlgEquiv.restrictScalars k σ ∈ (galRes k K L).ker := by
  rw [MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro x
  show (AlgEquiv.restrictNormal (AlgEquiv.restrictScalars k σ) K) x = x
  apply (algebraMap K L).injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
  exact σ.commutes x

/-- Every element of `ker (galRes : Gal(L/k) → Gal(K/k))` is the restriction of scalars of a
`K`-algebra automorphism of `L`. -/
lemma exists_restrictScalars_eq_of_mem_ker {n : L ≃ₐ[k] L} (hn : n ∈ (galRes k K L).ker) :
    ∃ σ : L ≃ₐ[K] L, AlgEquiv.restrictScalars k σ = n := by
  have hfix : ∀ x : K, n (algebraMap K L x) = algebraMap K L x := by
    intro x
    have h1 : (AlgEquiv.restrictNormal n K) x = x := by
      have h0 : (AlgEquiv.restrictNormalHom K n) x = x := by
        rw [MonoidHom.mem_ker.mp hn]
        rfl
      exact h0
    have h2 := AlgEquiv.restrictNormal_commutes n K x
    rw [h1] at h2
    exact h2.symm
  refine ⟨{ toFun := n
            invFun := n.symm
            left_inv := n.left_inv
            right_inv := n.right_inv
            map_mul' := n.map_mul
            map_add' := n.map_add
            commutes' := hfix }, ?_⟩
  apply AlgEquiv.ext
  intro x
  rfl

/-- The `k`-action and the `K`-action of an automorphism on the places of `L` agree on the
underlying `k`-algebra automorphism. -/
lemma restrictScalars_smul_place (σ : L ≃ₐ[K] L) (w' : NK.GlobalCFT.Place L) :
    (AlgEquiv.restrictScalars k σ) • w' = σ • w' := by
  have hinf : ∀ u : NumberField.InfinitePlace L,
      (AlgEquiv.restrictScalars k σ) • u = σ • u := fun u => rfl
  have hfin : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      NK.GlobalCFT.Place.smulHeightOneSpectrum (AlgEquiv.restrictScalars k σ) q =
        NK.GlobalCFT.Place.smulHeightOneSpectrum σ q := by
    intro q
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal,
      NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
    congr 1
  cases w' with
  | inl u =>
      rw [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.smul_ofInfinite]
      exact congrArg Sum.inl (hinf u)
  | inr q => rw [NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.smul_ofFinite, hfin q]

/-- Stabilizers of places are transported by `AlgEquiv.restrictScalars`. -/
lemma restrictScalars_mem_stabilizer {w' : NK.GlobalCFT.Place L} {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w') :
    AlgEquiv.restrictScalars k τ ∈ MulAction.stabilizer (L ≃ₐ[k] L) w' := by
  rw [MulAction.mem_stabilizer_iff] at hτ ⊢
  rw [restrictScalars_smul_place, hτ]

end Aux

section Aux2

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]

/-- `IsInertiaAt` is membership in the ideal-theoretic inertia subgroup. -/
lemma isInertiaAt_iff_mem_inertia
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) :
    IsInertiaAt q' σ ↔ σ ∈ Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal := by
  rw [Ideal.inertia, AddSubgroup.mem_inertia]
  refine forall_congr' fun x => ?_
  have key : ((σ • x - x : NumberField.RingOfIntegers L) : L) = σ (x : L) - (x : L) := by
    have h : algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x) -
          algebraMap (NumberField.RingOfIntegers L) L x := map_sub _ _ _
    rw [show ((σ • x - x : NumberField.RingOfIntegers L) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) from rfl, h]
    congr 1
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (v := q') _

/-- The inertia condition is preserved by `AlgEquiv.restrictScalars`. -/
lemma isInertiaAt_restrictScalars {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (q' : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal) :
    IsInertiaAt q' (AlgEquiv.restrictScalars k σ) := by
  rw [isInertiaAt_iff_mem_inertia, Ideal.inertia, AddSubgroup.mem_inertia] at ⊢
  intro x
  exact hσ x

end Aux2

end E9CaseB

open E9CaseB in
/-- **Case B of the finite-`S` continuity.** Let `H` be the maximal unramified abelian extension of
`K` (hypothesis `hH`: every unramified abelian `E/K` embeds into `H`) and let `W` be a finite set of
places of `K` which *witnesses* every nontrivial unramified abelian `E/K` inside `H`: for each such
`E` there is `v ∈ W` and a place `Wp` of `E` above `v` with nontrivial decomposition group.  If `h`
at a finite Galois level `L ⊇ K` is unramified at every finite place of `L`, trivial at every
archimedean place of `L` and trivial at every place of `L` above `W`, then `h` descends: its
restriction to `N = ker(galRes : Gal(L/k) → Gal(K/k))` vanishes.

Route. Take a cocycle representative `z` of `h`; since `N` acts trivially on `M`, `z|N : N → M` is
the canonical homomorphism attached to `h|N` (independent of the representative).  If it were
nonzero, its kernel `ker ⊆ N` would be normal in `Gal(L/k)` (using the cocycle identity for
`z(g n g⁻¹)`), so `E := L^ker` is a Galois extension of `K` with `Gal(E/K) ≅ N/ker ≅ im ⊆ M`
abelian and nontrivial, unramified over `K` at both finite and infinite places (the inertia
subgroups of `L/K` lie in `ker` because `h` is unramified, and the archimedean decomposition groups
because `h` is trivial there), hence `E` embeds into `H` and `hW` produces `v ∈ W` and a place of
`E` above `v` with nontrivial decomposition group.  Lifting that decomposition group along
`Gal(L/K) → Gal(E/K)` (surjective, decomposition groups of subextensions are the images of
decomposition groups) gives `n ∈ N ∩ D_{w'}` for a place `w'` of `L` above `v` with `z(n) ≠ 0`,
whence `h|_{D_{w'}} ≠ 0`, contradicting `htriv`. -/
theorem e9_caseB_descent (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M]
    (H : Type) [Field H] [NumberField H] [Algebra K H] [FiniteDimensional K H]
    (hH : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
      [IsGalois K E],
      IsMulCommutative (E ≃ₐ[K] E) → differentIdeal (𝓞 K) (𝓞 E) = ⊤ →
      IsUnramifiedAtInfinitePlaces K E → Nonempty (E →ₐ[K] H))
    (W : Finset (NK.GlobalCFT.Place K))
    (hW : ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
        [IsGalois K E],
        IsMulCommutative (E ≃ₐ[K] E) → differentIdeal (𝓞 K) (𝓞 E) = ⊤ →
        IsUnramifiedAtInfinitePlaces K E → Nonempty (E →ₐ[K] H) →
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
  -- ## Step 9: `hH` and `hW`
  obtain ⟨embH⟩ := hH ↥E hEab hunrfin hunrarch
  obtain ⟨v, Wp, hvW, hWp, hWpstab⟩ := hW ↥E hEab hunrfin hunrarch ⟨embH⟩ hEfin
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
