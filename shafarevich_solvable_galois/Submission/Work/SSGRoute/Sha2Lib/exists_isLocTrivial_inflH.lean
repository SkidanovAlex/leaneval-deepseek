import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.Sha2Lib.LevelLocTrivial
import Submission.Work.SSGRoute.Sha2Lib.Sha2InflHelpers
import Submission.Work.SSGRoute.Sha2Lib.chebotarev_element_stabilizer
import Submission.Work.SSGRoute.eCoh_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A locally trivial class at a level `L` comes from a locally trivial class at `K`

`Work.SSGRoute.Sha2Lib.exists_isLocTrivial_inflH`: for a tower `k ⊆ K ⊆ L` of number fields with
`L/k` and `K/k` Galois, every class `h ∈ H¹(Gal(L/k), M)` (with `M` a `Gal(K/k)`-module) which is
locally trivial at every place of `L` is the inflation of a class `h' ∈ H¹(Gal(K/k), M)` which is
locally trivial at every place of `K`.

The proof is Čebotarev: a cocycle `z` representing `h` is a coboundary on the decomposition group
`D_w ⊆ Gal(L/k)` of every place `w` of `L`.  Every element of `N = Gal(L/K)` lies in some `D_w`
(Čebotarev, `chebotarev_element_stabilizer`), and `N` acts trivially on the coefficients, so `z`
vanishes on `N`; hence `z` descends to a cocycle `z'` on `Gal(K/k)`.  Finally, for every place `v`
of `K`, the restriction map `D_w → D_v` is onto (`decomp_group_restrict_surjective` for finite `v`,
`infinite_place_stabilizer_trivial_or_two` plus Čebotarev for archimedean `v`), so `z'` is a
coboundary on `D_v`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.Sha2Lib

theorem exists_isLocTrivial_inflH
    (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1)
    (hh : SSGRoute.PTExt.IsLocTrivialLevel (k := k) (K := K) (L := L) h) :
    ∃ h' : SSGRoute.PTExt.extH M 1,
      SSGRoute.PTExt.IsLocTrivial (k := k) (K := K) h' ∧
      SSGRoute.PTExt.inflH (k := k) (K := K) (L := L) h' = h := by
  classical
  let f : (L ≃ₐ[k] L) →* (K ≃ₐ[k] K) := SSGRoute.PTExt.galRes k K L
  let B : Rep SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) := Rep.res f M
  have hfsurj : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L)
  -- (1) the level-`L` class, in Mathlib's group cohomology
  obtain ⟨y, hy⟩ : ∃ y : groupCohomology B 1,
      SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) B y = h :=
    ⟨(SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) B).symm h,
      (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) B).apply_symm_apply h⟩
  -- (2) a cocycle representative
  obtain ⟨z, hz⟩ : ∃ z : ↥(groupCohomology.cocycles₁ B),
      (groupCohomology.H1π B) z = y :=
    groupCohomology.H1_induction_on y fun z => ⟨z, rfl⟩
  have hzcoc : ∀ x y' : L ≃ₐ[k] L,
      (z : (L ≃ₐ[k] L) → ↥B) (x * y') = B.ρ x ((z : (L ≃ₐ[k] L) → ↥B) y')
        + (z : (L ≃ₐ[k] L) → ↥B) x :=
    fun x y' => (groupCohomology.mem_cocycles₁_iff (z : (L ≃ₐ[k] L) → ↥B)).mp z.2 x y'
  -- (3) the kernel of `f` acts trivially on `B`
  have htriv : ∀ n ∈ f.ker, ∀ m : ↥B, B.ρ n m = m := by
    intro n hn m
    have h1 : f n = 1 := hn
    rw [show (Rep.res f M).ρ n = M.ρ (f n) from rfl, h1, map_one]
    rfl
  -- (4) the local coboundary data at every place of `L`
  have hloc : ∀ w : NK.GlobalCFT.Place L, ∃ m : ↥B,
      ∀ σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) w,
        (z : (L ≃ₐ[k] L) → ↥B) σ = B.ρ σ m - m := by
    intro w
    set D : Subgroup (L ≃ₐ[k] L) := MulAction.stabilizer (L ≃ₐ[k] L) w with hD
    have h0 : SSGRoute.PTExt.extHRestrict D h = 0 := hh w
    have key : SSGRoute.PTExt.extHRestrict D h
        = SSGRoute.PTExt.eCoh 1 D (Rep.res D.subtype B)
            ((groupCohomology.map D.subtype
              (CategoryStruct.id (Rep.res D.subtype B)) 1).hom y) := by
      rw [← hy]
      rw [Work.SSGRoute.eCoh_map 1 (L ≃ₐ[k] L) D D.subtype B (Rep.res D.subtype B)
        (CategoryStruct.id (Rep.res D.subtype B)) y]
      rfl
    have h1 : (groupCohomology.map D.subtype
        (CategoryStruct.id (Rep.res D.subtype B)) 1).hom y = 0 := by
      apply (SSGRoute.PTExt.eCoh 1 D (Rep.res D.subtype B)).injective
      rw [← key, h0, map_zero]
    rw [← hz] at h1
    obtain ⟨m, hm⟩ := (map_H1pi_eq_zero_iff_exists_coboundary D.subtype B z
      (pullbackCocycles₁ D.subtype B z) (fun _ => rfl)).mp h1
    refine ⟨m, fun σ hσ => ?_⟩
    have h2 := hm ⟨σ, hσ⟩
    rwa [pullbackCocycles₁_apply] at h2
  -- (5) Čebotarev: `z` vanishes on `ker f`
  have hzero : ∀ n ∈ f.ker, (z : (L ≃ₐ[k] L) → ↥B) n = 0 := by
    intro n hn
    obtain ⟨w, hw⟩ := chebotarev_element_stabilizer k L n
    obtain ⟨m, hm⟩ := hloc w
    rw [hm n hw, htriv n hn m, sub_self]
  have hker_inv : ∀ g ∈ f.ker, ∀ s : L ≃ₐ[k] L,
      (z : (L ≃ₐ[k] L) → ↥B) (g * s) = (z : (L ≃ₐ[k] L) → ↥B) s := by
    intro g hg s
    rw [hzcoc g s, htriv g hg ((z : (L ≃ₐ[k] L) → ↥B) s), hzero g hg, add_zero]
  -- (6) the descended cocycle on `Gal(K/k)`
  let zQ : ↥(groupCohomology.cocycles₁ M) :=
    ⟨fun q => (z : (L ≃ₐ[k] L) → ↥B) (Classical.choose (hfsurj q)), by
      rw [groupCohomology.mem_cocycles₁_iff]
      intro a b
      let σa := Classical.choose (hfsurj a)
      let σb := Classical.choose (hfsurj b)
      let σab := Classical.choose (hfsurj (a * b))
      have hfa : f σa = a := Classical.choose_spec (hfsurj a)
      have hfb : f σb = b := Classical.choose_spec (hfsurj b)
      have hfab : f σab = a * b := Classical.choose_spec (hfsurj (a * b))
      have hg : σab * (σa * σb)⁻¹ ∈ f.ker := by
        show f (σab * (σa * σb)⁻¹) = 1
        rw [map_mul, map_inv, map_mul, hfab, hfa, hfb, mul_inv_cancel]
      have hZ : (z : (L ≃ₐ[k] L) → ↥B) σab = (z : (L ≃ₐ[k] L) → ↥B) (σa * σb) := by
        have hdec : σab = (σab * (σa * σb)⁻¹) * (σa * σb) := by group
        conv_lhs => rw [hdec]
        exact hker_inv _ hg _
      calc (fun q => (z : (L ≃ₐ[k] L) → ↥B) (Classical.choose (hfsurj q))) (a * b)
          = (z : (L ≃ₐ[k] L) → ↥B) σab := rfl
        _ = (z : (L ≃ₐ[k] L) → ↥B) (σa * σb) := hZ
        _ = B.ρ σa ((z : (L ≃ₐ[k] L) → ↥B) σb) + (z : (L ≃ₐ[k] L) → ↥B) σa := hzcoc σa σb
        _ = M.ρ a ((z : (L ≃ₐ[k] L) → ↥B) σb) + (z : (L ≃ₐ[k] L) → ↥B) σa := by
              rw [show B.ρ σa = M.ρ (f σa) from rfl, hfa]
        _ = M.ρ a ((fun q => (z : (L ≃ₐ[k] L) → ↥B) (Classical.choose (hfsurj q))) b)
              + (fun q => (z : (L ≃ₐ[k] L) → ↥B) (Classical.choose (hfsurj q))) a := rfl
      ⟩
  -- (7) `z` is the pullback of `zQ`
  have hzQ : ∀ x : L ≃ₐ[k] L, (z : (L ≃ₐ[k] L) → ↥B) x = (zQ : (K ≃ₐ[k] K) → ↥M) (f x) := by
    intro x
    have hg : x * (Classical.choose (hfsurj (f x)))⁻¹ ∈ f.ker := by
      show f (x * (Classical.choose (hfsurj (f x)))⁻¹) = 1
      rw [map_mul, map_inv, Classical.choose_spec (hfsurj (f x)), mul_inv_cancel]
    have hdec : x = (x * (Classical.choose (hfsurj (f x)))⁻¹) * (Classical.choose (hfsurj (f x))) :=
      by group
    have hL : (z : (L ≃ₐ[k] L) → ↥B) x
        = (z : (L ≃ₐ[k] L) → ↥B) (Classical.choose (hfsurj (f x))) := by
      conv_lhs => rw [hdec]
      exact hker_inv _ hg _
    rw [hL]
    rfl
  -- (8) the class of `zQ` inflates to the class of `z`
  have hmap : (groupCohomology.map f (CategoryStruct.id (Rep.res f M)) 1).hom
      ((groupCohomology.H1π M) zQ) = (groupCohomology.H1π B) z :=
    map_H1pi_eq_of_comp f M zQ z hzQ
  -- (9) the candidate
  refine ⟨SSGRoute.PTExt.eCoh 1 (K ≃ₐ[k] K) M ((groupCohomology.H1π M) zQ), ?_, ?_⟩
  · rw [SSGRoute.PTExt.IsLocTrivial, SSGRoute.PTExt.IsLocTrivialOn]
    intro v
    set D : Subgroup (K ≃ₐ[k] K) := SSGRoute.PTExt.decompK (k := k) v with hD
    have hcbQ : ∃ m : ↥M, ∀ x : D, (zQ : (K ≃ₐ[k] K) → ↥M) (x : K ≃ₐ[k] K)
        = (M.ρ (x : K ≃ₐ[k] K)) m - m := by
      cases v with
      | inl v₀ =>
        have hstab : MulAction.stabilizer (K ≃ₐ[k] K) (NK.GlobalCFT.Place.ofInfinite v₀)
            = MulAction.stabilizer (K ≃ₐ[k] K) v₀ := by
          ext τ
          rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
            NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
        rcases infinite_place_stabilizer_trivial_or_two k K v₀ with hbot | ⟨c, hc⟩
        · refine ⟨0, fun x => ?_⟩
          have hmem : (x : K ≃ₐ[k] K) ∈ MulAction.stabilizer (K ≃ₐ[k] K) v₀ := by
            rw [← hstab]
            exact x.2
          have hx : (x : K ≃ₐ[k] K) = 1 := by
            rw [hbot] at hmem
            simpa using hmem
          change (zQ : (K ≃ₐ[k] K) → ↥M) (x : K ≃ₐ[k] K)
            = (M.ρ (x : K ≃ₐ[k] K)) 0 - 0
          rw [hx]
          simp
        · obtain ⟨c', hc'⟩ : ∃ c' : L ≃ₐ[k] L, f c' = c := hfsurj c
          obtain ⟨w, hw⟩ := chebotarev_element_stabilizer k L c'
          obtain ⟨m, hm⟩ := hloc w
          refine ⟨m, fun x => ?_⟩
          have hmem : (x : K ≃ₐ[k] K) ∈ MulAction.stabilizer (K ≃ₐ[k] K) v₀ := by
            rw [← hstab]
            exact x.2
          have hx : (x : K ≃ₐ[k] K) = 1 ∨ (x : K ≃ₐ[k] K) = c := (hc _).mp hmem
          rcases hx with hx1 | hxc
          · change (zQ : (K ≃ₐ[k] K) → ↥M) (x : K ≃ₐ[k] K)
              = (M.ρ (x : K ≃ₐ[k] K)) m - m
            rw [hx1]
            have h1 : (zQ : (K ≃ₐ[k] K) → ↥M) 1 = 0 :=
              groupCohomology.cocycles₁_map_one zQ
            rw [h1]
            simp
          · change (zQ : (K ≃ₐ[k] K) → ↥M) (x : K ≃ₐ[k] K)
              = (M.ρ (x : K ≃ₐ[k] K)) m - m
            rw [hxc]
            rw [← hc', ← hzQ c', hm c' hw]
            rfl
      | inr q =>
        have hne : Nonempty (q.asIdeal.primesOver (NumberField.RingOfIntegers L)) :=
          Ideal.nonempty_primesOver q.asIdeal
        obtain ⟨P⟩ := hne
        let q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
          ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver q.ne_bot P.2⟩
        have hq' : (q'.asIdeal).LiesOver q.asIdeal := P.2.2
        obtain ⟨m, hm⟩ := hloc (NK.GlobalCFT.Place.ofFinite q')
        refine ⟨m, fun x => ?_⟩
        obtain ⟨σ, hσmem, hσres⟩ :=
          decomp_group_restrict_surjective k K L q q' hq' (x : K ≃ₐ[k] K) x.2
        change (zQ : (K ≃ₐ[k] K) → ↥M) (x : K ≃ₐ[k] K)
          = (M.ρ (x : K ≃ₐ[k] K)) m - m
        have hx_eq : (x : K ≃ₐ[k] K) = f σ := hσres.symm
        rw [hx_eq, ← hzQ σ, hm σ hσmem]
        rfl
    obtain ⟨m, hm⟩ := hcbQ
    have hcb : ∃ m : ↥(Rep.res D.subtype M), ∀ x : D,
        (pullbackCocycles₁ D.subtype M zQ : D → ↥(Rep.res D.subtype M)) x
          = ((Rep.res D.subtype M).ρ x) m - m :=
      ⟨m, fun x => by rw [pullbackCocycles₁_apply]; exact hm x⟩
    have hzero' : (groupCohomology.map D.subtype
        (CategoryStruct.id (Rep.res D.subtype M)) 1).hom
          ((groupCohomology.H1π M) zQ) = 0 :=
      (map_H1pi_eq_zero_iff_exists_coboundary D.subtype M zQ
        (pullbackCocycles₁ D.subtype M zQ) (fun _ => rfl)).mpr hcb
    have key : SSGRoute.PTExt.extHRestrict D
          (SSGRoute.PTExt.eCoh 1 (K ≃ₐ[k] K) M ((groupCohomology.H1π M) zQ))
        = SSGRoute.PTExt.eCoh 1 D (Rep.res D.subtype M)
            ((groupCohomology.map D.subtype
              (CategoryStruct.id (Rep.res D.subtype M)) 1).hom
                ((groupCohomology.H1π M) zQ)) := by
      rw [Work.SSGRoute.eCoh_map 1 (K ≃ₐ[k] K) D D.subtype M (Rep.res D.subtype M)
        (CategoryStruct.id (Rep.res D.subtype M)) ((groupCohomology.H1π M) zQ)]
      rfl
    rw [key, hzero', map_zero]
  · show SSGRoute.PTExt.extHMap f (𝟙 (Rep.res f M))
        (SSGRoute.PTExt.eCoh 1 (K ≃ₐ[k] K) M ((groupCohomology.H1π M) zQ)) = h
    rw [← Work.SSGRoute.eCoh_map 1 (K ≃ₐ[k] K) (L ≃ₐ[k] L) f M (Rep.res f M)
      (CategoryStruct.id (Rep.res f M)) ((groupCohomology.H1π M) zQ)]
    rw [hmap, hz, hy]

end Work.SSGRoute.Sha2Lib
