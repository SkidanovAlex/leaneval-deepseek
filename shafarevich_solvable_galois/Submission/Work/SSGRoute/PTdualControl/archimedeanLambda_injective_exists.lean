import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.ext_two_iso_divisible_cohomology
import Submission.Work.SSGRoute.PT.localDictionary_fin_injective
import Submission.Work.SSGRoute.PTembedding.homRep_dualMod_units_of_isCyclotomicDual
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalExt2Subsingleton
import Submission.Work.SSGRoute.dualUnits_linearEquiv
import Submission.Work.SSGRoute.homRep
import Submission.Work.Shrinking.finite_tensorProduct_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local dictionary: existence of the injective `Λ` (clause (A))

This file proves clause (A) of the archimedean local dictionary
(`Work.SSGRoute.SSGStage.archimedeanLocalDictionary`): for an infinite place `w` of `K` and an
involution `σ` of `Gal(Ω/k)` whose image under `res k K` contains the decomposition group `D_w`,
there is an injective additive map

  `Λ : Ext²_{D_w}(E'|, K_wˣ) →+ H²(⟨σ⟩, E)`,   `E' = DualMod p (E ⊗ T)`.

Three cases:

* `D_w = ⊥`: the first variable is a finite `ℤ`-module, so `Ext² = 0` and `Λ = 0`;
* `p ≠ 2`: the local `Ext²` is a subsingleton (`archimedeanLocalExt2Subsingleton`) and `Λ = 0`;
* `p = 2`: then `T` is a trivial module, `K_w = ℂ` has divisible units, the divisible-coefficient
  dictionary identifies `Ext²_{D_w}(E'|, K_wˣ)` with `H²(D_w, Hom_ℤ(E'|, K_wˣ))`, and the
  double-dual iso `Hom_ℤ(E'|, K_wˣ) ≅ E` together with the group isomorphism `D_w ≅ ⟨σ⟩` gives the
  desired equivalence.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory
open SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

/-! ## Elementary helpers -/

/-- `-1` is a primitive square root of unity in a domain of characteristic `≠ 2`. -/
private theorem isPrimitiveRoot_neg_one_units {A : Type} [CommRing A] [IsDomain A]
    (h2 : (2 : A) ≠ 0) : IsPrimitiveRoot (-1 : Aˣ) 2 := by
  have h1 : ((-1 : Aˣ)) ^ 2 = 1 := by ext; simp [sq]
  have hne : (-1 : Aˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Aˣ => (u : A)) h
    simp at this
    linear_combination (norm := ring_nf) -this
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime h1 hne)

/-- In a group, an element of `⟨a⟩` that is not `1` equals `a` when `a` is an involution. -/
private theorem eq_of_mem_zpowers_of_sq_eq_one {G : Type} [Group G] {a d : G} (ha2 : a ^ 2 = 1)
    (hd : d ∈ Subgroup.zpowers a) (hd1 : d ≠ 1) : d = a := by
  obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hd
  have h2 : a ^ (2:ℤ) = 1 := by rw [zpow_ofNat]; exact ha2
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact absurd (by rw [← hk, hm, show m + m = 2 * m from by ring, zpow_mul, h2, one_zpow]) hd1
  · rw [← hk, hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

/-! ## Abbreviations for the archimedean local data -/

/-- The decomposition group of the infinite place `Place.ofInfinite w`. -/
private abbrev Dinf (k : Type) [Field k] [NumberField k] (K : Type) [Field K] [NumberField K]
    [Algebra k K] (w : NumberField.InfinitePlace K) : Subgroup (K ≃ₐ[k] K) :=
  SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)

/-- The coefficient representation `E' = DualMod 2 (E ⊗ T)`. -/
private abbrev Mrep (k : Type) [Field k] (K : Type) [Field K] [Algebra k K]
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T] :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))

/-- The local units `K_wˣ` as a `D_w`-representation. -/
private abbrev Ninf (k : Type) [Field k] [NumberField k] (K : Type) [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NumberField.InfinitePlace K) :
    Rep.{0} SSGRoute.PTExt.Coeff (Dinf k K w) :=
  SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)

/-! ## The group isomorphism `D_w ≅ ⟨σ⟩` -/

/-- If the decomposition group `D_w` of an infinite place is nontrivial and contained in the image
of `⟨σ⟩` under `res k K`, for an involution `σ`, then `res k K` restricts to an isomorphism
`⟨σ⟩ ≅ D_w`. -/
theorem decompK_zpowers_iso (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K))
    (hbot : SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥) :
    ∃ Φ : SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w) ≃*
        ↥(Subgroup.zpowers σ),
      ∀ d : SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w),
        SSGRoute.res k K ((Φ d : ↥(Subgroup.zpowers σ)) : Ω ≃ₐ[k] Ω) = (d : K ≃ₐ[k] K) := by
  classical
  set D := SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w) with hD
  have hσ' : SSGRoute.res k K σ ^ 2 = 1 := by rw [← map_pow, hσ, map_one]
  have hσ'ne : SSGRoute.res k K σ ≠ 1 := by
    intro h
    apply hbot
    have hmapbot : (Subgroup.zpowers σ).map (SSGRoute.res k K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [map_zpow, h]; simp
    rw [hD]
    exact le_bot_iff.mp (hmapbot ▸ hle)
  have hDle : D ≤ Subgroup.zpowers (SSGRoute.res k K σ) := by
    intro x hx
    rcases Subgroup.mem_map.mp (hle hx) with ⟨g, hg, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  have hres_mem : SSGRoute.res k K σ ∈ D := by
    obtain ⟨d, hdD, hdne⟩ : ∃ d, d ∈ D ∧ d ≠ 1 := by
      by_contra h
      push Not at h
      exact hbot (by rw [hD]; exact (Subgroup.eq_bot_iff_forall D).mpr h)
    have hd_eq : d = SSGRoute.res k K σ :=
      eq_of_mem_zpowers_of_sq_eq_one hσ' (hDle hdD) hdne
    rwa [hd_eq] at hdD
  have hDimg : Subgroup.zpowers (SSGRoute.res k K σ) ≤ D := Subgroup.zpowers_le_of_mem hres_mem
  have hDeq : D = Subgroup.zpowers (SSGRoute.res k K σ) := le_antisymm hDle hDimg
  let Ψ : ↥(Subgroup.zpowers σ) →* ↥D :=
    { toFun := fun g => ⟨SSGRoute.res k K (g : Ω ≃ₐ[k] Ω), hDimg (by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
        rw [← hn, map_zpow]
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := by intro g h; ext; simp [map_mul] }
  have hker : ∀ g : ↥(Subgroup.zpowers σ), Ψ g = 1 → g = 1 := by
    intro g hg
    have hg' : SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) = 1 := by
      have h := congrArg (fun u : ↥D => (u : K ≃ₐ[k] K)) hg
      simpa [Ψ] using h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hn2 : (SSGRoute.res k K σ) ^ n = 1 := by rw [← map_zpow, hn]; exact hg'
    have hord : orderOf (SSGRoute.res k K σ) = 2 := orderOf_eq_prime hσ' hσ'ne
    have hdiv : (orderOf (SSGRoute.res k K σ) : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.mpr hn2
    rw [hord] at hdiv
    obtain ⟨m, hm⟩ := hdiv
    have hm' : n = (2:ℤ) * m := by simpa using hm
    apply Subtype.ext
    show (g : Ω ≃ₐ[k] Ω) = 1
    rw [← hn, hm', zpow_mul, show σ ^ (2:ℤ) = 1 from by rw [zpow_ofNat]; exact hσ, one_zpow]
  have hsurj : Function.Surjective Ψ := by
    intro d
    have hd : (d : K ≃ₐ[k] K) ∈ Subgroup.zpowers (SSGRoute.res k K σ) := by
      rw [← hDeq]; exact d.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hd
    refine ⟨⟨σ ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show SSGRoute.res k K (σ ^ n) = (d : K ≃ₐ[k] K)
    rw [map_zpow, hn]
  have hinj : Function.Injective Ψ := fun a b hab => by
    have h1 : Ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := hker _ h1
    exact mul_inv_eq_one.mp h2
  refine ⟨(MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm, ?_⟩
  intro d
  have h := MulEquiv.apply_symm_apply (MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩) d
  exact congrArg (fun u : ↥D => (u : K ≃ₐ[k] K)) h

/-! ## Triviality of the cyclotomic dual at `p = 2` -/

/-- For `p = 2` the cyclotomic dual `T` is a trivial `Gal(K/k)`-module. -/
theorem T_trivial_p2 (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2)
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) ζ) :
    ∀ (τ : K ≃ₐ[k] K) (t : T), τ • t = t := by
  have hζneg : ζ = -1 := by
    have h1 : ζ ≠ 1 := by
      simpa using hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num : 1 < 2)
    rcases (sq_eq_one_iff.mp hζ.pow_eq_one) with h | h
    · exact absurd h h1
    · exact h
  intro τ t
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) Ω τ
  have hc : σ • ζ = ζ ^ 1 := by
    rw [pow_one, show ζ = -1 from hζneg]
    show σ (-1) = -1
    simp
  have := hT.2 σ 1 hc t
  rw [one_smul, hσ] at this
  exact this

/-! ## The coefficient iso `Hom_ℤ(E'|, K_wˣ) ≅ E` at `p = 2` -/

/-- **The archimedean coefficient identification at `p = 2`.**  For a trivial one-dimensional
cyclotomic dual `T`, the internal `Hom_ℤ(E'|, K_wˣ)`, `E' = DualMod 2 (E ⊗ T)`, with the
`D_w`-conjugation action is `D_w`-equivariantly isomorphic to `E`. -/
theorem coeffEquiv_p2 (k : Type) [Field k] [NumberField k] (K : Type) [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (E T : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hTtriv : ∀ (τ : K ≃ₐ[k] K) (t : T), τ • t = t)
    (hrank : Module.finrank (ZMod 2) T = 1)
    (w : NumberField.InfinitePlace K) :
    ∃ Ψ : ((Mrep k K E T).V →ₗ[SSGRoute.PTExt.Coeff] (Ninf k K w).V) ≃+ E,
      ∀ (d : ↥(Dinf k K w)) (f : (Mrep k K E T).V →ₗ[SSGRoute.PTExt.Coeff] (Ninf k K w).V),
        Ψ (Work.SSGRoute.homSMul (Rep.res (Dinf k K w).subtype (Mrep k K E T)) (Ninf k K w) d f)
          = d • Ψ f := by
  classical
  haveI : Module.Finite (ZMod 2) T := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  let u : T ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq (R := ZMod 2) T (ZMod 2) (by rw [hrank, Module.finrank_self])
  let t₀ : T := u.symm 1
  let isoE : E ≃ₗ[ZMod 2] TensorProduct (ZMod 2) E T :=
    (TensorProduct.rid (ZMod 2) E).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod 2) E) u).symm)
  haveI : Finite (TensorProduct (ZMod 2) E T) :=
    Finite.of_injective isoE.symm isoE.symm.injective
  have hisoE : ∀ x : E, isoE x = x ⊗ₜ[ZMod 2] t₀ := by
    intro x
    rw [show isoE x = (TensorProduct.congr (LinearEquiv.refl (ZMod 2) E) u).symm
        ((TensorProduct.rid (ZMod 2) E).symm x) from rfl]
    rw [TensorProduct.rid_symm_apply, TensorProduct.congr_symm, TensorProduct.congr_tmul]
    simp [t₀]
  -- a primitive square root of unity in the local field
  have h2 : (2 : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w)) ≠ 0 := by
    rw [show (2 : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))
          = algebraMap K _ (2 : K) from (map_ofNat _ 2).symm]
    exact fun h => two_ne_zero (RingHom.injective (algebraMap K _) h)
  have hζu : IsPrimitiveRoot
      (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) 2 :=
    isPrimitiveRoot_neg_one_units h2
  haveI hFact2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨e, he⟩ := Work.SSGRoute.dualUnits_linearEquiv 2
    (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) hζu
    (TensorProduct (ZMod 2) E T)
  -- the `D_w`-action fixes the `p`-th roots of unity inside `K_wˣ`
  have hρ : ∀ (d : ↥(Dinf k K w))
      (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ),
      (Ninf k K w).ρ d (Additive.ofMul u)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := K)
            (NK.GlobalCFT.Place.ofInfinite w) d u) := fun _ _ => rfl
  have hlu : ∀ (d : ↥(Dinf k K w)),
      NK.HassePrinciple.localUnitsEquiv (K := k) (L := K)
        (NK.GlobalCFT.Place.ofInfinite w) d
        (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ)
        = (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) := by
    intro d
    apply Units.ext
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
    simp
  have hfix : ∀ (d : ↥(Dinf k K w)) (y : ZMod 2),
      (Ninf k K w).ρ d (Work.SSGRoute.SelfDual.zetaPowHom
          (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) hζu y)
        = Work.SSGRoute.SelfDual.zetaPowHom
          (-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) hζu y := by
    intro d y
    obtain ⟨n, hn⟩ : ∃ n : ℕ, y = (n : ZMod 2) := ⟨y.val, (ZMod.natCast_zmod_val y).symm⟩
    subst hn
    rw [Work.SSGRoute.SelfDual.zetaPowHom_coe_nat]
    exact (hρ d ((-1 : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ) ^ n)).trans
      (congrArg Additive.ofMul (by rw [map_pow, hlu d]))
  -- equivariance of the double-dual coefficient iso
  have he_smul : ∀ (d : ↥(Dinf k K w)) (x : TensorProduct (ZMod 2) E T),
      e (d • x) = Work.SSGRoute.homSMul (Rep.res (Dinf k K w).subtype (Mrep k K E T))
        (Ninf k K w) d (e x) := by
    intro d x
    apply LinearMap.ext
    intro φ
    change (e (d • x)) φ
      = (Ninf k K w).ρ d ((e x) ((Rep.res (Dinf k K w).subtype (Mrep k K E T)).ρ d⁻¹ φ))
    rw [he (d • x) φ,
      he x ((Rep.res (Dinf k K w).subtype (Mrep k K E T)).ρ d⁻¹ φ)]
    have hψ : ((Rep.res (Dinf k K w).subtype (Mrep k K E T)).ρ d⁻¹) φ
        = ((d⁻¹ : ↥(Dinf k K w)) • φ) := rfl
    rw [hψ, Work.SSGRoute.DualMod.dualSMul_apply, inv_inv]
    exact (hfix d (φ (d • x))).symm
  -- equivariance of the tensor iso
  have hisoE_smul : ∀ (d : ↥(Dinf k K w)) (x : E), isoE (d • x) = d • isoE x := by
    intro d x
    rw [hisoE (d • x), hisoE x]
    rw [show d • (x ⊗ₜ[ZMod 2] t₀) = (d • x) ⊗ₜ[ZMod 2] (d • t₀) from rfl,
      show d • t₀ = t₀ from hTtriv ((d : ↥(Dinf k K w)) : K ≃ₐ[k] K) t₀]
  refine ⟨e.symm.toAddEquiv.trans isoE.symm.toAddEquiv, ?_⟩
  intro d f
  have h1 : e.symm (Work.SSGRoute.homSMul (Rep.res (Dinf k K w).subtype (Mrep k K E T))
      (Ninf k K w) d f) = d • (e.symm f) := by
    conv_lhs => rw [← e.apply_symm_apply f]
    rw [← he_smul d (e.symm f)]
    rw [LinearEquiv.symm_apply_apply]
  have h2 : isoE.symm (d • (e.symm f)) = d • (isoE.symm (e.symm f)) := by
    apply isoE.injective
    rw [isoE.apply_symm_apply, hisoE_smul, isoE.apply_symm_apply]
  change isoE.symm (e.symm (Work.SSGRoute.homSMul (Rep.res (Dinf k K w).subtype (Mrep k K E T))
      (Ninf k K w) d f)) = d • (isoE.symm (e.symm f))
  rw [h1, h2]

end

/-! ## The main theorem -/

theorem archimedeanLambda_injective_exists (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ := by
  classical
  -- finiteness of the coefficient module, in the general form
  haveI hTfin : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let u₀ : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  haveI hTfin' : Finite T := Finite.of_injective u₀ u₀.injective
  haveI hXfin : Finite (TensorProduct (ZMod p) E T) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) E T
  haveI hMfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Finite.of_injective (fun f : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) =>
        (f : (TensorProduct (ZMod p) E T) → ZMod p)) DFunLike.coe_injective
  by_cases hbot : SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofInfinite w)
      = ⊥
  · -- Case 1: trivial decomposition group: `Ext² = 0`.
    haveI : Subsingleton ↥(SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w)) := by
      rw [hbot]; infer_instance
    haveI hResFin : Finite (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).V := hMfin
    haveI : Module.Finite ℤ (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))).V :=
      Work.SSGRoute.PT.module_finite_int_of_finite _
    haveI : Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
            (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w)) 2) :=
      Work.SSGRoute.PT.subsingleton_ext2_of_subsingleton _ _
    exact ⟨0, fun a b _ => Subsingleton.elim a b⟩
  · by_cases hp2 : p = 2
    · -- Case 3: `p = 2`.
      subst hp2
      letI instZp : DistribMulAction ↥(Subgroup.zpowers σ) E :=
        @Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
      -- local data
      have hw : w.IsComplex :=
        Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := K) hbot
      have hdiv : ∀ n : ℕ, 0 < n → ∀ y : (Ninf k K w).V, ∃ x : (Ninf k K w).V, n • x = y :=
        Work.SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := K) hw
      have hTtriv : ∀ (τ : K ≃ₐ[k] K) (t : T), τ • t = t :=
        T_trivial_p2 k Ω K ζ hζ T hT
      obtain ⟨e⟩ := Work.SSGRoute.ext_two_iso_divisible_cohomology (Dinf k K w)
        (Rep.res (Dinf k K w).subtype (Mrep k K E T)) (Ninf k K w) hdiv
      obtain ⟨Φ, hΦ⟩ := decompK_zpowers_iso k Ω K w σ hσ hle hbot
      obtain ⟨Ψ, hΨ⟩ := coeffEquiv_p2 k K E T hTtriv hT.1 w
      have hΨ' : ∀ (d : ↥(Dinf k K w))
          (f : (Rep.res (Dinf k K w).subtype (Mrep k K E T)).V →ₗ[SSGRoute.PTExt.Coeff]
            (Ninf k K w).V),
          Ψ (d • f) = Φ d • Ψ f := by
        intro d f
        rw [show (d • f) = Work.SSGRoute.homSMul (Rep.res (Dinf k K w).subtype (Mrep k K E T))
            (Ninf k K w) d f from rfl, hΨ d f]
        show (d : K ≃ₐ[k] K) • Ψ f
          = (SSGRoute.res k K ((Φ d : ↥(Subgroup.zpowers σ)) : Ω ≃ₐ[k] Ω)) • Ψ f
        rw [hΦ d]
      exact ⟨(e.trans (Work.SSGRoute.PT.gcH2Transfer Φ Ψ hΨ')).toAddMonoidHom,
        (e.trans (Work.SSGRoute.PT.gcH2Transfer Φ Ψ hΨ')).injective⟩
    · -- Case 2: odd `p`: the local `Ext²` is a subsingleton.
      haveI hXmod : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V := hMfin
      have hMptor : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T), p • x = 0 := by
        intro x
        rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
      haveI : Subsingleton (CategoryTheory.Abelian.Ext.{0}
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
              (NK.GlobalCFT.Place.ofInfinite w)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w)) 2) :=
        Work.SSGRoute.SSGStage.archimedeanLocalExt2Subsingleton p hp2 k ↥K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
          (fun x => hMptor x) w
      exact ⟨0, fun a b _ => Subsingleton.elim a b⟩

end Work.SSGRoute.PTdualControl
