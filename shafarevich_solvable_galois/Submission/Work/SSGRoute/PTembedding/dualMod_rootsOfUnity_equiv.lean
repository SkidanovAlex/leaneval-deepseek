import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `DualMod p T ≅ μ_p` as `G_k`-modules

For a cyclotomic dual `T` (`SSGRoute.IsCyclotomicDual p (SSGRoute.res k K) ζ`) the coefficient
module `DualMod p T = Hom(T, 𝔽_p)` is `Gal(K/k)`-equivariantly isomorphic to the `p`-th roots of
unity `μ_p = Additive (rootsOfUnity p Ω)` in the ambient field `Ω`, the primitive root `ζ ∈ K`
sitting in `Ω`.

This removes the `NumberField`/`IsAlgClosure` hypotheses that the sibling development
`PTembedding/KummerMuDefs.lean` carries (the statement itself needs neither): the coefficient
isomorphism lands in `μ_p ⊆ K` (`dualModEquivMu`), and the inclusion of `μ_p ⊆ K` into `μ_p ⊆ Ω`
is a bijection because `ζ ∈ K` generates all `p`-th roots of unity of `Ω`.
-/

namespace Work.SSGRoute.PTembedding

open SSGRoute
open Work.SSGRoute

noncomputable section

set_option linter.style.haveILetI false

/-! ## 1. The coefficient isomorphism `DualMod p T ≃+ μ_p ⊆ K` -/

section Coeff

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  {ζ : Ω} {T : Type} [AddCommGroup T] [Module (ZMod p) T]
  [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- **The action of `σ ∈ G_k` on `DualMod p T` is by the cyclotomic character.**  If the
restriction `res k K σ` maps the primitive `p`-th root of unity `ζ ∈ K` to `ζ^m`, then
`(res k K σ) • φ = m • φ`. -/
theorem dualMod_smul_res (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (σ : Ω ≃ₐ[k] Ω) (m : ℕ)
    (hm : (SSGRoute.res k K σ) • (⟨ζ, hζK⟩ : K) = (⟨ζ, hζK⟩ : K) ^ m)
    (φ : Work.SSGRoute.DualMod p T) :
    (SSGRoute.res k K σ) • φ = (m : ZMod p) • φ := by
  have hσζ : σ • ζ = ζ ^ m := by
    have h2 : ((SSGRoute.res k K σ) (⟨ζ, hζK⟩ : K) : Ω) = σ • ζ := by
      rw [AlgEquiv.smul_def]
      exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ (⟨ζ, hζK⟩ : K)
    have h4 : ((SSGRoute.res k K σ) (⟨ζ, hζK⟩ : K) : Ω) = ζ ^ m := by
      rw [← AlgEquiv.smul_def, hm, IntermediateField.coe_pow]
    rw [← h2, h4]
  have hkey : ∀ t : T, (m : ZMod p) • ((SSGRoute.res k K σ) • t) = t := by
    intro t
    have h := hT.2 σ m hσζ t
    rwa [← Nat.cast_smul_eq_nsmul (ZMod p) m ((SSGRoute.res k K σ) • t)] at h
  ext t
  have h1 : (SSGRoute.res k K σ)⁻¹ • t = (m : ZMod p) • t := by
    have h := hkey ((SSGRoute.res k K σ)⁻¹ • t)
    rw [smul_inv_smul] at h
    exact h.symm
  rw [DualMod.dualSMul_apply, LinearMap.smul_apply, h1, map_smul]

/-- The additive map `φ ↦ φ (t0) • ζ` from `DualMod p T` to `μ_p ⊆ K`. -/
noncomputable def dualModToMuK
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T →ₗ[ZMod p] MupCard.MuAdd p K where
  toFun φ := φ (Ach.t0 p T hT.1) • MupCard.zetaGen (p := p) ζ hζ hζK
  map_add' φ ψ := by rw [LinearMap.add_apply, add_smul]
  map_smul' c φ := by rw [RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, mul_smul]

@[simp] theorem dualModToMuK_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModToMuK hT hζ hζK φ = φ (Ach.t0 p T hT.1) • MupCard.zetaGen (p := p) ζ hζ hζK := rfl

theorem dualModToMuK_surjective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Surjective (dualModToMuK (p := p) (K := K) hT hζ hζK) := by
  intro x
  obtain ⟨c, hc⟩ := MupCard.exists_smul_zetaGen (p := p) ζ hζ hζK x
  refine ⟨c • Ach.coord p T hT.1, ?_⟩
  rw [dualModToMuK_apply, LinearMap.smul_apply, Ach.coord_t0, smul_eq_mul, mul_one]
  exact hc.symm

theorem dualModToMuK_injective
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Injective (dualModToMuK (p := p) (K := K) hT hζ hζK) := by
  intro φ ψ h
  rw [dualModToMuK_apply, dualModToMuK_apply] at h
  have h' : (φ (Ach.t0 p T hT.1) - ψ (Ach.t0 p T hT.1)) •
      MupCard.zetaGen (p := p) ζ hζ hζK = 0 := by
    rw [sub_smul, h, sub_self]
  have h2 : φ (Ach.t0 p T hT.1) = ψ (Ach.t0 p T hT.1) :=
    sub_eq_zero.mp ((MupCard.smul_zetaGen_eq_zero_iff ζ hζ hζK _).mp h')
  ext t
  rw [← Ach.smul_coord_t0 p T hT.1 t, map_smul, map_smul, h2]

/-- **The coefficient isomorphism** `DualMod p T ≃+ μ_p ⊆ K`. -/
noncomputable def dualModAddEquivMuK
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.DualMod p T ≃+ MupCard.MuAdd p K :=
  (LinearEquiv.ofBijective (dualModToMuK (p := p) (K := K) hT hζ hζK)
    ⟨dualModToMuK_injective hT hζ hζK, dualModToMuK_surjective hT hζ hζK⟩).toAddEquiv

@[simp] theorem dualModAddEquivMuK_apply
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (φ : Work.SSGRoute.DualMod p T) :
    dualModAddEquivMuK hT hζ hζK φ =
      φ (Ach.t0 p T hT.1) • MupCard.zetaGen (p := p) ζ hζ hζK := rfl

/-- **The coefficient isomorphism is `G_k`-equivariant.** -/
theorem dualModAddEquivMuK_smul
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (σ : Ω ≃ₐ[k] Ω)
    (φ : Work.SSGRoute.DualMod p T) :
    dualModAddEquivMuK hT hζ hζK (SSGRoute.res k K σ • φ) =
      SSGRoute.res k K σ • dualModAddEquivMuK hT hζ hζK φ := by
  obtain ⟨m, hm⟩ := MupCard.exists_smul_zeta_eq_pow (p := p) ζ hζ hζK (SSGRoute.res k K σ)
  have h1 : SSGRoute.res k K σ • φ = (m : ZMod p) • φ := dualMod_smul_res hζK hT σ m hm φ
  have h2 : SSGRoute.res k K σ • MupCard.zetaGen (p := p) ζ hζ hζK
      = (m : ZMod p) • MupCard.zetaGen (p := p) ζ hζ hζK :=
    MupCard.smul_zetaGen ζ hζ hζK (SSGRoute.res k K σ) m hm
  calc dualModAddEquivMuK hT hζ hζK (SSGRoute.res k K σ • φ)
      = ((SSGRoute.res k K σ) • φ) (Ach.t0 p T hT.1)
          • MupCard.zetaGen (p := p) ζ hζ hζK := dualModAddEquivMuK_apply hT hζ hζK _
    _ = ((m : ZMod p) • φ) (Ach.t0 p T hT.1)
          • MupCard.zetaGen (p := p) ζ hζ hζK := by rw [h1]
    _ = ((m : ZMod p) * φ (Ach.t0 p T hT.1))
          • MupCard.zetaGen (p := p) ζ hζ hζK := by
          rw [LinearMap.smul_apply, smul_eq_mul]
    _ = (φ (Ach.t0 p T hT.1) * (m : ZMod p))
          • MupCard.zetaGen (p := p) ζ hζ hζK := by rw [mul_comm]
    _ = φ (Ach.t0 p T hT.1)
          • ((m : ZMod p) • MupCard.zetaGen (p := p) ζ hζ hζK) := by rw [mul_smul]
    _ = φ (Ach.t0 p T hT.1)
          • (SSGRoute.res k K σ • MupCard.zetaGen (p := p) ζ hζ hζK) := by rw [← h2]
    _ = SSGRoute.res k K σ
          • (φ (Ach.t0 p T hT.1) • MupCard.zetaGen (p := p) ζ hζ hζK) := by
          rw [← smul_comm (SSGRoute.res k K σ) (φ (Ach.t0 p T hT.1))
            (MupCard.zetaGen (p := p) ζ hζ hζK)]
    _ = SSGRoute.res k K σ • dualModAddEquivMuK hT hζ hζK φ := by
          rw [dualModAddEquivMuK_apply]

end Coeff

/-! ## 2. The inclusion `μ_p ⊆ K ↪ μ_p ⊆ Ω` is a bijection -/

section Incl

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω}

/-- Coercing the `p`-th roots of unity of `K` into `Ω` along `K → Ω`. -/
noncomputable def muInclHom : rootsOfUnity p K →* rootsOfUnity p Ω :=
  MonoidHom.codRestrict
    ((Units.map (algebraMap K Ω).toMonoidHom).comp (Subgroup.subtype (rootsOfUnity p K)))
    (rootsOfUnity p Ω) (fun x => by
      rw [mem_rootsOfUnity]
      have hx : (x : Kˣ) ^ p = 1 := (mem_rootsOfUnity p (x : Kˣ)).mp x.2
      have h : (Units.map (algebraMap K Ω).toMonoidHom) ((x : Kˣ) ^ p) = 1 := by
        rw [hx, map_one]
      rwa [map_pow] at h)

@[simp] theorem muInclHom_coe (x : rootsOfUnity p K) :
    ((muInclHom (p := p) (K := K) x : rootsOfUnity p Ω) : Ωˣ) =
      Units.map (algebraMap K Ω).toMonoidHom (x : Kˣ) := rfl

theorem muInclHom_injective : Function.Injective (muInclHom (p := p) (K := K)) := by
  intro x y h
  have h3 : Units.map (algebraMap K Ω).toMonoidHom (x : Kˣ)
      = Units.map (algebraMap K Ω).toMonoidHom (y : Kˣ) := by
    have hh := congrArg (fun z : rootsOfUnity p Ω => (z : Ωˣ)) h
    rwa [muInclHom_coe, muInclHom_coe] at hh
  have hinj : Function.Injective ((algebraMap K Ω).toMonoidHom : ↥K → Ω) :=
    fun a b hab => Subtype.ext hab
  exact Subtype.ext (Units.map_injective (f := (algebraMap K Ω).toMonoidHom) hinj h3)

theorem muInclHom_surjective {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Function.Surjective (muInclHom (p := p) (K := K)) := by
  intro w
  have hw : ((w : Ωˣ) : Ω) ^ p = 1 := (mem_rootsOfUnity' p (w : Ωˣ)).mp w.2
  obtain ⟨i, _hi, hi⟩ := hζ.eq_pow_of_pow_eq_one hw
  refine ⟨⟨(MupCard.zetaUnit (p := p) ζ hζ hζK) ^ i, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity, ← pow_mul, mul_comm, pow_mul, MupCard.zetaUnit_pow, one_pow]
  · apply Subtype.ext
    apply Units.ext
    change ((Units.map (algebraMap K Ω).toMonoidHom
      ((MupCard.zetaUnit (p := p) ζ hζ hζK) ^ i) : Ωˣ) : Ω) = ((w : Ωˣ) : Ω)
    rw [Units.coe_map, Units.val_pow_eq_pow_val, map_pow]
    have hz : (algebraMap K Ω).toMonoidHom
        (((MupCard.zetaUnit (p := p) ζ hζ hζK) : Kˣ) : K) = ζ := by
      rw [MupCard.zetaUnit_val ζ hζ hζK]
      rfl
    rw [hz]
    exact hi

/-- The multiplicative equivalence `μ_p ⊆ K ≃* μ_p ⊆ Ω`. -/
noncomputable def muInclMulEquiv {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    rootsOfUnity p K ≃* rootsOfUnity p Ω :=
  MulEquiv.ofBijective (muInclHom (p := p) (K := K))
    ⟨muInclHom_injective, muInclHom_surjective hζ hζK⟩

@[simp] theorem muInclMulEquiv_apply {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (x : rootsOfUnity p K) :
    muInclMulEquiv (p := p) (K := K) hζ hζK x = muInclHom (p := p) (K := K) x := rfl

/-- The additive equivalence `μ_p ⊆ K ≃+ μ_p ⊆ Ω`. -/
noncomputable def muInclAddEquiv {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    MupCard.MuAdd p K ≃+ Additive (rootsOfUnity p Ω) :=
  (muInclMulEquiv (p := p) (K := K) hζ hζK).toAdditive

@[simp] theorem toMul_muInclAddEquiv {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (x : MupCard.MuAdd p K) :
    Additive.toMul (muInclAddEquiv (p := p) (K := K) hζ hζK x) =
      muInclHom (p := p) (K := K) (Additive.toMul x) := rfl

/-- The value of the natural `G_k`-action on `Additive (rootsOfUnity p Ω)`. -/
@[simp] theorem toMul_smul_rootsOfUnity {n : ℕ} (σ : Ω ≃ₐ[k] Ω)
    (a : Additive (rootsOfUnity n Ω)) :
    Additive.toMul (σ • a) =
      MupKummer.muMapOfField k Ω n σ (Additive.toMul a) := rfl

/-- **Compatibility of the inclusion with the Galois actions.** -/
theorem muInclHom_muMapOfField [Normal k K] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (σ : Ω ≃ₐ[k] Ω) (u : rootsOfUnity p K) :
    muInclHom (p := p) (K := K)
        (MupKummer.muMapOfField k K p (SSGRoute.res k K σ) u) =
      MupKummer.muMapOfField k Ω p σ (muInclHom (p := p) (K := K) u) := by
  apply Subtype.ext
  apply Units.ext
  simp only [muInclHom_coe, MupKummer.muMapOfField_coe, Units.coe_map,
    Work.SSGRoute.PT.algEquivUnitsMapOfField_coe]
  exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ ((u : Kˣ) : K)

/-- **The inclusion is `G_k`-equivariant.** -/
theorem muInclAddEquiv_smul [Normal k K] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (σ : Ω ≃ₐ[k] Ω) (x : MupCard.MuAdd p K) :
    muInclAddEquiv (p := p) (K := K) hζ hζK (SSGRoute.res k K σ • x) =
      σ • muInclAddEquiv (p := p) (K := K) hζ hζK x := by
  apply Additive.toMul.injective
  show muInclHom (p := p) (K := K)
      (MupKummer.muMapOfField k K p (SSGRoute.res k K σ) (Additive.toMul x)) =
    MupKummer.muMapOfField k Ω p σ (muInclHom (p := p) (K := K) (Additive.toMul x))
  exact muInclHom_muMapOfField hζ hζK σ (Additive.toMul x)

end Incl

/-! ## 3. The target -/

theorem dualMod_rootsOfUnity_equiv
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∃ Ψ : Work.SSGRoute.DualMod p T ≃+ Additive (rootsOfUnity p Ω),
      ∀ (σ : Ω ≃ₐ[k] Ω) (m : Work.SSGRoute.DualMod p T),
        Ψ (SSGRoute.res k K σ • m) = σ • Ψ m := by
  refine ⟨(dualModAddEquivMuK hT hζ hζK).trans (muInclAddEquiv hζ hζK), ?_⟩
  intro σ m
  show muInclAddEquiv (p := p) (K := K) hζ hζK
      (dualModAddEquivMuK hT hζ hζK (SSGRoute.res k K σ • m)) =
    σ • muInclAddEquiv (p := p) (K := K) hζ hζK (dualModAddEquivMuK hT hζ hζK m)
  rw [dualModAddEquivMuK_smul hT hζ hζK σ m]
  exact muInclAddEquiv_smul hζ hζK σ (dualModAddEquivMuK hT hζ hζK m)

end

end Work.SSGRoute.PTembedding
