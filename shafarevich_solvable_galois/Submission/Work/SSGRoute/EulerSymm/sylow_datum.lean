import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EulerSymm.h3triv_fixingSubgroup
import Submission.Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-Sylow datum of the decomposition group

For a number field `k`, an algebraic closure `Ω`, a finite Galois intermediate field `K ⊆ Ω` and a
finite place `A` of `Ω` over `k`, we construct an open subgroup `U ≤ D_A = decomp k A` of index
prime to `p` such that

* the restriction `res k K : D_A →* Gal(K/k)` maps `U` into a finite `p`-group `P`,
* the action of `U` on every finite `𝔽_p[Gal(K/k)]`-module is discrete,
* `H³(U, 𝔽_p) = 0`.

The construction: let `ζ` be a primitive `p`-th root of unity in `Ω`, `kζ = k(ζ)`, let `Q` be the
image in `Gal(K/k)` of a Sylow `p`-subgroup of the image of the restriction `D_A →* Gal(K/k)`,
let `K₀ = Ω^{res k K ⁻¹ Q}` and `L = K₀ ⊔ kζ`; then `U = Gal(Ω/L) ∩ D_A`.

* `res k K(U) ≤ Q` is a `p`-group; `[D_A : U]` is coprime to `p` because it is the product of the
  index of a Sylow subgroup in `Gal(K/k)` and of a divisor of `[kζ : k] ∣ p - 1`;
* `H³(U, 𝔽_p) = 0` is the base case `h3triv_subsingleton_fixingSubgroup` at the number field `L`
  (which contains `ζ`).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

open Work.SSGRoute
open scoped Pointwise

theorem exists_sylowDatum
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ (U : Subgroup ↥(SSGRoute.decomp k A)) (P : Subgroup (K ≃ₐ[k] K))
      (act : ↥U →* ↥P),
      IsPGroup p ↥P ∧
      IsOpen (U : Set ↥(SSGRoute.decomp k A)) ∧
      Subgroup.FiniteIndex U ∧
      Nat.Coprime U.index p ∧
      (∀ u : ↥U, ((act u : ↥P) : K ≃ₐ[k] K)
        = SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)) ∧
      (∀ (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N],
        letI : DistribMulAction ↥(SSGRoute.decomp k A) N := decompDistribMulAction K N A
        Work.AbsoluteKummer.IsDiscreteModule ↥U N) ∧
      Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥U) := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI hAlgCl : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hNeZero : NeZero (p : Ω) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero⟩
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  -- ## a primitive `p`-th root of unity and the field `k(ζ)`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  obtain ⟨hgalζ, hfinζ, hcopζ⟩ := adjoin_primitiveRoot_isGalois_coprime p k Ω ζ hζ
  let kζ : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hfinkζ : FiniteDimensional k kζ := hfinζ
  haveI hgalkζ : IsGalois k kζ := hgalζ
  have hζkζ : ζ ∈ kζ := IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
  have hcopkζ : Nat.Coprime (Module.finrank k kζ) p := hcopζ
  -- ## the restriction `D_A →* Gal(K/k)` and a Sylow of its image
  let f : ↥(SSGRoute.decomp k A) →* (K ≃ₐ[k] K) :=
    (SSGRoute.res k K).comp (Subgroup.subtype (SSGRoute.decomp k A))
  haveI : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k K
  haveI : Finite ↥f.range := inferInstance
  let Q₀ : Sylow p ↥f.range := default
  let P : Subgroup (K ≃ₐ[k] K) := Q₀.map f.range.subtype
  have hP : IsPGroup p ↥P := Q₀.isPGroup'.map f.range.subtype
  -- ## the number field `L = K₀ ⊔ k(ζ)`
  let H : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.comap (SSGRoute.res k K) P
  have hHle : K.fixingSubgroup ≤ H := by
    intro σ hσ
    have h1 : SSGRoute.res k K σ = 1 := by
      have h2 : σ ∈ (SSGRoute.res k K).ker := by
        rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
          IntermediateField.restrictNormalHom_ker K]
        exact hσ
      simpa using h2
    rw [Subgroup.mem_comap, h1]
    exact P.one_mem
  have hHop : IsOpen (H : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono hHle (IntermediateField.fixingSubgroup_isOpen K)
  have hHcl : IsClosed (H : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen H hHop
  let K₀ : IntermediateField k Ω := IntermediateField.fixedField H
  have hK₀ : K₀.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) ⟨H, hHcl⟩
  haveI hfinK₀ : FiniteDimensional k K₀ :=
    (InfiniteGalois.isOpen_iff_finite K₀).mp (by rw [hK₀]; exact hHop)
  let L : IntermediateField k Ω := K₀ ⊔ kζ
  haveI hfinL : FiniteDimensional k L := inferInstance
  have hLfix : L.fixingSubgroup = H ⊓ kζ.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, hK₀]
  -- ## the open subgroup `U = Gal(Ω/L) ∩ D_A`
  let U : Subgroup ↥(SSGRoute.decomp k A) :=
    (L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)
  have hUeq : U = (H.subgroupOf (SSGRoute.decomp k A))
      ⊓ ((kζ.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)) := by
    rw [show U = (L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A) from rfl, hLfix]
    rfl
  have hUleH : U ≤ H.subgroupOf (SSGRoute.decomp k A) := by
    intro u hu
    rw [hUeq] at hu
    exact (Subgroup.mem_inf.mp hu).1
  -- ## the action homomorphism
  let act : ↥U →* ↥P :=
    { toFun := fun u => ⟨SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω), by
        have h := hUleH u.2
        rw [Subgroup.mem_subgroupOf] at h
        rwa [show H = Subgroup.comap (SSGRoute.res k K) P from rfl,
          Subgroup.mem_comap] at h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u w => Subtype.ext (by simp) }
  have hactres : ∀ u : ↥U, ((act u : ↥P) : K ≃ₐ[k] K)
      = SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) := fun _ => rfl
  -- ## `U` is open in `D_A`
  have hKL : (K ⊔ kζ).fixingSubgroup ≤ L.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, hLfix]
    exact inf_le_inf hHle le_rfl
  have hUopen : IsOpen (U : Set ↥(SSGRoute.decomp k A)) := by
    refine Subgroup.isOpen_mono ?_
      (Subgroup.subgroupOf_isOpen _ _ (IntermediateField.fixingSubgroup_isOpen (K ⊔ kζ)))
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    show ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup
    exact hKL hu
  -- ## `H³(U, 𝔽_p) = 0`: the base case at `L`
  have hζL : ζ ∈ L := (le_sup_right : kζ ≤ L) hζkζ
  have hbaseU : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥U) :=
    h3triv_subsingleton_fixingSubgroup p k Ω L ζ hζ hζL A hA
  -- ## discreteness of the action
  have hdisc : ∀ (N : Type) [AddCommGroup N] [Module (ZMod p) N]
      [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N],
      letI : DistribMulAction ↥(SSGRoute.decomp k A) N := decompDistribMulAction K N A
      Work.AbsoluteKummer.IsDiscreteModule ↥U N := by
    intro N _ _ _ _ _
    letI : DistribMulAction ↥(SSGRoute.decomp k A) N := decompDistribMulAction K N A
    intro m
    refine Subgroup.isOpen_mono (show ((K.fixingSubgroup).subgroupOf
      (SSGRoute.decomp k A)).subgroupOf U ≤ MulAction.stabilizer ↥U m from ?_)
      (Subgroup.subgroupOf_isOpen _ _ (Subgroup.subgroupOf_isOpen _ _
        (IntermediateField.fixingSubgroup_isOpen K)))
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    have hu' : SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) = 1 := by
      have h2 : ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := hu
      have h3 : ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
        rw [show (SSGRoute.res k K).ker = K.fixingSubgroup from
          IntermediateField.restrictNormalHom_ker K]
        exact h2
      simpa using h3
    rw [show u • m = SSGRoute.res k K ((u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) • m from rfl,
      hu', one_smul]
  -- ## the index of `U` is prime to `p`
  let U₁ : Subgroup ↥(SSGRoute.decomp k A) := H.subgroupOf (SSGRoute.decomp k A)
  let U₂ : Subgroup ↥(SSGRoute.decomp k A) :=
    (kζ.fixingSubgroup).subgroupOf (SSGRoute.decomp k A)
  have hUeq' : U = U₁ ⊓ U₂ := hUeq
  have hPsub : P.subgroupOf f.range = Q₀ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [show P = Q₀.map f.range.subtype from rfl, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [← Subtype.ext hyx]
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      rw [show P = Q₀.map f.range.subtype from rfl, Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
  have hU₁ind : U₁.index = Q₀.index := by
    have h1 : U₁ = P.comap f := by
      rw [show U₁ = (P.comap (SSGRoute.res k K)).subgroupOf (SSGRoute.decomp k A) from rfl]
      rfl
    rw [h1, Subgroup.index_comap, ← hPsub]
    rfl
  have hU₁cop : Nat.Coprime U₁.index p := by
    rw [hU₁ind, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr Q₀.not_dvd_index
  have hrelcop : Nat.Coprime ((U₁ ⊓ U₂).relIndex U₁) p := by
    have hker : (U₁ ⊓ U₂).relIndex U₁ = Nat.card ↥(((SSGRoute.res k kζ).comp
        ((Subgroup.subtype (SSGRoute.decomp k A)).comp U₁.subtype)).range) := by
      rw [Subgroup.relIndex]
      have h1 : (U₁ ⊓ U₂).subgroupOf U₁ = U₂.subgroupOf U₁ := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨x.2, h⟩
      rw [h1]
      have h2 : U₂.subgroupOf U₁ = ((SSGRoute.res k kζ).comp
          ((Subgroup.subtype (SSGRoute.decomp k A)).comp U₁.subtype)).ker := by
        rw [show U₂ = (kζ.fixingSubgroup).subgroupOf (SSGRoute.decomp k A) from rfl]
        rw [show kζ.fixingSubgroup = (SSGRoute.res k kζ).ker from
          (IntermediateField.restrictNormalHom_ker kζ).symm]
        rfl
      rw [h2, Subgroup.index_ker]
    rw [hker]
    have hdvd : Nat.card ↥(((SSGRoute.res k kζ).comp
        ((Subgroup.subtype (SSGRoute.decomp k A)).comp U₁.subtype)).range)
        ∣ Module.finrank k kζ := by
      rw [← IsGalois.card_aut_eq_finrank (F := k) (E := ↥kζ)]
      exact Subgroup.card_subgroup_dvd_card _
    exact hcopkζ.coprime_dvd_left hdvd
  have hUcop : Nat.Coprime U.index p := by
    rw [hUeq']
    rw [← Subgroup.relIndex_mul_index (show U₁ ⊓ U₂ ≤ U₁ from inf_le_left)]
    exact hrelcop.mul_left hU₁cop
  have hfi : Subgroup.FiniteIndex U := Subgroup.finiteIndex_iff.mpr (by
    intro h0
    have h := hUcop
    rw [Nat.Coprime, h0, Nat.gcd_zero_left] at h
    exact (Fact.out : Nat.Prime p).ne_one h)
  exact ⟨U, P, act, hP, hUopen, hfi, hUcop, hactres, hdisc, hbaseU⟩

end Work.SSGRoute.EulerSymm
