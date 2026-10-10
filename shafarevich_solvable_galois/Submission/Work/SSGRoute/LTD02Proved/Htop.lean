import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTD02Proved.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct
open Classical

namespace Work.SSGRoute.LTD02Proved

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

noncomputable section

open Work.SSGRoute

/-- **The `H³`-vanishing input of the dévissage at a decomposition group**: for any finite
`𝔽_p[D_A]`-module `N₁` on which the level-`K` subgroup `U = D_A ∩ Gal(Ω/K)` acts trivially,
`H³(D_A, Hom_ℤ(N₁, Ωˣ)) = 0`.

This is Milne, *ADT*, Lemma 1.9 in the form used by the dévissage of Theorem I.1.8: the `D_A`-action
on `Hom_ℤ(N₁, Ωˣ)` factors through the finite quotient `D_A/U ≅ im(res k K) ⊆ Gal(K/k)`, so the
vanishing reduces to `cd_p(D_A) ≤ 2` for the *finite* Galois level `K/k`
(`Work.SSGRoute.EulerSymm.h3loc_subsingleton`) through
`Work.SSGRoute.PT.h3_H3_subsingleton_of_image`.

The two triviality inputs are `ζ ∈ K` (so that `U` fixes `μ_p = Ωˣ[p]`, the values of every hom out
of the exponent-`p` module `N₁`) and the triviality of the `U`-action on `N₁`. -/
theorem h3_units_conjHom_of_trivAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (N₁ : Type) [AddCommGroup N₁] [Module (ZMod p) N₁]
    [DistribMulAction ↥(SSGRoute.decomp k A) N₁]
    [SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) N₁] [Finite N₁]
    (htriv : ∀ (u : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K)) (n : N₁), u • n = n) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)))
      ↥(SSGRoute.decomp k A)) := by
  classical
  -- ## the primitive `p`-th root of unity
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  let ζu : Ωˣ := Units.mk0 ζ hζ0
  have hζu : IsPrimitiveRoot ζu p :=
    (IsPrimitiveRoot.coe_units_iff (ζ := ζu)).mp (by rw [Units.val_mk0]; exact hζ)
  have hζuK : (ζu : Ω) ∈ K := by rw [Units.val_mk0]; exact hζK
  haveI hNZ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hOneLt : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  -- ## the module `V = Hom_ℤ(N₁, Ωˣ)` and the values of its elements are `p`-torsion
  have hNp : ∀ n : N₁, p • n = 0 := by
    intro n
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p n, ZMod.natCast_self, zero_smul]
  -- ## `U` acts trivially on `V`
  have hfix : ∀ (g : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K)) (y : Additive (Units Ω)),
      p • y = 0 → g • y = y := by
    intro g y hy
    have hgK : ((g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact fun z hz => (Work.SSGRoute.PT.mem_levelFixSub).mp g.2 z hz
    exact Work.SSGRoute.PTUr.ptu_ptorsion_units_smul_eq (k := k) K ζu hζu hζuK _ hgK y hy
  have htrivV : ∀ (u : ↥(Work.SSGRoute.PT.levelFixSub k Ω A K))
      (v : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))), u • v = v :=
    fun u v =>
      Work.SSGRoute.PTUr.ptu_conjHom_units_smul_eq_of_fix hfix (fun g n => htriv g n) hNp u v
  -- ## finiteness of `V`: every hom out of an exponent-`p` module lands in `μ_p`
  have hmemzp : ∀ (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) (n : N₁),
      Additive.toMul (f n) ∈ Subgroup.zpowers ζu := by
    intro f n
    have hp : p • f n = 0 := by rw [← map_nsmul, hNp n, map_zero]
    have hpow : Additive.toMul (f n) ^ p = 1 := by
      simpa [toMul_nsmul] using congrArg Additive.toMul hp
    rw [hζu.zpowers_eq]
    exact (mem_rootsOfUnity p (Additive.toMul (f n))).2 hpow
  haveI hfinμ : Finite ↥(Subgroup.zpowers ζu) :=
    Finite.of_injective (fun u => hζu.zmodEquivZPowers.symm (Additive.ofMul u)) (by
      intro a b hab
      have h := hζu.zmodEquivZPowers.symm.injective hab
      simpa using congrArg (fun x : Additive ↥(Subgroup.zpowers ζu) => Additive.toMul x) h)
  haveI hFintypeN₁ : Fintype N₁ := Fintype.ofFinite N₁
  haveI hFintypeμ : Fintype ↥(Subgroup.zpowers ζu) := Fintype.ofFinite _
  haveI hfinV : Finite (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    Finite.of_injective
      (fun f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)) =>
        fun n : N₁ => (⟨Additive.toMul (f n), hmemzp f n⟩ : ↥(Subgroup.zpowers ζu)))
      (by
        intro f g h
        refine Work.SSGRoute.PT.ConjHom.ext_apply (fun n => ?_)
        have h' : (⟨Additive.toMul (f n), hmemzp f n⟩ : ↥(Subgroup.zpowers ζu))
            = ⟨Additive.toMul (g n), hmemzp g n⟩ := congrFun h n
        have h'' : Additive.toMul (f n) = Additive.toMul (g n) := congrArg Subtype.val h'
        simpa using congrArg Additive.ofMul h'')
  -- ## the pointwise `𝔽_p`-module structure on `V`
  have hpV : ∀ f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω)), p • f = 0 := by
    intro f
    refine Work.SSGRoute.PT.ConjHom.ext_apply (fun n => ?_)
    show p • f n = 0
    rw [← map_nsmul, hNp n, map_zero]
  have hmod : ∀ (m : ℕ) (f : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
      (m % p) • f = m • f := by
    intro m f
    conv_rhs => rw [← Nat.mod_add_div m p]
    rw [add_nsmul, mul_nsmul, hpV f, smul_zero, add_zero]
  letI : Module (ZMod p) (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    { smul := fun c f => c.val • f
      one_smul := fun f => by
        show (1 : ZMod p).val • f = f
        rw [ZMod.val_one p, one_nsmul]
      mul_smul := fun c d f => by
        show (c * d).val • f = c.val • (d.val • f)
        rw [ZMod.val_mul, hmod (c.val * d.val) f, mul_nsmul']
      smul_zero := fun c => nsmul_zero _
      zero_smul := fun f => by
        show (0 : ZMod p).val • f = 0
        rw [ZMod.val_zero, zero_nsmul]
      add_smul := fun c d f => by
        show (c + d).val • f = c.val • f + d.val • f
        rw [ZMod.val_add, hmod (c.val + d.val) f, add_nsmul]
      smul_add := fun c f g => nsmul_add _ _ _ }
  -- ## the image of the decomposition group in `Gal(K/k)` and a chosen section
  set im : Subgroup (K ≃ₐ[k] K) := (SSGRoute.decomp k A).map (SSGRoute.res k K) with himdef
  let lift : ↥im → ↥(SSGRoute.decomp k A) := fun g =>
    ⟨(Subgroup.mem_map.mp g.2).choose, (Subgroup.mem_map.mp g.2).choose_spec.1⟩
  have hlift (g : ↥im) :
      SSGRoute.res k K (((lift g : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)) = (g : K ≃ₐ[k] K) :=
    (Subgroup.mem_map.mp g.2).choose_spec.2
  have hmemU : ∀ (x : ↥(SSGRoute.decomp k A)),
      SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) = 1 → x ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
    intro x hx
    rw [Work.SSGRoute.PT.levelFixSub, Subgroup.mem_subgroupOf]
    have hmem : (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := MonoidHom.mem_ker.mpr hx
    rwa [show SSGRoute.res k K = AlgEquiv.restrictNormalHom K from rfl,
      IntermediateField.restrictNormalHom_ker] at hmem
  -- ## the action of `im` on `V`, transported along the chosen section
  letI imAction : DistribMulAction ↥im
      (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    { smul := fun g v => (lift g) • v
      one_smul := fun v => by
        have h1 : (lift (1 : ↥im) : ↥(SSGRoute.decomp k A))
            ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := hmemU (lift 1) (by rw [hlift 1]; rfl)
        show (lift (1 : ↥im)) • v = v
        exact htrivV ⟨lift 1, h1⟩ v
      mul_smul := fun g h v => by
        have hmem : (lift g * lift h)⁻¹ * lift (g * h)
            ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
          refine hmemU _ ?_
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [map_mul, map_inv, map_mul, hlift, hlift, hlift]
          simp only [Subgroup.coe_mul]
          group
        have h3 : ((lift g * lift h)⁻¹ * lift (g * h)) • v = v := htrivV ⟨_, hmem⟩ v
        have h4 : ((lift g * lift h) * ((lift g * lift h)⁻¹ * lift (g * h))) • v
            = (lift g * lift h) • v := by
          rw [mul_smul, h3]
        have h5 : lift (g * h) • v = (lift g * lift h) • v := by
          simpa only [mul_inv_cancel_left] using h4
        show lift (g * h) • v = (lift g) • ((lift h) • v)
        rw [h5, mul_smul]
      smul_zero := fun g => smul_zero (lift g)
      smul_add := fun g v w => smul_add (lift g) v w }
  haveI : SMulCommClass ↥im (ZMod p)
      (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) :=
    ⟨fun g c f => by
      show g • (c.val • f) = c.val • (g • f)
      induction c.val with
      | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
      | succ k ih => rw [succ_nsmul, smul_add, ih, succ_nsmul]⟩
  -- ## the compatibility of the two actions and the vanishing of `H³`
  have hcompat : ∀ (σ : ↥(SSGRoute.decomp k A))
      (v : Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))),
      σ • v = (⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
        Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩ : ↥im) • v := by
    intro σ v
    show σ • v = (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
      Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩) • v
    have hmem : (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ
        ∈ Work.SSGRoute.PT.levelFixSub k Ω A K := by
      refine hmemU _ ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [map_mul, map_inv, hlift]
      group
    have h3 : ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ) • v = v := htrivV ⟨_, hmem⟩ v
    have h4 : ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)
        * ((lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩)⁻¹ * σ)) • v
        = (lift ⟨SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω),
          Subgroup.mem_map.mpr ⟨σ, σ.2, rfl⟩⟩) • v := by
      rw [mul_smul, h3]
    simpa only [mul_inv_cancel_left] using h4
  exact Work.SSGRoute.PT.h3_H3_subsingleton_of_image p k Ω K A hA
    (Work.SSGRoute.EulerSymm.h3loc_subsingleton p k Ω K A hA)
    (Work.SSGRoute.PT.ConjHom N₁ (Additive (Units Ω))) hcompat

end

end Work.SSGRoute.LTD02Proved
