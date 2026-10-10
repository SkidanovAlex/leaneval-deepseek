import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.AbsoluteKummer.SES.ker_le_range_mapH0
import Submission.Work.AbsoluteKummer.SES.ker_mapH1_le_range_delta
import Submission.Work.SSGRoute.LTDDefs.H2locEquivH2
import Submission.Work.SSGRoute.range_mapH2_eq_ker_deltaH3
import Submission.Work.SSGRoute.range_mapH2_eq_ker_mapH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The short exact sequence at a decomposition group, from Galois-module data

The additivity of the Euler characteristic `Work.SSGRoute.euler_alternating_loc` takes as input a
short exact sequence `Work.AbsoluteKummer.ShortExactSeq ↥(decomp k A) M N P` of *discrete*
`↥(decomp k A)`-modules.  In applications the data come as a short exact sequence of finite
`𝔽_p[Gal(K/k)]`-modules, with `D_A = decomp k A` acting through `res k K`.

This file supplies the two missing pieces:

* `isDiscreteModule_decomp_of_compat` — for a compatible action the module is discrete for the
  Krull topology, because the stabiliser of every element contains the open subgroup
  `decomp k A ⊓ K.fixingSubgroup` (the kernel of `res k K`);
* `shortExactSeq_decomp_of_gamma` — the `ShortExactSeq` at `↥(decomp k A)` built from
  `𝔽_p`-linear, `Gal(K/k)`-equivariant `ι`, `π`.
-/

open Work

namespace Work.SSGRoute

noncomputable section

/-- **Every compatible `↥(decomp k A)`-module is discrete.**  The stabiliser of `m : M` contains
the subgroup `decomp k A ⊓ K.fixingSubgroup = ker (res k K)`, which is open in `↥(decomp k A)`
because `K.fixingSubgroup` is open in `G_k`; a subgroup containing an open subgroup is open. -/
theorem isDiscreteModule_decomp_of_compat
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (M : Type) [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M] [DistribMulAction ↥(SSGRoute.decomp k A) M]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.AbsoluteKummer.IsDiscreteModule ↥(SSGRoute.decomp k A) M := by
  intro m
  have hHopen : IsOpen ((K.fixingSubgroup).comap (Subgroup.subtype (SSGRoute.decomp k A)) :
      Set ↥(SSGRoute.decomp k A)) :=
    (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val
  have hle : (K.fixingSubgroup).comap (Subgroup.subtype (SSGRoute.decomp k A)) ≤
      MulAction.stabilizer ↥(SSGRoute.decomp k A) m := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [MulAction.mem_stabilizer_iff]
    have h1 : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) = 1 := by
      have hxker : (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
        rw [IntermediateField.restrictNormalHom_ker]
        exact hx
      exact MonoidHom.mem_ker.mp hxker
    rw [hcompat x m, h1, one_smul]
  refine Subgroup.isOpen_of_mem_nhds (g := 1)
    (MulAction.stabilizer ↥(SSGRoute.decomp k A) m) ?_
  refine Filter.mem_of_superset (hHopen.mem_nhds ?_) hle
  simp

/-- **The short exact sequence at a decomposition group, from `Gal(K/k)`-module data.**  A short
exact sequence `0 → M → N → P → 0` of finite `𝔽_p[Gal(K/k)]`-modules with `Gal(K/k)`-equivariant
maps, with `↥(decomp k A)` acting through `res k K`, gives a short exact sequence of *discrete*
`↥(decomp k A)`-modules. -/
noncomputable def shortExactSeq_decomp_of_gamma
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω)
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module (ZMod p) M] [Module (ZMod p) N] [Module (ZMod p) P]
    [DistribMulAction (K ≃ₐ[k] K) M] [DistribMulAction (K ≃ₐ[k] K) N]
    [DistribMulAction (K ≃ₐ[k] K) P]
    [DistribMulAction ↥(SSGRoute.decomp k A) M] [DistribMulAction ↥(SSGRoute.decomp k A) N]
    [DistribMulAction ↥(SSGRoute.decomp k A) P]
    (hm : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (hn : ∀ (h : ↥(SSGRoute.decomp k A)) (m : N),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (hp : ∀ (h : ↥(SSGRoute.decomp k A)) (m : P),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (ι : M →ₗ[ZMod p] N) (π : N →ₗ[ZMod p] P)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : ι.range = π.ker)
    (hιc : ∀ (g : K ≃ₐ[k] K) (x : M), ι (g • x) = g • ι x)
    (hπc : ∀ (g : K ≃ₐ[k] K) (x : N), π (g • x) = g • π x) :
    Work.AbsoluteKummer.ShortExactSeq ↥(SSGRoute.decomp k A) M N P where
  iota := ι.toAddMonoidHom
  pi := π.toAddMonoidHom
  iota_equivariant := by
    intro g x
    change ι (g • x) = g • ι x
    rw [hm g x, hιc (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) x, ← hn g (ι x)]
  pi_equivariant := by
    intro g x
    change π (g • x) = g • π x
    rw [hn g x, hπc (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) x, ← hp g (π x)]
  iota_injective := hι
  pi_surjective := hπ
  range_iota_eq_ker_pi := by
    refine SetLike.ext fun x => ?_
    have hx : x ∈ ι.range ↔ x ∈ π.ker := by rw [hex]
    simpa [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, LinearMap.mem_range,
      LinearMap.mem_ker] using hx
  isDiscreteM := isDiscreteModule_decomp_of_compat k Ω K A M hm
  isDiscreteN := isDiscreteModule_decomp_of_compat k Ω K A N hn
  isDiscreteP := isDiscreteModule_decomp_of_compat k Ω K A P hp

end

end Work.SSGRoute
