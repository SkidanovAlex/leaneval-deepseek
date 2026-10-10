import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDArch.AuxLemmas
import Submission.Work.SSGRoute.local_tate_duality_archimedean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
## Non-degeneracy of the real-place pairing `Ach.archPair`

`Work.SSGRoute.local_tate_duality_archimedean` exhibits *some* pairing on
`Z¹(⟨c⟩, E) × Z¹(⟨c⟩, DualMod p (E ⊗ T))` whose two radicals are the coboundary spaces
(local Tate duality at a real place).  This file proves that the *explicit* pairing
`Ach.archPair p (Ω ≃ₐ[k] Ω) E T hT.1 c` of `LTDArch.Defs` has the same two radical properties:
a cocycle pairing to zero against every cocycle on the other side is a coboundary.

For odd `p` this is immediate (`archPair ≡ 0`, and every cocycle on `⟨c⟩` is a coboundary since `2`
is invertible in `𝔽_p`).  For `p = 2` the content is the following.  The action of `⟨c⟩` on `T` is
trivial (`ζ = -1` is fixed by every automorphism, so `hT.2` at `n = 1` applies), hence the tensor
action on `E ⊗ T` is diagonal and `S := 1 + act c` on `E ⊗ T` is `S_E ⊗ id`.  `S` is `𝔽_p`-linear
and a `1`-cocycle on `⟨c⟩` with value `x` is a coboundary iff `x ∈ range S` (cocycle condition in
characteristic two reads `x ∈ ker S`).  The radical statements are then the double-annihilator
facts `x ∈ range S ↔ (∀ η ∈ range(S)ᵃ, η x = 0)` for `S = S_E`, and
`y ∈ range (dualMap S) = (ker S)ᵃ` for `S = S_M`; the separating cochains on the other side are
supplied by `ArchAux.exists_cocycle_locConst_conc`.

The argument is a self-contained replay, at the fixed pairing `Ach.archPair`, of the last two
conjuncts of `local_tate_duality_archimedean` (which constructs exactly that pairing).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.SSGRoute

theorem archPair_nondegenerate (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual (Γ := Ω ≃ₐ[k] Ω) (G := K ≃ₐ[k] K) p (T := T)
      (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    (∀ f : (Ω ≃ₐ[k] Ω) → E,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
      (∀ g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        SSGRoute.Ach.archPair p (Ω ≃ₐ[k] Ω) E T hT.1 c f g = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) f) ∧
    (∀ g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
      (∀ f : (Ω ≃ₐ[k] Ω) → E,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        SSGRoute.Ach.archPair p (Ω ≃ₐ[k] Ω) E T hT.1 c f g = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) g) := by
  classical
  have hfin : Module.finrank (ZMod p) T = 1 := hT.1
  have hσinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← pow_two, hc, map_one])
  have hTtriv : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (t : T), SSGRoute.res k K σ • t = t := by
    intro hp2 σ t
    subst hp2
    have hz : ζ = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right hζ
    have hσζ : σ • ζ = ζ ^ 1 := by rw [hz, pow_one]; simp
    have := hT.2 σ 1 hσζ t
    simpa using this
  have htoE : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (y : E ⊗[ZMod p] T),
      Ach.toE p E T (Ach.coord p T hfin) (SSGRoute.res k K σ • y) =
        SSGRoute.res k K σ • Ach.toE p E T (Ach.coord p T hfin) y := by
    intro hp2 σ y
    subst hp2
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t =>
        show Ach.coord 2 T hfin (SSGRoute.res k K σ • t) • (SSGRoute.res k K σ • e) =
          SSGRoute.res k K σ • (Ach.coord 2 T hfin t • e)
        rw [hTtriv rfl σ t, smul_comm (SSGRoute.res k K σ) (Ach.coord 2 T hfin t) e]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hAB : ∀ y : E ⊗[ZMod p] T,
      Ach.toE p E T (Ach.coord p T hfin) y ⊗ₜ[ZMod p] Ach.t0 p T hfin = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t => rw [Ach.toE_tmul, TensorProduct.smul_tmul, Ach.smul_coord_t0]
    | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy]
  refine ⟨?_, ?_⟩
  · intro f hf hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hf1, hfc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hf.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, 0, ?_⟩
        rw [hc1, hf1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hsmul : ∀ e : E, (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
            SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
          intro e
          rw [show SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
              (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
            hTtriv rfl c (Ach.t0 2 T hfin)]
        have hmem : f c ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) : E →ₗ[ZMod 2] E).range := by
          rw [Ach.mem_range_iff_forall_dual]
          intro φ hφ
          have hφ' : φ + SSGRoute.res k K c • φ = 0 := by
            ext v
            rw [LinearMap.add_apply, LinearMap.zero_apply,
              ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add,
              ← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) v]
            exact hφ v
          set ψ : SSGRoute.DualMod 2 (E ⊗[ZMod 2] T) :=
            φ.comp (Ach.toE 2 E T (Ach.coord 2 T hfin)) with hψdef
          have hψinv : ∀ y : E ⊗[ZMod 2] T, ψ (SSGRoute.res k K c • y) = ψ y := by
            intro y
            show φ (Ach.toE 2 E T (Ach.coord 2 T hfin) (SSGRoute.res k K c • y)) =
              φ (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [htoE rfl c y, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv]
            have h2 := DFunLike.congr_fun hφ' (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [LinearMap.add_apply, LinearMap.zero_apply] at h2
            exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
          have hψfix : ψ + SSGRoute.res k K c • ψ = 0 := by
            have hs : SSGRoute.res k K c • ψ = ψ := LinearMap.ext fun y => by
              rw [ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, hψinv y]
            rw [hs]
            exact Ach.add_self_eq_zero_of_eq_two 2 rfl ψ
          obtain ⟨g, hg1, hg2, hgc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj ψ hψfix
          have h0 := hzero g ⟨hg1, hg2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hgc,
            hψdef, LinearMap.comp_apply, Ach.toE_tmul, Ach.coord_t0, one_smul] at h0
          exact h0
        obtain ⟨m, hm⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, m, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl, ← hm, ArchAux.onePlus_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc f hf.1
  · intro g hg hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hg1, hgc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hg.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, 0, ?_⟩
        rw [hc1, hg1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hψinv : ∀ y : E ⊗[ZMod 2] T, (g c) (SSGRoute.res k K c • y) = (g c) y := by
          intro y
          have h2 := DFunLike.congr_fun hgc y
          rw [LinearMap.add_apply, LinearMap.zero_apply,
            ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv] at h2
          exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
        have hBop : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y) =
              Ach.toE 2 E T (Ach.coord 2 T hfin) (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y) := by
          intro y
          rw [ArchAux.onePlus_apply, ArchAux.onePlus_apply, map_add, htoE rfl c y]
        have hker : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y = 0 → (g c) y = 0 := by
          intro y hy
          obtain ⟨f, hf1, hf2, hfc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj (Ach.toE 2 E T (Ach.coord 2 T hfin) y) (by rw [← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y), hBop, hy, map_zero])
          have h0 := hzero f ⟨hf1, hf2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hfc] at h0
          rwa [hAB y] at h0
        have hmem : (g c) ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) :
            (E ⊗[ZMod 2] T) →ₗ[ZMod 2] (E ⊗[ZMod 2] T)).dualMap.range := by
          rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
          intro y hy
          exact hker y (by simpa using hy)
        obtain ⟨ψ₀, hψ₀⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, ψ₀, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl]
        refine LinearMap.ext fun y => ?_
        rw [← hψ₀, ArchAux.onePlus_dualMap_apply, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv,
          LinearMap.add_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc g hg.1


end Work.SSGRoute
