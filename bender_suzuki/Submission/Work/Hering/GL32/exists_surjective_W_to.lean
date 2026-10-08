import Mathlib
import Submission.Work.Hering.GL32.AppIXP0
import Submission.Work.Hering.GL32.pair_smul_transitive
import Submission.Work.Hering.GL32.pgroup_fixed_ne_bot
import Submission.Work.Hering.GL32.isPGroup_pairStab
import Submission.Work.Hering.GL32.fixedVectorTwoGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: the Frobenius step

Simplicity of the `F₂[GL(3,2)]`-module `M` together with transitivity of `GL(3,2)` on the pairs of
points of `PG(2,2)` produces a surjective `GL(3,2)`-equivariant linear map `W ↠ M`, where
`W = F₂[Ω]` is the permutation module on the `21` pairs, concretely `W = Pair → ZMod 2` with the
action `actW`.

The construction: the stabiliser `pairStab` of the standard pair `p₀` is a `2`-group, so it fixes a
nonzero vector `m ∈ M`; choosing for every pair `q` an element `gp q` with `gp q • p₀ = q`, the map
`ψ : W → M` given by `ψ f = Σ_q f q • ρ (gp q) m` is `GL(3,2)`-equivariant, because two choices
`gp q` differ by an element of `pairStab` and hence have the same effect on `m`.  Its range is a
nonzero `ρ`-invariant subspace of the simple module `M`, hence everything.
-/

set_option maxHeartbeats 1000000

namespace Work.Hering.GL32

section

set_option autoImplicit false

/-! ## A coherent choice of group elements carrying `p₀` to `q` -/

/-- A choice, for every pair `q`, of an element of `GL(3,2)` carrying the standard pair to `q`. -/
noncomputable def gp (q : Pair) : GL32 := Classical.choose (pair_smul_transitive q)

lemma gp_smul_p₀ (q : Pair) : gp q • p₀ = q := Classical.choose_spec (pair_smul_transitive q)

/-! ## The map `W → M` attached to a fixed vector -/

/-- The linear map `W → M`, `f ↦ Σ_q f q • ρ (gp q) m`, attached to the vector `m`. -/
noncomputable def psiOf {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M) : W →ₗ[ZMod 2] M :=
  ∑ p : Pair, LinearMap.smulRight (LinearMap.proj p) (ρ (gp p) m)

lemma psiOf_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M) (f : W) :
    psiOf ρ m f = ∑ p : Pair, f p • (ρ (gp p) m) := by
  simp only [psiOf, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

lemma psiOf_single {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M) (q : Pair) :
    psiOf ρ m (Pi.single q (1 : ZMod 2) : W) = ρ (gp q) m := by
  rw [psiOf_apply]
  rw [Finset.sum_eq_single q]
  · rw [Pi.single_eq_same, one_smul]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp, zero_smul]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

/-! ## Equivariance of `ψ` -/

/-- The chosen elements `gp` are coherent on `m`: since `pairStab` fixes `m`, the effect of `gp q`
on `m` depends only on the image `gp q • p₀ = q` of the standard pair. -/
lemma rho_gp_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M)
    (hm : ∀ g : GL32, g ∈ pairStab → ρ g m = m) (g : GL32) (q : Pair) :
    ρ (gp (g • q)) m = ρ (g * gp q) m := by
  have hmem : (g * gp q)⁻¹ * gp (g • q) ∈ pairStab := by
    rw [mem_pairStab_iff]
    show ((g * gp q)⁻¹ * gp (g • q)) • p₀ = p₀
    have h : g • q = (g * gp q) • p₀ := by
      calc g • q = g • (gp q • p₀) := by rw [gp_smul_p₀]
        _ = (g * gp q) • p₀ := (mul_smul g (gp q) p₀).symm
    rw [mul_smul, gp_smul_p₀, h, inv_smul_smul]
  have hm' : ρ ((g * gp q)⁻¹ * gp (g • q)) m = m := hm _ hmem
  have hprod : gp (g • q) = (g * gp q) * ((g * gp q)⁻¹ * gp (g • q)) := by group
  calc ρ (gp (g • q)) m
      = ρ ((g * gp q) * ((g * gp q)⁻¹ * gp (g • q))) m := by
          conv_lhs => rw [hprod]
    _ = (ρ (g * gp q) * ρ ((g * gp q)⁻¹ * gp (g • q))) m := by
          conv_lhs => rw [map_mul]
    _ = ρ (g * gp q) (ρ ((g * gp q)⁻¹ * gp (g • q)) m) := LinearEquiv.mul_apply _ _ m
    _ = ρ (g * gp q) m := by rw [hm']

/-- **`ψ` is `GL(3,2)`-equivariant.** -/
lemma psiOf_actW {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M)
    (hm : ∀ g : GL32, g ∈ pairStab → ρ g m = m) (g : GL32) (f : W) :
    psiOf ρ m (actW g f) = ρ g (psiOf ρ m f) := by
  have hL : psiOf ρ m (actW g f) = ∑ p : Pair, f ((pairPerm g).symm p) • (ρ (gp p) m) := by
    rw [psiOf_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [actW_apply, Function.comp_apply]
  have hR : ρ g (psiOf ρ m f) = ∑ q : Pair, f q • (ρ (g * gp q) m) := by
    rw [psiOf_apply, map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [map_smul, ← LinearEquiv.mul_apply, ← map_mul]
  rw [hL, hR]
  rw [← Equiv.sum_comp (pairPerm g) (fun p : Pair => f ((pairPerm g).symm p) • (ρ (gp p) m))]
  simp only [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  show f q • (ρ (gp (g • q)) m) = f q • (ρ (g * gp q) m)
  rw [rho_gp_eq ρ m hm g q]

/-! ## Surjectivity of `ψ` -/

/-- **`ψ` is onto**, because its range is a nonzero `ρ`-invariant subspace of the simple module
`M`. -/
lemma psiOf_surjective {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (m : M) (hm0 : m ≠ 0)
    (hm : ∀ g : GL32, g ∈ pairStab → ρ g m = m)
    (hsimple : ∀ W' : Submodule (ZMod 2) M,
      (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤) :
    Function.Surjective (psiOf ρ m) := by
  rw [← LinearMap.range_eq_top]
  have hinv : ∀ g, ∀ w ∈ LinearMap.range (psiOf ρ m),
      ρ g w ∈ LinearMap.range (psiOf ρ m) := by
    intro g w hw
    obtain ⟨f, rfl⟩ := hw
    exact ⟨actW g f, psiOf_actW ρ m hm g f⟩
  rcases hsimple _ hinv with h | h
  · exfalso
    have hmem : psiOf ρ m (Pi.single p₀ (1 : ZMod 2) : W) ∈ LinearMap.range (psiOf ρ m) :=
      LinearMap.mem_range.mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    rw [psiOf_single] at hmem
    exact hm0 ((ρ (gp p₀)).injective (by rw [hmem, map_zero]))
  · exact h

end

theorem exists_surjective_W_to {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (hne : ∃ m : M, m ≠ 0) (hsimple : ∀ W' : Submodule (ZMod 2) M, (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤) : ∃ ψ : W →ₗ[ZMod 2] M, Function.Surjective ψ ∧ ∀ g f, ψ (actW g f) = ρ g (ψ f) := by
  haveI : Finite GL32 :=
    Finite.of_injective (fun g : GL32 => ⇑g)
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  obtain ⟨m, hm0, hmfix⟩ :=
    fixedVectorTwoGroup (P := pairStab) hne isPGroup_pairStab
      (ρ.comp pairStab.subtype)
  exact ⟨psiOf ρ m, psiOf_surjective ρ m hm0 (fun g hg => hmfix ⟨g, hg⟩) hsimple,
    fun g f => psiOf_actW ρ m (fun g hg => hmfix ⟨g, hg⟩) g f⟩

end Work.Hering.GL32
