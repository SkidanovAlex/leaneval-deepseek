import Mathlib
import Submission.Work.SSGRoute.E7Fin.RedLattice.InvDimFunctional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The invariant `X ↦ dim (X ⊗ N)^G` on the regular module

Lane `Work.SSGRoute.coker_obstruction_pt`.  This file proves

  `invDimFunctional p G N (RegMod p G) = dim_{𝔽_p} N`,

i.e. the additive invariant of `RedLattice/InvDimFunctional.lean` evaluated on the regular module
`𝔽_p[G]` (`RedLattice/Regular.lean`) is the `𝔽_p`-dimension of `N`.  In other words the
`G`-invariants of `𝔽_p[G] ⊗ N` (diagonal action) are `≅ N`: this is the "Frobenius reciprocity /
Shapiro" input behind the `(ε)` identity `ρ (Λ/pΛ) = n · ρ (𝔽_p[G])` of the lane, applied to the
invariant `X ↦ dim (X ⊗ N)^G`.

The proof is elementary and does **not** need `p ∤ |G|`.  Writing `M = 𝔽_p[G] = G → 𝔽_p` and

* `E : M ⊗ N → (G → N)`, `E (f ⊗ n) = fun g => f g • n` (`regModCoordMap`),
* `E' : (G → N) → M ⊗ N`, `E' c = ∑ g, δ_g ⊗ c g` (`regModSumMap`),

the identity `E' ∘ E = id` (`regModSumMap_regModCoordMap`) shows that `E` is injective.  For the
diagonal action `g • (m ⊗ n) = (g • m) ⊗ (g • n)`, `E` is `G`-equivariant in the sense

  `E (g • x) = fun k => g • (E x (g⁻¹ * k))`   (`regModCoordMap_smul`),

so an element `x` is fixed by `G` iff `E x g = g • (E x 1)` for all `g`.  Consequently the fixed
points of `M ⊗ N` are exactly the image of the injective map

  `n ↦ ∑ g, δ_g ⊗ (g • n)`   (`regModInvariants`),

whence `dim (M ⊗ N)^G = dim N`.
-/

namespace Work.SSGRoute.E7Fin.RedLattice

open Work.ArtinInduction.LatticeModp
open Work.SSGRoute.PTCore
open scoped TensorProduct

variable (p : ℕ) (G : Type) [Group G] [Fintype G]

/-! ## The coordinate map `(G → 𝔽_p) ⊗ N → (G → N)` and its inverse

Both linear maps below are the two halves of the `𝔽_p`-linear isomorphism
`𝔽_p[G] ⊗ N ≅ G → N` (the tensor product of a free module on the basis `{δ_g}` with `N`). -/

section CoordMap

variable (N : Type) [AddCommGroup N] [Module (ZMod p) N]

/-- **The coordinate map** `(G → 𝔽_p) ⊗ N →ₗ (G → N)`, `f ⊗ n ↦ (g ↦ f g • n)`. -/
noncomputable def regModCoordMap : ((G → ZMod p) ⊗[ZMod p] N) →ₗ[ZMod p] (G → N) :=
  TensorProduct.lift (LinearMap.mk₂ (ZMod p) (fun f n g => f g • n)
    (fun f₁ f₂ n => by funext g; simp only [Pi.add_apply, add_smul])
    (fun c f n => by funext g; simp only [Pi.smul_apply, smul_eq_mul, mul_smul])
    (fun f n₁ n₂ => by funext g; simp only [smul_add, Pi.add_apply])
    (fun c f n => by funext g; exact smul_comm (f g) c n))

/-- The coordinate map on a pure tensor: `f ⊗ n ↦ (g ↦ f g • n)`. -/
@[simp]
lemma regModCoordMap_tmul (f : G → ZMod p) (n : N) :
    regModCoordMap p G N (f ⊗ₜ[ZMod p] n) = fun g => f g • n := by
  rw [regModCoordMap, TensorProduct.lift.tmul]
  rfl

/-- **The "basis expansion"** `(G → N) →ₗ (G → 𝔽_p) ⊗ N`, `c ↦ ∑ g, δ_g ⊗ c g`, i.e. the map
inverse to the coordinate map. -/
noncomputable def regModSumMap : (G → N) →ₗ[ZMod p] ((G → ZMod p) ⊗[ZMod p] N) :=
  letI := Classical.decEq G
  { toFun := fun c => ∑ g : G, (Pi.single g (1 : ZMod p)) ⊗ₜ[ZMod p] (c g)
    map_add' := by
      intro c c'
      simp only [Pi.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r c
      simp only [Pi.smul_apply, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- The basis expansion of a "twisted" coordinate function: `∑ g, δ_g ⊗ (f g • n) = f ⊗ n`. -/
lemma regModSumMap_apply_smul (f : G → ZMod p) (n : N) :
    regModSumMap p G N (fun g => f g • n) = f ⊗ₜ[ZMod p] n := by
  classical
  show (∑ g : G, (Pi.single g (1 : ZMod p)) ⊗ₜ[ZMod p] (f g • n)) = f ⊗ₜ[ZMod p] n
  have hsum : (∑ g : G, f g • (Pi.single g (1 : ZMod p) : G → ZMod p)) = f := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne (M := fun _ : G => ZMod p) hb.symm (1 : ZMod p), smul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  calc ∑ g : G, (Pi.single g (1 : ZMod p)) ⊗ₜ[ZMod p] (f g • n)
      = ∑ g : G, (f g • (Pi.single g (1 : ZMod p) : G → ZMod p)) ⊗ₜ[ZMod p] n :=
        Finset.sum_congr rfl (fun g _ =>
          (TensorProduct.smul_tmul (f g) (Pi.single g (1 : ZMod p) : G → ZMod p) n).symm)
    _ = (∑ g : G, f g • (Pi.single g (1 : ZMod p) : G → ZMod p)) ⊗ₜ[ZMod p] n :=
        (TensorProduct.sum_tmul Finset.univ
          (fun g : G => f g • (Pi.single g (1 : ZMod p) : G → ZMod p)) n).symm
    _ = f ⊗ₜ[ZMod p] n := by rw [hsum]

/-- `E` and `E'` are mutually inverse: `E' ∘ E = id` on `𝔽_p[G] ⊗ N`. -/
lemma regModSumMap_regModCoordMap (x : (G → ZMod p) ⊗[ZMod p] N) :
    regModSumMap p G N (regModCoordMap p G N x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => rw [regModCoordMap_tmul, regModSumMap_apply_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `E` and `E'` are mutually inverse: `E ∘ E' = id` on `G → N`. -/
lemma regModCoordMap_regModSumMap (c : G → N) :
    regModCoordMap p G N (regModSumMap p G N c) = c := by
  classical
  have h : regModSumMap p G N c
      = ∑ g : G, (Pi.single g (1 : ZMod p)) ⊗ₜ[ZMod p] (c g) := rfl
  rw [h, map_sum]
  funext k
  rw [Finset.sum_apply]
  simp only [regModCoordMap_tmul]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne (M := fun _ : G => ZMod p) hb.symm (1 : ZMod p), zero_smul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The coordinate map is injective. -/
lemma regModCoordMap_injective : Function.Injective (regModCoordMap p G N) := by
  intro x y h
  have h' := congrArg (regModSumMap p G N) h
  rwa [regModSumMap_regModCoordMap p G N x,
    regModSumMap_regModCoordMap p G N y] at h'

end CoordMap

/-! ## The invariants of the regular module tensored with `N` -/

section Invariants

variable (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
  [SMulCommClass G (ZMod p) N]

/-- **Equivariance of the coordinate map** for the diagonal action on `𝔽_p[G] ⊗ N` and the
action `(g • c) k = g • (c (g⁻¹ * k))` on `G → N`. -/
lemma regModCoordMap_smul (g : G) (x : (G → ZMod p) ⊗[ZMod p] N) :
    regModCoordMap p G N (g • x)
      = fun k => g • (regModCoordMap p G N x (g⁻¹ * k)) := by
  induction x using TensorProduct.induction_on with
  | zero => ext k; simp
  | tmul f n =>
      rw [Work.Shrinking.diagTensor_smul_tmul, regModCoordMap_tmul, regModCoordMap_tmul]
      funext k
      rw [regMod_smul_apply]
      exact (smul_comm g (f (g⁻¹ * k)) n).symm
  | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy]
      funext k
      simp only [Pi.add_apply, smul_add]

/-- The map `n ↦ ∑ g, δ_g ⊗ (g • n)`, i.e. the "anti-diagonal" section of the coordinate map;
its image is the set of `G`-fixed points of `𝔽_p[G] ⊗ N`. -/
noncomputable def regModInvMap : N →ₗ[ZMod p] ((G → ZMod p) ⊗[ZMod p] N) where
  toFun n := regModSumMap p G N (fun g => g • n)
  map_add' n₁ n₂ := by
    rw [← map_add]
    congr 1
    funext g
    rw [Pi.add_apply, smul_add]
  map_smul' c n := by
    rw [← map_smul]
    congr 1
    funext g
    simp only [Pi.smul_apply, smul_comm, RingHom.id_apply]

/-- The coordinate map on the image of `regModInvMap`: `E (∑ g, δ_g ⊗ (g • n)) = fun g => g • n`. -/
lemma regModCoordMap_regModInvMap (n : N) :
    regModCoordMap p G N (regModInvMap p G N n) = fun g => g • n :=
  regModCoordMap_regModSumMap p G N (fun g => g • n)

/-- The image of `regModInvMap` consists of `G`-fixed points. -/
lemma regModInvMap_mem_invariants (n : N) :
    regModInvMap p G N n ∈ invariantsSubmodule G (ZMod p) ((G → ZMod p) ⊗[ZMod p] N) := by
  rw [mem_invariantsSubmodule]
  intro g
  apply regModCoordMap_injective p G N
  rw [regModCoordMap_smul, regModCoordMap_regModInvMap]
  funext k
  show g • ((g⁻¹ * k) • n) = k • n
  rw [← mul_smul, mul_inv_cancel_left]

/-- Every `G`-fixed point of `𝔽_p[G] ⊗ N` lies in the image of `regModInvMap`. -/
lemma invariants_le_range_regModInvMap :
    invariantsSubmodule G (ZMod p) ((G → ZMod p) ⊗[ZMod p] N)
      ≤ LinearMap.range (regModInvMap p G N) := by
  intro x hx
  rw [mem_invariantsSubmodule] at hx
  refine ⟨regModCoordMap p G N x 1, ?_⟩
  have hkey : ∀ g k : G, regModCoordMap p G N x (g * k) = g • regModCoordMap p G N x k := by
    intro g k
    have h1 : regModCoordMap p G N (g • x) = regModCoordMap p G N x := by rw [hx g]
    have h3 := congrFun h1 (g * k)
    rw [regModCoordMap_smul] at h3
    simp only [inv_mul_cancel_left] at h3
    exact h3.symm
  have hE : regModCoordMap p G N x = fun k => k • regModCoordMap p G N x 1 := by
    funext k
    simpa using hkey k 1
  change regModSumMap p G N (fun k => k • regModCoordMap p G N x 1) = x
  rw [← hE]
  exact regModSumMap_regModCoordMap p G N x

/-- `regModInvMap` is injective. -/
lemma regModInvMap_injective : Function.Injective (regModInvMap p G N) := by
  intro n₁ n₂ h
  have h1 := congrArg (regModCoordMap p G N) h
  rw [regModCoordMap_regModInvMap, regModCoordMap_regModInvMap] at h1
  have h2 := congrFun h1 1
  simpa using h2

end Invariants

/-! ## The invariant evaluated on the regular module -/

/-- **The invariant `X ↦ dim (X ⊗ N)^G` evaluated on the regular module is `dim N`.**

The `G`-invariants of `𝔽_p[G] ⊗ N` (diagonal action) form an `𝔽_p`-vector space isomorphic to
`N` (Frobenius reciprocity for the regular module), so their dimensions agree. -/
theorem invDimFunctional_regMod (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Work.SSGRoute.E7Fin.RedLattice.invDimFunctional p G N
        (Work.SSGRoute.E7Fin.RedLattice.RegMod p G) = (Module.finrank (ZMod p) N : ℚ) := by
  have hsub : invariantsSubmodule G (ZMod p) (RegMod p G ⊗[ZMod p] N)
      = LinearMap.range (regModInvMap p G N) :=
    le_antisymm (invariants_le_range_regModInvMap p G N)
      (by rintro x ⟨n, rfl⟩; exact regModInvMap_mem_invariants p G N n)
  have hfr : Module.finrank (ZMod p) ↥(invariantsSubmodule G (ZMod p)
        (RegMod p G ⊗[ZMod p] N)) = Module.finrank (ZMod p) N := by
    rw [hsub]
    exact (LinearEquiv.ofInjective (regModInvMap p G N) (regModInvMap_injective p G N)).finrank_eq.symm
  show (Module.finrank (ZMod p) ↥(invariantsSubmodule G (ZMod p)
        (RegMod p G ⊗[ZMod p] N)) : ℚ) = (Module.finrank (ZMod p) N : ℚ)
  exact_mod_cast hfr

end Work.SSGRoute.E7Fin.RedLattice
