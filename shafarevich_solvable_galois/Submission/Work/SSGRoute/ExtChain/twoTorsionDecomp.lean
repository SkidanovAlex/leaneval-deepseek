import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.ExtChain.PtorsionDecompDefs
import Submission.Work.SSGRoute.ExtChain.zmodTwoJordan
import Submission.Work.SSGRoute.ExtChain.shiftCoordinateEquiv
import Submission.Work.SSGRoute.ExtChain.cardTwoGenerator
import Submission.Work.SSGRoute.ExtChain.ext2_fn_two_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The structure theorem for finite `𝔽₂[C₂]`-modules

Let `H` be a group of order two and `N` a finite `𝔽₂[H]`-module (a representation of `H` on a
finite module killed by `2`).  Then `N` is a direct sum of copies of the trivial module `𝔽₂` and of
the regular module `𝔽₂[H]`: there are `a, b` and coordinate maps

    `inclT : trivPow' a ⟶ N`, `projT : N ⟶ trivPow' a`,
    `inclR : regPow' b ⟶ N`, `projR : N ⟶ regPow' b`

with `projT ≫ inclT + projR ≫ inclR = 𝟙 N`.

The proof reduces to the Jordan normal form `zmod_two_jordan` of the involution `S = N.ρ σ`
(`ε = S - 1`, `ε² = 0`), together with the change of basis `shiftCoordinateEquiv` identifying `b`
copies of the 2-dimensional transvection `(x, y) ↦ (x, x + y)` with the free `𝔽₂[H]`-module of
rank `b`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped MonoidAlgebra
open Work.ExtChain (trivPow regPow)

noncomputable section

attribute [local instance] Classical.decEq

attribute [local instance 2000] Rep.hV2

variable {H : Type} [Group H]

/-- The trivial `𝔽₂[H]`-module of rank `a`, written as an `abbrev` so that its carrier type is
*transparently* `Fin a →₀ ZMod 2`. -/
abbrev trivPow' (a : ℕ) : Rep.{0} Coeff H := Rep.trivial Coeff H (Fin a →₀ ZMod 2)

/-- The free (regular) `𝔽₂[H]`-module of rank `b`, written as an `abbrev` so that its carrier type
is *transparently* `Fin b →₀ 𝔽₂[H]`. -/
abbrev regPow' (b : ℕ) : Rep.{0} Coeff H :=
  Rep.ofDistribMulAction Coeff H (Fin b →₀ MonoidAlgebra (ZMod 2) H)

/-- **The structure theorem for finite `𝔽₂[C₂]`-modules.** -/
theorem two_torsion_decomp (hH : Nat.card H = 2) (N : Rep.{0} Coeff H) [Finite N.V]
    (hN : ∀ x : N.V, (2 : Coeff) • x = 0) :
    ∃ (a b : ℕ) (inclT : trivPow' a ⟶ N) (projT : N ⟶ trivPow' a)
      (inclR : regPow' b ⟶ N) (projR : N ⟶ regPow' b),
      projT ≫ inclT + projR ≫ inclR = 𝟙 N := by
  classical
  obtain ⟨σ, hσne, hσsq, hgen⟩ := cardTwoGenerator hH
  have h2n : ∀ x : N.V, (2 : ℕ) • x = 0 := fun x => by
    rw [← coeff_two_smul_eq_two_nsmul (x := x)]
    exact hN x
  letI : Module (ZMod 2) N.V := AddCommGroup.zmodModule h2n
  -- the involution `S = ρ σ`
  have hσσ : ∀ v : N.V, N.ρ σ (N.ρ σ v) = v := fun v => by
    simp only [← Module.End.mul_apply, ← map_mul, hσsq, map_one, Module.End.one_apply]
  let S : N.V ≃ₗ[ZMod 2] N.V :=
    { toFun := fun v => N.ρ σ v
      invFun := fun v => N.ρ σ⁻¹ v
      left_inv := fun v => by
        have h : (N.ρ σ⁻¹ * N.ρ σ) v = v := by
          rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [Module.End.mul_apply] at h
      right_inv := fun v => by
        have h : (N.ρ σ * N.ρ σ⁻¹) v = v := by
          rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rwa [Module.End.mul_apply] at h
      map_add' := fun v w => map_add (N.ρ σ) v w
      map_smul' := fun c v => ZMod.map_smul (N.ρ σ) c v }
  have hS : S * S = 1 := by
    apply LinearEquiv.ext
    intro v
    show (S * S) v = (1 : N.V ≃ₗ[ZMod 2] N.V) v
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]
    exact hσσ v
  obtain ⟨a, b, e, he⟩ := zmod_two_jordan S hS
  obtain ⟨Ψ, _hΨapp, hΨeq⟩ := shiftCoordinateEquiv (H := H) σ hσne hσsq hgen b
  -- Finsupp/function comparisons
  let funA : (Fin a →₀ ZMod 2) ≃ₗ[ZMod 2] (Fin a → ZMod 2) :=
    Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin a)
  let funB : (Fin b →₀ MonoidAlgebra (ZMod 2) H) ≃ₗ[ZMod 2]
      (Fin b → MonoidAlgebra (ZMod 2) H) :=
    Finsupp.linearEquivFunOnFinite (ZMod 2) (MonoidAlgebra (ZMod 2) H) (Fin b)
  have hfunA_apply : ∀ z : Fin a →₀ ZMod 2, funA z = fun j => z j := fun _ => rfl
  have hfunB_apply : ∀ r : Fin b →₀ MonoidAlgebra (ZMod 2) H, funB r = fun j => r j :=
    fun _ => rfl
  -- the reordering of the three blocks
  let mfun : ((Fin a → ZMod 2) × (Fin b → MonoidAlgebra (ZMod 2) H)) →ₗ[ZMod 2]
      ((Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))) :=
    { toFun := fun t => ((Ψ.symm t.2).1, (t.1, (Ψ.symm t.2).2))
      map_add' := fun t t' => by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
      map_smul' := fun c t => by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply,
          RingHom.id_apply] }
  let minv : ((Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))) →ₗ[ZMod 2]
      ((Fin a → ZMod 2) × (Fin b → MonoidAlgebra (ZMod 2) H)) :=
    { toFun := fun t => (t.2.1, Ψ (t.1, t.2.2))
      map_add' := fun t t' => by
        have h : ((t + t').1, (t + t').2.2) = (t.1, t.2.2) + (t'.1, t'.2.2) := rfl
        show ((t + t').2.1, Ψ ((t + t').1, (t + t').2.2))
          = (t.2.1, Ψ (t.1, t.2.2)) + (t'.2.1, Ψ (t'.1, t'.2.2))
        rw [h, map_add]
        rfl
      map_smul' := fun c t => by
        have h : ((c • t).1, (c • t).2.2) = c • (t.1, t.2.2) := rfl
        show ((c • t).2.1, Ψ ((c • t).1, (c • t).2.2))
          = c • (t.2.1, Ψ (t.1, t.2.2))
        rw [h, map_smul]
        rfl }
  have hmfun_apply : ∀ (t : (Fin a → ZMod 2) × (Fin b → MonoidAlgebra (ZMod 2) H)),
      mfun t = ((Ψ.symm t.2).1, (t.1, (Ψ.symm t.2).2)) := fun _ => rfl
  have hminv_apply : ∀ (t : (Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))),
      minv t = (t.2.1, Ψ (t.1, t.2.2)) := fun _ => rfl
  have hml : minv.comp mfun = LinearMap.id := by
    apply LinearMap.ext
    intro t
    show minv (mfun t) = t
    rw [hmfun_apply, hminv_apply,
      show ((Ψ.symm t.2).1, (Ψ.symm t.2).2) = Ψ.symm t.2 from rfl,
      LinearEquiv.apply_symm_apply, Prod.mk.eta]
  have hmr : mfun.comp minv = LinearMap.id := by
    apply LinearMap.ext
    intro t
    show mfun (minv t) = t
    rw [hminv_apply, hmfun_apply, LinearEquiv.symm_apply_apply, Prod.mk.eta]
  let mEquiv : ((Fin a → ZMod 2) × (Fin b → MonoidAlgebra (ZMod 2) H)) ≃ₗ[ZMod 2]
      ((Fin b → ZMod 2) × ((Fin a → ZMod 2) × (Fin b → ZMod 2))) :=
    LinearEquiv.ofLinearMap mfun minv hmr hml
  -- the coordinate linear equivalence `θ`
  let θ : ((Fin a →₀ ZMod 2) × (Fin b →₀ MonoidAlgebra (ZMod 2) H)) ≃ₗ[ZMod 2] N.V :=
    funA.prodCongr funB ≪≫ₗ mEquiv ≪≫ₗ e
  have hθ : ∀ (z : Fin a →₀ ZMod 2) (r : Fin b →₀ MonoidAlgebra (ZMod 2) H),
      θ (z, r) = e ((Ψ.symm (funB r)).1, (funA z, (Ψ.symm (funB r)).2)) := by
    intro z r
    show e (mfun (funA z, funB r)) = e ((Ψ.symm (funB r)).1, (funA z, (Ψ.symm (funB r)).2))
    rw [hmfun_apply]
  -- the action of `H` in these coordinates
  have hfunB_rho : ∀ (g : H) (r : Fin b →₀ MonoidAlgebra (ZMod 2) H),
      funB ((regPow' b).ρ g r) = g • funB r := by
    intro g r
    rw [show (regPow' b).ρ g r = g • r from rfl]
    ext j
    simp only [hfunB_apply, Pi.smul_apply]
    rfl
  have hθρ : ∀ (g : H) (z : Fin a →₀ ZMod 2) (r : Fin b →₀ MonoidAlgebra (ZMod 2) H),
      N.ρ g (θ (z, r)) = θ ((trivPow' a).ρ g z, (regPow' b).ρ g r) := by
    intro g z r
    rcases hgen g with hg | hg
    · rw [hg, map_one, map_one, map_one]
      rfl
    · rw [hg, show (trivPow' a).ρ σ z = z from Rep.trivial_ρ_apply σ z]
      set t : (Fin b → ZMod 2) × (Fin b → ZMod 2) := Ψ.symm (funB r) with ht
      have hΨt : Ψ t = funB r := by rw [ht]; exact LinearEquiv.apply_symm_apply Ψ (funB r)
      have hkey : Ψ.symm (σ • funB r) = (t.1, t.1 + t.2) := by
        have h1 : σ • funB r = Ψ (t.1, t.1 + t.2) := by
          rw [← hΨt]
          exact hΨeq t.1 t.2
        rw [h1, LinearEquiv.symm_apply_apply]
      have hL : N.ρ σ (θ (z, r)) = e (t.1, (funA z, t.1 + t.2)) := by
        have hz : θ (z, r) = e (t.1, (funA z, t.2)) := by rw [hθ, ← ht]
        rw [hz]
        exact he (t.1, (funA z, t.2))
      have hR : θ (z, (regPow' b).ρ σ r) = e (t.1, (funA z, t.1 + t.2)) := by
        refine (hθ z ((regPow' b).ρ σ r)).trans ?_
        rw [hfunB_rho σ r, hkey]
      rw [hL, hR]
  -- the four coordinate maps
  let projTf : N.V →+ (Fin a →₀ ZMod 2) :=
    { toFun := fun v => (θ.symm v).1
      map_zero' := by simp
      map_add' := fun v w => by rw [map_add]; rfl }
  let projRf : N.V →+ (Fin b →₀ MonoidAlgebra (ZMod 2) H) :=
    { toFun := fun v => (θ.symm v).2
      map_zero' := by simp
      map_add' := fun v w => by rw [map_add]; rfl }
  let inclTf : (Fin a →₀ ZMod 2) →+ N.V :=
    { toFun := fun z => θ (z, 0)
      map_zero' := by simp
      map_add' := fun z z' => by
        rw [← map_add]
        simp }
  let inclRf : (Fin b →₀ MonoidAlgebra (ZMod 2) H) →+ N.V :=
    { toFun := fun r => θ (0, r)
      map_zero' := by simp
      map_add' := fun r r' => by
        rw [← map_add]
        simp }
  have hρzeroR : ∀ g : H, ((regPow' b).ρ g) (0 : Fin b →₀ MonoidAlgebra (ZMod 2) H)
      = (0 : Fin b →₀ MonoidAlgebra (ZMod 2) H) := fun g => map_zero ((regPow' b).ρ g)
  have hρzeroT : ∀ g : H, ((trivPow' a).ρ g) (0 : Fin a →₀ ZMod 2)
      = (0 : Fin a →₀ ZMod 2) := fun g => map_zero ((trivPow' a).ρ g)
  have hprojT : ∀ (g : H) (v : N.V),
      projTf (N.ρ g v) = (trivPow' a).ρ g (projTf v) := by
    intro g v
    have hv : N.ρ g v
        = θ ((trivPow' a).ρ g (θ.symm v).1, (regPow' b).ρ g (θ.symm v).2) := by
      conv_lhs => rw [← θ.apply_symm_apply v]
      exact hθρ g (θ.symm v).1 (θ.symm v).2
    have h2 : θ.symm (N.ρ g v)
        = ((trivPow' a).ρ g (θ.symm v).1, (regPow' b).ρ g (θ.symm v).2) := by
      refine θ.injective ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hv
    show (θ.symm (N.ρ g v)).1 = (trivPow' a).ρ g (θ.symm v).1
    rw [h2]
  have hprojR : ∀ (g : H) (v : N.V),
      projRf (N.ρ g v) = (regPow' b).ρ g (projRf v) := by
    intro g v
    have hv : N.ρ g v
        = θ ((trivPow' a).ρ g (θ.symm v).1, (regPow' b).ρ g (θ.symm v).2) := by
      conv_lhs => rw [← θ.apply_symm_apply v]
      exact hθρ g (θ.symm v).1 (θ.symm v).2
    have h2 : θ.symm (N.ρ g v)
        = ((trivPow' a).ρ g (θ.symm v).1, (regPow' b).ρ g (θ.symm v).2) := by
      refine θ.injective ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hv
    show (θ.symm (N.ρ g v)).2 = (regPow' b).ρ g (θ.symm v).2
    rw [h2]
  have hinclT : ∀ (g : H) (z : Fin a →₀ ZMod 2),
      inclTf ((trivPow' a).ρ g z) = N.ρ g (inclTf z) := by
    intro g z
    show θ ((trivPow' a).ρ g z, (0 : Fin b →₀ MonoidAlgebra (ZMod 2) H)) = N.ρ g (θ (z, 0))
    rw [hθρ g z 0, hρzeroR g]
  have hinclR : ∀ (g : H) (r : Fin b →₀ MonoidAlgebra (ZMod 2) H),
      inclRf ((regPow' b).ρ g r) = N.ρ g (inclRf r) := by
    intro g r
    show θ ((0 : Fin a →₀ ZMod 2), (regPow' b).ρ g r) = N.ρ g (θ (0, r))
    rw [hθρ g 0 r, hρzeroT g]
  refine ⟨a, b,
    Rep.ofHom (intertwiningMapOfAddHom (trivPow' a).hV2 N.hV2 inclTf hinclT),
    Rep.ofHom (intertwiningMapOfAddHom N.hV2 (trivPow' a).hV2 projTf hprojT),
    Rep.ofHom (intertwiningMapOfAddHom (regPow' b).hV2 N.hV2 inclRf hinclR),
    Rep.ofHom (intertwiningMapOfAddHom N.hV2 (regPow' b).hV2 projRf hprojR), ?_⟩
  apply Rep.hom_ext
  apply DFunLike.ext
  intro v
  change inclTf (projTf v) + inclRf (projRf v) = v
  have h1 : inclTf (projTf v) = θ ((θ.symm v).1, 0) := rfl
  have h2 : inclRf (projRf v) = θ (0, (θ.symm v).2) := rfl
  rw [h1, h2, ← map_add]
  have h3 : ((θ.symm v).1, (0 : Fin b →₀ MonoidAlgebra (ZMod 2) H))
      + ((0 : Fin a →₀ ZMod 2), (θ.symm v).2) = θ.symm v := by
    ext <;> simp
  rw [h3, LinearEquiv.apply_symm_apply]

end

end Work.SSGRoute.ExtChain
