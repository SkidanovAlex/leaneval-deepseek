import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.PT.archSwapHalf
import Submission.Work.SSGRoute.PT.decompK_linked
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-- **`z_b`, step 1: the descent of a local `⟨c⟩`-cocycle to the decomposition group `D_{u_c}`.**

`L_c` is the fixed level of `flags_2305` (chosen independently of `b`), `res_{L_c} c ≠ 1`, and `u_c`
its seam place with `D_{u_c} = (⟨c⟩).map (res k L_c)` (`PT.decompK_linked`).  Because `res_{L_c} c ≠ 1`,
the restriction `res k L_c` is injective on `⟨c⟩` — its kernel meets `⟨c⟩` trivially, since
`c ∈ ⟨c⟩ ∩ Gal(Ω/L_c)` would force `D_{u_c} = ⊥` — so a cocycle `b` on `⟨c⟩` descends to a
well-defined cocycle `bD` on `D_{u_c}` by `bD (res σ) := b σ`.

Route (measured, both reviewers).  Define `bD g := b (Classical.choose hpre)` for
`hpre g : ∃ σ ∈ ⟨c⟩, res k L_c σ = g` (`g ∈ D_{u_c}` from `hDu` and `Subgroup.mem_map`);
well-definedness uses injectivity of `res k L_c` on `⟨c⟩` (`⟨c⟩ = {1,c}` by `hc2`, and `res c ≠ 1` by
`hres`); the cocycle condition transports along the bijection `⟨c⟩ ≅ D_{u_c}`, the actions agreeing
because `galRes k ↥K ↥L_c (res k L_c σ) = res k K σ` (the `restrictNormalHom_comp_apply`-shape
identity, as in `PT/factorised_isCrossedHom.lean`).

This is `z_b` before the `H¹`/`eCoh` packaging (`z_b` is the class of `bD`), and it is the only new
construction `flags_2305`'s local `archPair` needs. -/
theorem localCocycle_descent_exists (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    ∃ bD : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T,
      (∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) u),
        bD (g * h) = bD g + SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L) • bD h) ∧
      ∀ σ : ↥(Subgroup.zpowers c),
        bD ⟨SSGRoute.res k L σ.1,
            by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ = b σ.1 := by
  classical
  -- `⟨c⟩ = {1, c}`: an involution generates a subgroup with at most two elements.
  have hc2z : c ^ (2 : ℤ) = 1 := by simpa using hc2
  have hclass : ∀ x : Ω ≃ₐ[k] Ω, x ∈ Subgroup.zpowers c → x = 1 ∨ x = c := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨m, rfl⟩ := hx
    have hmod : c ^ m = c ^ (m % 2) := zpow_eq_zpow_emod m hc2z
    rw [hmod]
    have hlt : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases hlt with h | h <;> rw [h] <;> simp
  -- `res k L` is injective on `⟨c⟩`, because `res k L c ≠ 1`.
  have hinj : ∀ σ ∈ Subgroup.zpowers c, ∀ τ ∈ Subgroup.zpowers c,
      SSGRoute.res k L σ = SSGRoute.res k L τ → σ = τ := by
    intro σ hσ τ hτ heq
    have hmem : σ⁻¹ * τ ∈ Subgroup.zpowers c := mul_mem (inv_mem hσ) hτ
    have hone : SSGRoute.res k L (σ⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    rcases hclass (σ⁻¹ * τ) hmem with h | h
    · exact inv_mul_eq_one.mp h
    · rw [h] at hone
      exact absurd hone hres
  -- The restriction `⟨c⟩ → D_{u_c}` is a `MulEquiv` (it is injective and, by `hDu`, onto).
  let f : ↥(Subgroup.zpowers c) →* ↥(SSGRoute.PTExt.decompK (k := k) u) :=
    { toFun := fun σ => ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun σ τ => Subtype.ext (by simp) }
  have hfinj : Function.Injective f := by
    intro σ τ h
    have h1 : SSGRoute.res k L σ.1 = SSGRoute.res k L τ.1 := congrArg Subtype.val h
    exact Subtype.ext (hinj σ.1 σ.2 τ.1 τ.2 h1)
  have hfsurj : Function.Surjective f := by
    intro g
    have hg : (g : ↥L ≃ₐ[k] ↥L) ∈ (Subgroup.zpowers c).map (SSGRoute.res k L) := by
      rw [← hDu]; exact g.2
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hg
    exact ⟨⟨σ, hσ⟩, Subtype.ext hσeq⟩
  let e : ↥(Subgroup.zpowers c) ≃* ↥(SSGRoute.PTExt.decompK (k := k) u) :=
    MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  -- The descended cochain, `b` read through the inverse of the restriction bijection.
  let bD : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T :=
    fun g => b ((e.symm g : ↥(Subgroup.zpowers c)).1)
  have key : ∀ σ : ↥(Subgroup.zpowers c), bD (f σ) = b σ.1 := by
    intro σ
    have hsym : (e.symm (f σ) : ↥(Subgroup.zpowers c)) = σ := by
      rw [show f σ = e σ from rfl, MulEquiv.symm_apply_apply]
    show b ((e.symm (f σ) : ↥(Subgroup.zpowers c)).1) = b σ.1
    rw [hsym]
  -- `bD ∘ res = b` on `⟨c⟩`.
  have h2 : ∀ σ : ↥(Subgroup.zpowers c),
      bD ⟨SSGRoute.res k L σ.1,
          by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ = b σ.1 := by
    intro σ
    rw [show (⟨SSGRoute.res k L σ.1,
          by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
        = f σ from Subtype.ext rfl]
    exact key σ
  -- The cocycle identity transports along the restriction bijection; the two actions agree by
  -- `IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`.
  have h1 : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) u),
      bD (g * h) = bD g + SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L) • bD h := by
    intro g h
    set σ : ↥(Subgroup.zpowers c) := e.symm g with hσdef
    set τ : ↥(Subgroup.zpowers c) := e.symm h with hτdef
    have hg : f σ = g := by rw [hσdef]; exact MulEquiv.apply_symm_apply e g
    have hh : f τ = h := by rw [hτdef]; exact MulEquiv.apply_symm_apply e h
    have hbg : bD g = b σ.1 := by rw [← hg]; exact key σ
    have hbh : bD h = b τ.1 := by rw [← hh]; exact key τ
    have hgh : g * h = f (σ * τ) := by rw [map_mul, hg, hh]
    rw [hgh, hbg, hbh, key (σ * τ)]
    have hcoc := hb σ.1 σ.2 τ.1 τ.2
    rw [show (σ * τ).1 = σ.1 * τ.1 from rfl, hcoc]
    have hgval : (g : ↥L ≃ₐ[k] ↥L) = SSGRoute.res k L σ.1 := (congrArg Subtype.val hg).symm
    have hcomp : SSGRoute.res k K σ.1
        = SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L) := by
      rw [hgval]
      exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥K) (↥L) σ.1
    rw [hcomp]
  exact ⟨bD, h1, h2⟩

end Work.SSGRoute.PT
