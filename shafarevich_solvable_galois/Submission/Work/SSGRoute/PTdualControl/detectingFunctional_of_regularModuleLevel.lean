import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.SSGStage.exists_regularModule_inert_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The detecting functional on a regular-module level

This file proves `Work.SSGRoute.PTdualControl.detectingFunctional_of_regularModuleLevel`: on a
level `L ⊇ K` at which the kernel `N = ker (galRes k K L)` of the restriction map
`galRes k K L : Gal(L/k) →* Gal(K/k)` is the **regular** `Gal(K/k)`-module
(`e : N ≃* Multiplicative (Gal(K/k) → ZMod p)`, intertwining conjugation with left translation,
hypothesis `he`), every non-zero `D_w`-equivariant functional `μ` on a `p`-torsion
`Gal(K/k)`-module `M` is detected by a `Gal(L/k)`-equivariant additive functional
`φ : N → M` which vanishes on the coordinates of the inertia subgroup at `q'` (`hI`) and which
`μ` does not kill at the `N`-coordinate of some element `d` of the decomposition group of `q'`
(`hd`).

The construction is the standard one for the regular module: fix `m₀ ∈ M` with `μ m₀ ≠ 0` and set

`φ (g) = ∑_{γ ∈ Gal(K/k)} (e g) γ • (γ • m₀)`,

the sum of the "coordinate weights" of `e g` against the orbit of `m₀`.  Because `e` intertwines
conjugation with left translation, `φ` is `Gal(L/k)`-equivariant; the coordinate of an inertia
element is trivial (`hI`), so `φ` vanishes there; and the element `d` supplied by `hd` has
coordinate the indicator function of the identity, so `φ (coordKer d) = m₀` and `μ` does not kill
it.

Everything above is linear algebra over `ZMod p` on the `p`-torsion module `M`; the arithmetic
content (existence of such a level) is the separate input
`Work.SSGRoute.SSGStage.exists_regularModule_level`.
-/

namespace Work.SSGRoute.PTdualControl

/-- **A non-zero morphism of `Rep`s is non-zero at some element.**  Used to extract an `m₀` with
`μ m₀ ≠ 0` from `μ ≠ 0`. -/
theorem exists_apply_ne_zero_of_rep_hom_ne_zero {R : Type*} [Ring R] {G : Type*} [Group G]
    {A B : Rep R G} (f : A ⟶ B) (hf : f ≠ 0) : ∃ m : A.V, f.hom m ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  apply Rep.hom_ext
  apply DFunLike.coe_injective (F := A.ρ.IntertwiningMap B.ρ)
  show (fun m : A.V => f.hom m) = (fun m : A.V => (0 : A.ρ.IntertwiningMap B.ρ) m)
  funext m
  rw [h m]
  simp

/-- **Equivariance of the regular-module sum.**  For a finite group `G`, a `ZMod p`-module `V`
with an action `ρ` of `G` and an element `m₀ ∈ V`, the "weighted orbit sum"
`f ↦ ∑_{γ} f γ • (ρ γ m₀)` transforms the coefficient function by left translation:
replacing `f` by `f ∘ (σ⁻¹ * ·)` applies `ρ σ`. -/
theorem regSum_translate {p : ℕ} {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module (ZMod p) V] (ρ : G →* (V →ₗ[ZMod p] V)) (m₀ : V) (f : G → ZMod p) (σ : G) :
    (∑ γ, f (σ⁻¹ * γ) • (ρ γ m₀)) = ρ σ (∑ γ, f γ • (ρ γ m₀)) := by
  rw [map_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft σ) (fun γ => f (σ⁻¹ * γ) • (ρ γ m₀))]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp only [Equiv.coe_mulLeft, MonoidHom.map_mul, map_smul, inv_mul_cancel_left]
  congr 1

/-- **The weighted orbit sum at the indicator of the identity.**  If the coefficient function `v`
is the indicator function of `1 ∈ G` (i.e. `v 1 = 1` and `v τ = 0` for `τ ≠ 1`), then the
weighted orbit sum is `m₀` itself. -/
theorem regSum_single {p : ℕ} {G V : Type*} [Group G] [Fintype G] [AddCommGroup V]
    [Module (ZMod p) V] (ρ : G →* (V →ₗ[ZMod p] V)) (m₀ : V) (v : G → ZMod p) (hv1 : v 1 = 1)
    (hv0 : ∀ τ : G, τ ≠ 1 → v τ = 0) : (∑ γ, v γ • (ρ γ m₀)) = m₀ := by
  classical
  have hv : v = Pi.single (1 : G) (1 : ZMod p) := by
    funext τ
    rw [Pi.single_apply]
    by_cases h : τ = 1
    · rw [if_pos h, h, hv1]
    · rw [if_neg h, hv0 τ h]
  rw [hv]
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne, hb]
  · intro h1
    exact absurd (Finset.mem_univ 1) h1

theorem detectingFunctional_of_regularModuleLevel
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (hM : ∀ m : M.V, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃* Multiplicative ((K ≃ₐ[k] K) → ZMod p))
    (he : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
        = Multiplicative.ofAdd (fun τ : K ≃ₐ[k] K =>
            Multiplicative.toAdd (e g) ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ)))
    (hI : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1)
    (hd : ∃ d : ↥L ≃ₐ[k] ↥L,
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      ∃ v : (K ≃ₐ[k] K) → ZMod p, v 1 = 1 ∧ (∀ τ : K ≃ₐ[k] K, τ ≠ 1 → v τ = 0) ∧
        e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d) = Multiplicative.ofAdd v)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V,
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
          = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) ∧
      (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0) ∧
      (∃ d : ↥L ≃ₐ[k] ↥L,
        d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
        (Rep.Hom.hom μ) (φ (Additive.ofMul
          (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) := by
  classical
  -- `ℤ/p`-module structure on the `p`-torsion module `M`
  haveI : Module (ZMod p) M.V := AddCommGroup.zmodModule hM
  -- a value `m₀` which `μ` does not kill
  obtain ⟨m₀, hm₀⟩ := exists_apply_ne_zero_of_rep_hom_ne_zero μ hμ
  -- the action of `Gal(K/k)` on `M`, as `ℤ/p`-linear maps
  let ρ' : (K ≃ₐ[k] K) →* (M.V →ₗ[ZMod p] M.V) :=
    { toFun := fun u => AddMonoidHom.toZModLinearMap p ((M.ρ u : M.V →+ M.V))
      map_one' := by ext x; simp
      map_mul' := by intro u v; ext x; simp [map_mul] }
  have hρ'eval : ∀ (u : K ≃ₐ[k] K) (x : M.V), ρ' u x = M.ρ u x := fun u x => rfl
  -- the detecting functional: the weighted orbit sum of the coordinates of `e`
  let φ : Additive (SSGRoute.PTExt.galRes k K ↥L).ker →+ M.V :=
    { toFun := fun x => ∑ γ : K ≃ₐ[k] K,
        (Multiplicative.toAdd (e (Additive.toMul x))) γ • (ρ' γ m₀)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [toMul_add, map_mul, toAdd_mul, Pi.add_apply, add_smul, Finset.sum_add_distrib] }
  have hφeval : ∀ (a : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul a) = ∑ γ : K ≃ₐ[k] K, (Multiplicative.toAdd (e a)) γ • (ρ' γ m₀) := by
    intro a
    simp [φ]
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- `Gal(L/k)`-equivariance
    intro σ g
    have h1 : Multiplicative.toAdd (e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = fun τ : K ≃ₐ[k] K =>
            Multiplicative.toAdd (e g) ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ) := by
      rw [he σ g]
      exact toAdd_ofAdd _
    rw [hφeval, h1, hφeval,
      regSum_translate ρ' m₀ (Multiplicative.toAdd (e g)) (SSGRoute.PTExt.galRes k K ↥L σ),
      hρ'eval]
  · -- vanishing on the coordinates of the inertia subgroup
    intro γ hγ
    rw [hI γ hγ, hφeval]
    simp
  · -- detection at the coordinate of an element of the decomposition group
    obtain ⟨d, hdmem, v, hv1, hv0, hev⟩ := hd
    refine ⟨d, hdmem, ?_⟩
    have hcoe : Multiplicative.toAdd (e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)) = v := by
      rw [hev]
      exact toAdd_ofAdd v
    have h2 : φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)) = m₀ := by
      rw [hφeval, hcoe]
      exact regSum_single ρ' m₀ v hv1 hv0
    rw [h2]
    exact hm₀

end Work.SSGRoute.PTdualControl
