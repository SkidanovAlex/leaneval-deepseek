import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E3In.normCriterion_general
import Submission.Work.SSGRoute.E3In.phi1_trivial_mono_in_of_inputs
import Submission.Work.SSGRoute.PTW.mem_pthPower_in
import Submission.Work.SSGRoute.extH_groupCohomology_bridge_nonempty
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# E3Ω `phi1_trivial_mono_in` (levels inside a fixed algebraic closure)

Base case of the `φ¹`-injectivity dévissage: for the trivial module `M = 𝔽_p` over `Gal(K/k)`,
with `μ_p ⊆ k`, a class `x ∈ Ext¹_{Gal(K/k)}(𝔽_p, C_K)` that pairs to zero with every character
`H¹(Gal(L/k), 𝔽_p)` at every finite Galois level `K ≤ L ≤ Ω` is zero.

The `Ext`-algebra spine (`E3Ext`) and the cyclic norm criterion (`CFTSide`) are proved elsewhere;
this file assembles them.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Decomposition of a class of `Ext¹_{G_K}(𝔽_p, C_K)`.**  Since `H¹(G_K, C_K) = 0`
(`E3Ext.subsingleton_extH_classesK`), every such class is the pushout of the `H⁰`-slot of a
`Gal(K/k)`-fixed element `a ∈ C_K`, i.e. of `powHomCls k K a ha`. -/
theorem exists_pushClass_powHomCls (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (x : Abelian.Ext (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) (classesK k K) 1) :
    ∃ (a : classesK k K) (ha : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ a = a),
      x = E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K) (SSGRoute.Phi1.powHomCls k K a ha) := by
  obtain ⟨φ, hφ⟩ := E3Ext.exists_pushClass (G := K ≃ₐ[k] K) p (classesK k K)
    (E3Ext.subsingleton_extH_classesK k K) x
  have hafix : ∀ σ : K ≃ₐ[k] K, (classesK k K).ρ σ (φ.hom 1) = φ.hom 1 := by
    intro σ
    have h := Rep.hom_comm_apply (A := SSGRoute.PTExt.unitRep (K ≃ₐ[k] K))
      (B := classesK k K) φ σ (1 : Coeff)
    simp only [SSGRoute.PTExt.unitRep, Rep.trivial_ρ_apply] at h
    exact h.symm
  have hφeq : φ = SSGRoute.Phi1.powHomCls k K (φ.hom 1) hafix := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    show (Rep.Hom.hom φ) n = (Rep.Hom.hom (SSGRoute.Phi1.powHomCls k K (φ.hom 1) hafix)) n
    rw [SSGRoute.Phi1.powHomCls_apply]
    have hn : n • (1 : Coeff) = n := by simp
    have key2 : (Rep.Hom.hom φ) n = (Rep.Hom.hom φ) (n • (1 : Coeff)) := by rw [hn]
    exact key2.trans ((Rep.Hom.hom φ).map_smul n (1 : Coeff))
  exact ⟨φ.hom 1, hafix, by
    rw [hφ]
    exact congrArg (fun ψ => E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K) ψ) hφeq⟩

/-- **`classIncl k k K a` is fixed by `Gal(K/k)`**: it lies in the image of the invariants
`C_k = C_K^{Gal(K/k)}` (here `Gal(k/k) = 1`). -/
theorem classIncl_k_k_fixed (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (a : SSGRoute.PTExt.classesK k k) :
    ∀ σ : K ≃ₐ[k] K,
      (SSGRoute.PTExt.classesK k K).ρ σ ((SSGRoute.PTExt.classIncl k k K).hom a)
        = (SSGRoute.PTExt.classIncl k k K).hom a := by
  intro σ
  have h := Rep.hom_comm_apply (SSGRoute.PTExt.classIncl k k K) σ a
  have h1' : ((Rep.res (SSGRoute.PTExt.galRes k k K)
      (SSGRoute.PTExt.classesK k k)).ρ σ) a = a := by
    change (SSGRoute.PTExt.classesK k k).ρ ((SSGRoute.PTExt.galRes k k K) σ) a = a
    rw [Subsingleton.elim (SSGRoute.PTExt.galRes k k K σ) 1]
    simp
  rw [h1'] at h
  exact h.symm

/-- **If `a₀ = b₀ ^ p` in `C_k`, then the pushed-forward class of the `H⁰`-slot of `a₀` vanishes**:
`a₀` is a `p`-th power, so the extension `0 → C_K → E → 𝔽_p → 0` splits. -/
theorem pushClass_classIncl_pow_eq_zero (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (a₀ b₀ : NK.GlobalCFT.IdeleClassGroup k) (hb : b₀ ^ p = a₀) :
    E3Ext.pushClass p (K ≃ₐ[k] K) (classesK k K)
      (SSGRoute.Phi1.powHomCls k K
        ((SSGRoute.PTExt.classIncl k k K).hom (Additive.ofMul a₀))
        (classIncl_k_k_fixed k K (Additive.ofMul a₀))) = 0 := by
  refine E3Ext.pushClass_powHomCls_eq_zero_of_eq_smul p k K
    ((SSGRoute.PTExt.classIncl k k K).hom (Additive.ofMul a₀))
    ((SSGRoute.PTExt.classIncl k k K).hom (Additive.ofMul b₀))
    (classIncl_k_k_fixed k K (Additive.ofMul a₀))
    (classIncl_k_k_fixed k K (Additive.ofMul b₀)) ?_
  rw [← hb]
  refine (congrArg (Rep.Hom.hom (SSGRoute.PTExt.classIncl k k K))
    (ofMul_pow p b₀)).trans ?_
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- **E3Ω.** Base case: `φ¹` is injective for `M = 𝔽_p` (trivial action), `μ_p ⊆ k`, testing only
on the finite Galois levels `K ≤ L ≤ Ω` of a fixed algebraic closure. -/
theorem phi1_trivial_mono_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (x : Abelian.Ext (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) (classesK k K) 1)
    (hx : PhiOneVanishesIn Ω x) : x = 0 := by
  exact E3In.phi1_trivial_mono_in_of_inputs p k K Ω ζ hζ
    (Classical.choice extH_groupCohomology_bridge_nonempty)
    (fun x hx' => PTW.mem_pthPower_in k p x hx')
    (fun L _ _ _ F _ _ _ hfin a hafix g hne hker hvan =>
      E3In.normCriterion_general k L p F hfin a hafix g hne hker hvan)
    x hx

end Work.SSGRoute
