import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.dual_injective_of_finite_index
import Submission.NK.Reconstruct.finite_of_fg_torsion
import Submission.NK.Reconstruct.proj_surjective
import Submission.NK.Reconstruct.ellRestrict_surjective

/-!
# The continuous dual `Hom_cts(Γ_K, ℤ_ℓ)` and Shimizu's Lemma 4f.1

Shimizu (arXiv:2009.10431, §4) studies the continuous dual

  `Hom_cts(Γ_K, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(Γ_K, ℤ_ℓ) ≅ ℤ_ℓ^{r_ℓ(K)}`

of the ℓ-adic abelianisation `Γ_K` of the absolute Galois group of a number field `K`, and its
behaviour under the transition maps of the tower of finite Galois levels.  This file records the
part of that theory which is *provable* in the present development:

* `NK.Reconstruct.Dual G ℓ` — the continuous dual of a compact abelian topological group `G`,
  as the type of continuous additive homomorphisms `G → ℤ_ℓ` (`G` written multiplicatively);
* `NK.Reconstruct.dualMap φ hφ` — the contravariant functoriality of the dual;
* `NK.Reconstruct.dualMap_comp` — the dual is a contravariant functor;
* `NK.Reconstruct.dualMap_injective_of_surjective` — **the injectivity half of Lemma 4f.1, in
  general form**: the dual of a *surjective* continuous homomorphism is injective.

Since the projections `Γ_K → Γ_{L,ℓ}` (`NK.Reconstruct.Gamma.proj`) and the transition maps
`Γ_{M,ℓ} → Γ_{L,ℓ}` (`NK.Reconstruct.ellRestrict`) are surjective
(`NK.Reconstruct.proj_surjective`, `NK.Reconstruct.ellRestrict_surjective`), the injectivity
half of Lemma 4f.1 follows for the whole projective system
(`NK.Reconstruct.dual_ellRestrict_injective`).

The *arithmetic* half of Lemma 4f.1 — that the cokernel of the restriction
`Hom_cts(Γ_K, ℤ_ℓ) → Hom_cts(Γ_L, ℤ_ℓ)^{G(L/K)}` is finite, whence
`rank_{ℤ_ℓ} Hom_cts(Γ_L, ℤ_ℓ)^{G(L/K)} = r_ℓ(K)` — is Shimizu's Hochschild–Serre computation: the
inflation–restriction sequence for the trivial module `ℤ/ℓⁿ`

  `0 → H¹(G(L/K), ℤ/ℓⁿ) → H¹(G_K, ℤ/ℓⁿ) → H¹(G_L, ℤ/ℓⁿ)^{G(L/K)} → H²(G(L/K), ℤ/ℓⁿ)`

passes to the limit to an exact sequence whose outer terms are trivial (`Hom(G(L/K), ℤ_ℓ) = 0`)
respectively finite (`H²(G(L/K), ℤ_ℓ)` is finite).  Its two *abstract* engines are proved in this
directory — `NK.Reconstruct.dual_injective_of_finite_index` (a `ℤ_ℓ`-linear form vanishing on a
finite-index submodule is zero) and `NK.Reconstruct.finite_of_fg_torsion` (a finitely generated
`ℤ_ℓ`-module killed by a power of `ℓ` is finite) — and the single arithmetic statement left is the
class-field-theory input `NK.Reconstruct.RankFormulaInput` (CoNF (10.3.20)), which supplies the
rank `r_ℓ(K)` and, with it, the finiteness of `Hom_cts(Γ_K, ℤ_ℓ)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace NK.Reconstruct

open scoped Pointwise

/-- The set of continuous additive homomorphisms `Γ → ℤ_ℓ`, as an additive subgroup of all the
additive homomorphisms. -/
def dualCarrier (G : Type*) [CommGroup G] [TopologicalSpace G] (ℓ : ℕ) [Fact ℓ.Prime] :
    AddSubgroup (Additive G →+ PadicInt ℓ) where
  carrier := {f | Continuous f}
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  zero_mem' := continuous_zero
  neg_mem' := by
    intro f hf
    exact hf.neg

/-- **The continuous dual `Hom_cts(Γ, ℤ_ℓ)`** of a compact abelian topological group `Γ`, as the
type of continuous additive homomorphisms `Γ → ℤ_ℓ` (the group `Γ` being written multiplicatively,
the homomorphisms are equivalently the elements of `Hom_{ℤ_ℓ}(Γ, ℤ_ℓ)` for `Γ` a profinite
`ℤ_ℓ`-module). -/
abbrev Dual (G : Type*) [CommGroup G] [TopologicalSpace G] (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  ↥(dualCarrier G ℓ)

instance instCoeFunDual (G : Type*) [CommGroup G] [TopologicalSpace G] (ℓ : ℕ) [Fact ℓ.Prime] :
    CoeFun (Dual G ℓ) (fun _ => Additive G → PadicInt ℓ) :=
  ⟨fun f => ⇑(f : Additive G →+ PadicInt ℓ)⟩

/-- **Contravariant functoriality of the continuous dual.**  A continuous homomorphism
`φ : G →* H` induces `Dual H → Dual G` by precomposition. -/
def dualMap {G H : Type*} [CommGroup G] [TopologicalSpace G] [CommGroup H] [TopologicalSpace H]
    (ℓ : ℕ) [Fact ℓ.Prime] (φ : G →* H) (hφ : Continuous ⇑φ) : Dual H ℓ → Dual G ℓ :=
  fun f => ⟨f.1.comp (MonoidHom.toAdditive φ), by
    show Continuous ((f.1 : Additive H →+ PadicInt ℓ) ∘ ⇑(MonoidHom.toAdditive φ))
    exact f.2.comp (by continuity)⟩

@[simp] theorem dualMap_apply {G H : Type*} [CommGroup G] [TopologicalSpace G] [CommGroup H]
    [TopologicalSpace H] (ℓ : ℕ) [Fact ℓ.Prime] (φ : G →* H) (hφ : Continuous ⇑φ)
    (f : Dual H ℓ) (x : Additive G) :
    dualMap ℓ φ hφ f x = f (MonoidHom.toAdditive φ x) := rfl

/-- The dual map is additive. -/
theorem dualMap_add {G H : Type*} [CommGroup G] [TopologicalSpace G] [CommGroup H]
    [TopologicalSpace H] (ℓ : ℕ) [Fact ℓ.Prime] (φ : G →* H) (hφ : Continuous ⇑φ)
    (f g : Dual H ℓ) : dualMap ℓ φ hφ (f + g) = dualMap ℓ φ hφ f + dualMap ℓ φ hφ g := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  rfl

/-- **The dual is a contravariant functor.** -/
theorem dualMap_comp {G H I : Type*} [CommGroup G] [TopologicalSpace G] [CommGroup H]
    [TopologicalSpace H] [CommGroup I] [TopologicalSpace I] (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : G →* H) (ψ : H →* I) (hφ : Continuous ⇑φ) (hψ : Continuous ⇑ψ) :
    dualMap ℓ (ψ.comp φ) (hψ.comp hφ) = (dualMap ℓ φ hφ).comp (dualMap ℓ ψ hψ) := by
  funext f
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  rfl

/-- **Injectivity half of Shimizu's Lemma 4f.1, in general form.**  The dual of a *surjective*
continuous homomorphism is injective: an additive homomorphism out of the target is determined by
its restriction along a surjection. -/
theorem dualMap_injective_of_surjective {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [CommGroup H] [TopologicalSpace H] (ℓ : ℕ) [Fact ℓ.Prime] (φ : G →* H)
    (hφ : Continuous ⇑φ) (hsurj : Function.Surjective φ) :
    Function.Injective (dualMap ℓ φ hφ) := by
  intro f g hfg
  have h : ∀ y : Additive H, f y = g y := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (Additive.toMul y)
    have hy : MonoidHom.toAdditive φ (Additive.ofMul x) = y := by
      rw [show MonoidHom.toAdditive φ (Additive.ofMul x) = Additive.ofMul (φ x) from rfl, hx,
        ofMul_toMul]
    have := congrFun (congrArg (fun u : Dual G ℓ => (u : Additive G → PadicInt ℓ)) hfg)
      (Additive.ofMul x)
    rw [dualMap_apply, dualMap_apply, hy] at this
    exact this
  apply Subtype.ext
  exact AddMonoidHom.ext h

/-- **The injectivity half of Lemma 4f.1 for the tower of levels.**  For `L ⊆ M` the transition map
`Γ_{M,ℓ} → Γ_{L,ℓ}` is surjective (`NK.Reconstruct.ellRestrict_surjective`), hence its dual is
injective. -/
theorem dual_ellRestrict_injective {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] {L M : FrobLevel K K'} (h : L.L ≤ M.L) :
    Function.Injective (dualMap ℓ (ellRestrict ℓ L M h) continuous_of_discreteTopology) :=
  dualMap_injective_of_surjective ℓ _ _ (ellRestrict_surjective ℓ h)

/-- **The injectivity half of Lemma 4f.1 for the projections of the limit.**  The projection
`Γ_K → Γ_{L,ℓ}` is surjective (`NK.Reconstruct.proj_surjective`) and continuous
(`NK.Reconstruct.continuous_proj`), hence its dual is injective. -/
theorem dual_proj_injective {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') :
    Function.Injective (dualMap ℓ (Gamma.proj L) (continuous_proj ℓ L)) :=
  dualMap_injective_of_surjective ℓ (Gamma.proj L) (continuous_proj ℓ L) (proj_surjective ℓ L)

/-- **The injectivity half of Lemma 4f.1 in the abstract `ℤ_ℓ`-module form**, Shimizu's
(1.6.7) argument: a `ℤ_ℓ`-linear form on the target which vanishes on a finite-index submodule
vanishes identically.  This is `NK.Reconstruct.dual_injective_of_finite_index`, restated. -/
theorem dual_injective_of_finite_index' {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [Module (PadicInt ℓ) A] [AddCommGroup B] [Module (PadicInt ℓ) B]
    (f : B →ₗ[PadicInt ℓ] A) (hfin : Finite (A ⧸ LinearMap.range f))
    (φ : A →ₗ[PadicInt ℓ] PadicInt ℓ) (hφ : φ.comp f = 0) : φ = 0 :=
  dual_injective_of_finite_index f hfin φ hφ

end NK.Reconstruct
