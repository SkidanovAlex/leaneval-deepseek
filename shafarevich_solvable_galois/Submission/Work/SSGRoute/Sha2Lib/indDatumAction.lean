import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.E7cC.inducedLevelDatum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Gal(K/k)`-action on `Ind_{D_w}^{G₀} 𝔽_p`, and its `𝔽_p`-valued augmentation

`Work.SSGRoute.E7cC.indDatum p k K w` is `Ind_{D_w}^{G₀} 𝔽_p` realised as the `𝔽_p`-valued functions
on `G₀ = Gal(K/k)` that are invariant under *right* multiplication by `D_w = decompK w`
(`f (γ * δ) = f γ`), with the left-translation action.

Mathlib has no `Module`/`DistribMulAction` packaging for this carrier (it is only an `AddSubgroup`
of a function type, and the left-translation action is not the pointwise one), so the action is
recorded here as an explicit function `indDatumSmul`, together with the two facts the level
statements need:

* `indDatumSmul_mem` — the action preserves the carrier (this is the by-hand membership proof);
* `indDatumSmul_add` — the action is additive, i.e. `↥(indDatum p k K w)` is a `Gal(K/k)`-module
  with this action.

The plan of the level input of `Work.SSGRoute.Sha2Lib.exists_level_detecting_functional` is:

* a level `L ⊇ K`, finite Galois over `k`, a place `q' | w` with `p ∤ e(q'|q)`, and a
  `Gal(K/k)`-equivariant isomorphism `e : ker (galRes k K L) ≃* Ind_{D_w}^{G₀} 𝔽_p`;
* a **nonzero `Gal(K/k)`-equivariant additive functional** `a` on `Ind_{D_w}^{G₀} 𝔽_p` — there is
  exactly a one-dimensional space of these, spanned by the *augmentation* (`Σ_τ f τ` over the
  coset representatives), since `Ind_{D_w}^{G₀} 𝔽_p` is generated as a `Gal(K/k)`-module by the
  indicator of `D_w` (`indDatumBase`) and the target carries the trivial action;
* `a (e (coordKer d)) ≠ 0` for some `d ∈ D_{q'}` and `a (e (coordKer γ)) = 0` for all inertia
  elements `γ`.  Because the target of `a` is trivial, `span (a ∘ e ∘ coordKer) (D_{q'})` is a
  subgroup of `𝔽_p` and `a ∘ e ∘ coordKer` is a *homomorphism* `D_{q'} → 𝔽_p` vanishing on the
  inertia, so this clause is exactly `p ∣ f(q'|q)` together with non-vanishing on the Frobenius.
-/

namespace Work.SSGRoute.Sha2Lib

open Work.SSGRoute.E7cC

/-- **The left-translation `Gal(K/k)`-action on `Ind_{D_w}^{G₀} 𝔽_p`.**  For `σ ∈ Gal(K/k)` and a
right-`D_w`-invariant function `f`, `σ • f` is the function `τ ↦ f (σ⁻¹ τ)`; it is again
right-`D_w`-invariant. -/
noncomputable def indDatumSmul (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (σ : K ≃ₐ[k] K) (f : ↥(indDatum p k K w)) :
    ↥(indDatum p k K w) :=
  ⟨fun τ : K ≃ₐ[k] K => (f : (K ≃ₐ[k] K) → ZMod p) (σ⁻¹ * τ),
    by
      intro δ hδ γ
      show (f : (K ≃ₐ[k] K) → ZMod p) (σ⁻¹ * (γ * δ)) = (f : (K ≃ₐ[k] K) → ZMod p) (σ⁻¹ * γ)
      rw [← mul_assoc]
      exact f.2 δ hδ (σ⁻¹ * γ)⟩

@[simp] theorem indDatumSmul_coe (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (σ : K ≃ₐ[k] K) (f : ↥(indDatum p k K w)) :
    ((indDatumSmul p k K w σ f : ↥(indDatum p k K w)) : (K ≃ₐ[k] K) → ZMod p)
      = fun τ => (f : (K ≃ₐ[k] K) → ZMod p) (σ⁻¹ * τ) := rfl

theorem indDatumSmul_add (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (σ : K ≃ₐ[k] K) (f g : ↥(indDatum p k K w)) :
    indDatumSmul p k K w σ (f + g) = indDatumSmul p k K w σ f + indDatumSmul p k K w σ g := by
  ext τ
  rfl

/-- The `Gal(K/k)`-action on `Ind_{D_w}^{G₀} 𝔽_p` is **trivial on the `D_w`-fixed basis vector**
`indDatumBase` (the indicator of `D_w`): for `δ ∈ D_w` the coset `δ⁻¹ τ` meets `D_w` iff `τ`
does. -/
theorem indDatumSmul_base (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (δ : K ≃ₐ[k] K)
    (hδ : δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w) :
    indDatumSmul p k K w δ (indDatumBase p k K w) = indDatumBase p k K w := by
  classical
  ext τ
  show (if δ⁻¹ * τ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w then (1 : ZMod p) else 0)
    = if τ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w then 1 else 0
  have h : δ⁻¹ * τ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w ↔
      τ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w := by
    constructor
    · intro hmem
      have h1 := (SSGRoute.PTExt.decompK (k := k) (K := K) w).mul_mem hδ hmem
      simpa using h1
    · intro hmem
      exact (SSGRoute.PTExt.decompK (k := k) (K := K) w).mul_mem
        ((SSGRoute.PTExt.decompK (k := k) (K := K) w).inv_mem hδ) hmem
  rw [if_congr h rfl rfl]

end Work.SSGRoute.Sha2Lib
