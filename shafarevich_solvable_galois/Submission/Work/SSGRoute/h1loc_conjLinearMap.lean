import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.isCoboundaryOn_conj
import Submission.Work.SSGRoute.isCocycleOn_conj
import Submission.Work.SSGRoute.isLocConstOn_conj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Conjugation on the local `H¹` of a subgroup of `G_k`

Let `N ≤ G_k = Ω ≃ₐ[k] Ω` be a subgroup and `σ ∈ G_k` with `σ⁻¹ N σ ⊆ N`.  Conjugation by `σ`
acts on the locally constant `1`-cocycles on `N` with values in a `Gal(K/k)`-module `M` by

  `f ↦ (n ↦ res k K σ • f (σ⁻¹ * n * σ))`,

and this action preserves cocycles, locally constant cochains and coboundaries
(`SSGRoute.isCocycleOn_conj`, `SSGRoute.isLocConstOn_conj`, `SSGRoute.isCoboundaryOn_conj`).
Hence it descends to a `𝔽_p`-linear endomorphism of `H¹_loc(N, M)`, which is what this file
constructs.  It is the algebraic backbone of the conjugation action on local cohomology used in
the Shafarevich/Scholz induction.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

set_option linter.unusedVariables false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

section Build

variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- The conjugation shift `f ↦ (n ↦ res k K σ • f (σ⁻¹ * n * σ))` on the cochains `G_k → M`,
as an `𝔽_p`-linear map.  Linearity in the coefficients uses `SMulCommClass (K ≃ₐ[k] K) (ZMod p) M`. -/
def h1locConjShift (σ : Ω ≃ₐ[k] Ω) :
    ((Ω ≃ₐ[k] Ω) → M) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → M) where
  toFun f n := SSGRoute.res k K σ • f (σ⁻¹ * n * σ)
  map_add' f g := by funext n; simp [smul_add]
  map_smul' c f := by
    funext n
    simp only [Pi.smul_apply]
    exact smul_comm (SSGRoute.res k K σ) c (f (σ⁻¹ * n * σ))

/-- The conjugation shift carries locally constant `1`-cocycles on `N` to locally constant
`1`-cocycles on `N`. -/
lemma h1locConjShift_mem_lcCocycles (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M N) :
    h1locConjShift p k Ω K M σ f ∈ lcCocycles p k Ω K M N := by
  obtain ⟨U, hUo, hU⟩ := isLocConstOn_conj hf.2 σ hnorm'
  refine ⟨isCocycleOn_conj (SSGRoute.res k K) hf.1 σ hnorm', U, hUo, ?_⟩
  intro g hg u hu huH
  show SSGRoute.res k K σ • f (σ⁻¹ * (g * u) * σ) = SSGRoute.res k K σ • f (σ⁻¹ * g * σ)
  exact congrArg (fun x => SSGRoute.res k K σ • x) (hU g hg u hu huH)

/-- The conjugation shift carries coboundaries on `N` to coboundaries on `N`. -/
lemma h1locConjShift_mem_coboundaries (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ coboundaries p k Ω K M N) :
    h1locConjShift p k Ω K M σ f ∈ coboundaries p k Ω K M N :=
  isCoboundaryOn_conj (SSGRoute.res k K) hf σ hnorm'

/-- The conjugation shift as a linear endomorphism of the module of locally constant cocycles
on `N`. -/
def h1locConjCocycles (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) :
    ↥(lcCocycles p k Ω K M N) →ₗ[ZMod p] ↥(lcCocycles p k Ω K M N) where
  toFun f := ⟨h1locConjShift p k Ω K M σ f.1,
    h1locConjShift_mem_lcCocycles p k Ω K M N σ hnorm' f.2⟩
  map_add' f g := Subtype.ext ((h1locConjShift p k Ω K M σ).map_add f.1 g.1)
  map_smul' c f := Subtype.ext ((h1locConjShift p k Ω K M σ).map_smul c f.1)

/-- The conjugation shift preserves the submodule of coboundaries, so it induces a map on `H¹_loc`. -/
lemma h1locConjCocycles_mem_cobQ (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N) :
    cobQ p k Ω K M N ≤ (cobQ p k Ω K M N).comap (h1locConjCocycles p k Ω K M N σ hnorm') := by
  intro x hx
  rw [Submodule.mem_comap] at hx ⊢
  exact h1locConjShift_mem_coboundaries p k Ω K M N σ hnorm' hx

end Build

theorem h1loc_conjLinearMap
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hnorm : ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) (hnorm' : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    ∃ conj : Work.SSGRoute.H1loc p k Ω K M N →ₗ[ZMod p] Work.SSGRoute.H1loc p k Ω K M N,
      ∀ (f : (Ω ≃ₐ[k] Ω) → M) (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M N),
        conj (Work.SSGRoute.toClass p k Ω K M N f) =
          Work.SSGRoute.toClass p k Ω K M N (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) := by
  refine ⟨Submodule.mapQ (cobQ p k Ω K M N) (cobQ p k Ω K M N)
      (h1locConjCocycles p k Ω K M N σ hnorm')
      (h1locConjCocycles_mem_cobQ p k Ω K M N σ hnorm'), ?_⟩
  intro f hf
  have hflc : h1locConjShift p k Ω K M σ f ∈ lcCocycles p k Ω K M N :=
    h1locConjShift_mem_lcCocycles p k Ω K M N σ hnorm' hf
  have h1 : toClass p k Ω K M N f = Submodule.mkQ (cobQ p k Ω K M N) ⟨f, hf⟩ := by
    rw [toClass, dif_pos hf]
  have hflc' : (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) ∈ lcCocycles p k Ω K M N :=
    hflc
  have h2 : toClass p k Ω K M N (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ))
      = Submodule.mkQ (cobQ p k Ω K M N)
          ⟨fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ), hflc'⟩ := by
    rw [toClass, dif_pos hflc']
  rw [h1, h2, Submodule.mkQ_apply, Submodule.mapQ_apply]
  exact congrArg (Submodule.mkQ (cobQ p k Ω K M N)) (Subtype.ext rfl)

end

end Work.SSGRoute
