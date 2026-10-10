import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.HSRow.coker_injects_H2loc
import Submission.Work.SSGRoute.HSRow.transgression_injective
import Submission.Work.SSGRoute.h1loc_decomp_finite
import Submission.Work.SSGRoute.inertiaStructureOfFinPlace_zhat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Euler characteristic at a finite place of non-`p` residue characteristic, clean

`Work.SSGRoute.PT.euler_notResidueChar_proof` (Milne, *Arithmetic Duality Theorems* I.2.9:
`dim H¹(D_A,M) = dim H⁰(D_A,M) + dim H²(D_A,M)` when `p` is a unit of `A`) imports the module
`Submission.Work.SSGRoute.hs_twoRow_decomp`, whose *source is not in the tree* (only a stale
`olean` survives), and that module in turn consumes the two degree-`2` rows of the two-row
decomposition as filed in `Submission/Work/SSGRoute/HSTwoRow/`.  Both of those are stalled
`sorry`s, so the whole node currently carries `sorryAx` (measured with `#print axioms`).

The three degree-wise rows are, however, *available and axiom-clean* elsewhere in the tree:

* `Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp` (`dim H¹(D,M) = dim ker (conj₀ - 1) + dim ker
  (conj₁ - 1)`) — clean;
* `Work.SSGRoute.finrank_H0loc_decomp` (`dim H⁰(D,M) = dim ker (conj₀ - 1)`) — clean;
* the degree-`2` row, assembled here as `finrank_H2loc_decomp_clean` from the *proved* halves
  `Work.SSGRoute.HSRow.transgression_injective` and `Work.SSGRoute.HSRow.coker_injects_H2loc`
  (both measured `[propext, Classical.choice, Quot.sound]`),

together with Herbrand's lemma (rank–nullity at `T - 1`).  This file re-assembles them, so that the
`ε = 0` half of the local Euler characteristic is available without the lost module.
-/

namespace Work.SSGRoute.EulerSymm

set_option linter.style.haveILetI false

private theorem finrank_ker_sub_one_eq_finrank_coker_clean
    (p : ℕ) [Fact p.Prime] (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (T : V →ₗ[ZMod p] V) :
    Module.finrank (ZMod p) ↥(LinearMap.ker (T - 1)) =
      Module.finrank (ZMod p) (V ⧸ LinearMap.range (T - 1)) := by
  have h1 : Module.finrank (ZMod p) ↥(LinearMap.range (T - 1))
      + Module.finrank (ZMod p) ↥(LinearMap.ker (T - 1)) = Module.finrank (ZMod p) V :=
    LinearMap.finrank_range_add_finrank_ker (T - 1)
  have h2 : Module.finrank (ZMod p) (V ⧸ LinearMap.range (T - 1))
      + Module.finrank (ZMod p) ↥(LinearMap.range (T - 1)) = Module.finrank (ZMod p) V :=
    Submodule.finrank_quotient_add_finrank (LinearMap.range (T - 1))
  omega

/-- **The degree-`2` row** `dim H²(D,M) = dim (H¹(I,M) ⧸ range (conj₁ - 1))` of the
Hochschild–Serre two-row decomposition, assembled from the *proved* transgression and inverse
transgression `Work.SSGRoute.HSRow.transgression_injective` / `...coker_injects_H2loc`. -/
theorem finrank_H2loc_decomp_clean
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (hvan : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subsingleton (Work.SSGRoute.H2loc p k Ω K M I))
    (hfin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I))
    (hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) := by
  classical
  obtain ⟨Φ, hΦ⟩ :=
    Work.SSGRoute.HSRow.transgression_injective p k Ω K A I σ hI hIclosed hnorm hσ hsup hinf hZ
      hvan M hnorm1 hnorm2
  obtain ⟨δ, hδ⟩ :=
    Work.SSGRoute.HSRow.coker_injects_H2loc p k Ω K A I σ hI hIclosed hnorm hσ hsup hinf hZ
      hvan hfin M hnorm1 hnorm2
  haveI hFinI : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I) := hfin M
  haveI hFinQ : Module.Finite (ZMod p)
      (Work.SSGRoute.H1loc p k Ω K M I ⧸
        LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  haveI hFinH2 : Module.Finite (ZMod p)
      (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) :=
    Module.Finite.of_injective Φ hΦ
  have hle1 : Module.finrank (ZMod p)
      (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) ≤
      Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  have hle2 : Module.finrank (ZMod p)
        (Work.SSGRoute.H1loc p k Ω K M I ⧸
          LinearMap.range (conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) ≤
      Module.finrank (ZMod p)
        (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) :=
    LinearMap.finrank_le_finrank_of_injective hδ
  omega

/-- **The local Euler characteristic at a finite place of residue characteristic `≠ p`** (Milne
I.2.9), reconstructed from the three degree-wise rows of the two-row Hochschild–Serre decomposition
so that no `sorryAx`-carrying module is needed. -/
theorem eulerChar_decomp_notResidueChar
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ∧
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) +
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) := by
  obtain ⟨I, σ, hI, hIclosed, hnorm, hσ, hsup, hinf, hZ, hvanfin⟩ :=
    Work.SSGRoute.inertiaStructureOfFinPlace_zhat p k Ω K A hA h
  intro M _ _ _ _ _
  obtain ⟨hvan, hfinI⟩ := hvanfin M
  have hnorm1 : ∀ n ∈ I, σ * n * σ⁻¹ ∈ I := fun n hn => hnorm σ hσ n hn
  have hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I :=
    fun n hn => hnorm σ⁻¹ ((SSGRoute.decomp k A).inv_mem hσ) n hn
  refine ⟨Work.SSGRoute.h1loc_decomp_finite p k Ω K A hA M, ?_⟩
  have h1eq : Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) ↥(LinearMap.ker
          (Work.SSGRoute.conj0 p k Ω K M I σ hnorm2 - LinearMap.id)) +
        Module.finrank (ZMod p) ↥(LinearMap.ker
          (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :=
    Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp p k Ω K A I σ hI hIclosed hnorm hσ hsup hinf hZ
      (fun N _ _ _ _ _ => (hvanfin N).1) (fun N _ _ _ _ _ => (hvanfin N).2) hnorm1 hnorm2 M
  have h2eq : Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I ⧸
        LinearMap.range (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) :=
    finrank_H2loc_decomp_clean p k Ω K A I σ hI hIclosed hnorm hσ hsup hinf hZ
      (fun N _ _ _ _ _ => (hvanfin N).1) (fun N _ _ _ _ _ => (hvanfin N).2) hnorm1 hnorm2 M
  have h0eq : Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) ↥(LinearMap.ker
          (Work.SSGRoute.conj0 p k Ω K M I σ hnorm2 - LinearMap.id)) :=
    Work.SSGRoute.finrank_H0loc_decomp p k Ω K M I σ A hI hσ hsup hnorm2
  have hrn : Module.finrank (ZMod p) ↥(LinearMap.ker
        (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) =
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I ⧸
        LinearMap.range (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2 - LinearMap.id)) := by
    haveI : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I) := hfinI
    exact finrank_ker_sub_one_eq_finrank_coker_clean p (Work.SSGRoute.H1loc p k Ω K M I)
      (Work.SSGRoute.conj1 p k Ω K M I σ hnorm1 hnorm2)
  rw [h1eq, h0eq, h2eq, hrn]

end Work.SSGRoute.EulerSymm
