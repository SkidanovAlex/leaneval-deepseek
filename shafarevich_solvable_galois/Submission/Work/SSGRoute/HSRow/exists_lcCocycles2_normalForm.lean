import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.HSRow.Fzext_mem_lcCocycles2
import Submission.Work.SSGRoute.HSRow.exists_crossedHom_Phi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

open Classical

theorem exists_lcCocycles2_normalForm
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
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : b ∈ Work.SSGRoute.lcCocycles p k Ω K M I) :
    ∃ F : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M,
      F ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A) ∧
      (∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, F g n = 0) ∧
      Work.SSGRoute.toClass p k Ω K M I (fun n => F n σ)
        = Work.SSGRoute.toClass p k Ω K M I b := by
  classical
  let H : Hcx k Ω I σ :=
    { A := A, hI := hI, hnorm := hnorm, hσ := hσ, hsup := hsup, hinf := hinf }
  let y : ↥(Zr p k Ω K M I) := resZr p k Ω K M I ⟨b, hb⟩
  have hfin' : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I) := hfin M
  obtain ⟨Φ, hΦ1, hΦc, hΦlc, hΦσ⟩ :=
    exists_crossedHom_Phi p k Ω K M I σ H hZ hfin' y
  refine ⟨Fzext p k Ω K M I σ H Φ, ?_, ?_, ?_⟩
  · -- the normal form is a locally constant 2-cocycle
    exact Fzext_mem_lcCocycles2 p k Ω K M I σ hIclosed H Φ hΦ1 hΦc hΦlc
  · -- it vanishes on `D × I`
    intro g hg n hn
    exact Fzext_normal p k Ω K M I σ H Φ hΦ1 g hg hn
  · -- its slice at `σ` represents the class of `b`
    have hF : Fzext p k Ω K M I σ H Φ
        ∈ Work.SSGRoute.lcCocycles2 p k Ω K M (SSGRoute.decomp k A) :=
      Fzext_mem_lcCocycles2 p k Ω K M I σ hIclosed H Φ hΦ1 hΦc hΦlc
    have hFn : ∀ g ∈ SSGRoute.decomp k A, ∀ n ∈ I, Fzext p k Ω K M I σ H Φ g n = 0 :=
      fun g hg n hn => Fzext_normal p k Ω K M I σ H Φ hΦ1 g hg hn
    have hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I :=
      fun n hn => hnorm σ⁻¹ ((SSGRoute.decomp k A).inv_mem hσ) n hn
    have hslice : (fun n => Fzext p k Ω K M I σ H Φ n σ)
        ∈ Work.SSGRoute.lcCocycles p k Ω K M I :=
      slice_mem_lcCocycles p k Ω K A I σ hI hσ hnorm2 M (Fzext p k Ω K M I σ H Φ) hF hFn
    refine toClass_eq_of_eqOn_I p k Ω K M I hslice hb ?_
    intro n hn
    rw [Fzext_slice p k Ω K M I σ H Φ hn, hΦσ]
    rfl

end Work.SSGRoute.HSRow
