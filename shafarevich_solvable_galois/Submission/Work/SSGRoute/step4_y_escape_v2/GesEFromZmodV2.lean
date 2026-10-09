import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.overK
import Submission.Work.SSGRoute.step4_y_escape_v2.GesZmodEscapeV2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The `E`-valued Grünwald-with-escape from the `ZMod p`-valued case (HEDGE, not used yet)

This module lifts the `ZMod p`-valued escape statement `Work.SSGRoute.ges_zmod_escape_v2` (the
`L₁ = K` case of Grünwald with escape, the arithmetic core of the Fourth Step) to coefficients in an
arbitrary finite `𝔽_p`-module `E`, coordinatewise along an `𝔽_p`-basis, exactly as
`Work.SSGRoute.step4_grunwald_E_over_K` lifts the local-realisation half.

It exists so that the node `Work.SSGRoute.step4_y_localData_escape` (which consumes the `E`-valued
form at `E = E p (K ≃ₐ[ℚ] K) n i j`) can be re-pointed to whichever of

* `Work.SSGRoute.grunwald_escape_support_E` (proved modulo `grunwald_escape_relative`), and
* `Work.SSGRoute.ges_zmod_escape_v2` (the `L₁ = K`, `ZMod p` case, being proved independently)

becomes `sorryAx`-free first. -/

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **The `E`-valued Grünwald-with-escape at `L₁ = K`, from the `ZMod p`-valued case.** -/
theorem gesE_of_zmod_escape_v2 (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1)
    (L : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (T : Finset (ValuationSubring SSGRoute.QBar))
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace ↥K A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B)
    (hTcov : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
      (B.valuation (p : SSGRoute.QBar) < 1 ∨ SSGRoute.IsRamifiedIn ↥K (overK K L hKL) B) →
      ∃ A ∈ T, SSGRoute.IsConjPlace ↥K A B)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (f : ValuationSubring SSGRoute.QBar → (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E)
    (hf : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp ↥K A, ∀ y ∈ SSGRoute.decomp ↥K A,
      f A (x * y) = f A x + f A y)
    (hfc : ∀ A ∈ T, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
      IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp ↥K A → f A x = 0)
    (hsupp : ∀ A ∈ T, (∀ δ ∈ SSGRoute.decomp ↥K A, f A δ = 0) ∨
      ∀ χ : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, χ (x * y) = χ x + χ y) →
        (∀ δ ∈ (overK K L hKL).fixingSubgroup, χ δ = 0) →
        ∀ δ ∈ SSGRoute.decomp ↥K A, χ δ = 0) :
    ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E,
      (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
      SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
      (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = f A δ) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
        ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
  classical
  have hfin : Module.Finite (ZMod p) E := Module.Finite.of_finite
  let eL : E ≃ₗ[ZMod p] (Fin (Module.finrank (ZMod p) E) → ZMod p) :=
    (Module.finBasis (ZMod p) E).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin (Module.finrank (ZMod p) E)))
  have hcoord : ∀ k : Fin (Module.finrank (ZMod p) E),
      ∃ ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → ZMod p,
        (∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y) ∧
        SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε ∧
        (∀ A ∈ T, ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = (eL (f A δ)) k) ∧
        (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
          (∀ A ∈ T, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ L B →
          ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0) := by
    intro k
    exact ges_zmod_escape_v2 p K ζ hζ hζK hKimag L hKL T hTfin hTdisj hTcov
      (fun A x => (eL (f A x)) k)
      (fun A hA x hx y hy => by simp only [hf A hA x hx y hy, map_add, Pi.add_apply])
      (fun A hA => by
        obtain ⟨U, hUo, hU⟩ := hfc A hA
        exact ⟨U, hUo, fun x hx hxdec => by simp [hU x hx hxdec]⟩)
      (fun A hA => by
        rcases hsupp A hA with h0 | hχ
        · exact Or.inl (fun δ hδ => by simp [h0 δ hδ])
        · exact Or.inr hχ)
  choose ε hεadd hεloc hεagr hεesc using hcoord
  refine ⟨fun σ => eL.symm (fun k => ε k σ), ?_, ?_, ?_, ?_⟩
  · intro x y
    change eL.symm (fun k => ε k (x * y)) = eL.symm (fun k => ε k x) + eL.symm (fun k => ε k y)
    have h1 : (fun k => ε k (x * y)) = (fun k => ε k x) + (fun k => ε k y) := by
      funext k; exact hεadd k x y
    rw [h1]; exact map_add eL.symm _ _
  · have hloc : ∀ k, ∃ U : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar),
        IsOpen (U : Set (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ∧
        ∀ a : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, a ∈ (⊤ : Subgroup _) → ∀ u ∈ U,
          u ∈ (⊤ : Subgroup _) → ε k (a * u) = ε k a := fun k => hεloc k
    choose U hUo hU using hloc
    refine ⟨⨅ k, U k, ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite (fun k => hUo k)
    · intro a ha u hu huH
      have hu' : ∀ k, u ∈ U k := fun k => (Subgroup.mem_iInf.mp hu) k
      have h1 : (fun k => ε k (a * u)) = (fun k => ε k a) := by
        funext k; exact hU k a ha u (hu' k) huH
      show eL.symm (fun k => ε k (a * u)) = eL.symm (fun k => ε k a)
      rw [h1]
  · intro A hA δ hδ
    show eL.symm (fun k => ε k δ) = f A δ
    apply eL.injective
    rw [LinearEquiv.apply_symm_apply]
    funext k
    exact hεagr k A hA δ hδ
  · intro B hB hconj hsplit δ hδI
    show eL.symm (fun k => ε k δ) = 0
    rw [show (fun k => ε k δ) = 0 from
      funext fun k => hεesc k B hB hconj hsplit δ hδI, map_zero]

end Work.SSGRoute
