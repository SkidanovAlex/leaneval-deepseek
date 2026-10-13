/-
  Area C2 (WilC2): the transfer of the fibre bounds from `ℝ` to every model of `TR`, and the
  resulting *uniform finiteness schema*: one bound `K` serves all models of `TR` at once.
-/
import Submission.Work.WilC2.Convert
import Submission.Work.WilC2.Square
import Submission.Work.WilC2.Family
import Submission.Work.WilC2.realSide_sliceGood
import Submission.Work.WilC2.sliceGood_fibre_ordConnected

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

/-- Uniform finiteness of the fibres of `φ` at `ℝ` gives the cut-point sentence at `ℝ`. -/
theorem real_sliceSent {n : ℕ} (φ : ParamFormula n) {N : ℕ}
    (hfib : ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      {t : ℝ | φ.Realize (Sum.elim c (fun _ => t))} = ⋃₀ (s : Set (Set ℝ))) :
    ℝ ⊨ sliceSent (N + 1) φ :=
  (realize_sliceSent_raw (N + 1) φ).mpr
    ((sliceRaw_iff_sliceGoodQ real_exists_sq (N + 1) φ).mpr
      ((sliceGoodQ_iff_sliceGood (N + 1) φ).mpr (realSide_sliceGood φ hfib)))

/-- The same fibre bound, read in a model `M ⊨ TR`: the fibres are convex on the pieces cut out
by monotone cut points. -/
theorem sliceGood_of_model {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M] [M ⊨ TR]
    {n : ℕ} (φ : ParamFormula n) {N : ℕ}
    (hfib : ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      {t : ℝ | φ.Realize (Sum.elim c (fun _ => t))} = ⋃₀ (s : Set (Set ℝ))) :
    SliceGood (N + 1) φ M := by
  have h𝔯 : ℝ ⊨ sliceSent (N + 1) φ := real_sliceSent φ hfib
  have hslice : M ⊨ sliceSent (N + 1) φ := by
    haveI : M ⊨ LRc.completeTheory ℝ := ‹M ⊨ TR›
    exact (realize_iff_of_model_completeTheory (L := LRc) (M := ℝ) (N := M)
      (sliceSent (N + 1) φ)).mpr h𝔯
  exact (sliceGoodQ_iff_sliceGood (N + 1) φ).mp
    ((sliceRaw_iff_sliceGoodQ (model_exists_sq ‹M ⊨ TR›) (N + 1) φ).mp
      ((realize_sliceSent_raw (N + 1) φ).mp hslice))

/-- **Uniform finiteness in every model of `TR`.**  There is one bound `K` (depending only on the
family `φ` and on the data of `ℝ_rexp`) such that in *every* model `M ⊨ TR` and for every choice
of real parameters, the fibre of `φ` is a union of at most `2K+1` order-convex subsets of `M`,
witnessed by `K` cut points. -/
theorem uniform_finite_models
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X → RExpExist X)
    (hUF : UnifFiniteRExp) {n : ℕ} (φ : ParamFormula n) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
        [rexpL.Structure M] [(constantsOn ℝ).Structure M] [M ⊨ TR] (v : Fin n → M),
        ∃ s : Finset (Set M), (∀ I ∈ s, I.OrdConnected) ∧
          {x : Fin 1 → M | φ.Realize (Sum.elim v x)} = {x | x 0 ∈ ⋃₀ (s : Set (Set M))} := by
  obtain ⟨N, hN⟩ := hUF n (familyOf φ) (hC0 (n + 1) (familyOf φ) (familyOf_definable φ))
  have hfib : ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      {t : ℝ | φ.Realize (Sum.elim c (fun _ => t))} = ⋃₀ (s : Set (Set ℝ)) := by
    intro c
    obtain ⟨s, hcard, hpre, heq⟩ := hN c
    exact ⟨s, hcard, hpre, by
      ext t
      exact ((familyOf_fibre φ c t).symm).trans (Set.ext_iff.mp heq t)⟩
  refine ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N), fun M _ _ _ _ _ _ _ v => ?_⟩
  exact sliceGood_fibre_ordConnected (N + 1)
    (Nat.succ_le_succ (Nat.zero_le N)) φ v (sliceGood_of_model φ hfib)

end Work.WilC2
