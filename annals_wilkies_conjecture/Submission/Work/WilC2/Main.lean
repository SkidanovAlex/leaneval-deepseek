/-
  Area C2 (WilC2): `C2_models_ominimal` — uniform finiteness of rexp-existential families in `ℝ`
  implies o-minimality of every model of `TR`.
-/
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC2.sliceGood_fibre_ordConnected
import Submission.Work.WilC2.definable_fin_params

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

/-- **C2.** Uniform finiteness of rexp-existential families in `ℝ` (plus the syntax bridge
`C0`: every `LRc`-definable set is rexp-existential) makes every model of `T_r` o-minimal. -/
theorem C2_models_ominimal_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X → RExpExist X)
    (hUF : UnifFiniteRExp) : OMinModels := by
  intro M _ _ _ _ _ _ hM X hX
  obtain ⟨n, φ, v, hXeq⟩ := definable_fin_params hX
  have hY : RExpExist (familyOf φ) := hC0 (n + 1) (familyOf φ) (familyOf_definable φ)
  obtain ⟨N, hN⟩ := hUF n (familyOf φ) hY
  have hfib : ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧ (∀ I ∈ s, IsPreconnected I) ∧
      {t : ℝ | φ.Realize (Sum.elim c (fun _ => t))} = ⋃₀ (s : Set (Set ℝ)) := by
    intro c
    obtain ⟨s, hcard, hpre, heq⟩ := hN c
    exact ⟨s, hcard, hpre, by
      ext t
      exact ((familyOf_fibre φ c t).symm).trans (Set.ext_iff.mp heq t)⟩
  have hgood : SliceGood (N + 1) φ M := by
    haveI : M ⊨ TR := hM
    exact sliceGood_of_model φ hfib
  obtain ⟨s, hconn, heq⟩ := sliceGood_fibre_ordConnected (N + 1) (Nat.succ_le_succ (Nat.zero_le N))
    φ v hgood
  exact ⟨s, hconn, by rw [hXeq, heq]⟩

end Work.WilC2
