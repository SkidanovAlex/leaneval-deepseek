import Mathlib
import Submission.Work.WilC2.ChoiceDefs
import Submission.Work.WilC2.choice_real
import Submission.Work.WilC2.selectForm_exists
import Submission.Work.WilC2.exists_choiceSentence
import Submission.Work.WilC2.Family
import Submission.Work.WilC2.Square

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- The fibre of `φ` over `c` is a finite union of preconnected (interval) pieces: this is
`hUF` applied to the `∅`-definable family attached to `φ`, together with the syntax bridge
`hC0`. -/
theorem real_fib_cover
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X →
      WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp) {n : ℕ} (φ : ParamFormula n) :
    ∀ c : Fin n → ℝ, ∃ s : Finset (Set ℝ), (∀ I ∈ s, IsPreconnected I) ∧
      Fib φ c = ⋃₀ (s : Set (Set ℝ)) := by
  obtain ⟨N, hN⟩ := hUF n (familyOf φ) (hC0 (n + 1) (familyOf φ) (familyOf_definable φ))
  intro c
  obtain ⟨s, -, hpre, heq⟩ := hN c
  exact ⟨s, hpre, by
    ext t
    exact ((familyOf_fibre φ c t).symm).trans (Set.ext_iff.mp heq t)⟩

theorem definable_choice_fibre
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {n : ℕ} (φ : ParamFormula n) :
    ∃ ψ : ParamFormula n, ∀ v : Fin n → M,
      (∃ y : M, φ.Realize (Sum.elim v (fun _ => y))) →
      ∃! y : M, ψ.Realize (Sum.elim v (fun _ => y)) ∧ φ.Realize (Sum.elim v (fun _ => y)) := by
  obtain ⟨ψ, hψ⟩ := selectForm_exists φ
  -- the choice condition has a unique solution on every nonempty fibre of `ℝ`
  have hreal : ∀ v : Fin n → ℝ, (∃ y : ℝ, φ.Realize (Sum.elim v (fun _ => y))) →
      ∃! y : ℝ, ψ.Realize (Sum.elim v (fun _ => y)) ∧
        φ.Realize (Sum.elim v (fun _ => y)) := by
    intro v hv
    have hne : (Fib φ v).Nonempty := hv
    obtain ⟨y₀, hy₀, huniq⟩ := real_choice φ (real_fib_cover hC0 hUF φ) v hne
    refine ⟨y₀, ⟨?_, ?_⟩, ?_⟩
    · exact (hψ (M := ℝ) real_exists_sq v y₀).mpr hy₀
    · exact LeftComp_subset_Fib hy₀.1
    · intro y' hy'
      exact huniq y' ((hψ (M := ℝ) real_exists_sq v y').mp hy'.1)
  -- the same statement, packaged as one sentence and transferred to `M`
  obtain ⟨σ, hσ⟩ := exists_choiceSentence φ ψ
  have hℝ : ℝ ⊨ σ := (hσ (M := ℝ)).mpr hreal
  haveI : M ⊨ LRc.completeTheory ℝ := ‹M ⊨ TR›
  have hM : M ⊨ σ :=
    (realize_iff_of_model_completeTheory (L := LRc) (M := ℝ) (N := M) σ).mpr hℝ
  exact ⟨ψ, (hσ (M := M)).mp hM⟩

end Work.WilC2
