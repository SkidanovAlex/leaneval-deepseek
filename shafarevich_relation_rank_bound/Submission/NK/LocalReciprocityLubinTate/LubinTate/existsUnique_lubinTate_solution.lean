import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Setup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Step
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Existence
import Submission.NK.LocalReciprocityLubinTate.Uniqueness.eq_of_Dsub_eq_zero

universe u

namespace NK.LocalReciprocityLubinTate.LubinTate

theorem existsUnique_lubinTate_solution {A : Type u} [CommRing A] {π : A} {q n : ℕ}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q)
    {f g : MvPowerSeries (Fin 1) A}
    (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f)
    (hg : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q g)
    (φ₁ : MvPowerSeries (Fin n) A)
    (hφ₁ : φ₁.constantCoeff = 0 ∧
      ∀ s : Fin n →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s φ₁ = 0) :
    ∃! φ : MvPowerSeries (Fin n) A,
      (∀ s : Fin n →₀ ℕ, s.degree ≤ 1 →
        MvPowerSeries.coeff s φ = MvPowerSeries.coeff s φ₁) ∧
      MvPowerSeries.subst ![φ] f =
        φ.subst (fun i => MvPowerSeries.subst ![MvPowerSeries.X i] g) := by
  obtain ⟨φ, hlin, heq⟩ := exists_sol hπ hpow hf hg hφ₁
  refine ⟨φ, ⟨hlin, Dsub_eq_zero_iff.mp heq⟩, fun y hy => ?_⟩
  exact NK.LocalReciprocityLubinTate.Uniqueness.eq_of_Dsub_eq_zero hπ hf hg hφ₁ hy.1 hlin
    (Dsub_eq_zero_iff.mpr hy.2) heq

end NK.LocalReciprocityLubinTate.LubinTate
