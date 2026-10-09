import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.ArchDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `⟹` branch of the reverse Artin–Schreier characterisation

A norm `m * c m` for the involution `c` attached to the real place `w` is not negative at `w`:
`φ a = Ψ m * star (Ψ m) = |Ψ m|² ≥ 0`, using step 1's restriction formula
`Ψ (algebraMap k Ω b) = ((φ b : ℝ) : ℂ)` and step 3's `Ψ (c x) = star (Ψ x)`.

Two coercion points, inherited from the `⟸` file's experience: `normSet`'s membership uses
`c.toRingEquiv`, so the involution's action needs `show`-absorption before `hc` can fire; and the
final positivity step must stay in `ℝ` (`Complex.ofReal_re` only, not the full `simp` set, which
would drag in the `embedding_of_isReal` identification).
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

theorem not_isNegAt_of_mem_normSet {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω] (w : NumberField.InfinitePlace k) (hw : w.IsReal)
    {Ψ : Ω →+* ℂ} {c : Ω ≃ₐ[k] Ω}
    (hΨ : ∀ a : k, Ψ (algebraMap k Ω a) =
      (((NumberField.InfinitePlace.embedding_of_isReal hw) a : ℝ) : ℂ))
    (hc : ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x))
    (a : kˣ) (hm : (algebraMap k Ω (a : k)) ∈
      Work.SSGRoute.TwoTorsion.normSet c.toRingEquiv) :
    ¬ Work.SSGRoute.ZDataTwo.IsNegAt w a := by
  obtain ⟨m, _hm0, hmeq⟩ := hm
  have h1 : Ψ (algebraMap k Ω (a : k)) = Ψ m * starRingEnd ℂ (Ψ m) := by
    rw [hmeq, map_mul]
    show Ψ m * Ψ (c m) = Ψ m * starRingEnd ℂ (Ψ m)
    rw [hc m]
  have hnonneg : 0 ≤ (NumberField.InfinitePlace.embedding_of_isReal hw) (a : k) := by
    have hval : (((NumberField.InfinitePlace.embedding_of_isReal hw) (a : k) : ℝ) : ℂ) =
        ((Complex.normSq (Ψ m) : ℝ) : ℂ) := by
      rw [← hΨ (a : k), h1]
      simpa [Complex.star_def] using Complex.mul_conj (Ψ m)
    have hre := congrArg Complex.re hval
    simp only [Complex.ofReal_re] at hre
    rw [hre]
    exact Complex.normSq_nonneg (Ψ m)
  intro hneg
  have hlt := (Work.SSGRoute.ZDataTwo.isNegAt_iff hw a).mp hneg
  linarith

end Work.SSGRoute.HRec
