import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.fract_mul_injOn
import Submission.Work.SeedSimple2.Invariance
import Submission.Work.SeedSimple2.Rotation.arcBound_of_sidePreserve
import Submission.Work.SeedSimple2.COP.landsN_pow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 2000000

namespace Work.SeedSimple2.COP

/-- **The iterated angles of a non-fixed landing angle are pairwise consecutive-distinct and avoid `0` and `α₁`** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L3` consequences (i)–(iii)): for `θ ∈ A` with `Int.fract (1024 * θ) ≠ θ`, writing `θₙ := Int.fract ((1024:ℝ)^n * θ)`, one has `θₙ ≠ θₙ₊₁`, `θₙ ≠ α₁` and `θₙ ≠ 0` for every `n`.  These are the non-degeneracy hypotheses of `cop_angles` in the `L9` triple `(θₙ, α₁, θₙ₊₁)`.

Proof design.  `θₙ ∈ A` (`Work.SeedSimple2.COP.landsN_pow`; if that module is not yet available, copy the `hland_pow` argument of `Submission/Work/SeedSimple2/Rotation/arcBound_of_sidePreserve.lean` — `landsN_T_iterate`, `Work.ELRig.T_iterate_eq_add_int`, `Work.SeedSimple2.landsN_add_int`).  Also `Int.fract (1024 * α₁) = α₁` (`Work.SeedSimple2.Rotation.mul_alpha1`) and `Int.fract (1024 * 0) = 0`.  Note `Int.fract (1024 * θₙ) = θₙ₊₁` and `θ = θ₀` (because `θ ∈ Set.Ico 0 1`).

* (first conjunct) If `θₙ = θₙ₊₁` with `n ≥ 1`, then `Int.fract (1024 * θₙ₋₁) = θₙ = Int.fract (1024 * θₙ)`, so `Work.SeedSimple2.COP.fract_mul_injOn` gives `θₙ₋₁ = θₙ`;  backwards induction gives `θ₁ = θ₀ = θ`, contradicting `hne`.
* (second conjunct) If `θₙ = α₁` (`n ≥ 1`), then `Int.fract (1024 * θₙ₋₁) = θₙ = α₁ = Int.fract (1024 * α₁)`, so `fract_mul_injOn` gives `θₙ₋₁ = α₁`;  backwards induction gives `θ = α₁`, hence `Int.fract (1024 * θ) = α₁ = θ`, contradicting `hne`.
* (third conjunct) Same with `0` in place of `α₁`. -/
theorem theta_iterate_ne {c : ℂ} (d : Work.EL.RootParabolic c) {θ : ℝ}
    (hθ : θ ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (hne : Int.fract (1024 * θ) ≠ θ) :
    (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Int.fract ((1024:ℝ)^(n+1) * θ)) ∧
    (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Work.EL.alpha1) ∧
    (∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ 0) := by
  have hmem : ∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ :=
    fun n => Work.SeedSimple2.COP.landsN_pow d hθ n
  have hstep : ∀ n : ℕ,
      Int.fract (1024 * Int.fract ((1024:ℝ)^n * θ)) = Int.fract ((1024:ℝ)^(n+1) * θ) := by
    intro n
    have hdec := Int.fract_add_floor ((1024:ℝ)^n * θ)
    have key : (1024:ℝ) * ((1024:ℝ)^n * θ)
        = 1024 * Int.fract ((1024:ℝ)^n * θ)
          + ((1024 * ⌊((1024:ℝ)^n * θ)⌋ : ℤ) : ℝ) := by
      have hcast : ((1024 * ⌊((1024:ℝ)^n * θ)⌋ : ℤ) : ℝ)
          = 1024 * (⌊((1024:ℝ)^n * θ)⌋ : ℝ) := by push_cast; ring
      rw [hcast]; linarith [hdec]
    have hp : (1024:ℝ)^(n+1) * θ = 1024 * ((1024:ℝ)^n * θ) := by
      rw [pow_succ]; ring
    rw [hp, key, Int.fract_add_intCast]
  have hθeq : Int.fract ((1024:ℝ)^0 * θ) = θ := by
    rw [pow_zero, one_mul]
    exact Int.fract_eq_self.mpr hθ.1
  have halpha1_mem : Work.EL.alpha1 ∈ Work.SeedSimple2.LandAngles d.hN d.z₁ :=
    ⟨by constructor <;> norm_num [Work.EL.alpha1],
      (Work.SeedSimple2.landsN_iff_landsAt d).mpr d.rays.1⟩
  have halpha1_fix : Int.fract (1024 * Work.EL.alpha1) = Work.EL.alpha1 := by
    rw [Work.SeedSimple2.Rotation.mul_alpha1,
        show (371:ℝ) + Work.EL.alpha1 = Work.EL.alpha1 + ((371:ℤ):ℝ) by push_cast; ring,
        Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by norm_num [Work.EL.alpha1], by norm_num [Work.EL.alpha1]⟩
  have hconj1 : ∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Int.fract ((1024:ℝ)^(n+1) * θ) := by
    have main : ∀ m : ℕ, Int.fract ((1024:ℝ)^m * θ) = Int.fract ((1024:ℝ)^(m+1) * θ) →
        Int.fract ((1024:ℝ)^0 * θ) = Int.fract ((1024:ℝ)^1 * θ) := by
      intro m
      induction m with
      | zero => intro h; exact h
      | succ k ih =>
        intro h
        have heq : Int.fract (1024 * Int.fract ((1024:ℝ)^k * θ))
            = Int.fract (1024 * Int.fract ((1024:ℝ)^(k+1) * θ)) := by
          rw [hstep k, hstep (k+1)]
          exact h
        exact ih (Work.SeedSimple2.COP.fract_mul_injOn d (hmem k) (hmem (k+1)) heq)
    intro n heq
    have hne' : Int.fract ((1024:ℝ)^1 * θ) ≠ Int.fract ((1024:ℝ)^0 * θ) := by
      rw [hθeq, show (1024:ℝ)^1 * θ = 1024 * θ by ring]
      exact hne
    exact hne' (main n heq).symm
  have hconj2 : ∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ Work.EL.alpha1 := by
    have main : ∀ m : ℕ, Int.fract ((1024:ℝ)^m * θ) = Work.EL.alpha1 →
        Int.fract ((1024:ℝ)^0 * θ) = Work.EL.alpha1 := by
      intro m
      induction m with
      | zero => intro h; exact h
      | succ k ih =>
        intro h
        have heq : Int.fract (1024 * Int.fract ((1024:ℝ)^k * θ))
            = Int.fract (1024 * Work.EL.alpha1) := by
          rw [hstep k, halpha1_fix]
          exact h
        exact ih (Work.SeedSimple2.COP.fract_mul_injOn d (hmem k) halpha1_mem heq)
    intro n h
    have h0 : θ = Work.EL.alpha1 := by
      rw [← hθeq]
      exact main n h
    have : Int.fract (1024 * θ) = θ := by
      rw [h0, halpha1_fix]
    exact hne this
  have hconj3 : ∀ n : ℕ, Int.fract ((1024:ℝ)^n * θ) ≠ 0 := by
    intro n hzero
    have hEq : Int.fract ((1024:ℝ)^n * θ) = Int.fract ((1024:ℝ)^(n+1) * θ) := by
      rw [← hstep n, hzero]
      rw [show (1024:ℝ) * 0 = 0 by ring, Int.fract_zero]
    exact hconj1 n hEq
  exact ⟨hconj1, hconj2, hconj3⟩

end Work.SeedSimple2.COP

