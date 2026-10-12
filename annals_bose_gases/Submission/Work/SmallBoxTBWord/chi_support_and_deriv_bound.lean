import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open scoped ContDiff

/--
The support of a smooth compactly supported `ℝ`-valued function `χ` on `ℝ³` is contained in
a ball `B(0,R)` with `R > 0`, and the iterated Fréchet derivatives up to order `3` of its
complexification are globally bounded by a nonnegative sequence `G`.

The proof splits into two independent pieces:
* compactness of `tsupport χ` gives a ball containing it (and we enlarge the radius to be `> 0`);
* each `iteratedFDeriv ℝ k (χ : ℝ³ → ℂ)` is continuous (as `χ` is `C^∞`) and has compact
  support (the support of an iterated derivative is contained in the support of the function),
  hence its range is compact, hence bounded, giving a uniform bound `G k`.
-/
theorem chi_support_and_deriv_bound {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hcs : HasCompactSupport χ) :
    ∃ R : ℝ, 0 < R ∧ tsupport χ ⊆ Metric.closedBall 0 R ∧
      ∃ G : ℕ → ℝ, (∀ k, 0 ≤ G k) ∧
        ∀ k ≤ 3, ∀ z : EuclideanSpace ℝ (Fin 3),
          ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) z‖ ≤ G k := by
  -- The support is compact, hence bounded, hence contained in a ball.
  obtain ⟨r, hr⟩ := hcs.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))
  have hRpos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hsupp : tsupport χ ⊆ Metric.closedBall 0 (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  -- The complexification `χ : ℝ³ → ℂ` is `C^∞` and compactly supported.
  have hfc : ContDiff ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) := by
    have key := Complex.ofRealCLM.contDiff (𝕜 := ℝ) (n := (⊤ : ENat)) |>.comp hχ
    have h : (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) = Complex.ofRealCLM ∘ χ := by
      ext z; simp [Complex.ofRealCLM_apply]
    rwa [h]
  have hfk : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) := by
    have key := hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
    have h : (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) =
        (fun x : ℝ => (x : ℂ)) ∘ χ := by ext z; rfl
    rwa [h]
  refine ⟨max r 1, hRpos, hsupp, ?_⟩
  -- Each iterated derivative is continuous with compact support, hence bounded.
  have hbound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ k (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) z‖ ≤ C := by
    intro k
    have hk : ContDiff ℝ (k : ℕ∞ω) (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) :=
      hfc.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    have hcont : Continuous (fun x => iteratedFDeriv ℝ k
        (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) x) := hk.continuous_iteratedFDeriv'
    have hcpt : HasCompactSupport (fun x => iteratedFDeriv ℝ k
        (fun z : EuclideanSpace ℝ (Fin 3) => (χ z : ℂ)) x) :=
      HasCompactSupport.iteratedFDeriv (𝕜 := ℝ) hfk k
    obtain ⟨C, hCpos, hCle⟩ := (hcpt.isCompact_range hcont).isBounded.subset_closedBall_lt 0 0
    refine ⟨C, le_of_lt hCpos, fun z => ?_⟩
    have hz := hCle ⟨z, rfl⟩
    rwa [Metric.mem_closedBall, dist_zero_right] at hz
  choose G hG0 hGbound using hbound
  exact ⟨G, hG0, fun k _ z => hGbound k z⟩

end Work.SmallBoxTBWord
