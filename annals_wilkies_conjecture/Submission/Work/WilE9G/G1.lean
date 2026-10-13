/-
  Subproject WilE9G — **G1 complete, in the form the construction consumes.**

  Combining
  * the normalised ambient `E5_strat` (`WilE9G/Reduce.lean`, `exists_strata_normalized`),
  * the per-stratum Sard theorem (`WilE9G/Sard/exists_null_of_Good`, from G1's Morse–Sard
    `WilE9G/Sard/morseSard` plus `WilE9G/Sard/volume_image_univ_eq_zero_of_lt`),
  * the finite-union-of-null-sets step (`WilE9G/Reduce.lean`, `exists_null_of_strata`),

  this file proves, unconditionally from the frozen `E5_strat`, the statement that the route calls
  step 2: every `X : SemiPf (0 + Q)` has a list of `Good` ambient strata covering `X.set`, of
  bounded format / degree / number of disjuncts, and a **null** set `N₁ ⊆ ℝ^n` outside which the
  base projection `π_n` is submersive along every stratum of the list at every one of its points.

  This is the only place where the Sard input of the subproject is used.
-/
import Submission.Work.WilE9G.Reduce
import Submission.Work.WilE9G.Sard.exists_null_of_Good

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-- **G1, assembled.**  From the frozen `E5_strat` (at `p = 0`) one gets, for every ambient
dimension `Q` and every `X : SemiPf (0 + Q)` of format `≤ F`, a list `L` of `Good` ambient strata
of `X` exactly covering `X.set` (with uniform format bound `a`, degree and disjunct-count both
bounded by `b X.deg`) and a null set `N₁ ⊆ ℝ^n` such that over every base point outside `N₁` the
projection `π_n` is submersive along every stratum of the list at each of its points.

This is the null set `N₁` of the route: outside it, the fibres of the strata are manifolds, which
is what the maximisation step (G3) needs. -/
theorem exists_strata_and_null
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (Q n : ℕ) (hn : n ≤ Q)
      (X : SemiPf (0 + Q)), X.fmt ≤ F →
      ∃ (L : List (Stratum 0 Q)) (N₁ : Set (Fin n → ℝ)),
        L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧
          S.X.basics.length ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        volume N₁ = 0 ∧
        ∀ S ∈ L, ∀ z ∈ S.X.set, projBase0 hn z ∉ N₁ →
          Work.WilE9G.Stratum.IsBaseSubmersiveAt S hn z := by
  intro F
  obtain ⟨a, b, hb⟩ := exists_strata_normalized hE5 F
  refine ⟨a, b, fun Q n hn X hX => ?_⟩
  obtain ⟨L, hlen, hgood, hunion⟩ := hb Q X hX
  obtain ⟨N₁, hnull, hN₁⟩ :=
    exists_null_of_strata hn (fun S hS => Sard.exists_null_of_Good hn S hS)
      L (fun S hS => (hgood S hS).2.2.2)
  exact ⟨L, N₁, hlen, hgood, hunion, hnull, fun S hS z hz hzN =>
    by_contra fun hnot => hzN (hN₁ S hS z hz hnot)⟩

end Work.WilE9G
