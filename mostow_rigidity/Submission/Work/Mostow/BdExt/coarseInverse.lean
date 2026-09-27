import Mathlib
import Submission.Work.Mostow.BdExt.Basic

/-!
# A quasi-isometry has a coarse inverse

Given a quasi-isometry `Φ` of `ℍⁿ` (upper bound `K, C`, lower bound `K, C`, and coarse
surjectivity with constant `C`), we build a coarse inverse `Ψ` and check the four standard
estimates.  Nothing here uses anything about `Φ` beyond the quasi-isometry inequalities and
the fact that `hdist` is a metric (`HypIsometryProp`).

The construction is `Ψ w := (hsurj w).choose`, i.e. choose for every `w` a point `u` with
`hdist (Φ u) w ≤ C`.  The estimates are then straightforward triangle-inequality chases:
* `Φ (Ψ w)` is `C`-close to `w`                                   (choice),
* `Ψ (Φ u)` is `K C + C`-close to `u`                            (lower bound on `Φ`),
* `Ψ` is a `(K, 2 K C + C)`-quasi-isometry                       (lower bound + two choices),
* `Ψ` is coarsely surjective with constant `K C + C`             (take `u = Φ w`).
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option linter.unusedVariables false in
theorem coarseInverse (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n) (Φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (hsurj : ∀ w, ∃ u, Submission.Mostow.hdist (Φ u) w ≤ C) :
    ∃ Ψ : Submission.Mostow.E n → Submission.Mostow.E n,
      (∀ w, Submission.Mostow.hdist (Φ (Ψ w)) w ≤ C) ∧
      (∀ u, Submission.Mostow.hdist (Ψ (Φ u)) u ≤ K * C + C) ∧
      (∀ u v, Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ K * Submission.Mostow.hdist u v + (2 * K * C + C)) ∧
      (∀ w, ∃ u, Submission.Mostow.hdist (Ψ u) w ≤ K * C + C) := by
  classical
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hsymm : ∀ u v : E n, hdist u v = hdist v u := fun u v => hI.2.1 u v
  have htri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := fun u v w => hI.2.2.2.1 u v w
  let Ψ : E n → E n := fun w => (hsurj w).choose
  have hΨ1 : ∀ w, hdist (Φ (Ψ w)) w ≤ C := fun w => (hsurj w).choose_spec
  have hΨ2 : ∀ u, hdist (Ψ (Φ u)) u ≤ K * C + C := by
    intro u
    have h := hlow (Ψ (Φ u)) u
    have h2 : hdist (Φ (Ψ (Φ u))) (Φ u) ≤ C := (hsurj (Φ u)).choose_spec
    have h3 : K * hdist (Φ (Ψ (Φ u))) (Φ u) ≤ K * C := mul_le_mul_of_nonneg_left h2 hK0
    linarith
  refine ⟨Ψ, hΨ1, hΨ2, ?_, ?_⟩
  · intro u v
    have h := hlow (Ψ u) (Ψ v)
    have h2a : hdist (Φ (Ψ u)) u ≤ C := (hsurj u).choose_spec
    have h2b : hdist (Φ (Ψ v)) v ≤ C := (hsurj v).choose_spec
    have hkey : hdist (Φ (Ψ u)) (Φ (Ψ v)) ≤ hdist u v + 2 * C := by
      have ht1 := htri (Φ (Ψ u)) u (Φ (Ψ v))
      have ht2 := htri u v (Φ (Ψ v))
      have hs := hsymm v (Φ (Ψ v))
      linarith
    have h3 : K * hdist (Φ (Ψ u)) (Φ (Ψ v)) ≤ K * (hdist u v + 2 * C) :=
      mul_le_mul_of_nonneg_left hkey hK0
    linarith
  · intro w
    exact ⟨Φ w, hΨ2 w⟩

end Work.Mostow.BdExt
