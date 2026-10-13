import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs
import Submission.Work.WilE9G.Sard.pairFlatOrderSucc
import Submission.Work.WilE9G.Sard.pairFlatLocal
import Submission.Work.WilE9G.Sard.analyticAtContDiffOnBall
import Submission.Work.WilE9G.Sard.volume_image_eq_zero_of_flat_along_vec

/-!
# The flat engine of the analytic Sard theorem

`engineFlat` : for `F : ℝᵈ → ℝᵐ` analytic at every point of a bounded set `A` on which all iterated
derivatives of orders `1, …, j-1` vanish, and with `d ≤ j * m`, the image `F '' A` is
Lebesgue-null.

Three ingredients are combined.

* `pairFlatLocal` (proved in this directory) is the local form of the pairwise flatness lemma
  `pairFlatOrderSucc`: a map that is `C^{J+2}` on a ball around `x` and whose derivatives of orders
  `1, …, J+1` vanish on `A ∋ x` is flat of order `J+2` along `A` at `x`.  The passage from
  `ContDiffOn` on a ball to the global `C^{J+2}` needed by `pairFlatOrderSucc` is done with a smooth
  cutoff which is `1` near `x` and supported inside the ball.

* `analyticAtContDiffOnBall` (proved in this directory) is the elementary observation that a map
  which is analytic at `x` is `C^n` on a ball of positive radius around `x`, so that the previous
  item applies in the analytic setting of the theorem.

* `volume_image_eq_zero_of_flat_along_vec` (proved in this directory) says that a map which is
  flat of order `q` along a bounded set `A`, with `d ≤ q * m`, has null image.

Putting these together with `J = j - 2` — so that `J + 2 = j` and `J + 1 = j - 1` — proves the
theorem.
-/

namespace Work.WilE9G.Sard

open MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

/-- **The flat engine.**  Let `F : ℝᵈ → ℝᵐ` be analytic at every point of a bounded set `A` at
which all iterated derivatives of orders `1, …, j-1` vanish, and suppose `d ≤ j * m`.  Then
`F '' A` is Lebesgue-null. -/
theorem engineFlat {d m j : ℕ} (hj : 2 ≤ j) (hm : 0 < m) (hjm : d ≤ j * m)
    (F : (Fin d → ℝ) → (Fin m → ℝ)) (A : Set (Fin d → ℝ)) (hbdd : Bornology.IsBounded A)
    (han : ∀ x ∈ A, AnalyticAt ℝ F x) (hflat : A ⊆ flatSetV F (j - 1)) :
    MeasureTheory.volume (F '' A) = 0 := by
  -- It suffices to show that `F` is flat of order `j` along `A`, since `d ≤ j * m`.
  refine volume_image_eq_zero_of_flat_along_vec (n := d) (m := m) (q := j) hm hjm F A hbdd ?_
  intro x hx ε hε
  -- `A ⊆ flatSetV F (j-1)` restated as vanishing of the first `(j-2)+1 = j-1` derivatives.
  have hflatx : A ⊆ {z : Fin d → ℝ |
      ∀ i, 1 ≤ i → i ≤ (j - 2) + 1 → iteratedFDeriv ℝ i F z = 0} := by
    intro z hz i hi hiJ
    have hz' := hflat hz
    rw [mem_flatSetV] at hz'
    exact hz' i hi (by omega)
  -- Analyticity at `x` gives `C^j` on a ball around `x`.
  obtain ⟨R, hR, hRcd⟩ := analyticAtContDiffOnBall (f := F) (x := x) (n := j) (han x hx)
  have hRcd' : ContDiffOn ℝ (((j - 2) + 2 : ℕ) : WithTop ℕ∞) F (Metric.ball x R) := by
    rw [show (j - 2) + 2 = j by omega]
    exact hRcd
  -- Local pairwise flatness of order `(j-2)+2 = j` along `A` at `x`.
  have hres := pairFlatLocal (f := F) (J := j - 2) A hx hR hRcd' hflatx
  obtain ⟨ρ, hρpos, hρ⟩ := hres ε hε
  exact ⟨ρ, hρpos, fun y hy hyρ => by
    have h1 := hρ y hy hyρ
    simpa only [show (j - 2) + 2 = j by omega] using h1⟩

end Work.WilE9G.Sard
