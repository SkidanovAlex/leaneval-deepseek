import Mathlib
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.FanTri.Phi_bdd

namespace Work.EQ.FanTri

/-- **The walk weights of `wtAux` are uniformly bounded.**
`wtAux a l 0 = ∏_j stW a l[j] (state_j)` is the product, along the walk of the letter list
`l` (started in state `0`), of the step weights `stW a c n = λ(1 ∓ 1/stQ a n)`,
`λ = eqLam a`, `stQ a n = |stCtr n + a/2|`.  Each excursion of the nearest-neighbour walk
away from the low states is paid for by an expansion on the way out and a contraction on the
way back, so the product is bounded; equivalently `wtAux a l 0 ≤ Phi a (stAux l 0)` by the
potential invariant of `Work.EQ.walk_bounds`, and the potential `Phi a` is bounded (it decays
geometrically since `λ < 1` while `∏_{j<n} (1 + 1/stQ a j)` grows at most polynomially).

Needed by `Work.EQ.FanTri.branchComp_radius`: the product of the one-step factors along a
finite composition of inverse branches is bounded by a constant depending only on `a`. -/
theorem wtAux_uniform_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : List Bool, Work.EQ.wtAux a l 0 ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Phi_bdd ha0 ha1
  refine ⟨C, hCpos, fun l => ?_⟩
  have hstep : ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ 1 :=
    fun n => le_of_lt (wb_upW_dnW_lt_one ha0 ha1 n)
  have h := wb_wtPhi_le ha0 ha1 hstep l 0
  rw [wb_Phi_zero, mul_one] at h
  exact le_trans h (hC (stAux l 0))

end Work.EQ.FanTri
