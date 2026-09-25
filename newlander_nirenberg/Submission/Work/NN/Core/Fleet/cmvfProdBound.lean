import Submission.Work.NN.Core.moserProductBound
import Submission.Work.NN.Core.Fleet.prodBoundQuant

namespace Work.NN.Core.Fleet

/-- Uniform bound on the partial products `∏_{j<J} b_j^{1/m_j}`, given `b_j ≤ B L^j`
and `m_j ≥ c p^j` with `p > 1` and `L ≥ 1`:
the product is at most `(max 1 B)^{1/(c(1-1/p))} * (max 1 L)^{p/(c(p-1)^2)}`,
uniformly in `J`.

This is the `L ≥ 1` form of `prodBoundQuant` (which only needs `L > 0`). -/
theorem cmvfProdBound {p c B L : ℝ} (hp : 1 < p) (hc : 0 < c) (hB : 0 < B) (hL : 1 ≤ L)
    {m : ℕ → ℕ} (hm : ∀ j, c * p ^ j ≤ (m j : ℝ)) (hmpos : ∀ j, 1 ≤ m j)
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hbd : ∀ j, b j ≤ B * L ^ j) :
    ∀ J : ℕ, (∏ j ∈ Finset.range J, b j ^ (1 / (m j : ℝ)))
      ≤ (max 1 B) ^ (1 / (c * (1 - 1 / p))) * (max 1 L) ^ (p / (c * (p - 1) ^ 2)) :=
  prodBoundQuant hp hc hB (lt_of_lt_of_le zero_lt_one hL) hm hmpos hb hbd

end Work.NN.Core.Fleet
