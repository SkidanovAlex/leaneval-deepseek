import Submission.Commons.Analysis.InfiniteSum.summable_prod_mul

namespace Commons.Analysis.Series

theorem summable_prod_mul_nonneg {α β : Type*} [Countable α] [Countable β]
    {f : α → ℝ} {g : β → ℝ} (hf : Summable f) (hg : Summable g)
    (hfn : ∀ a, 0 ≤ f a) (hgn : ∀ b, 0 ≤ g b) :
    Summable (fun p : α × β => f p.1 * g p.2) :=
  Commons.Analysis.InfiniteSum.summable_prod_mul hf hg hfn hgn

end Commons.Analysis.Series
