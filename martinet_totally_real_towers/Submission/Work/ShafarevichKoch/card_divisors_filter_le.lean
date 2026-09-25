import Mathlib

namespace Work.ShafarevichKoch

/-- `30030 = 2·3·5·7·11·13` is squarefree with exactly `2^6 = 64` divisors, and the map
`d ↦ 30030/d` is a fixed-point-free involution of the divisor set (`173² = 29929 < 30030 <
30276 = 174²`), so exactly one element of each pair `{d, 30030/d}` is `≤ 173`; hence exactly `32`
divisors of `30030` are at most `173`.  The 32 small divisors are
`{1,2,3,5,6,7,10,11,13,14,15,21,22,26,30,33,35,39,42,55,65,66,70,77,78,91,105,110,130,143,154,165}`,
so proving the `Finset` equality with this list and then evaluating the cardinality is one
acceptable route (over `Finset` of `ℕ`, e.g. `Finset.ext` + `Nat.mem_divisors` + `norm_num`).
NOTE: do NOT use `native_decide` (it depends on `Lean.ofReduceBool`, which is not among the
permitted axioms); plain `decide` needs `set_option maxRecDepth` raised a lot. -/
theorem card_divisors_filter_le : ((30030 : ℕ).divisors.filter (· ≤ 173)).card = 32 := by
  set_option maxRecDepth 1000000 in
  decide

end Work.ShafarevichKoch
