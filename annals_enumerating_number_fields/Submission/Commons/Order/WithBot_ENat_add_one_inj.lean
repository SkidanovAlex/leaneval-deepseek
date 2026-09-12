import Mathlib.Data.ENat.Basic

namespace Commons.Order

theorem WithBot_ENat_add_one_inj {x y : WithBot ℕ∞} (h : x + 1 = y + 1) : x = y :=
  (ENat.WithBot.add_one_cancel (a := x) (b := y)).mp h

end Commons.Order