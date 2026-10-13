import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaTaylor_remainder

namespace Work.WilE3.Taylor

open Classical Topology
open WilkiesDesign WilkiesDesign.E

/-- If `y` is in the closure of the Taylor set of `B` at `y` of order `κ ≥ 1`, then all the
equations of `B` vanish at `y`.  Proof: for each equation `f`, the set where
`|T_{κ²} f (x)| ≤ dist x y ^ (κ ^ 2)` is closed, contains the Taylor set, hence contains its
closure; at `x = y` it says `|eaEval c f y| ≤ 0`.  This is used in the `(⇐)` direction of
`E3_taylor_closure` to know that the zero set `Z = {x | ∀ f ∈ B.eqs, eaEval c f x = 0}` of the
equations is non-empty (it contains `y`). -/
theorem E3_eqs_vanish_of_closure {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (B : WilkiesDesign.E.Basic k r) (y : Fin k → ℝ) (κ : ℕ) (hκ : 1 ≤ κ)
    (h : y ∈ closure (Work.WilE3.taylorSet c B y κ)) :
    ∀ f ∈ B.eqs, WilkiesDesign.E.eaEval c f y = 0 := by
  intro f hf
  -- The order-`κ ^ 2` Taylor polynomial of `f` at `y` is continuous in the evaluation point.
  have hFcont : Continuous (fun x : Fin k → ℝ => eaTaylor c f (κ ^ 2) y x) := by
    unfold eaTaylor
    fun_prop
  have hGcont : Continuous (fun x : Fin k → ℝ => dist x y ^ (κ ^ 2)) := by fun_prop
  -- Hence the Taylor equation of `f` cuts out a closed set.
  have hclosed : IsClosed {x : Fin k → ℝ | |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)} :=
    isClosed_le hFcont.abs hGcont
  -- The Taylor set of `B` is contained in it, so its closure is too.
  have hsub : Work.WilE3.taylorSet c B y κ ⊆
      {x | |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)} :=
    fun x hx => hx.1 f hf
  have hy : y ∈ {x : Fin k → ℝ | |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)} :=
    closure_minimal hsub hclosed h
  -- Evaluating at `x = y` gives `|eaEval c f y| ≤ dist y y ^ (κ ^ 2) = 0`.
  rw [Set.mem_ofPred_eq, Work.WilE3.API.eaTaylor_self, dist_self] at hy
  have h0 : (0 : ℝ) ^ (κ ^ 2) = 0 := zero_pow (pow_ne_zero 2 (by omega))
  rw [h0] at hy
  exact abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))

end Work.WilE3.Taylor
