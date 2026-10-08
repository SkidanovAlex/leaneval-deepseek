import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.LocalPrelim.sylow_inf_pPrimeCore_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

-- A Sylow `p`-subgroup meets `O_{p'}(G)` trivially.  (Already available for
-- `Work.Fitting.pPrimeCore` as `Work.LocalPrelim.sylow_inf_pPrimeCore_eq_bot`;
-- this is the `Submission.Blueprint.pPrimeCore` version.)
theorem sylow_inf_pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) : (P : Subgroup G) ⊓ Submission.Blueprint.pPrimeCore p G = ⊥ := by
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  exact Work.LocalPrelim.sylow_inf_pPrimeCore_eq_bot hp P

end Work.GlaubermanZJ
