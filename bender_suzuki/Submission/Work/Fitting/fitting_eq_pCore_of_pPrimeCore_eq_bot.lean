import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_eq_iSup_pCore
import Submission.Work.Fitting.pCore_le_fitting
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- If `q ≠ p` then the `q`-core is a normal `p'`-subgroup, hence lies in the `p'`-core:
`O_q(G) ≤ O_{p'}(G)`. -/
theorem pCore_le_pPrimeCore_of_ne {G : Type*} [Group G] [Finite G] {p q : ℕ} (hqp : q ≠ p) :
    Work.Fitting.pCore q G ≤ Work.Fitting.pPrimeCore p G := by
  refine le_piCore (inferInstance : (Work.Fitting.pCore q G).Normal) ?_
  intro r hr hdvd
  have hrq : r = q := Work.Fitting.piCore_isPiNat G (fun s => s = q) r hr hdvd
  exact fun h => hqp (hrq ▸ h)

theorem fitting_eq_pCore_of_pPrimeCore_eq_bot (p : ℕ) (G : Type*) [Group G] [Finite G]
    (hp : p.Prime) (h : Work.Fitting.pPrimeCore p G = ⊥) :
    Work.Fitting.fitting G = Work.Fitting.pCore p G := by
  refine le_antisymm ?_ (Work.Fitting.pCore_le_fitting G p)
  rw [Work.Fitting.fitting_eq_iSup_pCore G]
  refine iSup_le fun q => iSup_le fun _ => ?_
  by_cases hqp : q = p
  · subst hqp; exact le_rfl
  · have hle := pCore_le_pPrimeCore_of_ne (G := G) hqp
    rw [h] at hle
    exact hle.trans bot_le

end Work.Fitting
