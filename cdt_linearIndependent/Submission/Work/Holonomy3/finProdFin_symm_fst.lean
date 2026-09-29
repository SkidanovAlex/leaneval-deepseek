import Mathlib

namespace Work.Holonomy3

lemma finProdFin_symm_fst {m d k : ℕ} (hmul : m * k = d) (j : Fin d) :
    ((((finProdFinEquiv (m := m) (n := k)).trans (finCongr hmul)).symm j).1 : ℕ) = (j : ℕ) / k := by
  simp only [Equiv.symm_trans_apply, finProdFinEquiv_symm_apply, finCongr_symm_apply]
  rfl

end Work.Holonomy3
