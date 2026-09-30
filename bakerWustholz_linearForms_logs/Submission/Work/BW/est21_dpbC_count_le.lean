import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.card_auxIdx
import Submission.Work.BW.num_13
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `1 ≤ dK K = [K : ℚ]`. -/
theorem est21_dpbC_one_le_dK (K : Type*) [Field K] [NumberField K] : 1 ≤ dK K := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos (R := ℚ) (M := K)
  change 1 ≤ Module.finrank ℚ K
  omega

/-- Port of `Work.BW.est21_dpb_count_le` — the summand-count bound of the BW p. 49 `0.255` estimate.  The original lives in `Submission/Work/BW/est21_dpb_clean.lean` (line 224) and its proof is a three-line consequence of `card_auxIdx` (`Fintype.card (AuxIdx …) = …`) and `num13_logN` (from `num_13`); it also uses `(acH_lower H).1` and `sigma_ge H` — copy it.  That file is not importable because it imports `Submission.Work.BW.est13`, which does not compile.  ANY extra declaration you make must have a name starting with `est21_dpbC_` and be public. -/
lemma est21_dpbC_count_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) {t0 : ℕ}
    (ht0 : (t0 : ℝ) ≤ (pT r (dK K) σ : ℝ)) :
    ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) ≤
      Real.exp (0.001 * (acH K b v : ℝ) * (pT r (dK K) σ : ℝ)) := by
  have hlog := num13_logN H.hr (est21_dpbC_one_le_dK K) (acH_lower H).1 σ
    (fun j => sigma_ge H j)
  rw [card_auxIdx]
  refine Real.le_exp_of_log_le ?_
  push_cast
  exact hlog

end Work.BW
