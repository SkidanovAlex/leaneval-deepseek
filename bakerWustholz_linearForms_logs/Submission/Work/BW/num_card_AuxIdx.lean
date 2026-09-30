import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.card_auxIdx
import Submission.Work.BW.num_13
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.split_aux
import Submission.Work.BW.num_card_AuxIdx_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- BW §13, (11): the number `N = h(D₀+1)∏_j(D_j+1)` of indices of the auxiliary polynomial satisfies `log N ≤ 0.001·S·D/d`. Follows from `num_13`/`num13_logN` (`log N ≤ 0.001·h·pT`) with `pT ≤ 11.75rD ≤ 16rD`. -/
theorem num_card_AuxIdx {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) :
    Real.log ↑(Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)))
      ≤ 0.001 * acS K r b v * acD K σ / (dK K : ℝ) := by
  classical
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := by
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos (R := ℚ) (M := K)
    have : 0 < dK K := hpos
    omega
  have hh : 19 ≤ acH K b v := (acH_lower H).1
  have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  -- BW (11) with the parameters `h = acH K b v`, `d = dK K`.
  have hlog := num13_logN (r := r) (d := dK K) (h := acH K b v) hr hd hh σ hσ
  -- `N = h(D₀+1)∏_j(D_j+1)`, with `h = acH K b v`, `D₀ = pD0 …`, `D_j = pDj …`.
  have hcast : ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ)
      = (acH K b v : ℝ) * (pD0 r (dK K) σ + 1)
        * ∏ j : Fin r, ((pDj r (dK K) σ j : ℝ) + 1) := by
    rw [card_auxIdx]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_prod]
  rw [hcast]
  exact le_trans hlog (num_card_AuxIdx_arith hr hd σ hσ)

end Work.BW
