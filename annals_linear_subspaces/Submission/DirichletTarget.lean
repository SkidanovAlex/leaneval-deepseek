import ChallengeDeps
import Submission.Helpers
import Submission.Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal

open LinearSubspaces
open ENNReal Real Module exteriorPower InnerProductGeometry
open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

namespace Submission

/-- Interface lemma for the first conjunct of `theorem_1`: the uniform lower bound
`β_k(x) ≥ d / (k * (d - l))` follows from the Dirichlet-type statement that for every
`0 < β < d / (k * (d - l))` (real arithmetic) and every `c > 0` there exists a rational
`k`-subspace `v` with `distSubspaces v x < c · H(v)^(-β)`. -/
lemma lower_bound_of_dirichlet
    {d : ℕ} (hd : 2 ≤ d) {l k : ℕ} (hl0 : 0 < l) (hld : l < d) (hk1 : 1 ≤ k) (hkl : k ≤ l)
    (hDir : ∀ (x : Submodule ℝ ℝᵈ) (hx : finrank ℝ x = l) (β : ℝ) (hβ : 0 < β),
      β < (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) → ∀ c : ℝ, 0 < c →
        ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v, finrank ℝ v = k ∧
          distSubspaces v x < c * height v hv ^ (-β)) :
    ∀ (x : Submodule ℝ ℝᵈ), finrank ℝ x = l →
      diophantineExponent k x ≥ (d : ℝ≥0∞) / (k * (d - l)) := by
  intro x hx
  refine Helpers.diophantineExponent_ge_of_forall_mem k x ((d : ℝ≥0∞) / (k * (d - l))) ?_
  intro β hβ0 hcond
  rcases hcond with ⟨c0, hc0, hcondAll⟩
  -- if `β` satisfied the defining condition of the exponent and were `< D`, the Dirichlet
  -- hypothesis would supply a rational k-plane closer than the uniform separation allows:
  have hDleβ : (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) ≤ β := by
    by_contra hb
    have hβD : β < (d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ))) := lt_of_not_ge hb
    obtain ⟨v, hv, hfv, hdist⟩ := hDir x hx β hβ0 hβD c0 hc0
    exact (not_lt_of_ge (hcondAll v hfv hv)) hdist
  -- bridge the ENNReal expression `d / (k * (d - l))` (whose denominator elaborates with
  -- ENNReal truncated subtraction) to `ofReal` of the real constant `d / (k·(d−l))`:
  have hfrac : (d : ℝ≥0∞) / (k * (d - l)) =
      ENNReal.ofReal ((d : ℝ) / ((k : ℝ) * ((d : ℝ) - (l : ℝ)))) := by
    simpa using
      (Commons.Analysis.ENNReal.natCast_div_natCast_sub_mul_ofReal (d := d) (l := l) (k := k)
        (hld := hld) (hk := hk1))
  rw [hfrac]
  exact ENNReal.ofReal_le_ofReal hDleβ

end Submission
