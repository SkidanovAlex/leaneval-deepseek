import Mathlib
import Submission.Work.HP.PFDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.HP2.Phi_continuous

set_option autoImplicit false

noncomputable section

namespace Work.HP.HP2

/-- The cone region `coneRegion d n a α T = {x : ‖x‖ ≤ T, toR a ∈ Cgam (veronese d n x) α}` is
closed.  (It is the intersection of the closed ball `{rNorm x ≤ T}` with the preimage under the
continuous map `x ↦ (dotR (veronese d n x) (toR a), rNorm (veronese d n x))` of the closed set
`{(u,v) : |u| ≤ v * ‖a‖ / (2α)}`.) -/
lemma isClosed_coneRegion (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (α T : ℝ) :
    IsClosed (Work.HP.coneRegion d n a α T) := by
  have hball : IsClosed {x : Fin (n + 1) → ℝ | rNorm x ≤ T} :=
    isClosed_le (continuous_rNorm_pi (ι := Fin (n + 1))) continuous_const
  have hdot : Continuous (fun x : Fin (n + 1) → ℝ => dotR (veronese d n x) (toR a)) :=
    continuous_dotR_pair.comp ((continuous_veronese d n).prodMk continuous_const)
  have hcone : IsClosed {x : Fin (n + 1) → ℝ |
      |dotR (veronese d n x) (toR a)|
        ≤ rNorm (veronese d n x) * (rNorm (toR a) / (2 * α))} :=
    isClosed_le hdot.abs
      ((continuous_rNorm_pi.comp (continuous_veronese d n)).mul continuous_const)
  have heq : coneRegion d n a α T =
      {x : Fin (n + 1) → ℝ | rNorm x ≤ T} ∩
      {x : Fin (n + 1) → ℝ |
        |dotR (veronese d n x) (toR a)|
          ≤ rNorm (veronese d n x) * (rNorm (toR a) / (2 * α))} := by
    ext x
    simp only [coneRegion, Cgam, Set.mem_ofPred_eq, Set.mem_inter_iff, mul_div_assoc]
  rw [heq]
  exact hball.inter hcone

end Work.HP.HP2
