import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Perm.permAmb_mem_Hsub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the symmetrisation average

`symAvgAmb N p = (N!)⁻¹ • ∑_σ permAmb N σ p` is the average of the permutation
orbit of `p` in the ambient space `Amb N = L²(Conf N) × ∏_j L²(Conf N)`.

It is a constant multiple of a finite sum of the maps `permAmb N σ`, and each of
those is continuous: by `permAmbCLM_apply`, the underlying function of
`permAmb N σ` is the underlying function of the continuous linear map
`permAmbCLM N σ`, so `Continuous.congr` transfers continuity.  A finite sum of
continuous maps (`continuous_finsetSum`) and a scalar multiple of a continuous
map (`Continuous.const_smul`) are continuous.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter

/-- The particle permutation acts continuously on the ambient space. -/
private lemma continuous_permAmb_amb {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (permAmb N σ) :=
  (permAmbCLM N σ).continuous.congr fun p => permAmbCLM_apply σ p

theorem continuous_symAvgAmb (N : ℕ) : Continuous (symAvgAmb N) := by
  have hfun : symAvgAmb N = fun p : Amb N =>
      (Nat.factorial N : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permAmb N σ p := rfl
  rw [hfun]
  exact (continuous_finsetSum Finset.univ fun σ _ => continuous_permAmb_amb σ).const_smul
    ((Nat.factorial N : ℝ)⁻¹)

end Work.BoseSym.Perm
