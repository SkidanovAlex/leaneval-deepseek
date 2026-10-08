import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `N_G(Q) = H` in the rank-one set-up

Feit's §3 computations (18) and (20) use the normaliser of the Frobenius kernel: in his notation
`N(M) = Q ⋊ D`, i.e. in the rank-one set-up `N_G(Q) = H` (of order `|Q|·|D|`).  The proof is the
base-point argument: if `g ∈ N_G(Q)` and `g ∉ H`, then for every `q ∈ Q` the conjugate
`g q g⁻¹ ∈ Q` fixes both `∞` and `g · ∞ ≠ ∞`, while a non-identity element of `Q` fixes only
`∞`; hence `g q g⁻¹ = 1` for all `q ∈ Q`, i.e. `Q = ⊥`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- In the split rank-one set-up with `Q ≠ ⊥`, the normaliser of `Q` is `H = Q ⋊ D`: this is
Feit's `N(M) = M ⋊ D` (`|N(M)| = qm`, Lemma 3.1), and it is what turns `Ind_Q^{N(Q)}` into
`Ind_Q^H` in Corollary 2.4 and display (18). -/
theorem normalizer_Q_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hQ : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) = H := by
  refine le_antisymm ?_ h.normal
  intro g hg
  by_contra hgH
  have hω : g • IsTIQ.basePt H ≠ IsTIQ.basePt H := by
    rw [IsTIQ.smul_basePt]
    exact (IsTIQ.basePt_ne_iff H g).mpr hgH
  have hbot : Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    have hginv : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hg
    have hq' : g * q * g⁻¹ ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff''.mp hginv q).mp hq
    have hfix : (g * q * g⁻¹) • (g • IsTIQ.basePt H) = g • IsTIQ.basePt H := by
      rw [← mul_smul, show (g * q * g⁻¹) * g = g * q by group, mul_smul,
        IsTIQ.smul_basePt_of_mem H (h.le hq)]
    have hone : g * q * g⁻¹ = 1 := IsTIQ.Q_smul_eq_self h hq' hfix hω
    calc q = g⁻¹ * 1 * g := by rw [← hone]; group
      _ = 1 := by group
  exact hQ hbot

end Work.ZassenhausTwoGroup
