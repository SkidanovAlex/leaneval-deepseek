import Mathlib
import Submission.Work.SSGRoute.PTembedding.CoindTransfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTembedding

/-!
# `Γ`-equivariance of the coind trace `coindTrace : Coind_S^Γ M →+ M`

For a subgroup `S ≤ Γ` of finite index and a `Γ`-module `M`, the trace
`coindTrace S f = ∑_{q ∈ Γ/S} t_q • f t_q` (with `t_q = Quotient.out q` a representative of the
left coset `q`) is a map of `Γ`-modules: `coindTrace (γ • f) = γ • coindTrace f`.

The proof is the standard reindexing of the coset sum.  Along a permutation `γ • ·` of `Γ ⧸ S`
the summand `q ↦ (out q) • f (γ⁻¹ * out q)` is invariant: for each coset `q` the element
`γ⁻¹ * out (γ • q)` is a representative of `q`, so by `coindTraceFun_summand_mk` the summand at
`γ • q` equals `(γ * out q) • f (out q)`, which is the corresponding summand of `γ • coindTrace f`.
-/

/-- **The summand identity behind the equivariance of the trace.**  For every coset `q`, the value
of the summand of `coindTrace (γ • f)` at the coset `γ • q` is the corresponding summand of
`γ • coindTrace f`. -/
theorem coindTrace_smul_aux {Γ : Type} [Group Γ] (S : Subgroup Γ) [Fintype (Γ ⧸ S)]
    {M : Type} [AddCommGroup M] [DistribMulAction Γ M]
    (g : Γ) (f : Work.SSGRoute.PT.Coind Γ S M) (q : Γ ⧸ S) :
    (Quotient.out (g • q)) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q))
      = (g * Quotient.out q) • (f : Γ → M) (Quotient.out q) := by
  -- `g⁻¹ * out (g • q)` is a representative of the coset `q`.
  have hmk : QuotientGroup.mk (g⁻¹ * Quotient.out (g • q)) = q := by
    rw [show QuotientGroup.mk (g⁻¹ * Quotient.out (g • q))
          = g⁻¹ • (QuotientGroup.mk (Quotient.out (g • q)) : Γ ⧸ S) from rfl]
    rw [QuotientGroup.out_eq', inv_smul_smul]
  -- ... so its summand equals the one at `out q`.
  have h2 : (Quotient.out q) • (f : Γ → M) (Quotient.out q)
      = (g⁻¹ * Quotient.out (g • q)) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q)) := by
    have hh := coindTraceFun_summand_mk S f (g⁻¹ * Quotient.out (g • q))
    rw [hmk] at hh
    exact hh
  calc (Quotient.out (g • q)) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q))
      = (g * (g⁻¹ * Quotient.out (g • q))) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q)) := by
        rw [mul_inv_cancel_left]
    _ = g • ((g⁻¹ * Quotient.out (g • q)) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q))) := by
        rw [mul_smul]
    _ = g • ((Quotient.out q) • (f : Γ → M) (Quotient.out q)) := by rw [← h2]
    _ = (g * Quotient.out q) • (f : Γ → M) (Quotient.out q) := by rw [← mul_smul]

/-- **The trace `Coind_S^Γ M →+ M` is `Γ`-equivariant.** -/
theorem coindTrace_equivariant {Γ : Type} [Group Γ] (S : Subgroup Γ) [Fintype (Γ ⧸ S)]
    {M : Type} [AddCommGroup M] [DistribMulAction Γ M] :
    Work.GroupCohomology.IsEquivariant Γ (Work.SSGRoute.PTembedding.coindTrace (M := M) S) := by
  intro g f
  rw [coindTrace_apply, coindTrace_apply]
  simp only [Work.SSGRoute.PT.Coind.smul_apply]
  rw [Finset.smul_sum]
  -- Reindex the left-hand sum along the permutation `q ↦ g • q` of `Γ ⧸ S`.
  have hA : (∑ q : Γ ⧸ S, (Quotient.out q) • (f : Γ → M) (g⁻¹ * Quotient.out q))
      = ∑ q : Γ ⧸ S, (Quotient.out (g • q)) • (f : Γ → M) (g⁻¹ * Quotient.out (g • q)) :=
    (Equiv.sum_comp (MulAction.toPerm g)
      (fun q : Γ ⧸ S => (Quotient.out q) • (f : Γ → M) (g⁻¹ * Quotient.out q))).symm
  rw [hA]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [coindTrace_smul_aux S g f q, mul_smul]

end Work.SSGRoute.PTembedding
