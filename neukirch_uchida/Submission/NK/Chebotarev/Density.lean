/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Basic
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_finite
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_density_zero
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_compl
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_primes_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_residueClass

/-!
# Density lemmas for Čebotarev

This module collects the Dirichlet-density API of the commons (additivity over disjoint unions,
insensitivity to finite sets, the completely split primes, Dirichlet's theorem) and adds the
elementary manipulation lemmas used in the reduction of Čebotarev's density theorem.
-/

open Filter IsDedekindDomain Set

namespace NK.Chebotarev

/-- Dirichlet density only depends on the set of primes. -/
theorem hasDirichletDensity_congr {K : Type*} [Field K] [NumberField K]
    {S T : Set (PrimeIdeal K)} {δ : ℝ} (h : S = T)
    (hS : NumberField.Set.HasDirichletDensity S δ) :
    NumberField.Set.HasDirichletDensity T δ := h ▸ hS

end NK.Chebotarev

namespace NK.Chebotarev

/-- **A set of primes of positive Dirichlet density is infinite.** -/
theorem infinite_of_hasDirichletDensity_pos {K : Type*} [Field K] [NumberField K]
    {S : Set (PrimeIdeal K)} {δ : ℝ} (hS : NumberField.Set.HasDirichletDensity S δ)
    (hδ : 0 < δ) : S.Infinite := by
  intro hfin
  have h0 : NumberField.Set.HasDirichletDensity S 0 :=
    Commons.NumberTheory.NumberField.Set.hasDirichletDensity_zero_of_finite hfin
  exact hδ.ne' (tendsto_nhds_unique hS h0)

end NK.Chebotarev
