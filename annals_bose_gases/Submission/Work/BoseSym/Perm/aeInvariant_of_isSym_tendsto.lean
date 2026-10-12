import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Perm.symAvgAmb_eq_of_isSym
import Submission.Work.BoseSym.Perm.symAvgAmb_fst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A limit of symmetric states is almost-everywhere permutation invariant

`IsSym N p` says that the ambient point `p` is fixed by the permutation action
`permAmb N σ` for every `σ : Equiv.Perm (Fin N)`.  We show that this property
passes to `L²` limits: if `(p n).1 ⇀ v` in `L²(Conf N)` and each `p n` is
symmetric, then `v` is almost everywhere invariant under every permutation of
the particles.

The route is:

* `permLp N σ` (the permutation action on `L²`) is an isometry, hence continuous;
  so `(p n).1 → v` implies `permLp N σ (p n).1 → permLp N σ v`.  But
  `permLp N σ (p n).1 = (permAmb N σ (p n)).1 = (p n).1` by symmetry, so
  uniqueness of limits gives `permLp N σ v = v`
  (`permLp_eq_of_tendsto`);
* transporting this equality to functions via the almost-everywhere formula for
  the coercion of `permLp` (`permLp_coeFn`) gives, for each `σ`,
  `v =ᵐ v ∘ tauPerm σ`; finitely many such equalities combine
  (`eventually_all`) into `v (tauPerm σ x) = v x` for all `σ` at once;
* the definition of the symmetrisation average `symAvgF N v`
  (`symAvg N f x = (1/N!) ∑_σ f (actPerm σ x)`) then makes the sum constant in
  `σ`, and `(1/N!) · N! = 1` finishes the proof.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter

/-- The permutation action `permLp N σ` on `L²` is an isometry, because it is
composition with the measure-preserving map `tauPerm N σ`. -/
private lemma isometry_permLp {N : ℕ} (σ : Equiv.Perm (Fin N)) : Isometry (permLp N σ) :=
  MeasureTheory.Lp.isometry_compMeasurePreserving (measurePreserving_tauPerm N σ)

/-- If every term of a convergent sequence in `L²` is fixed by `permLp N σ`, then
so is its limit. -/
private lemma permLp_eq_of_tendsto {N : ℕ} (σ : Equiv.Perm (Fin N)) {u : ℕ → L2 N} {v : L2 N}
    (hconv : Filter.Tendsto u Filter.atTop (nhds v)) (hfix : ∀ n, permLp N σ (u n) = u n) :
    permLp N σ v = v := by
  have ht : Filter.Tendsto (fun n => permLp N σ (u n)) Filter.atTop (nhds (permLp N σ v)) :=
    ((isometry_permLp σ).continuous.tendsto v).comp hconv
  rw [show (fun n => permLp N σ (u n)) = u from funext hfix] at ht
  exact tendsto_nhds_unique ht hconv

theorem aeInvariant_of_isSym_tendsto {N : ℕ} {p : ℕ → Work.BoseSym.Amb N} {v : Work.BoseSym.L2 N}
    (hp : ∀ n, Work.BoseSym.IsSym N (p n))
    (hconv : Filter.Tendsto (fun n => (p n).1) Filter.atTop (nhds v)) :
    Work.BoseSym.AEEq N (v : Work.BoseSym.Conf N → ℝ)
      (Work.BoseSym.symAvgF N (v : Work.BoseSym.Conf N → ℝ)) := by
  classical
  -- Step 1: every permutation fixes the limit `v`.
  have hfix : ∀ σ : Equiv.Perm (Fin N), permLp N σ v = v := by
    intro σ
    refine permLp_eq_of_tendsto σ hconv (fun n => ?_)
    exact congrArg Prod.fst (hp n σ)
  -- Step 2: transport to almost-everywhere equality of functions.
  have hσae : ∀ σ : Equiv.Perm (Fin N),
      (v : Conf N → ℝ) =ᵐ[volC N] fun x => (v : Conf N → ℝ) (tauPerm N σ x) := by
    intro σ
    have h := permLp_coeFn σ v
    rw [hfix σ] at h
    exact h
  have hall : ∀ᵐ x ∂(volC N), ∀ σ : Equiv.Perm (Fin N),
      (v : Conf N → ℝ) (tauPerm N σ x) = (v : Conf N → ℝ) x := by
    rw [eventually_all]
    intro σ
    filter_upwards [hσae σ] with x hx
    exact hx.symm
  -- Step 3: the symmetrisation average of an everywhere invariant function is
  -- that function.
  rw [AEEq, symAvgF]
  filter_upwards [hall] with x hx
  simp only [Submission.BoseGases.symAvg]
  have hsum : (∑ σ : Equiv.Perm (Fin N),
        (v : Conf N → ℝ) (Submission.BoseGases.actPerm N σ x))
      = ∑ σ : Equiv.Perm (Fin N), (v : Conf N → ℝ) x :=
    Finset.sum_congr rfl (fun σ _ => hx σ)
  rw [hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, smul_eq_mul, one_div]
  rw [inv_mul_cancel_left₀]
  exact_mod_cast Nat.factorial_ne_zero N

end Work.BoseSym.Perm
