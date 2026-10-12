import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The function part of the symmetrisation average

`symAvgAmb N p` is the average `(N!)⁻¹ • ∑_σ permAmb N σ p` of the permutation
orbit of `p` in the ambient space `Amb N`.  Its first component is the average
of the first components of the permuted points, and the coercion of that `L²`
element to a function is, almost everywhere, the symmetrisation average
`symAvg f` of the function part `f` of `p`.

The proof is a chain of almost-everywhere equalities: the coercion of a scalar
multiple (`Lp.coeFn_smul`), the coercion of a finite sum
(`Lp.coeFn_fun_finsetSum`), and the coercion of each permuted `L²` element
(`permLp_coeFn`), combined with the help of a finite-sum rule for `=ᵐ`.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter

/-- Almost-everywhere equality is stable under finite pointwise sums. -/
private lemma eventuallyEq_finsetSum_ae {α ι β : Type*} [MeasurableSpace α] [AddCommMonoid β]
    {μ : Measure α} {s : Finset ι} {f g : ι → α → β} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (∑ i ∈ s, f i) =ᵐ[μ] (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem symAvgAmb_fst {N : ℕ} (p : Amb N) :
    AEEq N ((symAvgAmb N p).1 : Conf N → ℝ) (symAvgF N (fun y => (p.1 : Conf N → ℝ) y)) := by
  rw [AEEq]
  have h1 : (symAvgAmb N p).1 =
      (Nat.factorial N : ℝ)⁻¹ • (∑ σ : Equiv.Perm (Fin N), permLp N σ p.1) := by
    simp only [symAvgAmb, Prod.smul_fst, Prod.fst_sum, permAmb_fst]
  have hAB : ⇑((symAvgAmb N p).1) =ᵐ[volC N]
      (fun _ : Conf N => (Nat.factorial N : ℝ)⁻¹) •
        ⇑(∑ σ : Equiv.Perm (Fin N), permLp N σ p.1) := by
    rw [h1]
    exact Lp.coeFn_smul (Nat.factorial N : ℝ)⁻¹
      (∑ σ : Equiv.Perm (Fin N), permLp N σ p.1)
  have hB' : ⇑(∑ σ : Equiv.Perm (Fin N), permLp N σ p.1) =ᵐ[volC N]
      fun x => ∑ σ : Equiv.Perm (Fin N), ⇑p.1 (tauPerm N σ x) := by
    refine (Lp.coeFn_fun_finsetSum Finset.univ
      (fun σ : Equiv.Perm (Fin N) => permLp N σ p.1)).trans ?_
    filter_upwards [eventuallyEq_finsetSum_ae (μ := volC N) (s := Finset.univ)
      (f := fun σ : Equiv.Perm (Fin N) => fun x => ⇑(permLp N σ p.1) x)
      (g := fun σ : Equiv.Perm (Fin N) => fun x => ⇑p.1 (tauPerm N σ x))
      (fun σ _ => permLp_coeFn σ p.1)] with x hx
    simpa using hx
  have hBC : (fun _ : Conf N => (Nat.factorial N : ℝ)⁻¹) •
        ⇑(∑ σ : Equiv.Perm (Fin N), permLp N σ p.1) =ᵐ[volC N]
      (fun _ : Conf N => (Nat.factorial N : ℝ)⁻¹) •
        (fun x => ∑ σ : Equiv.Perm (Fin N), ⇑p.1 (tauPerm N σ x)) :=
    (EventuallyEq.refl (ae (volC N)) (fun _ : Conf N => (Nat.factorial N : ℝ)⁻¹)).smul hB'
  have hCD : (fun _ : Conf N => (Nat.factorial N : ℝ)⁻¹) •
        (fun x => ∑ σ : Equiv.Perm (Fin N), ⇑p.1 (tauPerm N σ x))
      = fun x => (Nat.factorial N : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ⇑p.1 (tauPerm N σ x) := by
    funext x
    simp [smul_eq_mul]
  have hcoef : ⇑((symAvgAmb N p).1) =ᵐ[volC N]
      fun x => (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin N), ⇑p.1 (tauPerm N σ x) :=
    hAB.trans (hBC.trans (EventuallyEq.of_eq hCD))
  refine hcoef.trans ?_
  apply EventuallyEq.of_eq
  funext x
  simp only [symAvgF, Submission.BoseGases.symAvg, one_div]
  rfl

end Work.BoseSym.Perm
