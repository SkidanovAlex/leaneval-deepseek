import Mathlib
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.B3.scoeff_smul_of_support
import Submission.Work.Diff.STE.B3.abs_scoeff_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite sums of `scoeff`

`Work.Diff.STE.B3.scoeff n ρ ε f q` is the coefficient of the mode `q = (m, σ)` in the Friedrichs
truncation of the periodisation of `f` (see `J_finite_rank.lean`).  Its two linearity properties
for functions supported in the half-open cube `(-1/2, 1/2]^n` are
`Work.Diff.STE.B3.scoeff_add_of_support` and `Work.Diff.STE.B3.scoeff_smul_of_support`.

The present file combines them into the finite-sum statement used by the Galerkin scheme: for
continuous `U i` whose supports all lie in the half-open cube,

  `scoeff n ρ ε (∑ i ∈ s, d i • U i) q = ∑ i ∈ s, d i * scoeff n ρ ε (U i) q`.

The proof is an induction on `s`; the only auxiliary facts needed are the stability of the
hypotheses under the induction step, namely that
`∑ i ∈ s, d i • U i` is again continuous and again supported in the cube — and these are immediate,
the support of a finite sum being contained in the union of the supports.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3

variable {n : ℕ} {ι : Type*}

/-- A finite sum of functions supported in `C` (a set of points of `Fin n → ℝ`) is supported in
`C`: a non-zero value of the sum forces one of the summands to be non-zero. -/
private lemma support_finset_sum_smul_subset {C : Set (Fin n → ℝ)}
    (t : Finset ι) (d : ι → ℝ) (U : ι → (Fin n → ℝ) → ℝ)
    (hU : ∀ i ∈ t, Function.support (U i) ⊆ C) :
    Function.support (∑ i ∈ t, d i • U i) ⊆ C := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxc
  refine hx ?_
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have hzi : U i x = 0 := by
    by_contra hne
    exact hxc (hU i hi hne)
  simp [Pi.smul_apply, hzi]

/-- A constant multiple of a function supported in `C` is supported in `C`. -/
private lemma support_const_smul_subset {C : Set (Fin n → ℝ)} (c : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : Function.support f ⊆ C) :
    Function.support (c • f) ⊆ C := by
  intro x hx
  refine hf ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  exact hx (by simp [Pi.smul_apply, hfx])

/-- A finite sum of continuous functions is continuous. -/
private lemma continuous_finset_sum_smul (t : Finset ι) (d : ι → ℝ)
    (U : ι → (Fin n → ℝ) → ℝ) (hU : ∀ i ∈ t, Continuous (U i)) :
    Continuous (∑ i ∈ t, d i • U i) := by
  have h : Continuous (fun a : Fin n → ℝ => ∑ i ∈ t, (d i • U i) a) :=
    continuous_finsetSum t fun i hi => (hU i hi).const_smul (d i)
  have heq : (fun a : Fin n → ℝ => ∑ i ∈ t, (d i • U i) a) = (∑ i ∈ t, d i • U i) :=
    funext fun a => (Finset.sum_apply a t fun i => d i • U i).symm
  rwa [heq] at h

/-- The `scoeff` functional is additive over finite linear combinations of functions supported in
the half-open cube; the hypotheses on `U` are `Continuous` and support inside the cube. -/
private lemma scoeff_finset_sum_smul_aux {ρ : (Fin n → ℝ) → ℝ} {ε : ℝ} {q : QIdx n ε}
    (d : ι → ℝ) (U : ι → (Fin n → ℝ) → ℝ) (t : Finset ι)
    (hUc : ∀ i ∈ t, Continuous (U i))
    (hUs : ∀ i ∈ t, Function.support (U i) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    scoeff n ρ ε (∑ i ∈ t, d i • U i) q
      = ∑ i ∈ t, d i * scoeff n ρ ε (U i) q := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hz : scoeff n ρ ε (0 : (Fin n → ℝ) → ℝ) q = 0 := by
        have h := scoeff_smul_of_support ρ ε (0 : ℝ) (fun _ : Fin n → ℝ => (0 : ℝ))
          continuous_const (by simp) q
        simpa using h
      simpa using hz
  | insert a t' ha ih =>
      have hsum : (∑ i ∈ insert a t', d i • U i) = d a • U a + ∑ i ∈ t', d i • U i :=
        Finset.sum_insert ha
      have hca : Continuous (U a) := hUc a (Finset.mem_insert_self a t')
      have hsa : Function.support (U a) ⊆
          Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
        hUs a (Finset.mem_insert_self a t')
      have hct : Continuous (∑ i ∈ t', d i • U i) :=
        continuous_finset_sum_smul t' d U fun i hi => hUc i (Finset.mem_insert_of_mem hi)
      have hst : Function.support (∑ i ∈ t', d i • U i) ⊆
          Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
        support_finset_sum_smul_subset t' d U fun i hi =>
          hUs i (Finset.mem_insert_of_mem hi)
      have ih' : scoeff n ρ ε (∑ i ∈ t', d i • U i) q
          = ∑ i ∈ t', d i * scoeff n ρ ε (U i) q :=
        ih (fun i hi => hUc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hUs i (Finset.mem_insert_of_mem hi))
      rw [hsum]
      rw [scoeff_add_of_support ρ ε (d a • U a) (∑ i ∈ t', d i • U i)
        (hca.const_smul (d a)) hct
        (support_const_smul_subset (d a) (U a) hsa) hst q]
      rw [scoeff_smul_of_support ρ ε (d a) (U a) hca hsa q, ih']
      exact (Finset.sum_insert (s := t') (a := a)
        (f := fun i => d i * scoeff n ρ ε (U i) q) ha).symm

theorem scoeff_finset_sum_smul
    {n : ℕ} {ι : Type*} (s : Finset ι) (ρ : (Fin n → ℝ) → ℝ) (ε : ℝ) (q : Work.Diff.STE.B3.QIdx n ε)
    (d : ι → ℝ) (U : ι → (Fin n → ℝ) → ℝ)
    (hUc : ∀ i ∈ s, Continuous (U i))
    (hUs : ∀ i ∈ s, Function.support (U i) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :
    Work.Diff.STE.B3.scoeff n ρ ε (∑ i ∈ s, d i • U i) q
      = ∑ i ∈ s, d i * Work.Diff.STE.B3.scoeff n ρ ε (U i) q :=
  scoeff_finset_sum_smul_aux d U s hUc hUs

end Work.Diff.STE.B3
