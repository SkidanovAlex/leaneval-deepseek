import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Reed.Prob.Expectation
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint

/-!
# The oscillation of a slice expectation

If changing the `j`-th coordinate of a point of a product of finite probability
spaces changes the value of `Z` by at most `D`, then the expectations of `Z`
under the two product measures obtained by freezing the `j`-th coordinate at
two different values differ by at most `D`.  This is the "slice oscillation"
estimate used in the proof of the bounded-differences (Azuma--Hoeffding)
inequality for product measures.

The auxiliary `prodWeight` is the total weight that a product measure gives to
the coordinates other than `j`; it is unchanged when the `j`-th coordinate is
changed.
-/

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-- The weight that a product of finite probability spaces assigns to the
coordinates other than `j`. -/
private noncomputable def prodWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (f : ∀ i, Ω i) : ℝ :=
  ∏ i ∈ Finset.univ.erase j, (ν i).wt (f i)

private lemma prodWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (f : ∀ i, Ω i) : 0 ≤ prodWeight ν j f :=
  Finset.prod_nonneg fun i _ => (ν i).wt_nonneg (f i)

/-- Changing the `j`-th coordinate does not change `prodWeight`. -/
private lemma prodWeight_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (f : ∀ i, Ω i) (y : Ω j) :
    prodWeight ν j (Function.update f j y) = prodWeight ν j f := by
  simp only [prodWeight]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- **Slice oscillation for a product measure.**  If changing the `j`-th coordinate changes `Z`
by at most `D`, in the sense that `|Z (Function.update f j x) - Z f| ≤ D` for every `f` and `x`,
then the expectations of `Z` under the two slices of the product measure obtained by freezing
the `j`-th coordinate at `x` respectively at `x'` differ by at most `D`.

Proof sketch.  Write `P f := ∏ i ∈ Finset.univ.erase j, (ν i).wt (f i)`, so that
`(pi (freeze ν j x)).wt f = P f * (point x).wt (f j)` (`FinProb.pi_freeze_wt`) and
`(point x).wt y = Set.indicator {x} (fun _ => 1) y`.  Hence, splitting the sum with
`Finset.sum_filter`,
  `(pi (freeze ν j x)).exp Z = ∑ f ∈ Finset.univ.filter (fun f => f j = x), P f * Z f =: A x`.
Note `P` is unchanged by `Function.update f j y` (every factor has `i ≠ j`,
`Function.update_of_ne`).  The map `φ : f ↦ Function.update f j x` is a bijection from the
`x'`-slice onto the `x`-slice, with inverse `g ↦ Function.update g j x'`
(`Function.update_idem`, `Function.update_eq_self`), and it preserves `P`; hence
`A x = ∑ f ∈ Finset.univ.filter (fun f => f j = x'), P f * Z (Function.update f j x)`
(`Finset.sum_nbij'`).  Subtracting `A x'` gives
`A x - A x' = ∑ f ∈ filter (fun f => f j = x'), P f * (Z (Function.update f j x) - Z f)`,
whose absolute value is at most `D * (∑ f ∈ filter (fun f => f j = x'), P f) = D * 1 = D`:
bound the sum by `Finset.abs_sum_le_sum_abs` and `Finset.sum_le_sum`, where
`Z (Function.update f j x) - Z f = Z (Function.update (Function.update f j x') j x)
- Z (Function.update f j x')` because `Function.update_idem` and `f j = x'`, so it is at most
`D` by hypothesis and `P f ≥ 0`; and the total mass is `1` because `A x'` applied to the
constant function `1` equals `1` by `FinProb.exp_const`. -/
lemma abs_exp_freeze_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (Z : (∀ i, Ω i) → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ (f : ∀ i, Ω i) (x : Ω j), |Z (Function.update f j x) - Z f| ≤ D) (x x' : Ω j) :
    |(Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j x)).exp Z
      - (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j x')).exp Z| ≤ D := by
  classical
  have _hD := hD -- the hypothesis `0 ≤ D` is not needed for the estimate
  -- ## The expectation of a frozen measure is the weighted sum over the slice
  have key : ∀ (y : Ω j) (W : (∀ i, Ω i) → ℝ),
      (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j y)).exp W
        = ∑ f ∈ Finset.univ.filter (fun f => f j = y), prodWeight ν j f * W f := by
    intro y W
    have h2 : (∑ f ∈ Finset.univ.filter (fun f => f j = y), prodWeight ν j f * W f)
        = ∑ f, if f j = y then prodWeight ν j f * W f else 0 :=
      Finset.sum_filter (fun f => f j = y) (fun f => prodWeight ν j f * W f)
    rw [Work.Deep.Reed.FinProb.exp, h2]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Work.Deep.Reed.FinProb.pi_freeze_wt]
    by_cases hfj : f j = y
    · rw [if_pos hfj, Work.Deep.Reed.FinProb.point_wt_of_eq hfj, mul_one]
      rfl
    · rw [if_neg hfj, Work.Deep.Reed.FinProb.point_wt_of_ne hfj, mul_zero, zero_mul]
  -- ## The slice `{f | f j = x'}` carries total weight one
  have hmass : ∑ f ∈ Finset.univ.filter (fun f => f j = x'), prodWeight ν j f = 1 := by
    have h1 : (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j x')).exp
        (fun _ => (1 : ℝ)) = 1 := Work.Deep.Reed.FinProb.exp_const _ _
    rw [key x' (fun _ => (1 : ℝ))] at h1
    simpa using h1
  -- ## Reindexing the `x`-slice by the `x'`-slice
  have hbij : ∑ f ∈ Finset.univ.filter (fun f => f j = x'),
      prodWeight ν j f * Z (Function.update f j x)
      = ∑ f ∈ Finset.univ.filter (fun f => f j = x), prodWeight ν j f * Z f := by
    have h1 : ∀ f ∈ Finset.univ.filter (fun f => f j = x'),
        Function.update f j x ∈ Finset.univ.filter (fun g => g j = x) := fun f _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.update_self j x f⟩
    have h2 : ∀ g ∈ Finset.univ.filter (fun g => g j = x),
        Function.update g j x' ∈ Finset.univ.filter (fun f => f j = x') := fun g _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.update_self j x' g⟩
    have h3 : ∀ f ∈ Finset.univ.filter (fun f => f j = x'),
        Function.update (Function.update f j x) j x' = f := by
      intro f hf
      have hf' : f j = x' := (Finset.mem_filter.mp hf).2
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr hf'.symm
    have h4 : ∀ g ∈ Finset.univ.filter (fun g => g j = x),
        Function.update (Function.update g j x') j x = g := by
      intro g hg
      have hg' : g j = x := (Finset.mem_filter.mp hg).2
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr hg'.symm
    have h5 : ∀ f ∈ Finset.univ.filter (fun f => f j = x'),
        prodWeight ν j f * Z (Function.update f j x)
          = prodWeight ν j (Function.update f j x) * Z (Function.update f j x) := fun f _ =>
      by rw [prodWeight_update]
    exact Finset.sum_nbij' (fun f => Function.update f j x) (fun g => Function.update g j x')
      h1 h2 h3 h4 h5
  -- ## The difference of the two expectations, written over the `x'`-slice
  rw [show (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j x)).exp Z
      - (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze ν j x')).exp Z
      = ∑ f ∈ Finset.univ.filter (fun f => f j = x'),
          prodWeight ν j f * (Z (Function.update f j x) - Z f) from by
      rw [key x Z, key x' Z, ← hbij, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun f _ => by ring]
  -- ## Bound the sum termwise
  calc |∑ f ∈ Finset.univ.filter (fun f => f j = x'),
          prodWeight ν j f * (Z (Function.update f j x) - Z f)|
      ≤ ∑ f ∈ Finset.univ.filter (fun f => f j = x'),
          |prodWeight ν j f * (Z (Function.update f j x) - Z f)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ Finset.univ.filter (fun f => f j = x'), prodWeight ν j f * D := by
        refine Finset.sum_le_sum fun f hf => ?_
        have hfj : f j = x' := (Finset.mem_filter.mp hf).2
        have hf0 : Function.update f j x' = f :=
          Function.update_eq_self_iff.mpr hfj.symm
        have hZf : |Z (Function.update f j x) - Z f| ≤ D := by
          have h := hZ (Function.update f j x') x
          rwa [Function.update_idem, hf0] at h
        calc |prodWeight ν j f * (Z (Function.update f j x) - Z f)|
            = prodWeight ν j f * |Z (Function.update f j x) - Z f| := by
              rw [abs_mul, abs_of_nonneg (prodWeight_nonneg ν j f)]
          _ ≤ prodWeight ν j f * D :=
              mul_le_mul_of_nonneg_left hZf (prodWeight_nonneg ν j f)
    _ = D := by
        have h3 : (∑ f ∈ Finset.univ.filter (fun f => f j = x'), prodWeight ν j f) * D
            = ∑ f ∈ Finset.univ.filter (fun f => f j = x'), prodWeight ν j f * D :=
          Finset.sum_mul _ _ _
        rw [← h3, hmass, one_mul]

end Work.Deep.Reed.Prob
