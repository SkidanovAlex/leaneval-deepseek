import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.DependsOn
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint

/-!
# Box probabilities for the uniform colouring measure

Under the uniform distribution on colourings `V → Fin C` (i.e. the product of
uniform measures on the coordinates), the probability that every vertex of a
finite set `S` receives a colour from a prescribed set `B x` is
`∏_{x ∈ S} |B x| / C`.  The coordinates are independent and uniform.

The proof factors through two structural facts about the finite product
measure `FinProb.pi`:

* `pi_prob_mem_apply` — the marginal of a single coordinate,
* `pi_prob_box_finset` — the probability of a box `{f | ∀ i ∈ s, f i ∈ A i}`
  is the product of the marginals (proved by induction on `s` using
  `pi_prob_inter_eq_mul_of_disjoint`),

together with the elementary computation `uniform_prob_mem` for the uniform
measure on a finite type.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

section ProductBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- In a product measure, the probability that the coordinate `j` lands in a
set `A` equals the `j`-th marginal's probability of `A`.  (Proved by
disintegrating at `j` and using that the event only depends on `j`.) -/
lemma pi_prob_mem_apply (μ : ∀ i, FinProb (Ω i)) (j : ι) (A : Set (Ω j)) :
    (FinProb.pi μ).prob {f : ∀ i, Ω i | f j ∈ A} = (μ j).prob A := by
  classical
  have key : ∀ x : Ω j, (FinProb.pi (FinProb.freeze μ j x)).prob {f : ∀ i, Ω i | f j ∈ A}
      = (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    by_cases h : x ∈ A
    · have hc : ∀ f : ∀ i, Ω i, f j = x →
          (f ∈ ({f : ∀ i, Ω i | f j ∈ A}) ↔ f ∈ (Set.univ : Set (∀ i, Ω i))) := by
        intro f hf
        have hfj : f j ∈ A := by rw [hf]; exact h
        simp [hfj]
      rw [FinProb.freeze_prob_congr μ j x hc, FinProb.prob_univ]
      simp [h]
    · have hc : ∀ f : ∀ i, Ω i, f j = x →
          (f ∈ ({f : ∀ i, Ω i | f j ∈ A}) ↔ f ∈ (∅ : Set (∀ i, Ω i))) := by
        intro f hf
        have hfj : f j ∉ A := by rw [hf]; exact h
        simp [hfj]
      rw [FinProb.freeze_prob_congr μ j x hc, FinProb.prob_empty]
      simp [h]
  calc (FinProb.pi μ).prob {f : ∀ i, Ω i | f j ∈ A}
      = ∑ x : Ω j,
          (μ j).wt x * (FinProb.pi (FinProb.freeze μ j x)).prob {f : ∀ i, Ω i | f j ∈ A} :=
        FinProb.freeze_sum μ j {f : ∀ i, Ω i | f j ∈ A}
    _ = ∑ x : Ω j, (μ j).wt x * (if x ∈ A then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [key x]
    _ = ∑ x : Ω j, (if x ∈ A then (μ j).wt x else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : x ∈ A <;> simp [h]
    _ = (μ j).prob A := by
        rw [FinProb.prob]

/-- Marginal form of `pi_prob_mem_apply` for a `Finset` of values. -/
lemma pi_prob_mem_finset (μ : ∀ i, FinProb (Ω i)) (j : ι) (t : Finset (Ω j)) :
    (FinProb.pi μ).prob {f : ∀ i, Ω i | f j ∈ t} = (μ j).prob {c : Ω j | c ∈ t} := by
  have h : {f : ∀ i, Ω i | f j ∈ t} = {f : ∀ i, Ω i | f j ∈ {c : Ω j | c ∈ t}} := by
    ext f; simp
  rw [h, pi_prob_mem_apply μ j {c : Ω j | c ∈ t}]

/-- **Box probabilities in a product measure**: the probability that the
coordinates in a finite set `s` land in prescribed sets is the product of the
marginals.  (Induction on `s`, using `pi_prob_inter_eq_mul_of_disjoint` for the
independence of distinct coordinates.) -/
lemma pi_prob_box_finset (μ : ∀ i, FinProb (Ω i)) (s : Finset ι) (A : ∀ i, Finset (Ω i)) :
    (FinProb.pi μ).prob {f : ∀ i, Ω i | ∀ i ∈ s, f i ∈ A i}
      = ∏ i ∈ s, (μ i).prob {c : Ω i | c ∈ A i} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hset : {f : ∀ i, Ω i | ∀ i ∈ (∅ : Finset ι), f i ∈ A i} = Set.univ := by
        ext f
        change (∀ i ∈ (∅ : Finset ι), f i ∈ A i) ↔ True
        simp
      rw [hset, FinProb.prob_univ, Finset.prod_empty]
  | insert j s hj ih =>
      have hset : {f : ∀ i, Ω i | ∀ i ∈ insert j s, f i ∈ A i}
          = {c : ∀ i, Ω i | c j ∈ A j} ∩ {c : ∀ i, Ω i | ∀ i ∈ s, c i ∈ A i} := by
        ext f
        change (∀ i ∈ insert j s, f i ∈ A i) ↔ (f j ∈ A j ∧ ∀ i ∈ s, f i ∈ A i)
        constructor
        · intro h
          exact ⟨h j (Finset.mem_insert.mpr (Or.inl rfl)),
            fun i hi => h i (Finset.mem_insert.mpr (Or.inr hi))⟩
        · rintro ⟨hj', hs⟩ i hi
          rcases Finset.mem_insert.mp hi with rfl | hi'
          · exact hj'
          · exact hs i hi'
      have hdisj : Disjoint ({j} : Finset ι) s := Finset.disjoint_singleton_left.mpr hj
      have hdep1 : DependsOn ({j} : Finset ι) {c : ∀ i, Ω i | c j ∈ A j} := by
        intro f g hfg
        change (f j ∈ A j) ↔ (g j ∈ A j)
        rw [hfg j (Finset.mem_singleton.mpr rfl)]
      have hdep2 : DependsOn s {c : ∀ i, Ω i | ∀ i ∈ s, c i ∈ A i} := by
        intro f g hfg
        change (∀ i ∈ s, f i ∈ A i) ↔ (∀ i ∈ s, g i ∈ A i)
        constructor
        · intro h i hi; rw [← hfg i hi]; exact h i hi
        · intro h i hi; rw [hfg i hi]; exact h i hi
      rw [hset, pi_prob_inter_eq_mul_of_disjoint μ hdisj hdep1 hdep2,
        pi_prob_mem_finset μ j (A j), ih, Finset.prod_insert hj]

end ProductBox

section UniformBox

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Probability that a uniform point of a finite type lies in a finite set. -/
lemma uniform_prob_mem (t : Finset Ω) :
    (FinProb.uniform Ω).prob {c : Ω | c ∈ t} = ((t.card : ℝ)) / (Fintype.card Ω) := by
  classical
  rw [FinProb.prob]
  trans (∑ ω : Ω, (if ω ∈ t then ((Fintype.card Ω : ℝ))⁻¹ else 0))
  · refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω ∈ t <;> simp [h, FinProb.uniform]
  · have hsub : ∑ ω : Ω, (if ω ∈ t then ((Fintype.card Ω : ℝ))⁻¹ else 0)
        = ((t.card : ℝ)) * ((Fintype.card Ω : ℝ))⁻¹ := by
      have hf : ∀ c ∈ (Finset.univ : Finset Ω), c ∉ t →
          (if c ∈ t then ((Fintype.card Ω : ℝ))⁻¹ else 0) = 0 := by
        intro c _ hct; simp [hct]
      calc ∑ ω : Ω, (if ω ∈ t then ((Fintype.card Ω : ℝ))⁻¹ else 0)
          = ∑ c ∈ t, (if c ∈ t then ((Fintype.card Ω : ℝ))⁻¹ else 0) :=
            (Finset.sum_subset (Finset.subset_univ t) hf).symm
        _ = ∑ c ∈ t, ((Fintype.card Ω : ℝ))⁻¹ := by
            refine Finset.sum_congr rfl fun c hc => ?_
            simp [hc]
        _ = ((t.card : ℝ)) * ((Fintype.card Ω : ℝ))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsub, div_eq_mul_inv]

end UniformBox

/-- **Box probabilities for the uniform colouring measure**: under the uniform
distribution on colourings `V → Fin C`, the probability that every vertex of a
finite set `S` receives a colour from a prescribed set `B x` is the product
`∏_{x ∈ S} |B x| / C` (the coordinates are independent and uniform). -/
theorem pi_uniform_prob_box {V : Type*} [Fintype V] [DecidableEq V] {C : ℕ} [Nonempty (Fin C)]
    (S : Finset V) (B : V → Finset (Fin C)) :
    (FinProb.pi (fun _ : V => FinProb.uniform (Fin C))).prob
      {f : V → Fin C | ∀ x ∈ S, f x ∈ B x}
      = ∏ x ∈ S, ((B x).card : ℝ) / C := by
  calc (FinProb.pi (fun _ : V => FinProb.uniform (Fin C))).prob
        {f : V → Fin C | ∀ x ∈ S, f x ∈ B x}
      = ∏ x ∈ S, (FinProb.uniform (Fin C)).prob {c : Fin C | c ∈ B x} :=
        pi_prob_box_finset (fun _ : V => FinProb.uniform (Fin C)) S B
    _ = ∏ x ∈ S, ((B x).card : ℝ) / (Fintype.card (Fin C)) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        exact uniform_prob_mem (B x)
    _ = ∏ x ∈ S, ((B x).card : ℝ) / C := by rw [Fintype.card_fin]

end Work.Deep.Reed.Prob
