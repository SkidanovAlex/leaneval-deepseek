import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Reed.Prob.Product

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The **point mass** at `x`: the finite probability space in which `x` has
weight `1` and every other point has weight `0`. -/
noncomputable def point (x : Ω) : FinProb Ω where
  wt := Set.indicator {x} (fun _ => (1 : ℝ))
  wt_nonneg := fun y => by
    classical
    rw [Set.indicator_apply]
    by_cases h : y ∈ ({x} : Set Ω) <;> simp [h]
  wt_sum := by
    classical
    rw [Finset.sum_eq_single x]
    · exact Set.indicator_of_mem (Set.mem_singleton x) _
    · intro b _ hb
      exact Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using hb) _
    · intro hx
      exact absurd (Finset.mem_univ x) hx

lemma point_wt (x : Ω) : (point x).wt = Set.indicator {x} (fun _ => (1 : ℝ)) := rfl

@[simp] lemma point_wt_apply (x y : Ω) :
    (point x).wt y = Set.indicator {x} (fun _ => (1 : ℝ)) y := rfl

lemma point_wt_of_eq {x y : Ω} (h : y = x) : (point x).wt y = 1 := by
  rw [point_wt_apply, Set.indicator_of_mem (by simpa [Set.mem_singleton_iff] using h)]

lemma point_wt_of_ne {x y : Ω} (h : y ≠ x) : (point x).wt y = 0 := by
  rw [point_wt_apply, Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using h)]

@[simp] lemma point_wt_self (x : Ω) : (point x).wt x = 1 := point_wt_of_eq rfl

/-- Summation identity for the point masses: `∑ x, ν x · δ_x y = ν y`. -/
lemma point_sum (ν : FinProb Ω) (y : Ω) :
    ∑ x, ν.wt x * (point x).wt y = ν.wt y := by
  classical
  have h : ∀ x : Ω, ν.wt x * (point x).wt y = (if x = y then ν.wt x else 0) := by
    intro x
    by_cases hxy : x = y
    · rw [if_pos hxy, point_wt_of_eq hxy.symm, mul_one]
    · rw [if_neg hxy, point_wt_of_ne (Ne.symm hxy), mul_zero]
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_ite_eq']
  simp

/-- A finite probability space has a nonempty underlying type. -/
lemma nonempty_of_finprob (ν : FinProb Ω) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have h0 : (∑ _ω : Ω, ν.wt _ω) = 0 := by simp
  rw [ν.wt_sum] at h0
  exact one_ne_zero h0

end FinProb

namespace FinProb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- **Freeze the coordinate `j` at the value `x`**: the family of finite
probability spaces which agrees with `μ` on all coordinates `≠ j` and is a
point mass at `x` on coordinate `j`. -/
noncomputable def freeze (μ : ∀ i, FinProb (Ω i)) (j : ι) (x : Ω j) :
    ∀ i, FinProb (Ω i) :=
  Function.update μ j (point x)

@[simp] lemma freeze_self {μ : ∀ i, FinProb (Ω i)} {j : ι} {x : Ω j} :
    freeze μ j x j = point x := by
  unfold freeze
  exact Function.update_self j (point x) μ

@[simp] lemma freeze_of_ne {μ : ∀ i, FinProb (Ω i)} {j : ι} {x : Ω j} {i : ι}
    (h : i ≠ j) : freeze μ j x i = μ i := by
  unfold freeze
  exact Function.update_of_ne h (point x) μ

/-- Freezing at two different coordinates commutes. -/
lemma freeze_freeze (μ : ∀ i, FinProb (Ω i)) {j k : ι} (h : j ≠ k) (x : Ω j) (y : Ω k) :
    freeze (freeze μ j x) k y = freeze (freeze μ k y) j x := by
  funext i
  by_cases hik : i = k
  · subst hik
    rw [freeze_self, freeze_of_ne (Ne.symm h), freeze_self]
  · by_cases hij : i = j
    · subst hij
      rw [freeze_of_ne h, freeze_self, freeze_self]
    · rw [freeze_of_ne hik, freeze_of_ne hij, freeze_of_ne hij, freeze_of_ne hik]

/-- The weight of a product measure, split at one coordinate. -/
lemma pi_wt_split (μ : ∀ i, FinProb (Ω i)) (j : ι) (f : ∀ i, Ω i) :
    (pi μ).wt f = (μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) := by
  rw [pi_wt, ← Finset.mul_prod_erase Finset.univ (fun i => (μ i).wt (f i)) (Finset.mem_univ j)]

/-- The weight of a product measure with coordinate `j` frozen, split at `j`. -/
lemma pi_freeze_wt (μ : ∀ i, FinProb (Ω i)) (j : ι) (x : Ω j) (f : ∀ i, Ω i) :
    (pi (freeze μ j x)).wt f
      = (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * (point x).wt (f j) := by
  rw [pi_wt, ← Finset.mul_prod_erase Finset.univ
      (fun i => (freeze μ j x i).wt (f i)) (Finset.mem_univ j)]
  rw [freeze_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [freeze_of_ne (Finset.mem_erase.mp hi).1]

/-- Averaging the frozen weights over the value `x` recovers the weight of
coordinate `j`. -/
lemma freeze_wt_sum (μ : ∀ i, FinProb (Ω i)) (j : ι) (f : ∀ i, Ω i) :
    ∑ x : Ω j, (μ j).wt x *
        ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * (point x).wt (f j))
      = (μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) := by
  calc ∑ x : Ω j, (μ j).wt x *
        ((∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * (point x).wt (f j))
      = (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
          ∑ x : Ω j, (μ j).wt x * (point x).wt (f j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) * (μ j).wt (f j) := by
        rw [point_sum]
    _ = (μ j).wt (f j) * ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) := by ring

/-- **Disintegration at one coordinate**: the probability of an event in a
product measure is the average, over the value `x` of coordinate `j` weighted
by `μ j`, of its probability in the measure with coordinate `j` frozen at `x`. -/
lemma freeze_sum (μ : ∀ i, FinProb (Ω i)) (j : ι) (C : Set (∀ i, Ω i)) :
    (pi μ).prob C = ∑ x : Ω j, (μ j).wt x * (pi (freeze μ j x)).prob C := by
  classical
  have hLHS : (pi μ).prob C
      = ∑ f, (if f ∈ C then (μ j).wt (f j) *
          ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) else 0) := by
    rw [prob]
    exact Finset.sum_congr rfl fun f _ => by
      rw [pi_wt_split]
  have hRHS : ∀ x : Ω j, (pi (freeze μ j x)).prob C
      = ∑ f, (if f ∈ C then (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
          (point x).wt (f j) else 0) := by
    intro x
    rw [prob]
    exact Finset.sum_congr rfl fun f _ => by
      rw [pi_freeze_wt]
  rw [hLHS]
  calc ∑ f, (if f ∈ C then (μ j).wt (f j) *
          ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) else 0)
      = ∑ f, ∑ x : Ω j, (μ j).wt x *
          (if f ∈ C then (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
            (point x).wt (f j) else 0) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        by_cases hfC : f ∈ C
        · rw [if_pos hfC]
          simp only [if_pos hfC]
          exact (freeze_wt_sum μ j f).symm
        · have hL : (if f ∈ C then (μ j).wt (f j) *
              ∏ i ∈ Finset.univ.erase j, (μ i).wt (f i) else 0) = 0 := by
            rw [if_neg hfC]
          have hR : (∑ x : Ω j, (μ j).wt x *
              (if f ∈ C then (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
                (point x).wt (f j) else 0)) = 0 :=
            Finset.sum_eq_zero fun x _ => by rw [if_neg hfC, mul_zero]
          rw [hL, hR]
    _ = ∑ x : Ω j, ∑ f, (μ j).wt x *
          (if f ∈ C then (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
            (point x).wt (f j) else 0) := Finset.sum_comm
    _ = ∑ x : Ω j, (μ j).wt x *
          ∑ f, (if f ∈ C then (∏ i ∈ Finset.univ.erase j, (μ i).wt (f i)) *
            (point x).wt (f j) else 0) := by
        exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ x : Ω j, (μ j).wt x * (pi (freeze μ j x)).prob C := by
        exact Finset.sum_congr rfl fun x _ => by rw [hRHS x]

/-- In the measure with coordinate `j` frozen at `x`, two events which agree on
the fibre `{f | f j = x}` have the same probability. -/
lemma freeze_prob_congr (μ : ∀ i, FinProb (Ω i)) (j : ι) (x : Ω j)
    {C C' : Set (∀ i, Ω i)} (h : ∀ f, f j = x → (f ∈ C ↔ f ∈ C')) :
    (pi (freeze μ j x)).prob C = (pi (freeze μ j x)).prob C' := by
  classical
  rw [prob, prob]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hfx : f j = x
  · by_cases hfC : f ∈ C
    · rw [if_pos hfC, if_pos ((h f hfx).mp hfC)]
    · rw [if_neg hfC, if_neg (fun hC' => hfC ((h f hfx).mpr hC'))]
  · have hw : (pi (freeze μ j x)).wt f = 0 := by
      rw [pi_freeze_wt, point_wt_of_ne hfx, mul_zero]
    rw [hw]
    by_cases hfC : f ∈ C <;> by_cases hfC' : f ∈ C' <;> simp [hfC, hfC']

/-- An event which depends on no coordinate at all is either everything or
nothing. -/
lemma dependsOn_empty (μ : ∀ i, FinProb (Ω i)) {A : Set (∀ i, Ω i)}
    (hA : DependsOn ∅ A) : A = Set.univ ∨ A = ∅ := by
  classical
  have hne : ∀ i, Nonempty (Ω i) := fun i => (μ i).nonempty_of_finprob
  let f₀ : ∀ i, Ω i := fun i => Classical.choice (hne i)
  have hpt : ∀ f : ∀ i, Ω i, (f ∈ A ↔ f₀ ∈ A) := fun f =>
    hA f f₀ fun i hi => absurd hi (Finset.notMem_empty i)
  by_cases h : f₀ ∈ A
  · left
    ext f
    exact ⟨fun _ => trivial, fun _ => (hpt f).mpr h⟩
  · right
    ext f
    exact ⟨fun hf => absurd ((hpt f).mp hf) h, fun hf => absurd hf (Set.notMem_empty f)⟩

/-- Freezing a coordinate that the event does not depend on does not change its
probability. -/
lemma freeze_prob_eq : ∀ (S : Finset ι) (A : Set (∀ i, Ω i)) (μ : ∀ i, FinProb (Ω i))
    (j : ι) (x : Ω j), j ∉ S → DependsOn S A →
    (pi (freeze μ j x)).prob A = (pi μ).prob A := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro A μ j x _ hA
    rcases dependsOn_empty μ hA with hA | hA
    · rw [hA, prob_univ, prob_univ]
    · rw [hA, prob_empty, prob_empty]
  | insert k S' hk ih =>
    intro A μ j x hjS hA
    have hkj : k ≠ j := fun h => hjS (Finset.mem_insert.mpr (Or.inl h.symm))
    have hjS' : j ∉ S' := fun h => hjS (Finset.mem_insert_of_mem h)
    let Az : Ω k → Set (∀ i, Ω i) := fun z => {f | Function.update f k z ∈ A}
    have hsec : ∀ z : Ω k, DependsOn S' (Az z) := by
      intro z f g hfg
      show Function.update f k z ∈ A ↔ Function.update g k z ∈ A
      exact hA (Function.update f k z) (Function.update g k z) (fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hiS'
        · simp only [Function.update_self]
        · have hik : i ≠ k := fun h => hk (h ▸ hiS')
          rw [Function.update_of_ne hik, Function.update_of_ne hik, hfg i hiS'])
    have hAz : ∀ z : Ω k, ∀ f, f k = z → (f ∈ A ↔ f ∈ Az z) := by
      intro z f hfz
      show f ∈ A ↔ Function.update f k z ∈ A
      rw [Function.update_eq_self_iff.mpr hfz.symm]
    calc (pi (freeze μ j x)).prob A
        = ∑ z : Ω k, (freeze μ j x k).wt z *
            (pi (freeze (freeze μ j x) k z)).prob A := freeze_sum (freeze μ j x) k A
      _ = ∑ z : Ω k, (μ k).wt z * (pi (freeze (freeze μ j x) k z)).prob (Az z) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [freeze_of_ne hkj]
          rw [freeze_prob_congr _ _ _ (hAz z)]
      _ = ∑ z : Ω k, (μ k).wt z * (pi (freeze μ k z)).prob (Az z) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [freeze_freeze μ (Ne.symm hkj) x z]
          rw [ih (Az z) (freeze μ k z) j x hjS' (hsec z)]
      _ = ∑ z : Ω k, (μ k).wt z * (pi (freeze μ k z)).prob A := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [freeze_prob_congr _ _ _ (fun f hf => (hAz z f hf).symm)]
      _ = (pi μ).prob A := (freeze_sum μ k A).symm

end FinProb

namespace Prob

theorem pi_prob_inter_eq_mul_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i))
    {S T : Finset ι} (hST : Disjoint S T) {A B : Set (∀ i, Ω i)}
    (hA : DependsOn S A) (hB : DependsOn T B) :
    (FinProb.pi μ).prob (A ∩ B) = (FinProb.pi μ).prob A * (FinProb.pi μ).prob B := by
  classical
  suffices h : ∀ (T : Finset ι) (μ : ∀ i, FinProb (Ω i)) (S : Finset ι), Disjoint S T →
      ∀ {A B : Set (∀ i, Ω i)}, DependsOn S A → DependsOn T B →
      (FinProb.pi μ).prob (A ∩ B) = (FinProb.pi μ).prob A * (FinProb.pi μ).prob B from
    h T μ S hST hA hB
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro μ S _ A B hA hB
    rcases FinProb.dependsOn_empty μ hB with hB | hB
    · rw [hB, Set.inter_univ, FinProb.prob_univ, mul_one]
    · rw [hB, Set.inter_empty, FinProb.prob_empty, mul_zero]
  | insert j T' hj ih =>
    intro μ S hST A B hA hB
    have hSj : j ∉ S := fun hjS =>
      (Finset.disjoint_left.mp hST hjS) (Finset.mem_insert_self j T')
    have hST' : Disjoint S T' := hST.mono_right (Finset.subset_insert j T')
    let B' : Ω j → Set (∀ i, Ω i) := fun x => {f | Function.update f j x ∈ B}
    have hB'dep : ∀ x, DependsOn T' (B' x) := by
      intro x f g hfg
      exact hB (Function.update f j x) (Function.update g j x) (fun i hi => by
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hiT'
        · simp only [Function.update_self]
        · have hij : i ≠ j := fun h => hj (h ▸ hiT')
          rw [Function.update_of_ne hij, Function.update_of_ne hij, hfg i hiT'])
    have hfiber (x : Ω j) : ∀ f, f j = x → (f ∈ A ∩ B ↔ f ∈ A ∩ B' x) := by
      intro f hfx
      have hupd : Function.update f j x = f := Function.update_eq_self_iff.mpr hfx.symm
      have hfib : (f ∈ B' x) ↔ f ∈ B := by
        show Function.update f j x ∈ B ↔ f ∈ B
        rw [hupd]
      rw [Set.mem_inter_iff, Set.mem_inter_iff, hfib]
    have hfiberB (x : Ω j) : ∀ f, f j = x → (f ∈ B' x ↔ f ∈ B) := by
      intro f hfx
      show Function.update f j x ∈ B ↔ f ∈ B
      rw [Function.update_eq_self_iff.mpr hfx.symm]
    calc (FinProb.pi μ).prob (A ∩ B)
        = ∑ x : Ω j, (μ j).wt x * (FinProb.pi (FinProb.freeze μ j x)).prob (A ∩ B) :=
            FinProb.freeze_sum μ j (A ∩ B)
      _ = ∑ x : Ω j, (μ j).wt x *
            (FinProb.pi (FinProb.freeze μ j x)).prob (A ∩ B' x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [FinProb.freeze_prob_congr _ _ _ (hfiber x)]
      _ = ∑ x : Ω j, (μ j).wt x * ((FinProb.pi (FinProb.freeze μ j x)).prob A *
            (FinProb.pi (FinProb.freeze μ j x)).prob (B' x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [ih (FinProb.freeze μ j x) S hST' hA (hB'dep x)]
      _ = ∑ x : Ω j, (μ j).wt x * ((FinProb.pi μ).prob A *
            (FinProb.pi (FinProb.freeze μ j x)).prob (B' x)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [FinProb.freeze_prob_eq S A μ j x hSj hA]
      _ = ∑ x : Ω j, (μ j).wt x * ((FinProb.pi μ).prob A *
            (FinProb.pi (FinProb.freeze μ j x)).prob B) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [FinProb.freeze_prob_congr _ _ _ (hfiberB x)]
      _ = (FinProb.pi μ).prob A *
            ∑ x : Ω j, (μ j).wt x * (FinProb.pi (FinProb.freeze μ j x)).prob B := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = (FinProb.pi μ).prob A * (FinProb.pi μ).prob B := by
          rw [FinProb.freeze_sum μ j B]

end Prob

end Work.Deep.Reed
