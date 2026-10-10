import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.HeckeL.Series

noncomputable section

section

variable {σ : Type*} [DecidableEq σ]

/-- The subtype of finitely supported `ℕ`-valued functions whose support lies in `T`. -/
private def suppSubtype (T : Finset σ) : Type _ := {c : σ →₀ ℕ // c.support ⊆ T}

/-- The monomial attached to `c` and the family `a`. -/
private def phi (a : σ → ℂ) (T : Finset σ) (c : suppSubtype T) : ℂ :=
  ∏ i ∈ T, (a i) ^ (c.1 i)

omit [DecidableEq σ] in
private lemma phi_eq_prod_support (a : σ → ℂ) (T : Finset σ) (c : suppSubtype T) :
    (∏ i ∈ c.1.support, (a i) ^ (c.1 i)) = phi a T c := by
  rw [phi]
  exact Finset.prod_subset c.2 fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, pow_zero]

/-- Add a new coordinate `j` with exponent `n` to an element of `suppSubtype T`. -/
private def toF (j : σ) (T : Finset σ) (p : suppSubtype T × ℕ) : suppSubtype (insert j T) :=
  ⟨p.1.1 + Finsupp.single j p.2, by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases hij : i = j
    · exact Finset.mem_insert.mpr (Or.inl hij)
    · refine Finset.mem_insert.mpr (Or.inr (p.1.2 ((Finsupp.mem_support_iff).mpr ?_)))
      intro h0
      apply hi
      rw [Finsupp.add_apply, h0, Finsupp.single_eq_of_ne hij, add_zero]⟩

/-- Split off the coordinate `j` from an element of `suppSubtype (insert j T)`. -/
private def invF (j : σ) (T : Finset σ) (c : suppSubtype (insert j T)) : suppSubtype T × ℕ :=
  (⟨c.1.erase j, by
    intro i hi
    rw [Finsupp.support_erase, Finset.mem_erase] at hi
    obtain ⟨hij, hisupp⟩ := hi
    rcases Finset.mem_insert.mp (c.2 hisupp) with h | h
    · exact absurd h hij
    · exact h⟩, c.1 j)

/-- The bijection `suppSubtype T × ℕ ≃ suppSubtype (insert j T)` sending `(d, n)` to
`d + n • single j 1`, for `j ∉ T`. -/
private def equivInsert (j : σ) (T : Finset σ) (hj : j ∉ T) :
    suppSubtype T × ℕ ≃ suppSubtype (insert j T) where
  toFun := toF j T
  invFun := invF j T
  left_inv := by
    rintro ⟨d, n⟩
    have hdj : d.1 j = 0 := (Finsupp.notMem_support_iff).mp fun h => hj (d.2 h)
    refine Prod.ext (Subtype.ext ?_) ?_
    · show (toF j T (d, n)).1.erase j = d.1
      rw [toF]
      ext i
      rw [Finsupp.erase_apply, Finsupp.add_apply]
      by_cases hi : i = j
      · rw [hi, if_pos rfl, hdj]
      · rw [if_neg hi, Finsupp.single_eq_of_ne hi, add_zero]
    · show (d.1 + Finsupp.single j n) j = n
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hdj, zero_add]
  right_inv := by
    rintro ⟨c, hc⟩
    refine Subtype.ext ?_
    show c.erase j + Finsupp.single j (c j) = c
    exact Finsupp.erase_add_single j c

/-- The key multiplicativity relation: `phi` of the "added" coordinate factors. -/
private lemma phi_toF (a : σ → ℂ) (j : σ) (T : Finset σ) (hj : j ∉ T)
    (p : suppSubtype T × ℕ) :
    phi a (insert j T) (toF j T p) = phi a T p.1 * (a j) ^ p.2 := by
  obtain ⟨d, n⟩ := p
  have hdj : d.1 j = 0 := (Finsupp.notMem_support_iff).mp fun h => hj (d.2 h)
  have hTprod : (∏ i ∈ T, a i ^ ((d.1 + Finsupp.single j n) i)) = ∏ i ∈ T, a i ^ d.1 i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (fun h => hj (by rw [← h]; exact hi)), add_zero]
  show (∏ i ∈ insert j T, a i ^ ((d.1 + Finsupp.single j n) i)) =
      (∏ i ∈ T, a i ^ d.1 i) * a j ^ n
  rw [Finset.prod_insert hj, hTprod, Finsupp.add_apply, Finsupp.single_eq_same, hdj, zero_add]
  exact mul_comm _ _

/-- Summability and the value of the `T`-truncated Euler product. -/
private theorem summable_and_hasSum (a : σ → ℂ) (T : Finset σ)
    (hT : ∀ i ∈ T, ‖a i‖ < 1) :
    Summable (fun c : suppSubtype T => ‖phi a T c‖) ∧
      HasSum (fun c : suppSubtype T => phi a T c) (∏ i ∈ T, (1 - a i)⁻¹) := by
  classical
  revert hT
  induction T using Finset.induction with
  | empty =>
    intro _
    have huniq : Unique (suppSubtype (∅ : Finset σ)) :=
      { default := ⟨0, by simp⟩
        uniq := fun c => Subtype.ext (Finsupp.support_eq_empty.mp
          (Finset.eq_empty_iff_forall_notMem.mpr
            fun i hi => (Finset.notMem_empty i) (c.2 hi))) }
    letI := huniq
    refine ⟨(hasSum_unique _).summable, ?_⟩
    rw [Finset.prod_empty]
    exact (hasSum_unique (fun _ : suppSubtype (∅ : Finset σ) => (1 : ℂ))).congr_fun
      fun c => by simp [phi]
  | insert j T hj ih =>
    intro hT
    have hT' : ∀ i ∈ T, ‖a i‖ < 1 := fun i hi => hT i (Finset.mem_insert_of_mem hi)
    obtain ⟨ihsum, ihhas⟩ := ih hT'
    have hlt : ‖a j‖ < 1 := hT j (Finset.mem_insert_self j T)
    have hgeom : Summable (fun n : ℕ => ‖(a j) ^ n‖) := by
      have h := (summable_geometric_iff_norm_lt_one (ξ := (‖a j‖ : ℝ))).mpr (by
        rw [norm_norm]; exact hlt)
      simpa only [norm_pow] using h
    have hgeom_has : HasSum (fun n : ℕ => (a j) ^ n) ((1 - a j)⁻¹) :=
      hasSum_geometric_of_norm_lt_one hlt
    have h1 : Summable (fun p : suppSubtype T × ℕ => ‖phi a T p.1‖ * ‖(a j) ^ p.2‖) :=
      Summable.mul_of_nonneg ihsum hgeom (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have h2 : Summable (fun p : suppSubtype T × ℕ => ‖phi a T p.1 * (a j) ^ p.2‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_mul_le _ _) h1
    have h3 : Summable (fun p : suppSubtype T × ℕ => phi a T p.1 * (a j) ^ p.2) :=
      Summable.of_norm h2
    have h4 : HasSum (fun p : suppSubtype T × ℕ => phi a T p.1 * (a j) ^ p.2)
        ((∏ i ∈ T, (1 - a i)⁻¹) * (1 - a j)⁻¹) :=
      ihhas.mul hgeom_has h3
    have key : ∀ p : suppSubtype T × ℕ,
        phi a (insert j T) (toF j T p) = phi a T p.1 * (a j) ^ p.2 :=
      fun p => phi_toF a j T hj p
    refine ⟨?_, ?_⟩
    · have h2' : Summable
          ((fun c : suppSubtype (insert j T) => ‖phi a (insert j T) c‖) ∘ (equivInsert j T hj)) :=
        h2.congr fun p => by
          simp only [Function.comp_apply]
          congr 1
          exact (key p).symm
      exact (Equiv.summable_iff (equivInsert j T hj)).mp h2'
    · have h4' : HasSum
          ((fun c : suppSubtype (insert j T) => phi a (insert j T) c) ∘ (equivInsert j T hj))
          ((∏ i ∈ T, (1 - a i)⁻¹) * (1 - a j)⁻¹) :=
        h4.congr_fun fun p => by
          simp only [Function.comp_apply]
          exact key p
      have htrans := (Equiv.hasSum_iff (equivInsert j T hj)).mp h4'
      rw [Finset.prod_insert hj, mul_comm]
      exact htrans

end

theorem tsum_finsupp_support_subset_prod {σ : Type*} (T : Finset σ) (a : σ → ℂ)
    (ha : ∀ i ∈ T, ‖a i‖ < 1) :
    ∑' c : {c : σ →₀ ℕ // c.support ⊆ T}, (∏ i ∈ c.1.support, (a i) ^ (c.1 i)) =
      ∏ i ∈ T, (1 - a i)⁻¹ := by
  classical
  have h := (summable_and_hasSum a T ha).2
  show (∑' c : suppSubtype T, (∏ i ∈ c.1.support, (a i) ^ (c.1 i))) = ∏ i ∈ T, (1 - a i)⁻¹
  rw [← h.tsum_eq]
  exact tsum_congr fun c => phi_eq_prod_support a T c

end

end NK.HeckeL.Series
