import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Commons.Analysis.Normed.intVec_coord_norm_le_norm

set_option linter.style.haveILetI false

namespace Commons.Analysis.Normed

/-- The set of integers of norm at most `B` is finite. -/
lemma finite_int_ball (B : ℝ) : {z : ℤ | ‖z‖ ≤ B}.Finite := by
  rcases exists_nat_ge B with ⟨n, hn⟩
  have hsub : {z : ℤ | ‖z‖ ≤ B} ⊆ (Finset.Icc (-(n : ℤ)) (n : ℤ) : Set ℤ) := by
    intro z hz
    change ‖z‖ ≤ B at hz
    rw [Int.norm_eq_abs] at hz
    have hzn : |(z : ℝ)| ≤ (n : ℝ) := le_trans hz hn
    have habs : -(n : ℝ) ≤ (z : ℝ) ∧ (z : ℝ) ≤ (n : ℝ) := abs_le.mp hzn
    have h1 : -(n : ℤ) ≤ z := by
      exact_mod_cast habs.1
    have h2 : z ≤ (n : ℤ) := by
      exact_mod_cast habs.2
    simpa using (Finset.mem_Icc.mpr ⟨h1, h2⟩ : z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ))
  exact (Finset.finite_toSet (Finset.Icc (-(n : ℤ)) (n : ℤ))).subset hsub

theorem finite_bounded_int_vectors {σ : Type*} [Fintype σ] (B : ℝ) :
    {x : σ → ℤ | ‖x‖ ≤ B}.Finite := by
  classical
  let T : Set ℤ := {z : ℤ | ‖z‖ ≤ B}
  have hT : T.Finite := finite_int_ball B
  letI : Fintype ↥T := hT.fintype
  let s : Set (σ → ℤ) := {x | ‖x‖ ≤ B}
  let f : ↥s → σ → ↥T := fun x i => ⟨(x : σ → ℤ) i,
    le_trans (norm_le_pi_norm (x : σ → ℤ) i) x.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  exact (Set.finite_coe_iff).mp (Finite.of_injective f hf)

end Commons.Analysis.Normed