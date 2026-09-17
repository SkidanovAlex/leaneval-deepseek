import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib
import Submission.Commons.Probability.Gaussian.stdGaussian_map_inner_eq
import Submission.Commons.Probability.Reflection.iid_stdGaussian_maximal_tail_Phi

namespace Commons.Probability.Reflection

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- Antitonicity of the standard Gaussian upper tail. -/
theorem stdGaussian_real_tail_antitone {a b : ℝ} (hab : a ≤ b) :
    (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | b ≤ y}
      ≤ (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | a ≤ y} := by
  apply measureReal_mono
  · intro y hy; exact le_trans hab hy
  · exact measure_ne_top _ _

theorem fin_maximal_tail_Phi_of_map_pi {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → E) (hX : ∀ i, Measurable (X i))
    (hlaw : μ.map (fun ω => fun j : Fin n => X j ω)
      = MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian E))
    (w : E) (hw : ‖w‖ ≤ 1) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    μ.real {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
        ε * inner ℝ (X i ω) w|}
      ≤ 4 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (ε * Real.sqrt n) ≤ y} := by
  classical
  rcases eq_or_ne w 0 with rfl | hwne
  · -- Case w = 0 : everything is zero
    have hempty : {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
        ε * inner ℝ (X i ω) 0|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro k hk
      have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
          ε * inner ℝ (X i ω) 0) = 0 := by simp
      rw [hsum, abs_zero]
      exact not_le.mpr hr
    rw [hempty, measureReal_empty]
    exact mul_nonneg (by norm_num) measureReal_nonneg
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- Case n = 0 : the event is empty
      subst hn0
      have hempty : {ω | ∃ k ≤ 0, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin 0 => (i : ℕ) < k),
          ε * inner ℝ (X i ω) w|} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
        intro k hk
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        have hsum : (∑ i ∈ Finset.univ.filter (fun i : Fin 0 => (i : ℕ) < 0),
            ε * inner ℝ (X i ω) w) = 0 := by simp
        rw [hsum, abs_zero]
        exact not_le.mpr hr
      rw [hempty, measureReal_empty]
      exact mul_nonneg (by norm_num) measureReal_nonneg
    · -- Main case : w ≠ 0 and n ≥ 1
      set f : E → ℝ := fun x => inner ℝ x w with hfdef
      have hf : Measurable f := by rw [hfdef]; fun_prop
      set φ : Ω → (Fin n → E) := fun ω j => X j ω with hφdef
      have hφ : Measurable φ := measurable_pi_iff.mpr hX
      set Ψ : Ω → (Fin n → ℝ) := fun ω j => f (X j ω) with hΨdef
      have hΨ : Measurable Ψ := measurable_pi_iff.mpr (fun j => hf.comp (hX j))
      set ν : Measure ℝ := (ProbabilityTheory.stdGaussian E).map f with hνdef
      haveI hνprob : IsProbabilityMeasure ν := inferInstance
      have hmapΨ : μ.map Ψ = Measure.pi (fun _ : Fin n => ν) := by
        have hΦ : Measurable (fun x : Fin n → E => fun j : Fin n => f (x j)) :=
          measurable_pi_iff.mpr (fun j => hf.comp (measurable_pi_apply j))
        have h1 : Ψ = (fun x : Fin n → E => fun j : Fin n => f (x j)) ∘ φ := by
          funext ω; rfl
        rw [h1, ← Measure.map_map hΦ hφ, hlaw]
        have h2 := Measure.pi_map_pi (μ := fun _ : Fin n => ProbabilityTheory.stdGaussian E)
          (f := fun _ : Fin n => f) (fun _ => hf.aemeasurable)
        simpa [hνdef] using h2
      set P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => ν) with hPdef
      set Pstd : Measure (Fin n → ℝ) :=
        Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ) with hPstddef
      set A : Set (Fin n → ℝ) :=
        {y | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i|}
        with hAdef
      set Up : (Fin n → ℝ) → Prop := fun y =>
        ∃ k ≤ n, r ≤ ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i
        with hUpdef
      set negmap : (Fin n → ℝ) → (Fin n → ℝ) := fun y i => -y i with hnegdef
      set A_up : Set (Fin n → ℝ) := {y | Up y} with hAupdef
      set A_dn : Set (Fin n → ℝ) := {y | Up (negmap y)} with hAdndef
      -- the preimage bridge
      have hbridge : {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
          ε * inner ℝ (X i ω) w|} = Ψ ⁻¹' A := by
        rw [hΨdef, hAdef, hfdef]; rfl
      -- measurability of the summands
      have hsumMeas : ∀ k : ℕ, Measurable (fun y : Fin n → ℝ =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i) :=
        fun k => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
      have hsumEpsMeas : ∀ k : ℕ, Measurable (fun y : Fin n → ℝ =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i) :=
        fun k => by fun_prop
      have hA : MeasurableSet A := by
        rw [hAdef]
        have heq : {y : Fin n → ℝ | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i|}
            = ⋃ k ∈ Finset.range (n + 1), {y : Fin n → ℝ |
                r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i|} := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
          constructor
          · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.lt_succ_of_le hk, h⟩
          · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.le_of_lt_succ hk, h⟩
        rw [heq]
        exact Finset.measurableSet_biUnion _ (fun k _ =>
          measurableSet_le measurable_const (Measurable.abs (hsumEpsMeas k)))
      have hA_up : MeasurableSet A_up := by
        rw [hAupdef, hUpdef]
        have heq : {y : Fin n → ℝ | ∃ k ≤ n, r ≤ ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i}
            = ⋃ k ∈ Finset.range (n + 1), {y : Fin n → ℝ |
                r ≤ ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i} := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
          constructor
          · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.lt_succ_of_le hk, h⟩
          · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.le_of_lt_succ hk, h⟩
        rw [heq]
        exact Finset.measurableSet_biUnion _ (fun k _ =>
          measurableSet_le measurable_const (measurable_const.mul (hsumMeas k)))
      -- split A = A_up ∪ A_dn
      have hA_split : A = A_up ∪ A_dn := by
        ext y
        rw [hAdef, hAupdef, hAdndef, hUpdef, hnegdef]
        simp only [Set.mem_ofPred_eq, Set.mem_union]
        have key : ∀ k : ℕ,
            (r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i|)
            ↔ (r ≤ ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i)
              ∨ (r ≤ ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), -y i) := by
          intro k
          have h1 : (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ε * y i)
              = ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i :=
            (Finset.mul_sum _ y ε).symm
          have h3 : ε * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), -y i)
              = -(ε * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), y i) := by
            rw [Finset.sum_neg_distrib, mul_neg]
          rw [h1, h3]
          exact le_abs
        constructor
        · rintro ⟨k, hk, h⟩
          rcases (key k).mp h with h' | h'
          · exact Or.inl ⟨k, hk, h'⟩
          · exact Or.inr ⟨k, hk, h'⟩
        · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
          · exact ⟨k, hk, (key k).mpr (Or.inl h)⟩
          · exact ⟨k, hk, (key k).mpr (Or.inr h)⟩
      -- union bound
      have hunion : P.real A ≤ P.real A_up + P.real A_dn := by
        rw [hA_split]
        exact measureReal_union_le _ _
      -- symmetry ν.map neg = ν
      have hνsym : ν.map (fun x : ℝ => -x) = ν := by
        have hstdE : (ProbabilityTheory.stdGaussian E).map (fun x : E => -x)
            = ProbabilityTheory.stdGaussian E := by
          simpa using ProbabilityTheory.stdGaussian_map (E := E) (F := E) (LinearIsometryEquiv.neg ℝ)
        have hodd : (fun x : E => -(f x)) = fun x : E => f (-x) := by
          funext x; rw [hfdef]; simp
        have hcomp : (fun x : ℝ => -x) ∘ f = fun x : E => f (-x) := by
          funext x; exact congrFun hodd x
        calc ν.map (fun x : ℝ => -x)
            = ((ProbabilityTheory.stdGaussian E).map f).map (fun x : ℝ => -x) := by rw [hνdef]
          _ = (ProbabilityTheory.stdGaussian E).map ((fun x : ℝ => -x) ∘ f) :=
                Measure.map_map measurable_neg hf
          _ = (ProbabilityTheory.stdGaussian E).map (fun x : E => f (-x)) := by rw [hcomp]
          _ = (ProbabilityTheory.stdGaussian E).map (f ∘ (fun x : E => -x)) := rfl
          _ = ((ProbabilityTheory.stdGaussian E).map (fun x : E => -x)).map f :=
                (Measure.map_map hf measurable_neg).symm
          _ = (ProbabilityTheory.stdGaussian E).map f := by rw [hstdE]
          _ = ν := by rw [hνdef]
      have hnegmap : P.map negmap = P := by
        rw [hPdef, hnegdef]
        have h2 := Measure.pi_map_pi (μ := fun _ : Fin n => ν)
          (f := fun _ : Fin n => (fun x : ℝ => -x)) (fun _ => measurable_neg.aemeasurable)
        simpa [hνsym] using h2
      have hnegmap_meas : Measurable negmap := by
        rw [hnegdef]; exact measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).neg)
      -- symmetry : P.real A_dn = P.real A_up
      have hA_dn_eq : P.real A_dn = P.real A_up := by
        have hpre : A_dn = negmap ⁻¹' A_up := by
          rw [hAdndef, hAupdef]
          rfl
        rw [hpre, ← map_measureReal_apply hnegmap_meas hA_up]
        rw [hnegmap]
      -- reduction ν to standard Gaussian
      set g : ℝ → ℝ := fun y => ‖w‖ * y with hgdef
      have hg : Measurable g := by rw [hgdef]; fun_prop
      have hνeq : ν = (ProbabilityTheory.stdGaussian ℝ).map g := by
        rw [hνdef, hfdef, hgdef]
        exact Commons.Probability.Gaussian.stdGaussian_map_inner_eq w
      set T : (Fin n → ℝ) → (Fin n → ℝ) := fun z i => g (z i) with hTdef
      have hTmeas : Measurable T := by
        rw [hTdef]; exact measurable_pi_iff.mpr (fun i => hg.comp (measurable_pi_apply i))
      have hTmap : Pstd.map T = P := by
        rw [hTdef, hPstddef, hPdef]
        have h2 := Measure.pi_map_pi (μ := fun _ : Fin n => ProbabilityTheory.stdGaussian ℝ)
          (f := fun _ : Fin n => g) (fun _ => hg.aemeasurable)
        rw [h2, ← hνeq]
      set S : Set (Fin n → ℝ) := {z | ∃ k ≤ n,
          r ≤ (ε * ‖w‖) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), z i}
        with hSdef
      have hTpre : T ⁻¹' A_up = S := by
        ext z
        rw [hAupdef, hUpdef, hTdef, hgdef, hSdef]
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨k, hk, h⟩
          refine ⟨k, hk, ?_⟩
          have hfact : ε * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ‖w‖ * z i)
              = (ε * ‖w‖) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), z i := by
            rw [← Finset.mul_sum]; ring
          rwa [hfact] at h
        · rintro ⟨k, hk, h⟩
          refine ⟨k, hk, ?_⟩
          have hfact : ε * (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), ‖w‖ * z i)
              = (ε * ‖w‖) * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), z i := by
            rw [← Finset.mul_sum]; ring
          rw [hfact]; exact h
      -- one-sided bound
      have hone : P.real A_up ≤ 2 * (ProbabilityTheory.stdGaussian ℝ).real
          {y : ℝ | r / (ε * Real.sqrt n) ≤ y} := by
        rw [← hTmap, map_measureReal_apply hTmeas hA_up, hTpre]
        have hσ : 0 < ε * ‖w‖ := mul_pos hε hwpos
        have hbound := iid_stdGaussian_maximal_tail_Phi (n := n) (σ := ε * ‖w‖) hσ hr
        refine le_trans hbound ?_
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply stdGaussian_real_tail_antitone
        -- compare the two division points
        have hσ'le : ε * ‖w‖ ≤ ε := by
          simpa using mul_le_mul_of_nonneg_left hw (le_of_lt hε)
        have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
        exact div_le_div₀ (le_of_lt hr) le_rfl (mul_pos hσ hsqrt_pos)
          (mul_le_mul_of_nonneg_right hσ'le (Real.sqrt_nonneg n))
      -- final assembly
      have hA_dn_le : P.real A_dn ≤ 2 * (ProbabilityTheory.stdGaussian ℝ).real
          {y : ℝ | r / (ε * Real.sqrt n) ≤ y} := by
        rw [hA_dn_eq]; exact hone
      calc μ.real {ω | ∃ k ≤ n, r ≤ |∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k),
              ε * inner ℝ (X i ω) w|}
          = (μ.map Ψ).real A := by rw [hbridge, map_measureReal_apply hΨ hA]
        _ = P.real A := by rw [hmapΨ, hPdef]
        _ ≤ P.real A_up + P.real A_dn := hunion
        _ ≤ 2 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (ε * Real.sqrt n) ≤ y}
              + 2 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (ε * Real.sqrt n) ≤ y} :=
            add_le_add hone hA_dn_le
        _ = 4 * (ProbabilityTheory.stdGaussian ℝ).real {y : ℝ | r / (ε * Real.sqrt n) ≤ y} := by ring

end

end Commons.Probability.Reflection
