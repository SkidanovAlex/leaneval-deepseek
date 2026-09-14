import Mathlib
import Submission.Commons.Analysis.Calculus.ae_eq_add_intervalIntegral_of_forall_integral_inner_deriv_add_eq_zero_smooth

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter Function
open scoped Topology

/-- The `i`-th coordinate of an interval integral of a `PiLp`-valued function. -/
private lemma intervalIntegral_apply_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {N : ℕ} {g : ℝ → EuclideanSpace E (Fin N)} {a t : ℝ} (i : Fin N)
    (h : IntervalIntegrable g volume a t) :
    (∫ s in a..t, g s) i = ∫ s in a..t, g s i := by
  have hkey := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => E) i).intervalIntegral_comp_comm (𝕜 := ℝ) h
  simpa only [PiLp.proj_apply, Function.comp_apply] using hkey.symm

theorem ae_eq_add_intervalIntegral_of_forall_weighted_inner_deriv_add_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} {m : Fin N → ℝ} (hm : ∀ i, 0 < m i)
    {f g : ℝ → EuclideanSpace E (Fin N)} {a b : ℝ} (hab : a < b)
    (hf : MeasureTheory.LocallyIntegrableOn f (Set.Ioo a b) MeasureTheory.volume)
    (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ (ψ : ℝ → ℝ) (w : EuclideanSpace E (Fin N)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b →
      MeasureTheory.integral MeasureTheory.volume
          (fun t => deriv ψ t * (Finset.sum Finset.univ fun i => m i * inner ℝ (f t i) (w i)))
        + MeasureTheory.integral MeasureTheory.volume
          (fun t => ψ t * (Finset.sum Finset.univ fun i => m i * inner ℝ (g t i) (w i))) = 0) :
    ∃ c : EuclideanSpace E (Fin N),
      f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)] (fun t => c + ∫ s in a..t, g s) := by
  classical
  have key : ∀ i : Fin N, ∃ c : E,
      (fun t => f t i) =ᵐ[volume.restrict (Set.Ioo a b)]
        (fun t => c + ∫ s in a..t, g s i) := by
    intro i
    refine ae_eq_add_intervalIntegral_of_forall_integral_inner_deriv_add_eq_zero_smooth hab ?_ ?_ ?_
    · have h1 : LocallyIntegrableOn
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => E) i) ∘ f) (Set.Ioo a b) volume :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => E) i).locallyIntegrableOn_comp hf
      simpa only [Function.comp_def, PiLp.proj_apply] using h1
    · have h1 : ContinuousOn ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => E) i) ∘ g) (Set.Icc a b) :=
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => E) i).continuous.continuousOn).comp hg
          (fun x _ => Set.mem_univ _)
      simpa only [Function.comp_def, PiLp.proj_apply] using h1
    · intro ψ v hψ hcs hts
      have hsumF : ∀ t, (∑ j, m j * inner ℝ (f t j) (PiLp.single (β := fun _ : Fin N => E) 2 i v j))
          = m i * inner ℝ (f t i) v := by
        intro t
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [PiLp.single_eq_of_ne (β := fun _ : Fin N => E) (p := 2) hj v, inner_zero_right, mul_zero]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hsumG : ∀ t, (∑ j, m j * inner ℝ (g t j) (PiLp.single (β := fun _ : Fin N => E) 2 i v j))
          = m i * inner ℝ (g t i) v := by
        intro t
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [PiLp.single_eq_of_ne (β := fun _ : Fin N => E) (p := 2) hj v, inner_zero_right, mul_zero]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hh := h ψ (PiLp.single (β := fun _ : Fin N => E) 2 i v) hψ hcs hts
      rw [show (fun t => deriv ψ t * (∑ j, m j * inner ℝ (f t j) (PiLp.single (β := fun _ : Fin N => E) 2 i v j)))
            = (fun t => deriv ψ t * (m i * inner ℝ (f t i) v)) from by
              ext t; rw [hsumF t],
          show (fun t => ψ t * (∑ j, m j * inner ℝ (g t j) (PiLp.single (β := fun _ : Fin N => E) 2 i v j)))
            = (fun t => ψ t * (m i * inner ℝ (g t i) v)) from by
              ext t; rw [hsumG t]] at hh
      have hfacF : (∫ t, deriv ψ t * (m i * inner ℝ (f t i) v))
          = m i * ∫ t, deriv ψ t * inner ℝ (f t i) v := by
        rw [show (fun t => deriv ψ t * (m i * inner ℝ (f t i) v))
              = (fun t => m i * (deriv ψ t * inner ℝ (f t i) v)) from by ext t; ring]
        rw [MeasureTheory.integral_const_mul]
      have hfacG : (∫ t, ψ t * (m i * inner ℝ (g t i) v))
          = m i * ∫ t, ψ t * inner ℝ (g t i) v := by
        rw [show (fun t => ψ t * (m i * inner ℝ (g t i) v))
              = (fun t => m i * (ψ t * inner ℝ (g t i) v)) from by ext t; ring]
        rw [MeasureTheory.integral_const_mul]
      rw [hfacF, hfacG] at hh
      have hz : m i * ((∫ t, deriv ψ t * inner ℝ (f t i) v)
          + (∫ t, ψ t * inner ℝ (g t i) v)) = 0 := by
        rw [mul_add]; exact hh
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hm i))
  choose cc hcc using key
  refine ⟨(WithLp.toLp 2 (fun i => cc i) : EuclideanSpace E (Fin N)), ?_⟩
  change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
      f t = (WithLp.toLp 2 (fun i => cc i) : EuclideanSpace E (Fin N)) + ∫ s in a..t, g s
  rw [ae_restrict_iff' measurableSet_Ioo]
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i, t ∈ Set.Ioo a b →
      f t i = cc i + ∫ s in a..t, g s i := by
    rw [Filter.eventually_all]
    intro i
    exact (ae_restrict_iff' measurableSet_Ioo).mp (hcc i)
  filter_upwards [hall] with t ht htI
  apply PiLp.ext
  intro i
  rw [ht i htI]
  have hcomp : (∫ s in a..t, g s) i = ∫ s in a..t, g s i := by
    refine intervalIntegral_apply_pi i ?_
    have hcont : ContinuousOn g (Set.uIcc a t) := by
      rw [Set.uIcc_of_le htI.1.le]
      exact hg.mono (Set.Icc_subset_Icc_right htI.2.le)
    exact hcont.intervalIntegrable
  rw [PiLp.add_apply, hcomp]

end Commons.Analysis.Calculus
