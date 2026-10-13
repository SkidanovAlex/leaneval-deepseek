import Mathlib
import Submission.Work.WilE4.CAD.sign_eval_abs_large

namespace Work.WilE4.CAD

theorem eventually_coeff_bounds {X : Type*} [TopologicalSpace X] (Q : X → Polynomial ℝ)
    (hcont : ∀ j, Continuous fun x => (Q x).coeff j) {x₀ : X} {a : ℕ → X}
    (ha : Filter.Tendsto a Filter.atTop (nhds x₀)) {d : ℕ} (hc : (Q x₀).coeff d ≠ 0) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      (∀ j ∈ Finset.range (d + 1), |(Q x₀).coeff j| ≤ C) ∧
      ε ≤ |(Q x₀).coeff d| ∧
      (∀ᶠ n in Filter.atTop,
        (∀ j ∈ Finset.range (d + 1), |(Q (a n)).coeff j| ≤ C) ∧
        ε ≤ |(Q (a n)).coeff d|) := by
  refine ⟨(∑ j ∈ Finset.range (d + 1), |(Q x₀).coeff j|) + 1, |(Q x₀).coeff d| / 2,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h := Finset.sum_nonneg (s := Finset.range (d + 1))
      (f := fun j => |(Q x₀).coeff j|) (fun i _ => abs_nonneg _)
    linarith
  · exact half_pos (abs_pos.mpr hc)
  · intro j hj
    have h := Finset.single_le_sum (s := Finset.range (d + 1))
      (f := fun j => |(Q x₀).coeff j|) (fun i _ => abs_nonneg _) hj
    linarith
  · exact half_le_self (abs_nonneg _)
  · have hev1 : ∀ j ∈ Finset.range (d + 1),
        ∀ᶠ n in Filter.atTop,
          |(Q (a n)).coeff j| ≤ (∑ i ∈ Finset.range (d + 1), |(Q x₀).coeff i|) + 1 := by
      intro j hj
      have hlt : |(Q x₀).coeff j| < (∑ i ∈ Finset.range (d + 1), |(Q x₀).coeff i|) + 1 := by
        have h := Finset.single_le_sum (s := Finset.range (d + 1))
          (f := fun j => |(Q x₀).coeff j|) (fun i _ => abs_nonneg _) hj
        linarith
      have hopen : IsOpen {x : X | |(Q x).coeff j| <
          (∑ i ∈ Finset.range (d + 1), |(Q x₀).coeff i|) + 1} :=
        (hcont j).abs.isOpen_preimage
          (Set.Iio ((∑ i ∈ Finset.range (d + 1), |(Q x₀).coeff i|) + 1)) isOpen_Iio
      have hmem : {x : X | |(Q x).coeff j| <
          (∑ i ∈ Finset.range (d + 1), |(Q x₀).coeff i|) + 1} ∈ nhds x₀ :=
        hopen.mem_nhds hlt
      filter_upwards [ha.eventually hmem] with n hn
      exact le_of_lt hn
    have h1 := (Finset.eventually_all (Finset.range (d + 1))).mpr hev1
    have hev2 : ∀ᶠ n in Filter.atTop, |(Q x₀).coeff d| / 2 ≤ |(Q (a n)).coeff d| := by
      have hlt : |(Q x₀).coeff d| / 2 < |(Q x₀).coeff d| := half_lt_self (abs_pos.mpr hc)
      have hopen : IsOpen {x : X | |(Q x₀).coeff d| / 2 < |(Q x).coeff d|} :=
        (hcont d).abs.isOpen_preimage (Set.Ioi (|(Q x₀).coeff d| / 2)) isOpen_Ioi
      have hmem : {x : X | |(Q x₀).coeff d| / 2 < |(Q x).coeff d|} ∈ nhds x₀ :=
        hopen.mem_nhds hlt
      filter_upwards [ha.eventually hmem] with n hn
      exact le_of_lt hn
    filter_upwards [h1, hev2] with n hn1 hn2
    exact ⟨hn1, hn2⟩

end Work.WilE4.CAD
