import Mathlib

namespace Work.HP.Lat

lemma mem_span_pair_of_not_linIndep {ι : Type*} [Fintype ι] (x y z : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) (h : ¬ LinearIndependent ℤ ![x, y, z]) :
    (fun i => (z i : ℚ)) ∈
      Submodule.span ℚ {(fun i => (x i : ℚ)), (fun i => (y i : ℚ))} := by
  -- A nontrivial ℤ-linear relation among `x, y, z`.
  obtain ⟨g, hg, hgne⟩ := Fintype.not_linearIndependent_iff.mp h
  have hg3 : g 0 • x + g 1 • y + g 2 • z = 0 := by
    have := hg
    rw [Fin.sum_univ_three] at this
    simpa using this
  rw [Submodule.mem_span_pair]
  by_cases h2 : g 2 = 0
  · -- If the coefficient of `z` vanishes, the remaining relation contradicts `hxy`.
    exfalso
    have h12 : g 0 • x + g 1 • y = 0 := by
      have := hg3; rw [h2, zero_smul, add_zero] at this; exact this
    have hf : (∑ i : Fin 2, (![g 0, g 1] i) • ![x, y] i) = 0 := by
      simpa [Fin.sum_univ_two] using h12
    have hzero := (Fintype.linearIndependent_iff.mp hxy) ![g 0, g 1] hf
    have hg0 : g 0 = 0 := hzero 0
    have hg1 : g 1 = 0 := hzero 1
    obtain ⟨i, hi⟩ := hgne
    fin_cases i <;> simp_all
  · -- Otherwise `z` is a ℚ-linear combination of `x` and `y`.
    refine ⟨-(g 0 : ℚ) / (g 2 : ℚ), -(g 1 : ℚ) / (g 2 : ℚ), ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hcast : (g 0 : ℚ) * (x j : ℚ) + (g 1 : ℚ) * (y j : ℚ) + (g 2 : ℚ) * (z j : ℚ) = 0 := by
      have h := congr_fun hg3 j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      exact_mod_cast h
    have hC : (g 2 : ℚ) ≠ 0 := by exact_mod_cast h2
    field_simp
    linarith

end Work.HP.Lat
