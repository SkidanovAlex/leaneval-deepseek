import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

theorem linearIndependent_of_key {R : Type*} [Field R] {ι : Type*} [Fintype ι]
    (e : (Fin 5 → ℕ) → (Fin 5 →₀ ℕ)) (key : (Fin 5 → ℕ) → ℕ)
    (f : ι → MvPolynomial (Fin 5) R) (idx : ι → Fin 5 → ℕ)
    (he : ∀ (v : Fin 5 → ℕ) (j : Fin 5), e v j = v j)
    (hcoeff : ∀ i, (f i).coeff (e (idx i)) ≠ 0)
    (hmem : ∀ i m, m ∈ (f i).support → key (fun j => m j) ≤ key (idx i))
    (hinj : Function.Injective fun i => key (idx i)) :
    LinearIndependent R f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀
  by_contra hg₀
  -- the support of `g`, i.e. the indices that really occur in the relation
  let T : Finset ι := Finset.univ.filter (fun i => g i ≠ 0)
  have hi₀T : i₀ ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ i₀, hg₀⟩
  -- an index in `T` on which `key ∘ idx` is maximal
  obtain ⟨j, hjT, hjmax⟩ := Finset.exists_max_image T (fun i => key (idx i)) ⟨i₀, hi₀T⟩
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hjT).2
  have hkeyj : (fun k : Fin 5 => (e (idx j)) k) = idx j := funext fun k => he (idx j) k
  -- reading off the coefficient of the monomial `e (idx j)`, only the term `i = j` survives
  have hcoeff_sum :
      (∑ i, g i • f i).coeff (e (idx j)) = g j * (f j).coeff (e (idx j)) := by
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.coeff_C_mul]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    intro b _ hbj
    by_cases hgb : g b = 0
    · simp [hgb]
    · have hbT : b ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hgb⟩
      have hble : key (idx b) ≤ key (idx j) := hjmax b hbT
      have hfb : (f b).coeff (e (idx j)) = 0 := by
        by_contra hne
        have hmem' : e (idx j) ∈ (f b).support := MvPolynomial.mem_support_iff.mpr hne
        have h1 : key (fun k => (e (idx j)) k) ≤ key (idx b) := hmem b (e (idx j)) hmem'
        rw [hkeyj] at h1
        exact hbj (hinj (le_antisymm hble h1))
      simp [hfb]
  have hz : (∑ i, g i • f i).coeff (e (idx j)) = 0 := by
    rw [hg]; simp
  have hprod : g j * (f j).coeff (e (idx j)) = 0 := by
    rw [← hcoeff_sum]; exact hz
  exact (mul_ne_zero hgj (hcoeff j)) hprod

end Work.MotK.TwRuling
