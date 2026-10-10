import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CKLink6

open MvPolynomial

/-- Over a field `𝕜`, every maximal ideal of `𝕜[X₁,…,Xₙ]` has height `n`.

This is the equidimensionality of a polynomial ring over a field. It is proved by induction on
`n`, using `Polynomial.height_eq_height_add_one` (the additivity of height in the polynomial
extension) together with the fact that, `𝕜[X₁,…,Xₙ]` being Jacobson, the contraction of a maximal
ideal of `𝕜[X₁,…,Xₙ₊₁]` is again maximal (`Polynomial.isMaximal_comap_C_of_isJacobsonRing`). -/
theorem height_eq_of_isMaximal (𝕜 : Type) [Field 𝕜] :
    ∀ (n : ℕ) (𝔪 : Ideal (MvPolynomial (Fin n) 𝕜)), 𝔪.IsMaximal → 𝔪.height = (n : ℕ∞) := by
  intro n
  induction n with
  | zero =>
    intro 𝔪 h𝔪
    have hdim : ringKrullDim (MvPolynomial (Fin 0) 𝕜) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
      simp
    have hle := Ideal.height_le_ringKrullDim_of_ne_top h𝔪.ne_top
    rw [hdim] at hle
    have hle' : 𝔪.height ≤ (0 : ℕ∞) := by simpa using hle
    exact le_antisymm hle' (by simp)
  | succ n ih =>
    intro 𝔪 h𝔪
    let e := MvPolynomial.finSuccEquiv 𝕜 n
    set M : Ideal (Polynomial (MvPolynomial (Fin n) 𝕜)) := Ideal.map e.toRingEquiv 𝔪 with hMdef
    have hM : M.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have hLO : M.LiesOver (M.comap Polynomial.C) :=
      ⟨by rw [Ideal.under, Polynomial.algebraMap_eq]⟩
    have hp : (M.comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have hp' : (M.comap Polynomial.C).height = (n : ℕ∞) := ih _ hp
    have hPM : M.height = (M.comap Polynomial.C).height + 1 := by
      rw [Polynomial.height_eq_height_add_one (M.comap Polynomial.C) M]
    rw [← RingEquiv.height_map e.toRingEquiv 𝔪]
    change M.height = ((n+1 : ℕ) : ℕ∞)
    rw [hPM, hp']
    norm_num

/-- Over a field, every non-unit polynomial in `n ≥ 1` variables lies in a maximal ideal of
height `n` (the maximal possible, since `ringKrullDim 𝕜[X₁,…,Xₙ] = n`). -/
theorem exists_maximalIdeal_height_eq_of_ne_zero (𝕜 : Type) [Field 𝕜] {n : ℕ} (hn : 0 < n)
    (f : MvPolynomial (Fin n) 𝕜) (hf : ¬ IsUnit f) :
    ∃ 𝔪 : Ideal (MvPolynomial (Fin n) 𝕜),
      𝔪.IsMaximal ∧ 𝔪.height = (n : ℕ∞) ∧ f ∈ 𝔪 := by
  have _hn : 0 < n := hn
  have hne : Ideal.span {f} ≠ ⊤ := fun h => hf (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨𝔪, h𝔪max, hle⟩ := Ideal.exists_le_maximal (Ideal.span {f}) hne
  exact ⟨𝔪, h𝔪max, height_eq_of_isMaximal 𝕜 n 𝔪 h𝔪max,
    hle (Ideal.mem_span_singleton_self f)⟩

end Work.CKLink6
