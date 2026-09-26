import Mathlib

/-!
# `(f'.prod g')` is invertible when `g' ≠ 0` and `f'` is not a multiple of `g'`

Let `V = ℝ × ℝ`, which is a two-dimensional real vector space, and let
`f' g' : V →L[ℝ] ℝ` be linear functionals with `g' ≠ 0` and `f' ∉ ℝ • g'`.  Then the
continuous linear map
`x ↦ (f' x, g' x) : V →L[ℝ] V`
is invertible (a continuous linear equivalence).

This is the two-dimensional fact that two linearly independent elements of the dual of a
two-dimensional space form a basis of the dual, so the corresponding "evaluation" map is an
isomorphism.  The proof here is an explicit computation with the standard basis `(1,0)`, `(0,1)`:

* from `g' ≠ 0` the pair of values `(g'(1,0), g'(0,1))` is nonzero (a functional vanishing on both
  standard basis vectors is zero);
* if `(f'(1,0), f'(0,1))` and `(g'(1,0), g'(0,1))` were proportional, then `f' = t • g'` for some
  `t`, contradicting the hypothesis;
* hence the `2 × 2` system `f'(p,q) = 0`, `g'(p,q) = 0` has only the trivial solution: the two
  equations give `(a d - b c) p = 0` and `(b c - a d) q = 0` with `a d - b c ≠ 0`, so `p = q = 0`;
* thus `f'.prod g'` is injective, and an injective endomorphism of the finite-dimensional space
  `ℝ × ℝ` is a linear equivalence, which upgrades to a *continuous* one (`LinearEquiv.toContinuousLinearEquiv`).
-/

namespace Work.Drive.Mono

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the two standard
basis vectors: `φ u = u.1 * φ (1,0) + u.2 * φ (0,1)`. -/
private lemma apply_eq (φ : (ℝ × ℝ) →L[ℝ] ℝ) (u : ℝ × ℝ) :
    φ u = u.1 * φ (1, 0) + u.2 * φ (0, 1) := by
  have hu : u = u.1 • ((1,0):ℝ×ℝ) + u.2 • ((0,1):ℝ×ℝ) := by ext <;> simp
  conv_lhs => rw [hu]
  rw [map_add, map_smul, map_smul]
  simp

/-- Two continuous linear functionals on `ℝ × ℝ` agreeing on the two standard basis vectors are
equal. -/
private lemma ext_of_values (φ ψ : (ℝ × ℝ) →L[ℝ] ℝ)
    (h1 : φ (1,0) = ψ (1,0)) (h2 : φ (0,1) = ψ (0,1)) : φ = ψ := by
  apply ContinuousLinearMap.ext
  intro u
  rw [apply_eq φ u, apply_eq ψ u, h1, h2]

/-- If `(g'(1,0), g'(0,1)) ≠ 0` and the values of `f'` and `g'` on the standard basis are
proportional (zero determinant), then `f'` is a scalar multiple of `g'`. -/
private lemma exists_smul_of_values (f' g' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hcd : (g' (1,0), g' (0,1)) ≠ 0)
    (hdet : f' (1,0) * g' (0,1) = f' (0,1) * g' (1,0)) :
    ∃ t : ℝ, f' = t • g' := by
  have hcd' : g' (1,0) ≠ 0 ∨ g' (0,1) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hcd (by simp [hh.1, hh.2])
  rcases hcd' with hc | hd
  · refine ⟨f' (1,0) / g' (1,0), ?_⟩
    apply ext_of_values
    · show f' (1,0) = ((f' (1,0) / g' (1,0)) • g') (1,0)
      rw [smul_apply, smul_eq_mul]
      field_simp
    · show f' (0,1) = ((f' (1,0) / g' (1,0)) • g') (0,1)
      rw [smul_apply, smul_eq_mul]
      field_simp
      linarith [hdet]
  · refine ⟨f' (0,1) / g' (0,1), ?_⟩
    apply ext_of_values
    · show f' (1,0) = ((f' (0,1) / g' (0,1)) • g') (1,0)
      rw [smul_apply, smul_eq_mul]
      field_simp
      linarith [hdet]
    · show f' (0,1) = ((f' (0,1) / g' (0,1)) • g') (0,1)
      rw [smul_apply, smul_eq_mul]
      field_simp

theorem ProdInvertible_holds {f' g' : (ℝ × ℝ) →L[ℝ] ℝ} (hg : g' ≠ 0)
    (h : ∀ t : ℝ, f' ≠ t • g') : (f'.prod g').IsInvertible := by
  -- the values of `g'` on the standard basis are not both zero
  have hcd : (g' (1,0), g' (0,1)) ≠ 0 := by
    intro hcd0
    apply hg
    apply ext_of_values
    · simpa using congrArg Prod.fst hcd0
    · simpa using congrArg Prod.snd hcd0
  -- the two defining equations of the kernel of `f'.prod g'` have only the trivial solution
  have hkey : ∀ p q : ℝ, f' (p,q) = 0 → g' (p,q) = 0 → p = 0 ∧ q = 0 := by
    intro p q hf hgv
    have hfa : f' (1,0) * p + f' (0,1) * q = 0 := by
      have := hf
      rw [apply_eq] at this
      simpa [mul_comm] using this
    have hga : g' (1,0) * p + g' (0,1) * q = 0 := by
      have := hgv
      rw [apply_eq] at this
      simpa [mul_comm] using this
    -- eliminate `q`
    have e1 : (f' (1,0) * g' (0,1) - f' (0,1) * g' (1,0)) * p = 0 := by
      have key : g' (0,1) * (f' (1,0) * p + f' (0,1) * q)
          - f' (0,1) * (g' (1,0) * p + g' (0,1) * q)
          = (f' (1,0) * g' (0,1) - f' (0,1) * g' (1,0)) * p := by ring
      rw [hfa, hga] at key
      linarith [key]
    -- eliminate `p`
    have e2 : (f' (0,1) * g' (1,0) - f' (1,0) * g' (0,1)) * q = 0 := by
      have key : g' (1,0) * (f' (1,0) * p + f' (0,1) * q)
          - f' (1,0) * (g' (1,0) * p + g' (0,1) * q)
          = (f' (0,1) * g' (1,0) - f' (1,0) * g' (0,1)) * q := by ring
      rw [hfa, hga] at key
      linarith [key]
    by_cases hA : f' (1,0) * g' (0,1) - f' (0,1) * g' (1,0) = 0
    · -- the values are proportional, contradicting the hypothesis `h`
      have hdet : f' (1,0) * g' (0,1) = f' (0,1) * g' (1,0) := by linarith
      obtain ⟨t, ht⟩ := exists_smul_of_values f' g' hcd hdet
      exact absurd ht (h t)
    · have hp : p = 0 := (mul_eq_zero.mp e1).resolve_left hA
      have hnA : f' (0,1) * g' (1,0) - f' (1,0) * g' (0,1) ≠ 0 := by
        intro hh; exact hA (by linarith)
      have hq : q = 0 := (mul_eq_zero.mp e2).resolve_left hnA
      exact ⟨hp, hq⟩
  -- the kernel is trivial
  have hzero : ∀ w : ℝ × ℝ, f' w = 0 → g' w = 0 → w = 0 := by
    rintro ⟨p, q⟩ hf hgv
    obtain ⟨h1, h2⟩ := hkey p q hf hgv
    simp [h1, h2]
  -- hence `f'.prod g'` is injective
  have hinj : Function.Injective (f'.prod g') := by
    intro x y hxy
    have h0 : (f'.prod g') (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : f' (x - y) = 0 := by
      have := congrArg Prod.fst h0
      simpa [ContinuousLinearMap.prod_apply] using this
    have h2 : g' (x - y) = 0 := by
      have := congrArg Prod.snd h0
      simpa [ContinuousLinearMap.prod_apply] using this
    have := hzero (x - y) h1 h2
    exact sub_eq_zero.mp this
  -- an injective endomorphism of a finite-dimensional space is a continuous linear equivalence
  let L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := (f'.prod g').toLinearMap
  have hinjL : Function.Injective L := hinj
  refine ⟨(LinearEquiv.ofInjectiveEndo L hinjL).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp [L, LinearEquiv.ofInjectiveEndo]

end Work.Drive.Mono
