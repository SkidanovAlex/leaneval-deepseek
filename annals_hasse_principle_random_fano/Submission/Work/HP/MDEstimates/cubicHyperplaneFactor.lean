import Mathlib

/-!
# A cubic hypersurface containing a hyperplane has a linear factor

Let `B ∈ ℚ[X₀,…,X₄]` be a homogeneous polynomial of degree `3` and let `P ⊆ ℚ⁵` be a rational
hyperplane (a submodule of rank `4`).  If `B` vanishes at every point of `P`, then the linear form
of `P` divides `B`: there is a linear form `ℓ` (homogeneous of degree `1`) with `ℓ ∣ B`.

## The argument

The statement holds for a homogeneous form of *any* degree (homogeneity is not used): if `f` is a
nonzero linear functional vanishing on `P`, then `P ⊆ ker f` and both have rank `4`, so
`P = ker f`.  Write `L = ∑ᵢ f(eᵢ) Xᵢ` for the linear form of `f`, choose a coordinate `j` with
`f(e_j) ≠ 0` and substitute

  `X_j ↦ M := X_j - a⁻¹ L`,   `X_i ↦ X_i` `(i ≠ j)`,   where `a = f(e_j)`,

i.e. apply the `ℚ`-algebra endomorphism `ψ = aeval g`, `g i = if i = j then M else Xᵢ`, of
`ℚ[X₀,…,X₄]`.  Polynomials of the form `P(X₀,…,X_{j-1}, M, X_{j+1},…,X₄)` are exactly the
"restrictions of `P` to the hyperplane `L = 0`", so `ψ B = 0`: indeed, for every point `x` the
point `y` with `y_i = x_i` (`i ≠ j`) and `y_j = x_j - a⁻¹ f x` satisfies `f y = 0`, hence
`y ∈ ker f = P`, hence `B y = 0` (`B` vanishes on `P`).

On the other hand `ψ(Xᵢ) - Xᵢ ∈ (L)` for every `i` (for `i = j` this is `-(a⁻¹ L)`, otherwise it
is `0`), so by induction on the polynomial `ψ P - P ∈ (L)` for every `P`; with `ψ B = 0` this
gives `B ∈ (L)`, i.e. `L ∣ B`.

The two ingredients are `MvPolynomial.funext` (a polynomial over the infinite field `ℚ` is
determined by its values) and the ideal-membership induction `aeval_sub_mem_span` below.
-/

set_option autoImplicit false

namespace Work.HP.MDEstimates

open MvPolynomial

noncomputable section

/-- The linear form `∑ i, C (φ eᵢ) * Xᵢ` attached to a linear functional `φ` on `ℚ⁵`. -/
private def linFormOf (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) : MvPolynomial (Fin 5) ℚ :=
  ∑ i, C (φ (Pi.single i (1 : ℚ))) * X i

/-- `linFormOf φ` really is the linear form attached to `φ`. -/
private lemma eval_linFormOf (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (v : Fin 5 → ℚ) :
    MvPolynomial.eval v (linFormOf φ) = φ v := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℚ) : Fin 5 → ℚ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  rw [linFormOf, map_sum]
  simp only [map_mul, eval_C, eval_X]
  conv_rhs => rw [hv, map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `linFormOf φ` is homogeneous of degree `1`. -/
private lemma isHomogeneous_linFormOf (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) :
    (linFormOf φ).IsHomogeneous 1 := by
  rw [linFormOf]
  exact MvPolynomial.IsHomogeneous.sum _ _ 1 (fun i _ => isHomogeneous_C_mul_X _ i)

/-- If the substitution `Xᵢ ↦ gᵢ` moves every variable into the ideal `I` (`gᵢ - Xᵢ ∈ I`), then it
moves every polynomial into `I` modulo that polynomial: `aeval g P - P ∈ I`. -/
private lemma aeval_sub_mem_span {I : Ideal (MvPolynomial (Fin 5) ℚ)}
    {g : Fin 5 → MvPolynomial (Fin 5) ℚ} (hg : ∀ i, g i - X i ∈ I)
    (p : MvPolynomial (Fin 5) ℚ) : MvPolynomial.aeval g p - p ∈ I := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      have h : MvPolynomial.aeval g (p + q) - (p + q)
          = (MvPolynomial.aeval g p - p) + (MvPolynomial.aeval g q - q) := by
        rw [map_add]; ring
      rw [h]; exact I.add_mem hp hq
  | mul_X p j hp =>
      have h : MvPolynomial.aeval g (p * X j) - p * X j
          = (MvPolynomial.aeval g p - p) * g j + p * (g j - X j) := by
        simp only [map_mul, MvPolynomial.aeval_X]; ring
      rw [h]
      exact I.add_mem (I.mul_mem_right (g j) hp) (I.mul_mem_left p (hg j))

/-- **A cubic hypersurface containing a hyperplane has a linear factor.**  A homogeneous cubic
`B ∈ ℚ[X₀,…,X₄]` that vanishes on a rational hyperplane `P ⊆ ℚ⁵` is divisible by the linear form
of that hyperplane. -/
theorem cubicHyperplaneFactor (B : MvPolynomial (Fin 5) ℚ) (hB : B.IsHomogeneous 3)
    (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P = 4)
    (hvan : ∀ v ∈ P, MvPolynomial.eval v B = 0) :
    ∃ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 ∧ ℓ ∣ B := by
  -- Homogeneity of `B` of degree `3` is not used below: the argument works for an arbitrary
  -- polynomial that vanishes on the hyperplane (the hypothesis is recorded here for clarity).
  have _hBdeg3 : B.IsHomogeneous 3 := hB
  -- `P` is a proper subspace
  have hlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have htop' : Module.finrank ℚ P = Module.finrank ℚ (Fin 5 → ℚ) := by
      rw [htop]; exact finrank_top ℚ (Fin 5 → ℚ)
    rw [Module.finrank_fin_fun ℚ, hP] at htop'
    omega
  -- a nonzero linear functional vanishing on `P`
  obtain ⟨f, hfne, hfle⟩ := Submodule.exists_le_ker_of_lt_top P hlt
  have hker : f.ker = P := by
    have hne_top : f.ker ≠ ⊤ := fun h => hfne ((LinearMap.ker_eq_top).mp h)
    have hlt2 : f.ker < ⊤ := lt_top_iff_ne_top.mpr hne_top
    have hfr : Module.finrank ℚ f.ker ≤ 4 := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt2
      rw [finrank_top ℚ (Fin 5 → ℚ), Module.finrank_fin_fun ℚ] at h
      omega
    exact (Submodule.eq_of_le_of_finrank_le hfle (by rw [hP]; exact hfr)).symm
  -- a coordinate direction on which `f` does not vanish
  obtain ⟨j, hj⟩ : ∃ j : Fin 5, f (Pi.single j (1 : ℚ)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfne (LinearMap.ext fun y => by
      have hy : y = ∑ i, y i • (Pi.single i (1 : ℚ) : Fin 5 → ℚ) := by
        ext k; simp [Pi.single_apply, Finset.sum_apply]
      rw [hy, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_smul, h i, smul_zero])
  set a : ℚ := f (Pi.single j (1 : ℚ)) with ha
  have ha0 : a ≠ 0 := hj
  -- the linear form of the hyperplane
  set L : MvPolynomial (Fin 5) ℚ := linFormOf f with hL
  have hLev : ∀ v : Fin 5 → ℚ, MvPolynomial.eval v L = f v := fun v => by
    rw [hL]; exact eval_linFormOf f v
  -- the substitution `X j ↦ M = X j - a⁻¹ L`
  set M : MvPolynomial (Fin 5) ℚ := X j - C a⁻¹ * L with hM
  have hMeval : ∀ x : Fin 5 → ℚ, MvPolynomial.eval x M = x j - a⁻¹ * f x := by
    intro x
    rw [hM]
    simp only [eval_sub, eval_mul, eval_C, eval_X, hLev]
  set g : Fin 5 → MvPolynomial (Fin 5) ℚ :=
    Function.update (fun i => (X i : MvPolynomial (Fin 5) ℚ)) j M with hg
  -- the value of `g i` at a point
  have hval : ∀ (x : Fin 5 → ℚ) (i : Fin 5),
      MvPolynomial.eval x (g i)
        = x i - (a⁻¹ * f x) * (Pi.single j (1 : ℚ) : Fin 5 → ℚ) i := by
    intro x i
    by_cases hi : i = j
    · rw [hi, hg, Function.update_self, hMeval, Pi.single_eq_same]
      ring
    · rw [hg, Function.update_of_ne hi, eval_X, Pi.single_eq_of_ne hi]
      ring
  -- evaluating a substitution is the same as evaluating the substitution map
  have hmain : ∀ x : Fin 5 → ℚ,
      MvPolynomial.eval x (MvPolynomial.aeval g B)
        = MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) B := by
    intro x
    rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
  -- the substituted point always lies in `ker f = P`
  have hfzero : ∀ x : Fin 5 → ℚ, f (fun i => MvPolynomial.eval x (g i)) = 0 := by
    intro x
    have hyx : (fun i => MvPolynomial.eval x (g i))
        = x - (a⁻¹ * f x) • (Pi.single j (1 : ℚ) : Fin 5 → ℚ) := by
      funext i
      rw [hval x i, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hyx, map_sub, map_smul, smul_eq_mul, ← ha]
    have h1 : (a⁻¹ * f x) * a = f x := by
      rw [mul_comm a⁻¹ (f x), mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [h1, sub_self]
  -- hence the substituted cubic vanishes identically
  have hpsi : MvPolynomial.aeval g B = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [hmain x, map_zero]
    exact hvan _ (by rw [← hker, LinearMap.mem_ker]; exact hfzero x)
  -- and the substitution moves every polynomial into `(L)` modulo itself
  have hIn : MvPolynomial.aeval g B - B ∈ Ideal.span ({L} : Set (MvPolynomial (Fin 5) ℚ)) := by
    apply aeval_sub_mem_span
    intro i
    by_cases hi : i = j
    · rw [hi, hg, Function.update_self]
      have he : M - X j = -(C a⁻¹ * L) := by rw [hM]; ring
      rw [he]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rw [hg, Function.update_of_ne hi, sub_self]
      exact Ideal.zero_mem _
  have hBmem : B ∈ Ideal.span ({L} : Set (MvPolynomial (Fin 5) ℚ)) := by
    have h := hIn
    rw [hpsi, zero_sub] at h
    simpa using neg_mem h
  exact ⟨L, isHomogeneous_linFormOf f, Ideal.mem_span_singleton.mp hBmem⟩

end

end Work.HP.MDEstimates
