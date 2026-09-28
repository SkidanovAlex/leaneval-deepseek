import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs

namespace Work.HP.MDEstimates

noncomputable section

open MvPolynomial

/-!
# A quadratic form vanishing on a hyperplane is divisible by the linear form of the hyperplane

Let `Q` be a homogeneous polynomial of degree `2` in the five variables `X₀,…,X₄` over `ℚ`, and let
`P ⊆ ℚ^5` be a rational hyperplane (a submodule of dimension `4`) on which `Q` vanishes identically.
Then `Q` is divisible by the linear form defining `P`.

The proof is the one from the paper: if `f : ℚ^5 →ₗ ℚ` is a nonzero linear form with `ker f = P` and
`u` is a vector with `f u = 1`, then decomposition of `v` as `v = (v - f v • u) + (f v) • u` and the
polarisation identity `Q(x+y) = Q(x) + Q(y) + 2·polQ Q x y` for the homogeneous degree-`2` form `Q`
give, for all `v`,

  `Q v = (f v) * (2 * polQ Q v u - (f v) * Q u)`.

The right-hand factor is a rational linear form in `v`, so writing both linear forms as polynomials we
obtain `Q = ℓ * G` with `ℓ = linPoly f` the linear form attached to `f`; hence `ℓ ∣ Q`.

## Contents

* `existsPolarBilin_aux` : a homogeneous quadratic polynomial over `ℚ` has an associated symmetric
  bilinear form `B` with `B x x = eval x Q` (polarisation).
* `linPoly` and its API: the linear form `∑ i, C (φ eᵢ) * Xᵢ` attached to a linear functional `φ`.
* `hyperplaneFactor` : the requested statement.
-/

/-! ## Polarisation -/

/-- `polQ` is additive in the polynomial argument. -/
private lemma polQ_add (Q₁ Q₂ : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℚ) :
    polQ (Q₁ + Q₂) x y = polQ Q₁ x y + polQ Q₂ x y := by
  simp only [polQ, map_add]
  ring

/-- `polQ` is `ℚ`-homogeneous in the polynomial argument. -/
private lemma polQ_smul (c : ℚ) (Q : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℚ) :
    polQ (c • Q) x y = c * polQ Q x y := by
  simp only [polQ, smul_eq_C_mul, map_mul, eval_C]
  ring

/-- The polar form of the quadratic monomial `Xᵢ Xⱼ`. -/
private lemma polQ_X_mul_X (i j : Fin 5) (a b : Fin 5 → ℚ) :
    polQ (X i * X j) a b = (a i * b j + b i * a j) / 2 := by
  simp only [polQ, eval_mul, eval_X, Pi.add_apply]
  ring

/-- The set of polynomials whose polar form is symmetric bilinear. -/
private def Good (Q : MvPolynomial (Fin 5) ℚ) : Prop :=
  (∀ x x' y, polQ Q (x + x') y = polQ Q x y + polQ Q x' y) ∧
  (∀ (c : ℚ) x y, polQ Q (c • x) y = c * polQ Q x y) ∧
  (∀ x y, polQ Q x y = polQ Q y x) ∧
  (∀ x, polQ Q x x = MvPolynomial.eval x Q)

/-- **Polarisation.** A homogeneous polynomial of degree `2` in `5` variables over `ℚ` has an
associated symmetric bilinear form `B` with `B x x = eval x Q`. -/
private lemma existsPolarBilin_aux (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    ∃ B : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) →ₗ[ℚ] ℚ,
      (∀ x, B x x = MvPolynomial.eval x Q) ∧ (∀ x y, B x y = B y x) := by
  -- products of two linear forms span the homogeneous polynomials of degree `2`
  have hspan : MvPolynomial.homogeneousSubmodule (Fin 5) ℚ 2
      = Submodule.span ℚ (Set.range fun p : Fin 5 × Fin 5 =>
          (X p.1 * X p.2 : MvPolynomial (Fin 5) ℚ)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := Fin 5) ℚ 2,
      MvPolynomial.homogeneousSubmodule_one_eq_span_X, pow_two, Submodule.span_mul_span]
    congr 1
    ext z
    rw [Set.mem_mul]
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨X i, ⟨i, rfl⟩, X j, ⟨j, rfl⟩, rfl⟩
  have good_zero : Good 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro _ <;> simp [polQ]
  have good_add : ∀ Q₁ Q₂, Good Q₁ → Good Q₂ → Good (Q₁ + Q₂) := by
    intro Q₁ Q₂ h₁ h₂
    obtain ⟨a1, a2, a3, a4⟩ := h₁
    obtain ⟨b1, b2, b3, b4⟩ := h₂
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x x' y
      simp only [polQ_add]
      rw [a1 x x' y, b1 x x' y]
      ring
    · intro c x y
      simp only [polQ_add]
      rw [a2 c x y, b2 c x y]
      ring
    · intro x y
      simp only [polQ_add]
      rw [a3 x y, b3 x y]
    · intro x
      simp only [polQ_add]
      rw [a4 x, b4 x, map_add]
  have good_smul : ∀ (c : ℚ) Q, Good Q → Good (c • Q) := by
    intro c Q h
    obtain ⟨a1, a2, a3, a4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x x' y
      simp only [polQ_smul]
      rw [a1 x x' y]
      ring
    · intro d x y
      simp only [polQ_smul]
      rw [a2 d x y]
      ring
    · intro x y
      simp only [polQ_smul]
      rw [a3 x y]
    · intro x
      simp only [polQ_smul]
      rw [a4 x, smul_eq_C_mul, map_mul, eval_C]
  have good_gen : ∀ p : Fin 5 × Fin 5, Good (X p.1 * X p.2) := by
    intro p
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x x' y
      simp only [polQ_X_mul_X, Pi.add_apply]
      ring
    · intro c x y
      simp only [polQ_X_mul_X, Pi.smul_apply, smul_eq_mul]
      ring
    · intro x y
      simp only [polQ_X_mul_X]
      ring
    · intro x
      simp only [polQ_X_mul_X, eval_mul, eval_X]
      ring
  have hgood : Good Q := by
    have hQmem : Q ∈ MvPolynomial.homogeneousSubmodule (Fin 5) ℚ 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 Q).mpr hQ
    rw [hspan] at hQmem
    refine Submodule.span_induction (p := fun Q _ => Good Q) (fun z hz => ?_) good_zero
      (fun a b _ _ ha hb => good_add a b ha hb) (fun c a _ ha => good_smul c a ha) hQmem
    obtain ⟨p, rfl⟩ := hz
    exact good_gen p
  obtain ⟨h1, h2, h3, h4⟩ := hgood
  refine ⟨{ toFun := fun x => { toFun := fun y => polQ Q x y, map_add' := ?_, map_smul' := ?_ },
            map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro y y'
    rw [h3 x (y + y'), h1 y y' x, h3 y x, h3 y' x]
  · intro c y
    rw [h3 x (c • y), h2 c y x, h3 y x]
    rfl
  · intro x x'
    apply LinearMap.ext
    intro y
    exact h1 x x' y
  · intro c x
    apply LinearMap.ext
    intro y
    exact h2 c x y
  · intro x
    exact h4 x
  · intro x y
    exact h3 x y

/-! ## The linear form attached to a linear functional -/

/-- The linear form `∑ i, C (φ eᵢ) * Xᵢ` attached to the linear functional `φ`. -/
private def linPoly (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) : MvPolynomial (Fin 5) ℚ :=
  ∑ i, MvPolynomial.C (φ (Pi.single i (1 : ℚ))) * MvPolynomial.X i

private lemma eval_linPoly (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (v : Fin 5 → ℚ) :
    MvPolynomial.eval v (linPoly φ) = φ v := by
  have hv : v = ∑ i, v i • (Pi.single i (1 : ℚ) : Fin 5 → ℚ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  rw [linPoly, map_sum]
  simp only [map_mul, eval_C, eval_X]
  conv_rhs => rw [hv, map_sum]
  simp only [LinearMap.map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma isHomogeneous_linPoly (φ : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) :
    (linPoly φ).IsHomogeneous 1 := by
  rw [linPoly]
  exact MvPolynomial.IsHomogeneous.sum _ _ 1 (fun i _ => isHomogeneous_C_mul_X _ i)

/-! ## The main theorem -/

theorem hyperplaneFactor (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2)
    (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P = 4)
    (hvan : ∀ v ∈ P, MvPolynomial.eval v Q = 0) :
    ∃ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 ∧ ℓ ∣ Q := by
  -- a hyperplane is a proper submodule
  have hlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have htop' : Module.finrank ℚ P = Module.finrank ℚ (Fin 5 → ℚ) := by
      rw [htop]; exact finrank_top ℚ (Fin 5 → ℚ)
    rw [Module.finrank_fin_fun ℚ, hP] at htop'
    omega
  -- a nonzero linear functional whose kernel is `P`
  obtain ⟨f, hfne, hfle⟩ := Submodule.exists_le_ker_of_lt_top P hlt
  have hker : f.ker = P := by
    have hne_top : f.ker ≠ ⊤ := fun h => hfne ((LinearMap.ker_eq_top).mp h)
    have hlt2 : f.ker < ⊤ := lt_top_iff_ne_top.mpr hne_top
    have hfr : Module.finrank ℚ f.ker ≤ 4 := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt2
      rw [finrank_top ℚ (Fin 5 → ℚ), Module.finrank_fin_fun ℚ] at h
      omega
    exact (Submodule.eq_of_le_of_finrank_le hfle (by rw [hP]; exact hfr)).symm
  -- the polar form of `Q`
  obtain ⟨B, hBdiag, hBsymm⟩ := existsPolarBilin_aux Q hQ
  -- a vector with `f u = 1`
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hfne (LinearMap.ext fun y => by simpa using h y)
  set u : Fin 5 → ℚ := (f x)⁻¹ • x with hu_def
  have hu : f u = 1 := by
    rw [hu_def, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  -- the cofactor functional: `v ↦ 2 * B u v - (eval u Q) * f v`
  let g : (Fin 5 → ℚ) →ₗ[ℚ] ℚ := (2 : ℚ) • (B u) - (MvPolynomial.eval u Q) • f
  -- the key identity `Q v = (f v) * (g v)`
  have hkey : ∀ v : Fin 5 → ℚ, MvPolynomial.eval v Q = f v * g v := by
    intro v
    set t : ℚ := f v with ht
    set p : Fin 5 → ℚ := v - t • u with hp_def
    have hp_ker : p ∈ f.ker := by
      rw [LinearMap.mem_ker, hp_def, map_sub, map_smul, smul_eq_mul, ht, hu, mul_one, sub_self]
    have hpP : p ∈ P := hker ▸ hp_ker
    have hQp : MvPolynomial.eval p Q = 0 := hvan p hpP
    have hvsplit : v = p + t • u := by rw [hp_def]; abel
    have hBpp : B p p = 0 := by rw [hBdiag p, hQp]
    have hBpu : B p u = B v u - t * B u u := by
      simp only [hp_def, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
    have hBup : B u p = B v u - t * B u u := by
      rw [hBsymm u p]; exact hBpu
    have hBvv : B v v = t * (2 * B u v - MvPolynomial.eval u Q * t) := by
      rw [hvsplit]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hBpp, hBpu, hBup, hBdiag u, hBsymm v u]
      ring
    have hgv : g v = 2 * B u v - MvPolynomial.eval u Q * t := by
      simp only [g, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ht]
    rw [← hBdiag v, hBvv, hgv, ht]
  -- assemble: `Q = linPoly f * linPoly g` by function extensionality
  refine ⟨linPoly f, isHomogeneous_linPoly f, linPoly g, ?_⟩
  have hhom : (linPoly f * linPoly g).IsHomogeneous 2 := by
    simpa using (isHomogeneous_linPoly f).mul (isHomogeneous_linPoly g)
  refine MvPolynomial.IsHomogeneous.funext hQ hhom (fun v => ?_)
  rw [MvPolynomial.eval_mul, eval_linPoly, eval_linPoly]
  exact hkey v

end

end Work.HP.MDEstimates
