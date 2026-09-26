import Mathlib
import Submission.Work.Drive.N2.intervalIntegral_contDiff

/-!
# The two-dimensional Hadamard lemma at a critical point

If `g : EuclideanSpace ℝ (Fin 2) → ℝ` is smooth and `fderiv ℝ g x₀ = 0`, then there are smooth
functions `h i j` such that

* `g x = g x₀ + ∑ i, ∑ j, (x i - x₀ i) * (x j - x₀ j) * h i j x`, and
* the quadratic form of `h · · x₀` is half the second derivative of `g` at `x₀` (and `h` is
  symmetric in `i, j`).

The construction is the usual integral formula
`h i j x = ∫ t in 0..1, (1-t) * (fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) eᵢ eⱼ`.
-/

namespace Work.Drive.N2

open scoped ContDiff
open MeasureTheory

noncomputable section

/-- The `i`-th standard basis vector of `EuclideanSpace ℝ (Fin 2)`. -/
private def eb (i : Fin 2) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (Pi.single i 1)

private lemma eb_basis (u : EuclideanSpace ℝ (Fin 2)) : ∑ i, u i • eb i = u := by
  ext j; fin_cases j <;> simp [eb]

/-- A continuous linear functional is the sum of its values against the standard basis. -/
private lemma clm_functional_expand (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin 2)) : L v = ∑ j, (v j) * (L (eb j)) := by
  conv_lhs => rw [← eb_basis v]
  rw [map_sum]
  simp [map_smul, smul_eq_mul]

/-- Expansion of the quadratic form of a bilinear form in the standard basis. -/
private lemma fderiv2_expand
    (G : EuclideanSpace ℝ (Fin 2) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))
    (u : EuclideanSpace ℝ (Fin 2)) :
    G u u = ∑ i, ∑ j, (u i) * (u j) * (G (eb i) (eb j)) := by
  rw [clm_functional_expand (G u) u]
  have key : ∀ j, (G u) (eb j) = ∑ i, (u i) * (G (eb i) (eb j)) := by
    intro j
    simpa [ContinuousLinearMap.comp_apply] using
      clm_functional_expand ((ContinuousLinearMap.apply ℝ ℝ (eb j)).comp G) u
  simp_rw [key]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The second derivative of a smooth function is symmetric. -/
private lemma snd_fderiv_symm (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (y : EuclideanSpace ℝ (Fin 2)) (i j : Fin 2) :
    (fderiv ℝ (fderiv ℝ g) y) (eb i) (eb j) = (fderiv ℝ (fderiv ℝ g) y) (eb j) (eb i) := by
  exact (hg.contDiffAt).isSymmSndFDerivAt (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) (eb i) (eb j)

/-- Taylor's theorem with integral remainder, in the form used for the Hadamard lemma:
at a critical point the first order term drops out and
`g x - g x₀ = ∫ t in 0..1, (1-t) * D²g(x₀ + t(x-x₀)) (x-x₀) (x-x₀)`. -/
private lemma hadamard_taylor (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x₀ x : EuclideanSpace ℝ (Fin 2))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hcrit : fderiv ℝ g x₀ = 0) :
    g x = g x₀ +
      ∫ t in (0:ℝ)..1,
        (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (x - x₀) (x - x₀)) := by
  have hmain := map_add_eq_sum_add_integral_iteratedFDeriv (f := g)
    (x := x₀) (y := x - x₀) (n := 1) (fun t _ht => (hg.contDiffAt).of_le (by
      exact WithTop.coe_le_coe.mpr le_top))
  rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedFDeriv_zero_apply,
    iteratedFDeriv_one_apply] at hmain
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, mul_zero,
    add_zero, pow_one, smul_eq_mul] at hmain
  rw [hcrit] at hmain
  simp only [zero_apply, add_zero] at hmain
  have key : ∀ t : ℝ, (iteratedFDeriv ℝ 2 g (x₀ + t • (x - x₀))) (fun _ => x - x₀)
      = ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (x - x₀)) (x - x₀) := by
    intro t; rw [iteratedFDeriv_two_apply]
  simp_rw [key] at hmain
  rw [show x₀ + (x - x₀) = x from by abel] at hmain
  exact hmain

/-- The Hadamard integral expanded in the standard basis. -/
private lemma hadamard_integral_expand (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x₀ x : EuclideanSpace ℝ (Fin 2)) :
    (∫ t in (0:ℝ)..1,
        (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (x - x₀) (x - x₀)))
      = ∑ i, ∑ j, ((x - x₀) i) * ((x - x₀) j) *
          (∫ t in (0:ℝ)..1,
            (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i) (eb j))) := by
  have hcont : ∀ a b : EuclideanSpace ℝ (Fin 2),
      Continuous (fun t : ℝ => ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) a) b) := by
    intro a b
    have h1 : ContDiff ℝ (1:ℕ∞ω) (fderiv ℝ (fderiv ℝ g)) := by
      have h3 : ContDiff ℝ (3:ℕ∞ω) g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
      have h2 : ContDiff ℝ (2:ℕ∞ω) (fderiv ℝ g) := ContDiff.fderiv_right h3 (by norm_num)
      exact ContDiff.fderiv_right h2 (by norm_num)
    have h1c : Continuous (fderiv ℝ (fderiv ℝ g)) := h1.continuous
    have hy : Continuous (fun t : ℝ => x₀ + t • (x - x₀)) := by fun_prop
    exact ((h1c.comp hy).clm_apply continuous_const).clm_apply continuous_const
  have hone : Continuous (fun t : ℝ => (1:ℝ) - t) := continuous_const.sub continuous_id
  have hbase : ∀ a b : EuclideanSpace ℝ (Fin 2), Continuous
      (fun t : ℝ => (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) a) b) :=
    fun a b => hone.mul (hcont a b)
  have hm : ∀ (c d : ℝ) (a b : EuclideanSpace ℝ (Fin 2)), Continuous
      (fun t : ℝ => (c * d) * ((1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) a) b)) :=
    fun c d a b => ((continuous_const : Continuous fun _ : ℝ => c).mul
      (continuous_const : Continuous fun _ : ℝ => d)).mul (hbase a b)
  have hpt : ∀ t : ℝ,
      (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (x - x₀) (x - x₀))
      = ∑ i, ∑ j, ((x - x₀) i) * ((x - x₀) j) *
          ((1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i) (eb j))) := by
    intro t
    rw [fderiv2_expand (fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (x - x₀)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finsetSum (f := fun i (t:ℝ) => ∑ j, ((x - x₀) i) * ((x - x₀) j) *
        ((1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i) (eb j))))]
  · apply Finset.sum_congr rfl; intro i _
    rw [intervalIntegral.integral_finsetSum (f := fun j (t:ℝ) => ((x - x₀) i) * ((x - x₀) j) *
        ((1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i) (eb j))))]
    · apply Finset.sum_congr rfl; intro j _
      rw [intervalIntegral.integral_const_mul]
    · intro j _
      exact (hm ((x - x₀) i) ((x - x₀) j) (eb i) (eb j)).intervalIntegrable _ _
  · intro i _
    exact (continuous_finsetSum Finset.univ
      (fun j _ => hm ((x - x₀) i) ((x - x₀) j) (eb i) (eb j))).intervalIntegrable _ _

/-- At `x₀` the Hadamard integral is half the second derivative. -/
private lemma hadamard_at_x₀ (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin 2)) (i j : Fin 2) :
    (∫ t in (0:ℝ)..1,
        (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x₀ - x₀))) (eb i) (eb j)))
      = (1/2) * ((fderiv ℝ (fderiv ℝ g) x₀) (eb i) (eb j)) := by
  simp only [sub_self, smul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  have h : (∫ t in (0:ℝ)..1, (1-t)) = 1/2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, integral_id]
    norm_num
  rw [h]

/-- **Hadamard's lemma in dimension two**, at a critical point. -/
theorem hadamard2 (g : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hcrit : fderiv ℝ g x₀ = 0) :
    ∃ h : Fin 2 → Fin 2 → (EuclideanSpace ℝ (Fin 2) → ℝ),
      (∀ i j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i j)) ∧
      (∀ i j x, h i j x = h j i x) ∧
      (∀ x, g x = g x₀ + ∑ i, ∑ j, (x i - x₀ i) * (x j - x₀ j) * h i j x) ∧
      (∀ v : EuclideanSpace ℝ (Fin 2),
        ∑ i, ∑ j, v i * v j * h i j x₀
          = (1 / 2) * (fderiv ℝ (fderiv ℝ g) x₀ v v)) := by
  refine ⟨fun i j x => ∫ t in (0:ℝ)..1,
      (1-t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i) (eb j)), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact intervalIntegral_contDiff
      (f := fun p : EuclideanSpace ℝ (Fin 2) × ℝ =>
        (1 - p.2) * ((fderiv ℝ (fderiv ℝ g) (x₀ + p.2 • (p.1 - x₀))) (eb i) (eb j)))
      (a := (0:ℝ)) (b := 1) (by simp only [eb]; fun_prop)
  · intro i j x
    apply intervalIntegral.integral_congr
    intro t _
    change (1 - t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb i)) (eb j)
      = (1 - t) * ((fderiv ℝ (fderiv ℝ g) (x₀ + t • (x - x₀))) (eb j)) (eb i)
    rw [snd_fderiv_symm g hg (x₀ + t • (x - x₀)) i j]
  · intro x
    rw [hadamard_taylor g x₀ x hg hcrit, hadamard_integral_expand g hg x₀ x]
    simp only [PiLp.sub_apply]
  · intro v
    simp only [hadamard_at_x₀ g x₀]
    rw [fderiv2_expand (fderiv ℝ (fderiv ℝ g) x₀) v]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring

end

end Work.Drive.N2
