import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.one.Defs

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe.ddiSharp.one

private theorem rowGram_finite_step_gen {ι : Type} [DecidableEq ι] {Z : Type} [Fintype Z]
    [Nonempty Z] (X : Finset ℤ) (G : Z → ℤ → ℂ) (a : ℤ) (N : Finset ι) (Q : ι → ℤ)
    (Θ : ι → ℝ) :
    (∑ i ∈ N, ‖∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i))‖ ^ 2) ^ 2
      ≤ (∑ i ∈ N, ∑ j ∈ N, ‖∑ x ∈ X,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i) * star (G z (x + Q j)))‖ ^ 2)
        * (∑ x ∈ X, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2) ^ 2 := by
  classical
  have hM0 : (Fintype.card Z : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card Z := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast (ne_of_gt hpos)
  let S : Finset Z := Finset.univ
  let gw : Z × ℤ → ℂ := fun r => star (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (r.2 + a))
  let gV : ι → Z × ℤ → ℂ := fun i r =>
      Complex.exp (-(2 * Real.pi * Complex.I * (Θ i : ℂ) * (r.2 : ℂ))) *
        star (G r.1 (r.2 + Q i))
  let w : EuclideanSpace ℂ ↥(S ×ˢ X) := WithLp.toLp 2 (fun p => gw p.1)
  let V : ι → EuclideanSpace ℂ ↥(S ×ˢ X) := fun i => WithLp.toLp 2 (fun p => gV i p.1)
  let L : ι → ℂ := fun i => ∑ x ∈ X,
        Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + Q i))
  let Pq : ι → ι → ℂ := fun i j => ∑ x ∈ X,
        Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + Q i) * star (G z (x + Q j)))
  let C : ℝ := ∑ x ∈ X, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + a)‖ ^ 2
  let A : ℝ := ∑ i ∈ N, ‖L i‖ ^ 2
  let P : ℝ := ∑ i ∈ N, ∑ j ∈ N, ‖Pq i j‖ ^ 2
  change A ^ 2 ≤ P * C ^ 2
  have star_exp_neg : ∀ (θ : ℝ) (x : ℤ),
      star (Complex.exp (-(2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)))) =
        Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)) := by
    intro θ x
    have key : star (-(2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))) =
        2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ) := by
      simp [Complex.conj_ofReal, Complex.conj_I]
    calc star (Complex.exp (-(2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ))))
        = Complex.exp (star (-(2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)))) :=
          (Complex.exp_conj _).symm
      _ = Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ) * (x : ℂ)) := by rw [key]
  have h_exp_mul : ∀ (θ₁ θ₂ : ℝ) (x : ℤ),
      Complex.exp (-(2 * Real.pi * Complex.I * (θ₂ : ℂ) * (x : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * (θ₁ : ℂ) * (x : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((θ₁ : ℂ) - (θ₂ : ℂ)) * (x : ℂ)) := by
    intro θ₁ θ₂ x
    rw [← Complex.exp_add]
    congr 1
    ring
  have h1 : ∀ i : ι, inner ℂ (V i) w = (Fintype.card Z : ℂ) * L i := by
    intro i
    have hinner : inner ℂ (V i) w = ∑ p : ↥(S ×ˢ X), gw p.1 * star (gV i p.1) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, Complex.star_def]
      dsimp only [w, V]
    have hconv : (∑ p : ↥(S ×ˢ X), gw p.1 * star (gV i p.1))
        = ∑ z ∈ S, ∑ x ∈ X, gw (z,x) * star (gV i (z,x)) := by
      rw [Finset.sum_coe_sort (S ×ˢ X) (fun r : Z × ℤ => gw r * star (gV i r))]
      rw [Finset.sum_product]
    rw [hinner, hconv]
    have stepA : (∑ z ∈ S, ∑ x ∈ X, gw (z, x) * star (gV i (z, x)))
        = ∑ z ∈ S, ∑ x ∈ X,
            star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
              (Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
                G z (x + Q i)) := by
      apply Finset.sum_congr rfl; intro z hz
      apply Finset.sum_congr rfl; intro x hx
      simp only [gw, gV, star_mul, star_star, star_exp_neg]
      ring
    rw [stepA]
    have stepB : (∑ z ∈ S, ∑ x ∈ X,
            star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
              (Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
                G z (x + Q i)))
        = (Fintype.card Z : ℂ) * L i := by
      rw [show (Fintype.card Z : ℂ) * L i = (Fintype.card Z : ℂ) * (∑ x ∈ X,
            Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
            star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + Q i))) from rfl]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x hx
      have hfac : (∑ z ∈ S,
            star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
              (Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
                G z (x + Q i)))
          = star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
              Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
              (∑ z ∈ S, G z (x + Q i)) := by
        rw [show (∑ z ∈ S,
              star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
                (Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
                  G z (x + Q i)))
            = ∑ z ∈ S,
              (star (((Fintype.card Z : ℂ))⁻¹ * ∑ z' ∈ S, G z' (x + a)) *
                Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ))) *
                G z (x + Q i)
            from Finset.sum_congr rfl (fun z hz => by ring)]
        rw [← Finset.mul_sum]
      have hMG : (Fintype.card Z : ℂ) * (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S, G z (x + Q i))
          = ∑ z ∈ S, G z (x + Q i) := by
        rw [← mul_assoc, mul_inv_cancel₀ hM0, one_mul]
      rw [hfac]
      conv_lhs => rw [← hMG]
      ring
    rw [stepB]
  have h2 : ∀ i j : ι, inner ℂ (V i) (V j) = (Fintype.card Z : ℂ) * Pq i j := by
    intro i j
    have hinner : inner ℂ (V i) (V j) =
        ∑ p : ↥(S ×ˢ X), gV j p.1 * star (gV i p.1) := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, Complex.star_def]
      dsimp only [V]
    have hconv : (∑ p : ↥(S ×ˢ X), gV j p.1 * star (gV i p.1))
        = ∑ z ∈ S, ∑ x ∈ X, gV j (z,x) * star (gV i (z,x)) := by
      rw [Finset.sum_coe_sort (S ×ˢ X) (fun r : Z × ℤ => gV j r * star (gV i r))]
      rw [Finset.sum_product]
    rw [hinner, hconv]
    have hpt : ∀ (z : Z) (x : ℤ), gV j (z, x) * star (gV i (z, x)) =
        Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
          (G z (x + Q i) * star (G z (x + Q j))) := by
      intro z x
      have hf : gV j (z, x) =
          Complex.exp (-(2 * Real.pi * Complex.I * (Θ j : ℂ) * (x : ℂ))) *
            star (G z (x + Q j)) := rfl
      have hs : star (gV i (z, x)) =
          Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) * G z (x + Q i) := by
        show star (Complex.exp (-(2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ))) *
            star (G z (x + Q i))) = _
        rw [star_mul, star_star, star_exp_neg]
        ring
      rw [hf, hs]
      calc Complex.exp (-(2 * Real.pi * Complex.I * (Θ j : ℂ) * (x : ℂ))) *
              star (G z (x + Q j)) *
              (Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) * G z (x + Q i))
          = (Complex.exp (-(2 * Real.pi * Complex.I * (Θ j : ℂ) * (x : ℂ))) *
              Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ))) *
              (star (G z (x + Q j)) * G z (x + Q i)) := by ring
        _ = Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (star (G z (x + Q j)) * G z (x + Q i)) := by rw [h_exp_mul]
        _ = Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (G z (x + Q i) * star (G z (x + Q j))) := by ring
    have stepA : (∑ z ∈ S, ∑ x ∈ X, gV j (z, x) * star (gV i (z, x)))
        = ∑ z ∈ S, ∑ x ∈ X,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (G z (x + Q i) * star (G z (x + Q j))) := by
      apply Finset.sum_congr rfl; intro z hz
      apply Finset.sum_congr rfl; intro x hx
      exact hpt z x
    rw [stepA]
    have stepB : (∑ z ∈ S, ∑ x ∈ X,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (G z (x + Q i) * star (G z (x + Q j))))
        = (Fintype.card Z : ℂ) * Pq i j := by
      rw [show (Fintype.card Z : ℂ) * Pq i j = (Fintype.card Z : ℂ) * (∑ x ∈ X,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S,
              G z (x + Q i) * star (G z (x + Q j)))) from rfl]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x hx
      have hfac : (∑ z ∈ S,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (G z (x + Q i) * star (G z (x + Q j))))
          = Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
              (∑ z ∈ S, G z (x + Q i) * star (G z (x + Q j))) := by
        rw [← Finset.mul_sum]
      have hMG : (Fintype.card Z : ℂ) * (((Fintype.card Z : ℂ))⁻¹ * ∑ z ∈ S,
            G z (x + Q i) * star (G z (x + Q j)))
          = ∑ z ∈ S, G z (x + Q i) * star (G z (x + Q j)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hM0, one_mul]
      rw [hfac]
      conv_lhs => rw [← hMG]
      ring
    rw [stepB]
  have hw2 : ‖w‖ ^ 2 = (Fintype.card Z : ℝ) * C := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [w]
    rw [Finset.sum_coe_sort (S ×ˢ X) (fun r : Z × ℤ => ‖gw r‖^2)]
    rw [Finset.sum_product]
    simp only [gw, norm_star]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hw4 : ‖w‖ ^ 4 = ((Fintype.card Z : ℝ))^2 * C^2 := by
    rw [show ‖w‖^4 = (‖w‖^2)^2 by ring, hw2, mul_pow]
  have henergy := Work.Peluse.Tools.energy_lemma_fd (fun i : ↥N => V (i : ι)) w
  have hLi : ∀ i : ↥N, ‖inner ℂ (V (i:ι)) w‖ ^ 2 = ((Fintype.card Z : ℝ))^2 * ‖L (i:ι)‖^2 := by
    intro i
    rw [h1, norm_mul, Complex.norm_natCast, mul_pow]
  have hPi : ∀ i j : ↥N,
      ‖inner ℂ (V (i:ι)) (V (j:ι))‖ ^ 2 = ((Fintype.card Z : ℝ))^2 * ‖Pq (i:ι) (j:ι)‖^2 := by
    intro i j
    rw [h2, norm_mul, Complex.norm_natCast, mul_pow]
  have hAeq : (∑ i : ↥N, ‖inner ℂ (V (i:ι)) w‖ ^ 2) = ((Fintype.card Z : ℝ))^2 * A := by
    rw [Finset.sum_congr rfl (fun i _ => hLi i), ← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort N (fun i => ‖L i‖^2)
  have hPeq : (∑ i : ↥N, ∑ j : ↥N, ‖inner ℂ (V (i:ι)) (V (j:ι))‖ ^ 2)
      = ((Fintype.card Z : ℝ))^2 * P := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hPi i j))]
    rw [show (∑ i : ↥N, ∑ j : ↥N, ((Fintype.card Z : ℝ))^2 * ‖Pq (i:ι) (j:ι)‖^2)
          = ((Fintype.card Z : ℝ))^2 * (∑ i : ↥N, ∑ j : ↥N, ‖Pq (i:ι) (j:ι)‖^2) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]]
    congr 1
    have hinner : ∀ i : ↥N,
        (∑ j : ↥N, ‖Pq (i:ι) (j:ι)‖^2) = ∑ j ∈ N, ‖Pq (i:ι) j‖^2 :=
      fun i => Finset.sum_coe_sort N (fun j => ‖Pq (i:ι) j‖^2)
    simp only [hinner]
    exact Finset.sum_coe_sort N (fun i => ∑ j ∈ N, ‖Pq i j‖^2)
  have hkey : (((Fintype.card Z : ℝ))^2 * A)^2 ≤ (((Fintype.card Z : ℝ))^2 * P) *
      (((Fintype.card Z : ℝ))^2 * C^2) := by
    rw [← hAeq, ← hPeq, ← hw4]
    exact henergy
  have hfin : ((Fintype.card Z : ℝ))^4 * A^2 ≤ ((Fintype.card Z : ℝ))^4 * (P * C^2) := by
    calc ((Fintype.card Z : ℝ))^4 * A^2 = (((Fintype.card Z : ℝ))^2 * A)^2 := by ring
      _ ≤ (((Fintype.card Z : ℝ))^2 * P) * (((Fintype.card Z : ℝ))^2 * C^2) := hkey
      _ = ((Fintype.card Z : ℝ))^4 * (P * C^2) := by ring
  exact le_of_mul_le_mul_left hfin (by positivity)

private theorem rowGram_gen' {ι : Type} [DecidableEq ι] {Z : Type} [Fintype Z] [Nonempty Z]
    (T : Finset ℤ) (G : Z → ℤ → ℂ) (a : ℤ) (N : Finset ι) (Q : ι → ℤ) (Θ : ι → ℝ)
    (hG : ∀ z : Z, ∀ x : ℤ, x ∉ T → G z x = 0) :
    (∑ i ∈ N, ‖∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i))‖ ^ 2) ^ 2
      ≤ (∑ i ∈ N, ∑ j ∈ N, ‖∑' x : ℤ,
            Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2)
        * (∑' x : ℤ, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2) ^ 2 := by
  classical
  have hGbar : ∀ x : ℤ, x ∉ T → ((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z x = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero (fun z _ => hG z x hx), mul_zero]
  obtain ⟨X, hXa, hXq⟩ : ∃ X : Finset ℤ, (∀ x : ℤ, x + a ∈ T → x ∈ X) ∧
      (∀ i ∈ N, ∀ x : ℤ, x + Q i ∈ T → x ∈ X) := by
    refine ⟨T.image (fun t => t - a) ∪ N.biUnion (fun i => T.image (fun t => t - Q i)), ?_, ?_⟩
    · intro x hx
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x + a, hx, by ring⟩))
    · intro i hi x hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_image.mpr ⟨x + Q i, hx, by ring⟩⟩))
  have htsum1 : ∀ i ∈ N, (∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i)))
      = ∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i)) := by
    intro i hi
    refine tsum_eq_sum (fun x hx => ?_)
    have hxa : x + a ∉ T := fun h => hx (hXa x h)
    have hxq : x + Q i ∉ T := fun h => hx (hXq i hi x h)
    simp [hGbar (x + a) hxa, hGbar (x + Q i) hxq]
  have htsum2 : ∀ i ∈ N, ∀ j ∈ N, (∑' x : ℤ,
        Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i))))
      = ∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i))) := by
    intro i hi j hj
    refine tsum_eq_sum (fun x hx => ?_)
    have hxq : x + Q i ∉ T := fun h => hx (hXq i hi x h)
    rw [Finset.sum_eq_zero (fun z _ => by rw [hG z (x + Q i) hxq, star_zero, mul_zero]),
      mul_zero, mul_zero]
  have htsum3 : (∑' x : ℤ, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2)
      = ∑ x ∈ X, ‖((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)‖ ^ 2 := by
    refine tsum_eq_sum (fun x hx => ?_)
    have hxa : x + a ∉ T := fun h => hx (hXa x h)
    simp [hGbar (x + a) hxa]
  have e1 : (∑ i ∈ N, ‖∑' x : ℤ, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i))‖ ^ 2)
      = (∑ i ∈ N, ‖∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * (Θ i : ℂ) * (x : ℂ)) *
        star (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + a)) *
        (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [htsum1 i hi]
  have e2 : (∑ i ∈ N, ∑ j ∈ N, ‖∑' x : ℤ,
          Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
          (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2)
      = (∑ i ∈ N, ∑ j ∈ N, ‖∑ x ∈ X,
          Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
          (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [htsum2 i hi j hj]
  have hswap : (∑ i ∈ N, ∑ j ∈ N, ‖∑ x ∈ X,
          Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
          (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2)
      = (∑ i ∈ N, ∑ j ∈ N, ‖∑ x ∈ X,
          Complex.exp (2 * Real.pi * Complex.I * ((Θ i : ℂ) - (Θ j : ℂ)) * (x : ℂ)) *
          (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q i) * star (G z (x + Q j)))‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      show (‖∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2 : ℝ)
          = ‖∑ x ∈ X, Complex.exp (2 * Real.pi * Complex.I * ((Θ j : ℂ) - (Θ i : ℂ)) * (x : ℂ)) *
            (((Fintype.card Z : ℂ))⁻¹ * ∑ z, G z (x + Q j) * star (G z (x + Q i)))‖ ^ 2 from rfl))]
    rw [Finset.sum_comm]
  rw [e1, e2, htsum3, hswap]
  exact rowGram_finite_step_gen X G a N Q Θ

theorem rowGram_local {Z : Type} [Fintype Z] [Nonempty Z] (T : Finset ℤ) (G : Z → ℤ → ℂ)
    (a : Fin 1 → ℤ) (N : Finset (Fin 1 → ℤ))
    (φ : (Fin 1 → ℤ) → (Fin 1 → ℤ) → ℝ)
    (hG : ∀ z x, x ∉ T → G z x = 0) :
    (∑ u ∈ N, ‖rowC G φ a u‖ ^ 2) ^ 2
      ≤ (∑ u ∈ N, ∑ v ∈ N, ‖gramD G φ a u v‖ ^ 2)
        * (∑' x : ℤ, ‖avgFn G (x + a 0)‖ ^ 2) ^ 2 :=
  rowGram_gen' T G (a 0) N (fun u => u 0) (fun u => φ a u) hG

end Work.Peluse.Ulower.StepLe.ddiSharp.one
