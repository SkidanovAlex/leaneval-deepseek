import Mathlib

open Set Function MeasureTheory Metric
open scoped Classical
noncomputable section

namespace Commons.Analysis.MeasureTheory

private abbrev Eu (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Sph (n : ℕ) := Metric.sphere (0 : Eu n) 1

/-- The antipodal point of a point on the unit sphere. -/
private def negSphPoint {n : ℕ} (θ : Sph n) : Sph n :=
  ⟨-θ.1, by
    simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩

/-- The `i`-th coordinate as a continuous function on the unit sphere. -/
private def sphereCoord (n : ℕ) (i : Fin n) : C(Sph n, ℝ) :=
  ⟨fun θ : Sph n => (θ : Eu n) i, by fun_prop⟩

/-- The algebra homomorphism sending each polynomial to its restriction to the sphere. -/
private def spherePolyMap (n : ℕ) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(Sph n, ℝ) :=
  MvPolynomial.aeval (fun i : Fin n => sphereCoord n i)

private lemma spherePolyMap_apply (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (θ : Sph n) :
    (spherePolyMap n p) θ = MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) p := by
  unfold spherePolyMap
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      rw [map_add]
      change ((MvPolynomial.aeval (fun i : Fin n => sphereCoord n i)) p) θ +
        ((MvPolynomial.aeval (fun i : Fin n => sphereCoord n i)) q) θ =
          (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i)) (p + q)
      rw [hp, hq]
      rw [MvPolynomial.eval_add]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      change ((MvPolynomial.aeval (fun i : Fin n => sphereCoord n i)) p * sphereCoord n i) θ =
          (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i)) (p * MvPolynomial.X i)
      change ((MvPolynomial.aeval (fun i : Fin n => sphereCoord n i)) p) θ * (sphereCoord n i) θ =
          (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i)) (p * MvPolynomial.X i)
      rw [hp]
      change (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i)) p * (θ : Eu n) i =
          (MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i)) (p * MvPolynomial.X i)
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]

private lemma spherePolyMap_range_separates (n : ℕ) : (spherePolyMap n).range.SeparatesPoints := by
  intro θ₁ θ₂ hne
  have hv : (θ₁ : Eu n) ≠ (θ₂ : Eu n) := by
    intro h
    exact hne (Subtype.ext h)
  obtain ⟨i, hi⟩ : ∃ i : Fin n, (θ₁ : Eu n) i ≠ (θ₂ : Eu n) i := by
    by_contra hc
    apply hv
    ext i
    by_contra h
    exact hc ⟨i, h⟩
  refine ⟨(spherePolyMap n (MvPolynomial.X i) : Sph n → ℝ), ?_, ?_⟩
  · exact ⟨spherePolyMap n (MvPolynomial.X i),
      (spherePolyMap n).mem_range_self (MvPolynomial.X i), rfl⟩
  · simp [hi, spherePolyMap_apply]

/-- The automorphism of the polynomial ring induced by negating all variables. -/
private def polyNegSubst (n : ℕ) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (fun i : Fin n => - (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))

private lemma eval_polyNegSubst (n : ℕ) (t : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval t (polyNegSubst n p) = MvPolynomial.eval (fun i => - t i) p := by
  let f : MvPolynomial (Fin n) ℝ →+* ℝ := (MvPolynomial.eval t).comp (polyNegSubst n)
  let g : MvPolynomial (Fin n) ℝ →+* ℝ := MvPolynomial.eval (fun i => - t i)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, g, polyNegSubst]
    · intro j
      simp [f, g, polyNegSubst]
  change f p = MvPolynomial.eval (fun i => - t i) p
  exact congrArg (fun h : MvPolynomial (Fin n) ℝ →+* ℝ => h p) hfg

/-- The even part of a polynomial: `p ↦ (p + p(-·)) / 2`. -/
private def polyEvenPart (n : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  (1 / 2 : ℝ) • (p + polyNegSubst n p)

private lemma eval_smul (n : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) (t : Fin n → ℝ) :
    MvPolynomial.eval t (c • p) = c * MvPolynomial.eval t p := by
  rw [Algebra.smul_def, map_mul]
  simp

private lemma polyEvenPart_eval (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (t : Fin n → ℝ) :
    MvPolynomial.eval t (polyEvenPart n p) =
      (MvPolynomial.eval t p + MvPolynomial.eval (fun i => - t i) p) / 2 := by
  unfold polyEvenPart
  rw [eval_smul]
  rw [map_add, eval_polyNegSubst]
  ring

private lemma polyEvenPart_neg_eval (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (t : Fin n → ℝ) :
    MvPolynomial.eval (fun i => - t i) (polyEvenPart n p) =
      MvPolynomial.eval t (polyEvenPart n p) := by
  calc
    MvPolynomial.eval (fun i => - t i) (polyEvenPart n p)
        = (MvPolynomial.eval (fun i => - t i) p +
            MvPolynomial.eval (fun i => - - t i) p) / 2 := polyEvenPart_eval n p (fun i => - t i)
    _ = (MvPolynomial.eval (fun i => - t i) p + MvPolynomial.eval t p) / 2 := by
        have hmm : (fun i : Fin n => - - t i) = t := by
          funext i
          rw [neg_neg]
        rw [hmm]
    _ = (MvPolynomial.eval t p + MvPolynomial.eval (fun i => - t i) p) / 2 := by ring
    _ = MvPolynomial.eval t (polyEvenPart n p) := by
        rw [polyEvenPart_eval]

/-- A real inequality used for the uniform bound of the even part. -/
private lemma abs_avg_le_of_abs_le {a b c δ : ℝ} (h1 : |a - b| ≤ δ) (h2 : |a - c| ≤ δ) :
    |a - (b + c) / 2| ≤ δ := by
  have h1' : |(a - b) + (a - c)| / 2 ≤ (|a - b| + |a - c|) / 2 := by
    have h := abs_add_le (a - b) (a - c)
    exact div_le_div_of_nonneg_right h (by norm_num : 0 ≤ (2 : ℝ))
  calc
    |a - (b + c) / 2| = |((a - b) + (a - c)) / 2| := by congr 1; ring
    _ = |(a - b) + (a - c)| / 2 := by
      rw [abs_div]; rw [abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    _ ≤ (|a - b| + |a - c|) / 2 := h1'
    _ ≤ δ := by linarith


theorem sphere_even_polynomial_uniform_dense
    {n : ℕ} (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hfcont : Continuous f)
    (hfeven : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      f (⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = f θ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℝ,
      (∀ x : EuclideanSpace ℝ (Fin n), (MvPolynomial.eval (fun i : Fin n => x i) P) =
        MvPolynomial.eval (fun i : Fin n => (-x) i) P) ∧
      ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        |f θ - (MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P)| ≤ ε := by
  let ε2 := ε / 2
  have hε2 : 0 < ε2 := by
    dsimp [ε2]
    positivity
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (spherePolyMap n).range (spherePolyMap_range_separates n) f hfcont ε2 hε2
  obtain ⟨q, hq⟩ := (spherePolyMap n).mem_range.mp g.2
  have hq_approx : ∀ θ : Sph n,
      |MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) q - f θ| < ε2 := by
    intro θ
    have hh := hg θ
    rw [← hq, spherePolyMap_apply] at hh
    simpa using hh
  have hq_approx_neg : ∀ θ : Sph n,
      |MvPolynomial.eval (fun i : Fin n => ((negSphPoint θ : Eu n) i)) q - f θ| < ε2 := by
    intro θ
    have hh := hg (negSphPoint θ)
    rw [← hq, spherePolyMap_apply] at hh
    -- hh : ‖eval (coords of negSphPoint θ) q - f (negSphPoint θ)‖ < ε2
    rw [show f (negSphPoint θ) = f θ by
      unfold negSphPoint
      exact hfeven θ] at hh
    simpa using hh
  let P : MvPolynomial (Fin n) ℝ := polyEvenPart n q
  refine ⟨P, ?even, ?bound⟩
  · intro x
    have hneg : (fun i : Fin n => ((-x : Eu n) i)) = fun i : Fin n => - (x i) := by
      funext i
      rfl
    rw [hneg]
    exact (polyEvenPart_neg_eval n q (fun i : Fin n => x i)).symm
  · intro θ
    let qθ := MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) q
    let qθ' := MvPolynomial.eval (fun i : Fin n => ((negSphPoint θ : Eu n) i)) q
    have htmp : MvPolynomial.eval (fun i : Fin n => - (θ : Eu n) i) q =
        MvPolynomial.eval (fun i : Fin n => ((negSphPoint θ : Eu n) i)) q := by
      apply congrArg (fun u : Fin n → ℝ => MvPolynomial.eval u q)
      funext i
      change - ((θ : Eu n)).ofLp i = ((negSphPoint θ : Eu n)).ofLp i
      rw [show ((negSphPoint θ : Eu n)) = (-(θ : Eu n)) by rfl]
      rfl
    have hPeval : MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P =
        (qθ + qθ') / 2 := by
      dsimp [qθ, qθ']
      rw [polyEvenPart_eval, htmp]
    have hmain : |f θ - (qθ + qθ') / 2| ≤ ε2 := by
      apply abs_avg_le_of_abs_le
      · -- |f θ - qθ| ≤ ε2
        have hh := hq_approx θ
        rw [abs_sub_comm]
        exact le_of_lt hh
      · -- |f θ - qθ'| ≤ ε2
        have hh := hq_approx_neg θ
        rw [abs_sub_comm]
        exact le_of_lt hh
    calc
      |f θ - MvPolynomial.eval (fun i : Fin n => (θ : Eu n) i) P| = |f θ - (qθ + qθ') / 2| := by
          rw [hPeval]
      _ ≤ ε2 := hmain
      _ ≤ ε := by
          dsimp [ε2]
          linarith

end Commons.Analysis.MeasureTheory
