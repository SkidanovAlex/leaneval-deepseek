import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Algebra.MvPolynomial.harmonic_X2_intersection
import Submission.Commons.Algebra.MvPolynomial.lap_bind1_orthonormal

noncomputable section
open scoped BigOperators RealInnerProductSpace
open MvPolynomial

namespace Commons.Algebra.MvPolynomial

private abbrev hpa_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

section Coordinates

variable {n : ℕ}

/-- inner product of coordinate vectors is the plain dot product -/
private lemma hpa_inner_eq_sum (x y : hpa_E n) :
    inner ℝ x y = ∑ j : Fin n, x j * y j := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- `⟪eᵢ, Lx⟫ = ⟪L⁻¹eᵢ, x⟫` (adjoint of an isometry) -/
private lemma hpa_adjoint (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i : Fin n) (x : hpa_E n) :
    inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L x) =
      inner ℝ (L.symm (EuclideanSpace.single i (1 : ℝ))) x := by
  rw [← L.inner_map_map (L.symm (EuclideanSpace.single i (1 : ℝ))) x]
  simp

/-- `⟪eⱼ, L⁻¹eᵢ⟫ = ⟪eᵢ, Leⱼ⟫` -/
private lemma hpa_adjoint_basis (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i j : Fin n) :
    inner ℝ (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i (1 : ℝ))) =
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L (EuclideanSpace.single j (1 : ℝ))) := by
  calc
    inner ℝ (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i (1 : ℝ)))
        = inner ℝ (L (EuclideanSpace.single j (1 : ℝ))) (L (L.symm (EuclideanSpace.single i (1 : ℝ)))) := by
            rw [← L.inner_map_map (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i (1 : ℝ)))]
    _ = inner ℝ (L (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single i (1 : ℝ)) := by simp
    _ = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L (EuclideanSpace.single j (1 : ℝ))) := by
            rw [real_inner_comm]

/-- coordinate expansion `(Lx)ᵢ = ∑ⱼ (Leⱼ)ᵢ xⱼ` -/
private lemma hpa_coord_expand (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (x : hpa_E n) (i : Fin n) :
    (L x) i = ∑ j : Fin n, ((L (EuclideanSpace.single j (1 : ℝ))) i) * x j := by
  calc
    (L x) i = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L x) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℝ (L.symm (EuclideanSpace.single i (1 : ℝ))) x := hpa_adjoint L i x
    _ = ∑ j : Fin n, (L.symm (EuclideanSpace.single i (1 : ℝ))) j * x j := by
      rw [← hpa_inner_eq_sum (L.symm (EuclideanSpace.single i (1 : ℝ))) x]
    _ = ∑ j : Fin n, ((L (EuclideanSpace.single j (1 : ℝ))) i) * x j := by
      apply Finset.sum_congr rfl
      intro j _
      have hcoord : (L.symm (EuclideanSpace.single i (1 : ℝ))) j = (L (EuclideanSpace.single j (1 : ℝ))) i := by
        calc
          (L.symm (EuclideanSpace.single i (1 : ℝ))) j
              = inner ℝ (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i (1 : ℝ))) := by
                  simp [EuclideanSpace.inner_single_left]
          _ = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L (EuclideanSpace.single j (1 : ℝ))) := hpa_adjoint_basis L i j
          _ = (L (EuclideanSpace.single j (1 : ℝ))) i := by
                  simp [EuclideanSpace.inner_single_left]
      rw [hcoord]


section Sigma

variable {n : ℕ}

/-- linear forms `σᵢ(x) = (Lx)ᵢ` as polynomials -/
private def hpa_sigma (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) * MvPolynomial.X j

/-- evaluating the linear form `σᵢ` at `x` gives `(Lx)ᵢ` -/
private lemma hpa_sigma_eval (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (x : hpa_E n) (i : Fin n) :
    MvPolynomial.eval (fun k : Fin n => x k) (hpa_sigma L i) = (L x) i := by
  calc
    MvPolynomial.eval (fun k : Fin n => x k) (hpa_sigma L i)
        = ∑ j : Fin n, ((L (EuclideanSpace.single j (1 : ℝ))) i) * x j := by
            simp [hpa_sigma]
    _ = (L x) i := by
            rw [hpa_coord_expand L x i]

/-- substituting `σ` composes a polynomial with `L`: `(bind₁ σ p)(x) = p(Lx)` -/
private lemma hpa_comp_eval (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (p : MvPolynomial (Fin n) ℝ)
    (x : hpa_E n) :
    MvPolynomial.eval (fun k : Fin n => x k) (MvPolynomial.bind₁ (hpa_sigma L) p) =
      MvPolynomial.eval (fun k : Fin n => (L x) k) p := by
  calc
    MvPolynomial.eval (fun k : Fin n => x k) (MvPolynomial.bind₁ (hpa_sigma L) p)
        = MvPolynomial.eval (fun i : Fin n => MvPolynomial.eval (fun k : Fin n => x k) (hpa_sigma L i)) p := by
            simpa using (MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) (fun k : Fin n => x k) (hpa_sigma L) p)
    _ = MvPolynomial.eval (fun i : Fin n => (L x) i) p := by
            apply congrArg (fun g : Fin n → ℝ => MvPolynomial.eval g p)
            funext i
            exact hpa_sigma_eval L x i

/-- each `σᵢ` is homogeneous of degree one -/
private lemma hpa_sigma_homogeneous (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i : Fin n) :
    (hpa_sigma L i).IsHomogeneous 1 := by
  classical
  dsimp [hpa_sigma]
  refine MvPolynomial.IsHomogeneous.sum (σ := Fin n) (R := ℝ)
    (s := (Finset.univ : Finset (Fin n)))
    (φ := fun j : Fin n => MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) * MvPolynomial.X j) 1 ?_
  intro j hj
  -- summand C a * X j is homogeneous of degree 1
  have hC : (MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) : MvPolynomial (Fin n) ℝ).IsHomogeneous 0 := by
    exact MvPolynomial.isHomogeneous_C (Fin n) ((L (EuclideanSpace.single j (1 : ℝ))) i)
  have hX : (MvPolynomial.X j : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℝ j
  have hmul : ((MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) : MvPolynomial (Fin n) ℝ) * MvPolynomial.X j).IsHomogeneous (0 + 1) := hC.mul hX
  simpa using hmul

/-- `∂ⱼ σᵢ` is the constant `(Leⱼ)ᵢ` -/
private lemma hpa_pderiv_sigma (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i j : Fin n) :
    MvPolynomial.pderiv j (hpa_sigma L i) = MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) := by
  classical
  unfold hpa_sigma
  rw [map_sum]
  calc
    (∑ k : Fin n, MvPolynomial.pderiv j (MvPolynomial.C ((L (EuclideanSpace.single k (1 : ℝ))) i) * MvPolynomial.X k))
        = ∑ k : Fin n, (if k = j then MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hkj : k = j
            · subst k
              simp
            · have hp : MvPolynomial.pderiv j (MvPolynomial.X k) = 0 :=
                MvPolynomial.pderiv_X_of_ne (R := ℝ) (i := j) (j := k) hkj
              rw [MvPolynomial.pderiv_C_mul, hp]
              simp [hkj]
    _ = MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i) := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro k _ hkj
              have hif : (if k = j then (MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i : ℝ) : MvPolynomial (Fin n) ℝ) else 0) = 0 := by
                simp [hkj]
              rw [hif]
            · intro hnj
              exact False.elim (hnj (Finset.mem_univ j))

/-- `∂ⱼ² σᵢ = 0` (σᵢ is linear) -/
private lemma hpa_pderiv2_sigma (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i j : Fin n) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv j (hpa_sigma L i)) = 0 := by
  rw [hpa_pderiv_sigma]
  simp

/-- row-orthonormality of the matrix of `L` -/
private lemma hpa_row_orthonormal (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i i' : Fin n) :
    (∑ j : Fin n, ((L (EuclideanSpace.single j (1 : ℝ))) i) * ((L (EuclideanSpace.single j (1 : ℝ))) i')) =
      (if i = i' then 1 else 0) := by
  classical
  calc
    (∑ j : Fin n, ((L (EuclideanSpace.single j (1 : ℝ))) i) * ((L (EuclideanSpace.single j (1 : ℝ))) i'))
        = (∑ j : Fin n,
            (L.symm (EuclideanSpace.single i (1 : ℝ))) j * (L.symm (EuclideanSpace.single i' (1 : ℝ))) j) := by
            apply Finset.sum_congr rfl
            intro j _
            have h1 : (L (EuclideanSpace.single j (1 : ℝ))) i = (L.symm (EuclideanSpace.single i (1 : ℝ))) j := by
              calc
                (L (EuclideanSpace.single j (1 : ℝ))) i
                    = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (L (EuclideanSpace.single j (1 : ℝ))) := by
                        simp [EuclideanSpace.inner_single_left]
                _ = inner ℝ (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i (1 : ℝ))) :=
                        (hpa_adjoint_basis L i j).symm
                _ = (L.symm (EuclideanSpace.single i (1 : ℝ))) j := by
                        simp [EuclideanSpace.inner_single_left]
            have h2 : (L (EuclideanSpace.single j (1 : ℝ))) i' = (L.symm (EuclideanSpace.single i' (1 : ℝ))) j := by
              calc
                (L (EuclideanSpace.single j (1 : ℝ))) i'
                    = inner ℝ (EuclideanSpace.single i' (1 : ℝ)) (L (EuclideanSpace.single j (1 : ℝ))) := by
                        simp [EuclideanSpace.inner_single_left]
                _ = inner ℝ (EuclideanSpace.single j (1 : ℝ)) (L.symm (EuclideanSpace.single i' (1 : ℝ))) :=
                        (hpa_adjoint_basis L i' j).symm
                _ = (L.symm (EuclideanSpace.single i' (1 : ℝ))) j := by
                        simp [EuclideanSpace.inner_single_left]
            rw [h1, h2]
    _ = inner ℝ (L.symm (EuclideanSpace.single i (1 : ℝ))) (L.symm (EuclideanSpace.single i' (1 : ℝ))) := by
            rw [hpa_inner_eq_sum]
    _ = inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i' (1 : ℝ)) := by
            rw [L.symm.inner_map_map]
    _ = if i = i' then 1 else 0 := by
            simp [EuclideanSpace.inner_single_left]

/-- row-orthonormality hypothesis `h2` for the substitution `σ` -/
private lemma hpa_sigma_h2 (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (i i' : Fin n) :
    (∑ j : Fin n, (MvPolynomial.pderiv j (hpa_sigma L i)) * (MvPolynomial.pderiv j (hpa_sigma L i'))) =
      (if i = i' then (1 : MvPolynomial (Fin n) ℝ) else 0) := by
  classical
  calc
    (∑ j : Fin n, (MvPolynomial.pderiv j (hpa_sigma L i)) * (MvPolynomial.pderiv j (hpa_sigma L i')))
        = ∑ j : Fin n, MvPolynomial.C ((L (EuclideanSpace.single j (1 : ℝ))) i * (L (EuclideanSpace.single j (1 : ℝ))) i') := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hpa_pderiv_sigma L i j, hpa_pderiv_sigma L i' j]
            rw [← map_mul MvPolynomial.C]
    _ = MvPolynomial.C ((∑ j : Fin n, (L (EuclideanSpace.single j (1 : ℝ))) i * (L (EuclideanSpace.single j (1 : ℝ))) i')) := by
            simp [map_sum]
    _ = MvPolynomial.C ((if i = i' then 1 else 0 : ℝ)) := by
            rw [hpa_row_orthonormal L i i']
    _ = if i = i' then (1 : MvPolynomial (Fin n) ℝ) else 0 := by
            by_cases h : i = i'
            · subst i'
              simp
            · have : i ≠ i' := h
              simp [this]

/-- Laplacian commutes with composition by `σ` (orthogonal substitution) -/
private lemma hpa_lap_bind1 (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (p : MvPolynomial (Fin n) ℝ) :
    (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (MvPolynomial.bind₁ (hpa_sigma L) p))) =
      MvPolynomial.bind₁ (hpa_sigma L) (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j p)) := by
  exact Commons.Algebra.MvPolynomial.lap_bind1_orthonormal (hpa_sigma L) p
    (fun i j => hpa_pderiv2_sigma L i j)
    (fun i i' => hpa_sigma_h2 L i i')

/-- substituting σ preserves homogeneity of degree `k` -/
private lemma hpa_bind1_homogeneous (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n)
    {p : MvPolynomial (Fin n) ℝ} {k : ℕ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    MvPolynomial.bind₁ (hpa_sigma L) p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have hpI : p.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule (n := k) p).mp hp
  have hbind : (MvPolynomial.bind₁ (hpa_sigma L) p).IsHomogeneous (1 * k) := by
    change ((MvPolynomial.aeval (hpa_sigma L)) p).IsHomogeneous (1 * k)
    exact MvPolynomial.IsHomogeneous.aeval (R := ℝ) (S := ℝ) hpI (hpa_sigma L)
      (fun i => hpa_sigma_homogeneous L i)
  simpa using hbind

end Sigma

section Values

variable {n : ℕ}

/-- `‖x‖² = ∑ xⱼ²` -/
private lemma hpa_norm_sq (x : hpa_E n) : ‖x‖ ^ 2 = ∑ j : Fin n, (x j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  simp

/-- evaluation of `∑ (X j)^2` -/
private lemma hpa_r2_eval (x : hpa_E n) :
    MvPolynomial.eval (fun j : Fin n => x j) (∑ j : Fin n, (MvPolynomial.X j) ^ 2) = ‖x‖ ^ 2 := by
  calc
    MvPolynomial.eval (fun j : Fin n => x j) (∑ j : Fin n, (MvPolynomial.X j) ^ 2)
        = ∑ j : Fin n, (x j) ^ 2 := by simp
    _ = ‖x‖ ^ 2 := by rw [hpa_norm_sq]

/-- orthogonal maps preserve the norm -/
private lemma hpa_norm_iso (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n) (x : hpa_E n) :
    ‖L x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [L.norm_map]

variable [NeZero n]

/-- evaluation of the axis monomial -/
private lemma hpa_X0_eval {k : ℕ} (x : hpa_E n) :
    MvPolynomial.eval (fun j : Fin n => x j) ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) =
      (x (0 : Fin n)) ^ k := by
  simp

/-- `L` fixing `e₀` preserves the `0`-coordinate of every point -/
private lemma hpa_coord_zero_fix (L : hpa_E n ≃ₗᵢ[ℝ] hpa_E n)
    (hfix : L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ))
    (x : hpa_E n) : (L x) (0 : Fin n) = x (0 : Fin n) := by
  calc
    (L x) (0 : Fin n) = inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) (L x) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℝ (L.symm (EuclideanSpace.single (0 : Fin n) (1 : ℝ))) x := hpa_adjoint L (0 : Fin n) x
    _ = inner ℝ (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) x := by
      have hsymm : L.symm (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by
        calc
          L.symm (EuclideanSpace.single (0 : Fin n) (1 : ℝ))
              = L.symm (L (EuclideanSpace.single (0 : Fin n) (1 : ℝ))) := by rw [hfix]
          _ = EuclideanSpace.single (0 : Fin n) (1 : ℝ) := by simp
      rw [hsymm]
    _ = x (0 : Fin n) := by simp [EuclideanSpace.inner_single_left]

end Values

end Coordinates

theorem harmonic_part_axisInvariant
    {n : ℕ} {k : ℕ} [NeZero n]
    (Z R : MvPolynomial (Fin n) ℝ)
    (hZ : Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlapZ : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j Z)) = 0)
    (hR : R ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2))
    (hdec : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) = Z +
        (∑ j : Fin n, (MvPolynomial.X j)^2) * R) :
    ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        MvPolynomial.eval (fun i : Fin n => (L x) i) Z =
          MvPolynomial.eval (fun i : Fin n => x i) Z := by
  classical
  intro L hfix x
  let r2 : MvPolynomial (Fin n) ℝ := ∑ j : Fin n, (MvPolynomial.X j)^2
  let ZL : MvPolynomial (Fin n) ℝ := MvPolynomial.bind₁ (hpa_sigma L) Z
  let RL : MvPolynomial (Fin n) ℝ := MvPolynomial.bind₁ (hpa_sigma L) R
  have hdecr2 : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) = Z + r2 * R := by
    simpa [r2] using hdec
  have hZLhom : ZL ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
    dsimp [ZL]
    exact hpa_bind1_homogeneous L hZ
  have hRLhom : RL ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
    dsimp [RL]
    exact hpa_bind1_homogeneous L hR
  have hlapZL : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j ZL)) = 0 := by
    dsimp [ZL]
    rw [hpa_lap_bind1 L Z]
    rw [hlapZ]
    simp
  have hcompevalZ : ∀ y : hpa_E n,
      MvPolynomial.eval (fun i : Fin n => y i) ZL = MvPolynomial.eval (fun i : Fin n => (L y) i) Z := by
    intro y
    dsimp [ZL]
    exact hpa_comp_eval L Z y
  have hcompevalR : ∀ y : hpa_E n,
      MvPolynomial.eval (fun i : Fin n => y i) RL = MvPolynomial.eval (fun i : Fin n => (L y) i) R := by
    intro y
    dsimp [RL]
    exact hpa_comp_eval L R y
  -- decomposition identity : X0^k = ZL + r2 * RL
  have hdec' : ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) = ZL + r2 * RL := by
    apply MvPolynomial.funext
    intro f
    let y : hpa_E n := WithLp.toLp 2 f
    have hfun : (fun i : Fin n => y i) = f := by
      funext i
      rfl
    calc
      MvPolynomial.eval f ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k)
          = (y (0 : Fin n)) ^ k := by
              rw [← hfun]
              exact hpa_X0_eval (k := k) y
      _ = ((L y) (0 : Fin n)) ^ k := by
              rw [← hpa_coord_zero_fix L hfix y]
      _ = MvPolynomial.eval (fun i : Fin n => (L y) i) ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k) := by
              exact (hpa_X0_eval (k := k) (x := L y)).symm
      _ = MvPolynomial.eval (fun i : Fin n => (L y) i) Z
            + ‖L y‖^2 * MvPolynomial.eval (fun i : Fin n => (L y) i) R := by
            calc
              MvPolynomial.eval (fun i : Fin n => (L y) i) ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k)
                  = MvPolynomial.eval (fun i : Fin n => (L y) i) (Z + r2 * R) := by
                      rw [hdecr2]
              _ = MvPolynomial.eval (fun i : Fin n => (L y) i) Z
                    + MvPolynomial.eval (fun i : Fin n => (L y) i) r2
                        * MvPolynomial.eval (fun i : Fin n => (L y) i) R := by
                    simp
              _ = MvPolynomial.eval (fun i : Fin n => (L y) i) Z
                    + ‖L y‖^2 * MvPolynomial.eval (fun i : Fin n => (L y) i) R := by
                    have he2 : MvPolynomial.eval (fun i : Fin n => (L y) i) r2 = ‖L y‖^2 := by
                      dsimp [r2]
                      exact hpa_r2_eval (L y)
                    rw [he2]
      _ = MvPolynomial.eval (fun i : Fin n => (L y) i) Z
            + ‖y‖^2 * MvPolynomial.eval (fun i : Fin n => (L y) i) R := by
            rw [hpa_norm_iso L y]
      _ = MvPolynomial.eval f (ZL + r2 * RL) := by
            calc
              MvPolynomial.eval (fun i : Fin n => (L y) i) Z
                    + ‖y‖^2 * MvPolynomial.eval (fun i : Fin n => (L y) i) R
                  = MvPolynomial.eval (fun i : Fin n => y i) ZL
                      + ‖y‖^2 * MvPolynomial.eval (fun i : Fin n => y i) RL := by
                      rw [← hcompevalZ y, ← hcompevalR y]
              _ = MvPolynomial.eval (fun i : Fin n => y i) (ZL + r2 * RL) := by
                      simp [r2, hpa_r2_eval y]
              _ = MvPolynomial.eval f (ZL + r2 * RL) := by rw [hfun]
  -- uniqueness of the decomposition : ZL = Z
  have hEqX : ZL + r2 * RL = Z + r2 * R := by
    calc
      ZL + r2 * RL = (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ k := hdec'.symm
      _ = Z + r2 * R := hdecr2
  have hZLeq : ZL = Z := by
    have hH : ZL - Z = r2 * (R - RL) := by
      have hz : (ZL + r2 * RL) - (Z + r2 * R) = 0 := by
        rw [hEqX]
        ring
      calc
        ZL - Z = (ZL + r2 * RL) - (Z + r2 * R) + (r2 * R - r2 * RL) := by ring
        _ = 0 + r2 * (R - RL) := by
              rw [hz]
              ring
        _ = r2 * (R - RL) := by simp
    have hHhom : ZL - Z ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := by
      exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).sub_mem hZLhom hZ
    have hQhom : R - RL ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2) := by
      exact (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (k - 2)).sub_mem hR hRLhom
    have hlapH : (∑ j : Fin n, MvPolynomial.pderiv j (MvPolynomial.pderiv j (ZL - Z))) = 0 := by
      simp [hlapZL, hlapZ]
    have huniq := harmonic_X2_intersection (n := n) (k := k) (H := ZL - Z) (Q := R - RL)
      hHhom hQhom hlapH hH
    exact sub_eq_zero.mp huniq
  -- conclusion at the point x
  calc
    MvPolynomial.eval (fun i : Fin n => (L x) i) Z
        = MvPolynomial.eval (fun i : Fin n => x i) ZL := by
            exact (hcompevalZ x).symm
    _ = MvPolynomial.eval (fun i : Fin n => x i) Z := by
            rw [hZLeq]