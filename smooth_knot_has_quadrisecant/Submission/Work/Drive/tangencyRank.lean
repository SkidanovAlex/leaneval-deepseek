import Mathlib
import Submission.Work.Drive.knotPerturbDefs
import Submission.Work.Drive.trigRelation_trivial

/-!
# The rank (surjectivity) lemma for the tangency conditions

For the perturbation family of `knotPerturbDefs` the bad configurations (collinear triples
whose chord is tangent at the tangency slot `x`) are the zeros of the map

  `Ψ_x (c, lam, mu, a, b, m) = (v_c x - lam (r_c a - r_c b), v_c x - mu (r_c a - r_c m))`.

Its derivative in the perturbation variable `c` is the linear map

  `δc ↦ (Σ j, (ℓ j) • δc j, Σ j, (ℓ' j) • δc j)`,

with `ℓ j = trigBasisD j x - lam (trigBasis j a - trigBasis j b)` and
`ℓ' j = trigBasisD j x - mu (trigBasis j a - trigBasis j m)`.

Here we prove that this linear map is **surjective** whenever `x` is one of `a, b, m`,
those three points are pairwise distinct in `[0, 2π)`, and `lam, mu ≠ 0`.  The proof:
the relation `α ℓ + β ℓ' ≡ 0` on the scalar basis would force both coefficients to vanish
(by `trigRelation_trivial`), hence no two of the vectors `(ℓ j, ℓ' j)` can be proportional,
and a `2 × 2` system with a nonvanishing determinant then solves for any pair of vectors.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- Coefficient of the first functional. -/
def ellCoeff (x a b : ℝ) (lam : ℝ) (j : Fin 9) : ℝ :=
  trigBasisD j x - lam * (trigBasis j a - trigBasis j b)

/-- Coefficient of the second functional. -/
def ellCoeff' (x a m : ℝ) (mu : ℝ) (j : Fin 9) : ℝ :=
  trigBasisD j x - mu * (trigBasis j a - trigBasis j m)

/-- For a nonzero pair `(u, v)` of reals there is a nonzero `(α, β)` with `α * u + β * v = 0`. -/
lemma exists_ne_zero_mul_add_mul_eq_zero {u v : ℝ} (h : (u, v) ≠ 0) :
    ∃ α β : ℝ, (α, β) ≠ 0 ∧ α * u + β * v = 0 := by
  by_cases hu : u = 0
  · refine ⟨1, 0, ?_, ?_⟩
    · intro hcon
      exact one_ne_zero (congrArg Prod.fst hcon)
    · rw [hu]; ring
  · exact ⟨v, -u, by simp [hu], by ring⟩

/-- The combination `α ℓ + β ℓ'` written coefficientwise. -/
lemma combine_coeff (x a b m lam mu α β : ℝ) (j : Fin 9) :
    α * ellCoeff x a b lam j + β * ellCoeff' x a m mu j
      = (α + β) * trigBasisD j x + (-(α * lam) - β * mu) * trigBasis j a
        + (α * lam) * trigBasis j b + (β * mu) * trigBasis j m := by
  simp only [ellCoeff, ellCoeff']; ring

/-- **Independence of the two tangency functionals.**  If `x` is one of the three parameters
`a, b, m` (pairwise distinct in `[0, 2π)`) and `lam, mu ≠ 0`, then no nontrivial combination of the
functionals `ℓ`, `ℓ'` vanishes on the scalar basis. -/
theorem not_forall_combine (x a b m : ℝ) (ha : a ∈ Set.Ico 0 (2 * Real.pi))
    (hb : b ∈ Set.Ico 0 (2 * Real.pi)) (hm : m ∈ Set.Ico 0 (2 * Real.pi))
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) (hx : x = a ∨ x = b ∨ x = m)
    (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) (α β : ℝ)
    (h : ∀ c : Fin 9 → ℝ,
      α * (∑ j, (ellCoeff x a b lam j) * c j) + β * (∑ j, (ellCoeff' x a m mu j) * c j) = 0) :
    α = 0 ∧ β = 0 := by
  -- coefficientwise vanishing
  have hsingle : ∀ j : Fin 9, α * ellCoeff x a b lam j + β * ellCoeff' x a m mu j = 0 := by
    intro j
    have h1 : (∑ i, (ellCoeff x a b lam i) * (if i = j then (1:ℝ) else 0))
        = ellCoeff x a b lam j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have h2 : (∑ i, (ellCoeff' x a m mu i) * (if i = j then (1:ℝ) else 0))
        = ellCoeff' x a m mu j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi; simp [hi]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have hh := h (fun i => if i = j then (1:ℝ) else 0)
    rw [h1, h2] at hh
    exact hh
  have hcoeff : ∀ j : Fin 9, (α + β) * trigBasisD j x + (-(α * lam) - β * mu) * trigBasis j a
      + (α * lam) * trigBasis j b + (β * mu) * trigBasis j m = 0 := by
    intro j
    rw [← combine_coeff x a b m lam mu α β j]
    exact hsingle j
  -- the sum form required by the trigonometric relation lemma
  have hsum : ∀ c : Fin 9 → ℝ,
      (α + β) * (∑ j, (trigBasisD j x) * c j) + (-(α * lam) - β * mu) * (∑ j, (trigBasis j a) * c j)
        + (α * lam) * (∑ j, (trigBasis j b) * c j) + (β * mu) * (∑ j, (trigBasis j m) * c j) = 0 := by
    intro c
    have hzero : ∑ j, ((α + β) * trigBasisD j x + (-(α * lam) - β * mu) * trigBasis j a
        + (α * lam) * trigBasis j b + (β * mu) * trigBasis j m) * c j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcoeff j, zero_mul]
    calc (α + β) * (∑ j, (trigBasisD j x) * c j)
            + (-(α * lam) - β * mu) * (∑ j, (trigBasis j a) * c j)
            + (α * lam) * (∑ j, (trigBasis j b) * c j) + (β * mu) * (∑ j, (trigBasis j m) * c j)
        = (∑ j, (α + β) * ((trigBasisD j x) * c j))
            + (∑ j, (-(α * lam) - β * mu) * ((trigBasis j a) * c j))
            + (∑ j, (α * lam) * ((trigBasis j b) * c j))
            + (∑ j, (β * mu) * ((trigBasis j m) * c j)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ j, ((α + β) * ((trigBasisD j x) * c j)
            + (-(α * lam) - β * mu) * ((trigBasis j a) * c j)
            + (α * lam) * ((trigBasis j b) * c j)
            + (β * mu) * ((trigBasis j m) * c j)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ = ∑ j, ((α + β) * trigBasisD j x + (-(α * lam) - β * mu) * trigBasis j a
            + (α * lam) * trigBasis j b + (β * mu) * trigBasis j m) * c j := by
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := hzero
  rcases hx with hxa | hxb | hxm
  · rw [hxa] at hsum
    obtain ⟨-, -, h3, h4⟩ := trigRelation_trivial ha hb hm hab ham hbm (α + β)
      (-(α * lam) - β * mu) (α * lam) (β * mu) hsum
    exact ⟨(mul_eq_zero.mp h3).resolve_right hlam, (mul_eq_zero.mp h4).resolve_right hmu⟩
  · rw [hxb] at hsum
    have hswap : ∀ c : Fin 9 → ℝ,
        (α + β) * (∑ j, (trigBasisD j b) * c j) + (α * lam) * (∑ j, (trigBasis j b) * c j)
          + (-(α * lam) - β * mu) * (∑ j, (trigBasis j a) * c j)
          + (β * mu) * (∑ j, (trigBasis j m) * c j) = 0 := by
      intro c
      have hh := hsum c
      linarith [hh]
    obtain ⟨-, h2, -, h4⟩ := trigRelation_trivial hb ha hm (Ne.symm hab) hbm ham
      (α + β) (α * lam) (-(α * lam) - β * mu) (β * mu) hswap
    exact ⟨(mul_eq_zero.mp h2).resolve_right hlam, (mul_eq_zero.mp h4).resolve_right hmu⟩
  · rw [hxm] at hsum
    have hswap : ∀ c : Fin 9 → ℝ,
        (α + β) * (∑ j, (trigBasisD j m) * c j) + (β * mu) * (∑ j, (trigBasis j m) * c j)
          + (-(α * lam) - β * mu) * (∑ j, (trigBasis j a) * c j)
          + (α * lam) * (∑ j, (trigBasis j b) * c j) = 0 := by
      intro c
      have hh := hsum c
      linarith [hh]
    obtain ⟨-, h2, -, h4⟩ := trigRelation_trivial hm ha hb (Ne.symm ham) (Ne.symm hbm) hab
      (α + β) (β * mu) (-(α * lam) - β * mu) (α * lam) hswap
    exact ⟨(mul_eq_zero.mp h4).resolve_right hlam, (mul_eq_zero.mp h2).resolve_right hmu⟩

/-- A `2 × 2` linear system with nonzero determinant is solvable in `Space`. -/
lemma smul_solve {u v u' v' : ℝ} (h : u * v' - v * u' ≠ 0) (x y : Space) :
    ∃ c c' : Space, u • c + v • c' = x ∧ u' • c + v' • c' = y := by
  have h' : v' * u - v * u' ≠ 0 := by
    intro hc
    exact h (by linarith [hc])
  refine ⟨(u * v' - v * u')⁻¹ • (v' • x - v • y),
          (u * v' - v * u')⁻¹ • (-(u' • x) + u • y), ?_, ?_⟩
  · ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp [h']
    ring
  · ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    rw [show u' * ((u * v' - v * u')⁻¹ * (v' * x.ofLp i - v * y.ofLp i))
          + v' * ((u * v' - v * u')⁻¹ * (-(u' * x.ofLp i) + u * y.ofLp i))
        = (u * v' - v * u')⁻¹ * (u * v' - v * u') * y.ofLp i by ring,
      inv_mul_cancel₀ h, one_mul]

/-- A single-coordinate vector in the coefficient space. -/
noncomputable def singleCoeff (j : Fin 9) (c : Space) : Fin 9 → Space :=
  fun i => if i = j then c else 0

lemma sum_singleCoeff (ell : Fin 9 → ℝ) (j : Fin 9) (c : Space) :
    (∑ i, (ell i) • (singleCoeff j c i)) = ell j • c := by
  rw [Finset.sum_eq_single j]
  · simp [singleCoeff]
  · intro i _ hi
    rw [show singleCoeff j c i = 0 from if_neg hi, smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The linear map of a family of coefficient pairs is onto as soon as one determinant is
nonzero. -/
lemma surjective_of_det_ne_zero {ell ell' : Fin 9 → ℝ} {j j' : Fin 9}
    (h : ell j * ell' j' - ell j' * ell' j ≠ 0) :
    ∀ x y : Space, ∃ c : Fin 9 → Space,
      (∑ i, (ell i) • c i) = x ∧ (∑ i, (ell' i) • c i) = y := by
  intro x y
  obtain ⟨c, c', h1, h2⟩ := smul_solve h x y
  refine ⟨singleCoeff j c + singleCoeff j' c', ?_, ?_⟩
  · have hexp : (∑ i, (ell i) • (singleCoeff j c + singleCoeff j' c') i)
        = (∑ i, (ell i) • (singleCoeff j c i)) + (∑ i, (ell i) • (singleCoeff j' c' i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, smul_add]
    rw [hexp, sum_singleCoeff, sum_singleCoeff, h1]
  · have hexp : (∑ i, (ell' i) • (singleCoeff j c + singleCoeff j' c') i)
        = (∑ i, (ell' i) • (singleCoeff j c i)) + (∑ i, (ell' i) • (singleCoeff j' c' i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, smul_add]
    rw [hexp, sum_singleCoeff, sum_singleCoeff, h2]

/-- The coefficientwise form of `not_forall_combine`. -/
lemma not_forall_combine' (x a b m : ℝ) (ha : a ∈ Set.Ico 0 (2 * Real.pi))
    (hb : b ∈ Set.Ico 0 (2 * Real.pi)) (hm : m ∈ Set.Ico 0 (2 * Real.pi))
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) (hx : x = a ∨ x = b ∨ x = m)
    (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) (α β : ℝ)
    (h : ∀ j : Fin 9, α * ellCoeff x a b lam j + β * ellCoeff' x a m mu j = 0) :
    α = 0 ∧ β = 0 := by
  refine not_forall_combine x a b m ha hb hm hab ham hbm hx lam mu hlam hmu α β fun c => ?_
  have hzip : α * (∑ j, (ellCoeff x a b lam j) * c j)
        + β * (∑ j, (ellCoeff' x a m mu j) * c j)
      = ∑ j, (α * ellCoeff x a b lam j + β * ellCoeff' x a m mu j) * c j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hzip, Finset.sum_eq_zero fun j _ => by rw [h j, zero_mul]]

/-- Proportionality of two planar vectors from the vanishing of their determinant. -/
lemma proportional_of_det_zero {u v u' v' : ℝ} (h : (u, v) ≠ 0) (h0 : u * v' = u' * v) :
    ∃ ρ : ℝ, u' = ρ * u ∧ v' = ρ * v := by
  rcases eq_or_ne u 0 with hu | hu
  · have hv : v ≠ 0 := fun hv0 => h (Prod.ext hu hv0)
    refine ⟨v' / v, ?_, ?_⟩
    · rw [hu, mul_zero]
      rw [hu, zero_mul] at h0
      exact (mul_eq_zero.mp h0.symm).resolve_right hv
    · rw [div_mul_cancel₀ _ hv]
  · refine ⟨u' / u, ?_, ?_⟩
    · field_simp
    · rw [div_mul_eq_mul_div, eq_div_iff hu]
      linarith [h0]

/-- **Some coefficient pair has a nonzero determinant.** -/
theorem exists_det_ne_zero (x a b m : ℝ) (ha : a ∈ Set.Ico 0 (2 * Real.pi))
    (hb : b ∈ Set.Ico 0 (2 * Real.pi)) (hm : m ∈ Set.Ico 0 (2 * Real.pi))
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) (hx : x = a ∨ x = b ∨ x = m)
    (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    ∃ j j' : Fin 9, ellCoeff x a b lam j * ellCoeff' x a m mu j'
      ≠ ellCoeff x a b lam j' * ellCoeff' x a m mu j := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  by_cases hzero : ∃ j : Fin 9, (ellCoeff x a b lam j, ellCoeff' x a m mu j) ≠ 0
  · obtain ⟨j₀, hj₀⟩ := hzero
    obtain ⟨α, β, hαβ, hαβ0⟩ := exists_ne_zero_mul_add_mul_eq_zero hj₀
    have key : ∀ j : Fin 9, α * ellCoeff x a b lam j + β * ellCoeff' x a m mu j = 0 := by
      intro j
      have h0 : ellCoeff x a b lam j * ellCoeff' x a m mu j₀
          = ellCoeff x a b lam j₀ * ellCoeff' x a m mu j := hcon j j₀
      obtain ⟨ρ, hρ1, hρ2⟩ := proportional_of_det_zero hj₀ h0.symm
      rw [hρ1, hρ2]
      linear_combination ρ * hαβ0
    have := not_forall_combine' x a b m ha hb hm hab ham hbm hx lam mu hlam hmu α β key
    exact hαβ (Prod.ext this.1 this.2)
  · simp only [not_exists, not_not] at hzero
    have := not_forall_combine' x a b m ha hb hm hab ham hbm hx lam mu hlam hmu 1 0
      (fun j => by
        have h1 : ellCoeff x a b lam j = 0 := congrArg Prod.fst (hzero j)
        have h2 : ellCoeff' x a m mu j = 0 := congrArg Prod.snd (hzero j)
        rw [h1, h2]; ring)
    exact one_ne_zero this.1

/-- **Surjectivity of the perturbation-derivative of the tangency conditions.** -/
theorem surjective_tangency (x a b m : ℝ) (ha : a ∈ Set.Ico 0 (2 * Real.pi))
    (hb : b ∈ Set.Ico 0 (2 * Real.pi)) (hm : m ∈ Set.Ico 0 (2 * Real.pi))
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) (hx : x = a ∨ x = b ∨ x = m)
    (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    Function.Surjective (fun c : Fin 9 → Space =>
      (∑ j, (ellCoeff x a b lam j) • c j, ∑ j, (ellCoeff' x a m mu j) • c j)) := by
  obtain ⟨j, j', hj⟩ := exists_det_ne_zero x a b m ha hb hm hab ham hbm hx lam mu hlam hmu
  intro q
  obtain ⟨c, h1, h2⟩ := surjective_of_det_ne_zero (ell := ellCoeff x a b lam)
    (ell' := ellCoeff' x a m mu) (j := j) (j' := j') (sub_ne_zero.mpr hj) q.1 q.2
  exact ⟨c, Prod.ext h1 h2⟩

end

end Work.Drive
