import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chi_one_add_primePow_isPrimitiveRoot
import Submission.Commons.NumberTheory.GaussSum.prime_field_quadratic_bound
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_criticalClasses
import Submission.Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow
import Submission.Commons.RingTheory.ZMod.prod_signed_quad_expand
import Submission.Commons.NumberTheory.GaussSum.quadratic_gauss_primitive_root

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000
set_option autoImplicit true
set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

variable {p e ℓ M : ℕ}

variable [NeZero p]

/-! ## Elementary ring lemmas in `ZMod (p^e)` -/

/-- `p ^ ℓ` as an element of `ZMod (p ^ e)`. -/
noncomputable def pPow (p e ℓ : ℕ) : ZMod (p ^ e) := (((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e))

/-- In `ZMod (p ^ e)`, `(p ^ ℓ) ^ 2 = 0` as soon as `2 * ℓ ≥ e`. -/
lemma primePow_sq_eq_zero (h : e ≤ 2 * ℓ) :
    (((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e)) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  rw [show ((p ^ ℓ) ^ 2 : ℕ) = p ^ (2 * ℓ) by rw [← pow_mul]; ring]
  rw [ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p h

/-- **Deep linearity.**  If `2 * ℓ ≥ e` then `(1 + p^ℓ * x) ^ n = 1 + n * (p^ℓ * x)`
in `ZMod (p ^ e)`, because `(p^ℓ * x)^2 = 0`. -/
lemma one_add_primePow_pow (h : e ≤ 2 * ℓ) (x : ZMod (p ^ e)) (n : ℕ) :
    (1 + (((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e)) * x) ^ n
      = 1 + (n : ZMod (p ^ e)) * ((((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e)) * x) := by
  have h2 : ((((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e)) * x) ^ 2 = 0 := by
    rw [mul_pow, primePow_sq_eq_zero (p := p) (e := e) h, zero_mul]
  exact CharCorr.pow_one_add_eq_of_sq_eq_zero h2 n


/-! ## Values of a Dirichlet character on units -/

/-- Deep linearity in the `pPow` notation. -/
lemma one_add_pPow_pow (h : e ≤ 2 * ℓ) (x : ZMod (p ^ e)) (n : ℕ) :
    (1 + pPow p e ℓ * x) ^ n = 1 + (n : ZMod (p ^ e)) * (pPow p e ℓ * x) := by
  rw [pPow]; exact one_add_primePow_pow h x n

/-- `χ` of a unit of `ZMod N` has norm one. -/
lemma norm_apply_unit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    ‖χ ((u : ZMod N))‖ = 1 := by
  have hpow : (χ ((u : ZMod N))) ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have hpos : 0 < Fintype.card (ZMod N)ˣ := Fintype.card_pos_iff.mpr ⟨1⟩
  have h1 : ‖χ ((u : ZMod N))‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← norm_pow, hpow, norm_one]
  rcases lt_trichotomy ‖χ ((u : ZMod N))‖ 1 with h | h | h
  · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg _) h hpos.ne'))
  · exact h
  · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hpos.ne'))

/-- `conj (χ u) = χ u⁻¹` for a unit `u`. -/
lemma star_apply_eq_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    (starRingEnd ℂ) (χ ((u : ZMod N))) = χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) := by
  have hnorm : ‖χ ((u : ZMod N))‖ = 1 := norm_apply_unit χ u
  have hconj : (starRingEnd ℂ) (χ ((u : ZMod N))) = (χ ((u : ZMod N)))⁻¹ :=
    (Complex.inv_eq_conj hnorm).symm
  rw [hconj]
  have h1 : χ ((u : ZMod N)) * χ (((u⁻¹ : (ZMod N)ˣ) : ZMod N)) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact (eq_inv_of_mul_eq_one_right h1).symm

/-- In `ZMod (p^e)`, `1 + x` is a unit whenever `x ^ e = 0`. -/
lemma isUnit_one_add_of_pow_eq_zero (x : ZMod (p ^ e)) (hx : x ^ e = 0) : IsUnit (1 + x) := by
  refine isUnit_iff_exists_inv.mpr ⟨∑ i ∈ Finset.range e, (-x) ^ i, ?_⟩
  have hne : (-x) ^ e = 0 := by rw [neg_pow, hx, mul_zero]
  have h := geom_sum_mul_neg (-x) e
  rw [show (1 : ZMod (p ^ e)) - (-x) = 1 + x by ring, hne, sub_zero] at h
  rw [mul_comm (∑ i ∈ Finset.range e, (-x) ^ i) (1 + x)] at h
  exact h

/-- `1 + p^ℓ * A * w` is a unit of `ZMod (p^e)` for `ℓ ≥ 1`. -/
lemma isUnit_one_add_primePow_mul (hℓ : 1 ≤ ℓ) (A w : ZMod (p ^ e)) :
    IsUnit (1 + (((p : ℕ) ^ ℓ : ℕ) : ZMod (p ^ e)) * A * w) := by
  refine isUnit_one_add_of_pow_eq_zero (p := p) (e := e) _ ?_
  rw [show (((p:ℕ)^ℓ : ℕ) : ZMod (p^e)) * A * w = ((p:ℕ)^ℓ : ℕ) * (A * w) by ring, mul_pow]
  have h0 : ((((p:ℕ)^ℓ : ℕ) : ZMod (p^e))) ^ e = 0 := by
    rw [← Nat.cast_pow, show ((p ^ ℓ) ^ e : ℕ) = p ^ (ℓ * e) by rw [pow_mul],
      ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by have : 0 < ℓ := hℓ; nlinarith)
  rw [h0, zero_mul]

/-- `1 + p^ℓ * A * w` is a unit of `ZMod (p^e)` for `ℓ ≥ 1` (product-coordinate form). -/
lemma isUnit_one_add_pPow_mul (hℓ : 1 ≤ ℓ) (A w : ZMod (p ^ e)) :
    IsUnit (1 + pPow p e ℓ * A * w) := by
  rw [pPow]; exact isUnit_one_add_primePow_mul hℓ A w

/-- The product of four factors with signs `(+,+,-,-)`, all of whose pairwise products
vanish, collapses to `1 + (a + b - c - d)`. -/
lemma prod_signed_eq_one_add (a b c d : ZMod (p ^ e))
    (hab : a * b = 0) (hac : a * c = 0) (had : a * d = 0)
    (hbc : b * c = 0) (hbd : b * d = 0) (hcd : c * d = 0)
    (hcc : c * c = 0) (hdd : d * d = 0) :
    (1 + a) * (1 + b) * (1 + c)⁻¹ * (1 + d)⁻¹ = 1 + (a + b - c - d) := by
  have hcinv : (1 + c)⁻¹ = 1 - c :=
    ZMod.inv_eq_of_mul_eq_one _ _ _ (by linear_combination -hcc)
  have hdinv : (1 + d)⁻¹ = 1 - d :=
    ZMod.inv_eq_of_mul_eq_one _ _ _ (by linear_combination -hdd)
  rw [hcinv, hdinv]
  have h1 : (1 + a) * (1 + b) = 1 + (a + b) := by linear_combination hab
  have h2 : (1 - c) * (1 - d) = 1 - (c + d) := by linear_combination hcd
  have h3 : (a + b) * (c + d) = 0 := by linear_combination hac + had + hbc + hbd
  rw [h1]
  rw [show (1 + (a + b)) * (1 - c) * (1 - d) = (1 + (a + b)) * ((1 - c) * (1 - d)) by ring,
    h2]
  linear_combination -h3

/-- The geometric sum of a `p`-th root of unity over `ZMod p`. -/
lemma sum_zmod_pow_eq (p : ℕ) [NeZero p] {ζ : ℂ} (hζ : ζ ^ p = 1) :
    ∑ t : ZMod p, ζ ^ (t.val) = if ζ = 1 then (p : ℂ) else 0 := by
  rw [Commons.NumberTheory.GaussSum.zmod_sum_range p (fun t : ZMod p => ζ ^ (t.val))]
  have hcongr : ∀ j ∈ Finset.range p, ζ ^ (((j : ZMod p)).val) = ζ ^ j := by
    intro j hj
    congr 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl hcongr]
  by_cases h : ζ = 1
  · subst h; simp
  · rw [if_neg h]
    have hmul := geom_sum_mul ζ p
    rw [hζ, sub_self] at hmul
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') h

open scoped BigOperators


/-! ## The level-`ℓ` phase and its product coordinate -/

/-- The "product coordinate" `∏_u (1 + p^ℓ a_u w)^{ε_u}` at level `ℓ`, with the
sign pattern `(+,+,-,-)`. -/
noncomputable def prodCoord (p e ℓ : ℕ) (A B C D : ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    ZMod (p ^ e) :=
  (1 + pPow p e ℓ * A * w) * (1 + pPow p e ℓ * B * w)
    * (1 + pPow p e ℓ * C * w)⁻¹ * (1 + pPow p e ℓ * D * w)⁻¹

/-- The "phase" `χ(1+p^ℓ a w) χ(1+p^ℓ b w) conj χ(1+p^ℓ c w) conj χ(1+p^ℓ d w)` at level `ℓ`. -/
noncomputable def phase (p e ℓ : ℕ) (χ : DirichletCharacter ℂ (p ^ e)) (A B C D : ZMod (p ^ e))
    (w : ZMod (p ^ e)) : ℂ :=
  χ (1 + pPow p e ℓ * A * w) * χ (1 + pPow p e ℓ * B * w)
    * (starRingEnd ℂ) (χ (1 + pPow p e ℓ * C * w))
    * (starRingEnd ℂ) (χ (1 + pPow p e ℓ * D * w))

/-- The sum of the level-`ℓ` phase over the lifts of `ZMod (p^M)`. -/
noncomputable def levelSum (p e ℓ M : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ e))
    (A B C D : ZMod (p ^ e)) : ℂ :=
  ∑ w : ZMod (p ^ M), phase p e ℓ χ A B C D ((w.val : ℕ) : ZMod (p ^ e))

/-- `conj (χ x) = χ x⁻¹` for a unit `x`. -/
lemma star_chi_eq_chi_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ZMod N)
    (hx : IsUnit x) : (starRingEnd ℂ) (χ x) = χ x⁻¹ := by
  have h := star_apply_eq_inv χ hx.unit
  rw [IsUnit.unit_spec] at h
  rw [h, ← ZMod.inv_coe_unit, IsUnit.unit_spec]

/-- The phase is the character of the product coordinate. -/
lemma phase_eq_chi_prodCoord (hℓ : 1 ≤ ℓ) (χ : DirichletCharacter ℂ (p ^ e))
    (A B C D w : ZMod (p ^ e)) :
    phase p e ℓ χ A B C D w = χ (prodCoord p e ℓ A B C D w) := by
  have hA : IsUnit (1 + pPow p e ℓ * A * w) := by
    rw [pPow]; exact isUnit_one_add_primePow_mul (p := p) (e := e) hℓ A w
  have hB : IsUnit (1 + pPow p e ℓ * B * w) := by
    rw [pPow]; exact isUnit_one_add_primePow_mul (p := p) (e := e) hℓ B w
  have hC : IsUnit (1 + pPow p e ℓ * C * w) := by
    rw [pPow]; exact isUnit_one_add_primePow_mul (p := p) (e := e) hℓ C w
  have hD : IsUnit (1 + pPow p e ℓ * D * w) := by
    rw [pPow]; exact isUnit_one_add_primePow_mul (p := p) (e := e) hℓ D w
  simp only [phase, prodCoord]
  rw [star_chi_eq_chi_inv χ _ hC, star_chi_eq_chi_inv χ _ hD]
  rw [← map_mul, ← map_mul, ← map_mul]

/-- The level sum as a sum of `χ` of the product coordinate. -/
lemma levelSum_eq_sum_chi_prodCoord (hℓ : 1 ≤ ℓ) (χ : DirichletCharacter ℂ (p ^ e))
    (A B C D : ZMod (p ^ e)) :
    levelSum p e ℓ M χ A B C D
      = ∑ w : ZMod (p ^ M), χ (prodCoord p e ℓ A B C D ((w.val : ℕ) : ZMod (p ^ e))) := by
  refine Finset.sum_congr rfl fun w _ => ?_
  exact phase_eq_chi_prodCoord (p := p) (e := e) (ℓ := ℓ) hℓ χ A B C D _

/-- `(x * y)⁻¹ = x⁻¹ * y⁻¹` for units of a commutative ring. -/
lemma inv_mul_eq_mul_inv (x y : ZMod (p ^ e)) (hx : IsUnit x) (hy : IsUnit y) :
    (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
  rw [show x * y * (x⁻¹ * y⁻¹) = (x * x⁻¹) * (y * y⁻¹) by ring,
    ZMod.mul_inv_of_unit x hx, ZMod.mul_inv_of_unit y hy, one_mul]

/-- The elementary factorisation `(1+X) * (1 + (Y * u) * t) = 1 + X + Y * t` for `u` an
inverse of `1 + X`. -/
lemma one_add_mul_one_add_mul_inv {R : Type*} [CommRing R] (X Y t u : R)
    (h : (1 + X) * u = 1) :
    (1 + X) * (1 + (Y * u) * t) = 1 + X + Y * t := by
  calc (1 + X) * (1 + (Y * u) * t)
      = (1 + X) + (1 + X) * ((Y * u) * t) := by ring
    _ = (1 + X) + ((1 + X) * u) * (Y * t) := by ring
    _ = (1 + X) + Y * t := by rw [h, one_mul]

/-- **The single-term factorisation.**  The factor `1 + p^ℓ U (w' + p^(M-1) t)` splits as
`(1 + p^ℓ U w') * (1 + p^(ℓ+M-1) U (1 + p^ℓ U w')⁻¹ t)`. -/
lemma one_add_primePow_factor (hℓ : 1 ≤ ℓ) (hM : 1 ≤ M) (U w' t : ZMod (p ^ e)) :
    (1 + pPow p e ℓ * U * (w' + ((p : ℕ) ^ (M - 1) : ℕ) * t))
      = (1 + pPow p e ℓ * U * w')
        * (1 + pPow p e (ℓ + M - 1) * (U * (1 + pPow p e ℓ * U * w')⁻¹) * t) := by
  have hP : pPow p e (ℓ + M - 1) = pPow p e ℓ * (((p : ℕ) ^ (M - 1) : ℕ) : ZMod (p ^ e)) := by
    rw [pPow, pPow, ← Nat.cast_mul]
    congr 1
    rw [← pow_add]
    congr 1
    omega
  have hxinv : (1 + pPow p e ℓ * U * w') * (1 + pPow p e ℓ * U * w')⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (by rw [pPow]; exact isUnit_one_add_primePow_mul hℓ U w')
  have hstep : (1 + pPow p e ℓ * U * w')
      * (1 + pPow p e ℓ * (((p : ℕ) ^ (M - 1) : ℕ) : ZMod (p ^ e))
          * (U * (1 + pPow p e ℓ * U * w')⁻¹) * t)
      = 1 + pPow p e ℓ * U * w'
        + pPow p e ℓ * (((p : ℕ) ^ (M - 1) : ℕ) : ZMod (p ^ e)) * U * t := by
    have h := one_add_mul_one_add_mul_inv (X := pPow p e ℓ * U * w')
      (Y := pPow p e ℓ * (((p : ℕ) ^ (M - 1) : ℕ) : ZMod (p ^ e)) * U) (t := t)
      (u := (1 + pPow p e ℓ * U * w')⁻¹) hxinv
    linear_combination h
  rw [hP, hstep]
  ring

/-- **The single-term factorisation of the product coordinate.** -/
lemma prodCoord_peel (hℓ : 1 ≤ ℓ) (hM : 1 ≤ M) (A B C D : ZMod (p ^ e))
    (w' t : ZMod (p ^ e)) :
    prodCoord p e ℓ A B C D (w' + ((p : ℕ) ^ (M - 1) : ℕ) * t)
      = prodCoord p e ℓ A B C D w'
        * prodCoord p e (ℓ + M - 1)
            (A * (1 + pPow p e ℓ * A * w')⁻¹) (B * (1 + pPow p e ℓ * B * w')⁻¹)
            (C * (1 + pPow p e ℓ * C * w')⁻¹) (D * (1 + pPow p e ℓ * D * w')⁻¹) t := by
  have hℓ' : 1 ≤ ℓ + M - 1 := by omega
  simp only [prodCoord]
  rw [one_add_primePow_factor (p := p) (e := e) hℓ hM A w' t,
    one_add_primePow_factor (p := p) (e := e) hℓ hM B w' t,
    one_add_primePow_factor (p := p) (e := e) hℓ hM C w' t,
    one_add_primePow_factor (p := p) (e := e) hℓ hM D w' t]
  rw [inv_mul_eq_mul_inv _ _ (by rw [pPow]; exact isUnit_one_add_primePow_mul hℓ C w')
      (by rw [pPow]; exact isUnit_one_add_primePow_mul hℓ' (C * (1 + pPow p e ℓ * C * w')⁻¹) t),
    inv_mul_eq_mul_inv _ _ (by rw [pPow]; exact isUnit_one_add_primePow_mul hℓ D w')
      (by rw [pPow]; exact isUnit_one_add_primePow_mul hℓ' (D * (1 + pPow p e ℓ * D * w')⁻¹) t)]
  ring


/-! ## The top-level character value and vanishing lemmas -/

/-- `χ (1 + p^(e-1) * y) = ζ ^ y.val` where `ζ = χ (1 + p^(e-1))`. -/
lemma chi_top_level (he : 2 ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (y : ZMod (p ^ e)) :
    χ (1 + pPow p e (e - 1) * y)
      = (χ (1 + pPow p e (e - 1))) ^ y.val := by
  have hsq : pPow p e (e - 1) ^ 2 = 0 := by
    rw [pPow, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    rw [show ((p ^ (e - 1)) ^ 2 : ℕ) = p ^ (2 * (e - 1)) by rw [← pow_mul]; ring]
    exact pow_dvd_pow p (by omega)
  have h1 : (1 + pPow p e (e - 1) * y)
      = (1 + ((y.val : ℕ) : ZMod (p ^ e)) * pPow p e (e - 1)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    ring
  rw [h1, ← map_pow χ (1 + pPow p e (e - 1)) y.val,
    ← CharCorr.pow_one_add_eq_of_sq_eq_zero hsq y.val]

/-- If `p^j ∣ z.val` in `ZMod (p^e)` and `j + ℓ ≥ e`, then `p^ℓ * z = 0`. -/
lemma pPow_mul_eq_zero_of_dvd_val {j ℓ : ℕ} (z : ZMod (p ^ e))
    (h : p ^ j ∣ z.val) (hj : e ≤ j + ℓ) : pPow p e ℓ * z = 0 := by
  obtain ⟨k, hk⟩ := h
  have hz : z = ((p ^ j * k : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.natCast_zmod_val z, hk]
  rw [hz, pPow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  rw [show p ^ ℓ * (p ^ j * k) = p ^ (j + ℓ) * k by ring]
  exact dvd_mul_of_dvd_left (pow_dvd_pow p hj) k

/-- **First-order expansion of the product coordinate.**  If `2 * ℓ ≥ e` then the
pairwise products of the four elementary factors vanish and
`∏_u (1 + p^ℓ a_u w)^{ε_u} = 1 + (a_1 + a_2 - a_3 - a_4) * p^ℓ * w`. -/
lemma prodCoord_eq_one_add (h : e ≤ 2 * ℓ) (A B C D w : ZMod (p ^ e)) :
    prodCoord p e ℓ A B C D w
      = 1 + (A + B - C - D) * pPow p e ℓ * w := by
  have hsq : pPow p e ℓ * pPow p e ℓ = 0 := by
    rw [pPow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    rw [show (p ^ ℓ) * (p ^ ℓ) = p ^ (ℓ + ℓ) by ring]
    exact pow_dvd_pow p (by omega)
  have key : ∀ U V : ZMod (p ^ e),
      (pPow p e ℓ * U * w) * (pPow p e ℓ * V * w) = 0 := by
    intro U V
    rw [show (pPow p e ℓ * U * w) * (pPow p e ℓ * V * w)
        = (pPow p e ℓ * pPow p e ℓ) * (U * w * V * w) by ring, hsq, zero_mul]
  rw [prodCoord, prod_signed_eq_one_add (a := pPow p e ℓ * A * w) (b := pPow p e ℓ * B * w)
    (c := pPow p e ℓ * C * w) (d := pPow p e ℓ * D * w)
    (key A B) (key A C) (key A D) (key B C) (key B D) (key C D)
    (by rw [key C C]) (by rw [key D D])]
  ring


/-! ## Powers of `p` and the geometric expansion -/

lemma pPow_mul_pPow (i j : ℕ) : pPow p e i * pPow p e j = pPow p e (i + j) := by
  rw [pPow, pPow, pPow, ← Nat.cast_mul, ← pow_add]

lemma pPow_eq_zero_of_le (h : e ≤ j) : pPow p e j = 0 := by
  rw [pPow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p h

/-- The key geometric expansion: for `ℓ ≥ 1` and `ℓ' = e - ℓ - 1`,
`p^{ℓ'} · U (1 + p^ℓ U x)⁻¹ = p^{ℓ'} U - p^{e-1} U^2 x`. -/
lemma pPow_mul_inv_expand (hℓ : 1 ≤ ℓ) (he : 2 * ℓ ≤ e) (U x : ZMod (p ^ e)) :
    pPow p e (e - ℓ - 1) * (U * (1 + pPow p e ℓ * U * x)⁻¹)
      = pPow p e (e - ℓ - 1) * U - pPow p e (e - 1) * U ^ 2 * x := by
  set y : ZMod (p ^ e) := pPow p e ℓ * U * x with hy
  have hunit : (1 + y) * (1 + y)⁻¹ = 1 := by
    rw [hy]; exact ZMod.mul_inv_of_unit _ (isUnit_one_add_pPow_mul hℓ U x)
  have hyinv : (1 + y)⁻¹ = 1 - y + y ^ 2 * (1 + y)⁻¹ := by
    refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
    calc (1 + y) * (1 - y + y ^ 2 * (1 + y)⁻¹)
        = (1 - y ^ 2) + y ^ 2 * ((1 + y) * (1 + y)⁻¹) := by ring
      _ = (1 - y ^ 2) + y ^ 2 := by rw [hunit, mul_one]
      _ = 1 := by ring
  have h_a : pPow p e (e - ℓ - 1) * y * U = pPow p e (e - 1) * U ^ 2 * x := by
    rw [hy]
    calc pPow p e (e - ℓ - 1) * (pPow p e ℓ * U * x) * U
        = (pPow p e (e - ℓ - 1) * pPow p e ℓ) * (U * x * U) := by ring
      _ = pPow p e (e - 1) * (U * x * U) := by
          have h : e - ℓ - 1 + ℓ = e - 1 := by omega
          rw [pPow_mul_pPow, h]
      _ = pPow p e (e - 1) * U ^ 2 * x := by ring
  have h_b : pPow p e (e - ℓ - 1) * U * y ^ 2 * (1 + y)⁻¹ = 0 := by
    rw [hy]
    calc pPow p e (e - ℓ - 1) * U * (pPow p e ℓ * U * x) ^ 2 * (1 + pPow p e ℓ * U * x)⁻¹
        = (pPow p e (e - ℓ - 1) * pPow p e ℓ * pPow p e ℓ)
            * (U * U ^ 2 * x ^ 2) * (1 + pPow p e ℓ * U * x)⁻¹ := by ring
      _ = 0 := by
          have h : e - ℓ - 1 + ℓ + ℓ = (e - ℓ - 1) + ℓ + ℓ := rfl
          rw [show pPow p e (e - ℓ - 1) * pPow p e ℓ * pPow p e ℓ
              = pPow p e ((e - ℓ - 1) + ℓ + ℓ) by
                rw [pPow_mul_pPow, pPow_mul_pPow]]
          rw [pPow_eq_zero_of_le (by omega)]
          ring
  rw [show U * (1 + pPow p e ℓ * U * x)⁻¹ = U * (1 + y)⁻¹ by rw [hy], hyinv]
  have expand : pPow p e (e - ℓ - 1) * (U * (1 - y + y ^ 2 * (1 + y)⁻¹))
      = pPow p e (e - ℓ - 1) * U - pPow p e (e - ℓ - 1) * U * y
        + pPow p e (e - ℓ - 1) * U * y ^ 2 * (1 + y)⁻¹ := by ring
  rw [expand,
    show pPow p e (e - ℓ - 1) * U * y = pPow p e (e - 1) * U ^ 2 * x by
      rw [show pPow p e (e - ℓ - 1) * U * y = pPow p e (e - ℓ - 1) * y * U by ring, h_a],
    h_b]
  ring

/-- The level sum as a sum over `Finset.range`. -/
lemma levelSum_eq_range_sum (χ : DirichletCharacter ℂ (p ^ e)) (A B C D : ZMod (p ^ e)) :
    levelSum p e ℓ M χ A B C D
      = ∑ n ∈ Finset.range (p ^ M), phase p e ℓ χ A B C D ((n : ℕ) : ZMod (p ^ e)) := by
  rw [levelSum, Commons.NumberTheory.GaussSum.zmod_sum_range (p ^ M)
    (fun w : ZMod (p ^ M) => phase p e ℓ χ A B C D ((w.val : ℕ) : ZMod (p ^ e)))]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hval : (((n : ZMod (p ^ M))).val : ℕ) = n := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
  rw [hval]

/-- If `p^j ∣ m` and `j ≤ e` then `p^j` divides the representative of `m` in `ZMod (p^e)`. -/
lemma dvd_val_natCast {j m : ℕ} (hj : j ≤ e) (h : p ^ j ∣ m) :
    p ^ j ∣ (((m : ℕ) : ZMod (p ^ e))).val := by
  obtain ⟨c, hc⟩ := h
  rw [hc, ZMod.val_natCast]
  have h1 : (p ^ j * c) % p ^ e ≡ 0 [MOD p ^ j] :=
    (Nat.ModEq.of_dvd (pow_dvd_pow p hj) (Nat.mod_modEq (p ^ j * c) (p ^ e))).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))
  exact Nat.modEq_zero_iff_dvd.mp h1

/-- **First-order expansion, modulo `p^(ℓ+1)`.**  For `ℓ ≥ 1`,
`U (1 + p^ℓ U x)⁻¹ ≡ U - p^ℓ U^2 x  (mod p^(ℓ+1))`. -/
lemma inv_expand_dvd (hℓ : 1 ≤ ℓ) (he : 2 * ℓ ≤ e) (U x : ZMod (p ^ e)) :
    p ^ (ℓ + 1) ∣ (U * (1 + pPow p e ℓ * U * x)⁻¹ - (U - pPow p e ℓ * U ^ 2 * x)).val := by
  set y : ZMod (p ^ e) := pPow p e ℓ * U * x with hy
  have hunit : (1 + y) * (1 + y)⁻¹ = 1 := by
    rw [hy]; exact ZMod.mul_inv_of_unit _ (isUnit_one_add_pPow_mul hℓ U x)
  have hyinv : (1 + y)⁻¹ = 1 - y + y ^ 2 * (1 + y)⁻¹ := by
    refine ZMod.inv_eq_of_mul_eq_one _ _ _ ?_
    calc (1 + y) * (1 - y + y ^ 2 * (1 + y)⁻¹)
        = (1 - y ^ 2) + y ^ 2 * ((1 + y) * (1 + y)⁻¹) := by ring
      _ = (1 - y ^ 2) + y ^ 2 := by rw [hunit, mul_one]
      _ = 1 := by ring
  have hdiff : U * (1 + pPow p e ℓ * U * x)⁻¹ - (U - pPow p e ℓ * U ^ 2 * x)
      = (pPow p e ℓ * pPow p e ℓ) * (U ^ 3 * x ^ 2 * (1 + pPow p e ℓ * U * x)⁻¹) := by
    rw [show (1 + pPow p e ℓ * U * x)⁻¹ = (1 + y)⁻¹ by rw [hy], hyinv]
    rw [show y ^ 2 * (1 + y)⁻¹ = (y - 1) + (1 + y)⁻¹ by
      linear_combination (y - 1) * hunit]
    rw [hy] at hunit ⊢
    linear_combination (U * (1 - pPow p e ℓ * U * x)) * hunit
  rw [hdiff]
  rw [show pPow p e ℓ * pPow p e ℓ = pPow p e (2 * ℓ) by rw [pPow_mul_pPow, show ℓ + ℓ = 2 * ℓ by omega]]
  have hcast : pPow p e (2 * ℓ) * (U ^ 3 * x ^ 2 * (1 + pPow p e ℓ * U * x)⁻¹)
      = (((p ^ (2 * ℓ) * (U ^ 3 * x ^ 2 * (1 + pPow p e ℓ * U * x)⁻¹).val : ℕ)) : ZMod (p ^ e)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (U ^ 3 * x ^ 2 * (1 + pPow p e ℓ * U * x)⁻¹)]
    rw [pPow]
    push_cast
    ring
  rw [hcast]
  refine dvd_val_natCast (j := ℓ + 1) (by omega) (dvd_mul_of_dvd_left ?_ _)
  rw [show p ^ (2 * ℓ) = p ^ (ℓ + 1) * p ^ (2 * ℓ - (ℓ + 1)) by
    rw [← pow_add]; congr 1; omega]
  exact dvd_mul_right _ _


/-! ## Reduction modulo `p^j` -/

/-- The reduction `ZMod (p^e) → ZMod (p^j)` vanishes iff `p^j` divides the representative. -/
lemma castHom_eq_zero_iff_dvd_val {j : ℕ} (hd : p ^ j ∣ p ^ e) (z : ZMod (p ^ e)) :
    ZMod.castHom hd (ZMod (p ^ j)) z = 0 ↔ p ^ j ∣ z.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- In `ZMod (p^(ℓ+1))`, multiplication by `p^ℓ` vanishes iff `p` divides the representative. -/
lemma pPow_mul_eq_zero_iff (_hp : 0 < p) (hℓ : 1 ≤ ℓ) (w : ZMod (p ^ (ℓ + 1))) :
    pPow p (ℓ + 1) ℓ * w = 0 ↔ (p : ℕ) ∣ w.val := by
  have hw : pPow p (ℓ + 1) ℓ * w
      = (((p ^ ℓ * w.val : ℕ)) : ZMod (p ^ (ℓ + 1))) := by
    conv_lhs => rw [pPow, ← ZMod.natCast_zmod_val w]
    push_cast
    ring
  rw [hw, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_iff_left (pow_pos _hp ℓ)

/-- **Termwise first-order expansion, modulo `p^(ℓ+1)`.** -/
lemma castHom_inv_expand (hℓ : 1 ≤ ℓ) (hd : p ^ (ℓ + 1) ∣ p ^ e) (U x : ZMod (p ^ e)) :
    ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (U * (1 + pPow p e ℓ * U * x)⁻¹)
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) U
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
          * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) U ^ 2
          * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x := by
  set u : ZMod (p ^ (ℓ + 1)) := ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) U with hu
  set q : ZMod (p ^ (ℓ + 1)) := ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ) with hq
  set xx : ZMod (p ^ (ℓ + 1)) := ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x with hxx
  have hq2 : q ^ 2 = 0 := by
    rw [hq, ← map_pow,
      show pPow p e ℓ ^ 2 = pPow p e (2 * ℓ) by
        rw [show pPow p e ℓ ^ 2 = pPow p e ℓ * pPow p e ℓ by ring, pPow_mul_pPow,
          show ℓ + ℓ = 2 * ℓ by omega],
      pPow, map_natCast, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by omega)
  have h1 : ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (1 + pPow p e ℓ * U * x) = 1 + q * u * xx := by
    rw [map_add, map_one, map_mul, map_mul, hq, hu, hxx]
  have hU : U * (1 + pPow p e ℓ * U * x)⁻¹ * (1 + pPow p e ℓ * U * x) = U := by
    rw [mul_assoc, ZMod.inv_mul_of_unit _ (isUnit_one_add_pPow_mul hℓ U x), mul_one]
  have h2 : ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (U * (1 + pPow p e ℓ * U * x)⁻¹)
      * (1 + q * u * xx) = u := by
    rw [← h1, ← map_mul, hU, hu]
  have h3 : (1 + q * u * xx) * (1 - q * u * xx) = 1 := by
    rw [show (1 + q * u * xx) * (1 - q * u * xx) = 1 - (q * (u * xx)) ^ 2 by ring,
      mul_pow, hq2, zero_mul, sub_zero]
  have hunit : IsUnit (1 + q * u * xx) := isUnit_iff_exists_inv.mpr ⟨1 - q * u * xx, h3⟩
  calc ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (U * (1 + pPow p e ℓ * U * x)⁻¹)
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (U * (1 + pPow p e ℓ * U * x)⁻¹)
        * ((1 + q * u * xx) * (1 + q * u * xx)⁻¹) := by
          rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
    _ = (ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (U * (1 + pPow p e ℓ * U * x)⁻¹)
        * (1 + q * u * xx)) * (1 + q * u * xx)⁻¹ := by ring
    _ = u * (1 + q * u * xx)⁻¹ := by rw [h2]
    _ = u * (1 - q * u * xx) := by rw [ZMod.inv_eq_of_mul_eq_one _ _ _ h3]
    _ = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) U
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
          * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) U ^ 2
          * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x := by
          rw [hu, hq, hxx]; ring


/-- **Summed first-order expansion of the "derivative" `G` modulo `p^(ℓ+1)`.** -/
lemma G_expand (hℓ : 1 ≤ ℓ) (hd : p ^ (ℓ + 1) ∣ p ^ e) (κ : ℕ)
    (hsum : A + B - C - D = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e))) (x : ZMod (p ^ e)) :
    ZMod.castHom hd (ZMod (p ^ (ℓ + 1)))
        (A * (1 + pPow p e ℓ * A * x)⁻¹ + B * (1 + pPow p e ℓ * B * x)⁻¹
          - C * (1 + pPow p e ℓ * C * x)⁻¹ - D * (1 + pPow p e ℓ * D * x)⁻¹)
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
        * (((κ : ℕ) : ZMod (p ^ (ℓ + 1)))
          - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x
            * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2)) := by
  have step1 : ZMod.castHom hd (ZMod (p ^ (ℓ + 1)))
        (A * (1 + pPow p e ℓ * A * x)⁻¹ + B * (1 + pPow p e ℓ * B * x)⁻¹
          - C * (1 + pPow p e ℓ * C * x)⁻¹ - D * (1 + pPow p e ℓ * D * x)⁻¹)
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) A + ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) B
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) C - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) D
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ)
          * ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) x
          * (ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) A ^ 2
            + ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) B ^ 2
            - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) C ^ 2
            - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) D ^ 2) := by
    rw [map_sub, map_sub, map_add,
      castHom_inv_expand hℓ hd A x, castHom_inv_expand hℓ hd B x,
      castHom_inv_expand hℓ hd C x, castHom_inv_expand hℓ hd D x]
    ring
  have step2 : ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) A + ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) B
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) C - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) D
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ) * ((κ : ℕ) : ZMod (p ^ (ℓ + 1))) := by
    rw [← map_add, ← map_sub, ← map_sub, hsum, map_natCast, pPow, map_natCast]
    push_cast
    ring
  have step3 : ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2)
      = ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) A ^ 2 + ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) B ^ 2
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) C ^ 2
        - ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) D ^ 2 := by
    rw [map_sub, map_sub, map_add, map_pow, map_pow, map_pow, map_pow]
  rw [step1, step2, step3]
  ring


/-- The geometric sum of a `p`-th root of unity over `Finset.range p`. -/
lemma sum_range_pow_eq (p : ℕ) {η : ℂ} (hη : η ^ p = 1) :
    ∑ t ∈ Finset.range p, η ^ t = if η = 1 then (p : ℂ) else 0 := by
  by_cases h : η = 1
  · subst h; simp
  · rw [if_neg h]
    have hmul := geom_sum_mul η p
    rw [hη, sub_self] at hmul
    rcases mul_eq_zero.mp hmul with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') h

/-- The integers below `p^(k+1)` in the residue class `c mod p` are exactly `c + p*m`. -/
lemma sum_range_filter_mod_eq (p c k : ℕ) (hc : c < p) (f : ℕ → ℂ) :
    ∑ n ∈ (Finset.range (p ^ (k + 1))).filter (fun n => n % p = c), f n
      = ∑ m ∈ Finset.range (p ^ k), f (c + p * m) := by
  have hset : (Finset.range (p ^ (k + 1))).filter (fun n => n % p = c)
      = (Finset.range (p ^ k)).image (fun m => c + p * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hn1, hn2⟩
      refine ⟨n / p, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < p)]
        rw [show p ^ (k + 1) = p ^ k * p by rw [pow_succ]] at hn1
        exact hn1
      · conv_rhs => rw [← Nat.mod_add_div n p]
        rw [hn2]
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [show p ^ (k + 1) = p ^ k * p by rw [pow_succ]]
        calc c + p * m < p + p * m := Nat.add_lt_add_right hc _
          _ = p * (m + 1) := by ring
          _ ≤ p * p ^ k := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hm)
          _ = p ^ k * p := by ring
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [hset, Finset.sum_image]
  intro m _ m' _ h
  exact Nat.mul_left_cancel (by omega : 0 < p) (Nat.add_left_cancel h)


/-- Reduction to `ZMod p` vanishes iff `p` divides the representative. -/
lemma castHom_eq_zero_iff_dvd_val_one (hd : p ∣ p ^ e) (z : ZMod (p ^ e)) :
    ZMod.castHom hd (ZMod p) z = 0 ↔ p ∣ z.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- The reduction of `p^ℓ` to `ZMod (p^(ℓ+1))`. -/
lemma castHom_pPow (hd : p ^ (ℓ + 1) ∣ p ^ e) :
    ZMod.castHom hd (ZMod (p ^ (ℓ + 1))) (pPow p e ℓ) = pPow p (ℓ + 1) ℓ := by
  rw [pPow, map_natCast, pPow]

/-- One stationary-phase step: the level-`ℓ` sum over `ZMod (p^M)` equals `p` times the
level-`(ℓ+1)` sum over `ZMod (p^(M-2))`, with residual units `a_u (1 + p^ℓ a_u c)⁻¹`. -/
theorem level_step (p e ℓ M : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (hℓ : 1 ≤ ℓ) (hM : 2 ≤ M) (heq : e = 2 * ℓ + M)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A B C D : ZMod (p ^ e)) (κ : ℕ)
    (hsum : A + B - C - D = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hnd : ¬ (p : ℕ) ∣ (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2 : ZMod (p ^ e)).val) :
    ∃ (A' B' C' D' : ZMod (p ^ e)) (κ' : ℕ),
      A' + B' - C' - D' = ((p ^ (ℓ + 1) * κ' : ℕ) : ZMod (p ^ e))
      ∧ ¬ (p : ℕ) ∣ (A' ^ 2 + B' ^ 2 - C' ^ 2 - D' ^ 2 : ZMod (p ^ e)).val
      ∧ ‖levelSum p e ℓ M χ A B C D‖
          = (p : ℝ) * ‖levelSum p e (ℓ + 1) (M - 2) χ A' B' C' D'‖ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p (show 1 ≤ e by omega)
  have hdiv' : p ^ (ℓ + 1) ∣ p ^ e := pow_dvd_pow p (by omega)
  have h2ℓ : 2 * ℓ ≤ e := by omega
  have hℓ'e : ℓ + M - 1 = e - ℓ - 1 := by omega
  have h2ℓ' : e ≤ 2 * (ℓ + M - 1) := by omega
  -- ### the reduction data
  set Δ : ZMod (p ^ e) := A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2 with hΔdef
  set δ : ZMod p := ZMod.castHom hdiv1 (ZMod p) Δ with hδdef
  have hδne : δ ≠ 0 := by
    intro h
    apply hnd
    rw [hΔdef, ← castHom_eq_zero_iff_dvd_val_one hdiv1 (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2)]
    exact h
  -- ### the localisation class
  set c₀ : ℕ := ((κ : ZMod p) * δ⁻¹).val with hc₀def
  have hc₀lt : c₀ < p := ZMod.val_lt _
  have hc₀spec : (c₀ : ZMod p) = (κ : ZMod p) * δ⁻¹ := ZMod.natCast_zmod_val _
  set xc : ZMod (p ^ e) := ((c₀ : ℕ) : ZMod (p ^ e)) with hxcdef
  -- ### the localisation condition
  have hcond : ∀ n' : ℕ,
      (p ∣ (((κ : ℕ) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ).val) ↔ n' % p = c₀ := by
    intro n'
    rw [← castHom_eq_zero_iff_dvd_val_one hdiv1
      (((κ : ℕ) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ)]
    rw [map_sub, map_mul, map_natCast, map_natCast, ← hδdef]
    constructor
    · intro h
      have h2 : ((n' : ZMod p)) * δ = (κ : ZMod p) := (sub_eq_zero.mp h).symm
      have h3 : (n' : ZMod p) = (κ : ZMod p) * δ⁻¹ := by
        rw [← h2]
        rw [show (n' : ZMod p) * δ * δ⁻¹ = (n' : ZMod p) * (δ * δ⁻¹) by ring,
          mul_inv_cancel₀ hδne, mul_one]
      have h4 : (n' : ZMod p) = (c₀ : ZMod p) := by rw [h3, hc₀spec]
      have h5 := congrArg ZMod.val h4
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hc₀lt] at h5
      exact h5
    · intro h
      have h2 : (n' : ZMod p) = (c₀ : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' n' c₀ p).mpr (by rw [h, Nat.mod_eq_of_lt hc₀lt])
      rw [sub_eq_zero, h2, hc₀spec, mul_assoc, inv_mul_cancel₀ hδne, mul_one]

  have hcond2 : ∀ n' : ℕ,
      (p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * ((n' : ℕ) : ZMod (p ^ e))).val) ↔ n' % p = c₀ := by
    intro n'
    rw [show ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * ((n' : ℕ) : ZMod (p ^ e)))
        = ((((κ : ℕ)) : ZMod (p ^ e)) - ((n' : ℕ) : ZMod (p ^ e)) * Δ) by ring]
    exact hcond n'
  -- ### the residual units and the derivative
  set θA : ZMod (p ^ e) → ZMod (p ^ e) := fun x => A * (1 + pPow p e ℓ * A * x)⁻¹ with hθA
  set θB : ZMod (p ^ e) → ZMod (p ^ e) := fun x => B * (1 + pPow p e ℓ * B * x)⁻¹ with hθB
  set θC : ZMod (p ^ e) → ZMod (p ^ e) := fun x => C * (1 + pPow p e ℓ * C * x)⁻¹ with hθC
  set θD : ZMod (p ^ e) → ZMod (p ^ e) := fun x => D * (1 + pPow p e ℓ * D * x)⁻¹ with hθD
  set Gfun : ZMod (p ^ e) → ZMod (p ^ e) := fun x => θA x + θB x - θC x - θD x with hGfun
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  -- ### the expansion of the derivative
  have hexpand : ∀ x : ZMod (p ^ e),
      pPow p e (ℓ + M - 1) * Gfun x
        = pPow p e (e - 1) * ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x) := by
    intro x
    have hA' := pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ A x
    have hB' := pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ B x
    have hC' := pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ C x
    have hD' := pPow_mul_inv_expand (p := p) (e := e) (ℓ := ℓ) hℓ h2ℓ D x
    rw [← hℓ'e] at hA' hB' hC' hD'
    have hpp : pPow p e (ℓ + M - 1) * (A + B - C - D)
        = pPow p e (e - 1) * ((κ : ℕ) : ZMod (p ^ e)) := by
      rw [hsum, pPow, pPow, ← Nat.cast_mul, ← Nat.cast_mul]
      congr 1
      have hexp : ℓ + M - 1 + ℓ = e - 1 := by omega
      rw [show p ^ (ℓ + M - 1) * (p ^ ℓ * κ) = p ^ (ℓ + M - 1 + ℓ) * κ by
        rw [← mul_assoc, ← pow_add], hexp]
    simp only [hθA, hθB, hθC, hθD, hGfun, hΔdef]
    linear_combination hA' + hB' - hC' - hD' + hpp

  -- ### the character value of the inner exponential
  have hη : ∀ x : ZMod (p ^ e),
      χ (1 + pPow p e (ℓ + M - 1) * Gfun x)
        = ζ ^ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val := by
    intro x
    rw [hexpand x, chi_top_level (p := p) (e := e) (by omega) χ]
  have hηpow : ∀ x : ZMod (p ^ e),
      (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ p = 1 := by
    intro x
    rw [hη x, ← pow_mul, mul_comm, pow_mul, hζprim.pow_eq_one, one_pow]

  -- ### the inner sum over the last digit
  have hinner : ∀ x : ZMod (p ^ e),
      (∑ t ∈ Finset.range p,
          χ (prodCoord p e (ℓ + M - 1) (θA x) (θB x) (θC x) (θD x) ((t : ℕ) : ZMod (p ^ e))))
        = (p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val then 1 else 0) := by
    intro x
    have hpc : ∀ t ∈ Finset.range p,
        χ (prodCoord p e (ℓ + M - 1) (θA x) (θB x) (θC x) (θD x) ((t : ℕ) : ZMod (p ^ e)))
          = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by
      intro t ht
      calc χ (prodCoord p e (ℓ + M - 1) (θA x) (θB x) (θC x) (θD x) ((t : ℕ) : ZMod (p ^ e)))
          = χ ((1 + pPow p e (ℓ + M - 1) * (θA x + θB x - θC x - θD x)) ^ t) := by
            rw [prodCoord_eq_one_add (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ']
            rw [show (θA x + θB x - θC x - θD x) * pPow p e (ℓ + M - 1) * ((t : ℕ) : ZMod (p ^ e))
                = (t : ZMod (p ^ e)) * (pPow p e (ℓ + M - 1) * (θA x + θB x - θC x - θD x)) by ring,
              ← one_add_pPow_pow (p := p) (e := e) (ℓ := ℓ + M - 1) h2ℓ'
                (θA x + θB x - θC x - θD x) t]
        _ = (χ (1 + pPow p e (ℓ + M - 1) * Gfun x)) ^ t := by
            rw [map_pow, hGfun]
    rw [Finset.sum_congr rfl hpc, sum_range_pow_eq p (hηpow x)]
    by_cases h : p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - Δ * x).val
    · have h2 : χ (1 + pPow p e (ℓ + M - 1) * Gfun x) = 1 := by
        rw [hη x, hζprim.pow_eq_one_iff_dvd]; exact h
      rw [if_pos h2, if_pos h, mul_one]
    · have h2 : χ (1 + pPow p e (ℓ + M - 1) * Gfun x) ≠ 1 := by
        intro hh
        exact h ((hζprim.pow_eq_one_iff_dvd _).mp (by rw [← hη x]; exact hh))
      rw [if_neg h2, if_neg h, mul_zero]

  -- ### the two-level decomposition of the level sum
  have hdecomp : levelSum p e ℓ M χ A B C D
      = ∑ n' ∈ Finset.range (p ^ (M - 1)),
          χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e)))
            * ((p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e))
                - Δ * ((n' : ℕ) : ZMod (p ^ e))).val then 1 else 0)) := by
    rw [levelSum_eq_range_sum]
    have h1 : ∀ n ∈ Finset.range (p ^ M),
        phase p e ℓ χ A B C D ((n : ℕ) : ZMod (p ^ e))
          = χ (prodCoord p e ℓ A B C D ((n : ℕ) : ZMod (p ^ e))) := by
      intro n hn
      exact phase_eq_chi_prodCoord (p := p) (e := e) (ℓ := ℓ) hℓ χ A B C D _
    rw [Finset.sum_congr rfl h1]
    have h2 : p ^ M = p ^ (M - 1) * p := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega]
      rw [pow_succ]
    rw [h2]
    rw [Commons.Algebra.BigOperators.sum_range_mul_eq
      (fun n => χ (prodCoord p e ℓ A B C D ((n : ℕ) : ZMod (p ^ e)))) (p ^ (M - 1)) p]
    refine Finset.sum_congr rfl fun n' hn' => ?_
    have hpeel : ∀ t ∈ Finset.range p,
        χ (prodCoord p e ℓ A B C D (((n' + p ^ (M - 1) * t : ℕ)) : ZMod (p ^ e)))
          = χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e)))
            * χ (prodCoord p e (ℓ + M - 1) (θA ((n' : ℕ) : ZMod (p ^ e)))
                (θB ((n' : ℕ) : ZMod (p ^ e))) (θC ((n' : ℕ) : ZMod (p ^ e)))
                (θD ((n' : ℕ) : ZMod (p ^ e))) ((t : ℕ) : ZMod (p ^ e))) := by
      intro t ht
      rw [show ((n' + p ^ (M - 1) * t : ℕ) : ZMod (p ^ e))
          = ((n' : ℕ) : ZMod (p ^ e)) + ((p : ℕ) ^ (M - 1) : ℕ) * ((t : ℕ) : ZMod (p ^ e)) by
        push_cast; ring]
      rw [prodCoord_peel (p := p) (e := e) (ℓ := ℓ) (M := M) hℓ (by omega) A B C D _ _,
        map_mul]
    rw [Finset.sum_congr rfl hpeel, ← Finset.mul_sum, hinner ((n' : ℕ) : ZMod (p ^ e))]


  -- ### restrict to the localisation class
  have hclass : levelSum p e ℓ M χ A B C D
      = (p : ℂ) * ∑ n' ∈ (Finset.range (p ^ (M - 1))).filter (fun n' => n' % p = c₀),
          χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e))) := by
    rw [hdecomp]
    rw [show (∑ n' ∈ Finset.range (p ^ (M - 1)),
          χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e)))
            * ((p : ℂ) * (if p ∣ ((((κ : ℕ)) : ZMod (p ^ e))
                - Δ * ((n' : ℕ) : ZMod (p ^ e))).val then 1 else 0)))
        = ∑ n' ∈ Finset.range (p ^ (M - 1)),
          (if n' % p = c₀ then (p : ℂ) * χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e)))
            else 0) by
      refine Finset.sum_congr rfl fun n' hn' => ?_
      by_cases h : n' % p = c₀
      · rw [if_pos ((hcond2 n').mpr h), if_pos h]; ring
      · rw [if_neg (fun hh => h ((hcond2 n').mp hh)), if_neg h]; ring]
    rw [← Finset.sum_filter, Finset.mul_sum]
  -- ### the residual sum
  have hresidual :
      (∑ n' ∈ (Finset.range (p ^ (M - 1))).filter (fun n' => n' % p = c₀),
          χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e))))
        = χ (prodCoord p e ℓ A B C D xc)
          * levelSum p e (ℓ + 1) (M - 2) χ (θA xc) (θB xc) (θC xc) (θD xc) := by
    rw [show p ^ (M - 1) = p ^ ((M - 2) + 1) by
      congr 1; omega]
    rw [sum_range_filter_mod_eq p c₀ (M - 2) hc₀lt
      (fun n' => χ (prodCoord p e ℓ A B C D ((n' : ℕ) : ZMod (p ^ e))))]
    rw [levelSum_eq_range_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show ((c₀ + p * m : ℕ) : ZMod (p ^ e))
        = xc + ((p : ℕ) ^ 1 : ℕ) * ((m : ℕ) : ZMod (p ^ e)) by
      rw [hxcdef]; push_cast; ring]
    rw [prodCoord_peel (p := p) (e := e) (ℓ := ℓ) (M := 2) hℓ (by norm_num) A B C D _ _,
      map_mul]
    rw [show ℓ + 2 - 1 = ℓ + 1 by omega,
      phase_eq_chi_prodCoord (p := p) (e := e) (ℓ := ℓ + 1) (by omega) χ
        (θA xc) (θB xc) (θC xc) (θD xc) ((m : ℕ) : ZMod (p ^ e))]
  -- ### the invariant and the norm
  have hGlocal : p ^ (ℓ + 1) ∣ (θA xc + θB xc - θC xc - θD xc).val := by
    have hGe := G_expand (p := p) (e := e) (ℓ := ℓ) hℓ hdiv' κ hsum xc
    rw [castHom_pPow hdiv'] at hGe
    have hL : ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        (A * (1 + pPow p e ℓ * A * xc)⁻¹ + B * (1 + pPow p e ℓ * B * xc)⁻¹
          - C * (1 + pPow p e ℓ * C * xc)⁻¹ - D * (1 + pPow p e ℓ * D * xc)⁻¹)
        = ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) (θA xc + θB xc - θC xc - θD xc) := by
      simp only [hθA, hθB, hθC, hθD]
    rw [hL] at hGe
    have hw : ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ)
        = (((κ : ℕ)) : ZMod (p ^ (ℓ + 1))) - ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) xc
            * ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1))) Δ := by
      rw [map_sub, map_mul, map_natCast]
    rw [← hw] at hGe
    have hy : p ∣ ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ).val := by
      rw [hxcdef]
      exact (hcond c₀).mpr (Nat.mod_eq_of_lt hc₀lt)
    have hval : p ∣ (ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ)).val := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
      have h1 : ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ).val % p ^ (ℓ + 1)
          ≡ 0 [MOD p] :=
        (Nat.ModEq.of_dvd (show (p : ℕ) ∣ p ^ (ℓ + 1) by
            simpa using pow_dvd_pow p (show 1 ≤ ℓ + 1 by omega))
          (Nat.mod_modEq _ _)).trans (Nat.modEq_zero_iff_dvd.mpr hy)
      exact Nat.modEq_zero_iff_dvd.mp h1
    have hzero : pPow p (ℓ + 1) ℓ * ZMod.castHom hdiv' (ZMod (p ^ (ℓ + 1)))
        ((((κ : ℕ)) : ZMod (p ^ e)) - xc * Δ) = 0 :=
      (pPow_mul_eq_zero_iff hp hℓ _).mpr hval
    rw [hzero] at hGe
    rw [← castHom_eq_zero_iff_dvd_val hdiv' (θA xc + θB xc - θC xc - θD xc)]
    exact hGe
  have hnd' : ¬ (p : ℕ) ∣ (θA xc ^ 2 + θB xc ^ 2 - θC xc ^ 2 - θD xc ^ 2).val := by
    have hθ : ∀ U : ZMod (p ^ e),
        ZMod.castHom hdiv1 (ZMod p) (U * (1 + pPow p e ℓ * U * xc)⁻¹)
          = ZMod.castHom hdiv1 (ZMod p) U := by
      intro U
      have h1 : ZMod.castHom hdiv1 (ZMod p) (1 + pPow p e ℓ * U * xc) = 1 := by
        rw [map_add, map_one, map_mul, map_mul, pPow, map_natCast]
        have hz : (((p : ℕ) ^ ℓ : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]
          simpa [pow_one] using pow_dvd_pow p hℓ
        rw [hz, zero_mul, zero_mul, add_zero]
      have h2 : ZMod.castHom hdiv1 (ZMod p) ((1 + pPow p e ℓ * U * xc)⁻¹) = 1 := by
        have hu : (1 + pPow p e ℓ * U * xc) * (1 + pPow p e ℓ * U * xc)⁻¹ = 1 :=
          ZMod.mul_inv_of_unit _ (isUnit_one_add_pPow_mul hℓ U xc)
        have h3 := congrArg (ZMod.castHom hdiv1 (ZMod p)) hu
        rw [map_mul, h1, map_one, one_mul] at h3
        exact h3
      rw [map_mul, h2, mul_one]
    have hred : ZMod.castHom hdiv1 (ZMod p)
        (θA xc ^ 2 + θB xc ^ 2 - θC xc ^ 2 - θD xc ^ 2) = δ := by
      rw [hδdef, hΔdef, map_sub, map_sub, map_add, map_sub, map_sub, map_add,
        map_pow, map_pow, map_pow, map_pow, map_pow, map_pow, map_pow, map_pow]
      simp only [hθA, hθB, hθC, hθD, hθ]
    intro hcon
    have h0 : ZMod.castHom hdiv1 (ZMod p) (θA xc ^ 2 + θB xc ^ 2 - θC xc ^ 2 - θD xc ^ 2) = 0 :=
      (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hcon
    exact hδne (by rw [← hred]; exact h0)
  -- ### conclusion
  obtain ⟨κ', hκ'⟩ := hGlocal
  refine ⟨θA xc, θB xc, θC xc, θD xc, κ', ?_, hnd', ?_⟩
  · rw [← ZMod.natCast_zmod_val (θA xc + θB xc - θC xc - θD xc), hκ']
  · rw [hclass, hresidual, norm_mul, norm_mul]
    have hunit : IsUnit (prodCoord p e ℓ A B C D xc) := by
      rw [prodCoord]
      refine IsUnit.mul (IsUnit.mul (IsUnit.mul (isUnit_one_add_pPow_mul hℓ A xc)
        (isUnit_one_add_pPow_mul hℓ B xc)) ?_) ?_
      · exact isUnit_iff_exists_inv.mpr ⟨1 + pPow p e ℓ * C * xc,
          ZMod.inv_mul_of_unit _ (isUnit_one_add_pPow_mul hℓ C xc)⟩
      · exact isUnit_iff_exists_inv.mpr ⟨1 + pPow p e ℓ * D * xc,
          ZMod.inv_mul_of_unit _ (isUnit_one_add_pPow_mul hℓ D xc)⟩
    have hnr : ‖χ (prodCoord p e ℓ A B C D xc)‖ = 1 := by
      rw [← IsUnit.unit_spec hunit]
      exact norm_apply_unit χ hunit.unit
    have hpnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
    rw [hnr, hpnorm, one_mul]




/-! ## The reduction of the target sum to a level sum -/

/-- The unit `(r + u)⁻¹` of `ZMod (p^e)` (with `r` lifted from `ZMod p` and `u : ℕ`). -/
noncomputable def gammaU (p e : ℕ) (r : ZMod p) (u : ℕ) : ZMod (p ^ e) :=
  ((((r.val + u : ℕ)) : ZMod (p ^ e)))⁻¹

lemma gammaU_mul (p e : ℕ) [Fact p.Prime] (r : ZMod p) (u : ℕ)
    (hu : (r + (u : ZMod p)) ≠ 0) (he : 1 ≤ e) :
    ((((r.val + u : ℕ)) : ZMod (p ^ e))) * gammaU p e r u = 1 := by
  refine ZMod.mul_inv_of_unit _ ?_
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]
  intro h
  refine hu ?_
  have h2 : ((r.val + u : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  rw [Nat.cast_add, ZMod.natCast_zmod_val] at h2
  simpa using h2

/-- The summand of the target is the constant `χ (r+a) χ (r+b) conj χ (r+c) conj χ (r+d)`
times the level-`1` phase in the unit part. -/
lemma target_term_eq (p e : ℕ) [Fact p.Prime] (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b c d : ℕ) (r : ZMod p)
    (ha : (r + (a : ZMod p)) ≠ 0) (hb : (r + (b : ZMod p)) ≠ 0)
    (hc : (r + (c : ZMod p)) ≠ 0) (hd : (r + (d : ZMod p)) ≠ 0) (z : ZMod (p ^ (e - 2))) :
    χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ))) *
     ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ))))
  * (starRingEnd ℂ) (χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ))) *
     ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ)))))
      = χ (((r.val + a : ℕ) : ZMod (p ^ e))) * χ (((r.val + b : ℕ) : ZMod (p ^ e)))
        * (starRingEnd ℂ) (χ (((r.val + c : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (((r.val + d : ℕ) : ZMod (p ^ e))))
        * phase p e 1 χ (gammaU p e r a) (gammaU p e r b) (gammaU p e r c) (gammaU p e r d)
            ((z.val : ℕ) : ZMod (p ^ e)) := by
  have he1 : 1 ≤ e := by omega
  have hfac : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ((((r.val : ℕ) : ZMod (p ^ e)) + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (u : ℕ)))
        = (((r.val + u : ℕ) : ZMod (p ^ e)))
          * (1 + (p : ZMod (p ^ e)) * gammaU p e r u * ((z.val : ℕ) : ZMod (p ^ e))) := by
    intro u hu
    have h1 : (((r.val + u : ℕ) : ZMod (p ^ e))) * gammaU p e r u = 1 := gammaU_mul p e r u hu he1
    rw [mul_add, mul_one,
      show (((r.val + u : ℕ) : ZMod (p ^ e))) * ((p : ZMod (p ^ e)) * gammaU p e r u * ((z.val : ℕ) : ZMod (p ^ e)))
        = (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) * ((((r.val + u : ℕ) : ZMod (p ^ e))) * gammaU p e r u) by ring,
      h1, mul_one]
    push_cast
    ring
  have hA := hfac a ha
  have hB := hfac b hb
  have hC := hfac c hc
  have hD := hfac d hd
  rw [hA, hB, hC, hD]
  simp only [map_mul, map_one, mul_one, phase, pPow, pow_one]
  ring

/-- **The target sum equals a constant times the level-`1` sum.** -/
theorem target_sum_eq (p e : ℕ) [Fact p.Prime] (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (a b c d : ℕ) (r : ZMod p)
    (ha : (r + (a : ZMod p)) ≠ 0) (hb : (r + (b : ZMod p)) ≠ 0)
    (hc : (r + (c : ZMod p)) ≠ 0) (hd : (r + (d : ZMod p)) ≠ 0) :
    (∑ z : ZMod (p ^ (e - 2)),
        χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ))) *
     ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ))))
  * (starRingEnd ℂ) (χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ))) *
     ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ))))))
      = χ (((r.val + a : ℕ) : ZMod (p ^ e))) * χ (((r.val + b : ℕ) : ZMod (p ^ e)))
        * (starRingEnd ℂ) (χ (((r.val + c : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (((r.val + d : ℕ) : ZMod (p ^ e))))
        * levelSum p e 1 (e - 2) χ (gammaU p e r a) (gammaU p e r b) (gammaU p e r c) (gammaU p e r d) := by
  rw [levelSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact target_term_eq p e he χ a b c d r ha hb hc hd z


/-- The quadratic coefficient identity `2 K₂ = -(A²+B²-C²-D²)` under criticality. -/
lemma two_mul_K2_eq (A B C D : ZMod p) (h : A + B - C - D = 0) :
    2 * (A * B - (A + B) * (C + D) + (C ^ 2 + C * D + D ^ 2))
      = -(A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2) := by
  linear_combination (A + B - C - D) * h

/-- **Base case `M = 1`.**  With a single remaining digit `e = 2ℓ + 1`, the level-`ℓ` sum is a
non-degenerate quadratic Gauss sum modulo `p`, hence at most `2 √p`. -/
theorem levelSum_base_one (p e ℓ : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hℓ : 1 ≤ ℓ) (heq : e = 2 * ℓ + 1) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (A B C D : ZMod (p ^ e)) (κ : ℕ)
    (hsum : A + B - C - D = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)))
    (hnd : ¬ (p : ℕ) ∣ (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2 : ZMod (p ^ e)).val) :
    ‖levelSum p e ℓ 1 χ A B C D‖ ≤ 2 * Real.sqrt p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have he1 : 1 ≤ e := by omega
  have h3 : e ≤ 3 * ℓ := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  -- the cube of `p^ℓ` vanishes
  have hP3 : pPow p e ℓ ^ 3 = 0 := by
    rw [show pPow p e ℓ ^ 3 = pPow p e (ℓ + ℓ + ℓ) by
      rw [show pPow p e ℓ ^ 3 = pPow p e ℓ * pPow p e ℓ * pPow p e ℓ by ring,
        pPow_mul_pPow, pPow_mul_pPow],
      pPow_eq_zero_of_le (j := ℓ + ℓ + ℓ) (by omega)]
  -- the quadratic coefficient
  set K2 : ZMod (p ^ e) := A * B - (A + B) * (C + D) + (C ^ 2 + C * D + D ^ 2) with hK2def
  -- the primitive `p`-th root of unity
  set ζ : ℂ := χ (1 + pPow p e (e - 1)) with hζdef
  have hζprim : IsPrimitiveRoot ζ p := by
    rw [hζdef, pPow]
    simpa using chi_one_add_primePow_isPrimitiveRoot p e hp2 (by omega) χ hχ
  have hζp : ζ ^ p = 1 := hζprim.pow_eq_one
  -- the reduction of the criticality
  have hcritp : ZMod.castHom hdiv1 (ZMod p) (A + B - C - D) = 0 := by
    rw [hsum, map_natCast, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_of_dvd_left (by simpa [pow_one] using pow_dvd_pow p hℓ : p ∣ p ^ ℓ) κ
  -- the quadratic coefficient is a unit modulo `p`
  have hK2ne : ¬ (p : ℤ) ∣ ((K2.val : ℕ) : ℤ) := by
    intro hcon
    apply hnd
    have hK2zero : ZMod.castHom hdiv1 (ZMod p) K2 = 0 := by
      rw [castHom_eq_zero_iff_dvd_val_one]
      exact_mod_cast hcon
    have hcritp' : ZMod.castHom hdiv1 (ZMod p) A + ZMod.castHom hdiv1 (ZMod p) B
        - ZMod.castHom hdiv1 (ZMod p) C - ZMod.castHom hdiv1 (ZMod p) D = 0 := by
      rw [map_sub, map_sub, map_add] at hcritp
      exact hcritp
    have hL : ZMod.castHom hdiv1 (ZMod p) K2
        = ZMod.castHom hdiv1 (ZMod p) A * ZMod.castHom hdiv1 (ZMod p) B
          - (ZMod.castHom hdiv1 (ZMod p) A + ZMod.castHom hdiv1 (ZMod p) B)
            * (ZMod.castHom hdiv1 (ZMod p) C + ZMod.castHom hdiv1 (ZMod p) D)
          + (ZMod.castHom hdiv1 (ZMod p) C ^ 2
              + ZMod.castHom hdiv1 (ZMod p) C * ZMod.castHom hdiv1 (ZMod p) D
              + ZMod.castHom hdiv1 (ZMod p) D ^ 2) := by
      rw [hK2def]
      simp only [map_add, map_sub, map_mul, map_pow]
    have hK2id : 2 * ZMod.castHom hdiv1 (ZMod p) K2
        = -(ZMod.castHom hdiv1 (ZMod p) (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2)) := by
      rw [hL, map_sub, map_sub, map_add, map_pow, map_pow, map_pow, map_pow]
      exact two_mul_K2_eq _ _ _ _ hcritp'
    have hΔ0 : ZMod.castHom hdiv1 (ZMod p) (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2) = 0 := by
      have h := hK2id
      rw [hK2zero, mul_zero] at h
      exact neg_eq_zero.mp h.symm
    exact (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp hΔ0
  -- the product coordinate is a quadratic exponential in the digit
  have hpp : pPow p e ℓ * pPow p e ℓ = pPow p e (2 * ℓ) := by
    rw [pPow_mul_pPow, show ℓ + ℓ = 2 * ℓ by omega]
  have hprod : ∀ w : ZMod (p ^ e), prodCoord p e ℓ A B C D w
      = 1 + pPow p e (2 * ℓ) * ((κ : ZMod (p ^ e)) * w + K2 * w ^ 2) := by
    intro w
    have hkey := Commons.RingTheory.ZMod.prod_signed_quad_expand (p ^ e) (pPow p e ℓ)
      (A * w) (B * w) (C * w) (D * w) hP3
    have hpc : prodCoord p e ℓ A B C D w
        = (1 + pPow p e ℓ * (A * w)) * (1 + pPow p e ℓ * (B * w))
          * (1 + pPow p e ℓ * (C * w))⁻¹ * (1 + pPow p e ℓ * (D * w))⁻¹ := by
      rw [prodCoord]; ring
    rw [hpc, hkey]
    have h1 : pPow p e ℓ * (A * w + B * w - C * w - D * w)
        = pPow p e (2 * ℓ) * ((κ : ZMod (p ^ e)) * w) := by
      rw [← hpp, show A * w + B * w - C * w - D * w = (A + B - C - D) * w by ring, hsum]
      simp only [pPow]
      push_cast
      ring
    have h2 : pPow p e ℓ ^ 2 * ((A * w) * (B * w) - (A * w + B * w) * (C * w + D * w)
          + ((C * w) ^ 2 + (C * w) * (D * w) + (D * w) ^ 2))
        = pPow p e (2 * ℓ) * (K2 * w ^ 2) := by
      rw [show pPow p e ℓ ^ 2 = pPow p e (2 * ℓ) by
        rw [show pPow p e ℓ ^ 2 = pPow p e ℓ * pPow p e ℓ by ring, hpp],
        hK2def]
      ring
    rw [h1, h2]
    ring
  have hterm : ∀ n : ℕ, phase p e ℓ χ A B C D ((n : ℕ) : ZMod (p ^ e))
      = ζ ^ (((κ : ℤ) * (n : ZMod p)
          - ((-((K2.val : ℕ) : ℤ))) * (n : ZMod p) ^ 2 : ZMod p)).val := by
    intro n
    have hphase : phase p e ℓ χ A B C D ((n : ℕ) : ZMod (p ^ e))
        = χ (1 + pPow p e (e - 1)
            * ((κ : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e))
              + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)) := by
      rw [phase_eq_chi_prodCoord (p := p) (e := e) (ℓ := ℓ) hℓ χ A B C D, hprod,
        show (2 : ℕ) * ℓ = e - 1 by omega]
    rw [hphase, chi_top_level (p := p) (e := e) (by omega) χ, hζdef]
    refine pow_eq_pow_of_modEq ?_ hζp
    have hred : ZMod.castHom hdiv1 (ZMod p)
        ((κ : ZMod (p ^ e)) * ((n : ℕ) : ZMod (p ^ e)) + K2 * ((n : ℕ) : ZMod (p ^ e)) ^ 2)
        = (κ : ZMod p) * (n : ZMod p) + (K2.val : ZMod p) * (n : ZMod p) ^ 2 := by
      rw [map_add, map_mul, map_mul, map_pow]
      simp only [map_natCast]
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    have hWeq : (((κ : ℤ) * (n : ZMod p)
          - ((-((K2.val : ℕ) : ℤ))) * (n : ZMod p) ^ 2 : ZMod p))
        = (κ : ZMod p) * (n : ZMod p) + (K2.val : ZMod p) * (n : ZMod p) ^ 2 := by
      push_cast
      ring
    rw [hWeq, ← hred, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).symm
  rw [levelSum_eq_range_sum, show p ^ 1 = p by norm_num,
    Finset.sum_congr rfl (fun n _ => hterm n)]
  rw [← Commons.NumberTheory.GaussSum.zmod_sum_range p
    (fun x : ZMod p => ζ ^ ((((κ : ℤ) * x - ((-((K2.val : ℕ) : ℤ))) * x ^ 2 : ZMod p))).val)]
  refine le_of_eq_of_le ?_ (Commons.NumberTheory.GaussSum.quadratic_gauss_primitive_root p hp2 ζ
    hζprim ((κ : ℤ)) ((-((K2.val : ℕ) : ℤ))) (fun h => hK2ne (by simpa using h)))
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  push_cast
  ring

/-! ## The induction over the number of remaining digits -/

/-- **The level bound.**  For `e = 2ℓ + M` the level-`ℓ` sum over `ZMod (p^M)` is bounded by
`2 p^(M/2)`. -/
theorem level_bound (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e) (M : ℕ) :
    ∀ ℓ : ℕ, e = 2 * ℓ + M → 1 ≤ ℓ →
      ∀ (χ : DirichletCharacter ℂ (p ^ e)), χ.IsPrimitive →
        ∀ (A B C D : ZMod (p ^ e)) (κ : ℕ),
          A + B - C - D = ((p ^ ℓ * κ : ℕ) : ZMod (p ^ e)) →
          ¬ (p : ℕ) ∣ (A ^ 2 + B ^ 2 - C ^ 2 - D ^ 2 : ZMod (p ^ e)).val →
          ‖levelSum p e ℓ M χ A B C D‖ ≤ 2 * (p : ℝ) ^ ((M : ℝ) / 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hppos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro ℓ heq hℓ χ hχ A B C D κ hsum hnd
    rcases Nat.lt_or_ge M 2 with hM | hM
    · interval_cases M
      · have h1 : levelSum p e ℓ 0 χ A B C D = 1 := by
          rw [levelSum_eq_range_sum]
          rw [show p ^ 0 = 1 by norm_num, Finset.sum_range_one]
          simp [phase]
        rw [h1, show ((0 : ℕ) : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
        norm_num
      · -- the last digit: the quadratic Gauss sum
        have h1 : e = 2 * ℓ + 1 := by omega
        refine (levelSum_base_one p e ℓ hp2 hℓ h1 χ hχ A B C D κ hsum hnd).trans_eq ?_
        rw [Real.sqrt_eq_rpow]
        norm_num
    · obtain ⟨A', B', C', D', κ', hsum', hnd', hnorm⟩ :=
        level_step p e ℓ M hp2 he hℓ hM heq χ hχ A B C D κ hsum hnd
      rw [hnorm]
      have hrec := ih (M - 2) (by omega) (ℓ + 1) (by omega) (by omega) χ hχ A' B' C' D' κ' hsum' hnd'
      calc (p : ℝ) * ‖levelSum p e (ℓ + 1) (M - 2) χ A' B' C' D'‖
          ≤ (p : ℝ) * (2 * (p : ℝ) ^ (((M - 2 : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hrec hppos.le
        _ = 2 * (p : ℝ) ^ ((M : ℝ) / 2) := by
            have hcast : ((M - 2 : ℕ) : ℝ) = (M : ℝ) - 2 := by
              rw [Nat.cast_sub (by omega)]; norm_num
            rw [show (M : ℝ) / 2 = ((M - 2 : ℕ) : ℝ) / 2 + 1 by rw [hcast]; ring,
              Real.rpow_add hppos, Real.rpow_one]
            ring

/-- **Local Gauss-sum bound on a critical residue class modulo `p^e`.**

Let `p` be an odd prime, `e ≥ 3`, and `χ` a primitive Dirichlet character modulo `p ^ e`.
Fix `a b c d : ℕ` and a residue class `r : ZMod p` such that none of `r + a, r + b, r + c, r + d`
vanishes modulo `p`, which is *critical* (`∑ ± (r+u)⁻¹ = 0` in `ZMod p`) and *non-degenerate*
(the quadratic coefficient `∑ ± (r+u)⁻²` is non-zero in `ZMod p`).

Then the correlation sum over the `p ^ (e-2)` lifts `z` of `r` (i.e. over
`x = r + p * z ∈ ZMod (p^e)`) is bounded by `2 * p ^ ((e-2)/2)`:

`‖∑_z χ ((x+a)*(x+b)) * conj (χ ((x+c)*(x+d)))‖ ≤ 2 * p ^ ((e-2)/2)`,  `x = r + p*z`.

This is the "Gauss sum" evaluation of the multiplicative character correlation on one critical
class: writing `x + u = (r+u) * (1 + p*z*(r+u)⁻¹)` and using that `χ` is non-trivial on the
kernel `1 + p^(e-1)` of `(ZMod (p^e))ˣ → (ZMod (p^(e-1)))ˣ`, the sum becomes (up to a constant)
`∑_z ω^(H z)` with `ω = χ (1+p)` a primitive `p^(e-1)`-st root of unity and `H` an integral
polynomial whose reduction mod `p` is `β*z - δ*z^2` with `δ ≠ 0` (`δ` is the non-degenerate
quadratic coefficient above). This is then bounded by `quadratic_phase_prime_pow`. -/
theorem criticalClass_gaussSum_primePow (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 3 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) (a b c d : ℕ) (r : ZMod p)
    (hunit : (r + (a : ZMod p)) ≠ 0 ∧ (r + (b : ZMod p)) ≠ 0 ∧
             (r + (c : ZMod p)) ≠ 0 ∧ (r + (d : ZMod p)) ≠ 0)
    (hcrit : (r + (a : ZMod p))⁻¹ + (r + (b : ZMod p))⁻¹ - (r + (c : ZMod p))⁻¹
              - (r + (d : ZMod p))⁻¹ = 0)
    (hnd : (r + (a : ZMod p))⁻¹ ^ 2 + (r + (b : ZMod p))⁻¹ ^ 2 - (r + (c : ZMod p))⁻¹ ^ 2
              - (r + (d : ZMod p))⁻¹ ^ 2 ≠ 0) :
    ‖∑ z : ZMod (p ^ (e - 2)),
        χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (a : ℕ))) *
           ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (b : ℕ))))
        * (starRingEnd ℂ) (χ (((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (c : ℕ))) *
           ((((r.val : ℕ) : ZMod (p^e)) + (p : ZMod (p^e)) * ((z.val : ℕ) : ZMod (p^e)) + (d : ℕ)))))‖
      ≤ 2 * (p : ℝ) ^ (((e : ℝ) - 2) / 2) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have he1 : 1 ≤ e := by omega
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p (show 1 ≤ e by omega)
  obtain ⟨ha, hb, hc, hd⟩ := hunit
  have hnormU : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ‖χ (((r.val + u : ℕ) : ZMod (p ^ e)))‖ = 1 := by
    intro u hu
    have hunit : IsUnit ((((r.val + u : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he1]
      intro h
      refine hu ?_
      have h2 : ((r.val + u : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at h2
      simpa using h2
    rw [← IsUnit.unit_spec hunit]
    exact norm_apply_unit χ hunit.unit
  have hinc : ∀ u : ℕ, (r + (u : ZMod p)) ≠ 0 →
      ZMod.castHom hdiv1 (ZMod p) (gammaU p e r u) = (r + (u : ZMod p))⁻¹ := by
    intro u hu
    have h1 : ((((r.val + u : ℕ)) : ZMod (p ^ e))) * gammaU p e r u = 1 :=
      gammaU_mul p e r u hu he1
    have h2 := congrArg (ZMod.castHom hdiv1 (ZMod p)) h1
    rw [map_mul, map_one, map_natCast, Nat.cast_add, ZMod.natCast_zmod_val] at h2
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
  -- the target sum is a level sum up to a constant of modulus one
  rw [target_sum_eq p e he χ a b c d r ha hb hc hd, norm_mul]
  have hC : ‖χ (((r.val + a : ℕ) : ZMod (p ^ e))) * χ (((r.val + b : ℕ) : ZMod (p ^ e)))
      * (starRingEnd ℂ) (χ (((r.val + c : ℕ) : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (((r.val + d : ℕ) : ZMod (p ^ e))))‖ = 1 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj,
      hnormU a ha, hnormU b hb, hnormU c hc, hnormU d hd]
    norm_num
  rw [hC, one_mul]
  -- the invariants of the four units
  have hredsum : ZMod.castHom hdiv1 (ZMod p)
      (gammaU p e r a + gammaU p e r b - gammaU p e r c - gammaU p e r d) = 0 := by
    rw [map_sub, map_sub, map_add, hinc a ha, hinc b hb, hinc c hc, hinc d hd]
    exact hcrit
  have hz : p ∣ (gammaU p e r a + gammaU p e r b - gammaU p e r c - gammaU p e r d).val :=
    (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mp hredsum
  obtain ⟨κ, hκ⟩ := hz
  have hsumg : gammaU p e r a + gammaU p e r b - gammaU p e r c - gammaU p e r d
      = ((p ^ 1 * κ : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.natCast_zmod_val (gammaU p e r a + gammaU p e r b - gammaU p e r c - gammaU p e r d),
      hκ, pow_one]
  have hredquad : ZMod.castHom hdiv1 (ZMod p)
      (gammaU p e r a ^ 2 + gammaU p e r b ^ 2 - gammaU p e r c ^ 2 - gammaU p e r d ^ 2)
      = (r + (a : ZMod p))⁻¹ ^ 2 + (r + (b : ZMod p))⁻¹ ^ 2
        - (r + (c : ZMod p))⁻¹ ^ 2 - (r + (d : ZMod p))⁻¹ ^ 2 := by
    rw [map_sub, map_sub, map_add, map_pow, map_pow, map_pow, map_pow,
      hinc a ha, hinc b hb, hinc c hc, hinc d hd]
  have hndg : ¬ (p : ℕ) ∣ (gammaU p e r a ^ 2 + gammaU p e r b ^ 2
      - gammaU p e r c ^ 2 - gammaU p e r d ^ 2).val := by
    intro hcon
    refine hnd ?_
    have h0 : ZMod.castHom hdiv1 (ZMod p)
        (gammaU p e r a ^ 2 + gammaU p e r b ^ 2 - gammaU p e r c ^ 2 - gammaU p e r d ^ 2) = 0 :=
      (castHom_eq_zero_iff_dvd_val_one hdiv1 _).mpr hcon
    rwa [hredquad] at h0
  refine (level_bound p e hp2 he (e - 2) 1 (by omega) (by omega) χ hχ
    (gammaU p e r a) (gammaU p e r b) (gammaU p e r c) (gammaU p e r d) κ hsumg hndg).trans_eq ?_
  rw [show ((e - 2 : ℕ) : ℝ) = (e : ℝ) - 2 by
    rw [Nat.cast_sub (by omega : 2 ≤ e)]; norm_num]

end Commons.NumberTheory.DirichletCharacter
