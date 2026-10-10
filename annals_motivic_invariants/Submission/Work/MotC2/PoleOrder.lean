import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.PoleSetup
import Submission.Work.MotC2.PoleTgen
import Submission.Work.MotC2.PolePlace
import Submission.Work.MotC2.w_sq_deg_constraints
import Submission.Work.MotC2.w_cube_deg_constraints
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

set_option maxHeartbeats 2000000

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## Elementary complements -/

lemma cubicPoly_natDegree (E : WeierstrassCurve L) : (cubicPoly E).natDegree = 3 :=
  Polynomial.natDegree_eq_of_degree_eq_some (cubicPoly_degree E)

lemma infCoordRing_le_infPlace (E : WeierstrassCurve L) : infCoordRing E ≤ infPlace E := fun _ hf =>
  Algebra.subset_adjoin (Or.inl hf)

lemma infU_mem_infPlace (E : WeierstrassCurve L) : infU E ∈ infPlace E :=
  infCoordRing_le_infPlace E (Algebra.subset_adjoin (by simp))

lemma infW_mem_infPlace (E : WeierstrassCurve L) : infW E ∈ infPlace E :=
  infCoordRing_le_infPlace E (Algebra.subset_adjoin (by simp))

lemma infW_sq_mem_infPlace (E : WeierstrassCurve L) : (infW E) ^ 2 ∈ infPlace E :=
  pow_mem (infW_mem_infPlace E) 2

lemma infW_cube_mem_infPlace (E : WeierstrassCurve L) : (infW E) ^ 3 ∈ infPlace E :=
  pow_mem (infW_mem_infPlace E) 3

/-- `x·w²` is the chart element `1 + a₂u + a₄u² + a₆u³ - (a₁ + a₃u)w`, hence lies in the local ring
of the point at infinity. -/
lemma genX_mul_infW_sq_mem_infPlace (E : WeierstrassCurve L) :
    genX E * (infW E) ^ 2 ∈ infPlace E := by
  have hmem : (1 + algebraMap L (Func E) E.a₂ * infU E + algebraMap L (Func E) E.a₄ * infU E ^ 2 +
      algebraMap L (Func E) E.a₆ * infU E ^ 3) -
      (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * infW E ∈ infPlace E := by
    refine Subalgebra.sub_mem _ ?_ ?_
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.one_mem _) ?_) ?_) ?_
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (infU_mem_infPlace E)
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (pow_mem (infU_mem_infPlace E) 2)
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (pow_mem (infU_mem_infPlace E) 3)
    · exact Subalgebra.mul_mem _ (Subalgebra.add_mem _
        (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (infU_mem_infPlace E)))
        (infW_mem_infPlace E)
  simpa [genX_mul_infW_sq E] using hmem

lemma genX_mul_infW_cube_mem_infPlace (E : WeierstrassCurve L) :
    genX E * (infW E) ^ 3 ∈ infPlace E := by
  rw [genX_mul_infW_cube E]
  exact mul_mem (genX_mul_infW_sq_mem_infPlace E) (infW_mem_infPlace E)

lemma genY_mul_infW_cube_mem_infPlace (E : WeierstrassCurve L) :
    genY E * (infW E) ^ 3 ∈ infPlace E := by
  rw [genY_mul_infW_cube E]
  exact pow_mem (genX_mul_infW_sq_mem_infPlace E) 2

/-- A polynomial of degree at most one is determined by its first two coefficients. -/
lemma eq_C_add_C_mul_X_of_degree_le_one {p : Polynomial L} (h : p.degree ≤ 1) :
    p = C (p.coeff 0) + C (p.coeff 1) * X := by
  ext n
  rcases n with _ | _ | m
  · simp
  · simp
  · have h0 : p.coeff (m + 2) = 0 :=
      (Polynomial.degree_le_iff_coeff_zero p 1).mp h (m + 2)
        (by exact_mod_cast (by omega : (1 : ℕ) < m + 2))
    simp [h0]

/-! ## The explicit decomposition of `r·w²` and `r·w³` -/

/-- If `f = p(x) + q(x)·y` is the image of an element of the affine coordinate ring, then
`f·w² = c(x)(p - q·t(x))/x⁴ + (-p·t(x) + q(c(x) + t(x)²))·w/x²`, where `c = cubicPoly E` and
`t = linPoly E`. -/
lemma algebraMap_mul_infW_sq_eq (E : WeierstrassCurve L) (p q : Polynomial L) :
    (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) * (infW E) ^ 2 =
      Tgen E (cubicPoly E * (p - q * linPoly E)) (X ^ 4) +
        Tgen E (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)) (X ^ 2) * infW E := by
  have h1 := infW_sq_eq E
  have h2 := genY_mul_infW_sq_eq E
  calc (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) * (infW E) ^ 2
      = Polynomial.aeval (genX E) p * (infW E) ^ 2 +
        Polynomial.aeval (genX E) q * (genY E * (infW E) ^ 2) := by ring
    _ = Polynomial.aeval (genX E) p *
          (Polynomial.aeval (genX E) (cubicPoly E) / (genX E) ^ 4 -
            Polynomial.aeval (genX E) (linPoly E) * infW E / (genX E) ^ 2) +
        Polynomial.aeval (genX E) q *
          ((Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^ 2) *
              infW E / (genX E) ^ 2 -
            Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
              (genX E) ^ 4) := by rw [h2, h1]
    _ = Tgen E (cubicPoly E * (p - q * linPoly E)) (X ^ 4) +
        Tgen E (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)) (X ^ 2) * infW E := by
      simp only [Tgen_def, map_mul, map_sub, map_add, map_neg, map_pow, aeval_X]
      field_simp
      first | refl_ring1 | ring

/-- If `f = p(x) + q(x)·y` is the image of an element of the affine coordinate ring, then
`f·w³ = c(x)(-p·t(x) + q(c(x) + t(x)²))/x⁶ + (p(c(x) + t(x)²) - q·t(x)(2c(x) + t(x)²))·w/x⁴`. -/
lemma algebraMap_mul_infW_cube_eq (E : WeierstrassCurve L) (p q : Polynomial L) :
    (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) * (infW E) ^ 3 =
      Tgen E (cubicPoly E * (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2))) (X ^ 6) +
        Tgen E (p * (cubicPoly E + linPoly E ^ 2) -
            q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))) (X ^ 4) * infW E := by
  have h1 := infW_cube_eq E
  have h2 := genY_mul_infW_sq_eq E
  have hw := infW_sq_eq E
  calc (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) * (infW E) ^ 3
      = Polynomial.aeval (genX E) p * (infW E) ^ 3 +
        Polynomial.aeval (genX E) q * (genY E * (infW E) ^ 2) * infW E := by ring
    _ = Polynomial.aeval (genX E) p *
          ((Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^ 2) *
              infW E / (genX E) ^ 4 -
            Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
              (genX E) ^ 6) +
        Polynomial.aeval (genX E) q *
          ((Polynomial.aeval (genX E) (cubicPoly E) + (Polynomial.aeval (genX E) (linPoly E)) ^ 2) *
              infW E / (genX E) ^ 2 -
            Polynomial.aeval (genX E) (linPoly E) * Polynomial.aeval (genX E) (cubicPoly E) /
              (genX E) ^ 4) * infW E := by rw [h2, h1]
    _ = Tgen E (cubicPoly E * (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2))) (X ^ 6) +
        Tgen E (p * (cubicPoly E + linPoly E ^ 2) -
            q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))) (X ^ 4) * infW E := by
      simp only [Tgen_def, map_mul, map_sub, map_add, map_neg, map_pow, map_ofNat, aeval_X]
      field_simp
      ring_nf
      rw [hw]
      field_simp
      ring_nf

/-! ## Transferring degree bounds from a `T E`-witness to the explicit decomposition -/

/-- If `Tgen E P Q = Tgen E M N` then `P * N = M * Q`. -/
lemma poly_eq_of_Tgen_eq (E : WeierstrassCurve L) {P Q M N : Polynomial L} (hQ : Q ≠ 0)
    (hN : N ≠ 0) (h : Tgen E P Q = Tgen E M N) : P * N = M * Q := by
  have hQ' : Polynomial.aeval (genX E) Q ≠ 0 := aeval_genX_ne_zero E hQ
  have hN' : Polynomial.aeval (genX E) N ≠ 0 := aeval_genX_ne_zero E hN
  have h3 : Polynomial.aeval (genX E) P * Polynomial.aeval (genX E) N =
      Polynomial.aeval (genX E) M * Polynomial.aeval (genX E) Q := by
    have h' : Polynomial.aeval (genX E) P * (Polynomial.aeval (genX E) Q)⁻¹ =
        Polynomial.aeval (genX E) M * (Polynomial.aeval (genX E) N)⁻¹ := by
      rw [Tgen_def, Tgen_def] at h
      exact h
    calc Polynomial.aeval (genX E) P * Polynomial.aeval (genX E) N
        = Polynomial.aeval (genX E) P * (Polynomial.aeval (genX E) Q)⁻¹ *
            (Polynomial.aeval (genX E) Q * Polynomial.aeval (genX E) N) := by field_simp
      _ = Polynomial.aeval (genX E) M * (Polynomial.aeval (genX E) N)⁻¹ *
            (Polynomial.aeval (genX E) Q * Polynomial.aeval (genX E) N) := by rw [h']
      _ = Polynomial.aeval (genX E) M * Polynomial.aeval (genX E) Q := by field_simp
  refine sub_eq_zero.mp ((aeval_genX_eq_zero_iff E (P * N - M * Q)).mp ?_)
  rw [map_sub, map_mul, map_mul, h3, sub_self]

/-- Degree transfer: if `Tgen E P Q = Tgen E M (X ^ n)` with `deg P ≤ deg Q` and `M ≠ 0`, then
`M.natDegree ≤ n`. -/
lemma natDegree_le_of_Tgen_eq_X_pow (E : WeierstrassCurve L) {P Q M : Polynomial L} {n : ℕ}
    (hQ : Q ≠ 0) (hM : M ≠ 0) (h : Tgen E P Q = Tgen E M (X ^ n))
    (d : P.degree ≤ Q.degree) : M.natDegree ≤ n := by
  have hXn : (X : Polynomial L) ^ n ≠ 0 := pow_ne_zero n X_ne_zero
  have hpoly : P * X ^ n = M * Q := poly_eq_of_Tgen_eq E hQ hXn h
  have hP : P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hpoly
    exact hM ((mul_eq_zero.mp hpoly.symm).resolve_right hQ)
  have hdP : P.natDegree ≤ Q.natDegree := Polynomial.natDegree_le_natDegree d
  have h1 : (P * X ^ n).natDegree = (M * Q).natDegree := by rw [hpoly]
  rw [Polynomial.natDegree_mul hP hXn, Polynomial.natDegree_mul hM hQ,
    Polynomial.natDegree_X_pow] at h1
  omega

/-- Degree transfer for a numerator of the form `cubicPoly E * M` over the denominator `X ^ n`:
`deg M ≤ n - 3`. -/
lemma natDegree_le_of_Tgen_eq_mul_cubicPoly (E : WeierstrassCurve L) {P Q M : Polynomial L} {n : ℕ}
    (hQ : Q ≠ 0) (h : Tgen E P Q = Tgen E (cubicPoly E * M) (X ^ n)) (d : P.degree ≤ Q.degree)
    (hn : 3 ≤ n) : M.natDegree ≤ n - 3 := by
  by_cases hM : M = 0
  · rw [hM]; simp
  have hc : cubicPoly E ≠ 0 := cubicPoly_ne_zero E
  have hcM : cubicPoly E * M ≠ 0 := mul_ne_zero hc hM
  have hle := natDegree_le_of_Tgen_eq_X_pow E hQ hcM h d
  have hsplit : (cubicPoly E * M).natDegree = 3 + M.natDegree := by
    rw [Polynomial.natDegree_mul hc hM, cubicPoly_natDegree E]
  omega

/-!
Route.  `infW E = y/x²` is the uniformizer of the DVR `infPlace E` (generator of its maximal ideal,
see `MotC2/InfPlace`), so for `f : Func E` and `n : ℕ`, `f * (infW E)^n ∈ infPlace E` is
equivalent to `v_O(f) ≥ -n`, where `v_O` is the order of vanishing at `O`, with `v_O(genX E) = -2`,
`v_O(genY E) = -3` and multiplicativity `v_O(u) = 2`, `v_O(w) = 1` for `u = 1/x`, `w = y/x²`.

Write an element of `Coord E` uniquely as `p(x) + q(x)·y` with `p, q ∈ L[X]` (the basis
`CoordinateRing.basis`, or `smul_basis_eq_zero`/`exists_smul_basis_eq`) and use
`CoordinateRing.degree_norm_smul_basis`: the norm of `p + q·y` has degree
`max (2 deg p) (2 deg q + 3)`, which computes `v_O` of the image in `L(E)`.  Since `-2·deg p` is
even and `-2·deg q - 3` is odd, there is never cancellation between the two summands.  Hence
`v_O ≥ -2` forces `q = 0` and `deg p ≤ 1` (giving `L + L·x`), and `v_O ≥ -3` forces `deg q = 0`,
`deg p ≤ 1` (giving `L + L·x + L·y`).
-/
theorem PoleOrder (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic] :
    (∀ r : Work.MotC2.Coord E,
      (algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r * (Work.MotC2.infW E) ^ 2 ∈
          Work.MotC2.infPlace E ↔
        ∃ a b : L, algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r =
          algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E)) ∧
    (∀ r : Work.MotC2.Coord E,
      (algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r * (Work.MotC2.infW E) ^ 3 ∈
          Work.MotC2.infPlace E ↔
        ∃ a b c : L, algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r =
          algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E +
            algebraMap L (Work.MotC2.Func E) c * Work.MotC2.genY E)) := by
  constructor
  · intro r
    constructor
    · intro hr
      obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) r
      have hf : algebraMap (Coord E) (Func E) r =
          Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E := by
        rw [← hpq, map_add, (algebraMap_smul_eq_aeval L E p).1,
          (algebraMap_smul_eq_aeval L E q).2]
      have hT : (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) *
          (infW E) ^ 2 ∈ T E := infPlace_le_T E (hf ▸ hr)
      obtain ⟨P, Q, P', Q', hQ, hQ', dQ, dQ', heq⟩ := (mem_T_iff E _).mp hT
      have hexp := algebraMap_mul_infW_sq_eq E p q
      obtain ⟨huniq1, huniq2⟩ := T_unique E
        (A := Tgen E P Q) (B := Tgen E P' Q')
        (A' := Tgen E (cubicPoly E * (p - q * linPoly E)) (X ^ 4))
        (B' := Tgen E (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)) (X ^ 2))
        ⟨P, Q, hQ, rfl⟩ ⟨P', Q', hQ', rfl⟩
        ⟨cubicPoly E * (p - q * linPoly E), X ^ 4, pow_ne_zero 4 X_ne_zero, rfl⟩
        ⟨-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2), X ^ 2,
          pow_ne_zero 2 X_ne_zero, rfl⟩ (by rw [← heq, hexp])
      have h1 : (p - q * linPoly E).natDegree ≤ 1 :=
        natDegree_le_of_Tgen_eq_mul_cubicPoly E hQ huniq1 dQ (by norm_num)
      have h2 : (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)).natDegree ≤ 2 := by
        rcases eq_or_ne (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)) 0 with h0 | h0
        · rw [h0]; simp
        · exact natDegree_le_of_Tgen_eq_X_pow E hQ' h0 huniq2 dQ'
      obtain ⟨hq0, hp1⟩ := w_sq_deg_constraints L E p q
        (Polynomial.natDegree_le_iff_degree_le.mp h1)
        ((Polynomial.natDegree_le_iff_degree_le (p := -(p * linPoly E) +
          q * (cubicPoly E + linPoly E ^ 2)) (n := 2)).mp h2)
      refine ⟨p.coeff 0, p.coeff 1, ?_⟩
      rw [hf, hq0, map_zero, zero_mul, add_zero, eq_C_add_C_mul_X_of_degree_le_one hp1]
      simp [aeval_def]
    · rintro ⟨a, b, hab⟩
      rw [hab]
      have h : (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) * (infW E) ^ 2 =
          algebraMap L (Func E) a * (infW E) ^ 2 +
            algebraMap L (Func E) b * (genX E * (infW E) ^ 2) := by ring
      rw [h]
      exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ a) (infW_sq_mem_infPlace E))
        (mul_mem (Subalgebra.algebraMap_mem _ b) (genX_mul_infW_sq_mem_infPlace E))
  · intro r
    constructor
    · intro hr
      obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) r
      have hf : algebraMap (Coord E) (Func E) r =
          Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E := by
        rw [← hpq, map_add, (algebraMap_smul_eq_aeval L E p).1,
          (algebraMap_smul_eq_aeval L E q).2]
      have hT : (Polynomial.aeval (genX E) p + Polynomial.aeval (genX E) q * genY E) *
          (infW E) ^ 3 ∈ T E := infPlace_le_T E (hf ▸ hr)
      obtain ⟨P, Q, P', Q', hQ, hQ', dQ, dQ', heq⟩ := (mem_T_iff E _).mp hT
      have hexp := algebraMap_mul_infW_cube_eq E p q
      obtain ⟨huniq1, huniq2⟩ := T_unique E
        (A := Tgen E P Q) (B := Tgen E P' Q')
        (A' := Tgen E (cubicPoly E * (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)))
          (X ^ 6))
        (B' := Tgen E (p * (cubicPoly E + linPoly E ^ 2) -
          q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))) (X ^ 4))
        ⟨P, Q, hQ, rfl⟩ ⟨P', Q', hQ', rfl⟩
        ⟨cubicPoly E * (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)), X ^ 6,
          pow_ne_zero 6 X_ne_zero, rfl⟩
        ⟨p * (cubicPoly E + linPoly E ^ 2) -
            q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2)), X ^ 4,
          pow_ne_zero 4 X_ne_zero, rfl⟩ (by rw [← heq, hexp])
      have h1 : (-(p * linPoly E) + q * (cubicPoly E + linPoly E ^ 2)).natDegree ≤ 3 :=
        natDegree_le_of_Tgen_eq_mul_cubicPoly E hQ huniq1 dQ (by norm_num)
      have h2 : (p * (cubicPoly E + linPoly E ^ 2) -
          q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))).natDegree ≤ 4 := by
        rcases eq_or_ne (p * (cubicPoly E + linPoly E ^ 2) -
            q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))) 0 with h0 | h0
        · rw [h0]; simp
        · exact natDegree_le_of_Tgen_eq_X_pow E hQ' h0 huniq2 dQ'
      obtain ⟨hq0, hp1⟩ := w_cube_deg_constraints L E p q
        (Polynomial.natDegree_le_iff_degree_le.mp h1)
        ((Polynomial.natDegree_le_iff_degree_le (p := p * (cubicPoly E + linPoly E ^ 2) -
          q * (linPoly E * (2 * cubicPoly E + linPoly E ^ 2))) (n := 4)).mp h2)
      refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_⟩
      rw [hf, Polynomial.eq_C_of_degree_le_zero hq0, eq_C_add_C_mul_X_of_degree_le_one hp1]
      simp [aeval_def]
    · rintro ⟨a, b, c, hab⟩
      rw [hab]
      have h : (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E +
            algebraMap L (Func E) c * genY E) * (infW E) ^ 3 =
          algebraMap L (Func E) a * (infW E) ^ 3 +
            algebraMap L (Func E) b * (genX E * (infW E) ^ 3) +
            algebraMap L (Func E) c * (genY E * (infW E) ^ 3) := by ring
      rw [h]
      exact add_mem (add_mem (mul_mem (Subalgebra.algebraMap_mem _ a) (infW_cube_mem_infPlace E))
        (mul_mem (Subalgebra.algebraMap_mem _ b) (genX_mul_infW_cube_mem_infPlace E)))
        (mul_mem (Subalgebra.algebraMap_mem _ c) (genY_mul_infW_cube_mem_infPlace E))

end Work.MotC2
