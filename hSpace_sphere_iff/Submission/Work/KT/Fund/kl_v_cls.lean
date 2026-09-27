import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs
import Submission.Work.KT.Fund.kl_hom_defs
import Submission.Work.KT.Fund.isUnit_matrix_forall
import Submission.Work.KT.Fund.kappa_homotopic
import Submission.Work.KT.Fund.spectral_split_out

/-!
# `Work.KT.Fund.kl_v_cls` — the "inside" factor `klV` is homotopic to the Bott unit `klV0`

For `b` a matrix over `C(X, ℂ)` and `E` an idempotent commuting with `b`, the "inside" factor of
the linear clutching splitting

  `klV X n b E = z • E + E b + (1 - E)`

is homotopic, through units over `C((X × I) × S¹, ℂ)`, to the Bott unit

  `klV0 X n E = z • E + (1 - E)`.

The homotopy is `H(x, t, z) = z • E(x) + t • (E b)(x) + (1 - E(x))` (see
`Work.KT.Fund.klHom`); it is a unit because `E` is idempotent and `E b` commutes with `E`, so that
inside the Peirce decomposition `1 = E + (1 - E)` one has the block decomposition

  `z • E + t • (E b) + (1 - E) = (z • E + (1 - E)) * (1 + (z⁻¹ t) • (E b))`,

a product of a unit and the scalar multiple of the unit `z • 1 + t • (E b)` supplied by the
hypothesis `hins`.

Since `Work.KT.Fund.kappa` is invariant under homotopy of the clutching function
(`Work.KT.Fund.kappa_homotopic`), the two clutching classes agree:
`κ(klV) = κ(klV0)`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

@[simp] lemma coe_zero_unitInterval : (((0 : unitInterval) : ℝ) : ℂ) = 0 := rfl
@[simp] lemma coe_one_unitInterval : (((1 : unitInterval) : ℝ) : ℂ) = 1 := rfl

/-- The real scalar action on complex matrices is the complex one. -/
lemma real_smul_matrix {n : ℕ} (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply]

@[simp] lemma tCoeff_apply_real (p : (X × unitInterval) × Sph ℂ) :
    tCoeff X p = ((p.1.2 : ℝ) : ℂ) := rfl

@[simp] lemma incl0_apply' (p : X × Sph ℂ) :
    incl0 X p = ((p.1, (0 : unitInterval)), p.2) := rfl

@[simp] lemma incl1_apply' (p : X × Sph ℂ) :
    incl1 X p = ((p.1, (1 : unitInterval)), p.2) := rfl

/-- Pointwise evaluation is multiplicative on matrices over `C(X, ℂ)`. -/
lemma map_eval_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) :
    (M * N).map (fun f => f x) = M.map (fun f => f x) * N.map (fun f => f x) :=
  Matrix.map_mul (f := (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)

/-- The pointwise evaluation of the homotopy matrix `klHom`. -/
lemma klHom_apply (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (y : (X × unitInterval) × Sph ℂ) :
    klHom X n b E i j y
      = (y.2 : ℂ) * (E i j y.1.1)
        + (tCoeff X y) * ((E * b) i j y.1.1)
        + ((if i = j then (1 : ℂ) else 0) - E i j y.1.1) := by
  simp only [klHom, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply,
    DFunLike.ite_apply, klz_apply, klP_apply, pullI_apply, tCoeff_apply_real, smul_eq_mul]

/-- The `t = 0` slice of the homotopy is the Bott unit `klV0`. -/
lemma klHom_slice0 (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (klHom X n b E).map (fun f => f.comp (incl0 X)) = klV0 X n E := by
  ext i j p
  change klHom X n b E i j (incl0 X p) = klV0 X n E i j p
  rw [klHom_apply]
  simp only [klV0, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, DFunLike.ite_apply, klz_apply,
    klP_apply, tCoeff_apply_real, smul_eq_mul, incl0_apply', coe_zero_unitInterval,
    zero_mul, add_zero]

/-- The `t = 1` slice of the homotopy is the "inside" factor `klV`. -/
lemma klHom_slice1 (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (klHom X n b E).map (fun f => f.comp (incl1 X)) = klV X n b E := by
  ext i j p
  change klHom X n b E i j (incl1 X p) = klV X n b E i j p
  rw [klHom_apply]
  simp only [klV, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.one_apply, ContinuousMap.zero_apply, DFunLike.ite_apply, klz_apply,
    klP_apply, tCoeff_apply_real, smul_eq_mul, incl1_apply', coe_one_unitInterval,
    one_mul]

/-- **Algebraic core.**  For an idempotent `P` and a matrix `B` with `P * B = B`, if
`z • 1 + w • B` is a unit (`z ≠ 0`) then so is `z • P + w • B + (1 - P)`.  The two factors
`z • P + (1 - P)` and `1 + (z⁻¹ w) • B` are units. -/
lemma isUnit_smul_idem_add {n : ℕ} (P B : Matrix (Fin n) (Fin n) ℂ) (z w : ℂ)
    (hP : P * P = P) (hPB : P * B = B) (hz : z ≠ 0)
    (hW : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + w • B)) :
    IsUnit (z • P + w • B + (1 - P)) := by
  have hfact : z • P + w • B + (1 - P)
      = (z • P + (1 - P)) * (1 + (z⁻¹ * w) • B) := by
    have h1 : (z • P) * ((z⁻¹ * w) • B) = w • B := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPB, ← mul_assoc, mul_inv_cancel₀ hz,
        one_mul]
    have h2 : (1 - P) * ((z⁻¹ * w) • B) = 0 := by
      rw [Matrix.mul_smul, sub_mul, one_mul, hPB, sub_self, smul_zero]
    rw [mul_add, mul_one, add_mul, h1, h2, add_zero]
    abel
  have hU : IsUnit (z • P + (1 - P)) := by
    have h1 : (z • P) * (z⁻¹ • P) = P := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, mul_inv_cancel₀ hz, one_smul]
    have h2 : (z⁻¹ • P) * (z • P) = P := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, inv_mul_cancel₀ hz, one_smul]
    have h3 := isUnit_of_mul_eq_idem (e := P) (a := z • P) (t := z⁻¹ • P) hP h1 h2
    simpa only [Matrix.mul_smul, hP] using h3
  have hV : IsUnit (1 + (z⁻¹ * w) • B) := by
    have hzU : IsUnit (z⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
      ⟨⟨z⁻¹ • 1, z • 1,
        by rw [Matrix.smul_mul, one_mul, smul_smul, inv_mul_cancel₀ hz, one_smul],
        by rw [Matrix.smul_mul, one_mul, smul_smul, mul_inv_cancel₀ hz, one_smul]⟩, rfl⟩
    have heq : z⁻¹ • (z • (1 : Matrix (Fin n) (Fin n) ℂ) + w • B)
        = 1 + (z⁻¹ * w) • B := by
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul]
    rw [← heq]
    have h2 : z⁻¹ • (z • (1 : Matrix (Fin n) (Fin n) ℂ) + w • B)
        = (z⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ))
          * (z • (1 : Matrix (Fin n) (Fin n) ℂ) + w • B) := by
      rw [Matrix.smul_mul, one_mul]
    rw [h2]
    exact hzU.mul hW
  rw [hfact]
  exact hU.mul hV

/-- **The homotopy matrix is a unit.**  Under the pointwise invertibility hypothesis `hins` on
`z • 1 + t • (E b)(x)`, the homotopy matrix `klHom` is a unit of matrices over
`C((X × I) × S¹, ℂ)`. -/
lemma isUnit_klHom (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E)
    (hins : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x)))) :
    IsUnit (klHom X n b E) := by
  rw [isUnit_matrix_forall]
  intro y
  set B : Matrix (Fin n) (Fin n) ℂ := (E * b).map (fun f => f y.1.1) with hB
  set P : Matrix (Fin n) (Fin n) ℂ := E.map (fun f => f y.1.1) with hPdef
  have hP : P * P = P := by rw [hPdef, ← map_eval_mul X E E y.1.1, hE]
  have hPB : P * B = B := by
    rw [hPdef, hB, ← map_eval_mul X E (E * b) y.1.1, ← mul_assoc, hE]
  have hz : ‖(y.2 : ℂ)‖ = 1 := by
    have h := Metric.mem_sphere.mp y.2.2
    rwa [dist_eq_norm, sub_zero] at h
  have hz0 : (y.2 : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
  have hW : IsUnit ((y.2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (tCoeff X y) • B) := by
    have h := hins y.1.1 (y.1.2 : ℝ) (y.2 : ℂ) (unitInterval.nonneg y.1.2)
      (unitInterval.le_one y.1.2) hz
    rw [← hB] at h
    have hc : (y.1.2 : ℝ) • B = (tCoeff X y) • B := by
      rw [real_smul_matrix, tCoeff_apply_real]
    rwa [hc] at h
  have hev : (klHom X n b E).map (fun f => f y)
      = (y.2 : ℂ) • P + (tCoeff X y) • B + (1 - P) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [klHom_apply]
    simp only [hPdef, hB, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hev]
  exact isUnit_smul_idem_add P B (y.2 : ℂ) (tCoeff X y) hP hPB hz0 hW

end

section Main

theorem kl_v_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) (hc : E * b = b * E)
    (hins : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) + t • ((E * b).map (fun f => f x))))
    (v : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hv : (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klV X n b E)
    (v₀ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hv₀ : (v₀ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klV0 X n E) :
    Work.KT.Fund.kappa X n v = Work.KT.Fund.kappa X n v₀ := by
  have hH : IsUnit (klHom X n b E) := isUnit_klHom X n b E hE hins
  let H : (Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ))ˣ := hH.unit
  have hHcoe : (H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)) = klHom X n b E :=
    hH.unit_spec
  have h0 : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
      (fun f => f.comp (incl0 X))) = (v₀ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hHcoe, klHom_slice0, ← hv₀]
  have h1 : ((H : Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ)).map
      (fun f => f.comp (incl1 X))) = (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hHcoe, klHom_slice1, ← hv]
  exact (kappa_homotopic X n v₀ v H h0 h1).symm

end Main

end Work.KT.Fund
