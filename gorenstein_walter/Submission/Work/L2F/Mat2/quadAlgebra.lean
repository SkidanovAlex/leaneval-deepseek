/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quadratic algebra `A = F·1 + F·T` inside `M₂(F)`, and the inverting element `w`

For a field `F`, `d : F` and

* `T = quadT d = !![0, d; 1, 0]`  (so `T * T = d • 1`, `det T = -d`),

the `F`-linear span `A = F·1 + F·T` is the quadratic algebra `F[X]/(X²-d)`; it is the
`F`-span of the "non-split torus" `hypTorus F d = {!![a, d*b; b, a] | a² - d·b² = 1}`
(the norm-one elements of `A`), and `A ∩ SL(2,F) = hypTorus F d`.

Membership in `A` is the pair of entry equations `M 0 1 = d * M 1 0` and `M 1 1 = M 0 0`
(`inQuad d M`).  The basic structure of `A` is collected here:

* `quadMat_mul`, `inQuad_mul`: `A` is closed under multiplication, and `A` is commutative;
* `inQuad_iff`: `M ∈ A ↔ ∃ a b, M = !![a, d*b; b, a]`;
* `inQuad_of_commute`: the commutant of `T` is exactly `A`;
* `inQuad_sq_eq`: the only `M ∈ A` with `M * M = d • 1` are `±T`;
* `mem_hypTorus_of_inQuad`, `inQuad_of_mem_hypTorus`: `A ∩ SL(2,F) = hypTorus F d`.

For `p q : F` with `p² - d·q² = -1` the matrix

* `w = hypWMat d p q = !![p, -d*q; q, -p]`

lies in `SL(2,F)` (`hypWSL`), has `w * w = -1` (`hypWMat_mul_self`), conjugates `T` to `-T`
(`hypWMat_mul_quadT`) and hence conjugates `a•1 + b•T` to `a•1 - b•T`
(`hypWMat_mul_quadMat`).  Consequently (`hypWSL_inverts`) `w` inverts every element of
`hypTorus F d`:

`w * u * w⁻¹ = u⁻¹`  for all `u ∈ hypTorus F d`,

so `w` lies in the normalizer of `hypTorus F d` in `SL(2,F)` (`hypWSL_mem_normalizer`).

Existence of `p, q` is `exists_sq_sub_mul_sq F h2 d hd (-1)` (`Work.L2F.Conic`), and the
normalizer computation for `hypTorus F d` in `SL(2,F)` is in
`Submission/Work/L2F/PSL/normalizer_pslHypTorus_dihedral.lean`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Involution.mem_normalizer_zpowers

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

variable {F : Type*} [Field F]

/-! ## The algebra `A = F·1 + F·T` -/

/-- The matrix `T = !![0, d; 1, 0]`; `T * T = d • 1` and `det T = -d`. -/
def quadT (d : F) : Matrix (Fin 2) (Fin 2) F := !![0, d; 1, 0]

/-- The matrix `!![a, d*b; b, a] = a • 1 + b • T` of the quadratic algebra `A`. -/
def quadMat (d a b : F) : Matrix (Fin 2) (Fin 2) F := !![a, d * b; b, a]

/-- Membership in `A = F·1 + F·T`, as the two entry equations. -/
def inQuad (d : F) (M : Matrix (Fin 2) (Fin 2) F) : Prop :=
  M 0 1 = d * M 1 0 ∧ M 1 1 = M 0 0

@[simp] theorem quadT_apply_00 (d : F) : (quadT d) 0 0 = 0 := rfl
@[simp] theorem quadT_apply_01 (d : F) : (quadT d) 0 1 = d := rfl
@[simp] theorem quadT_apply_10 (d : F) : (quadT d) 1 0 = 1 := rfl
@[simp] theorem quadT_apply_11 (d : F) : (quadT d) 1 1 = 0 := rfl

@[simp] theorem quadMat_apply_00 (d a b : F) : (quadMat d a b) 0 0 = a := rfl
@[simp] theorem quadMat_apply_01 (d a b : F) : (quadMat d a b) 0 1 = d * b := rfl
@[simp] theorem quadMat_apply_10 (d a b : F) : (quadMat d a b) 1 0 = b := rfl
@[simp] theorem quadMat_apply_11 (d a b : F) : (quadMat d a b) 1 1 = a := rfl

/-- The product formula in `A`: `(a+bT)(c+eT) = (ac+d·be) + (ae+bc)T`. -/
theorem quadMat_mul (d a b c e : F) :
    quadMat d a b * quadMat d c e = quadMat d (a * c + d * (b * e)) (a * e + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The coefficients in `A` are unique. -/
theorem quadMat_eq_iff (d a b c e : F) :
    quadMat d a b = quadMat d c e ↔ a = c ∧ b = e := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) h
    simp only [quadMat_apply_00, quadMat_apply_10] at h00 h10
    exact ⟨h00, h10⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem quadT_mul_quadT (d : F) : quadT d * quadT d = d • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadT, Matrix.mul_apply, Fin.sum_univ_two]

theorem quadMat_smul_one_add (d a b : F) :
    quadMat d a b = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • quadT d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat, quadT] <;> ring

theorem quadMat_zero (d : F) : quadMat d 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat]

theorem quadMat_one (d : F) : quadMat d 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat]

theorem quadMat_quadT (d : F) : quadMat d 0 1 = quadT d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat, quadT]

theorem quadMat_neg_quadT (d : F) : quadMat d 0 (-1) = -quadT d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat, quadT]

theorem quadMat_det (d a b : F) : (quadMat d a b).det = a ^ 2 - d * b ^ 2 := by
  rw [quadMat, Matrix.det_fin_two_of]
  ring

/-- `inQuad d M` is exactly `∃ a b, M = !![a, d*b; b, a]`. -/
theorem inQuad_iff (d : F) (M : Matrix (Fin 2) (Fin 2) F) :
    inQuad d M ↔ ∃ a b : F, M = quadMat d a b := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨M 0 0, M 1 0, by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [quadMat, h1, h2]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨by simp [inQuad, quadMat], by simp [inQuad, quadMat]⟩

theorem inQuad_quadMat (d a b : F) : inQuad d (quadMat d a b) :=
  (inQuad_iff d _).mpr ⟨a, b, rfl⟩

theorem inQuad_zero (d : F) : inQuad d (0 : Matrix (Fin 2) (Fin 2) F) :=
  (inQuad_iff d _).mpr ⟨0, 0, (quadMat_zero d).symm⟩

theorem inQuad_one (d : F) : inQuad d (1 : Matrix (Fin 2) (Fin 2) F) :=
  (inQuad_iff d _).mpr ⟨1, 0, (quadMat_one d).symm⟩

theorem inQuad_quadT (d : F) : inQuad d (quadT d) :=
  (inQuad_iff d _).mpr ⟨0, 1, (quadMat_quadT d).symm⟩

theorem inQuad_neg_quadT (d : F) : inQuad d (-(quadT d)) :=
  (inQuad_iff d _).mpr ⟨0, -1, (quadMat_neg_quadT d).symm⟩

theorem inQuad_add {d : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : inQuad d M)
    (hN : inQuad d N) : inQuad d (M + N) := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hM
  obtain ⟨c, e, rfl⟩ := (inQuad_iff d N).mp hN
  rw [show quadMat d a b + quadMat d c e = quadMat d (a + c) (b + e) from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quadMat] <;> ring]
  exact inQuad_quadMat d (a + c) (b + e)

theorem inQuad_neg {d : F} {M : Matrix (Fin 2) (Fin 2) F} (hM : inQuad d M) :
    inQuad d (-M) := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hM
  rw [show -(quadMat d a b) = quadMat d (-a) (-b) from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quadMat] <;> ring]
  exact inQuad_quadMat d (-a) (-b)

theorem inQuad_sub {d : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : inQuad d M)
    (hN : inQuad d N) : inQuad d (M - N) := by
  rw [sub_eq_add_neg]
  exact inQuad_add hM (inQuad_neg hN)

theorem inQuad_smul {d : F} {M : Matrix (Fin 2) (Fin 2) F} (c : F) (hM : inQuad d M) :
    inQuad d (c • M) := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hM
  rw [show c • quadMat d a b = quadMat d (c * a) (c * b) from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quadMat] <;> ring]
  exact inQuad_quadMat d (c * a) (c * b)

theorem inQuad_mul {d : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : inQuad d M)
    (hN : inQuad d N) : inQuad d (M * N) := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hM
  obtain ⟨c, e, rfl⟩ := (inQuad_iff d N).mp hN
  rw [quadMat_mul]
  exact inQuad_quadMat d _ _

/-- `A` is commutative. -/
theorem inQuad_mul_comm {d : F} {M N : Matrix (Fin 2) (Fin 2) F} (hM : inQuad d M)
    (hN : inQuad d N) : M * N = N * M := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hM
  obtain ⟨c, e, rfl⟩ := (inQuad_iff d N).mp hN
  rw [quadMat_mul, quadMat_mul]
  congr 1 <;> ring

/-- The commutant of `T = !![0,d;1,0]` is exactly `A`. -/
theorem inQuad_of_commute {d : F} {M : Matrix (Fin 2) (Fin 2) F}
    (h : M * quadT d = quadT d * M) : inQuad d M := by
  refine ⟨?_, ?_⟩
  · have h00 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 0 0) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two, quadT, inQuad] using h00
  · have h10 := congrArg (fun N : Matrix (Fin 2) (Fin 2) F => N 1 0) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two, quadT, inQuad] using h10

/-- The only `M ∈ A` with `M * M = d • 1` are `±T` (`d ≠ 0` a nonsquare, `2 ≠ 0`). -/
theorem inQuad_sq_eq {d : F} (h2 : (2 : F) ≠ 0) (hd : d ≠ 0) (hns : ∀ a : F, a * a ≠ d)
    {M : Matrix (Fin 2) (Fin 2) F} (hA : inQuad d M)
    (hsq : M * M = d • (1 : Matrix (Fin 2) (Fin 2) F)) :
    M = quadT d ∨ M = -quadT d := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hA
  have hmul : quadMat d a b * quadMat d a b = quadMat d (a * a + d * (b * b)) (a * b + b * a) :=
    quadMat_mul d a b a b
  rw [hmul, show d • (1 : Matrix (Fin 2) (Fin 2) F) = quadMat d d 0 from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [quadMat]] at hsq
  obtain ⟨h1, h2'⟩ := (quadMat_eq_iff d _ _ _ _).mp hsq
  have h2'' : 2 * (a * b) = 0 := by linear_combination h2'
  have hab : a * b = 0 := by
    rcases mul_eq_zero.mp h2'' with h | h
    · exact absurd h h2
    · exact h
  rcases mul_eq_zero.mp hab with ha | hb
  · subst ha
    have hb2 : b * b = 1 := by
      refine mul_left_cancel₀ hd ?_
      simpa using h1
    rcases mul_self_eq_one_iff.mp hb2 with hb1 | hbn1
    · left
      rw [hb1, quadMat_quadT]
    · right
      rw [hbn1, quadMat_neg_quadT]
  · subst hb
    exact absurd (by linear_combination h1 : a * a = d) (hns a)

/-! ## `A ∩ SL(2,F) = hypTorus F d` -/

theorem inQuad_of_mem_hypTorus {d : F} {x : Matrix.SpecialLinearGroup (Fin 2) F}
    (hx : x ∈ Work.L2F.hypTorus F d) : inQuad d (x : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨a, b, -, hx'⟩ := (Work.L2F.Conic.mem_hypTorus F d x).mp hx
  rw [hx']
  exact inQuad_quadMat d a b

theorem mem_hypTorus_of_inQuad {d : F} {M : Matrix (Fin 2) (Fin 2) F} (hA : inQuad d M)
    (hdet : M.det = 1) :
    (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F) ∈ Work.L2F.hypTorus F d := by
  obtain ⟨a, b, rfl⟩ := (inQuad_iff d M).mp hA
  refine (Work.L2F.Conic.mem_hypTorus F d
    (⟨quadMat d a b, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F)).mpr ⟨a, b, ?_, rfl⟩
  rw [← quadMat_det d a b]
  exact hdet

/-! ## The inverting element `w = !![p, -d*q; q, -p]` -/

/-- The matrix `w = !![p, -d*q; q, -p]`. -/
def hypWMat (d p q : F) : Matrix (Fin 2) (Fin 2) F := !![p, -(d * q); q, -p]

@[simp] theorem hypWMat_apply_00 (d p q : F) : (hypWMat d p q) 0 0 = p := rfl
@[simp] theorem hypWMat_apply_01 (d p q : F) : (hypWMat d p q) 0 1 = -(d * q) := rfl
@[simp] theorem hypWMat_apply_10 (d p q : F) : (hypWMat d p q) 1 0 = q := rfl
@[simp] theorem hypWMat_apply_11 (d p q : F) : (hypWMat d p q) 1 1 = -p := rfl

/-- `det w = 1` when `p² - d*q² = -1`. -/
theorem hypWMat_det (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) : (hypWMat d p q).det = 1 := by
  rw [hypWMat, Matrix.det_fin_two_of]
  linear_combination -hpq

/-- The element `w` of `SL(2,F)` attached to `p, q` with `p² - d*q² = -1`. -/
def hypWSL (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨hypWMat d p q, hypWMat_det d p q hpq⟩

@[simp] theorem coe_hypWSL (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    ((hypWSL d p q hpq : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      hypWMat d p q := rfl

/-- `w * w = (p² - d*q²) • 1`; in particular `w * w = -1` when `p² - d*q² = -1`. -/
theorem hypWMat_mul_self (d p q : F) :
    hypWMat d p q * hypWMat d p q = (p ^ 2 - d * q ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypWMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `w * T = -(T * w)`: `w` conjugates `T` to `-T`. -/
theorem hypWMat_mul_quadT (d p q : F) :
    hypWMat d p q * quadT d = -(quadT d * hypWMat d p q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypWMat, quadT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `w * (a + bT) = (a - bT) * w`: conjugation by `w` is `T ↦ -T` on `A`. -/
theorem hypWMat_mul_quadMat (d p q a b : F) :
    hypWMat d p q * quadMat d a b = quadMat d a (-b) * hypWMat d p q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypWMat, quadMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The square of `w` is `-1` in `SL(2,F)` when `p² - d*q² = -1`. -/
theorem hypWSL_mul_self (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    hypWSL d p q hpq * hypWSL d p q hpq = Work.L2F.negOne F := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_hypWSL,
    show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = -1 from rfl]
  rw [hypWMat_mul_self, hpq]
  simp

/-- The adjugate of `w = !![p, -d*q; q, -p]` is `!![-p, d*q; -q, p] = hypWMat d (-p) (-q)`. -/
theorem hypWMat_adjugate (d p q : F) :
    (hypWMat d p q).adjugate = hypWMat d (-p) (-q) := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypWMat] <;> ring

/-- The matrix of `w⁻¹` in `SL(2,F)` is `hypWMat d (-p) (-q)` (since `det w = 1`, the inverse is
the adjugate). -/
theorem coe_hypWSL_inv (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    (((hypWSL d p q hpq)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = hypWMat d (-p) (-q) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_hypWSL, hypWMat_adjugate]

/-- `w * w⁻¹ = 1` at the level of matrices (as `w * adjugate w = det w • 1 = 1`). -/
theorem hypWMat_mul_adjugate (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    hypWMat d p q * hypWMat d (-p) (-q) = 1 := by
  rw [← hypWMat_adjugate, Matrix.mul_adjugate, hypWMat_det d p q hpq, one_smul]

/-- `w` inverts `T`. -/
theorem hypWSL_conj_quadT (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    ((hypWSL d p q hpq : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        quadT d *
        (((hypWSL d p q hpq)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = -quadT d := by
  rw [coe_hypWSL, coe_hypWSL_inv, hypWMat_mul_quadT, neg_mul, mul_assoc,
    hypWMat_mul_adjugate d p q hpq, mul_one]

/-- Conjugation by `w` on `A` is `a + bT ↦ a - bT`. -/
theorem hypWSL_conj_quadMat (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) (a b : F) :
    ((hypWSL d p q hpq : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        quadMat d a b *
        (((hypWSL d p q hpq)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = quadMat d a (-b) := by
  rw [coe_hypWSL, coe_hypWSL_inv, hypWMat_mul_quadMat, mul_assoc,
    hypWMat_mul_adjugate d p q hpq, mul_one]

/-- `w` conjugates `u ∈ hypTorus F d` to `u⁻¹ -/
theorem hypWSL_conj_hypTorus (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1)
    {u : Matrix.SpecialLinearGroup (Fin 2) F} (hu : u ∈ Work.L2F.hypTorus F d) :
    hypWSL d p q hpq * u * (hypWSL d p q hpq)⁻¹ = u⁻¹ := by
  obtain ⟨a, b, hab, hu'⟩ := (Work.L2F.Conic.mem_hypTorus F d u).mp hu
  have hdet : (quadMat d a b).det = 1 := by rw [quadMat_det]; exact hab
  have hu_m : (u : Matrix (Fin 2) (Fin 2) F) = quadMat d a b := hu'
  have hu_inv : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      quadMat d a (-b) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hu_m, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [quadMat] <;> ring
  have hmul : hypWSL d p q hpq * u = u⁻¹ * hypWSL d p q hpq := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_hypWSL, hu_m, hu_inv,
      hypWMat_mul_quadMat]
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

/-- `w ∈ N_{SL(2,F)}(hypTorus F d)`. -/
theorem hypWSL_mem_normalizer (d p q : F) (hpq : p ^ 2 - d * q ^ 2 = -1) :
    hypWSL d p q hpq ∈
      Subgroup.normalizer (Work.L2F.hypTorus F d :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hinv : ∀ u ∈ Work.L2F.hypTorus F d,
      hypWSL d p q hpq * u * (hypWSL d p q hpq)⁻¹ = u⁻¹ :=
    fun u hu => hypWSL_conj_hypTorus d p q hpq hu
  have hinv' : ∀ z ∈ Work.L2F.hypTorus F d,
      (hypWSL d p q hpq)⁻¹ * z * hypWSL d p q hpq = z⁻¹ := by
    intro z hz
    have h1 := hinv z⁻¹ ((Work.L2F.hypTorus F d).inv_mem hz)
    rw [inv_inv] at h1
    calc (hypWSL d p q hpq)⁻¹ * z * hypWSL d p q hpq
        = (hypWSL d p q hpq)⁻¹ * (hypWSL d p q hpq * z⁻¹ * (hypWSL d p q hpq)⁻¹) *
            hypWSL d p q hpq := by rw [h1]
      _ = z⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hinv h hh]
    exact (Work.L2F.hypTorus F d).inv_mem hh
  · intro hh
    have hthis : h = (hypWSL d p q hpq)⁻¹ *
        (hypWSL d p q hpq * h * (hypWSL d p q hpq)⁻¹) * hypWSL d p q hpq := by group
    rw [hthis, hinv' _ hh]
    exact (Work.L2F.hypTorus F d).inv_mem hh

/-! ## An element of `hypTorus F d` with non-zero lower left entry -/

/-- For `q = |F| ≥ 5`, `d ≠ 0` a nonsquare, there is an element of `hypTorus F d` with
non-zero `(1,0)` entry: the only elements of `hypTorus F d` with vanishing `(1,0)` entry are
`1` and `-1`, and `|hypTorus F d| = q + 1 ≥ 6 > 2`. -/
theorem hypTorus_entry_ne_zero (d : F) [Fintype F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F)
    (hd : d ≠ 0) (hns : ∀ a : F, a * a ≠ d) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h ∈ Work.L2F.hypTorus F d ∧ (h : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hle : Work.L2F.hypTorus F d ≤ Subgroup.zpowers (Work.L2F.negOne F) := by
    intro x hx
    have h0 := hcon x hx
    obtain ⟨a, b, hab, hx'⟩ := (Work.L2F.Conic.mem_hypTorus F d x).mp hx
    have hb : b = 0 := by simpa [hx'] using h0
    have ha2 : a ^ 2 = 1 := by rw [hb] at hab; simpa using hab
    rcases sq_eq_one_iff.mp ha2 with ha | ha
    · rw [show x = 1 from Subtype.ext (by
        rw [hx', hb, ha]
        ext i j; fin_cases i <;> fin_cases j <;> simp)]
      exact Subgroup.one_mem _
    · rw [show x = Work.L2F.negOne F from Subtype.ext (by
        rw [hx', hb, ha]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne])]
      exact Subgroup.mem_zpowers _
  have hne : Work.L2F.negOne F ≠ (1 : Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro h
    have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h00
    have h' : (-1 : F) = 1 := by
      simpa [Work.L2F.negOne] using h00
    have h'' : (1 : F) + 1 = 0 := neg_eq_iff_add_eq_zero.mp h'
    rw [one_add_one_eq_two] at h''
    exact h2 h''
  have hzp : Nat.card ↥(Subgroup.zpowers (Work.L2F.negOne F)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (Work.L2F.Involution.negOne_pow_two F) hne
  have hcard := Subgroup.card_le_of_le hle
  rw [hzp, Work.L2F.Conic.hypTorus_card F h2 d hd hns] at hcard
  omega

end Work.L2F.Mat2
