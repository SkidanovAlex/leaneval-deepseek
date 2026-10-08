import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Conic.mem_hypTorus
import Submission.Work.L2F.Conic.hypTorus_cyclic
import Submission.Work.L2F.Conic.hypTorus_card
import Submission.Work.L2F.Conic.exists_sq_sub_mul_sq
import Submission.Work.L2F.Mat2.quadAlgebra
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Involution.mem_normalizer_zpowers
import Submission.Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two

open scoped MatrixGroups
open Matrix
open Subgroup (centralizer normalizer zpowers)

namespace Work.L2F.Semisimple

variable {F : Type*} [Field F]

/-! ## The commutant of a traceless matrix with `W * W = δ • 1` -/

/-- If `W` is a traceless `2×2` matrix over a field of odd characteristic with `W * W = δ • 1` and
`δ ≠ 0`, then any matrix that commutes with `W` lies in the `F`-span `algSpan F W = F·1 + F·W`. -/
theorem commutant_algSpan (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (W : Matrix (Fin 2) (Fin 2) F) (δ : F) (htr : W.trace = 0) (hsq : W * W = δ • 1)
    (hδ : δ ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) (hM : M * W = W * M) :
    M ∈ Work.L2F.Torus.algSpan F W := by
  have htr' : W 0 0 + W 1 1 = 0 := by
    have h := htr; rw [Matrix.trace_fin_two] at h; exact h
  have h11 : W 1 1 = -W 0 0 := by linear_combination htr'
  have h00 : W 0 0 * W 0 0 + W 0 1 * W 1 0 = δ := by
    have h := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e00 : M 0 0 * W 0 0 + M 0 1 * W 1 0 = W 0 0 * M 0 0 + W 0 1 * M 1 0 := by
    have h := congrFun (congrFun hM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e01 : M 0 0 * W 0 1 + M 0 1 * W 1 1 = W 0 0 * M 0 1 + W 0 1 * M 1 1 := by
    have h := congrFun (congrFun hM 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e10 : M 1 0 * W 0 0 + M 1 1 * W 1 0 = W 1 0 * M 0 0 + W 1 1 * M 1 0 := by
    have h := congrFun (congrFun hM 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hI : M 0 1 * W 1 0 = W 0 1 * M 1 0 := by linear_combination e00
  have hII : W 0 1 * (M 0 0 - M 1 1) = 2 * (W 0 0 * M 0 1) := by
    rw [h11] at e01; linear_combination e01
  have hIII : W 1 0 * (M 0 0 - M 1 1) = 2 * (W 0 0 * M 1 0) := by
    rw [h11] at e10; linear_combination -e10
  rcases eq_or_ne (W 0 0) 0 with hp | hp
  · have hq : W 0 1 ≠ 0 := by
      intro h0
      have h := h00
      rw [hp, h0] at h
      simp only [zero_mul, mul_zero, add_zero] at h
      exact hδ h.symm
    have hW10 : W 1 0 ≠ 0 := by
      intro h0
      have h := h00
      rw [hp, h0] at h
      simp only [zero_mul, mul_zero, add_zero] at h
      exact hδ h.symm
    have hMdd : M 0 0 = M 1 1 := by
      have h := hII
      rw [hp] at h
      simp only [zero_mul, mul_zero] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hq)
    refine ⟨M 0 0, M 1 0 / W 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hp, h11]
    · rw [div_mul_eq_mul_div, eq_div_iff hW10]
      linear_combination hI
    · field_simp
    · exact hMdd.symm
  · refine ⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / (2 * W 0 0), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, h11]
    · field_simp
      ring
    · rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero h2 hp)]
      linear_combination -hII
    · rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero h2 hp)]
      linear_combination -hIII
    · field_simp
      ring

/-- `det (a • 1 + b • W) = a ^ 2 - δ * b ^ 2` for a traceless `W` with `W * W = δ • 1`. -/
theorem det_smul_one_add_smul (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (htr : W.trace = 0) (hsq : W * W = δ • 1) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W).det = a ^ 2 - δ * b ^ 2 := by
  have htr' : W 0 0 + W 1 1 = 0 := by
    have h := htr; rw [Matrix.trace_fin_two] at h; exact h
  have h11 : W 1 1 = -W 0 0 := by linear_combination htr'
  have h00 : W 0 0 * W 0 0 + W 0 1 * W 1 0 = δ := by
    have h := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [Matrix.det_fin_two]
  simp [Matrix.add_apply, Matrix.smul_apply, h11]
  linear_combination (-(b * b)) * h00

/-- The product formula `(a • 1 + b • W) * (c • 1 + e • W) = (ac + δbe) • 1 + (ae + bc) • W`. -/
theorem smul_one_add_smul_mul (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (hsq : W * W = δ • 1) (a b c e : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W) * (c • (1 : Matrix (Fin 2) (Fin 2) F) + e • W)
      = (a * c + δ * (b * e)) • (1 : Matrix (Fin 2) (Fin 2) F) + (a * e + b * c) • W := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hsq, smul_smul, add_smul, smul_add]
  module

/-- Elements of `F[W]` commute. -/
theorem smul_one_add_smul_comm (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (hsq : W * W = δ • 1) (a b c e : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W) * (c • (1 : Matrix (Fin 2) (Fin 2) F) + e • W)
      = (c • (1 : Matrix (Fin 2) (Fin 2) F) + e • W) *
        (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W) := by
  rw [smul_one_add_smul_mul F W δ hsq a b c e, smul_one_add_smul_mul F W δ hsq c e a b]
  congr 1
  · ring
  · ring

/-- `(a • 1 + b • W) * W = W * (a • 1 + b • W)`. -/
theorem smul_one_add_smul_mul_W (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (hsq : W * W = δ • 1) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W) * W
      = W * (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hsq, smul_smul]

/-- `conjMat F X` is not a scalar matrix when `disc F X ≠ 0`. -/
theorem conjMat_ne_smul_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (hδ : Work.L2F.Torus.disc F X ≠ 0) (c : F) :
    Work.L2F.Torus.conjMat F X ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have htr := Work.L2F.Torus.conjMat_trace F X
  rw [h] at htr
  simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
  have hc : c = 0 := by
    rcases mul_eq_zero.mp htr with h' | h'
    · exact h'
    · exact absurd h' h2
  rw [hc, zero_smul] at h
  exact Work.L2F.Torus.conjMat_ne_zero F X hδ h

/-- `Z` commutes with `X ∈ SL(2,F)` iff it commutes with `conjMat F X`. -/
theorem commute_conjMat_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (Z : Matrix (Fin 2) (Fin 2) F) :
    Z * Work.L2F.Torus.conjMat F X = Work.L2F.Torus.conjMat F X * Z ↔
      Z * ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Z := by
  have hX : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (2 : F)⁻¹ • Work.L2F.Torus.conjMat F X
        + ((2 : F)⁻¹ * (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)).trace) • (1 : Matrix (Fin 2) (Fin 2) F) :=
    Work.L2F.Torus.x_eq_smul_conjMat F h2 X
  constructor
  · intro h
    rw [hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, h]
  · intro h
    rw [Work.L2F.Torus.conjMat_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, h]

/-- The element `a • 1 + b • W` attached to `(a, b) ∈ hypTorus`. -/
noncomputable def hypToSL (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (htr : W.trace = 0) (hsq : W * W = δ • 1)
    (x : Work.L2F.hypTorus F δ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 •
      (1 : Matrix (Fin 2) (Fin 2) F)
    + ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 • W,
   by
    rw [det_smul_one_add_smul F W δ htr hsq]
    obtain ⟨a, b, hab, hx⟩ :=
      (Work.L2F.Conic.mem_hypTorus F δ (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
    have h1 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by
      rw [hx]; rfl
    have h2 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by
      rw [hx]; rfl
    rw [h1, h2]
    exact hab⟩

/-- `hypToSL` depends on `x` only through the entries `x 0 0`, `x 1 0`. -/
theorem hypToSL_apply (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (htr : W.trace = 0) (hsq : W * W = δ • 1) (x : Work.L2F.hypTorus F δ) :
    ((hypToSL F W δ htr hsq x : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
      = ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 •
          (1 : Matrix (Fin 2) (Fin 2) F)
        + ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 • W :=
  rfl

/-- `hypToSL` is a monoid homomorphism `hypTorus F δ →* SL(2,F)`. -/
noncomputable def hypToSLHom (F : Type*) [Field F] (W : Matrix (Fin 2) (Fin 2) F) (δ : F)
    (htr : W.trace = 0) (hsq : W * W = δ • 1) :
    Work.L2F.hypTorus F δ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := hypToSL F W δ htr hsq
  map_one' := by
    apply Subtype.ext
    rw [hypToSL_apply]
    have h1 : ((1 : Work.L2F.hypTorus F δ) : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := rfl
    rw [h1, Matrix.SpecialLinearGroup.coe_one]
    simp
  map_mul' := by
    intro x y
    obtain ⟨a, b, hab, hx⟩ :=
      (Work.L2F.Conic.mem_hypTorus F δ (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
    obtain ⟨c, e, hce, hy⟩ :=
      (Work.L2F.Conic.mem_hypTorus F δ (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
    have hx00 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by
      rw [hx]; rfl
    have hx10 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by
      rw [hx]; rfl
    have hy00 : ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
      rw [hy]; rfl
    have hy10 : ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = e := by
      rw [hy]; rfl
    have hxy : (((x * y : Work.L2F.hypTorus F δ) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
        = Work.L2F.Mat2.quadMat δ (a * c + δ * (b * e)) (a * e + b * c) := by
      rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rw [show ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            = Work.L2F.Mat2.quadMat δ a b from hx,
          show ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            = Work.L2F.Mat2.quadMat δ c e from hy]
      rw [Work.L2F.Mat2.quadMat_mul]
    have hxy00 : (((x * y : Work.L2F.hypTorus F δ) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = a * c + δ * (b * e) := by
      rw [hxy]; rfl
    have hxy10 : (((x * y : Work.L2F.hypTorus F δ) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = a * e + b * c := by
      rw [hxy]; rfl
    change hypToSL F W δ htr hsq (x * y)
      = hypToSL F W δ htr hsq x * hypToSL F W δ htr hsq y
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hypToSL_apply, hypToSL_apply, hypToSL_apply,
      hxy00, hxy10, hx00, hx10, hy00, hy10, smul_one_add_smul_mul F W δ hsq]

/-- `hypToSLHom` is injective. -/
theorem hypToSLHom_injective (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (W : Matrix (Fin 2) (Fin 2) F) (δ : F) (htr : W.trace = 0) (hsq : W * W = δ • 1)
    (hδ : δ ≠ 0) (hWns : ∀ c : F, W ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    Function.Injective (hypToSLHom F W δ htr hsq) := by
  intro x y hxy
  change hypToSL F W δ htr hsq x = hypToSL F W δ htr hsq y at hxy
  obtain ⟨a, b, -, hx⟩ :=
    (Work.L2F.Conic.mem_hypTorus F δ (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
  obtain ⟨c, e, -, hy⟩ :=
    (Work.L2F.Conic.mem_hypTorus F δ (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
  have hx00 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = a := by
    rw [hx]; rfl
  have hx10 : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = b := by
    rw [hx]; rfl
  have hy00 : ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = c := by
    rw [hy]; rfl
  have hy10 : ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = e := by
    rw [hy]; rfl
  have hmat : ((hypToSL F W δ htr hsq x : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)
      = ((hypToSL F W δ htr hsq y : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => ((z : Matrix.SpecialLinearGroup
      (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hxy
  rw [hypToSL_apply, hypToSL_apply, hx00, hx10, hy00, hy10] at hmat
  have hzero : (a - c) • (1 : Matrix (Fin 2) (Fin 2) F) + (b - e) • W = 0 := by
    have key : (a - c) • (1 : Matrix (Fin 2) (Fin 2) F) + (b - e) • W
        = (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • W)
          - (c • (1 : Matrix (Fin 2) (Fin 2) F) + e • W) := by
      rw [sub_smul, sub_smul]; abel
    rw [key, sub_eq_zero.mpr hmat]
  obtain ⟨hac, hbe⟩ := Work.L2F.Torus.algSpan_eq_zero F hWns (a - c) (b - e) hzero
  have hae : a = c := sub_eq_zero.mp hac
  have hbe' : b = e := sub_eq_zero.mp hbe
  exact Subtype.ext (Subtype.ext (by rw [hx, hy, hae, hbe']))

/-- Membership in the centralizer of `X ∈ SL(2,F)` is commuting with `conjMat F X`. -/
theorem mem_centralizer_iff_commute_conjMat (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X Z : Matrix.SpecialLinearGroup (Fin 2) F) :
    Z ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ↔
      ((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X =
        Work.L2F.Torus.conjMat F X *
          ((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h' : X * Z = Z * X := h X (Set.mem_singleton X)
    have h'' : ((X * Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((Z * X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [h']
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h''
    exact (commute_conjMat_iff F h2 X ((Z : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).mpr h''.symm
  · intro h
    intro Y hY
    rw [Set.mem_singleton_iff] at hY
    rw [hY]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact ((commute_conjMat_iff F h2 X ((Z : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).mp h).symm

/-- The range of `hypToSLHom` is the centralizer of `X` (with `W = conjMat F X`). -/
theorem hypToSLHom_range (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (hδ : Work.L2F.Torus.disc F X ≠ 0) :
    (hypToSLHom F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
        (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X)).range
      = Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    change hypToSL F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
      (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X) x
      ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))
    rw [mem_centralizer_iff_commute_conjMat F h2 X]
    rw [hypToSL_apply]
    exact smul_one_add_smul_mul_W F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
      (Work.L2F.Torus.conjMat_mul_self F X) _ _
  · intro g hg
    have hcomm : ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X =
        Work.L2F.Torus.conjMat F X *
          ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
      (mem_centralizer_iff_commute_conjMat F h2 X g).mp hg
    obtain ⟨a, b, hab⟩ := commutant_algSpan F h2 (Work.L2F.Torus.conjMat F X)
      (Work.L2F.Torus.disc F X) (Work.L2F.Torus.conjMat_trace F X)
      (Work.L2F.Torus.conjMat_mul_self F X) hδ _ hcomm
    have hdet : a ^ 2 - Work.L2F.Torus.disc F X * b ^ 2 = 1 := by
      have h1 := det_smul_one_add_smul F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
        (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X) a b
      have h2 := Matrix.SpecialLinearGroup.det_coe g
      rw [hab] at h2
      rw [h1] at h2
      exact h2
    have hmem : (⟨Work.L2F.Mat2.quadMat (Work.L2F.Torus.disc F X) a b, by
        rw [Work.L2F.Mat2.quadMat_det]; exact hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F)
        ∈ Work.L2F.hypTorus F (Work.L2F.Torus.disc F X) :=
      (Work.L2F.Conic.mem_hypTorus F (Work.L2F.Torus.disc F X) _).mpr ⟨a, b, hdet, rfl⟩
    have hyval : hypToSL F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
        (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X)
        ⟨⟨Work.L2F.Mat2.quadMat (Work.L2F.Torus.disc F X) a b, by
          rw [Work.L2F.Mat2.quadMat_det]; exact hdet⟩, hmem⟩ = g := by
      apply Subtype.ext
      rw [hypToSL_apply]
      change a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Work.L2F.Torus.conjMat F X
        = ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      rw [hab]
    exact ⟨⟨⟨Work.L2F.Mat2.quadMat (Work.L2F.Torus.disc F X) a b, by
      rw [Work.L2F.Mat2.quadMat_det]; exact hdet⟩, hmem⟩, hyval⟩

/-- For a nonzero square `δ = c ^ 2` in a finite field of odd characteristic, `hypTorus F δ` has
`Nat.card F - 1` elements. -/
theorem hypTorus_card_of_sq (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (δ c : F) (hc : c ≠ 0) (hc2 : c * c = δ) :
    Nat.card (Work.L2F.hypTorus F δ) = Nat.card F - 1 := by
  classical
  have hρ : c * c = RingHom.id F δ := by rw [RingHom.id_apply]; exact hc2
  let φ : Work.L2F.hypTorus F δ →* F := Work.L2F.Conic.hypHom δ (RingHom.id F) c hρ
  have hinj : Function.Injective φ := Work.L2F.Conic.hypHom_id_injective δ c hρ hc h2
  have hval : ∀ x : Work.L2F.hypTorus F δ,
      φ x = ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0
        + ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 * c :=
    fun x => rfl
  let ψ : Work.L2F.hypTorus F δ → Fˣ := fun x =>
    Units.mk0 (φ x) (by
      obtain ⟨a, b, hab, hx⟩ :=
        (Work.L2F.Conic.mem_hypTorus F δ (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
      have hv : φ x = a + b * c := by
        rw [hval, hx]
        simp [Work.L2F.Mat2.quadMat]
      rw [hv]
      intro h0
      have h1 : (a + b * c) * (a - b * c) = 1 := by
        have h3 : (a + b * c) * (a - b * c) = a ^ 2 - δ * b ^ 2 := by
          rw [← hc2]; ring
        rw [h3, hab]
      rw [h0, zero_mul] at h1
      exact one_ne_zero h1.symm)
  have hψinj : Function.Injective ψ := fun x y hxy =>
    hinj (by
      have h := congrArg (fun u : Fˣ => (u : F)) hxy
      simpa [ψ] using h)
  have hψsurj : Function.Surjective ψ := by
    intro u
    refine ⟨⟨⟨Work.L2F.Mat2.quadMat δ (((u : F) + (u : F)⁻¹) / 2)
        (((u : F) - (u : F)⁻¹) / (2 * c)), ?det⟩, ?mem⟩, ?eq⟩
    · rw [Work.L2F.Mat2.quadMat_det]
      rw [show δ = c * c from hc2.symm]
      field_simp
      ring
    · refine (Work.L2F.Conic.mem_hypTorus F δ _).mpr ⟨_, _, ?_, rfl⟩
      rw [show δ = c * c from hc2.symm]
      field_simp
      ring
    · apply Units.ext
      simp only [ψ, Units.val_mk0]
      rw [hval]
      simp only [Work.L2F.Mat2.quadMat, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.of_apply]
      field_simp
      ring
  have hcard : Nat.card (Work.L2F.hypTorus F δ) = Nat.card Fˣ :=
    Nat.card_congr (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]

/-- The centralizer in `SL(2,F)` of a semisimple element is cyclic, of order `q ± 1`. -/
theorem centralizer_isCyclic_and_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) (hδ : Work.L2F.Torus.disc F X ≠ 0) :
    IsCyclic (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) ∧
      (Nat.card (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
          = Nat.card F - 1 ∨
       Nat.card (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
          = Nat.card F + 1) := by
  classical
  have hWns : ∀ c : F, Work.L2F.Torus.conjMat F X ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) :=
    conjMat_ne_smul_one F h2 X hδ
  have hinj : Function.Injective (hypToSLHom F (Work.L2F.Torus.conjMat F X)
      (Work.L2F.Torus.disc F X) (Work.L2F.Torus.conjMat_trace F X)
      (Work.L2F.Torus.conjMat_mul_self F X)) :=
    hypToSLHom_injective F h2 _ _ _ _ hδ hWns
  have hrange : (hypToSLHom F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
      (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X)).range
      = Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    hypToSLHom_range F h2 X hδ
  have hcard : Nat.card (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      = Nat.card (Work.L2F.hypTorus F (Work.L2F.Torus.disc F X)) := by
    rw [← hrange, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (K := (⊤ : Subgroup (Work.L2F.hypTorus F
        (Work.L2F.Torus.disc F X)))) hinj]
    exact Nat.card_congr (Subgroup.topEquiv (G := Work.L2F.hypTorus F
      (Work.L2F.Torus.disc F X))).toEquiv
  refine ⟨?_, ?_⟩
  · rw [← hrange]
    exact isCyclic_of_surjective (hH := Work.L2F.Conic.hypTorus_cyclic F h2 _ hδ)
      (hypToSLHom F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
        (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X)).rangeRestrict
      (hypToSLHom F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
        (Work.L2F.Torus.conjMat_trace F X)
        (Work.L2F.Torus.conjMat_mul_self F X)).rangeRestrict_surjective
  · rcases Classical.em (∃ c : F, c * c = Work.L2F.Torus.disc F X) with ⟨c, hc⟩ | hns
    · left
      rw [hcard]
      exact hypTorus_card_of_sq F h2 _ c (by rintro rfl; rw [mul_zero] at hc; exact hδ hc.symm) hc
    · right
      rw [hcard]
      exact Work.L2F.Conic.hypTorus_card F h2 _ hδ (fun a ha => hns ⟨a, ha⟩)

/-- `tr (A * B * A⁻¹) = tr B` for `A ∈ SL(2,F)`. -/
theorem trace_conj_SL (F : Type*) [Field F] (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((A * B * A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F).trace
      = ((B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle]
  rw [show (((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        ((A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 from by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]]
  rw [Matrix.one_mul]

theorem algSpan_neg {W : Matrix (Fin 2) (Fin 2) F} {M : Matrix (Fin 2) (Fin 2) F}
    (hM : M ∈ Work.L2F.Torus.algSpan F W) : -M ∈ Work.L2F.Torus.algSpan F W := by
  simpa only [neg_one_smul] using Work.L2F.Torus.algSpan_smul F hM (-1)

theorem algSpan_sub {W : Matrix (Fin 2) (Fin 2) F} {M N : Matrix (Fin 2) (Fin 2) F}
    (hM : M ∈ Work.L2F.Torus.algSpan F W) (hN : N ∈ Work.L2F.Torus.algSpan F W) :
    M - N ∈ Work.L2F.Torus.algSpan F W := by
  have h := Work.L2F.Torus.algSpan_add F hM (algSpan_neg hN)
  simpa only [sub_eq_add_neg] using h

/-- The normalizer in `SL(2,F)` of the centralizer of a semisimple element: any `Y` normalizing
`C_{SL}(X)` either centralizes `X` or equals `t * w` for some `t ∈ C_{SL}(X)`, where `w` is an
element with `w * w = -1` anticommuting with `conjMat F X`. -/
theorem mem_normalizer_centralizer (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hδ : Work.L2F.Torus.disc F X ≠ 0) (w : Matrix.SpecialLinearGroup (Fin 2) F)
    (hw2 : w * w = Work.L2F.negOne F)
    (haw : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              Work.L2F.Torus.conjMat F X
            = -(Work.L2F.Torus.conjMat F X *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)))
    (Y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hY : Y ∈ Subgroup.normalizer
      (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) :
    Y ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ∃ t ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)), Y = t * w := by
  classical
  have hWns := conjMat_ne_smul_one F h2 X hδ
  have htr := Work.L2F.Torus.conjMat_trace F X
  have hsq := Work.L2F.Torus.conjMat_mul_self F X
  have hnegT : Work.L2F.negOne F ∈
      Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [mem_centralizer_iff_commute_conjMat F h2 X]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [neg_mul, one_mul, mul_neg, mul_one]
  -- Step 1: an element of the centralizer of the form `a•1 + b•W` with `b ≠ 0`.
  have hex : ∃ Z ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)),
      ∃ a b : F, ((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Work.L2F.Torus.conjMat F X ∧ b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
        Subgroup.zpowers (Work.L2F.negOne F) := by
      intro Z hZ
      have hZW := (mem_centralizer_iff_commute_conjMat F h2 X Z).mp hZ
      obtain ⟨a, b, hab⟩ := commutant_algSpan F h2 _ _ htr hsq hδ _ hZW
      have hb0 := hcon Z hZ a b hab
      have hZeq : ((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hab, hb0, zero_smul, add_zero]
      have hdet : a ^ 2 = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe Z
        rw [hZeq] at h
        rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
        exact h
      rcases mul_self_eq_one_iff.mp (by rwa [pow_two] at hdet) with h1 | h1
      · rw [h1] at hZeq
        have hZ1 : Z = 1 := Subtype.ext (by rw [hZeq]; simp)
        rw [hZ1]; exact Subgroup.one_mem _
      · rw [h1] at hZeq
        have hZ1 : Z = Work.L2F.negOne F := by
          apply Subtype.ext
          rw [hZeq]
          change (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)
            = ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F)
          rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
          simp
        rw [hZ1]; exact Subgroup.mem_zpowers _
    have hcard2 : Nat.card (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
        ≤ 2 := by
      have h1 := Nat.card_le_card_of_injective
        (fun z : ↥(Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =>
          (Subgroup.inclusion hle z : ↥(Subgroup.zpowers (Work.L2F.negOne F))))
        (fun x y hxy => Subtype.ext (congrArg
          (fun z : ↥(Subgroup.zpowers (Work.L2F.negOne F)) =>
            (z : Matrix.SpecialLinearGroup (Fin 2) F)) hxy))
      have h2' : Nat.card (Subgroup.zpowers (Work.L2F.negOne F)) = 2 := by
        rw [Nat.card_zpowers]
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two]
          exact Work.L2F.Involution.negOne_mul_self F
        · intro h
          have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
            ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h
          simp [Work.L2F.negOne] at h'
          exact h2 (by linear_combination -h')
      omega
    rcases (centralizer_isCyclic_and_card F h2 X hδ).2 with h | h <;> omega
  obtain ⟨Z, hZT, a, b, hZab, hb⟩ := hex
  -- Step 2: `Y W Y⁻¹ ∈ F[W]`.
  have hYZY : Y * Z * Y⁻¹ ∈
      Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
    (Subgroup.mem_normalizer_iff.mp hY Z).mp hZT
  have hYZYW := (mem_centralizer_iff_commute_conjMat F h2 X (Y * Z * Y⁻¹)).mp hYZY
  obtain ⟨a', b', hab'⟩ := commutant_algSpan F h2 _ _ htr hsq hδ _ hYZYW
  have hWdec : Work.L2F.Torus.conjMat F X
      = b⁻¹ • (((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          - a • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    rw [hZab, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hYZYm : (((Y * Z * Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F)
      = ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hYYinv : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hYinvY : (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
      ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hPA : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      ∈ Work.L2F.Torus.algSpan F (Work.L2F.Torus.conjMat F X) := by
    have hPeq : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        = b⁻¹ • ((((Y * Z * Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix (Fin 2) (Fin 2) F)
            - a • (1 : Matrix (Fin 2) (Fin 2) F)) := by
      rw [hWdec, hYZYm, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [show ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
              a • (1 : Matrix (Fin 2) (Fin 2) F)) *
            (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
          = ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (((Z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
              (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
            - a • (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
                Matrix (Fin 2) (Fin 2) F)) from by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]]
      rw [hYYinv]
    rw [hPeq]
    exact Work.L2F.Torus.algSpan_smul F
      (algSpan_sub (M := ((Y * Z * Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)) ⟨a', b', hab'⟩
        (Work.L2F.Torus.algSpan_smul F
          (Work.L2F.Torus.algSpan_one F (Work.L2F.Torus.conjMat F X)) a)) b⁻¹
  obtain ⟨a₁, b₁, hab₁⟩ := hPA
  -- Step 3: `P * P = δ • 1`.
  have hP2 : (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
      (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))
      = Work.L2F.Torus.disc F X • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [show ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))
        = ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (Work.L2F.Torus.conjMat F X * Work.L2F.Torus.conjMat F X) *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) from by
      rw [show ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
          (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))
          = ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            Work.L2F.Torus.conjMat F X * ((((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix (Fin 2) (Fin 2) F) * ((Y : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)) * Work.L2F.Torus.conjMat F X *
            (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
            from by noncomm_ring]
      rw [hYinvY, Matrix.mul_one]
      noncomm_ring]
    rw [hsq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hYYinv]
  have hsq₁ : (a₁ • (1 : Matrix (Fin 2) (Fin 2) F) + b₁ • Work.L2F.Torus.conjMat F X) *
      (a₁ • (1 : Matrix (Fin 2) (Fin 2) F) + b₁ • Work.L2F.Torus.conjMat F X)
      = Work.L2F.Torus.disc F X • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← hab₁]; exact hP2
  rw [smul_one_add_smul_mul F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X) hsq a₁ b₁]
    at hsq₁
  have hzero : (a₁ * a₁ + Work.L2F.Torus.disc F X * (b₁ * b₁) - Work.L2F.Torus.disc F X) •
        (1 : Matrix (Fin 2) (Fin 2) F) + (a₁ * b₁ + b₁ * a₁) • Work.L2F.Torus.conjMat F X = 0 := by
    have h : (a₁ * a₁ + Work.L2F.Torus.disc F X * (b₁ * b₁)) •
          (1 : Matrix (Fin 2) (Fin 2) F) + (a₁ * b₁ + b₁ * a₁) • Work.L2F.Torus.conjMat F X
        = Work.L2F.Torus.disc F X • (1 : Matrix (Fin 2) (Fin 2) F) := hsq₁
    rw [sub_smul, ← h]
    abel
  obtain ⟨h1, h2'⟩ := Work.L2F.Torus.algSpan_eq_zero F hWns _ _ hzero
  have hab1 : a₁ * b₁ = 0 := by
    have h : (2 : F) * (a₁ * b₁) = 0 := by linear_combination h2'
    exact (mul_eq_zero.mp h).resolve_left h2
  rcases eq_or_ne b₁ 0 with hb₁ | hb₁
  · exfalso
    have hPW : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        = a₁ • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hab₁, hb₁, zero_smul, add_zero]
    refine hWns a₁ ?_
    have hconj : (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
        ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = Work.L2F.Torus.conjMat F X := by
      rw [show (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
          (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
          ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = ((((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
            Work.L2F.Torus.conjMat F X *
            ((((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
            from by noncomm_ring]
      rw [hYinvY, Matrix.one_mul, Matrix.mul_one]
    have hconj2 : (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *
        (a₁ • (1 : Matrix (Fin 2) (Fin 2) F)) *
        ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = a₁ • (1 : Matrix (Fin 2) (Fin 2) F) := by
      simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hYinvY]
    rw [← hconj, hPW, hconj2]
  · have ha1 : a₁ = 0 := (mul_eq_zero.mp hab1).resolve_right hb₁
    have hb1sq : b₁ * b₁ = 1 := by
      rw [ha1] at h1
      have h := h1
      simp only [zero_mul, zero_add, sub_eq_zero] at h
      exact mul_left_cancel₀ hδ (by rw [h, mul_one])
    rcases mul_self_eq_one_iff.mp hb1sq with hb1 | hb1
    · left
      rw [mem_centralizer_iff_commute_conjMat F h2 X Y]
      rw [show ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X
          = (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            Work.L2F.Torus.conjMat F X *
            (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) *
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from by
        rw [Matrix.mul_assoc, hYinvY, Matrix.mul_one]]
      rw [hab₁, ha1, hb1]; simp
    · right
      have hPY : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X *
          (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
          = -Work.L2F.Torus.conjMat F X := by
        rw [hab₁, ha1, hb1]; simp
      have hcommY : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          Work.L2F.Torus.conjMat F X
          = -(Work.L2F.Torus.conjMat F X *
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
        have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
          M * ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hPY
        rw [Matrix.mul_assoc (((Y : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F X)
            (((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
          hYinvY, Matrix.mul_one, neg_mul] at h
        exact h
      have hYwT : Y * w ∈
          Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
        rw [mem_centralizer_iff_commute_conjMat F h2 X (Y * w),
          Matrix.SpecialLinearGroup.coe_mul]
        rw [show (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
              Work.L2F.Torus.conjMat F X
            = Work.L2F.Torus.conjMat F X *
              (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) from by
          rw [show (((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
                Work.L2F.Torus.conjMat F X
              = ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                Work.L2F.Torus.conjMat F X) from by noncomm_ring]
          rw [haw]
          rw [show ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                -(Work.L2F.Torus.conjMat F X *
                  ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
              = -(((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                Work.L2F.Torus.conjMat F X *
                ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
              from by noncomm_ring]
          rw [hcommY]
          noncomm_ring]
      refine ⟨Work.L2F.negOne F * (Y * w), Subgroup.mul_mem _ hnegT hYwT, ?_⟩
      rw [show Work.L2F.negOne F * (Y * w) * w = Y from by
        rw [mul_assoc (Work.L2F.negOne F) (Y * w) w, mul_assoc Y w w, hw2]
        rw [show Work.L2F.negOne F * (Y * Work.L2F.negOne F)
            = Y * (Work.L2F.negOne F * Work.L2F.negOne F) from by
          rw [← mul_assoc, ← mul_assoc, Work.L2F.Involution.negOne_mul_comm F Y]]
        rw [Work.L2F.Involution.negOne_mul_self F, mul_one]]

/-- For `X ∈ SL(2,F)` with `tr X ≠ 0`, the centralizer of `π(X)` in `PSL(2,F)` is the image of the
centralizer of `X`. -/
theorem centralizer_psl_eq_map (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (htr : (((X : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F).trace
      ≠ 0) :
    Subgroup.centralizer ({Work.PSL2.pslMap F X} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) =
      (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
        (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨Y, hY⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
    have hg' : ∀ h ∈ ({Work.PSL2.pslMap F X} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)), h * g = g * h :=
      Subgroup.mem_centralizer_iff.mp hg
    have h2' : Work.PSL2.pslMap F Y * Work.PSL2.pslMap F X
        = Work.PSL2.pslMap F X * Work.PSL2.pslMap F Y := by
      have hthis : Work.PSL2.pslMap F X * g = g * Work.PSL2.pslMap F X :=
        hg' (Work.PSL2.pslMap F X) (Set.mem_singleton _)
      rw [← hY] at hthis
      exact hthis.symm
    have h1 : Work.PSL2.pslMap F (Y * X * Y⁻¹ * X⁻¹) = 1 := by
      have hsplit : Work.PSL2.pslMap F (Y * X * Y⁻¹ * X⁻¹)
          = Work.PSL2.pslMap F Y * Work.PSL2.pslMap F X * (Work.PSL2.pslMap F Y)⁻¹ *
            (Work.PSL2.pslMap F X)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [hsplit, h2']
      group
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Y * X * Y⁻¹ * X⁻¹)).mp h1 with h | h
    · refine Subgroup.mem_map.mpr ⟨Y, ?_, hY⟩
      rw [mem_centralizer_iff_commute_conjMat F h2 X Y]
      have h3 : Y * X * Y⁻¹ = X := mul_inv_eq_one.mp h
      have hYX : ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        have h3' : Y * X = X * Y := mul_inv_eq_iff_eq_mul.mp h3
        exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
          ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h3'
      simp only [Work.L2F.Torus.conjMat_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, hYX]
    · exfalso
      have h3 : Y * X * Y⁻¹ = Work.L2F.negOne F * X := mul_inv_eq_iff_eq_mul.mp h
      have ht1 : (((Y * X * Y⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F).trace
          = ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace :=
        trace_conj_SL F Y X
      rw [h3] at ht1
      have h5 : (((Work.L2F.negOne F * X : Matrix.SpecialLinearGroup (Fin 2) F)) :
          Matrix (Fin 2) (Fin 2) F).trace
          = -((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
        rw [Matrix.SpecialLinearGroup.coe_mul,
          show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
        rw [neg_mul, one_mul, Matrix.trace_neg]
      rw [h5] at ht1
      have hh : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
          + ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
        linear_combination -ht1
      exact htr (by
        have hh' : (2 : F) * ((X : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).trace = 0 := by linear_combination hh
        exact (mul_eq_zero.mp hh').resolve_left h2)
  · rintro g ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, ← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_centralizer_iff.mp hy) X (Set.mem_singleton X)

/-- `(1 + N) ^ n = 1 + (n : F) • N` when `N * N = 0`. -/
theorem pow_one_add_nilpotent (F : Type*) [Field F] (N : Matrix (Fin 2) (Fin 2) F)
    (hN : N * N = 0) (n : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) F) + N) ^ n
      = 1 + (n : F) • N := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.mul_one, hN, add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

/-- `1 ≠ -1` in `SL(2,F)` for a field of characteristic `≠ 2`. -/
theorem one_ne_negOne (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    (1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ Work.L2F.negOne F := by
  intro h
  have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
    ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Work.L2F.negOne] at h'
  exact h2 (by linear_combination h')

/-- An odd power of `-1` (in `SL(2,F)`) is `-1`. -/
theorem negOne_pow_odd (F : Type*) [Field F] {n : ℕ} (hn : Odd n) :
    Work.L2F.negOne F ^ n = Work.L2F.negOne F := by
  obtain ⟨k, hk⟩ := hn
  rw [hk, pow_succ, pow_mul, Work.L2F.Involution.negOne_pow_two, one_pow, one_mul]

/-- If `c` centralizes `x` then `c` commutes with every element of `⟨x⟩`. -/
theorem zpowers_mem_centralizer {G : Type*} [Group G] {c x w : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) (hw : w ∈ Subgroup.zpowers x) :
    c * w = w * c := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hn]
  exact Commute.zpow_right (show Commute c x from
    ((Subgroup.mem_centralizer_iff.mp hc) x (Set.mem_singleton x)).symm) n

/-- The normalizer of `⟨x⟩` is contained in the normalizer of `C(x)`. -/
theorem normalizer_zpowers_le_normalizer_centralizer {G : Type*} [Group G] (x : G) :
    Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  intro g hg
  have hginv : g⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    Subgroup.inv_mem _ hg
  rw [Subgroup.mem_normalizer_iff] at hg hginv ⊢
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcomm := zpowers_mem_centralizer hc ((hginv x).mp (Subgroup.mem_zpowers x))
    simp only [inv_inv] at hcomm
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * c * g⁻¹) * x := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hcomm := zpowers_mem_centralizer hc ((hg x).mp (Subgroup.mem_zpowers x))
    have key : c * x = x * c := by
      calc c * x = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by rw [hcomm]
        _ = x * c := by group
    exact key.symm

/-- For a traceless `2×2` matrix `W` over a finite field of odd characteristic with
`W * W = δ • 1` and `δ ≠ 0`, there is `w ∈ SL(2,F)` with `w * w = -1` anticommuting with `W`. -/
theorem existsAnticommuting (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (W : Matrix (Fin 2) (Fin 2) F) (δ : F) (htr : W.trace = 0) (hsq : W * W = δ • 1)
    (hδ : δ ≠ 0) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * w = Work.L2F.negOne F ∧
      ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * W =
        -(W * ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
  classical
  have htr' : W 0 0 + W 1 1 = 0 := by
    have h := htr; rw [Matrix.trace_fin_two] at h; exact h
  have h11 : W 1 1 = -W 0 0 := by linear_combination htr'
  have h00 : W 0 0 * W 0 0 + W 0 1 * W 1 0 = δ := by
    have h := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have key : ∀ u v s : F, 2 * W 0 0 * u + v * W 1 0 + W 0 1 * s = 0 →
      u * u + v * s = -1 →
      ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * w = Work.L2F.negOne F ∧
        ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * W =
          -(W * ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
    intro u v s hlin hcon
    have hdet : (!![u, v; s, -u] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Matrix.det_fin_two_of]; linear_combination -hcon
    refine ⟨⟨!![u, v; s, -u], hdet⟩, ?_, ?_⟩
    · apply Subtype.ext
      change (!![u, v; s, -u] : Matrix (Fin 2) (Fin 2) F) * !![u, v; s, -u]
        = ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)
      rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp <;>
        first | linear_combination hcon | ring
    · change (!![u, v; s, -u] : Matrix (Fin 2) (Fin 2) F) * W = -(W * !![u, v; s, -u])
      rw [show W = !![W 0 0, W 0 1; W 1 0, W 1 1] from by
        ext i j; fin_cases i <;> fin_cases j <;> rfl, h11]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp <;>
        first | linear_combination hlin | ring
  rcases eq_or_ne (W 0 1) 0 with hq0 | hq0
  · have hp0 : W 0 0 ≠ 0 := by
      intro h; rw [h, hq0] at h00; simp at h00; exact hδ h00.symm
    have h4 : (4 : F) ≠ 0 := by
      have hh : (4 : F) = 2 * 2 := by norm_num
      rw [hh]; exact mul_ne_zero h2 h2
    refine key (-(W 1 0) / (2 * W 0 0)) 1 (-(4 * (W 0 0) ^ 2 + (W 1 0) ^ 2) / (4 * (W 0 0) ^ 2))
      ?_ ?_
    · rw [hq0]; field_simp; ring
    · field_simp; ring
  · obtain ⟨X, Y, hXY⟩ := Work.L2F.Conic.exists_sq_sub_mul_sq F h2 δ hδ (-(W 0 1 * W 0 1))
    refine key ((X + W 0 0 * Y) / W 0 1) Y
      (-(2 * W 0 0 * ((X + W 0 0 * Y) / W 0 1) + Y * W 1 0) / W 0 1) ?_ ?_
    · field_simp; ring
    · have hδ' : δ = W 0 0 * W 0 0 + W 0 1 * W 1 0 := h00.symm
      field_simp
      linear_combination hXY + (Y ^ 2) * hδ'

/-- The centralizer of an element of prime order `r ≠ 2`, `r ≠ p` in `PSL(2,F)` is a cyclic torus of
order `(q±1)/2`, and the normalizer of the subgroup `⟨x⟩` is dihedral of order `q±1`.
Proof: `x` of order `r` lifts to `SL(2,F)`; since `r ≠ p` the element is semisimple, with
eigenvalues `λ, λ⁻¹` in `F` or in `F_{q²}`, so it lies in a (split or non-split) torus, which is its
own centralizer in `SL`; the image is cyclic of order `(q±1)/2` in `PSL`, and normalizing `⟨x⟩`
normalizes `C(x)`, so the normalizer of `⟨x⟩` is that of the torus, a dihedral group of order
`q±1 = 2 * |C(x)|`.  (Note `Subgroup.normalizer ({x} : Set _)` would be the *centralizer*; the
normalizer of the generated subgroup is meant.) -/
theorem primeOrderCentralizer (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (p r : ℕ) [Fact p.Prime] [Fact r.Prime] (hchar : CharP F p) (hr2 : r ≠ 2)
    (hrp : r ≠ p) (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hx : orderOf x = r) :
    let C := Subgroup.centralizer ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    let N := Subgroup.normalizer ((Subgroup.zpowers x : Subgroup _) :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    IsCyclic C ∧ (2 * Nat.card C = Nat.card F + 1 ∨ 2 * Nat.card C = Nat.card F - 1) ∧
      Nonempty (N ≃* DihedralGroup (Nat.card C)) := by
  classical
  obtain ⟨X, hX⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) x
  have hX' : Work.PSL2.pslMap F X = x := hX
  have hrod : Odd r := (Fact.out : Nat.Prime r).odd_of_ne_two hr2
  have hr0 : (r : F) ≠ 0 := by
    intro h
    have hdiv : p ∣ r := (CharP.cast_eq_zero_iff F p r).mp h
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime r)).mp hdiv with h1 | h1
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hrp h1.symm
  have h2r0 : (↑(2 * r) : F) ≠ 0 := by
    rw [Nat.cast_mul]; exact mul_ne_zero h2 hr0
  have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hXr : X ^ r = 1 ∨ X ^ r = Work.L2F.negOne F := by
    have h : Work.PSL2.pslMap F (X ^ r) = 1 := by rw [map_pow, hX', hxr]
    exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (X ^ r)).mp h
  have hX2r : X ^ (2 * r) = 1 := by
    rw [mul_comm 2 r, pow_mul]
    rcases hXr with h | h
    · rw [h, one_pow]
    · rw [h, Work.L2F.Involution.negOne_pow_two]
  have hne1 : (1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ Work.L2F.negOne F :=
    one_ne_negOne F h2
  -- trace of the lift is nonzero
  have htrX : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
    intro htr0
    have hsq : X ^ 2 = Work.L2F.negOne F := by
      apply Subtype.ext
      rw [pow_two]
      change ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)
      rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
      have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F
        (((X : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      rw [htr0, Matrix.SpecialLinearGroup.det_coe] at h
      rw [h]; simp
    have hpow : X ^ (2 * r) = Work.L2F.negOne F := by
      rw [pow_mul, hsq]; exact negOne_pow_odd F hrod
    rw [hpow] at hX2r
    exact hne1 hX2r.symm
  -- discriminant of the lift is nonzero
  have hdiscX : Work.L2F.Torus.disc F X ≠ 0 := by
    intro hdisc0
    have htr2 : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace
        = 2 ∨ ((X : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).trace = -2 := by
      have h := hdisc0
      rw [Work.L2F.Torus.disc_apply] at h
      have hf : (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace - 2) *
          (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace + 2)
          = 0 := by linear_combination h
      rcases mul_eq_zero.mp hf with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    have hmatpow : (((X : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) ^ (2 * r) = 1 := by
      have h := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
        ((z : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) hX2r
      simpa using h
    have hx1 : x = 1 := by
      rcases htr2 with htr | htr
      · have hN2 : (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) - 1) *
            (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
          have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F
            (((X : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
          rw [htr, Matrix.SpecialLinearGroup.det_coe] at h
          rw [show (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) - 1) *
              (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1)
              = ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                - 2 • ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                + 1 from by noncomm_ring, h]
          module
        have hXm : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            = 1 + (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) - 1) := by abel
        rw [hXm, pow_one_add_nilpotent F _ hN2 (2 * r)] at hmatpow
        have hz : (↑(2 * r) : F) • (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
          have h := sub_eq_zero.mpr hmatpow
          simpa only [add_sub_cancel_left] using h
        have hN0 : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 = 0 :=
          (smul_eq_zero.mp hz).resolve_left h2r0
        have hXeq : X = 1 := by
          apply Subtype.ext
          rw [Matrix.SpecialLinearGroup.coe_one]
          exact sub_eq_zero.mp hN0
        rw [← hX', hXeq, map_one]
      · have hM2 : (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) + 1) *
            (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) + 1) = 0 := by
          have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F
            (((X : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
          rw [htr, Matrix.SpecialLinearGroup.det_coe] at h
          rw [show (((X : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) + 1) *
              (((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) + 1)
              = ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                + 2 • ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                + 1 from by noncomm_ring, h]
          module
        have hN2 : (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) + 1)) *
            (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) + 1)) = 0 := by
          rw [neg_mul_neg]; exact hM2
        have hXm : ((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            = -(1 + (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) + 1))) := by abel
        have hneg : (-(1 + (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) + 1)))) ^ (2 * r)
            = (1 + (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) + 1))) ^ (2 * r) := by
          rw [neg_pow, pow_mul, pow_two, neg_mul_neg, mul_one, one_pow, one_mul]
        rw [hXm, hneg, pow_one_add_nilpotent F _ hN2 (2 * r)] at hmatpow
        have hz : (↑(2 * r) : F) • (-(((X : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) + 1)) = 0 := by
          have h := sub_eq_zero.mpr hmatpow
          simpa only [add_sub_cancel_left] using h
        have hN0 : -(((X : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) + 1) = 0 :=
          (smul_eq_zero.mp hz).resolve_left h2r0
        have hXeq : X = Work.L2F.negOne F := by
          apply Subtype.ext
          rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
          exact add_eq_zero_iff_eq_neg.mp (neg_eq_zero.mp hN0)
        rw [← hX', hXeq]
        exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
    rw [hx1, orderOf_one] at hx
    exact (Fact.out : Nat.Prime r).ne_one hx.symm
  obtain ⟨w, hw2, haw⟩ := existsAnticommuting F h2 (Work.L2F.Torus.conjMat F X)
    (Work.L2F.Torus.disc F X) (Work.L2F.Torus.conjMat_trace F X)
    (Work.L2F.Torus.conjMat_mul_self F X) hdiscX
  have hnegT : Work.L2F.negOne F ∈
      Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [mem_centralizer_iff_commute_conjMat F h2 X]
    rw [show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
    rw [neg_mul, one_mul, mul_neg, mul_one]
  have hTcyc : IsCyclic (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    (centralizer_isCyclic_and_card F h2 X hdiscX).1
  have hTcard := (centralizer_isCyclic_and_card F h2 X hdiscX).2
  have hCdef : Subgroup.centralizer ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
      = (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
          (Work.PSL2.pslMap F) := by
    rw [← hX']; exact centralizer_psl_eq_map F h2 X htrX
  have hker : Nat.card ((Work.PSL2.pslMap F).comp
      (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).subtype).ker = 2 := by
    have hsub : ((Work.PSL2.pslMap F).comp
        (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).subtype).ker
        = Subgroup.zpowers (⟨Work.L2F.negOne F, hnegT⟩ :
            ↥(Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) := by
      apply le_antisymm
      · intro y hy
        rw [MonoidHom.mem_ker] at hy
        change Work.PSL2.pslMap F ((y : ↥(Subgroup.centralizer
          ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) :
            Matrix.SpecialLinearGroup (Fin 2) F) = 1 at hy
        rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 _).mp hy with h | h
        · have hyg : y = 1 := Subtype.ext h
          rw [hyg]; exact Subgroup.one_mem _
        · have hyg : y = ⟨Work.L2F.negOne F, hnegT⟩ := Subtype.ext h
          rw [hyg]; exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
        change Work.PSL2.pslMap F (Work.L2F.negOne F) = 1
        exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
    rw [hsub, Nat.card_zpowers]
    refine orderOf_eq_prime ?_ ?_
    · have h2g : (⟨Work.L2F.negOne F, hnegT⟩ : ↥(Subgroup.centralizer
          ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) *
          ⟨Work.L2F.negOne F, hnegT⟩ = 1 := by
        apply Subtype.ext
        exact Work.L2F.Involution.negOne_mul_self F
      rwa [pow_two]
    · intro hcon
      have h' := congrArg (fun z : ↥(Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) =>
        (((z : ↥(Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)))) :
          Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) hcon
      simp [Work.L2F.negOne] at h'
      exact h2 (by linear_combination -h')
  have hφrange : ((Work.PSL2.pslMap F).comp
      (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).subtype).range
      = (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).map
          (Work.PSL2.pslMap F) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hCcyc : IsCyclic (Subgroup.centralizer
      ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) := by
    rw [hCdef, ← hφrange]
    exact isCyclic_of_surjective (hH := hTcyc) _ (MonoidHom.rangeRestrict_surjective _)
  refine ⟨hCcyc, ?_, ?_⟩
  · rw [hCdef]
    have hcard := Subgroup.card_ker_mul_card_range ((Work.PSL2.pslMap F).comp
      (Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F))).subtype)
    rw [hker, hφrange] at hcard
    rcases hTcard with h | h
    · right; rw [hcard, h]
    · left; rw [hcard, h]
  · change Nonempty (Subgroup.normalizer
      ((Subgroup.zpowers x : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃*
      DihedralGroup (Nat.card (Subgroup.centralizer
        ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))))
    have hXT : X ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff] at hh; subst hh; rfl)
    have hwwinv : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hwW : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        Work.L2F.Torus.conjMat F X *
        (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
        = -Work.L2F.Torus.conjMat F X := by
      rw [haw, neg_mul, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    have hwinvT : ∀ t ∈ Subgroup.centralizer ({X} :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)), w * t * w⁻¹ = t⁻¹ := by
      intro t ht
      have hcomm := (mem_centralizer_iff_commute_conjMat F h2 X t).mp ht
      obtain ⟨a, b, hab⟩ := commutant_algSpan F h2 _ _ (Work.L2F.Torus.conjMat_trace F X)
        (Work.L2F.Torus.conjMat_mul_self F X) hdiscX _ hcomm
      have hab' : a ^ 2 - Work.L2F.Torus.disc F X * b ^ 2 = 1 := by
        have h := det_smul_one_add_smul F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
          (Work.L2F.Torus.conjMat_trace F X) (Work.L2F.Torus.conjMat_mul_self F X) a b
        rw [← hab] at h
        rw [← h]; exact Matrix.SpecialLinearGroup.det_coe t
      have hmat : ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
          = a • (1 : Matrix (Fin 2) (Fin 2) F)
            + (-b) • Work.L2F.Torus.conjMat F X := by
        rw [hab]
        rw [show ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Work.L2F.Torus.conjMat F X) *
            (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
            = a • (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * 1 *
                (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))
              + b • (((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
                Work.L2F.Torus.conjMat F X *
                (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F))
            from by noncomm_ring]
        rw [Matrix.mul_one, hwwinv, hwW]
        congr 1
        rw [smul_neg, neg_smul]
      have hmul1 : t * (w * t * w⁻¹) = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
        change ((t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
              ((t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
              (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) = 1
        rw [hmat, hab]
        rw [smul_one_add_smul_mul F (Work.L2F.Torus.conjMat F X) (Work.L2F.Torus.disc F X)
          (Work.L2F.Torus.conjMat_mul_self F X) a b a (-b)]
        rw [show a * a + Work.L2F.Torus.disc F X * (b * -b) = 1 from by
              linear_combination hab',
          show a * -b + b * a = 0 from by ring]
        simp
      exact (inv_eq_of_mul_eq_one_right hmul1).symm
    have hwx : Work.PSL2.pslMap F w * x * (Work.PSL2.pslMap F w)⁻¹ = x⁻¹ := by
      rw [← hX',
        show Work.PSL2.pslMap F w * Work.PSL2.pslMap F X * (Work.PSL2.pslMap F w)⁻¹
          = Work.PSL2.pslMap F (w * X * w⁻¹) from by rw [map_mul, map_mul, map_inv],
        hwinvT X hXT, map_inv]
    have hwxi : (Work.PSL2.pslMap F w)⁻¹ * x * Work.PSL2.pslMap F w = x⁻¹ := by
      have hconj : (Work.PSL2.pslMap F w)⁻¹ * x⁻¹ * Work.PSL2.pslMap F w = x := by
        rw [← hwx]; group
      have h2 := congrArg Inv.inv hconj
      rw [show ((Work.PSL2.pslMap F w)⁻¹ * x⁻¹ * Work.PSL2.pslMap F w)⁻¹
          = (Work.PSL2.pslMap F w)⁻¹ * x * Work.PSL2.pslMap F w from by group] at h2
      simpa using h2
    set N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hNdef
    set C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Subgroup.centralizer ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) with hCdef2
    have hwbarN : Work.PSL2.pslMap F w ∈ N := by
      rw [hNdef, Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨n, hn⟩ := hz
        refine ⟨-n, ?_⟩
        rw [← hn,
          show Work.PSL2.pslMap F w * x ^ n * (Work.PSL2.pslMap F w)⁻¹ = x ^ (-n) from by
            rw [_root_.zpow_neg, ← _root_.inv_zpow, ← conj_zpow, hwx]]
      · intro hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨n, hn⟩ := hz
        refine ⟨-n, ?_⟩
        rw [show x ^ (-n)
            = (Work.PSL2.pslMap F w)⁻¹ * x ^ n * Work.PSL2.pslMap F w from by
          rw [_root_.zpow_neg, ← _root_.inv_zpow]
          rw [show (Work.PSL2.pslMap F w)⁻¹ * x ^ n * Work.PSL2.pslMap F w
              = (MulAut.conj (Work.PSL2.pslMap F w)⁻¹) (x ^ n) from by
            rw [MulAut.conj_apply, inv_inv]]
          rw [map_zpow, MulAut.conj_apply, inv_inv, hwxi]]
        rw [hn]; group
    have hC'eq : C = (Subgroup.centralizer ({X} :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) := hCdef
    have hCN : C ≤ N := by
      intro c hc
      rw [hNdef, Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [show c * z * c⁻¹ = z from by
          rw [zpowers_mem_centralizer hc hz, mul_assoc, mul_inv_cancel, mul_one]]
        exact hz
      · intro hz
        rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group]
        rw [show c⁻¹ * (c * z * c⁻¹) * c = c * z * c⁻¹ from by
          rw [mul_assoc, ← zpowers_mem_centralizer hc hz, ← mul_assoc, inv_mul_cancel, one_mul]]
        exact hz
    have hwbar_notmem : (⟨Work.PSL2.pslMap F w, hwbarN⟩ : ↥N) ∉ C.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      intro hwC
      have hwT : w ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
        rw [hC'eq] at hwC
        obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hwC
        have hker'' : w * t⁻¹ ∈ (Work.PSL2.pslMap F).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, mul_inv_cancel]
        rw [MonoidHom.mem_ker] at hker''
        rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (w * t⁻¹)).mp hker'' with h | h
        · rw [show w = (w * t⁻¹) * t from by group, h, one_mul]; exact ht
        · rw [show w = (w * t⁻¹) * t from by group, h]
          exact Subgroup.mul_mem _ hnegT ht
      have hcomm := (mem_centralizer_iff_commute_conjMat F h2 X w).mp hwT
      have hzero : Work.L2F.Torus.conjMat F X = 0 := by
        have h := haw; rw [hcomm] at h
        have hsum : Work.L2F.Torus.conjMat F X *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            + Work.L2F.Torus.conjMat F X *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 0 :=
          (eq_neg_iff_add_eq_zero).mp h
        have h2' : (2 : F) • (Work.L2F.Torus.conjMat F X *
            ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = 0 := by
          rw [show (2 : F) • (Work.L2F.Torus.conjMat F X *
              ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
              = Work.L2F.Torus.conjMat F X *
                  ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                + Work.L2F.Torus.conjMat F X *
                  ((w : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from by
            rw [show (2 : F) = 1 + 1 from by norm_num, add_smul, one_smul]]
          exact hsum
        have h3 := (smul_eq_zero.mp h2').resolve_left h2
        have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
          M * (((w⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)) h3
        rwa [Matrix.mul_assoc, hwwinv, Matrix.mul_one, zero_mul] at h4
      exact Work.L2F.Torus.conjMat_ne_zero F X hdiscX hzero
    have hwbar2 : Work.PSL2.pslMap F w * Work.PSL2.pslMap F w = 1 := by
      rw [← map_mul, hw2]
      exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
    have hmemT : ∀ v : Matrix.SpecialLinearGroup (Fin 2) F,
        Work.PSL2.pslMap F v ∈ (Subgroup.centralizer ({X} :
          Set (Matrix.SpecialLinearGroup (Fin 2) F))).map (Work.PSL2.pslMap F) →
        v ∈ Subgroup.centralizer ({X} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      intro v hv
      obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hv
      have hker'' : v * t⁻¹ ∈ (Work.PSL2.pslMap F).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, ht_eq, mul_inv_cancel]
      rw [MonoidHom.mem_ker] at hker''
      rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (v * t⁻¹)).mp hker'' with h | h
      · rw [show v = (v * t⁻¹) * t from by group, h, one_mul]; exact ht
      · rw [show v = (v * t⁻¹) * t from by group, h]
        exact Subgroup.mul_mem _ hnegT ht
    have hNstruct : ∀ g ∈ N, g ∈ C ∨ ∃ c ∈ C, g = c * Work.PSL2.pslMap F w := by
      intro g hg
      have hgC : g ∈ Subgroup.normalizer (C : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
        normalizer_zpowers_le_normalizer_centralizer x (by rw [← hNdef]; exact hg)
      obtain ⟨Y, hY⟩ := QuotientGroup.mk'_surjective (Subgroup.center
        (Matrix.SpecialLinearGroup (Fin 2) F)) g
      have hY' : Work.PSL2.pslMap F Y = g := hY
      have hYN : Y ∈ Subgroup.normalizer (Subgroup.centralizer ({X} :
          Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
        rw [Subgroup.mem_normalizer_iff]
        intro u
        have hiff := Subgroup.mem_normalizer_iff.mp hgC (Work.PSL2.pslMap F u)
        have hkey : Work.PSL2.pslMap F (Y * u * Y⁻¹)
            = g * Work.PSL2.pslMap F u * g⁻¹ := by
          rw [map_mul, map_mul, map_inv, hY']
        constructor
        · intro hu
          apply hmemT
          rw [← hC'eq]
          have h1 : Work.PSL2.pslMap F u ∈ C := by
            rw [hC'eq]; exact Subgroup.mem_map_of_mem _ hu
          rw [hkey]
          exact hiff.mp h1
        · intro hu
          apply hmemT
          rw [← hC'eq]
          exact hiff.mpr (by
            rw [← hkey]
            rw [hC'eq]
            exact Subgroup.mem_map_of_mem _ hu)
      rcases mem_normalizer_centralizer F h2 h5 X hdiscX w hw2 haw Y hYN with hYT | ⟨t, ht, hteq⟩
      · left
        rw [← hY']; rw [hC'eq]; exact Subgroup.mem_map_of_mem _ hYT
      · right
        refine ⟨Work.PSL2.pslMap F t, ?_, ?_⟩
        · rw [hC'eq]; exact Subgroup.mem_map_of_mem _ ht
        · rw [← hY', hteq, map_mul]
    have hC'idx : (C.subgroupOf N).index = 2 := by
      rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨⟨Work.PSL2.pslMap F w, hwbarN⟩, hwbar_notmem, ?_⟩
      intro b
      have hb := hNstruct (b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) b.2
      rcases hb with hbC | ⟨c, hc, hceq⟩
      · right; exact Subgroup.mem_subgroupOf.mpr hbC
      · left
        rw [Subgroup.mem_subgroupOf]
        rw [show (((b * ⟨Work.PSL2.pslMap F w, hwbarN⟩ : ↥N) :
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
            = (b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * Work.PSL2.pslMap F w from rfl]
        rw [hceq, mul_assoc, hwbar2, mul_one]
        exact hc
    have hC'cyc : IsCyclic ↥(C.subgroupOf N) :=
      (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hCN)).mpr hCcyc
    have hwbar2' : (⟨Work.PSL2.pslMap F w, hwbarN⟩ : ↥N) *
        ⟨Work.PSL2.pslMap F w, hwbarN⟩ = 1 := by
      apply Subtype.ext
      exact hwbar2
    have hC'inv : ∀ c ∈ C.subgroupOf N,
        (⟨Work.PSL2.pslMap F w, hwbarN⟩ : ↥N) * c *
          (⟨Work.PSL2.pslMap F w, hwbarN⟩ : ↥N)⁻¹ = c⁻¹ := by
      intro c hc
      have hc' : (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∈ C :=
        Subgroup.mem_subgroupOf.mp hc
      rw [hC'eq] at hc'
      obtain ⟨t, ht, ht_eq⟩ := Subgroup.mem_map.mp hc'
      apply Subtype.ext
      change Work.PSL2.pslMap F w *
          (c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
          (Work.PSL2.pslMap F w)⁻¹
        = ((c : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))⁻¹
      rw [← ht_eq]
      have hkey : Work.PSL2.pslMap F w * Work.PSL2.pslMap F t * (Work.PSL2.pslMap F w)⁻¹
          = Work.PSL2.pslMap F (w * t * w⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [hkey, hwinvT t ht, map_inv]
    obtain ⟨e⟩ := Work.L2F.Dihedral.mulEquiv_dihedral_of_cyclic_index_two (C.subgroupOf N)
      hC'cyc hC'idx ⟨⟨Work.PSL2.pslMap F w, hwbarN⟩, hwbar_notmem, hwbar2', hC'inv⟩
    have hcardeq : Nat.card ↥(C.subgroupOf N) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
    rw [← hcardeq]
    exact ⟨e⟩
