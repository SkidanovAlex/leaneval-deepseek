import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_const
import Submission.Work.KT.Fund.hopf_trace_det
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det
import Submission.Work.KT.Fund.clutch_agree

/-!
# `Work.KT.KL.Defs` — explicit matrices for the Bott-unit computation of `kappa_bottKL`

Setup for the proof of `Work.KT.Fund.kappa_bottKL`.  For an idempotent `P` over `C(X, ℂ)` with
`A = 1 - P`, `B = P` and the unit `u = A + z·B` over `C(X × S¹, ℂ)` (so that
`u = pullMat A + zUnit • pullMat B`), the clutched idempotent of `u` is *explicitly*
Murray–von Neumann equivalent to the geometric bundle `A ⊕ (B ⊗ H)`, where `H` is the Hopf bundle
(represented by `Work.KT.hopfIdem`).

Everything happens over the disc algebra `C(X × Ball ℂ, ℂ)` with coordinate `ζ` (`zc`) and
`s = √(1-|ζ|²)` (`zs`):

* `RhopUp` (resp. `RhopDn`) is `hopfIdem` pulled back to the upper (resp. lower) hemisphere; its
  explicit form is `(1/2) • !![1+s, ζ̄; ζ, 1-s]` (resp. `(1/2) • !![1-s, ζ̄; ζ, 1+s]`), see
  `kb_chart`;
* `Uup` (resp. `Udn`) is the graph (resp. reciprocal-graph) projection of the lift
  `Fup = A + ζB` (resp. `Fdn = A + ζ̄B`) of `u` (resp. `u⁻¹`);
* `Tup = A ⊕ (B ⊗ RhopUp)` (resp. `Tdn = A ⊕ (B ⊗ RhopDn)`) is the geometric target;
* `aUp, bUp` (resp. `aDn, bDn`) are explicit Murray–von Neumann data `Uup ~ Tup`
  (resp. `Udn ~ Tdn`), see `kb_disc_data`; they agree on the equator, see `kb_bdry_data`.

The `Y`-index types are chosen so that `Tup` is the *block sum* `A ⊕ (B ⊗ RhopUp)`: the index type
of `Tup` is `Fin n ⊕ (Fin n × Fin 2)`.
-/

namespace Work.KT.Fund
namespace KL

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The disc coordinates -/

/-- The coordinate `ζ` on the disc. -/
def zc : C(X × Ball ℂ, ℂ) := ⟨fun p => (p.2 : ℂ), by fun_prop⟩

/-- The conjugate coordinate `ζ̄`. -/
def zcb : C(X × Ball ℂ, ℂ) := ⟨fun p => star (p.2 : ℂ), by fun_prop⟩

/-- The normalising factor `c = (1 + |ζ|²)⁻¹ = (1 + ζζ̄)⁻¹`. -/
def zcn : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹, by
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro p
      have : (0 : ℝ) < 1 + ‖(p.2 : ℂ)‖ ^ 2 := by positivity
      exact_mod_cast this.ne'⟩

/-- `s = √(1-|ζ|²)`, as a complex valued function. -/
def zs : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => ((Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2) : ℝ) : ℂ), by fun_prop⟩

/-- `(1 + s)⁻¹`, the inverse of `1 + s` as an explicit continuous function. -/
def zsinv : C(X × Ball ℂ, ℂ) :=
  ⟨fun p => (((1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℝ)⁻¹ : ℂ), by
    have h1 : Continuous (fun p : X × Ball ℂ =>
        (1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2) : ℝ)) := by fun_prop
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp h1) ?_
    intro p
    have h : (0 : ℝ) < 1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2) := by positivity
    exact_mod_cast h.ne'⟩

@[simp] lemma zc_apply (p : X × Ball ℂ) : zc X p = (p.2 : ℂ) := rfl
@[simp] lemma zcb_apply (p : X × Ball ℂ) : zcb X p = star (p.2 : ℂ) := rfl
@[simp] lemma zcn_apply (p : X × Ball ℂ) :
    zcn X p = ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ := rfl
@[simp] lemma zs_apply (p : X × Ball ℂ) :
    zs X p = ((Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2) : ℝ) : ℂ) := rfl
@[simp] lemma zsinv_apply (p : X × Ball ℂ) :
    zsinv X p = (((1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℝ)⁻¹ : ℂ) := rfl

lemma zc_mul_zcb (p : X × Ball ℂ) :
    zc X p * zcb X p = ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
  show (p.2 : ℂ) * star (p.2 : ℂ) = _
  rw [show star (p.2 : ℂ) = (starRingEnd ℂ) (p.2 : ℂ) from rfl, Complex.mul_conj,
    ← Complex.sq_norm]
  push_cast
  ring

lemma zs_sq_point (p : X × Ball ℂ) :
    (zs X p) ^ 2 = 1 - ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
  have hv : ‖(p.2 : ℂ)‖ ≤ 1 := ball_norm_le_one p.2
  have h0 : (0 : ℝ) ≤ 1 - ‖(p.2 : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (p.2 : ℂ), sq_le_one_of_le_one (norm_nonneg (p.2 : ℂ)) hv]
  show ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ)) ^ 2 = _
  rw [← Complex.ofReal_pow, Real.sq_sqrt h0]
  push_cast
  ring

/-- `s² = 1 - ζζ̄`. -/
lemma zs_mul_zs : zs X * zs X = 1 - zc X * zcb X := by
  ext p
  show zs X p * zs X p = 1 - zc X p * zcb X p
  rw [← sq, zs_sq_point, zc_mul_zcb]

/-- `ζζ̄ = 1 - s²`. -/
lemma zc_mul_zcb_eq : zc X * zcb X = 1 - zs X * zs X := by
  rw [zs_mul_zs]; ring

/-- `c (1 + ζζ̄) = 1`. -/
lemma zcn_mul_one_add : zcn X * (1 + zc X * zcb X) = 1 := by
  ext p
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply]
  have hcast : ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 + ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2 := by
    push_cast; ring
  have hne : (1 + ((‖(p.2 : ℂ)‖ : ℝ) : ℂ) ^ 2) ≠ 0 := by
    have hpos : (0 : ℝ) < 1 + ‖(p.2 : ℂ)‖ ^ 2 := by positivity
    intro hc
    have hcast0 : ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [hcast]; exact hc
    exact (by exact_mod_cast hpos.ne' : ((1 + ‖(p.2 : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0) hcast0
  rw [zc_mul_zcb, ← hcast]
  exact inv_mul_cancel₀ (by rw [hcast]; exact hne)

/-- `(1+s)(1-s) = ζζ̄`. -/
lemma one_add_zs_mul_one_sub_zs : (1 + zs X) * (1 - zs X) = zc X * zcb X := by
  rw [zc_mul_zcb_eq]; ring

/-- `(1+s)² + ζζ̄ = 2(1+s)`. -/
lemma one_add_zs_gram : (1 + zs X) * (1 + zs X) + zc X * zcb X = 2 * (1 + zs X) := by
  rw [zc_mul_zcb_eq]; ring

/-- `(1-s)² + ζζ̄ = 2(1-s)`. -/
lemma one_sub_zs_gram : (1 - zs X) * (1 - zs X) + zc X * zcb X = 2 * (1 - zs X) := by
  rw [zc_mul_zcb_eq]; ring

/-- `s` is real. -/
lemma star_zs : star (zs X) = zs X := by
  ext p
  show star ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ)) = _
  rw [show star ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ))
      = (starRingEnd ℂ) ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ)) from rfl]
  exact Complex.conj_ofReal _

lemma zs_mul_zsinv : zs X * zsinv X = zsinv X * zs X := mul_comm _ _

lemma one_add_zs_mul_zsinv : (1 + zs X) * zsinv X = 1 := by
  ext p
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply]
  show (1 + ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ)))
      * ((((1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℝ)⁻¹ : ℂ)) = 1
  rw [show ((1 : ℂ) + ((↑(Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℂ)))
      = (((1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2)) : ℝ) : ℂ) by push_cast; ring]
  exact mul_inv_cancel₀ (by
    have h : (0 : ℝ) < 1 + Real.sqrt (1 - ‖(p.2 : ℂ)‖ ^ 2) := by positivity
    exact_mod_cast h.ne')

lemma zsinv_mul_one_add_zs : zsinv X * (1 + zs X) = 1 := by
  rw [mul_comm]; exact one_add_zs_mul_zsinv X

lemma isUnit_one_add_zs : IsUnit (1 + zs X) :=
  ⟨⟨1 + zs X, zsinv X, one_add_zs_mul_zsinv X, zsinv_mul_one_add_zs X⟩, rfl⟩

/-! ## Boundary values of the coordinates -/

lemma bdryRestrict_zc : bdryRestrict X (zc X) = (zUnit X : C(X × Sph ℂ, ℂ)) := by
  ext p
  rfl

/-- The value of the inverse unit `z⁻¹` of the circle. -/
lemma coe_inv_zUnit_apply (p : X × Sph ℂ) :
    (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p = ((p.2 : ℂ))⁻¹ := by
  have h : (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) * (zUnit X : C(X × Sph ℂ, ℂ)) = 1 := by
    simpa using congrArg (fun w : (C(X × Sph ℂ, ℂ))ˣ => (w : C(X × Sph ℂ, ℂ)))
      (Units.inv_mul (zUnit X))
  have hp := DFunLike.congr_fun h p
  rw [ContinuousMap.mul_apply, ContinuousMap.one_apply, zUnit_apply] at hp
  have hp' : (p.2 : ℂ) * (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p = 1 := by
    rw [mul_comm]; exact hp
  exact eq_inv_of_mul_eq_one_right hp'

/-- `star z = z⁻¹` on the unit circle. -/
lemma star_eq_inv_of_norm_eq_one (z : ℂ) (h : ‖z‖ = 1) : star z = z⁻¹ := by
  have hz : star z * z = 1 := by
    rw [show star z = (starRingEnd ℂ) z from rfl, mul_comm, Complex.mul_conj,
      ← Complex.sq_norm, h]
    norm_num
  exact eq_inv_of_mul_eq_one_left hz

lemma bdryRestrict_zcb : bdryRestrict X (zcb X) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) := by
  ext p
  show star (((sphIncl p.2 : Ball ℂ) : ℂ)) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p
  rw [coe_inv_zUnit_apply]
  exact star_eq_inv_of_norm_eq_one (p.2 : ℂ) (norm_coe_sph p.2)

lemma bdryRestrict_zcn : bdryRestrict X (zcn X) = algebraMap ℂ C(X × Sph ℂ, ℂ) (1/2) := by
  ext p
  have hv : ((sphIncl p.2 : Ball ℂ) : ℂ) = (p.2 : ℂ) := rfl
  simp only [bdryRestrict_apply, zcn_apply, hv, norm_coe_sph]
  rw [show ((1 + (1 : ℝ) ^ 2 : ℝ) : ℂ) = 2 by norm_num]
  rw [show ((algebraMap ℂ C(X × Sph ℂ, ℂ) (1 / 2) : C(X × Sph ℂ, ℂ)) p)
      = (1/2 : ℂ) from rfl]
  norm_num

lemma bdryRestrict_zs : bdryRestrict X (zs X) = 0 := by
  ext p
  have h : (1 : ℝ) - ‖((sphIncl p.2 : Ball ℂ) : ℂ)‖ ^ 2 = 0 := by
    rw [show (((sphIncl p.2 : Ball ℂ)) : ℂ) = (p.2 : ℂ) from rfl, norm_coe_sph]; ring
  simp only [bdryRestrict_apply, zs_apply, h, Real.sqrt_zero, ContinuousMap.zero_apply]
  norm_num

lemma bdryRestrict_zsinv :
    bdryRestrict X (zsinv X) = algebraMap ℂ C(X × Sph ℂ, ℂ) 1 := by
  ext p
  have hv : ((sphIncl p.2 : Ball ℂ) : ℂ) = (p.2 : ℂ) := rfl
  simp only [bdryRestrict_apply, zsinv_apply, hv, norm_coe_sph]
  rw [show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, Real.sqrt_zero]
  norm_num

/-! ## The Hopf chart projections and their chart generators -/

/-- `hopfIdem` pulled back to the upper hemisphere. -/
def RhopUp : Matrix (Fin 2) (Fin 2) C(X × Ball ℂ, ℂ) :=
  hopfIdem.2.map (⇑(pullUp X) ∘ ⇑(pullAlg (ContinuousMap.snd : C(X × S2, S2))))

/-- `hopfIdem` pulled back to the lower hemisphere. -/
def RhopDn : Matrix (Fin 2) (Fin 2) C(X × Ball ℂ, ℂ) :=
  hopfIdem.2.map (⇑(pullDn X) ∘ ⇑(pullAlg (ContinuousMap.snd : C(X × S2, S2))))

/-- The upper-chart generator `(1+s, ζ)`. -/
def uColUp : Matrix (Fin 2) (Fin 1) C(X × Ball ℂ, ℂ) := !![1 + zs X; zc X]

/-- The lower-chart generator `(ζ̄, 1+s)`. -/
def uColDn' : Matrix (Fin 2) (Fin 1) C(X × Ball ℂ, ℂ) := !![zcb X; 1 + zs X]

/-! ## The lifts and the geometric targets over the disc -/

/-- The lift `A + ζ B` of `A + z B`. -/
def FupD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := A + zc X • B

/-- The lift `A + ζ̄ B` of `A + z⁻¹ B`. -/
def FdnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := A + zcb X • B

/-- `v ↦ B v ⊗ (1+s, ζ)`, as a `(n × 2) × n` matrix. -/
def kronU {n : ℕ} (B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n × Fin 2) (Fin n) C(X × Ball ℂ, ℂ) :=
  fun (i, α) j => B i j * uColUp X α 0

/-- `v ↦ B v ⊗ (ζ̄, 1+s)`. -/
def kronS {n : ℕ} (B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n × Fin 2) (Fin n) C(X × Ball ℂ, ℂ) :=
  fun (i, α) j => B i j * uColDn' X α 0

/-- `y ↦ B · y(·,0)/(1+s)`. -/
def selU {n : ℕ} (B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n × Fin 2) C(X × Ball ℂ, ℂ) :=
  fun i (k, α) => B i k * (if (α : Fin 2) = 0 then zsinv X else 0)

/-- `y ↦ B · y(·,1)/(1+s)`. -/
def selS {n : ℕ} (B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n) (Fin n × Fin 2) C(X × Ball ℂ, ℂ) :=
  fun i (k, α) => B i k * (if (α : Fin 2) = 1 then zsinv X else 0)

/-- `A ⊕ (B ⊗ RhopUp)`, the geometric target over the upper disc. -/
def TupD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks A 0 0 (Matrix.kroneckerMap (· * ·) B (RhopUp X))

/-- `A ⊕ (B ⊗ RhopDn)`, the geometric target over the lower disc. -/
def TdnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks A 0 0 (Matrix.kroneckerMap (· * ·) B (RhopDn X))

/-- The entrance map `(v,w) ↦ (Av, Bv ⊗ (1+s,ζ))`, upper disc. -/
def alphaUpD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks A 0 (kronU X B) 0

/-- The exit map `(x,y) ↦ (Ax + By(·,0)/(1+s), F(Ax + By(·,0)/(1+s)))`, upper disc. -/
def betaUpD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks A (selU X B) (FupD X A B * A) (FupD X A B * selU X B)

/-- The entrance map `(v,w) ↦ (Aw, Bw ⊗ (ζ̄,1+s))`, lower disc. -/
def alphaDnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks A 0 0 (kronS X B)

/-- The exit map `(x,y) ↦ (G(Ax + By(·,1)/(1+s)), Ax + By(·,1)/(1+s))`, lower disc. -/
def betaDnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  Matrix.fromBlocks (FdnD X A B * A) (FdnD X A B * selS X B) A (selS X B)

/-- The graph projection of the upper lift. -/
def UupD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  graphProj C(X × Ball ℂ, ℂ) (FupD X A B)

/-- The reciprocal-graph projection of the lower lift. -/
def UdnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  recipProj C(X × Ball ℂ, ℂ) (FdnD X A B)

/-- The entrance MvN datum over the upper disc. -/
def aUpD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  alphaUpD X A B * UupD X A B

/-- The exit MvN datum over the upper disc. -/
def bUpD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  betaUpD X A B * TupD X A B

/-- The entrance MvN datum over the lower disc. -/
def aDnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  alphaDnD X A B * UdnD X A B

/-- The exit MvN datum over the lower disc. -/
def bDnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  betaDnD X A B * TdnD X A B

/-! ## The same objects attached to a matrix over `C(X, ℂ)` -/

/-- The lift `gUp A + ζ · gUp B`. -/
def Fup {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := FupD X (KC.gUp X A) (KC.gUp X B)

/-- The lift `gUp A + ζ̄ · gUp B`. -/
def Fdn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) := FdnD X (KC.gUp X A) (KC.gUp X B)

/-- The upper graph projection of the lift of `u`. -/
def Uup {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) := UupD X (KC.gUp X A) (KC.gUp X B)

/-- The lower reciprocal-graph projection of the lift of `u⁻¹`. -/
def Udn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) := UdnD X (KC.gUp X A) (KC.gUp X B)

/-- The upper geometric target. -/
def Tup {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  TupD X (KC.gUp X A) (KC.gUp X B)

/-- The lower geometric target. -/
def Tdn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  TdnD X (KC.gUp X A) (KC.gUp X B)

/-- The upper entrance datum. -/
def aUp {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  aUpD X (KC.gUp X A) (KC.gUp X B)

/-- The upper exit datum. -/
def bUp {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  bUpD X (KC.gUp X A) (KC.gUp X B)

/-- The lower entrance datum. -/
def aDn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ (Fin n × Fin 2)) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
  aDnD X (KC.gUp X A) (KC.gUp X B)

/-- The lower exit datum. -/
def bDn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ (Fin n × Fin 2)) C(X × Ball ℂ, ℂ) :=
  bDnD X (KC.gUp X A) (KC.gUp X B)

/-! ## Boundary values of the lifts -/

/-- `bdryRestrict` commutes with addition of matrices. -/
lemma bdry_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (A + B).map (bdryRestrict X)
      = A.map (bdryRestrict X) + B.map (bdryRestrict X) :=
  Matrix.map_add (⇑(bdryRestrict X)) (fun a b => map_add (bdryRestrict X) a b) A B

/-- `bdryRestrict` commutes with scalar multiplication of matrices (the scalar being a function). -/
lemma bdry_smul {n : ℕ} (c : C(X × Ball ℂ, ℂ)) (B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (c • B).map (bdryRestrict X)
      = (bdryRestrict X c) • B.map (bdryRestrict X) := by
  ext i j p
  simp only [Matrix.map_apply, Matrix.smul_apply, ContinuousMap.smul_apply, map_mul,
    ContinuousMap.mul_apply]
  rfl

lemma bdry_FupD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (FupD X A B).map (bdryRestrict X) = A.map (bdryRestrict X)
      + (zUnit X : C(X × Sph ℂ, ℂ)) • B.map (bdryRestrict X) := by
  rw [FupD, bdry_add, bdry_smul, bdryRestrict_zc]

lemma bdry_FdnD {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (FdnD X A B).map (bdryRestrict X) = A.map (bdryRestrict X)
      + (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) • B.map (bdryRestrict X) := by
  rw [FdnD, bdry_add, bdry_smul, bdryRestrict_zcb]

lemma bdry_Fup {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Fup X A B).map (bdryRestrict X) = pullMat X A
      + (zUnit X : C(X × Sph ℂ, ℂ)) • pullMat X B := by
  rw [Fup, bdry_FupD, KC.gUp_bdry, KC.gUp_bdry]

lemma bdry_Fdn {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Fdn X A B).map (bdryRestrict X) = pullMat X A
      + (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) • pullMat X B := by
  rw [Fdn, bdry_FdnD, KC.gUp_bdry, KC.gUp_bdry]

end

end KL
end Work.KT.Fund
