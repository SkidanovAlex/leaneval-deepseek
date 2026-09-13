import Submission.Grassmann.Transport
import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.DerivativeDegree
import Submission.Grassmann.Prop56
import Submission.Grassmann.Counting
import Submission.Commons.LinearAlgebra.Matrix.sum_comp_mul_mul
import Submission.Commons.LinearAlgebra.Matrix.exists_invertible_mul_of_ker_eq
import Submission.Commons.LinearAlgebra.Matrix.exists_mul_invertible_of_range_eq

/-!
# Reparametrisation of restrictions, and the two coordinate models for the `X`-derivatives

`DopX` (the `X`-derivative of arXiv:2209.04243 §8) is defined through the canonical *quotient*
maps `QsupT V₁ V₂`, `IsubT W₁ W₂` from `RestrictProp.lean`, while the switching-roles
Proposition of `SwitchingRoles.lean` is stated with the canonical maps `Qp V₁`, `Ip W₁`.  The two
pairs differ only by the choice of a basis of the same quotient space (`exist`-statements
`exists_Qp_Vco` (proved) and its `W`-side analogue `exists_Ip_Wco` (still to be done; the
column-reindexing analogue of the three `reindex_finCongr_*` helpers below is what it needs),
provable from
`Commons.LinearAlgebra.Matrix.exists_invertible_mul_of_ker_eq` — but with a `Fin`-index
mismatch), so the *`L²`/`L⁴` norms* of the two forms agree; this file records that fact in the
form in which it is used.

Contents:

* `restr_mul_mul` and the reparametrisation invariance `l2sq_restr_mul_eq` / `l4q_restr_mul_eq`;
* `range_Qsup`, `finrank_Vco`, `finrank_Wco` (the dimension bookkeeping of `Vco`/`Wco`);
* `DopUpQ` (the `QsupT`-coordinate version of `DopUpS`) and `DopX_eq_DopUpQ`;
* **`l2sq_DopUpS_eq_DopUpQ` / `l4q_DopUpS_eq_DopUpQ`**: the `L²`/`L⁴` norms of the two
  coordinate models of the `X`-derivative agree — proved through the intrinsic formula
  `l2sq_restr_shift_eq_homSub`, which depends only on `(ker Q, range ι)`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## Reparametrisation of the restriction -/

/-- Restricting by `(T * Q, ι * S)` is restricting by `(Q, ι)` followed by the reparametrisation
`A ↦ S * A * T`. -/
lemma restr_mul_mul {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin n') (Fin n') 𝔽₂)
    (S : Matrix (Fin m') (Fin m') 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr (T * Q) (ι * S) g =
      fun A : Matrix (Fin m') (Fin n') 𝔽₂ => restr Q ι g (S * A * T) := by
  funext A
  simp only [restr]
  rw [show (ι * S) * A * (T * Q) = ι * (S * A * T) * Q from by
    simp only [Matrix.mul_assoc]]

/-- **Reparametrisation invariance, `L⁴` form.** -/
theorem l4q_restr_mul_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin n') (Fin n') 𝔽₂)
    (S : Matrix (Fin m') (Fin m') 𝔽₂)
    (hT : Function.Bijective T.mulVecLin) (hS : Function.Bijective S.mulVecLin)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q (restr (T * Q) (ι * S) g) = l4q (restr Q ι g) := by
  rw [restr_mul_mul, l4q, l4q]
  congr 1
  exact Commons.LinearAlgebra.Matrix.sum_comp_mul_mul S T hS hT
    (fun A => ‖restr Q ι g A‖ ^ 4)

/-- **Reparametrisation invariance, `L²` form.** -/
theorem l2sq_restr_mul_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin n') (Fin n') 𝔽₂)
    (S : Matrix (Fin m') (Fin m') 𝔽₂)
    (hT : Function.Bijective T.mulVecLin) (hS : Function.Bijective S.mulVecLin)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr (T * Q) (ι * S) g) = l2sq (restr Q ι g) := by
  rw [restr_mul_mul, l2sq, l2sq]
  congr 1
  exact Commons.LinearAlgebra.Matrix.sum_comp_mul_mul S T hS hT
    (fun A => ‖restr Q ι g A‖ ^ 2)

/-! ## Dimension bookkeeping for `Vco` and `Wco` -/

/-- `Qsup V₁ V₂ h` is onto. -/
theorem range_Qsup {n : ℕ} (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    LinearMap.range (Qsup V₁ V₂ h).mulVecLin = ⊤ := by
  have hcomp : LinearMap.range ((Qsup V₁ V₂ h).mulVecLin.comp (Qp V₂).mulVecLin) =
      LinearMap.range (Qsup V₁ V₂ h).mulVecLin := by
    rw [LinearMap.range_comp, range_Qp, Submodule.map_top]
  have h2 := range_Qp V₁
  rw [← Qsup_mul_Qp V₁ V₂ h, Matrix.mulVecLin_mul, hcomp] at h2
  exact h2

/-- `dim (Vco V₂ V₁) = dim V₁ - dim V₂`. -/
theorem finrank_Vco {n : ℕ} (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    Module.finrank 𝔽₂ (Vco V₂ V₁) = Module.finrank 𝔽₂ V₁ - Module.finrank 𝔽₂ V₂ := by
  have h1 : Module.finrank 𝔽₂ (Submodule.map (Qe V₂).toLinearMap
        (Submodule.map (Submodule.mkQ V₂) V₁)) =
      Module.finrank 𝔽₂ (Submodule.map (Submodule.mkQ V₂) V₁) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (Qe V₂).toLinearMap
      (Qe V₂).injective (Submodule.map (Submodule.mkQ V₂) V₁))).symm
  rw [Vco, h1, finrank_map_mkQ_of_le V₂ V₁ h]

/-- `dim (Wco W₂ W₁) = dim W₁` (for `W₁ ≤ W₂`). -/
theorem finrank_Wco {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    Module.finrank 𝔽₂ (Wco W₂ W₁) = Module.finrank 𝔽₂ W₁ := by
  have h1 : Module.finrank 𝔽₂ (Submodule.map (ecW W₂).symm.toLinearMap
        (Submodule.comap W₂.subtype W₁)) = Module.finrank 𝔽₂ (Submodule.comap W₂.subtype W₁) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ecW W₂).symm.toLinearMap
      (ecW W₂).symm.injective (Submodule.comap W₂.subtype W₁))).symm
  have h2 : Module.finrank 𝔽₂ (Submodule.comap W₂.subtype W₁) = Module.finrank 𝔽₂ W₁ :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := W₁) (q := W₂) h)
  rw [Wco, h1, h2]

/-! ## The two coordinate models of the `X`-derivative -/

/-- The `X`-derivative in the `QsupT`/`IsubT` coordinates: a restriction of the multiplier
`plLE X` of the quotient space, written directly on the coordinates of `L(V/V₂,W₂)` and of
`L(V/V₁,W₁)`. -/
noncomputable def DopUpQ {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) :
    Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂ → ℂ :=
  restr (QsupT V₁ V₂) (IsubT W₁ W₂) (shift S (lapMulN (plLE X) g))

/-- **`DopX` is the `QsupT`-coordinate version of the `X`-derivative.** -/
theorem DopX_eq_DopUpQ {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂))
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DopX V₁ W₁ V₂ W₂ X T f =
      DopUpQ V₁ W₁ V₂ W₂ (XtOf V₂ W₂ X) 0 (Dop0S V₂ W₂ T f) := by
  rw [DopX, DopUpQ, shift_zero_left]
  rfl

/-- The kernel of `QsupT V₁ V₂` is `Vco V₂ V₁`. -/
theorem ker_QsupT {n : ℕ} (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    LinearMap.ker (QsupT V₁ V₂).mulVecLin = Vco V₂ V₁ := by
  rw [QsupT_eq V₁ V₂ h, ker_Qsup]

/-- The range of `QsupT V₁ V₂` is everything. -/
theorem range_QsupT {n : ℕ} (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    LinearMap.range (QsupT V₁ V₂).mulVecLin = ⊤ := by
  rw [QsupT_eq V₁ V₂ h]; exact range_Qsup V₁ V₂ h

/-- The range of `IsubT W₁ W₂` is `Wco W₂ W₁`. -/
theorem range_IsubT {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    LinearMap.range (IsubT W₁ W₂).mulVecLin = Wco W₂ W₁ := by
  rw [IsubT_eq W₁ W₂ h, range_Isub]

/-- The kernel of `IsubT W₁ W₂` is trivial. -/
theorem ker_IsubT {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    LinearMap.ker (IsubT W₁ W₂).mulVecLin = ⊥ := by
  rw [IsubT_eq W₁ W₂ h, ker_Isub]

/-- **The two coordinate models of the `X`-derivative have the same `L⁴` norm.** -/
theorem l4q_DopUpS_eq_DopUpQ {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (X : Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) :
    l4q (DopUpS (Vco V₂ V₁) (Wco W₂ W₁) X S g) =
      l4q (DopUpQ V₁ W₁ V₂ W₂ X S g) := by
  have h1 := l4q_restr_shift_eq_homSub (Vco V₂ V₁) (Wco W₂ W₁) (Qp (Vco V₂ V₁))
    (Ip (Wco W₂ W₁)) (ker_Qp _) (range_Qp _) (range_Ip _) (ker_Ip _) S (lapMulN (plLE X) g)
  have h2 := l4q_restr_shift_eq_homSub (Vco V₂ V₁) (Wco W₂ W₁) (QsupT V₁ V₂) (IsubT W₁ W₂)
    (ker_QsupT V₁ V₂ hV) (range_QsupT V₁ V₂ hV) (range_IsubT W₁ W₂ hW)
    (ker_IsubT W₁ W₂ hW) S (lapMulN (plLE X) g)
  rw [DopUpS, DopUpQ, h1, h2]

/-- **The two coordinate models of the `X`-derivative have the same `L²` norm.** -/
theorem l2sq_DopUpS_eq_DopUpQ {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hV : V₂ ≤ V₁) (hW : W₁ ≤ W₂)
    (X : Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) :
    l2sq (DopUpS (Vco V₂ V₁) (Wco W₂ W₁) X S g) =
      l2sq (DopUpQ V₁ W₁ V₂ W₂ X S g) := by
  have h1 := l2sq_restr_shift_eq_homSub (Vco V₂ V₁) (Wco W₂ W₁) (Qp (Vco V₂ V₁))
    (Ip (Wco W₂ W₁)) (ker_Qp _) (range_Qp _) (range_Ip _) (ker_Ip _) S (lapMulN (plLE X) g)
  have h2 := l2sq_restr_shift_eq_homSub (Vco V₂ V₁) (Wco W₂ W₁) (QsupT V₁ V₂) (IsubT W₁ W₂)
    (ker_QsupT V₁ V₂ hV) (range_QsupT V₁ V₂ hV) (range_IsubT W₁ W₂ hW)
    (ker_IsubT W₁ W₂ hW) S (lapMulN (plLE X) g)
  rw [DopUpS, DopUpQ, h1, h2]


/-! ## The two composition identities needed for the induction step -/

/-- **Restricting a hybrid Laplacian**: the transported predicate is the hybrid predicate of the
restricted character. -/
theorem Lsub_restr_eq {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (V₄ : Submodule 𝔽₂ (Fin n' → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin m' → 𝔽₂)) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Lsub V₄ W₄ (restr Q ι g) =
      restr Q ι (lapMulN (fun Z : Matrix (Fin n) (Fin m) 𝔽₂ =>
        hybridPredSub V₄ W₄ (Q * Z * ι)) g) :=
  (restr_lapMulN_comp Q ι (hybridPredSub V₄ W₄) g).symm

/-- **The `X`-derivative on the character basis in the `QsupT` coordinates**: it is the
transported `plLE`-multiplier of the big space. -/
theorem DopUpQ_eq_restr {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : Matrix (Fin (n - Module.finrank 𝔽₂ V₂)) (Fin (Module.finrank 𝔽₂ W₂)) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂)
    (g : Matrix (Fin (Module.finrank 𝔽₂ W₂)) (Fin (n - Module.finrank 𝔽₂ V₂)) 𝔽₂ → ℂ) :
    DopUpQ V₁ W₁ V₂ W₂ X S g =
      restr (QsupT V₁ V₂) (IsubT W₁ W₂)
        (shift S (lapMulN (plLE X) g)) := rfl

/-- **Composition of two shifted restrictions** (with the shift staying in the big space). -/
theorem restr_shift_restr_shift {m n m₁ n₁ m₂ n₂ : ℕ}
    (Q₁ : Matrix (Fin n₁) (Fin n) 𝔽₂) (ι₁ : Matrix (Fin m) (Fin m₁) 𝔽₂)
    (Q₂ : Matrix (Fin n₂) (Fin n₁) 𝔽₂) (ι₂ : Matrix (Fin m₁) (Fin m₂) 𝔽₂)
    (S : Matrix (Fin m₁) (Fin n₁) 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q₂ ι₂ (shift S (restr Q₁ ι₁ (shift T h))) =
      restr (Q₂ * Q₁) (ι₁ * ι₂) (shift (T + ι₁ * S * Q₁) h) := by
  rw [shift_restr, restr_restr, shift_shift]


/-! ## `finCongr`-transport of a matrix (the bridge between the two index types) -/

/-- Reindexing the rows of a matrix along `finCongr` acts on `mulVec` by precomposition. -/
theorem reindex_finCongr_mulVec {a a' b : ℕ} (h : a = a') (M : Matrix (Fin a) (Fin b) 𝔽₂)
    (x : Fin b → 𝔽₂) :
    (Matrix.reindex (finCongr h) (Equiv.refl (Fin b)) M).mulVec x =
      fun i => M.mulVec x ((finCongr h).symm i) := by
  rw [Matrix.reindex_apply]
  funext i
  simp [Matrix.submatrix, Matrix.mulVec]

/-- Reindexing the rows along `finCongr` does not change the kernel. -/
theorem ker_reindex_finCongr {a a' b : ℕ} (h : a = a') (M : Matrix (Fin a) (Fin b) 𝔽₂) :
    LinearMap.ker (Matrix.reindex (finCongr h) (Equiv.refl (Fin b)) M).mulVecLin =
      LinearMap.ker M.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
  rw [reindex_finCongr_mulVec]
  constructor
  · intro hx i
    simpa using hx ((finCongr h) i)
  · intro hx i
    exact hx _

/-- Reindexing the rows along `finCongr` preserves surjectivity. -/
theorem range_reindex_finCongr_eq_top {a a' b : ℕ} (h : a = a') (M : Matrix (Fin a) (Fin b) 𝔽₂)
    (hM : LinearMap.range M.mulVecLin = ⊤) :
    LinearMap.range (Matrix.reindex (finCongr h) (Equiv.refl (Fin b)) M).mulVecLin = ⊤ := by
  rw [LinearMap.range_eq_top] at hM ⊢
  intro y
  obtain ⟨x, hx⟩ := hM (fun i => y (finCongr h i))
  have hx' : M.mulVec x = fun i => y (finCongr h i) := by
    rwa [Matrix.mulVecLin_apply] at hx
  refine ⟨x, ?_⟩
  funext i
  rw [Matrix.mulVecLin_apply, reindex_finCongr_mulVec, hx']
  simp

/-- **The two "second restriction" maps on the `V`-side differ by an invertible factor.**  The
`finCongr`-reindexing reconciles the two index types (`dim (Vco V₂ V₁) = dim V₁ - dim V₂`). -/
theorem exists_Qp_Vco {n : ℕ} (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (h : V₂ ≤ V₁) :
    ∃ T : Matrix (Fin (n - Module.finrank 𝔽₂ V₁)) (Fin (n - Module.finrank 𝔽₂ V₁)) 𝔽₂,
      Function.Bijective T.mulVecLin ∧
      Matrix.reindex
        (finCongr (show (n - Module.finrank 𝔽₂ V₂) - Module.finrank 𝔽₂ (Vco V₂ V₁) =
            n - Module.finrank 𝔽₂ V₁ from by
          have hle1 : Module.finrank 𝔽₂ V₂ ≤ Module.finrank 𝔽₂ V₁ :=
            Submodule.finrank_mono h
          have hle2 : Module.finrank 𝔽₂ V₁ ≤ n := by
            have hh := Submodule.finrank_le (R := 𝔽₂) V₁
            rwa [Module.finrank_fin_fun (R := 𝔽₂)] at hh
          rw [finrank_Vco V₁ V₂ h]
          omega))
        (Equiv.refl _) (Qp (Vco V₂ V₁)) =
        T * Qsup V₁ V₂ h := by
  refine Commons.LinearAlgebra.Matrix.exists_invertible_mul_of_ker_eq (Qsup V₁ V₂ h) _ ?_ ?_ ?_
  · rw [ker_Qsup, ker_reindex_finCongr, ker_Qp]
  · exact range_Qsup V₁ V₂ h
  · exact range_reindex_finCongr_eq_top _ _ (range_Qp _)


/-- Reindexing the *columns* of a matrix along `finCongr` acts on `mulVec` by precomposition. -/
theorem reindex_finCongr_mulVec_col {a b b' : ℕ} (h : b = b') (M : Matrix (Fin a) (Fin b) 𝔽₂)
    (x : Fin b' → 𝔽₂) :
    (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVec x =
      M.mulVec (fun j => x (finCongr h j)) := by
  rw [Matrix.reindex_apply]
  funext i
  rw [Matrix.mulVec, Matrix.mulVec]
  simp only [Matrix.submatrix]
  exact Fintype.sum_equiv (finCongr h).symm
    (fun k => M i ((finCongr h).symm k) * x k) (fun j => M i j * x (finCongr h j))
    (fun k => by simp)

/-- Reindexing the columns along `finCongr` does not change the range. -/
theorem range_reindex_finCongr_col_eq {a b b' : ℕ} (h : b = b')
    (M : Matrix (Fin a) (Fin b) 𝔽₂) :
    LinearMap.range (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVecLin =
      LinearMap.range M.mulVecLin := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨fun j => x (finCongr h j), by
      simp only [Matrix.mulVecLin_apply, reindex_finCongr_mulVec_col]⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨fun j => x ((finCongr h).symm j), by
      simp only [Matrix.mulVecLin_apply, reindex_finCongr_mulVec_col,
        Equiv.symm_apply_apply]⟩

/-- Reindexing the columns along `finCongr` preserves injectivity. -/
theorem ker_reindex_finCongr_col_eq_bot_iff {a b b' : ℕ} (h : b = b')
    (M : Matrix (Fin a) (Fin b) 𝔽₂) :
    LinearMap.ker (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVecLin = ⊥ ↔
      LinearMap.ker M.mulVecLin = ⊥ := by
  rw [LinearMap.ker_eq_bot, LinearMap.ker_eq_bot]
  constructor
  · intro hx x x' hxx'
    have hxx'' : M.mulVec x = M.mulVec x' := by
      simpa only [Matrix.mulVecLin_apply] using hxx'
    have h1 : (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVecLin
        (fun j => x ((finCongr h).symm j)) =
        (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVecLin
          (fun j => x' ((finCongr h).symm j)) := by
      simp only [Matrix.mulVecLin_apply, reindex_finCongr_mulVec_col,
        Equiv.symm_apply_apply]
      exact hxx''
    have h2 := hx h1
    funext j
    have h3 := congrFun h2 (finCongr h j)
    simpa using h3
  · intro hx x x' hxx'
    have hxx'' : (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVec x =
        (Matrix.reindex (Equiv.refl (Fin a)) (finCongr h) M).mulVec x' := by
      simpa only [Matrix.mulVecLin_apply] using hxx'
    have h1 : M.mulVecLin (fun j => x (finCongr h j)) =
        M.mulVecLin (fun j => x' (finCongr h j)) := by
      simp only [Matrix.mulVecLin_apply, ← reindex_finCongr_mulVec_col]
      exact hxx''
    have h2 := hx h1
    funext j
    have h3 := congrFun h2 ((finCongr h).symm j)
    simpa using h3

/-- **The two "second restriction" maps on the `W`-side differ by an invertible factor.** -/
theorem exists_Ip_Wco {m : ℕ} (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (h : W₁ ≤ W₂) :
    ∃ S : Matrix (Fin (Module.finrank 𝔽₂ W₁)) (Fin (Module.finrank 𝔽₂ W₁)) 𝔽₂,
      Function.Bijective S.mulVecLin ∧
      Matrix.reindex (Equiv.refl _)
        (finCongr (show Module.finrank 𝔽₂ (Wco W₂ W₁) = Module.finrank 𝔽₂ W₁ from
          finrank_Wco W₁ W₂ h))
        (Ip (Wco W₂ W₁)) = Isub W₁ W₂ h * S := by
  refine Commons.LinearAlgebra.Matrix.exists_mul_invertible_of_range_eq (Isub W₁ W₂ h) _ ?_ ?_ ?_
  · rw [range_Isub, range_reindex_finCongr_col_eq, range_Ip]
  · exact ker_Isub W₁ W₂ h
  · exact (ker_reindex_finCongr_col_eq_bot_iff _ _).mpr (ker_Ip _)

end

end Submission.Grassmann
