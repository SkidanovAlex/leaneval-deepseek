import Submission.Grassmann.Assembly2
import Submission.Grassmann.Reparam
import Submission.Commons.Algebra.AddSubgroup.sum_sum_add_eq

/-!
# Step (E) of §8 of arXiv:2209.04243, stage 1: reparametrising `BareS`

`BareS Vr Wr V₂r W₂r V₃ W₃ X S' g` is built out of two restrictions and multiplication by
coordinate matrices.  This file shows that it is the restriction `(Qp V₂r, Ip W₂r)` of a
Laplacian of the ambient space whose multiplier is the transported `plLE`-predicate, and then
that the *nested* restriction of `Dop0S t.1 t.2.1 T f` can be collapsed into a single shift of a
single Laplacian of the big space.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- **The `BareS` summand as an ambient Laplacian restricted to `(V₂r, W₂r)`.** -/
theorem BareS_eq_restr {N M : ℕ} (Vr : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (Wr : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂r : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (X : Matrix (Fin N) (Fin M) 𝔽₂)
    (S' : Matrix (Fin M) (Fin N) 𝔽₂) (hV : V₃ ≤ V₂r) (hW : W₂r ≤ W₃)
    (g : Matrix (Fin M) (Fin N) 𝔽₂ → ℂ) :
    BareS Vr Wr V₂r W₂r V₃ W₃ X S' g =
      restr (Qp V₂r) (Ip W₂r)
        (lapMulN (fun Z : Matrix (Fin N) (Fin M) 𝔽₂ =>
          plLE (charMat V₃ W₃ X) (charMat V₃ W₃ Z))
          (shift S' (Lsub V₃ W₃ g))) := by
  rw [BareS, Dop0S]
  rw [← restr_lapMulN_comp (Qp V₃) (Ip W₃) (plLE (charMat V₃ W₃ X))
    (shift S' (Lsub V₃ W₃ g))]
  rw [restr_restr (Qp V₃) (Ip W₃) (QsupT V₂r V₃) (IsubT W₂r W₃)
    (lapMulN (fun X₁ : Matrix (Fin N) (Fin M) 𝔽₂ =>
      plLE (charMat V₃ W₃ X) (Qp V₃ * X₁ * Ip W₃)) (shift S' (Lsub V₃ W₃ g)))]
  rw [QsupT_eq V₂r V₃ hV, Qsup_mul_Qp V₂r V₃ hV, IsubT_eq W₂r W₃ hW, Ip_mul_Isub W₂r W₃ hW]
  rfl

/-! ## Collapsing the nested restriction into a single big-space shift -/

/-- The transported `plLE`-predicate: `plLE` against the `(V₃,W₃)`-coordinates of `X₀`. -/
abbrev PTranspA (t : Triple m n) (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂)) :
    Matrix (Fin (n - Module.finrank 𝔽₂ t.1)) (Fin (Module.finrank 𝔽₂ t.2.1)) 𝔽₂ → Prop :=
  fun Y => plLE (charMat V₃ W₃ (XtOf t.1 t.2.1 t.2.2)) (charMat V₃ W₃ Y)

/-- The hybrid predicate of the quotient space, transported to the big space. -/
abbrev PInA (t : Triple m n) (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂)) :
    Matrix (Fin n) (Fin m) 𝔽₂ → Prop :=
  fun Z => hybridPredSub V₃ W₃ (Qp t.1 * Z * Ip t.2.1)

/-- The combined multiplier of the collapsed expression. -/
abbrev PComb (t : Triple m n) (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂)) :
    Matrix (Fin n) (Fin m) 𝔽₂ → Prop :=
  fun Z => PTranspA t V₃ W₃ (Qp t.1 * Z * Ip t.2.1) ∧ PInA t V₃ W₃ Z

/-- **The nested restriction collapses**: `BareS … (Dop0S t.1 t.2.1 T f)` is the restriction of
a single Laplacian of the big space, shifted by a *single* shift
`T + Ip t.2.1 * (Ip Wr * S * Qp Vr) * Qp t.1`. -/
theorem BareS_Dop0S_eq_restr (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂))
    (hV : V₃ ≤ liftV (Vco t.1 (trV₁ t)) V₄)
    (hW : liftW (Wco t.2.1 (trW₁ t)) W₄ ≤ W₃)
    (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))))
      (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    BareS (Vco t.1 (trV₁ t)) (Wco t.2.1 (trW₁ t))
        (liftV (Vco t.1 (trV₁ t)) V₄) (liftW (Wco t.2.1 (trW₁ t)) W₄) V₃ W₃
        (XtOf t.1 t.2.1 t.2.2)
        (0 + Ip (Wco t.2.1 (trW₁ t)) * S * Qp (Vco t.1 (trV₁ t)))
        (Dop0S t.1 t.2.1 T f)
      = restr (Qp (liftV (Vco t.1 (trV₁ t)) V₄) * Qp t.1)
          (Ip t.2.1 * Ip (liftW (Wco t.2.1 (trW₁ t)) W₄))
          (shift (T + Ip t.2.1 *
              (0 + Ip (Wco t.2.1 (trW₁ t)) * S * Qp (Vco t.1 (trV₁ t))) * Qp t.1)
            (lapMulN (PComb t V₃ W₃) (Lsub t.1 t.2.1 f))) := by
  rw [BareS_eq_restr (Vco t.1 (trV₁ t)) (Wco t.2.1 (trW₁ t))
    (liftV (Vco t.1 (trV₁ t)) V₄) (liftW (Wco t.2.1 (trW₁ t)) W₄) V₃ W₃
    (XtOf t.1 t.2.1 t.2.2) _ hV hW (Dop0S t.1 t.2.1 T f)]
  rw [Dop0S]
  rw [Lsub_restr_eq (Qp t.1) (Ip t.2.1) V₃ W₃ (shift T (Lsub t.1 t.2.1 f))]
  rw [lapMulN_shift]
  rw [← restr_lapMulN_comp (Qp t.1) (Ip t.2.1) (PTranspA t V₃ W₃)
    (lapMulN (PInA t V₃ W₃) (shift T (Lsub t.1 t.2.1 f)))]
  rw [lapMulN_comp, lapMulN_shift]
  rw [shift_restr, shift_shift]
  rw [restr_restr]

/-- **The `l2sq` version of the collapse**: the composite coordinate maps may be replaced by
the canonical `Qp`/`Ip` of the corresponding *big space* subspaces. -/
theorem l2sq_BareS_Dop0S (t : Triple m n)
    (V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (Vco t.1 (trV₁ t))) → 𝔽₂))
    (W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))) → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂))
    (hV : V₃ ≤ liftV (Vco t.1 (trV₁ t)) V₄)
    (hW : liftW (Wco t.2.1 (trW₁ t)) W₄ ≤ W₃)
    (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (Wco t.2.1 (trW₁ t))))
      (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (Vco t.1 (trV₁ t)))) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (BareS (Vco t.1 (trV₁ t)) (Wco t.2.1 (trW₁ t))
        (liftV (Vco t.1 (trV₁ t)) V₄) (liftW (Wco t.2.1 (trW₁ t)) W₄) V₃ W₃
        (XtOf t.1 t.2.1 t.2.2)
        (0 + Ip (Wco t.2.1 (trW₁ t)) * S * Qp (Vco t.1 (trV₁ t)))
        (Dop0S t.1 t.2.1 T f)) =
      l2sq (restr (Qp (liftV t.1 (liftV (Vco t.1 (trV₁ t)) V₄)))
          (Ip (liftW t.2.1 (liftW (Wco t.2.1 (trW₁ t)) W₄)))
          (shift (T + Ip t.2.1 *
              (0 + Ip (Wco t.2.1 (trW₁ t)) * S * Qp (Vco t.1 (trV₁ t))) * Qp t.1)
            (lapMulN (PComb t V₃ W₃) (Lsub t.1 t.2.1 f)))) := by
  rw [BareS_Dop0S_eq_restr t V₄ W₄ V₃ W₃ hV hW T S f]
  have h1 : LinearMap.ker ((Qp (liftV (Vco t.1 (trV₁ t)) V₄) * Qp t.1)).mulVecLin
      = liftV t.1 (liftV (Vco t.1 (trV₁ t)) V₄) := by
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Qp]
  have h2 : LinearMap.range ((Qp (liftV (Vco t.1 (trV₁ t)) V₄) * Qp t.1)).mulVecLin = ⊤ := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]
  have h3 : LinearMap.range (Ip t.2.1 * Ip (liftW (Wco t.2.1 (trW₁ t)) W₄)).mulVecLin
      = liftW t.2.1 (liftW (Wco t.2.1 (trW₁ t)) W₄) := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Ip]
  have h4 : LinearMap.ker (Ip t.2.1 * Ip (liftW (Wco t.2.1 (trW₁ t)) W₄)).mulVecLin = ⊥ := by
    rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip]
  refine l2sq_restr_congr (liftV t.1 (liftV (Vco t.1 (trV₁ t)) V₄))
    (liftW t.2.1 (liftW (Wco t.2.1 (trW₁ t)) W₄))
    (Qp (liftV (Vco t.1 (trV₁ t)) V₄) * Qp t.1)
    (Ip t.2.1 * Ip (liftW (Wco t.2.1 (trW₁ t)) W₄))
    (Qp (liftV t.1 (liftV (Vco t.1 (trV₁ t)) V₄)))
    (Ip (liftW t.2.1 (liftW (Wco t.2.1 (trW₁ t)) W₄)))
    h1 h2 h3 h4 (ker_Qp _) (range_Qp _) (range_Ip _) (ker_Ip _) _
/-! ## Stage 2: the collapse of `SwSum` -/

/-- The subspace `Vco t.1 (trV₁ t)` of a triple. -/
abbrev VrOf {m n : ℕ} (t : Triple m n) :
    Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) :=
  Vco t.1 (trV₁ t)

/-- The subspace `Wco t.2.1 (trW₁ t)` of a triple. -/
abbrev WrOf {m n : ℕ} (t : Triple m n) :
    Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂) :=
  Wco t.2.1 (trW₁ t)

/-- The `W`-side factor of the combined shift. -/
abbrev ShiftM₁ {m n : ℕ} (t : Triple m n) :
    Matrix (Fin m) (Fin (Module.finrank 𝔽₂ (WrOf t))) 𝔽₂ :=
  Ip t.2.1 * Ip (WrOf t)

/-- The `V`-side factor of the combined shift. -/
abbrev ShiftM₂ {m n : ℕ} (t : Triple m n) :
    Matrix (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) (Fin n) 𝔽₂ :=
  Qp (VrOf t) * Qp t.1

/-- The two forms of the combined shift agree. -/
lemma shift_shift_eq {m n : ℕ} (t : Triple m n)
    (S : Matrix (Fin (Module.finrank 𝔽₂ (WrOf t)))
      (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) 𝔽₂) :
    Ip t.2.1 * (0 + Ip (WrOf t) * S * Qp (VrOf t)) * Qp t.1
      = ShiftM₁ t * S * ShiftM₂ t := by
  simp only [ShiftM₁, ShiftM₂, zero_add, Matrix.mul_assoc]

/-- `l2sq` vanishes on the zero function. -/
lemma l2sq_eq_zero_of_eq_zero {m n : ℕ} {g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (h : ∀ A, g A = 0) : l2sq g = 0 := by
  rw [l2sq]
  simp [h]

lemma l2sq_SwitchSummandS {N M : ℕ} (V₁ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₂ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (V₃ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (X : Matrix (Fin N) (Fin M) 𝔽₂)
    (S : Matrix (Fin M) (Fin N) 𝔽₂) (g : Matrix (Fin M) (Fin N) 𝔽₂ → ℂ) :
    l2sq (SwitchSummandS V₁ W₁ V₂ W₂ V₃ W₃ X S g) =
      if Fr V₁ W₁ V₂ W₂ V₃ W₃ then l2sq (BareS V₁ W₁ V₂ W₂ V₃ W₃ X S g) else 0 := by
  rw [SwitchSummandS]
  by_cases h : Fr V₁ W₁ V₂ W₂ V₃ W₃
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    refine l2sq_eq_zero_of_eq_zero (fun A => rfl)

/-- Two `l2sq`-squared terms with an `if` agree. -/
lemma ite_sq_eq (p : Prop) [Decidable p] (a : ℝ) : (if p then a else 0) ^ 2 = if p then a ^ 2 else 0 := by
  by_cases h : p <;> simp [h]

/-- **The collapsed switching sum**: the nested restrictions have been replaced by a single
restriction of a single Laplacian of the big space, and the shift is the combined shift. -/
def SwColl (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂),
    ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂),
      (if SwGuard t d V₄ W₄ then
        ∑ S : Matrix (Fin (Module.finrank 𝔽₂ (WrOf t)))
              (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) 𝔽₂,
          ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
              Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
            (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
              then (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift (T + ShiftM₁ t * S * ShiftM₂ t)
                      (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
              else 0)
        else 0)

/-- **`SwSum = SwColl`** (pointwise in the shift `T`). -/
theorem SwSum_eq_SwColl (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    SwSum t T f d = SwColl t T f d := by
  unfold SwSum SwColl
  refine Finset.sum_congr rfl (fun V₄ _ => Finset.sum_congr rfl (fun W₄ _ => ?_))
  by_cases hg : SwGuard t d V₄ W₄
  · rw [if_pos hg, if_pos hg]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun p _ => ?_))
    rw [l2sq_SwitchSummandS]
    by_cases hF : Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
    · rw [if_pos hF, if_pos hF]
      rw [l2sq_BareS_Dop0S t V₄ W₄ p.1 p.2 (le_trans le_sup_left (le_of_eq hF.2.1))
        hF.2.2.1 T S f, shift_shift_eq]
    · rw [if_neg hF, if_neg hF]
      norm_num
  · rw [if_neg hg, if_neg hg]

/-! ## Stage 3: averaging over the shift `S` -/

/-- The image of the shift map `S ↦ M₁ * S * M₂`, as an additive subgroup. -/
def shiftSub {m n P Q : ℕ} (M₁ : Matrix (Fin m) (Fin P) 𝔽₂) (M₂ : Matrix (Fin Q) (Fin n) 𝔽₂) :
    AddSubgroup (Matrix (Fin m) (Fin n) 𝔽₂) where
  carrier := {T | ∃ S : Matrix (Fin P) (Fin Q) 𝔽₂, T = M₁ * S * M₂}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨S, rfl⟩ ⟨S', rfl⟩
    exact ⟨S + S', by rw [Matrix.mul_add, Matrix.add_mul]⟩
  neg_mem' := by
    rintro a ⟨S, rfl⟩
    exact ⟨-S, by rw [Matrix.mul_neg, Matrix.neg_mul]⟩

/-- If `M₁` is injective and `M₂` is onto then `S ↦ M₁ * S * M₂` is injective. -/
lemma mul_mul_eq_zero_imp {m n P Q : ℕ} (M₁ : Matrix (Fin m) (Fin P) 𝔽₂)
    (M₂ : Matrix (Fin Q) (Fin n) 𝔽₂)
    (h₁ : LinearMap.ker M₁.mulVecLin = ⊥) (h₂ : LinearMap.range M₂.mulVecLin = ⊤)
    {S : Matrix (Fin P) (Fin Q) 𝔽₂} (h : M₁ * S * M₂ = 0) : S = 0 := by
  have hcomp : (M₁ * S * M₂).mulVecLin = 0 := by rw [h, Matrix.mulVecLin_zero]
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul] at hcomp
  have hS : S.mulVecLin = 0 := by
    apply LinearMap.ext
    intro y
    have hy : y ∈ LinearMap.range M₂.mulVecLin := by rw [h₂]; exact Submodule.mem_top
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
    have hxx := congrArg (fun f => f x) hcomp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hxx
    rw [hx] at hxx
    have : S.mulVecLin y ∈ LinearMap.ker M₁.mulVecLin := hxx
    rw [h₁] at this
    simpa using this
  exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply', Matrix.mulVecLin_zero] using hS)

/-- **Averaging over the shift `S`**: for `ker M₁ = ⊥` and `range M₂ = ⊤`,
`Σ_T Σ_S φ (T + M₁ * S * M₂) = 2^{PQ} Σ_T φ T`. -/
theorem sum_sum_add_mul_mul_zmod2 {m n P Q : ℕ} (M₁ : Matrix (Fin m) (Fin P) 𝔽₂)
    (M₂ : Matrix (Fin Q) (Fin n) 𝔽₂)
    (h₁ : LinearMap.ker M₁.mulVecLin = ⊥) (h₂ : LinearMap.range M₂.mulVecLin = ⊤)
    (φ : Matrix (Fin m) (Fin n) 𝔽₂ → ℝ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        ∑ S : Matrix (Fin P) (Fin Q) 𝔽₂, φ (T + M₁ * S * M₂)) =
      (2 : ℝ) ^ (P * Q) * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂, φ T := by
  classical
  set H := shiftSub M₁ M₂ with hH
  have hinj : ∀ S S' : Matrix (Fin P) (Fin Q) 𝔽₂, M₁ * S * M₂ = M₁ * S' * M₂ → S = S' := by
    intro S S' h
    have h0 : M₁ * (S - S') * M₂ = 0 := by rw [Matrix.mul_sub, Matrix.sub_mul, h, sub_self]
    have := mul_mul_eq_zero_imp M₁ M₂ h₁ h₂ h0
    simpa using sub_eq_zero.mp this
  have hbij : Function.Bijective (fun S : Matrix (Fin P) (Fin Q) 𝔽₂ =>
      (⟨M₁ * S * M₂, ⟨S, rfl⟩⟩ : H)) := by
    constructor
    · intro S S' h
      exact hinj S S' (Subtype.ext_iff.mp h)
    · rintro ⟨T, ⟨S, rfl⟩⟩
      exact ⟨S, rfl⟩
  rw [Finset.sum_congr rfl (fun T _ =>
    Fintype.sum_equiv (Equiv.ofBijective _ hbij) (fun S => φ (T + M₁ * S * M₂))
      (fun h => φ (T + (h : Matrix (Fin m) (Fin n) 𝔽₂))) (fun S => rfl))]
  rw [Commons.Algebra.AddSubgroup.sum_sum_add_eq H φ]
  congr 1
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.ofBijective _ hbij),
    fintype_card_matrix_zmod_two, Nat.cast_pow, Nat.cast_ofNat]

/-! ## Stage 4: averaging over the shift `T` and `S` together -/

/-- The switching sum after the two shift averages: every summand is an honest restriction of a
single Laplacian of the big space. -/
def SwFinal (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) : ℝ :=
  ∑ V₄ : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
        Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂),
    ∑ W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂),
      (if SwGuard t d V₄ W₄ then
        ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
            Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
          (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
            then (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
                ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
              ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
                (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
            else 0)
        else 0)

theorem ker_ShiftM₁ (t : Triple m n) : LinearMap.ker (ShiftM₁ t).mulVecLin = ⊥ := by
  simp only [ShiftM₁]
  rw [Matrix.mulVecLin_mul, LinearMap.ker_comp, ker_Ip, Submodule.comap_bot, ker_Ip]

theorem range_ShiftM₂ (t : Triple m n) : LinearMap.range (ShiftM₂ t).mulVecLin = ⊤ := by
  simp only [ShiftM₂]
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp, range_Qp, Submodule.map_top, range_Qp]

/-- **Stage 4**: summing `SwColl` over the shift `T` and averaging over `S` gives `SwFinal`. -/
theorem sum_SwColl_eq_SwFinal (t : Triple m n) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (d : ℕ) :
    (∑ T : Matrix (Fin m) (Fin n) 𝔽₂, SwColl t T f d) = SwFinal t f d := by
  unfold SwColl SwFinal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun V₄ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun W₄ _ => ?_)
  by_cases hg : SwGuard t d V₄ W₄
  · simp only [if_pos hg]
    have hcore : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          ∑ S : Matrix (Fin (Module.finrank 𝔽₂ (WrOf t)))
              (Fin ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) 𝔽₂,
            ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
                Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
              (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
                then (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift (T + ShiftM₁ t * S * ShiftM₂ t)
                      (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
                else 0)) =
        ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
            Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
          (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
            then (2 : ℝ) ^ (Module.finrank 𝔽₂ (WrOf t) *
                ((n - Module.finrank 𝔽₂ t.1) - Module.finrank 𝔽₂ (VrOf t))) *
              ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
                (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
            else 0) := by
      rw [sum_sum_add_mul_mul_zmod2 (ShiftM₁ t) (ShiftM₂ t) (ker_ShiftM₁ t) (range_ShiftM₂ t)
        (fun T' => ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
              Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
            (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
              then (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                  (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                  (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
              else 0))]
      have hL : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
                Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
              (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
                then (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift T (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
                else 0)) =
          ∑ p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
              Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂),
            (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
              then ∑ T' : Matrix (Fin m) (Fin n) 𝔽₂,
                (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                    (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                    (shift T' (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
              else 0) := by
        rw [Finset.sum_comm (f := fun (T : Matrix (Fin m) (Fin n) 𝔽₂)
          (p : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂) ×
              Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂)) =>
            (if Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
              then (l2sq (restr (Qp (liftV t.1 (liftV (VrOf t) V₄)))
                  (Ip (liftW t.2.1 (liftW (WrOf t) W₄)))
                  (shift T (lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f))))) ^ 2
              else 0))]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
        · simp only [if_pos hp]
        · simp only [if_neg hp, Finset.sum_const_zero]
      rw [hL, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) p.1 p.2
      · simp only [if_pos hp]
      · simp only [if_neg hp, mul_zero]
    rw [hcore]
  · simp [hg]

/-! ## Stage 5: the re-indexing `(V₄,W₄,p) ↦ p`

The `Fr`-conditions determine `V₂r = V₃ ⊔ Vr` and `W₂r = W₃ ⊓ Wr`, hence (through `Vco`/`Wco`)
the pair `(V₄,W₄)`; so the map `(V₄,W₄,p) ↦ p` is injective on the `Fr`-locus, and its image is
characterised by `V₃ ⊓ Vr = ⊥` and `W₃ ⊔ Wr = ⊤`. -/

/-- `Vco V₁r X = map (Qp V₁r) X`. -/
theorem Vco_eq_map_Qp {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (X : Submodule 𝔽₂ (Fin N → 𝔽₂)) :
    Vco V₁r X = Submodule.map (Qp V₁r).mulVecLin X := by
  rw [Vco, Qp_mulVecLin, ← Submodule.map_comp]

/-- `liftW W₁r (Wco W₁r X) = X ⊓ W₁r`. -/
theorem liftW_Wco {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    (X : Submodule 𝔽₂ (Fin M → 𝔽₂)) :
    liftW W₁r (Wco W₁r X) = X ⊓ W₁r := by
  rw [liftW, Ip_mulVecLin, Wco, Submodule.map_equiv_eq_comap_symm, ← Submodule.comap_comp]
  rw [LinearEquiv.symm_symm]
  rw [show (↑(ecW W₁r) : (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂) →ₗ[𝔽₂] ↥W₁r)
      = ↑(Module.finBasis 𝔽₂ ↥W₁r).equivFun.symm from rfl]
  rw [Submodule.map_comap_eq, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype, inf_comm]

/-- `liftV V₁r (Vco V₁r X) = X ⊔ V₁r`. -/
theorem liftV_Vco {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (X : Submodule 𝔽₂ (Fin N → 𝔽₂)) :
    liftV V₁r (Vco V₁r X) = X ⊔ V₁r := by
  rw [liftV, Vco_eq_map_Qp, Submodule.comap_map_eq, ker_Qp]

/-- The pair `(V₄,W₄)` is determined by `p` on the `Fr`-locus. -/
theorem Fr_V₄W₄_unique {m n : ℕ} (t : Triple m n)
    (V₄ V₄' : Submodule 𝔽₂ (Fin ((n - Module.finrank 𝔽₂ t.1) -
      Module.finrank 𝔽₂ (VrOf t)) → 𝔽₂))
    (W₄ W₄' : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ (WrOf t)) → 𝔽₂))
    (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂))
    (h : Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄) (liftW (WrOf t) W₄) V₃ W₃)
    (h' : Fr (VrOf t) (WrOf t) (liftV (VrOf t) V₄') (liftW (WrOf t) W₄') V₃ W₃) :
    V₄ = V₄' ∧ W₄ = W₄' := by
  have hV : liftV (VrOf t) V₄ = liftV (VrOf t) V₄' := by rw [← h.2.1, ← h'.2.1]
  have hW : liftW (WrOf t) W₄ = liftW (WrOf t) W₄' := by rw [← h.2.2.2.1, ← h'.2.2.2.1]
  refine ⟨?_, ?_⟩
  · rw [← Vco_liftV (VrOf t) V₄, ← Vco_liftV (VrOf t) V₄', hV]
  · rw [← Wco_liftW (WrOf t) W₄, ← Wco_liftW (WrOf t) W₄', hW]

/-- On the image of the `(V₄,W₄)`-projection, the `Fr`-conditions reduce to
`V₃ ⊓ Vr = ⊥` and `W₃ ⊔ Wr = ⊤`. -/
theorem Fr_exists {m n : ℕ} (t : Triple m n)
    (V₃ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂))
    (W₃ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ t.2.1) → 𝔽₂))
    (hV : V₃ ⊓ VrOf t = ⊥) (hW : W₃ ⊔ WrOf t = ⊤) :
    Fr (VrOf t) (WrOf t) (liftV (VrOf t) (Vco (VrOf t) (V₃ ⊔ VrOf t)))
      (liftW (WrOf t) (Wco (WrOf t) (W₃ ⊓ WrOf t))) V₃ W₃ := by
  refine ⟨hV, ?_, ?_, ?_, hW⟩
  · rw [liftV_Vco, sup_assoc, sup_idem]
  · rw [liftW_Wco]
    exact le_trans (inf_le_left : (W₃ ⊓ WrOf t) ⊓ WrOf t ≤ W₃ ⊓ WrOf t)
      (inf_le_left : W₃ ⊓ WrOf t ≤ W₃)
  · rw [liftW_Wco, inf_assoc, inf_idem]

end

end Submission.Grassmann