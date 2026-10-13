import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.isRpow_canon
import Submission.Work.WilC4.PBSyntax
import Submission.Work.WilC4.mul_pow_toNat_eq_iff
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize)

/-! ## 1. The ring atom `∃ w, w ≠ 0 ∧ w * w = t` -/

/-- The ring atom `∃ w, w ≠ 0 ∧ w * w = t`; the free variable `0` plays the role of `t`. -/
def isSqNeZeroAtom : ring.Formula (Fin 1) :=
  (BoundedFormula.not
      (Term.bdEqual (Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1))
        (0 : ring.Term (Fin 1 ⊕ Fin 1))) ⊓
    (Term.bdEqual
      (Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1) * Term.var (Sum.inr 0 : Fin 1 ⊕ Fin 1))
      (Term.var (Sum.inl 0 : Fin 1 ⊕ Fin 1)))).ex

/-- Realisation of `isSqNeZeroAtom`. -/
theorem isSqNeZeroAtom_realize {R : Type} [Field R] [Ring.CompatibleRing R] (u : R) :
    isSqNeZeroAtom.Realize ![u] ↔ ∃ w : R, w ≠ 0 ∧ w * w = u := by
  constructor
  · intro h
    simp only [isSqNeZeroAtom, Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      Ring.realize_mul, Ring.realize_zero, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_fin_one, Fin.snoc_zero, ne_eq] at h ⊢
    exact h
  · intro h
    simp only [isSqNeZeroAtom, Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual, BoundedFormula.realize_not,
      Ring.realize_mul, Ring.realize_zero, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_fin_one, Fin.snoc_zero, ne_eq] at h ⊢
    exact h

/-- Realisation of `isSqNeZeroAtom` after substituting a context variable for its free
variable. -/
theorem isSqNeZeroAtom_lift {M : Type} [Field M] [Ring.CompatibleRing M] [rexpL.Structure M]
    [(constantsOn ℝ).Structure M] {Ctx : Type} (f : Fin 1 → Ctx) (rw : Ctx → M) :
    (liftR f isSqNeZeroAtom).Realize rw ↔ ∃ w : M, w ≠ 0 ∧ w * w = rw (f 0) := by
  have h : rw ∘ f = ![rw (f 0)] := by funext i; fin_cases i; rfl
  rw [liftR_realize, h]
  exact isSqNeZeroAtom_realize _

/-! ## 2. The defining formula -/

section Form

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- The `LRc`-formula with free variables `(x, t) = (v 0, v 1)` asserting
`0 < x ∧ t ^ n * x ^ B = x ^ A ∧ (t = 0 ∨ ∃ w, w ≠ 0 ∧ w * w = t)`, where `A = p.toNat` and
`B = (-p).toNat`.  For `0 < x` this is exactly `IsRpow x (p / n) t`. -/
def isRpowForm (p : ℤ) (n : ℕ) : LRc.Formula (Fin 2) :=
  (liftR (fun _ : Fin 1 => (0 : Fin 2)) posStrictAtom) ⊓
    ((liftR (id : Fin 2 → Fin 2) (rpowAtom n (-p).toNat p.toNat)) ⊓
      ((liftR (fun _ : Fin 1 => (1 : Fin 2)) zeroAtom) ⊔
        (liftR (fun _ : Fin 1 => (1 : Fin 2)) isSqNeZeroAtom)))

theorem isRpowForm_realize (hM : M ⊨ TR) (p : ℤ) (n : ℕ) (v : Fin 2 → M) :
    (isRpowForm p n).Realize v ↔
      0 < v 0 ∧ (v 1 ^ n * v 0 ^ (-p).toNat = v 0 ^ p.toNat ∧
        (v 1 = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = v 1)) := by
  have hsq := Work.WilC2.model_exists_sq hM
  have hps : (liftR (fun _ : Fin 1 => (0 : Fin 2)) posStrictAtom).Realize v ↔ 0 < v 0 :=
    posStrictAtom_lift (fun _ : Fin 1 => (0 : Fin 2)) v hsq
  have hrp : (liftR (id : Fin 2 → Fin 2) (rpowAtom n (-p).toNat p.toNat)).Realize v ↔
      v 1 ^ n * v 0 ^ (-p).toNat = v 0 ^ p.toNat :=
    rpowAtom_lift n (-p).toNat p.toNat (id : Fin 2 → Fin 2) v
  have hz : (liftR (fun _ : Fin 1 => (1 : Fin 2)) zeroAtom).Realize v ↔ v 1 = 0 :=
    zeroAtom_lift (fun _ : Fin 1 => (1 : Fin 2)) v
  have hs : (liftR (fun _ : Fin 1 => (1 : Fin 2)) isSqNeZeroAtom).Realize v ↔
      ∃ w : M, w ≠ 0 ∧ w * w = v 1 :=
    isSqNeZeroAtom_lift (fun _ : Fin 1 => (1 : Fin 2)) v
  simp only [isRpowForm, Formula.realize_inf, Formula.realize_sup, hps, hrp, hz, hs]

end Form

/-! ## 3. The target -/

theorem isRpow_definable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR) (p : ℤ) (n : ℕ) (hn : 0 < n) : (∅ : Set M).Definable₂ WilkiesDesign.CG.LRc {xt : M × M | 0 < xt.1 ∧ Work.WilC4.IsRpow xt.1 ((p : ℚ) / (n : ℚ)) xt.2} := by
  have key : ∀ v : Fin 2 → M, (0 < v 0 ∧ IsRpow (v 0) ((p : ℚ) / (n : ℚ)) (v 1)) ↔
      (0 < v 0 ∧ (v 1 ^ n = v 0 ^ p ∧ (v 1 = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = v 1))) := by
    intro v
    constructor
    · rintro ⟨hx, hI⟩
      exact ⟨hx, by
        simpa [pow_two] using (isRpow_canon (p := p) (n := n) hn hx).mp hI⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, (isRpow_canon (p := p) (n := n) hn hx).mpr
        ⟨h1, by simpa [pow_two] using h2⟩⟩
  have key2 : ∀ v : Fin 2 → M,
      (0 < v 0 ∧ (v 1 ^ n = v 0 ^ p ∧ (v 1 = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = v 1))) ↔
      (0 < v 0 ∧ (v 1 ^ n * v 0 ^ (-p).toNat = v 0 ^ p.toNat ∧
        (v 1 = 0 ∨ ∃ w : M, w ≠ 0 ∧ w * w = v 1))) := by
    intro v
    constructor
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, (mul_pow_toNat_eq_iff (ne_of_gt hx) p n).mpr h1, h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨hx, (mul_pow_toNat_eq_iff (ne_of_gt hx) p n).mp h1, h2⟩
  have hDef : (∅ : Set M).Definable LRc
      {v : Fin 2 → M | 0 < v 0 ∧ IsRpow (v 0) ((p : ℚ) / (n : ℚ)) (v 1)} := by
    refine Set.empty_definable_iff.mpr ⟨isRpowForm p n, ?_⟩
    ext v
    show (0 < v 0 ∧ IsRpow (v 0) ((p : ℚ) / (n : ℚ)) (v 1)) ↔
      (isRpowForm p n).Realize v
    exact ((key v).trans (key2 v)).trans (isRpowForm_realize hM p n v).symm
  unfold Set.Definable₂
  show (∅ : Set M).Definable LRc
    {v : Fin 2 → M | 0 < v 0 ∧ IsRpow (v 0) ((p : ℚ) / (n : ℚ)) (v 1)}
  exact hDef

end Work.WilC4
