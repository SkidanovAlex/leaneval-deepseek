import Mathlib
import Submission.Work.WilVP.IsoBallSyntax
import Submission.Work.WilVP.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilVP

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize)
open Work.WilC4

/-! ## 0. Helper realisation lemmas for the ring atoms

`isoBallLtAtom`, `isoAbsLeAtom`, `sqLeAtom` are realised w.r.t. the matrix `![⋯]` of the
variables; these are the lifted versions used at the various contexts of the sentence. -/

theorem relabel_vec3 {L : FirstOrder.Language} {M : Type} [L.Structure M] {Ctx : Type}
    (u v w : Ctx) (rw : Ctx → M) (F : L.Formula (Fin 3)) :
    (Formula.relabel ![u, v, w] F).Realize rw ↔ F.Realize ![rw u, rw v, rw w] := by
  rw [Formula.realize_relabel]
  have h : rw ∘ ![u, v, w] = ![rw u, rw v, rw w] := by funext i; fin_cases i <;> rfl
  rw [h]

theorem sqLeAtom_lift2 {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {Ctx : Type} (u v : Ctx) (rw : Ctx → M) :
    (liftR ![u, v] sqLeAtom).Realize rw ↔ rw u * rw u ≤ rw v * rw v := by
  have hh : rw ∘ ![u, v] = ![rw u, rw v] := by funext i; fin_cases i <;> rfl
  rw [liftR_realize, hh, sqLeAtom_realize hsq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem isoAbsLeAtom_lift2 {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (N : ℕ) {Ctx : Type} (u v : Ctx) (rw : Ctx → M) :
    (liftR ![u, v] (isoAbsLeAtom N)).Realize rw ↔ |rw u| ≤ (N : M) * |rw v| := by
  have hh : rw ∘ ![u, v] = ![rw u, rw v] := by funext i; fin_cases i <;> rfl
  rw [liftR_realize, hh, isoAbsLeAtom_realize hsq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem isoBallLtAtom_lift3 {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (N : ℕ) {Ctx : Type} (x y p : Ctx) (rw : Ctx → M) :
    (liftR ![x, y, p] (isoBallLtAtom N)).Realize rw ↔
      (N : M) * |rw y - rw x| < |rw x - rw p| := by
  have hh : rw ∘ ![x, y, p] = ![rw x, rw y, rw p] := by funext i; fin_cases i <;> rfl
  rw [liftR_realize, hh, isoBallLtAtom_realize hsq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-! ## 1. The clean fibre predicate -/

/-- The fibre-level content of the iso-ball clause (the second conjunct of `IsoBallProp` at a
fixed value `c` of the parameters): the `ψ`-fibre has at most `N` points, and on the ball of
radius `dist(x, P_c)/N` the value `|F_c|` changes at most by the factor `N`. -/
def IsoFibGood (k N : ℕ) (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1)))
    (M : Type) [LRc.Structure M] [Field M] [LinearOrder M] (c : Fin k → M) : Prop :=
  {x : M | upsiVal k ψ M c x}.encard ≤ N ∧
    ∀ x y₀ y : M, uphiVal k φ M c x y₀ → y₀ ≠ 0 →
      (∀ p : M, upsiVal k ψ M c p → (N : M) * |y - x| < |x - p|) →
      ∃ y₁ : M, uphiVal k φ M c y y₁ ∧
        |y₁| ≤ (N : M) * |y₀| ∧ |y₀| ≤ (N : M) * |y₁|

/-! ## 2. Realisation of the bounded-fibre hypothesis -/

theorem uBddB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (rw : UCBXY k → M) :
    (uBddB k φ).Realize rw ↔
      (uphiVal k φ M (fun j => rw (ucbxyC j)) (rw ucbxyX) (rw ucbxyY) →
        rw ucbxyX * rw ucbxyX ≤ rw ucbxyR * rw ucbxyR) := by
  rw [uBddB, Formula.realize_imp, uphiG_realize, sqLeAtom_lift2 hsq ucbxyX ucbxyR rw]
  exact Iff.rfl

theorem uBdd_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (rw : UC0 k → M) :
    (uBdd k φ).Realize rw ↔
      ∃ R : M, ∀ x y : M, uphiVal k φ M (fun j => rw (ucC j)) x y → x * x ≤ R * R := by
  rw [uBdd, Formula.realize_iExs]
  simp only [Formula.realize_iAlls]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R 0, fun x y hxy => ?_⟩
    have h := hR ![x, y]
    rw [uBddB_realize hsq] at h
    exact h hxy
  · rintro ⟨R, hR⟩
    refine ⟨fun _ => R, fun b => ?_⟩
    rw [uBddB_realize hsq]
    exact fun hxy => hR (b 0) (b 1) hxy

theorem uBdd_all_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (v : Empty → M) :
    ((Formula.iAlls (Fin k) (uBdd k φ)) : LRc.Formula Empty).Realize v ↔
      ∀ c : Fin k → M, ∃ R : M, ∀ x y : M, uphiVal k φ M c x y → |x| ≤ R := by
  rw [Formula.realize_iAlls]
  constructor
  · intro h c
    have h1 := h c
    rw [uBdd_realize hsq] at h1
    exact (exists_sqBound_iff_absBound _).mp h1
  · intro h c
    rw [uBdd_realize hsq]
    exact (exists_sqBound_iff_absBound _).mpr (h c)

/-! ## 3. Realisation of the ball hypothesis -/

theorem uBallB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (rw : UCIP k → M) :
    (uBallB k N ψ).Realize rw ↔
      (upsiVal k ψ M (fun j => rw (ucipC j)) (rw ucipP) →
        (N : M) * |rw ucipY - rw ucipX| < |rw ucipX - rw ucipP|) := by
  rw [uBallB, Formula.realize_imp, upsiG_realize,
    isoBallLtAtom_lift3 hsq N ucipX ucipY ucipP rw]
  exact Iff.rfl

theorem uBall_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (rw : UCI k → M) :
    (uBall k N ψ).Realize rw ↔
      ∀ p : M, upsiVal k ψ M (fun j => rw (uciC j)) p →
        (N : M) * |rw uciY - rw uciX| < |rw uciX - p| := by
  rw [uBall, Formula.realize_iAlls]
  constructor
  · intro h p
    have h3 := h (fun _ : Fin 1 => p)
    rw [uBallB_realize hsq] at h3
    exact h3
  · intro h b
    rw [uBallB_realize hsq]
    exact h (b 0)

/-! ## 4. Realisation of the witness and the iso clause -/

theorem uWitBody_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) (φ : LRc.Formula (Fin (k + 2)))
    (rw : UCIY k → M) :
    (uWitBody k N φ).Realize rw ↔
      (uphiVal k φ M (fun j => rw (uciyC j)) (rw uciyY) (rw uciyY1) ∧
        |rw uciyY1| ≤ (N : M) * |rw uciyY0| ∧ |rw uciyY0| ≤ (N : M) * |rw uciyY1|) := by
  rw [uWitBody, Formula.realize_inf, Formula.realize_inf, uphiG_realize,
    isoAbsLeAtom_lift2 hsq N uciyY1 uciyY0 rw, isoAbsLeAtom_lift2 hsq N uciyY0 uciyY1 rw]
  exact Iff.rfl

theorem uIsoBody_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (rw : UCI k → M) :
    (uIsoBody k N φ ψ).Realize rw ↔
      (uphiVal k φ M (fun j => rw (uciC j)) (rw uciX) (rw uciY0) → rw uciY0 ≠ 0 →
        (uBall k N ψ).Realize rw →
        ∃ y₁ : M, uphiVal k φ M (fun j => rw (uciC j)) (rw uciY) y₁ ∧
          |y₁| ≤ (N : M) * |rw uciY0| ∧ |rw uciY0| ≤ (N : M) * |y₁|) := by
  rw [uIsoBody, Formula.realize_imp, Formula.realize_imp, Formula.realize_imp, uphiG_realize,
    neZeroAtom_lift2, Formula.realize_iExs]
  constructor
  · intro h h1 h2 h3
    obtain ⟨i, hi⟩ := h h1 h2 h3
    exact ⟨i 0, (uWitBody_realize (M := M) hsq k N φ (Sum.elim rw i)).mp hi⟩
  · intro h h1 h2 h3
    obtain ⟨y₁, hy⟩ := h h1 h2 h3
    exact ⟨fun _ => y₁,
      (uWitBody_realize (M := M) hsq k N φ (Sum.elim rw (fun _ => y₁))).mpr hy⟩

/-! ## 5. Realisation of the iso clause at fixed parameters -/

theorem uIsoAll_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (rw : UC0 k → M) :
    (uIsoAll k N φ ψ).Realize rw ↔ IsoFibGood k N φ ψ M (fun j => rw (ucC j)) := by
  rw [uIsoAll, Formula.realize_inf, ucard_realize_encard, Formula.realize_iAlls]
  constructor
  · rintro ⟨hcard, hiso⟩
    refine ⟨hcard, ?_⟩
    intro x y₀ y hφ hy0 hball
    have h3 := hiso ![x, y₀, y]
    rw [uIsoBody_realize hsq, uBall_realize hsq] at h3
    exact h3 hφ hy0 hball
  · rintro ⟨hcard, hiso⟩
    refine ⟨hcard, ?_⟩
    intro b
    rw [uIsoBody_realize hsq, uBall_realize hsq]
    exact fun hφ hy0 hball => hiso (b 0) (b 1) (b 2) hφ hy0 hball

theorem uIsoAll_all_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (v : Empty → M) :
    ((Formula.iAlls (Fin k) (uIsoAll k N φ ψ)) : LRc.Formula Empty).Realize v ↔
      ∀ c : Fin k → M, IsoFibGood k N φ ψ M c := by
  rw [Formula.realize_iAlls]
  constructor
  · intro h c
    have h1 := h c
    rw [uIsoAll_realize hsq] at h1
    exact h1
  · intro h c
    rw [uIsoAll_realize hsq]
    exact h c

/-! ## 6. The semantic characterisation -/

theorem isoSentRealize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (φ : WilkiesDesign.CG.LRc.Formula (Fin (k + 2)))
    (ψ : WilkiesDesign.CG.LRc.Formula (Fin (k + 1))) :
    (M ⊨ Work.WilVP.isoSent k N φ ψ) ↔ Work.WilVP.IsoBallGood k N φ ψ M := by
  rw [isoSent, Sentence.Realize, Formula.realize_imp, Formula.realize_imp,
    uGraphAll_all_realize, uBdd_all_realize hsq, uIsoAll_all_realize hsq]
  exact Iff.rfl

end Work.WilVP
