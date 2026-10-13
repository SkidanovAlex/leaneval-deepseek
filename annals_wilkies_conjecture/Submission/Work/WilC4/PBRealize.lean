import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Square
import Submission.Work.WilC4.PBSyntax

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize leF leF_realize leF_realize_le ringToLRc)

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-! ## 4. Realisation of the sentence -/

/-- `φ` at the point `(x, y)`, with the `Gam`-assignment `ψ`. -/
def phiV {M : Type} [LRc.Structure M] (n k : ℕ) (φ : LRc.Formula (Fin n ⊕ Fin (k + 2)))
    (ψ : Gam n k → M) (x y : M) : Prop :=
  φ.Realize (Sum.elim (fun i => ψ (gA i)) (Fin.cases x (Fin.cases y (fun j => ψ (gC j)))))

theorem phiV_phiVal {M : Type} [LRc.Structure M] {n k : ℕ}
    (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (v0 : Empty → M) (aa : Fin n → M)
    (cc : Fin k → M) (x y : M) :
    phiV n k φ (fun b => Sum.elim (Sum.elim v0 aa) cc b) x y ↔ phiVal n k φ aa cc x y := by
  have h : Sum.elim (fun i => (fun b => Sum.elim (Sum.elim v0 aa) cc b) (gA i))
      (Fin.cases x (Fin.cases y (fun j => (fun b => Sum.elim (Sum.elim v0 aa) cc b) (gC j))))
      = Sum.elim aa (Fin.cases x (Fin.cases y cc)) := by
    funext v
    rcases v with i | j
    · rfl
    · refine Fin.cases ?_ ?_ j
      · rfl
      · intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j'
          rfl
  unfold phiV phiVal
  rw [h]

theorem phiV_phiVal' {M : Type} [LRc.Structure M] {n k : ℕ}
    (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (v0 : Empty → M) (aa : Fin n → M)
    (cc : Fin k → M) (x y : M) :
    phiV n k φ (Sum.elim (Sum.elim v0 aa) cc) x y ↔ phiVal n k φ aa cc x y := by
  rw [show (Sum.elim (Sum.elim v0 aa) cc : Gam n k → M)
      = (fun b => Sum.elim (Sum.elim v0 aa) cc b) from rfl]
  exact phiV_phiVal φ v0 aa cc x y

theorem exists_fin1_iff {M : Type} {Q : (Fin 1 → M) → Prop} :
    (∃ f : Fin 1 → M, Q f) ↔ ∃ x : M, Q (fun _ => x) :=
  ⟨fun ⟨f, hf⟩ => ⟨f 0, by
      have hf' : (fun _ : Fin 1 => f 0) = f := funext fun i => by fin_cases i; rfl
      rw [hf']; exact hf⟩,
   fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩

theorem forall_fin1_iff {M : Type} {Q : (Fin 1 → M) → Prop} :
    (∀ f : Fin 1 → M, Q f) ↔ ∀ x : M, Q (fun _ => x) :=
  ⟨fun h x => h (fun _ => x),
   fun h f => by
     have hf : (fun _ : Fin 1 => f 0) = f := funext fun i => by fin_cases i; rfl
     rw [← hf]
     exact h (f 0)⟩

theorem forall_fin2_iff {M : Type} {Q : (Fin 2 → M) → Prop} :
    (∀ f : Fin 2 → M, Q f) ↔ ∀ x y : M, Q ![x, y] :=
  ⟨fun h x y => h ![x, y],
   fun h f => by
     have hf : (![f 0, f 1] : Fin 2 → M) = f := funext fun i => by fin_cases i <;> rfl
     rw [← hf]
     exact h (f 0) (f 1)⟩

theorem exists_fin2_iff {M : Type} {Q : (Fin 2 → M) → Prop} :
    (∃ f : Fin 2 → M, Q f) ↔ ∃ x y : M, Q ![x, y] :=
  ⟨fun ⟨f, hf⟩ => ⟨f 0, f 1, by
      have hf' : (![f 0, f 1] : Fin 2 → M) = f := funext fun i => by fin_cases i <;> rfl
      rw [hf']; exact hf⟩,
   fun ⟨x, y, h⟩ => ⟨![x, y], h⟩⟩

theorem eqAtom_lift2 {Ctx : Type} (u v : Ctx) (rw : Ctx → M) :
    (liftR ![u, v] eqAtom).Realize rw ↔ rw u = rw v := by
  rw [eqAtom_lift]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem zeroAtom_lift2 {Ctx : Type} (u : Ctx) (rw : Ctx → M) :
    (liftR ![u] zeroAtom).Realize rw ↔ rw u = 0 := by
  rw [zeroAtom_lift]
  simp [Matrix.cons_val_fin_one, Matrix.cons_val_zero]

theorem neZeroAtom_lift2 {Ctx : Type} (u : Ctx) (rw : Ctx → M) :
    (liftR ![u] neZeroAtom).Realize rw ↔ rw u ≠ 0 := by
  rw [neZeroAtom_lift]
  simp [Matrix.cons_val_fin_one, Matrix.cons_val_zero]

theorem posStrictAtom_lift2 {Ctx : Type} (u : Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR ![u] posStrictAtom).Realize rw ↔ 0 < rw u := by
  rw [posStrictAtom_lift _ _ hsq]
  simp [Matrix.cons_val_fin_one, Matrix.cons_val_zero]

theorem leF_lift2 {Ctx : Type} (u v : Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR ![u, v] leF).Realize rw ↔ rw u ≤ rw v := by
  rw [leF_lift _ _ hsq]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem sqAtom_lift2 {Ctx : Type} (u w : Ctx) (rw : Ctx → M) :
    (liftR ![u, w] sqAtom).Realize rw ↔ rw w * rw w = rw u := by
  rw [sqAtom_lift]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem rpowAtom_lift2 {Ctx : Type} (q : ℚ) (u v : Ctx) (rw : Ctx → M) :
    (liftR ![u, v] (rpowAtom q.den ((-q.num).toNat) q.num.toNat)).Realize rw ↔
      rw v ^ q.den * rw u ^ ((-q.num).toNat) = rw u ^ q.num.toNat := by
  rw [rpowAtom_lift]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem absLeAtom_lift2 {Ctx : Type} (y a t e : Ctx) (rw : Ctx → M)
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (liftR ![y, a, t, e] absLeAtom).Realize rw ↔ |rw y - rw a * rw t| ≤ rw e * rw t := by
  rw [absLeAtom_lift _ _ hsq]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

theorem phiG_realize {n k : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) {Ctx : Type}
    (inj : Gam n k → Ctx) (xt yt : Ctx) (rw : Ctx → M) :
    (phiG n k φ inj xt yt).Realize rw ↔
      phiV n k φ (fun g => rw (inj g)) (rw xt) (rw yt) := by
  rw [phiG, Formula.realize_relabel]
  have h : rw ∘ (Sum.elim (fun i => inj (gA i)) (Fin.cases xt (Fin.cases yt
        (fun j => inj (gC j)))))
      = Sum.elim (fun i => rw (inj (gA i))) (Fin.cases (rw xt) (Fin.cases (rw yt)
        (fun j => rw (inj (gC j))))) := by
    funext v
    rcases v with i | j
    · rfl
    · refine Fin.cases ?_ ?_ j
      · rfl
      · intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j'
          rfl
  rw [h]
  rfl

theorem GC_realize' {n k : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (rw : GamG n k → M) :
    (GC n k φ).Realize rw ↔
      (phiV n k φ (fun g => rw (gG g)) (rw gX) (rw gY) →
        phiV n k φ (fun g => rw (gG g)) (rw gX) (rw gY') → rw gY = rw gY') := by
  rw [GC, Formula.realize_imp, Formula.realize_imp, phiG_realize, phiG_realize, eqAtom_lift2]

theorem graphAll_realize' {n k : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2)))
    (rw : Gam n k → M) :
    (graphAll n k φ).Realize rw ↔
      ∀ x y y' : M, phiV n k φ rw x y → phiV n k φ rw x y' → y = y' := by
  rw [graphAll, Formula.realize_iAlls]
  constructor
  · intro h x y y' h1 h2
    have h3 := h ![x, y, y']
    rw [GC_realize',
      show (fun g : Gam n k => (Sum.elim rw ![x, y, y']) (gG g)) = rw from funext fun g => rfl]
      at h3
    have h3' : phiV n k φ rw x y → phiV n k φ rw x y' → y = y' := by
      simpa [gX, gY, gY', Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h3
    exact h3' h1 h2
  · intro h i
    rw [GC_realize',
      show (fun g : Gam n k => (Sum.elim rw i) (gG g)) = rw from funext fun g => rfl]
    simp only [gX, gY, gY', Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    simpa using h (i 0) (i 1) (i 2)

theorem BODYQ_realize' {n k : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (q : ℚ)
    (rw : Con n k → M) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (BODYQ n k φ q).Realize rw ↔
      (rw cAl = 0 ∧ (0 < rw cEp → 0 < rw cR ∧ (rw cR ≤ rw cX →
            (phiV n k φ (fun g => rw (cG g)) (rw cX) (rw cY) → rw cY = 0))))
        ∨ (rw cAl ≠ 0 ∧ (0 < rw cEp → 0 < rw cR ∧ (rw cR ≤ rw cX →
            phiV n k φ (fun g => rw (cG g)) (rw cX) (rw cY) →
              ((rw cT) ^ q.den * (rw cX) ^ ((-q.num).toNat) = (rw cX) ^ q.num.toNat ∧
                ((rw cW) * (rw cW) = rw cT ∧
                  |rw cY - rw cAl * rw cT| ≤ rw cEp * rw cT))))) := by
  have hps : ∀ u : Con n k, (liftR ![u] posStrictAtom).Realize rw ↔ 0 < rw u :=
    fun u => posStrictAtom_lift2 u rw hsq
  have hle : ∀ u v : Con n k, (liftR ![u, v] leF).Realize rw ↔ rw u ≤ rw v :=
    fun u v => leF_lift2 u v rw hsq
  simp only [BODYQ, b1, b2, posStrictL, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_imp, zeroAtom_lift2, neZeroAtom_lift2, hps, hle, phiG_realize,
    rpowAtom_lift2, sqAtom_lift2, absLeAtom_lift2 _ _ _ _ rw hsq]

theorem ConclOf_realize' {n k : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2))) (q : ℚ)
    (v : Gam n k → M) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (ConclOf n k φ q).Realize v ↔
      ∃ (α : M),
        (α = 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
            phiV n k φ v x y → y = 0))
        ∨ (α ≠ 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
            phiV n k φ v x y →
            ∃ t : M, ∃ w : M, t ^ q.den * x ^ ((-q.num).toNat) = x ^ q.num.toNat ∧
              (w * w = t ∧ |y - α * t| ≤ ε * t))) := by
  have hBQ : ∀ (rw : Con n k → M),
      (BODYQ n k φ q).Realize rw ↔
        (rw cAl = 0 ∧ (0 < rw cEp → 0 < rw cR ∧ (rw cR ≤ rw cX →
              (phiV n k φ (fun g => rw (cG g)) (rw cX) (rw cY) → rw cY = 0))))
          ∨ (rw cAl ≠ 0 ∧ (0 < rw cEp → 0 < rw cR ∧ (rw cR ≤ rw cX →
              phiV n k φ (fun g => rw (cG g)) (rw cX) (rw cY) →
                ((rw cT) ^ q.den * (rw cX) ^ ((-q.num).toNat) = (rw cX) ^ q.num.toNat ∧
                  ((rw cW) * (rw cW) = rw cT ∧
                    |rw cY - rw cAl * rw cT| ≤ rw cEp * rw cT))))) :=
    fun rw => BODYQ_realize' φ q rw hsq
  simp only [ConclOf, Formula.realize_iExs, Formula.realize_iAlls]
  simp only [hBQ, cAl, cEp, cR, cX, cY, cT, cW, cG, gA, gC, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, phiV, exists_fin1_iff, forall_fin1_iff, forall_fin2_iff,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨α, h⟩
    refine ⟨α, ?_⟩
    by_cases hα : α = 0
    · left
      refine ⟨hα, fun ε hε => ?_⟩
      obtain ⟨R, hR⟩ := h ε
      have hR0 : 0 < R := by
        obtain ⟨t, w, h1 | h2⟩ := hR 0 0
        · exact (h1.2 hε).1
        · exact absurd hα h2.1
      refine ⟨R, hR0, fun x y hx hφ => ?_⟩
      obtain ⟨t, w, h1 | h2⟩ := hR x y
      · exact (h1.2 hε).2 hx hφ
      · exact absurd hα h2.1
    · right
      refine ⟨hα, fun ε hε => ?_⟩
      obtain ⟨R, hR⟩ := h ε
      have hR0 : 0 < R := by
        obtain ⟨t, w, h1 | h2⟩ := hR 0 0
        · exact absurd h1.1 hα
        · exact (h2.2 hε).1
      refine ⟨R, hR0, fun x y hx hφ => ?_⟩
      obtain ⟨t, w, h1 | h2⟩ := hR x y
      · exact absurd h1.1 hα
      · obtain ⟨ht, hw, ha⟩ := (h2.2 hε).2 hx hφ
        exact ⟨t, w, ht, hw, ha⟩
  · rintro ⟨α, h | h⟩
    · obtain ⟨hα, h⟩ := h
      refine ⟨α, fun ε => ?_⟩
      by_cases hε0 : 0 < ε
      · obtain ⟨R, hR, hprop⟩ := h ε hε0
        refine ⟨R, fun x y => ?_⟩
        by_cases hx : R ≤ x
        · by_cases hφ : phiV n k φ v x y
          · exact ⟨0, 0, Or.inl ⟨hα, fun _ => ⟨hR, fun _ _ => hprop x y hx hφ⟩⟩⟩
          · exact ⟨0, 0, Or.inl ⟨hα, fun _ => ⟨hR, fun _ hφ' => absurd hφ' hφ⟩⟩⟩
        · exact ⟨0, 0, Or.inl ⟨hα, fun _ => ⟨hR, fun hx' _ => absurd hx' hx⟩⟩⟩
      · exact ⟨0, fun x y => ⟨0, 0, Or.inl ⟨hα, fun hε' => absurd hε' hε0⟩⟩⟩
    · obtain ⟨hα, h⟩ := h
      refine ⟨α, fun ε => ?_⟩
      by_cases hε0 : 0 < ε
      · obtain ⟨R, hR, hprop⟩ := h ε hε0
        refine ⟨R, fun x y => ?_⟩
        by_cases hx : R ≤ x
        · by_cases hφ : phiV n k φ v x y
          · obtain ⟨t, w, ht, hw, ha⟩ := hprop x y hx hφ
            exact ⟨t, w, Or.inr ⟨hα, fun _ => ⟨hR, fun _ _ => ⟨ht, hw, ha⟩⟩⟩⟩
          · exact ⟨0, 0, Or.inr ⟨hα, fun _ => ⟨hR, fun _ hφ' => absurd hφ' hφ⟩⟩⟩
        · exact ⟨0, 0, Or.inr ⟨hα, fun _ => ⟨hR, fun hx' _ => absurd hx' hx⟩⟩⟩
      · exact ⟨0, fun x y => ⟨0, 0, Or.inr ⟨hα, fun hε' => absurd hε' hε0⟩⟩⟩

theorem BODY_realize' {n k N : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2)))
    (qs : Fin N → ℚ) (rw : Gam n k → M) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (BODY n k N φ qs).Realize rw ↔
      ((∀ x y y' : M, phiV n k φ rw x y → phiV n k φ rw x y' → y = y') →
        ∃ (i : Fin N) (α : M),
          (α = 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
              phiV n k φ rw x y → y = 0))
          ∨ (α ≠ 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
              phiV n k φ rw x y →
              ∃ t : M, ∃ w : M, t ^ (qs i).den * x ^ ((-(qs i).num).toNat) = x ^ (qs i).num.toNat ∧
                (w * w = t ∧ |y - α * t| ≤ ε * t)))) := by
  rw [BODY, Formula.realize_imp, Formula.realize_iSup, graphAll_realize']
  constructor
  · rintro h hg
    obtain ⟨i, hi⟩ := h hg
    refine ⟨i, ?_⟩
    rw [ConclOf_realize' φ (qs i) rw hsq] at hi
    exact hi
  · rintro h hg
    obtain ⟨i, hi⟩ := h hg
    refine ⟨i, ?_⟩
    rw [ConclOf_realize' φ (qs i) rw hsq]
    exact hi

theorem pbSent_realize {n k N : ℕ} (φ : LRc.Formula (Fin n ⊕ Fin (k + 2)))
    (qs : Fin N → ℚ) (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) :
    (M ⊨ pbSent n k N φ qs) ↔ PBGood n k N φ qs M := by
  have hB : ∀ (rw : Gam n k → M),
      (BODY n k N φ qs).Realize rw ↔
        ((∀ x y y' : M, phiV n k φ rw x y → phiV n k φ rw x y' → y = y') →
          ∃ (i : Fin N) (α : M),
            (α = 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
                phiV n k φ rw x y → y = 0))
            ∨ (α ≠ 0 ∧ (∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
                phiV n k φ rw x y →
                ∃ t : M, ∃ w : M, t ^ (qs i).den * x ^ ((-(qs i).num).toNat) = x ^ (qs i).num.toNat ∧
                  (w * w = t ∧ |y - α * t| ≤ ε * t)))) :=
    fun rw => BODY_realize' φ qs rw hsq
  rw [PBGood, pbSent, Sentence.Realize]
  simp only [Formula.realize_iAlls, hB, phiV_phiVal, phiV_phiVal']

end Work.WilC4
