/-
  WilC4/ULPMRealize : the realisation lemmas for the ULPM sentence `WilC4/ULPMSyntax.lean`,
  ending with the semantic characterisation `ulpmSent_realize`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMSyntax
import Submission.Work.WilC4.encardLePigeonhole

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR liftR_realize leF leF_realize leF_realize_le)

/-! ## 7. Realisation lemmas -/

/-- `f ∘ Fin.cases a g = Fin.cases (f a) (f ∘ g)`. -/
theorem comp_finCases {α β : Type*} {n : ℕ} (f : α → β) (a : α) (g : Fin n → α) :
    f ∘ Fin.cases a g = Fin.cases (f a) (f ∘ g) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-- Realisation of a formula relabelled along `![u, v]`. -/
theorem relabel_vec2 {L : FirstOrder.Language} {M : Type} [L.Structure M] {Ctx : Type}
    (u v : Ctx) (rw : Ctx → M) (ψ : L.Formula (Fin 2)) :
    (Formula.relabel ![u, v] ψ).Realize rw ↔ ψ.Realize ![rw u, rw v] := by
  rw [Formula.realize_relabel]
  have h : rw ∘ ![u, v] = ![rw u, rw v] := by funext i; fin_cases i <;> rfl
  rw [h]

/-- `IsRpow x q t` forces `t ≥ 0`. -/
theorem isRpow_nonneg {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x t : M} {q : ℚ} (h : IsRpow x q t) : 0 ≤ t := by
  obtain ⟨p, n, hn, hq, hpow, hsq⟩ := h
  rcases hsq with h | ⟨w, hw, hw2⟩
  · rw [h]
  · rw [← hw2, pow_two]; exact mul_self_nonneg w

theorem uphiG_realize {M : Type} [LRc.Structure M] {Ctx : Type} (k : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (cc : Fin k → Ctx) (xt yt : Ctx) (rw : Ctx → M) :
    (uphiG k φ cc xt yt).Realize rw ↔
      φ.Realize (Fin.cases (rw xt) (Fin.cases (rw yt) (fun j => rw (cc j)))) := by
  rw [uphiG, Formula.realize_relabel]
  have h : rw ∘ Fin.cases xt (Fin.cases yt cc) =
      Fin.cases (rw xt) (Fin.cases (rw yt) (fun j => rw (cc j))) := by
    rw [comp_finCases, comp_finCases]; rfl
  rw [h]

theorem upsiG_realize {M : Type} [LRc.Structure M] {Ctx : Type} (k : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (cc : Fin k → Ctx) (bt : Ctx) (rw : Ctx → M) :
    (upsiG k ψ cc bt).Realize rw ↔ ψ.Realize (Fin.cases (rw bt) (fun j => rw (cc j))) := by
  rw [upsiG, Formula.realize_relabel]
  have h : rw ∘ Fin.cases bt cc = Fin.cases (rw bt) (fun j => rw (cc j)) := by
    rw [comp_finCases]; rfl
  rw [h]

theorem uGC_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (rw : UCG k → M) :
    (uGC k φ).Realize rw ↔
      (uphiVal k φ M (fun j => rw (ucgC j)) (rw ucgX) (rw ucgY) →
        uphiVal k φ M (fun j => rw (ucgC j)) (rw ucgX) (rw ucgY') → rw ucgY = rw ucgY') := by
  rw [uGC, Formula.realize_imp, Formula.realize_imp, uphiG_realize, uphiG_realize,
    eqAtom_lift2]
  rfl

theorem uGraphAll_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (rw : UC0 k → M) :
    (uGraphAll k φ).Realize rw ↔
      ∀ b : Fin 3 → M, (uphiVal k φ M (fun j => rw (ucC j)) (b 0) (b 1) →
        uphiVal k φ M (fun j => rw (ucC j)) (b 0) (b 2) → b 1 = b 2) := by
  rw [uGraphAll, Formula.realize_iAlls]
  constructor
  · intro h b
    have h3 := h b
    rw [uGC_realize] at h3
    simp only [ucgX, ucgY, ucgY', ucgC, ucC, Sum.elim_inl, Sum.elim_inr] at h3
    exact h3
  · intro h b
    rw [uGC_realize]
    simp only [ucgX, ucgY, ucgY', ucgC, ucC, Sum.elim_inl, Sum.elim_inr]
    exact h b

theorem uGraphAll_all_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (v : Empty → M) :
    ((Formula.iAlls (Fin k) (uGraphAll k φ)) : LRc.Formula Empty).Realize v ↔
      ∀ (c : Fin k → M) (x y y' : M), uphiVal k φ M c x y → uphiVal k φ M c x y' → y = y' := by
  rw [Formula.realize_iAlls]
  constructor
  · intro h c x y y' h1 h2
    have h3 := h c
    rw [uGraphAll_realize] at h3
    simp only [ucC, Sum.elim_inr] at h3
    exact h3 ![x, y, y'] h1 h2
  · intro h c
    rw [uGraphAll_realize]
    intro b h1 h2
    exact h c (b 0) (b 1) (b 2) h1 h2

/-! ## 8. Realisation of the cardinality clause -/

theorem ucardB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) (rw : UCT k N → M) :
    (ucardB k N ψ).Realize rw ↔
      ((∀ i : Fin (N + 1), ψ.Realize (Fin.cases (rw (uctT i)) (fun l => rw (uctC l)))) →
        ∃ pq : {pq : Fin (N + 1) × Fin (N + 1) // pq.1 < pq.2},
          rw (uctT pq.1.1) = rw (uctT pq.1.2)) := by
  rw [ucardB, Formula.realize_imp, Formula.realize_iInf, Formula.realize_iSup]
  simp only [upsiG_realize, eqAtom_lift2]

theorem ucard_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) (v : UC0 k → M) :
    (ucard k N ψ).Realize v ↔
      ∀ t : Fin (N + 1) → M, (∀ i, upsiVal k ψ M (fun j => v (ucC j)) (t i)) →
        ∃ i j : Fin (N + 1), i < j ∧ t i = t j := by
  rw [ucard, Formula.realize_iAlls]
  constructor
  · intro h t
    have h1 := h t
    rw [ucardB_realize] at h1
    simp only [uctT, uctC, ucC, Sum.elim_inl, Sum.elim_inr] at h1
    rintro ht
    obtain ⟨pq, hpq⟩ := h1 ht
    exact ⟨pq.1.1, pq.1.2, pq.2, hpq⟩
  · intro h t
    rw [ucardB_realize]
    simp only [uctT, uctC, ucC, Sum.elim_inl, Sum.elim_inr]
    rintro ht
    obtain ⟨i, j, hij, hEq⟩ := h t ht
    exact ⟨⟨(i, j), hij⟩, hEq⟩

theorem ucard_realize_encard {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k N : ℕ) (ψ : LRc.Formula (Fin (k + 1))) (v : UC0 k → M) :
    (ucard k N ψ).Realize v ↔
      {x : M | upsiVal k ψ M (fun j => v (ucC j)) x}.encard ≤ N := by
  rw [ucard_realize, encardLePigeonhole]
  exact Iff.rfl

/-! ## 9. Realisation of the `x₁, x₂` clause -/

theorem ussB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (rw : UCPB k → M) :
    (ussB k N ψ).Realize rw ↔
      (upsiVal k ψ M (fun j => rw (ucpbC j)) (rw ucpbB) →
        (((N : M) * rw ucpbB < rw ucpbX1 ∧ (N : M) * rw ucpbB < rw ucpbX2) ∨
         ((N : M) * rw ucpbX1 < rw ucpbB ∧ (N : M) * rw ucpbX2 < rw ucpbB))) := by
  simp only [ussB, Formula.realize_imp, Formula.realize_sup, Formula.realize_inf,
    upsiG_realize, ltNMul_lift hsq]
  exact Iff.rfl

theorem ussHyp_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ)
    (ψ : LRc.Formula (Fin (k + 1))) (rw : UCP k → M) :
    (ussHyp k N ψ).Realize rw ↔
      ∀ b : M, upsiVal k ψ M (fun j => rw (ucpC j)) b →
        (((N : M) * b < rw ucpX1 ∧ (N : M) * b < rw ucpX2) ∨
         ((N : M) * rw ucpX1 < b ∧ (N : M) * rw ucpX2 < b)) := by
  rw [ussHyp, Formula.realize_iAlls]
  constructor
  · intro h b
    have h3 := h (fun _ : Fin 1 => b)
    rw [ussB_realize hsq] at h3
    simp only [ucpbB, ucpbX1, ucpbX2, ucpbC, ucpC, ucC, Sum.elim_inl, Sum.elim_inr] at h3
    exact h3
  · intro h b
    rw [ussB_realize hsq]
    simp only [ucpbB, ucpbX1, ucpbX2, ucpbC, ucpC, ucC, Sum.elim_inl, Sum.elim_inr]
    exact h (b 0)

theorem uexistsY1_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (rw : UCP k → M) :
    (uexistsY1 k φ).Realize rw ↔
      ∃ y : M, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y := by
  rw [uexistsY1, Formula.realize_iExs]
  constructor
  · rintro ⟨y, hy⟩
    rw [uphiG_realize] at hy
    simp only [ucpdC, ucpdX1, ucpdY, ucpC, ucC, Sum.elim_inl, Sum.elim_inr] at hy
    exact ⟨y 0, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun _ => y, ?_⟩
    rw [uphiG_realize]
    simp only [ucpdC, ucpdX1, ucpdY, ucpC, ucC, Sum.elim_inl, Sum.elim_inr]
    exact hy

theorem uexistsY2_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (rw : UCP k → M) :
    (uexistsY2 k φ).Realize rw ↔
      ∃ y : M, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y := by
  rw [uexistsY2, Formula.realize_iExs]
  constructor
  · rintro ⟨y, hy⟩
    rw [uphiG_realize] at hy
    simp only [ucpdC, ucpdX2, ucpdY, ucpC, ucC, Sum.elim_inl, Sum.elim_inr] at hy
    exact ⟨y 0, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun _ => y, ?_⟩
    rw [uphiG_realize]
    simp only [ucpdC, ucpdX2, ucpdY, ucpC, ucC, Sum.elim_inl, Sum.elim_inr]
    exact hy

theorem udomIff_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (k : ℕ) (φ : LRc.Formula (Fin (k + 2))) (rw : UCP k → M) :
    (udomIff k φ).Realize rw ↔
      ((∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y) ↔
       (∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y)) := by
  simp only [udomIff, Formula.realize_inf, Formula.realize_imp, uexistsY1_realize,
    uexistsY2_realize]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem isRpow_of_relabel {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    {Ctx : Type} (q : ℚ) (x t : Ctx) (rw : Ctx → M) (hx : 0 < rw x) :
    (Formula.relabel ![x, t] (rpowRel q.num q.den)).Realize rw ↔ IsRpow (rw x) q (rw t) := by
  rw [relabel_vec2]
  exact rpowRel_iff_isRpow q hx

theorem uapproxB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) {Nq : ℕ}
    (qs : Fin Nq → ℚ) (i : Fin Nq) (rw : UAPT k → M)
    (hx1 : 0 < rw uaptX1) (hx2 : 0 < rw uaptX2) :
    (uapproxB k N qs i).Realize rw ↔
      (IsRpow (rw uaptX1) (qs i) (rw uaptT1) ∧ IsRpow (rw uaptX2) (qs i) (rw uaptT2) ∧
        |rw uaptY2| * rw uaptT1 ≤ (N : M) * (|rw uaptY1| * rw uaptT2) ∧
        |rw uaptY1| * rw uaptT2 ≤ (N : M) * (|rw uaptY2| * rw uaptT1)) := by
  have hr1 : (Formula.relabel ![uaptX1, uaptT1] (rpowRel (qs i).num (qs i).den)).Realize rw ↔
      IsRpow (rw uaptX1) (qs i) (rw uaptT1) := isRpow_of_relabel (qs i) uaptX1 uaptT1 rw hx1
  have hr2 : (Formula.relabel ![uaptX2, uaptT2] (rpowRel (qs i).num (qs i).den)).Realize rw ↔
      IsRpow (rw uaptX2) (qs i) (rw uaptT2) := isRpow_of_relabel (qs i) uaptX2 uaptT2 rw hx2
  simp only [uapproxB, Formula.realize_inf, hr1, hr2]
  constructor
  · rintro ⟨ha1, ha2, ha3, ha4⟩
    have ht1 := isRpow_nonneg ha1
    have ht2 := isRpow_nonneg ha2
    exact ⟨ha1, ha2,
      (approxAtom_lift2 hsq N uaptY1 uaptY2 uaptT1 uaptT2 rw ht1 ht2).mp ha3,
      (approxAtom_lift2 hsq N uaptY2 uaptY1 uaptT2 uaptT1 rw ht2 ht1).mp ha4⟩
  · rintro ⟨ha1, ha2, ha3, ha4⟩
    have ht1 := isRpow_nonneg ha1
    have ht2 := isRpow_nonneg ha2
    exact ⟨ha1, ha2,
      (approxAtom_lift2 hsq N uaptY1 uaptY2 uaptT1 uaptT2 rw ht1 ht2).mpr ha3,
      (approxAtom_lift2 hsq N uaptY2 uaptY1 uaptT2 uaptT1 rw ht2 ht1).mpr ha4⟩

theorem uapprox_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) {Nq : ℕ}
    (φ : LRc.Formula (Fin (k + 2))) (qs : Fin Nq → ℚ) (rw : UCP k → M)
    (hx1 : 0 < rw ucpX1) (hx2 : 0 < rw ucpX2) :
    (uapprox k N φ qs).Realize rw ↔
      ∀ y₁ y₂ : M, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y₁ →
        uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y₂ →
        ∃ i : Fin Nq, ∃ t₁ t₂ : M, IsRpow (rw ucpX1) (qs i) t₁ ∧
          IsRpow (rw ucpX2) (qs i) t₂ ∧
          |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁) := by
  rw [uapprox, Formula.realize_iAlls]
  constructor
  · intro h y₁ y₂ h1 h2
    have h3 := h ![y₁, y₂]
    simp only [Formula.realize_imp, Formula.realize_iSup, Formula.realize_iExs, uphiG_realize]
      at h3
    simp only [ucpyX1, ucpyX2, ucpyY1, ucpyY2, ucpyC, ucpC, ucC, Sum.elim_inl,
      Sum.elim_inr] at h3
    obtain ⟨i, t, ht⟩ := h3 h1 h2
    exact ⟨i, t 0, t 1,
      (uapproxB_realize hsq k N qs i (Sum.elim (Sum.elim rw ![y₁, y₂]) t) hx1 hx2).mp ht⟩
  · intro h y
    simp only [Formula.realize_imp, Formula.realize_iSup, Formula.realize_iExs, uphiG_realize,
      ucpyX1, ucpyX2, ucpyY1, ucpyY2, ucpyC, ucpC, ucC, Sum.elim_inl, Sum.elim_inr]
    intro h1 h2
    obtain ⟨i, t₁, t₂, hpos⟩ := h (y 0) (y 1) h1 h2
    exact ⟨i, ![t₁, t₂],
      (uapproxB_realize hsq k N qs i (Sum.elim (Sum.elim rw y) ![t₁, t₂]) hx1 hx2).mpr hpos⟩

theorem uconclB_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) {Nq : ℕ}
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (qs : Fin Nq → ℚ)
    (rw : UCP k → M) :
    (uconclB k N φ ψ qs).Realize rw ↔
      ((0 < rw ucpX1) → (0 < rw ucpX2) →
        ((∀ b : M, upsiVal k ψ M (fun j => rw (ucpC j)) b →
            (((N : M) * b < rw ucpX1 ∧ (N : M) * b < rw ucpX2) ∨
             ((N : M) * rw ucpX1 < b ∧ (N : M) * rw ucpX2 < b))) →
          (((∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y) ↔
            (∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y)) ∧
           (∀ y₁ y₂ : M, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y₁ →
              uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y₂ →
              ∃ i : Fin Nq, ∃ t₁ t₂ : M, IsRpow (rw ucpX1) (qs i) t₁ ∧
                IsRpow (rw ucpX2) (qs i) t₂ ∧
                |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧
                |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁))))) := by
  have hps1 : (liftR ![ucpX1] posStrictAtom).Realize rw ↔ 0 < rw ucpX1 :=
    posStrictAtom_lift2 ucpX1 rw hsq
  have hps2 : (liftR ![ucpX2] posStrictAtom).Realize rw ↔ 0 < rw ucpX2 :=
    posStrictAtom_lift2 ucpX2 rw hsq
  have huss : (ussHyp k N ψ).Realize rw ↔ ∀ b : M,
      upsiVal k ψ M (fun j => rw (ucpC j)) b →
        (((N : M) * b < rw ucpX1 ∧ (N : M) * b < rw ucpX2) ∨
         ((N : M) * rw ucpX1 < b ∧ (N : M) * rw ucpX2 < b)) :=
    ussHyp_realize hsq k N ψ rw
  have hdom : (udomIff k φ).Realize rw ↔
      ((∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX1) y) ↔
       (∃ y, uphiVal k φ M (fun j => rw (ucpC j)) (rw ucpX2) y)) :=
    udomIff_realize k φ rw
  simp only [uconclB, Formula.realize_imp, Formula.realize_inf, hps1, hps2, huss, hdom]
  constructor
  · rintro h hp1 hp2 hss
    obtain ⟨h1, h2⟩ := h hp1 hp2 hss
    exact ⟨h1, (uapprox_realize hsq k N φ qs rw hp1 hp2).mp h2⟩
  · rintro h hp1 hp2 hss
    obtain ⟨h1, h2⟩ := h hp1 hp2 hss
    exact ⟨h1, (uapprox_realize hsq k N φ qs rw hp1 hp2).mpr h2⟩

theorem uconcl_all_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) {Nq : ℕ}
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (qs : Fin Nq → ℚ)
    (v : UC0 k → M) :
    (uconcl k N φ ψ qs).Realize v ↔
      ∀ x₁ x₂ : M, 0 < x₁ → 0 < x₂ →
        (∀ b : M, upsiVal k ψ M (fun j => v (ucC j)) b →
          (((N : M) * b < x₁ ∧ (N : M) * b < x₂) ∨
           ((N : M) * x₁ < b ∧ (N : M) * x₂ < b))) →
        ((∃ y, uphiVal k φ M (fun j => v (ucC j)) x₁ y) ↔
         (∃ y, uphiVal k φ M (fun j => v (ucC j)) x₂ y)) ∧
        ∀ y₁ y₂ : M, uphiVal k φ M (fun j => v (ucC j)) x₁ y₁ →
          uphiVal k φ M (fun j => v (ucC j)) x₂ y₂ →
          ∃ i : Fin Nq, ∃ t₁ t₂ : M, IsRpow x₁ (qs i) t₁ ∧ IsRpow x₂ (qs i) t₂ ∧
            |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁) := by
  rw [uconcl, Formula.realize_iAlls]
  constructor
  · intro h x₁ x₂ hx1 hx2 hss
    have h3 := h ![x₁, x₂]
    rw [uconclB_realize hsq] at h3
    simp only [ucpX1, ucpX2, ucpC, ucC, Sum.elim_inl, Sum.elim_inr] at h3
    exact h3 hx1 hx2 hss
  · intro h x
    rw [uconclB_realize hsq]
    simp only [ucpX1, ucpX2, ucpC, ucC, Sum.elim_inl, Sum.elim_inr]
    intro hx1 hx2 hss
    exact h (x 0) (x 1) hx1 hx2 hss

theorem uBody_all_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N : ℕ) {Nq : ℕ}
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (qs : Fin Nq → ℚ)
    (v : Empty → M) :
    ((Formula.iAlls (Fin k) (uBody k N φ ψ qs)) : LRc.Formula Empty).Realize v ↔
      ∀ c : Fin k → M, ({x : M | upsiVal k ψ M c x}.encard ≤ N ∧
        ∀ x₁ x₂ : M, 0 < x₁ → 0 < x₂ →
          (∀ b : M, upsiVal k ψ M c b →
            (((N : M) * b < x₁ ∧ (N : M) * b < x₂) ∨
             ((N : M) * x₁ < b ∧ (N : M) * x₂ < b))) →
          ((∃ y, uphiVal k φ M c x₁ y) ↔ (∃ y, uphiVal k φ M c x₂ y)) ∧
          ∀ y₁ y₂ : M, uphiVal k φ M c x₁ y₁ → uphiVal k φ M c x₂ y₂ →
            ∃ i : Fin Nq, ∃ t₁ t₂ : M, IsRpow x₁ (qs i) t₁ ∧ IsRpow x₂ (qs i) t₂ ∧
              |y₂| * t₁ ≤ (N : M) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N : M) * (|y₂| * t₁)) := by
  rw [Formula.realize_iAlls]
  constructor
  · intro h c
    have h3 := h c
    rw [uBody, Formula.realize_inf] at h3
    obtain ⟨h1, h2⟩ := h3
    rw [ucard_realize_encard] at h1
    rw [uconcl_all_realize hsq] at h2
    simp only [ucC, Sum.elim_inr] at h1 h2
    exact ⟨h1, h2⟩
  · intro h c
    rw [uBody, Formula.realize_inf]
    refine ⟨?_, ?_⟩
    · rw [ucard_realize_encard]
      simpa only [ucC, Sum.elim_inr] using (h c).1
    · rw [uconcl_all_realize hsq]
      simpa only [ucC, Sum.elim_inr] using (h c).2

theorem ulpmSent_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) (k N Nq : ℕ)
    (φ : LRc.Formula (Fin (k + 2))) (ψ : LRc.Formula (Fin (k + 1))) (qs : Fin Nq → ℚ) :
    (M ⊨ ulpmSent k N Nq φ ψ qs) ↔ ULPMGood k N Nq φ ψ qs M := by
  rw [ulpmSent, Sentence.Realize, Formula.realize_imp, uGraphAll_all_realize,
    uBody_all_realize hsq]
  exact Iff.rfl

end Work.WilC4
