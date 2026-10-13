/-
  WilC4/Diag_definable : `Work.WilC4.Diag Y B₀ ρ R` is `∅`-definable whenever `Y` and `B₀` are.

  `Diag Y B₀ ρ R ⊆ ℝ²` is the set of pairs `v = (β, y)` with `R ≤ β`, `y` a lower bound of the
  candidate values `Cand Y B₀ ρ β`, and `y` approximated from above by them.

  The proof has three layers.

  * `CandBody` (see `Work.WilC4.DiagDefs`) is the *body* of the formula for
    `y ∈ Cand Y B₀ ρ β`: all the (in)equalities, with every quantified variable free.  It is
    `∅`-definable (`Work.WilC4.CandBody_definable`).
  * Projecting the body quantifier by quantifier (`CandPeel`) and comparing with the definition
    of `Cand`/`IsWit`/`IsDeepR` gives the definability of the *graph* `CandG` of `Cand`
    (`CandPeel_eq_CandG`).
  * The three clauses of `Diag` are then assembled from `CandG` by two more quantifier
    projections and polynomial (in)equalities.

  Everything is proved with `univ` as the parameter set (polynomial (in)equalities with real
  coefficients are then `WilkiesI.definable_eval_*`), and the single conversion
  `definable_univ_iff_empty` (every real is a constant of `LRc`) produces the `∅`-statement.
-/
import Mathlib
import Submission.Work.WilC4.DiagDefs
import Submission.Work.WilC4.CandBody_definable

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/-! ## 1. Reading off the body in the raw coordinates -/

/-- The parameter tuple read off the `c`-block of `E : Fin (k+5) → ℝ`. -/
def eC (E : Fin (k+5) → ℝ) : Fin k → ℝ := fun i => E (Fin.castLE (Nat.le_add_right k 5) i)

/-- Membership in `CandBody` in the raw coordinates `(w, E, U, Q)`. -/
lemma mem_CandBody_iff (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ)
    (w : Fin 2 → ℝ) (E : Fin (k+5) → ℝ) (U : Fin 6 → ℝ) (Q : Fin 2 → ℝ) :
    Sum.elim (Sum.elim (Sum.elim w E) U) Q ∈ CandBody Y B₀ ρ ↔
      (0 < E (Fin.natAdd k 0) ∧
       Fin.cons (E (Fin.natAdd k 0))
          (Fin.cons (E (Fin.natAdd k 1)) (eC (k := k) E)) ∈ Y ∧
       Fin.cons (E (Fin.natAdd k 3))
          (Fin.cons (E (Fin.natAdd k 2)) (eC (k := k) E)) ∈ Y ∧
       E (Fin.natAdd k 3) = E (Fin.natAdd k 0) * w 0 ∧
       E (Fin.natAdd k 2) = E (Fin.natAdd k 1) * w 1 ∧
       IsDivR (E (Fin.natAdd k 0)) (w 0) (E (Fin.natAdd k 4)) ∧
       ¬(Fin.cons (U 0) (eC (k := k) E) ∈ B₀ ∧
           IsDivR (E (Fin.natAdd k 0)) (2 * w 0) (U 1) ∧
           U 1 ≤ U 0 ∧ U 0 ≤ 2 * w 0 * E (Fin.natAdd k 0)) ∧
       (¬(E (Fin.natAdd k 4) ≤ U 2 ∧ U 2 ≤ E (Fin.natAdd k 3) ∧ U 3 = U 2 + U 2 ∧
            Fin.cons (U 2) (Fin.cons (U 4) (eC (k := k) E)) ∈ Y ∧
            Fin.cons (U 3) (Fin.cons (U 5) (eC (k := k) E)) ∈ Y ∧ U 4 ≠ 0) ∨
        (IsDivR (U 5) (U 4) (Q 0) ∧ IsDivR 1 (w 0) (Q 1) ∧
           Q 0 ≤ Q 1 + ρ ∧ ρ ≤ Q 0 + Q 1))) := by
  have htail : (Sum.elim (Sum.elim (Sum.elim w E) U) Q) ∘ embC ∘ Fin.succ
      = eC (k := k) E := by
    funext i
    simp [embC, eC, cc, Function.comp_apply]
  have htail1 : (Sum.elim (Sum.elim (Sum.elim w E) U) Q) ∘ cc = eC (k := k) E := by
    funext i
    simp [eC, cc, Function.comp_apply]
  simp only [CandBody, Set.mem_ofPred_eq, GrSub, GrSub1, Bmem, cx, cu, cv, cz, cq0, cβ, cy,
    cb, cq1, ct, ct2, cy1, cy2, cqq, cpinv, Sum.elim_inl, Sum.elim_inr, htail, htail1]

/-! ## 2. Projecting the body down to the retained variables -/

/-- The projection of `CandBody` down to `(β, y)`: existentially quantify `(c,x,u,v,z,q₀)`,
universally quantify `(b,q₁,t,t₂,y₁,y₂)` and existentially quantify `(q,q⁻¹)`. -/
def CandPeel (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    Set (Fin 2 → ℝ) :=
  {w | ∃ E : Fin (k+5) → ℝ, ∀ U : Fin 6 → ℝ, ∃ Q : Fin 2 → ℝ,
        Sum.elim (Sum.elim (Sum.elim w E) U) Q ∈ CandBody Y B₀ ρ}

theorem CandPeel_definable {Y : Set (Fin (k+2) → ℝ)} {B₀ : Set (Fin (k+1) → ℝ)} {ρ : ℝ}
    (hC : (Set.univ : Set ℝ).Definable LRc (CandBody Y B₀ ρ)) :
    (Set.univ : Set ℝ).Definable LRc (CandPeel Y B₀ ρ) := by
  have hQ : (Set.univ : Set ℝ).Definable LRc
      {h : ((Fin 2 ⊕ Fin (k+5)) ⊕ Fin 6) → ℝ |
        ∃ Q : Fin 2 → ℝ, Sum.elim h Q ∈ CandBody Y B₀ ρ} :=
    hC.exists_of_finite (α := (Fin 2 ⊕ Fin (k+5)) ⊕ Fin 6) (β := Fin 2)
  have hU : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin (k+5)) → ℝ | ∀ U : Fin 6 → ℝ, Sum.elim g U ∈
        {h : ((Fin 2 ⊕ Fin (k+5)) ⊕ Fin 6) → ℝ |
          ∃ Q : Fin 2 → ℝ, Sum.elim h Q ∈ CandBody Y B₀ ρ}} :=
    hQ.forall_of_finite (α := Fin 2 ⊕ Fin (k+5)) (β := Fin 6)
  have hE : (Set.univ : Set ℝ).Definable LRc
      {w : Fin 2 → ℝ | ∃ E : Fin (k+5) → ℝ, Sum.elim w E ∈
        {g : (Fin 2 ⊕ Fin (k+5)) → ℝ | ∀ U : Fin 6 → ℝ, Sum.elim g U ∈
          {h : ((Fin 2 ⊕ Fin (k+5)) ⊕ Fin 6) → ℝ |
            ∃ Q : Fin 2 → ℝ, Sum.elim h Q ∈ CandBody Y B₀ ρ}}} :=
    hU.exists_of_finite (α := Fin 2) (β := Fin (k+5))
  have hset : {w : Fin 2 → ℝ | ∃ E : Fin (k+5) → ℝ, Sum.elim w E ∈
        {g : (Fin 2 ⊕ Fin (k+5)) → ℝ | ∀ U : Fin 6 → ℝ, Sum.elim g U ∈
          {h : ((Fin 2 ⊕ Fin (k+5)) ⊕ Fin 6) → ℝ |
            ∃ Q : Fin 2 → ℝ, Sum.elim h Q ∈ CandBody Y B₀ ρ}}} = CandPeel Y B₀ ρ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, CandPeel]
  rw [hset] at hE
  exact hE

/-! ## 3. The projection is the graph of `Cand` -/

theorem CandPeel_eq_CandG (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    CandPeel Y B₀ ρ = CandG Y B₀ ρ := by
  ext w
  constructor
  · rintro ⟨E, hE⟩
    obtain ⟨Q₀, hQ₀⟩ := hE 0
    rw [mem_CandBody_iff] at hQ₀
    obtain ⟨hx, hG1, hG2, hz, hv, hdiv0, -, -⟩ := hQ₀
    have hq0 : E (Fin.natAdd k 4) = E (Fin.natAdd k 0) / (w 0) := ((isDivR_iff _ _ _).mp hdiv0).symm
    show w 1 ∈ Cand Y B₀ ρ (w 0)
    refine ⟨eC E, E (Fin.natAdd k 0), ⟨hx, ?_, ?_⟩, E (Fin.natAdd k 1), E (Fin.natAdd k 2),
      hG1, ?_, ?_⟩
    · -- the deepness condition
      intro b hb
      obtain ⟨Qb, hQb⟩ := hE ![b, E (Fin.natAdd k 0) / (2 * w 0), 0, 0, 0, 0]
      rw [mem_CandBody_iff] at hQb
      obtain ⟨-, -, -, -, -, -, hD1b, -⟩ := hQb
      simp only [Fin.isValue, Matrix.cons_val] at hD1b
      intro hcon
      exact hD1b ⟨hb, (isDivR_iff _ _ _).mpr rfl, hcon.1, hcon.2⟩
    · -- the window condition
      intro t ht1 ht2 y₁ y₂ hg1 hg2 hy₁
      obtain ⟨Qw, hQw⟩ := hE ![0, 0, t, 2 * t, y₁, y₂]
      rw [mem_CandBody_iff] at hQw
      obtain ⟨-, -, -, -, -, -, -, hD2w⟩ := hQw
      simp only [Fin.isValue, Matrix.cons_val] at hD2w
      rcases hD2w with hpre | ⟨hqq, hpinv, h1, h2⟩
      · exact absurd ⟨by rw [hq0]; exact ht1, by rw [hz]; exact ht2, by ring, hg1, hg2, hy₁⟩ hpre
      · have hqq' : Qw 0 = y₂ / y₁ := ((isDivR_iff _ _ _).mp hqq).symm
        have hpinv' : Qw 1 = 1 / (w 0) := ((isDivR_iff _ _ _).mp hpinv).symm
        rw [hqq', hpinv'] at h1 h2
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
    · show Fin.cons (E (Fin.natAdd k 0) * w 0) (Fin.cons (E (Fin.natAdd k 2)) (eC E)) ∈ Y
      rw [← hz]
      exact hG2
    · rw [hv]; ring
  · intro hw
    show ∃ E : Fin (k+5) → ℝ, ∀ U : Fin 6 → ℝ, ∃ Q : Fin 2 → ℝ,
      Sum.elim (Sum.elim (Sum.elim w E) U) Q ∈ CandBody Y B₀ ρ
    obtain ⟨c, x, ⟨hx, hDeep, hWin⟩, u, v, hG1, hG2, hprod⟩ := hw
    have hNe : (2 : ℝ) * w 0 = w 0 + w 0 := by ring
    set E : Fin (k+5) → ℝ := Fin.append c ![x, u, v, x * w 0, x / (w 0)] with hEdef
    have hEc : eC (k := k) E = c := by
      funext i
      simp [E, eC, Fin.append_left]
    have hEx : E (Fin.natAdd k 0) = x := by simp [E]
    have hEu : E (Fin.natAdd k 1) = u := by simp [E]
    have hEv : E (Fin.natAdd k 2) = v := by simp [E]
    have hEz : E (Fin.natAdd k 3) = x * w 0 := by simp [E]
    have hEq : E (Fin.natAdd k 4) = x / (w 0) := by simp [E]
    refine ⟨E, fun U => ⟨![U 5 / U 4, 1 / (w 0)], ?_⟩⟩
    rw [mem_CandBody_iff]
    refine ⟨by rw [hEx]; exact hx, ?_, ?_, by rw [hEz, hEx],
      by rw [hEv, hEu, mul_comm]; exact hprod.symm,
      by rw [hEx, hEq]; exact (isDivR_iff _ _ _).mpr rfl, ?_, ?_⟩
    · rw [hEx, hEu, hEc]; exact hG1
    · rw [hEz, hEv, hEc]; exact hG2
    · rw [hEc, hEx]
      rintro ⟨hb, hdiv, hle1, hle2⟩
      have hU1 : U 1 = x / (2 * w 0) := ((isDivR_iff _ _ _).mp hdiv).symm
      exact hDeep (U 0) hb ⟨by rw [← hU1]; exact hle1, hle2⟩
    · rw [hEc, hEz, hEq]
      simp only [Fin.isValue, Matrix.cons_val]
      by_cases hpre : (x / (w 0) ≤ U 2 ∧ U 2 ≤ x * w 0 ∧ U 3 = U 2 + U 2 ∧
          Fin.cons (U 2) (Fin.cons (U 4) c) ∈ Y ∧
          Fin.cons (U 3) (Fin.cons (U 5) c) ∈ Y ∧ U 4 ≠ 0)
      · refine Or.inr ⟨(isDivR_iff _ _ _).mpr rfl, (isDivR_iff _ _ _).mpr rfl, ?_, ?_⟩
        · have h3 : U 3 = 2 * U 2 := by rw [hpre.2.2.1]; ring
          have hwin : |U 5 / U 4 - ρ| ≤ 1 / (w 0) :=
            hWin (U 2) hpre.1 hpre.2.1 (U 4) (U 5) hpre.2.2.2.1
              (by rw [← h3]; exact hpre.2.2.2.2.1) hpre.2.2.2.2.2
          have := (abs_le.mp hwin).2
          linarith
        · have h3 : U 3 = 2 * U 2 := by rw [hpre.2.2.1]; ring
          have hwin : |U 5 / U 4 - ρ| ≤ 1 / (w 0) :=
            hWin (U 2) hpre.1 hpre.2.1 (U 4) (U 5) hpre.2.2.2.1
              (by rw [← h3]; exact hpre.2.2.2.2.1) hpre.2.2.2.2.2
          have := (abs_le.mp hwin).1
          linarith
      · exact Or.inl hpre

theorem CandG_definable {Y : Set (Fin (k+2) → ℝ)} {B₀ : Set (Fin (k+1) → ℝ)} {ρ : ℝ}
    (hC : (Set.univ : Set ℝ).Definable LRc (CandBody Y B₀ ρ)) :
    (Set.univ : Set ℝ).Definable LRc (CandG Y B₀ ρ) := by
  rw [← CandPeel_eq_CandG Y B₀ ρ]
  exact CandPeel_definable hC

/-! ## 4. The three clauses of `Diag` -/

/-- `∀ y ∈ Cand Y B₀ ρ (v 0), v 1 ≤ y`. -/
def DiagUpper (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | ∀ y : ℝ, y ∈ Cand Y B₀ ρ (v 0) → v 1 ≤ y}

/-- `∀ ε > 0, ∃ y ∈ Cand Y B₀ ρ (v 0), y < v 1 + ε`. -/
def DiagApprox (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    Set (Fin 2 → ℝ) :=
  {v | ∀ ε : ℝ, 0 < ε → ∃ y : ℝ, y ∈ Cand Y B₀ ρ (v 0) ∧ y < v 1 + ε}

/-- The coordinate-free description of `Diag`. -/
theorem Diag_eq (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ R : ℝ) :
    Diag Y B₀ ρ R = {v : Fin 2 → ℝ | R ≤ v 0} ∩ DiagUpper Y B₀ ρ ∩ DiagApprox Y B₀ ρ := by
  ext v
  simp only [Diag, DiagUpper, DiagApprox, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun y hy => h2 y hy⟩, fun e he => by
      obtain ⟨y, hy, hlt⟩ := h3 e he; exact ⟨y, hy, hlt⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun y hy => h2 y hy, fun e he => by
      obtain ⟨y, hy, hlt⟩ := h3 e he; exact ⟨y, hy, hlt⟩⟩

theorem DiagUpper_definable {Y : Set (Fin (k+2) → ℝ)} {B₀ : Set (Fin (k+1) → ℝ)} {ρ : ℝ}
    (hC : (Set.univ : Set ℝ).Definable LRc (CandG Y B₀ ρ)) :
    (Set.univ : Set ℝ).Definable LRc (DiagUpper Y B₀ ρ) := by
  have hpre : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ CandG Y B₀ ρ} :=
    hC.preimage_comp (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
      Fin 2 → Fin 2 ⊕ Fin 1)
  have hle : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ | g (Sum.inl 1) ≤ g (Sum.inr 0)} := by
    have h := definable_le_LRc (σ := Fin 2 ⊕ Fin 1) (MvPolynomial.X (Sum.inl (1 : Fin 2)))
      (MvPolynomial.X (Sum.inr (0 : Fin 1)))
    convert h using 1
    ext g
    simp [MvPolynomial.eval_X]
  have hS : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ |
        g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
          Fin 2 → Fin 2 ⊕ Fin 1) ∈ CandG Y B₀ ρ →
        g (Sum.inl 1) ≤ g (Sum.inr 0)} := by
    have h := hpre.compl.union hle
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    tauto
  have h := hS.forall_of_finite (α := Fin 2) (β := Fin 1)
  have hset : {v : Fin 2 → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈
        {g : (Fin 2 ⊕ Fin 1) → ℝ |
          g ∘ (![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] :
            Fin 2 → Fin 2 ⊕ Fin 1) ∈ CandG Y B₀ ρ →
          g (Sum.inl 1) ≤ g (Sum.inr 0)}} = DiagUpper Y B₀ ρ := by
    ext v
    simp only [Set.mem_setOf_eq, DiagUpper, CandG, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Fin.isValue, Matrix.cons_val]
    constructor
    · intro hv y hy
      exact hv (fun _ => y) hy
    · intro hv u hu
      exact hv (u 0) hu
  rw [hset] at h
  exact h

theorem DiagApprox_definable {Y : Set (Fin (k+2) → ℝ)} {B₀ : Set (Fin (k+1) → ℝ)} {ρ : ℝ}
    (hC : (Set.univ : Set ℝ).Definable LRc (CandG Y B₀ ρ)) :
    (Set.univ : Set ℝ).Definable LRc (DiagApprox Y B₀ ρ) := by
  have hpre : (Set.univ : Set ℝ).Definable LRc
      {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        h ∘ (![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] :
          Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1) ∈ CandG Y B₀ ρ} :=
    hC.preimage_comp (![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] :
      Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1)
  have hpos : (Set.univ : Set ℝ).Definable LRc
      {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ | 0 < h (Sum.inl (Sum.inr (0 : Fin 1)))} := by
    have h := definable_eval_pos_LRc
      (σ := (Fin 2 ⊕ Fin 1) ⊕ Fin 1) (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))))
    convert h using 1
    ext g
    simp [MvPolynomial.eval_X]
  have hlt : (Set.univ : Set ℝ).Definable LRc
      {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        h (Sum.inr (0 : Fin 1)) < h (Sum.inl (Sum.inl (1 : Fin 2))) +
          h (Sum.inl (Sum.inr (0 : Fin 1)))} := by
    have h := definable_eval_pos_LRc (σ := (Fin 2 ⊕ Fin 1) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inl (Sum.inl (1 : Fin 2))) +
        MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - MvPolynomial.X (Sum.inr (0 : Fin 1)))
    convert h using 1
    ext g
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      Set.mem_setOf_eq]
    constructor <;> intro hg <;> linarith
  have hT : (Set.univ : Set ℝ).Definable LRc
      {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ |
        ¬(0 < h (Sum.inl (Sum.inr (0 : Fin 1)))) ∨
          (h ∘ (![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] :
            Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1) ∈ CandG Y B₀ ρ ∧
            h (Sum.inr (0 : Fin 1)) < h (Sum.inl (Sum.inl (1 : Fin 2))) +
              h (Sum.inl (Sum.inr (0 : Fin 1))))} := by
    have h := hpos.compl.union (hpre.inter hlt)
    convert h using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
  have hE : (Set.univ : Set ℝ).Definable LRc
      {g : (Fin 2 ⊕ Fin 1) → ℝ | ∃ y : Fin 1 → ℝ, Sum.elim g y ∈
        {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ |
          ¬(0 < h (Sum.inl (Sum.inr (0 : Fin 1)))) ∨
            (h ∘ (![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] :
              Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1) ∈ CandG Y B₀ ρ ∧
              h (Sum.inr (0 : Fin 1)) < h (Sum.inl (Sum.inl (1 : Fin 2))) +
                h (Sum.inl (Sum.inr (0 : Fin 1))))}} :=
    hT.exists_of_finite (α := Fin 2 ⊕ Fin 1) (β := Fin 1)
  have hA := hE.forall_of_finite (α := Fin 2) (β := Fin 1)
  have hset : {v : Fin 2 → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈
        {g : (Fin 2 ⊕ Fin 1) → ℝ | ∃ y : Fin 1 → ℝ, Sum.elim g y ∈
          {h : ((Fin 2 ⊕ Fin 1) ⊕ Fin 1) → ℝ |
            ¬(0 < h (Sum.inl (Sum.inr (0 : Fin 1)))) ∨
              (h ∘ (![Sum.inl (Sum.inl (0 : Fin 2)), Sum.inr (0 : Fin 1)] :
                Fin 2 → (Fin 2 ⊕ Fin 1) ⊕ Fin 1) ∈ CandG Y B₀ ρ ∧
                h (Sum.inr (0 : Fin 1)) < h (Sum.inl (Sum.inl (1 : Fin 2))) +
                  h (Sum.inl (Sum.inr (0 : Fin 1))))}}} = DiagApprox Y B₀ ρ := by
    ext v
    simp only [Set.mem_setOf_eq, DiagApprox, CandG, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply, Fin.isValue, Matrix.cons_val]
    constructor
    · intro hv e he
      obtain ⟨y, h | ⟨hc, hl⟩⟩ := hv (fun _ => e)
      · exact absurd he h
      · exact ⟨y 0, hc, hl⟩
    · intro hv u
      by_cases h : 0 < u 0
      · obtain ⟨y, hy, hlt⟩ := hv (u 0) h
        exact ⟨fun _ => y, Or.inr ⟨hy, hlt⟩⟩
      · exact ⟨fun _ => 0, Or.inl h⟩
  rw [hset] at hA
  exact hA

/-! ## 5. The theorem -/

theorem Diag_definable_univ {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (B₀ : Set (Fin (k + 1) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) (ρ R : ℝ) :
    (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Diag Y B₀ ρ R) := by
  have hYu : (Set.univ : Set ℝ).Definable LRc Y := hY.mono (Set.subset_univ _)
  have hBu : (Set.univ : Set ℝ).Definable LRc B₀ := hB₀.mono (Set.subset_univ _)
  have hC : (Set.univ : Set ℝ).Definable LRc (CandG Y B₀ ρ) :=
    CandG_definable (CandBody_definable Y B₀ ρ hY hB₀)
  have h1 : (Set.univ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | R ≤ v 0} := by
    have h := definable_le_LRc (σ := Fin 2) (MvPolynomial.C R) (MvPolynomial.X 0)
    convert h using 1
    ext v
    simp [MvPolynomial.eval_X]
  rw [Diag_eq]
  exact (h1.inter (DiagUpper_definable hC)).inter (DiagApprox_definable hC)

theorem Diag_definable {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) (ρ R : ℝ) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.Diag Y B₀ ρ R) :=
  (definable_univ_iff_empty).mp (Diag_definable_univ Y B₀ hY hB₀ ρ R)

end Work.WilC4
