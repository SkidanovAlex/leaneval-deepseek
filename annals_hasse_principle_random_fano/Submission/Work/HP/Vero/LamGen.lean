import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.LiftDefs
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulAux
import Submission.Work.HP.Vero.MulMono
import Submission.Work.HP.Vero.mulVec_assoc
import Submission.Work.HP.Vero.mulVec_symm
import Submission.Work.HP.Sig2.lift_two_vectors

/-!
# The `Ψ`-lift spanning statement `Lam (a+2) = Lam2V a (a+2)`

`Lam d n z w` is the space of degree-`d` real forms vanishing at the two real points `z`, `w`, and
`Lam2V a (a+2) n z w` is the span of the products of a degree-`a` form with a quadric through `z`
and `w`.  The identity proved here is the algebraic heart of the paper's reduction of "Key result
two vectors" from `d = 2` to all `d`.
-/

set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

namespace Aux

open Work.HP.Sig2.LiftTwo (exists_sub_eMon)

/-- The unique exponent vector of degree `0`. -/
def zeroMon (n : ℕ) : Mon 0 n := ⟨fun _ => 0, by simp⟩

/-- The `k`-th power of the linear form with coefficient vector `U`. -/
def powLin {n : ℕ} (U : Mon 1 n → ℝ) : (k : ℕ) → (Mon k n → ℝ)
  | 0 => unitMon (R := ℝ) (zeroMon n)
  | (k + 1) => mulVec k 1 (k + 1) (powLin U k) U

@[simp] lemma powLin_zero {n : ℕ} (U : Mon 1 n → ℝ) :
    powLin U 0 = unitMon (R := ℝ) (zeroMon n) := rfl

@[simp] lemma powLin_succ {n : ℕ} (U : Mon 1 n → ℝ) (k : ℕ) :
    powLin U (k + 1) = mulVec k 1 (k + 1) (powLin U k) U := rfl

/-- Evaluation of a power. -/
lemma formEvalR_powLin {n : ℕ} (U : Mon 1 n → ℝ) (z : Fin (n + 1) → ℝ) (k : ℕ) :
    formEvalR k n (powLin U k) z = (formEvalR 1 n U z) ^ k := by
  induction k with
  | zero =>
      rw [powLin_zero, formEvalR, pow_zero]
      rw [Finset.sum_eq_single (zeroMon n)]
      · rw [unitMon_same, one_mul]; simp [veronese]
      · intro b _ hb; rw [unitMon_of_ne hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ k ih =>
      rw [powLin_succ, Work.HP.Sig2.LiftTwo.mulVec_formEvalR', ih, pow_succ]

/-- For `M : Mon (j+1) n` there is an index with positive exponent. -/
lemma exists_pos_coord {j n : ℕ} (M : Mon (j + 1) n) :
    ∃ i : Fin (n + 1), 1 ≤ (M.1 i : ℕ) := by
  by_contra h
  have h0 : ∀ i, (M.1 i : ℕ) = 0 := fun i => by
    have hi := (not_exists.mp h) i
    omega
  have hs : (∑ i, (M.1 i : ℕ)) = 0 := Finset.sum_eq_zero (fun i _ => h0 i)
  rw [M.2] at hs
  omega

/-- **The real span of the products of a degree-`j` form with a linear form is everything.** -/
theorem span_one_mul (j n : ℕ) :
    Submodule.span ℝ (Set.range (fun p : (Mon j n → ℝ) × (Mon 1 n → ℝ) =>
        mulVec j 1 (j + 1) p.1 p.2)) = ⊤ := by
  rw [eq_top_iff]
  intro F _
  rw [← sum_smul_unitMon (R := ℝ) F]
  refine Submodule.sum_mem _ fun M _ => ?_
  obtain ⟨i, hi⟩ := exists_pos_coord M
  obtain ⟨μ, hμ⟩ := exists_sub_eMon M hi
  have h1 : mulVec j 1 (j + 1) (unitMon (R := ℝ) μ) (unitMon (R := ℝ) (eMon n i))
      = unitMon (R := ℝ) (addMon μ (eMon n i)) :=
    mulVec_unitMon_unitMon μ (eMon n i)
  rw [hμ] at h1
  rw [← h1]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨(unitMon (R := ℝ) μ, unitMon (R := ℝ) (eMon n i)), rfl⟩)

set_option maxHeartbeats 800000

/-! ## Linearity of `formEvalR` and the evaluation of a unit monomial -/

lemma formEvalR_add {d n : ℕ} (A B : Mon d n → ℝ) (z : Fin (n + 1) → ℝ) :
    formEvalR d n (A + B) z = formEvalR d n A z + formEvalR d n B z := by
  rw [← evalLinR_apply, ← evalLinR_apply, ← evalLinR_apply, map_add]

lemma formEvalR_smul {d n : ℕ} (c : ℝ) (A : Mon d n → ℝ) (z : Fin (n + 1) → ℝ) :
    formEvalR d n (c • A) z = c * formEvalR d n A z := by
  rw [← evalLinR_apply, ← evalLinR_apply, map_smul]
  rfl

lemma formEvalR_unitMon {d n : ℕ} (P : Mon d n) (z : Fin (n + 1) → ℝ) :
    formEvalR d n (unitMon (R := ℝ) P) z = veronese d n z P := by
  rw [formEvalR, Finset.sum_eq_single P]
  · rw [unitMon_same, one_mul]
  · intro b _ hb; rw [unitMon_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma veronese_eMonR {n : ℕ} (z : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    veronese 1 n z (eMon n i) = z i := by
  rw [veronese, Finset.prod_eq_single i]
  · rw [eMon_val, if_pos rfl, pow_one]
  · intro j _ hj; rw [eMon_val, if_neg hj, pow_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Two real vectors are independent iff some `2 × 2` minor is nonzero. -/
lemma exists_minor_ne {n : ℕ} (z w : Fin (n + 1) → ℝ) (hzw : LinearIndependent ℝ ![z, w]) :
    ∃ i j : Fin (n + 1), z i * w j - z j * w i ≠ 0 := by
  by_contra h
  have h' : ∀ i j : Fin (n + 1), z i * w j - z j * w i = 0 := fun i j => by
    by_contra hh; exact h ⟨i, j, hh⟩
  have hz0 : z ≠ 0 := hzw.ne_zero 0
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hz0
  set a : ℝ := w i₀ / z i₀ with ha
  have hw : w = a • z := by
    funext j
    rw [ha, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hi₀]
    linarith [h' i₀ j]
  have hrel : a • z + (-1 : ℝ) • w = 0 := by
    funext j
    have hj := congrFun hw j
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, smul_eq_mul,
      hj, Pi.smul_apply, smul_eq_mul]
    ring
  exact absurd ((LinearIndependent.pair_iff.mp hzw) a (-1) hrel).2 (by norm_num)

/-- A linear form with `ev z = 1`, `ev w = 0` (built from a nonzero minor). -/
def dualU {n : ℕ} (z w : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Mon 1 n → ℝ :=
  (w j / (z i * w j - z j * w i)) • unitMon (R := ℝ) (eMon n i)
    + (-(w i) / (z i * w j - z j * w i)) • unitMon (R := ℝ) (eMon n j)

/-- A linear form with `ev z = 0`, `ev w = 1` (built from a nonzero minor). -/
def dualW {n : ℕ} (z w : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : Mon 1 n → ℝ :=
  (-(z j) / (z i * w j - z j * w i)) • unitMon (R := ℝ) (eMon n i)
    + (z i / (z i * w j - z j * w i)) • unitMon (R := ℝ) (eMon n j)

lemma formEvalR_dualU {n : ℕ} (z w : Fin (n + 1) → ℝ) {i j : Fin (n + 1)}
    (hij : z i * w j - z j * w i ≠ 0) :
    formEvalR 1 n (dualU z w i j) z = 1 ∧ formEvalR 1 n (dualU z w i j) w = 0 := by
  constructor
  · rw [dualU, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_unitMon,
      formEvalR_unitMon, veronese_eMonR, veronese_eMonR,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hij]
    ring
  · rw [dualU, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_unitMon,
      formEvalR_unitMon, veronese_eMonR, veronese_eMonR,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]
    left; ring

lemma formEvalR_dualW {n : ℕ} (z w : Fin (n + 1) → ℝ) {i j : Fin (n + 1)}
    (hij : z i * w j - z j * w i ≠ 0) :
    formEvalR 1 n (dualW z w i j) z = 0 ∧ formEvalR 1 n (dualW z w i j) w = 1 := by
  constructor
  · rw [dualW, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_unitMon,
      formEvalR_unitMon, veronese_eMonR, veronese_eMonR,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]
    left; ring
  · rw [dualW, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_unitMon,
      formEvalR_unitMon, veronese_eMonR, veronese_eMonR,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hij]
    ring

/-- `dualU` and `dualW` span a complement to the linear forms vanishing at both points. -/
lemma top_le_span_dualU_dualW {n : ℕ} (z w : Fin (n + 1) → ℝ) {i j : Fin (n + 1)}
    (hij : z i * w j - z j * w i ≠ 0) :
    (⊤ : Submodule ℝ (Mon 1 n → ℝ))
      ≤ Submodule.span ℝ {dualU z w i j, dualW z w i j} ⊔ Lam 1 n z w := by
  intro F _
  obtain ⟨hUz, hUw⟩ := formEvalR_dualU z w hij
  obtain ⟨hWz, hWw⟩ := formEvalR_dualW z w hij
  have hmem : (F + (-(formEvalR 1 n F z)) • dualU z w i j
      + (-(formEvalR 1 n F w)) • dualW z w i j) ∈ Lam 1 n z w := by
    rw [mem_Lam_iff]
    refine ⟨?_, ?_⟩
    · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul, hUz, hWz]
      ring
    · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul, hUw, hWw]
      ring
  rw [show F = ((formEvalR 1 n F z) • dualU z w i j
        + (formEvalR 1 n F w) • dualW z w i j)
      + (F + (-(formEvalR 1 n F z)) • dualU z w i j
          + (-(formEvalR 1 n F w)) • dualW z w i j) by module]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right hmem)
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left (Submodule.subset_span
        (Set.mem_insert_iff.mpr (Or.inl rfl))))
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left (Submodule.subset_span
        (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))))

/-! ## The product as a linear map in its first argument -/

/-- `A ↦ mulVec a b d A B` as a real linear map. -/
def mulVecRgen {n : ℕ} (a b d : ℕ) (B : Mon b n → ℝ) : (Mon a n → ℝ) →ₗ[ℝ] (Mon d n → ℝ) where
  toFun A := mulVec a b d A B
  map_add' A A' := mulVec_add_left A A' B
  map_smul' c A := mulVec_smul_left c A B

@[simp] lemma mulVecRgen_apply {n : ℕ} (a b d : ℕ) (B : Mon b n → ℝ) (A : Mon a n → ℝ) :
    mulVecRgen a b d B A = mulVec a b d A B := rfl

/-- Multiplying the constant form `1` (a degree-`0` form) by `Q` gives `Q`. -/
lemma mulVec_zero_unitMon {b n : ℕ} (Q : Mon b n → ℝ) :
    mulVec 0 b b (unitMon (R := ℝ) (zeroMon n)) Q = Q := by
  funext M
  rw [mulVec]
  rw [Finset.sum_eq_single (zeroMon n)]
  · rw [Finset.sum_eq_single M]
    · rw [if_pos (fun i => by simp [zeroMon]), unitMon_same, one_mul]
    · intro q _ hq
      rw [if_neg]
      intro hc
      exact hq (by
        apply Subtype.ext; funext i; apply Fin.ext
        have := hc i; simp only [zeroMon, Pi.zero_apply] at this; omega)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro p _ hp
    apply Finset.sum_eq_zero
    intro q _
    rw [unitMon_of_ne hp, zero_mul]
    split <;> rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Basic properties of `Lam` and `Lam2V` -/

theorem Lam2V_le_Lam (a n : ℕ) (z w : Fin (n + 1) → ℝ) :
    Lam2V a (a + 2) n z w ≤ Lam (a + 2) n z w := by
  rw [Lam2V, Submodule.span_le]
  rintro B ⟨G, Q, hQ, rfl⟩
  have hQ' := mem_Lam_iff.mp hQ
  refine mem_Lam_iff.mpr ⟨?_, ?_⟩
  · rw [Work.HP.Sig2.LiftTwo.mulVec_formEvalR', hQ'.1, mul_zero]
  · rw [Work.HP.Sig2.LiftTwo.mulVec_formEvalR', hQ'.2, mul_zero]

theorem Lam2V_zero (n : ℕ) (z w : Fin (n + 1) → ℝ) :
    Lam2V 0 2 n z w = Lam 2 n z w := by
  refine le_antisymm (Lam2V_le_Lam 0 n z w) ?_
  intro Q hQ
  rw [Lam2V]
  exact Submodule.subset_span ⟨unitMon (R := ℝ) (zeroMon n), Q, hQ,
    (mulVec_zero_unitMon Q).symm⟩

lemma mulVec_formEvalR_11 {n : ℕ} (A B : Mon 1 n → ℝ) (z : Fin (n + 1) → ℝ) :
    formEvalR 2 n (mulVec 1 1 2 A B) z = formEvalR 1 n A z * formEvalR 1 n B z :=
  Work.HP.Sig2.LiftTwo.mulVec_formEvalR' A B z

/-- The product of a linear form vanishing at both points with any linear form vanishes at both
points. -/
lemma lam1_mul_lam1_le_lam2 {n : ℕ} (z w : Fin (n + 1) → ℝ) {l₁ l₂ : Mon 1 n → ℝ}
    (h : l₁ ∈ Lam 1 n z w) : mulVec 1 1 2 l₁ l₂ ∈ Lam 2 n z w := by
  have h' := mem_Lam_iff.mp h
  refine mem_Lam_iff.mpr ⟨?_, ?_⟩
  · rw [mulVec_formEvalR_11, h'.1, zero_mul]
  · rw [mulVec_formEvalR_11, h'.2, zero_mul]

/-- `Lam2V k (k+2)` is closed under right multiplication by a linear form, up to the next
degree:  `(Q·G)·U = Q·(G·U)`. -/
lemma mulVec_Lam2V_U {k n : ℕ} (z w : Fin (n + 1) → ℝ) (U : Mon 1 n → ℝ)
    {H : Mon (k + 2) n → ℝ} (hH : H ∈ Lam2V k (k + 2) n z w) :
    mulVec (k + 2) 1 (k + 3) H U ∈ Lam2V (k + 1) (k + 3) n z w := by
  have hgen : ∀ B ∈ { B : Mon (k + 2) n → ℝ |
        ∃ G : Mon k n → ℝ, ∃ Q : Mon 2 n → ℝ,
          Q ∈ Lam 2 n z w ∧ B = mulVec k 2 (k + 2) G Q },
      mulVecRgen (k + 2) 1 (k + 3) U B ∈ Lam2V (k + 1) (k + 3) n z w := by
    rintro B ⟨G, Q, hQ, rfl⟩
    rw [mulVecRgen_apply,
      ← mulVec_assoc (a := k) (b := 2) (c := 1) (d := k + 3) G Q U,
      mulVec_symm (A := Q) (B := U)]
    show mulVec k (1 + 2) (k + 3) G (mulVec 1 2 (1 + 2) U Q)
      ∈ Lam2V (k + 1) (k + 3) n z w
    rw [mulVec_assoc (a := k) (b := 1) (c := 2) (d := k + 3) G U Q]
    exact Submodule.subset_span ⟨mulVec k 1 (k + 1) G U, Q, hQ, rfl⟩
  have hle : Submodule.span ℝ { B : Mon (k + 2) n → ℝ |
        ∃ G : Mon k n → ℝ, ∃ Q : Mon 2 n → ℝ,
          Q ∈ Lam 2 n z w ∧ B = mulVec k 2 (k + 2) G Q }
      ≤ Submodule.comap (mulVecRgen (k + 2) 1 (k + 3) U) (Lam2V (k + 1) (k + 3) n z w) :=
    Submodule.span_le.mpr (fun B hB => hgen B hB)
  exact Submodule.mem_comap.mp (hle hH)

/-- The same with the multiplication reversed (used for `W`). -/
lemma mulVec_W_Lam2V {k n : ℕ} (z w : Fin (n + 1) → ℝ) (W : Mon 1 n → ℝ)
    {H : Mon (k + 2) n → ℝ} (hH : H ∈ Lam2V k (k + 2) n z w) :
    mulVec 1 (k + 2) (k + 3) W H ∈ Lam2V (k + 1) (k + 3) n z w := by
  rw [mulVec_symm (A := W) (B := H)]
  exact mulVec_Lam2V_U z w W hH

/-! ## The main spanning theorem -/

/-- `V_1 = span{U,W} + Lam 1` for two linear forms with `ev_z U = 1`, `ev_w U = 0` and
`ev_z W = 0`, `ev_w W = 1`. -/
lemma top_le_span_UW_Lam1 {n : ℕ} (z w : Fin (n + 1) → ℝ) (U W : Mon 1 n → ℝ)
    (hU : formEvalR 1 n U z = 1 ∧ formEvalR 1 n U w = 0)
    (hW : formEvalR 1 n W z = 0 ∧ formEvalR 1 n W w = 1) :
    (⊤ : Submodule ℝ (Mon 1 n → ℝ)) ≤ Submodule.span ℝ {U, W} ⊔ Lam 1 n z w := by
  intro F _
  have hmem : (F + (-(formEvalR 1 n F z)) • U + (-(formEvalR 1 n F w)) • W)
      ∈ Lam 1 n z w := by
    rw [mem_Lam_iff]
    refine ⟨?_, ?_⟩
    · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul, hU.1, hW.1]; ring
    · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul, hU.2, hW.2]; ring
  rw [show F = ((formEvalR 1 n F z) • U + (formEvalR 1 n F w) • W)
      + (F + (-(formEvalR 1 n F z)) • U + (-(formEvalR 1 n F w)) • W) by module]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right hmem)
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl))))
  · exact Submodule.smul_mem _ _
      (Submodule.mem_sup_left (Submodule.subset_span
        (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl)))))

/-- Multiplying a degree-`(k+2)` form by a linear form `μ` vanishing at both points lands in
`Lam2V (k+1) (k+3)`. -/
lemma lam1_mul_V_le_Lam2V {k n : ℕ} (z w : Fin (n + 1) → ℝ) {μ : Mon 1 n → ℝ}
    (hμ : μ ∈ Lam 1 n z w) (G : Mon (k + 2) n → ℝ) :
    mulVec (k + 2) 1 (k + 3) G μ ∈ Lam2V (k + 1) (k + 3) n z w := by
  have hle : (⊤ : Submodule ℝ (Mon (k + 2) n → ℝ)) ≤
      Submodule.comap (mulVecRgen (k + 2) 1 (k + 3) μ) (Lam2V (k + 1) (k + 3) n z w) := by
    rw [← span_one_mul (k + 1) n, Submodule.span_le]
    rintro _ ⟨⟨H, l⟩, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [mulVecRgen_apply,
      ← mulVec_assoc (a := k + 1) (b := 1) (c := 1) (d := k + 3) H l μ]
    refine Submodule.subset_span ⟨H, mulVec 1 1 2 l μ, ?_, rfl⟩
    rw [mulVec_symm (A := l) (B := μ)]
    exact lam1_mul_lam1_le_lam2 z w hμ
  exact Submodule.mem_comap.mp (hle (Submodule.mem_top))

/-- The `U`-multiple of `Lam2V k (k+2) ⊕ span{U^{k+2}, W^{k+2}}` lies in
`Lam2V (k+1) (k+3) ⊕ span{U^{k+3}, W^{k+3}}`. -/
lemma mulVec_U_mem {k n : ℕ} (z w : Fin (n + 1) → ℝ) (U W : Mon 1 n → ℝ)
    (hUW : mulVec 1 1 2 U W ∈ Lam 2 n z w) {G : Mon (k + 2) n → ℝ}
    (hG : G ∈ Lam2V k (k + 2) n z w ⊔ Submodule.span ℝ {powLin U (k + 2), powLin W (k + 2)}) :
    mulVec (k + 2) 1 (k + 3) G U ∈ Lam2V (k + 1) (k + 3) n z w
      ⊔ Submodule.span ℝ {powLin U (k + 3), powLin W (k + 3)} := by
  obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := Submodule.mem_sup.mp hG
  rw [mulVec_add_left]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left (mulVec_Lam2V_U z w U hG₁)) ?_
  have hle : Submodule.span ℝ {powLin U (k + 2), powLin W (k + 2)} ≤
      Submodule.comap (mulVecRgen (k + 2) 1 (k + 3) U)
        (Lam2V (k + 1) (k + 3) n z w
          ⊔ Submodule.span ℝ {powLin U (k + 3), powLin W (k + 3)}) := by
    rw [Submodule.span_le]
    rintro B (rfl | rfl)
    · refine Submodule.mem_comap.mpr ?_
      rw [mulVecRgen_apply, ← powLin_succ U (k + 2)]
      exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · refine Submodule.mem_comap.mpr ?_
      rw [mulVecRgen_apply, powLin_succ W (k + 1),
        ← mulVec_assoc (a := k + 1) (b := 1) (c := 1) (d := k + 3) (powLin W (k + 1)) W U,
        mulVec_symm (A := W) (B := U)]
      exact Submodule.mem_sup_left (Submodule.subset_span
        ⟨powLin W (k + 1), mulVec 1 1 2 U W, hUW, rfl⟩)
  exact Submodule.mem_comap.mp (hle hG₂)

/-- The `W`-multiple. -/
lemma mulVec_W_mem {k n : ℕ} (z w : Fin (n + 1) → ℝ) (U W : Mon 1 n → ℝ)
    (hUW : mulVec 1 1 2 U W ∈ Lam 2 n z w) {G : Mon (k + 2) n → ℝ}
    (hG : G ∈ Lam2V k (k + 2) n z w ⊔ Submodule.span ℝ {powLin U (k + 2), powLin W (k + 2)}) :
    mulVec (k + 2) 1 (k + 3) G W ∈ Lam2V (k + 1) (k + 3) n z w
      ⊔ Submodule.span ℝ {powLin U (k + 3), powLin W (k + 3)} := by
  obtain ⟨G₁, hG₁, G₂, hG₂, rfl⟩ := Submodule.mem_sup.mp hG
  rw [mulVec_add_left]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.mem_sup_left ?_
    rw [mulVec_symm (A := G₁) (B := W)]
    exact mulVec_W_Lam2V z w W hG₁
  · have hle : Submodule.span ℝ {powLin U (k + 2), powLin W (k + 2)} ≤
        Submodule.comap (mulVecRgen (k + 2) 1 (k + 3) W)
          (Lam2V (k + 1) (k + 3) n z w
            ⊔ Submodule.span ℝ {powLin U (k + 3), powLin W (k + 3)}) := by
      rw [Submodule.span_le]
      rintro B (rfl | rfl)
      · refine Submodule.mem_comap.mpr ?_
        rw [mulVecRgen_apply, powLin_succ U (k + 1),
          ← mulVec_assoc (a := k + 1) (b := 1) (c := 1) (d := k + 3) (powLin U (k + 1)) U W]
        exact Submodule.mem_sup_left (Submodule.subset_span
          ⟨powLin U (k + 1), mulVec 1 1 2 U W, hUW, rfl⟩)
      · refine Submodule.mem_comap.mpr ?_
        rw [mulVecRgen_apply, ← powLin_succ W (k + 2)]
        exact Submodule.mem_sup_right (Submodule.subset_span
          (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))))
    exact Submodule.mem_comap.mp (hle hG₂)

/-- **The inductive spanning statement.** -/
theorem Lam_gen_aux {n : ℕ} (z w : Fin (n + 1) → ℝ) (U W : Mon 1 n → ℝ)
    (hU : formEvalR 1 n U z = 1 ∧ formEvalR 1 n U w = 0)
    (hW : formEvalR 1 n W z = 0 ∧ formEvalR 1 n W w = 1) (k : ℕ) :
    (⊤ : Submodule ℝ (Mon (k + 2) n → ℝ)) ≤ Lam2V k (k + 2) n z w
      ⊔ Submodule.span ℝ {powLin U (k + 2), powLin W (k + 2)} := by
  have hUW : mulVec 1 1 2 U W ∈ Lam 2 n z w := by
    refine mem_Lam_iff.mpr ⟨?_, ?_⟩
    · rw [mulVec_formEvalR_11, hU.1, hW.1, mul_zero]
    · rw [mulVec_formEvalR_11, hU.2, hW.2, zero_mul]
  induction k with
  | zero =>
      intro F _
      have hUev : formEvalR 2 n (powLin U 2) z = 1 ∧ formEvalR 2 n (powLin U 2) w = 0 :=
        ⟨by rw [formEvalR_powLin, hU.1]; norm_num,
         by rw [formEvalR_powLin, hU.2]; norm_num⟩
      have hWev : formEvalR 2 n (powLin W 2) z = 0 ∧ formEvalR 2 n (powLin W 2) w = 1 :=
        ⟨by rw [formEvalR_powLin, hW.1]; norm_num,
         by rw [formEvalR_powLin, hW.2]; norm_num⟩
      have hrem : (F + (-(formEvalR 2 n F z)) • powLin U 2
          + (-(formEvalR 2 n F w)) • powLin W 2) ∈ Lam 2 n z w := by
        rw [mem_Lam_iff]
        refine ⟨?_, ?_⟩
        · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul,
            hUev.1, hWev.1]; ring
        · rw [formEvalR_add, formEvalR_add, formEvalR_smul, formEvalR_smul,
            hUev.2, hWev.2]; ring
      rw [show F = ((formEvalR 2 n F z) • powLin U 2 + (formEvalR 2 n F w) • powLin W 2)
          + (F + (-(formEvalR 2 n F z)) • powLin U 2
              + (-(formEvalR 2 n F w)) • powLin W 2) by module]
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.mem_sup_right ?_
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl)))
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))))
      · refine Submodule.mem_sup_left ?_
        rw [show Lam2V 0 (0 + 2) n z w = Lam 2 n z w from Lam2V_zero n z w]
        exact hrem
  | succ k ih =>
      rw [← span_one_mul (k + 2) n, Submodule.span_le]
      rintro _ ⟨⟨G, l⟩, rfl⟩
      dsimp only
      have hl : l ∈ Submodule.span ℝ {U, W} ⊔ Lam 1 n z w :=
        top_le_span_UW_Lam1 z w U W hU hW (Submodule.mem_top)
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hl
      rw [Submodule.mem_span_pair] at hp
      obtain ⟨c₁, c₂, hc⟩ := hp
      have hleq : l = c₁ • U + c₂ • W + q := by rw [← hpq, hc]
      rw [hleq, mulVec_add_right, mulVec_add_right, mulVec_smul_right, mulVec_smul_right]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
        (Submodule.mem_sup_left (lam1_mul_V_le_Lam2V z w hq G))
      · exact Submodule.smul_mem _ _ (mulVec_U_mem z w U W hUW (ih (Submodule.mem_top)))
      · exact Submodule.smul_mem _ _ (mulVec_W_mem z w U W hUW (ih (Submodule.mem_top)))

/-- **The `Ψ`-lift spanning statement.**  The degree-`(a+2)` real forms through the two
independent points `z, w` are exactly the products of a degree-`a` form with a quadric through `z`
and `w`. -/
theorem Lam_gen_a (a n : ℕ) (z w : Fin (n + 1) → ℝ) (hzw : LinearIndependent ℝ ![z, w]) :
    Lam (a + 2) n z w = Lam2V a (a + 2) n z w := by
  obtain ⟨i, j, hij⟩ := exists_minor_ne z w hzw
  set U := dualU z w i j with hUdef
  set W := dualW z w i j with hWdef
  have hU : formEvalR 1 n U z = 1 ∧ formEvalR 1 n U w = 0 := formEvalR_dualU z w hij
  have hW : formEvalR 1 n W z = 0 ∧ formEvalR 1 n W w = 1 := formEvalR_dualW z w hij
  refine le_antisymm ?_ (Lam2V_le_Lam a n z w)
  intro F hF
  have hmem : F ∈ Lam2V a (a + 2) n z w
      ⊔ Submodule.span ℝ {powLin U (a + 2), powLin W (a + 2)} :=
    Lam_gen_aux z w U W hU hW a (Submodule.mem_top)
  obtain ⟨F₀, hF₀, B, hB, hFB⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hB
  have hBlam : B ∈ Lam (a + 2) n z w := by
    have h1 : B = F + (-1 : ℝ) • F₀ := by rw [← hFB]; module
    rw [h1]
    exact Submodule.add_mem _ hF (Submodule.smul_mem _ _ (Lam2V_le_Lam a n z w hF₀))
  have hc1 : c₁ = 0 := by
    have h := (mem_Lam_iff.mp hBlam).1
    rw [← hc, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_powLin,
      formEvalR_powLin, hU.1, hW.1] at h
    rw [one_pow, mul_one, zero_pow (by omega : a + 2 ≠ 0), mul_zero, add_zero] at h
    exact h
  have hc2 : c₂ = 0 := by
    have h := (mem_Lam_iff.mp hBlam).2
    rw [← hc, formEvalR_add, formEvalR_smul, formEvalR_smul, formEvalR_powLin,
      formEvalR_powLin, hU.2, hW.2] at h
    rw [zero_pow (by omega : a + 2 ≠ 0), mul_zero, one_pow, mul_one, zero_add] at h
    exact h
  have hB0 : B = 0 := by rw [← hc, hc1, hc2, zero_smul, zero_smul, add_zero]
  rw [← hFB, hB0, add_zero]
  exact hF₀


end Aux
end Work.HP.Vero
