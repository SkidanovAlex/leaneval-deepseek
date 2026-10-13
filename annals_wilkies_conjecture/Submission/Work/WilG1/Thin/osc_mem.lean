/-
  WilG1 / Thin — the one-sided oscillation sets of a definable unary function are `Ω`-sets.

  `oscR g q` (resp. `oscL g q`) is the set of `x` where points to the right (resp. left) of `x`
  with difference quotient `> q` and with difference quotient `< q` accumulate at `x`.  We show
  that both transport to `S.Ω (F + 1000) ((C 1000 * (X + C 1)).eval D) 1` whenever the graph of
  `g` is in `S.Ω F D 2`.

  The proof is a first-order formula construction.  Writing `x = z 0`, `v = z 1`, `δ = z 2`,
  `y = z 3`, `u = z 4`, the "body" predicate of the formula is the conjunction of three strict
  inequalities and the graph atom `(y,u) ∈ X`; `oscBody` collects these as an `Ω`-set in `ℝ⁵`.
  Eliminating `y, u` (two `projLast`s), complementing, intersecting with `δ > 0`, projecting `δ`
  away, complementing again (`¬∃δ>0, ¬body` is `∀δ>0, body`), intersecting with the graph slice
  and projecting `v` away yields the set of `x`; each step costs a bounded amount of format and
  the degrees add.  The four instances (right/left window, upward/downward value inequality)
  are the four combinations of `winR*`/`winL*` with `valUp`/`valDn`.

  The last ingredient is the arithmetic identity `y > x ⟹ (q < (g y - g x)/(y - x) ↔
  q(y-x) < g y - g x)`, and for `y < x` the same with the inequality reversed (`dq_lt_iff`,
  `lt_dq_iff`).
-/
import Mathlib
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.Main
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture

/-! ## 0. Vector bookkeeping -/

@[simp] lemma osc_init_zero (z : Fin 2 → ℝ) : Fin.init z 0 = z 0 := rfl

@[simp] lemma osc_snoc2 (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) = ![z 0, t] := by
  funext i; fin_cases i <;> simp [Fin.snoc] <;> try congr 1
@[simp] lemma osc_snoc3 (z : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 3 → ℝ) = ![z 0, z 1, t] := by
  funext i; fin_cases i <;> simp [Fin.snoc] <;> try congr 1
@[simp] lemma osc_snoc4 (z : Fin 3 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 4 → ℝ) = ![z 0, z 1, z 2, t] := by
  funext i; fin_cases i <;> simp [Fin.snoc] <;> try congr 1
@[simp] lemma osc_snoc5 (z : Fin 4 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 5 → ℝ) = ![z 0, z 1, z 2, z 3, t] := by
  funext i; fin_cases i <;> simp [Fin.snoc] <;> try congr 1

/-- The substitution `Fin 2 → Fin 5` picking the value coordinates `y, u`. -/
def iota34 : Fin 2 → Fin 5 := ![3, 4]

@[simp] lemma comp_iota34 (z : Fin 5 → ℝ) : z ∘ iota34 = ![z 3, z 4] := by
  funext j; fin_cases j <;> rfl

/-! ## 1. The graph and the window/value polynomials -/

/-- The graph of `g : ℝ → ℝ` inside `ℝ²`. -/
def oscGraph (g : ℝ → ℝ) : Set (Fin 2 → ℝ) := graphOf (fun x : Fin 1 → ℝ => g (x 0))

lemma mem_oscGraph {g : ℝ → ℝ} (z : Fin 2 → ℝ) : z ∈ oscGraph g ↔ z 1 = g (z 0) := by
  simp [oscGraph, graphOf]

/-- The right window: `0 < y - x`. -/
def winR1 : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 3 - MvPolynomial.X 0

/-- The right window: `0 < x + δ - y`. -/
def winR2 : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 0 + MvPolynomial.X 2 - MvPolynomial.X 3

/-- The left window: `0 < y - (x - δ)`. -/
def winL1 : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 3 + MvPolynomial.X 2 - MvPolynomial.X 0

/-- The left window: `0 < x - y`. -/
def winL2 : MvPolynomial (Fin 5) ℝ := MvPolynomial.X 0 - MvPolynomial.X 3

/-- The upward value inequality `0 < (u - v) - q(y - x)`. -/
def valUp (q : ℝ) : MvPolynomial (Fin 5) ℝ :=
  (MvPolynomial.X 4 - MvPolynomial.X 1) - MvPolynomial.C q * (MvPolynomial.X 3 - MvPolynomial.X 0)

/-- The downward value inequality `0 < q(y - x) - (u - v)`. -/
def valDn (q : ℝ) : MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.C q * (MvPolynomial.X 3 - MvPolynomial.X 0) - (MvPolynomial.X 4 - MvPolynomial.X 1)

lemma eval_winR1 (x v δ y u : ℝ) : MvPolynomial.eval ![x,v,δ,y,u] winR1 = y - x := by
  simp [winR1, Matrix.cons_val]
lemma eval_winR2 (x v δ y u : ℝ) : MvPolynomial.eval ![x,v,δ,y,u] winR2 = x + δ - y := by
  simp [winR2, Matrix.cons_val]
lemma eval_winL1 (x v δ y u : ℝ) : MvPolynomial.eval ![x,v,δ,y,u] winL1 = y + δ - x := by
  simp [winL1, Matrix.cons_val]
lemma eval_winL2 (x v δ y u : ℝ) : MvPolynomial.eval ![x,v,δ,y,u] winL2 = x - y := by
  simp [winL2, Matrix.cons_val]
lemma eval_valUp (q x v δ y u : ℝ) :
    MvPolynomial.eval ![x,v,δ,y,u] (valUp q) = (u - v) - q * (y - x) := by
  simp [valUp, Matrix.cons_val]
lemma eval_valDn (q x v δ y u : ℝ) :
    MvPolynomial.eval ![x,v,δ,y,u] (valDn q) = q * (y - x) - (u - v) := by
  simp [valDn, Matrix.cons_val]

/-! ## 2. Degree bookkeeping for the atoms -/

lemma td_sub_le_one (i j : Fin 5) :
    ((MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin 5) ℝ)).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩

lemma td_lin_le_one (a b c : Fin 5) :
    ((MvPolynomial.X a + MvPolynomial.X b - MvPolynomial.X c : MvPolynomial (Fin 5) ℝ)).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  constructor
  · refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [max_le_iff]
    exact ⟨by simp [MvPolynomial.totalDegree_X], by simp [MvPolynomial.totalDegree_X]⟩
  · simp [MvPolynomial.totalDegree_X]

lemma td_C_mul_le_one (q : ℝ) (i j : Fin 5) :
    ((MvPolynomial.C q * (MvPolynomial.X i - MvPolynomial.X j) : MvPolynomial (Fin 5) ℝ)).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C]
  have h := td_sub_le_one i j
  omega

lemma td_valUp (q : ℝ) : (valUp q).totalDegree ≤ 2 := by
  rw [valUp]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_trans (td_sub_le_one 4 1) (by norm_num), le_trans (td_C_mul_le_one q 3 0) (by norm_num)⟩

lemma td_valDn (q : ℝ) : (valDn q).totalDegree ≤ 2 := by
  rw [valDn]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  exact ⟨le_trans (td_C_mul_le_one q 3 0) (by norm_num), le_trans (td_sub_le_one 4 1) (by norm_num)⟩

lemma td_winR1 : winR1.totalDegree ≤ 2 := le_trans (td_sub_le_one 3 0) (by norm_num)
lemma td_winR2 : winR2.totalDegree ≤ 2 := le_trans (td_lin_le_one 0 2 3) (by norm_num)
lemma td_winL1 : winL1.totalDegree ≤ 2 := le_trans (td_lin_le_one 3 2 0) (by norm_num)
lemma td_winL2 : winL2.totalDegree ≤ 2 := le_trans (td_sub_le_one 0 3) (by norm_num)

/-! ## 3. The body of the formula, the accumulated set, the final set -/

/-- The body of the oscillation formula on the five coordinates `(x, v, δ, y, u)`: the two
window inequalities, the value inequality and the graph atom. -/
def oscBody (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) : Set (Fin 5 → ℝ) :=
  {z | 0 < MvPolynomial.eval z P ∧ 0 < MvPolynomial.eval z Q ∧ 0 < MvPolynomial.eval z R ∧
    (![z 3, z 4] : Fin 2 → ℝ) ∈ X}

/-- `(x, v)` such that for every `δ > 0` there are `y, u` satisfying the body. -/
def oscAccum (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) : Set (Fin 2 → ℝ) :=
  {z | ∀ δ : ℝ, 0 < δ → ∃ y u : ℝ, (![z 0, z 1, δ, y, u] : Fin 5 → ℝ) ∈ oscBody X P Q R}

/-- `x` such that `(x, v) ∈ X` for some `v` and the accumulation condition holds. -/
def oscGeneric (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) : Set (Fin 1 → ℝ) :=
  {w | ∃ v : ℝ, (![w 0, v] : Fin 2 → ℝ) ∈ X ∧ (Fin.snoc w v) ∈ oscAccum X P Q R}

lemma mem_oscBody (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) (x v δ y u : ℝ) :
    (![x, v, δ, y, u] : Fin 5 → ℝ) ∈ oscBody X P Q R ↔
      0 < MvPolynomial.eval ![x, v, δ, y, u] P ∧ 0 < MvPolynomial.eval ![x, v, δ, y, u] Q ∧
      0 < MvPolynomial.eval ![x, v, δ, y, u] R ∧ (![y, u] : Fin 2 → ℝ) ∈ X := by
  simp only [oscBody, Set.mem_ofPred_eq, Matrix.cons_val]

lemma mem_oscGeneric (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) (w : Fin 1 → ℝ) :
    w ∈ oscGeneric X P Q R ↔ ∃ v : ℝ, (![w 0, v] : Fin 2 → ℝ) ∈ X ∧
      ∀ δ : ℝ, 0 < δ → ∃ y u : ℝ, (![w 0, v, δ, y, u] : Fin 5 → ℝ) ∈ oscBody X P Q R := by
  simp only [oscGeneric, oscAccum, Set.mem_ofPred_eq, osc_snoc2, osc_snoc3, osc_snoc4, osc_snoc5,
    Matrix.cons_val]

/-- Eliminating the witnesses `y, u` and negating gives the accumulation condition. -/
lemma compl_projLast_inter_pos (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) :
    (projLast ({z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ))ᶜ
      = oscAccum X P Q R := by
  ext z
  simp only [Set.mem_compl_iff, projLast, Set.mem_inter_iff, Set.mem_ofPred_eq, oscAccum,
    osc_snoc3, osc_snoc4, osc_snoc5]
  constructor
  · intro h δ hδ
    by_contra hc
    exact h ⟨δ, hδ, hc⟩
  · rintro h ⟨δ, hδ, hc⟩
    exact hc (h δ hδ)

/-- Eliminating the witness `v` after intersecting with the graph. -/
lemma projLast_inter_oscAccum (X : Set (Fin 2 → ℝ)) (P Q R : MvPolynomial (Fin 5) ℝ) :
    projLast (X ∩ oscAccum X P Q R) = oscGeneric X P Q R := by
  ext w
  simp only [projLast, oscGeneric, Set.mem_inter_iff, Set.mem_ofPred_eq, oscAccum,
    osc_snoc2, osc_snoc3, osc_snoc4, osc_snoc5]

/-! ## 4. The format/degree bounds carried through the chain -/

def deg0 : Polynomial ℕ := Polynomial.C 4 * Polynomial.X + Polynomial.C 20
def deg1 : Polynomial ℕ := Polynomial.C 8 * Polynomial.X + Polynomial.C 60
def deg2 : Polynomial ℕ := Polynomial.C 20 * Polynomial.X + Polynomial.C 200

/-! ## 5. The two Ω-membership steps -/

/-- The body is an `Ω`-set. -/
theorem oscBody_mem {S : WilkiesDesign.SOMin} {F D : ℕ} {X : Set (Fin 2 → ℝ)}
    (hX : X ∈ S.Ω F D 2) (P Q R : MvPolynomial (Fin 5) ℝ)
    (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2) (hR : R.totalDegree ≤ 2) :
    oscBody X P Q R ∈ S.Ω (F + 40) (deg0.eval D) 5 := by
  have h1 : {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z P} ∈ S.Ω (F + 30) ((Polynomial.C 4).eval D) 5 := by
    refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D P) (by omega) ?_
    simp only [Polynomial.eval_C]
    omega
  have h2 : {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z Q} ∈ S.Ω (F + 30) ((Polynomial.C 4).eval D) 5 := by
    refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D Q) (by omega) ?_
    simp only [Polynomial.eval_C]
    omega
  have h3 : {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z R} ∈ S.Ω (F + 30) ((Polynomial.C 4).eval D) 5 := by
    refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D R) (by omega) ?_
    simp only [Polynomial.eval_C]
    omega
  have h4 : {z : Fin 5 → ℝ | z ∘ iota34 ∈ X} ∈ S.Ω (F + 30) ((Polynomial.X + Polynomial.C 2).eval D) 5 := by
    refine Work.WilG1.Omega.mono (Work.WilG0.substSet_mem (S := S) hX 5 iota34) (by omega) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain h12 := Work.WilG0.Omega_inter2 h1 h2
  have h3' := Work.WilG0.Omega_mono_F (F := F + 30) (F' := F + 31) (by omega) h3
  obtain h123 := Work.WilG0.Omega_inter2 h12 h3'
  have h4' := Work.WilG0.Omega_mono_F (F := F + 30) (F' := F + 32) (by omega) h4
  obtain h1234 := Work.WilG0.Omega_inter2 h123 h4'
  have hset : {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z P} ∩ {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z Q} ∩
      {z : Fin 5 → ℝ | 0 < MvPolynomial.eval z R} ∩ {z : Fin 5 → ℝ | z ∘ iota34 ∈ X}
      = oscBody X P Q R := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, oscBody, comp_iota34]
    tauto
  rw [hset] at h1234
  refine Work.WilG1.Omega.mono h1234 (by omega) ?_
  simp only [deg0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- The final set of the formula is an `Ω`-set. -/
theorem oscGeneric_mem {S : WilkiesDesign.SOMin} {F D : ℕ} {X : Set (Fin 2 → ℝ)}
    (hX : X ∈ S.Ω F D 2) (P Q R : MvPolynomial (Fin 5) ℝ)
    (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2) (hR : R.totalDegree ≤ 2) :
    oscGeneric X P Q R ∈ S.Ω (F + 100) (deg2.eval D) 1 := by
  have h5 : oscBody X P Q R ∈ S.Ω (F + 40) (deg0.eval D) 5 := oscBody_mem hX P Q R hP hQ hR
  have h4 := Work.WilG1.Omega.projLast_mem (S := S) (n := 4) (a := F + 40) (b := deg0) (D := D) h5
  have h3 := Work.WilG1.Omega.projLast_mem (S := S) (n := 3) (a := F + 41) (b := deg0) (D := D) h4
  have h3c : (projLast (projLast (oscBody X P Q R)))ᶜ ∈ S.Ω (F + 43) (deg0.eval D) 3 :=
    Work.WilG1.Omega.mono (S.compl h3) (by omega) le_rfl
  have hpos : {z : Fin 3 → ℝ | 0 < z 2} ∈ S.Ω (F + 43) (deg0.eval D) 3 := by
    have h0 : {z : Fin 3 → ℝ | 0 < MvPolynomial.eval z (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ)}
        ∈ S.Ω (F + 43) (deg0.eval D) 3 := by
      refine Work.WilG1.Omega.mono (Work.WilG1.Calc.pos_mem (S := S) D (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ)) (by omega) ?_
      simp only [MvPolynomial.totalDegree_X, deg0, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    simpa [MvPolynomial.eval_X] using h0
  have hn3 : {z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ
      ∈ S.Ω (F + 44) (deg0.eval D + deg0.eval D) 3 := Work.WilG0.Omega_inter2 hpos h3c
  have hn3' : {z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ
      ∈ S.Ω (F + 44) (deg1.eval D) 3 := by
    refine Work.WilG1.Omega.mono hn3 le_rfl ?_
    simp only [deg0, deg1, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  have hn2 := Work.WilG1.Omega.projLast_mem (S := S) (n := 2) (a := F + 44) (b := deg1) (D := D) hn3'
  have hf2 : (projLast ({z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ))ᶜ
      ∈ S.Ω (F + 46) (deg1.eval D) 2 := Work.WilG1.Omega.mono (S.compl hn2) (by omega) le_rfl
  have hX' : X ∈ S.Ω (F + 46) (deg1.eval D) 2 := by
    refine Work.WilG1.Omega.mono hX (by omega) ?_
    simp only [deg1, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  have hg2 : X ∩ (projLast ({z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ))ᶜ
      ∈ S.Ω (F + 47) (deg1.eval D + deg1.eval D) 2 := Work.WilG0.Omega_inter2 hX' hf2
  have hg2' : X ∩ (projLast ({z : Fin 3 → ℝ | 0 < z 2} ∩ (projLast (projLast (oscBody X P Q R)))ᶜ))ᶜ
      ∈ S.Ω (F + 47) (deg2.eval D) 2 := by
    refine Work.WilG1.Omega.mono hg2 le_rfl ?_
    simp only [deg1, deg2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  have hres := Work.WilG1.Omega.projLast_mem (S := S) (n := 1) (a := F + 47) (b := deg2) (D := D) hg2'
  rw [compl_projLast_inter_pos, projLast_inter_oscAccum] at hres
  exact Work.WilG1.Omega.mono hres (by omega) le_rfl

/-! ## 6. The difference quotient, cleared of denominators -/

lemma dq_lt_iff {g : ℝ → ℝ} {q x y : ℝ} (h : x < y) :
    q < Work.WilG1.dq g x y ↔ q * (y - x) < g y - g x := by
  rw [Work.WilG1.dq, lt_div_iff₀ (by linarith)]

lemma lt_dq_iff {g : ℝ → ℝ} {q x y : ℝ} (h : x < y) :
    Work.WilG1.dq g x y < q ↔ g y - g x < q * (y - x) := by
  rw [Work.WilG1.dq, div_lt_iff₀ (by linarith)]

lemma dq_lt_iff_neg {g : ℝ → ℝ} {q x y : ℝ} (h : y < x) :
    q < Work.WilG1.dq g x y ↔ g y - g x < q * (y - x) := by
  rw [Work.WilG1.dq, lt_div_iff_of_neg (by linarith)]

lemma lt_dq_iff_neg {g : ℝ → ℝ} {q x y : ℝ} (h : y < x) :
    Work.WilG1.dq g x y < q ↔ q * (y - x) < g y - g x := by
  rw [Work.WilG1.dq, div_lt_iff_of_neg (by linarith)]

/-! ## 7. The four instances -/

/-- The right-window, upward-value condition on `w : Fin 1 → ℝ`. -/
def oscSetRU (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {w | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, w 0 < y ∧ y < w 0 + δ ∧ q * (y - w 0) < g y - g (w 0)}

/-- The right-window, downward-value condition on `w : Fin 1 → ℝ`. -/
def oscSetRD (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {w | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, w 0 < y ∧ y < w 0 + δ ∧ g y - g (w 0) < q * (y - w 0)}

/-- The left-window, upward-value condition on `w : Fin 1 → ℝ`. -/
def oscSetLU (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {w | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, w 0 - δ < y ∧ y < w 0 ∧ q * (y - w 0) < g y - g (w 0)}

/-- The left-window, downward-value condition on `w : Fin 1 → ℝ`. -/
def oscSetLD (g : ℝ → ℝ) (q : ℝ) : Set (Fin 1 → ℝ) :=
  {w | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, w 0 - δ < y ∧ y < w 0 ∧ g y - g (w 0) < q * (y - w 0)}

/-- Eliminating the witnesses through the graph: only the value conditions remain. -/
lemma oscGeneric_oscGraph_iff {g : ℝ → ℝ} (P Q R : MvPolynomial (Fin 5) ℝ) (w : Fin 1 → ℝ) :
    w ∈ oscGeneric (oscGraph g) P Q R ↔
      ∀ δ : ℝ, 0 < δ → ∃ y : ℝ,
        0 < MvPolynomial.eval ![w 0, g (w 0), δ, y, g y] P ∧
        0 < MvPolynomial.eval ![w 0, g (w 0), δ, y, g y] Q ∧
        0 < MvPolynomial.eval ![w 0, g (w 0), δ, y, g y] R := by
  rw [mem_oscGeneric]
  constructor
  · rintro ⟨v, hv, h⟩ δ hδ
    obtain ⟨y, u, hb⟩ := h δ hδ
    rw [mem_oscBody] at hb
    obtain ⟨h1, h2, h3, h4⟩ := hb
    have hv' : v = g (w 0) := (mem_oscGraph _).mp hv
    have hu' : u = g y := (mem_oscGraph _).mp h4
    rw [hv', hu'] at h1 h2 h3
    exact ⟨y, h1, h2, h3⟩
  · intro h
    refine ⟨g (w 0), (mem_oscGraph _).mpr (by simp), ?_⟩
    intro δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    refine ⟨y, g y, ?_⟩
    rw [mem_oscBody]
    exact ⟨h1, h2, h3, (mem_oscGraph _).mpr (by simp)⟩

lemma oscGeneric_RU (g : ℝ → ℝ) (q : ℝ) :
    oscGeneric (oscGraph g) winR1 winR2 (valUp q) = oscSetRU g q := by
  ext w
  rw [oscGeneric_oscGraph_iff]
  simp only [oscSetRU, Set.mem_ofPred_eq, eval_winR1, eval_winR2, eval_valUp]
  constructor
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩

lemma oscGeneric_RD (g : ℝ → ℝ) (q : ℝ) :
    oscGeneric (oscGraph g) winR1 winR2 (valDn q) = oscSetRD g q := by
  ext w
  rw [oscGeneric_oscGraph_iff]
  simp only [oscSetRD, Set.mem_ofPred_eq, eval_winR1, eval_winR2, eval_valDn]
  constructor
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩

lemma oscGeneric_LU (g : ℝ → ℝ) (q : ℝ) :
    oscGeneric (oscGraph g) winL1 winL2 (valUp q) = oscSetLU g q := by
  ext w
  rw [oscGeneric_oscGraph_iff]
  simp only [oscSetLU, Set.mem_ofPred_eq, eval_winL1, eval_winL2, eval_valUp]
  constructor
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩

lemma oscGeneric_LD (g : ℝ → ℝ) (q : ℝ) :
    oscGeneric (oscGraph g) winL1 winL2 (valDn q) = oscSetLD g q := by
  ext w
  rw [oscGeneric_oscGraph_iff]
  simp only [oscSetLD, Set.mem_ofPred_eq, eval_winL1, eval_winL2, eval_valDn]
  constructor
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩
  · intro h δ hδ
    obtain ⟨y, h1, h2, h3⟩ := h δ hδ
    exact ⟨y, by linarith, by linarith, by linarith⟩

/-! ## 8. The identification with `oscR` and `oscL` -/

lemma oscSetRU_inter_RD (g : ℝ → ℝ) (q : ℝ) :
    oscSetRU g q ∩ oscSetRD g q = Work.WilG1.liftR (Work.WilG1.oscR g q) := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Work.WilG1.liftR, Work.WilG1.oscR]
  constructor
  · rintro ⟨hU, hD⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hU δ hδ
        exact ⟨y, h1, h2, (dq_lt_iff h1).mpr h3⟩,
      fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hD δ hδ
        exact ⟨y, h1, h2, (lt_dq_iff h1).mpr h3⟩⟩
  · rintro ⟨hU, hD⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hU δ hδ
        exact ⟨y, h1, h2, (dq_lt_iff h1).mp h3⟩,
      fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hD δ hδ
        exact ⟨y, h1, h2, (lt_dq_iff h1).mp h3⟩⟩

lemma oscSetLU_inter_LD (g : ℝ → ℝ) (q : ℝ) :
    oscSetLU g q ∩ oscSetLD g q = Work.WilG1.liftR (Work.WilG1.oscL g q) := by
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Work.WilG1.liftR, Work.WilG1.oscL]
  constructor
  · rintro ⟨hU, hD⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hD δ hδ
        exact ⟨y, h1, h2, (dq_lt_iff_neg h2).mpr h3⟩,
      fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hU δ hδ
        exact ⟨y, h1, h2, (lt_dq_iff_neg h2).mpr h3⟩⟩
  · rintro ⟨hU, hD⟩
    exact ⟨fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hD δ hδ
        exact ⟨y, h1, h2, (lt_dq_iff_neg h2).mp h3⟩,
      fun δ hδ => by
        obtain ⟨y, h1, h2, h3⟩ := hU δ hδ
        exact ⟨y, h1, h2, (dq_lt_iff_neg h2).mp h3⟩⟩

/-! ## 9. The theorem -/

theorem osc_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    (Work.WilG1.liftR (Work.WilG1.oscR g q) ∈
        S.Ω (F + 1000) ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1) ∧
    (Work.WilG1.liftR (Work.WilG1.oscL g q) ∈
        S.Ω (F + 1000) ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1) := by
  have hgr : oscGraph g ∈ S.Ω F D 2 := hg
  have hRU := oscGeneric_mem (S := S) hgr winR1 winR2 (valUp q) td_winR1 td_winR2 (td_valUp q)
  have hRD := oscGeneric_mem (S := S) hgr winR1 winR2 (valDn q) td_winR1 td_winR2 (td_valDn q)
  have hLU := oscGeneric_mem (S := S) hgr winL1 winL2 (valUp q) td_winL1 td_winL2 (td_valUp q)
  have hLD := oscGeneric_mem (S := S) hgr winL1 winL2 (valDn q) td_winL1 td_winL2 (td_valDn q)
  have hR := Work.WilG0.Omega_inter2 hRU hRD
  have hL := Work.WilG0.Omega_inter2 hLU hLD
  have hdeg : deg2.eval D + deg2.eval D ≤
      (Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D := by
    simp only [deg2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  constructor
  · rw [← oscSetRU_inter_RD (g := g) (q := q), ← oscGeneric_RU, ← oscGeneric_RD]
    exact Work.WilG1.Omega.mono hR (by omega) hdeg
  · rw [← oscSetLU_inter_LD (g := g) (q := q), ← oscGeneric_LU, ← oscGeneric_LD]
    exact Work.WilG1.Omega.mono hL (by omega) hdeg

end Work.WilG1.Thin
