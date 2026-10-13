import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.TSh
import Submission.Work.WilG5.Basic
import Submission.Work.WilCruxN.JointSetDefs

/-!
# `Work.WilCruxN.JointSetMem` — N4d plumbing

For a definable family `f : ℝ^a → ℝ^b → ℝ`, the set of parameters at which the *joint* limit holds
is `Ω`-definable, with format and degree bounds independent of `D`.  The shape calculus and the
`projLast`/`compl` completion are exactly as in the source module
`Submission/Work/WilCrux/JointSetMem.lean`; the coordinate API lives in
`Submission/Work/WilCruxN/JointSetDefs.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

lemma td_X_le4 {K : ℕ} (i : Fin K) :
    (MvPolynomial.X i : MvPolynomial (Fin K) ℝ).totalDegree ≤ 4 :=
  (Work.WilG5.td_X_le i).trans (by norm_num)

lemma td_C_le4 {K : ℕ} (c : ℝ) :
    (MvPolynomial.C c : MvPolynomial (Fin K) ℝ).totalDegree ≤ 4 :=
  (Work.WilG5.td_C_le c).trans (by norm_num)

lemma td_add_le4 {K : ℕ} {P Q : MvPolynomial (Fin K) ℝ}
    (hP : P.totalDegree ≤ 4) (hQ : Q.totalDegree ≤ 4) : (P + Q).totalDegree ≤ 4 :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le hP hQ)

/-- The value condition `|t| < ε`, as a shape (`-ε < t ∧ t < ε`). -/
def absLtS (S : SOMin) (F D a b : ℕ) : PKS S F D (D4 a b) :=
  PKS.conj
    (ltS S F D (MvPolynomial.X (tc (a := a) (b := b)))
      (MvPolynomial.X (ec (a := a) (b := b))) (td_X_le4 _) (td_X_le4 _))
    (ltS S F D (MvPolynomial.C (0 : ℝ))
      (MvPolynomial.X (tc (a := a) (b := b)) + MvPolynomial.X (ec (a := a) (b := b)))
      (td_C_le4 _) (td_add_le4 (td_X_le4 _) (td_X_le4 _)))

lemma absLtS_Real {S : SOMin} {F D a b : ℕ} :
    (absLtS S F D a b).Real =
      {v : Fin (D4 a b) → ℝ | |v (tc (a := a) (b := b))| < v (ec (a := a) (b := b))} := by
  rw [absLtS, PKS.Real_conj, ltS_Real, ltS_Real]
  ext v
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_add,
    MvPolynomial.eval_C]
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by linarith⟩

/-- The innermost formula: `(w',z) ∈ Qset → t ∈ famGraph f → |t| < ε`, where the index map
`iG` places the block `(w',z,t)` and `t` is its last coordinate. -/
def bodyShape (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hAT : Qset a b ∈ S.Ω F D (D4 a b)) : PKS S F D (D4 a b) :=
  PKS.imp (PKS.mem (Qset a b) hAT id)
    (PKS.imp (PKS.mem (famGraph f) hG (iG (a := a) (b := b))) (absLtS S F D a b))

/-- The level `(w, ε, δ)` formula: `δ > 0` and the body for the block `(w',z,t)`. -/
def S2shape (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hAT : Qset a b ∈ S.Ω F D (D4 a b)) : PKS S F D (a + 2) :=
  PKS.conj (posS S F D (d2 (a := a)))
    (PKS.allb (n := a + 2) (k := a + b + 1) (bodyShape S F D f hG hAT))
lemma bodyShape_Real {S : SOMin} {F D : ℕ} {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hAT : Qset a b ∈ S.Ω F D (D4 a b)) :
    (bodyShape S F D f hG hAT).Real =
      {v : Fin (D4 a b) → ℝ | v ∈ Qset a b →
        ((v ∘ (iG (a := a) (b := b))) ∈ famGraph f →
          |v (tc (a := a) (b := b))| < v (ec (a := a) (b := b)))} := by
  rw [bodyShape, PKS.Real_imp, PKS.Real_imp, PKS.Real_mem, PKS.Real_mem, absLtS_Real]
  ext v
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Function.comp_id]
  tauto

lemma mem_S2shape_iff {S : SOMin} {F D : ℕ} {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hAT : Qset a b ∈ S.Ω F D (D4 a b)) (x : Fin (a + 2) → ℝ) :
    x ∈ (S2shape S F D f hG hAT).Real ↔
      0 < x (d2 (a := a)) ∧
        ∀ y : Fin (a + b + 1) → ℝ, (Fin.append x y ∈ Qset a b →
          (y ∈ famGraph f → |y (tB (a := a) (b := b))| < x (e2 (a := a)))) := by
  rw [S2shape, PKS.Real_conj, PKS.Real_allb, posS_Real, bodyShape_Real]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun y hy hyG => ?_⟩
    have h := h2 y
    rw [append_iG, append_tc, append_ec] at h
    exact h hy hyG
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun y => ?_⟩
    rw [append_iG, append_tc, append_ec]
    exact fun hy hyG => h2 y hy hyG

/-- `Fin.append x y ∈ Qset` in terms of the coordinates of `x` and `y`. -/
lemma append_mem_Qset {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) :
    Fin.append x y ∈ Qset a b ↔
      (∀ i : Fin a, |y (wpB (b := b) i) - x (w2 i)| < x (d2 (a := a)))
      ∧ (fun j : Fin b => y (zB (a := a) j)) ≠ 0
      ∧ (∀ j : Fin b, |y (zB (a := a) j)| < x (d2 (a := a))) := by
  rw [Qset]
  simp only [Set.mem_ofPred_eq, append_wpc, append_wc, append_dc, append_zc]

/-! ## 5. The two formulations of the block condition -/

/-- The block `(w',z,t)` satisfies the coordinatewise conditions. -/
def condY {a b : ℕ} (w : Fin a → ℝ) (δ : ℝ) (y : Fin (a + b + 1) → ℝ) : Prop :=
  (∀ i : Fin a, |y (wpB (b := b) i) - w i| < δ)
    ∧ (fun j : Fin b => y (zB (a := a) j)) ≠ 0
    ∧ (∀ j : Fin b, |y (zB (a := a) j)| < δ)

lemma append_mem_Qset_condY {a b : ℕ} (w : Fin a → ℝ) (ε δ : ℝ)
    (y : Fin (a + b + 1) → ℝ) :
    Fin.append (ss w ε δ) y ∈ Qset a b ↔ condY w δ y := by
  rw [append_mem_Qset]
  simp only [condY, ss_w2, ss_d2]

/-- The block formulation `∀ y` and the pair formulation `∀ w' z` agree. -/
lemma forall_y_iff {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (ε δ : ℝ) :
    (∀ y : Fin (a + b + 1) → ℝ, condY w δ y →
        (y ∈ famGraph f → |y (tB (a := a) (b := b))| < ε))
      ↔ (∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
          (∀ i : Fin a, |w' i - w i| < δ) → z ≠ 0 → (∀ j : Fin b, |z j| < δ) →
            |f w' z| < ε) := by
  constructor
  · intro h w' z h1 h2 h3
    have hy : Fin.append (Fin.append w' z) (fun _ : Fin 1 => f w' z) ∈ famGraph f := by
      rw [mem_famGraph_iff, init_append_append, famFun_append, ← tB_eq_last]
      exact append_append_tB w' z (f w' z)
    have hres := h (Fin.append (Fin.append w' z) (fun _ : Fin 1 => f w' z))
      ⟨fun i => by rw [append_append_wpB]; exact h1 i,
        fun hc => h2 (funext fun j => by
          have hcj := congrFun hc j
          rw [append_append_zB] at hcj
          exact hcj),
        fun j => by rw [append_append_zB]; exact h3 j⟩
      hy
    rwa [append_append_tB] at hres
  · intro h y hy hyG
    obtain ⟨h1, h2, h3⟩ := hy
    have hz := h (fun i : Fin a => y (wpB (b := b) i)) (fun j : Fin b => y (zB (a := a) j))
      h1 h2 h3
    rw [mem_famGraph_iff, famFun_init_coords] at hyG
    rw [tB_eq_last, hyG]
    exact hz

/-- The level `(w,ε,δ)` point `ss w ε δ` satisfies the `δ`-formula, in coordinates. -/
lemma mem_S2shape_snoc {S : SOMin} {F D : ℕ} {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hAT : Qset a b ∈ S.Ω F D (D4 a b)) (w : Fin a → ℝ) (ε δ : ℝ) :
    ss w ε δ ∈ (S2shape S F D f hG hAT).Real ↔
      (0 < δ ∧ ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        (∀ i : Fin a, |w' i - w i| < δ) → z ≠ 0 → (∀ j : Fin b, |z j| < δ) →
          |f w' z| < ε) := by
  rw [mem_S2shape_iff, ss_d2, ss_e2]
  simp only [append_mem_Qset_condY]
  exact and_congr Iff.rfl (forall_y_iff f w ε δ)

/-! ## 6. `dist` and `‖·‖` in coordinates -/

lemma dist_iff_coord {a : ℕ} {w w' : Fin a → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ((∀ i : Fin a, |w' i - w i| < δ) ↔ dist w' w < δ) := by
  rw [dist_pi_lt_iff hδ]
  exact forall_congr' (fun i => by rw [Real.dist_eq])

lemma norm_iff_coord {b : ℕ} {z : Fin b → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ((∀ j : Fin b, |z j| < δ) ↔ ‖z‖ < δ) := by
  rw [pi_norm_lt_iff hδ]
  exact forall_congr' (fun j => by rw [Real.norm_eq_abs])

/-! ## 7. The target -/

/-- **N4d plumbing: the set of parameters where the *joint* limit holds is `Ω`-definable.**

Same statement as `Work.WilCrux.JointSetMem` (`Submission/Work/WilCrux/JointSetMem.lean`, which is
`sorry`-free and compiles — you may copy its proof into your own module, or re-prove it).  For a
definable family `f : ℝ^a → ℝ^b → ℝ` (`famGraph f ∈ S.Ω F D (a+b+1)`) the set of `w` such that

  `∀ ε > 0, ∃ δ > 0, ∀ w' z, dist w' w < δ → z ≠ 0 → ‖z‖ < δ → |f w' z| < ε`

is `Ω`-definable, with format and degree bounds independent of `D` (degree a polynomial in `D`).

Route: this is a pure first-order formula over the single atom `famGraph f` — read `u = f w z`
from `(w,z,u) ∈ famGraph f`.  The quantifier prefix is the real block `ε`, the real block `δ`, the
parameter block `w'` (: `a` coordinates) and the fibre block `z` (: `b` coordinates); eliminate it
with the block quantifiers `Work.WilG4c.PKS.exb`/`allb` of the shape calculus
(`Submission/Work/WilG4c/TSh.lean`).  `Work.WilkG4c.FibreContSublevelMem` (proven, in
`Submission/Work/WilkG4c/`) is a worked template with the same atom and the same
`projLast`/`compl` completion, and `Work.WilkG4c.FibreDerivGraphMem` (proven) uses `PKS.exb`.
`‖z‖ < δ` is the finite conjunction `∀ j, |z j| < δ` (sup norm) and `dist w' w < δ` the finite
conjunction `∀ i, |w' i - w i| < δ`; `S.SharpCD` is NOT needed.

Keep each file you write under ~15 KB (`maxHeartbeats` at most 4000000).  Do NOT `sorry` and do NOT
use any declaration whose `#print axioms` mentions `sorryAx`. -/
theorem JointSetMem (S : WilkiesDesign.SOMin) {a b F : ℕ} :
    ∃ (A : ℕ) (c : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F D (a + b + 1) →
      {w : Fin a → ℝ | ∀ ε > 0, ∃ δ > 0, ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        dist w' w < δ → z ≠ 0 → ‖z‖ < δ → |f w' z| < ε} ∈ S.Ω A (c.eval D) a := by
  classical
  obtain ⟨AT0, q, hQ⟩ := Qset_mem (S := S) (a := a) (b := b)
  have hmaxF : F ≤ max F AT0 := le_max_left _ _
  have hmaxA : AT0 ≤ max F AT0 := le_max_right _ _
  have hFF' : F ≤ max F AT0 + (a + b + 1) + 4 := by omega
  have hAFF' : AT0 ≤ max F AT0 + (a + b + 1) + 4 := by omega
  have habF' : a + b + 1 ≤ max F AT0 + (a + b + 1) + 4 := by omega
  have h4Dc : 4 ≤ max 4 (q.eval 4) := le_max_left _ _
  have hq4Dc : q.eval 4 ≤ max 4 (q.eval 4) := le_max_right _ _
  -- the canonical instance, used only to read off the format and the number of atoms
  have hG0base : WilkiesDesign.CG.famGraph
      (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) ∈ S.Ω (a + b + 1) 1 (a + b + 1) := by
    have h := S.hyp (a + b + 1)
      (MvPolynomial.X (Fin.last (a + b)) : MvPolynomial (Fin (a + b + 1)) ℝ)
    have hset : {x : Fin (a + b + 1) → ℝ |
        MvPolynomial.eval x (MvPolynomial.X (Fin.last (a + b)) :
          MvPolynomial (Fin (a + b + 1)) ℝ) = 0} =
        WilkiesDesign.CG.famGraph (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) := by
      rw [← Work.WilG4c.graphOf_famFun]
      ext x
      simp [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Work.WilG4c.famFun]
    rw [hset] at h
    refine Work.WilG5.mem_mono h (a + b + 1) 1 le_rfl ?_
    simp [MvPolynomial.totalDegree_X]
  have hG0 : WilkiesDesign.CG.famGraph
      (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) ∈
      S.Ω (max F AT0 + (a + b + 1) + 4) (max 4 (q.eval 4)) (a + b + 1) :=
    Work.WilG5.mem_mono hG0base _ _ habF' (le_trans (by norm_num) h4Dc)
  have hAT0 : Qset a b ∈ S.Ω (max F AT0 + (a + b + 1) + 4) (max 4 (q.eval 4)) (D4 a b) :=
    Work.WilG5.mem_mono (hQ 4) _ _ hAFF' hq4Dc
  let c0 : PKS S (max F AT0 + (a + b + 1) + 4) (max 4 (q.eval 4)) (a + 2) :=
    S2shape S (max F AT0 + (a + b + 1) + 4) (max 4 (q.eval 4))
      (fun (_ : Fin a → ℝ) (_ : Fin b → ℝ) => (0 : ℝ)) hG0 hAT0
  let cq : Polynomial ℕ := Polynomial.C c0.Atoms * (Polynomial.X + q + Polynomial.C 10)
  let ctot : Polynomial ℕ := Polynomial.C 8 + cq
  refine ⟨max (4 * (a + 1) + 20) (c0.Fmt + 2) + 3, ctot, ?_⟩
  intro D f hG
  obtain ⟨D', hDD', hqDD', hD'ub⟩ : ∃ D' : ℕ, D ≤ D' ∧ q.eval D ≤ D' ∧ D' ≤ D + q.eval D :=
    ⟨max D (q.eval D), le_max_left _ _, le_max_right _ _,
      max_le (by omega) (by omega)⟩
  have hG' : WilkiesDesign.CG.famGraph f ∈ S.Ω (max F AT0 + (a + b + 1) + 4) D' (a + b + 1) :=
    Work.WilG5.mem_mono hG _ _ hFF' hDD'
  have hAT : Qset a b ∈ S.Ω (max F AT0 + (a + b + 1) + 4) D' (D4 a b) :=
    Work.WilG5.mem_mono (hQ D) _ _ hAFF' hqDD'
  let shp : PKS S (max F AT0 + (a + b + 1) + 4) D' (a + 2) := S2shape S _ D' f hG' hAT
  have hcq : cq.eval D = c0.Atoms * (D + q.eval D + 10) := by
    dsimp only [cq]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have hctot : ctot.eval D = 8 + c0.Atoms * (D + q.eval D + 10) := by
    dsimp only [ctot]
    rw [Polynomial.eval_add, hcq, Polynomial.eval_C]
  have hcmem : shp.Real ∈ S.Ω c0.Fmt (cq.eval D) (a + 2) := by
    have h := PKS.Real_mem_Omega shp
    have hAt : shp.Atoms = c0.Atoms := rfl
    have hFt : shp.Fmt = c0.Fmt := rfl
    refine Work.WilG1.Omega.mono h (le_of_eq hFt) ?_
    refine (PKS.Deg_le shp).trans ?_
    rw [hcq, hAt]
    exact Nat.mul_le_mul_left _ (by omega)
  have hstep1 : projLast shp.Real ∈ S.Ω (c0.Fmt + 1) (cq.eval D) (a + 1) :=
    Work.WilG1.Omega.projLast_mem hcmem
  have hstep2 : (projLast shp.Real)ᶜ ∈ S.Ω (c0.Fmt + 1 + 1) (cq.eval D) (a + 1) :=
    Work.WilG1.Omega.compl_mem hstep1
  have hE : {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∈
      S.Ω (4 * (a + 1) + 20) ((Polynomial.C 8).eval D) (a + 1) := by
    refine Work.WilG1.Omega.mono (Work.WilG5.ltSet_mem (S := S) (Fin.last a) 0) le_rfl ?_
    simp only [Polynomial.eval_C]
    exact le_rfl
  have hstep3 : {p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩ (projLast shp.Real)ᶜ ∈
      S.Ω (max (4 * (a + 1) + 20) (c0.Fmt + 2) + 1) (ctot.eval D) (a + 1) :=
    Work.WilG1.Omega.inter₂ hE hstep2
  have hstep4 : projLast ({p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
      (projLast shp.Real)ᶜ) ∈
      S.Ω (max (4 * (a + 1) + 20) (c0.Fmt + 2) + 2) (ctot.eval D) a :=
    Work.WilG1.Omega.projLast_mem hstep3
  have hstep5 : (projLast ({p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
      (projLast shp.Real)ᶜ))ᶜ ∈
      S.Ω (max (4 * (a + 1) + 20) (c0.Fmt + 2) + 3) (ctot.eval D) a :=
    Work.WilG1.Omega.compl_mem hstep4
  -- the set identity
  have hmemJ : ∀ (w : Fin a → ℝ) (ε δ : ℝ),
      (ss w ε δ ∈ shp.Real) ↔
      (0 < δ ∧ ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        (∀ i : Fin a, |w' i - w i| < δ) → z ≠ 0 → (∀ j : Fin b, |z j| < δ) →
          |f w' z| < ε) :=
    fun w ε δ => mem_S2shape_snoc (S := S) (F := max F AT0 + (a + b + 1) + 4) (D := D')
      (a := a) (b := b) f hG' hAT w ε δ
  have hkey : ∀ w : Fin a → ℝ,
      (w ∈ (projLast ({p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
        (projLast shp.Real)ᶜ))ᶜ) ↔
      (∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        (∀ i : Fin a, |w' i - w i| < δ) → z ≠ 0 → (∀ j : Fin b, |z j| < δ) →
          |f w' z| < ε) := by
    intro w
    have h1 : (w ∈ (projLast ({p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
        (projLast shp.Real)ᶜ))ᶜ) ↔
        (∀ t : ℝ, 0 < t → ∃ δ : ℝ, Fin.snoc (Fin.snoc w t) δ ∈ shp.Real) := by
      rw [Set.mem_compl_iff, WilkiesDesign.projLast, Set.mem_ofPred_eq, not_exists]
      refine forall_congr' (fun t => ?_)
      rw [Set.mem_inter_iff, Set.mem_compl_iff, not_and, not_not, Set.mem_ofPred_eq,
        Fin.snoc_last, WilkiesDesign.projLast, Set.mem_ofPred_eq]
    rw [h1]
    refine forall_congr' (fun t => imp_congr_right (fun _ => ?_))
    exact exists_congr (fun δ => hmemJ w t δ)
  have hset : {w : Fin a → ℝ | ∀ ε > 0, ∃ δ > 0, ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        dist w' w < δ → z ≠ 0 → ‖z‖ < δ → |f w' z| < ε} =
      (projLast ({p : Fin (a + 1) → ℝ | 0 < p (Fin.last a)} ∩
        (projLast shp.Real)ᶜ))ᶜ := by
    ext w
    rw [Set.mem_ofPred_eq, hkey w]
    constructor
    · intro h ε hε
      obtain ⟨δ, hδ, hrest⟩ := h ε hε
      exact ⟨δ, hδ, fun w' z hd hz hn =>
        hrest w' z ((dist_iff_coord hδ).mp hd) hz ((norm_iff_coord hδ).mp hn)⟩
    · intro h ε hε
      obtain ⟨δ, hδ, hrest⟩ := h ε hε
      exact ⟨δ, hδ, fun w' z hc hz hn =>
        hrest w' z ((dist_iff_coord hδ).mpr hc) hz ((norm_iff_coord hδ).mpr hn)⟩
  rw [hset]
  exact hstep5

end Work.WilCruxN
