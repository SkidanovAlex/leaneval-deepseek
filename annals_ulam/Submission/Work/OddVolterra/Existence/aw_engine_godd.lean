import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.aw_data
import Submission.Work.OddVolterra.Existence.aw_clamp
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.aw_contDiffOn_awGodd
import Submission.Work.OddCurveB.Est.dist_fderiv_Godd_le
import Submission.Work.OddCurveB.Existence.Explicit
import Submission.Work.OddCurveB.Existence.KdiagForm
import Submission.Work.Anchor.deriv_close

/-!
# The uniform second `z`-derivative bound for the localised state datum `awGodd`

This module proves the second conjunct of `Work.OddVolterra.Existence.aw_engine_constants`:
there is a constant `Cg`, uniform in the bump `h`, such that on the unit ball around
`baseState s` the map `z ↦ fderiv (awGodd n h s ·) z` is differentiable and its differential is
bounded by `Cg`.

The structural input is `Work.OddCurveB.Existence.Godd_eq_GoddDiag`: on the diagonal the perturbed
system depends on `h` only through the two *numbers* `h s` and `h'(s)`,

`Godd n h s z = GoddDiag n s (h s) (deriv h s) z`

(`GoddM = Godd` by `Work.OddVolterra.Window.GoddM_eq_Godd`), and `GoddDiag` is an explicit
function of `(s, hs, hp, z)`, smooth wherever the two diagonal radicands `Drad s hs hp (-(z 0))`
and `Drad s hs hp (z 1)` are positive.  Hence the whole estimate is an estimate about the *fixed*
joint function

`awGj n ((s,hs,hp),z) = awChiG s z • GoddDiag n s hs hp z`

on a compact box — compactness of the box turns the `C^2`-regularity into a bound, and the
`h`-dependence enters only through the evaluation point `(s, h s, h' s)` inside the compact box.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Existence

open Work.OddVolterra
open Work.OddCurveB.Existence

noncomputable section

/-! ## The joint data and the joint datum -/

/-- The joint data `((s, h s, h' s), z)` of the localised state datum. -/
abbrev awQ : Type := (ℝ × ℝ × ℝ) × St

/-- The joint (cut-off) diagonal state datum: the localised state datum as a function of the
joint data `((s, h s, h' s), z)`. -/
def awGj (n : ℕ) (q : awQ) : St :=
  awChiG q.1.1 q.2 • GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2

/-! ## The two boxes -/

/-- The compact state box: `z 0, z 1 ∈ [1/4,3/2]`, `z 2, z 3 ∈ [-(B+1),B+1]`. -/
def awZbox (B : ℝ) : Set St :=
  Set.Icc ![1 / 4, 1 / 4, -(B + 1), -(B + 1)] ![3 / 2, 3 / 2, B + 1, B + 1]

/-- The open state box containing `awZbox`. -/
def awZopen (B : ℝ) : Set St :=
  {z : St | (1 / 5 : ℝ) < z 0} ∩ {z : St | z 0 < 8 / 5} ∩
    {z : St | (1 / 5 : ℝ) < z 1} ∩ {z : St | z 1 < 8 / 5} ∩
    {z : St | -(B + 2) < z 2} ∩ {z : St | z 2 < B + 2} ∩
    {z : St | -(B + 2) < z 3} ∩ {z : St | z 3 < B + 2}

/-- The compact box of the estimate, with `B` a bound for `|deriv profileX|` on the window. -/
def awKbox (B : ℝ) : Set awQ :=
  (Set.Icc (1 / 2 : ℝ) (19 / 20) ×ˢ
      (Set.Icc (-(1 / 100) : ℝ) (1 / 100) ×ˢ Set.Icc (-(1 / 100) : ℝ) (1 / 100))) ×ˢ
    awZbox B

/-- An open box containing `awKbox B` on which `awGj` is smooth. -/
def awUbox (B : ℝ) : Set awQ :=
  (Set.Ioo (2 / 5 : ℝ) (11 / 10) ×ˢ
      (Set.Ioo (-(1 / 50) : ℝ) (1 / 50) ×ˢ Set.Ioo (-(1 / 50) : ℝ) (1 / 50))) ×ˢ
    awZopen B

lemma isOpen_awZopen (B : ℝ) : IsOpen (awZopen B) := by
  have h : ∀ (i : Fin 4) (lo hi : ℝ), IsOpen {z : St | lo < z i ∧ z i < hi} := by
    intro i lo hi
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  have he : awZopen B = {z : St | (1 / 5 : ℝ) < z 0 ∧ z 0 < 8 / 5} ∩
      {z : St | (1 / 5 : ℝ) < z 1 ∧ z 1 < 8 / 5} ∩
      {z : St | -(B + 2) < z 2 ∧ z 2 < B + 2} ∩
      {z : St | -(B + 2) < z 3 ∧ z 3 < B + 2} := by
    ext z; simp only [awZopen, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
  rw [he]
  exact (((h 0 (1 / 5) (8 / 5)).inter (h 1 (1 / 5) (8 / 5))).inter
    (h 2 (-(B + 2)) (B + 2))).inter (h 3 (-(B + 2)) (B + 2))

lemma isOpen_awUbox (B : ℝ) : IsOpen (awUbox B) :=
  IsOpen.prod
    (IsOpen.prod isOpen_Ioo (IsOpen.prod isOpen_Ioo isOpen_Ioo)) (isOpen_awZopen B)

lemma mem_awZbox_iff (B : ℝ) (z : St) :
    z ∈ awZbox B ↔ (1 / 4 : ℝ) ≤ z 0 ∧ z 0 ≤ 3 / 2 ∧ (1 / 4 : ℝ) ≤ z 1 ∧ z 1 ≤ 3 / 2 ∧
      -(B + 1) ≤ z 2 ∧ z 2 ≤ B + 1 ∧ -(B + 1) ≤ z 3 ∧ z 3 ≤ B + 1 := by
  rw [awZbox, Set.mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa using h1 0, by simpa using h2 0, by simpa using h1 1, by simpa using h2 1,
      by simpa using h1 2, by simpa using h2 2, by simpa using h1 3, by simpa using h2 3⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    constructor
    · intro i; fin_cases i <;> simp_all
    · intro i; fin_cases i <;> simp_all

lemma mem_awZopen_iff (B : ℝ) (z : St) :
    z ∈ awZopen B ↔ (1 / 5 : ℝ) < z 0 ∧ z 0 < 8 / 5 ∧ (1 / 5 : ℝ) < z 1 ∧ z 1 < 8 / 5 ∧
      -(B + 2) < z 2 ∧ z 2 < B + 2 ∧ -(B + 2) < z 3 ∧ z 3 < B + 2 := by
  simp only [awZopen, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto

lemma convex_awZbox (B : ℝ) : Convex ℝ (awZbox B) := convex_Icc _ _

lemma convex_awKbox (B : ℝ) : Convex ℝ (awKbox B) :=
  ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))).prod (convex_awZbox B)

lemma isCompact_awZbox (B : ℝ) : IsCompact (awZbox B) := isCompact_Icc

lemma isCompact_awKbox (B : ℝ) : IsCompact (awKbox B) :=
  ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_awZbox B))

lemma mem_awUbox_iff (B : ℝ) (q : awQ) :
    q ∈ awUbox B ↔
      q.1.1 ∈ Set.Ioo (2 / 5 : ℝ) (11 / 10) ∧
      q.1.2.1 ∈ Set.Ioo (-(1 / 50) : ℝ) (1 / 50) ∧
      q.1.2.2 ∈ Set.Ioo (-(1 / 50) : ℝ) (1 / 50) ∧ q.2 ∈ awZopen B := by
  simp only [awUbox, Set.mem_prod]
  tauto

lemma awKbox_subset_awUbox {B : ℝ} : awKbox B ⊆ awUbox B := by
  intro q hq
  rw [mem_awUbox_iff, Set.mem_Ioo, Set.mem_Ioo, Set.mem_Ioo, mem_awZopen_iff]
  rw [awKbox, Set.mem_prod] at hq
  obtain ⟨hp1, hz⟩ := hq
  rw [Set.mem_prod] at hp1
  obtain ⟨hs, hrest⟩ := hp1
  rw [Set.mem_prod] at hrest
  obtain ⟨hhs, hhp⟩ := hrest
  rw [mem_awZbox_iff] at hz
  obtain ⟨hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7⟩ := hz
  rw [Set.mem_Icc] at hs hhs hhp
  exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
    ⟨by linarith [hhs.1], by linarith [hhs.2]⟩,
    ⟨by linarith [hhp.1], by linarith [hhp.2]⟩,
    by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- On the open box the two diagonal radicands are positive. -/
lemma awDrad_pos_of_mem_Ubox {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    0 < Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) ∧
      0 < Drad q.1.1 q.1.2.1 q.1.2.2 (q.2 1) := by
  rw [mem_awUbox_iff, Set.mem_Ioo, Set.mem_Ioo, Set.mem_Ioo, mem_awZopen_iff] at hq
  obtain ⟨hs, hhs, hhp, hz0a, hz0b, hz1a, hz1b, -, -, -, -⟩ := hq
  have hspos : 0 < q.1.1 := by linarith [hs.1]
  constructor <;> simp only [Drad]
  · have h1 : -(q.2 0) + q.1.2.2 < 0 := by linarith [hz0a, hhp.2]
    have h2 : q.1.1 * (-(q.2 0)) + q.1.2.1 < 0 := by
      have h : (2 / 5 : ℝ) * (1 / 5) < q.1.1 * q.2 0 := by
        have h1' := mul_lt_mul_of_pos_right hs.1 (by norm_num : (0:ℝ) < 1 / 5)
        have h2' := mul_lt_mul_of_pos_left hz0a hspos
        linarith [h1', h2']
      linarith [h, hhs.2]
    exact mul_pos_of_neg_of_neg h1 h2
  · have h1 : 0 < q.2 1 + q.1.2.2 := by linarith [hz1a, hhp.1]
    have h2 : 0 < q.1.1 * q.2 1 + q.1.2.1 := by
      have h : (2 / 5 : ℝ) * (1 / 5) < q.1.1 * q.2 1 := by
        have h1' := mul_lt_mul_of_pos_right hs.1 (by norm_num : (0:ℝ) < 1 / 5)
        have h2' := mul_lt_mul_of_pos_left hz1a hspos
        linarith [h1', h2']
      linarith [h, hhs.1]
    exact mul_pos h1 h2

/-! ## Smoothness of the explicit diagonal data on the open box -/

lemma aw_contDiffAt_pow_mul_sqrt (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (fun v : ℝ => v ^ k * Real.sqrt v) u :=
  ((contDiffAt_id (x := u)).pow k).mul (Real.contDiffAt_sqrt (ne_of_gt hu))

/-- The radicand at the left endpoint `t = -(z 0)`. -/
def awDlo (q : awQ) : ℝ := Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))

/-- The radicand at the right endpoint `t = z 1`. -/
def awDhi (q : awQ) : ℝ := Drad q.1.1 q.1.2.1 q.1.2.2 (q.2 1)

lemma contDiff_awDlo : ContDiff ℝ ∞ awDlo := by
  rw [show awDlo = fun q : awQ => Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) from rfl]
  unfold Drad; fun_prop

lemma contDiff_awDhi : ContDiff ℝ ∞ awDhi := by
  rw [show awDhi = fun q : awQ => Drad q.1.1 q.1.2.1 q.1.2.2 (q.2 1) from rfl]
  unfold Drad; fun_prop

lemma awD_lo_eq {q : awQ} : awDlo q = Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) := rfl

lemma contDiffAt_Kdiag1_lo (n : ℕ) {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    ContDiffAt ℝ ∞ (fun q : awQ => Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))) q := by
  have hpos : 0 < awDlo q := (awDrad_pos_of_mem_Ubox hq).1
  have heq : (fun q : awQ => Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))) = fun q : awQ =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (awDlo q ^ n * Real.sqrt (awDlo q)) := by
    funext q; exact Kdiag1_eq n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : awQ => awDlo q ^ n * Real.sqrt (awDlo q)) q :=
    (aw_contDiffAt_pow_mul_sqrt n hpos).comp q contDiff_awDlo.contDiffAt
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_Kdiag1_hi (n : ℕ) {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    ContDiffAt ℝ ∞ (fun q : awQ => Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)) q := by
  have hpos : 0 < awDhi q := (awDrad_pos_of_mem_Ubox hq).2
  have heq : (fun q : awQ => Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)) = fun q : awQ =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (awDhi q ^ n * Real.sqrt (awDhi q)) := by
    funext q; exact Kdiag1_eq n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : awQ => awDhi q ^ n * Real.sqrt (awDhi q)) q :=
    (aw_contDiffAt_pow_mul_sqrt n hpos).comp q contDiff_awDhi.contDiffAt
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_Kdiag2_lo (n : ℕ) (hn : 1 ≤ n) {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    ContDiffAt ℝ ∞ (fun q : awQ => Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))) q := by
  have hpos : 0 < awDlo q := (awDrad_pos_of_mem_Ubox hq).1
  have heq : (fun q : awQ => Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))) = fun q : awQ =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (awDlo q ^ (n - 1) * Real.sqrt (awDlo q)) * (-(q.2 0) + q.1.2.2) := by
    funext q; exact Kdiag2_eq n hn q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : awQ => awDlo q ^ (n - 1) * Real.sqrt (awDlo q)) q :=
    (aw_contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q contDiff_awDlo.contDiffAt
  have hlin : ContDiffAt ℝ ∞ (fun q : awQ => -(q.2 0) + q.1.2.2) q := by fun_prop
  simpa [smul_eq_mul] using
    (hcomp.const_smul ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_Kdiag2_hi (n : ℕ) (hn : 1 ≤ n) {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    ContDiffAt ℝ ∞ (fun q : awQ => Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)) q := by
  have hpos : 0 < awDhi q := (awDrad_pos_of_mem_Ubox hq).2
  have heq : (fun q : awQ => Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)) = fun q : awQ =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (awDhi q ^ (n - 1) * Real.sqrt (awDhi q)) * (q.2 1 + q.1.2.2) := by
    funext q; exact Kdiag2_eq n hn q.1.1 q.1.2.1 q.1.2.2 (q.2 1)
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : awQ => awDhi q ^ (n - 1) * Real.sqrt (awDhi q)) q :=
    (aw_contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q contDiff_awDhi.contDiffAt
  have hlin : ContDiffAt ℝ ∞ (fun q : awQ => q.2 1 + q.1.2.2) q := by fun_prop
  simpa [smul_eq_mul] using
    (hcomp.const_smul ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_GoddDiag_comp (n : ℕ) (hn : 1 ≤ n) {B : ℝ} {q : awQ} (hq : q ∈ awUbox B) :
    ContDiffAt ℝ ∞ (fun q : awQ => GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2) q := by
  have h1lo := contDiffAt_Kdiag1_lo n hq
  have h1hi := contDiffAt_Kdiag1_hi n hq
  have h2lo := contDiffAt_Kdiag2_lo n hn hq
  have h2hi := contDiffAt_Kdiag2_hi n hn hq
  have hz0 : ContDiffAt ℝ ∞ (fun q : awQ => q.2 0) q := by fun_prop
  have hz1 : ContDiffAt ℝ ∞ (fun q : awQ => q.2 1) q := by fun_prop
  have hz2 : ContDiffAt ℝ ∞ (fun q : awQ => q.2 2) q := by fun_prop
  have hz3 : ContDiffAt ℝ ∞ (fun q : awQ => q.2 3) q := by fun_prop
  have hfun : (fun q : awQ => GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2) = fun q : awQ =>
      ![q.2 0, q.2 1,
        -(abelMass * (-(Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) * q.2 2 +
          Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1) * q.2 3))),
        -(abelMass * (-(Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) * q.2 2 +
          Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1) * q.2 3)))] := by
    funext q
    simp only [GoddDiag, KvecDiag, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
  rw [hfun, contDiffAt_pi]
  intro i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  · exact hz0
  · exact hz1
  · exact (((h1lo.mul hz2).add (h1hi.mul hz3)).neg.const_smul abelMass).neg
  · exact (((h2lo.mul hz2).add (h2hi.mul hz3)).neg.const_smul abelMass).neg

lemma contDiffOn_awGj (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ContDiffOn ℝ ∞ (fun q => awGj n q) (awUbox B) := by
  rw [(isOpen_awUbox B).contDiffOn_iff]
  intro q hq
  have hc : ContDiffAt ℝ ∞ (fun q : awQ => awChiG q.1.1 q.2) q := by
    have := contDiff_awChiG.contDiffAt.comp q
      (f := fun q : awQ => (q.1.1, q.2)) (by fun_prop)
    simpa only [Function.comp_def] using this
  have hg := contDiffAt_GoddDiag_comp n hn hq
  have hfun : (fun q => awGj n q) = fun q : awQ =>
      awChiG q.1.1 q.2 • GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2 := rfl
  rw [hfun]
  exact hc.smul hg

/-- `fderiv (awGj n)` is `C^2` on the open box. -/
lemma contDiffOn_fderiv_awGj (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ContDiffOn ℝ 2 (fun q => fderiv ℝ (awGj n) q) (awUbox B) :=
  (contDiffOn_awGj n hn B).fderiv_of_isOpen (isOpen_awUbox B)
    (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ∞) + 1) ≤ ⊤))

/-- On the compact box the second `q`-derivative of `awGj` is bounded. -/
lemma exists_bound_second_awGj (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ awKbox B,
      ‖fderiv ℝ (fun q => fderiv ℝ (awGj n) q) q‖ ≤ M := by
  have h2 : ContDiffOn ℝ 2 (fun q : awQ => fderiv ℝ (awGj n) q) (awUbox B) :=
    contDiffOn_fderiv_awGj n hn B
  have h3 : ContDiffOn ℝ 1
      (fun q : awQ => fderiv ℝ (fun q' : awQ => fderiv ℝ (awGj n) q') q) (awUbox B) :=
    h2.fderiv_of_isOpen (isOpen_awUbox B) (WithTop.coe_le_coe.mpr le_rfl)
  have h4 : ContinuousOn
      (fun q : awQ => fderiv ℝ (fun q' : awQ => fderiv ℝ (awGj n) q') q) (awUbox B) :=
    h3.continuousOn
  have hcont : ContinuousOn
      (fun q : awQ => ‖fderiv ℝ (fun q' : awQ => fderiv ℝ (awGj n) q') q‖) (awKbox B) :=
    (ContinuousOn.norm (f := fun q : awQ => fderiv ℝ (fun q' : awQ => fderiv ℝ (awGj n) q') q)
      h4).mono (awKbox_subset_awUbox (B := B))
  obtain ⟨M, hM⟩ := (isCompact_awKbox B).exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro q hq
  have h := hM q hq
  rw [Real.norm_eq_abs] at h
  rw [abs_of_nonneg (norm_nonneg (fderiv ℝ (fun q' : awQ => fderiv ℝ (awGj n) q') q))] at h
  exact le_trans h (le_max_left _ _)

/-! ## The identification of `awGodd` with a section of `awGj` -/

lemma awGodd_eq_awGj (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s : ℝ) (z : St) :
    awGodd n h s z = awGj n ((s, h s, deriv h s), z) := by
  rw [awGodd, awGj, Work.OddVolterra.Window.GoddM_eq_Godd n hh s z, Godd_eq_GoddDiag]

/-- The `z`-differential of the section of `awGj`, as a composition with the inclusion. -/
lemma fderiv_awGj_section (n : ℕ) (hn : 1 ≤ n) {B : ℝ} {p : ℝ × ℝ × ℝ} {z : St}
    (hp : (p, z) ∈ awUbox B) :
    fderiv ℝ (fun w => awGj n (p, w)) z =
      (fderiv ℝ (awGj n) (p, z)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St) := by
  have hd : DifferentiableAt ℝ (awGj n) (p, z) :=
    ((contDiffOn_awGj n hn B).contDiffAt
      ((isOpen_awUbox B).mem_nhds hp)).differentiableAt (by simp)
  have hin : DifferentiableAt ℝ (fun w : St => (p, w)) z :=
    (differentiableAt_const p).prodMk differentiableAt_id
  have hcomp : fderiv ℝ ((awGj n) ∘ (fun w : St => (p, w))) z =
      (fderiv ℝ (awGj n) (p, z)).comp (fderiv ℝ (fun w : St => (p, w)) z) :=
    fderiv_comp z hd hin
  rw [show (fun w => awGj n (p, w)) = (awGj n) ∘ (fun w : St => (p, w)) from rfl, hcomp,
    (hasFDerivAt_prodMk_right p z).fderiv]

/-! ## A Lipschitz bound on the differential gives a bound on the second derivative -/

/-- **A generic lemma**: if `f` is Lipschitz with constant `L` on a set `s` containing `z` in its
interior and `f` is differentiable at `z`, then `‖fderiv f z‖ ≤ L`. -/
lemma aw_norm_fderiv_le_of_lipschitzOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : St → F} {L : ℝ} (hL : 0 ≤ L) {s : Set St} {z : St}
    (hlip : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (hz : z ∈ interior s) (hd : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ f z‖ ≤ L := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ((mem_interior_iff_mem_nhds.mp hz))
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  set g : ℝ → F := fun t => f (z + t • v) with hg
  have hcurve : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 := by
      simpa only [id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const v
    rw [one_smul] at h1
    simpa using h1.const_add z
  have hfx : HasFDerivAt f (fderiv ℝ f z) (z + (0 : ℝ) • v) := by
    rw [zero_smul, add_zero]; exact hd.hasFDerivAt
  have hgd : HasDerivAt g ((fderiv ℝ f z) v) 0 :=
    hfx.comp_hasDerivAt 0 hcurve
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hslope : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖slope g 0 t‖ ≤ L * ‖v‖ := by
    have hε' : 0 < ε / ‖v‖ := div_pos hε hpos
    have hball' : Metric.ball (0 : ℝ) (ε / ‖v‖) ∈ 𝓝[≠] (0 : ℝ) :=
      Filter.le_def.mp nhdsWithin_le_nhds _ (Metric.ball_mem_nhds (0 : ℝ) hε')
    filter_upwards [self_mem_nhdsWithin, hball'] with t ht hmem
    have ht0 : t ≠ 0 := ht
    have hmem' : z + t • v ∈ s := by
      refine hball ?_
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have h3 : |t| < ε / ‖v‖ := by
        have h4 := hmem
        rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] at h4
        exact h4
      calc ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ < (ε / ‖v‖) * ‖v‖ := mul_lt_mul_of_pos_right h3 hpos
        _ = ε := by field_simp
    have hzmem : z ∈ s := interior_subset hz
    have hb := hlip _ hmem' _ hzmem
    rw [add_sub_cancel_left] at hb
    have hgt : g t - g 0 = f (z + t • v) - f z := by simp [hg]
    rw [show slope g 0 t = ((t - 0)⁻¹) • (g t - g 0) from rfl,
      hgt, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      inv_mul_eq_div, div_le_iff₀ (abs_pos.mpr ht0)]
    calc ‖f (z + t • v) - f z‖ ≤ L * ‖t • v‖ := hb
      _ = L * ‖v‖ * |t| := by rw [norm_smul, Real.norm_eq_abs]; ring
  exact le_of_tendsto (hgd.tendsto_slope.norm) hslope

/-! ## The second conjunct of `aw_engine_constants` -/

theorem aw_godd_second_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ),
        ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
          DifferentiableAt ℝ
            (fun z' => fderiv ℝ (fun w => Work.OddVolterra.Existence.awGodd n h s w) z') z ∧
          ‖fderiv ℝ
            (fun z' => fderiv ℝ (fun w => Work.OddVolterra.Existence.awGodd n h s w) z') z‖ ≤ Cg := by
  obtain ⟨B, hB1, hB⟩ := Work.Anchor.DClose.exists_deriv_profileX_bound
  have hB0 : (0 : ℝ) ≤ B := le_trans (by norm_num) hB1
  obtain ⟨M, hM0, hM⟩ := exists_bound_second_awGj n hn B
  obtain ⟨L, hL⟩ : ∃ L : NNReal,
      LipschitzOnWith L (fun q : awQ => fderiv ℝ (awGj n) q) (awKbox B) :=
    ((contDiffOn_fderiv_awGj n hn B).mono (awKbox_subset_awUbox (B := B))).exists_lipschitzOnWith
      (by decide) (convex_awKbox B) (isCompact_awKbox B)
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  refine ⟨M + (L : ℝ), add_nonneg hM0 hL0, ?_⟩
  intro h hh hsupp hjet s hs z hz
  have hs0 : |h s| ≤ 1 / 100 := by simpa using hjet 0 (by omega) s
  have hs1 : |deriv h s| ≤ 1 / 100 := by
    have := hjet 1 (by omega) s
    rwa [iteratedDeriv_one] at this
  have hpxl : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s :=
    Work.Anchor.DClose.profileX_lower hs
  have hpxu : Commons.Geometry.Ulam.profileX s ≤ 19 / 20 :=
    Work.Anchor.DClose.profileX_upper hs
  have hbs0 : baseState s 0 = Commons.Geometry.Ulam.profileX s := Work.Anchor.DClose.baseState_zero s
  have hbs1 : baseState s 1 = Commons.Geometry.Ulam.profileX s := Work.Anchor.DClose.baseState_one s
  have hbs2 : baseState s 2 = deriv Commons.Geometry.Ulam.profileX s :=
    Work.Anchor.DClose.baseState_two s
  have hbs3 : baseState s 3 = deriv Commons.Geometry.Ulam.profileX s :=
    Work.Anchor.DClose.baseState_three s
  set p : ℝ × ℝ × ℝ := (s, h s, deriv h s) with hp
  have hcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ 1 := fun i => by
    have h := norm_le_pi_norm (z - baseState s) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    have hz1 : ‖z - baseState s‖ ≤ 1 := by
      have := hz; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    exact le_trans h hz1
  -- the differentiability of the `fderiv` map
  have hsec : ContDiff ℝ ∞ (fun w : St => awGodd n h s w) := by
    have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 :=
      fun k hk t => hjet k (by omega) t
    have hC := aw_contDiffOn_awGodd n hh hsupp hsmall
    have h2 : ContDiffOn ℝ ∞ (fun w : St => awGodd n h s w) Set.univ :=
      hC.comp (f := fun w : St => (s, w)) (s := Set.univ)
        (contDiffOn_const.prodMk contDiffOn_id) (fun x _ => Set.mem_univ _)
    rwa [contDiffOn_univ] at h2
  have hfdsec : ContDiff ℝ ∞ (fun z' => fderiv ℝ (fun w : St => awGodd n h s w) z') :=
    hsec.fderiv_right le_rfl
  have hdiff : DifferentiableAt ℝ (fun z' => fderiv ℝ (fun w : St => awGodd n h s w) z') z :=
    (hfdsec.differentiable (by simp)).differentiableAt
  have heqfun : (fun w : St => awGodd n h s w) = fun w => awGj n (p, w) := by
    funext w; exact awGodd_eq_awGj n hh s w
  refine ⟨?_, ?_⟩
  · simpa only [heqfun] using hdiff
  · by_cases hcase : ‖z - baseState s‖ ≤ 2 / 5
    · -- inside the `2/5`-ball: use the joint box
      have hzp : ‖z - baseState s‖ ≤ 2 / 5 := hcase
      have box_of_coord : ∀ (z₁ : St) (R : ℝ), R ≤ 9 / 20 →
          (∀ i : Fin 4, |z₁ i - baseState s i| ≤ R) → (p, z₁) ∈ awKbox B := by
        intro z₁ R hR hc
        rw [awKbox, Set.mem_prod, Set.mem_prod, Set.mem_prod]
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · show s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20); exact hs
        · show h s ∈ Set.Icc (-(1 / 100) : ℝ) (1 / 100)
          exact Set.mem_Icc.mpr (abs_le.mp hs0)
        · show deriv h s ∈ Set.Icc (-(1 / 100) : ℝ) (1 / 100)
          exact Set.mem_Icc.mpr (abs_le.mp hs1)
        · rw [mem_awZbox_iff]
          have hc0 := hc 0; have hc1 := hc 1; have hc2 := hc 2; have hc3 := hc 3
          rw [hbs0] at hc0; rw [hbs1] at hc1; rw [hbs2] at hc2; rw [hbs3] at hc3
          have hB' := abs_le.mp (hB s hs)
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have h := (abs_le.mp hc0).1; linarith
          · have h := (abs_le.mp hc0).2; linarith
          · have h := (abs_le.mp hc1).1; linarith
          · have h := (abs_le.mp hc1).2; linarith
          · have h := (abs_le.mp hc2).1; linarith
          · have h := (abs_le.mp hc2).2; linarith
          · have h := (abs_le.mp hc3).1; linarith
          · have h := (abs_le.mp hc3).2; linarith
      have hcoord2 : ∀ i : Fin 4, |z i - baseState s i| ≤ 2 / 5 := fun i => by
        have h := norm_le_pi_norm (z - baseState s) i
        rw [Pi.sub_apply, Real.norm_eq_abs] at h
        exact le_trans h hzp
      have hbox_in : (p, z) ∈ awKbox B := box_of_coord z (2 / 5) (by norm_num) hcoord2
      have hbox_ball : ∀ z₁ ∈ Metric.closedBall (baseState s) (9 / 20 : ℝ), (p, z₁) ∈ awKbox B := by
        intro z₁ hz₁
        rw [Metric.mem_closedBall, dist_eq_norm] at hz₁
        refine box_of_coord z₁ (9 / 20) le_rfl fun i => ?_
        have h := norm_le_pi_norm (z₁ - baseState s) i
        rw [Pi.sub_apply, Real.norm_eq_abs] at h
        exact le_trans h hz₁
      have hLipSec : ∀ z₁ ∈ Metric.closedBall (baseState s) (9 / 20 : ℝ),
          ∀ z₂ ∈ Metric.closedBall (baseState s) (9 / 20 : ℝ),
          ‖fderiv ℝ (fun w => awGj n (p, w)) z₁ - fderiv ℝ (fun w => awGj n (p, w)) z₂‖
            ≤ (L : ℝ) * ‖z₁ - z₂‖ := by
        intro z₁ hz₁ z₂ hz₂
        have hm₁ := hbox_ball z₁ hz₁
        have hm₂ := hbox_ball z₂ hz₂
        rw [fderiv_awGj_section n hn (awKbox_subset_awUbox hm₁),
          fderiv_awGj_section n hn (awKbox_subset_awUbox hm₂), ← ContinuousLinearMap.sub_comp]
        calc ‖((fderiv ℝ (awGj n) (p, z₁) - fderiv ℝ (awGj n) (p, z₂))).comp
                (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St)‖
            ≤ ‖fderiv ℝ (awGj n) (p, z₁) - fderiv ℝ (awGj n) (p, z₂)‖ *
                ‖ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖fderiv ℝ (awGj n) (p, z₁) - fderiv ℝ (awGj n) (p, z₂)‖ := by
              rw [ContinuousLinearMap.norm_inr, mul_one]
          _ ≤ (L : ℝ) * ‖(p, z₁) - (p, z₂)‖ := by
              have h := hL.dist_le_mul _ hm₁ _ hm₂
              rwa [dist_eq_norm, dist_eq_norm] at h
          _ = (L : ℝ) * ‖z₁ - z₂‖ := by simp
      have hzint : z ∈ interior (Metric.closedBall (baseState s) (9 / 20 : ℝ)) := by
        rw [interior_closedBall _ (by norm_num), Metric.mem_ball, dist_eq_norm]
        linarith
      have hfeq : (fun z' : St => fderiv ℝ (fun w : St => awGodd n h s w) z')
          = fun z' : St => fderiv ℝ (fun w : St => awGj n (p, w)) z' :=
        funext fun z' => congrArg (fun F : St → St => fderiv ℝ F z') heqfun
      have hd : DifferentiableAt ℝ (fun z' => fderiv ℝ (fun w => awGj n (p, w)) z') z := by
        rw [← hfeq]
        exact hdiff
      have hbnd := aw_norm_fderiv_le_of_lipschitzOn
        (f := fun z' => fderiv ℝ (fun w => awGj n (p, w)) z') hL0 hLipSec hzint hd
      calc ‖fderiv ℝ (fun z' => fderiv ℝ (fun w => awGodd n h s w) z') z‖
          = ‖fderiv ℝ (fun z' => fderiv ℝ (fun w => awGj n (p, w)) z') z‖ := by rw [hfeq]
        _ ≤ (L : ℝ) := hbnd
        _ ≤ M + (L : ℝ) := le_add_of_nonneg_left hM0
    · -- outside: the datum vanishes identically near `z`
      have hlt : (2 / 5 : ℝ) < ‖z - baseState s‖ := lt_of_not_ge hcase
      have hU : {w : St | (2 / 5 : ℝ) < ‖w - baseState s‖} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hlt
      have hzero : (fun w : St => awGodd n h s w) =ᶠ[𝓝 z] (fun _ => (0 : St)) := by
        filter_upwards [hU] with w hw
        rw [awGodd]
        simp only [awChiG, awCz_eq_zero (le_of_lt hw), mul_zero, zero_smul]
      have hfd1 : fderiv ℝ (fun w : St => awGodd n h s w) z = 0 := by
        have h := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hzero
        simpa using h
      have hfd2 : (fun z' => fderiv ℝ (fun w : St => awGodd n h s w) z') =ᶠ[𝓝 z]
          (fun _ => (0 : St →L[ℝ] St)) := by
        filter_upwards [hU] with w hw
        have hzero' : (fun w' : St => awGodd n h s w') =ᶠ[𝓝 w] (fun _ => (0 : St)) := by
          have hU' : {w' : St | (2 / 5 : ℝ) < ‖w' - baseState s‖} ∈ 𝓝 w :=
            (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hw
          filter_upwards [hU'] with w' hw'
          rw [awGodd]
          simp only [awChiG, awCz_eq_zero (le_of_lt hw'), mul_zero, zero_smul]
        simpa using Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hzero'
      have hzero2 : fderiv ℝ (fun z' => fderiv ℝ (fun w : St => awGodd n h s w) z') z = 0 := by
        have h := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hfd2
        simpa using h
      have h0 : (0 : ℝ) ≤ M + (L : ℝ) := add_nonneg hM0 hL0
      rw [hzero2]
      rw [ContinuousLinearMap.opNorm_zero]
      exact h0

end

end Work.OddVolterra.Existence
