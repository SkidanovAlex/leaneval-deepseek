import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddCurveB.Est.Defs
import Submission.Work.OddCurveB.Existence.Explicit
import Submission.Work.OddCurveB.Existence.KdiagForm
import Submission.Work.OddCurveB.Est.Model
import Submission.Work.OddCurveB.Est.dist_fderiv_Godd_le

/-!
# Closeness of the differential of `𝐆` in the state and in the perturbation

`Work.Anchor.deriv_close`: there are constants `C₁, C₂ > 0` such that for every smooth bump `h`
supported in the transition window `[1 - 2τ, 1 - τ]` with `‖h‖_{C^{n+2}} ≤ δ ≤ 1/100`, every
slope `s ∈ [1/2, 19/20]` and every state `z` with `‖z - baseState s‖ ≤ 1/4`,

`‖fderiv (Godd n h s ·) z - fderiv (Godd n 0 s ·) (baseState s)‖ ≤ C₁ ‖z - baseState s‖ + C₂ δ`.

The map `Godd n h s` depends on `h` only through the two numbers `(h s, h'(s))`
(`Godd_eq_GoddDiag`), and the diagonal system is the *explicit* function
`GoddDiag n s (h s) (h' s) ·` of its arguments.  On the region where the two radicands
`Drad s hs hp (-z 0)` and `Drad s hs hp (z 1)` are positive, that explicit function is a
composition of the smooth functions `u ↦ u ^ k √u` (smooth on `(0,∞)`) with polynomial data,
hence `C^∞`; and the `fderiv` of a `C^∞` map is Lipschitz on a convex compact box by the mean
value theorem.  Everything is packaged as `exists_lipschitz_fderiv_Gdiag`.

The one place where the shape of the state box matters is the lower bound on `z 0` and `z 1`:
the radicand `Drad s hs hp (-(z 0)) = (h' s - z 0)(h s - s z 0)` must stay away from `0`, and on
the ball `‖z - baseState s‖ ≤ 1/4` this is guaranteed by `z 0 ≥ profileX s - 1/4 ≥ 9/20 > 0`.

(Import note: the statement only needs the *diagonal* data `GoddDiag`, `Kdiag1`, `Kdiag2` and
`abelMass`, so the file imports `OddCurveB.Existence.{Explicit,KdiagForm}` and
`OddCurveB.Est.Defs`; the `OddVolterra.Existence.data_close_of_small` import present in the
original skeleton is not used by the statement and was dropped while that module was temporarily
broken.)
-/

namespace Work.Anchor

open Work.OddVolterra Work.OddCurveB.Existence
open scoped Topology ContDiff

noncomputable section

/- The local development is wrapped in its own namespace so that the (rather generic) names
used below cannot clash with anything else in `Work.Anchor`. -/
namespace DClose

/-! ## 1. The joint data type, the two radicands and the two regions -/

/-- The joint data `(s, h s, h'(s), z)` of the diagonal system. -/
abbrev Q : Type := (ℝ × ℝ × ℝ) × St

/-- The diagonal Volterra map `𝐆` as a function of the joint data. -/
def Gdiag (n : ℕ) : Q → St := fun q => GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2

/-- The first diagonal kernel at the left endpoint `t = -z 0`. -/
def KA (n : ℕ) (q : Q) : ℝ := Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))

/-- The first diagonal kernel at the right endpoint `t = z 1`. -/
def KB (n : ℕ) (q : Q) : ℝ := Kdiag1 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)

/-- The second diagonal kernel at the left endpoint `t = -z 0`. -/
def KC (n : ℕ) (q : Q) : ℝ := Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))

/-- The second diagonal kernel at the right endpoint `t = z 1`. -/
def KD (n : ℕ) (q : Q) : ℝ := Kdiag2 n q.1.1 q.1.2.1 q.1.2.2 (q.2 1)

/-- The radicand `Drad = (t + h') (s t + h)` at the left endpoint `t = -z 0`. -/
def D1 (q : Q) : ℝ := Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0))

/-- The radicand `Drad` at the right endpoint `t = z 1`. -/
def D2 (q : Q) : ℝ := Drad q.1.1 q.1.2.1 q.1.2.2 (q.2 1)

/-- The open set of states on which the diagonal system is smooth: the two endpoint coordinates
must stay in `(2/5, 13/10)`, so that the radicands are bounded away from `0`. -/
def Zopen : Set St :=
  {z : St | (2 / 5 : ℝ) < z 0} ∩ {z : St | z 0 < 13 / 10} ∩
    {z : St | (2 / 5 : ℝ) < z 1} ∩ {z : St | z 1 < 13 / 10}

/-- The closed box of the estimate, with the bound `B` on `deriv profileX`. -/
def Zsafe (B : ℝ) : Set St :=
  Set.Icc ![9 / 20, 9 / 20, -(B + 1), -(B + 1)] ![6 / 5, 6 / 5, B + 1, B + 1]

/-- The closed box of the estimate. -/
def Ksafe (B : ℝ) : Set Q :=
  (Set.Icc (1 / 2 : ℝ) (19 / 20) ×ˢ
      (Set.Icc (-(1 / 100) : ℝ) (1 / 100) ×ˢ Set.Icc (-(1 / 100) : ℝ) (1 / 100))) ×ˢ
    Zsafe B

/-- The open box on which the diagonal system is `C^∞`. -/
def Usafe : Set Q :=
  (Set.Ioo (2 / 5 : ℝ) (11 / 10) ×ˢ
      (Set.Ioo (-(1 / 50) : ℝ) (1 / 50) ×ˢ Set.Ioo (-(1 / 50) : ℝ) (1 / 50))) ×ˢ Zopen

/-! ## 2. The two regions: openness, convexity, compactness, inclusion -/

lemma mem_Zopen {z : St} :
    z ∈ Zopen ↔ (2 / 5 : ℝ) < z 0 ∧ z 0 < 13 / 10 ∧ (2 / 5 : ℝ) < z 1 ∧ z 1 < 13 / 10 := by
  simp only [Zopen, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

lemma isOpen_Zopen : IsOpen Zopen := by
  have h : Zopen = {z : St | (2 / 5 : ℝ) < z 0} ∩ {z : St | z 0 < 13 / 10} ∩
      {z : St | (2 / 5 : ℝ) < z 1} ∩ {z : St | z 1 < 13 / 10} := rfl
  rw [h]
  exact IsOpen.inter (IsOpen.inter (IsOpen.inter
    (isOpen_lt continuous_const (continuous_apply 0)) (isOpen_lt (continuous_apply 0) continuous_const))
    (isOpen_lt continuous_const (continuous_apply 1))) (isOpen_lt (continuous_apply 1) continuous_const)

lemma isOpen_Usafe : IsOpen Usafe :=
  IsOpen.prod (IsOpen.prod isOpen_Ioo (IsOpen.prod isOpen_Ioo isOpen_Ioo)) isOpen_Zopen

lemma mem_Zsafe (B : ℝ) (z : St) : z ∈ Zsafe B ↔
    (9 / 20 ≤ z 0 ∧ z 0 ≤ 6 / 5) ∧ (9 / 20 ≤ z 1 ∧ z 1 ≤ 6 / 5) ∧
      (-(B + 1) ≤ z 2 ∧ z 2 ≤ B + 1) ∧ (-(B + 1) ≤ z 3 ∧ z 3 ≤ B + 1) := by
  simp only [Zsafe, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by simpa using h1 0, by simpa using h2 0⟩, ⟨by simpa using h1 1, by simpa using h2 1⟩,
      ⟨by simpa using h1 2, by simpa using h2 2⟩, ⟨by simpa using h1 3, by simpa using h2 3⟩⟩
  · rintro ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩, ⟨ha2, hb2⟩, ⟨ha3, hb3⟩⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp_all

lemma convex_Ksafe (B : ℝ) : Convex ℝ (Ksafe B) :=
  ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))).prod (convex_Icc _ _)

lemma isCompact_Ksafe (B : ℝ) : IsCompact (Ksafe B) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc

lemma Ksafe_subset_Usafe (B : ℝ) : Ksafe B ⊆ Usafe := by
  intro q hq
  obtain ⟨⟨hs, hh, hp⟩, hz⟩ := hq
  refine ⟨⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
    ⟨by linarith [hh.1], by linarith [hh.2]⟩,
    ⟨by linarith [hp.1], by linarith [hp.2]⟩⟩, ?_⟩
  have h := (mem_Zsafe B q.2).mp hz
  rw [mem_Zopen]
  exact ⟨by linarith [h.1.1], by linarith [h.1.2], by linarith [h.2.1.1], by linarith [h.2.1.2]⟩

/-! ## 3. Positivity of the two radicands on `Usafe` -/

lemma D1_pos_of_mem_Usafe {q : Q} (hq : q ∈ Usafe) : 0 < D1 q := by
  obtain ⟨⟨⟨hslo, hshi⟩, ⟨hplo, hphi⟩, ⟨hqlo, hqhi⟩⟩, hz⟩ := hq
  rw [mem_Zopen] at hz
  rw [D1, Drad]
  have h1 : 0 < q.2 0 - q.1.2.2 := by linarith [hz.1, hphi]
  have hspos : 0 < q.1.1 := by linarith
  have hzpos : 0 < q.2 0 := by linarith [hz.1]
  have hmul : (2 / 5 : ℝ) * (2 / 5) < q.1.1 * q.2 0 :=
    mul_lt_mul hslo (le_of_lt hz.1) (by norm_num) hspos.le
  have h2 : 0 < q.1.1 * q.2 0 - q.1.2.1 := by linarith [hmul, hqhi]
  rw [show (-(q.2 0) + q.1.2.2) * (q.1.1 * (-(q.2 0)) + q.1.2.1) =
      (q.2 0 - q.1.2.2) * (q.1.1 * q.2 0 - q.1.2.1) by ring]
  exact mul_pos h1 h2

lemma D2_pos_of_mem_Usafe {q : Q} (hq : q ∈ Usafe) : 0 < D2 q := by
  obtain ⟨⟨⟨hslo, hshi⟩, ⟨hplo, hphi⟩, ⟨hqlo, hqhi⟩⟩, hz⟩ := hq
  rw [mem_Zopen] at hz
  rw [D2, Drad]
  have h1 : 0 < q.2 1 + q.1.2.2 := by linarith [hz.2.2.1, hplo]
  have hspos : 0 < q.1.1 := by linarith
  have hzpos : 0 < q.2 1 := by linarith [hz.2.2.1]
  have hmul : (2 / 5 : ℝ) * (2 / 5) < q.1.1 * q.2 1 :=
    mul_lt_mul hslo (le_of_lt hz.2.2.1) (by norm_num) hspos.le
  have h2 : 0 < q.1.1 * q.2 1 + q.1.2.1 := by linarith [hmul, hplo]
  exact mul_pos h1 h2

/-! ## 4. Smoothness of the diagonal system on `Usafe` -/

lemma contDiffAt_pow_mul_sqrt (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (fun v : ℝ => v ^ k * Real.sqrt v) u :=
  ((contDiffAt_id (x := u)).pow k).mul (Real.contDiffAt_sqrt (ne_of_gt hu))

lemma contDiff_D1 : ContDiff ℝ ∞ (D1 : Q → ℝ) := by
  rw [show D1 = fun q : Q => Drad q.1.1 q.1.2.1 q.1.2.2 (-(q.2 0)) from rfl]
  simp only [Drad]
  fun_prop

lemma contDiff_D2 : ContDiff ℝ ∞ (D2 : Q → ℝ) := by
  rw [show D2 = fun q : Q => Drad q.1.1 q.1.2.1 q.1.2.2 (q.2 1) from rfl]
  simp only [Drad]
  fun_prop

lemma contDiff_proj (i : Fin 4) : ContDiff ℝ ∞ (fun q : Q => q.2 i) :=
  ((ContinuousLinearMap.proj (R := ℝ) i).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) St)).contDiff

lemma contDiff_lin : ContDiff ℝ ∞ (fun q : Q => -(q.2 0) + q.1.2.2) := by fun_prop

lemma contDiffAt_KA (n : ℕ) {q : Q} (hq : q ∈ Usafe) :
    ContDiffAt ℝ ∞ (fun q : Q => KA n q) q := by
  have hpos : 0 < D1 q := D1_pos_of_mem_Usafe hq
  have heq : (fun q : Q => KA n q) = fun q : Q =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (D1 q ^ n * Real.sqrt (D1 q)) := by
    funext q
    rw [KA, Kdiag1_eq]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : Q => D1 q ^ n * Real.sqrt (D1 q)) q :=
    (contDiffAt_pow_mul_sqrt n hpos).comp q (contDiff_D1.contDiffAt)
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_KB (n : ℕ) {q : Q} (hq : q ∈ Usafe) :
    ContDiffAt ℝ ∞ (fun q : Q => KB n q) q := by
  have hpos : 0 < D2 q := D2_pos_of_mem_Usafe hq
  have heq : (fun q : Q => KB n q) = fun q : Q =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (D2 q ^ n * Real.sqrt (D2 q)) := by
    funext q
    rw [KB, Kdiag1_eq]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : Q => D2 q ^ n * Real.sqrt (D2 q)) q :=
    (contDiffAt_pow_mul_sqrt n hpos).comp q (contDiff_D2.contDiffAt)
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_KC (n : ℕ) (hn : 1 ≤ n) {q : Q} (hq : q ∈ Usafe) :
    ContDiffAt ℝ ∞ (fun q : Q => KC n q) q := by
  have hpos : 0 < D1 q := D1_pos_of_mem_Usafe hq
  have heq : (fun q : Q => KC n q) = fun q : Q =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (D1 q ^ (n - 1) * Real.sqrt (D1 q)) * (-(q.2 0) + q.1.2.2) := by
    funext q
    rw [KC, Kdiag2_eq n hn]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : Q => D1 q ^ (n - 1) * Real.sqrt (D1 q)) q :=
    (contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q (contDiff_D1.contDiffAt)
  have hlin : ContDiffAt ℝ ∞ (fun q : Q => -(q.2 0) + q.1.2.2) q := contDiff_lin.contDiffAt
  simpa [smul_eq_mul] using (hcomp.const_smul
    ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_KD (n : ℕ) (hn : 1 ≤ n) {q : Q} (hq : q ∈ Usafe) :
    ContDiffAt ℝ ∞ (fun q : Q => KD n q) q := by
  have hpos : 0 < D2 q := D2_pos_of_mem_Usafe hq
  have heq : (fun q : Q => KD n q) = fun q : Q =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (D2 q ^ (n - 1) * Real.sqrt (D2 q)) * (q.2 1 + q.1.2.2) := by
    funext q
    rw [KD, Kdiag2_eq n hn]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : Q => D2 q ^ (n - 1) * Real.sqrt (D2 q)) q :=
    (contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q (contDiff_D2.contDiffAt)
  have hlin : ContDiffAt ℝ ∞ (fun q : Q => q.2 1 + q.1.2.2) q := by
    have h : ContDiff ℝ ∞ (fun q : Q => q.2 1 + q.1.2.2) := by fun_prop
    exact h.contDiffAt
  simpa [smul_eq_mul] using (hcomp.const_smul
    ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_Gdiag (n : ℕ) (hn : 1 ≤ n) {q : Q} (hq : q ∈ Usafe) :
    ContDiffAt ℝ ∞ (Gdiag n) q := by
  have hA := contDiffAt_KA n hq
  have hB := contDiffAt_KB n hq
  have hC := contDiffAt_KC n hn hq
  have hD := contDiffAt_KD n hn hq
  have h0 : ContDiffAt ℝ ∞ (fun q : Q => q.2 0) q := (contDiff_proj 0).contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun q : Q => q.2 1) q := (contDiff_proj 1).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun q : Q => q.2 2) q := (contDiff_proj 2).contDiffAt
  have h3 : ContDiffAt ℝ ∞ (fun q : Q => q.2 3) q := (contDiff_proj 3).contDiffAt
  have e2 : ContDiffAt ℝ ∞
      (fun q : Q => -(abelMass * (-(KA n q * q.2 2 + KB n q * q.2 3)))) q :=
    (((hA.mul h2).add (hB.mul h3)).neg.const_smul abelMass).neg
  have e3 : ContDiffAt ℝ ∞
      (fun q : Q => -(abelMass * (-(KC n q * q.2 2 + KD n q * q.2 3)))) q :=
    (((hC.mul h2).add (hD.mul h3)).neg.const_smul abelMass).neg
  have hfun : Gdiag n = fun q : Q => ![q.2 0, q.2 1,
      -(abelMass * (-(KA n q * q.2 2 + KB n q * q.2 3))),
      -(abelMass * (-(KC n q * q.2 2 + KD n q * q.2 3)))] := by
    funext q
    simp only [Gdiag, GoddDiag, KvecDiag, KA, KB, KC, KD, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  rw [hfun]
  refine (contDiffAt_pi).mpr (fun i => ?_)
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using e2
  · simpa using e3

lemma contDiffOn_Gdiag (n : ℕ) (hn : 1 ≤ n) : ContDiffOn ℝ ∞ (Gdiag n) Usafe := by
  rw [isOpen_Usafe.contDiffOn_iff]
  intro q hq
  exact contDiffAt_Gdiag n hn hq

lemma contDiffOn_fderiv_Gdiag (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ContDiffOn ℝ 1 (fun q : Q => fderiv ℝ (Gdiag n) q) (Ksafe B) := by
  have h2 : ContDiffOn ℝ 2 (Gdiag n) Usafe := (contDiffOn_Gdiag n hn).of_le (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiffOn ℝ 1 (fun q : Q => fderiv ℝ (Gdiag n) q) Usafe :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen isOpen_Usafe).1 h2).2.2
  exact ContDiffOn.mono h1 (Ksafe_subset_Usafe B)

/-- **Lipschitz bound for the differential of the diagonal system on the compact box.** -/
lemma exists_lipschitz_fderiv_Gdiag (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ∃ L : NNReal, LipschitzOnWith L (fun q : Q => fderiv ℝ (Gdiag n) q) (Ksafe B) :=
  (contDiffOn_fderiv_Gdiag n hn B).exists_lipschitzOnWith (by decide) (convex_Ksafe B)
    (isCompact_Ksafe B)

/-! ## 5. The partial derivative: the diagonal system in `z` -/

/-- The differential of the diagonal system with respect to the state, written as the joint
`fderiv` composed with the inclusion of the state in the joint space. -/
def Pdiag (n : ℕ) (q : Q) : St →L[ℝ] St :=
  (fderiv ℝ (Gdiag n) q).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St)

lemma Pdiag_eq (n : ℕ) (hn : 1 ≤ n) {q : Q} (hq : q ∈ Usafe) :
    Pdiag n q = fderiv ℝ (fun w : St => Gdiag n (q.1, w)) q.2 := by
  have hd : DifferentiableAt ℝ (Gdiag n) q :=
    ((contDiffOn_Gdiag n hn).contDiffAt (isOpen_Usafe.mem_nhds hq)).differentiableAt (by decide)
  have hin : DifferentiableAt ℝ (fun w : St => (q.1, w)) q.2 :=
    (differentiableAt_const q.1).prodMk differentiableAt_id
  have hcomp : fderiv ℝ (fun w : St => Gdiag n (q.1, w)) q.2 =
      (fderiv ℝ (Gdiag n) (q.1, q.2)).comp (fderiv ℝ (fun w : St => (q.1, w)) q.2) := by
    simpa [Function.comp_def] using fderiv_comp (x := q.2) (g := Gdiag n)
      (f := fun w : St => (q.1, w)) hd hin
  have hin' : fderiv ℝ (fun w : St => (q.1, w)) q.2
      = ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St :=
    (hasFDerivAt_prodMk_right q.1 q.2).fderiv
  rw [Pdiag, hcomp, hin']

/-! ## 6. Bounds on `profileX` and its derivative -/

lemma profileX_lower {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by nlinarith [hs.1, hs.2]
  have hpos : (0 : ℝ) < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Commons.Geometry.Ulam.profileX]
  rw [le_div_iff₀ hpos]
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ 10 / 7 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [hs2]⟩
  nlinarith [Real.sqrt_nonneg (1 + s ^ 2)]

lemma profileX_upper {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20)) :
    Commons.Geometry.Ulam.profileX s ≤ 19 / 20 := by
  have hpos : (0 : ℝ) < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Commons.Geometry.Ulam.profileX]
  rw [div_le_iff₀ hpos]
  have hsqrt : (20 / 19 : ℝ) ≤ Real.sqrt (1 + s ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hs.1]
  nlinarith

lemma baseState_zero (s : ℝ) : baseState s 0 = Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma baseState_one (s : ℝ) : baseState s 1 = Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma baseState_two (s : ℝ) : baseState s 2 = deriv Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

lemma baseState_three (s : ℝ) : baseState s 3 = deriv Commons.Geometry.Ulam.profileX s := by
  simp [baseState]

/-- An existential bound for the derivative of the profile. -/
lemma exists_deriv_profileX_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20),
      |deriv Commons.Geometry.Ulam.profileX s| ≤ B := by
  have hcont : Continuous (deriv Commons.Geometry.Ulam.profileX) :=
    Work.OddCurveB.Est.contDiff_profileX_est.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 1, le_max_right _ _, fun s hs => ?_⟩
  have h := hB s hs
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- The distance between two points of `Q` with the same slope, in terms of the coordinates. -/
lemma dist_q_le (s a a' : ℝ) (z z' : St) :
    dist (((s, a, a'), z) : Q) (((s, 0, 0), z') : Q) ≤ |a| + |a'| + ‖z - z'‖ := by
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq,
    dist_eq_norm, sub_zero, sub_zero, sub_self, abs_zero]
  change max (max 0 (max |a| |a'|)) ‖z - z'‖ ≤ |a| + |a'| + ‖z - z'‖
  refine max_le (max_le (by positivity) (max_le ?_ ?_)) ?_
  · linarith [abs_nonneg a, abs_nonneg a', norm_nonneg (z - z')]
  · linarith [abs_nonneg a, abs_nonneg a', norm_nonneg (z - z')]
  · linarith [abs_nonneg a, abs_nonneg a', norm_nonneg (z - z')]

end DClose

open DClose

/-! ## 7. The main theorem -/

theorem deriv_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ), ∀ z : Work.OddVolterra.St,
        ‖z - Work.OddVolterra.baseState s‖ ≤ 1 / 4 →
        ‖fderiv ℝ (fun w => Work.OddVolterra.Godd n h s w) z -
          fderiv ℝ (fun w => Work.OddVolterra.Godd n 0 s w)
            (Work.OddVolterra.baseState s)‖
          ≤ C₁ * ‖z - Work.OddVolterra.baseState s‖ + C₂ * δ := by
  obtain ⟨B, hB1, hB⟩ := exists_deriv_profileX_bound
  obtain ⟨L, hL⟩ := exists_lipschitz_fderiv_Gdiag n hn B
  refine ⟨(L : ℝ) + 1, 2 * (L : ℝ) + 1, by linarith [L.coe_nonneg],
    by linarith [L.coe_nonneg], ?_⟩
  intro h hh hsupp δ hδ hδ100 hder s hs z hz
  -- bounds on the two jets of `h`
  have hhsδ : |h s| ≤ δ := by
    have h0 := hder 0 (by omega) s
    rwa [iteratedDeriv_zero] at h0
  have hhpδ : |deriv h s| ≤ δ := by
    have h1 := hder 1 (by omega) s
    rwa [iteratedDeriv_one] at h1
  have hhs : |h s| ≤ 1 / 100 := le_trans hhsδ hδ100
  have hhp : |deriv h s| ≤ 1 / 100 := le_trans hhpδ hδ100
  -- coordinates of `z` relative to the base state
  have hzcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ ‖z - baseState s‖ := by
    intro i
    simpa using norm_le_pi_norm (z - baseState s) i
  have hz0 : |z 0 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 4 := by
    have h := hzcoord 0
    rw [baseState_zero] at h
    exact h.trans hz
  have hz1 : |z 1 - Commons.Geometry.Ulam.profileX s| ≤ 1 / 4 := by
    have h := hzcoord 1
    rw [baseState_one] at h
    exact h.trans hz
  have hz2 : |z 2 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 4 := by
    have h := hzcoord 2
    rw [baseState_two] at h
    exact h.trans hz
  have hz3 : |z 3 - deriv Commons.Geometry.Ulam.profileX s| ≤ 1 / 4 := by
    have h := hzcoord 3
    rw [baseState_three] at h
    exact h.trans hz
  have hpx : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s ∧
      Commons.Geometry.Ulam.profileX s ≤ 19 / 20 := ⟨profileX_lower hs, profileX_upper hs⟩
  -- membership in the open region
  have hque : (((s, h s, deriv h s), z) : Q) ∈ Usafe := by
    refine ⟨⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [(abs_le.mp hhs).1], by linarith [(abs_le.mp hhs).2]⟩,
      ⟨by linarith [(abs_le.mp hhp).1], by linarith [(abs_le.mp hhp).2]⟩⟩, ?_⟩
    rw [mem_Zopen]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h := (abs_le.mp hz0).1; linarith [hpx.1, h]
    · have h := (abs_le.mp hz0).2; linarith [hpx.2, h]
    · have h := (abs_le.mp hz1).1; linarith [hpx.1, h]
    · have h := (abs_le.mp hz1).2; linarith [hpx.2, h]
  -- membership of the two points in the closed box
  have hqK : (((s, h s, deriv h s), z) : Q) ∈ Ksafe B := by
    refine ⟨⟨⟨hs.1, hs.2⟩, ⟨abs_le.mp hhs, abs_le.mp hhp⟩⟩, ?_⟩
    rw [mem_Zsafe]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have h := (abs_le.mp hz0).1; linarith [hpx.1]
    · have h := (abs_le.mp hz0).2; linarith [hpx.2]
    · have h := (abs_le.mp hz1).1; linarith [hpx.1]
    · have h := (abs_le.mp hz1).2; linarith [hpx.2]
    · show -(B + 1) ≤ z 2
      have h := (abs_le.mp hz2).1
      linarith [hB s hs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
    · show z 2 ≤ B + 1
      have h := (abs_le.mp hz2).2
      linarith [hB s hs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
    · show -(B + 1) ≤ z 3
      have h := (abs_le.mp hz3).1
      linarith [hB s hs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
    · show z 3 ≤ B + 1
      have h := (abs_le.mp hz3).2
      linarith [hB s hs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
  have hq0K : (((s, 0, 0), baseState s) : Q) ∈ Ksafe B := by
    refine ⟨⟨⟨hs.1, hs.2⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩, ?_⟩
    rw [mem_Zsafe]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · show (9 / 20 : ℝ) ≤ baseState s 0
      rw [baseState_zero]; linarith [hpx.1]
    · show baseState s 0 ≤ 6 / 5
      rw [baseState_zero]; linarith [hpx.2]
    · show (9 / 20 : ℝ) ≤ baseState s 1
      rw [baseState_one]; linarith [hpx.1]
    · show baseState s 1 ≤ 6 / 5
      rw [baseState_one]; linarith [hpx.2]
    · show -(B + 1) ≤ baseState s 2
      rw [baseState_two]
      linarith [hB s hs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
    · show baseState s 2 ≤ B + 1
      rw [baseState_two]
      linarith [hB s hs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
    · show -(B + 1) ≤ baseState s 3
      rw [baseState_three]
      linarith [hB s hs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
    · show baseState s 3 ≤ B + 1
      rw [baseState_three]
      linarith [hB s hs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
  have hq0ue : (((s, 0, 0), baseState s) : Q) ∈ Usafe := Ksafe_subset_Usafe B hq0K
  -- the two differentials as joint `fderiv`s
  have hp1 : Pdiag n (((s, h s, deriv h s), z) : Q) =
      fderiv ℝ (fun w : St => Godd n h s w) z := by
    rw [Pdiag_eq n hn hque]
    simp only [Gdiag, Godd_eq_GoddDiag]
  have hp0 : Pdiag n (((s, 0, 0), baseState s) : Q) =
      fderiv ℝ (fun w : St => Godd n 0 s w) (baseState s) := by
    rw [Pdiag_eq n hn hq0ue]
    simp only [Gdiag, Godd_zero_eq]
  rw [← hp1, ← hp0]
  set q : Q := ((s, h s, deriv h s), z) with hqdef
  set q₀ : Q := ((s, 0, 0), baseState s) with hq0def
  have hrmem : q ∈ Ksafe B := hqK
  have hrmem0 : q₀ ∈ Ksafe B := hq0K
  have hLip := hL.dist_le_mul q hrmem q₀ hrmem0
  have hdqb : dist q q₀ ≤ |h s| + |deriv h s| + ‖z - baseState s‖ := by
    rw [hqdef, hq0def]
    exact dist_q_le s (h s) (deriv h s) z (baseState s)
  calc ‖Pdiag n q - Pdiag n q₀‖
      = ‖(fderiv ℝ (Gdiag n) q - fderiv ℝ (Gdiag n) q₀).comp
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St)‖ := by
        simp only [Pdiag, ContinuousLinearMap.sub_comp]
    _ ≤ ‖fderiv ℝ (Gdiag n) q - fderiv ℝ (Gdiag n) q₀‖ *
          ‖ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (Gdiag n) q - fderiv ℝ (Gdiag n) q₀‖ := by
        rw [ContinuousLinearMap.norm_inr, mul_one]
    _ = dist (fderiv ℝ (Gdiag n) q) (fderiv ℝ (Gdiag n) q₀) := by rw [dist_eq_norm]
    _ ≤ (L : ℝ) * dist q q₀ := hLip
    _ ≤ (L : ℝ) * (|h s| + |deriv h s| + ‖z - baseState s‖) :=
        mul_le_mul_of_nonneg_left hdqb L.coe_nonneg
    _ ≤ ((L : ℝ) + 1) * ‖z - baseState s‖ + (2 * (L : ℝ) + 1) * δ := by
        have hsum : |h s| + |deriv h s| ≤ 2 * δ := by linarith
        nlinarith [L.coe_nonneg, norm_nonneg (z - baseState s), hδ.le, abs_nonneg (h s),
          abs_nonneg (deriv h s)]

end

end Work.Anchor
