import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.Anchor.deriv_close
import Submission.Work.OddExistence.Estimates.godd_differentiable

/-!
# Closeness of the differential of `𝐆` on an arbitrary slope box

`Work.OddVolterra.WinData.FderivGoddCloseBox n a b ρ`: there are `Cg > 0` such that for every
smooth bump `h` supported in the transition window `[1 - 2τ, 1 - τ]` with
`‖h‖_{C^{n+2}} ≤ δ ≤ 1/100`, every slope `s ∈ [a,b] ⊆ (0,1]` (`a > 0`) and every state `z` with
`‖z - baseState s‖ ≤ ρ ≤ 1/2`,

`‖fderiv (Godd n h s ·) z - fderiv (Godd n 0 s ·) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + Cg δ`.

The proof is the same as the anchor-slope version `Work.Anchor.deriv_close`
(`s ∈ [1/2, 19/20]`, radius `1/4`), with two differences forced by the larger state ball
`ρ ≤ 1/2`:

* the two radicands `Drad s (h s) (h' s) (-(z 0))` and `Drad s (h s) (h' s) (z 1)` are only
  bounded away from `0` on the *support* of `h`: for `h s ≠ 0` the slope is `s ∈ [4/5, 9/10]`,
  and for `h s = 0` the two radicands equal `(z 0 - h' s) (s z 0)` and `(z 1 + h' s) (s z 1)`
  which are positive because `s ≥ a > 0` and `z 0, z 1 ≥ profileX s - 1/2 ≥ 1/5`.  Since the
  mean-value box has to stay inside the positivity region, the argument is split into the two
  cases `h s = 0` / `h s ≠ 0`, each with its own product box;
* `n = 1` is allowed: on the boxes `D1, D2 > 0`, so `Kdiag2 = c (D1^{n-1} √D1) (·)` is `C^∞` there
  (`Real.contDiffAt_sqrt`) — no `ContDiff` at a zero of the radicand is needed.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

open Work.OddVolterra
open Work.OddCurveB.Existence
open Work.Anchor.DClose (Gdiag D1 D2 Pdiag KA KB KC KD)

noncomputable section

/-- The compact box of states: the two endpoint coordinates lie in `[1/5, 3/2]` and the two
derivative coordinates in `[-C, C]`.  For `C ≥ B + 1/2` it contains the ball of radius `1/2`
around every `baseState s` with `|deriv profileX s| ≤ B`. -/
def Zbox (C : ℝ) : Set St := Set.Icc ![1 / 5, 1 / 5, -C, -C] ![3 / 2, 3 / 2, C, C]

lemma convex_Zbox (C : ℝ) : Convex ℝ (Zbox C) := convex_Icc _ _

lemma isCompact_Zbox (C : ℝ) : IsCompact (Zbox C) := isCompact_Icc

lemma mem_Zbox {C : ℝ} {z : St} :
    z ∈ Zbox C ↔ (1 / 5 ≤ z 0 ∧ z 0 ≤ 3 / 2) ∧ (1 / 5 ≤ z 1 ∧ z 1 ≤ 3 / 2) ∧
      (-C ≤ z 2 ∧ z 2 ≤ C) ∧ (-C ≤ z 3 ∧ z 3 ≤ C) := by
  simp only [Zbox, Set.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h1 0
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h2 0
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h1 1
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h2 1
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h1 2
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h2 2
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h1 3
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h2 3
  · rintro ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;> simp_all

/-- A compact product box of joint data `((s, hs, hp), z)`. -/
def Qbox (slo shi hlo hhi plo phi C : ℝ) : Set ((ℝ × ℝ × ℝ) × St) :=
  (Set.Icc slo shi ×ˢ (Set.Icc hlo hhi ×ˢ Set.Icc plo phi)) ×ˢ Zbox C

lemma convex_Qbox (slo shi hlo hhi plo phi C : ℝ) :
    Convex ℝ (Qbox slo shi hlo hhi plo phi C) :=
  ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))).prod (convex_Zbox C)

lemma isCompact_Qbox (slo shi hlo hhi plo phi C : ℝ) :
    IsCompact (Qbox slo shi hlo hhi plo phi C) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod (isCompact_Zbox C)

lemma mem_Qbox {slo shi hlo hhi plo phi C s hs hp : ℝ} {z : St} :
    (((s, hs, hp), z) : (ℝ × ℝ × ℝ) × St) ∈ Qbox slo shi hlo hhi plo phi C ↔
      (slo ≤ s ∧ s ≤ shi) ∧ (hlo ≤ hs ∧ hs ≤ hhi) ∧ (plo ≤ hp ∧ hp ≤ phi) ∧ z ∈ Zbox C := by
  simp only [Qbox, Set.mem_prod, Set.mem_Icc]
  tauto

/-! ## 2. Smoothness of the diagonal system where the two radicands are positive -/

/-- `x ↦ x ^ k √x` is `C^∞` at every `u > 0`. -/
lemma contDiffAt_pow_mul_sqrt (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ ∞ (fun v : ℝ => v ^ k * Real.sqrt v) u :=
  ((contDiffAt_id (x := u)).pow k).mul (Real.contDiffAt_sqrt (ne_of_gt hu))

lemma contDiffAt_KA_pos (n : ℕ) {q : (ℝ × ℝ × ℝ) × St} (hpos : 0 < D1 q) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => KA n q) q := by
  have heq : (fun q : (ℝ × ℝ × ℝ) × St => KA n q) = fun q : (ℝ × ℝ × ℝ) × St =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (D1 q ^ n * Real.sqrt (D1 q)) := by
    funext q
    rw [KA, Kdiag1_eq]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => D1 q ^ n * Real.sqrt (D1 q)) q :=
    (contDiffAt_pow_mul_sqrt n hpos).comp q (Work.Anchor.DClose.contDiff_D1.contDiffAt)
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_KB_pos (n : ℕ) {q : (ℝ × ℝ × ℝ) × St} (hpos : 0 < D2 q) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => KB n q) q := by
  have heq : (fun q : (ℝ × ℝ × ℝ) × St => KB n q) = fun q : (ℝ × ℝ × ℝ) × St =>
      ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
        (D2 q ^ n * Real.sqrt (D2 q)) := by
    funext q
    rw [KB, Kdiag1_eq]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => D2 q ^ n * Real.sqrt (D2 q)) q :=
    (contDiffAt_pow_mul_sqrt n hpos).comp q (Work.Anchor.DClose.contDiff_D2.contDiffAt)
  simpa [smul_eq_mul] using hcomp.const_smul
    ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2)

lemma contDiffAt_KC_pos (n : ℕ) (hn : 1 ≤ n) {q : (ℝ × ℝ × ℝ) × St} (hpos : 0 < D1 q) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => KC n q) q := by
  have heq : (fun q : (ℝ × ℝ × ℝ) × St => KC n q) = fun q : (ℝ × ℝ × ℝ) × St =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (D1 q ^ (n - 1) * Real.sqrt (D1 q)) * (-(q.2 0) + q.1.2.2) := by
    funext q
    rw [KC, Kdiag2_eq n hn]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St =>
      D1 q ^ (n - 1) * Real.sqrt (D1 q)) q :=
    (contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q (Work.Anchor.DClose.contDiff_D1.contDiffAt)
  have hlin : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => -(q.2 0) + q.1.2.2) q :=
    Work.Anchor.DClose.contDiff_lin.contDiffAt
  simpa [smul_eq_mul] using (hcomp.const_smul
    ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_KD_pos (n : ℕ) (hn : 1 ≤ n) {q : (ℝ × ℝ × ℝ) × St} (hpos : 0 < D2 q) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => KD n q) q := by
  have heq : (fun q : (ℝ × ℝ × ℝ) × St => KD n q) = fun q : (ℝ × ℝ × ℝ) × St =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (D2 q ^ (n - 1) * Real.sqrt (D2 q)) * (q.2 1 + q.1.2.2) := by
    funext q
    rw [KD, Kdiag2_eq n hn]
    rfl
  rw [heq]
  have hcomp : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St =>
      D2 q ^ (n - 1) * Real.sqrt (D2 q)) q :=
    (contDiffAt_pow_mul_sqrt (n - 1) hpos).comp q (Work.Anchor.DClose.contDiff_D2.contDiffAt)
  have hlin : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 1 + q.1.2.2) q := by
    have h : ContDiff ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 1 + q.1.2.2) := by fun_prop
    exact h.contDiffAt
  simpa [smul_eq_mul] using (hcomp.const_smul
    ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2)).mul hlin

lemma contDiffAt_Gdiag_pos (n : ℕ) (hn : 1 ≤ n) {q : (ℝ × ℝ × ℝ) × St}
    (h1 : 0 < D1 q) (h2 : 0 < D2 q) : ContDiffAt ℝ ∞ (Gdiag n) q := by
  have hA := contDiffAt_KA_pos n h1
  have hB := contDiffAt_KB_pos n h2
  have hC := contDiffAt_KC_pos n hn h1
  have hD := contDiffAt_KD_pos n hn h2
  have h0 : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 0) q :=
    (Work.Anchor.DClose.contDiff_proj 0).contDiffAt
  have h1' : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 1) q :=
    (Work.Anchor.DClose.contDiff_proj 1).contDiffAt
  have h2' : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 2) q :=
    (Work.Anchor.DClose.contDiff_proj 2).contDiffAt
  have h3' : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ × ℝ) × St => q.2 3) q :=
    (Work.Anchor.DClose.contDiff_proj 3).contDiffAt
  have e2 : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ × ℝ) × St => -(abelMass * (-(KA n q * q.2 2 + KB n q * q.2 3)))) q :=
    (((hA.mul h2').add (hB.mul h3')).neg.const_smul abelMass).neg
  have e3 : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℝ × ℝ) × St => -(abelMass * (-(KC n q * q.2 2 + KD n q * q.2 3)))) q :=
    (((hC.mul h2').add (hD.mul h3')).neg.const_smul abelMass).neg
  have hfun : Gdiag n = fun q : (ℝ × ℝ × ℝ) × St => ![q.2 0, q.2 1,
      -(abelMass * (-(KA n q * q.2 2 + KB n q * q.2 3))),
      -(abelMass * (-(KC n q * q.2 2 + KD n q * q.2 3)))] := by
    funext q
    simp only [Gdiag, GoddDiag, KvecDiag, KA, KB, KC, KD, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  rw [hfun]
  refine (contDiffAt_pi).mpr (fun i => ?_)
  fin_cases i
  · simpa using h0
  · simpa using h1'
  · simpa using e2
  · simpa using e3

/-- The open region on which the diagonal system is smooth: both radicands positive. -/
def Upos : Set ((ℝ × ℝ × ℝ) × St) := {q | 0 < D1 q} ∩ {q | 0 < D2 q}

lemma isOpen_Upos : IsOpen Upos :=
  (isOpen_lt continuous_const Work.Anchor.DClose.contDiff_D1.continuous).inter
    (isOpen_lt continuous_const Work.Anchor.DClose.contDiff_D2.continuous)

lemma contDiffOn_Gdiag_Upos (n : ℕ) (hn : 1 ≤ n) : ContDiffOn ℝ ∞ (Gdiag n) Upos := by
  rw [isOpen_Upos.contDiffOn_iff]
  intro q hq
  exact contDiffAt_Gdiag_pos n hn hq.1 hq.2

lemma contDiffOn_fderiv_Gdiag_Upos (n : ℕ) (hn : 1 ≤ n) :
    ContDiffOn ℝ 1 (fun q => fderiv ℝ (Gdiag n) q) Upos := by
  have h2 : ContDiffOn ℝ 2 (Gdiag n) Upos :=
    (contDiffOn_Gdiag_Upos n hn).of_le (WithTop.coe_le_coe.mpr le_top)
  exact ((contDiffOn_succ_iff_fderiv_of_isOpen isOpen_Upos).1 h2).2.2

/-- **Lipschitz bound for the differential of the diagonal system** on any compact convex box
inside the positivity region. -/
lemma exists_lipschitz_fderiv_Gdiag_pos (n : ℕ) (hn : 1 ≤ n) {K : Set ((ℝ × ℝ × ℝ) × St)}
    (hK : K ⊆ Upos) (hconv : Convex ℝ K) (hcomp : IsCompact K) :
    ∃ L : NNReal, LipschitzOnWith L (fun q => fderiv ℝ (Gdiag n) q) K :=
  ((contDiffOn_fderiv_Gdiag_Upos n hn).mono hK).exists_lipschitzOnWith (by decide) hconv hcomp

/-- The differential in the state, as the joint differential composed with the inclusion of the
state. -/
lemma Pdiag_eq_of_pos (n : ℕ) (hn : 1 ≤ n) {q : (ℝ × ℝ × ℝ) × St}
    (h1 : 0 < D1 q) (h2 : 0 < D2 q) :
    Pdiag n q = fderiv ℝ (fun w : St => Gdiag n (q.1, w)) q.2 := by
  have hd : DifferentiableAt ℝ (Gdiag n) q :=
    (contDiffAt_Gdiag_pos n hn h1 h2).differentiableAt (by decide)
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

/-! ## 3. Positivity of the two radicands on the boxes -/

lemma D1_pos_of_bounds {s hs hp : ℝ} {z : St}
    (hs45 : (4 : ℝ) / 5 ≤ s) (hz : 1 / 5 ≤ z 0) (hhs : |hs| ≤ 1 / 100)
    (hhp : |hp| ≤ 1 / 100) : 0 < D1 (((s, hs, hp), z) : (ℝ × ℝ × ℝ) × St) := by
  rw [D1, Drad]
  have h1 : 0 < z 0 - hp := by
    have h := (abs_le.mp hhp).2; linarith
  have h2 : 0 < s * z 0 - hs := by
    have hsz : ((4 : ℝ) / 5) * (1 / 5) ≤ s * z 0 := by nlinarith [hs45, hz]
    have h := (abs_le.mp hhs).2; linarith
  have key : (-(z 0) + hp) * (s * (-(z 0)) + hs) = (z 0 - hp) * (s * z 0 - hs) := by ring
  rw [key]
  exact mul_pos h1 h2

lemma D1_pos_of_zero {s hp : ℝ} {z : St} (hs0 : 0 < s) (hz : 1 / 5 ≤ z 0)
    (hhp : |hp| ≤ 1 / 100) : 0 < D1 (((s, 0, hp), z) : (ℝ × ℝ × ℝ) × St) := by
  rw [D1, Drad]
  have h1 : 0 < z 0 - hp := by
    have h := (abs_le.mp hhp).2; linarith
  have h2 : 0 < s * z 0 := mul_pos hs0 (by linarith)
  have key : (-(z 0) + hp) * (s * (-(z 0)) + 0) = (z 0 - hp) * (s * z 0) := by ring
  rw [key]
  exact mul_pos h1 h2

lemma D2_pos_of_bounds {s hs hp : ℝ} {z : St}
    (hs45 : (4 : ℝ) / 5 ≤ s) (hz : 1 / 5 ≤ z 1) (hhs : |hs| ≤ 1 / 100)
    (hhp : |hp| ≤ 1 / 100) : 0 < D2 (((s, hs, hp), z) : (ℝ × ℝ × ℝ) × St) := by
  rw [D2, Drad]
  have h1 : 0 < z 1 + hp := by
    have h := (abs_le.mp hhp).1; linarith
  have h2 : 0 < s * z 1 + hs := by
    have hsz : ((4 : ℝ) / 5) * (1 / 5) ≤ s * z 1 := by nlinarith [hs45, hz]
    have h := (abs_le.mp hhs).1; linarith
  exact mul_pos h1 h2

lemma D2_pos_of_zero {s hp : ℝ} {z : St} (hs0 : 0 < s) (hz : 1 / 5 ≤ z 1)
    (hhp : |hp| ≤ 1 / 100) : 0 < D2 (((s, 0, hp), z) : (ℝ × ℝ × ℝ) × St) := by
  rw [D2, Drad]
  have h1 : 0 < z 1 + hp := by
    have h := (abs_le.mp hhp).1; linarith
  have h2 : 0 < s * z 1 := mul_pos hs0 (by linarith)
  show 0 < (z 1 + hp) * (s * z 1 + 0)
  rw [show s * z 1 + 0 = s * z 1 by ring]
  exact mul_pos h1 h2

/-! ## 4. Bounds on the profile and on the state ball -/

lemma profileX_le_one (s : ℝ) : Commons.Geometry.Ulam.profileX s ≤ 1 := by
  rw [Commons.Geometry.Ulam.profileX]
  rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
  exact Real.one_le_sqrt.2 (by linarith [sq_nonneg s])

lemma profileX_mem_Icc {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s ∧
      Commons.Geometry.Ulam.profileX s ≤ 1 :=
  ⟨Work.OddExistence.Estimates.gd_profileX_ge hs0 hs1, profileX_le_one s⟩

/-- The ball of radius `ρ ≤ 1/2` around `baseState s` lies in the fixed box `Zbox C`, provided
`C ≥ B + 1/2` where `B` bounds `(profileX)'` at the slope. -/
lemma mem_Zbox_of_mem_ball {B C ρ s : ℝ} {z : St}
    (hz : z ∈ Metric.closedBall (baseState s) ρ) (hρ : ρ ≤ 1 / 2)
    (hpx : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s ∧
      Commons.Geometry.Ulam.profileX s ≤ 1)
    (hBs : |deriv Commons.Geometry.Ulam.profileX s| ≤ B) (hBC : B + 1 / 2 ≤ C) :
    z ∈ Zbox C := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ 1 / 2 := by
    intro i
    have h := norm_le_pi_norm (z - baseState s) i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact le_trans h (le_trans hz hρ)
  have h0 := hcoord 0
  rw [Work.Anchor.DClose.baseState_zero] at h0
  have h1 := hcoord 1
  rw [Work.Anchor.DClose.baseState_one] at h1
  have h2 := hcoord 2
  rw [Work.Anchor.DClose.baseState_two] at h2
  have h3 := hcoord 3
  rw [Work.Anchor.DClose.baseState_three] at h3
  rw [mem_Zbox]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h := (abs_le.mp h0).1; linarith [hpx.1]
  · have h := (abs_le.mp h0).2; linarith [hpx.2]
  · have h := (abs_le.mp h1).1; linarith [hpx.1]
  · have h := (abs_le.mp h1).2; linarith [hpx.2]
  · have h := (abs_le.mp h2).1
    linarith [hBs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
  · have h := (abs_le.mp h2).2
    linarith [hBs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]
  · have h := (abs_le.mp h3).1
    linarith [hBs, neg_abs_le (deriv Commons.Geometry.Ulam.profileX s)]
  · have h := (abs_le.mp h3).2
    linarith [hBs, le_abs_self (deriv Commons.Geometry.Ulam.profileX s)]

/-! ## 5. From Lipschitz on the box to the estimate -/

lemma norm_Pdiag_sub_le {n : ℕ} {L : NNReal} {K : Set ((ℝ × ℝ × ℝ) × St)}
    (hL : LipschitzOnWith L (fun q => fderiv ℝ (Gdiag n) q) K)
    {q q₀ : (ℝ × ℝ × ℝ) × St} (hq : q ∈ K) (hq₀ : q₀ ∈ K) :
    ‖Pdiag n q - Pdiag n q₀‖ ≤ (L : ℝ) * dist q q₀ := by
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
    _ ≤ (L : ℝ) * dist q q₀ := hL.dist_le_mul q hq q₀ hq₀


/-! ## 6. Positivity of the radicands on the two boxes -/

lemma D1D2_pos_box_zero {a b C : ℝ} (ha : 0 < a) :
    ∀ q ∈ Qbox a b 0 0 (-(1 / 100)) (1 / 100) C, 0 < D1 q ∧ 0 < D2 q := by
  intro q hq
  obtain ⟨⟨s, hs, hp⟩, z⟩ := q
  rw [mem_Qbox] at hq
  obtain ⟨⟨hs1, hs2⟩, ⟨hh1, hh2⟩, ⟨hp1, hp2⟩, hz⟩ := hq
  obtain rfl : hs = 0 := le_antisymm hh2 hh1
  obtain ⟨hz0, hz1, hz2, hz3⟩ := mem_Zbox.mp hz
  have hspos : 0 < s := lt_of_lt_of_le ha hs1
  exact ⟨D1_pos_of_zero hspos hz0.1 (abs_le.mpr ⟨hp1, hp2⟩),
    D2_pos_of_zero hspos hz1.1 (abs_le.mpr ⟨hp1, hp2⟩)⟩

lemma D1D2_pos_box_window {a b C : ℝ} :
    ∀ q ∈ Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
          (-(1 / 100)) (1 / 100) C, 0 < D1 q ∧ 0 < D2 q := by
  intro q hq
  obtain ⟨⟨s, hs, hp⟩, z⟩ := q
  rw [mem_Qbox] at hq
  obtain ⟨⟨hs1, hs2⟩, ⟨hh1, hh2⟩, ⟨hp1, hp2⟩, hz⟩ := hq
  obtain ⟨hz0, hz1, hz2, hz3⟩ := mem_Zbox.mp hz
  have hs45 : (4 : ℝ) / 5 ≤ s := le_trans (le_max_right _ _) hs1
  exact ⟨D1_pos_of_bounds hs45 hz0.1 (abs_le.mpr ⟨hh1, hh2⟩) (abs_le.mpr ⟨hp1, hp2⟩),
    D2_pos_of_bounds hs45 hz1.1 (abs_le.mpr ⟨hh1, hh2⟩) (abs_le.mpr ⟨hp1, hp2⟩)⟩

/-! ## 7. The identification of the state differential with `Pdiag` -/

lemma Pdiag_Godd (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ) {s : ℝ} {z : St}
    (h1 : 0 < D1 (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St))
    (h2 : 0 < D2 (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St)) :
    Pdiag n (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) =
      fderiv ℝ (fun w => Godd n h s w) z := by
  rw [Pdiag_eq_of_pos n hn h1 h2]
  simp only [Gdiag, Godd_eq_GoddDiag]

lemma Pdiag_Godd_zero (n : ℕ) (hn : 1 ≤ n) {s : ℝ} {z : St}
    (h1 : 0 < D1 (((s, 0, 0), z) : (ℝ × ℝ × ℝ) × St))
    (h2 : 0 < D2 (((s, 0, 0), z) : (ℝ × ℝ × ℝ) × St)) :
    Pdiag n (((s, 0, 0), z) : (ℝ × ℝ × ℝ) × St) =
      fderiv ℝ (fun w => Godd n 0 s w) z := by
  rw [Pdiag_eq_of_pos n hn h1 h2]
  simp only [Gdiag, Godd_zero_eq]

lemma Pdiag_Godd_of_zero (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} {s : ℝ} {z : St}
    (hzero : h s = 0)
    (h1 : 0 < D1 (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St))
    (h2 : 0 < D2 (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St)) :
    Pdiag n (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St) =
      fderiv ℝ (fun w => Godd n h s w) z := by
  rw [Pdiag_eq_of_pos n hn h1 h2]
  simp only [Gdiag, Godd_eq_GoddDiag, hzero]

/-! ## 8. The estimate -/

theorem fderiv_godd_close_box (n : ℕ) (hn : 1 ≤ n) {a b ρ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) ρ,
        ‖fderiv ℝ (fun w => Work.OddVolterra.Godd n h s w) z -
         fderiv ℝ (fun w => Work.OddVolterra.Godd n 0 s w) (Work.OddVolterra.baseState s)‖
          ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + Cg * δ := by
  -- a bound for the derivative of the profile on the slope box
  obtain ⟨B, hB1, hB⟩ : ∃ B : ℝ, 1 ≤ B ∧
      ∀ s ∈ Set.Icc a b, |deriv Commons.Geometry.Ulam.profileX s| ≤ B := by
    have hcont : Continuous (deriv Commons.Geometry.Ulam.profileX) :=
      Work.OddCurveB.Est.contDiff_profileX_est.continuous_deriv (by simp)
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
      (s := Set.Icc a b)
    refine ⟨max B 1, le_max_right _ _, fun s hs => ?_⟩
    have h := hB s hs
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  set C : ℝ := B + 1 with hC
  have hBC : B + 1 / 2 ≤ C := by rw [hC]; linarith
  -- the two Lipschitz constants
  obtain ⟨L0, hL0⟩ := exists_lipschitz_fderiv_Gdiag_pos n hn
    (K := Qbox a b 0 0 (-(1 / 100)) (1 / 100) C) (D1D2_pos_box_zero ha)
    (convex_Qbox a b 0 0 (-(1 / 100)) (1 / 100) C)
    (isCompact_Qbox a b 0 0 (-(1 / 100)) (1 / 100) C)
  obtain ⟨L1, hL1⟩ := exists_lipschitz_fderiv_Gdiag_pos n hn
    (K := Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
      (-(1 / 100)) (1 / 100) C) D1D2_pos_box_window
    (convex_Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
      (-(1 / 100)) (1 / 100) C)
    (isCompact_Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
      (-(1 / 100)) (1 / 100) C)
  have hCgpos : 0 < max (L0 : ℝ) (2 * (L1 : ℝ)) + 1 := by
    have h : (0 : ℝ) ≤ max (L0 : ℝ) (2 * (L1 : ℝ)) :=
      le_trans L0.coe_nonneg (le_max_left _ _)
    linarith
  refine ⟨max (L0 : ℝ) (2 * (L1 : ℝ)) + 1, hCgpos, ?_⟩
  intro h hh hsupp δ hδ hδ100 hjet s hs z hz
  -- jet bounds on `h` at `s`
  have hhsδ : |h s| ≤ δ := by
    have h0 := hjet 0 (by omega) s
    rwa [iteratedDeriv_zero] at h0
  have hhpδ : |deriv h s| ≤ δ := by
    have h1 := hjet 1 (by omega) s
    rwa [iteratedDeriv_one] at h1
  have hhs : |h s| ≤ 1 / 100 := le_trans hhsδ hδ100
  have hhp : |deriv h s| ≤ 1 / 100 := le_trans hhpδ hδ100
  -- the state and the base state in the fixed box
  have hsr : ‖z - baseState s‖ ≤ ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
  have hs0 : 0 ≤ s := le_of_lt (lt_of_lt_of_le ha hs.1)
  have hs1 : s ≤ 1 := le_trans hs.2 hb
  have hpx := profileX_mem_Icc hs0 hs1
  have hzC : z ∈ Zbox C := mem_Zbox_of_mem_ball hz hρ1 hpx (hB s hs) hBC
  have hbsC : baseState s ∈ Zbox C :=
    mem_Zbox_of_mem_ball (Metric.mem_closedBall_self (le_of_lt hρ0)) hρ1 hpx (hB s hs) hBC
  have hCg : (L0 : ℝ) ≤ max (L0 : ℝ) (2 * (L1 : ℝ)) + 1 := by
    linarith [le_max_left (L0 : ℝ) (2 * (L1 : ℝ)), L0.coe_nonneg]
  have hCg' : (2 * (L1 : ℝ)) ≤ max (L0 : ℝ) (2 * (L1 : ℝ)) + 1 := by
    linarith [le_max_right (L0 : ℝ) (2 * (L1 : ℝ))]
  have hCg'' : (L1 : ℝ) ≤ max (L0 : ℝ) (2 * (L1 : ℝ)) + 1 := by
    linarith [le_max_right (L0 : ℝ) (2 * (L1 : ℝ)), L1.coe_nonneg]
  rcases eq_or_ne (h s) 0 with hzero | hne
  · -- ## Case `h s = 0`
    have hq : (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St) ∈
        Qbox a b 0 0 (-(1 / 100)) (1 / 100) C := by
      rw [mem_Qbox]
      exact ⟨⟨hs.1, hs.2⟩, ⟨le_rfl, le_rfl⟩,
        ⟨(abs_le.mp hhp).1, (abs_le.mp hhp).2⟩, hzC⟩
    have hq₀ : (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St) ∈
        Qbox a b 0 0 (-(1 / 100)) (1 / 100) C := by
      rw [mem_Qbox]
      exact ⟨⟨hs.1, hs.2⟩, ⟨le_rfl, le_rfl⟩, ⟨by norm_num, by norm_num⟩, hbsC⟩
    have hpos := D1D2_pos_box_zero ha _ hq
    have hpos₀ := D1D2_pos_box_zero ha _ hq₀
    rw [← Pdiag_Godd_of_zero n hn hzero hpos.1 hpos.2,
      ← Pdiag_Godd_zero n hn hpos₀.1 hpos₀.2]
    have hb := norm_Pdiag_sub_le hL0 hq hq₀
    have hd := Work.Anchor.DClose.dist_q_le s 0 (deriv h s) z (baseState s)
    calc ‖Pdiag n (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St) -
          Pdiag n (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St)‖
        ≤ (L0 : ℝ) * dist (((s, 0, deriv h s), z) : (ℝ × ℝ × ℝ) × St)
            (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St) := hb
      _ ≤ (L0 : ℝ) * (|(0 : ℝ)| + |deriv h s| + ‖z - baseState s‖) :=
          mul_le_mul_of_nonneg_left hd L0.coe_nonneg
      _ ≤ (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * ‖z - baseState s‖ +
          (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * δ := by
          have h1 : (L0 : ℝ) * |deriv h s| ≤ (L0 : ℝ) * δ :=
            mul_le_mul_of_nonneg_left hhpδ L0.coe_nonneg
          have h2 : (L0 : ℝ) * ‖z - baseState s‖ ≤
              (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * ‖z - baseState s‖ :=
            mul_le_mul_of_nonneg_right hCg (norm_nonneg _)
          have h3 : (L0 : ℝ) * δ ≤ (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * δ :=
            mul_le_mul_of_nonneg_right hCg hδ.le
          rw [abs_zero]
          nlinarith [h1, h2, h3]
  · -- ## Case `h s ≠ 0`: the slope lies in the transition window
    have hmem : s ∈ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
      hsupp hne
    have hs45 : (4 : ℝ) / 5 ≤ s := by
      have h := hmem.1
      rw [Work.OddVolterra.tau] at h
      norm_num at h
      exact h
    have hs910 : s ≤ 9 / 10 := by
      have h := hmem.2
      rw [Work.OddVolterra.tau] at h
      norm_num at h
      exact h
    have hq : (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) ∈
        Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
          (-(1 / 100)) (1 / 100) C := by
      rw [mem_Qbox]
      exact ⟨⟨max_le hs.1 hs45, le_min hs.2 hs910⟩,
        ⟨(abs_le.mp hhs).1, (abs_le.mp hhs).2⟩,
        ⟨(abs_le.mp hhp).1, (abs_le.mp hhp).2⟩, hzC⟩
    have hq₀ : (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St) ∈
        Qbox (max a (4 / 5)) (min b (9 / 10)) (-(1 / 100)) (1 / 100)
          (-(1 / 100)) (1 / 100) C := by
      rw [mem_Qbox]
      exact ⟨⟨max_le hs.1 hs45, le_min hs.2 hs910⟩, ⟨by norm_num, by norm_num⟩,
        ⟨by norm_num, by norm_num⟩, hbsC⟩
    have hpos := D1D2_pos_box_window _ hq
    have hpos₀ := D1D2_pos_box_window _ hq₀
    rw [← Pdiag_Godd n hn h hpos.1 hpos.2, ← Pdiag_Godd_zero n hn hpos₀.1 hpos₀.2]
    have hb := norm_Pdiag_sub_le hL1 hq hq₀
    have hd := Work.Anchor.DClose.dist_q_le s (h s) (deriv h s) z (baseState s)
    calc ‖Pdiag n (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St) -
          Pdiag n (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St)‖
        ≤ (L1 : ℝ) * dist (((s, h s, deriv h s), z) : (ℝ × ℝ × ℝ) × St)
            (((s, 0, 0), baseState s) : (ℝ × ℝ × ℝ) × St) := hb
      _ ≤ (L1 : ℝ) * (|h s| + |deriv h s| + ‖z - baseState s‖) :=
          mul_le_mul_of_nonneg_left hd L1.coe_nonneg
      _ ≤ (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * ‖z - baseState s‖ +
          (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * δ := by
          have h1 : (L1 : ℝ) * |h s| ≤ (L1 : ℝ) * δ :=
            mul_le_mul_of_nonneg_left hhsδ L1.coe_nonneg
          have h2 : (L1 : ℝ) * |deriv h s| ≤ (L1 : ℝ) * δ :=
            mul_le_mul_of_nonneg_left hhpδ L1.coe_nonneg
          have h3 : (L1 : ℝ) * ‖z - baseState s‖ ≤
              (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * ‖z - baseState s‖ :=
            mul_le_mul_of_nonneg_right hCg'' (norm_nonneg _)
          have h4 : (L1 : ℝ) * δ + (L1 : ℝ) * δ ≤
              (max (L0 : ℝ) (2 * (L1 : ℝ)) + 1) * δ := by
            nlinarith [hCg', hδ.le]
          nlinarith [h1, h2, h3, h4]

end

end Work.OddVolterra.WinData
