/-
# Conjunct 2 of the Theorem-A arc certificate on the `NARC2 = 1024` grid (certificate v4)

This is the copy-edit of the proved 4096-grid lemma `Work.Cert.a_conj2_core`
(`Submission/Work/Cert/a_conj2_core.lean`) to the coarser grid of `RotConsts2` / `ArcCover2` /
`Conj2Cert2`:

* `Work.ArcCert.rearrInt_arc_bound` is generic in the grid size `N`, so it is used as is with
  `N := NARC2`;
* `Work.Cert.drift_le2` (`Submission/Work/Cert/drift_le2.lean`) is the 1024-grid drift
  `‖E k j − (Rk k/S)·rot (j/NARC2)‖ ≤ 65536/S` feeding `ArcCover2`;
* `Work.Cert.ACore.continuousOn_circleLog_phiAfam` (grid independent) gives the continuity of the
  three integrands;
* `rearrInt_sum_bound2_aux` below is the 1024-grid weighted arithmetic (the analogue of
  `Work.Cert.ACore.rearrInt_sum_bound`).

Assembly: `drift_le2` + `ArcCover2` locate, for every arc `[j/NARC2, (j+1)/NARC2]` of the circle
`|z| = Rk k/S`, a leaf `l` of the certificate's chain whose disc contains `(Rk k/S)·rot t`;
`LeafSound` then gives `log ‖φ_A(c_k·rot t)‖ ≤ G k j / S`, i.e. `circleLog (phiAfam k) t ≤ G k j / S`;
`rearrInt_arc_bound` turns that into the block sum, and the certificate's weighted max-sum
`ΣΣΣΣ wtS k·wtS k'·max (G k j) (G k' j') ≤ 112·DENS2²·S/10` gives the final `112/10`.
-/
import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.LeafAux
import Submission.Work.Cert.ACGeom.GeomAux
import Submission.Work.APsi.psiA_facts
import Submission.Work.Haupt.haupt_facts
import Submission.Work.ArcCert.rearrInt_arc_bound
import Submission.Work.Cert.ACore.drift_le
import Submission.Work.Cert.ACore.continuousOn_circleLog_phiAfam
import Submission.Work.Cert.drift_le2

open scoped BigOperators
open Submission.CDTPlan
namespace Work.Cert

/-! ## Elementary geometry of the circle points `(Rk k/S) · rot t`

Local copies of the helpers of `Submission/Work/Cert/a_conj2_core.lean`, placed in the nested
namespace `Work.Cert.A2Core` so that this file can be imported alongside the 4096-grid version
without name clashes. -/
namespace A2Core

/-- the exact point of circle `k` at parameter `t`: `(Rk k / S) · e^{2πit}`. -/
noncomputable def cPt (k : ℕ) (z : ℂ) : ℂ := (((Rk k : ℝ) / (S : ℝ) : ℝ) : ℂ) * z

lemma leafOK_geomOK (L : Leaf) (h : leafOK L = true) : geomOK L = true := by
  have h5 := (leafOK_spec L h).1
  have h1 := stage1_ok L (stage2_ok L (stage3_ok L (stage4_ok L h5)))
  have h0 := stage0_ok L h1
  simpa [stage0] using h0

lemma Rk0 : ((Rk 0 : ℤ) : ℝ) / (S : ℝ) = 1 / 10000 := by norm_num [Rk, S, fdiv]
lemma Rk1 : ((Rk 1 : ℤ) : ℝ) / (S : ℝ) = 283 / 500 := by norm_num [Rk, S, fdiv]
lemma Rk2 : ((Rk 2 : ℤ) : ℝ) / (S : ℝ) = 1 := by norm_num [Rk, S, fdiv]

lemma Rk_div_le_one (k : ℕ) (hk : k ≤ 2) : ((Rk k : ℤ) : ℝ) / (S : ℝ) ≤ 1 := by
  interval_cases k <;> norm_num [Rk, S, fdiv]

lemma Rk_div_pos (k : ℕ) (hk : k ≤ 2) : 0 < ((Rk k : ℤ) : ℝ) / (S : ℝ) := by
  interval_cases k <;> norm_num [Rk, S, fdiv]

lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h2 : ‖(r : ℂ)‖ = Real.sqrt (Complex.normSq (r : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma norm_rot (t : ℝ) : ‖rot t‖ = 1 := by
  rw [rot]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma rot_ne_zero (t : ℝ) : rot t ≠ 0 := by
  intro h0
  have h := congrArg norm h0
  rw [norm_rot, norm_zero] at h
  norm_num at h

lemma phiAfam_apply (k : Fin 3) (z : ℂ) :
    phiAfam k z = phiA (cPt (k : ℕ) z) := by
  have h0 : ((((Rk 0 : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) = (10000 : ℂ)⁻¹ := by
    rw [show (((Rk 0 : ℤ) : ℝ) / (S : ℝ) : ℝ) = 1 / 10000 by rw [Rk0]]
    norm_num
  have h1 : ((((Rk 1 : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) = (283 : ℂ) / 500 := by
    rw [show (((Rk 1 : ℤ) : ℝ) / (S : ℝ) : ℝ) = 283 / 500 by rw [Rk1]]
    norm_num
  have h2 : ((((Rk 2 : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) = 1 := by
    rw [show (((Rk 2 : ℤ) : ℝ) / (S : ℝ) : ℝ) = 1 by rw [Rk2]]
    norm_num
  fin_cases k
  · simp only [phiAfam, Fin.reduceFinMk, Matrix.cons_val_zero]
    rw [cPt, h0]
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  · simp only [phiAfam, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [cPt, h1]
    congr 1
    ring_nf
  · simp [phiAfam, h2, cPt]

lemma phiA_ne_zero {z : ℂ} (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) : phiA z ≠ 0 := by
  have hP : PsiAFacts := Work.APsi.psiA_facts
  have hM : HauptFacts := Work.Haupt.haupt_facts
  obtain ⟨-, -, -, hlt, hzero⟩ := hP
  obtain ⟨-, -, hne, -⟩ := hM
  intro h
  have hmem : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have h1 : ‖psiA z‖ < 1 := hlt z hmem
  have h2 : psiA z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using h1
  have h3 : psiA z = 0 := hne (psiA z) h2 (by simpa [phiA] using h)
  exact hz0 (hzero z hmem h3)

lemma norm_Rk_mul_rot (k : ℕ) (hk : k ≤ 2) (t : ℝ) :
    ‖((((Rk k : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) * rot t‖ ≤ 1 := by
  rw [norm_mul, norm_rot, mul_one, norm_ofReal_eq_abs, abs_of_pos (Rk_div_pos k hk)]
  exact Rk_div_le_one k hk

/-- the two ways of writing `(a/S)·z` (division in `ℂ` vs. division in `ℝ` then coercion) agree. -/
lemma cdiv_cast (a b : ℤ) (z : ℂ) :
    ((((a : ℤ) : ℝ) : ℂ) / (((b : ℤ) : ℝ) : ℂ)) * z
      = ((((a : ℤ) : ℝ) / ((b : ℤ) : ℝ) : ℝ) : ℂ) * z := by
  rw [← Complex.ofReal_div]

lemma Rk_mul_rot_ne_zero (k : ℕ) (hk : k ≤ 2) (t : ℝ) :
    ((((Rk k : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) * rot t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Rk_div_pos k hk))) (rot_ne_zero t)

end A2Core

open A2Core

/-! ## The weighted arithmetic on the 1024-grid

`rearrInt_sum_bound2_aux` is the 1024-grid copy of `Work.Cert.ACore.rearrInt_sum_bound`
(4096-grid): same reindexing and scaling, with `4096 -> 1024` and `DENS -> 7168000 = DENS2`. -/

private lemma fin_to_range4 {N M : ℕ} (W : ℕ → ℝ) (H : ℕ → ℕ → ℕ → ℕ → ℝ) (c : ℝ) :
    (∑ k : Fin N, ∑ k' : Fin N, ∑ j : Fin M, ∑ j' : Fin M,
        (W ↑k * W ↑k') * (c * H ↑k ↑k' ↑j ↑j'))
      = ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M, ∑ j' ∈ Finset.range M,
          (W k * W k') * (c * H k k' j j') := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ∑ k' : Fin N, ∑ j : Fin M, ∑ j' : Fin M, (W k * W ↑k') * (c * H k ↑k' ↑j ↑j'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Fin.sum_univ_eq_sum_range
    (fun k' => ∑ j : Fin M, ∑ j' : Fin M, (W k * W k') * (c * H k k' ↑j ↑j'))]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ j' : Fin M, (W k * W k') * (c * H k k' j ↑j'))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fin.sum_univ_eq_sum_range (fun j' => (W k * W k') * (c * H k k' j j'))]

/-- Pull a constant out of a fourfold `range` sum. -/
private lemma pull_const4 {N M : ℕ} (C : ℝ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M, ∑ j' ∈ Finset.range M,
        C * F k k' j j')
      = C * (∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M,
          ∑ j' ∈ Finset.range M, F k k' j j') := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]

/-- Convert a fourfold `Fin` sum with an inner division by `s` into a `range` sum,
pulling the constant `c / s` out. -/
private lemma four_sum_range_div {N M : ℕ} (W : ℕ → ℝ) (H : ℕ → ℕ → ℕ → ℕ → ℝ) (c s : ℝ) :
    (∑ k : Fin N, ∑ k' : Fin N, ∑ j : Fin M, ∑ j' : Fin M,
        (W ↑k * W ↑k') * (c * (H ↑k ↑k' ↑j ↑j' / s)))
      = (c / s) * (∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M,
          ∑ j' ∈ Finset.range M, W k * W k' * H k k' j j') := by
  have hA : (∑ k : Fin N, ∑ k' : Fin N, ∑ j : Fin M, ∑ j' : Fin M,
        (W ↑k * W ↑k') * (c * (H ↑k ↑k' ↑j ↑j' / s)))
      = (∑ k : Fin N, ∑ k' : Fin N, ∑ j : Fin M, ∑ j' : Fin M,
          (W ↑k * W ↑k') * ((c / s) * H ↑k ↑k' ↑j ↑j')) := by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))))
    ring
  rw [hA]
  rw [fin_to_range4 W H (c / s)]
  rw [show (∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M,
        ∑ j' ∈ Finset.range M, (W k * W k') * ((c / s) * H k k' j j'))
      = (∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ∑ j ∈ Finset.range M,
          ∑ j' ∈ Finset.range M, (c / s) * (W k * W k' * H k k' j j')) from by
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))))
    ring]
  rw [pull_const4 (c / s)]

open Submission.CDTPlan in
/-- **Weighted-sum arithmetic on the 1024-grid.**  The right-hand side produced by
`Work.ArcCert.rearrInt_arc_bound` at `N = 1024` with weights `(γ_{k+1}-γ_k)/14` and per-arc bounds
`(G k j)/S` is bounded by `112/10` using the conjunct-2 certificate's weighted sum
`ΣΣΣΣ wtS k * wtS k' * max (G k j) (G k' j') ≤ 112 * 7168000 ^ 2 * S / 10`.

Key arithmetic: `(γ_{k+1}-γ_k)/14 = wtS k * 1024 / 7168000` for `k = 0,1,2`
(`γ = (0, 71/125, 277/100, 14)`, `wtS = (284, 1101, 5615)`, `DENS2 = 7168000 = 500*14*1024`), and
`max (a/S) (b/S) = max a b / S` for `0 < S`. -/
theorem rearrInt_sum_bound2_aux (G : ℕ → ℕ → ℤ)
    (hsum : ∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024, ∑ j' ∈ Finset.range 1024,
        Work.Cert.wtS k * Work.Cert.wtS k' * max (G k j) (G k' j') ≤
          112 * 7168000 * 7168000 * Work.Cert.S / 10) :
    ∑ k : Fin 3, ∑ k' : Fin 3, ((gammaA k.succ - gammaA k.castSucc) / 14) *
        ((gammaA k'.succ - gammaA k'.castSucc) / 14) *
        ∑ j : Fin 1024, ∑ j' : Fin 1024, (1 / (1024 : ℝ) ^ 2) *
          max ((G (k : ℕ) (j : ℕ) : ℝ) / (Work.Cert.S : ℝ)) ((G (k' : ℕ) (j' : ℕ) : ℝ) / (Work.Cert.S : ℝ))
      ≤ 112 / 10 := by
  have hSpos : (0 : ℝ) < (Work.Cert.S : ℝ) := by norm_num [Work.Cert.S]
  -- the weight identity `(γ_{k+1} − γ_k)/14 = wtS k * 1024 / DENS`
  have hwt : ∀ k : Fin 3, (gammaA k.succ - gammaA k.castSucc) / 14
      = (Work.Cert.wtS (k : ℕ) : ℝ) * 1024 / (7168000 : ℝ) := by
    intro k
    fin_cases k <;> norm_num [gammaA, Work.Cert.wtS,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
  -- scaling the two entries of a `max` by `1/S`
  have hmax : ∀ a b : ℤ, max ((a : ℝ) / (Work.Cert.S : ℝ)) ((b : ℝ) / (Work.Cert.S : ℝ))
      = ((max a b : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    intro a b; rw [max_div_div_right hSpos.le a b, Int.cast_max]
  set Sr : ℝ := ∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
      ∑ j' ∈ Finset.range 1024,
        (Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) * ((max (G k j) (G k' j') : ℤ) : ℝ)
    with hSrdef
  have key : (∑ k : Fin 3, ∑ k' : Fin 3, ((gammaA k.succ - gammaA k.castSucc) / 14) *
        ((gammaA k'.succ - gammaA k'.castSucc) / 14) *
        ∑ j : Fin 1024, ∑ j' : Fin 1024, (1 / (1024 : ℝ) ^ 2) *
          max ((G (k : ℕ) (j : ℕ) : ℝ) / (Work.Cert.S : ℝ))
            ((G (k' : ℕ) (j' : ℕ) : ℝ) / (Work.Cert.S : ℝ)))
      = (1 / ((7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ))) * Sr := by
    rw [hSrdef]
    conv_lhs => simp only [hwt, hmax, Finset.mul_sum]
    rw [four_sum_range_div (fun n => (Work.Cert.wtS n : ℝ) * 1024 / (7168000 : ℝ))
          (fun k k' j j' => ((max (G k j) (G k' j') : ℤ) : ℝ)) (1 / (1024 : ℝ) ^ 2)
          (Work.Cert.S : ℝ)]
    have hstep : (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
          ∑ j' ∈ Finset.range 1024,
          ((Work.Cert.wtS k : ℝ) * 1024 / (7168000 : ℝ)) *
            ((Work.Cert.wtS k' : ℝ) * 1024 / (7168000 : ℝ)) *
            ((max (G k j) (G k' j') : ℤ) : ℝ))
        = ((1024 : ℝ) / (7168000 : ℝ)) ^ 2 *
          (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            (Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) *
              ((max (G k j) (G k' j') : ℤ) : ℝ)) := by
      rw [show (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            ((Work.Cert.wtS k : ℝ) * 1024 / (7168000 : ℝ)) *
              ((Work.Cert.wtS k' : ℝ) * 1024 / (7168000 : ℝ)) *
              ((max (G k j) (G k' j') : ℤ) : ℝ))
          = (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            ((1024 : ℝ) / (7168000 : ℝ)) ^ 2 *
              ((Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) *
                ((max (G k j) (G k' j') : ℤ) : ℝ))) from by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ =>
          Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))))
        ring]
      rw [pull_const4 (((1024 : ℝ) / (7168000 : ℝ)) ^ 2)]
    rw [hstep]
    rw [show (1 / (1024 : ℝ) ^ 2) / (Work.Cert.S : ℝ) *
          (((1024 : ℝ) / (7168000 : ℝ)) ^ 2 *
          (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            (Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) *
              ((max (G k j) (G k' j') : ℤ) : ℝ)))
        = ((1 / (1024 : ℝ) ^ 2) / (Work.Cert.S : ℝ) * ((1024 : ℝ) / (7168000 : ℝ)) ^ 2) *
          (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            (Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) *
              ((max (G k j) (G k' j') : ℤ) : ℝ)) from by ring]
    rw [show (1 / (1024 : ℝ) ^ 2) / (Work.Cert.S : ℝ) * ((1024 : ℝ) / (7168000 : ℝ)) ^ 2
        = 1 / ((7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ)) from by field_simp]
  rw [key]
  have hSr : Sr ≤ 112 * (7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ) / 10 := by
    rw [hSrdef]
    have hcast : (∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
          ∑ j' ∈ Finset.range 1024,
          (Work.Cert.wtS k : ℝ) * (Work.Cert.wtS k' : ℝ) * ((max (G k j) (G k' j') : ℤ) : ℝ))
        = ((∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            Work.Cert.wtS k * Work.Cert.wtS k' * max (G k j) (G k' j') : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [hcast]
    calc ((∑ k ∈ Finset.range 3, ∑ k' ∈ Finset.range 3, ∑ j ∈ Finset.range 1024,
            ∑ j' ∈ Finset.range 1024,
            Work.Cert.wtS k * Work.Cert.wtS k' * max (G k j) (G k' j') : ℤ) : ℝ)
        ≤ ((112 * 7168000 * 7168000 * Work.Cert.S / 10 : ℤ) : ℝ) := by
          exact_mod_cast hsum
      _ = 112 * (7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ) / 10 := by
          norm_num [Work.Cert.S]
  calc (1 / ((7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ))) * Sr
      ≤ (1 / ((7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ))) *
          (112 * (7168000 : ℝ) ^ 2 * (Work.Cert.S : ℝ) / 10) :=
        mul_le_mul_of_nonneg_left hSr (le_of_lt (by positivity))
    _ = 112 / 10 := by field_simp

open Submission.CDTPlan in
theorem a_conj2_core2 (hL : LeafSound) (hC : ArcCover2) (hR : RotConsts2) (hF : Conj2Cert2) :
    rearrInt (fun k => (gammaA k.succ - gammaA k.castSucc) / 14) phiAfam ≤ 112 / 10 := by
  obtain ⟨G, E, LS, hbase, harc, hsum⟩ := hF
  have hdrift : ∀ k j, k ≤ 2 → j ≤ NARC2 →
      ‖cx (E k j).1 (E k j).2 - ((((Rk k : ℤ) : ℝ) / (S : ℝ) : ℝ) : ℂ) * rot ((j : ℝ) / NARC2)‖
        ≤ 65536 / (S : ℝ) := by
    intro k j hk hj
    have h := drift_le2 hR k hk (E k) (hbase k hk).1 (fun i hi => (harc k i hk hi).2.2.1) j hj
    rwa [cdiv_cast (Rk k) S (rot ((j : ℝ) / NARC2))] at h
  have key : ∀ (k : Fin 3) (j : Fin NARC2) (t : ℝ),
      t ∈ Set.Icc ((j : ℝ) / NARC2) (((j : ℝ) + 1) / NARC2) →
      circleLog (phiAfam k) t ≤ (G (k : ℕ) (j : ℕ) : ℝ) / (S : ℝ) := by
    intro k j t ht
    have hk2 : (k : ℕ) ≤ 2 := by omega
    have hj4 : (j : ℕ) < NARC2 := j.isLt
    obtain ⟨hfirst, hchain, _, hall⟩ := harc (k : ℕ) (j : ℕ) hk2 hj4
    have hmem' : ∀ l ∈ LS (k : ℕ) (j : ℕ),
        decide (l.k = (k : ℕ)) = true ∧ decide (l.G ≤ G (k : ℕ) (j : ℕ)) = true ∧
          leafOK l = true := by
      intro l hl
      have h := (List.all_eq_true.mp hall) l hl
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hgeom_all : (LS (k : ℕ) (j : ℕ)).all (fun l => decide (l.k = (k : ℕ)) && geomOK l) = true := by
      rw [List.all_eq_true]
      intro l hl
      obtain ⟨h1, -, h3⟩ := hmem' l hl
      simp only [Bool.and_eq_true]
      exact ⟨h1, leafOK_geomOK l h3⟩
    obtain ⟨l, hlmem, hdist⟩ := hC (k : ℕ) (j : ℕ) (E (k : ℕ) (j : ℕ)).1 (E (k : ℕ) (j : ℕ)).2
      (E (k : ℕ) ((j : ℕ) + 1)).1 (E (k : ℕ) ((j : ℕ) + 1)).2 (LS (k : ℕ) (j : ℕ)) hk2 hj4
      (hdrift (k : ℕ) (j : ℕ) hk2 (by omega))
      (by have h := hdrift (k : ℕ) ((j : ℕ) + 1) hk2 (by omega)
          simpa [Nat.cast_add, Nat.cast_one] using h)
      hfirst hchain hgeom_all t ht
    obtain ⟨hlk, hlG, hlok⟩ := hmem' l hlmem
    have hexp : ‖phiA (cPt (k : ℕ) (rot t))‖
        ≤ Real.exp ((G (k : ℕ) (j : ℕ) : ℝ) / (S : ℝ)) := by
      have h := hL l hlok _ hdist
      refine le_trans h (Real.exp_le_exp.mpr ?_)
      apply div_le_div_of_nonneg_right _ (le_of_lt S_posR)
      exact_mod_cast (of_decide_eq_true hlG)
    have hne : phiA (cPt (k : ℕ) (rot t)) ≠ 0 :=
      phiA_ne_zero (norm_Rk_mul_rot (k : ℕ) hk2 t) (Rk_mul_rot_ne_zero (k : ℕ) hk2 t)
    have hlog : circleLog (phiAfam k) t
        = Real.log ‖phiA (cPt (k : ℕ) (rot t))‖ := by
      rw [circleLog, phiAfam_apply, rot]
    rw [hlog]
    calc Real.log ‖phiA (cPt (k : ℕ) (rot t))‖
        ≤ Real.log (Real.exp ((G (k : ℕ) (j : ℕ) : ℝ) / (S : ℝ))) :=
          Real.log_le_log (norm_pos_iff.mpr hne) hexp
      _ = (G (k : ℕ) (j : ℕ) : ℝ) / (S : ℝ) := Real.log_exp _
  have hw : ∀ k : Fin 3, 0 ≤ (gammaA k.succ - gammaA k.castSucc) / 14 := by
    intro k
    fin_cases k <;>
      norm_num [gammaA, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
  have hN : 0 < NARC2 := by norm_num [NARC2]
  have hbridge := Work.ArcCert.rearrInt_arc_bound (l := 2) (N := NARC2) hN
    (fun k : Fin 3 => (gammaA k.succ - gammaA k.castSucc) / 14) hw phiAfam
    (fun (k : Fin 3) (j : Fin NARC2) => (G (k : ℕ) (j : ℕ) : ℝ) / (S : ℝ))
    (fun k => Work.Cert.ACore.continuousOn_circleLog_phiAfam k) key
  refine le_trans hbridge ?_
  exact rearrInt_sum_bound2_aux G (by simpa only [Work.Cert.NARC2, Work.Cert.DENS2] using hsum)

end Work.Cert
