/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Item A1: the certified parabolic point `(z₁, c_b)` of the α-root arc

Assembly of the Krawczyk certificate `krawData` (`Submission/Work/SeedCertNum/A1Data.lean`) into
the existence and uniqueness of the zero of `Φ`, and the three facts the seed needs:

* `g_fix` — `(T_{c_b})^[5] z₁ = z₁`;
* `mult_one` — `multiplier2 c_b 5 z₁ = 1` (so `z₁` is *parabolic*, of multiplier exactly `1`, with
  the `2‖·‖` normalisation of `Work.Landing.multiplier2`);
* `exact_period` — the exact period is `5`, from the four disjointness checks of
  `Submission/Work/SeedCertNum/A2Sep.lean`.

The boxes are `KrawData.Xz krawData` (for `z₁`) and `KrawData.Xt krawData` (for `Im c_b`), of
radius `2^-30` about the centre `(-1.1760066832884205819, 0.1777445809573267193, 0.178196511188…)`
at grid `2^-60`, with `Re c_b = -1293728561597/2^40` exactly.

## Main results

* `kraw_sound` — `ok = true` gives `∃! u ∈ closedBall u₀ r, Φ u = 0`;
* `krawData_sound`, `krawU`, `z1`, `cb`, `g_fix`, `mult_one`, `exact_period`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A2Sep
import Submission.Work.SeedCertNum.kraw_ok_numeric
import Submission.Work.SeedCertNum.mem_closedBall_iff
import Submission.Work.SeedCertNum.krawczyk_numeric
import Submission.Work.SeedCertNum.multiplier2_eq_Pi
import Submission.Work.SeedCertNum.hasFDerivAt_Phi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- `Z x₀ n u` is the `n`-th iterate of `T_{c(u)}` applied to `z(u)`. -/
theorem Z_eq_iterate (x₀ : ℝ) (n : ℕ) (u : E3) :
    Z x₀ n u = (Tantibar (cOf x₀ u))^[n] (zOf u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Z_succ, ih, Function.iterate_succ_apply']
    rfl

/-- `mkE` is a section of the pair `(zOf, fun u => u.2.2)`. -/
@[simp] theorem mkE_zOf (u : E3) : mkE (zOf u) u.2.2 = u := by
  obtain ⟨a, b, c⟩ := u
  simp [mkE, zOf]

/-! ## The soundness of the certificate -/

/-- **The Krawczyk certificate is sound**: `ok = true` yields a unique zero of `Φ` in the box. -/
theorem kraw_sound (D : KrawData) (h : D.ok = true) :
    ∃! u ∈ Metric.closedBall D.u₀ D.rad, Phi D.x₀.toReal u = 0 := by
  obtain ⟨hr, hε0, hη0, hα0, hβ0, hJac, hA, hB, hEta, hball⟩ := Work.SeedCertNum.kraw_ok_numeric D h
  exact Work.SeedCertNum.krawczyk_numeric hr hε0 hη0 hα0 hβ0
    (fun u _ => (Work.SeedCertNum.hasFDerivAt_Phi D.x₀.toReal u).differentiableAt)
    hJac hA hB hEta hball

/-- The soundness of the emitted certificate. -/
theorem krawData_sound :
    ∃! u ∈ Metric.closedBall krawData.u₀ krawData.rad, Phi krawData.x₀.toReal u = 0 :=
  kraw_sound krawData krawData_ok

/-! ## The certified point -/

theorem krawData_exists :
    ∃ u, u ∈ Metric.closedBall krawData.u₀ krawData.rad ∧
      Phi krawData.x₀.toReal u = 0 :=
  krawData_sound.exists

/-- The unique zero of `Φ` in the certified box. -/
def krawU : E3 := Classical.choose krawData_exists

theorem krawU_spec : krawU ∈ Metric.closedBall krawData.u₀ krawData.rad ∧
    Phi krawData.x₀.toReal krawU = 0 := Classical.choose_spec krawData_exists

theorem krawU_mem : krawU ∈ Metric.closedBall krawData.u₀ krawData.rad := krawU_spec.1

theorem krawU_Phi : Phi krawData.x₀.toReal krawU = 0 := krawU_spec.2

/-- The certified parabolic point `z₁`. -/
def z1 : ℂ := zOf krawU

/-- The certified parameter `c_b` (with `Re c_b = -1293728561597/2^40`). -/
def cb : ℂ := cOf krawData.x₀.toReal krawU

theorem Theta_eq_zero : Theta krawData.x₀.toReal krawU = 0 := by
  refine Complex.ext ?_ ?_
  · have := congrArg Prod.fst krawU_Phi
    simpa [Phi] using this
  · have := congrArg (fun v : E3 => v.2.1) krawU_Phi
    simpa [Phi] using this

theorem Pi_eq_one : Pi krawData.x₀.toReal krawU = 1 := by
  have h := congrArg (fun v : E3 => v.2.2) krawU_Phi
  have h2 : (Pi krawData.x₀.toReal krawU - 1 : ℝ) = 0 := by
    have hh := h
    simp only [Phi] at hh
    exact hh
  linarith

theorem Z_five : Z krawData.x₀.toReal 5 krawU = zOf krawU := by
  have h := Theta_eq_zero
  simp only [Theta, Pi] at h
  exact sub_eq_zero.mp h

/-- **A1, `g`-fixedness**: `z₁` is a fixed point of the fifth iterate. -/
theorem g_fix : (Tantibar cb)^[5] z1 = z1 := by
  have h := Z_five
  rw [Z_eq_iterate] at h
  simpa [z1, cb] using h

/-- **A1, multiplier one**: `z₁` is parabolic. -/
theorem mult_one : Work.Landing.multiplier2 cb 5 z1 = 1 := by
  have h := Work.SeedCertNum.multiplier2_eq_Pi (x₀ := krawData.x₀.toReal) (u := krawU) g_fix
  have hcb : cb = cOf krawData.x₀.toReal krawU := rfl
  have hz : z1 = zOf krawU := rfl
  rw [hcb, hz, h, Pi_eq_one]
  norm_num

/-! ## The exact period -/

theorem krawU_closedBall :
    (mkE (zOf krawU) krawU.2.2 : E3) ∈ Metric.closedBall krawData.u₀ krawData.rad := by
  simpa only [mkE_zOf] using krawU_mem

theorem krawU_z_mem : zOf krawU ∈ krawData.Xz.toSet :=
  ((Work.SeedCertNum.mem_closedBall_iff krawData (z := zOf krawU) (t := krawU.2.2)).mp
    krawU_closedBall).1

theorem krawU_t_mem : krawU.2.2 ∈ krawData.Xt.toSet :=
  ((Work.SeedCertNum.mem_closedBall_iff krawData (z := zOf krawU) (t := krawU.2.2)).mp
    krawU_closedBall).2

theorem Z_j_mem (j : ℕ) :
    Z krawData.x₀.toReal j krawU ∈
      (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz j).toSet := by
  have h := mem_boxV krawData.x₀ krawData.Xt krawData.Xz j krawU_z_mem krawU_t_mem
  rwa [mkE_zOf] at h

theorem Z_zero_mem : Z krawData.x₀.toReal 0 krawU ∈ krawData.Xz.toSet := by
  simpa [boxV, Z] using krawU_z_mem

theorem Z_j_ne (j : ℕ) (hj : 0 < j) (hj5 : j < 5) :
    Z krawData.x₀.toReal j krawU ≠ zOf krawU := by
  have hj' : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  have hdisj : Disjoint (boxV (pbox krawData.x₀ krawData.Xt) krawData.Xz j).toSet
      krawData.Xz.toSet := by
    rcases hj' with rfl | rfl | rfl | rfl
    · exact disjoint_of_sep krawData_sep1
    · exact disjoint_of_sep krawData_sep2
    · exact disjoint_of_sep krawData_sep3
    · exact disjoint_of_sep krawData_sep4
  intro hcontra
  exact Set.disjoint_left.mp hdisj (Z_j_mem j) (by rw [hcontra]; exact Z_zero_mem)

/-- **A1, exact period**: the period of `z₁` under `T_{c_b}` is exactly `5`. -/
theorem exact_period : ∀ j : ℕ, 0 < j → j < 5 → (Tantibar cb)^[j] z1 ≠ z1 := by
  intro j hj hj5 hcontra
  have h := Z_j_ne j hj hj5
  apply h
  rw [Z_eq_iterate]
  simpa [z1, cb] using hcontra

end

end Work.SeedCert
