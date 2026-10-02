/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Item E-E: the Taylor model of the petal

The hypothesis of `petal_P1`/`petal_P2`: `F (z₁+u) = z₁ + u + A u² + E u` with
`‖E u‖ ≤ M‖u‖³` for `‖u‖ ≤ ρ₂`, supplied with *explicit* constants at the certified point.

The bound is the third-order Taylor remainder in integral form,
`‖E u‖ ≤ sup_{‖w‖≤ρ₂} ‖F'''(z₁+w)‖ · ‖u‖³ / 6`,
so it suffices to enclose `F'''` over the box `Xz2 = Xz ⊕ [−ρ₂,ρ₂]²`, which is done by the rounded
3-jet `jet3IterR 400` of `Submission/Work/SeedCertNum/Jet3.lean` and one `decide`-checked
comparison.

The numerical constants (`ρ₂ = 2^-11`, `ρ₁ = 2^-12`, `K = Kee = 5056372`, `M = K/6`, `R = 7`,
`δ = 1/4`) and the petal conditions `(C1)`, `(C2)` live in
`Submission/Work/SeedCertNum/EEConst.lean` (`ee_petal_constants`).

## Main results

* `ee_d3_check` — `decide`-checked `(d3box.normSq).hi ≤ K²`;
* `Xz2_mem` — `z₁ + u ∈ Xz2` for `‖u‖ ≤ ρ₂`;
* `ee_third_bound` — `‖F'''(z₁+w)‖ ≤ K` for `‖w‖ ≤ ρ₂`;
* `ee_taylor` — `‖F(z₁+u) − z₁ − u − A u²‖ ≤ M‖u‖³` for `‖u‖ ≤ ρ₂`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Export
import Submission.Work.SeedCertNum.EEConst
import Submission.Work.SeedCertNum.Jet3
import Submission.Work.SeedCertNum.mem_jet3R
import Submission.Work.SeedCertNum.norm_sq_le_jet3box
import Submission.Work.SeedCertNum.norm_taylor2_remainder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxRecDepth 8000

/-- The box `Xz ⊕ [−ρ₂,ρ₂]²`, containing `z₁ + u` for every `‖u‖ ≤ ρ₂`. -/
def Xz2 : CBox :=
  ⟨Dya.sub krawData.Xz.rlo rho2, Dya.add krawData.Xz.rhi rho2,
   Dya.sub krawData.Xz.ilo rho2, Dya.add krawData.Xz.ihi rho2⟩

/-- The enclosure of `F'''` over `Xz2`. -/
def d3box : CBox := (jet3IterR 400 (pbox krawData.x₀ krawData.Xt) Xz2 5).d3

theorem ee_d3_check : Dya.le (d3box.normSq).hi (Dya.mul Kee Kee) = true := by decide

theorem Xz2_mem {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) : z1 + w ∈ Xz2.toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_mem
  have hrho : 0 ≤ rho2.toReal := by rw [rho2R]; positivity
  have hwr : |w.re| ≤ rho2.toReal := le_trans (Complex.abs_re_le_norm w) hw
  have hwi : |w.im| ≤ rho2.toReal := le_trans (Complex.abs_im_le_norm w) hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Xz2, CBox.toSet, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
      Dya.toReal_sub, Dya.toReal_add]
  · linarith [abs_le.mp hwr]
  · linarith [abs_le.mp hwr]
  · linarith [abs_le.mp hwi]
  · linarith [abs_le.mp hwi]

theorem ee_third_bound {w : ℂ} (hw : ‖w‖ ≤ rho2.toReal) :
    ‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖ ≤ Kee.toReal := by
  have h := Work.SeedCertNum.norm_sq_le_jet3box (x₀ := krawData.x₀) (Xt := krawData.Xt)
    (Xz2 := Xz2) (ρ := rho2.toReal) (z := z1) (t := krawU.2.2)
    (fun u hu => Xz2_mem hu) krawU_t_mem w hw
  have hd3 : iteratedDeriv 3 ((Work.Landing.Tsq ((krawData.x₀.toReal : ℂ)
      + ↑krawU.2.2 * Complex.I))^[5]) (z1 + w) =
      iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w) := rfl
  rw [hd3] at h
  have hK : (d3box.normSq).hi.toReal ≤ (Kee.toReal) ^ 2 := by
    have := (Dya.toReal_le_iff _ _).mp ee_d3_check
    simpa [d3box, Kee, Dya.toReal_mul, pow_two] using this
  have h2 : ‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖ ^ 2 ≤ Kee.toReal ^ 2 :=
    le_trans h hK
  have h3 : |‖iteratedDeriv 3 (Work.FSeed.F cb) (z1 + w)‖| ≤ |Kee.toReal| := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by rw [Kee_toReal]; norm_num)] at h3

theorem Tsq_diff : Differentiable ℂ (Work.Landing.Tsq cb) := by
  unfold Work.Landing.Tsq
  fun_prop

theorem F_diff : ∀ w : ℂ, DifferentiableAt ℂ (Work.FSeed.F cb) w := by
  intro w
  rw [Work.FSeed.F_apply]
  exact (Tsq_diff.iterate 5).differentiableAt

theorem F_fix : Work.FSeed.F cb z1 = z1 := by
  have h := Work.FSeed.Tantibar_iterate_ten cb z1
  rw [← h, show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, g_fix, g_fix]

theorem F_deriv : deriv (Work.FSeed.F cb) z1 = 1 := by
  rw [Work.FSeed.F_apply]
  exact mult_one

theorem F_deriv2 : iteratedDeriv 2 (Work.FSeed.F cb) z1 = 2 * Aquad := iteratedDeriv2_eq

/-- **The Taylor model**: `‖F(z₁+u) − z₁ − u − A u²‖ ≤ M‖u‖³` for `‖u‖ ≤ ρ₂`, with `M = K/6`. -/
theorem ee_taylor {u : ℂ} (hu : ‖u‖ ≤ rho2.toReal) :
    ‖Work.FSeed.F cb (z1 + u) - z1 - u - Aquad * u ^ 2‖ ≤ Mee * ‖u‖ ^ 3 := by
  have h := Work.SeedCertNum.norm_taylor2_remainder (F := Work.FSeed.F cb) (z₀ := z1)
    (A := Aquad) (K := Kee.toReal) (ρ := rho2.toReal) F_diff (Kee_toReal ▸ by norm_num)
    (by rw [rho2R]; positivity) (fun w hw => ee_third_bound hw) F_fix F_deriv F_deriv2 hu
  simpa only [Mee, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end

end Work.SeedCert
