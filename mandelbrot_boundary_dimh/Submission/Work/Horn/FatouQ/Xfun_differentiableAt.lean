import Mathlib
import Submission.Work.Horn.fatouQ_defs
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.zBranch_contDiff

namespace Work.Horn.FatouQ

open Work.Horn.Flower

/-!
# Holomorphy of the approximate Fatou coordinate `Xfun` in the chart

The approximate Abel coordinate `Acorr f q a` is an explicit elementary function of `z`
(`cc / z^q`, a finite sum of powers of `z⁻¹`, and a multiple of the branch `Lbranch q a` of the
logarithm), hence holomorphic away from `z = 0` as soon as the argument of the logarithm
`z^q / cc q a` lies in the slit plane.  Since `Xfun f q a j = Acorr f q a ∘ zBranch q a j` and
`zBranch q a j w` is non-zero with `(zBranch q a j w)^q / cc q a` in the slit plane whenever
`M < w.re` (the inverse chart lies on the `j`-th petal, where the root disc `DM q a M` sits inside
`cc • slitPlane`), the chain rule gives holomorphy of `Xfun` on the half plane `{Re w > M}`.
-/

/-- The approximate Fatou coordinate `Acorr f q a` is holomorphic at `z` when `z ≠ 0` and the
argument of the branch logarithm `z^q / cc q a` lies in the slit plane. -/
theorem Acorr_differentiableAt {f : ℂ → ℂ} {q : ℕ} {a : ℂ} {z : ℂ}
    (hz : z ≠ 0) (hlog : z ^ q / cc q a ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (Acorr f q a) z := by
  unfold Acorr
  have h1 : DifferentiableAt ℂ (fun z : ℂ => cc q a / z ^ q) z :=
    (differentiableAt_const _).div (differentiableAt_id.pow q) (pow_ne_zero q hz)
  have h2 : DifferentiableAt ℂ (fun z : ℂ =>
      ∑ i ∈ Finset.Icc 1 (q - 1),
        gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i)) z := by
    rw [show (fun z : ℂ => ∑ i ∈ Finset.Icc 1 (q - 1),
          gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i))
        = ∑ i ∈ Finset.Icc 1 (q - 1),
          fun z : ℂ => gcoef f q a i / ((i : ℂ) - (q : ℂ)) * (z⁻¹) ^ (q - i) from by
      funext z; rw [Finset.sum_apply]]
    apply DifferentiableAt.sum
    intro i _
    exact (differentiableAt_const _).mul ((differentiableAt_inv hz).pow (q - i))
  have h3 : DifferentiableAt ℂ (fun z : ℂ =>
      (gcoef f q a q + ((q : ℂ) + 1) / 2) * Lbranch q a z) z := by
    apply DifferentiableAt.const_mul
    show DifferentiableAt ℂ
      (fun w : ℂ => (Complex.log (w ^ q / cc q a) + Complex.log (cc q a)) / (q : ℂ)) z
    exact ((((differentiableAt_id.pow q).div_const (cc q a)).clog hlog).add_const
      (Complex.log (cc q a))).div_const ((q : ℂ))
  exact (h1.add h2).add h3

theorem Xfun_differentiableAt {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M) (j : Fin q)
    (hpetal : ∀ w : ℂ, M < w.re → Work.Horn.FatouQ.zBranch q a j w ∈ Work.Horn.Flower.petal q a M j) :
    ∀ w : ℂ, M < w.re → DifferentiableAt ℂ (Work.Horn.FatouQ.Xfun f q a j) w := by
  intro w hw
  have hq : 1 ≤ q := hd.hS.hq
  have ha : a ≠ 0 := hd.hS.ha
  have hM : 0 < M := hd.hM
  have hwpos : 0 < w.re := lt_trans hM hw
  have hzmem : zBranch q a j w ∈ petal q a M j := hpetal w hw
  obtain ⟨hzpos, hzqDM, _⟩ := (hd.hgeo.mem_petal_iff j _).mp hzmem
  have hz0 : zBranch q a j w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hslit : (zBranch q a j w) ^ q / cc q a ∈ Complex.slitPlane :=
    Work.Horn.PetalFactsAux.DM_slit hM hzqDM
  have hAdiff : DifferentiableAt ℂ (Acorr f q a) (zBranch q a j w) :=
    Acorr_differentiableAt hz0 hslit
  have hzdiff : DifferentiableAt ℂ (zBranch q a j) w :=
    (zBranch_contDiff hq ha j w hwpos).1
  unfold Xfun
  exact hAdiff.comp w hzdiff

end Work.Horn.FatouQ
