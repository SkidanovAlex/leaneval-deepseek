import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.FTfibre.holderNorm_comp_right_le_of_contDiff
import Submission.Work.NN.Newton.FTs2.holderNorm_sharpCut_univ_le
import Submission.Work.NN.Newton.FTs2.delta_geom_bound

/-!
# The `C^{1,α}` norm of the parametric cutoff `kappa (ftG δ) s`

The parametric cutoff in the `s`-th coordinate is
`kappa G s z = sharpCut (G.a s) (G.b s) (z s)`, the planar cutoff
`sharpCut a b ζ = σ((b² - ‖ζ‖²)/(b² - a²))` (`σ = Real.smoothTransition`) composed with the
coordinate projection `z ↦ z s`.

The content of this file is that on the tracking polydisc `Eset (ftG δ) s` of the thin-gap
telescope (`a = 1 - 15δ/16`, `b = 1 - 7δ/8`) the `C^{1,α}`-norm of `kappa (ftG δ) s` is bounded
by `M / δ ^ 6` with a constant `M` **independent of `δ`**.

The proof has three steps:

* the planar `C^{1,α}` bound `Work.NN.Newton.FTs2.holderNorm_sharpCut_univ_le`: for
  `1/2 ≤ a < b ≤ 1` the `C^{1,α}`-norm of `sharpCut a b` on all of `ℂ` is
  `≤ ofReal (D (b - a)⁻²)`, with `D` independent of `a` and `b`;
* the transfer to the slice `Work.NN.Newton.FTfibre.holderNorm_comp_right_le_of_contDiff`: right
  composition with the coordinate projection, which is a contraction, loses no constant;
* the geometry `Work.NN.Newton.FTs2.delta_geom_bound`: for the telescope `b - a = δ/16`, so
  `(b - a)⁻² = 256/δ² ≤ 256/δ^6` for `δ ≤ 1/4`.
-/

namespace Work.NN.Newton.FTs2

open scoped ENNReal

/-- The parametric cutoff `kappa G s` is the planar cutoff `sharpCut (G.a s) (G.b s)` composed
with the coordinate projection `z ↦ z s`; since that projection is a contraction, the
`C^{1,α}`-norm of `kappa G s` on the tracking polydisc `Eset G s` is bounded by the
`C^{1,α}`-norm of the planar cutoff on all of `ℂ`. -/
theorem holderNorm_kappa_le {n : ℕ} (G : Work.NN.Core.TelTwoDF.Geom n) (s : Fin n) {α : ℝ}
    (hα : 0 ≤ α) :
    Work.CR.Flat.holderNorm 1 α (Work.NN.Core.TelTwoDF.kappa G s)
        (Work.NN.Core.TelTwoDF.Eset G s)
      ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Core.sharpCut (G.a s) (G.b s)) Set.univ := by
  let Φ : (Fin n → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) s
  have hΦapp : ∀ z : Fin n → ℂ, Φ z = z s := fun z => ContinuousLinearMap.proj_apply s z
  have hΦnorm : ‖Φ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound Φ zero_le_one (fun z => ?_)
    rw [one_mul, hΦapp z]
    exact norm_le_pi_norm z s
  have hΩ : ∀ x ∈ Work.NN.Core.TelTwoDF.Eset G s,
      Work.NN.Core.TelTwoDF.Eset G s ∈ nhds x :=
    fun x hx => (Work.NN.Core.TelTwoDF.isOpen_Eset G s).mem_nhds hx
  have ht : ∀ x ∈ Work.NN.Core.TelTwoDF.Eset G s, (Set.univ : Set ℂ) ∈ nhds (Φ x) :=
    fun _ _ => Filter.univ_mem
  have hmain := Work.NN.Newton.FTfibre.holderNorm_comp_right_le_of_contDiff Φ 1 hα
    ((Work.NN.Core.contDiff_sharpCut (a := G.a s) (b := G.b s)).of_le (by simp)) hΩ ht
  have hmax : ENNReal.ofReal (max 1 (‖Φ‖ ^ (((1 : ℕ) : ℝ) + α))) = 1 := by
    rw [max_eq_left, ENNReal.ofReal_one]
    exact Real.rpow_le_one (norm_nonneg Φ) hΦnorm (by positivity)
  rw [hmax, one_mul] at hmain
  rw [show (fun z : Fin n → ℂ => Work.NN.Core.sharpCut (G.a s) (G.b s) (Φ z))
      = (fun z => Work.NN.Core.sharpCut (G.a s) (G.b s) (z s)) from
        funext (fun z => by rw [hΦapp z])] at hmain
  change Work.CR.Flat.holderNorm 1 α
      (fun z : Fin n → ℂ => Work.NN.Core.sharpCut (G.a s) (G.b s) (z s))
      (Work.NN.Core.TelTwoDF.Eset G s)
    ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Core.sharpCut (G.a s) (G.b s)) Set.univ
  exact hmain

-- GOAL: the `C^{1,α}` norm of the parametric cutoff `kappa (ftG δ) s` on the tracking polydisc
-- `Eset (ftG δ) s` is `≤ M/δ^6` with `M` INDEPENDENT OF `δ` (this is the whole point: the true
-- size is `O(δ^{-2})`; the exponent 6 is deliberately generous, so any bound `≲ δ^{-k}`, `k ≤ 6`,
-- in the form `≤ M'/λ^2` with `λ = b^2 - a^2 ≥ δ/16` suffices).
--
-- ROUTE (implemented).  `kappa (ftG δ) s z = sharpCut a b (z s)` with `a = 1 - 15δ/16`,
-- `b = 1 - 7δ/8`, so it is the planar cutoff composed with the coordinate projection
-- `Φ z = z s`, a contraction.
--   * `Work.NN.Newton.FTsharp.sharpCut_fderiv_bounds` gives δ-independent constants `C` for
--     `‖∇ sharpCut a b‖ ≤ C/(b-a)` and `‖∇ sharpCut a b x - ∇ sharpCut a b y‖ ≤
--     C(1/(a(b-a)) + 1/(b-a)²)‖x-y‖`; feeding these to
--     `Work.NN.Core.Lev.holderNorm_one_le_of_deriv_bounds` (which contains the two-case
--     comparison of `‖x-y‖` with `‖x-y‖^α`) gives
--     `Work.NN.Newton.FTs2.holderNorm_sharpCut_univ_le`:
--     `holderNorm 1 α (sharpCut a b) univ ≤ ofReal (D (b-a)⁻²)` for `1/2 ≤ a < b ≤ 1`.
--   * `Work.NN.Newton.FTfibre.holderNorm_comp_right_le_of_contDiff` moves this from `ℂ` to the
--     slice on `Eset (ftG δ) s` (here `holderNorm_kappa_le` below), losing no constant because
--     the projection is a contraction.
--   * `b - a = δ/16` gives `(b-a)⁻² = 256/δ² ≤ 256/δ^6` for `δ ≤ 1/4`
--     (`Work.NN.Newton.FTs2.delta_geom_bound`), so `M := 256 * D` works for every `δ`.
theorem kappa_holderNorm_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (s : Fin n),
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.TelTwoDF.kappa (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
          (Work.NN.Core.TelTwoDF.Eset (Work.NN.Newton.ftG (n := n) δ hδ0 hδ4) s)
        ≤ ENNReal.ofReal (M / δ ^ 6) := by
  obtain ⟨D, hDpos, hD⟩ := holderNorm_sharpCut_univ_le (α := α) hα0 hα1
  refine ⟨256 * D, by positivity, ?_⟩
  intro δ hδ0 hδ4 s
  set G : Work.NN.Core.TelTwoDF.Geom n := Work.NN.Newton.ftG (n := n) δ hδ0 hδ4 with hG
  have ha_eq : G.a s = 1 - 15 * δ / 16 := by
    rw [hG]; exact Work.NN.Newton.ftG_a δ hδ0 hδ4 s
  have hb_eq : G.b s = 1 - 7 * δ / 8 := by
    rw [hG]; exact Work.NN.Newton.ftG_b δ hδ0 hδ4 s
  have ha2 : 1 / 2 ≤ G.a s := by rw [ha_eq]; linarith
  have hab : G.a s < G.b s := by rw [ha_eq, hb_eq]; linarith
  have hb1 : G.b s ≤ 1 := by rw [hb_eq]; linarith
  have hcomp := holderNorm_kappa_le G s hα0.le
  have hplanar := hD (G.a s) (G.b s) ha2 hab hb1
  have hgeom : D * (1 / (G.b s - G.a s) ^ 2) ≤ 256 * D / δ ^ 6 := by
    rw [ha_eq, hb_eq]
    exact delta_geom_bound D δ hDpos.le hδ0 hδ4
  exact le_trans (le_trans hcomp hplanar) (ENNReal.ofReal_le_ofReal hgeom)

end Work.NN.Newton.FTs2
