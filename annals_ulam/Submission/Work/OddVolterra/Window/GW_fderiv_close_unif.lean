import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.Window.GW_fderiv_close
import Submission.Work.OddVolterra.Existence.aw_engine_godd
import Submission.Work.Anchor.deriv_close

/-!
# Uniform (in the perturbation) closeness of the differential of the cut-off datum `GW`

`Work.OddVolterra.Window.GW n h s z = chiG s z • Godd n h s z` is the state datum of the
long-interval Volterra engine for the odd transition-slope window (`WindowDefs`).  The
ε-δ form of the engine's estimate is `Work.OddVolterra.Window.GW_fderiv_close`: for every
tolerance `ε` there is `δ` and a constant `Cg` (depending on `h`) with

`‖fderiv (GW n h s ·) z - fderiv (GW n 0 s ·) (baseState s)‖ ≤ Cg ‖z - baseState s‖ + ε`

whenever `h` is small in `C^{n+2}` by `δ`.  The engine wants the *uniform* form: a single pair
of constants `(Cg, C₃)`, valid for **every** perturbation `h` whose jets up to order `n+2` are
bounded by the same `δ ≤ 1/100` on the right-hand side.

The proof rests on the structural fact that the state datum does not see all of `h`:

`Godd n h s z = GoddDiag n s (h s) (h' s) z`
(`Work.OddCurveB.Existence.Godd_eq_GoddDiag`),

so that on the tube `‖z - baseState s‖ ≤ 7/16` every quantity attached to `Godd n h s ·` is the
evaluation at the *compact* box

`{((s, hs, hp), z) : s ∈ [7/10, 19/20], |hs|, |hp| ≤ 1/100, z 0, z 1 ∈ [1/4, 3/2], …}`

of a fixed smooth function of the joint data (`Godd_tube_unif`).  Compactness of the box —
not any property of `h` beyond the two bounds `|h s| ≤ 1/100`, `|h' s| ≤ 1/100` — gives a
uniform bound `K` for `Godd` and for `‖fderiv (Godd n h s ·) z‖`, and hence a uniform Lipschitz
constant `M` for `GW n h s` on the tube (`GW_lipschitz_tube_unif`).

The final estimate is then the same two-case splitting as in `GW_fderiv_close`:

* `‖z - baseState s‖ < 1/5`: the cut-off is locally `1`, so `GW` agrees with `Godd` near `z` and
  near `baseState s`, and `Work.Anchor.deriv_close` gives the bound with the *uniform* constants
  `C₁` (slope in the state) and `C₂` (slope in `δ`);
* `‖z - baseState s‖ ≥ 1/5`: both differentials are bounded by the uniform Lipschitz constant
  `M` of `GW` on the tube — directly when `‖z - baseState s‖ ≤ 2/5`, and through the vanishing of
  the cut-off when `‖z - baseState s‖ > 2/5` — and the required slope constant `Cg = 10 M + 1`
  absorbs the factor `1/5`.

## Main declarations

* `Godd_tube_unif` — the uniform value / differential / Lipschitz bounds for `Godd` on the tube;
* `GW_lipschitz_tube_unif` — the uniform Lipschitz constant of `GW n h s` on the tube;
* `GW_fderiv_close_unif` — the requested uniform estimate.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## 1. The joint (diagonal) system as a function of `((s, h s, h' s), z)` -/

/-- The diagonal Volterra system, as a function of the joint data `((s, h s, h'(s)), z)`. -/
def GjDiag (n : ℕ) (q : Work.OddVolterra.Existence.awQ) : St :=
  Work.OddCurveB.Existence.GoddDiag n q.1.1 q.1.2.1 q.1.2.2 q.2

lemma contDiffOn_GjDiag (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ContDiffOn ℝ ∞ (GjDiag n) (Work.OddVolterra.Existence.awUbox B) := by
  rw [(Work.OddVolterra.Existence.isOpen_awUbox B).contDiffOn_iff]
  intro q hq
  exact Work.OddVolterra.Existence.contDiffAt_GoddDiag_comp n hn hq

lemma contDiffOn_fderiv_GjDiag (n : ℕ) (hn : 1 ≤ n) (B : ℝ) :
    ContDiffOn ℝ 2 (fun q => fderiv ℝ (GjDiag n) q)
      (Work.OddVolterra.Existence.awUbox B) :=
  (contDiffOn_GjDiag n hn B).fderiv_of_isOpen
    (Work.OddVolterra.Existence.isOpen_awUbox B)
    (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ∞) + 1) ≤ ⊤))

/-- The `z`-differential of a section of the joint system, as a composition of the joint
differential with the inclusion of the state space. -/
lemma fderiv_GjDiag_section (n : ℕ) (hn : 1 ≤ n) {B : ℝ} {p : ℝ × ℝ × ℝ} {z : St}
    (hp : (p, z) ∈ Work.OddVolterra.Existence.awUbox B) :
    fderiv ℝ (fun w => GjDiag n (p, w)) z =
      (fderiv ℝ (GjDiag n) (p, z)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St) := by
  have hd : DifferentiableAt ℝ (GjDiag n) (p, z) :=
    ((contDiffOn_GjDiag n hn B).contDiffAt
      ((Work.OddVolterra.Existence.isOpen_awUbox B).mem_nhds hp)).differentiableAt (by simp)
  have hin : DifferentiableAt ℝ (fun w : St => (p, w)) z :=
    (differentiableAt_const p).prodMk differentiableAt_id
  have hcomp := fderiv_comp (x := z) (g := GjDiag n) (f := fun w : St => (p, w)) hd hin
  rw [show (fun w : St => GjDiag n (p, w)) = (GjDiag n) ∘ (fun w : St => (p, w)) from rfl,
    hcomp, (hasFDerivAt_prodMk_right p z).fderiv]

/-! ## 2. The uniform tube bounds for `Godd` -/

/-- **Uniform bounds for the diagonal system on the tube, over the whole jet box.**

There is `K ≥ 0` such that for every function `h` with `|h| ≤ 1/100` and `|h'| ≤ 1/100`
(no smoothness, no support hypothesis is needed), every `s ∈ [7/10, 19/20]` and every
`z ∈ tube s`:

* `z ↦ Godd n h s z` is Lipschitz on `tube s` with constant `K`;
* `‖Godd n h s z‖ ≤ K` and `‖fderiv (Godd n h s ·) z‖ ≤ K`.

The point is that `Godd n h s z = GoddDiag n s (h s) (h' s) z` depends on `h` only through the
two numbers `(h s, h' s)`, which range over the *fixed* compact box `awKbox B` of
`Work.OddVolterra.Existence.aw_engine_godd`. -/
theorem Godd_tube_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ → ℝ, (∀ x : ℝ, |h x| ≤ 1 / 100) →
      (∀ x : ℝ, |deriv h x| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc wLeft wRight,
        LipschitzOnWith K.toNNReal (fun z => Godd n h s z) (tube s) ∧
        (∀ z ∈ tube s, ‖Godd n h s z‖ ≤ K ∧
          ‖fderiv ℝ (fun w => Godd n h s w) z‖ ≤ K) := by
  obtain ⟨B, hB1, hB⟩ := Work.Anchor.DClose.exists_deriv_profileX_bound
  have hCD := contDiffOn_GjDiag n hn B
  have hCD2 := contDiffOn_fderiv_GjDiag n hn B
  obtain ⟨Kf, hKf⟩ :=
    (Work.OddVolterra.Existence.isCompact_awKbox B).exists_bound_of_continuousOn
      (hCD2.continuousOn.mono (Work.OddVolterra.Existence.awKbox_subset_awUbox (B := B)))
  obtain ⟨Kv, hKv⟩ :=
    (Work.OddVolterra.Existence.isCompact_awKbox B).exists_bound_of_continuousOn
      (hCD.continuousOn.mono (Work.OddVolterra.Existence.awKbox_subset_awUbox (B := B)))
  refine ⟨max (max Kf Kv) 0, le_max_right _ _, ?_⟩
  intro h hb0 hb1 s hs
  have hs' : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) :=
    ⟨by have h := hs.1; rw [wLeft] at h; linarith,
     by have h := hs.2; rw [wRight] at h; linarith⟩
  have hpxl : (7 / 10 : ℝ) ≤ Commons.Geometry.Ulam.profileX s :=
    Work.Anchor.DClose.profileX_lower hs'
  have hpxu : Commons.Geometry.Ulam.profileX s ≤ 19 / 20 :=
    Work.Anchor.DClose.profileX_upper hs'
  have hbs0 := Work.Anchor.DClose.baseState_zero s
  have hbs1 := Work.Anchor.DClose.baseState_one s
  have hbs2 := Work.Anchor.DClose.baseState_two s
  have hbs3 := Work.Anchor.DClose.baseState_three s
  have hBabs := abs_le.mp (hB s hs')
  -- every tube point gives a point of the compact box
  have hmem : ∀ z : St, ‖z - baseState s‖ ≤ 7 / 16 →
      (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) ∈ Work.OddVolterra.Existence.awKbox B := by
    intro z hz
    refine ⟨⟨hs', Set.mem_Icc.mpr (abs_le.mp (hb0 s)),
      Set.mem_Icc.mpr (abs_le.mp (hb1 s))⟩, ?_⟩
    rw [Work.OddVolterra.Existence.mem_awZbox_iff]
    have hcoord : ∀ i : Fin 4, |z i - baseState s i| ≤ 7 / 16 := fun i => by
      have h := norm_le_pi_norm (z - baseState s) i
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      exact le_trans h hz
    have h0 := hcoord 0; rw [hbs0] at h0
    have h1 := hcoord 1; rw [hbs1] at h1
    have h2 := hcoord 2; rw [hbs2] at h2
    have h3 := hcoord 3; rw [hbs3] at h3
    have a0 := abs_le.mp h0; have a1 := abs_le.mp h1
    have a2 := abs_le.mp h2; have a3 := abs_le.mp h3
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by linarith⟩
  -- the pointwise value and differential bounds
  have hpoint : ∀ z ∈ tube s, ‖Godd n h s z‖ ≤ max (max Kf Kv) 0 ∧
      ‖fderiv ℝ (fun w => Godd n h s w) z‖ ≤ max (max Kf Kv) 0 := by
    intro z hz
    have hz' : ‖z - baseState s‖ ≤ 7 / 16 := by
      rw [tube, Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have hmemz := hmem z hz'
    have hmemU := Work.OddVolterra.Existence.awKbox_subset_awUbox hmemz
    have hval : Godd n h s z = GjDiag n (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) := by
      rw [Work.OddCurveB.Existence.Godd_eq_GoddDiag]; rfl
    have heqfun : (fun w : St => GjDiag n (((s, h s, deriv h s) : ℝ × ℝ × ℝ), w))
        = (fun w => Godd n h s w) := by
      funext w; rw [Work.OddCurveB.Existence.Godd_eq_GoddDiag]; rfl
    have hsec := fderiv_GjDiag_section n hn hmemU
    have hsec' : fderiv ℝ (fun w => Godd n h s w) z =
        (fderiv ℝ (GjDiag n) (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z)).comp
          (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) St) := by
      rw [← heqfun]; exact hsec
    refine ⟨?_, ?_⟩
    · rw [hval]
      exact le_trans (hKv _ hmemz) (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [hsec']
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      rw [ContinuousLinearMap.norm_inr, mul_one]
      exact le_trans (hKf _ hmemz) (le_trans (le_max_left _ _) (le_max_left _ _))
  -- differentiability of the section on the tube
  have hdiff : ∀ z ∈ tube s, DifferentiableAt ℝ (fun w => Godd n h s w) z := by
    intro z hz
    have hz' : ‖z - baseState s‖ ≤ 7 / 16 := by
      rw [tube, Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have hmemU := Work.OddVolterra.Existence.awKbox_subset_awUbox (hmem z hz')
    have hd : DifferentiableAt ℝ (GjDiag n) (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) :=
      ((hCD.contDiffAt ((Work.OddVolterra.Existence.isOpen_awUbox B).mem_nhds hmemU)))
        |>.differentiableAt (by simp)
    have hin : DifferentiableAt ℝ
        (fun w : St => (((s, h s, deriv h s) : ℝ × ℝ × ℝ), w)) z :=
      (differentiableAt_const _).prodMk differentiableAt_id
    have hcomp := hd.comp z hin
    have heqfun : (fun w : St => GjDiag n (((s, h s, deriv h s) : ℝ × ℝ × ℝ), w))
        = (fun w => Godd n h s w) := by
      funext w; rw [Work.OddCurveB.Existence.Godd_eq_GoddDiag]; rfl
    rw [← heqfun]; simpa [Function.comp_def] using hcomp
  refine ⟨?_, hpoint⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (s := tube s)
    (f := fun z => Godd n h s z) (C := (max (max Kf Kv) 0).toNNReal)
    (fun z hz => hdiff z hz) (fun z hz => ?_) ?_
  · rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hpoint z hz).2
  · rw [tube]; exact convex_closedBall _ _

/-! ## 3. The uniform Lipschitz constant of `GW` on the tube -/

/-- **The cut-off datum `GW n h s` is Lipschitz on the tube with a constant uniform in `h`.**

`GW n h s = cz ‖· - baseState s‖ • Godd n h s` on the window (`cs = 1` there), so the Lipschitz
constant is the one of `Godd n h s` on the tube plus the Lipschitz constant of `cz` times the
bound on `‖Godd n h s‖`; both are uniform by `Godd_tube_unif`. -/
theorem GW_lipschitz_tube_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ M : NNReal, ∀ h : ℝ → ℝ, (∀ x : ℝ, |h x| ≤ 1 / 100) →
      (∀ x : ℝ, |deriv h x| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc wLeft wRight, LipschitzOnWith M (fun z => GW n h s z) (tube s) := by
  obtain ⟨K, hK0, hK⟩ := Godd_tube_unif n hn
  obtain ⟨L, hL⟩ := cz_lipschitz
  refine ⟨K.toNNReal + L * K.toNNReal, fun h hb0 hb1 s hs => ?_⟩
  obtain ⟨hLipG, hbnd⟩ := hK h hb0 hb1 s hs
  have hKnn : ((K.toNNReal : NNReal) : ℝ) = K := Real.coe_toNNReal K hK0
  have hcs : (cs : ℝ → ℝ) s = 1 := cs_eq_one_of_mem hs
  have hcl : LipschitzOnWith L (fun z : St => (cz : ℝ → ℝ) ‖z - baseState s‖) (tube s) :=
    (cz_comp_norm_lipschitz hL s).lipschitzOnWith
  refine lipschitzOnWith_iff_norm_sub_le.mpr fun u hu v hv => ?_
  have hGWu : GW n h s u = (cz : ℝ → ℝ) ‖u - baseState s‖ • Godd n h s u := by
    rw [GW, chiG, hcs, one_mul]
  have hGWv : GW n h s v = (cz : ℝ → ℝ) ‖v - baseState s‖ • Godd n h s v := by
    rw [GW, chiG, hcs, one_mul]
  rw [hGWu, hGWv]
  have hsplit : (cz : ℝ → ℝ) ‖u - baseState s‖ • Godd n h s u -
        (cz : ℝ → ℝ) ‖v - baseState s‖ • Godd n h s v
      = (cz : ℝ → ℝ) ‖u - baseState s‖ •
          (Godd n h s u - Godd n h s v) +
        ((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
          Godd n h s v := by
    rw [smul_sub, sub_smul]
    abel
  rw [hsplit]
  have hcU : |(cz : ℝ → ℝ) ‖u - baseState s‖| ≤ 1 := abs_cz_le_one _
  have hcd : ‖(cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖‖
      ≤ (L : ℝ) * ‖u - v‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hcl.dist_le_mul u hu v hv
  have hgd : ‖Godd n h s u - Godd n h s v‖ ≤ ((K.toNNReal : NNReal) : ℝ) * ‖u - v‖ := by
    simpa only [dist_eq_norm] using hLipG.dist_le_mul u hu v hv
  have hgv : ‖Godd n h s v‖ ≤ ((K.toNNReal : NNReal) : ℝ) := by
    rw [hKnn]
    exact (hbnd v hv).1
  have hgnn : (0 : ℝ) ≤ ((K.toNNReal : NNReal) : ℝ) := by rw [hKnn]; exact hK0
  calc ‖(cz : ℝ → ℝ) ‖u - baseState s‖ •
          (Godd n h s u - Godd n h s v) +
        ((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
          Godd n h s v‖
      ≤ ‖(cz : ℝ → ℝ) ‖u - baseState s‖ •
            (Godd n h s u - Godd n h s v)‖ +
        ‖((cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖) •
            Godd n h s v‖ := norm_add_le _ _
    _ ≤ |(cz : ℝ → ℝ) ‖u - baseState s‖| *
            ‖Godd n h s u - Godd n h s v‖ +
        ‖(cz : ℝ → ℝ) ‖u - baseState s‖ - (cz : ℝ → ℝ) ‖v - baseState s‖‖ *
            ‖Godd n h s v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (((K.toNNReal : NNReal) : ℝ) * ‖u - v‖) +
        ((L : ℝ) * ‖u - v‖) * ((K.toNNReal : NNReal) : ℝ) :=
        add_le_add (mul_le_mul hcU hgd (norm_nonneg _) (by norm_num))
          (mul_le_mul hcd hgv (norm_nonneg _) (by positivity))
    _ = (((K.toNNReal + L * K.toNNReal : NNReal)) : ℝ) * ‖u - v‖ := by
        rw [NNReal.coe_add, NNReal.coe_mul]
        ring

/-! ## 4. The uniform estimate -/

theorem GW_fderiv_close_unif (n : ℕ) (hn : 1 ≤ n) :
    ∃ Cg C₃ : ℝ, 0 ≤ Cg ∧ 0 ≤ C₃ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc Work.OddVolterra.Window.wLeft Work.OddVolterra.Window.wRight,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) 1,
        ‖fderiv ℝ (fun w => Work.OddVolterra.Window.GW n h s w) z -
           fderiv ℝ (fun w => Work.OddVolterra.Window.GW n 0 s w)
             (Work.OddVolterra.baseState s)‖
          ≤ Cg * ‖z - Work.OddVolterra.baseState s‖ + C₃ * δ := by
  obtain ⟨C₁, C₂, hC1, hC2, hdc⟩ := Work.Anchor.deriv_close n hn
  obtain ⟨M, hM⟩ := GW_lipschitz_tube_unif n hn
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  refine ⟨max (C₁ + 1) (10 * (M : ℝ) + 1), C₂, le_max_of_le_left (by linarith), hC2.le, ?_⟩
  intro δ hδ hδ100 h hh hsupp hjet s hs z hz
  -- the two pointwise jet bounds, and those for the zero perturbation
  have hb0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => by
    have h0 := hjet 0 (Nat.zero_le _) x
    rw [iteratedDeriv_zero] at h0
    exact le_trans h0 hδ100
  have hb1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    have h1 := hjet 1 (by omega) x
    rw [iteratedDeriv_one] at h1
    exact le_trans h1 hδ100
  have hz0 : ∀ x : ℝ, |(0 : ℝ → ℝ) x| ≤ 1 / 100 := fun x => by simp
  have hz1 : ∀ x : ℝ, |deriv (0 : ℝ → ℝ) x| ≤ 1 / 100 := fun x => by simp
  have hMh : LipschitzOnWith M (fun z => GW n h s z) (tube s) := hM h hb0 hb1 s hs
  have hM0 : LipschitzOnWith M (fun z => GW n 0 s z) (tube s) :=
    hM (fun _ => (0 : ℝ)) hz0 hz1 s hs
  have hs' : s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20) :=
    ⟨by have h := hs.1; rw [wLeft] at h; linarith,
     by have h := hs.2; rw [wRight] at h; linarith⟩
  have hr1 : ‖z - baseState s‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
  rcases lt_or_ge ‖z - baseState s‖ (1 / 5) with hlt | hge
  · -- close to the base state: use the ε-δ estimate with `ε = C₂ δ`
    have heq1 : (fun w : St => GW n h s w) =ᶠ[𝓝 z] (fun w => Godd n h s w) :=
      eventuallyEq_GW_Godd hs (by linarith)
    have heq0 : (fun w : St => GW n 0 s w) =ᶠ[𝓝 (baseState s)] (fun w => Godd n 0 s w) :=
      eventuallyEq_GW_Godd hs (by simp)
    rw [heq1.fderiv_eq, heq0.fderiv_eq]
    have hb := hdc h hh hsupp δ hδ hδ100 hjet s hs' z (by linarith)
    have hCgle : C₁ ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) :=
      le_trans (by linarith) (le_max_left _ _)
    have h1 : C₁ * ‖z - baseState s‖ ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) *
        ‖z - baseState s‖ :=
      mul_le_mul_of_nonneg_right hCgle (norm_nonneg _)
    linarith
  · -- far from the base state: both differentials are bounded by the Lipschitz constant
    have hbndh : ‖fderiv ℝ (fun w : St => GW n h s w) z‖ ≤ (M : ℝ) := by
      by_cases hr : ‖z - baseState s‖ ≤ 2 / 5
      · have hnb : tube s ∈ 𝓝 z := by
          refine Filter.mem_of_superset
            (Metric.ball_mem_nhds z (by linarith : 0 < 7 / 16 - ‖z - baseState s‖)) ?_
          intro w hw
          rw [Metric.mem_ball, dist_eq_norm] at hw
          rw [tube, Metric.mem_closedBall, dist_eq_norm]
          calc ‖w - baseState s‖ ≤ ‖w - z‖ + ‖z - baseState s‖ := by
                rw [show w - baseState s = (w - z) + (z - baseState s) by abel]
                exact norm_add_le _ _
            _ ≤ 7 / 16 := by linarith
        exact norm_fderiv_le_of_lipschitzOn ℝ hnb hMh
      · have hr' : 2 / 5 < ‖z - baseState s‖ := lt_of_not_ge hr
        rw [(eventuallyEq_GW_zero (h := h) hr').fderiv_eq]
        simp
    have hbnd0 : ‖fderiv ℝ (fun w : St => GW n 0 s w) (baseState s)‖ ≤ (M : ℝ) :=
      norm_fderiv_le_of_lipschitzOn ℝ
        (Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 7 / 16)) hM0
    have hsum : ‖fderiv ℝ (fun w : St => GW n h s w) z -
        fderiv ℝ (fun w : St => GW n 0 s w) (baseState s)‖ ≤ (M : ℝ) + (M : ℝ) :=
      le_trans (norm_sub_le _ _) (add_le_add hbndh hbnd0)
    have hmax : 10 * (M : ℝ) + 1 ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) := le_max_right _ _
    have hmax0 : (0 : ℝ) ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) := by
      refine le_trans ?_ (le_max_right _ _); linarith
    have hr : (1 / 5 : ℝ) ≤ ‖z - baseState s‖ := hge
    have hkey : (M : ℝ) + (M : ℝ) ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) *
        ‖z - baseState s‖ := by
      have h1 : (10 * (M : ℝ) + 1) * (1 / 5) ≤ max (C₁ + 1) (10 * (M : ℝ) + 1) *
          ‖z - baseState s‖ :=
        mul_le_mul hmax hr (by norm_num) hmax0
      nlinarith [h1, hMnn]
    linarith [hsum, hkey, mul_nonneg hC2.le hδ.le]

end

end Work.OddVolterra.Window
