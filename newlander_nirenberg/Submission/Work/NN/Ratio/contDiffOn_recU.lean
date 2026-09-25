/-
# `C^m`-regularity of the telescoping solution `recU` from *local* smoothness of the data

`Geom.recU f` is built out of the one-variable Cauchy-type transforms
`dbarTransform G.r j` applied to the cut-off data `cutF j · recF f j j`, and the
intermediate data `recF f s k` are themselves obtained by iterating these transforms.
The existing smoothness theorem `contDiff_dbarTransform` requires the datum of the
transform to be *globally* `C^m`; here the datum is only known to be `C^m` on a
polydisc, so we prove the corresponding local statement

* `contDiffOn_dbarTransform` : if `g` is `C^m` on the polydisc of radii `φ`, vanishes
  for `‖y j‖ ≥ b`, and `ψ l ≤ φ l` for `l ≠ j` with `b < φ j`, then `dbarTransform ρ j g`
  is `C^m` on the polydisc of radii `ψ` (the transform is smooth in the `j`-th variable
  without any hypothesis, so no constraint on `ψ j` is needed).

This is proved exactly like `contDiff_dbarTransform`, with the parametrised-integrand
hypothesis obtained from locality of `ContDiffOn` rather than from global smoothness.

With it, the induction defining `recF` shows that every stage is `C^m` on a fixed
smaller polydisc, and summing the `n` terms gives `contDiffOn_recU`.
-/
import Mathlib
import Submission.Work.NN.Ratio.Defs

noncomputable section

open scoped NNReal ENNReal ContDiff Convolution Topology
open MeasureTheory Set Filter

namespace Work.NN.Ratio

open Work.CR.Flat (polydisc)

/-! ## The convolution identifiation for the Cauchy-type transform -/

/-- Lebesgue measure on `ℂ` is invariant under `w ↦ -w`, hence so is the Bochner integral. -/
private lemma integral_comp_neg_complex (F : ℂ → ℂ) : ∫ t, F (-t) = ∫ t, F t := by
  have h := MeasurableEmbedding.integral_map (μ := (volume : Measure ℂ)) measurableEmbedding_neg F
  rw [Measure.map_neg_eq_self (volume : Measure ℂ)] at h
  exact h.symm

/-- The integral of an indicator times a function, written as a set integral. -/
private lemma integral_indicator_mul_eq_setIntegral (s : Set ℂ) (hs : MeasurableSet s)
    (f h : ℂ → ℂ) : ∫ t, s.indicator f t * h t = ∫ t in s, f t * h t := by
  rw [← MeasureTheory.integral_indicator hs (f := fun t => f t * h t)]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]

/-- The "disc Cauchy kernel" `w ↦ -1/w` on `‖w‖ < ρ` (and `0` outside) is locally integrable,
since it is dominated by `‖w‖ ^ (-1)` and `1 < finrank ℝ ℂ = 2`. -/
private lemma locallyIntegrable_cauchyKernelBall (ρ : ℝ) :
    LocallyIntegrable ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)))
      (volume : Measure ℂ) := by
  refine MeasureTheory.locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (C := 1) (α := 1)
    (le_of_lt (by rw [Complex.finrank_real_complex]; norm_num))
    (by rw [Complex.finrank_real_complex]; norm_num) ?_ ?_
  · filter_upwards with x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Real.rpow_neg_one, one_mul]
      by_cases hxb : x ∈ Metric.ball (0 : ℂ) ρ
      · rw [Set.indicator_of_mem hxb, norm_neg, norm_inv]
      · rw [Set.indicator_of_notMem hxb, norm_zero]
        positivity
  · exact ((measurable_inv.neg).indicator measurableSet_ball).aestronglyMeasurable

/-- The disc integral defining `dbarTransform` equals the integral of the "sign-flipped"
Cauchy kernel against `g`, obtained through the substitution `w ↦ -w`. -/
private lemma setIntegral_ball_eq_cauchyKernel {n : ℕ} (ρ : ℝ) (j : Fin n)
    (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
            * g (z + Function.update (0 : Fin n → ℂ) j (-t)) := by
  have hKneg : ∀ t : ℂ, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
      = ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => a⁻¹)) t := by
    intro t
    by_cases ht : t ∈ Metric.ball (0 : ℂ) ρ
    · have hnt : -t ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        simpa using ht
      simp only [Set.indicator_of_mem hnt, Set.indicator_of_mem ht, inv_neg, neg_neg]
    · have hnt : -t ∉ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        simpa using ht
      simp only [Set.indicator_of_notMem hnt, Set.indicator_of_notMem ht]
  have h1 : (∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
                * g (z + Function.update (0 : Fin n → ℂ) j (-t)))
          = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
                * g (z + Function.update (0 : Fin n → ℂ) j t) := by
    have h := integral_comp_neg_complex (fun t : ℂ =>
      ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
        * g (z + Function.update (0 : Fin n → ℂ) j (-t)))
    simp only [neg_neg] at h
    exact h.symm
  have h2 : (∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
                * g (z + Function.update (0 : Fin n → ℂ) j t))
          = ∫ t in Metric.ball (0 : ℂ) ρ,
              t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t) := by
    simp only [hKneg]
    exact integral_indicator_mul_eq_setIntegral (Metric.ball (0 : ℂ) ρ) measurableSet_ball
      (fun a : ℂ => a⁻¹) (fun t : ℂ => g (z + Function.update (0 : Fin n → ℂ) j t))
  calc (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = ∫ t in Metric.ball (0 : ℂ) ρ,
          t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro t _
        change g (z + Function.update (0 : Fin n → ℂ) j t) / t
          = t⁻¹ * g (z + Function.update (0 : Fin n → ℂ) j t)
        rw [div_eq_mul_inv, mul_comm]
    _ = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) (-t)
            * g (z + Function.update (0 : Fin n → ℂ) j t) := h2.symm
    _ = ∫ t, ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹))) t
            * g (z + Function.update (0 : Fin n → ℂ) j (-t)) := h1.symm

/-- Pointwise, `dbarTransform` is (up to the constant `-1/π`) the convolution, in the `j`-th
coordinate, of `g` with the disc Cauchy kernel. -/
private lemma dbarTransform_eq_convolution {n : ℕ} (ρ : ℝ) (j : Fin n)
    (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j g z
      = -((Real.pi : ℂ))⁻¹
        * convolution ((Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)))
            (fun t : ℂ => g (z + Function.update (0 : Fin n → ℂ) j t))
            (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0 := by
  simp only [Work.CR.Flat.Cauchy.dbarTransform, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply', zero_sub]
  rw [setIntegral_ball_eq_cauchyKernel ρ j g z]

/-! ## The local smoothness theorem for `dbarTransform` -/

/-- **Local smoothness of the Cauchy-type transform.**  If the datum `g` is `C^m` on the
polydisc of radii `φ`, vanishes for `‖y j‖ ≥ b`, and `ψ l ≤ φ l` for `l ≠ j` with `b < φ j`,
then `dbarTransform ρ j g` is `C^m` on the polydisc of radii `ψ` (no condition on `ψ j`:
the transform is smoothing in the `j`-th variable). -/
theorem contDiffOn_dbarTransform {n : ℕ} {ρ b : ℝ} (hρ : b < ρ) (j : Fin n) (m : ℕ)
    {g : (Fin n → ℂ) → ℂ} {φ ψ : Fin n → ℝ}
    (hψφ : ∀ l, l ≠ j → ψ l ≤ φ l) (hbj : b < φ j)
    (hsupp : ∀ y, b ≤ ‖y j‖ → g y = 0)
    (hg : ContDiffOn ℝ m g (polydisc 0 φ)) :
    ContDiffOn ℝ m (Work.CR.Flat.Cauchy.dbarTransform ρ j g) (polydisc 0 ψ) := by
  set K : ℂ → ℂ := (Metric.ball (0 : ℂ) ρ).indicator (fun a : ℂ => -(a⁻¹)) with hK
  set Gt : (Fin n → ℂ) → ℂ → ℂ :=
    fun p t => g (p + Function.update (0 : Fin n → ℂ) j t) with hGt
  -- the bound on the `j`-th coordinate over the polydisc of radii `ψ`
  set C : ℝ := max (ψ j) 0 with hC
  have hCt : ∀ p : Fin n → ℂ, p ∈ polydisc 0 ψ → ‖p j‖ < C := by
    intro p hp
    have h1 : ‖p j‖ < ψ j := by simpa using hp j
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  -- the inequality `ψ l ≤ φ l` for `l ≠ j` gives the pointwise containment of the polydiscs
  have hsm : ContDiffOn ℝ m (Function.uncurry Gt) ((polydisc 0 ψ) ×ˢ (univ : Set ℂ)) := by
    rw [IsOpen.contDiffOn_iff ((Work.CR.Flat.isOpen_polydisc 0 ψ).prod isOpen_univ)]
    rintro ⟨p, t⟩ ⟨hp, -⟩
    have hyj : (p + Function.update (0 : Fin n → ℂ) j t) j = p j + t := by
      simp [Function.update_apply]
    by_cases hbt : b < ‖(p + Function.update (0 : Fin n → ℂ) j t) j‖
    · -- the integrand vanishes identically near `(p,t)`
      have hopen : IsOpen {q : (Fin n → ℂ) × ℂ | b < ‖q.1 j + q.2‖} :=
        isOpen_lt continuous_const (((continuous_apply j).comp continuous_fst).add
          continuous_snd).norm
      have hmem : (p, t) ∈ {q : (Fin n → ℂ) × ℂ | b < ‖q.1 j + q.2‖} := by
        simpa [hyj] using hbt
      have hev : Function.uncurry Gt =ᶠ[𝓝 (p, t)] fun _ => (0 : ℂ) := by
        filter_upwards [hopen.mem_nhds hmem] with q hq
        simp only [Function.uncurry, hGt]
        refine hsupp _ ?_
        rw [show (q.1 + Function.update (0 : Fin n → ℂ) j q.2) j = q.1 j + q.2 by
          simp [Function.update_apply]]
        exact le_of_lt hq
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · -- the integrand is `g` composed with the smooth map `q ↦ q.1 + e_j q.2`, and the
      -- point lies in the polydisc of radii `φ`
      have hbtj : ¬ b < ‖p j + t‖ := by rw [hyj] at hbt; exact hbt
      have hyφ : p + Function.update (0 : Fin n → ℂ) j t ∈ polydisc 0 φ := by
        intro l
        simp only [Pi.zero_apply, sub_zero]
        by_cases hl : l = j
        · rw [hl, hyj]
          exact lt_of_le_of_lt (le_of_not_gt hbtj) hbj
        · have hyl : (p + Function.update (0 : Fin n → ℂ) j t) l = p l := by
            simp [Function.update_apply, hl]
          rw [hyl]
          exact lt_of_lt_of_le (by simpa using hp l) (hψφ l hl)
      have hgc : ContDiffAt ℝ m g (p + Function.update (0 : Fin n → ℂ) j t) :=
        hg.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 φ).mem_nhds hyφ)
      have hTsm : ContDiffAt ℝ m
          (fun q : (Fin n → ℂ) × ℂ => q.1 + Function.update (0 : Fin n → ℂ) j q.2) (p, t) := by
        have hupd : ContDiff ℝ m (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t) := by
          rw [contDiff_pi]
          intro l
          by_cases hl : l = j
          · have hcomp : (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t l)
                = fun t : ℂ => t := by
              funext t
              simp only [Function.update_apply, ite_eq_left hl]
            rw [hcomp]; exact contDiff_id
          · have hcomp : (fun t : ℂ => Function.update (0 : Fin n → ℂ) j t l)
                = fun _ : ℂ => (0 : ℂ) := by
              funext t
              simp only [Function.update_apply, ite_eq_right hl]
              rfl
            rw [hcomp]; exact contDiff_const
        exact ((contDiff_fst (E := Fin n → ℂ) (F := ℂ)).add
          (hupd.comp contDiff_snd)).contDiffAt
      refine (hgc.comp (p, t) hTsm).congr_of_eventuallyEq ?_
      filter_upwards with q
      simp only [Function.uncurry, hGt, Function.comp_apply]
  -- the support condition for the convolution formula
  have hsupp_conv : ∀ p : Fin n → ℂ, ∀ x : ℂ, p ∈ polydisc 0 ψ →
      x ∉ Metric.closedBall (0 : ℂ) (b + C) → Gt p x = 0 := by
    intro p x hp hx
    have hx' : b + C < ‖x‖ := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact lt_of_not_ge hx
    have hpj : ‖p j‖ < C := hCt p hp
    have hnorm : b < ‖p j + x‖ := by
      have h1 : ‖x‖ ≤ ‖p j + x‖ + ‖p j‖ := by
        have h2 : (p j + x) - p j = x := by ring
        calc ‖x‖ = ‖(p j + x) - p j‖ := by rw [h2]
          _ ≤ ‖p j + x‖ + ‖p j‖ := norm_sub_le _ _
      linarith
    have : (p + Function.update (0 : Fin n → ℂ) j x) j = p j + x := by
      simp [Function.update_apply]
    simp only [hGt]
    exact hsupp _ (le_of_lt (by rwa [this]))
  have hk : IsCompact (Metric.closedBall (0 : ℂ) (b + C)) := isCompact_closedBall _ _
  have hconv := MeasureTheory.contDiffOn_convolution_right_with_param
      (L := ContinuousLinearMap.mul ℝ ℂ) (f := K) (g := Gt) (μ := (volume : Measure ℂ))
      (s := polydisc 0 ψ) (k := Metric.closedBall (0 : ℂ) (b + C)) (n := m)
      (Work.CR.Flat.isOpen_polydisc 0 ψ) hk hsupp_conv
      (locallyIntegrable_cauchyKernelBall ρ) hsm
  have hcomp := hconv.comp (contDiffOn_id.prodMk (contDiffOn_const (c := (0 : ℂ))))
    (fun x hx => ⟨hx, trivial⟩)
  have hident : Work.CR.Flat.Cauchy.dbarTransform ρ j g
      = fun z => -((Real.pi : ℂ))⁻¹
          * convolution K (Gt z) (ContinuousLinearMap.mul ℝ ℂ) (volume : Measure ℂ) 0 := by
    funext z
    simp only [hK, hGt]
    exact dbarTransform_eq_convolution ρ j g z
  rw [hident]
  exact (contDiffOn_const (c := -((Real.pi : ℂ))⁻¹)).mul hcomp

/-! ## Every stage of the recursion is `C^m` on a smaller polydisc -/

/-- If the datum is `C^m` on the polydisc of radius `G.T`, then every intermediate datum
`G.recF f s k` is `C^m` on the polydisc of radius `ϑ`, for any `G.b < ϑ ≤ G.T`.

(The recursion replaces the `j`-th cut-off factor in the `m`-fold transform, so the
smoothness region loses nothing in the `j`-th variable and the `m`-th variable there is
only needed below `G.b`; hence a single smaller polydisc works at every stage.) -/
private theorem contDiffOn_recF {n : ℕ} (G : Geom n) {m : ℕ} {ϑ : ℝ}
    (hbϑ : G.b < ϑ) (hϑT : ϑ ≤ G.T)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ m (f j) (Work.CR.Flat.polydisc 0 (fun _ => G.T))) :
    ∀ s k, ContDiffOn ℝ m (G.recF f s k) (Work.CR.Flat.polydisc 0 (fun _ => ϑ)) := by
  intro s
  induction s with
  | zero =>
      intro k
      exact (hf k).mono (Work.CR.Flat.polydisc_mono (fun _ => hϑT))
  | succ s ih =>
      intro k
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hrec : G.recF f (s + 1) = G.stepData j (G.recF f s) := G.recF_succ_of_lt hlt
        rw [hrec]
        simp only [Geom.stepData]
        set δ : ℝ := (ϑ - G.b) / 2 with hδ
        have hδpos : 0 < δ := by rw [hδ]; linarith
        have hbδϑ : G.b + δ < ϑ := by rw [hδ]; linarith
        have hrb : G.b < G.r := by linarith [G.hr, G.ha, G.hab]
        have hupd : Function.update (fun _ : Fin n => ϑ) j (G.b + δ) j = G.b + δ := by
          simp [Function.update_apply]
        refine contDiffOn_dbarTransform (hρ := hrb) (j := j) (m := m)
          (g := fun y => G.cutFbar j y * G.recF f s k y)
          (φ := Function.update (fun _ : Fin n => ϑ) j (G.b + δ)) (ψ := fun _ => ϑ)
          ?_ ?_ ?_ ?_
        · intro l hl
          simp [Function.update_apply, hl]
        · rw [hupd]; linarith
        · intro y hy
          rw [Geom.cutFbar_eq_zero_of_ge (G := G) hy, zero_mul]
        · have hsub : Work.CR.Flat.polydisc 0
                (Function.update (fun _ : Fin n => ϑ) j (G.b + δ))
              ⊆ Work.CR.Flat.polydisc 0 (fun _ => ϑ) :=
            Work.CR.Flat.polydisc_mono (fun l => by
              by_cases hl : l = j
              · rw [hl, hupd]; exact le_of_lt hbδϑ
              · simp [Function.update_apply, hl])
          exact (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty m)).contDiffOn).mul
            ((ih k).mono hsub)
      · have hrec : G.recF f (s + 1) = G.recF f s := by
          rw [Geom.recF_succ]; simp [hlt]
        rw [hrec]
        exact ih k

/-- **`C^m`-regularity of the telescoping solution from local smoothness of the data.** -/
theorem contDiffOn_recU {n : ℕ} (G : Work.NN.Ratio.Geom n) {m : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ m (f j) (Work.CR.Flat.polydisc 0 (fun _ => G.T))) :
    ContDiffOn ℝ m (fun z => G.recU f z) (Work.CR.Flat.polydisc 0 (fun _ => G.e)) := by
  set ϑ : ℝ := (G.b + G.T) / 2 with hϑ
  have hbϑ : G.b < ϑ := by rw [hϑ]; linarith [G.hbT]
  have hϑT : ϑ ≤ G.T := by rw [hϑ]; linarith [G.hbT]
  set e' : ℝ := (G.e + G.a) / 2 with he'
  have hee' : G.e < e' := by rw [he']; linarith [G.hea]
  have he'a : e' < G.a := by rw [he']; linarith [G.hea]
  have he'b : e' < G.b := lt_trans he'a G.hab
  have hbase := contDiffOn_recF G hbϑ hϑT hf
  have hterm : ∀ j : Fin n, ContDiffOn ℝ m
      (fun z => Work.CR.Flat.Cauchy.dbarTransform G.r j
        (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z)
      (Work.CR.Flat.polydisc 0 (fun _ => e')) := by
    intro j
    set δ : ℝ := (ϑ - G.b) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hbδϑ : G.b + δ < ϑ := by rw [hδ]; linarith
    have hrb : G.b < G.r := by linarith [G.hr, G.ha, G.hab]
    have hupd : Function.update (fun _ : Fin n => e') j (G.b + δ) j = G.b + δ := by
      simp [Function.update_apply]
    refine contDiffOn_dbarTransform (hρ := hrb) (j := j) (m := m)
      (g := fun y => G.cutF j y * G.recF f (j : ℕ) j y)
      (φ := Function.update (fun _ : Fin n => e') j (G.b + δ)) (ψ := fun _ => e')
      ?_ ?_ ?_ ?_
    · intro l hl
      simp [Function.update_apply, hl]
    · rw [hupd]; linarith
    · intro y hy
      rw [Geom.cutF_eq_zero (G := G) hy, zero_mul]
    · have hsub : Work.CR.Flat.polydisc 0
              (Function.update (fun _ : Fin n => e') j (G.b + δ))
            ⊆ Work.CR.Flat.polydisc 0 (fun _ => ϑ) :=
          Work.CR.Flat.polydisc_mono (fun l => by
            by_cases hl : l = j
            · rw [hl, hupd]; exact le_of_lt hbδϑ
            · simp [Function.update_apply, hl]; exact le_of_lt (lt_trans he'b hbϑ))
      exact (((Geom.contDiff_cutF (G := G) j).of_le (le_infty m)).contDiffOn).mul
        ((hbase (j : ℕ) j).mono hsub)
  have hsum : ContDiffOn ℝ m (fun z => G.recU f z) (Work.CR.Flat.polydisc 0 (fun _ => e')) := by
    rw [show (fun z => G.recU f z) = fun z => ∑ j : Fin n,
        Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z from rfl]
    exact ContDiffOn.sum (s := Finset.univ) (fun j _ => hterm j)
  exact hsum.mono (Work.CR.Flat.polydisc_mono (fun _ => le_of_lt hee'))

end Work.NN.Ratio
