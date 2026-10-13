/-
  WilC4aCS.EucMax -- the maximiser argument for the inequality-only (`F =ᶠ 0`) case of the
  curve-selection induction step `C4a_CS_step`.

  Route.  For every small radius `R` maximise `ψ` over the *Euclidean* ball
  `K = {x | Σᵢ xᵢ² ≤ R²} ∩ {x | ∀ j, 0 ≤ gⱼ x}` (which also lies in the metric ball
  `Metric.closedBall 0 R`, because the sup norm is bounded by the Euclidean norm).  At the
  maximiser `x` all inequalities are strict (by `hkills`), so for every direction `v` with
  `⟨x,v⟩ = Σᵢ xᵢvᵢ < 0` the point `x + t·v` lies in `K` for all small `t > 0`; hence the
  one-sided derivative at `0⁺` of `t ↦ ψ (x + t·v)` is `≤ 0`.  `rotSq_eq_zero_of_sum_mul_neg`
  then gives `rotSq ψ x = 0`, and `x` is as close to `0` as we like -- so the zero set of
  `rotSq ψ` still accumulates at `0` inside `{∀ j, 0 < gⱼ}`.

  The metric (sup-norm) ball CANNOT be used directly: on `Fin m → ℝ` it is the cube, and a
  maximum at a corner of the cube carries no Lagrange condition -- `rotSq ψ x ≠ 0` is possible
  there (this is exactly what refutes the earlier `rotSq_eq_zero_of_isMaxOn_closedBall`).
-/
import Mathlib
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.rotSq_eq_zero_of_sum_mul_neg

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a

/-! ## 1. The squared Euclidean norm and its relation to the sup norm -/

/-- The squared Euclidean norm of a finite real tuple. -/
def eucSq {m : ℕ} (x : Fin m → ℝ) : ℝ := ∑ i, x i ^ 2

lemma eucSq_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ eucSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

lemma eucSq_eq_zero {m : ℕ} {x : Fin m → ℝ} (h : eucSq x = 0) : x = 0 := by
  funext i
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin m)), x j ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp h
  exact sq_eq_zero_iff.mp (h1 i (Finset.mem_univ i))

lemma continuous_eucSq {m : ℕ} : Continuous (eucSq : (Fin m → ℝ) → ℝ) := by
  have h : Continuous fun x : Fin m → ℝ => ∑ i : Fin m, x i ^ 2 :=
    continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).pow 2
  exact h

/-- `‖·‖` is the sup norm on `Fin m → ℝ`, so it is bounded by the Euclidean norm. -/
lemma norm_le_sqrt_eucSq {m : ℕ} (x : Fin m → ℝ) : ‖x‖ ≤ Real.sqrt (eucSq x) :=
  (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg (eucSq x))).mpr fun i => by
    refine (Real.le_sqrt (norm_nonneg (x i)) (eucSq_nonneg x)).mpr ?_
    rw [Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- Conversely each coordinate is bounded by the sup norm, so `eucSq x ≤ m ‖x‖²`. -/
lemma eucSq_le_card_mul_norm_sq {m : ℕ} (y : Fin m → ℝ) :
    eucSq y ≤ (m : ℝ) * ‖y‖ ^ 2 := by
  have hterm : ∀ i : Fin m, y i ^ 2 ≤ ‖y‖ ^ 2 := fun i => by
    have h : |y i| ≤ ‖y‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
    exact sq_le_sq.mpr (by rwa [abs_of_nonneg (norm_nonneg y)])
  calc eucSq y = ∑ i : Fin m, y i ^ 2 := rfl
    _ ≤ ∑ _i : Fin m, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (m : ℝ) * ‖y‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A point of the Euclidean ball of radius `R ≥ 0` lies in the metric ball of radius `R`. -/
lemma norm_le_of_eucSq_le {m : ℕ} {z : Fin m → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : eucSq z ≤ R ^ 2) : ‖z‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR]
  intro i
  have h1 : z i ^ 2 ≤ eucSq z :=
    Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have h2 : z i ^ 2 ≤ R ^ 2 := le_trans h1 h
  calc ‖z i‖ = Real.sqrt (z i ^ 2) := by rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h2
    _ = R := Real.sqrt_sq hR

/-- The quadratic expansion of the squared Euclidean norm along a line. -/
lemma eucSq_add_smul {m : ℕ} (x v : Fin m → ℝ) (t : ℝ) :
    eucSq (x + t • v) = eucSq x + 2 * t * (∑ i, x i * v i) + t ^ 2 * eucSq v := by
  have hB : (∑ i : Fin m, 2 * t * (x i * v i)) = 2 * t * ∑ i, x i * v i :=
    (Finset.mul_sum Finset.univ (fun i => x i * v i) (2 * t)).symm
  have hC : (∑ i : Fin m, t ^ 2 * v i ^ 2) = t ^ 2 * ∑ i, v i ^ 2 :=
    (Finset.mul_sum Finset.univ (fun i => v i ^ 2) (t ^ 2)).symm
  have hsum : eucSq (x + t • v)
      = ∑ i : Fin m, (x i ^ 2 + 2 * t * (x i * v i) + t ^ 2 * v i ^ 2) := by
    simp only [eucSq]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hB, hC]
  simp only [eucSq]

/-! ## 2. The one-sided derivative bound -/

/-- If `ψ` has Fréchet derivative `S` at `x` and is `≤ ψ x` along the ray `x + t·v` for all small
`t > 0`, then `S v ≤ 0`.  This is the one-sided Fermat condition used at a maximiser. -/
theorem fderiv_apply_nonpos_of_eventually_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → ℝ} {x v : E} {S : E →L[ℝ] ℝ} (hS : HasFDerivAt ψ S x)
    (h : ∀ᶠ t in 𝓝[Set.Ioi 0] (0 : ℝ), ψ (x + t • v) ≤ ψ x) : S v ≤ 0 := by
  have hcurve : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    simpa using h1.const_add x
  have hcomp : HasDerivAt (fun t : ℝ => ψ (x + t • v)) (S v) 0 := by
    have hS' : HasFDerivAt ψ S (x + (0 : ℝ) • v) := by simpa using hS
    have h2 := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hS' hcurve
    simpa only [Function.comp_def] using h2
  refine le_of_tendsto hcomp.tendsto_slope_zero_right ?_
  filter_upwards [h, self_mem_nhdsWithin] with t ht hpos
  have hgoal : t⁻¹ • (ψ (x + t • v) - ψ x) ≤ 0 := by
    rw [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hpos.le) (sub_nonpos.mpr ht)
  simpa using hgoal

/-! ## 3. The maximiser on a Euclidean ball -/

/-- At a maximum of `ψ` on the Euclidean ball cut by the inequalities (with all inequalities
strict at the maximiser), the radial-orthogonality defect `rotSq ψ` vanishes. -/
theorem rotSq_zero_of_isMaxOn_eucBall {m l : ℕ} (ψ : (Fin m → ℝ) → ℝ)
    (g : Fin l → (Fin m → ℝ) → ℝ) {R : ℝ} {x : Fin m → ℝ}
    (hx : eucSq x ≤ R ^ 2) (hxg : ∀ j, 0 < g j x) (hgc : ∀ j, ContinuousAt (g j) x)
    (hmax : ∀ y, eucSq y ≤ R ^ 2 → (∀ j, 0 ≤ g j y) → ψ y ≤ ψ x)
    (hψ : AnalyticAt ℝ ψ x) : rotSq ψ x = 0 := by
  refine rotSq_eq_zero_of_sum_mul_neg ψ fun v hv => ?_
  have hder : HasFDerivAt ψ (fderiv ℝ ψ x) x := hψ.hasStrictFDerivAt.hasFDerivAt
  refine fderiv_apply_nonpos_of_eventually_le hder ?_
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    simp at hv
  have hvpos : 0 < eucSq v :=
    lt_of_le_of_ne (eucSq_nonneg v) (Ne.symm fun h => hvne (eucSq_eq_zero h))
  -- the Euclidean constraint is satisfied for all small positive `t`
  have hquad : ∀ᶠ t in 𝓝[Set.Ioi 0] (0 : ℝ), eucSq (x + t • v) ≤ R ^ 2 := by
    set t₀ : ℝ := -(2 * (∑ i, x i * v i)) / eucSq v with ht₀
    have ht₀pos : 0 < t₀ := by
      rw [ht₀]
      exact div_pos (by linarith) hvpos
    have hstep : ∀ t : ℝ, 0 < t → t < t₀ → eucSq (x + t • v) ≤ R ^ 2 := by
      intro t ht0 htlt
      rw [eucSq_add_smul]
      have h3 : t * eucSq v < -(2 * (∑ i, x i * v i)) := by
        rw [ht₀] at htlt
        exact (lt_div_iff₀ hvpos).mp htlt
      have h4 : 2 * t * (∑ i, x i * v i) + t ^ 2 * eucSq v < 0 := by
        have h5 : 2 * t * (∑ i, x i * v i) + t ^ 2 * eucSq v
            = t * (2 * (∑ i, x i * v i) + t * eucSq v) := by ring
        rw [h5]
        exact mul_neg_of_pos_of_neg ht0 (by linarith)
      linarith
    have hmem : Set.Ioo (0 : ℝ) t₀ ∈ 𝓝[Set.Ioi 0] (0 : ℝ) :=
      inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht₀pos))
    exact Filter.mem_of_superset hmem fun t ht => hstep t ht.1 ht.2
  -- the inequality constraints stay satisfied for all small positive `t`
  have hg_ev : ∀ᶠ t in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ j, 0 ≤ g j (x + t • v) := by
    rw [Filter.eventually_all]
    intro j
    have htend : Tendsto (fun t : ℝ => x + t • v) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 x) := by
      have hsmul : Tendsto (fun t : ℝ => t • v) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) • v)) :=
        Tendsto.smul (tendsto_id (x := 𝓝 (0 : ℝ)))
          (tendsto_const_nhds (x := v) (f := 𝓝 (0 : ℝ)))
      have h0 : Tendsto (fun t : ℝ => x + t • v) (𝓝 (0 : ℝ)) (𝓝 (x + (0 : ℝ) • v)) :=
        Tendsto.add (tendsto_const_nhds (x := x) (f := 𝓝 (0 : ℝ))) hsmul
      simpa using h0.mono_left nhdsWithin_le_nhds
    have h1 : ∀ᶠ y in 𝓝 x, 0 < g j y :=
      (hgc j).preimage_mem_nhds (isOpen_Ioi.mem_nhds (hxg j))
    exact (htend.eventually h1).mono fun t ht => le_of_lt ht
  filter_upwards [hquad, hg_ev] with t ht1 ht2
  exact hmax (x + t • v) ht1 ht2

/-! ## 4. The closure statement used by the induction step -/

/-- **Maximiser form of the inequality-only case.**  If `ψ` is analytic near `0`, the inequalities
are continuous near `0`, `ψ > 0` on `Y = {∀ j, 0 < gⱼ}` (near `0`) and `ψ > 0` forces all the
inequalities to be strict, then the zero set of `rotSq ψ` still accumulates at `0` inside `Y`. -/
theorem closure_rotSq {m l : ℕ} (ψ : (Fin m → ℝ) → ℝ) (g : Fin l → (Fin m → ℝ) → ℝ)
    (hψ : ∀ᶠ x in nhds (0 : Fin m → ℝ), AnalyticAt ℝ ψ x)
    (hg : ∀ᶠ x in nhds (0 : Fin m → ℝ), ∀ j, ContinuousAt (g j) x)
    (hkills : ∀ x, (∀ j, 0 ≤ g j x) → 0 < ψ x → ∀ j, 0 < g j x)
    (hposY : ∀ᶠ x in nhds (0 : Fin m → ℝ), (∀ j, 0 < g j x) → 0 < ψ x)
    (hcl : (0 : Fin m → ℝ) ∈ closure {x : Fin m → ℝ | ∀ j, 0 < g j x}) :
    (0 : Fin m → ℝ) ∈ closure ({x : Fin m → ℝ | rotSq ψ x = 0} ∩
      {x : Fin m → ℝ | ∀ j, 0 < g j x}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hψ
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hg
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.eventually_nhds_iff.mp hposY
  set δ : ℝ := min δ₁ (min δ₂ δ₃) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδ₁pos (lt_min hδ₂pos hδ₃pos)
  have hδ₁le : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδ₂le : δ ≤ δ₂ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₃le : δ ≤ δ₃ := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hden : 0 < Real.sqrt (m : ℝ) + 1 := by linarith [Real.sqrt_nonneg (m : ℝ)]
  -- a point of `Y` very close to `0`
  obtain ⟨y, hyY, hydist⟩ := Metric.mem_closure_iff.mp hcl
    (min δ ε / (Real.sqrt (m : ℝ) + 1)) (div_pos (lt_min hδpos hε) hden)
  have hynorm : ‖y‖ < min δ ε / (Real.sqrt (m : ℝ) + 1) := by
    simpa [dist_eq_norm] using hydist
  set R : ℝ := Real.sqrt (eucSq y) with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hRle : R < min δ ε := by
    have h1 : eucSq y ≤ (m : ℝ) * ‖y‖ ^ 2 := eucSq_le_card_mul_norm_sq y
    have h2 : Real.sqrt ((m : ℝ) * ‖y‖ ^ 2) = Real.sqrt (m : ℝ) * ‖y‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq (norm_nonneg y)]
    have h3 : Real.sqrt (m : ℝ) * ‖y‖ < min δ ε := by
      have h5 : ‖y‖ * (Real.sqrt (m : ℝ) + 1) < min δ ε := (lt_div_iff₀ hden).mp hynorm
      calc Real.sqrt (m : ℝ) * ‖y‖ ≤ (Real.sqrt (m : ℝ) + 1) * ‖y‖ :=
            mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_nonneg (m : ℝ)])
              (norm_nonneg y)
        _ = ‖y‖ * (Real.sqrt (m : ℝ) + 1) := by ring
        _ < min δ ε := h5
    have h4 : R ≤ Real.sqrt (m : ℝ) * ‖y‖ := by
      rw [hRdef, ← h2]
      exact Real.sqrt_le_sqrt h1
    linarith
  have hRmin : R < δ := lt_of_lt_of_le hRle (min_le_left _ _)
  have hRε : R < ε := lt_of_lt_of_le hRle (min_le_right _ _)
  let K : Set (Fin m → ℝ) := ({x : Fin m → ℝ | eucSq x ≤ R ^ 2}) ∩
    (Metric.closedBall (0 : Fin m → ℝ) R ∩ ⋂ j : Fin l, {x : Fin m → ℝ | 0 ≤ g j x})
  have hball_closed : IsClosed (Metric.closedBall (0 : Fin m → ℝ) R) := Metric.isClosed_closedBall
  have heuc_closed : IsClosed ({x : Fin m → ℝ | eucSq x ≤ R ^ 2}) :=
    isClosed_Iic.preimage continuous_eucSq
  have hclosed : IsClosed K := by
    refine heuc_closed.inter ?_
    rw [← closure_subset_iff_isClosed]
    intro z hz
    have hzball : z ∈ Metric.closedBall (0 : Fin m → ℝ) R :=
      hball_closed.closure_subset (closure_mono (fun x hx => hx.1) hz)
    refine ⟨hzball, ?_⟩
    refine Set.mem_iInter.mpr fun j => ?_
    have hsubset : (Metric.closedBall (0 : Fin m → ℝ) R
        ∩ ⋂ j : Fin l, {x : Fin m → ℝ | 0 ≤ g j x})
        ⊆ (Metric.closedBall (0 : Fin m → ℝ) R ∩ {x : Fin m → ℝ | 0 ≤ g j x}) :=
      fun x hx => ⟨hx.1, Set.mem_iInter.mp hx.2 j⟩
    have hzsub : z ∈ closure (Metric.closedBall (0 : Fin m → ℝ) R
        ∩ {x : Fin m → ℝ | 0 ≤ g j x}) :=
      closure_mono hsubset hz
    have hzj : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
    have hcont : ContinuousAt (g j) z :=
      hδ₂ (y := z)
        (by simpa [dist_eq_norm] using lt_of_lt_of_le (lt_of_le_of_lt hzj hRmin) hδ₂le) j
    have htend : Tendsto (g j) (𝓝[Metric.closedBall (0 : Fin m → ℝ) R
        ∩ {x : Fin m → ℝ | 0 ≤ g j x}] z) (𝓝 (g j z)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ y in 𝓝[Metric.closedBall (0 : Fin m → ℝ) R
        ∩ {x : Fin m → ℝ | 0 ≤ g j x}] z, 0 ≤ g j y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hy.2
    haveI : (𝓝[Metric.closedBall (0 : Fin m → ℝ) R
        ∩ {x : Fin m → ℝ | 0 ≤ g j x}] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hzsub
    exact ge_of_tendsto htend hev
  have hKcpt : IsCompact K :=
    (isCompact_closedBall (0 : Fin m → ℝ) R).of_isClosed_subset hclosed
      (fun x hx => hx.2.1)
  have hKnorm : ∀ x ∈ K, ‖x‖ < δ := fun x hx => by
    have h1 : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2.1
    exact lt_of_le_of_lt h1 hRmin
  have hyY' : ∀ j : Fin l, 0 < g j y := fun j => hyY j
  have hyK : y ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · show eucSq y ≤ R ^ 2
      rw [hRdef]
      exact le_of_eq (Real.sq_sqrt (eucSq_nonneg y)).symm
    · show y ∈ Metric.closedBall (0 : Fin m → ℝ) R
      rw [hRdef, Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_le_sqrt_eucSq y
    · refine Set.mem_iInter.mpr fun j => ?_
      exact le_of_lt (hyY' j)
  have hψcont : ContinuousOn ψ K := fun x hx =>
    ((hδ₁ (y := x)
      (by simpa [dist_eq_norm] using lt_of_lt_of_le (hKnorm x hx) hδ₁le)).continuousAt).continuousWithinAt
  obtain ⟨x, hxK, hxmax⟩ := hKcpt.exists_isMaxOn ⟨y, hyK⟩ hψcont
  have hxnorm : ‖x‖ < δ := hKnorm x hxK
  have hgan : AnalyticAt ℝ ψ x :=
    hδ₁ (y := x) (by simpa [dist_eq_norm] using lt_of_lt_of_le hxnorm hδ₁le)
  have hgcx : ∀ j, ContinuousAt (g j) x :=
    hδ₂ (y := x) (by simpa [dist_eq_norm] using lt_of_lt_of_le hxnorm hδ₂le)
  have hψypos : 0 < ψ y :=
    hδ₃ (y := y) (by
      have hyle : ‖y‖ < δ := by
        refine lt_of_le_of_lt ?_ hRmin
        rw [hRdef]
        exact norm_le_sqrt_eucSq y
      simpa [dist_eq_norm] using lt_of_lt_of_le hyle hδ₃le) hyY'
  have hψxpos : 0 < ψ x := lt_of_lt_of_le hψypos ((isMaxOn_iff.mp hxmax) y hyK)
  have hxge : ∀ j, 0 ≤ g j x := fun j => Set.mem_iInter.mp hxK.2.2 j
  have hxg : ∀ j, 0 < g j x := hkills x hxge hψxpos
  have hmax : ∀ z, eucSq z ≤ R ^ 2 → (∀ j, 0 ≤ g j z) → ψ z ≤ ψ x := by
    intro z hz hzge
    have hzball : z ∈ Metric.closedBall (0 : Fin m → ℝ) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact norm_le_of_eucSq_le hRnn hz
    exact (isMaxOn_iff.mp hxmax) z ⟨hz, hzball, Set.mem_iInter.mpr hzge⟩
  have hcrit : rotSq ψ x = 0 :=
    rotSq_zero_of_isMaxOn_eucBall ψ g hxK.1 hxg hgcx hmax hgan
  refine ⟨x, ⟨hcrit, hxg⟩, ?_⟩
  rw [dist_eq_norm, zero_sub, norm_neg]
  exact lt_of_le_of_lt
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hxK.2.1) hRε

end Work.WilC4aCS
