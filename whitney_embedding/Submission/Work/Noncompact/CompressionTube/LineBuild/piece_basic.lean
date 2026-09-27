import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.ProperLine.raySmooth
import Submission.Work.Noncompact.ProperLine.orthogonalDirection
import Submission.Work.Noncompact.ProperLine.contMDiffAt_glue_flat
import Submission.Work.Noncompact.ProperLine.rayHalfOpen
import Submission.Work.Noncompact.ProperLine.flatGlue2
import Submission.Work.Whitney.SmoothArc.Arc
import Submission.Work.Noncompact.Routing.arcs_removal

/-!
# The basic pieces of the line construction

Raw material for `Work.Noncompact.CompressionTube.exists_smoothProperLine_of_nested`, built in the
import cone of `Work.Noncompact.Routing.arcs_removal` (the cone of the canal construction).

* `nc_exists_orthogonal`: a unit vector orthogonal to a given unit vector (`n ≥ 2`);
* `nc_chartExpr_smooth`: the chart transition `u ↦ extChartAt q (c.symm u)` is `C^∞` near `u₀`;
* `nc_chartRadius_left` / `nc_chartRadius_right`: the *access* and *arrival* straight chart radii,
  `C^∞`, constant on one side of the outer parameter, flat there (in the chart at the outer
  point); these are the two ends of every piece;
* `nc_access_avoids_germ`: the access radius in a direction orthogonal to a straight germ meets
  the germ only at the base point.
-/

open Set Metric Topology
open scoped Manifold ContDiff Pointwise

namespace Work.Noncompact.CompressionTube

/-- **A unit vector orthogonal to a given unit vector** (`n ≥ 2`). -/
theorem nc_exists_orthogonal {n : ℕ} (hn : 2 ≤ n) {w : EuclideanSpace ℝ (Fin n)}
    (hw : ‖w‖ = 1) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧ inner ℝ v w = 0 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; norm_num at hw
  obtain ⟨v₀, hv₀, hin⟩ :=
    Work.Noncompact.ProperLine.exists_ne_zero_inner_eq_zero (n := n) hn hw0
  refine ⟨(‖v₀‖)⁻¹ • v₀, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v₀),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀)]
  · rw [real_inner_smul_left, hin, mul_zero]

/-- **The chart transition at a point is smooth near the point.** -/
theorem nc_chartExpr_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target)
    {q : M} {u₀ : EuclideanSpace ℝ (Fin n)} (hu₀tgt : u₀ ∈ c.target)
    (hu₀ : c.symm u₀ = q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ smoothOrder
      (fun u : EuclideanSpace ℝ (Fin n) => extChartAt (MC n) q (c.symm u))
      (Metric.ball u₀ ρ) := by
  have hcont : ContinuousAt (⇑c.symm) u₀ :=
    hcsymm.continuousOn.continuousAt (c.open_target.mem_nhds hu₀tgt)
  have hsrc : (extChartAt (MC n) q).source ∈ 𝓝 q := extChartAt_source_mem_nhds q
  have hsrc' : (extChartAt (MC n) q).source ∈ 𝓝 (c.symm u₀) := hu₀ ▸ hsrc
  have hnbhd : c.target ∩ c.symm ⁻¹' (extChartAt (MC n) q).source ∈ 𝓝 u₀ :=
    Filter.inter_mem (c.open_target.mem_nhds hu₀tgt) (hcont.preimage_mem_nhds hsrc')
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  refine ⟨ρ, hρ, ?_⟩
  have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (extChartAt (MC n) q)
      (extChartAt (MC n) q).source := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := MC n) (x := q) (n := smoothOrder)
  have h2 : ContMDiffOn (MC n) (MC n) smoothOrder (fun u : EuclideanSpace ℝ (Fin n) => c.symm u)
      (Metric.ball u₀ ρ) :=
    hcsymm.mono (fun u hu => (hρsub hu).1)
  have h3 : ContMDiffOn (MC n) (MC n) smoothOrder
      (fun u : EuclideanSpace ℝ (Fin n) => extChartAt (MC n) q (c.symm u)) (Metric.ball u₀ ρ) :=
    h1.comp h2 (fun u hu => (hρsub hu).2)
  exact h3.contDiffOn

/-- **The access radius** `t ↦ c.symm ((s₀ * smoothTransition (1 + t)) • v)`: `C^∞`, constant for
`t ≥ 0` (at the outer point `c.symm (s₀ • v)`), equal to `c.symm 0` at `t = -1`, and flat at `t = 0`
from the left in the chart at the outer point. -/
theorem nc_chartRadius_left {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target)
    {s₀ : ℝ} (hs₀ : 0 ≤ s₀) (htgt : Metric.closedBall 0 s₀ ⊆ c.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) :
    ContMDiff MCreal (MC n) smoothOrder
        (fun t : ℝ => c.symm ((s₀ * Real.smoothTransition (1 + t)) • v)) ∧
      (∀ t : ℝ, 0 ≤ t →
        c.symm ((s₀ * Real.smoothTransition (1 + t)) • v) = c.symm (s₀ • v)) ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun t : ℝ => extChartAt (MC n) (c.symm (s₀ • v))
          (c.symm ((s₀ * Real.smoothTransition (1 + t)) • v))) (Set.Iic 0) 0 = 0) := by
  have hbound : ∀ t : ℝ, ‖(s₀ * Real.smoothTransition (1 + t)) • v‖ ≤ s₀ := by
    intro t
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hs₀ (Real.smoothTransition.nonneg _))]
    exact mul_le_of_le_one_right hs₀ (Real.smoothTransition.le_one _)
  have htgt' : ∀ t : ℝ, (s₀ * Real.smoothTransition (1 + t)) • v ∈ c.target := fun t =>
    htgt (by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound t)
  have hφ : ContMDiff MCreal (MC n) smoothOrder
      (fun t : ℝ => (s₀ * Real.smoothTransition (1 + t)) • v) := by
    rw [contMDiff_iff_contDiff]
    exact (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.add contDiff_id))).smul contDiff_const
  have hmem₀ : s₀ • v ∈ c.target := htgt (by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs₀])
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (hcsymm.contMDiffAt (c.open_target.mem_nhds (htgt' t))).comp t hφ.contMDiffAt
  · intro t ht
    rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  · intro k hk
    have hψsm : ContDiffOn ℝ smoothOrder
        (fun t : ℝ => s₀ * Real.smoothTransition (1 + t)) (Set.Iic 0) :=
      (contDiff_const.mul (Real.smoothTransition.contDiff.comp
        (contDiff_const.add contDiff_id))).contDiffOn
    have hψ0 : s₀ * Real.smoothTransition (1 + 0) = s₀ := by
      rw [show (1:ℝ) + 0 = 1 from by norm_num, Real.smoothTransition.one, mul_one]
    have hψ : ∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun t : ℝ => s₀ * Real.smoothTransition (1 + t)) (Set.Iic 0) 0 = 0 := by
      intro k hk
      rw [iteratedDerivWithin_const_mul_field (s := Set.Iic 0) (x := 0) s₀
        (fun t : ℝ => Real.smoothTransition (1 + t))]
      have h := congrFun (iteratedDerivWithin_comp_const_add (𝕜 := ℝ)
        (f := Real.smoothTransition) (c := 1) (s := Set.Iic (0:ℝ)) (n := k)) 0
      have hset : (1:ℝ) +ᵥ Set.Iic (0:ℝ) = Set.Iic 1 := by
        ext u
        simp only [Set.mem_vadd_set, Set.mem_Iic, vadd_eq_add]
        constructor
        · rintro ⟨t, ht, htu⟩; linarith
        · intro hu; exact ⟨u - 1, by linarith, by ring⟩
      have hderiv : iteratedDerivWithin k (fun t : ℝ => Real.smoothTransition (1 + t))
          (Set.Iic (0:ℝ)) 0 = iteratedDerivWithin k Real.smoothTransition (Set.Iic (1:ℝ)) 1 := by
        rw [h, hset, add_zero]
      rw [hderiv, Work.Noncompact.ProperLine.smoothTransition_flat.2 k hk, mul_zero]
    obtain ⟨ρ, hρ, hH⟩ := nc_chartExpr_smooth (n := n) (M := M) (c := c) hcsymm hmem₀ rfl
    have hHlin : ContDiffOn ℝ smoothOrder
        (fun x : ℝ => extChartAt (MC n) (c.symm (s₀ • v)) (c.symm (x • v)))
        (Metric.ball s₀ ρ) := by
      have hlin : ContDiffOn ℝ smoothOrder (fun x : ℝ => x • v) (Metric.ball s₀ ρ) :=
        (contDiff_id.smul contDiff_const).contDiffOn
      have hmaps : Set.MapsTo (fun x : ℝ => x • v) (Metric.ball s₀ ρ)
          (Metric.ball (s₀ • v) ρ) := by
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
        rw [← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
        exact hx
      exact hH.comp hlin hmaps
    have hH0 : ContDiffOn ℝ smoothOrder
        (fun x : ℝ => extChartAt (MC n) (c.symm (s₀ • v)) (c.symm (x • v)))
        (Metric.ball ((fun t : ℝ => s₀ * Real.smoothTransition (1 + t)) 0) ρ) := by
      simpa only [hψ0] using hHlin
    exact Work.Noncompact.ProperLine.flatComp_left (τ := 0)
      (ψ := fun t : ℝ => s₀ * Real.smoothTransition (1 + t))
      (H := fun x : ℝ => extChartAt (MC n) (c.symm (s₀ • v)) (c.symm (x • v)))
      hρ hψsm hψ hH0 k hk

/-- **The arrival radius** `s ↦ c.symm ((s₁ * (1 - smoothTransition s)) • v)`: `C^∞`, constant for
`s ≤ 0` (at the outer point `c.symm (s₁ • v)`), equal to `c.symm 0` at `s = 1`, and flat at `s = 0`
from the right in the chart at the outer point. -/
theorem nc_chartRadius_right {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target)
    {s₁ : ℝ} (hs₁ : 0 ≤ s₁) (htgt : Metric.closedBall 0 s₁ ⊆ c.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) :
    ContMDiff MCreal (MC n) smoothOrder
        (fun s : ℝ => c.symm ((s₁ * (1 - Real.smoothTransition s)) • v)) ∧
      (∀ s : ℝ, s ≤ 0 →
        c.symm ((s₁ * (1 - Real.smoothTransition s)) • v) = c.symm (s₁ • v)) ∧
      (c.symm ((s₁ * (1 - Real.smoothTransition 1)) • v) = c.symm 0) ∧
      (∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun s : ℝ => extChartAt (MC n) (c.symm (s₁ • v))
          (c.symm ((s₁ * (1 - Real.smoothTransition s)) • v))) (Set.Ici 0) 0 = 0) := by
  have hbound : ∀ s : ℝ, ‖(s₁ * (1 - Real.smoothTransition s)) • v‖ ≤ s₁ := by
    intro s
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg]
    · exact mul_le_of_le_one_right hs₁ (by linarith [Real.smoothTransition.nonneg s])
    · exact mul_nonneg hs₁ (by linarith [Real.smoothTransition.le_one s])
  have htgt' : ∀ s : ℝ, (s₁ * (1 - Real.smoothTransition s)) • v ∈ c.target := fun s =>
    htgt (by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound s)
  have hφ : ContMDiff MCreal (MC n) smoothOrder
      (fun s : ℝ => (s₁ * (1 - Real.smoothTransition s)) • v) := by
    rw [contMDiff_iff_contDiff]
    exact (contDiff_const.mul (contDiff_const.sub Real.smoothTransition.contDiff)).smul contDiff_const
  have hmem₁ : s₁ • v ∈ c.target := htgt (by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hs₁])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    exact (hcsymm.contMDiffAt (c.open_target.mem_nhds (htgt' s))).comp s hφ.contMDiffAt
  · intro s hs
    rw [Real.smoothTransition.zero_of_nonpos hs, sub_zero, mul_one]
  · rw [Real.smoothTransition.one, sub_self, mul_zero, zero_smul]
  · intro k hk
    have hψsm : ContDiffOn ℝ smoothOrder
        (fun s : ℝ => s₁ * (1 - Real.smoothTransition s)) (Set.Ici 0) :=
      (contDiff_const.mul (contDiff_const.sub Real.smoothTransition.contDiff)).contDiffOn
    have hψ : ∀ k : ℕ, 0 < k → iteratedDerivWithin k
        (fun s : ℝ => s₁ * (1 - Real.smoothTransition s)) (Set.Ici 0) 0 = 0 := by
      intro k hk
      rw [iteratedDerivWithin_const_mul_field (s := Set.Ici 0) (x := 0) s₁
        (fun s : ℝ => 1 - Real.smoothTransition s)]
      have h2 : iteratedDerivWithin k (fun s : ℝ => 1 - Real.smoothTransition s)
          (Set.Ici 0) 0 = 0 := by
        rw [iteratedDerivWithin_const_sub (hn := hk) (c := (1:ℝ))
          (f := Real.smoothTransition) (s := Set.Ici 0) (x := 0),
          iteratedDerivWithin_fun_neg, (Work.Noncompact.ProperLine.smoothTransition_flat.1 k hk),
          neg_zero]
      rw [h2, mul_zero]
    obtain ⟨ρ, hρ, hH⟩ := nc_chartExpr_smooth (n := n) (M := M) (c := c) hcsymm hmem₁ rfl
    have hHlin : ContDiffOn ℝ smoothOrder
        (fun x : ℝ => extChartAt (MC n) (c.symm (s₁ • v)) (c.symm (x • v)))
        (Metric.ball s₁ ρ) := by
      have hlin : ContDiffOn ℝ smoothOrder (fun x : ℝ => x • v) (Metric.ball s₁ ρ) :=
        (contDiff_id.smul contDiff_const).contDiffOn
      have hmaps : Set.MapsTo (fun x : ℝ => x • v) (Metric.ball s₁ ρ)
          (Metric.ball (s₁ • v) ρ) := by
        intro x hx
        rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
        rw [← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
        exact hx
      exact hH.comp hlin hmaps
    have hψ0 : s₁ * (1 - Real.smoothTransition 0) = s₁ := by
      rw [Real.smoothTransition.zero, sub_zero, mul_one]
    have hH0 : ContDiffOn ℝ smoothOrder
        (fun x : ℝ => extChartAt (MC n) (c.symm (s₁ • v)) (c.symm (x • v)))
        (Metric.ball ((fun s : ℝ => s₁ * (1 - Real.smoothTransition s)) 0) ρ) := by
      simpa only [hψ0] using hHlin
    exact Work.Noncompact.ProperLine.flatComp (τ := 0)
      (ψ := fun s : ℝ => s₁ * (1 - Real.smoothTransition s))
      (H := fun x : ℝ => extChartAt (MC n) (c.symm (s₁ • v)) (c.symm (x • v)))
      hρ hψsm hψ hH0 k hk

/-- **The access radius in a direction orthogonal to a straight germ meets the germ only at its
base point.**  If the part of `σsp` inside the chart ball of radius `δ` is the straight radius in
the direction `w`, and `v ⊥ w` is a unit vector, then the straight radius of length `ε < δ` in the
direction `v` meets `σsp` only at `z = σsp 0`. -/
theorem nc_access_avoids_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {σsp : ℝ → M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {z : M} {w v : EuclideanSpace ℝ (Fin n)} {δ ε : ℝ}
    (hσ0 : σsp 0 = z)
    (hσstraight : ∀ t ∈ Set.Ioc (0:ℝ) 1, σsp t ∈ c.symm '' Metric.ball 0 δ →
      ∃ s : ℝ, 0 < s ∧ s < δ ∧ σsp t = c.symm (s • w))
    (hcsrc : z ∈ c.source) (hcz : c z = 0)
    (hδtgt : Metric.closedBall 0 δ ⊆ c.target)
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hvw : inner ℝ v w = 0) (hε : ε < δ) :
    c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ s : ℝ, 0 ≤ s ∧ s ≤ ε ∧ y = s • v}
      ∩ (σsp '' Set.Ico (0:ℝ) 1) ⊆ {z} := by
  rintro x ⟨hxA, hxB⟩
  rw [Set.mem_singleton_iff]
  obtain ⟨y, hy, hyx⟩ := hxA
  obtain ⟨s, hs0, hsε, hyv⟩ := hy
  obtain ⟨t, ht, htx⟩ := hxB
  have hc0 : c.symm 0 = z := by rw [← hcz]; exact c.left_inv hcsrc
  -- the point of the germ equals the point of the access radius
  have hkey : σsp t = c.symm (s • v) := by rw [htx, ← hyv, ← hyx]
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · -- `t = 0`: the base point of the germ
    have hx_eq : x = c.symm (s • v) := by rw [← hyx, hyv]
    have hzz : c.symm (s • v) = z := by rw [← hkey, ← ht0, hσ0]
    rw [hx_eq, hzz]
  · -- `t > 0`: the germ is straight, so orthogonality forces `s = 0`
    have hs_ball : s • v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs0]
      linarith
    have hsp_ball : σsp t ∈ c.symm '' Metric.ball 0 δ :=
      ⟨s • v, hs_ball, hkey.symm⟩
    obtain ⟨s', hs'0, hs'δ, hs'eq⟩ := hσstraight t ⟨ht0, le_of_lt ht.2⟩ hsp_ball
    have hs_tgt : s • v ∈ c.target := hδtgt (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs0]
      linarith)
    have hs'_tgt : s' • w ∈ c.target := hδtgt (by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hw, mul_one, Real.norm_eq_abs,
        abs_of_pos hs'0]
      linarith)
    have heq : s • v = s' • w :=
      c.symm.injOn hs_tgt hs'_tgt (hkey.symm.trans hs'eq)
    have h1 : inner ℝ v (s • v) = s := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
      norm_num
    have h2 : inner ℝ v (s' • w) = 0 := by
      rw [real_inner_smul_right, hvw, mul_zero]
    have hs_eq : s = 0 := by
      rw [heq, h2] at h1
      exact h1.symm
    have hx_eq : x = c.symm (s • v) := by rw [← hyx, hyv]
    have hzz : c.symm (s • v) = z := by rw [hs_eq, zero_smul, hc0]
    rw [hx_eq, hzz]


/-- **A straight radius orthogonal to the germ misses the obstacle.**  If the obstacle `G` inside
the chart ball of radius `δ` is contained in the straight radius in the direction `w`, then the
straight radius of length `s ≤ δ` in an orthogonal unit direction `v` meets `G` only at the base
point of the chart. -/
theorem nc_seg_avoids_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {G : Set M} {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {z : M} {w v : EuclideanSpace ℝ (Fin n)} {δ s : ℝ}
    (hcsrc : z ∈ c.source) (hcz : c z = 0)
    (hδtgt : Metric.closedBall 0 δ ⊆ c.target)
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hvw : inner ℝ v w = 0)
    (hGerm : G ∩ (c.symm '' Metric.closedBall 0 δ)
      ⊆ c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, 0 ≤ t ∧ t ≤ δ ∧ y = t • w})
    (hs0 : 0 ≤ s) (hsδ : s ≤ δ) :
    G ∩ (c.symm '' {y : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = t • v})
      ⊆ {z} := by
  rintro x ⟨hxG, hxS⟩
  rw [Set.mem_singleton_iff]
  obtain ⟨y, hy, hyx⟩ := hxS
  obtain ⟨t, ht0, hts, hyv⟩ := hy
  have hc0 : c.symm 0 = z := by rw [← hcz]; exact c.left_inv hcsrc
  -- `x` lies in the chart ball, hence (by the germ hypothesis) on the `w`-radius
  have hx_ball : x ∈ c.symm '' Metric.closedBall 0 δ := by
    refine ⟨y, ?_, hyx⟩
    rw [hyv, Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    linarith
  obtain ⟨y', hy', hyx'⟩ := hGerm ⟨hxG, hx_ball⟩
  obtain ⟨t', ht'0, ht'δ, hy'v⟩ := hy'
  have hcc : c.symm (t • v) = c.symm (t' • w) := by rw [← hyv, hyx, ← hyx', hy'v]
  have ht_tgt : t • v ∈ c.target := hδtgt (by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    linarith)
  have ht'_tgt : t' • w ∈ c.target := hδtgt (by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hw, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ht'0]
    exact ht'δ)
  have heq : t • v = t' • w := c.symm.injOn ht_tgt ht'_tgt hcc
  have h1 : inner ℝ v (t • v) = t := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    norm_num
  have h2 : inner ℝ v (t' • w) = 0 := by
    rw [real_inner_smul_right, hvw, mul_zero]
  have ht_eq : t = 0 := by
    rw [heq, h2] at h1
    exact h1.symm
  rw [← hyx, hyv, ht_eq, zero_smul, hc0]

end Work.Noncompact.CompressionTube
