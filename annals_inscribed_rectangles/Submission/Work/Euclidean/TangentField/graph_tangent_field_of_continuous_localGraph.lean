import Mathlib
import Submission.Work.ManifoldParity.graph_tangent_field

namespace Work.Euclidean.TangentField

open scoped Topology InnerProductSpace
open Set Metric
open Work.ManifoldParity (chartField chartField_smooth chartField_ne_zero eventually_sign_eq)

/-- This is `Work.ManifoldParity.graph_tangent_field_of_continuous` with the local graph hypothesis
stated for the *ambient predicate* `P` (with `K ⊆ P`) instead of for `K`.  The proof is a verbatim
copy of the existing one with `IsGraphChart K i U η` replaced by the `P`-form condition (which is
the only thing the existing proof uses: a chart at each point of `K`, the sign of the inner product
with the chart tangent, and the parallelism hypothesis). -/
theorem graph_tangent_field_of_continuous_localGraph {n : ℕ}
    {P : EuclideanSpace ℝ (Fin n) → Prop} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKsub : ∀ x ∈ K, P x)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    (U₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hU₀cont : ContinuousOn U₀ K)
    (hU₀ne : ∀ x ∈ K, U₀ x ≠ 0)
    (hU₀par : ∀ x ∈ K, ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen V → x ∈ V → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ V, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ U₀ x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) :
    ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧ (∀ x ∈ K, V x ≠ 0) ∧
      (∀ x ∈ K, ∀ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U → x ∈ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧ V x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  classical
  -- ## Step 1: at every point of `K` pick a graph chart, a ball and a locally constant sign.
  have hdata : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K},
      ∃ (idx : Fin n) (S : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n))
        (ρ : ℝ) (σ : ℝ),
        0 < ρ ∧ IsOpen S ∧ p.1 ∈ S ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
        (∀ t, η t idx = 0) ∧
        (∀ y ∈ S, (P y ↔ y = (y idx) • EuclideanSpace.single idx (1:ℝ) + η (y idx))) ∧
        Metric.closedBall p.1 (2 * ρ) ⊆ S ∧
        (σ = 1 ∨ σ = -1) ∧
        (∀ z ∈ K, dist z p.1 ≤ 2 * ρ → 0 < σ * ⟪U₀ z, chartField idx η z⟫_ℝ) := by
    intro p
    obtain ⟨i, S, η, hSopen, hpS, hηsmooth, hη0, hgraph⟩ := hgra p.1 p.2
    obtain ⟨c, hc, hpar⟩ := hU₀par p.1 p.2 i S η hSopen hpS hηsmooth hη0 hgraph
    have hWne : chartField i η p.1 ≠ 0 :=
      chartField_ne_zero i η hη0 (hηsmooth.differentiable (by simp)).differentiableAt
    have hin : (0 : ℝ) < ⟪chartField i η p.1, chartField i η p.1⟫_ℝ := real_inner_self_pos.mpr hWne
    have hg_ne : ⟪U₀ p.1, chartField i η p.1⟫_ℝ ≠ 0 := by
      rw [hpar, real_inner_smul_left]
      exact mul_ne_zero hc (ne_of_gt hin)
    have hcont : ContinuousOn (fun z => ⟪U₀ z, chartField i η z⟫_ℝ) K :=
      hU₀cont.inner (chartField_smooth i η hηsmooth).continuous.continuousOn
    obtain ⟨δ, hδ, hsign⟩ := eventually_sign_eq K hcont p.2 hg_ne
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSopen p.1 hpS
    refine ⟨i, S, η, min (ε / 4) (δ / 4),
      if 0 < ⟪U₀ p.1, chartField i η p.1⟫_ℝ then 1 else -1,
      lt_min (by linarith) (by linarith), hSopen, hpS, hηsmooth, hη0, hgraph, ?_, ?_, ?_⟩
    · intro z hz
      refine hεS ?_
      have h2 : 2 * min (ε / 4) (δ / 4) ≤ ε / 2 := by
        have := min_le_left (ε / 4) (δ / 4); linarith
      have h3 : dist z p.1 ≤ 2 * min (ε / 4) (δ / 4) := Metric.mem_closedBall.mp hz
      have : dist z p.1 < ε := lt_of_le_of_lt (le_trans h3 h2) (by linarith)
      simpa [Metric.mem_ball, dist_comm] using this
    · split_ifs <;> simp
    · intro z hz hzd
      refine hsign z hz ?_
      have h2 : 2 * min (ε / 4) (δ / 4) < δ := by
        have := min_le_right (ε / 4) (δ / 4); linarith
      exact lt_of_le_of_lt hzd h2
  choose idx S η ρ σ hρ hSopen hpS hηsmooth hη0 hgraph hball hσ hsign using hdata
  -- ## Step 2: finitely many patches cover `K`.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} =>
      Metric.ball p.1 (ρ p)) (fun p => Metric.isOpen_ball) (fun x hx => by
        refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        exact Metric.mem_ball_self (hρ ⟨x, hx⟩))
  -- ## Step 3: the cut-off bumps and the local fields.
  let bump : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}, ContDiffBump p.1 := fun p =>
    ⟨ρ p, 2 * ρ p, hρ p, by linarith [hρ p]⟩
  let χ : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}, EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => (bump p : EuclideanSpace ℝ (Fin n) → ℝ)
  let Wf : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun p => chartField (idx p) (η p)
  let Ŵ : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) := fun p z => (⟪Wf p z, Wf p z⟫_ℝ)⁻¹ • Wf p z
  let V₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => ∑ p ∈ t, χ p z • (σ p • Ŵ p z)
  have hWfsmooth : ∀ p, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Wf p) := fun p =>
    chartField_smooth (idx p) (η p) (hηsmooth p)
  have hWfne : ∀ p z, Wf p z ≠ 0 := fun p z => by
    rw [show Wf p z = chartField (idx p) (η p) z from rfl]
    exact chartField_ne_zero (idx p) (η p) (hη0 p)
      ((hηsmooth p).differentiable (by simp)).differentiableAt
  have hV₀smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V₀ := by
    refine ContDiff.sum (f := fun (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K})
      (z : EuclideanSpace ℝ (Fin n)) => χ p z • (σ p • Ŵ p z)) fun p hp => ?_
    refine ContDiff.smul ((bump p).contDiff (n := ⊤)) ?_
    refine ContDiff.const_smul (σ p) ?_
    have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (⟪Wf p z, Wf p z⟫_ℝ)⁻¹) :=
      (ContDiff.inner ℝ (hWfsmooth p) (hWfsmooth p)).inv
        (fun z => inner_self_ne_zero.mpr (hWfne p z))
    exact hinv.smul (hWfsmooth p)
  -- ## Step 4: for `x ∈ K`, `V₀ x` is a *positive* multiple of `U₀ x`.
  have hmultiples : ∀ x ∈ K, ∃ a : ℝ, 0 < a ∧ V₀ x = a • U₀ x := by
    intro x hx
    have key : ∀ p ∈ t, ∃ μ : ℝ, 0 ≤ μ ∧ (χ p x ≠ 0 → 0 < μ) ∧
        χ p x • (σ p • Ŵ p x) = (χ p x * μ) • U₀ x := by
      intro p hp
      by_cases hχ : χ p x = 0
      · exact ⟨0, le_refl 0, fun h => (h hχ).elim, by rw [hχ, zero_mul, zero_smul, zero_smul]⟩
      · have hxts : x ∈ tsupport (χ p) := subset_tsupport _ (Function.mem_support.mpr hχ)
        rw [show tsupport (χ p) = Metric.closedBall p.1 (2 * ρ p) from
          ContDiffBump.tsupport_eq (bump p)] at hxts
        have hxd : dist x p.1 ≤ 2 * ρ p := Metric.mem_closedBall.mp hxts
        have hxS : x ∈ S p := hball p (Metric.mem_closedBall.mpr hxd)
        obtain ⟨c, hc, hpar⟩ := hU₀par x hx (idx p) (S p) (η p) (hSopen p) hxS
          (hηsmooth p) (hη0 p) (hgraph p)
        have hWne : Wf p x ≠ 0 := hWfne p x
        have hin : (0 : ℝ) < ⟪Wf p x, Wf p x⟫_ℝ := real_inner_self_pos.mpr hWne
        have hpos : 0 < σ p * (c * ⟪Wf p x, Wf p x⟫_ℝ) := by
          have h1 := hsign p x hx hxd
          rwa [show ⟪U₀ x, Wf p x⟫_ℝ = c * ⟪Wf p x, Wf p x⟫_ℝ by
            rw [show U₀ x = c • Wf p x from hpar, real_inner_smul_left]] at h1
        have hsc : 0 < σ p * c := by
          have h2 : 0 < (σ p * c) * ⟪Wf p x, Wf p x⟫_ℝ := by rw [mul_assoc]; exact hpos
          rcases mul_pos_iff.mp h2 with ⟨h, _⟩ | ⟨h, hlt⟩
          · exact h
          · exact absurd hlt (not_lt.mpr hin.le)
        have hcpos : 0 < σ p * c⁻¹ := by
          rcases lt_trichotomy c 0 with hneg | hzero | hpos
          · have hσ : σ p < 0 := by
              by_contra h
              push_neg at h
              exact absurd hsc (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos h hneg.le))
            exact mul_pos_of_neg_of_neg hσ (inv_neg''.mpr hneg)
          · exact (hc hzero).elim
          · have hσ : 0 < σ p := by
              by_contra h
              push_neg at h
              exact absurd hsc (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg h hpos.le))
            exact mul_pos hσ (inv_pos.mpr hpos)
        have hWs : Wf p x = c⁻¹ • U₀ x := by
          conv_rhs => rw [hpar]
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
          rfl
        refine ⟨(σ p * c⁻¹) * (⟪Wf p x, Wf p x⟫_ℝ)⁻¹, ?_, fun _ => ?_, ?_⟩
        · exact (mul_pos hcpos (inv_pos.mpr hin)).le
        · exact mul_pos hcpos (inv_pos.mpr hin)
        · simp only [Ŵ, hWs, smul_smul]
          congr 1
          ring
    choose μ hμ hμpos hμeq using key
    set M : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → ℝ :=
      fun p => if hp : p ∈ t then μ p hp else 0 with hM
    have hMapp : ∀ (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}) (hp : p ∈ t), M p = μ p hp :=
      fun p hp => by simp only [hM, dif_pos hp]
    have hxcover : x ∈ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := ht hx
    simp only [mem_iUnion, exists_prop] at hxcover
    obtain ⟨p₀, hp₀t, hp₀x⟩ := hxcover
    have hχp₀ : χ p₀ x = 1 := by
      refine ContDiffBump.one_of_mem_closedBall (bump p₀) ?_
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp₀x).le
    have h1 : ∀ p ∈ t, χ p x • (σ p • Ŵ p x) = (χ p x * M p) • U₀ x := by
      intro p hp
      rw [hMapp p hp]
      exact hμeq p hp
    have hV₀x : V₀ x = (∑ p ∈ t, χ p x * M p) • U₀ x := by
      show (∑ p ∈ t, χ p x • (σ p • Ŵ p x)) = (∑ p ∈ t, χ p x * M p) • U₀ x
      rw [Finset.sum_congr rfl h1, Finset.sum_smul]
    have hcoeff : 0 < ∑ p ∈ t, χ p x * M p := by
      refine Finset.sum_pos' (fun q hq => mul_nonneg (bump q).nonneg ?_) ⟨p₀, hp₀t, ?_⟩
      · rw [hMapp q hq]; exact hμ q hq
      · rw [hχp₀, one_mul, hMapp p₀ hp₀t]
        exact hμpos p₀ hp₀t (by rw [hχp₀]; norm_num)
    exact ⟨_, hcoeff, hV₀x⟩
  -- ## Step 5: the compactly supported global cut-off.
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hR' : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by simpa using hR x hx
  let βb : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨|R| + 3, |R| + 4, by positivity, by linarith⟩
  let β : EuclideanSpace ℝ (Fin n) → ℝ := (βb : EuclideanSpace ℝ (Fin n) → ℝ)
  have hβone : ∀ x ∈ K, β x = 1 := by
    intro x hx
    have h1 : dist x (0 : EuclideanSpace ℝ (Fin n)) ≤ |R| + 3 := by
      rw [dist_zero_right]
      have h2 : ‖x‖ ≤ |R| := le_trans (hR' x hx) (le_abs_self R)
      linarith
    refine ContDiffBump.one_of_mem_closedBall βb ?_
    simpa [Metric.mem_closedBall] using h1
  have hsupp : HasCompactSupport (β • V₀) := βb.hasCompactSupport.smul_right
  refine ⟨β • V₀, ContDiff.smul βb.contDiff hV₀smooth, hsupp, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    show β x • V₀ x ≠ 0
    rw [hβone x hx, one_smul, haeq]
    exact smul_ne_zero (ne_of_gt ha) (hU₀ne x hx)
  · intro x hx i V' η hV'open hxV' hηsmooth' hη0' hgraph'
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    obtain ⟨c, hc, hpar⟩ := hU₀par x hx i V' η hV'open hxV' hηsmooth' hη0' hgraph'
    refine ⟨a * c, mul_ne_zero (ne_of_gt ha) hc, ?_⟩
    show β x • V₀ x = (a * c) • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))
    rw [hβone x hx, one_smul, haeq, hpar, smul_smul]

end Work.Euclidean.TangentField
