import Mathlib
import Submission.Work.ManifoldParity.graph_tangent_field

/-!
# A smooth field parallel to a continuous field, from local data

Given a compact set `K ⊆ ℝⁿ`, a continuous nowhere-vanishing `U₀` on `K`, and the hypothesis that
*locally* (near every point of `K`) there is a smooth field `W` which is parallel to `U₀` on `K`,
we build a smooth, compactly supported field `V` on `ℝⁿ` which is nowhere zero on `K` and parallel
to `U₀` at every point of `K`.

The construction is a smooth partition-of-unity gluing of the local fields, with the signs chosen
so that every summand is a *positive* multiple of `U₀` on the region where its cut-off is non-zero.
The pointwise sign of `⟪U₀, W⟫` is locally constant on `K` (both maps are continuous there), so at
each point `p` of `K` there is a constant sign `σ p ∈ {±1}` which is correct on a whole ball around
`p`; taking one such ball around each point and a finite subcover, and cut-off bumps supported in
these balls, makes the glued field non-vanishing on `K`.

-/

namespace Work.ManifoldParity

open scoped Topology InnerProductSpace
open Set Metric

theorem exists_parallel_smooth_field {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (U₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hU₀c : ContinuousOn U₀ K) (hU₀ne : ∀ x ∈ K, U₀ x ≠ 0)
    (hloc : ∀ x ∈ K, ∃ (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (U : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
        ∀ y ∈ K ∩ U, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y) :
    ∃ V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧ HasCompactSupport V ∧ (∀ x ∈ K, V x ≠ 0) ∧
      (∀ x ∈ K, ∃ c : ℝ, c ≠ 0 ∧ V x = c • U₀ x) := by
  classical
  -- ## Step 1: at every point of `K` pick local data, a ball and a locally constant sign.
  have hdata : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K},
      ∃ (W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (U : Set (EuclideanSpace ℝ (Fin n))) (ρ σ : ℝ),
        0 < ρ ∧ IsOpen U ∧ p.1 ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
        (∀ y ∈ K ∩ U, ∃ c : ℝ, c ≠ 0 ∧ W y = c • U₀ y) ∧
        Metric.closedBall p.1 (2 * ρ) ⊆ U ∧
        (σ = 1 ∨ σ = -1) ∧
        (∀ z ∈ K, dist z p.1 ≤ 2 * ρ → 0 < σ * ⟪U₀ z, W z⟫_ℝ) := by
    intro p
    obtain ⟨W, U, hUopen, hpU, hWsmooth, hpar⟩ := hloc p.1 p.2
    obtain ⟨c₀, hc₀, hWp⟩ := hpar p.1 ⟨p.2, hpU⟩
    have hU0p : U₀ p.1 ≠ 0 := hU₀ne p.1 p.2
    have hinnerp : (0 : ℝ) < ⟪U₀ p.1, U₀ p.1⟫_ℝ := real_inner_self_pos.mpr hU0p
    have hgne : ⟪U₀ p.1, W p.1⟫_ℝ ≠ 0 := by
      rw [hWp, real_inner_smul_right]
      exact mul_ne_zero hc₀ (ne_of_gt hinnerp)
    have hcont : ContinuousOn (fun z => ⟪U₀ z, W z⟫_ℝ) K :=
      hU₀c.inner hWsmooth.continuous.continuousOn
    obtain ⟨δ, hδ, hsign⟩ := eventually_sign_eq K hcont p.2 hgne
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen p.1 hpU
    refine ⟨W, U, min (ε / 4) (δ / 4),
      if 0 < ⟪U₀ p.1, W p.1⟫_ℝ then 1 else -1,
      lt_min (by linarith) (by linarith), hUopen, hpU, hWsmooth, hpar, ?_, ?_, ?_⟩
    · intro z hz
      refine hεU ?_
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
  choose W U ρ σ hρ hUopen hpU hWsmooth hpar hball hσ hsign using hdata
  -- ## Step 2: finitely many of these balls cover `K`.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} =>
      Metric.ball p.1 (ρ p)) (fun p => Metric.isOpen_ball) (fun x hx => by
        refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        exact Metric.mem_ball_self (hρ ⟨x, hx⟩))
  -- ## Step 3: cut-off bumps and the glued field.
  let bump : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}, ContDiffBump p.1 := fun p =>
    ⟨ρ p, 2 * ρ p, hρ p, by linarith [hρ p]⟩
  let χ : ∀ p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K},
      EuclideanSpace ℝ (Fin n) → ℝ := fun p => (bump p : EuclideanSpace ℝ (Fin n) → ℝ)
  let V₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => ∑ p ∈ t, χ p z • (σ p • W p z)
  have hV₀smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V₀ := by
    refine ContDiff.sum (f := fun (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K})
      (z : EuclideanSpace ℝ (Fin n)) => χ p z • (σ p • W p z)) fun p hp => ?_
    refine ContDiff.smul ((bump p).contDiff (n := ⊤)) ?_
    exact ContDiff.const_smul (σ p) (hWsmooth p)
  -- ## Step 4: at every `x ∈ K`, `V₀ x` is a *positive* multiple of `U₀ x`.
  have hmultiples : ∀ x ∈ K, ∃ a : ℝ, 0 < a ∧ V₀ x = a • U₀ x := by
    intro x hx
    have key : ∀ p ∈ t, ∃ μ : ℝ, 0 ≤ μ ∧ (χ p x ≠ 0 → 0 < μ) ∧
        χ p x • (σ p • W p x) = (χ p x * μ) • U₀ x := by
      intro p hp
      by_cases hχ : χ p x = 0
      · exact ⟨0, le_refl 0, fun h => (h hχ).elim, by rw [hχ, zero_mul, zero_smul, zero_smul]⟩
      · have hxts : x ∈ tsupport (χ p) := subset_tsupport _ (Function.mem_support.mpr hχ)
        rw [show tsupport (χ p) = Metric.closedBall p.1 (2 * ρ p) from
          ContDiffBump.tsupport_eq (bump p)] at hxts
        have hxd : dist x p.1 ≤ 2 * ρ p := Metric.mem_closedBall.mp hxts
        have hxU : x ∈ U p := hball p (Metric.mem_closedBall.mpr hxd)
        obtain ⟨c, hc, hparx⟩ := hpar p x ⟨hx, hxU⟩
        have hinnerU : (0 : ℝ) < ⟪U₀ x, U₀ x⟫_ℝ := real_inner_self_pos.mpr (hU₀ne x hx)
        have hsc : 0 < σ p * c := by
          have h1 : 0 < σ p * (c * ⟪U₀ x, U₀ x⟫_ℝ) := by
            have h0 := hsign p x hx hxd
            rwa [hparx, real_inner_smul_right] at h0
          have h2 : 0 < (σ p * c) * ⟪U₀ x, U₀ x⟫_ℝ := by
            rwa [← mul_assoc] at h1
          exact pos_of_mul_pos_left h2 hinnerU.le
        refine ⟨σ p * c, hsc.le, fun _ => hsc, ?_⟩
        rw [hparx, smul_smul, smul_smul, mul_assoc]
    choose μ hμ hμpos hμeq using key
    set M : {x : EuclideanSpace ℝ (Fin n) // x ∈ K} → ℝ :=
      fun p => if hp : p ∈ t then μ p hp else 0 with hM
    have hMapp : ∀ (p : {x : EuclideanSpace ℝ (Fin n) // x ∈ K}) (hp : p ∈ t),
        M p = μ p hp := fun p hp => by simp only [hM, dif_pos hp]
    have hxcover : x ∈ ⋃ p ∈ t, Metric.ball p.1 (ρ p) := ht hx
    simp only [mem_iUnion, exists_prop] at hxcover
    obtain ⟨p₀, hp₀t, hp₀x⟩ := hxcover
    have hχp₀ : χ p₀ x = 1 := by
      refine ContDiffBump.one_of_mem_closedBall (bump p₀) ?_
      exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp hp₀x).le
    have h1 : ∀ p ∈ t, χ p x • (σ p • W p x) = (χ p x * M p) • U₀ x := by
      intro p hp
      rw [hMapp p hp]
      exact hμeq p hp
    have hV₀x : V₀ x = (∑ p ∈ t, χ p x * M p) • U₀ x := by
      show (∑ p ∈ t, χ p x • (σ p • W p x)) = (∑ p ∈ t, χ p x * M p) • U₀ x
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
  refine ⟨β • V₀, ContDiff.smul (βb.contDiff (n := ⊤)) hV₀smooth, hsupp, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    show β x • V₀ x ≠ 0
    rw [hβone x hx, one_smul, haeq]
    exact smul_ne_zero (ne_of_gt ha) (hU₀ne x hx)
  · intro x hx
    obtain ⟨a, ha, haeq⟩ := hmultiples x hx
    exact ⟨a, ne_of_gt ha, by show β x • V₀ x = a • U₀ x; rw [hβone x hx, one_smul, haeq]⟩

end Work.ManifoldParity
