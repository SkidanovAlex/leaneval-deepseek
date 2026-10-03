import Mathlib
import Submission.Work.Normal.Basic

namespace Work.Normal

open Filter Topology Metric

lemma exists_subseq_tendstoUniformlyOn_of_locallyBounded
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (v : ℕ → ℂ → ℂ) (hv : ∀ k, DifferentiableOn ℂ (v k) U)
    (hb : IsLocallyBoundedOn (Set.range v) U) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun k => v (σ k)) g atTop K := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδpos, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδ2 : 0 < δ / 2 := half_pos hδpos
  have hK'c : IsCompact (cthickening δ K) := hK.cthickening
  obtain ⟨M, hM⟩ := hb (cthickening δ K) hδU hK'c
  set M₀ := max M 0 with hM₀def
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hbdd : ∀ k z, z ∈ cthickening δ K → ‖v k z‖ ≤ M₀ :=
    fun k z hz => (hM _ ⟨k, rfl⟩ z hz).trans (le_max_left _ _)
  have hcont : ∀ k, ContinuousOn (v k) K := fun k => (hv k).continuousOn.mono hKU
  set w : ℕ → C(K, ℂ) := fun k => ⟨K.domRestrict (v k), (hcont k).domRestrict⟩ with hw
  set F : ℕ → BoundedContinuousFunction K ℂ :=
    fun k => BoundedContinuousFunction.mkOfCompact (w k) with hF
  set A : Set (BoundedContinuousFunction K ℂ) := Set.range F with hA
  have hdx : ∀ (k : ℕ) (x : K), (F k) x = v k x := by
    intro k x
    simp [F, w, Set.domRestrict]
  -- global Lipschitz bound for the family, on K
  have hLip : ∀ k (x y : K), dist (v k x) (v k y) ≤ (4 * M₀ / δ) * dist x y := by
    intro k x y
    have hD : dist x y = ‖(x : ℂ) - (y : ℂ)‖ := by rw [Subtype.dist_eq, dist_eq_norm]
    have hD' : ‖(y : ℂ) - (x : ℂ)‖ = dist x y := by rw [norm_sub_rev, hD]
    rcases le_or_gt (dist x y) (δ / 2) with hxy | hxy
    · -- near case: mean value inequality on the closed ball of radius δ/2 around x
      have hsub : closedBall (x : ℂ) (δ / 2) ⊆ U :=
        (closedBall_subset_closedBall (by linarith)).trans
          ((Metric.closedBall_subset_cthickening x.2 δ).trans hδU)
      have hderiv : ∀ z ∈ closedBall (x : ℂ) (δ / 2), ‖deriv (v k) z‖ ≤ 2 * M₀ / δ := by
        intro z hz
        have hzx : dist z (x : ℂ) ≤ δ / 2 := by rwa [mem_closedBall] at hz
        have hzU : closedBall z (δ / 2) ⊆ U :=
          (show closedBall z (δ/2) ⊆ closedBall (x:ℂ) δ from
            closedBall_subset_closedBall' (ε₁ := δ / 2) (x := z) (y := (x : ℂ)) (ε₂ := δ)
              (by linarith)).trans ((Metric.closedBall_subset_cthickening x.2 δ).trans hδU)
        have hd : DiffContOnCl ℂ (v k) (ball z (δ / 2)) := by
          refine DifferentiableOn.diffContOnCl ?_
          rw [closure_ball z hδ2.ne']
          exact (hv k).mono hzU
        have hCsphere : ∀ w ∈ sphere z (δ / 2), ‖v k w‖ ≤ M₀ := by
          intro w hw
          refine hbdd k w ?_
          refine (Metric.closedBall_subset_cthickening x.2 δ) ?_
          exact closedBall_subset_closedBall' (ε₁ := δ / 2) (x := z) (y := (x : ℂ)) (ε₂ := δ)
            (by linarith) (sphere_subset_closedBall hw)
        have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ2 hd hCsphere
        calc ‖deriv (v k) z‖ ≤ M₀ / (δ / 2) := h
          _ = 2 * M₀ / δ := by ring
      have hy : (y : ℂ) ∈ closedBall (x : ℂ) (δ / 2) := by
        rw [mem_closedBall, ← Subtype.dist_eq, dist_comm]
        exact hxy
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (f := v k) (s := closedBall (x : ℂ) (δ / 2)) (C := 2 * M₀ / δ)
        (fun z hz => (hv k).differentiableAt (hU.mem_nhds (hsub hz)))
        hderiv (convex_closedBall _ _) (mem_closedBall_self (by linarith)) hy
      have h3 : dist (v k x) (v k y) = ‖v k y - v k x‖ := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [h3]
      refine hmvt.trans ?_
      rw [hD']
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      exact div_le_div_of_nonneg_right (by linarith [hM₀0]) hδpos.le
    · -- far case: use only the bound
      have hx' : (x : ℂ) ∈ cthickening δ K := Metric.self_subset_cthickening K x.2
      have hy' : (y : ℂ) ∈ cthickening δ K := Metric.self_subset_cthickening K y.2
      have h1 : dist (v k x) (v k y) ≤ 2 * M₀ := by
        rw [dist_eq_norm]
        calc ‖v k x - v k y‖ ≤ ‖v k x‖ + ‖v k y‖ := norm_sub_le _ _
          _ ≤ M₀ + M₀ := add_le_add (hbdd k x hx') (hbdd k y hy')
          _ = 2 * M₀ := by ring
      have hle : M₀ ≤ (2 * M₀ / δ) * dist x y := by
        have h1 : (1 : ℝ) / 2 ≤ dist x y / δ := by
          rw [le_div_iff₀ hδpos]; linarith
        have hM₀' : (0:ℝ) ≤ 2 * M₀ := by linarith
        calc M₀ = 2 * M₀ * (1 / 2) := by ring
          _ ≤ 2 * M₀ * (dist x y / δ) := mul_le_mul_of_nonneg_left h1 hM₀'
          _ = (2 * M₀ / δ) * dist x y := by ring
      have h2 : 2 * M₀ ≤ (4 * M₀ / δ) * dist x y := by
        calc 2 * M₀ ≤ 2 * ((2 * M₀ / δ) * dist x y) := by linarith
          _ = (4 * M₀ / δ) * dist x y := by ring
      exact h1.trans h2
  -- equicontinuity of the set of restrictions
  have hH : Equicontinuous ((↑) : A → K → ℂ) := by
    refine Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (4 * M₀ / δ) * r) ?_
      (fun i : A => (i.1 : K → ℂ)) ?_
    · have h : Tendsto (fun r : ℝ => (4 * M₀ / δ) * r) (𝓝 0) (𝓝 ((4 * M₀ / δ) * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      simpa using h
    · intro x y i
      obtain ⟨k, hk⟩ := Set.mem_range.mp i.2
      have hik : ((i.1 : BoundedContinuousFunction K ℂ) : K → ℂ) = fun z : K => v k z := by
        rw [← hk]; ext z; simp [F, w, Set.domRestrict]
      rw [hik]
      exact hLip k x y
  -- Arzela-Ascoli
  have hin : ∀ (f : BoundedContinuousFunction K ℂ) (x : K), f ∈ A → f x ∈ closedBall (0 : ℂ) M₀ := by
    intro f x hf
    obtain ⟨k, hk⟩ := Set.mem_range.mp hf
    rw [← hk, hdx k x, mem_closedBall, dist_zero_right]
    exact hbdd k x (Metric.self_subset_cthickening K x.2)
  have hA_compact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M₀) (isCompact_closedBall 0 M₀)
      A hin hH
  obtain ⟨a, _ha, σ, hσ, hlim⟩ := hA_compact.isSeqCompact (x := F)
    (fun n => subset_closure (Set.mem_range_self n))
  -- convert the sup-norm convergence into uniform convergence
  have hTU : TendstoUniformly (fun k (x : K) => v (σ k) x) (fun x : K => a x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    rw [Metric.tendsto_nhds] at hlim
    filter_upwards [hlim ε hε] with k hk x
    calc dist (a x) (v (σ k) x) = dist (a x) ((F (σ k)) x) := by rw [hdx]
      _ ≤ dist a (F (σ k)) := BoundedContinuousFunction.dist_coe_le_dist x
      _ < ε := by rwa [dist_comm]
  set g : ℂ → ℂ := fun z => if h : z ∈ K then a ⟨z, h⟩ else 0 with hg
  refine ⟨σ, hσ, g, ?_⟩
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hgg : (g ∘ Subtype.val) = fun x : K => a x := by
    funext x
    simp only [Function.comp_apply, hg]
    rw [dite_eq_left x.2]
  rw [hgg]
  exact hTU



end Work.Normal
