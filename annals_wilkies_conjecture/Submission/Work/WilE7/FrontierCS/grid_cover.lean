/-
  WilE7 / CS-slice, node **N5** (`grid_cover`): the grid cover of the slice chart.

  For `G : ℝ^N → ℝ^j` entire, `W ⊆ {rank dG = j}`, and a chart `Φ(t,e) = γ t + B e` whose
  derivative `sliceDeriv γ B τ = Dγ(τ) ∘ fst + B ∘ snd` is a linear isomorphism at `0`, every
  `τ` close to `0` satisfies: for one of the finitely many `0/1` slope matrices `Λ = gridMat b`,
  the point `(τ,0)` lies in the closure of the slice set `sliceSet G W (sliceChart γ B Λ)`, i.e.
  is a limit of points where `sliceChart γ B Λ` meets `W` and the slice Jacobian is surjective.

  Proof (design `sources/wilkiesE7/wilkies_e7_frontier.md`, node N5):
  * `gc_bijective_eventually`: `sliceDeriv γ B t` is bijective for all `t` near `0` (analyticity
    makes `t ↦ fderiv ℝ γ t` continuous, and invertibility of CLMs is open).
  * hence, for such `τ` with `γ τ ∈ closure W`, the chart `Φ (t,e) = γ t + B e` is a local
    homeomorphism at `(τ,0)` with `Φ (τ,0) = γ τ ∈ closure W`, so `(τ,0) ∈ closure (Φ ⁻¹' W)`
    (`gc_closure_preimage`, via `mem_closure_preimage`).
  * picking points `q` of `Φ ⁻¹' W` arbitrarily close to `(τ,0)`, the grid lemma
    `exists_grid_det_ne_zero` applied to `mat (dG (Φ q)) * mat (dγ q.1)` and `mat (dG (Φ q)) * mat B`
    (which is surjective because `sliceDeriv γ B q.1` is) produces a slope matrix `Λ = gridMat b`
    with `dG (Φ q) ∘ (dγ (q.1) ∘ Λ + B)` invertible, and then
    `(q.1 - Λ q.2, q.2) ∈ sliceSet G W (sliceChart γ B Λ)` (`gc_witness`).
  * the maps `(q) ↦ (q.1 - Λ q.2, q.2)` are uniformly close to the identity near `(τ,0)` because
    the entries of `gridMat b` are in `{0,1}` (`gc_norm_gridMat_mulVec_le`), and the finite union
    of the closures of the slice sets is closed; hence `(τ,0)` lies in the closure of one of them.
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.gc_defs
import Submission.Work.WilE7.FrontierCS.exists_grid_det_ne_zero
import Submission.Work.WilE7.FrontierCS.mem_closure_preimage
import Submission.Work.WilE7.FrontierCS.gc_bijective_eventually
import Submission.Work.WilE7.FrontierCS.gc_closure_preimage
import Submission.Work.WilE7.FrontierCS.gc_witness
import Submission.Work.WilE7.FrontierCS.gc_norm_gridMat_mulVec_le

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-! ## Assembly -/

theorem grid_cover {N d j : ℕ} {G : (Fin N → ℝ) → (Fin j → ℝ)}
    (hG : AnalyticOnNhd ℝ G Set.univ) {W : Set (Fin N → ℝ)}
    (hWrk : ∀ w ∈ W, (fderiv ℝ G w).range = ⊤)
    {γ : (Fin d → ℝ) → (Fin N → ℝ)} (hγ : AnalyticOnNhd ℝ γ Set.univ)
    {B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)}
    (hB : Function.Bijective (fun p : (Fin d → ℝ) × (Fin j → ℝ) => fderiv ℝ γ 0 p.1 + B p.2))
    (hγW : Filter.Eventually (fun s => γ s ∈ closure W) (nhds (0 : Fin d → ℝ))) :
    Filter.Eventually (fun τ : Fin d → ℝ => ∃ b : Fin d → Fin j → Bool,
      (τ, (0 : Fin j → ℝ)) ∈ closure
        (Work.WilE7.FrontierCS.sliceSet G W
          (Work.WilE7.FrontierCS.sliceChart γ B (Work.WilE7.FrontierCS.gridMat b))))
      (nhds (0 : Fin d → ℝ)) := by
  obtain ⟨ε₁, hε₁, hε₁ball⟩ := Metric.mem_nhds_iff.mp (gc_bijective_eventually hγ hB)
  obtain ⟨ε₂, hε₂, hε₂ball⟩ := Metric.mem_nhds_iff.mp hγW
  have hr : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Fin d → ℝ) hr) ?_
  intro τ hτ
  have hτ1 : τ ∈ Metric.ball (0 : Fin d → ℝ) ε₁ := Metric.ball_subset_ball (min_le_left _ _) hτ
  have hτ2 : τ ∈ Metric.ball (0 : Fin d → ℝ) ε₂ := Metric.ball_subset_ball (min_le_right _ _) hτ
  have hBij : Function.Bijective (sliceDeriv γ B τ) := hε₁ball hτ1
  have hγτ : γ τ ∈ closure W := hε₂ball hτ2
  have hcl : (τ, (0 : Fin j → ℝ)) ∈
      closure ((fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1 + B p.2) ⁻¹' W) :=
    gc_closure_preimage hγ hBij hγτ
  have hUnion : (τ, (0 : Fin j → ℝ)) ∈
      closure (⋃ b : Fin d → Fin j → Bool, sliceSet G W (sliceChart γ B (gridMat b))) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
    set ρ : ℝ := δ / (2 * ((j : ℝ) + 1)) with hρdef
    have hρpos : 0 < ρ := by positivity
    have hδnonneg : (0 : ℝ) ≤ δ := le_of_lt hδ
    have hchoice : ∀ n : ℕ, ∃ q : (Fin d → ℝ) × (Fin j → ℝ),
        q ∈ Metric.ball (τ, (0 : Fin j → ℝ)) (min ρ (1 / ((n : ℝ) + 1))) ∧
          γ q.1 + B q.2 ∈ W := by
      intro n
      have hpos : 0 < min ρ (1 / ((n : ℝ) + 1)) := lt_min hρpos (by positivity)
      obtain ⟨q, hq1, hq2⟩ := (mem_closure_iff_nhds.mp hcl) _
        (Metric.ball_mem_nhds (τ, (0 : Fin j → ℝ)) hpos)
      exact ⟨q, hq1, hq2⟩
    choose q hqball hqW using hchoice
    have hqtend : Tendsto q atTop (𝓝 (τ, (0 : Fin j → ℝ))) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
      refine ⟨M, fun n hn => ?_⟩
      have h1 : 1 / ((n : ℝ) + 1) < ε := by
        have h3 : 1 < ε * (M : ℝ) := by
          rw [div_lt_iff₀ hε] at hM
          linarith
        have h4 : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [h3, h4, hε]
      calc dist (q n) (τ, (0 : Fin j → ℝ)) < min ρ (1 / ((n : ℝ) + 1)) := hqball n
        _ ≤ 1 / ((n : ℝ) + 1) := min_le_right _ _
        _ < ε := h1
    have hq1tend : Tendsto (fun n => (q n).1) atTop (𝓝 τ) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hqtend ε hε
      refine ⟨M, fun n hn => ?_⟩
      calc dist (q n).1 τ ≤ max (dist (q n).1 τ) (dist (q n).2 (0 : Fin j → ℝ)) :=
            le_max_left _ _
        _ = dist (q n) (τ, (0 : Fin j → ℝ)) :=
              (Prod.dist_eq (x := q n) (y := (τ, (0 : Fin j → ℝ)))).symm
        _ < ε := hM n hn
    have hnbij : {t : Fin d → ℝ | Function.Bijective (sliceDeriv γ B t)} ∈ 𝓝 τ :=
      Filter.mem_of_superset
        ((Metric.isOpen_ball (x := (0 : Fin d → ℝ)) (ε := ε₁)).mem_nhds hτ1) hε₁ball
    have hev : ∀ᶠ n in atTop, Function.Bijective (sliceDeriv γ B (q n).1) :=
      hq1tend.eventually hnbij
    obtain ⟨n, hn_bij⟩ := hev.exists
    have hT : (sliceDeriv γ B (q n).1).range = ⊤ := LinearMap.range_eq_top.mpr hn_bij.2
    obtain ⟨b, hb⟩ := gc_witness (q := q n) hG hWrk hγ (hqW n) hT
    refine ⟨((q n).1 - (gridMat b).mulVec (q n).2, (q n).2), ?_, ?_⟩
    · have hD : dist (q n) (τ, (0 : Fin j → ℝ)) < ρ :=
        lt_of_lt_of_le (hqball n) (min_le_left _ _)
      have hfst : dist (q n).1 τ ≤ dist (q n) (τ, (0 : Fin j → ℝ)) := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      have hsnd : ‖(q n).2‖ ≤ dist (q n) (τ, (0 : Fin j → ℝ)) := by
        rw [Prod.dist_eq]
        have h : ‖(q n).2‖ = dist (q n).2 ((τ, (0 : Fin j → ℝ)).2) := by
          rw [dist_eq_norm]; simp
        rw [h]
        exact le_max_right _ _
      have hΛ : ‖(gridMat b).mulVec (q n).2‖ ≤
          (j : ℝ) * dist (q n) (τ, (0 : Fin j → ℝ)) :=
        le_trans (gc_norm_gridMat_mulVec_le b (q n).2)
          (mul_le_mul_of_nonneg_left hsnd (Nat.cast_nonneg j))
      have hmain : dist ((q n).1 - (gridMat b).mulVec (q n).2) τ < δ := by
        rw [dist_eq_norm]
        have h2 : ‖(q n).1 - (gridMat b).mulVec (q n).2 - τ‖ ≤
            ‖(q n).1 - τ‖ + ‖(gridMat b).mulVec (q n).2‖ := by
          have h3 : (q n).1 - (gridMat b).mulVec (q n).2 - τ =
              ((q n).1 - τ) - (gridMat b).mulVec (q n).2 := by abel
          rw [h3]
          exact norm_sub_le _ _
        have h4 : ‖(q n).1 - τ‖ ≤ dist (q n) (τ, (0 : Fin j → ℝ)) := by
          rw [← dist_eq_norm]; exact hfst
        have hDnn : (0 : ℝ) ≤ dist (q n) (τ, (0 : Fin j → ℝ)) := dist_nonneg
        have h5 : ‖(q n).1 - (gridMat b).mulVec (q n).2 - τ‖ ≤
            ((j : ℝ) + 1) * dist (q n) (τ, (0 : Fin j → ℝ)) := by
          calc ‖(q n).1 - (gridMat b).mulVec (q n).2 - τ‖
              ≤ ‖(q n).1 - τ‖ + ‖(gridMat b).mulVec (q n).2‖ := h2
            _ ≤ dist (q n) (τ, (0 : Fin j → ℝ)) +
                  (j : ℝ) * dist (q n) (τ, (0 : Fin j → ℝ)) := add_le_add h4 hΛ
            _ = ((j : ℝ) + 1) * dist (q n) (τ, (0 : Fin j → ℝ)) := by ring
        have h7 : ((j : ℝ) + 1) * ρ = δ / 2 := by
          rw [hρdef]; field_simp
        have h6 : ((j : ℝ) + 1) * dist (q n) (τ, (0 : Fin j → ℝ)) < δ := by
          have h8 : ((j : ℝ) + 1) * dist (q n) (τ, (0 : Fin j → ℝ)) < ((j : ℝ) + 1) * ρ :=
            mul_lt_mul_of_pos_left hD (by positivity)
          rw [h7] at h8
          linarith
        exact lt_of_le_of_lt h5 h6
      have hsnd2 : dist (q n).2 (0 : Fin j → ℝ) < δ := by
        rw [dist_eq_norm, sub_zero]
        have h9 : ρ ≤ δ := by
          have hden : (1 : ℝ) ≤ 2 * ((j : ℝ) + 1) :=
            by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
          have hρeq : ρ * (2 * ((j : ℝ) + 1)) = δ := by rw [hρdef]; field_simp
          calc ρ ≤ ρ * (2 * ((j : ℝ) + 1)) := by
                nth_rewrite 1 [← mul_one ρ]
                exact mul_le_mul_of_nonneg_left hden hρpos.le
            _ = δ := hρeq
        exact lt_of_lt_of_le (lt_of_le_of_lt hsnd hD) h9
      have hdistp : dist ((q n).1 - (gridMat b).mulVec (q n).2, (q n).2) (τ, (0 : Fin j → ℝ)) < δ := by
        rw [Prod.dist_eq]
        exact max_lt hmain hsnd2
      exact hδU hdistp
    · exact Set.mem_iUnion.mpr ⟨b, hb⟩
  have hclosed : IsClosed (⋃ b : Fin d → Fin j → Bool,
      closure (sliceSet G W (sliceChart γ B (gridMat b)))) :=
    isClosed_iUnion_of_finite fun b => isClosed_closure
  have hsub : closure (⋃ b : Fin d → Fin j → Bool,
        sliceSet G W (sliceChart γ B (gridMat b))) ⊆
      ⋃ b : Fin d → Fin j → Bool, closure (sliceSet G W (sliceChart γ B (gridMat b))) :=
    closure_minimal (Set.iUnion_subset fun b =>
      subset_trans subset_closure (Set.subset_iUnion (fun b : Fin d → Fin j → Bool =>
        closure (sliceSet G W (sliceChart γ B (gridMat b)))) b)) hclosed
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hsub hUnion)
  exact ⟨b, hb⟩

end Work.WilE7.FrontierCS
