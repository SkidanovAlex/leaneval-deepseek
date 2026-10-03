import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.gholo
import Submission.Work.L62.chain_branches

namespace Work.L62

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

/-- The numerical/geometric package of a model chain, used to perturb it: for a chain `W` (open connected, `W 0 = ball ζ₀ r`, `ĥ`-bijections, all `W j ⊆ d.DE` for `1 ≤ j`) with its holomorphic branches `Ψ j : ball ζ₀ r → W j` (`Ψ 0 = id`, injective on the ball, image `W j`) and holomorphic step inverses `ψ j : W j → W (j+1)` of `ĥ = d.E - β` (as produced by `chain_branches`), there is a radius `q ∈ (ρ, r)` and constants `ε > 0`, `L > 0`, `κ > 0` with: (i) the `ε`-ball about every point of the compact `Ψ j '' closedBall ζ₀ q` lies in `W j` (a uniform collar, by compactness of the image and openness of `W j`); (ii) `‖deriv (ψ j)‖ ≤ L` on that collar (possible since the collar lies inside `W j` where `ψ j` is holomorphic, by compactness); (iii) the model iteration `ĥ^j` is `κ`-Lipschitz on that collar (by compactness of the derivative of the holomorphic iterates: `ĥ = d.E - β` is holomorphic on the open `d.DE`, the chain identifies `ĥ '' W (j+1) = W j`, and only the first `j-1` iterates of a collar point need to stay in `d.DE`). -/
theorem chain_geometry {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {W : ℕ → Set ℂ} {J : ℕ} {ζ₀ : ℂ} {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < r)
    (hW0 : W 0 = Metric.ball ζ₀ r)
    (hopen : ∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j))
    (hDE : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ d.DE)
    (hchain : ∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
      (fun w => d.E w - β) '' W (j + 1) = W j)
    {Ψ ψ : ℕ → ℂ → ℂ}
    (hΨ : ∀ j, j ≤ J → DifferentiableOn ℂ (Ψ j) (Metric.ball ζ₀ r) ∧
        Set.InjOn (Ψ j) (Metric.ball ζ₀ r) ∧ Ψ j '' Metric.ball ζ₀ r = W j)
    (hψ : ∀ j, j < J → DifferentiableOn ℂ (ψ j) (W j) ∧
        (∀ w ∈ W j, (fun u => d.E u - β) (ψ j w) = w)) :
    ∃ (q ε L κ : ℝ), ρ < q ∧ q < r ∧ 0 < ε ∧ 0 < L ∧ 0 < κ ∧
      (∀ j, j ≤ J → ∀ z ∈ Ψ j '' Metric.closedBall ζ₀ q, Metric.closedBall z ε ⊆ W j) ∧
      (∀ j, j < J → ∀ z ∈ Ψ j '' Metric.closedBall ζ₀ q, ∀ z', dist z' z < ε →
        ‖deriv (ψ j) z'‖ ≤ L) ∧
      (∀ j, j ≤ J → ∀ z ∈ Ψ j '' Metric.closedBall ζ₀ q, ∀ z', dist z' z < ε →
        ‖((fun u => d.E u - β)^[j]) z' - ((fun u => d.E u - β)^[j]) z‖ ≤ κ * ‖z' - z‖) := by
  classical
  -- a radius `q` strictly between `ρ` and `r`
  obtain ⟨q, hρq, hqr⟩ : ∃ q : ℝ, ρ < q ∧ q < r := ⟨(ρ + r) / 2, by linarith, by linarith⟩
  -- the model step map `ĥ = d.E - β`
  set F : ℂ → ℂ := fun u => d.E u - β with hF
  have hFdiff : DifferentiableOn ℂ F d.DE := by
    have h := (Work.Horn.differentiableOn_E d).sub_const β
    simpa only [hF] using h
  have hqs : Metric.closedBall ζ₀ q ⊆ Metric.ball ζ₀ r := Metric.closedBall_subset_ball hqr
  -- the compact images `K j = Ψ j '' closedBall ζ₀ q` lie in the open sets `W j`
  have hKc : ∀ j (hj : j ≤ J), IsCompact (Ψ j '' Metric.closedBall ζ₀ q) := by
    intro j hj
    exact (isCompact_closedBall ζ₀ q).image_of_continuousOn ((hΨ j hj).1.continuousOn.mono hqs)
  have hKW : ∀ j (hj : j ≤ J), Ψ j '' Metric.closedBall ζ₀ q ⊆ W j := by
    intro j hj
    exact (Set.image_mono hqs).trans (le_of_eq (hΨ j hj).2.2)
  -- a uniform collar radius: the finite minimum of the per-index ones
  have hδexists : ∀ j : Fin (J + 1), ∃ dd : ℝ, 0 < dd ∧
      Metric.cthickening dd (Ψ j.val '' Metric.closedBall ζ₀ q) ⊆ W j.val := by
    intro j
    have hj : j.val ≤ J := Nat.lt_succ_iff.mp j.isLt
    exact (hKc j.val hj).exists_cthickening_subset_open (hopen j.val hj).1 (hKW j.val hj)
  choose dd hdd using hδexists
  set D : ℝ := (Finset.univ : Finset (Fin (J + 1))).inf' Finset.univ_nonempty dd with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => (hdd i).1)
  have hDle : ∀ j : Fin (J + 1), D ≤ dd j := by
    intro j
    rw [hD]
    exact Finset.inf'_le dd (Finset.mem_univ j)
  set ε : ℝ := D / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hεdd : ∀ j : Fin (J + 1), ε ≤ dd j := by
    intro j
    have h1 := hDle j
    have h2 := (hdd j).1
    rw [hε]; linarith
  -- differentiability of the iterates of `ĥ` on the chain
  have hiterDiff : ∀ j, j ≤ J → DifferentiableOn ℂ (F^[j]) (W j) := by
    intro j
    induction j with
    | zero =>
        intro _
        rw [Function.iterate_zero]
        exact differentiableOn_id.mono (Set.subset_univ _)
    | succ n ih =>
        intro hnJ
        have hn : n ≤ J := Nat.le_of_succ_le hnJ
        have hnlt : n < J := Nat.lt_of_succ_le hnJ
        rw [Function.iterate_succ]
        intro w hw
        have hFw : F w ∈ W n := by
          rw [← (hchain n hnlt).2]
          exact mem_image_of_mem F hw
        have h1 : DifferentiableAt ℂ (F^[n]) (F w) :=
          (ih hn).differentiableAt ((hopen n hn).1.mem_nhds hFw)
        have h2 : DifferentiableAt ℂ F w :=
          hFdiff.differentiableAt (Filter.mem_of_superset ((hopen (n + 1) hnJ).1.mem_nhds hw)
            (hDE (n + 1) (by omega) hnJ))
        exact (h1.comp w h2).differentiableWithinAt
  have hiterCont : ∀ j, j ≤ J → ContinuousOn (deriv (F^[j])) (W j) := by
    intro j hj
    exact (((hiterDiff j hj).analyticOnNhd (hopen j hj).1).deriv).continuousOn
  have hpsiCont : ∀ j, j < J → ContinuousOn (deriv (ψ j)) (W j) := by
    intro j hj
    exact (((hψ j hj).1.analyticOnNhd (hopen j (le_of_lt hj)).1).deriv).continuousOn
  -- uniform Lipschitz constants for the iterates of `ĥ` on the collars
  have hCexists : ∀ j : Fin (J + 1), ∃ C : ℝ, 0 < C ∧
      ∀ z' ∈ Metric.cthickening ε (Ψ j.val '' Metric.closedBall ζ₀ q),
        ‖deriv (F^[j.val]) z'‖ ≤ C := by
    intro j
    have hj : j.val ≤ J := Nat.lt_succ_iff.mp j.isLt
    have hsub : Metric.cthickening ε (Ψ j.val '' Metric.closedBall ζ₀ q) ⊆ W j.val :=
      (Metric.cthickening_mono (hεdd j) _).trans (hdd j).2
    obtain ⟨C, hC⟩ := ((hKc j.val hj).cthickening (r := ε)).exists_bound_of_continuousOn
      ((hiterCont j.val hj).mono hsub)
    exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun z' hz => le_trans (hC z' hz) (le_max_left _ _)⟩
  choose Cb hCb using hCexists
  set κ : ℝ := (Finset.univ : Finset (Fin (J + 1))).sup' Finset.univ_nonempty Cb with hκ
  have hκpos : 0 < κ := by
    rw [hκ]
    exact lt_of_lt_of_le (hCb ⟨0, Nat.succ_pos J⟩).1 (Finset.le_sup' Cb (Finset.mem_univ _))
  -- uniform bound for the derivative of the step inverses `ψ j` on the collars
  have hLexists : ∀ j : Fin (J + 1), ∃ Lb : ℝ, 0 < Lb ∧
      (j.val < J → ∀ z' ∈ Metric.cthickening ε (Ψ j.val '' Metric.closedBall ζ₀ q),
        ‖deriv (ψ j.val) z'‖ ≤ Lb) := by
    intro j
    by_cases hj : j.val < J
    · have hsub : Metric.cthickening ε (Ψ j.val '' Metric.closedBall ζ₀ q) ⊆ W j.val :=
        (Metric.cthickening_mono (hεdd j) _).trans (hdd j).2
      obtain ⟨Lb, hLb⟩ := ((hKc j.val (le_of_lt hj)).cthickening (r := ε)).exists_bound_of_continuousOn
        ((hpsiCont j.val hj).mono hsub)
      exact ⟨max Lb 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
        fun _ z' hz => le_trans (hLb z' hz) (le_max_left _ _)⟩
    · exact ⟨1, one_pos, fun h => absurd h hj⟩
  choose Lb hLb using hLexists
  set L : ℝ := (Finset.univ : Finset (Fin (J + 1))).sup' Finset.univ_nonempty Lb with hL
  have hLpos : 0 < L := by
    rw [hL]
    exact lt_of_lt_of_le (hLb ⟨0, Nat.succ_pos J⟩).1 (Finset.le_sup' Lb (Finset.mem_univ _))
  refine ⟨q, ε, L, κ, hρq, hqr, hεpos, hLpos, hκpos, ?_, ?_, ?_⟩
  · -- (i) the collar is inside `W j`
    intro j hj z hz z' hz'
    exact (hdd ⟨j, Nat.lt_succ_of_le hj⟩).2
      ((Metric.cthickening_mono (hεdd ⟨j, Nat.lt_succ_of_le hj⟩) _)
        (Metric.mem_cthickening_of_dist_le z' z ε _ hz (Metric.mem_closedBall.mp hz')))
  · -- (ii) the derivative of the step inverse is bounded
    intro j hj z hz z' hz'
    exact ((hLb ⟨j, Nat.lt_succ_of_le (le_of_lt hj)⟩).2 hj z'
      (Metric.mem_cthickening_of_dist_le z' z ε _ hz (le_of_lt hz'))).trans
      (Finset.le_sup' Lb (Finset.mem_univ _))
  · -- (iii) the model iterate is Lipschitz: mean value inequality on the collar ball
    intro j hj z hz z' hz'
    have hsubj : Metric.cthickening ε (Ψ j '' Metric.closedBall ζ₀ q) ⊆ W j :=
      (Metric.cthickening_mono (hεdd ⟨j, Nat.lt_succ_of_le hj⟩) _).trans
        (hdd ⟨j, Nat.lt_succ_of_le hj⟩).2
    have hmem : ∀ x ∈ Metric.closedBall z ε,
        x ∈ Metric.cthickening ε (Ψ j '' Metric.closedBall ζ₀ q) :=
      fun x hx => Metric.mem_cthickening_of_dist_le x z ε _ hz (Metric.mem_closedBall.mp hx)
    have hbound : ∀ x ∈ Metric.closedBall z ε,
        ‖deriv (F^[j]) x‖ ≤ Cb ⟨j, Nat.lt_succ_of_le hj⟩ :=
      fun x hx => (hCb ⟨j, Nat.lt_succ_of_le hj⟩).2 x (hmem x hx)
    have hmvt : ‖F^[j] z' - F^[j] z‖ ≤ Cb ⟨j, Nat.lt_succ_of_le hj⟩ * ‖z' - z‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (f := F^[j]) (x := z) (y := z')
        (fun x hx => (hiterDiff j hj).differentiableAt
          ((hopen j hj).1.mem_nhds (hsubj (hmem x hx))))
        hbound (convex_closedBall z ε) (Metric.mem_closedBall.mpr (by rw [dist_self]; linarith))
        (Metric.mem_closedBall.mpr (le_of_lt hz'))
    calc ‖F^[j] z' - F^[j] z‖ ≤ Cb ⟨j, Nat.lt_succ_of_le hj⟩ * ‖z' - z‖ := hmvt
      _ ≤ κ * ‖z' - z‖ :=
        mul_le_mul_of_nonneg_right (Finset.le_sup' Cb (Finset.mem_univ _)) (norm_nonneg _)

end

end Work.L62
