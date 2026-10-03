import Mathlib
import Submission.Work.Dim.Setup

/-!
# The coding map of a contracting conformal IFS (area DIM, step A)

`Work.Dim.Coding.map`: for a family `τ : Fin N → ℂ → ℂ` of branches mapping `ball p r` into
`ball p (r/2)`, with `‖deriv (τ i)‖ ≤ θ < 1` on `closedBall p (r/2)`:

* `k ↦ ifsComp τ (pref ω k) p` converges to `codingPt τ p ω` (the composition is a contraction);
* `codingPt τ p ω` lies in every piece `piece τ p r (pref ω k)`;
* the coding map `ω ↦ codingPt τ p ω` is continuous for the product topology on `ℕ → Fin N`;
* the contraction estimate `‖codingPt ω - codingPt ω'‖ ≤ 2 * r * θ^k` for words sharing `k` letters.
-/

namespace Work.Dim.Coding

open MandelDim
open scoped Topology
open Set Metric Filter Function

noncomputable section

/-- **Step A.** Mean value inequality for a word: `ifsComp τ w` is `θ^|w|`-Lipschitz on the inner
closed ball `closedBall p (r/2)`, which is convex and strictly inside `ball p r`. -/
private theorem lipschitz_aux {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (r θ : ℝ) (hr : 0 < r)
    (_hθ0 : 0 ≤ θ)
    (hmaps : ∀ i, Set.MapsTo (τ i) (Metric.ball p r) (Metric.ball p (r / 2)))
    (hderiv : ∀ i, ∀ z ∈ Metric.closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (Metric.ball p r)) (w : List (Fin N)) :
    ∀ z ∈ Metric.closedBall p (r / 2), ∀ z' ∈ Metric.closedBall p (r / 2),
      ‖MandelDim.ifsComp τ w z - MandelDim.ifsComp τ w z'‖ ≤ θ ^ w.length * ‖z - z'‖ := by
  intro z hz z' hz'
  rcases eq_or_ne w [] with rfl | hw
  · simp [MandelDim.ifsComp]
  · have hdiffw : ∀ x ∈ Metric.closedBall p (r / 2), DifferentiableAt ℂ (ifsComp τ w) x := by
      intro x hx
      refine ifsComp_differentiableAt hr hdiff hmaps w hw x ?_
      rw [mem_closedBall] at hx; rw [mem_ball]; linarith
    have hbnd : ∀ x ∈ Metric.closedBall p (r / 2), ‖deriv (ifsComp τ w) x‖ ≤ θ ^ w.length :=
      fun x hx => norm_deriv_ifsComp_le hr hdiff hmaps hderiv w hw x hx
    exact Convex.norm_image_sub_le_of_norm_deriv_le hdiffw hbnd (convex_closedBall p (r / 2)) hz' hz

theorem map {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (r θ : ℝ) (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hmaps : ∀ i, Set.MapsTo (τ i) (Metric.ball p r) (Metric.ball p (r / 2)))
    (hderiv : ∀ i, ∀ z ∈ Metric.closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (Metric.ball p r))
    (hdisj : Pairwise fun i j => Disjoint (τ i '' Metric.ball p r) (τ j '' Metric.ball p r)) :
    (∀ ω : ℕ → Fin N, Filter.Tendsto (fun k => MandelDim.ifsComp τ (Work.Dim.pref ω k) p) Filter.atTop
        (nhds (MandelDim.codingPt τ p ω))) ∧
    (∀ (ω : ℕ → Fin N) (k : ℕ),
      MandelDim.codingPt τ p ω ∈ Work.Dim.piece τ p r (Work.Dim.pref ω k)) ∧
    Continuous (MandelDim.codingPt τ p) ∧
    (∀ (ω ω' : ℕ → Fin N) (k : ℕ), (∀ j < k, ω j = ω' j) →
      ‖MandelDim.codingPt τ p ω - MandelDim.codingPt τ p ω'‖ ≤ 2 * r * θ ^ k) := by
  have hp_mem : p ∈ Metric.closedBall p (r / 2) := by
    rw [mem_closedBall, dist_self]; linarith
  have hp_ball : p ∈ Metric.ball p r := by
    rw [mem_ball]; simpa using hr
  -- the mean value (Lipschitz) bound for a word
  have hLips : ∀ (w : List (Fin N)) (z z' : ℂ),
      z ∈ Metric.closedBall p (r / 2) → z' ∈ Metric.closedBall p (r / 2) →
      ‖ifsComp τ w z - ifsComp τ w z'‖ ≤ θ ^ w.length * ‖z - z'‖ :=
    fun w z z' hz hz' => lipschitz_aux τ p r θ hr hθ0 hmaps hderiv hdiff w z hz z' hz'
  ----------------------------------------------------------------------------------------------
  -- (1) the sequence of compositions converges to the coding point
  ----------------------------------------------------------------------------------------------
  have hconv : ∀ ω : ℕ → Fin N,
      Tendsto (fun k => ifsComp τ (Work.Dim.pref ω k) p) atTop (nhds (codingPt τ p ω)) := by
    intro ω
    have hstep : ∀ k : ℕ,
        ‖ifsComp τ (Work.Dim.pref ω k) p - ifsComp τ (Work.Dim.pref ω (k + 1)) p‖
          ≤ (r / 2) * θ ^ k := by
      intro k
      have hrec : ifsComp τ (Work.Dim.pref ω (k + 1)) p
          = ifsComp τ (Work.Dim.pref ω k) (τ (ω k) p) := by
        rw [Work.Dim.pref_succ, Work.Dim.ifsComp_append_singleton]
        rfl
      rw [hrec]
      have hmem1 : τ (ω k) p ∈ Metric.closedBall p (r / 2) := by
        have h := hmaps (ω k) hp_ball
        rw [mem_ball] at h
        rw [mem_closedBall]; linarith
      have hb := hLips (Work.Dim.pref ω k) p (τ (ω k) p) hp_mem hmem1
      rw [Work.Dim.pref_length] at hb
      have hd : ‖p - τ (ω k) p‖ ≤ r / 2 := by
        have h := hmaps (ω k) hp_ball
        rw [mem_ball, dist_eq_norm] at h
        rw [norm_sub_rev]; linarith
      calc ‖ifsComp τ (Work.Dim.pref ω k) p - ifsComp τ (Work.Dim.pref ω k) (τ (ω k) p)‖
          ≤ θ ^ k * ‖p - τ (ω k) p‖ := hb
        _ ≤ θ ^ k * (r / 2) := mul_le_mul_of_nonneg_left hd (pow_nonneg hθ0 k)
        _ = (r / 2) * θ ^ k := by ring
    have hcau : CauchySeq (fun k => ifsComp τ (Work.Dim.pref ω k) p) :=
      SeminormedAddCommGroup.cauchySeq_of_le_geometric hθ1 hstep
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
    have hlim := tendsto_nhds_limUnder (g := fun k => ifsComp τ (Work.Dim.pref ω k) p) ⟨L, hL⟩
    simpa [codingPt, Work.Dim.pref] using hlim
  ----------------------------------------------------------------------------------------------
  -- pieces are closed and nested
  ----------------------------------------------------------------------------------------------
  have hpiece_closed : ∀ w : List (Fin N), IsClosed (Work.Dim.piece τ p r w) := by
    intro w
    rcases eq_or_ne w [] with rfl | hw
    · have h : Work.Dim.piece τ p r [] = Metric.closedBall p (r / 2) := by
        simp [Work.Dim.piece, MandelDim.ifsComp]
      rw [h]; exact isClosed_closedBall
    · have hcont : ContinuousOn (ifsComp τ w) (Metric.closedBall p (r / 2)) :=
        fun z hz => (ifsComp_differentiableAt hr hdiff hmaps w hw z (by
          rw [mem_closedBall] at hz; rw [mem_ball]; linarith)).continuousAt.continuousWithinAt
      have hc := (isCompact_closedBall p (r / 2)).image_of_continuousOn hcont
      simpa [Work.Dim.piece] using hc.isClosed
  have hnest : ∀ (ω : ℕ → Fin N) (j k : ℕ), k ≤ j →
      Work.Dim.piece τ p r (Work.Dim.pref ω j) ⊆ Work.Dim.piece τ p r (Work.Dim.pref ω k) := by
    intro ω j k hkj
    induction j, hkj using Nat.le_induction with
    | base => exact Subset.rfl
    | succ n _ ih =>
        have hs : Work.Dim.piece τ p r (Work.Dim.pref ω (n + 1)) ⊆
            Work.Dim.piece τ p r (Work.Dim.pref ω n) := by
          rw [Work.Dim.pref_succ]
          exact Work.Dim.piece_append_subset hr hmaps (Work.Dim.pref ω n) [ω n]
        exact hs.trans ih
  ----------------------------------------------------------------------------------------------
  -- (2) the coding point lies in every piece of its prefixes
  ----------------------------------------------------------------------------------------------
  have hmem : ∀ (ω : ℕ → Fin N) (k : ℕ),
      codingPt τ p ω ∈ Work.Dim.piece τ p r (Work.Dim.pref ω k) := by
    intro ω k
    have hev : ∀ᶠ j in atTop,
        ifsComp τ (Work.Dim.pref ω j) p ∈ Work.Dim.piece τ p r (Work.Dim.pref ω k) := by
      filter_upwards [eventually_ge_atTop k] with j hj
      exact hnest ω j k hj ⟨p, hp_mem, rfl⟩
    exact (hpiece_closed (Work.Dim.pref ω k)).mem_of_tendsto (hconv ω) hev
  ----------------------------------------------------------------------------------------------
  -- (4) the contraction estimate
  ----------------------------------------------------------------------------------------------
  have hpref_eq : ∀ (ω ω' : ℕ → Fin N) (k : ℕ), (∀ j < k, ω j = ω' j) →
      Work.Dim.pref ω k = Work.Dim.pref ω' k := by
    intro ω ω' k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
        intro hk
        rw [Work.Dim.pref_succ, Work.Dim.pref_succ,
          ih (fun j hj => hk j (Nat.lt_succ_of_lt hj)), hk n (Nat.lt_succ_self n)]
  have h4 : ∀ (ω ω' : ℕ → Fin N) (k : ℕ), (∀ j < k, ω j = ω' j) →
      ‖codingPt τ p ω - codingPt τ p ω'‖ ≤ 2 * r * θ ^ k := by
    intro ω ω' k hk
    have hpref := hpref_eq ω ω' k hk
    obtain ⟨z, hz, hzω⟩ := hmem ω k
    have hm2 : codingPt τ p ω' ∈ Work.Dim.piece τ p r (Work.Dim.pref ω k) := by
      simpa [hpref] using hmem ω' k
    obtain ⟨z', hz', hz'ω⟩ := hm2
    have hzr : dist z z' ≤ r := by
      have h1 : dist z p ≤ r / 2 := mem_closedBall.mp hz
      have h2 : dist p z' ≤ r / 2 := by rw [dist_comm]; exact mem_closedBall.mp hz'
      calc dist z z' ≤ dist z p + dist p z' := dist_triangle z p z'
        _ ≤ r / 2 + r / 2 := add_le_add h1 h2
        _ = r := by ring
    calc ‖codingPt τ p ω - codingPt τ p ω'‖
        = ‖ifsComp τ (Work.Dim.pref ω k) z - ifsComp τ (Work.Dim.pref ω k) z'‖ := by
          rw [hzω, hz'ω]
      _ ≤ θ ^ (Work.Dim.pref ω k).length * ‖z - z'‖ := hLips _ z z' hz hz'
      _ = θ ^ k * ‖z - z'‖ := by rw [Work.Dim.pref_length]
      _ ≤ θ ^ k * r := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 k)
          rw [← dist_eq_norm]; exact hzr
      _ ≤ 2 * r * θ ^ k := by
          have hk0 : (0 : ℝ) ≤ θ ^ k := pow_nonneg hθ0 k
          nlinarith [hr, hk0]
  ----------------------------------------------------------------------------------------------
  -- (3) continuity of the coding map
  ----------------------------------------------------------------------------------------------
  have hcont : Continuous (codingPt τ p) := by
    refine continuous_iff_continuousAt.mpr (fun ω => ?_)
    show Tendsto (codingPt τ p) (𝓝 ω) (𝓝 ((codingPt τ p) ω))
    rw [Metric.tendsto_nhds]
    intro ε hε
    have htend : Tendsto (fun k : ℕ => 2 * r * θ ^ k) atTop (nhds 0) := by
      have h1 : Tendsto (fun k : ℕ => θ ^ k) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
      simpa using h1.const_mul (2 * r)
    obtain ⟨k, hk⟩ := (htend.eventually (Iio_mem_nhds hε)).exists
    have hUopen : IsOpen {ω' : ℕ → Fin N | ∀ j < k, ω' j = ω j} := by
      have hset : {ω' : ℕ → Fin N | ∀ j < k, ω' j = ω j}
          = ⋂ j ∈ (Finset.range k : Set ℕ), {ω' : ℕ → Fin N | ω' j = ω j} := by
        ext ω'; simp
      rw [hset]
      refine Finite.isOpen_biInter (Finset.finite_toSet _) ?_
      intro j _
      have hc : Continuous (fun ω' : ℕ → Fin N => ω' j) := continuous_apply j
      exact hc.isOpen_preimage ({ω j} : Set (Fin N)) (isOpen_discrete _)
    have hUmem : ω ∈ {ω' : ℕ → Fin N | ∀ j < k, ω' j = ω j} := fun j _ => rfl
    refine Filter.mem_of_superset (hUopen.mem_nhds hUmem) ?_
    intro ω' hω'
    change dist (codingPt τ p ω') (codingPt τ p ω) < ε
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (h4 ω' ω k hω') hk
  exact ⟨hconv, hmem, hcont, h4⟩

end

end Work.Dim.Coding
