import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.chain_v9_diff
import Submission.Work.Repel.V10.cell_iterate
import Submission.Work.Repel.uniform_iterate_of_orbit
import Submission.Work.Repel.V10.chain_image_mem
import Submission.Work.Repel.V10.SrcC_isConnected
import Submission.Work.Repel.V10.SrcC_sub_Dflat
import Submission.Work.Repel.V10.Raw_open
import Submission.Work.Repel.V10.uOf_differentiableOn

/-!
# `Work.Repel.chain_v9_walk` : the level-0 walk data of a §6 cell, and the uniform iterate

`Work.Repel.cell_iterate` gives the *pointwise* statement `∃ n ≥ 1, f^[n] (φ₀ w) = φ₀ w₁` for one
cell and one source point `w`.  Shishikura §6, Step 6 needs the *uniform* statement on the whole
source region, with the walk length depending on `w`.  This file:

* proves that a source point `w ∈ SrcC j k n` has a *level-0 return count* `m w ≥ 1` with the
  `P₀.R`-walk `P₀.R^[i] w ∈ P₀.DR` (`i < m w`), `π (P₀.R^[m w] w) = π (wOfCell q w)` and the angle
  condition of (4.2.3) at level 0 — the intermediate data of `cell_iterate`'s proof;
* upgrades it to a single iterate `N` on the whole (open, connected) source region
  `SrcC j k n`, via `Work.Repel.uniform_iterate_of_orbit`.

The level-0 walk data comes from the level-1 orbit field `P₁.orbit` (applied with `m = j ≥ 1`)
through the bridge `Work.Repel.walk_of_germ1`, exactly as in `cell_iterate`.
-/

set_option linter.style.haveILetI false

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The source region of a cell lies in the domain of `φ₀`. -/
theorem SrcC_sub_Dφ {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) : V.SrcC j k n ⊆ V.P₀.Dφ :=
  fun _ hw => V.P₀.D_sub (Or.inl (Dflat_subset_Dsm V.η (SrcC_sub_Dflat V hSm hn hw)))

/-- The source region of a cell lies in the return domain `P₀.DR`. -/
theorem SrcC_sub_DR {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) : V.SrcC j k n ⊆ V.P₀.DR :=
  fun _ hw => V.hDflatDR (SrcC_sub_Dflat V hSm hn hw)

/-- A source point of a cell has modulus at most `2η`. -/
theorem norm_le_two_eta_of_mem_SrcC {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) {w : ℂ} (hw : w ∈ V.SrcC j k n) :
    ‖w‖ ≤ 2 * V.η := by
  have h := SrcC_sub_Dflat V hSm hn hw
  rw [Dflat, Metric.mem_closedBall, dist_eq_norm] at h
  have h2 : ‖w‖ ≤ ‖w - Complex.I * (V.η : ℂ)‖ + V.η := by
    have h3 : Complex.I * (V.η : ℂ) = (V.η : ℂ) * Complex.I := by ring
    calc ‖w‖ = ‖(w - Complex.I * (V.η : ℂ)) + Complex.I * (V.η : ℂ)‖ := by congr 1; ring
      _ ≤ ‖w - Complex.I * (V.η : ℂ)‖ + ‖Complex.I * (V.η : ℂ)‖ := norm_add_le _ _
      _ = ‖w - Complex.I * (V.η : ℂ)‖ + V.η := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos V.hηpos]
  have h4 : ‖w - Complex.I * (V.η : ℂ)‖ ≤ V.η / 8 := by
    rw [abs_of_pos V.hηpos] at h; exact h
  linarith [h2, h4, V.hηpos]

/-- **The level-0 walk data of a cell.**  For `w ∈ SrcC j k n` there is a return count `m ≥ 1`
with the `P₀.R`-walk staying in `P₀.DR`, the `π`-agreement at the end, and the angle condition of
(4.2.3) at level 0.  These are exactly the hypotheses of `Work.Repel.uniform_iterate_of_orbit`. -/
theorem cell_walk_data {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) {w : ℂ} (hw : w ∈ V.SrcC j k n) :
    ∃ m : ℕ, 1 ≤ m ∧ (∀ i < m, V.P₀.R^[i] w ∈ V.P₀.DR) ∧
      MandelDim.piExp (V.P₀.R^[m] w) = MandelDim.piExp (V.wOfCell (j, k, n) w) ∧
      |Complex.arg (V.wOfCell (j, k, n) w + 1 / (2 * MandelDim.rotOf V.f) - w)|
        < 2 * Real.pi / 3 := by
  obtain ⟨k₀, -, hk₀⟩ := V.hk
  have hc : ∀ x : ℂ, V.R x - V.β = V.P₁.R x + ((k₀ : ℕ) : ℂ) := by
    intro x; rw [V.hR, hk₀]; ring
  -- the level-1 source and its chain walk
  set u : ℂ := V.uOf (V.s * MandelDim.piExp w) with hu_def
  have hu : u ∈ V.fib j k := V.uOfSrc_mem_fib hSm hw.1
  have huSm : u ∈ V.Sm1 := hSm hu
  set u' : ℂ := (fun x : ℂ => V.R x - V.β)^[j] u - ((k : ℤ) : ℂ) with hu'_def
  have hu' : u' ∈ V.W 0 := V.wOfCell_target_mem_Raw hj hSm hw.1
  have hchain : (fun x => V.R x - V.β)^[j] u = u' + ((k : ℤ) : ℂ) := by
    rw [hu'_def]; ring
  have hwDR : w ∈ V.P₀.DR := SrcC_sub_DR V hSm hn hw
  have hwDφ : w ∈ V.P₀.Dφ := SrcC_sub_Dφ V hSm hn hw
  have hwbd : ‖w‖ ≤ 2 * V.η := norm_le_two_eta_of_mem_SrcC V hSm hn hw
  have hpi : V.s * MandelDim.piExp w = V.P₁.φ u := by
    rw [hu_def]
    exact ((V.uOf_spec (Set.image_mono hSm hw.1)).2).symm
  -- walk of the return map along the chain
  have hwalk := walk_of_sub V.hIsChain V.hReq V.P₁.R_equiv V.hDRsub hc hu
  have hwalkDR : ∀ i < j, V.P₁.R^[i] u ∈ V.P₁.DR := hwalk.1
  have hwalkR : ∀ i ≤ j, V.P₁.R^[i] u = (fun x => V.R x - V.β)^[i] u - ((i * k₀ : ℕ) : ℂ) :=
    hwalk.2
  have huDφ : u ∈ V.P₁.Dφ := V.Sm1_sub_Dφ huSm
  have hu'ball : u' ∈ Metric.ball V.cbase V.ρ := by rw [← V.hbase]; exact hu'
  have hu'Dφ : u' ∈ V.P₁.Dφ := V.hsub₁ hu'ball
  have hu_norm : ‖u‖ ≤ 2 * V.η₁ := norm_le_two_eta₁_of_mem_Sm1 V huSm
  have hu'_norm : ‖u'‖ ≤ 2 * V.η₁ := by
    have h : ‖u' - V.cbase‖ < V.ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hu'ball; exact hu'ball
    have h2 : ‖u'‖ ≤ ‖u' - V.cbase‖ + ‖V.cbase‖ := by
      calc ‖u'‖ = ‖(u' - V.cbase) + V.cbase‖ := by congr 1; ring
        _ ≤ ‖u' - V.cbase‖ + ‖V.cbase‖ := norm_add_le _ _
    linarith [h, V.hcbase, V.hη₁pos, h2]
  have hpi_j : MandelDim.piExp (V.P₁.R^[j] u) = MandelDim.piExp u' := by
    rw [hwalkR j le_rfl, hchain]
    exact piExp_add_intCast_sub_natCast u' k (j * k₀)
  obtain ⟨n₁, hn₁, hn₁_eq, hn₁_mem⟩ :=
    V.P₁.orbit u huDφ u' hu'Dφ j hj hwalkDR hpi_j (V.hangle₁ u u' hu_norm hu'_norm)
  have hsπw : V.P₁.φ u = V.s * MandelDim.piExp w := hpi.symm
  have hsπw₁ : V.s * MandelDim.piExp (V.wOfCell (j, k, n) w) = V.P₁.φ u' := by
    rw [V.piExp_wOfCell hj hSm hw, mul_div_cancel₀ _ V.hs]
  have hbridge : (germ1 V.s V.P₀.R)^[n₁] (V.s * MandelDim.piExp w)
      = V.s * MandelDim.piExp (V.wOfCell (j, k, n) w) := by
    rw [← hsπw, hn₁_eq, hsπw₁]
  have horbit : ∀ i < n₁, (germ1 V.s V.P₀.R)^[i] (V.s * MandelDim.piExp w)
      ∈ (fun ζ => V.s * ζ) '' (insert 0 (MandelDim.piExp '' V.P₀.DR)) := by
    intro i hi
    have h := hn₁_mem i hi
    rwa [hsπw] at h
  have hne_same : ∀ i < n₁, (germ1 V.s V.P₀.R)^[i] (V.s * MandelDim.piExp w) ≠ 0 := by
    have hzero : ∀ m : ℕ, (germ1 V.s V.P₀.R)^[m] 0 = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ p ih => rw [Function.iterate_succ_apply', ih, germ1_zero]
    intro i hi h0
    have hle : i ≤ n₁ := le_of_lt hi
    have hsub : n₁ - i + i = n₁ := Nat.sub_add_cancel hle
    have hsplit : (germ1 V.s V.P₀.R)^[n₁] (V.s * MandelDim.piExp w)
        = (germ1 V.s V.P₀.R)^[n₁ - i] 0 := by
      have h1 : (germ1 V.s V.P₀.R)^[n₁ - i + i] (V.s * MandelDim.piExp w)
          = (germ1 V.s V.P₀.R)^[n₁ - i] 0 := by
        rw [Function.iterate_add_apply, h0]
      simpa only [hsub] using h1
    have hcontra : V.s * MandelDim.piExp (V.wOfCell (j, k, n) w) = 0 := by
      rw [← hbridge, hsplit, hzero]
    exact mul_ne_zero V.hs (Work.Horn.MandelDim.piExp_ne_zero _) hcontra
  have hDRT : MandelDim.IsTInvariant V.P₀.DR := V.P₀.R_equiv.1
  have hEreq : ∀ x ∈ V.P₀.DR, V.P₀.R (x + 1) = V.P₀.R x + 1 :=
    fun x hx => V.P₀.R_equiv.2 x hx
  obtain ⟨hwalk₀_mem, hwalk₀_eq⟩ := walk_of_germ1 hDRT hEreq V.hs hwDR horbit hne_same
  have hπ_final : MandelDim.piExp (V.P₀.R^[n₁] w)
      = MandelDim.piExp (V.wOfCell (j, k, n) w) := by
    have hstep := germ1_iterate_of_walk hDRT hEreq V.hs hn₁ hwalk₀_mem hwalk₀_eq
    rw [hstep] at hbridge
    exact mul_left_cancel₀ V.hs hbridge
  have hw₁ball : V.wOfCell (j, k, n) w ∈ Metric.ball V.wt₀ V.ρ₀ := V.wOfCell_mem_ball hj hSm hw
  have hw₁bd : ‖V.wOfCell (j, k, n) w‖ ≤ 2 * V.η := by
    have h : ‖V.wOfCell (j, k, n) w - V.wt₀‖ < V.ρ₀ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw₁ball; exact hw₁ball
    have h2 : ‖V.wOfCell (j, k, n) w‖ ≤ ‖V.wOfCell (j, k, n) w - V.wt₀‖ + ‖V.wt₀‖ := by
      calc ‖V.wOfCell (j, k, n) w‖
          = ‖(V.wOfCell (j, k, n) w - V.wt₀) + V.wt₀‖ := by congr 1; ring
        _ ≤ ‖V.wOfCell (j, k, n) w - V.wt₀‖ + ‖V.wt₀‖ := norm_add_le _ _
    linarith [h, V.hwt₀, h2]
  exact ⟨n₁, hn₁, hwalk₀_mem, hπ_final, V.hangle₀ w _ hwbd hw₁bd⟩

/-- **The uniform iterate of a cell.**  On the whole source region of the cell there is a single
iterate `N ≥ 1` of `f` realising the §6 composite `φ₀ ∘ wOfCell q ∘ φ₀⁻¹`. -/
theorem SrcC_uniform_iterate {j : ℕ} (hj : 1 ≤ j) {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1)
    (hn : |((n : ℤ) : ℝ)| ≤ V.η / 10 + 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w ∈ V.SrcC j k n,
      V.f ^[N] (V.P₀.φ w) = V.P₀.φ (V.wOfCell (j, k, n) w) := by
  classical
  have hex : ∀ w : ℂ, ∃ m : ℕ, w ∈ V.SrcC j k n →
      (1 ≤ m ∧ (∀ i < m, V.P₀.R^[i] w ∈ V.P₀.DR) ∧
        MandelDim.piExp (V.P₀.R^[m] w) = MandelDim.piExp (V.wOfCell (j, k, n) w) ∧
        |Complex.arg (V.wOfCell (j, k, n) w + 1 / (2 * MandelDim.rotOf V.f) - w)|
          < 2 * Real.pi / 3) := by
    intro w
    by_cases hw : w ∈ V.SrcC j k n
    · obtain ⟨m, h1, h2, h3, h4⟩ := V.cell_walk_data hj hSm hn hw
      exact ⟨m, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun hw' => absurd hw' hw⟩
  obtain ⟨M, hM⟩ : ∃ M : ℂ → ℕ, ∀ w ∈ V.SrcC j k n,
      (1 ≤ M w ∧ (∀ i < M w, V.P₀.R^[i] w ∈ V.P₀.DR) ∧
        MandelDim.piExp (V.P₀.R^[M w] w) = MandelDim.piExp (V.wOfCell (j, k, n) w) ∧
        |Complex.arg (V.wOfCell (j, k, n) w + 1 / (2 * MandelDim.rotOf V.f) - w)|
          < 2 * Real.pi / 3) :=
    ⟨fun w => Classical.choose (hex w), fun w hw => Classical.choose_spec (hex w) hw⟩
  exact uniform_iterate_of_orbit V.P₀ isOpen_univ V.hfdiff.differentiableOn
    ((Raw_open V hSm).inter (Metric.isOpen_ball))
    (SrcC_isConnected V hSm) (SrcC_sub_Dφ V hSm hn)
    (fun w => V.wOfCell (j, k, n) w)
    (V.wOfCell_differentiableOn_SrcC hj hSm (uOf_differentiableOn V))
    (fun w hw => V.hsub₀ (V.wOfCell_mem_ball hj hSm hw))
    M (fun w hw => (hM w hw).1) (fun w hw => (hM w hw).2.1) (fun w hw => (hM w hw).2.2.1)
    (fun w hw => (hM w hw).2.2.2) (fun _ _ _ => Set.mem_univ _)

end V10

end

end Work.Repel
