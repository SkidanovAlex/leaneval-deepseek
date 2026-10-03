import Mathlib
import Submission.Work.Repel.V10.chain_v9_setup
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.walk_of_sub
import Submission.Work.Repel.chain_preimage_mem
import Submission.Work.Repel.walk_of_germ1

/-!
# `Work.Repel.cell_iterate` : the pointwise identity `f^n (φ₀ w) = φ₀ w₁` of one §6 cell

This is the pointwise input for the "island" step (row 12 of the step table of
`Work.Repel.chain_returns_v9`): for a cell whose level-0 source point is `w` and whose level-0
target point is `w₁`, the two Fatou coordinates differ by an iterate of `f`.

The chain of maps of a cell is

  `w ↦ ζ = s·π w ↦ u = (φ₁|Dsm)⁻¹ ζ ↦ u' = ĥ^j u - k ↦ w₁ ↦ P₀.φ w₁`,

so the proof has three ingredients:

* the walk of the *return map* `R₁ = P₁.R` along the chain: `R₁^[i] u = ĥ^[i] u - i·k₀`, where `k₀`
  is the integer with `1/rotOf (germ1 s P₀.R) = β + k₀` (`Work.Repel.walk_of_sub`).  This licenses
  the level-1 orbit field `P₁.orbit` with `m = j ≥ 1`; its third conjunct
  (`∀ i < n₁, ǧ^[i] (φ₁ u) ∈ Dgerm1 s P₀.DR`) is *exactly* the hypothesis `horbit` of
  `Work.Repel.walk_of_germ1`;
* the bridge between the level-1 orbit and the level-0 walk of `P₀.R`
  (`Work.Repel.walk_of_germ1`), giving `P₀.R^[i] w ∈ P₀.DR` for `i < n₁` together with
  `ǧ^[i] (s·π w) = s·π (P₀.R^[i] w)`; the `n₁`-th step (not covered by `walk_of_germ1`) is the
  helper `germ1_iterate_of_walk`;
* the level-0 orbit field `P₀.orbit` (`m = n₁`), applied to `w ∈ P₀.DR ∩ P₀.Dφ` and
  `w₁ ∈ P₀.Dφ`, with the angle condition supplied by `hangle₀` and `hwt₀`
  (`‖w‖, ‖w₁‖ ≤ 2η`; note `hw : w ∈ P₀.DR` is used through `walk_of_germ1`).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- `π` is invariant under the shift `x ↦ x + a - m` with `a : ℤ` and `m : ℕ`. -/
lemma piExp_add_intCast_sub_natCast (x : ℂ) (a : ℤ) (m : ℕ) :
    MandelDim.piExp (x + ((a : ℤ) : ℂ) - ((m : ℕ) : ℂ)) = MandelDim.piExp x := by
  have h : x + ((a : ℤ) : ℂ) - ((m : ℕ) : ℂ) = x + (((a - (m : ℤ)) : ℤ) : ℂ) := by
    push_cast; ring
  rw [h, Work.Horn.MandelDim.piExp_add_intCast]

/-- A point of the level-1 disc `Sm1` has modulus at most `2η₁`. -/
lemma norm_le_two_eta₁_of_mem_Sm1 (V : V10) {u : ℂ} (hu : u ∈ V.Sm1) : ‖u‖ ≤ 2 * V.η₁ := by
  have hη : 0 < V.η₁ := V.hη₁pos
  by_cases h1 : V.sgn = 1
  · have hmem : u ∈ MandelDim.Dsm V.η₁ := by simpa [V10.Sm1, h1] using hu
    have h' := norm_bounds_of_mem_Dsm hη hmem
    linarith [h'.2]
  · have hmem : u ∈ MandelDim.Dsm (-V.η₁) := by simpa [V10.Sm1, h1] using hu
    have h' := norm_bounds_of_mem_Dsm_neg hη hmem
    linarith [h'.2]

/-- The iterate index `n` of `walk_of_germ1` can be pushed one step further: if the first `n` terms
of the level-0 walk stay in `DR` and the level-1 iterates correspond with the level-0 ones for
`i < n`, then the `n`-th iterates correspond as well. -/
lemma germ1_iterate_of_walk {R : ℂ → ℂ} {DR : Set ℂ} (hDR : MandelDim.IsTInvariant DR)
    (hReq : ∀ w ∈ DR, R (w + 1) = R w + 1) {s : ℂ} (hs : s ≠ 0) {w : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hmem : ∀ i < n, R^[i] w ∈ DR)
    (heq : ∀ i < n, (germ1 s R)^[i] (s * MandelDim.piExp w) = s * MandelDim.piExp (R^[i] w)) :
    (germ1 s R)^[n] (s * MandelDim.piExp w) = s * MandelDim.piExp (R^[n] w) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m < m + 1 := Nat.lt_succ_self m
  rw [show (germ1 s R)^[m + 1] (s * MandelDim.piExp w)
      = (germ1 s R) ((germ1 s R)^[m] (s * MandelDim.piExp w)) from
    Function.iterate_succ_apply' _ m _]
  rw [heq m hm, germ1_mul_piExp hs,
    Work.Horn.MandelDim.pushdown_piExp hDR (fun x hx _ => hReq x hx) (hmem m hm)]
  rw [show R^[m + 1] w = R (R^[m] w) from Function.iterate_succ_apply' _ m _]

theorem cell_iterate (V : Work.Repel.V10) {j : ℕ} (hj : 1 ≤ j) {k : ℤ} {u w w₁ u' : ℂ}
    (hu : u ∈ (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' V.W j)
    (huSm : u ∈ V.Sm1)
    (hu' : u' ∈ V.W 0)
    (hw : w ∈ V.P₀.DR) (hwDφ : w ∈ V.P₀.Dφ) (hwbd : ‖w‖ ≤ 2 * V.η)
    (hpi : V.s * MandelDim.piExp w = V.P₁.φ u)
    (hchain : (fun x => V.R x - V.β)^[j] u = u' + ((k : ℤ) : ℂ))
    (hw₁ : w₁ ∈ Metric.ball V.wt₀ V.ρ₀) (hw₁Dφ : w₁ ∈ V.P₀.Dφ)
    (hπw₁ : MandelDim.piExp w₁ = V.P₁.φ u' / V.s) :
    ∃ n : ℕ, 1 ≤ n ∧ V.f^[n] (V.P₀.φ w) = V.P₀.φ w₁ := by
  -- the integer shift `k₀` relating the return map `P₁.R` to `ĥ = R - β`
  obtain ⟨k₀, -, hk₀⟩ := V.hk
  have hc : ∀ x : ℂ, V.R x - V.β = V.P₁.R x + ((k₀ : ℕ) : ℂ) := by
    intro x
    rw [V.hR, hk₀]
    ring
  -- walk of the return map along the chain
  have hwalk := walk_of_sub V.hIsChain V.hReq V.P₁.R_equiv V.hDRsub hc hu
  have hwalkDR : ∀ i < j, V.P₁.R^[i] u ∈ V.P₁.DR := hwalk.1
  have hwalkR : ∀ i ≤ j, V.P₁.R^[i] u = (fun x => V.R x - V.β)^[i] u - ((i * k₀ : ℕ) : ℂ) :=
    hwalk.2
  -- domains and moduli of the level-1 source and target
  have huDφ : u ∈ V.P₁.Dφ := V.Sm1_sub_Dφ huSm
  have hu'ball : u' ∈ Metric.ball V.cbase V.ρ := by
    rw [← V.hbase]; exact hu'
  have hu'Dφ : u' ∈ V.P₁.Dφ := V.hsub₁ hu'ball
  have hu_norm : ‖u‖ ≤ 2 * V.η₁ := norm_le_two_eta₁_of_mem_Sm1 V huSm
  have hu'_norm : ‖u'‖ ≤ 2 * V.η₁ := by
    have h : ‖u' - V.cbase‖ < V.ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hu'ball; exact hu'ball
    have h2 : ‖u'‖ ≤ ‖u' - V.cbase‖ + ‖V.cbase‖ := by
      calc ‖u'‖ = ‖(u' - V.cbase) + V.cbase‖ := by congr 1; ring
        _ ≤ ‖u' - V.cbase‖ + ‖V.cbase‖ := norm_add_le _ _
    linarith [h, V.hcbase, V.hη₁pos, h2]
  -- the `π`-images agree at the end of the chain
  have hpi_j : MandelDim.piExp (V.P₁.R^[j] u) = MandelDim.piExp u' := by
    rw [hwalkR j le_rfl, hchain]
    exact piExp_add_intCast_sub_natCast u' k (j * k₀)
  -- level-1 orbit (Shishikura §6, (4.2.3) at level 1)
  obtain ⟨n₁, hn₁, hn₁_eq, hn₁_mem⟩ :=
    V.P₁.orbit u huDφ u' hu'Dφ j hj hwalkDR hpi_j (V.hangle₁ u u' hu_norm hu'_norm)
  -- rewrite the level-1 orbit in terms of `π` at level 0
  have hsπw : V.P₁.φ u = V.s * MandelDim.piExp w := hpi.symm
  have hsπw₁ : V.s * MandelDim.piExp w₁ = V.P₁.φ u' := by
    rw [hπw₁, mul_div_cancel₀ _ V.hs]
  have hbridge : (germ1 V.s V.P₀.R)^[n₁] (V.s * MandelDim.piExp w)
      = V.s * MandelDim.piExp w₁ := by
    rw [← hsπw, hn₁_eq, hsπw₁]
  -- the third conjunct of `P₁.orbit` is exactly `horbit` of `walk_of_germ1`
  have horbit : ∀ i < n₁, (germ1 V.s V.P₀.R)^[i] (V.s * MandelDim.piExp w)
      ∈ (fun ζ => V.s * ζ) '' (insert 0 (MandelDim.piExp '' V.P₀.DR)) := by
    intro i hi
    have h := hn₁_mem i hi
    rwa [hsπw] at h
  -- the level-1 orbit never hits `0` (else all later iterates would, contradicting `hbridge`)
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
    have hcontra : V.s * MandelDim.piExp w₁ = 0 := by rw [← hbridge, hsplit, hzero]
    exact mul_ne_zero V.hs (Work.Horn.MandelDim.piExp_ne_zero w₁) hcontra
  -- bridge: the level-1 orbit is the `π`-image of the level-0 walk
  have hDRT : MandelDim.IsTInvariant V.P₀.DR := V.P₀.R_equiv.1
  have hEreq : ∀ x ∈ V.P₀.DR, V.P₀.R (x + 1) = V.P₀.R x + 1 :=
    fun x hx => V.P₀.R_equiv.2 x hx
  obtain ⟨hwalk₀_mem, hwalk₀_eq⟩ := walk_of_germ1 hDRT hEreq V.hs hw horbit hne_same
  -- the level-0 walk reaches a point with the `π`-image of `w₁` in `n₁ ≥ 1` steps
  have hπ_final : MandelDim.piExp (V.P₀.R^[n₁] w) = MandelDim.piExp w₁ := by
    have hstep := germ1_iterate_of_walk hDRT hEreq V.hs hn₁ hwalk₀_mem hwalk₀_eq
    rw [hstep] at hbridge
    exact mul_left_cancel₀ V.hs hbridge
  -- level-0 orbit (Shishikura §6, (4.2.3) at level 0)
  have hw₁bd : ‖w₁‖ ≤ 2 * V.η := by
    have h : ‖w₁ - V.wt₀‖ < V.ρ₀ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw₁; exact hw₁
    have h2 : ‖w₁‖ ≤ ‖w₁ - V.wt₀‖ + ‖V.wt₀‖ := by
      calc ‖w₁‖ = ‖(w₁ - V.wt₀) + V.wt₀‖ := by congr 1; ring
        _ ≤ ‖w₁ - V.wt₀‖ + ‖V.wt₀‖ := norm_add_le _ _
    linarith [h, V.hwt₀, h2]
  obtain ⟨n, hn1, hn2, -⟩ :=
    V.P₀.orbit w hwDφ w₁ hw₁Dφ n₁ hn₁ hwalk₀_mem hπ_final
      (V.hangle₀ w w₁ hwbd hw₁bd)
  exact ⟨n, hn1, hn2⟩

end

end Work.Repel
