import Mathlib
import Submission.Work.Transfer.Setup
import Submission.Work.Transfer.critOrbit_lipschitz_of_subset
import Submission.Work.Transfer.iterate_equiv

/-!
# `Work.Transfer.hitSet_subset_frontier`

Every parameter at which the critical value `critOrbit m c` is realised by the coding map of a
holomorphic motion (`c ∈ HitSet m c₁ ρ₁ phi W`) lies in the frontier of the Mandelbrot set.

Two ingredients.

* `c ∈ Mandelbrot`: the code `w` realising the critical value has a bounded forward orbit
  (`MotionData.orbBdd`), so the critical orbit of `c` is bounded.

* `c ∉ interior Mandelbrot`: if a ball `ball c ε` around `c` were contained in `M`, the critical
  orbits `critOrbit j` would be uniformly bounded by `2` on it, hence uniformly Lipschitz there
  (`Work.Transfer.critOrbit_lipschitz_of_subset`, from Cauchy estimates and
  `Work.Transfer.family_lipschitz_of_norm_le_ball`).  Pick two words `x₁ ≠ x₂` (possible since
  `2 ≤ N`); their images `phi c xᵢ` under the motion stay `g > 0` apart (`MotionData.inj`).  For
  every small `R`, the hitting hypothesis produces — for the codes `uᵢ = w|k₀ ++ xᵢ` agreeing with
  `w` on a long prefix — hit points `dᵢ ∈ ball c R` with `critOrbit m dᵢ = phi dᵢ uᵢ`.  Iterating
  the equivariance of the motion (`MotionData.equiv`) along the common prefix turns this into
  `critOrbit (S + m) dᵢ = phi dᵢ xᵢ` with the *same* iterate `S + m` for `i = 1, 2`.  Uniform
  Lipschitz continuity of `critOrbit (S + m)` on `ball c (ε/2)` then forces
  `g ≤ 2 L' R + 2 κ R`, which is `< g` for `R` small.  Contradiction.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open Classical

noncomputable section

namespace Work.Transfer

/-! ## The main theorem -/

theorem hitSet_subset_frontier {N : ℕ} (hM : MandelDim.MsetStatement) (hN : 2 ≤ N)
    {c₀ : ℂ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {ρ a : ℝ}
    {phi : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ) (hMD : Work.Transfer.MotionData c₀ N τ n p ρ a phi)
    (m : ℕ) {c₁ : ℂ} (hc₁ : c₁ ∈ Metric.ball c₀ ρ) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hsub : Metric.ball c₁ ρ₁ ⊆ Metric.ball c₀ ρ)
    (hne : ∀ w : ℕ → Fin N, ∃ z ∈ Metric.ball c₀ ρ, Work.Transfer.critOrbit m z ≠ phi z w)
    (hzt : ∀ (w : ℕ → Fin N),
      (∃ z ∈ Metric.ball c₀ ρ, Work.Transfer.critOrbit m z ≠ phi z w) →
      ∀ {R : ℝ} {c_s : ℂ}, 0 < R → c_s ∈ Metric.ball c₀ ρ → Metric.ball c_s R ⊆ Metric.ball c₀ ρ →
        Work.Transfer.critOrbit m c_s = phi c_s w →
        ∃ k₀ : ℕ, ∀ u : ℕ → Fin N, (∀ j < k₀, u j = w j) →
          ∃ c ∈ Metric.ball c_s R, Work.Transfer.critOrbit m c = phi c u)
    (W : Set (ℕ → Fin N)) :
    Work.Transfer.HitSet m c₁ ρ₁ phi W ⊆
      frontier LeanEval.Dynamics.MandelbrotBoundary.Mandelbrot := by
  intro c hc
  obtain ⟨hcball, w, -, hceq⟩ := hc
  have hcc₀ : c ∈ Metric.ball c₀ ρ := hsub hcball
  -- Step 1: a hit parameter lies in `M`.
  have hcM : c ∈ Mandelbrot := by
    obtain ⟨B, hB⟩ := hMD.orbBdd
    exact mem_mandelbrot_of_bound_orbit hM (fun j => hB c hcc₀ w j) hceq
  -- Step 2: a hit parameter is not in the interior of `M`.
  have hnotint : c ∉ interior Mandelbrot := by
    intro hint
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    obtain ⟨κ, hκ0, hκl⟩ := critOrbit_lipschitz_of_subset hM hε hεsub
    -- Lipschitz dependence on the parameter of the motion.
    obtain ⟨L, hL⟩ := hMD.lipschitz
    have hL0 : 0 ≤ max L 0 := le_max_right _ _
    have hLl : ∀ c' ∈ Metric.ball c₀ ρ, ∀ c'' ∈ Metric.ball c₀ ρ, ∀ ω : ℕ → Fin N,
        ‖phi c' ω - phi c'' ω‖ ≤ max L 0 * ‖c' - c''‖ := by
      intro c' hc' c'' hc'' ω
      have h := hL c' hc' c'' hc'' ω
      calc ‖phi c' ω - phi c'' ω‖ ≤ L * ‖c' - c''‖ := h
        _ ≤ max L 0 * ‖c' - c''‖ := mul_le_mul_of_nonneg_right (le_max_left L 0) (norm_nonneg _)
    -- two distinct words
    have hN0 : 0 < N := by omega
    have hN1 : 1 < N := by omega
    set x₁ : ℕ → Fin N := fun _ => (⟨0, hN0⟩ : Fin N) with hx₁def
    set x₂ : ℕ → Fin N := fun _ => (⟨1, hN1⟩ : Fin N) with hx₂def
    have hxne : x₁ ≠ x₂ := by
      intro h
      have hv : (0 : ℕ) = 1 := congrArg Fin.val (congrFun h 0)
      exact Nat.zero_ne_one hv
    have hg : 0 < ‖phi c x₁ - phi c x₂‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact hxne (hMD.inj c hcc₀ h)
    -- distance of `c` to the boundary of the smaller ball
    have hδpos : 0 < ρ₁ - dist c c₁ := by
      have h := Metric.mem_ball.mp hcball
      linarith
    -- the small radius on which everything is played out
    obtain ⟨R, hRpos, hRε, hRδ, hRκL⟩ : ∃ R : ℝ, 0 < R ∧ R ≤ ε / 2 ∧ R ≤ ρ₁ - dist c c₁ ∧
        2 * κ * R + 2 * (max L 0) * R < ‖phi c x₁ - phi c x₂‖ / 2 := by
      have hκL0 : 0 ≤ κ + max L 0 := by have := hκ0; have := hL0; linarith
      have hC : 0 < ‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1)) :=
        div_pos hg (by linarith)
      have hm0 : 0 < min (min (ε / 2) (ρ₁ - dist c c₁))
          (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) :=
        lt_min (lt_min (by linarith) hδpos) hC
      refine ⟨min (min (ε / 2) (ρ₁ - dist c c₁))
          (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) / 2,
        by linarith, ?_, ?_, ?_⟩
      · have h6 : min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) ≤ ε / 2 :=
          le_trans (min_le_left _ _) (min_le_left _ _)
        linarith
      · have h6 : min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) ≤ ρ₁ - dist c c₁ :=
          le_trans (min_le_left _ _) (min_le_right _ _)
        linarith
      · have hm : min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1)))
            ≤ ‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1)) := min_le_right _ _
        have h1 : 2 * κ * (min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) / 2)
            + 2 * (max L 0) * (min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) / 2)
            = (κ + max L 0) * (min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1)))) := by ring_nf
        rw [h1]
        have h2 : (κ + max L 0) * (min (min (ε / 2) (ρ₁ - dist c c₁))
            (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))))
            ≤ (κ + max L 0) * (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1))) :=
          mul_le_mul_of_nonneg_left hm hκL0
        have h3 : (κ + max L 0) * (‖phi c x₁ - phi c x₂‖ / (16 * (κ + max L 0 + 1)))
            < ‖phi c x₁ - phi c x₂‖ / 2 := by
          rw [← mul_div_assoc,
            div_lt_iff₀ (by linarith : (0 : ℝ) < 16 * (κ + max L 0 + 1))]
          nlinarith [hg, hκ0, hL0]
        linarith
    -- geometry: the small ball stays inside `ball c₁ ρ₁ ⊆ ball c₀ ρ`
    have hRsub₁ : Metric.ball c R ⊆ Metric.ball c₁ ρ₁ := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      have h1 : dist z c₁ ≤ dist z c + dist c c₁ := dist_triangle _ _ _
      linarith
    have hRsub : Metric.ball c R ⊆ Metric.ball c₀ ρ := hRsub₁.trans hsub
    -- the hitting hypothesis at `c` (a hit point with code `w`)
    obtain ⟨k₀, hk₀⟩ := hzt w (hne w) hRpos hcc₀ hRsub hceq
    -- the two perturbed codes
    set u₁ : ℕ → Fin N := (fun j => if j < k₀ then w j else x₁ (j - k₀)) with hu₁def
    set u₂ : ℕ → Fin N := (fun j => if j < k₀ then w j else x₂ (j - k₀)) with hu₂def
    have hu₁agree : ∀ j < k₀, u₁ j = w j := by
      intro j hj
      rw [hu₁def]
      simp [hj]
    have hu₂agree : ∀ j < k₀, u₂ j = w j := by
      intro j hj
      rw [hu₂def]
      simp [hj]
    obtain ⟨d₁, hd₁ball, hd₁eq⟩ := hk₀ u₁ hu₁agree
    obtain ⟨d₂, hd₂ball, hd₂eq⟩ := hk₀ u₂ hu₂agree
    have hd₁c₀ : d₁ ∈ Metric.ball c₀ ρ := hRsub hd₁ball
    have hd₂c₀ : d₂ ∈ Metric.ball c₀ ρ := hRsub hd₂ball
    have hd₁half : d₁ ∈ Metric.ball c (ε / 2) := Metric.ball_subset_ball hRε hd₁ball
    have hd₂half : d₂ ∈ Metric.ball c (ε / 2) := Metric.ball_subset_ball hRε hd₂ball
    have hd₁R : ‖d₁ - c‖ < R := by
      have h := Metric.mem_ball.mp hd₁ball
      rwa [dist_eq_norm] at h
    have hd₂R : ‖d₂ - c‖ < R := by
      have h := Metric.mem_ball.mp hd₂ball
      rwa [dist_eq_norm] at h
    have hd₁R' : ‖c - d₁‖ < R := by rw [norm_sub_rev]; exact hd₁R
    have hd₂R' : ‖c - d₂‖ < R := by rw [norm_sub_rev]; exact hd₂R
    -- the two perturbations agree with `w` on the first `k₀` letters
    have hsum₁ : (∑ j ∈ Finset.range k₀, n (u₁ j)) = ∑ j ∈ Finset.range k₀, n (w j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hu₁agree j (Finset.mem_range.mp hj)]
    have hsum₂ : (∑ j ∈ Finset.range k₀, n (u₂ j)) = ∑ j ∈ Finset.range k₀, n (w j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hu₂agree j (Finset.mem_range.mp hj)]
    -- shifting the perturbed codes past the common prefix gives `xᵢ`
    have hsh₁ : (fun j => u₁ (j + k₀)) = x₁ := by
      funext j
      rw [hu₁def]
      show (if j + k₀ < k₀ then w (j + k₀) else x₁ (j + k₀ - k₀)) = x₁ j
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left k₀ j)), Nat.add_sub_cancel]
    have hsh₂ : (fun j => u₂ (j + k₀)) = x₂ := by
      funext j
      rw [hu₂def]
      show (if j + k₀ < k₀ then w (j + k₀) else x₂ (j + k₀ - k₀)) = x₂ j
      rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left k₀ j)), Nat.add_sub_cancel]
    -- iterate the equivariance along the common prefix
    have hit₁ : (Tc d₁)^[∑ j ∈ Finset.range k₀, n (w j)] (phi d₁ u₁) = phi d₁ x₁ := by
      rw [← hsum₁]
      simpa [hsh₁] using iterate_equiv hMD hd₁c₀ u₁ k₀
    have hit₂ : (Tc d₂)^[∑ j ∈ Finset.range k₀, n (w j)] (phi d₂ u₂) = phi d₂ x₂ := by
      rw [← hsum₂]
      simpa [hsh₂] using iterate_equiv hMD hd₂c₀ u₂ k₀
    have hcrit₁ : critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₁ = phi d₁ x₁ := by
      rw [← critOrbit_iterate_apply m (∑ j ∈ Finset.range k₀, n (w j)) d₁, hd₁eq]
      exact hit₁
    have hcrit₂ : critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₂ = phi d₂ x₂ := by
      rw [← critOrbit_iterate_apply m (∑ j ∈ Finset.range k₀, n (w j)) d₂, hd₂eq]
      exact hit₂
    -- the key (contradictory) estimate
    have hLT1 : ‖phi c x₁ - phi d₁ x₁‖ ≤ max L 0 * ‖c - d₁‖ := hLl c hcc₀ d₁ hd₁c₀ x₁
    have hLT2 : ‖phi d₂ x₂ - phi c x₂‖ ≤ max L 0 * ‖c - d₂‖ := by
      rw [norm_sub_rev]
      exact hLl c hcc₀ d₂ hd₂c₀ x₂
    have hUP : ‖critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₁
        - critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₂‖ ≤ κ * ‖d₁ - d₂‖ :=
      hκl _ d₁ hd₁half d₂ hd₂half
    have hnorm : ‖phi d₁ x₁ - phi d₂ x₂‖ =
        ‖critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₁
          - critOrbit ((∑ j ∈ Finset.range k₀, n (w j)) + m) d₂‖ := by
      rw [hcrit₁, hcrit₂]
    have hd₁₂ : ‖d₁ - d₂‖ < 2 * R := by
      have h3 : ‖d₁ - d₂‖ ≤ ‖d₁ - c‖ + ‖d₂ - c‖ := by
        calc ‖d₁ - d₂‖ = ‖(d₁ - c) + (c - d₂)‖ := by ring_nf
          _ ≤ ‖d₁ - c‖ + ‖c - d₂‖ := norm_add_le _ _
          _ = ‖d₁ - c‖ + ‖d₂ - c‖ := by rw [norm_sub_rev c d₂]
      linarith
    have hkey : ‖phi c x₁ - phi c x₂‖ ≤ 2 * (max L 0) * R + 2 * κ * R := by
      have htri : ‖phi c x₁ - phi c x₂‖ ≤
          ‖phi c x₁ - phi d₁ x₁‖ + ‖phi d₁ x₁ - phi d₂ x₂‖ + ‖phi d₂ x₂ - phi c x₂‖ := by
        have h1 : phi c x₁ - phi c x₂ = (phi c x₁ - phi d₁ x₁)
            + (phi d₁ x₁ - phi d₂ x₂) + (phi d₂ x₂ - phi c x₂) := by ring
        rw [h1]
        calc ‖(phi c x₁ - phi d₁ x₁) + (phi d₁ x₁ - phi d₂ x₂) + (phi d₂ x₂ - phi c x₂)‖
            ≤ ‖(phi c x₁ - phi d₁ x₁) + (phi d₁ x₁ - phi d₂ x₂)‖
              + ‖phi d₂ x₂ - phi c x₂‖ := norm_add_le _ _
          _ ≤ (‖phi c x₁ - phi d₁ x₁‖ + ‖phi d₁ x₁ - phi d₂ x₂‖)
              + ‖phi d₂ x₂ - phi c x₂‖ := by
              linarith [norm_add_le (phi c x₁ - phi d₁ x₁) (phi d₁ x₁ - phi d₂ x₂)]
      have e1 : max L 0 * ‖c - d₁‖ ≤ max L 0 * R := mul_le_mul_of_nonneg_left hd₁R'.le hL0
      have e2 : max L 0 * ‖c - d₂‖ ≤ max L 0 * R := mul_le_mul_of_nonneg_left hd₂R'.le hL0
      have e3 : κ * ‖d₁ - d₂‖ ≤ κ * (2 * R) := mul_le_mul_of_nonneg_left hd₁₂.le hκ0
      calc ‖phi c x₁ - phi c x₂‖
          ≤ ‖phi c x₁ - phi d₁ x₁‖ + ‖phi d₁ x₁ - phi d₂ x₂‖ + ‖phi d₂ x₂ - phi c x₂‖ := htri
        _ ≤ max L 0 * ‖c - d₁‖ + κ * ‖d₁ - d₂‖ + max L 0 * ‖c - d₂‖ := by
            rw [hnorm]
            linarith
        _ ≤ 2 * (max L 0) * R + 2 * κ * R := by linarith
    have : ‖phi c x₁ - phi c x₂‖ < ‖phi c x₁ - phi c x₂‖ := by linarith
    exact lt_irrefl _ this
  -- Step 3: assemble.
  have hcl : c ∈ closure Mandelbrot := by
    rw [hM.1.closure_eq]
    exact hcM
  have hclc : c ∈ closure Mandelbrotᶜ := by
    have h : (interior Mandelbrot)ᶜ = closure Mandelbrotᶜ := by
      have h1 := closure_eq_compl_interior_compl (s := Mandelbrotᶜ)
      rw [compl_compl] at h1
      exact h1.symm
    exact h ▸ hnotint
  rw [frontier_eq_closure_inter_closure]
  exact ⟨hcl, hclc⟩

end Work.Transfer

end
