import Mathlib
import Submission.Work.L62LD.setup
import Submission.Work.L62LD.iterate_translate
import Submission.Work.L62LD.iterate_lipschitz

/-!
# L62LD — the quantitative separation of a backward chain of discs

Shishikura's Lemma 6.2 (lower end) separates the discs `W j` of a backward chain of `ĥ = d.E - β`
in the lift: two discs of different index must stay at distance at least `ε` modulo `ℤ`.

`Work.L62LD.sep_chain_const` makes the constant explicit.  Its inputs are

* the level-`0` separation `hsep0 : ∀ k : ℤ, ε₀ ≤ ‖u - v - k‖` for `u ∈ W 0` and `v ∈ W m`
  (`1 ≤ m ≤ J`);
* a compact `K ⊆ hd.Bl` containing the discs `W 1, …, W J` (`hWK`), together with a
  `δ`-neighbourhood `K + closedBall 0 δ ⊆ hd.Bl` on which `‖ĥ'‖ ≤ Δ` (`hKδ`, `hΔbd`).

Then *every* pair of distinct levels `i ≠ j ≤ J` is separated modulo `ℤ` by
`min ε₀ δ / (2 * Δ ^ J)`.

The mechanism is the only structure the chain carries that interacts with the integer
translation `k`: `ĥ` is `T`-equivariant on `hd.Bl` (`Work.L62.E_add_one_Bl`), so along an orbit
lying in `K ⊆ hd.Bl` its iterates commute with `w ↦ w + k`
(`Work.L62LD.iterate_translate`).  Given `u ∈ W i`, `v ∈ W j` with `i < j`, push both forward by
`ĥ^[i]`: this lands in `W 0` and `W (j - i)`, where the level-`0` separation `ε₀` applies, while
the inverse map is `Δ ^ i`-Lipschitz as long as the two orbits stay within the `δ`-ball built on
`K` (`Work.L62LD.iterate_lipschitz`).  The contradiction estimate gives
`ε₀ ≤ Δ ^ J ‖u - v - k‖` and hence the stated bound.  (When `i = 0` the pushforward is the
identity and the level-`0` separation is used directly; the argument is uniform in `i`.)
-/

namespace Work.L62LD

open Classical MandelDim Set

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

theorem sep_chain_const {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d)
    {β ζc : ℂ} {ρ ε₀ δ Δ : ℝ} {W : ℕ → Set ℂ} {K : Set ℂ} {J : ℕ}
    (hρ : 0 < ρ) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hΔ1 : 1 ≤ Δ)
    (hEdiff : DifferentiableOn ℂ d.E hd.Bl)
    (hKδ : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ hd.Bl)
    (hΔbd : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ →
      ‖deriv (fun w => d.E w - β) (v + z)‖ ≤ Δ)
    (hc : Work.L62LD.Chain d hd β W) (hW0 : W 0 = Metric.ball ζc ρ)
    (hWK : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ K)
    (hsep0 : ∀ m, 1 ≤ m → m ≤ J → ∀ u ∈ W 0, ∀ v ∈ W m, ∀ k : ℤ, ε₀ ≤ ‖u - v - (k : ℂ)‖) :
    ∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
      min ε₀ δ / (2 * Δ ^ J) ≤ ‖u - v - (k : ℂ)‖ := by
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1
  have hminpos : 0 < min ε₀ δ := lt_min hε₀ hδ
  have hΔJpos : 0 < Δ ^ J := pow_pos hΔpos J
  have hcpos : 0 < min ε₀ δ / (2 * Δ ^ J) := by
    apply div_pos hminpos; positivity
  have hKBl : K ⊆ hd.Bl := fun v hv => by
    have h := hKδ v hv 0 (by simp; linarith)
    simpa using h
  have hFd : DifferentiableOn ℂ (fun w => d.E w - β) hd.Bl := hEdiff.sub_const β
  -- the main step: distinct levels with `i < j`
  have key : ∀ i j, i < j → j ≤ J → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
      min ε₀ δ / (2 * Δ ^ J) ≤ ‖u - v - (k : ℂ)‖ := by
    intro i j hij hjJ u hu v hv k
    by_contra hcon
    push Not at hcon
    set w : ℂ := v + (k : ℂ) with hw
    have huw : ‖u - w‖ = ‖u - v - (k : ℂ)‖ := by
      rw [hw]; congr 1; ring
    have hd0 : ‖u - w‖ < min ε₀ δ / (2 * Δ ^ J) := by rw [huw]; exact hcon
    have hpow : Δ ^ i ≤ Δ ^ J := pow_le_pow_right₀ hΔ1 (by omega)
    have hpowpos : 0 < Δ ^ i := pow_pos hΔpos i
    -- the two pushed-forward points are still within the `δ`-ball of `K`
    have hltε : ‖u - w‖ * Δ ^ i ≤ δ := by
      have h1 : ‖u - w‖ * Δ ^ i < (min ε₀ δ / (2 * Δ ^ J)) * Δ ^ i :=
        mul_lt_mul_of_pos_right hd0 hpowpos
      have h2 : (min ε₀ δ / (2 * Δ ^ J)) * Δ ^ i ≤ (min ε₀ δ / (2 * Δ ^ J)) * Δ ^ J :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hcpos)
      have h3 : (min ε₀ δ / (2 * Δ ^ J)) * Δ ^ J = min ε₀ δ / 2 := by
        field_simp
      have h4 : min ε₀ δ / 2 ≤ δ / 2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      have h5 : δ / 2 < δ := by linarith
      linarith
    -- the orbit of `u` below level `i` stays in `K`
    have hpu : ∀ n, n < i → ((fun w => d.E w - β)^[n]) u ∈ K := by
      intro n hn
      exact hWK (i - n) (by omega) (by omega) (hc.iterate_mem (le_of_lt hn) hu)
    have hlip := iterate_lipschitz hδ hΔ1 hd.Bl_open hKδ hFd hΔbd i u w hpu hltε
    -- the orbit of `v` below level `i` stays in `K`, so `ĥ^[i]` commutes with `+k` there
    have hqv : ∀ m, m ≤ i → ((fun w => d.E w - β)^[m]) v ∈ K := by
      intro m hm
      exact hWK (j - m) (by omega) (by omega) (hc.iterate_mem (by omega) hv)
    have htr := iterate_translate d hd (S := K) hKBl hqv k
    -- the pushforward lands in `W 0` and `W (j - i)`
    have hai : ((fun w => d.E w - β)^[i]) u ∈ W 0 := by
      have h := hc.iterate_mem (le_refl i) hu
      simpa using h
    have hbi : ((fun w => d.E w - β)^[i]) v ∈ W (j - i) := hc.iterate_mem hij.le hv
    have hsep := hsep0 (j - i) (by omega) (by omega) (((fun w => d.E w - β)^[i]) u) hai
      (((fun w => d.E w - β)^[i]) v) hbi k
    have htrw : ((fun w => d.E w - β)^[i]) w = ((fun w => d.E w - β)^[i]) v + (k : ℂ) := by
      simpa [hw] using htr
    have heq : ‖((fun w => d.E w - β)^[i]) u - ((fun w => d.E w - β)^[i]) v - (k : ℂ)‖
        = ‖((fun w => d.E w - β)^[i]) u - ((fun w => d.E w - β)^[i]) w‖ := by
      rw [htrw]; congr 1; ring
    have hsep' : ε₀ ≤ ‖((fun w => d.E w - β)^[i]) u - ((fun w => d.E w - β)^[i]) w‖ := by
      rw [heq] at hsep; exact hsep
    have hfin : ε₀ ≤ Δ ^ J * ‖u - v - (k : ℂ)‖ := by
      calc ε₀ ≤ ‖((fun w => d.E w - β)^[i]) u - ((fun w => d.E w - β)^[i]) w‖ := hsep'
        _ ≤ Δ ^ i * ‖u - w‖ := hlip
        _ ≤ Δ ^ J * ‖u - w‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = Δ ^ J * ‖u - v - (k : ℂ)‖ := by rw [huw]
    have hlt2 : Δ ^ J * ‖u - v - (k : ℂ)‖ < ε₀ := by
      have h1 : Δ ^ J * ‖u - v - (k : ℂ)‖ < Δ ^ J * (min ε₀ δ / (2 * Δ ^ J)) :=
        mul_lt_mul_of_pos_left hcon hΔJpos
      have h2 : Δ ^ J * (min ε₀ δ / (2 * Δ ^ J)) = min ε₀ δ / 2 := by field_simp
      have h3 : min ε₀ δ / 2 ≤ ε₀ / 2 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      have h4 : ε₀ / 2 < ε₀ := by linarith
      linarith
    linarith
  intro i j hiJ hjJ hijne u hu v hv k
  rcases lt_or_gt_of_ne hijne with hlt | hgt
  · exact key i j hlt hjJ u hu v hv k
  · -- symmetry: exchange the two levels and negate the integer
    have h := key j i hgt hiJ v hv u hu (-k)
    rw [show (((-k : ℤ)) : ℂ) = -(k : ℂ) by push_cast; ring] at h
    rw [show v - u - -(k : ℂ) = -(u - v - (k : ℂ)) by ring, norm_neg] at h
    exact h

end

end Work.L62LD
