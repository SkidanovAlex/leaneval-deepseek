import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62LD.iterate_lipschitz

/-! ## `sep_chain_abstract`: separation of the discs of a `T`-equivariant chain

This is `Work.L62LD.sep_chain_const` with the horn `hd.Bl` and the map `fun w => d.E w - β`
replaced by an abstract open set `O` and an abstract map `F`, and with the `T`-equivariance of
`d.E` replaced by the abstract hypothesis `hT`.  It is the separation engine of the perturbed
head: applied with `F = fun w => R w - β` and `O = int K` it separates the discs of the
*perturbed* chain without any reference to the model chain. -/

namespace Work.L62

open Set Metric Filter Topology
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

/-- **Separation of the levels of a `T`-equivariant chain.**  Let `W 0 = ball ζc ρ` and
`F '' W (j+1) = W j` injectively, `W j ⊆ K` for `1 ≤ j ≤ J`, with `K` a compactum whose
`δ`-neighbourhood lies in the open set `O` where `F` is holomorphic and `‖deriv F‖ ≤ Δ`.  If
moreover `F` commutes with the integer translations on `O` and the first disc is `ε₀`-separated
from the later discs modulo `ℤ`, then *all* the discs are separated modulo `ℤ` by
`min ε₀ δ / (2 Δ^J)`. -/
theorem sep_chain_abstract {F : ℂ → ℂ} {K O : Set ℂ} {ζc : ℂ} {ρ ε₀ δ Δ : ℝ}
    {W : ℕ → Set ℂ} {J : ℕ}
    (hρ : 0 < ρ) (hε₀ : 0 < ε₀) (hδ : 0 < δ) (hΔ1 : 1 ≤ Δ)
    (hO : IsOpen O) (hFd : DifferentiableOn ℂ F O)
    (hT : ∀ w ∈ O, ∀ k : ℤ, F (w + (k : ℂ)) = F w + (k : ℂ))
    (hKδ : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → v + z ∈ O)
    (hΔbd : ∀ v ∈ K, ∀ z : ℂ, ‖z‖ ≤ δ → ‖deriv F (v + z)‖ ≤ Δ)
    (hchain : ∀ j, j < J → Set.InjOn F (W (j + 1)) ∧ F '' W (j + 1) = W j)
    (hW0 : W 0 = Metric.ball ζc ρ)
    (hWK : ∀ j, 1 ≤ j → j ≤ J → W j ⊆ K)
    (hsep0 : ∀ m, 1 ≤ m → m ≤ J → ∀ u ∈ W 0, ∀ v ∈ W m, ∀ k : ℤ,
      ε₀ ≤ ‖u - v - (k : ℂ)‖) :
    ∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, ∀ k : ℤ,
      min ε₀ δ / (2 * Δ ^ J) ≤ ‖u - v - (k : ℂ)‖ := by
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1
  have hKsubO : K ⊆ O := fun v hv => by
    have h := hKδ v hv 0 (by simp; linarith)
    simpa using h
  have hminpos : 0 < min ε₀ δ := lt_min hε₀ hδ
  have hΔJpos : 0 < Δ ^ J := pow_pos hΔpos J
  have hcpos : 0 < min ε₀ δ / (2 * Δ ^ J) := by
    apply div_pos hminpos; positivity
  -- ### the iterates land in the lower-numbered discs
  have hiter_mem : ∀ (n i : ℕ), i ≤ J → n ≤ i → ∀ u ∈ W i, (F^[n]) u ∈ W (i - n) := by
    intro n
    induction n with
    | zero => intro i _ _ u hu; simpa using hu
    | succ m ih =>
        intro i hiJ hm1 u hu
        have hmi : m ≤ i := le_of_lt (Nat.lt_of_succ_le hm1)
        have hmJ : i - (m + 1) < J := by omega
        have hstep : F ((F^[m]) u) ∈ W (i - (m + 1)) := by
          have hmem : (F^[m]) u ∈ W (i - m) := ih i hiJ hmi u hu
          have hidx : i - m = (i - (m + 1)) + 1 := by omega
          rw [hidx] at hmem
          rw [← (hchain (i - (m + 1)) hmJ).2]
          exact ⟨(F^[m]) u, hmem, rfl⟩
        simpa only [Function.iterate_succ_apply'] using hstep
  have hiter_K : ∀ (n i : ℕ), i ≤ J → n < i → ∀ u ∈ W i, (F^[n]) u ∈ K := by
    intro n i hiJ hni u hu
    exact hWK (i - n) (by omega) (by omega) (hiter_mem n i hiJ hni.le u hu)
  -- ### translation commutes with the iterates along an orbit in `K`
  have htrans : ∀ (n : ℕ) (y : ℂ), (∀ m, m ≤ n → (F^[m]) y ∈ K) → ∀ k : ℤ,
      (F^[n]) (y + (k : ℂ)) = (F^[n]) y + (k : ℂ) := by
    intro n
    induction n with
    | zero => intro y _ k; simp
    | succ m ih =>
        intro y hy k
        have hm : ∀ t, t ≤ m → (F^[t]) y ∈ K := fun t ht => hy t (by omega)
        have hmemO : (F^[m]) y ∈ O := hKsubO (hy m (by omega))
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih y hm k,
          hT _ hmemO k]
  -- ### the main step
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
    have hpu : ∀ n, n < i → (F^[n]) u ∈ K := fun n hn => hiter_K n i (by omega) hn u hu
    have hlip := Work.L62LD.iterate_lipschitz (F := F) (K := K) (O := O) (Δ := Δ) (δ := δ)
      hδ hΔ1 hO hKδ hFd hΔbd i u w hpu hltε
    have hqv : ∀ m, m ≤ i → (F^[m]) v ∈ K := by
      intro m hm
      exact hiter_K m j hjJ (by omega) v hv
    have htr := htrans i v hqv k
    have hai : (F^[i]) u ∈ W 0 := by
      have h := hiter_mem i i (by omega) le_rfl u hu
      rwa [Nat.sub_self] at h
    have hbi : (F^[i]) v ∈ W (j - i) := hiter_mem i j hjJ hij.le v hv
    have hsep := hsep0 (j - i) (by omega) (by omega) ((F^[i]) u) hai ((F^[i]) v) hbi k
    have htrw : (F^[i]) w = (F^[i]) v + (k : ℂ) := by
      simpa [hw] using htr
    have heq : ‖(F^[i]) u - (F^[i]) v - (k : ℂ)‖ = ‖(F^[i]) u - (F^[i]) w‖ := by
      rw [htrw]; congr 1; ring
    have hsep' : ε₀ ≤ ‖(F^[i]) u - (F^[i]) w‖ := by
      rw [heq] at hsep; exact hsep
    have hfin : ε₀ ≤ Δ ^ J * ‖u - v - (k : ℂ)‖ := by
      calc ε₀ ≤ ‖(F^[i]) u - (F^[i]) w‖ := hsep'
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
  · have h := key j i hgt hiJ v hv u hu (-k)
    rw [show (((-k : ℤ)) : ℂ) = -(k : ℂ) by push_cast; ring] at h
    rw [show v - u - -(k : ℂ) = -(u - v - (k : ℂ)) by ring, norm_neg] at h
    exact h

end

end Work.L62
