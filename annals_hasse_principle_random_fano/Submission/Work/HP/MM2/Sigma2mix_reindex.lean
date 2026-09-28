import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MMReindex
import Submission.Work.HP.FM4.xi_sum_vero
import Submission.Work.HP.MM2.Sstar_GamMix_Tmix_le_S1ball
import Submission.Work.HP.MM2.finsum_mem_pair_prod_le

/-!
# Reindexing the degenerate part `Σ₂^{mix}` of `D^mix`

`Σ₂^{mix}` is the contribution of the pairs `p = (x,y) ∈ Ω_bad(⊆ Ω(B))` to the reindexed mixed
second moment (`DmixReindex`):

`Σ₂^{mix} = (α W / 4) · Σ_{p ∈ Ω_bad} 𝓢*₁(Γ^{mix}_{x,y}(W); 𝒯^{mix}_y(A,α)) / ‖ν(y)‖`,

with `α = log B`, `W = bigW (wOf B)`, `Ω_bad = {p ∈ Ω(B) : A^{3/4} < W λ(x)}` and
`λ(x) = lamX d n x`.

The bound proved here is the one needed by `Sigma2mix_bound`:

* for `p ∈ Ω_bad`, `𝓢*₁(Γ^{mix}_{x,y}(W); 𝒯^{mix}_y(A,α)) ≤ 𝓢₁(Λ_{ν(x)}; B(A)) = S1ball d n x A`:
  the index set `Γ^{mix} ∩ 𝒯^{mix}` is contained in `Λ_{ν(x)} ∩ {‖a‖ ≤ A}`, and `IsPrim a`
  forces `a ≠ 0`;
* `Ω_bad ⊆ {x bad} × Ξ(B)`, so the pair sum factors through the two marginal sums, and the
  `y`-sum is `≤ C·B` by `xi_sum_vero` (`FM4.xi_sum_vero`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Local plumbing for `finsum`s over finite sets -/

/-- Monotonicity of a finite `finsum` in its summand. -/
private lemma s2rx_finsum_mem_mono {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ s, f a ≤ g a) : (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ s, g a := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_le_sum fun a ha => h a (hs.mem_toFinset.mp ha)

/-- A finite `finsum` of nonnegative terms is nonnegative. -/
private lemma s2rx_finsum_mem_nonneg {α : Type*} {s : Set α} (hs : s.Finite) {f : α → ℝ}
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ ∑ᶠ a ∈ s, f a := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_nonneg fun a ha => h a (hs.mem_toFinset.mp ha)

/-- `S1ball` is a sum of nonnegative terms (the ball is finite, and `1/‖a‖ ≥ 0`). -/
private lemma s2rx_S1ball_nonneg (d n : ℕ) (x : Fin (n + 1) → ℤ) (A : ℝ) :
    0 ≤ S1ball d n x A := by
  rw [S1ball]
  exact s2rx_finsum_mem_nonneg
    ((MDBasic.finite_eNorm_le (ι := Mon d n) A).subset (fun a ha => ha.2.2))
    (fun a _ => div_nonneg zero_le_one (eNorm_nonneg a))

/-- Reindexing step of `Sigma2mix_bound`.  `Σ₂^{mix}` sums over the bad pairs `p ∈ Ω_bad ⊆ Ω(B)`, `Ω_bad = {p ∈ Ω : A^{3/4} < W·λ(p.1)}` with `W = bigW (wOf B)`. For such a pair `Γ^{mix}_{x,y}(W) ⊆ Λ_{ν(x)}` and `𝒯^{mix}_y(A,α) ⊆ {‖a‖ ≤ A}`, so `Sstar 1 (GamMix x y W) (TmixSet y A α) ≤ S1ball d n x A`; and `Ω_bad ⊆ {x bad} × Ξ(B)`, so summing `1/‖ν(y)‖` over `y ∈ Ξ(B)`, which is `≪ B` by `FM4.xi_sum_vero`, leaves `Σ₂^{mix} ≤ K(αW/4)B·Σ_{x bad} S1ball d n x A`. -/
theorem Sigma2mix_reindex (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → 1 ≤ A →
      Sigma2mix d n A B ≤ K * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
        ∑ᶠ x ∈ {x : Fin (n + 1) → ℤ | x ∈ Xi d n B ∧ IsPrim x ∧
            A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x},
          S1ball d n x A := by
  obtain ⟨C, Bc, hCpos, hBcpos, hC⟩ := FM4.xi_sum_vero d n hd hdn
  refine ⟨C, max Bc 1, hCpos, lt_of_lt_of_le one_pos (le_max_right Bc 1), ?_⟩
  intro A B hB _
  have hBc_le : Bc ≤ B := le_trans (le_max_left Bc 1) hB
  have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_right Bc 1) hB
  set Xb : Set (Fin (n + 1) → ℤ) := {x : Fin (n + 1) → ℤ | x ∈ Xi d n B ∧ IsPrim x ∧
      A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x} with hXbdef
  have hObad : (OmegaBad d n A B).Finite := (Omega_finite d n B).subset (fun p hp => hp.1)
  have hXbfin : Xb.Finite := (Xi_finite d n B).subset (fun x hx => hx.1)
  have hXifin : (Xi d n B).Finite := Xi_finite d n B
  have hsub : OmegaBad d n A B ⊆ Xb ×ˢ Xi d n B := by
    intro p hp
    rw [Set.mem_prod]
    refine ⟨?_, hp.1.2.1⟩
    rw [hXbdef]
    exact ⟨hp.1.1, hp.1.1.1, not_le.mp hp.2⟩
  have hS1nn : ∀ x ∈ Xb, 0 ≤ S1ball d n x A := fun x _ => s2rx_S1ball_nonneg d n x A
  have hgnn : ∀ y ∈ Xi d n B, 0 ≤ 1 / eNorm (veronese d n y) :=
    fun y _ => div_nonneg zero_le_one (eNorm_nonneg _)
  have hstep2 : (∑ᶠ p ∈ OmegaBad d n A B, S1ball d n p.1 A * (1 / eNorm (veronese d n p.2)))
      ≤ (∑ᶠ x ∈ Xb, S1ball d n x A) * (∑ᶠ y ∈ Xi d n B, 1 / eNorm (veronese d n y)) :=
    finsum_mem_pair_prod_le hXbfin hXifin hObad hsub hS1nn hgnn
  have hstep3 : (∑ᶠ y ∈ Xi d n B, 1 / eNorm (veronese d n y)) ≤ C * B := hC B hBc_le
  have hSumFnn : 0 ≤ ∑ᶠ x ∈ Xb, S1ball d n x A := s2rx_finsum_mem_nonneg hXbfin hS1nn
  have hstep4 : (∑ᶠ x ∈ Xb, S1ball d n x A) * (∑ᶠ y ∈ Xi d n B, 1 / eNorm (veronese d n y))
      ≤ (∑ᶠ x ∈ Xb, S1ball d n x A) * (C * B) :=
    mul_le_mul_of_nonneg_left hstep3 hSumFnn
  have hfac : 0 ≤ Real.log B * (bigW (wOf B) : ℝ) / 4 :=
    div_nonneg (mul_nonneg (Real.log_nonneg hB1) (Nat.cast_nonneg _)) (by norm_num)
  calc Sigma2mix d n A B
      ≤ (Real.log B * (bigW (wOf B) : ℝ) / 4) *
          (∑ᶠ p ∈ OmegaBad d n A B, S1ball d n p.1 A * (1 / eNorm (veronese d n p.2))) := by
        rw [Sigma2mix]
        exact mul_le_mul_of_nonneg_left
          (s2rx_finsum_mem_mono hObad (fun p _ => by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right
              (Sstar_GamMix_Tmix_le_S1ball d n p.1 p.2 (bigW (wOf B)) A (Real.log B))
              (div_nonneg zero_le_one (eNorm_nonneg _))))
          hfac
    _ ≤ (Real.log B * (bigW (wOf B) : ℝ) / 4) *
          ((∑ᶠ x ∈ Xb, S1ball d n x A) * (C * B)) :=
        mul_le_mul_of_nonneg_left (le_trans hstep2 hstep4) hfac
    _ = C * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B * (∑ᶠ x ∈ Xb, S1ball d n x A) := by
        ring

end Work.HP.MM2
