import Mathlib
import Submission.Work.GM.Energy.RMoments.SqDefs
import Submission.Work.GM.Energy.RMoments.SqBumpFacts

/-!
# The double sum `Σ_{t,s∈W} ‖Ψ(t-s)‖ ≪ |W|`

This file proves that if `W ⊆ ℝ` is `1`-separated and `Ψ = sqPsi` decays like
`‖Ψ(δ)‖ ≤ C₀` everywhere and like `‖Ψ(δ)‖ ≤ C₂/|δ|²` away from `0`, then

`Σ_{t∈W} Σ_{s∈W} ‖Ψ(t-s)‖ ≤ (C₀ + 16 C₂) |W|`.

The diagonal `s = t` contributes `C₀ |W|`.  For the off-diagonal, the bound
`1/|t-s|²` is summed against the `1`-separated set `W`:  splitting `W \ {t}` into
the points above and below `t` and using that the points of a `1`-separated set
`⊆ [t+1, ∞)` are (after flooring the distance to `t`) *distinct* positive
integers, the sum is at most `2 Σ_{k ≥ 1} 1/k² ≤ 4` (the constant `16` leaves
plenty of room).
-/

namespace Work.GM.Energy.RMoments

open Finset

set_option autoImplicit false

/-- `Σ_{m=1}^{M} 1/m² ≤ 2`.  Telescoping: `1/k² ≤ 1/(k-1) - 1/k` for `k ≥ 2`. -/
lemma sum_Icc_inv_sq_le_two (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · -- stronger form `≤ 2 - 1/M`, proved by induction on `M ≥ 1`
    have h : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) := by
      refine Nat.le_induction (m := 1) ?base ?step M hM
      · rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
      · intro k hk ih
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have key : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤ 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
          have hden : (1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)
              = 1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
            rw [div_sub_div _ _ (ne_of_gt hkpos) (ne_of_gt hk1pos)]
            ring_nf
          rw [hden]
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith
    linarith [show (0 : ℝ) ≤ 1 / (M : ℝ) by positivity]

/-- For a `1`-separated set `A ⊆ [t+1, ∞)`, `Σ_{s∈A} 1/(s-t)² ≤ 2`.
The map `s ↦ ⌊s-t⌋₊` is injective on `A`, and `0 < ⌊s-t⌋₊ ≤ s-t`, so the sum is
dominated by `Σ_{k ≥ 1} 1/k² ≤ 2`. -/
lemma sum_inv_sq_le_of_ge {A : Finset ℝ} {t : ℝ}
    (hge : ∀ s ∈ A, t + 1 ≤ s)
    (hsep : ∀ s ∈ A, ∀ s' ∈ A, s ≠ s' → 1 ≤ |s - s'|) :
    ∑ s ∈ A, (1 : ℝ) / (s - t) ^ 2 ≤ 2 := by
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA; simp
  · have hinj : Set.InjOn (fun s => Nat.floor (s - t)) (↑A : Set ℝ) := by
      intro s hs s' hs' heq
      simp only at heq
      by_contra hne
      have hs0 : 0 ≤ s - t := by have := hge s hs; linarith
      have hs0' : 0 ≤ s' - t := by have := hge s' hs'; linarith
      have h1 : ((Nat.floor (s - t) : ℕ) : ℝ) ≤ s - t := Nat.floor_le hs0
      have h2 : s - t < ((Nat.floor (s - t) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h3 : ((Nat.floor (s' - t) : ℕ) : ℝ) ≤ s' - t := Nat.floor_le hs0'
      have h4 : s' - t < ((Nat.floor (s' - t) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [← heq] at h3 h4
      have hlt : |s - s'| < 1 := by
        rw [abs_sub_lt_iff]; constructor <;> linarith
      have := hsep s hs s' hs' hne
      linarith
    have hterm : ∀ s ∈ A, (1 : ℝ) / (s - t) ^ 2
        ≤ (1 : ℝ) / ((Nat.floor (s - t) : ℕ) : ℝ) ^ 2 := by
      intro s hs
      have hk1 : 1 ≤ Nat.floor (s - t) := (Nat.one_le_floor_iff (s - t)).mpr (by have := hge s hs; linarith)
      have hkpos : (0 : ℝ) < ((Nat.floor (s - t) : ℕ) : ℝ) := by exact_mod_cast hk1
      have hle : ((Nat.floor (s - t) : ℕ) : ℝ) ≤ s - t := Nat.floor_le (by have := hge s hs; linarith)
      have hsq : (((Nat.floor (s - t) : ℕ) : ℝ)) ^ 2 ≤ (s - t) ^ 2 := by
        have := mul_self_le_mul_self (le_of_lt hkpos) hle
        simpa [pow_two] using this
      exact one_div_le_one_div_of_le (by positivity) hsq
    have hSne : (A.image (fun s => Nat.floor (s - t))).Nonempty := hA.image _
    set S := A.image (fun s => Nat.floor (s - t)) with hS
    have hsub : S ⊆ Finset.Icc 1 (S.max' hSne) := by
      intro m hm
      rw [Finset.mem_Icc]
      refine ⟨?_, Finset.le_max' S m hm⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
      exact (Nat.one_le_floor_iff (s - t)).mpr (by have := hge s hs; linarith)
    calc ∑ s ∈ A, (1 : ℝ) / (s - t) ^ 2
        ≤ ∑ s ∈ A, (1 : ℝ) / ((Nat.floor (s - t) : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hterm
      _ = ∑ m ∈ S, (1 : ℝ) / (m : ℝ) ^ 2 := by
            rw [hS, Finset.sum_image hinj]
      _ ≤ ∑ m ∈ Finset.Icc 1 (S.max' hSne), (1 : ℝ) / (m : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
      _ ≤ 2 := sum_Icc_inv_sq_le_two _

/-- Mirror of `sum_inv_sq_le_of_ge`: for a `1`-separated set `A ⊆ (-∞, t-1]`,
`Σ_{s∈A} 1/(t-s)² ≤ 2`.  Obtained from the previous lemma by reflecting `A`. -/
lemma sum_inv_sq_le_of_le {A : Finset ℝ} {t : ℝ}
    (hle : ∀ s ∈ A, s + 1 ≤ t)
    (hsep : ∀ s ∈ A, ∀ s' ∈ A, s ≠ s' → 1 ≤ |s - s'|) :
    ∑ s ∈ A, (1 : ℝ) / (t - s) ^ 2 ≤ 2 := by
  have hge : ∀ u ∈ A.image (fun s => -s), (-t) + 1 ≤ u := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    have := hle s hs
    linarith
  have hsep' : ∀ u ∈ A.image (fun s => -s), ∀ v ∈ A.image (fun s => -s),
      u ≠ v → 1 ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hsr : s ≠ r := by intro h; exact huv (by rw [h])
    have h := hsep s hs r hr hsr
    have h1 : -s - -r = -(s - r) := by ring
    rw [h1, abs_neg]
    exact h
  have heq : ∑ s ∈ A, (1 : ℝ) / (t - s) ^ 2
      = ∑ u ∈ A.image (fun s => -s), (1 : ℝ) / (u - (-t)) ^ 2 := by
    rw [Finset.sum_image (f := fun u => (1 : ℝ) / (u - (-t)) ^ 2) (g := fun s => -s)
        (fun a _ b _ h => by simpa using h)]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring_nf
  rw [heq]
  exact sum_inv_sq_le_of_ge hge hsep'

/-- For `t ∈ W` with `W` `1`-separated, `Σ_{s∈W, s≠t} 1/|t-s|² ≤ 4`. -/
lemma sum_erase_inv_sq_le (W : Finset ℝ) (hsep : Submission.GM.Separated W 1) {t : ℝ}
    (ht : t ∈ W) :
    ∑ s ∈ W.erase t, (1 : ℝ) / |t - s| ^ 2 ≤ 4 := by
  have hsep' : ∀ s ∈ W.erase t, ∀ s' ∈ W.erase t, s ≠ s' → 1 ≤ |s - s'| := by
    intro s hs s' hs' hne
    exact hsep s (Finset.mem_of_mem_erase hs) s' (Finset.mem_of_mem_erase hs') hne
  have hmem : ∀ s ∈ W.erase t, s ≠ t := fun s hs => (Finset.mem_erase.mp hs).1
  have hA : ∑ s ∈ (W.erase t).filter (fun s => t < s), (1 : ℝ) / |t - s| ^ 2 ≤ 2 := by
    have hge : ∀ s ∈ (W.erase t).filter (fun s => t < s), t + 1 ≤ s := by
      intro s hs
      have hts : t < s := (Finset.mem_filter.mp hs).2
      have hww := Finset.mem_of_mem_filter s hs
      have hne : s ≠ t := hmem s hww
      have h := hsep t ht s (Finset.mem_of_mem_erase hww) hne.symm
      rw [abs_of_neg (by linarith : t - s < 0)] at h
      linarith
    have hsepA : ∀ s ∈ (W.erase t).filter (fun s => t < s),
        ∀ s' ∈ (W.erase t).filter (fun s => t < s), s ≠ s' → 1 ≤ |s - s'| :=
      fun s hs s' hs' hne =>
        hsep' s (Finset.mem_of_mem_filter s hs) s' (Finset.mem_of_mem_filter s' hs') hne
    refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sq_le_of_ge hge hsepA)
    intro s hs
    have hts : t < s := (Finset.mem_filter.mp hs).2
    have : |t - s| = s - t := by rw [abs_of_neg (by linarith : t - s < 0)]; ring
    rw [this]
  have hB : ∑ s ∈ (W.erase t).filter (fun s => ¬ t < s), (1 : ℝ) / |t - s| ^ 2 ≤ 2 := by
    have hle : ∀ s ∈ (W.erase t).filter (fun s => ¬ t < s), s + 1 ≤ t := by
      intro s hs
      have hts : ¬ t < s := (Finset.mem_filter.mp hs).2
      have hww := Finset.mem_of_mem_filter s hs
      have hne : s ≠ t := hmem s hww
      have hst : s < t := lt_of_le_of_ne (not_lt.mp hts) hne
      have h := hsep t ht s (Finset.mem_of_mem_erase hww) hne.symm
      rw [abs_of_pos (by linarith : 0 < t - s)] at h
      linarith
    have hsepB : ∀ s ∈ (W.erase t).filter (fun s => ¬ t < s),
        ∀ s' ∈ (W.erase t).filter (fun s => ¬ t < s), s ≠ s' → 1 ≤ |s - s'| :=
      fun s hs s' hs' hne =>
        hsep' s (Finset.mem_of_mem_filter s hs) s' (Finset.mem_of_mem_filter s' hs') hne
    refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sq_le_of_le hle hsepB)
    intro s hs
    have hts : ¬ t < s := (Finset.mem_filter.mp hs).2
    have hww := Finset.mem_of_mem_filter s hs
    have hne : s ≠ t := hmem s hww
    have hst : s < t := lt_of_le_of_ne (not_lt.mp hts) hne
    have : |t - s| = t - s := abs_of_pos (by linarith : 0 < t - s)
    rw [this]
  have hsplit := Finset.sum_filter_add_sum_filter_not (W.erase t) (fun s => t < s)
    (fun s => (1 : ℝ) / |t - s| ^ 2)
  rw [← hsplit]
  linarith

set_option linter.unusedVariables false in
theorem sum_norm_sqPsi_le (W : Finset ℝ) (hsep : Submission.GM.Separated W 1)
    {C0 C2 : ℝ} (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2)
    (h0 : ∀ δ : ℝ, ‖sqPsi δ‖ ≤ C0) (h2 : ∀ δ : ℝ, δ ≠ 0 → ‖sqPsi δ‖ ≤ C2 / |δ| ^ 2) :
    ∑ t ∈ W, ∑ s ∈ W, ‖sqPsi (t - s)‖ ≤ (C0 + 16 * C2) * (W.card : ℝ) := by
  have hkey : ∀ t ∈ W, ∑ s ∈ W, ‖sqPsi (t - s)‖ ≤ C0 + 4 * C2 := by
    intro t ht
    have hdiag : ‖sqPsi (t - t)‖ ≤ C0 := by simpa using h0 0
    have hoff : ∑ s ∈ W.erase t, ‖sqPsi (t - s)‖ ≤ 4 * C2 := by
      calc ∑ s ∈ W.erase t, ‖sqPsi (t - s)‖
          ≤ ∑ s ∈ W.erase t, C2 / |t - s| ^ 2 := by
            refine Finset.sum_le_sum fun s hs => ?_
            have hst : s ≠ t := (Finset.mem_erase.mp hs).1
            have hne : t - s ≠ 0 := sub_ne_zero.mpr (fun h => hst h.symm)
            exact h2 (t - s) hne
        _ = C2 * ∑ s ∈ W.erase t, (1 : ℝ) / |t - s| ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ ≤ C2 * 4 := mul_le_mul_of_nonneg_left (sum_erase_inv_sq_le W hsep ht) hC2
        _ = 4 * C2 := by ring
    have hsum := Finset.sum_erase_add W (fun s => ‖sqPsi (t - s)‖) ht
    rw [← hsum]
    linarith
  calc ∑ t ∈ W, ∑ s ∈ W, ‖sqPsi (t - s)‖
      ≤ ∑ t ∈ W, (C0 + 4 * C2) := Finset.sum_le_sum hkey
    _ = (C0 + 4 * C2) * (W.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (C0 + 16 * C2) * (W.card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        linarith

end Work.GM.Energy.RMoments
