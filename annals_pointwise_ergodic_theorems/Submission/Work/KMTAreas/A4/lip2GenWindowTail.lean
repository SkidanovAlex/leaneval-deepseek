/-
# The window-tail estimate of Proposition `lip-2` in the free-window form

`Work.KMTAreas.A4.lip2WindowTail` truncates the shift sum of the `lip-2` expansion
`⟨Ã*_N(h,g), F⟩ = ∑_s ∑_y h y F(y+s) lip2Avg N P M γ g s y` at `|s| ≤ S` and pays the tail
`C · Y⁻¹¹ · ‖F‖₁ · ‖h‖₁` when `S ≥ N + M·Y`.  That estimate uses the nonnegativity of
`∑_y ‖h y‖ ‖F(y+s)‖` in the form `∑_{s∈v}∑_y ‖h y‖‖F(y+s)‖ ≤ ‖h‖₁‖F‖₁`, i.e. it needs `h ∈ ℓ¹`.

In the free-window assembly of `lip2Gen` (`Work.KMTAreas.A4.lip2Gen`) the function `h` is only
*bounded* by `1` — its `ℓ¹`-mass is not available — so the truncated expansion has to be paid for
by `∑_x ‖F x‖` alone.  The present module supplies that estimate:

`∑_{|s| > S} ‖∑'_y h y F(y+s) lip2Avg N P M γ g s y‖ ≤ C · Y⁻¹¹ · ∑_x ‖F x‖`

whenever `M ≥ 1`, `Y ≥ 1` and `S ≥ N + M·Y`, uniformly in `P`, `γ`, `F`, `g`, `h`.

## Why the estimate survives without `h ∈ ℓ¹`

The window `win M γ` is the dilated Schwartz function `M⁻¹ψ(·/M)` modulated by `γ`.  For
`|s| > S ≥ N + M·Y` and every `n ∈ (N/2, N]` one has `|n - s| ≥ |s| - N > M·Y`, so *every* window
value occurring in `lip2Avg` is evaluated beyond the scale `M·Y`; this gives the per-shift bound

`‖∑'_y h y F(y+s) lip2Avg … s y‖ ≤ N⁻¹ (∑_{n ∈ (N/2,N]} ‖win M γ (n-s)‖) · ‖F‖₁`,

with the norm of `h` discarded through `‖h‖_∞ ≤ 1`.  Summing over `|s| > S` and exchanging the two
finite sums produces `N⁻¹ ∑_{n ∈ (N/2,N]} ∑_{|s|>S} ‖win M γ (n-s)‖`; the *inner* sum is now a
finite piece of the `ℓ¹`-tail of the window, and the tail estimate `fbWinTail` below bounds it by
`C'·Y⁻¹¹`, uniformly in `n`.  There are at most `N` values of `n`, so the `N⁻¹` prefactor cancels
exactly:

`∑_{|s|>S} ‖…‖ ≤ N⁻¹ · N · C·Y⁻¹¹ · ‖F‖₁ = C·Y⁻¹¹·‖F‖₁`.

Since Mathlib's `tsum` of a non-summable nonnegative family is `0`, the identity is proved in the
finite-partial-sum form (`Real.tsum_le_of_sum_le`): it suffices to bound every finite partial sum,
which is what the argument above does.

## The pieces

* `fbWinTail` — the quantitative window tail estimate.  Past the scale `U ≥ M·Y` the window is
  dominated by `Cψ · M¹¹ |m|^{-12}` (`fbWin_tail_point_le`), and the finite tails of `|m|^{-12}`
  are bounded by the discrete `p`-series tail `Work.KMTAreas.A4.intTailInvPowLe`;
* `genWinTailC`, `genWinTailC_pos`, `winTail_tsum_le` — the resulting constant and the unwrapped
  tail estimate;
* `summable_win_tail`, `finset_win_tail_le`, `finset_win_shift_tail_le` — the tail-dominated
  window is summable, and the finite-set (shifted) form of the tail bound;
* `Work.KMTAreas.A4.normTsumLip2AvgLe` (imported) — the per-shift bound;
* `lip2GenWindowTail` — the assembly.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.intTailInvPowLe
import Submission.Work.KMTAreas.A4.normTsumLip2AvgLe

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The window tail estimate -/

/-- The Schwartz decay constant of `ψ = lipSchPsi`, as in `Work.Analysis.InverseTheory.calc_approx`
and `Work.KMTAreas.A4.winTailC`. -/
noncomputable def fbCpsi : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)

theorem fbCpsi_pos : 0 < fbCpsi := by
  rw [fbCpsi]
  have := schwartzSeminormSum_nonneg lipSchPsi
  positivity

/-- The absolute value of an integer, cast to `ℝ` through `ℤ.natAbs`. -/
theorem fbAbsCast (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- Pointwise decay of the window: `‖win M γ m‖ ≤ Cψ M⁻¹ ⟨m/M⟩^{-12}`. -/
theorem fbWin_point_le (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) (m : ℤ) :
    ‖win M γ m‖ ≤ fbCpsi * M⁻¹ * jbDecay 12 ((m : ℝ) / M) := by
  have hMpos : 0 < M := by linarith
  rw [norm_win M hMpos γ m]
  have h := schwartz_decay lipSchPsi ((m : ℝ) / M)
  rw [fbCpsi]
  calc M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) ((m : ℝ) / M)‖
      ≤ M⁻¹ * ((2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)
          * jbDecay 12 ((m : ℝ) / M)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hMpos.le)
    _ = (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1) * M⁻¹
          * jbDecay 12 ((m : ℝ) / M) := by ring

/-- Pointwise tail decay: past the scale `U ≥ M`, the window is dominated by `Cψ M¹¹ |m|^{-12}`.
Indeed `M⁻¹⟨m/M⟩^{-12} ≤ M⁻¹(|m|/M)^{-12} = M¹¹|m|^{-12}`. -/
theorem fbWin_tail_point_le (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) {U : ℝ} {m : ℤ}
    (hm : U < |(m : ℝ)|) (hUM : M ≤ U) :
    ‖win M γ m‖ ≤ fbCpsi * M ^ 11 * (((|(m : ℝ)|))⁻¹) ^ 12 := by
  have hMpos : 0 < M := by linarith
  have hmabs : 0 < |(m : ℝ)| := lt_of_le_of_lt (le_trans hMpos.le hUM) hm
  have habs : |((m : ℝ) / M)| = |(m : ℝ)| / M := by rw [abs_div, abs_of_pos hMpos]
  have hdec : jbDecay 12 ((m : ℝ) / M) ≤ (((|(m : ℝ)| / M))⁻¹) ^ 12 := by
    rw [jbDecay]
    refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 12
    exact (inv_le_inv₀ (jb_pos _) (div_pos hmabs hMpos)).mpr
      (by simpa [habs] using abs_le_jb ((m : ℝ) / M))
  have h2 : (((|(m : ℝ)| / M))⁻¹) ^ 12 = M ^ 12 * (((|(m : ℝ)|))⁻¹) ^ 12 := by
    rw [inv_div, div_pow, inv_pow, div_eq_mul_inv]
  calc ‖win M γ m‖ ≤ fbCpsi * M⁻¹ * jbDecay 12 ((m : ℝ) / M) := fbWin_point_le M hM γ m
    _ ≤ fbCpsi * M⁻¹ * (((|(m : ℝ)| / M))⁻¹) ^ 12 :=
        mul_le_mul_of_nonneg_left hdec (mul_nonneg fbCpsi_pos.le (inv_nonneg.mpr hMpos.le))
    _ = fbCpsi * M⁻¹ * (M ^ 12 * (((|(m : ℝ)|))⁻¹) ^ 12) := by rw [h2]
    _ = fbCpsi * M ^ 11 * (((|(m : ℝ)|))⁻¹) ^ 12 := by
        have hMne : M ≠ 0 := ne_of_gt hMpos
        field_simp

/-- **The window tail estimate.**  For `M ≥ 1`, `Y ≥ 1` and `M·Y ≤ U` the `ℓ¹`-mass of the
window outside `[-U,U]` is at most `fbCpsi · 4 · Y⁻¹¹`: the `N`-free form of the estimate used by
`Work.KMTAreas.A4.lip2GenWindowTail`. -/
theorem fbWinTail :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (γ : FreqCircle) {U Y : ℝ}, 1 ≤ M → 1 ≤ Y → M * Y ≤ U →
      (∑' m : ℤ, (if U < |(m : ℝ)| then ‖win M γ m‖ else 0)) ≤ C * Y⁻¹ ^ 11 := by
  refine ⟨fbCpsi * 4, ?_, ?_⟩
  · exact mul_pos fbCpsi_pos (by norm_num)
  · intro M γ U Y hM hY hUY
    have hMpos : 0 < M := by linarith
    have hYpos : 0 < Y := by linarith
    have hUM : M ≤ U := by nlinarith [hM, hY]
    have hUpos : 0 < U := lt_of_lt_of_le (mul_pos hMpos hYpos) hUY
    set K : ℕ := Nat.ceil U with hKdef
    have hK1 : 1 ≤ K := by rw [hKdef]; exact Nat.ceil_pos.mpr hUpos
    have hUK : U ≤ (K : ℝ) := by rw [hKdef]; exact Nat.le_ceil U
    have hKMY : M * Y ≤ (K : ℝ) := le_trans hUY hUK
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
    have hnonneg : ∀ i : ℤ, 0 ≤ fbCpsi * M ^ 11 * (((|(i : ℝ)|))⁻¹) ^ 12 := fun i =>
      mul_nonneg (mul_nonneg fbCpsi_pos.le (pow_nonneg hMpos.le 11))
        (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) 12)
    refine Real.tsum_le_of_sum_le
      (f := fun m : ℤ => if U < |(m : ℝ)| then ‖win M γ m‖ else 0)
      (fun m => by by_cases h : U < |(m : ℝ)| <;> simp [h]) (fun v => ?_)
    rw [← Finset.sum_filter]
    have hsub : v.filter (fun m : ℤ => U < |(m : ℝ)|)
        ⊆ v.filter (fun m : ℤ => (K : ℝ) ≤ |(m : ℝ)|) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, ?_⟩
      have hmabs : U ≤ ((m.natAbs : ℕ) : ℝ) := by
        rw [fbAbsCast]; exact le_of_lt hm.2
      have h1 : K ≤ m.natAbs := by rw [hKdef]; exact Nat.ceil_le.mpr hmabs
      calc (K : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast h1
        _ = |(m : ℝ)| := fbAbsCast m
    have hinv : ((K : ℝ)⁻¹) ^ 11 ≤ ((M * Y)⁻¹) ^ 11 :=
      pow_le_pow_left₀ (by positivity)
        ((inv_le_inv₀ hKpos (mul_pos hMpos hYpos)).mpr hKMY) 11
    calc ∑ m ∈ v.filter (fun m : ℤ => U < |(m : ℝ)|), ‖win M γ m‖
        ≤ ∑ m ∈ v.filter (fun m : ℤ => U < |(m : ℝ)|),
            fbCpsi * M ^ 11 * (((|(m : ℝ)|))⁻¹) ^ 12 :=
          Finset.sum_le_sum (fun m hm =>
            fbWin_tail_point_le M hM γ (Finset.mem_filter.mp hm).2 hUM)
      _ ≤ ∑ m ∈ v.filter (fun m : ℤ => (K : ℝ) ≤ |(m : ℝ)|),
            fbCpsi * M ^ 11 * (((|(m : ℝ)|))⁻¹) ^ 12 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
      _ = fbCpsi * M ^ 11 * ∑ m ∈ v.filter (fun m : ℤ => (K : ℝ) ≤ |(m : ℝ)|),
            (((|(m : ℝ)|))⁻¹) ^ 12 := by rw [Finset.mul_sum]
      _ ≤ fbCpsi * M ^ 11 * (4 * ((K : ℝ)⁻¹) ^ 11) :=
          mul_le_mul_of_nonneg_left (intTailInvPowLe K hK1 v)
            (mul_nonneg fbCpsi_pos.le (pow_nonneg hMpos.le 11))
      _ ≤ fbCpsi * M ^ 11 * (4 * ((M * Y)⁻¹) ^ 11) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by norm_num))
            (mul_nonneg fbCpsi_pos.le (pow_nonneg hMpos.le 11))
      _ = fbCpsi * 4 * Y⁻¹ ^ 11 := by
          have hMne : M ≠ 0 := ne_of_gt hMpos
          rw [mul_inv]
          field_simp

/-! ## The constant and its unwrapped form -/

/-- The absolute constant of the window-tail estimate. -/
noncomputable def genWinTailC : ℝ := Classical.choose fbWinTail

theorem genWinTailC_pos : 0 < genWinTailC := (Classical.choose_spec fbWinTail).1

/-- **The window tail estimate, unwrapped.**  For `M ≥ 1`, `Y ≥ 1` and `M·Y ≤ U`, the `ℓ¹`-mass
of the window outside `[-U,U]` is at most `genWinTailC · Y⁻¹¹`. -/
theorem winTail_tsum_le {M : ℝ} {γ : FreqCircle} {U Y : ℝ} (hM : 1 ≤ M) (hY : 1 ≤ Y)
    (hUY : M * Y ≤ U) :
    (∑' m : ℤ, (if U < |(m : ℝ)| then ‖win M γ m‖ else 0)) ≤ genWinTailC * Y⁻¹ ^ 11 :=
  (Classical.choose_spec fbWinTail).2 M γ hM hY hUY

/-- The tail-dominated window is summable (it is dominated by the summable window). -/
theorem summable_win_tail (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) (U : ℝ) :
    Summable (fun m : ℤ => (if U < |(m : ℝ)| then ‖win M γ m‖ else 0)) :=
  Summable.of_nonneg_of_le (fun m => by by_cases h : U < |(m : ℝ)| <;> simp [h])
    (fun m => by by_cases h : U < |(m : ℝ)| <;> simp [h, norm_nonneg])
    (win_summable M hM γ)

/-- **Finite-set form of the window tail estimate.** -/
theorem finset_win_tail_le {M : ℝ} (hM : 1 ≤ M) (γ : FreqCircle) {U Y : ℝ} (hY : 1 ≤ Y)
    (hUY : M * Y ≤ U) (v : Finset ℤ) :
    (∑ m ∈ v.filter (fun m : ℤ => U < |(m : ℝ)|), ‖win M γ m‖) ≤ genWinTailC * Y⁻¹ ^ 11 := by
  have h := Summable.sum_le_tsum (v.filter (fun m : ℤ => U < |(m : ℝ)|))
    (fun i _ => by by_cases h : U < |(i : ℝ)| <;> simp [h])
    (summable_win_tail M hM γ U)
  calc ∑ m ∈ v.filter (fun m : ℤ => U < |(m : ℝ)|), ‖win M γ m‖
      = ∑ m ∈ v.filter (fun m : ℤ => U < |(m : ℝ)|),
          (if U < |(m : ℝ)| then ‖win M γ m‖ else 0) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [if_pos (Finset.mem_filter.mp hm).2]
    _ ≤ ∑' m : ℤ, (if U < |(m : ℝ)| then ‖win M γ m‖ else 0) := h
    _ ≤ genWinTailC * Y⁻¹ ^ 11 := winTail_tsum_le hM hY hUY

/-- **Shifted finite-set form of the window tail estimate.**  If `|n| ≤ N` and `S ≥ N + M·Y` then
the shifted window sum `∑_{s ∈ v, |s| > S} ‖win M γ (n - s)‖` is at most `genWinTailC · Y⁻¹¹`:
for each such `s` one has `|n - s| ≥ |s| - |n| > S - N ≥ M·Y`, so the summands are a finite piece
of the window `ℓ¹`-tail. -/
theorem finset_win_shift_tail_le {N : ℕ} {M S Y : ℝ} (hM : 1 ≤ M) (hY : 1 ≤ Y)
    (hS : (N : ℝ) + M * Y ≤ S) (γ : FreqCircle) {n : ℤ} (hn : |(n : ℝ)| ≤ (N : ℝ))
    (v : Finset ℤ) :
    (∑ s ∈ v.filter (fun s : ℤ => S < |(s : ℝ)|), ‖win M γ (n - s)‖) ≤ genWinTailC * Y⁻¹ ^ 11 := by
  have hUY : M * Y ≤ S - (N : ℝ) := by linarith
  set w : Finset ℤ := v.filter (fun s : ℤ => S < |(s : ℝ)|) with hw
  have hshift : ∀ s ∈ w, S - (N : ℝ) < |((n - s : ℤ) : ℝ)| := by
    intro s hs
    rw [hw, Finset.mem_filter] at hs
    have hsS := hs.2
    have hcast : (((n - s : ℤ)) : ℝ) = (n : ℝ) - (s : ℝ) := by push_cast; ring
    rw [hcast, abs_sub_comm (n : ℝ) (s : ℝ)]
    have h1 : |(s : ℝ)| - |(n : ℝ)| ≤ |(s : ℝ) - (n : ℝ)| :=
      abs_sub_abs_le_abs_sub (s : ℝ) (n : ℝ)
    linarith [hn, hsS, h1]
  have hFsumm : Summable
      (fun m : ℤ => (if S - (N : ℝ) < |(m : ℝ)| then ‖win M γ m‖ else 0)) :=
    summable_win_tail M hM γ (S - (N : ℝ))
  have hinj : Set.InjOn (fun s : ℤ => n - s) ↑w := fun x _ y _ hxy => sub_right_injective hxy
  have hsym : (∑ s ∈ w,
        (if S - (N : ℝ) < |((n - s : ℤ) : ℝ)| then ‖win M γ (n - s)‖ else 0))
      = ∑ m ∈ w.image (fun s : ℤ => n - s),
          (if S - (N : ℝ) < |(m : ℝ)| then ‖win M γ m‖ else 0) :=
    (Finset.sum_image (f := fun m : ℤ =>
        (if S - (N : ℝ) < |(m : ℝ)| then ‖win M γ m‖ else 0))
      (g := fun s : ℤ => n - s) hinj).symm
  calc ∑ s ∈ w, ‖win M γ (n - s)‖
      = ∑ s ∈ w, (if S - (N : ℝ) < |((n - s : ℤ) : ℝ)| then ‖win M γ (n - s)‖ else 0) := by
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [if_pos (hshift s hs)]
    _ = ∑ m ∈ w.image (fun s : ℤ => n - s),
          (if S - (N : ℝ) < |(m : ℝ)| then ‖win M γ m‖ else 0) := hsym
    _ ≤ ∑' m : ℤ, (if S - (N : ℝ) < |(m : ℝ)| then ‖win M γ m‖ else 0) :=
        Summable.sum_le_tsum _ (fun i _ => by
          by_cases h : S - (N : ℝ) < |(i : ℝ)| <;> simp [h]) hFsumm
    _ ≤ genWinTailC * Y⁻¹ ^ 11 := winTail_tsum_le hM hY hUY

/-! ## The assembly -/

theorem lip2GenWindowTail : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (P : Polynomial ℤ) {M S Y : ℝ}, 1 ≤ M → 1 ≤ Y → (N : ℝ) + M * Y ≤ S → ∀ {γ : Work.Analysis.InverseTheory.FreqCircle} {F : ℤ → ℂ}, Summable (fun x : ℤ => ‖F x‖) → ∀ {g h : ℤ → ℂ}, (∀ y : ℤ, ‖h y‖ ≤ 1) → (∀ y : ℤ, ‖g y‖ ≤ 1) → (∑' s : ℤ, (if S < |(s : ℝ)| then ‖∑' y : ℤ, h y * F (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y‖ else 0)) ≤ C * Y⁻¹ ^ 11 * (∑' x : ℤ, ‖F x‖) := by
  refine ⟨genWinTailC, genWinTailC_pos, ?_⟩
  intro N P M S Y hM hY hS γ F hF g h hhb hgb
  have hYpos : 0 < Y := by linarith
  have hK0 : 0 ≤ genWinTailC * Y⁻¹ ^ 11 :=
    mul_nonneg genWinTailC_pos.le (pow_nonneg (inv_nonneg.mpr hYpos.le) 11)
  have hF0 : 0 ≤ ∑' x : ℤ, ‖F x‖ := tsum_nonneg (fun _ => norm_nonneg _)
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le N (N / 2)
  have hfac : (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · subst hN0
      simp
    · have hN0' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)
          ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hN0'.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hN0')
  refine Real.tsum_le_of_sum_le
    (f := fun s : ℤ => if S < |(s : ℝ)| then
      ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖ else 0)
    (fun s => ?_) (fun u => ?_)
  · dsimp only
    split_ifs with hs
    · exact norm_nonneg _
    · exact le_refl 0
  · rw [← Finset.sum_filter]
    have htw : ∀ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
        ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
          ≤ ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖)
              * (∑' x : ℤ, ‖F x‖) := fun s _ => normTsumLip2AvgLe P γ s hgb hF hhb
    have hinner : (∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
          ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖))
        ≤ genWinTailC * Y⁻¹ ^ 11 := by
      calc ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
              ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖)
          = (N : ℝ)⁻¹ * ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
              ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖ := by
            rw [Finset.mul_sum]
        _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
              ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|), ‖win M γ ((n : ℤ) - s)‖ := by
            rw [Finset.sum_comm]
        _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.Ioc (N / 2) N, genWinTailC * Y⁻¹ ^ 11 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => ?_))
              (inv_nonneg.mpr (Nat.cast_nonneg N))
            refine finset_win_shift_tail_le hM hY hS γ ?_ _
            rw [Finset.mem_Ioc] at hn
            rw [abs_of_nonneg (Nat.cast_nonneg n)]
            exact_mod_cast hn.2
        _ = ((N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ)) * (genWinTailC * Y⁻¹ ^ 11) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ 1 * (genWinTailC * Y⁻¹ ^ 11) := mul_le_mul_of_nonneg_right hfac hK0
        _ = genWinTailC * Y⁻¹ ^ 11 := one_mul _
    calc ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
            ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
        ≤ ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
            ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖)
              * (∑' x : ℤ, ‖F x‖) := Finset.sum_le_sum htw
      _ = (∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
            ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖))
            * (∑' x : ℤ, ‖F x‖) := by
          rw [Finset.sum_mul]
      _ ≤ (genWinTailC * Y⁻¹ ^ 11) * (∑' x : ℤ, ‖F x‖) :=
          mul_le_mul_of_nonneg_right hinner hF0
      _ = genWinTailC * Y⁻¹ ^ 11 * (∑' x : ℤ, ‖F x‖) := by ring

end Work.KMTAreas.A4
