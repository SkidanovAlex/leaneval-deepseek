/-
# The window-tail estimate of Proposition `lip-2` (`Work.KMTAreas.A4.lip2WindowTail`)

The main-case expansion of Proposition `lip-2` (Krause--Mirek--Tao, §5.2) transforms the pairing
`⟨Ã*_N(h,g), F⟩` into the double sum
`∑_s ∑_y h y · F (y + s) · lip2Avg N P M γ g s y`
(see `Work.KMTAreas.A4.lip2WindowExpansion`).  Truncating the outer sum to `|s| ≤ S` costs the
*tail*

`∑_{|s| > S} ‖∑_y h y · F (y+s) · lip2Avg N P M γ g s y‖`,

and the point of the present lemma is that this tail gains a power of `Y⁻¹` whenever
`S ≥ N + M Y`: the window `win M γ` is the dilated Schwartz function `M⁻¹ ψ(·/M)`, and for
`|s| > S ≥ N + MY` and `n ∈ (N/2, N]` one has `|n - s| ≥ |s| - N > MY`, so *every* window value
occurring in `lip2Avg` is evaluated at a point of modulus `> Y`, giving `M⁻¹⟨·/M⟩^{-12} ≤ Y⁻¹¹`.

The estimate is uniform in `M`, `γ`, `P`, `S`, `F`, `g`, `h`; the constant is the Schwartz decay
constant `2^12 (schwartzSeminormSum lipSchPsi + 1)` of `Work.Analysis.InverseTheory.calc_approx`.

## Structure of the proof

* `winTailC` — the absolute constant;
* `winTailDecayT` — the window bound `‖win M γ m‖ ≤ winTailC · Y⁻¹¹` in the tail regime;
* `winShiftSummable` — the shifted product `y ↦ a y · b (y + s)` of two summable nonnegative
  sequences is summable;
* `finset_sum_tsum_conv_le` — the `ℓ¹`-convolution bound
  `∑_{s ∈ v} ∑'_y a y · b (y + s) ≤ (∑'_y a y)(∑'_x b x)` for a finite `v`;
* `norm_lip2Avg_le` — the uniform bound on the windowed average;
* `norm_tsum_mul_lip2Avg_le` — the per-shift triangle inequality;
* `lip2WindowTail` — the assembly (a finite-partial-sum argument followed by
  `Real.tsum_le_of_sum_le`, so no summability of the (possibly divergent) left-hand side is
  needed).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2MainDefs
import Submission.Work.KMTAreas.A4.lip2Kernel
import Submission.Work.KMTAreas.A4.summable_tsum_eps_jbDecay_weighted_shift

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The absolute constant of the window-tail estimate: the constant `2 ^ 12 (S + 1)` of the
Schwartz decay `Work.Analysis.InverseTheory.schwartz_decay` of `ψ = lipSchPsi`. -/
noncomputable def winTailC : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum lipSchPsi + 1)

theorem winTailC_pos : 0 < winTailC := by
  rw [winTailC]
  have h := schwartzSeminormSum_nonneg lipSchPsi
  positivity

/-! ## The window in the tail regime -/

/-- **The window decays as `Y⁻¹¹` past the scale `M · Y`.**  If `M ≥ 1`, `Y ≥ 1` and
`M * Y ≤ |m|` then `‖win M γ m‖ ≤ winTailC * Y⁻¹¹`: indeed
`‖win M γ m‖ = M⁻¹‖ψ(m/M)‖ ≤ M⁻¹ · winTailC · ⟨m/M⟩^{-12}` and `|m/M| ≥ Y ≥ 1`. -/
theorem winTailDecayT {M Y : ℝ} (hM : 1 ≤ M) (hY : 1 ≤ Y)
    (γ : FreqCircle) {m : ℤ} (hm : M * Y ≤ |(m : ℝ)|) :
    ‖win M γ m‖ ≤ winTailC * Y⁻¹ ^ 11 := by
  have hMpos : 0 < M := by linarith
  have hYpos : 0 < Y := by linarith
  rw [norm_win M hMpos γ m]
  set u : ℝ := (m : ℝ) / M with hu
  have hu_ge : Y ≤ |u| := by
    rw [hu, abs_div, abs_of_pos hMpos, le_div_iff₀ hMpos]
    linarith [hm, mul_comm M Y]
  have hu_pos : 0 < |u| := lt_of_lt_of_le hYpos hu_ge
  have hdec : ‖(lipSchPsi : ℝ → ℂ) u‖ ≤ winTailC * jbDecay 12 u := by
    rw [winTailC]
    exact schwartz_decay lipSchPsi u
  have h1 : jbDecay 12 u ≤ Y⁻¹ ^ 11 := by
    have hb : (jb u)⁻¹ ≤ (|u|)⁻¹ :=
      (inv_le_inv₀ (jb_pos u) hu_pos).mpr (abs_le_jb u)
    have hab : (|u|)⁻¹ ≤ Y⁻¹ := (inv_le_inv₀ hu_pos hYpos).mpr hu_ge
    have hu1 : (|u|)⁻¹ ≤ 1 := (inv_le_one₀ hu_pos).mpr (by linarith)
    calc jbDecay 12 u = ((jb u)⁻¹) ^ 12 := rfl
      _ ≤ ((|u|)⁻¹) ^ 12 := pow_le_pow_left₀ (inv_nonneg.mpr (jb_nonneg u)) hb 12
      _ ≤ ((|u|)⁻¹) ^ 11 := pow_le_pow_of_le_one (inv_nonneg.mpr hu_pos.le) hu1 (by norm_num)
      _ ≤ (Y⁻¹) ^ 11 := pow_le_pow_left₀ (inv_nonneg.mpr hu_pos.le) hab 11
  calc M⁻¹ * ‖(lipSchPsi : ℝ → ℂ) u‖
      ≤ M⁻¹ * (winTailC * jbDecay 12 u) :=
        mul_le_mul_of_nonneg_left hdec (inv_nonneg.mpr hMpos.le)
    _ ≤ M⁻¹ * (winTailC * Y⁻¹ ^ 11) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 winTailC_pos.le) (inv_nonneg.mpr hMpos.le)
    _ ≤ winTailC * Y⁻¹ ^ 11 := by
        have h1M : M⁻¹ ≤ 1 := (inv_le_one₀ hMpos).mpr hM
        have h2 : 0 ≤ winTailC * Y⁻¹ ^ 11 :=
          mul_nonneg winTailC_pos.le (pow_nonneg (inv_nonneg.mpr hYpos.le) 11)
        calc M⁻¹ * (winTailC * Y⁻¹ ^ 11) ≤ 1 * (winTailC * Y⁻¹ ^ 11) :=
              mul_le_mul_of_nonneg_right h1M h2
          _ = winTailC * Y⁻¹ ^ 11 := one_mul _

/-! ## Summability of the shifted product -/

/-- For two summable nonnegative sequences `a`, `b` on `ℤ` and any shift `s`, the family
`y ↦ a y * b (y + s)` is summable.  The proof dominates it by `(∑' b) * a y`, using that each
term of a summable nonnegative series is at most the total. -/
lemma winShiftSummable {a b : ℤ → ℝ} (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ y : ℤ, 0 ≤ a y) (hb0 : ∀ x : ℤ, 0 ≤ b x) (s : ℤ) :
    Summable (fun y : ℤ => a y * b (y + s)) :=
  Summable.of_nonneg_of_le (fun y => mul_nonneg (ha0 y) (hb0 _))
    (fun y => by
      calc a y * b (y + s) ≤ a y * (∑' x : ℤ, b x) :=
            mul_le_mul_of_nonneg_left (Summable.le_tsum hb (y + s) (fun j _ => hb0 j)) (ha0 y)
        _ = (∑' x : ℤ, b x) * a y := mul_comm _ _)
    (ha.mul_left (∑' x : ℤ, b x))

/-! ## The `ℓ¹`-convolution bound -/

/-- **`ℓ¹`-convolution bound.**  For summable nonnegative `a`, `b` on `ℤ` and a finite set
`v : Finset ℤ`,
`∑_{s ∈ v} ∑'_y a y · b (y + s) ≤ (∑'_y a y) * (∑'_x b x)`.

The left-hand side sums `a y * b x` over the pairs with `x - y ∈ v`, a subset of `ℤ × ℤ`; the
proof interchanges the finite `s`-sum with the `tsum` in `y` (`Summable.tsum_finsetSum`) and
bounds `∑_{s∈v} b (y+s) ≤ ∑'_x b x` through the injective shift `s ↦ y + s`. -/
theorem finset_sum_tsum_conv_le {a b : ℤ → ℝ} (ha : Summable a) (hb : Summable b)
    (ha0 : ∀ y : ℤ, 0 ≤ a y) (hb0 : ∀ x : ℤ, 0 ≤ b x) (v : Finset ℤ) :
    ∑ s ∈ v, (∑' y : ℤ, a y * b (y + s)) ≤ (∑' y : ℤ, a y) * (∑' x : ℤ, b x) := by
  have hsum_s : ∀ s : ℤ, Summable (fun y : ℤ => a y * b (y + s)) :=
    fun s => winShiftSummable ha hb ha0 hb0 s
  have hswap : ∑ s ∈ v, (∑' y : ℤ, a y * b (y + s))
      = ∑' y : ℤ, ∑ s ∈ v, a y * b (y + s) :=
    (Summable.tsum_finsetSum (f := fun s y => a y * b (y + s)) (s := v)
      (fun s _ => hsum_s s)).symm
  rw [hswap]
  have hleft : Summable (fun y : ℤ => ∑ s ∈ v, a y * b (y + s)) := by
    refine Summable.of_nonneg_of_le
      (fun y => Finset.sum_nonneg (fun s _ => mul_nonneg (ha0 y) (hb0 _))) (fun y => ?_)
      (ha.mul_left ((v.card : ℝ) * (∑' x : ℤ, b x)))
    calc ∑ s ∈ v, a y * b (y + s) ≤ ∑ s ∈ v, a y * (∑' x : ℤ, b x) :=
          Finset.sum_le_sum (fun s _ =>
            mul_le_mul_of_nonneg_left (Summable.le_tsum hb (y + s) (fun j _ => hb0 j)) (ha0 y))
      _ = (v.card : ℝ) * (a y * (∑' x : ℤ, b x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((v.card : ℝ) * (∑' x : ℤ, b x)) * a y := by ring
  have hinner : ∀ y : ℤ, (∑ s ∈ v, b (y + s)) ≤ ∑' x : ℤ, b x := by
    intro y
    calc ∑ s ∈ v, b (y + s) = ∑ z ∈ v.image (fun s : ℤ => y + s), b z :=
          (Finset.sum_image (f := b) (g := fun s : ℤ => y + s) (s := v)
            (fun x _ z _ hxz => add_left_cancel hxz)).symm
      _ ≤ ∑' x : ℤ, b x :=
          Summable.sum_le_tsum (v.image (fun s : ℤ => y + s)) (fun i _ => hb0 i) hb
  have hbound : ∀ y : ℤ, (∑ s ∈ v, a y * b (y + s)) ≤ a y * (∑' x : ℤ, b x) := by
    intro y
    rw [(Finset.mul_sum v (fun s : ℤ => b (y + s)) (a y)).symm]
    exact mul_le_mul_of_nonneg_left (hinner y) (ha0 y)
  calc ∑' y : ℤ, ∑ s ∈ v, a y * b (y + s)
      ≤ ∑' y : ℤ, a y * (∑' x : ℤ, b x) :=
        Summable.tsum_le_tsum hbound hleft (ha.mul_right _)
    _ = (∑' y : ℤ, a y) * (∑' x : ℤ, b x) := tsum_mul_right

/-! ## The uniform bound on the windowed average -/

/-- **The windowed average is bounded by the window-tail constant.**  For `S ≥ N + M Y` and
`|s| > S`, every shift `n - s` with `n ∈ (N/2, N]` exceeds `M Y` in modulus, so each of the at
most `N` summands of `lip2Avg` is bounded by `K`; multiplying by `N⁻¹` gives the claim. -/
theorem norm_lip2Avg_le {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M S Y : ℝ}
    (hM : 1 ≤ M) (hY : 1 ≤ Y) (hS : (N : ℝ) + M * Y ≤ S) (γ : FreqCircle) {g : ℤ → ℂ}
    (hg : ∀ y : ℤ, ‖g y‖ ≤ 1) {K : ℝ}
    (hK : ∀ {m : ℤ}, M * Y ≤ |(m : ℝ)| → ‖win M γ m‖ ≤ K) {s y : ℤ} (hs : S < |(s : ℝ)|) :
    ‖lip2Avg N P M γ g s y‖ ≤ K := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hK0 : 0 ≤ K := by
    have hw : ‖win M γ (((⌈M * Y⌉₊ : ℕ) : ℤ))‖ ≤ K :=
      hK (m := ((⌈M * Y⌉₊ : ℕ) : ℤ)) (by
        rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.le_ceil (M * Y))
    linarith [norm_nonneg (win M γ (((⌈M * Y⌉₊ : ℕ) : ℤ)))]
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    have h : (Finset.Ioc (N / 2) N).card ≤ N := by
      rw [Nat.card_Ioc]
      exact Nat.sub_le _ _
    exact_mod_cast h
  have hnorminv : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (inv_nonneg.mpr hNpos.le)]
  rw [lip2Avg, norm_mul]
  first
    | rw [hnorminv]
    | rw [show (((N : ℝ) : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) from
          (Complex.ofReal_inv (N : ℝ)).symm, hnorminv]
  have hterms : ∀ n ∈ Finset.Ioc (N / 2) N,
      ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖ ≤ K := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    obtain ⟨hn1, hn2⟩ := hn
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn2
    have hdiff : M * Y ≤ |(((n : ℤ) - s : ℤ) : ℝ)| := by
      have hcast : ((((n : ℤ) - s : ℤ)) : ℝ) = (n : ℝ) - (s : ℝ) := by push_cast; ring
      rw [hcast, abs_sub_comm]
      have h1 : M * Y ≤ |(s : ℝ)| - (N : ℝ) := by linarith
      have h3 : |(s : ℝ)| - (n : ℝ) ≤ |(s : ℝ) - (n : ℝ)| := by
        have h := abs_sub_abs_le_abs_sub (s : ℝ) (n : ℝ)
        rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))] at h
      linarith
    calc ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
        = ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ := norm_mul _ _
      _ ≤ K * 1 := mul_le_mul (hK hdiff) (hg _) (norm_nonneg _) hK0
      _ = K := mul_one K
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N, win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, K := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hNpos.le)
        calc ‖∑ n ∈ Finset.Ioc (N / 2) N, win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
            ≤ ∑ n ∈ Finset.Ioc (N / 2) N,
                ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖ :=
              norm_sum_le _ _
          _ ≤ ∑ n ∈ Finset.Ioc (N / 2) N, K := Finset.sum_le_sum hterms
    _ = (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * K := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ K := by
        have h1 : (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ 1 := by
          calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
                mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hNpos.le)
            _ = 1 := inv_mul_cancel₀ (ne_of_gt hNpos)
        calc (N : ℝ)⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) * K ≤ 1 * K :=
              mul_le_mul_of_nonneg_right h1 hK0
          _ = K := one_mul K

/-! ## The per-shift triangle inequality -/

/-- **The `y`-sum at a fixed shift `s`.**  If the windowed average is bounded by `K` at every `y`
and `‖F‖`, `‖h‖` are summable, then
`‖∑'_y h y F (y+s) (lip2Avg s y)‖ ≤ K ∑'_y ‖h y‖ ‖F (y+s)‖`. -/
theorem norm_tsum_mul_lip2Avg_le {N : ℕ} (P : Polynomial ℤ) {M : ℝ} (γ : FreqCircle)
    {g F h : ℤ → ℂ} (s : ℤ) {K : ℝ}
    (hc : ∀ y : ℤ, ‖lip2Avg N P M γ g s y‖ ≤ K)
    (hF : Summable (fun x : ℤ => ‖F x‖)) (hh : Summable (fun y : ℤ => ‖h y‖)) :
    ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
      ≤ K * ∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖ := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hc 0)
  have hmaj : Summable (fun y : ℤ => ‖h y‖ * ‖F (y + s)‖) :=
    winShiftSummable hh hF (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) s
  have hsumm : Summable (fun y : ℤ => ‖h y * F (y + s) * lip2Avg N P M γ g s y‖) := by
    refine Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => ?_) (hmaj.mul_right K)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hc y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
      ≤ ∑' y : ℤ, ‖h y * F (y + s) * lip2Avg N P M γ g s y‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' y : ℤ, (‖h y‖ * ‖F (y + s)‖) * K := by
        refine Summable.tsum_le_tsum (fun y => ?_) hsumm (hmaj.mul_right K)
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hc y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖) * K := tsum_mul_right
    _ = K * ∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖ := by ring

/-! ## The assembly -/

theorem lip2WindowTail :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M S Y : ℝ},
      1 ≤ M → 1 ≤ Y → (N : ℝ) + M * Y ≤ S →
      ∀ {γ : Work.Analysis.InverseTheory.FreqCircle} {F : ℤ → ℂ}, Summable (fun x : ℤ => ‖F x‖) →
      ∀ {g h : ℤ → ℂ}, Summable (fun y : ℤ => ‖h y‖) → (∀ y : ℤ, ‖h y‖ ≤ 1) →
      (∀ y : ℤ, ‖g y‖ ≤ 1) →
      (∑' s : ℤ, if S < |(s : ℝ)| then
        ‖∑' y : ℤ, h y * F (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y‖ else 0)
        ≤ C * Y⁻¹ ^ 11 * (∑' x : ℤ, ‖F x‖) * (∑' y : ℤ, ‖h y‖) := by
  refine ⟨winTailC, winTailC_pos, ?_⟩
  intro N hN P M S Y hM hY hS γ F hF g h hh hhbd hgbd
  have hYpos : 0 < Y := by linarith
  have hK0 : 0 ≤ winTailC * Y⁻¹ ^ 11 :=
    mul_nonneg winTailC_pos.le (pow_nonneg (inv_nonneg.mpr hYpos.le) 11)
  refine Real.tsum_le_of_sum_le
    (f := fun s : ℤ => if S < |(s : ℝ)| then
      ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖ else 0) (fun s => ?_) (fun u => ?_)
  · dsimp only
    split_ifs with hs
    · exact norm_nonneg _
    · exact le_refl 0
  · rw [← Finset.sum_filter]
    calc ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
            ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
        ≤ ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
            (winTailC * Y⁻¹ ^ 11) * (∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖) := by
          refine Finset.sum_le_sum (fun s hs => ?_)
          rw [Finset.mem_filter] at hs
          have hc : ∀ y : ℤ, ‖lip2Avg N P M γ g s y‖ ≤ winTailC * Y⁻¹ ^ 11 :=
            fun y => norm_lip2Avg_le hN P hM hY hS γ hgbd
              (fun {m} hm => winTailDecayT hM hY γ hm) hs.2
          exact norm_tsum_mul_lip2Avg_le P γ s hc hF hh
      _ = (winTailC * Y⁻¹ ^ 11)
            * ∑ s ∈ u.filter (fun s : ℤ => S < |(s : ℝ)|),
                (∑' y : ℤ, ‖h y‖ * ‖F (y + s)‖) := by
          rw [Finset.mul_sum]
      _ ≤ (winTailC * Y⁻¹ ^ 11)
            * ((∑' y : ℤ, ‖h y‖) * (∑' x : ℤ, ‖F x‖)) :=
          mul_le_mul_of_nonneg_left
            (finset_sum_tsum_conv_le hh hF (fun y => norm_nonneg _) (fun x => norm_nonneg _)
              (u.filter (fun s : ℤ => S < |(s : ℝ)|))) hK0
      _ = winTailC * Y⁻¹ ^ 11 * (∑' x : ℤ, ‖F x‖) * (∑' y : ℤ, ‖h y‖) := by ring

end Work.KMTAreas.A4
