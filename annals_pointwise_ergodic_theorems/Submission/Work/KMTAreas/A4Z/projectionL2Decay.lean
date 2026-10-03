/-
# Area A4Z: the `ℓ²` decay of the windowed projection

Krause--Mirek--Tao, §5.2.  The projection step of the alternate inverse theorem `lip-2` replaces a
`1`-bounded, absolutely summable function `g` supported in `[-N₀,N₀]` by its windowed projection
`F = win M s * g`, where `win M s m = M⁻¹ ψ(m/M) e(m s)` is the normalised reproducing window.
This module proves the *spatial* `ℓ²` decay of that projection:

`∑_{R N^d < |x|} ‖F x‖² ≤ C² R⁻¹ N^d`,   `d = P.natDegree`,

uniformly in `M ≥ 2`, `s`, `R ≥ 1` and in the input `g`, with a constant `C` depending only on the
parameter `A` of `N₀ ≤ A N^d` and on `P`.  This is the *unscaled* form of clause (9) of
`Work.KMTAreas.A4Z.LipOutputGenTwoTail` (`K₂ = 1`).

## The proof

Write `w = win M s`, `F = w * g`, `G = 2N₀+1` (the number of shifts `m` with `|x - m| ≤ N₀`) and
`L = R N^d`, `Λ = L - N₀`, `ν = max 0 (Λ/M)`.  The only properties of `g` used are `‖g‖_∞ ≤ 1`,
`∑ ‖g‖ < ∞` and `SupportIn g N₀`.

(i) `‖F x‖ ≤ A x := ∑_{|x-m|≤N₀} ‖w m‖`, since `g` vanishes off `[-N₀,N₀]`;
(ii) `A x ≤ min (G C_ψ/M) C_win` (there are `G` terms of size `≤ C_ψ/M`, and the total mass of the
     window is `≤ C_win`);
(iii) `∑_{|x|>L} A x ≤ G·(window tail mass beyond Λ) ≤ K G ⟨ν⟩^{-11}` (lattice counting +
     Riemann comparison for the tail of `⟨·⟩^{-12}`);
(iv) hence `∑_{|x|>L} ‖F x‖² ≤ K G min(G/M,1) ⟨ν⟩^{-11}`, and the arithmetic lemma `decay_arith`
     gives `L·min(G/M,1)·⟨ν⟩^{-11} ≤ N₀ + G ≤ 2G`, so that the tail is `≤ 2KG²/L ≤ 18KA²N^d/R`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Kernel
import Submission.Work.KMTAreas.A4.winBase

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped BigOperators

namespace Work.KMTAreas.A4Z

open Work.Analysis.InverseTheory

/-- The absolute constant of the pointwise decay of the window: `‖ψ(t)‖ ≤ C_ψ ⟨t⟩^{-12}`. -/
noncomputable def winC : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum Work.KMTAreas.A4.lipSchPsi + 1)

/-! ## Lattice sums of `⟨·⟩^{-12}` -/

/-- `∑_j ⟨t + j/M⟩^{-(n+1)} ≤ 2^60 M ⟨t⟩^{-n}` for `M ≥ 1`, `t ≥ 0`: the `ℕ`-half-lattice
Riemann comparison `riemann_shift`, cleared of the `1/M` factor. -/
theorem half_lattice_tail_le (n : ℕ) (hn : 1 ≤ n) {M : ℝ} (hM : 1 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    (∑' j : ℕ, jbDecay (n+1) (t + (j:ℝ)/M)) ≤ (2:ℝ)^60 * M * jbDecay n t := by
  have hM0 : 0 < M := by linarith
  have hlam0 : (0:ℝ) < 1/M := by positivity
  have hlam1 : (1:ℝ)/M ≤ 1 := by rw [div_le_one hM0]; exact hM
  have hr := riemann_shift n hn (ε := 1/M) (t := t) hlam0 hlam1 ht
  have hcongr : (∑' j : ℕ, (1/M) * jbDecay (n+1) (t + (j:ℝ)/M))
      = ∑' j : ℕ, (1/M) * jbDecay (n+1) (t + (1/M) * (j:ℝ)) := by
    refine tsum_congr (fun j => ?_)
    congr 2
    ring
  have hr' : (∑' j : ℕ, (1/M) * jbDecay (n+1) (t + (j:ℝ)/M)) ≤ (2:ℝ)^60 * jbDecay n t := by
    rw [hcongr]; exact hr
  have h2 : (∑' j : ℕ, jbDecay (n+1) (t + (j:ℝ)/M))
      = ∑' j : ℕ, M * ((1/M) * jbDecay (n+1) (t + (j:ℝ)/M)) := by
    refine tsum_congr (fun j => ?_)
    field_simp
  rw [h2, tsum_mul_left]
  calc M * (∑' j : ℕ, (1/M) * jbDecay (n+1) (t + (j:ℝ)/M)) ≤ M * ((2:ℝ)^60 * jbDecay n t) :=
        mul_le_mul_of_nonneg_left hr' hM0.le
    _ = (2:ℝ)^60 * M * jbDecay n t := by ring

/-- **Tail of the `⟨·⟩^{-12}`-lattice.**  For `M ≥ 1`, `θ ≥ 0`,
`∑_{|m| > θ} ⟨m/M⟩^{-12} ≤ 4·2^60 M ⟨θ/M⟩^{-11}`. -/
theorem jbDecayIntTailLe {M θ : ℝ} (hM : 1 ≤ M) (hθ : 0 ≤ θ) :
    (∑' m : ℤ, (if θ < |((m:ℤ):ℝ)| then jbDecay 12 ((m:ℝ)/M) else 0))
      ≤ 4 * (2:ℝ)^60 * M * jbDecay 11 (θ/M) := by
  have hM0 : 0 < M := by linarith
  have hlam0 : (0:ℝ) < 1/M := by positivity
  have jdabs : ∀ (n : ℕ) (t : ℝ), jbDecay n |t| = jbDecay n t := by
    intro n t; rw [jbDecay, jbDecay, jb_abs]
  set f : ℤ → ℝ := fun m => if θ < |(m:ℝ)| then jbDecay 12 ((m:ℝ)/M) else 0 with hf
  have hev : ∀ z : ℤ, θ < |(z:ℝ)| → f z = jbDecay 12 (|(z:ℝ)|/M) := by
    intro z hz
    simp only [hf]
    rw [if_pos hz, ← jdabs 12 ((z:ℝ)/M), abs_div, abs_of_pos hM0]
  have hnev : ∀ z : ℤ, |(z:ℝ)| ≤ θ → f z = 0 := by
    intro z hz; simp only [hf]; rw [if_neg (not_lt.mpr hz)]
  have hfdec : ∀ z : ℤ, f z ≤ jbDecay 12 (|(z:ℝ)|/M) := by
    intro z
    by_cases h : θ < |(z:ℝ)|
    · rw [hev z h]
    · rw [hnev z (not_lt.mp h)]; exact jbDecay_nonneg _ _
  have hfn : ∀ m, 0 ≤ f m := by
    intro m; simp only [hf]; split_ifs
    · exact jbDecay_nonneg _ _
    · exact le_refl 0
  have hg1 : Summable (fun k : ℕ => f (k:ℤ)) := by
    refine Summable.of_nonneg_of_le (f := fun k : ℕ => jbDecay 12 ((k:ℝ)/M))
      (fun k => hfn _) (fun k => ?_) ?_
    · simp only [hf]
      split_ifs with h
      · rfl
      · exact jbDecay_nonneg _ _
    · refine (Work.KMTAreas.A4.jbDecay_nat_summable (N := 12) le_rfl (lam := 1/M) hlam0).congr
        (fun k => ?_)
      congr 1
      rw [div_eq_mul_inv]; ring
  have hg2 : Summable (fun k : ℕ => f (-((k:ℤ)+1))) := by
    refine Summable.of_nonneg_of_le (f := fun k : ℕ => jbDecay 12 (((k:ℝ)+1)/M))
      (fun k => hfn _) (fun k => ?_) ?_
    · refine (hfdec (-((k:ℤ)+1))).trans ?_
      refine le_of_eq ?_
      congr 1
      rw [show (((-(((k:ℤ)+1))):ℤ):ℝ) = -((k:ℝ)+1) by push_cast; ring, abs_neg,
        abs_of_nonneg (by positivity)]
    · refine (Work.KMTAreas.A4.jbDecay_nat_shift_summable (N := 12) le_rfl (lam := 1/M) hlam0
        (t := (1:ℝ)/M) (by positivity)).congr (fun k => ?_)
      ring_nf
  have hfk0 : (0:ℤ) ≤ ⌊θ⌋ := Int.le_floor.mpr (by simpa using hθ)
  set k : ℕ := ⌊θ⌋.toNat with hk
  have hkR : ((k:ℝ)) = (⌊θ⌋ : ℝ) := by
    rw [hk]; exact_mod_cast (Int.toNat_of_nonneg hfk0)
  have hkR1 : θ < (k:ℝ) + 1 := by rw [hkR]; linarith [Int.lt_floor_add_one θ]
  have hk1pos : (0:ℝ) ≤ ((k:ℝ) + 1)/M :=
    div_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) + 1) hM0.le
  have h2e : (0:ℝ) ≤ (2:ℝ)^60 * M :=
    mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 60) hM0.le
  rw [tsum_of_nat_of_neg_add_one (f := f) hg1 hg2]
  have hpos : (∑' n : ℕ, f (n:ℤ)) ≤ (2:ℝ)^60 * M * jbDecay 11 (θ/M) := by
    have hzero : (∑ n ∈ Finset.range (k+1), f (n:ℤ)) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      refine hnev _ ?_
      have h3 : ((n:ℝ)) ≤ (k:ℝ) := by
        have h1 : n ≤ k := by
          have h2 : n < k + 1 := Finset.mem_range.mp hn
          omega
        exact_mod_cast h1
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (((n:ℤ)):ℝ))]
      push_cast
      rw [hkR] at h3
      linarith [Int.floor_le θ]
    have hsplit := Summable.sum_add_tsum_nat_add (k+1) hg1
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have hval : (∑' j : ℕ, f (((j + (k+1) : ℕ)) : ℤ))
        = ∑' j : ℕ, jbDecay 12 (((j:ℝ) + (k:ℝ) + 1)/M) := by
      refine tsum_congr (fun j => ?_)
      rw [hev _ ?_]
      · congr 1
        push_cast
        rw [abs_of_nonneg (by positivity)]
        try ring
      · rw [abs_of_nonneg (by positivity)]
        push_cast
        linarith [hkR1, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
    rw [hval]
    have h2 : (∑' j : ℕ, jbDecay 12 (((j:ℝ) + (k:ℝ) + 1)/M))
        = ∑' j : ℕ, jbDecay 12 (((k:ℝ) + 1)/M + (j:ℝ)/M) := by
      refine tsum_congr (fun j => by congr 1; ring)
    rw [h2]
    refine (half_lattice_tail_le 11 (by norm_num) hM (t := ((k:ℝ)+1)/M) hk1pos).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ h2e
    refine jbDecay_le_of_abs_le ?_
    rw [abs_of_nonneg (div_nonneg hθ hM0.le), abs_of_nonneg hk1pos]
    exact div_le_div_of_nonneg_right (by linarith [hkR1]) hM0.le
  have hneg : (∑' n : ℕ, f (-((n:ℤ)+1))) ≤ (2:ℝ)^60 * M * jbDecay 11 (θ/M) := by
    have hzero : (∑ n ∈ Finset.range k, f (-((n:ℤ)+1))) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      refine hnev _ ?_
      have h3 : ((n:ℝ)) + 1 ≤ (k:ℝ) := by
        have h1 : n + 1 ≤ k := by
          have h2 : n < k := Finset.mem_range.mp hn
          omega
        exact_mod_cast h1
      rw [show (((-((n:ℤ)+1) : ℤ)) : ℝ) = -((n:ℝ)+1) by push_cast; ring, abs_neg,
        abs_of_nonneg (by positivity)]
      rw [hkR] at h3
      linarith [Int.floor_le θ]
    have hsplit := Summable.sum_add_tsum_nat_add k hg2
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have hval : (∑' j : ℕ, f (-(((((j + k : ℕ)):ℤ)) + 1)))
        = ∑' j : ℕ, jbDecay 12 (((j:ℝ) + (k:ℝ) + 1)/M) := by
      refine tsum_congr (fun j => ?_)
      rw [hev _ ?_]
      · congr 1
        push_cast
        rw [abs_neg, abs_of_nonneg (by positivity)]
        try ring
      · rw [show (((-(((((j + k : ℕ)):ℤ)) + 1) : ℤ)) : ℝ) = -(((j:ℝ) + (k:ℝ)) + 1) by
            push_cast; ring, abs_neg, abs_of_nonneg (by positivity)]
        linarith [hkR1, (Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ))]
    rw [hval]
    have h2 : (∑' j : ℕ, jbDecay 12 (((j:ℝ) + (k:ℝ) + 1)/M))
        = ∑' j : ℕ, jbDecay 12 (((k:ℝ) + 1)/M + (j:ℝ)/M) := by
      refine tsum_congr (fun j => by congr 1; ring)
    rw [h2]
    refine (half_lattice_tail_le 11 (by norm_num) hM (t := ((k:ℝ)+1)/M) hk1pos).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ h2e
    refine jbDecay_le_of_abs_le ?_
    rw [abs_of_nonneg (div_nonneg hθ hM0.le), abs_of_nonneg hk1pos]
    exact div_le_div_of_nonneg_right (by linarith [hkR1]) hM0.le
  have hfin : (2:ℝ)^60 * M * jbDecay 11 (θ/M) + (2:ℝ)^60 * M * jbDecay 11 (θ/M)
      ≤ 4 * (2:ℝ)^60 * M * jbDecay 11 (θ/M) := by
    have h1 : (0:ℝ) ≤ (2:ℝ)^60 * M * jbDecay 11 (θ/M) :=
      mul_nonneg h2e (jbDecay_nonneg _ _)
    linarith
  linarith [hpos, hneg, hfin]

/-- **Summability of the shifted lattice of `⟨·⟩^{-n}` over `ℤ`.** For `12 ≤ n`, `M > 0` and any
`N₀ : ℕ`, the family `x ↦ ⟨max 0 ((|x| - N₀)/M)⟩^{-n}` is summable. -/
theorem summable_jbDecay_max {n : ℕ} (hn : 12 ≤ n) {M : ℝ} (hM : 0 < M) (N₀ : ℕ) :
    Summable (fun x : ℤ => jbDecay n (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)))) := by
  have hbase : Summable (fun z : ℤ => jbDecay n ((z:ℝ)/M)) :=
    Summable.of_nonneg_of_le (fun z => jbDecay_nonneg _ _)
      (fun z => jbDecay_anti hn _) (Work.KMTAreas.A4.jbDecay_int_summable_div (N := 12) le_rfl hM)
  have hshift1 : Summable (fun x : ℤ => jbDecay n (((x:ℝ) - (N₀:ℝ))/M)) := by
    have hinj : Function.Injective (fun x : ℤ => x - (N₀:ℤ)) := by
      intro a b h
      dsimp only at h
      omega
    refine (hbase.comp_injective hinj).congr (fun x => ?_)
    show jbDecay n ((((x - (N₀:ℤ)) : ℤ):ℝ)/M) = jbDecay n (((x:ℝ) - (N₀:ℝ))/M)
    rw [show (((x - (N₀:ℤ) : ℤ)):ℝ) = (x:ℝ) - (N₀:ℝ) by push_cast; ring]
  have hshift2 : Summable (fun x : ℤ => jbDecay n (((-(x:ℝ)) - (N₀:ℝ))/M)) := by
    have hinj : Function.Injective (fun x : ℤ => -x - (N₀:ℤ)) := by
      intro a b h
      dsimp only at h
      omega
    refine (hbase.comp_injective hinj).congr (fun x => ?_)
    show jbDecay n ((((-x - (N₀:ℤ)) : ℤ):ℝ)/M) = jbDecay n (((-(x:ℝ)) - (N₀:ℝ))/M)
    rw [show ((((-x - (N₀:ℤ)) : ℤ)):ℝ) = (-(x:ℝ)) - (N₀:ℝ) by push_cast; ring]
  have hmem : ∀ b : ℤ, |(b:ℝ)| ≤ (N₀:ℝ) → b ∈ Finset.Icc (-(N₀:ℤ)) (N₀:ℤ) := by
    intro b hb
    rw [Finset.mem_Icc]
    rw [abs_le] at hb
    constructor
    · have h1 : -((N₀:ℤ):ℝ) ≤ (b:ℝ) := by push_cast at hb ⊢; exact hb.1
      exact_mod_cast h1
    · have h1 : (b:ℝ) ≤ ((N₀:ℤ):ℝ) := by push_cast at hb ⊢; exact hb.2
      exact_mod_cast h1
  have hfin : Summable (fun x : ℤ => (if |(x:ℝ)| ≤ (N₀:ℝ) then (1:ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)) (fun b hb => by
      rw [if_neg (fun h => hb (hmem b h))])
  refine Summable.of_nonneg_of_le (fun x => jbDecay_nonneg _ _) (fun x => ?_)
    ((hshift1.add hshift2).add hfin)
  by_cases hx : |(x:ℝ)| ≤ (N₀:ℝ)
  · have h0 : max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)) = 0 := by
      rw [max_eq_left]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hM.le
    rw [h0, jbDecay_n_zero]
    simp only [if_pos hx]
    have h2 : (0:ℝ) ≤ jbDecay n (((x:ℝ) - (N₀:ℝ))/M) + jbDecay n (((-(x:ℝ)) - (N₀:ℝ))/M) :=
      add_nonneg (jbDecay_nonneg _ _) (jbDecay_nonneg _ _)
    linarith
  · have hx' : (N₀:ℝ) < |(x:ℝ)| := not_le.mp hx
    have h1 : max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)) = ((|(x:ℝ)| - (N₀:ℝ))/M) :=
      max_eq_right (div_nonneg (by linarith) hM.le)
    rw [h1]
    simp only [if_neg hx, add_zero]
    by_cases hx0 : (0:ℤ) ≤ x
    · have habs : |(x:ℝ)| = (x:ℝ) := abs_of_nonneg (by exact_mod_cast hx0)
      rw [habs]
      linarith [jbDecay_nonneg n (((-(x:ℝ)) - (N₀:ℝ))/M)]
    · have hx0' : x < 0 := not_le.mp hx0
      have habs : |(x:ℝ)| = -(x:ℝ) := abs_of_neg (by exact_mod_cast hx0')
      rw [habs]
      linarith [jbDecay_nonneg n (((x:ℝ) - (N₀:ℝ))/M)]

/-! ## Pointwise decay and tail mass of the window -/

/-- The pointwise Schwartz decay of the window: `‖win M γ m‖ ≤ C_ψ M⁻¹ ⟨m/M⟩^{-12}`. -/
theorem win_pointwise_le (M : ℝ) (hM : 0 < M) (γ : FreqCircle) (m : ℤ) :
    ‖Work.KMTAreas.A4.win M γ m‖ ≤ winC / M * jbDecay 12 ((m:ℝ)/M) := by
  have hψ := schwartz_decay Work.KMTAreas.A4.lipSchPsi ((m:ℝ)/M)
  have hfour : ‖(fourier m γ : ℂ)‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  rw [Work.KMTAreas.A4.win, norm_mul, norm_mul, hfour, mul_one]
  have hMinv : ‖((M:ℂ))⁻¹‖ = M⁻¹ := by
    have h1 : ‖((M:ℂ))‖ = |M| := RCLike.norm_ofReal M
    rw [norm_inv, h1, abs_of_pos hM]
  rw [hMinv, winC]
  calc M⁻¹ * ‖Work.KMTAreas.A4.lipSchPsi ((m:ℝ)/M)‖
      ≤ M⁻¹ * ((2:ℝ)^12 * (schwartzSeminormSum Work.KMTAreas.A4.lipSchPsi + 1)
          * jbDecay 12 ((m:ℝ)/M)) := mul_le_mul_of_nonneg_left hψ (by positivity)
    _ = (2:ℝ)^12 * (schwartzSeminormSum Work.KMTAreas.A4.lipSchPsi + 1) / M
          * jbDecay 12 ((m:ℝ)/M) := by ring

/-- **Tail mass of the window.**  For `M ≥ 1`, `γ` and any threshold `θ`,
`∑_{|m| > θ} ‖win M γ m‖ ≤ K ⟨max 0 θ/M⟩^{-11}`, where `K = max C_win (4·2^60 C_ψ)` and `C_win`
bounds the total mass `∑_m ‖win M γ m‖` uniformly. -/
theorem win_tail_le (Cwin : ℝ)
    (hCwin : ∀ (M : ℝ) (γ : FreqCircle), 1 ≤ M → (∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖) ≤ Cwin)
    (M : ℝ) (hM : 1 ≤ M) (γ : FreqCircle) (θ : ℝ) :
    (∑' m : ℤ, (if θ < |((m:ℤ):ℝ)| then ‖Work.KMTAreas.A4.win M γ m‖ else 0))
      ≤ max Cwin (4 * (2:ℝ)^60 * winC) * jbDecay 11 (max 0 (θ / M)) := by
  have hM0 : 0 < M := by linarith
  have hCn : (0:ℝ) ≤ winC := by
    rw [winC]
    have := schwartzSeminormSum_nonneg Work.KMTAreas.A4.lipSchPsi
    positivity
  set T : ℤ → ℝ := fun m => if θ < |(m:ℝ)| then ‖Work.KMTAreas.A4.win M γ m‖ else 0 with hT
  have hTnn : ∀ m, 0 ≤ T m := by
    intro m; simp only [hT]; split_ifs
    · exact norm_nonneg _
    · exact le_refl 0
  have hTle : ∀ m, T m ≤ ‖Work.KMTAreas.A4.win M γ m‖ := by
    intro m; simp only [hT]; split_ifs
    · exact le_refl _
    · exact norm_nonneg _
  have hTsum : Summable T :=
    Summable.of_nonneg_of_le hTnn hTle (Work.KMTAreas.A4.win_summable M hM γ)
  by_cases hθ : θ ≤ 0
  · have h1 : (∑' m : ℤ, T m) ≤ Cwin :=
      (Summable.tsum_le_tsum hTle hTsum (Work.KMTAreas.A4.win_summable M hM γ)).trans
        (hCwin M γ hM)
    have h3 : max 0 (θ / M) = 0 := max_eq_left (div_nonpos_of_nonpos_of_nonneg hθ hM0.le)
    rw [h3, jbDecay_n_zero, mul_one]
    exact h1.trans (le_max_left _ _)
  · have hθ' : 0 < θ := not_le.mp hθ
    have hTle' : ∀ m, T m ≤ (if θ < |(m:ℝ)| then winC / M * jbDecay 12 ((m:ℝ)/M) else 0) := by
      intro m
      simp only [hT]
      split_ifs with h
      · exact win_pointwise_le M hM0 γ m
      · exact le_refl 0
    have hmaj : Summable (fun m : ℤ =>
        (if θ < |(m:ℝ)| then winC / M * jbDecay 12 ((m:ℝ)/M) else 0)) := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        ((Work.KMTAreas.A4.jbDecay_int_summable_div (N := 12) le_rfl hM0).mul_left (winC / M))
      · split_ifs
        · exact mul_nonneg (div_nonneg hCn hM0.le) (jbDecay_nonneg _ _)
        · exact le_refl 0
      · split_ifs with h
        · exact le_rfl
        · exact mul_nonneg (div_nonneg hCn hM0.le) (jbDecay_nonneg _ _)
    have h2 : (∑' m : ℤ, T m)
        ≤ ∑' m : ℤ, (if θ < |(m:ℝ)| then winC / M * jbDecay 12 ((m:ℝ)/M) else 0) :=
      Summable.tsum_le_tsum hTle' hTsum hmaj
    have h3 : (∑' m : ℤ, (if θ < |(m:ℝ)| then winC / M * jbDecay 12 ((m:ℝ)/M) else 0))
        = winC / M * ∑' m : ℤ, (if θ < |(m:ℝ)| then jbDecay 12 ((m:ℝ)/M) else 0) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun m => ?_)
      by_cases h : θ < |(m:ℝ)| <;> simp [h]
    have h4 : (∑' m : ℤ, (if θ < |(m:ℝ)| then jbDecay 12 ((m:ℝ)/M) else 0))
        ≤ 4 * (2:ℝ)^60 * M * jbDecay 11 (θ/M) := jbDecayIntTailLe hM hθ'.le
    have h5 : winC / M * (4 * (2:ℝ)^60 * M * jbDecay 11 (θ/M))
        = (4 * (2:ℝ)^60 * winC) * jbDecay 11 (θ/M) := by
      field_simp
    have h6 : max 0 (θ / M) = θ / M := max_eq_right (div_nonneg hθ'.le hM0.le)
    rw [h6]
    calc (∑' m : ℤ, T m)
        ≤ winC / M * (4 * (2:ℝ)^60 * M * jbDecay 11 (θ/M)) := by
          rw [h3] at h2
          exact h2.trans (mul_le_mul_of_nonneg_left h4 (div_nonneg hCn hM0.le))
      _ = (4 * (2:ℝ)^60 * winC) * jbDecay 11 (θ/M) := h5
      _ ≤ max Cwin (4 * (2:ℝ)^60 * winC) * jbDecay 11 (θ / M) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (jbDecay_nonneg _ _)

/-! ## The arithmetic core of the spatial decay -/

/-- **The arithmetic of the decay.**  For `M > 0`, `N₀, G ≥ 0`, `L` arbitrary and
`ν = max 0 ((L - N₀)/M)`:
`L · min(G/M, 1) · ⟨ν⟩^{-11} ≤ N₀ + G`. -/
theorem decay_arith (M L N₀ G : ℝ) (hM : 0 < M) (hN₀ : 0 ≤ N₀) (hG : 0 ≤ G) :
    L * min (G / M) 1 * jbDecay 11 (max 0 ((L - N₀) / M)) ≤ N₀ + G := by
  set s : ℝ := max 0 ((L - N₀) / M) with hs
  have hs0 : 0 ≤ s := le_max_left _ _
  have hmin0 : 0 ≤ min (G / M) 1 := le_min (div_nonneg hG hM.le) (by norm_num)
  have hL : L ≤ N₀ + M * s := by
    have h1 : (L - N₀) / M ≤ s := le_max_right _ _
    rw [div_le_iff₀ hM] at h1
    linarith
  have hMs : M * min (G / M) 1 ≤ G := by
    calc M * min (G / M) 1 ≤ M * (G / M) := mul_le_mul_of_nonneg_left (min_le_left _ _) hM.le
      _ = G := by field_simp
  have hkey : L * min (G / M) 1 * jbDecay 11 s
      ≤ (N₀ + M * s) * min (G / M) 1 * jbDecay 11 s := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hmin0) (jbDecay_nonneg _ _)
  by_cases hs1 : s ≤ 1
  · have hjb : jbDecay 11 s ≤ 1 := jbDecay_le_one _ _
    have hN0s : (0:ℝ) ≤ N₀ + M * s := by
      have : 0 ≤ M * s := mul_nonneg hM.le hs0
      linarith
    calc L * min (G / M) 1 * jbDecay 11 s
        ≤ (N₀ + M * s) * min (G / M) 1 * jbDecay 11 s := hkey
      _ ≤ (N₀ + M * s) * min (G / M) 1 * 1 :=
          mul_le_mul_of_nonneg_left hjb (mul_nonneg hN0s hmin0)
      _ = N₀ * min (G / M) 1 + s * (M * min (G / M) 1) := by ring
      _ ≤ N₀ * 1 + s * G := add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hN₀)
            (mul_le_mul_of_nonneg_left hMs hs0)
      _ ≤ N₀ + G := by nlinarith [hs1, hG, hs0]
  · have hs1' : (1:ℝ) ≤ s := not_le.mp hs1 |>.le
    have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs1'
    have hjb : jbDecay 11 s ≤ s⁻¹ ^ 11 := by
      rw [jbDecay]
      refine pow_le_pow_left₀ (jb_inv_nonneg _) ?_ 11
      rw [inv_le_inv₀ (jb_pos _) hspos]
      exact (le_abs_self s).trans (abs_le_jb s)
    have hsinv : s * s⁻¹ ^ 11 = s⁻¹ ^ 10 := by
      rw [show s⁻¹ ^ 11 = s⁻¹ ^ 10 * s⁻¹ by rw [pow_succ]]
      rw [show s * (s⁻¹ ^ 10 * s⁻¹) = s⁻¹ ^ 10 * (s * s⁻¹) by ring,
        mul_inv_cancel₀ (by positivity), mul_one]
    calc L * min (G / M) 1 * jbDecay 11 s
        ≤ (N₀ + M * s) * min (G / M) 1 * s⁻¹ ^ 11 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hL hmin0) hjb (jbDecay_nonneg _ _)
            (by positivity)
      _ = N₀ * (min (G / M) 1 * s⁻¹ ^ 11) + (M * min (G / M) 1) * (s⁻¹ ^ 10) := by
          rw [show (N₀ + M * s) * min (G / M) 1 * s⁻¹ ^ 11
              = N₀ * (min (G / M) 1 * s⁻¹ ^ 11) + (M * min (G / M) 1) * (s * s⁻¹ ^ 11) by
            ring]
          rw [hsinv]
      _ ≤ N₀ * 1 + G * 1 := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_left ?_ hN₀
            exact mul_le_one₀ (min_le_right _ _) (pow_nonneg (by positivity) 11) (pow_le_one₀ (by positivity) (by rw [inv_le_one₀ hspos]; exact hs1'))
          · exact mul_le_mul hMs (pow_le_one₀ (by positivity) (by rw [inv_le_one₀ hspos]; exact hs1'))
              (by positivity) hG
      _ = N₀ + G := by ring


/-! ## The lattice counting bound for the tail -/

/-- Membership criterion for the window around `x`: `|x - m| ≤ N₀` iff
`m ∈ [x - N₀, x + N₀]`. -/
theorem abs_sub_le_iff_mem_Icc (N₀ : ℕ) (x m : ℤ) :
    |(((x - m : ℤ)) : ℝ)| ≤ (N₀:ℝ) ↔ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)) := by
  have h4 : (((x - m : ℤ)) : ℝ) = (x:ℝ) - (m:ℝ) := by push_cast; ring
  have h5 : (((x - (N₀:ℤ) : ℤ)) : ℝ) = (x:ℝ) - (N₀:ℝ) := by push_cast; ring
  have h6 : (((x + (N₀:ℤ) : ℤ)) : ℝ) = (x:ℝ) + (N₀:ℝ) := by push_cast; ring
  rw [Finset.mem_Icc, abs_le, h4]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h3 : (((x - (N₀:ℤ)) : ℤ) : ℝ) ≤ (m:ℝ) := by rw [h5]; linarith
      exact_mod_cast h3
    · have h3 : (m:ℝ) ≤ (((x + (N₀:ℤ)) : ℤ) : ℝ) := by rw [h6]; linarith
      exact_mod_cast h3
  · rintro ⟨h1, h2⟩
    constructor
    · have h3 : (m:ℝ) ≤ (((x + (N₀:ℤ)) : ℤ) : ℝ) := by exact_mod_cast h2
      rw [h6] at h3
      linarith
    · have h3 : (((x - (N₀:ℤ)) : ℤ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast h1
      rw [h5] at h3
      linarith

/-- **Lattice counting for the tail.**  If `f ≥ 0` is summable, then the double sum of `f` over
all pairs `(x,m)` with `L < |x|` and `|x - m| ≤ N₀` is at most `(2N₀+1)` times the tail of `f`
beyond `L - N₀`: every contributing `m` lies in the tail, and for each `m` there are at most
`2N₀+1` such `x`. -/
theorem tsum_tail_fubini_own (f : ℤ → ℝ) (hf : ∀ m, 0 ≤ f m) (hfs : Summable f)
    (N₀ : ℕ) (L : ℝ) :
    (∑' x : ℤ, (if L < |((x : ℤ) : ℝ)| then
        ∑' m : ℤ, (if |(((x - m : ℤ)) : ℝ)| ≤ (N₀ : ℝ) then f m else 0) else 0))
      ≤ (2 * (N₀ : ℝ) + 1) *
          (∑' m : ℤ, (if L - (N₀ : ℝ) < |((m : ℤ) : ℝ)| then f m else 0)) := by
  set F : ℤ → ℝ := fun m => if L - (N₀:ℝ) < |(m:ℝ)| then f m else 0 with hF
  set g : ℤ → ℝ := fun x => if L < |(x:ℝ)| then
      ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), f m else 0 with hg
  have hFnn : ∀ m, 0 ≤ F m := by
    intro m
    show 0 ≤ (if L - (N₀:ℝ) < |(m:ℝ)| then f m else 0)
    split_ifs
    · exact hf m
    · exact le_refl 0
  have hFsum : Summable F := by
    refine Summable.of_nonneg_of_le hFnn (fun m => ?_) hfs
    show (if L - (N₀:ℝ) < |(m:ℝ)| then f m else 0) ≤ f m
    split_ifs
    · exact le_refl _
    · exact hf m
  have hgnn : ∀ x, 0 ≤ g x := by
    intro x
    show 0 ≤ (if L < |(x:ℝ)| then
      ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), f m else 0)
    split_ifs
    · exact Finset.sum_nonneg (fun m _ => hf m)
    · exact le_refl 0
  have himg : ∀ x : ℤ, (Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).image (fun y => x + y)
      = Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)) := by
    intro x
    ext m
    constructor
    · intro hm
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
      rw [Finset.mem_Icc] at hy ⊢
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · intro hm
      rw [Finset.mem_Icc] at hm
      refine Finset.mem_image.mpr ⟨m - x, ?_, by ring⟩
      rw [Finset.mem_Icc]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hreindex : ∀ (x : ℤ) (G : ℤ → ℝ),
      (∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), G m)
        = ∑ y ∈ Finset.Icc (-(N₀:ℤ)) (N₀:ℤ), G (x + y) := by
    intro x G
    rw [← himg x, Finset.sum_image]
    intro a _ b _ hab
    dsimp only at hab
    omega
  have hcardJ : (((Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).card : ℕ) : ℝ) = 2 * (N₀:ℝ) + 1 := by
    have h2 : (((Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).card : ℕ) : ℤ) = 1 + (N₀:ℤ) * 2 := by
      rw [Int.card_Icc]
      have h3 : (0:ℤ) ≤ (N₀:ℤ) + 1 - (-(N₀:ℤ)) := by omega
      rw [Int.toNat_of_nonneg h3]
      ring
    have h3 : (((Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).card : ℕ) : ℝ)
        = (((1 + (N₀:ℤ) * 2 : ℤ)) : ℝ) := by
      rw [show (((Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).card : ℕ) : ℝ)
          = ((((Finset.Icc (-(N₀:ℤ)) (N₀:ℤ)).card : ℕ) : ℤ) : ℝ) from by push_cast; ring]
      rw [h2]
    rw [h3]
    push_cast
    ring
  have hm : ∀ x m : ℤ, m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)) → L < |(x:ℝ)| →
      L - (N₀:ℝ) < |(m:ℝ)| := by
    intro x m hm' hx
    have h2 : |(((x - m : ℤ)):ℝ)| ≤ (N₀:ℝ) := (abs_sub_le_iff_mem_Icc N₀ x m).mpr hm'
    have h5 : (((x - m : ℤ)):ℝ) = (x:ℝ) - (m:ℝ) := by push_cast; ring
    have h3 : |(x:ℝ)| ≤ |(m:ℝ)| + (N₀:ℝ) := by
      have h4 : |(x:ℝ)| = |((x:ℝ) - (m:ℝ)) + (m:ℝ)| := by
        conv_lhs => rw [show ((x:ℝ)) = ((x:ℝ) - (m:ℝ)) + (m:ℝ) by ring]
      rw [h5] at h2
      rw [h4]
      calc |((x:ℝ) - (m:ℝ)) + (m:ℝ)| ≤ |((x:ℝ) - (m:ℝ))| + |(m:ℝ)| := abs_add_le _ _
        _ ≤ (N₀:ℝ) + |(m:ℝ)| := by linarith
        _ = |(m:ℝ)| + (N₀:ℝ) := by ring
    linarith
  have hpt : ∀ x : ℤ, g x ≤ ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), F m := by
    intro x
    by_cases hx : L < |(x:ℝ)|
    · have hgx : g x = ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), f m := by
        simp only [hg, if_pos hx]
      rw [hgx]
      refine Finset.sum_le_sum (fun m hm' => ?_)
      show f m ≤ (if L - (N₀:ℝ) < |(m:ℝ)| then f m else 0)
      rw [if_pos (hm x m hm' hx)]
    · have hgx : g x = 0 := by simp only [hg, if_neg hx]
      rw [hgx]
      exact Finset.sum_nonneg (fun m _ => hFnn m)
  have hmain : ∀ u : Finset ℤ, (∑ x ∈ u, g x) ≤ (2 * (N₀:ℝ) + 1) * (∑' m : ℤ, F m) := by
    intro u
    have h1 : (∑ x ∈ u, g x)
        ≤ ∑ x ∈ u, ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), F m :=
      Finset.sum_le_sum (fun x _ => hpt x)
    refine h1.trans ?_
    have h2 : (∑ x ∈ u, ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), F m)
        = ∑ y ∈ Finset.Icc (-(N₀:ℤ)) (N₀:ℤ), ∑ x ∈ u, F (x + y) := by
      rw [Finset.sum_congr rfl (fun x _ => hreindex x F), Finset.sum_comm]
    rw [h2]
    calc ∑ y ∈ Finset.Icc (-(N₀:ℤ)) (N₀:ℤ), ∑ x ∈ u, F (x + y)
        ≤ ∑ y ∈ Finset.Icc (-(N₀:ℤ)) (N₀:ℤ), (∑' m : ℤ, F m) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          refine (Summable.sum_le_tsum u (fun m _ => hFnn (m + y))
            (hFsum.comp_injective (show Function.Injective (fun x : ℤ => x + y) from
              (fun a b h => by dsimp only at h; omega)))).trans_eq ?_
          exact (Equiv.addRight y).tsum_eq F
      _ = (2 * (N₀:ℝ) + 1) * (∑' m : ℤ, F m) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardJ]
  have hgl : (∑' x : ℤ, (if L < |((x:ℤ):ℝ)| then
        ∑' m : ℤ, (if |(((x - m : ℤ)):ℝ)| ≤ (N₀:ℝ) then f m else 0) else 0))
      = ∑' x : ℤ, g x := by
    refine tsum_congr (fun x => ?_)
    by_cases h : L < |(x:ℝ)|
    · have hgx : g x = ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), f m := by
        simp only [hg, if_pos h]
      rw [hgx]
      refine (if_pos h).trans ?_
      refine (tsum_eq_sum (s := Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)))
        (f := fun m : ℤ => (if |(((x - m : ℤ)):ℝ)| ≤ (N₀:ℝ) then f m else 0)) ?_).trans ?_
      · intro m hm'
        rw [if_neg]
        exact fun hh => hm' ((abs_sub_le_iff_mem_Icc N₀ x m).mp hh)
      · refine Finset.sum_congr rfl (fun m hm' => ?_)
        rw [if_pos ((abs_sub_le_iff_mem_Icc N₀ x m).mpr hm')]
    · have hgx : g x = 0 := by simp only [hg, if_neg h]
      rw [hgx]
      exact if_neg h
  have hFs : (∑' m : ℤ, (if L - (N₀ : ℝ) < |((m : ℤ) : ℝ)| then f m else 0))
      = ∑' m : ℤ, F m := by
    refine tsum_congr (fun m => ?_)
    rw [hF]
  rw [hgl, hFs]
  exact Real.tsum_le_of_sum_le hgnn hmain

/-! ## The main theorem -/

theorem projectionL2Decay (P : Polynomial ℤ) : ∀ (A : ℝ), 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (N₀ : ℕ), (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree → ∀ (g : ℤ → ℂ), Summable (fun x : ℤ => ‖g x‖) → (∀ x : ℤ, ‖g x‖ ≤ 1) → Work.Analysis.InverseTheory.SupportIn g N₀ → ∀ (M : ℝ), 2 ≤ M → ∀ (s : ℝ), ∀ (R : ℝ), 1 ≤ R → (∑' x : ℤ, (if R * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖(star (fun x : ℤ => ∑' m : ℤ, Work.KMTAreas.A4.win M (((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle)) m * g (x - m))) x‖ ^ 2 else 0)) ≤ C ^ 2 * R ^ (-(1 : ℝ)) * (N : ℝ) ^ P.natDegree := by
  intro A hA
  obtain ⟨Cwin, hCwin0, hCwin⟩ := Work.KMTAreas.A4.win_tsum_le
  have hwinC0 : 0 < winC := by
    rw [winC]
    have := schwartzSeminormSum_nonneg Work.KMTAreas.A4.lipSchPsi
    positivity
  set Kwin : ℝ := max Cwin (4 * (2:ℝ)^60 * winC) with hKwin
  set Kc : ℝ := max winC Cwin with hKc
  have hKwin0 : 0 < Kwin := by rw [hKwin]; exact lt_of_lt_of_le hCwin0 (le_max_left _ _)
  have hKc0 : 0 < Kc := by rw [hKc]; exact lt_of_lt_of_le hwinC0 (le_max_left _ _)
  refine ⟨Real.sqrt (18 * Kwin * Kc * A ^ 2),
    Real.sqrt_pos.mpr (mul_pos (mul_pos (mul_pos (by norm_num) hKwin0) hKc0)
      (pow_pos (by linarith) 2)), ?_⟩
  intro N hN N₀ hN0 g hgsum hgbd hsupp M hM s R hR
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have he1 : (1:ℝ) ≤ (N:ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  set e : ℝ := (N:ℝ) ^ P.natDegree with he
  set G : ℝ := 2*(N₀:ℝ) + 1 with hGdef
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hGle : G ≤ 3*A*e := by
    rw [hGdef, he]
    nlinarith [hN0, hA, he1]
  have hGsq : G^2 ≤ 9*A^2*e^2 := by nlinarith [hG0, hGle, hA, he1]
  set L : ℝ := R * e with hLdef
  have hL0 : 0 < L := by rw [hLdef]; positivity
  set w : ℤ → ℂ := Work.KMTAreas.A4.win M ((s:ℝ):FreqCircle) with hwdef
  set F : ℤ → ℂ := fun x : ℤ => ∑' m : ℤ, w m * g (x - m) with hFdef
  set Af : ℤ → ℝ := fun x : ℤ =>
    ∑' m : ℤ, (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0) with hAfdef
  have hwsum : Summable fun m : ℤ => ‖w m‖ := by
    rw [hwdef]; exact Work.KMTAreas.A4.win_summable M hM1 _
  have hwm : (∑' m : ℤ, ‖w m‖) ≤ Cwin := by rw [hwdef]; exact hCwin M _ hM1
  have hwp : ∀ m : ℤ, ‖w m‖ ≤ winC / M * jbDecay 12 ((m:ℝ)/M) := by
    intro m; rw [hwdef]; exact win_pointwise_le M hM0 _ m
  have hwt : ∀ θ : ℝ, (∑' m : ℤ, (if θ < |((m:ℤ):ℝ)| then ‖w m‖ else 0))
      ≤ Kwin * jbDecay 11 (max 0 (θ / M)) := by
    intro θ
    have h := win_tail_le Cwin hCwin M hM1 ((s:ℝ):FreqCircle) θ
    rw [hKwin]
    simpa only [hwdef] using h
  -- rewrite the target
  have hgoal : (∑' x : ℤ, (if L < |(x:ℝ)| then ‖(star F) x‖ ^ 2 else 0))
      = ∑' x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0) := by
    refine tsum_congr (fun x => ?_)
    rw [Pi.star_apply, norm_star]
  rw [hgoal]
  -- (i) ‖F x‖ ≤ Af x
  have hFA : ∀ x : ℤ, ‖F x‖ ≤ Af x := by
    intro x
    have hsum' : Summable (fun m : ℤ => w m * g (x - m)) := by
      refine Summable.of_norm_bounded hwsum (fun m => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hgbd _)
    show ‖(∑' m : ℤ, w m * g (x - m))‖
      ≤ ∑' m : ℤ, (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0)
    refine (norm_tsum_le_tsum_norm hsum'.norm).trans ?_
    have hnn : ∀ m : ℤ, 0 ≤ (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0) := by
      intro m
      by_cases h : |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ)
      · exact le_trans (norm_nonneg (w m)) (le_of_eq (if_pos h).symm)
      · exact le_of_eq (if_neg h).symm
    have hmaj : Summable (fun m : ℤ =>
        (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0)) :=
      Summable.of_nonneg_of_le hnn (fun m => by
        by_cases h : |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ)
        · exact le_of_eq (if_pos h)
        · exact le_trans (le_of_eq (if_neg h)) (norm_nonneg (w m))) hwsum
    refine Summable.tsum_le_tsum (fun m => ?_) ?_ hmaj
    · rw [norm_mul]
      by_cases h : |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ)
      · rw [if_pos h]
        exact mul_le_of_le_one_right (norm_nonneg _) (hgbd _)
      · have hz : g (x - m) = 0 := by
          by_contra hne
          have hm := Work.Analysis.InverseTheory.SupportIn.mem_Icc hsupp hne
          rw [Finset.mem_Icc] at hm
          have h1 : (((x - m : ℤ)) : ℝ) ≤ (N₀:ℝ) := by
            have hh : x - m ≤ (N₀:ℤ) := hm.2
            exact_mod_cast hh
          have h2 : -((N₀:ℝ)) ≤ (((x - m : ℤ)) : ℝ) := by
            have hh : -(N₀:ℤ) ≤ x - m := hm.1
            exact_mod_cast hh
          have h3 : |(((x - m : ℤ)) : ℝ)| ≤ (N₀:ℝ) := by
            rw [abs_le]; exact ⟨h2, h1⟩
          have h4 : (((x - m : ℤ)) : ℝ) = (x:ℝ) - (m:ℝ) := by push_cast; ring
          rw [h4] at h3
          exact h h3
        have hzero : ‖w m‖ * ‖g (x - m)‖ = 0 := by rw [hz, norm_zero, mul_zero]
        exact le_trans (le_of_eq hzero) (le_of_eq (if_neg h).symm)
    · exact Summable.of_nonneg_of_le (fun m => by rw [norm_mul]; positivity)
        (fun m => by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hgbd _)) hwsum
  -- (ii) the membership criterion and the finitely supported form of `Af`
  have habs_cast : ∀ x m : ℤ, |(((x - m : ℤ)) : ℝ)| = |((x:ℝ) - (m:ℝ))| := by
    intro x m
    congr 1
    push_cast
    ring
  have hkey : ∀ (x m : ℤ), |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) ↔
      x - (N₀:ℤ) ≤ m ∧ m ≤ x + (N₀:ℤ) := by
    intro x m
    have h5 : (((x - (N₀:ℤ) : ℤ)) : ℝ) = (x:ℝ) - (N₀:ℝ) := by push_cast; ring
    have h6 : (((x + (N₀:ℤ) : ℤ)) : ℝ) = (x:ℝ) + (N₀:ℝ) := by push_cast; ring
    rw [abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have h3 : (((x - (N₀:ℤ)) : ℤ) : ℝ) ≤ (m:ℝ) := by rw [h5]; linarith
        exact_mod_cast h3
      · have h3 : (m:ℝ) ≤ (((x + (N₀:ℤ)) : ℤ) : ℝ) := by rw [h6]; linarith
        exact_mod_cast h3
    · rintro ⟨h1, h2⟩
      constructor
      · have h3 : (m:ℝ) ≤ (((x + (N₀:ℤ)) : ℤ) : ℝ) := by exact_mod_cast h2
        rw [h6] at h3
        linarith
      · have h3 : (((x - (N₀:ℤ)) : ℤ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast h1
        rw [h5] at h3
        linarith
  have hAf_fin : ∀ x : ℤ, Af x = ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), ‖w m‖ := by
    intro x
    show (∑' m : ℤ, (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0))
        = ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), ‖w m‖
    rw [tsum_eq_sum (s := Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)))
      (f := fun m : ℤ => (if |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) then ‖w m‖ else 0)) ?_]
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [if_pos ((hkey x m).mpr (Finset.mem_Icc.mp hm))]
    · intro m hm
      rw [if_neg]
      exact fun h => hm (Finset.mem_Icc.mpr ((hkey x m).mp h))
  -- (iii) the uniform bound `Af x ≤ min (G C_ψ/M) C_win`
  have hcard : ∀ x : ℤ, (((Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card : ℕ) : ℝ) = G := by
    intro x
    have h1 : x - (N₀:ℤ) ≤ (x + (N₀:ℤ)) + 1 := by omega
    have h2 : (((Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card : ℕ) : ℤ)
        = 1 + (N₀:ℤ) * 2 := by
      rw [Int.card_Icc]
      have h3 : (0:ℤ) ≤ x + (N₀:ℤ) + 1 - (x - (N₀:ℤ)) := by omega
      rw [Int.toNat_of_nonneg h3]
      ring
    rw [hGdef]
    have h3 : (((Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card : ℕ) : ℝ)
        = (((1 + (N₀:ℤ) * 2 : ℤ)) : ℝ) := by
      rw [show (((Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card : ℕ) : ℝ)
          = ((((Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card : ℕ) : ℤ) : ℝ) from by
        push_cast; ring]
      rw [h2]
    rw [h3]
    push_cast
    ring
  have hAn : ∀ x : ℤ, 0 ≤ Af x := by
    intro x; rw [hAf_fin x]; exact Finset.sum_nonneg (fun m _ => norm_nonneg _)
  have hAmax : ∀ x : ℤ, Af x ≤ min (G * winC / M) Cwin := by
    intro x
    rw [hAf_fin x]
    refine le_min ?_ ?_
    · calc ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), ‖w m‖
          ≤ ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), winC / M := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            exact (hwp m).trans (mul_le_of_le_one_right (div_nonneg (le_of_lt hwinC0) hM0.le)
              (jbDecay_le_one 12 _))
        _ = (Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card • (winC / M) := Finset.sum_const _
        _ = G * (winC / M) := by rw [nsmul_eq_mul, hcard x]
        _ = G * winC / M := by ring
    · exact (Summable.sum_le_tsum (Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)))
        (fun m _ => norm_nonneg _) hwsum).trans hwm
  -- (iv) summability of `x ↦ [L < |x|] Af x`
  have hAf_maj : ∀ x : ℤ, Af x ≤ G * (winC / M) * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M))) := by
    intro x
    rw [hAf_fin x]
    have h6 : ∀ m : ℤ, m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)) →
        max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)) ≤ |(m:ℝ)|/M := by
      intro m hm
      have h2 : |((x:ℝ) - (m:ℝ))| ≤ (N₀:ℝ) := (hkey x m).mpr (Finset.mem_Icc.mp hm)
      have h7 : |(x:ℝ)| ≤ |(m:ℝ)| + (N₀:ℝ) := by
        have h8 : |(x:ℝ)| = |((x:ℝ) - (m:ℝ)) + (m:ℝ)| := by
          conv_lhs => rw [show ((x:ℝ)) = ((x:ℝ) - (m:ℝ)) + (m:ℝ) by ring]
        rw [h8]
        calc |((x:ℝ) - (m:ℝ)) + (m:ℝ)| ≤ |((x:ℝ) - (m:ℝ))| + |(m:ℝ)| := abs_add_le _ _
          _ ≤ (N₀:ℝ) + |(m:ℝ)| := by linarith
          _ = |(m:ℝ)| + (N₀:ℝ) := by ring
      by_cases hx : (N₀:ℝ) ≤ |(x:ℝ)|
      · rw [max_eq_right (div_nonneg (by linarith) hM0.le)]
        rw [div_le_div_iff_of_pos_right hM0]
        linarith
      · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hM0.le)]
        exact div_nonneg (abs_nonneg _) hM0.le
    calc ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)), ‖w m‖
        ≤ ∑ m ∈ Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ)),
            winC / M * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M))) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          refine (hwp m).trans (mul_le_mul_of_nonneg_left ?_
            (div_nonneg (le_of_lt hwinC0) hM0.le))
          refine jbDecay_le_of_abs_le ?_
          rw [abs_of_nonneg (le_max_left (0:ℝ) _), abs_div, abs_of_pos hM0]
          exact h6 m hm
      _ = (Finset.Icc (x - (N₀:ℤ)) (x + (N₀:ℤ))).card
            • (winC / M * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)))) := Finset.sum_const _
      _ = G * (winC / M * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)))) := by
          rw [nsmul_eq_mul, hcard x]
      _ = G * (winC / M) * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M))) := by ring
  have hsum_maj : Summable (fun x : ℤ => (if L < |(x:ℝ)| then Af x else 0)) := by
    have h1 : Summable (fun x : ℤ =>
        jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M)))) :=
      summable_jbDecay_max (n := 12) le_rfl hM0 N₀
    have hmaj : ∀ x : ℤ, (if L < |(x:ℝ)| then Af x else 0)
        ≤ G * (winC / M) * jbDecay 12 (max 0 (((|(x:ℝ)| - (N₀:ℝ))/M))) := by
      intro x
      by_cases h : L < |(x:ℝ)|
      · rw [if_pos h]; exact hAf_maj x
      · rw [if_neg h]
        exact mul_nonneg (mul_nonneg hG0 (div_nonneg (le_of_lt hwinC0) hM0.le))
          (jbDecay_nonneg _ _)
    refine Summable.of_nonneg_of_le (fun x => ?_) hmaj (h1.mul_left (G * (winC / M)))
    by_cases h : L < |(x:ℝ)|
    · exact le_trans (hAn x) (le_of_eq (if_pos h).symm)
    · exact le_of_eq (if_neg h).symm
  -- (v) the lattice counting for the `ℓ¹` mass of the tail
  have hAsum : (∑' x : ℤ, (if L < |(x:ℝ)| then Af x else 0))
      ≤ G * (Kwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))) := by
    have h1 : (∑' x : ℤ, (if L < |(x:ℝ)| then Af x else 0))
        = ∑' x : ℤ, (if L < |(x:ℝ)| then
            ∑' m : ℤ, (if |(((x - m : ℤ)):ℝ)| ≤ (N₀:ℝ) then ‖w m‖ else 0) else 0) := by
      refine tsum_congr (fun x => ?_)
      by_cases h : L < |(x:ℝ)|
      · refine (if_pos h).trans ((tsum_congr (fun m => ?_)).trans (if_pos h).symm)
        rw [habs_cast x m]
      · exact (if_neg h).trans (if_neg h).symm
    rw [h1]
    have h2 := tsum_tail_fubini_own (fun m : ℤ => ‖w m‖)
      (fun m => norm_nonneg _) hwsum (N₀ := N₀) (L := L)
    refine h2.trans ?_
    calc (2 * (N₀:ℝ) + 1) * (∑' m : ℤ, (if L - (N₀:ℝ) < |((m:ℤ):ℝ)| then ‖w m‖ else 0))
        = G * (∑' m : ℤ, (if L - (N₀:ℝ) < |((m:ℤ):ℝ)| then ‖w m‖ else 0)) := by rw [← hGdef]
      _ ≤ G * (Kwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))) :=
          mul_le_mul_of_nonneg_left (hwt (L - (N₀:ℝ))) hG0
  -- (vi) the `ℓ²` tail
  have hmajF : ∀ x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0)
      ≤ min (G * winC / M) Cwin * (if L < |(x:ℝ)| then Af x else 0) := by
    intro x
    by_cases h : L < |(x:ℝ)|
    · have h1 : ‖F x‖ ^ 2 ≤ min (G * winC / M) Cwin * Af x := by
        calc ‖F x‖ ^ 2 ≤ Af x * Af x := by nlinarith [norm_nonneg (F x), hFA x]
          _ ≤ Af x * min (G * winC / M) Cwin := mul_le_mul_of_nonneg_left (hAmax x) (hAn x)
          _ = min (G * winC / M) Cwin * Af x := by ring
      rw [if_pos h, if_pos h]
      exact h1
    · have hAn2 : (0:ℝ) ≤ min (G * winC / M) Cwin * (if L < |(x:ℝ)| then Af x else 0) :=
        mul_nonneg (le_min (div_nonneg (by positivity) hM0.le) (le_of_lt hCwin0))
          (by by_cases hh : L < |(x:ℝ)|
              · exact le_trans (hAn x) (le_of_eq (if_pos hh).symm)
              · exact le_of_eq (if_neg hh).symm)
      calc (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0) = 0 := by rw [if_neg h]
        _ ≤ min (G * winC / M) Cwin * (if L < |(x:ℝ)| then Af x else 0) := by
            simpa using hAn2
  have hsumF : Summable (fun x : ℤ => (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun x => ?_) hmajF (hsum_maj.mul_left _)
    by_cases h : L < |(x:ℝ)|
    · exact le_trans (sq_nonneg ‖F x‖) (le_of_eq (if_pos h).symm)
    · exact le_of_eq (if_neg h).symm
  have htail : (∑' x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0))
      ≤ min (G * winC / M) Cwin * (∑' x : ℤ, (if L < |(x:ℝ)| then Af x else 0)) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hmajF hsumF (hsum_maj.mul_left _)
  -- (vii) combine
  have hLt : L * min (G * winC / M) Cwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))
      ≤ Kc * (N₀ + G) := by
    have hd := decay_arith M L (N₀:ℝ) G hM0 (by positivity) hG0
    by_cases hGM : G ≤ M
    · have hdiv : G / M ≤ 1 := by rw [div_le_one hM0]; exact hGM
      have hmin : min (G / M) 1 = G / M := min_eq_left hdiv
      have hb : min (G * winC / M) Cwin ≤ winC * (G / M) := by
        rw [show G * winC / M = winC * (G / M) by ring]
        exact min_le_left _ _
      rw [hmin] at hd
      calc L * min (G * winC / M) Cwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))
          ≤ L * (winC * (G / M)) * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hL0.le)
              (jbDecay_nonneg _ _)
        _ = winC * (L * (G / M) * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))) := by ring
        _ ≤ winC * (N₀ + G) := mul_le_mul_of_nonneg_left hd (le_of_lt hwinC0)
        _ ≤ Kc * (N₀ + G) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hdiv : 1 ≤ G / M := by rw [one_le_div hM0]; linarith
      have hmin : min (G / M) 1 = 1 := min_eq_right hdiv
      have hb : min (G * winC / M) Cwin ≤ Cwin := min_le_right _ _
      rw [hmin, mul_one] at hd
      calc L * min (G * winC / M) Cwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))
          ≤ L * Cwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hL0.le)
              (jbDecay_nonneg _ _)
        _ = Cwin * (L * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))) := by ring
        _ ≤ Cwin * (N₀ + G) := mul_le_mul_of_nonneg_left hd (le_of_lt hCwin0)
        _ ≤ Kc * (N₀ + G) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hNG : N₀ + G ≤ 2 * G := by rw [hGdef]; linarith
  have hfin : (∑' x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0))
      ≤ 2 * Kwin * Kc * G^2 / L := by
    have hB : (0:ℝ) ≤ min (G * winC / M) Cwin :=
      le_min (div_nonneg (by positivity) hM0.le) (le_of_lt hCwin0)
    have hstep : min (G * winC / M) Cwin
          * (∑' x : ℤ, (if L < |(x:ℝ)| then Af x else 0))
        ≤ min (G * winC / M) Cwin * (G * (Kwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M)))) :=
      mul_le_mul_of_nonneg_left hAsum hB
    refine (htail.trans hstep).trans ?_
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hid : min (G * winC / M) Cwin * (G * (Kwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))))
        = (G * Kwin / L) * (L * min (G * winC / M) Cwin
            * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M))) := by
      field_simp
    rw [hid]
    calc (G * Kwin / L) * (L * min (G * winC / M) Cwin * jbDecay 11 (max 0 ((L - (N₀:ℝ))/M)))
        ≤ (G * Kwin / L) * (Kc * (N₀ + G)) :=
          mul_le_mul_of_nonneg_left hLt (by positivity)
      _ ≤ (G * Kwin / L) * (Kc * (2 * G)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNG (le_of_lt hKc0)) (by positivity)
      _ = 2 * Kwin * Kc * G^2 / L := by ring
  -- (viii) arithmetic
  have hfinal : (∑' x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0))
      ≤ 18 * Kwin * Kc * A ^ 2 * R ^ (-(1:ℝ)) * e := by
    refine hfin.trans ?_
    have hRe : (0:ℝ) < R * e := by
      rw [he]
      exact mul_pos (by linarith) (pow_pos (by exact_mod_cast (by omega : 0 < N)) _)
    rw [hLdef, Real.rpow_neg_one, div_le_iff₀ hRe]
    calc 2 * Kwin * Kc * G^2
        ≤ 2 * Kwin * Kc * (9 * A^2 * e^2) := by
          refine mul_le_mul_of_nonneg_left hGsq (by positivity)
      _ = 18 * Kwin * Kc * A ^ 2 * R⁻¹ * e * (R * e) := by
          field_simp
          ring
  calc (∑' x : ℤ, (if L < |(x:ℝ)| then ‖F x‖ ^ 2 else 0))
      ≤ 18 * Kwin * Kc * A ^ 2 * R ^ (-(1:ℝ)) * e := hfinal
    _ = (Real.sqrt (18 * Kwin * Kc * A ^ 2)) ^ 2 * R ^ (-(1:ℝ)) * e := by
        rw [Real.sq_sqrt (by positivity)]
end Work.KMTAreas.A4Z
