/-
# Area A4Z: the spatial fringe bound for the reproducing window `win`

Let `win M γ m = M⁻¹ ψ(m/M) e(mγ)` be the normalized reproducing window of Proposition `lip-2`
(`Work.KMTAreas.A4.lip2Kernel`), `ψ = lipSchPsi = 𝓕⁻ lipSchChi`.  This module proves

  `lip2FringeWin`,

the **free-window spatial fringe estimate** needed in the second half of §5.2 of
Krause--Mirek--Tao: for `g : ℤ → ℂ` with `‖g‖_∞ ≤ 1`, supported in `[-N₀, N₀]` with
`N₀ ≤ A N^d` (`d = deg P`, `A ≥ 1`), every `M ≥ 1` and every modulation `s`,

  `∑_{|x| > A N^d} ‖(win M s * g) x‖ ≤ C · M`,

with a constant `C` depending only on `ψ` (hence only on the paper's cut-off) --- *not* on `A`,
`N`, `N₀`, `g`, `M` or `s`.  The point is the *shape* of the bound: the mass of the smoothing of
a `1`-bounded finitely supported function outside the support window is at most a constant times
the *width* `M` of the smoothing window, uniformly in everything else.  (A constant bound in place
of `C · M` is false: the fringe of the smoothing of a dense window by a window of width `M` is of
order `M`.)

## The proof

The convolution is estimated pointwise in `x` by the absolutely convergent series
`∑_m ‖win M γ m‖ ‖g (x-m)‖ ≤ ∑_{|x-m| ≤ N₀} ‖win M γ m‖`, so for a finite set `u` of fringe
points

  `∑_{x∈u} ‖(win M γ * g) x‖ ≤ ∑'_m ‖win M γ m‖ · #{x ∈ u : |x| > A N^d, |x-m| ≤ N₀}`

(the finite `x`-sum is interchanged with the `m`-tsum by `Summable.tsum_finsetSum`), and the count
is bounded by `|m| + 1` in `fringeCount_aux`.  The resulting weighted lattice sum
`∑_m ‖win M γ m‖ (|m|+1) ≤ C M` is the *first moment* of the window, proved in
`winWeightedTsumLe_aux` from the two weighted lattice-sum bounds
`∑_u ε⟨εu⟩^{-12}|u| ≤ 2^61/ε` (`lipWeightAbsMomentLattice`) and `ε∑_u ⟨εu⟩^{-12} ≤ 2^61`
(`eps_tsum_jbDecay_twelve_int_le`) at `ε = M⁻¹`.

The outer `tsum` over the fringe is handled by `Real.tsum_le_of_sum_le`, so no summability of the
(possibly non-summable) fringe series is needed.

Both auxiliary estimates are proved below (as `private` lemmas, so that they do not collide with
the standalone modules `A4Z/winWeightedTsumLe` and `A4Z/fringeCount_le`, which state the same
facts).
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Kernel
import Submission.Work.KMTAreas.A4.lipWeightAbsMomentLattice
import Submission.Work.KMTAreas.A4.summable_tsum_eps_jbDecay_weighted_shift
import Submission.Work.KMTAreas.A4.shellLeWindow

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4Z

open Work.Analysis.InverseTheory

/-! ## The two auxiliary estimates -/

private theorem fringeCount_aux (g : ℤ → ℂ) {N₀ : ℕ} {W : ℝ} (hN₀W : (N₀ : ℝ) ≤ W)
    (hg1 : ∀ y : ℤ, ‖g y‖ ≤ 1) (hgs : SupportIn g N₀) (m : ℤ) :
    (∑' y : ℤ, (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0)) ≤ |(m : ℝ)| + 1 := by
  have hfl : (N₀ : ℤ) ≤ ⌊W⌋ := Int.le_floor.mpr hN₀W
  have hfl0 : 0 ≤ ⌊W⌋ := le_trans (by positivity) hfl
  set D : ℕ := (⌊W⌋).toNat with hD
  have hDcastZ : ((D : ℕ) : ℤ) = ⌊W⌋ := by rw [hD]; exact Int.toNat_of_nonneg hfl0
  have hDcastR : ((D : ℕ) : ℝ) = (⌊W⌋ : ℝ) := by
    rw [← Int.cast_natCast, hDcastZ]
  have hN₀D : N₀ ≤ D := by
    have h : (N₀ : ℤ) ≤ (D : ℤ) := by rw [hDcastZ]; exact hfl
    exact_mod_cast h
  set N' : ℕ := D - N₀ with hN'
  have hN'cast : ((N' : ℕ) : ℤ) = (D : ℤ) - (N₀ : ℤ) := by
    rw [hN']; exact Int.natCast_sub hN₀D
  have hqN' : (1 : ℤ) * (N' : ℤ) ≤ (D : ℤ) := by rw [hN'cast]; omega
  have hsupp : ∀ y : ℤ, g y ≠ 0 →
      -((D : ℤ)) + (↑(1 : ℕ) : ℤ) * (N' : ℤ) ≤ y ∧ y ≤ (D : ℤ) - (↑(1 : ℕ) : ℤ) * (N' : ℤ) := by
    intro y hy
    have hmem := SupportIn.mem_Icc hgs hy
    rw [Finset.mem_Icc] at hmem
    simp only [Nat.cast_one, one_mul, hN'cast]
    exact ⟨by omega, by omega⟩
  have hshell := Work.KMTAreas.A4.shellLeWindow (G := g) (D := D) (q := 1) (N' := N') (m := m)
    hqN' hsupp hg1
  have hcast : ∀ y : ℤ,
      ((((y + (↑(1 : ℕ) : ℤ) * m).natAbs : ℕ)) : ℝ) = |(y : ℝ) + (m : ℝ)| := by
    intro y
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    push_cast
    ring_nf
  have hcond : ∀ y : ℤ,
      (D < (y + (↑(1 : ℕ) : ℤ) * m).natAbs) ↔ W < |(y : ℝ) + (m : ℝ)| := by
    intro y
    constructor
    · intro h
      have h1 : ((D : ℕ) : ℝ) + 1 ≤ (((y + (↑(1 : ℕ) : ℤ) * m).natAbs : ℕ) : ℝ) := by
        have h2 : (D : ℕ) + 1 ≤ (y + (↑(1 : ℕ) : ℤ) * m).natAbs := Nat.lt_iff_add_one_le.mp h
        exact_mod_cast h2
      rw [hDcastR, hcast y] at h1
      have h3 : W < (⌊W⌋ : ℝ) + 1 := Int.lt_floor_add_one W
      linarith
    · intro h
      rw [← hcast y] at h
      have h1 : ((D : ℕ) : ℝ) < (((y + (↑(1 : ℕ) : ℤ) * m).natAbs : ℕ) : ℝ) := by
        rw [hDcastR]
        exact lt_of_le_of_lt (Int.floor_le W) h
      exact (Nat.cast_lt (α := ℝ)).mp h1
  refine le_trans (le_of_eq ?_) (le_trans hshell ?_)
  · exact tsum_congr (fun y => if_congr (hcond y).symm rfl rfl)
  · rw [Nat.cast_one, one_mul]
    have hle : max 0 (|(m : ℝ)| - (N' : ℝ)) ≤ |(m : ℝ)| :=
      max_le (by positivity)
        (by have hN'0 : (0 : ℝ) ≤ (N' : ℝ) := Nat.cast_nonneg N'; linarith)
    linarith


private theorem winWeightedTsumLe_aux : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 1 ≤ M →
    ∀ (γ : FreqCircle),
      Summable (fun m : ℤ => ‖Work.KMTAreas.A4.win M γ m‖ * (|((m : ℤ) : ℝ)| + 1)) ∧
      (∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * (|((m : ℤ) : ℝ)| + 1)) ≤ C * M := by
  set A₀ : ℝ := (2 : ℝ) ^ 12 * (schwartzSeminormSum Work.KMTAreas.A4.lipSchPsi + 1) with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]; have := schwartzSeminormSum_nonneg Work.KMTAreas.A4.lipSchPsi; positivity
  refine ⟨A₀ * 2 ^ 62, by positivity, ?_⟩
  intro M hM γ
  have hMpos : 0 < M := by linarith
  have hε0 : 0 < M⁻¹ := inv_pos.mpr hMpos
  have hε1 : M⁻¹ ≤ 1 := (inv_le_one₀ hMpos).mpr hM
  have hwin : ∀ m : ℤ,
      ‖Work.KMTAreas.A4.win M γ m‖ = M⁻¹ * ‖(Work.KMTAreas.A4.lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖ := by
    intro m
    rw [Work.KMTAreas.A4.norm_win M hMpos γ m, div_eq_inv_mul]
  have hpt : ∀ m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * (|((m : ℤ) : ℝ)| + 1) ≤
      A₀ * (M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|
        + M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))) := by
    intro m
    have h1 : ‖(Work.KMTAreas.A4.lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖
        ≤ A₀ * jbDecay 12 (M⁻¹ * (m : ℝ)) := by
      rw [hA₀]; exact schwartz_decay Work.KMTAreas.A4.lipSchPsi _
    rw [hwin m]
    have h2 : M⁻¹ * ‖(Work.KMTAreas.A4.lipSchPsi : ℝ → ℂ) (M⁻¹ * (m : ℝ))‖ * (|((m : ℤ) : ℝ)| + 1)
        ≤ M⁻¹ * (A₀ * jbDecay 12 (M⁻¹ * (m : ℝ))) * (|((m : ℤ) : ℝ)| + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hε0.le) (by positivity)
    refine h2.trans (le_of_eq ?_)
    ring
  have hsumm1 : Summable (fun m : ℤ => M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|) :=
    (Work.KMTAreas.A4.summable_tsum_eps_jbDecay_weighted_shift hε0 0).1.congr (fun m => by simp)
  have hsumm2 : Summable (fun m : ℤ => M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))) :=
    ((summable_jbDecay_twelve_shift hε0 0).mul_left M⁻¹).congr (fun m => by simp)
  have hsummDom : Summable (fun m : ℤ => A₀ * (M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))
      * |((m : ℤ) : ℝ)| + M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)))) :=
    (hsumm1.add hsumm2).mul_left A₀
  have hsumm : Summable (fun m : ℤ => ‖Work.KMTAreas.A4.win M γ m‖ * (|((m : ℤ) : ℝ)| + 1)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hpt hsummDom
  refine ⟨hsumm, ?_⟩
  have hle := Summable.tsum_le_tsum hpt hsumm hsummDom
  have hb1 : (∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|)
      ≤ (2 : ℝ) ^ 61 * M := by
    have h := Work.KMTAreas.A4.lipWeightAbsMomentLattice (ε := M⁻¹) hε0 hε1
    rwa [div_inv_eq_mul] at h
  have hb2 : (∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))) ≤ (2 : ℝ) ^ 61 := by
    have h := Work.KMTAreas.A4.eps_tsum_jbDecay_twelve_int_le (ε := M⁻¹) hε0 hε1
    rwa [← tsum_mul_left] at h
  have hdom : (∑' m : ℤ, A₀ * (M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|
        + M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))))
      = A₀ * ((∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|)
        + (∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)))) := by
    rw [tsum_mul_left, Summable.tsum_add hsumm1 hsumm2]
  calc ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * (|((m : ℤ) : ℝ)| + 1)
      ≤ ∑' m : ℤ, A₀ * (M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|
          + M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ))) := hle
    _ = A₀ * ((∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)) * |((m : ℤ) : ℝ)|)
          + (∑' m : ℤ, M⁻¹ * jbDecay 12 (M⁻¹ * (m : ℝ)))) := hdom
    _ ≤ A₀ * ((2 : ℝ) ^ 61 * M + (2 : ℝ) ^ 61) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hA₀pos.le
    _ ≤ A₀ * 2 ^ 62 * M := by
        have h3 : (2 : ℝ) ^ 61 * M + (2 : ℝ) ^ 61 ≤ (2 : ℝ) ^ 62 * M := by
          have h4 : (2 : ℝ) ^ 62 = (2 : ℝ) ^ 61 * 2 := by norm_num
          rw [h4]
          nlinarith [hM]
        calc A₀ * ((2 : ℝ) ^ 61 * M + (2 : ℝ) ^ 61) ≤ A₀ * ((2 : ℝ) ^ 62 * M) :=
              mul_le_mul_of_nonneg_left h3 hA₀pos.le
          _ = A₀ * 2 ^ 62 * M := by ring

/-! ## The fringe estimate -/

theorem lip2FringeWin (P : Polynomial ℤ) : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (A : ℝ), 1 ≤ A → ∀ (N₀ : ℕ), (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree → ∀ (g : ℤ → ℂ), (∀ x : ℤ, ‖g x‖ ≤ 1) → Work.Analysis.InverseTheory.SupportIn g N₀ → ∀ (M : ℝ), 1 ≤ M → ∀ (s : ℝ), ∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖(star (fun x : ℤ => ∑' m : ℤ, Work.KMTAreas.A4.win M (((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle)) m * g (x - m))) x‖ else 0) ≤ C * M := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := winWeightedTsumLe_aux
  refine ⟨2 * C₁ + 1, by positivity, ?_⟩
  intro N hN A hA N₀ hN₀le g hg1 hgs M hM s
  set W : ℝ := A * (N : ℝ) ^ P.natDegree with hW
  set γ : Work.Analysis.InverseTheory.FreqCircle := ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle) with hγ
  have hNd : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree :=
    one_le_pow₀ (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
  have hWge : 1 ≤ W := by rw [hW]; nlinarith
  have hmul : ∀ (c : ℝ) (z : ℂ), 0 ≤ c → ‖z‖ ≤ 1 → c * ‖z‖ ≤ c := by
    intro c z hc hz
    calc c * ‖z‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hz hc
      _ = c := mul_one c
  have hstar : (∑' x : ℤ, (if W < |(x : ℝ)| then
        ‖(star (fun x : ℤ => ∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m))) x‖ else 0))
      = ∑' x : ℤ, (if W < |(x : ℝ)| then
        ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖ else 0) := by
    refine tsum_congr fun x => ?_
    rw [Pi.star_apply, norm_star]
  rw [hstar]
  have hwsum : Summable (fun m : ℤ => ‖Work.KMTAreas.A4.win M γ m‖) :=
    Work.KMTAreas.A4.win_summable M hM γ
  have hpt : ∀ x : ℤ, ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖
      ≤ ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ := by
    intro x
    have hsumm : Summable (fun m : ℤ => ‖Work.KMTAreas.A4.win M γ m * g (x - m)‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => by rw [norm_mul]; exact hmul _ _ (norm_nonneg _) (hg1 (x - m))) hwsum
    calc ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖
        ≤ ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m * g (x - m)‖ := norm_tsum_le_tsum_norm hsumm
      _ = ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ :=
          tsum_congr fun m => norm_mul _ _
  refine Real.tsum_le_of_sum_le
    (f := fun x : ℤ => if W < |(x : ℝ)| then
      ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖ else 0) (fun x => ?_) (fun u => ?_)
  · dsimp only
    split_ifs with h
    · exact norm_nonneg _
    · exact le_refl 0
  · have h1 : ∑ x ∈ u, (if W < |(x : ℝ)| then
          ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖ else 0)
        ≤ ∑ x ∈ u, (if W < |(x : ℝ)| then
          ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) := by
      refine Finset.sum_le_sum (fun x _ => ?_)
      by_cases hx : W < |(x : ℝ)|
      · rw [if_pos hx, if_pos hx]; exact hpt x
      · rw [if_neg hx, if_neg hx]
    have h2 : ∀ x : ℤ, (if W < |(x : ℝ)| then
          ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0)
        = ∑' m : ℤ, (if W < |(x : ℝ)| then
          ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) := by
      intro x
      by_cases hx : W < |(x : ℝ)| <;> simp [hx]
    have h3 : ∑ x ∈ u, ∑' m : ℤ, (if W < |(x : ℝ)| then
          ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0)
        = ∑' m : ℤ, ∑ x ∈ u, (if W < |(x : ℝ)| then
          ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) :=
      (Summable.tsum_finsetSum (f := fun (x : ℤ) (m : ℤ) =>
          (if W < |(x : ℝ)| then ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0))
        (fun x _ => by
          by_cases hx : W < |(x : ℝ)|
          · simpa [hx] using Summable.of_nonneg_of_le (fun m => by positivity)
              (fun m => hmul _ _ (norm_nonneg _) (hg1 (x - m))) hwsum
          · simpa [hx] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ))))).symm
    have h4 : ∑' m : ℤ, ∑ x ∈ u, (if W < |(x : ℝ)| then
          ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0)
        = ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ *
            ∑ x ∈ u, (if W < |(x : ℝ)| then ‖g (x - m)‖ else 0) := by
      refine tsum_congr fun m => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by by_cases hx : W < |(x : ℝ)| <;> simp [hx])
    have h5 : ∀ m : ℤ, ∑ x ∈ u, (if W < |(x : ℝ)| then ‖g (x - m)‖ else 0)
        ≤ |(m : ℝ)| + 1 := by
      intro m
      have hreindex : ∑ x ∈ u, (if W < |(x : ℝ)| then ‖g (x - m)‖ else 0)
          = ∑ y ∈ u.image (fun x : ℤ => x - m),
              (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0) := by
        rw [Finset.sum_image (f := fun y : ℤ => (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0))
          (g := fun x : ℤ => x - m) (s := u) (fun x _ y _ h => by simpa using h)]
        exact Finset.sum_congr rfl (fun x _ => by
          have h1 : (((x - m : ℤ)) : ℝ) + (m : ℝ) = ((x : ℝ)) := by push_cast; ring
          rw [h1])
      have hFsumm : Summable (fun y : ℤ => (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0)) := by
        refine summable_of_ne_finset_zero (s := Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ)) (fun y hy => ?_)
        have hgy : g y = 0 := by
          by_contra hgz
          exact hy (SupportIn.mem_Icc hgs hgz)
        by_cases hWy : W < |(y : ℝ) + (m : ℝ)| <;> simp [hgy, hWy]
      calc ∑ x ∈ u, (if W < |(x : ℝ)| then ‖g (x - m)‖ else 0)
          = ∑ y ∈ u.image (fun x : ℤ => x - m),
              (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0) := hreindex
        _ ≤ ∑' y : ℤ, (if W < |(y : ℝ) + (m : ℝ)| then ‖g y‖ else 0) :=
            Summable.sum_le_tsum _ (fun y _ => by split_ifs <;> positivity) hFsumm
        _ ≤ |(m : ℝ)| + 1 := fringeCount_aux g hN₀le hg1 hgs m
    calc ∑ x ∈ u, (if W < |(x : ℝ)| then
          ‖∑' m : ℤ, Work.KMTAreas.A4.win M γ m * g (x - m)‖ else 0)
        ≤ ∑ x ∈ u, (if W < |(x : ℝ)| then
            ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) := h1
      _ = ∑ x ∈ u, ∑' m : ℤ, (if W < |(x : ℝ)| then
            ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) :=
            Finset.sum_congr rfl (fun x _ => h2 x)
      _ = ∑' m : ℤ, ∑ x ∈ u, (if W < |(x : ℝ)| then
            ‖Work.KMTAreas.A4.win M γ m‖ * ‖g (x - m)‖ else 0) := h3
      _ = ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ *
            ∑ x ∈ u, (if W < |(x : ℝ)| then ‖g (x - m)‖ else 0) := h4
      _ ≤ ∑' m : ℤ, ‖Work.KMTAreas.A4.win M γ m‖ * (|(m : ℝ)| + 1) := by
          refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hC₁ M hM γ).1
          · exact mul_le_mul_of_nonneg_left (h5 m) (norm_nonneg _)
          · refine Summable.of_nonneg_of_le (fun m => ?_)
              (fun m => mul_le_mul_of_nonneg_left (h5 m) (norm_nonneg _)) (hC₁ M hM γ).1
            positivity
      _ ≤ C₁ * M := (hC₁ M hM γ).2
      _ ≤ (2 * C₁ + 1) * M := by nlinarith [hM, hC₁pos]

end Work.KMTAreas.A4Z
