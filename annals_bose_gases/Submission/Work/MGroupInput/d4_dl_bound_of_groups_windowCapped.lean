import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.MGroupInput.exists_two_arm_split_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.d4_dl_bound_of_groups_windowCapped`

The two-arm assembly of FS's `thm:smallbox` at the faithful energy
`Work.BlockBound4.diagWeBAt`, with a CAPPED group window.

This is `Work.MGroupInput.d4_dl_bound_of_groups_window` with the `m`-arm input
weakened from the uncapped `MGroupLinear Cn` to the capped
`MGroupLinearCapped Cn Cn'`: the assembly applies its `m`-arm slot at the single
group count `n'` of `exists_two_arm_split_gen`, which is trapped in
`[Cn μ s^3, (Cn+1) μ s^3] ⊆ [Cn μ s^3, Cn' μ s^3]` as soon as `Cn + 1 ≤ Cn'`,
so the cap is free where the slot is used, while `Cn' ≤ 9` (together with
`Cn + 1 ≤ Cn'`) keeps every count in the assembly inside the tight block window
`P/s^3 ≤ 9μ` on which `hblk` is available.
-/

open scoped Real

set_option maxHeartbeats 4000000

namespace Work.MGroupInput

theorem d4_dl_bound_of_groups_windowCapped {s μ R0 R K_B : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v}
    {c₀ cgap Cb Cn Cn' : ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hμβ : 1 ≤ μ * s ^ 3) (hav : 0 ≤ BoseGases.a v)
    (hR0 : 0 < R0) (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hR0s : R0 ≤ s * Submission.BoseGases.chiR0) (hR0R : R0 ≤ R)
    (hKB : 0 < K_B) (hCb : 0 ≤ Cb) (hcgap0 : 0 ≤ cgap)
    (hint : Work.BlockBound4.DiagWKinIntegrable s c₀)
    (hCn : 2 ≤ Cn) (hCnCn' : Cn + 1 ≤ Cn') (hCn9 : Cn' ≤ 9)
    (hM : Work.MGroupInput.MGroupLinearCapped Cn Cn' s μ v h c₀ cgap)
    (hblk : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
        - Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - Cb * μ * (BoseGases.a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap)
    (hzero : 0 ≤ Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap)
    (N : ℕ) :
    ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
        - (1 / 2 : ℝ) * μ ^ 2) * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
      - Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
      - Cb * μ * (BoseGases.a v)
    ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap := by
  have hCn9' : Cn + 1 ≤ 9 := le_trans hCnCn' hCn9
  have hs3 : 0 < s ^ 3 := by positivity
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have h8 : (0 : ℝ) ≤ 8 * π * (BoseGases.a v) * s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) hav) (le_of_lt hs3)
  have hΓ : 0 ≤ Work.DLRepoint.d4GammaWith R s K_B μ v := by
    unfold Work.DLRepoint.d4GammaWith
    exact add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3)
      (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg hav 3)) _))
  have hE1 : (0 : ℝ) ≤ Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3
      * Work.DLRepoint.d4GammaWith R s K_B μ v :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCb (sq_nonneg μ)) hav)
      (le_of_lt hs3)) hΓ
  have hE2 : (0 : ℝ) ≤ Cb * μ * (BoseGases.a v) :=
    mul_nonneg (mul_nonneg hCb (le_of_lt hμ)) hav
  obtain ⟨m, n', n'', hN, _hlt, hwin1, hwin2, hwin3, hdens⟩ :=
    exists_two_arm_split_gen (μ := μ) (β := s ^ 3) hμ hs3 hμβ
      (Cn := Cn) hCn N
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- the `m = 0` arm: `n″ = N`, already inside the tight block window
    have hn''N : n'' = N := by rw [hN, hm0]; simp
    have hcast : (n'' : ℝ) = (N : ℝ) := by rw [hn''N]
    have hdens' : (1 / 18) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
        ≤ (1 / 4) * (((N : ℝ) / s ^ 3 - μ) ^ 2) := by
      have hthis := hdens
      rw [hcast] at hthis
      have hz : (1 / 18) * μ * (((N : ℝ) - (N : ℝ)) / s ^ 3) = 0 := by ring
      rw [hz, add_zero] at hthis
      exact hthis
    have hdens8 : (1 / 18) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
          * (8 * π * (BoseGases.a v) * s ^ 3)
        ≤ (1 / 4) * (((N : ℝ) / s ^ 3 - μ) ^ 2) * (8 * π * (BoseGases.a v) * s ^ 3) :=
      mul_le_mul_of_nonneg_right hdens' h8
    by_cases hN0 : N = 0
    · have hx0 : (N : ℝ) / s ^ 3 = 0 := by rw [hN0]; simp
      have hleft : ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2
              / (1 + ((N : ℝ) / s ^ 3) / μ)) - (1 / 2 : ℝ) * μ ^ 2)
            * (8 * π * (BoseGases.a v) * s ^ 3)
          - Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
          - Cb * μ * (BoseGases.a v) ≤ 0 := by
        rw [hx0]
        have hmain : (0 : ℝ) ≤ - (((1 / 18 : ℝ) * ((0 - μ) ^ 2 / (1 + 0 / μ))
            - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (BoseGases.a v) * s ^ 3)) := by
          have hb : ((1 / 18 : ℝ) * ((0 - μ) ^ 2 / (1 + 0 / μ)) - (1 / 2 : ℝ) * μ ^ 2) ≤ 0 := by
            rw [zero_div, add_zero, div_one]
            nlinarith [sq_nonneg μ]
          have := mul_le_mul_of_nonneg_right hb h8
          linarith
        linarith [hmain, hE1, hE2]
      have hz : Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap
          = Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap := by rw [hN0]
      rw [hz]
      linarith [hleft, hzero]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
      have hwinN : (N : ℝ) / s ^ 3 ≤ 9 * μ := by
        have h3 : (N : ℝ) / s ^ 3 < 9 * μ := by
          rw [div_lt_iff₀ hs3]
          have hle : (Cn + 1) * μ * s ^ 3 ≤ 9 * μ * s ^ 3 := by
            have h1 : (Cn + 1) * μ ≤ 9 * μ := by nlinarith [hCn9', hμ]
            exact mul_le_mul_of_nonneg_right h1 (le_of_lt hs3)
          rw [← hcast]
          linarith [hwin3, hle]
        exact le_of_lt h3
      have hb := hblk N hN1 hwinN
      linarith [hdens8, hb]
  · -- the `m ≥ 1` arm: superadditivity, `m` groups of `n′` and the remainder
    have hCnpos : 0 < Cn := by linarith [hCn]
    have hApos : (0 : ℝ) < Cn * μ * s ^ 3 := by positivity
    have hn'1 : 1 ≤ n' := by
      have hpos : (0 : ℝ) < (n' : ℝ) := lt_of_lt_of_le hApos hwin1
      have hne : n' ≠ 0 := by
        intro h; rw [h] at hpos; simp at hpos
      exact Nat.one_le_iff_ne_zero.mpr hne
    have hsa := Work.KinPSuperadd.diagKinPeBAt_group_superadd (m := m) (N' := n') (N'' := n'')
      hR0 hv_nonneg hvrad hv_memL1 hv_supp h hs hR0s hμ hcgap0 hint
    have hsaN : (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap
        + Work.BlockBound4.diagWeBAt n'' s μ v h c₀ cgap
        ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap := by
      have hidx : m * n' + n'' = N := by omega
      rwa [hidx] at hsa
    have hcastN : (N : ℝ) = (m : ℝ) * (n' : ℝ) + (n'' : ℝ) := by
      rw [hN]; push_cast; ring
    have hcapn' : (n' : ℝ) ≤ Cn' * μ * s ^ 3 := by
      have h1 : (Cn + 1) * μ * s ^ 3 ≤ Cn' * μ * s ^ 3 := by
        have h2 : (Cn + 1) * μ ≤ Cn' * μ := mul_le_mul_of_nonneg_right hCnCn' (le_of_lt hμ)
        exact mul_le_mul_of_nonneg_right h2 (le_of_lt hs3)
      linarith [hwin2, h1]
    have hlin : (1 / 18) * μ * ((n' : ℝ) / s ^ 3) * (8 * π * (BoseGases.a v) * s ^ 3)
        ≤ Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap := hM n' hn'1 hwin1 hcapn'
    have hmm : (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / s ^ 3) * (8 * π * (BoseGases.a v) * s ^ 3))
        ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap :=
      mul_le_mul_of_nonneg_left hlin (by positivity)
    have hsub : (N : ℝ) - (n'' : ℝ) = (m : ℝ) * (n' : ℝ) := by linarith [hcastN]
    have hdiv : ((N : ℝ) - (n'' : ℝ)) / s ^ 3 = (m : ℝ) * ((n' : ℝ) / s ^ 3) := by
      rw [hsub]; ring
    have hmTot : (1 / 18) * μ * (((N : ℝ) - (n'' : ℝ)) / s ^ 3)
          * (8 * π * (BoseGases.a v) * s ^ 3)
        ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap := by
      rw [hdiv]
      calc (1 / 18) * μ * ((m : ℝ) * ((n' : ℝ) / s ^ 3)) * (8 * π * (BoseGases.a v) * s ^ 3)
          = (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / s ^ 3) * (8 * π * (BoseGases.a v) * s ^ 3)) := by
            ring
        _ ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap := hmm
    have hrest : ((1 / 4 : ℝ) * (((n'' : ℝ) / s ^ 3 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (BoseGases.a v) * s ^ 3)
        - Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
        - Cb * μ * (BoseGases.a v)
        ≤ Work.BlockBound4.diagWeBAt n'' s μ v h c₀ cgap := by
      rcases Nat.eq_zero_or_pos n'' with hn''0 | hn''pos
      · have hx : ((n'' : ℝ)) / s ^ 3 = 0 := by rw [hn''0]; simp
        rw [hx, hn''0]
        have hmain : ((1 / 4 : ℝ) * ((0 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2)
              * (8 * π * (BoseGases.a v) * s ^ 3)
            - Cb * μ ^ 2 * (BoseGases.a v) * s ^ 3 * Work.DLRepoint.d4GammaWith R s K_B μ v
            - Cb * μ * (BoseGases.a v) ≤ 0 := by
          have hsq : (1 / 4 : ℝ) * ((0 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2 ≤ 0 := by
            nlinarith [sq_nonneg μ]
          have hb := mul_le_mul_of_nonneg_right hsq h8
          linarith [hb, hE1, hE2]
        exact le_trans hmain hzero
      · have hwin'' : (n'' : ℝ) / s ^ 3 ≤ 9 * μ := by
          have h3 : (n'' : ℝ) / s ^ 3 < 9 * μ := by
            rw [div_lt_iff₀ hs3]
            have hle : (Cn + 1) * μ * s ^ 3 ≤ 9 * μ * s ^ 3 := by
              have h1 : (Cn + 1) * μ ≤ 9 * μ := by nlinarith [hCn9', hμ]
              exact mul_le_mul_of_nonneg_right h1 (le_of_lt hs3)
            linarith [hwin3, hle]
          exact le_of_lt h3
        exact hblk n'' hn''pos hwin''
    have hfinal : (1 / 18) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
          * (8 * π * (BoseGases.a v) * s ^ 3)
        ≤ (1 / 18) * μ * (((N : ℝ) - (n'' : ℝ)) / s ^ 3) * (8 * π * (BoseGases.a v) * s ^ 3)
          + (1 / 4) * (((n'' : ℝ) / s ^ 3 - μ) ^ 2) * (8 * π * (BoseGases.a v) * s ^ 3) := by
      have hd8 := mul_le_mul_of_nonneg_right hdens h8
      nlinarith [hd8]
    nlinarith [hfinal, hmTot, hrest, hsaN]

end Work.MGroupInput

