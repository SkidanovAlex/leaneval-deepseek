import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.DLRepoint.Zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.DLRepoint.Assembly` — the two-arm assembly at the faithful energy

FS `thm:smallbox`'s proof is the group decomposition
`N = m·n′ + n″` (`n″ < n′`, `n′` in the group window `[C_n μs³,(C_n+1)μs³)`),
the *superadditivity* of the box ground energy
(`Work.KinPSuperadd.diagKinPeBAt_group_superadd`, PROVED at the faithful word),
the `m`-arm's per-group bound `MGroupInput` and the `n″`-arm's tight block
bound, followed by the pure arithmetic `Submission.BoseGases.exists_two_arm_split`
+ `two_arm_group_bound` (`Work/SmallBoxTwoArm.lean`, PROVED).

This module assembles them into `d4_dl_bound_of_groups`: the DL shape at the
faithful energy `Work.BlockBound4.diagWeBAt`, with `c = 1/18`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.DLRepoint

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The `m`-arm's per-group input** (FS's `eq:simpleaprioribog` chain): at a
group count `P` with density `u := P/s³ ≥ 2μ` (the group window), the faithful
box ground energy dominates the sharp per-group bound
`(1/9)(μ − u)²·∬w₁` with `∬w₁ ≥ 8π(a v)s³`.

This is the ONE genuine input that the tight block bound does NOT supply (see
the module doc of `Defs.lean`: at the group window the block bound subtracts
`(272π+40)μ²a s³Γ`, which dwarfs `(1/18)μu·8πa s³`).  It is FS's per-group
bound obtained from `lm:appinteractionestimate` + `eq:simpleaprioribog` +
`eq:wepsilong` — the *simple* (unrefined) Bogoliubov chain, whose error is
`Cμa·(n′/|B|)∫χ²` with no `Γ` factor and no `−½μ²∬w₁` subtraction. -/
def MGroupInput (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (c₀ cgap : ℝ) : Prop :=
  ∀ P : ℕ, 1 ≤ P → 2 * μ * s ^ 3 ≤ (P : ℝ) →
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap

/-- **The `m`-arm, in the linear shape FS's assembly consumes**: at a group
count `P` with `2μ ≤ u := P/s³`,

    (1/18)·μ·u·8π(a v)s³ ≤ e_B(P) .

(`(1/18)μu ≤ (1/9)(μ−u)²` for `u ≥ 2μ` — `Submission.BoseGases.two_arm_group_bound`.) -/
theorem m_arm_linear {s μ : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap : ℝ}
    (hM : MGroupInput s μ v h c₀ cgap) (hμ : 0 < μ) (hs : 0 < s) (hav : 0 ≤ a v)
    {P : ℕ} (hP1 : 1 ≤ P) (hP2 : 2 * μ * s ^ 3 ≤ (P : ℝ)) :
    (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := by
  have hs3 : 0 < s ^ 3 := by positivity
  have hu : 2 * μ ≤ (P : ℝ) / s ^ 3 := by
    rw [le_div_iff₀ hs3]
    linarith [hP2]
  have hgrp := Submission.BoseGases.two_arm_group_bound (μ := μ) (u := (P : ℝ) / s ^ 3) hμ hu
  have h8 : (0 : ℝ) ≤ 8 * π * (a v) * s ^ 3 := by
    have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) hav) (le_of_lt hs3)
  calc (1 / 18) * μ * ((P : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)
      = ((1 / 18) * μ * ((P : ℝ) / s ^ 3)) * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ (((1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2)) * (8 * π * (a v) * s ^ 3) :=
        mul_le_mul_of_nonneg_right hgrp h8
    _ = (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * π * (a v) * s ^ 3) := by ring
    _ ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap := hM P hP1 hP2


/-- **The two-arm assembly at the faithful energy** — FS's `thm:smallbox` bound
from the group decomposition, the superadditivity of the faithful ground energy,
the `m`-arm input `MGroupInput` and the tight block bound at the remainder
count.  `c = 1/18` (FS's `eq:simpleaprioribog`/`two_arm_gain` constant).

The hypotheses are exactly the ones the DL bundle supplies:

* `hM` — FS's *simple* per-group bound at the group window (`MGroupInput`);
* `hblk` — the tight **block** bound at every density-window count `P` with
  `P/s³ ≤ 9μ` (`d4_block_bound_at`, from the delivered
  `Work.BlockBound4.diagW_block_bound`);
* `hzero` — the empty box (`diagWeBAt_zero_nonneg`);
* the standing potential/regime data needed by the superadditivity
  (`Door4Superadd`). -/
theorem d4_dl_bound_of_groups {s μ R0 R K_B : ℝ} {v : ℝ³ → ℝ}
    {h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v} {c₀ cgap Cb : ℝ}
    (hs : 0 < s) (hμ : 0 < μ) (hμβ : 1 ≤ μ * s ^ 3) (hav : 0 ≤ a v)
    (hR0 : 0 < R0) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0s : R0 ≤ s * chiR0)
    (hR0R : R0 ≤ R)
    (hKB : 0 < K_B) (hCb : 0 ≤ Cb) (hcgap0 : 0 ≤ cgap)
    (hint : Work.BlockBound4.DiagWKinIntegrable s c₀)
    (hM : MGroupInput s μ v h c₀ cgap)
    (hblk : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      ((1 / 4 : ℝ) * ((P : ℝ) / s ^ 3 - μ) ^ 2 - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v - Cb * μ * (a v)
      ≤ Work.BlockBound4.diagWeBAt P s μ v h c₀ cgap)
    (hzero : 0 ≤ Work.BlockBound4.diagWeBAt 0 s μ v h c₀ cgap)
    (N : ℕ) :
    ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
        - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)
      - Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v
      - Cb * μ * (a v)
    ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap := by
  have hs3 : 0 < s ^ 3 := by positivity
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have h8 : (0 : ℝ) ≤ 8 * π * (a v) * s ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hπ) hav) (le_of_lt hs3)
  have hΓ : 0 ≤ d4GammaWith R s K_B μ v := by
    unfold d4GammaWith
    exact add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg (le_of_lt hKB) 3)
      (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg hav 3)) _))
  have hE1 : (0 : ℝ) ≤ Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCb (sq_nonneg μ)) hav)
      (le_of_lt hs3)) hΓ
  have hE2 : (0 : ℝ) ≤ Cb * μ * (a v) :=
    mul_nonneg (mul_nonneg hCb (le_of_lt hμ)) hav
  obtain ⟨m, n', n'', hN, _hlt, hwin1, hwin2, hdens⟩ :=
    Submission.BoseGases.exists_two_arm_split (μ := μ) (β := s ^ 3) hμ hs3 hμβ N
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- the `m = 0` arm: `n'' = N` and the single sharp group carries the bound
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
          * (8 * π * (a v) * s ^ 3)
        ≤ (1 / 4) * (((N : ℝ) / s ^ 3 - μ) ^ 2) * (8 * π * (a v) * s ^ 3) :=
      mul_le_mul_of_nonneg_right hdens' h8
    by_cases hN0 : N = 0
    · have hx0 : (N : ℝ) / s ^ 3 = 0 := by rw [hN0]; simp
      have hleft : ((1 / 18 : ℝ) * (((N : ℝ) / s ^ 3 - μ) ^ 2
              / (1 + ((N : ℝ) / s ^ 3) / μ)) - (1 / 2 : ℝ) * μ ^ 2)
            * (8 * π * (a v) * s ^ 3)
          - Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v - Cb * μ * (a v) ≤ 0 := by
        rw [hx0]
        have hmain : (0 : ℝ) ≤ - (((1 / 18 : ℝ) * ((0 - μ) ^ 2 / (1 + 0 / μ))
            - (1 / 2 : ℝ) * μ ^ 2) * (8 * π * (a v) * s ^ 3)) := by
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
        have h3 : (N : ℝ) / s ^ 3 < 3 * μ := by
          rw [div_lt_iff₀ hs3, ← hcast]
          linarith [hwin2]
        linarith [hμ]
      have hb := hblk N hN1 hwinN
      linarith [hdens8, hb]
  · -- the `m ≥ 1` arm: superadditivity, the `m` groups and the remainder group
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hn'1 : 1 ≤ n' := by
      have hpos : (0 : ℝ) < (n' : ℝ) := lt_of_lt_of_le (by positivity) hwin1
      exact_mod_cast hpos
    have hsa := Work.KinPSuperadd.diagKinPeBAt_group_superadd (m := m) (N' := n') (N'' := n'')
      hR0 hv_nonneg hvrad hv_memL1 hv_supp h hs hR0s hμ hcgap0 hint
    have hsaN : (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap
        + Work.BlockBound4.diagWeBAt n'' s μ v h c₀ cgap
        ≤ Work.BlockBound4.diagWeBAt N s μ v h c₀ cgap := by
      have hidx : m * n' + n'' = N := by omega
      rwa [hidx] at hsa
    have hcastN : (N : ℝ) = (m : ℝ) * (n' : ℝ) + (n'' : ℝ) := by
      rw [hN]; push_cast; ring
    have hlin := m_arm_linear (s := s) (μ := μ) (v := v) (h := h) (c₀ := c₀) (cgap := cgap)
      hM hμ hs hav hn'1 hwin1
    have hmm : (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3))
        ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap :=
      mul_le_mul_of_nonneg_left hlin (by positivity)
    have hsub : (N : ℝ) - (n'' : ℝ) = (m : ℝ) * (n' : ℝ) := by linarith [hcastN]
    have hdiv : ((N : ℝ) - (n'' : ℝ)) / s ^ 3 = (m : ℝ) * ((n' : ℝ) / s ^ 3) := by
      rw [hsub]; ring
    have hmTot : (1 / 18) * μ * (((N : ℝ) - (n'' : ℝ)) / s ^ 3) * (8 * π * (a v) * s ^ 3)
        ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap := by
      rw [hdiv]
      calc (1 / 18) * μ * ((m : ℝ) * ((n' : ℝ) / s ^ 3)) * (8 * π * (a v) * s ^ 3)
          = (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / s ^ 3) * (8 * π * (a v) * s ^ 3)) := by ring
        _ ≤ (m : ℝ) * Work.BlockBound4.diagWeBAt n' s μ v h c₀ cgap := hmm
    have hrest : ((1 / 4 : ℝ) * (((n'' : ℝ) / s ^ 3 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2)
          * (8 * π * (a v) * s ^ 3)
        - Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v - Cb * μ * (a v)
        ≤ Work.BlockBound4.diagWeBAt n'' s μ v h c₀ cgap := by
      rcases Nat.eq_zero_or_pos n'' with hn''0 | hn''pos
      · have hx : ((n'' : ℝ)) / s ^ 3 = 0 := by rw [hn''0]; simp
        rw [hx, hn''0]
        have hmain : ((1 / 4 : ℝ) * ((0 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2)
              * (8 * π * (a v) * s ^ 3)
            - Cb * μ ^ 2 * (a v) * s ^ 3 * d4GammaWith R s K_B μ v - Cb * μ * (a v) ≤ 0 := by
          have hsq : (1 / 4 : ℝ) * ((0 - μ) ^ 2) - (1 / 2 : ℝ) * μ ^ 2 ≤ 0 := by
            nlinarith [sq_nonneg μ]
          have hb := mul_le_mul_of_nonneg_right hsq h8
          linarith [hb, hE1, hE2]
        exact le_trans hmain hzero
      · have hwin'' : (n'' : ℝ) / s ^ 3 ≤ 9 * μ := by
          have h3 : (n'' : ℝ) / s ^ 3 < 3 * μ := by
            rw [div_lt_iff₀ hs3]; linarith [hwin2]
          linarith [hμ]
        exact hblk n'' hn''pos hwin''
    have hfinal : (1 / 18) * (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + ((N : ℝ) / s ^ 3) / μ))
          * (8 * π * (a v) * s ^ 3)
        ≤ (1 / 18) * μ * (((N : ℝ) - (n'' : ℝ)) / s ^ 3) * (8 * π * (a v) * s ^ 3)
          + (1 / 4) * (((n'' : ℝ) / s ^ 3 - μ) ^ 2) * (8 * π * (a v) * s ^ 3) := by
      have hd8 := mul_le_mul_of_nonneg_right hdens h8
      nlinarith [hd8]
    nlinarith [hfinal, hmTot, hrest, hsaN]

end Work.DLRepoint
