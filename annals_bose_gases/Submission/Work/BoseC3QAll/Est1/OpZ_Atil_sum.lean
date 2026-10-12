import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.Defs
import Submission.Work.BoseC3QAll.NWindow_ta_sum
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.q3Denom_le_four
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.OpZ_Atil_sum`

The `θ`-mode window bound for the combination `Ã_s = ã_s + β_{sk}ã_{-s}†`
(`β_{sk} = α_kα_{s-k}`) that the shift `Y_k = (z/ℓ³)Σ_s γ_{sk}b_{s-k}†Ã_s`
carries: for every mode `k ∈ P_H`, every `v` in FS's window
`T.NWindow (𝓜+1) v` and every `Q3KernelFSAll`,

  `Σ_{s∈excited} f_L(s)q3Denom(s,k)‖Ã_s v‖² ≤ 16(𝓜 + 1 + K₀(K_ℓK_L)³)‖v‖²`.

The proof is the naive one:
* `f_L ≤ 1` drops the `f_L`, `q3Denom ≤ 4` drops the denominators
  (`q3Denom_le_four`), costing a factor `4`;
* `‖x + c•y‖² ≤ 2‖x‖² + 2c²‖y‖²` costs a factor `2`;
* `|α_q| ≤ 1` (from `|ℬ_q| ≤ 𝒜_q`, the `Q3KernelFSAll.AB` field) makes `|β| ≤ 1`,
  so no `β`-weight is needed;
* the remaining sums `Σ_{s∈S}‖ã_s v‖²` and `Σ_{s∈S}‖ã_{-s}† v‖²` are the
  window moments: the first is `≤ 𝓜‖v‖²`, the second is
  `Σ‖ã_{-s}v‖² + |S|‖v‖² ≤ 𝓜‖v‖² + |S|‖v‖²` because `[ã_s,ã_s†] = 1` — the
  `+1` per mode is paid by `Q3KernelFSAll.count_PL` (`|S| ≤ K₀(K_ℓK_L)³`);
* the total `16(𝓜+1) + 8|S| ≤ 16(𝓜+1+K₀(K_ℓK_L)³)` is the claimed shape.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll.Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. `|α| ≤ 1` from FS's cruder smallness `|ℬ| ≤ 𝒜` -/

/-- `|α(𝒜,ℬ)| ≤ 1` whenever `|ℬ| ≤ 𝒜`.

`α = ℬ/(𝒜+√(𝒜²-ℬ²))` and `𝒜 + √(𝒜²-ℬ²) ≥ 𝒜 ≥ |ℬ|` (the case `𝒜 = 0`
forces `ℬ = 0` and `α = 0`). -/
theorem abs_alphaCoef_le_one {A B : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A) :
    |Work.BoseB7.alphaCoef A B| ≤ 1 := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- `A = 0` forces `B = 0`
    have hB0 : B = 0 := by
      have h : |B| = 0 := le_antisymm (hA0 ▸ hB) (abs_nonneg B)
      exact abs_eq_zero.mp h
    rw [hB0, ← hA0]
    norm_num [Work.BoseB7.alphaCoef, Submission.BoseGases.bogAlpha,
      Submission.BoseGases.bogS]
  · have hs : 0 ≤ Submission.BoseGases.bogS A B := Submission.BoseGases.bogS_nonneg A B
    have hden : 0 < A + Submission.BoseGases.bogS A B := by linarith
    have hBA : |B| ≤ A + Submission.BoseGases.bogS A B := by linarith
    rw [Work.BoseB7.alphaCoef, Submission.BoseGases.bogAlpha, abs_div, abs_of_pos hden]
    calc |B| / (A + Submission.BoseGases.bogS A B)
        ≤ (A + Submission.BoseGases.bogS A B) / (A + Submission.BoseGases.bogS A B) :=
          div_le_div_of_nonneg_right hBA hden.le
      _ = 1 := div_self (ne_of_gt hden)

/-- `|α_k| ≤ 1` for every mode `k` (no momentum region needed): only
`|ℬ_k| ≤ 𝒜_k` (FS's `eq:BoverA` in its crudest form) is used. -/
theorem abs_alpha_le_one (E : Q3Env Mode) (hAB : ∀ k, |E.B k| ≤ E.A k) (k : Mode) :
    |E.alpha k| ≤ 1 :=
  abs_alphaCoef_le_one (le_trans (abs_nonneg (E.B k)) (hAB k)) (hAB k)

/-! ## 2. The `Ã`-norm bound -/

/-- `‖ã_s v + c·ã_{-s}†v‖² ≤ 2‖ã_s v‖² + 2c²‖ã_{-s}†v‖²` (Cauchy–Schwarz/AM–GM
in the Fock form, valid for every real `c`). -/
theorem Atil_normSq_le (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (s k : Mode) (v : F.H) :
    F.normSq (Atil F T E s k v)
      ≤ 2 * F.normSq (T.ta s v) + 2 * (bA E s k) ^ 2 * F.normSq (T.taDag (-s) v) := by
  have hAtil : Atil F T E s k v = T.ta s v + (bA E s k) • T.taDag (-s) v := by
    simp only [Atil, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hAtil]
  simp only [Work.BoseB7.FockData.normSq]
  set β := bA E s k
  set x := T.ta s v
  set y := T.taDag (-s) v
  have hxx : 0 ≤ F.bp x x := F.bp_nonneg x
  have hyy : 0 ≤ F.bp y y := F.bp_nonneg y
  have hexp : F.bp (x + β • y) (x + β • y)
      = F.bp x x + 2 * β * F.bp x y + β ^ 2 * F.bp y y := by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [F.bp_symm y x]
    ring
  rw [hexp]
  have hcs := Work.BoseB7.bp_cauchy_abs F x y
  have h1 : 2 * β * F.bp x y ≤ F.bp x x + β ^ 2 * F.bp y y := by
    have h2 : β * F.bp x y ≤ |β| * (Real.sqrt (F.bp x x) * Real.sqrt (F.bp y y)) := by
      calc β * F.bp x y ≤ |β * F.bp x y| := le_abs_self _
        _ = |β| * |F.bp x y| := abs_mul _ _
        _ ≤ |β| * (Real.sqrt (F.bp x x) * Real.sqrt (F.bp y y)) :=
            mul_le_mul_of_nonneg_left hcs (abs_nonneg β)
    have h2' : 2 * (β * F.bp x y)
        ≤ 2 * (|β| * (Real.sqrt (F.bp x x) * Real.sqrt (F.bp y y))) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h3 : 2 * (|β| * (Real.sqrt (F.bp x x) * Real.sqrt (F.bp y y)))
        ≤ F.bp x x + β ^ 2 * F.bp y y := by
      have hsq := sq_nonneg (Real.sqrt (F.bp x x) - |β| * Real.sqrt (F.bp y y))
      rw [sub_sq, mul_pow, sq_abs, Real.sq_sqrt hxx, Real.sq_sqrt hyy] at hsq
      nlinarith [hsq]
    linarith [h2', h3]
  nlinarith [h1]

/-! ## 3. The window moment of `ã†` -/

/-- `Σ_{s∈S}‖ã_{-s}†Ψ‖² ≤ 𝓜‖Ψ‖² + |S|‖Ψ‖²` for a window state
`Ψ ∈ Ran 1_{[0,𝓜]}(n₊)`: the exact identity `‖ã_s†Ψ‖² = ‖ã_sΨ‖² + ‖Ψ‖²`
(`[ã_s,ã_s†] = 1`) plus `NWindow_ta_sum`. -/
theorem NWindow_taDag_neg_sum (F : FockData Mode) (T : TildeData F) {M : ℝ} (hM : 0 ≤ M)
    {Ψ : F.H} (hΨ : T.NWindow M Ψ) (S : Finset Mode) (hS : ∀ s ∈ S, s ≠ 0) :
    ∑ s ∈ S, F.normSq (T.taDag (-s) Ψ) ≤ M * F.normSq Ψ + (S.card : ℝ) * F.normSq Ψ := by
  have hterm : ∀ s ∈ S, F.normSq (T.taDag (-s) Ψ)
      = F.normSq (T.ta (-s) Ψ) + F.normSq Ψ := by
    intro s hs
    have hs' : -s ≠ 0 := neg_ne_zero.mpr (hS s hs)
    have h1 : F.bp (T.taDag (-s) Ψ) (T.taDag (-s) Ψ)
        = F.bp Ψ (T.ta (-s) (T.taDag (-s) Ψ)) :=
      T.taDag_adjoint (-s) Ψ (T.taDag (-s) Ψ)
    have h2 : T.ta (-s) (T.taDag (-s) Ψ) = T.taDag (-s) (T.ta (-s) Ψ) + Ψ := by
      have hccr := T.ta_ccr (-s) (-s) hs' hs'
      have h := congrArg (fun (L : F.H →ₗ[ℝ] F.H) => L Ψ) hccr
      rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
      rw [if_pos (rfl : -s = -s), one_smul, Module.End.one_apply] at h
      exact h
    simp only [Work.BoseB7.FockData.normSq, h1, h2, map_add]
    rw [F.bp_symm Ψ (T.taDag (-s) (T.ta (-s) Ψ)),
      T.taDag_adjoint (-s) (T.ta (-s) Ψ) Ψ]
  calc ∑ s ∈ S, F.normSq (T.taDag (-s) Ψ)
      = ∑ s ∈ S, (F.normSq (T.ta (-s) Ψ) + F.normSq Ψ) := Finset.sum_congr rfl hterm
    _ = (∑ s ∈ S, F.normSq (T.ta (-s) Ψ)) + (S.card : ℝ) * F.normSq Ψ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * F.normSq Ψ + (S.card : ℝ) * F.normSq Ψ := by
        have hsum : ∑ s ∈ S, F.normSq (T.ta (-s) Ψ) ≤ M * F.normSq Ψ := by
          have himg : ∑ s ∈ S, F.normSq (T.ta (-s) Ψ)
              = ∑ t ∈ S.image (fun s => -s), F.normSq (T.ta t Ψ) := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact neg_injective hab
          rw [himg]
          have hS' : ∀ t ∈ S.image (fun s => -s), t ≠ 0 := by
            intro t ht
            obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
            exact neg_ne_zero.mpr (hS s hs)
          have hwin := NWindow_ta_sum F T hM hΨ (S.image (fun s => -s)) hS'
          simpa only [Work.BoseB7.FockData.normSq] using hwin
        linarith

/-! ## 4. The target -/

theorem OpZ_Atil_sum (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ (k : Mode), k ∈ F.PHset E → E.W1 k ≠ 0 → ∀ (v : F.H), T.NWindow (E.bigM + 1) v →
          ∑ s ∈ Work.BoseB7.excited Mode, E.fL s * E.q3Denom s k * F.normSq (Work.BoseC3QAll.Est1.Atil F T E s k v)
            ≤ 16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) * F.normSq v := by
  obtain ⟨t₁, ht₁, hq3⟩ := q3Denom_le_four K₀ b₀ hb₀
  refine ⟨t₁, ht₁, ?_⟩
  intro Mode _ _ _ F T E hv htle hb hK k hk hW v hwin
  -- the support of `f_L` inside the excited modes
  set S : Finset Mode := (Work.BoseB7.excited Mode).filter (fun s => E.fL s ≠ 0) with hSdef
  have hmemS : ∀ s ∈ S, s ∈ Work.BoseB7.excited Mode ∧ E.fL s ≠ 0 := by
    intro s hs
    rw [hSdef] at hs
    exact Finset.mem_filter.mp hs
  have hne : ∀ s ∈ S, s ≠ 0 := by
    intro s hs
    have h1 := (hmemS s hs).1
    rw [Work.BoseB7.excited, Finset.mem_erase] at h1
    exact h1.1
  have hq3le : ∀ s ∈ S, E.q3Denom s k ≤ 4 := fun s hs =>
    hq3 F T E hv htle hb hK s k (hmemS s hs).2 hk hW
  -- the termwise bound
  have hterm : ∀ s ∈ S, E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v)
      ≤ 8 * F.normSq (T.ta s v) + 8 * F.normSq (T.taDag (-s) v) := by
    intro s hs
    have hfLnn : 0 ≤ E.fL s := hK.fL_nonneg s
    have hfLle : E.fL s ≤ 1 := hK.fL_le_one s
    have hq : E.q3Denom s k ≤ 4 := hq3le s hs
    have hqden : E.fL s * E.q3Denom s k ≤ 4 := by
      have h1 : E.fL s * E.q3Denom s k ≤ E.fL s * 4 :=
        mul_le_mul_of_nonneg_left hq hfLnn
      have h2 : E.fL s * 4 ≤ 1 * 4 := mul_le_mul_of_nonneg_right hfLle (by norm_num)
      linarith
    have hnn : 0 ≤ F.normSq (Atil F T E s k v) := F.bp_nonneg _
    have hstep1 : E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v)
        ≤ 4 * F.normSq (Atil F T E s k v) := mul_le_mul_of_nonneg_right hqden hnn
    have hAtil := Atil_normSq_le F T E s k v
    have hbA : |bA E s k| ≤ 1 := by
      have hαk : |E.alpha k| ≤ 1 := abs_alpha_le_one E hK.AB k
      have hαsk : |E.alpha (s - k)| ≤ 1 := abs_alpha_le_one E hK.AB (s - k)
      rw [bA, abs_mul]
      calc |E.alpha k| * |E.alpha (s - k)| ≤ 1 * 1 :=
            mul_le_mul hαk hαsk (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hβ : (bA E s k) ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) hbA
    have hstep2 : 4 * F.normSq (Atil F T E s k v)
        ≤ 8 * F.normSq (T.ta s v) + 8 * F.normSq (T.taDag (-s) v) := by
      have h1 : 4 * F.normSq (Atil F T E s k v)
          ≤ 4 * (2 * F.normSq (T.ta s v)
              + 2 * (bA E s k) ^ 2 * F.normSq (T.taDag (-s) v)) :=
        mul_le_mul_of_nonneg_left hAtil (by norm_num)
      have hy : 0 ≤ F.normSq (T.taDag (-s) v) := F.bp_nonneg _
      nlinarith [h1, hβ, hy]
    linarith [hstep1, hstep2]
  -- restrict the sum to the support of `f_L`
  have hsum_eq : ∑ s ∈ Work.BoseB7.excited Mode,
        E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v)
      = ∑ s ∈ S, E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v) := by
    rw [hSdef]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro s hs hnot
    have hfl : E.fL s = 0 := by
      by_contra hcon
      exact hnot (Finset.mem_filter.mpr ⟨hs, hcon⟩)
    simp [hfl]
  have hsum_le : ∑ s ∈ S, E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v)
      ≤ 8 * (∑ s ∈ S, F.normSq (T.ta s v))
        + 8 * (∑ s ∈ S, F.normSq (T.taDag (-s) v)) := by
    have h := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
    exact h
  -- the window moments
  have hMnn : 0 ≤ E.bigM + 1 := by linarith [hv.one_le_bigM]
  have hA1 : ∑ s ∈ S, F.normSq (T.ta s v) ≤ (E.bigM + 1) * F.normSq v := by
    simpa only [Work.BoseB7.FockData.normSq] using
      NWindow_ta_sum F T hMnn hwin S hne
  have hB1 : ∑ s ∈ S, F.normSq (T.taDag (-s) v)
      ≤ (E.bigM + 1) * F.normSq v + (S.card : ℝ) * F.normSq v :=
    NWindow_taDag_neg_sum F T hMnn hwin S hne
  -- the count of low modes
  have hcard : (S.card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3 := by
    rw [hSdef]; exact hK.count_PL
  have hK0 : 0 ≤ K₀ * (E.Kl * E.KL) ^ 3 := le_trans (Nat.cast_nonneg S.card) hcard
  have hnorm : 0 ≤ F.normSq v := F.bp_nonneg v
  calc ∑ s ∈ Work.BoseB7.excited Mode,
        E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v)
      = ∑ s ∈ S, E.fL s * E.q3Denom s k * F.normSq (Atil F T E s k v) := hsum_eq
    _ ≤ 8 * (∑ s ∈ S, F.normSq (T.ta s v))
          + 8 * (∑ s ∈ S, F.normSq (T.taDag (-s) v)) := hsum_le
    _ ≤ 8 * ((E.bigM + 1) * F.normSq v)
          + 8 * ((E.bigM + 1) * F.normSq v + (S.card : ℝ) * F.normSq v) := by
        have h1 := mul_le_mul_of_nonneg_left hA1 (by norm_num : (0 : ℝ) ≤ 8)
        have h2 := mul_le_mul_of_nonneg_left hB1 (by norm_num : (0 : ℝ) ≤ 8)
        linarith
    _ ≤ 16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) * F.normSq v := by
        have heq : 8 * ((E.bigM + 1) * F.normSq v)
              + 8 * ((E.bigM + 1) * F.normSq v + (S.card : ℝ) * F.normSq v)
            = (16 * (E.bigM + 1) + 8 * (S.card : ℝ)) * F.normSq v := by ring
        rw [heq]
        have h3 : 8 * (S.card : ℝ) ≤ 8 * (K₀ * (E.Kl * E.KL) ^ 3) :=
          mul_le_mul_of_nonneg_left hcard (by norm_num)
        have h2 : 16 * (E.bigM + 1) + 8 * (S.card : ℝ)
            ≤ 16 * (E.bigM + 1 + K₀ * (E.Kl * E.KL) ^ 3) := by
          nlinarith [h3, hK0]
        exact mul_le_mul_of_nonneg_right h2 hnorm

end Work.BoseC3QAll.Est1
