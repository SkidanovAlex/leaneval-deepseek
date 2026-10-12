import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.Est1.ComZb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.ComZ` — the analysis of the `χ̂²` half

This module proves the inequalities of the `χ̂²` half `Est1.estT2sum_comZ`
(FS `eq:EstimT2comm`): the split of `T2ComF` (`Est1.t2com_split`) is bounded by
the `Ã`-form `FA` (`Est1.FA`) plus the two errors (`wc`-deviation and the
`χ̂(s-k)χ̂(s'-k)` term), and `FA` is compared with `⟨G Φ⟩` and the two moments
`⟨n₊⟩`, `‖Φ‖²`.

## Contents

* `two_abs_bp_le` — AM–GM for the Fock form.
* `sum_excited_neg` — the reindexing `s ↦ -s` on the excited modes.
* `sum_fL_le_NPL` — `Σ_{s}f_L(s) ≤ NPL`.
* `TA_le_N` — `TA ≤ ⟨n₊⟩`.
* `TB_le` — `TB ≤ TA + NPL·‖Φ‖²`.
* `AbsA0_le` — `Σ f_Lf_L'|⟨Ã_s,Ã_{s'}⟩| ≤ NPL·Σ f_L‖Ã_s‖²`.
* `sum_hatChiSq_shift` — `Σ_{s'}|χ̂²(s'-s)| ≤ K₀+1`.
* `sum_Atil_sq_le` — `Σ f_L‖Ã_{s,k}Φ‖² ≤ 2TA + 2β²TB`.
* `FA_PSD`, `FA_le_Q` — positivity of `FA` and the comparison with `⟨G Φ⟩`.
* `rawY_bound` — the `χ̂(s-k)χ̂(s'-k)` error.
-/

noncomputable section
open scoped BigOperators
namespace Work.BoseC3QAll
namespace Est1
open Work.BoseB7
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
/-- **`FA ≤ ⟨G Φ⟩ + C_b(⟨n₊⟩ + N_PL‖Φ‖²)`** at the parameter point. -/
theorem FA_le_Q (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∀ (k : Mode) (Φ : F.H), k ∈ F.PHset E → E.W1 k ≠ 0 →
          FA F T E k Φ ≤ F.qw Φ (T.Gop E)
            + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
  obtain ⟨t₁, ht₁, h₁⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := lille_threshold K₀
  refine ⟨min (min t₁ t₂) t₃, lt_min (lt_min ht₁ ht₂) ht₃, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK k Φ hk hW
  have hle₁ : hv.t ≤ t₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle₂ : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans hle (min_le_right _ _)
  obtain ⟨hPHq, hsubq, -⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨-, -, -, hαle, -⟩ := h₂ F T E hv hle₂ hb hK
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hlil : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have h96 : 96 * max K₀ 0 * E.lille ≤ 1 := h₃ E hv hle₃
  have hbm : ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E := by
    intro s hfs
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHq k hkPH
    have hqsk : F.PHq E.KH E.aScat (s - k) := hsubq s k hfs hk hW
    have h1 := hαle k hqk
    have h2 := hαle (s - k) hqsk
    rw [bA, abs_mul]
    have hmax : K₀ ≤ max K₀ 0 := le_max_left _ _
    have h3 : K₀ * E.lille ≤ max K₀ 0 * E.lille := mul_le_mul_of_nonneg_right hmax hlil
    have h4 : (64 * K₀ * E.lille) * (64 * K₀ * E.lille) ≤ (2 ^ 12 : ℝ) * K₀ ^ 2 * E.lille ^ 2 := by
      have h5 : 64 * K₀ * E.lille ≤ 2 / 3 := by nlinarith
      have h6 : 0 ≤ 64 * K₀ * E.lille := by positivity
      nlinarith
    calc |E.alpha k| * |E.alpha (s - k)| ≤ (64 * K₀ * E.lille) * (64 * K₀ * E.lille) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (2 ^ 12 : ℝ) * K₀ ^ 2 * E.lille ^ 2 := h4
      _ = bm K₀ E := by rw [bm]
  have hmain := FA_sub_Q_le hK k Φ hK0 hbm
  have hTA := TA_le_N (K₀ := K₀) hK Φ
  have hTB := TB_le (K₀ := K₀) hK Φ
  have hTB0 : 0 ≤ TB F T E Φ := Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
  have hTA0 : 0 ≤ TA F T E Φ := Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
  have hNPL0 : 0 ≤ NPL E := NPL_nonneg E
  have hNAP0 : 0 ≤ F.bp (T.N Φ) Φ := T.N_nonneg Φ
  have hNS0 : 0 ≤ F.normSq Φ := F.bp_nonneg _
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hK0
  have hcb : cbeta K₀ E = (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2) := rfl
  have hK1 : 0 ≤ K₀ + 1 := by linarith
  have hfin : 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ)
      ≤ cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
    rw [hcb]
    have h1 : TA F T E Φ + TB F T E Φ ≤ 2 * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
      nlinarith [hTA, hTB, hNPL0, hNS0, hNAP0]
    have h2 : 0 ≤ bm K₀ E + bm K₀ E ^ 2 := by nlinarith [sq_nonneg (bm K₀ E), hbm0]
    have h3 : 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * 2
        ≤ (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2) := by nlinarith [hK1, hbm0]
    calc 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ)
        ≤ 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2)
            * (2 * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) :=
          mul_le_mul_of_nonneg_left h1 (by nlinarith [hK1, hbm0])
      _ = (2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * 2)
            * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by ring
      _ ≤ ((K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2))
            * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) :=
          mul_le_mul_of_nonneg_right h3 (by nlinarith [hNAP0, hNPL0, hNS0])
  linarith [hmain, hfin]

end Est1

end Work.BoseC3QAll
