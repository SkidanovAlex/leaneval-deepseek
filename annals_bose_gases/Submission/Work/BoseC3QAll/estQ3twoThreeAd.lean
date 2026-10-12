import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseC3QAll.estQ3twoThreeAc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.estQ3twoThreeA` — FS `eq:EstimateQ3Tilde2+3` (`Q₃⁽²⁾ + Q₃⁽³⁾`)

The estimate of FS §10 controlling the second and third pieces of the
Bogoliubov-split cubic word `Q₃⁽²⁾ + Q₃⁽³⁾` by the kinetic reserve
`(𝓁²/2)∫_{P_H^q}𝒟_k b_k†b_k` on the quarter region `P_H^q`:

```
−C·e23A·‖Φ‖²  ≤  ⟨Φ, (Q₃⁽²⁾ + Q₃⁽³⁾ + (𝓁²/2)·dNumOpR P_H^q) Φ⟩   (Φ ∈ NWindow 𝓜).
```

## The two words and the commutator

With `p = -k`, `q = s − k` (for `Q₃⁽²⁾`) and `p = k − s`, `q = k` (for
`Q₃⁽³⁾`), each of the four monomials is of the form

`ã_s† b_p† b_q`  resp.  `b_q† b_p ã_s`,

and moving `ã_s†` (`ã_s`) past `b_p†` (`b_p`) costs a **scalar** commutator
(`taDag_bOpDag_swap`, `bOp_ta_swap`):

`[ã_s†, b_p†] = [b_p, ã_s] = −α_p·ccrX(s,−p) • 1`.

Hence the *pair* `ã_s†b_p†b_q + b_q†b_pã_s` has the quadratic form

`2⟨ã_s(b_pΦ), b_qΦ⟩ + 2σ_{sp}⟨b_qΦ, Φ⟩`,   `σ_{sp} = −α_p·ccrX(s,−p)`,

the first term an off-diagonal pairing of `ã_s(b_pΦ)` with `b_qΦ` (both factors
carrying the low/high momentum split), the second the "constant" part.

## The two absorptions

* The pairing term is bounded by `ε‖ã_s(b_pΦ)‖² + ε⁻¹‖b_qΦ‖²` (`bp_cauchy`).
  Summed over `s` with `ε = (𝓜+1)^{-1/2}` the first half is
  `√(𝓜+1)Σ_q‖b_qΦ‖²` (`NWindow_ta_sum`, the window of `b_pΦ` being `𝓜+1`) and
  the second half costs the *number* `N_f ≤ K₀(K_ℓK_L)³` of modes in the
  support of `f_L` (`Q3KernelFSAll.count_PL`, `k ↦ s−k` injective into `P_H^q`);
  both are absorbed by the reserve, whose weight is `𝒟_q ≥ 1/(64K_H²a²)` on
  `P_H^q` (`kernel_basic`).  This is `absorb_errA`'s first two conjuncts.
* The constant part is dominated by the *sum* `Σ_{k∈P_H}|Ŵ₁(k)α_k|`: by
  `|α_k| ≤ 2ρ|Ŵ₁(k)|/‖k‖²` on `P_H^q` and `sum_W1sq` this is at most
  `2ρK₀aℓ³` (`sum_W1alpha_le`), so the whole constant part is at most
  `C ρ a ℓ³ (K_ℓK_L)³ (|z|/ℓ³)𝓁η` — exactly `e23A` up to the factor `𝓁`
  (`absorb_errA`'s third conjunct).

Everything is asserted with one absolute constant `C` depending only on `K₀`.
-/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace Work.BoseC3QAll
open Work.BoseB7
variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
theorem estQ3twoThreeA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Work.BoseC3QAll.EstQ3twoThreeA K₀ b₀ hb₀ := by
  classical
  have hCpos : 0 < CtwoThree K₀ := CtwoThree_pos K₀
  have hC2 : (2 : ℝ) ≤ CtwoThree K₀ := CtwoThree_ge_two K₀
  have hcinv_pos : 0 < 1 / CtwoThree K₀ := by positivity
  by_cases hK0 : 0 ≤ K₀
  · obtain ⟨tAbs, htAbs, hAbsE⟩ := absorb_errA K₀ b₀ hb₀ hK0 (1 / CtwoThree K₀) hcinv_pos
    obtain ⟨tW, htW, hWE⟩ := sum_W1alpha_le K₀ hK0
    obtain ⟨tDen, htDen, hDenE⟩ := q3Denom_le_four K₀ b₀ hb₀
    obtain ⟨tWs, htWs, hWsubE⟩ := sum_W1alpha_sub_le K₀ b₀ hb₀ hK0
    obtain ⟨tK, htK, hbas⟩ := kernel_basic K₀ b₀ hb₀
    obtain ⟨tP, htP, hPs⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
    obtain ⟨tS, htS, hSm⟩ := smallness_ratios K₀ b₀ hb₀ (1 / CtwoThree K₀) hcinv_pos
    obtain ⟨tE, htE, hEt⟩ := eta_mul_le K₀ b₀ hb₀ (1 / CtwoThree K₀) hcinv_pos
    refine ⟨CtwoThree K₀,
      min tWs (min tW (min tAbs (min tDen (min tS (min tE (min tK tP)))))), le_of_lt hCpos, ?_, ?_⟩
    · exact lt_min htWs (lt_min htW (lt_min htAbs (lt_min htDen (lt_min htS (lt_min htE (lt_min htK htP))))))
    · intro Mode instA instF instD F T E hv htle hb hK Φ hΦ
      -- ===================== thresholds =====================
      have hTWs : hv.t ≤ tWs := le_trans htle (min_le_left _ _)
      have h00 : hv.t ≤ min tW (min tAbs (min tDen (min tS (min tE (min tK tP))))) :=
        le_trans htle (min_le_right _ _)
      have hTW : hv.t ≤ tW := le_trans h00 (min_le_left _ _)
      have h1 : hv.t ≤ min tAbs (min tDen (min tS (min tE (min tK tP)))) :=
        le_trans h00 (min_le_right _ _)
      have hTabs : hv.t ≤ tAbs := le_trans h1 (min_le_left _ _)
      have h2 : hv.t ≤ min tDen (min tS (min tE (min tK tP))) := le_trans h1 (min_le_right _ _)
      have hTden : hv.t ≤ tDen := le_trans h2 (min_le_left _ _)
      have h3 : hv.t ≤ min tS (min tE (min tK tP)) := le_trans h2 (min_le_right _ _)
      have hTs : hv.t ≤ tS := le_trans h3 (min_le_left _ _)
      have h4 : hv.t ≤ min tE (min tK tP) := le_trans h3 (min_le_right _ _)
      have hTe : hv.t ≤ tE := le_trans h4 (min_le_left _ _)
      have h5 : hv.t ≤ min tK tP := le_trans h4 (min_le_right _ _)
      have hTk : hv.t ≤ tK := le_trans h5 (min_le_left _ _)
      have hTp : hv.t ≤ tP := le_trans h5 (min_le_right _ _)
      -- ===================== scalars =====================
      have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
      have ha : 0 < E.aScat := hv.a_pos
      have hKH : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
      have hKl : 0 < E.Kl := lt_of_lt_of_le one_pos hv.one_le_Kl
      have hKL : 0 < E.KL := lt_of_lt_of_le one_pos hv.one_le_KL
      have hbigM1 : (1 : ℝ) ≤ E.bigM := hv.one_le_bigM
      have hbigM : (0 : ℝ) ≤ E.bigM := Work.BoseB7.bigM_nonneg E hv
      have hlille_nn : (0 : ℝ) ≤ E.lille := by
        rw [Work.BoseB7.lille_val E hv]
        exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
      have hlille_pos : 0 < E.KH ^ 2 := by positivity
      have hmu : 0 < E.mu := Work.BoseB7.mu_pos E hv
      have hrho_nn : 0 ≤ E.rho := (Work.BoseB7.rho_pos E hv).le
      have hη_nn : 0 ≤ eta E := by
        rw [eta]
        exact Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hKl.le _) hlille_nn) _
      have hzsq : E.z ^ 2 = E.rho * E.ell ^ 3 := Work.BoseB7.zsq_eq E hv
      have hzabs : |E.z| = Real.sqrt (E.rho * E.ell ^ 3) := by
        rw [← hzsq, Real.sqrt_sq_eq_abs]
      have hMx : 0 < E.bigM + 1 := by linarith
      -- ===================== kernel facts =====================
      obtain ⟨hαeven, hAB, hHalf, hαle, hDq⟩ := hbas F T E hv hTk hb hK
      obtain ⟨hPHsub, hsubPHq, _hRHi⟩ := hPs F T E hv hTp hb hK
      have hDen4 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E → E.W1 k ≠ 0 →
          E.q3Denom s k ≤ 4 :=
        hDenE F T E hv hTden hb hK
      have hW1sum : ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤
          2 * E.rho * E.aScat * K₀ * E.ell ^ 3 := hWE F T E hv hTW hK
      obtain ⟨hSm1, hSm2, hSm3, hSm4, hSm5, hSm6, hSm7, hSm8, hSm9⟩ := hSm E hv hTs hb
      obtain ⟨hηle, hη2le, hη3le, hη4le⟩ := hEt E hv hTe hb
      obtain ⟨hAbs1, hAbs2, hAbs3⟩ := hAbsE E hv hTabs hb
      -- ===================== the window =====================
      have hnonzero : ∀ s ∈ excited Mode, s ≠ 0 := fun s hs => by
        rw [Work.BoseB7.excited, Finset.mem_erase] at hs
        exact hs.1
      have hbOpWin : ∀ k : Mode, T.NWindow (E.bigM + 1) (F.bOp E.alpha k Φ) := fun k =>
        (NWindow_shift F T E hbigM hΦ 0 k).2.2.2.2.2.2.1
      have hWin : ∀ Ψ : F.H, T.NWindow (E.bigM + 1) Ψ →
          ∑ s ∈ excited Mode, F.bp (T.ta s Ψ) (T.ta s Ψ) ≤ (E.bigM + 1) * F.normSq Ψ :=
        fun Ψ hΨ => NWindow_ta_sum F T (by linarith : (0 : ℝ) ≤ E.bigM + 1) hΨ
          (excited Mode) hnonzero
      -- ===================== abbreviations =====================
      set ε : ℝ := (Real.sqrt (E.bigM + 1))⁻¹ with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      have hεmul : ε * (E.bigM + 1) = Real.sqrt (E.bigM + 1) := by
        rw [hεdef, inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hMx))]
        have hsq := Real.sq_sqrt hMx.le
        rw [sq] at hsq
        exact hsq.symm
      have hεinv : ε⁻¹ = Real.sqrt (E.bigM + 1) := by rw [hεdef, inv_inv]
      set Wc : ℝ := 256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille with hWcdef
      set Sσ : ℝ := 64 * K₀ ^ 2 * E.lille * eta E with hSσdef
      set Sf : Finset Mode := (excited Mode).filter (fun s => E.fL s ≠ 0) with hSfdef
      set Sq : Finset Mode := (excited Mode).filter (F.PHq E.KH E.aScat) with hSqdef
      set Nf : ℝ := (Sf.card : ℝ) with hNfdef
      set Tq : ℝ := ∑ q ∈ Sq, F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ) with hTqdef
      set B2 : Mode → Mode → ℝ :=
        fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))
        with hB2def
      set B3 : Mode → Mode → ℝ :=
        fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k))
        with hB3def
      set c2 : Mode → Mode → ℝ := fun s k => -(E.alpha k * T.ccrX s k) with hc2def
      set c3 : Mode → Mode → ℝ := fun s k => -(E.alpha (s - k) * T.ccrX s (s - k)) with hc3def
      set u2 : Mode → Mode → F.H := fun s k => T.ta s (F.bOp E.alpha (-k) Φ) with hu2def
      set v2 : Mode → Mode → F.H := fun s k => F.bOp E.alpha (s - k) Φ with hv2def
      have hv2val : ∀ s k, v2 s k = F.bOp E.alpha (s - k) Φ := by
        intro s k; rw [hv2def]
      set u3 : Mode → Mode → F.H := fun s k => T.ta s (F.bOp E.alpha (k - s) Φ) with hu3def
      set v3 : Mode → Mode → F.H := fun s k => F.bOp E.alpha k Φ with hv3def
      have hv3val : ∀ s k, v3 s k = F.bOp E.alpha k Φ := by
        intro s k; rw [hv3def]

      refine twoThree_core K₀ F T E Φ
        (256 * (|E.z| / E.ell ^ 3) * K₀ ^ 2 * E.aScat * E.lille)
        (64 * K₀ ^ 2 * E.lille * eta E)
        ((Real.sqrt (E.bigM + 1))⁻¹)
        (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
        (∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          F.bp (F.bOp E.alpha q Φ) (F.bOp E.alpha q Φ))
        ((excited Mode).filter (fun s => E.fL s ≠ 0))
        ((excited Mode).filter (F.PHq E.KH E.aScat))
        (fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)))
        (fun s k => (E.z / E.ell ^ 3) * (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)))
        (fun s k => -(E.alpha k * T.ccrX s k))
        (fun s k => -(E.alpha (s - k) * T.ccrX s (s - k)))
        (fun s k => T.ta s (F.bOp E.alpha (-k) Φ))
        (fun s k => F.bOp E.alpha (s - k) Φ)
        (fun s k => T.ta s (F.bOp E.alpha (k - s) Φ))
        (fun s k => F.bOp E.alpha k Φ)
        rfl rfl rfl
        (by
          have hsq := Real.sq_sqrt hMx.le
          rw [sq] at hsq
          rw [inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hMx))]
          exact hsq.symm)
        (by rw [inv_inv])
        rfl rfl rfl rfl
        (fun s k => rfl) (fun s k => rfl) (fun s k => rfl) (fun s k => rfl)
        (fun s k => rfl) (fun s k => rfl) (fun s k => rfl) (fun s k => rfl)
        hαeven hPHsub hsubPHq hHalf hαle hDq hDen4
        (fun k => hK.W1_le k) (fun s => hK.fL_nonneg s) (fun s => hK.fL_le_one s)
        (fun s q hfL hq => hK.ccrX_small s q hfL hq)
        hK.count_PL hW1sum
        (fun s hfL => hWsubE F T E hv hTWs hb hK s hfL)
        (fun k => hbOpWin k)
        hell ha hKl hKH hKL hmu hlille_nn hη_nn hK0 hrho_nn hbigM hzabs
        (hAbsE E hv hTabs hb).1 (hAbsE E hv hTabs hb).2.1 (hAbsE E hv hTabs hb).2.2
  · refine ⟨0, 1, le_refl 0, one_pos, ?_⟩
    intro Mode instA instF instD F T E hv htle hb hK Φ hΦ
    exfalso
    have h1 : |E.W1 0| ≤ K₀ * E.aScat := hK.W1_le 0
    have h2 : 0 < E.aScat := hv.a_pos
    have h3 : K₀ * E.aScat < 0 := mul_neg_of_neg_of_pos (not_le.mp hK0) h2
    linarith [abs_nonneg (E.W1 0)]

end Work.BoseC3QAll
