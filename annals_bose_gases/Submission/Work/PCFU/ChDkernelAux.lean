import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.ChDpieceAsm
import Submission.Work.BoseBoxFock.PCFU.W1fun_chat_small
import Submission.Work.BoseRowQ2.chatTailEst
import Submission.Work.PCFU.chDaliasSum_le
import Submission.Work.PCFU.chDaliasSum_summable
import Submission.Work.PCFU.chDpoisson_E
import Submission.Work.PCFU.chDpoisson_uvSmear
import Submission.Work.PCFU.mu_ell_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PCFU.ChDkernelAux` — the kernel bound of the `(D)`-slot

The `(D)`-slot piece is closed by

    chDslot_le_of_kernelBound   (PROVED, `PCFU/ChDpieceAsm.lean`)
      + chDkernel_le            (`PCFU/chDkernel_le.lean`, from this file)
      + chDslot_le_of_kernel    (delegated)                       state-side reduction
      + chDA_arith / mu_ell_bounds / chDA_budget                  arithmetic

The kernel bound is the assembly of

* `Work.PCFU.chDpoisson_uvSmear`  — `KχfrU z = Σ'_d (χ_ℓ ⋆ uvSmear)(z+ℓd)`   **(P1, PROVED)**
* `Work.PCFU.chDpoisson_E`        — the Fourier series of the truncation periodisation
                                                                             **(P2, PROVED)**
* `Work.PCFU.chDaliasSum_le`      — the face-layer alias bound               **(P4, PROVED)**
* `PCFU.W1fun_chat_small`         — `|chat W1fun| ≤ θ` beyond any radius    (corpus)
* `BoseRowQ2.summable_chiHat_abs` — the lattice mass of `χ̂`                 (corpus)
* `chDkernel_glue`                — the combination of (P2) + (P4)          **(PROVED, `ChDpieceAsm`)**

This file proves the *instantiation*: the constants `K0` (from `chDA_arith` with the admissible
ranges `mu_ell_bounds`), the lattice mass `Tailmax := 1 + Σ'_m|χ̂(vec m)|`, `Cχ := √(48/π)`, the
cut-off `θ(μ) := chDA v K0 μ /(2·Cχ·Tailmax·ℓ³)` (so that the truncation piece contributes exactly
`chDA v K0 μ /(2ℓ³)`), and the threshold

    T μ := ⌈(2ℓ/π)·P(μ)⌉ + 1      (`ℓ = ellH v μ`, `P(μ)` the radius of `W1fun_chat_small` at `θ(μ)`),

so that `uvRad ℓ N ≥ P(μ)` for `N ≥ T μ`.  The alias piece is paid by `chDA_arith`, which reserves
the other half of `chDA v K0 μ /ℓ³`.

`chDkernel_le_aux` isolates everything except the pointwise *decomposition*

    KχfrU − chDC = Σ'_d (χ_ℓ ⋆ chDkerE)(z+ℓd) + Σ'_{d≠0}(χ_ℓ ⋆ W1fun)(z+ℓd)      (`PCFU.chD_split`)

and the summability of the `W1fun` family (`PCFU.chDW1sum_summable`); both are delegated and are
supplied in `chDkernel_le`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The kernel bound of the `(D)`-slot, from the decomposition.**  Given the pointwise
decomposition `hσ` and the summability `halSum` of the `W1fun` family, there are `K0 > 0` and a
threshold `T : ℝ → ℕ` such that, for every admissible `μ` in the regime (`R ≤ ℓ·chiR0`, `4R ≤ ℓ`)
and every `N ≥ T μ`, the `z`-kernel of the slot is bounded by `chDA v K0 μ / ℓ³`. -/
theorem chDkernel_le_aux {v : E3 → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < BoseGases.a v)
    (fu : Work.BoseBoxFix.LowCut) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hσ : ∀ (μ : ℝ), 0 < μ → ∀ (N : ℕ), 1 ≤ N →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 → ∀ z : E3,
      Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
          - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z
        = (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
              (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu
                (Work.BoseBoxFock.ellH v μ) N u : ℝ) : ℂ))
              (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d))
          + (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
              Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
                (fun u => ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))
                (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d))))
    (halSum : ∀ (μ : ℝ), 0 < μ → ∀ z : E3,
      Summable (fun d : Fin 3 → ℤ => ‖Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
        (fun u => ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))
        (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d)‖)) :
    ∃ (K0 : ℝ) (T : ℝ → ℕ), 0 < K0 ∧
      ∀ (μ : ℝ), 0 < μ → Work.BoseBoxFix.Adm v ε₀ μ →
        R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
        4 * R ≤ Work.BoseBoxFock.ellH v μ →
        ∀ (N : ℕ), T μ ≤ N → ∀ z : E3,
          ‖(((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ)) : ℂ)
            * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z)‖
            ≤ Work.BoseBoxFock.PCFU.chDA v K0 μ / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
  -- ## the constants
  obtain ⟨CA, hCA0, hCAle⟩ := Work.PCFU.chDaliasSum_le (v := v) (h := h) hR hv hvrad hv_supp
  obtain ⟨K0, hK0pos, hK0arith⟩ :=
    Work.BoseBoxFock.PCFU.chDA_arith (v := v) (R := R) (CA := CA)
      (M1 := ε₀ / (BoseGases.a v) ^ 3)
      (M2 := (BoseGases.a v) ^ (-6 : ℤ) * ε₀ ^ (812 / 323 : ℝ))
      hR hav hCA0 (by positivity) (by positivity)
  have hM1b := (Work.PCFU.mu_ell_bounds (v := v) hε₀ hav).1
  have hM2b := (Work.PCFU.mu_ell_bounds (v := v) hε₀ hav).2
  -- ## the explicit `L¹` constant `16π·(a v)`
  have hL1 : ∀ ℓ : ℝ, R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 16 * Real.pi * BoseGases.a v := by
    intro ℓ hRℓ
    have hchi0 : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
    have hpos : 0 < ℓ * Submission.BoseGases.chiR0 := lt_of_lt_of_le hR hRℓ
    have hℓ : 0 < ℓ := by nlinarith [hpos, hchi0]
    simpa [Work.BoseFixR.W1fun] using
      Submission.BoseGases.wScaled_g0_abs_integral_le (v := v) (R := R) (ℓ := ℓ)
        hR hv hvrad hv_supp h hℓ hRℓ
  -- ## the lattice mass of `χ̂`
  have hSumm : Summable (fun m : Fin 3 → ℤ =>
      |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)|) := by
    simpa [Work.BoseRowQ2.chiHat] using Work.BoseRowQ2.summable_chiHat_abs
  set Tmass : ℝ := ∑' m : Fin 3 → ℤ, |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec m)|
    with hTmass
  have hTmassnn : 0 ≤ Tmass := by
    rw [hTmass]; exact tsum_nonneg (fun m => abs_nonneg _)
  set Tailmax : ℝ := 1 + Tmass with hTailmax
  have hTailmaxpos : 0 < Tailmax := by rw [hTailmax]; linarith
  set Cχ : ℝ := Real.sqrt (48 / Real.pi) with hCχdef
  have hCχ0 : 0 ≤ Cχ := by rw [hCχdef]; exact Real.sqrt_nonneg _
  have hCχpos : 0 < Cχ := by
    rw [hCχdef]; exact Real.sqrt_pos.mpr (by positivity)
  -- ## the alias allowance, the cut-off and the threshold
  set Kalias : ℝ → ℝ := fun μ =>
    CA * (R / Work.BoseBoxFock.ellH v μ) ^ 6 * (16 * Real.pi * BoseGases.a v) with hKaliasdef
  set θ : ℝ → ℝ := fun μ =>
    Work.BoseBoxFock.PCFU.chDA v K0 μ
      / (2 * Cχ * Tailmax * (Work.BoseBoxFock.ellH v μ) ^ 3) with hθdef
  set Pfun : ℝ → ℝ := fun μ => if hh : 0 < θ μ then
      Classical.choose (Work.BoseBoxFock.PCFU.W1fun_chat_small (v := v) (h := h)
        (ℓ := Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hh) else 0
    with hPfun
  set T : ℝ → ℕ := fun μ => if 0 < θ μ then
      Nat.ceil ((2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ) + 1 else 1 with hTdef
  refine ⟨K0, T, hK0pos, ?_⟩
  intro μ hμ hAdm hRℓ h4R N hTN z
  -- ## the local facts at this `μ`
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hchDApos : 0 < Work.BoseBoxFock.PCFU.chDA v K0 μ := by
    rw [Work.BoseBoxFock.PCFU.chDA_of_pos hμ]
    have h3 : (0 : ℝ) < (Work.BoseBoxFock.ellH v μ) ^ 3 := by positivity
    have h3i : (0 : ℝ) < (Work.BoseBoxFock.ellH v μ) ^ (-3 : ℤ) := zpow_pos hℓ (-3)
    have ha : 0 < BoseGases.a v := hav
    have hν : 0 < μ := hμ
    positivity
  have hθeq : θ μ = Work.BoseBoxFock.PCFU.chDA v K0 μ
      / (2 * Cχ * Tailmax * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
    simp only [hθdef]
  have hθpos : 0 < θ μ := by
    rw [hθeq]; exact div_pos hchDApos (by positivity)
  have hθ0 : 0 ≤ θ μ := hθpos.le
  have hCχne : Cχ ≠ 0 := ne_of_gt hCχpos
  have hTne : Tailmax ≠ 0 := ne_of_gt hTailmaxpos
  have hℓ3ne : (Work.BoseBoxFock.ellH v μ) ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  -- ## the threshold
  have hTval : T μ = Nat.ceil ((2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ) + 1 := by
    simp only [hTdef, if_pos hθpos]
  have hTN' : Nat.ceil ((2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ) + 1 ≤ N := by
    rw [hTval] at hTN; exact hTN
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hTN'
  have hceil : ((Nat.ceil ((2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ) : ℕ) : ℝ)
      ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_of_succ_le hTN'
  have hcle : (2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) hceil
  have hPle' : Pfun μ ≤ Real.pi / (2 * Work.BoseBoxFock.ellH v μ) * (N : ℝ) := by
    have hc : 0 ≤ Real.pi / (2 * Work.BoseBoxFock.ellH v μ) := by positivity
    have h := mul_le_mul_of_nonneg_left hcle hc
    have hid : Real.pi / (2 * Work.BoseBoxFock.ellH v μ)
        * ((2 * Work.BoseBoxFock.ellH v μ / Real.pi) * Pfun μ) = Pfun μ := by
      field_simp
    rwa [hid] at h
  have hPle : Pfun μ ≤ Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N := by
    rw [Work.BoseBoxFock.uvRad]
    have heq : 2 * Real.pi / Work.BoseBoxFock.ellH v μ * (N : ℝ) / 4
        = Real.pi / (2 * Work.BoseBoxFock.ellH v μ) * (N : ℝ) := by
      field_simp
      ring
    rw [heq]; exact hPle'
  -- ## the smallness of `chat W1fun` beyond `uvRad ℓ N`
  have hPeq : Pfun μ = Classical.choose (Work.BoseBoxFock.PCFU.W1fun_chat_small (v := v) (h := h)
      (ℓ := Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hθpos) := by
    simp only [hPfun]
    exact dif_pos hθpos
  have hPprop : ∀ p : E3, Pfun μ ≤ ‖p‖ →
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p| ≤ θ μ := by
    intro p hp
    have hspec := (Classical.choose_spec (Work.BoseBoxFock.PCFU.W1fun_chat_small (v := v) (h := h)
      (ℓ := Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hθpos)).2
    rw [hPeq] at hp
    exact hspec p hp
  have hS : ∀ p : E3, Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N ≤ ‖p‖ →
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p| ≤ θ μ :=
    fun p hp => hPprop p (le_trans hPle hp)
  -- ## the pointwise bound on the bump
  have hχ : ∀ z : E3, |Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z| ≤ Cχ := by
    intro z
    rw [hCχdef, Work.BoseBoxFock.chiLam_eq_chiR]
    exact Work.BoseBoxFock.abs_chiR_le _
  -- ## the alias bound
  have h2R : 2 * R ≤ Work.BoseBoxFock.ellH v μ := by linarith
  have hAlias : ∀ z : E3, (∑' d : Fin 3 → ℤ, (if d = 0 then 0 else
      ‖(((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ)) : ℂ)
        * Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
            (fun u => ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ))
            (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d)‖)) ≤ Kalias μ := by
    intro z
    have h1 := hCAle (ℓ := Work.BoseBoxFock.ellH v μ) hℓ (N := N) z hRℓ h2R
    have h2 := mul_le_mul_of_nonneg_left (hL1 (Work.BoseBoxFock.ellH v μ) hRℓ)
      (mul_nonneg hCA0 (pow_nonneg (div_nonneg hR.le hℓ.le) 6))
    simp only [hKaliasdef]
    exact le_trans h1 h2
  -- ## the arithmetic: the two halves of `chDA`
  have hθtail : Cχ * (θ μ * Tailmax)
      = Work.BoseBoxFock.PCFU.chDA v K0 μ / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
    rw [hθeq]
    field_simp
  have hKali : Kalias μ ≤ Work.BoseBoxFock.PCFU.chDA v K0 μ
      / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
    have h2 := hK0arith hμ (hM1b hμ hAdm) (hM2b hμ hAdm)
    have hgoal : Work.BoseBoxFock.PCFU.chDA v K0 μ / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3)
        = (Work.BoseBoxFock.PCFU.chDA v K0 μ / (Work.BoseBoxFock.ellH v μ) ^ 3) / 2 := by
      field_simp
    simp only [hKaliasdef]
    rw [hgoal]
    linarith
  -- ## the two flat inputs of the glue
  have hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) :=
    Work.BoseBoxFock.PCFU.W1fun_integrable hR hℓ hv_supp hRℓ
  have hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) :=
    (isCompact_closedBall (0 : E3) R).of_isClosed_subset
      (isClosed_tsupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
      ((Work.BoseFixR.tsupport_W1fun_subset h hv_supp (Work.BoseBoxFock.ellH v μ)).trans
        Metric.ball_subset_closedBall)
  have hev : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x :=
    Work.BoseFixR.isEven_W1fun h hvrad (Work.BoseBoxFock.ellH v μ)
  have hP2 : ∀ z : E3,
      (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
        (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu
          (Work.BoseBoxFock.ellH v μ) N u : ℝ) : ℂ))
        (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d))
      = ∑' m : Fin 3 → ℤ,
          (((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                  (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi
                  ((Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.kmomInt
                    (Work.BoseBoxFock.ellH v μ) m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I *
                (inner ℝ (Work.BoseBoxFock.kmomInt (Work.BoseBoxFock.ellH v μ) m) z : ℂ)) :=
    fun z => Work.PCFU.chDpoisson_E hℓ hN1 hI hcs hev z
  -- ## the glue
  have hglue := Work.BoseBoxFock.PCFU.chDkernel_glue (v := v) (h := h) (fu := fu)
      (ℓ := Work.BoseBoxFock.ellH v μ) (N := N) (μ := μ)
      hℓ hN1 (Cχ := Cχ) (θ₁ := θ μ) (Tailmax := Tailmax) (Kalias := Kalias μ)
      hCχ0 hθ0 hTailmaxpos.le hχ hS hSumm (by rw [hTailmax, hTmass]; linarith)
      (hσ μ hμ N hN1 hRℓ) hP2 (halSum μ hμ) hAlias
  refine le_trans (hglue z) ?_
  calc Cχ * (θ μ * Tailmax) + Kalias μ
      = Work.BoseBoxFock.PCFU.chDA v K0 μ / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3)
          + Kalias μ := by rw [hθtail]
    _ ≤ Work.BoseBoxFock.PCFU.chDA v K0 μ / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3)
          + Work.BoseBoxFock.PCFU.chDA v K0 μ / (2 * (Work.BoseBoxFock.ellH v μ) ^ 3) := by
        linarith [hKali]
    _ = Work.BoseBoxFock.PCFU.chDA v K0 μ / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
        field_simp
        ring

end Work.PCFU
