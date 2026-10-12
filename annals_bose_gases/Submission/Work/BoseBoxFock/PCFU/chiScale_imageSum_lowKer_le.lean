import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.latVec_add_sub_norm_ge
import Submission.Work.BoseBoxFock.PCFU.latticeTailNSqBound
import Submission.Work.BoseBoxFock.PCFU.lowKer_decay
import Submission.Work.BoseBoxFock.PCFU.scalarImageSumBound
import Submission.Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
import Submission.Work.BoseBoxFock.kernelImage_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le`

**The `Ksfr`-image bound.**  For FS's low-momentum cut-off `fc` and every `κ, M` there is `C ≥ 0`
with

    ‖ χ_ℓ(b) · ℓ³ · ∑'_{d ≠ 0} Κ(u - b + ℓ • latVec d) ‖ ≤ C / ℓ^M    (0 < ℓ, u ∈ acube ℓ),

where `Κ = lowKer fc κ` is the position kernel of the multiplier `f(‖p‖/κ)`
(`PCFU/dictBricks.lean`).

## Why it is true

`Κ` is the inverse Fourier transform of the smooth compactly supported symbol `f(‖p‖/κ)`
(`Work.BoseBoxFock.PCFU.lowKer_decay`: `(1 + ‖z‖)^{2N} ‖Κ z‖ ≤ C_N` for every `N`), so the image
sum is a Riemann sum of a rapidly decaying function.  Two mechanisms make it small:

* **the `d = 0` term is excluded and the remaining images are far from the origin.**  Write
  `α = ℓ⁻¹ • u`, `β = ℓ⁻¹ • b`, `w = α - β`.  Since `u ∈ acube ℓ` every coordinate of `α` is at
  most `1/2` in modulus, and `chiScale ℓ b ≠ 0` forces `‖β‖ < 1/2`; hence for `d ≠ 0` some
  coordinate of `latVec d + α` has modulus `≥ 1/2`, so
  `‖latVec d + w‖ ≥ 1/2 - ‖β‖ =: δ` (`Work.BoseBoxFock.PCFU.latVec_add_sub_norm_ge`).  Thus
  `‖u - b + ℓ • latVec d‖ = ℓ ‖latVec d + w‖ ≥ ℓ δ`, and splitting the lattice at radius
  `R = max 3 ℓ⁻¹` (finitely many points inside, counted by `125 (1+R)³`) gives
  `∑'_{d ≠ 0} ‖Κ(u - b + ℓ • latVec d)‖ ≤ C (1+R)³ (1 + ℓδ)^{-2N} + C ℓ^{-2N} R^{3-2N}`.
* **the flatness of the bump `χ` at the boundary of its support.**  `chiScale ℓ b ≤ C_K δ^K`
  (`Work.BoseFixB1.chi_boundary_taylor`), and `R = max 3 ℓ⁻¹` is exactly the radius at which
  `δ^K` pays for all the factors of `ℓ` and `R` (the elementary bookkeeping is
  `Work.BoseBoxFock.PCFU.scalarImageSumBound`).

## Structure of this file

`imageSum_shift_partial` is the finite-set form of the sum bound (used twice: for the summability
of the majorant and for its `tsum` bound).  `chiScale_imageSum_lowKer_le_aux` carries the two
lattice/arithmetic inputs as hypotheses, so that the analytic assembly is independent of them; the
final theorem instantiates them.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

/-- The norm of a real number seen in `ℂ` is its absolute value. -/
private lemma complexNorm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- **The finite-set form of the lattice/kernel bound.**  With `R ≥ 3`, the lattice is split at
radius `R`: at most `125 (1+R)³` points are "near" (each contributing at most `(1 + ℓδ)^{-2N}`,
since all nonzero images have norm at least `δ`), and the "far" points are bounded by the sharp
lattice tail `CT · R^{3-2N}`, scaled by `ℓ^{-2N}` (as `‖latVec d + w‖ ≥ ‖latVec d‖/2` there). -/
private theorem imageSum_shift_partial {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ0 : 0 < δ)
    {w : E3} (hw : ‖w‖ ≤ 3 / 2)
    (hgeo : ∀ d : Fin 3 → ℤ, d ≠ 0 → δ ≤ ‖Work.BoseBoxFock.latVec d + w‖)
    {N : ℕ} (hN : 2 ≤ N) {CT : ℝ}
    (hCT : ∀ (ρ : ℝ), 1 ≤ ρ → ∀ u : Finset (Fin 3 → ℤ),
      ∑ d ∈ u.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
          ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹ ≤ CT * ((ρ ^ (2 * N - 3))⁻¹))
    {R : ℝ} (hR3 : 3 ≤ R) (u : Finset (Fin 3 → ℤ)) :
    ∑ d ∈ u, (if d = 0 then (0 : ℝ)
        else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹)
      ≤ 125 * (1 + R) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
        + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹) * (CT * ((R ^ (2 * N - 3))⁻¹)) := by
  classical
  have hR1 : 1 ≤ R := by linarith
  set F : (Fin 3 → ℤ) → ℝ := fun d => if d = 0 then (0 : ℝ)
      else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹ with hF
  have hsplit : (∑ d ∈ u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)), F d)
      + (∑ d ∈ u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))), F d)
      = ∑ d ∈ u, F d :=
    Finset.sum_filter_add_sum_filter_not u (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)) F
  rw [← hsplit, add_comm]
  refine add_le_add ?_ ?_
  · -- the near points
    have hcard : (((u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))).card : ℕ) : ℝ)
        ≤ 125 * (1 + R) ^ 3 := by
      have hsub : u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))
          ⊆ Work.BoseBoxFock.box (Nat.floor R + 1) := by
        intro d hd
        rw [Finset.mem_filter] at hd
        have hle : (Work.BoseBoxFock.nSq d : ℝ) ≤ R ^ 2 := not_lt.mp hd.2
        rw [Work.BoseBoxFock.mem_box_iff]
        intro i
        have hK : (((Work.BoseBoxFock.K d : ℕ)) : ℝ) ≤ R := by
          have h1 : (((Work.BoseBoxFock.K d : ℕ)) : ℝ) ≤ ‖Work.BoseBoxFock.latVec d‖ :=
            Work.BoseBoxFock.K_le_norm_latVec d
          have h2 : ‖Work.BoseBoxFock.latVec d‖ ^ 2 ≤ R ^ 2 := by
            rw [Work.BoseBoxFock.latVec_norm_sq]
            exact hle
          nlinarith [norm_nonneg (Work.BoseBoxFock.latVec d)]
        exact le_trans (Work.BoseBoxFock.K_spec d i)
          (le_trans (Nat.le_floor hK) (Nat.le_succ _))
      have hcard0 : ((u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))).card : ℕ)
          ≤ (Work.BoseBoxFock.box (Nat.floor R + 1)).card := Finset.card_le_card hsub
      have hcard1 : ((Work.BoseBoxFock.box (Nat.floor R + 1)).card : ℝ)
          = (((2 * (Nat.floor R + 1) + 1) ^ 3 : ℕ) : ℝ) := by
        rw [Work.BoseBoxFock.shellCard_box_card]
      have hfloor : ((Nat.floor R : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
      have h6 : (((2 * (Nat.floor R + 1) + 1 : ℕ)) : ℝ) ≤ 5 * (1 + R) := by
        push_cast
        linarith
      calc (((u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))).card : ℕ) : ℝ)
          ≤ ((Work.BoseBoxFock.box (Nat.floor R + 1)).card : ℝ) := by exact_mod_cast hcard0
        _ = (((2 * (Nat.floor R + 1) + 1) ^ 3 : ℕ) : ℝ) := hcard1
        _ = (((2 * (Nat.floor R + 1) + 1 : ℕ)) : ℝ) ^ 3 := by rw [Nat.cast_pow]
        _ ≤ (5 * (1 + R)) ^ 3 := pow_le_pow_left₀ (by positivity) h6 3
        _ = 125 * (1 + R) ^ 3 := by ring
    have hpt : ∀ d ∈ u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))),
        F d ≤ ((1 + ℓ * δ) ^ (2 * N))⁻¹ := by
      intro d hd
      rw [Finset.mem_filter] at hd
      by_cases hd0 : d = 0
      · rw [hF]
        simp only [hd0, if_pos rfl]
        positivity
      · rw [hF]
        simp only [if_neg hd0]
        have h1 : δ ≤ ‖Work.BoseBoxFock.latVec d + w‖ := hgeo d hd0
        have h3 : (1 + ℓ * δ) ≤ 1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖ := by
          have h2 := mul_le_mul_of_nonneg_left h1 hℓ.le
          linarith
        exact (inv_le_inv₀ (by positivity)
          (pow_pos (by positivity) (2 * N))).mpr (pow_le_pow_left₀ (by positivity) h3 (2 * N))
    calc ∑ d ∈ u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))), F d
        ≤ ∑ d ∈ u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))),
            (((1 + ℓ * δ) ^ (2 * N))⁻¹) := Finset.sum_le_sum hpt
      _ = (((u.filter (fun d => ¬ (R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))).card : ℕ) : ℝ)
            * (((1 + ℓ * δ) ^ (2 * N))⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (125 * (1 + R) ^ 3) * (((1 + ℓ * δ) ^ (2 * N))⁻¹) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 125 * (1 + R) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹) := by ring
  · -- the far points
    have hpt : ∀ d ∈ u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
        F d ≤ (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
            * (((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdR : R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ) := hd.2
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0] at hdR
        simp only [Work.BoseBoxFock.nSq_zero, Nat.cast_zero] at hdR
        nlinarith [sq_nonneg R]
      rw [hF]
      simp only [if_neg hd0]
      have hnorm3 : 3 < ‖Work.BoseBoxFock.latVec d‖ := by
        have h9 : (9 : ℝ) < (Work.BoseBoxFock.nSq d : ℝ) := by nlinarith [hR3, hdR]
        have hsq : ‖Work.BoseBoxFock.latVec d‖ ^ 2 = (Work.BoseBoxFock.nSq d : ℝ) :=
          Work.BoseBoxFock.latVec_norm_sq d
        nlinarith [norm_nonneg (Work.BoseBoxFock.latVec d)]
      have hr2 : ‖Work.BoseBoxFock.latVec d‖ / 2 ≤ ‖Work.BoseBoxFock.latVec d + w‖ := by
        have h1 : ‖Work.BoseBoxFock.latVec d‖ - ‖w‖ ≤ ‖Work.BoseBoxFock.latVec d + w‖ := by
          have h2 := norm_add_le (Work.BoseBoxFock.latVec d + w) (-w)
          have h3 : (Work.BoseBoxFock.latVec d + w) + (-w) = Work.BoseBoxFock.latVec d := by abel
          rw [h3, norm_neg] at h2
          linarith
        linarith
      have hge : (ℓ * ‖Work.BoseBoxFock.latVec d‖ / 2) ^ (2 * N)
          ≤ (1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N) := by
        refine pow_le_pow_left₀ (by positivity) ?_ (2 * N)
        nlinarith [mul_le_mul_of_nonneg_left hr2 hℓ.le]
      have hpow : ‖Work.BoseBoxFock.latVec d‖ ^ (2 * N)
          = (Work.BoseBoxFock.nSq d : ℝ) ^ N := by
        rw [pow_mul (‖Work.BoseBoxFock.latVec d‖) 2 N, Work.BoseBoxFock.latVec_norm_sq]
      have hbase : ((ℓ * ‖Work.BoseBoxFock.latVec d‖ / 2) ^ (2 * N))⁻¹
          = (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
              * (((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹) := by
        rw [div_pow, mul_pow, hpow, inv_div, div_eq_mul_inv, mul_inv]
        ring
      rw [← hbase]
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hge
    have hidem : (u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))).filter
        (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ))
        = u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)) := by
      ext d
      simp only [Finset.mem_filter]
      tauto
    calc ∑ d ∈ u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)), F d
        ≤ ∑ d ∈ u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
            (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
              * (((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹) := Finset.sum_le_sum hpt
      _ = (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
            * ∑ d ∈ u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
                (((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹) := by
          rw [Finset.mul_sum]
      _ ≤ (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹) * (CT * ((R ^ (2 * N - 3))⁻¹)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := hCT R hR1 (u.filter (fun d => R ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)))
          rwa [hidem] at h

/-- **The assembly, with the two lattice/arithmetic inputs as hypotheses.**  This is the analytic
content of `chiScale_imageSum_lowKer_le`; the final theorem instantiates `hTail`
(`Work.BoseBoxFock.PCFU.latticeTailNSqBound`) and `hScalar`
(`Work.BoseBoxFock.PCFU.scalarImageSumBound`). -/
private theorem chiScale_imageSum_lowKer_le_aux
    (hTail : ∀ (N : ℕ), 2 ≤ N → ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 1 ≤ ρ →
      ∀ u : Finset (Fin 3 → ℤ),
        ∑ d ∈ u.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
            ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹ ≤ C * ((ρ ^ (2 * N - 3))⁻¹))
    (hScalar : ∀ {M N K : ℕ}, 2 * N ≤ K → M + 3 ≤ 2 * N →
      ∀ {δ ℓ CT CK Cdec : ℝ}, 0 < ℓ → 0 < δ → δ ≤ 1 → 0 ≤ CT → 0 ≤ CK → 0 ≤ Cdec →
        CK * δ ^ K * ℓ ^ 3 * Cdec
            * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * ((1 + ℓ * δ) ^ (2 * N))⁻¹
                + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                    * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)))
          ≤ CK * Cdec * (8000 + (2 : ℝ) ^ (2 * N) * CT) * ((ℓ ^ M)⁻¹))
    (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ b u : EuclideanSpace ℝ (Fin 3),
      u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d))‖
        ≤ C / ℓ ^ M := by
  classical
  set N : ℕ := M + 4 with hNdef
  have hN2 : 2 ≤ N := by omega
  have hNM : M + 3 ≤ 2 * N := by omega
  obtain ⟨Cdec, hCdec0, hCdec⟩ := lowKer_decay fc hκ N
  obtain ⟨CK, hCKpos, hCK⟩ := Work.BoseFixB1.chi_boundary_taylor (2 * N)
  obtain ⟨CT, hCT0, hCT⟩ := hTail N hN2
  refine ⟨CK * Cdec * (8000 + (2 : ℝ) ^ (2 * N) * CT), ?_, ?_⟩
  · positivity
  · intro ℓ hℓ b u hu
    by_cases hχ0 : ‖(ℓ⁻¹ : ℝ) • b‖ < 1 / 2
    · -- the main case: the bump does not vanish
      set δ : ℝ := 1 / 2 - ‖(ℓ⁻¹ : ℝ) • b‖ with hδdef
      have hδ0 : 0 < δ := by rw [hδdef]; linarith
      have hδ1 : δ ≤ 1 := by
        have h : (0 : ℝ) ≤ ‖(ℓ⁻¹ : ℝ) • b‖ := norm_nonneg _
        rw [hδdef]; linarith
      have hχle : Submission.BoseGases.chiScale ℓ b ≤ CK * δ ^ (2 * N) := by
        have h := hCK ((ℓ⁻¹ : ℝ) • b) hχ0.le
        rw [hδdef]
        simpa only [Submission.BoseGases.chiScale] using h
      set w : E3 := (ℓ⁻¹ : ℝ) • (u - b) with hwdef
      have hα : ∀ m : Fin 3, |((ℓ⁻¹ : ℝ) • u) m| ≤ 1 / 2 := by
        intro m
        have hm : u m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) :=
          (Submission.BoseGases.mem_acube_iff ℓ u).mp hu m
        have h1 : |u m| ≤ ℓ / 2 := by
          rw [abs_le]
          exact ⟨by linarith [hm.1], hm.2⟩
        have h2 : ((ℓ⁻¹ : ℝ) • u) m = ℓ⁻¹ * u m := by simp
        rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
        calc ℓ⁻¹ * |u m| ≤ ℓ⁻¹ * (ℓ / 2) := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hℓ).le
          _ = 1 / 2 := by field_simp
      have hβ : ‖(ℓ⁻¹ : ℝ) • b‖ = 1 / 2 - δ := by rw [hδdef]; ring
      have hgeo : ∀ d : Fin 3 → ℤ, d ≠ 0 → δ ≤ ‖Work.BoseBoxFock.latVec d + w‖ := by
        intro d hd
        have h := latVec_add_sub_norm_ge (δ := δ) (α := (ℓ⁻¹ : ℝ) • u)
          (β := (ℓ⁻¹ : ℝ) • b) hα hβ.le d hd
        have hw' : Work.BoseBoxFock.latVec d + (ℓ⁻¹ : ℝ) • u - (ℓ⁻¹ : ℝ) • b
            = Work.BoseBoxFock.latVec d + w := by
          rw [hwdef, smul_sub]
          abel
        rwa [hw'] at h
      have hw32 : ‖w‖ ≤ 3 / 2 := by
        have hαn : ‖(ℓ⁻¹ : ℝ) • u‖ ≤ 1 := by
          have h1 : ‖(ℓ⁻¹ : ℝ) • u‖ ^ 2 ≤ 3 * (1 / 2 : ℝ) ^ 2 := by
            rw [EuclideanSpace.norm_sq_eq]
            calc ∑ m : Fin 3, ‖((ℓ⁻¹ : ℝ) • u) m‖ ^ 2 ≤ ∑ _m : Fin 3, (1 / 2 : ℝ) ^ 2 := by
                  refine Finset.sum_le_sum (fun m _ => ?_)
                  rw [Real.norm_eq_abs]
                  nlinarith [hα m, abs_nonneg (((ℓ⁻¹ : ℝ) • u) m)]
              _ = 3 * (1 / 2 : ℝ) ^ 2 := by
                  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          nlinarith [norm_nonneg ((ℓ⁻¹ : ℝ) • u)]
        have h3 : w = (ℓ⁻¹ : ℝ) • u - (ℓ⁻¹ : ℝ) • b := by rw [hwdef, smul_sub]
        rw [h3]
        calc ‖(ℓ⁻¹ : ℝ) • u - (ℓ⁻¹ : ℝ) • b‖
            ≤ ‖(ℓ⁻¹ : ℝ) • u‖ + ‖(ℓ⁻¹ : ℝ) • b‖ := norm_sub_le _ _
          _ ≤ 1 + 1 / 2 := by linarith [hχ0.le]
          _ = 3 / 2 := by norm_num
      -- the sum bound
      have hpartial : ∀ u' : Finset (Fin 3 → ℤ), ∑ d ∈ u',
          (if d = 0 then (0 : ℝ)
            else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹)
          ≤ 125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
            + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)) :=
        fun u' => imageSum_shift_partial hℓ hδ0 hw32 hgeo hN2 hCT (le_max_left 3 ℓ⁻¹) u'
      have hsumm : Summable (fun d : Fin 3 → ℤ => (if d = 0 then (0 : ℝ)
          else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹)) :=
        summable_of_sum_le (fun d => by split_ifs <;> positivity) hpartial
      have htsum : ∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℝ)
          else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹)
          ≤ 125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
            + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)) :=
        hsumm.tsum_le_of_sum_le hpartial
      -- pointwise domination of the low-momentum images
      have hstep : ∀ d : Fin 3 → ℤ,
          ‖(if d = 0 then (0 : ℂ)
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
            ≤ Cdec * (if d = 0 then (0 : ℝ)
                else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹) := by
        intro d
        by_cases hd : d = 0
        · rw [if_pos hd, if_pos hd]
          simp
        · rw [if_neg hd, if_neg hd, complexNorm_ofReal]
          have hz : u - b + ℓ • Work.BoseBoxFock.latVec d
              = ℓ • (Work.BoseBoxFock.latVec d + w) := by
            rw [hwdef, smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ), one_smul]
            abel
          have hdec' : ‖Work.BoseBoxFock.PCFU.lowKer fc κ
              (ℓ • (Work.BoseBoxFock.latVec d + w))‖
              ≤ Cdec * (((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹) := by
            have h := hCdec (ℓ • (Work.BoseBoxFock.latVec d + w))
            rw [norm_smul, Real.norm_of_nonneg hℓ.le] at h
            rw [le_mul_inv_iff₀ (by positivity :
              (0 : ℝ) < (1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))]
            rw [mul_comm]
            exact h
          rw [hz]
          exact hdec'
      have hSsumm : Summable (fun d : Fin 3 → ℤ =>
          ‖(if d = 0 then (0 : ℂ)
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖) :=
        Summable.of_nonneg_of_le (fun d => norm_nonneg _) hstep (hsumm.mul_left Cdec)
      have hSbound : ‖(∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ)
            else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))‖
          ≤ Cdec * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
            + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹))) := by
        calc ‖∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ)
              else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
            ≤ ∑' d : Fin 3 → ℤ, ‖(if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ :=
              norm_tsum_le_tsum_norm hSsumm
          _ ≤ ∑' d : Fin 3 → ℤ, Cdec * (if d = 0 then (0 : ℝ)
                else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹) :=
              Summable.tsum_le_tsum hstep hSsumm (hsumm.mul_left Cdec)
          _ = Cdec * ∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℝ)
                else ((1 + ℓ * ‖Work.BoseBoxFock.latVec d + w‖) ^ (2 * N))⁻¹) := tsum_mul_left
          _ ≤ Cdec * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
            + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹))) :=
              mul_le_mul_of_nonneg_left htsum hCdec0
      -- the final arithmetic
      have hnormeq : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
            * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
                else Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d))‖
          = Submission.BoseGases.chiScale ℓ b * ℓ ^ 3
            * ‖(∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))‖ := by
        have h1 : ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)‖
            = Submission.BoseGases.chiScale ℓ b := by
          rw [Submission.BoseGases.chiScale]
          exact Complex.norm_of_nonneg (Submission.BoseGases.chi_nonneg ((ℓ⁻¹ : ℝ) • b))
        have h2 : ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ = ℓ ^ 3 := Complex.norm_of_nonneg (by positivity)
        rw [norm_mul, norm_mul, h1, h2]
      rw [hnormeq]
      calc Submission.BoseGases.chiScale ℓ b * ℓ ^ 3
            * ‖(∑' d : Fin 3 → ℤ, (if d = 0 then (0 : ℂ)
                else ((Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))‖
          ≤ (CK * δ ^ (2 * N)) * ℓ ^ 3
            * (Cdec * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
              + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                  * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹)))) := by
            refine mul_le_mul (mul_le_mul hχle le_rfl (by positivity) (by positivity)) hSbound
              (by positivity) (by positivity)
        _ ≤ CK * Cdec * (8000 + (2 : ℝ) ^ (2 * N) * CT) / ℓ ^ M := by
            have hsc := hScalar (M := M) (N := N) (K := 2 * N) le_rfl hNM
              hℓ hδ0 hδ1 hCT0 hCKpos.le hCdec0
            have heq : CK * δ ^ (2 * N) * ℓ ^ 3
                  * (Cdec * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
                    + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                        * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹))))
                = CK * δ ^ (2 * N) * ℓ ^ 3 * Cdec
                    * (125 * (1 + max 3 ℓ⁻¹) ^ 3 * (((1 + ℓ * δ) ^ (2 * N))⁻¹)
                      + (2 : ℝ) ^ (2 * N) * ((ℓ ^ (2 * N))⁻¹)
                          * (CT * (((max 3 ℓ⁻¹) ^ (2 * N - 3))⁻¹))) := by ring
            rw [heq, div_eq_mul_inv]
            exact hsc
    · -- the bump vanishes
      have hzero : Submission.BoseGases.chiScale ℓ b = 0 := by
        simp only [Submission.BoseGases.chiScale]
        exact Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (not_lt.mp hχ0)
      rw [hzero]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact div_nonneg (by positivity) (by positivity)

theorem chiScale_imageSum_lowKer_le (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ b u : EuclideanSpace ℝ (Fin 3),
      u ∈ Submission.BoseGases.acube ℓ →
      ‖((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ)
        * (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
            else Work.BoseBoxFock.PCFU.lowKer fc κ (u - b + ℓ • Work.BoseBoxFock.latVec d))‖
        ≤ C / ℓ ^ M :=
  chiScale_imageSum_lowKer_le_aux latticeTailNSqBound
    scalarImageSumBound fc hκ M

end Work.BoseBoxFock.PCFU
