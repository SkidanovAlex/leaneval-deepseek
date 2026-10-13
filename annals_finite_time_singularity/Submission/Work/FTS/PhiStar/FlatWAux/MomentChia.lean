/-
# `Work.FTS.PhiStar.FlatWAux.MomentChia` — the moment/smoothness package for `chia ψ j`

The resummed angular profiles `chia ψ j = sin 2θ · Wt ψ j` of `FlatWAux/Defs.lean` are, for
`j ≥ 1`, the eigenfunction series `chia ψ j = Σ_m bco ψ j m · eFam m` with
`bco ψ j m = bmode m ψ · (lam m)⁻¹ ^ j` (`MomentChiaAux.chia_eq_tsum_bco`).  This file proves
the three facts requested of them under the coefficient decay `hdec`, the growth `hgr`, the
interior smoothness and boundedness of `ψ` and the vanishing `sin θ cos²θ`-moment:

* `chia ψ j` is `C^8` on `(0, π/2)` for `j ≤ J`;
* `chia ψ j · sin θ cos² θ` is integrable on `Iθ` and has vanishing integral, for `1 ≤ j ≤ J`
  (the compatibility condition of the zero-moment inverse `Linv`).

The proof of the smoothness splits the series as the `Lzero`-inverse of the next profile:

  `Lzero (chia ψ (j+1)) = chia ψ j`   on `(0, π/2)`   (`MomentChiaAux.SeriesOde`),

with the `j = 0` instance `Lzero (chia ψ 1) = ψ` provided by the eigenfunction expansion
`Σ_m bmode m ψ · eFam m = ψ` (`MomentChiaAux.BmodeExpansion`).  A function whose `Lzero`-image
is `C^m` is `C^{m+2}` in the interior (`MomentChiaAux.LzeroBootstrap`), so starting from
`chia ψ 0 = ψ` (smooth) every `chia ψ j` is smooth; iterating the bootstrap six times from the
`C²` produced by the series identity gives `C^8`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.FlatWAux.eFamSupBound
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.BmodeExpansionSelf
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOde
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.CoefSummable
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.LzeroBootstrap
import Submission.Work.FTS.PhiStar.FlatWAux.ChiaBasic
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

namespace MomentChiaAux

/-- `sin 2θ ≠ 0` on the open angular interval. -/
theorem s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]
  exact mul_ne_zero (mul_ne_zero two_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))))
    (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))

/-- The vanishing `sin θ cos²θ`-moment kills the kernel coefficient `bmode 0 ψ`. -/
theorem bmode_zero_of_moment' {ψ : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF

/-- `Lzero` is local: two functions which agree near `θ` give the same value. -/
theorem Lzero_congr_of_eventuallyEq {f₁ f₂ : ℝ → ℝ} {θ : ℝ} (h : f₁ =ᶠ[𝓝 θ] f₂) :
    Work.Elliptic.Lzero (fun _ θ' => f₁ θ') 0 θ
      = Work.Elliptic.Lzero (fun _ θ' => f₂ θ') 0 θ := by
  rw [Lzero_of_thetaOnly f₁ 0 θ, Lzero_of_thetaOnly f₂ 0 θ]
  have htan : (fun t : ℝ => Real.tan t * f₁ t) =ᶠ[𝓝 θ] (fun t : ℝ => Real.tan t * f₂ t) := by
    filter_upwards [h] with t ht
    rw [ht]
  rw [h.deriv.deriv_eq, h.eq_of_nhds, htan.deriv_eq]

/-- `lam m > 0` for `m ≥ 1`. -/
theorem lam_pos_of_one_le {m : ℕ} (hm : 1 ≤ m) : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
  rw [Work.FTS.PhiStar.Gegenbauer.lam]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

/-- `bco ψ 1 m · lam m = bmode m ψ` for `m ≥ 1`. -/
theorem bco_one_mul_lam {ψ : ℝ → ℝ} {m : ℕ} (hm : 1 ≤ m) :
    bco ψ 1 m * Work.FTS.PhiStar.Gegenbauer.lam m = Work.FTS.PhiStar.Series.bmode m ψ := by
  have hne : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt (lam_pos_of_one_le hm)
  simp only [bco, pow_one]
  field_simp

/-- `bco ψ (j+1) m · lam m = bco ψ j m` for `m ≥ 1`. -/
theorem bco_succ_mul_lam {ψ : ℝ → ℝ} {j m : ℕ} (hm : 1 ≤ m) :
    bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m = bco ψ j m := by
  have hne : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt (lam_pos_of_one_le hm)
  have h : ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j + 1)
        * Work.FTS.PhiStar.Gegenbauer.lam m
      = ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j := by
    rw [pow_succ, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  simp only [bco]
  rw [← h]
  ring

end MomentChiaAux

theorem MomentChia (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    (∀ j : ℕ, j ≤ Work.FTS.PhiStar.FlatWAux.J →
      ContDiffOn ℝ 8 (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.PhiStar.FlatWAux.chia ψ j θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.FlatWAux.chia ψ j θ
        * Work.Elliptic.sinCos2 θ) = 0) := by
  -- the angular derivative bound of the sibling `QmDerivBound` is available
  have hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Qm m) θ| ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2) := QmDerivBound
  -- integrability and the vanishing moment follow from `ChiaBasic`
  obtain ⟨-, -, hInt, hMom⟩ := ChiaBasic ψ hdec hgr hQ
  -- the kernel coefficient vanishes
  have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := MomentChiaAux.bmode_zero_of_moment' hmom
  -- the eigenfunction expansion of `ψ`
  have hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
    MomentChiaAux.BmodeExpansionSelf ψ hdec hgr (hsm 0).continuousOn hbdd hmom
  -- one more derivative for free, six times in a row
  have chain : ∀ {f h : ℝ → ℝ}, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 6 h (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ = h θ) →
      ContDiffOn ℝ 8 f (Set.Ioo 0 (Real.pi / 2)) := by
    intro f h hf hh heq
    have h3 := MomentChiaAux.LzeroBootstrap (m := 2) (by norm_num) hf
      (hh.of_le (by norm_num)) heq
    have h4 := MomentChiaAux.LzeroBootstrap (m := 3) (by norm_num) h3
      (hh.of_le (by norm_num)) heq
    have h5 := MomentChiaAux.LzeroBootstrap (m := 4) (by norm_num) h4
      (hh.of_le (by norm_num)) heq
    have h6 := MomentChiaAux.LzeroBootstrap (m := 5) (by norm_num) h5
      (hh.of_le (by norm_num)) heq
    have h7 := MomentChiaAux.LzeroBootstrap (m := 6) (by norm_num) h6
      (hh.of_le (by norm_num)) heq
    exact MomentChiaAux.LzeroBootstrap (m := 7) (by norm_num) h7
      (hh.of_le (by norm_num)) heq
  -- the induction on the level `j`
  have main : ∀ j : ℕ, ContDiffOn ℝ 8 (chia ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro j
    induction j with
    | zero =>
      refine (hsm 8).congr (fun θ hθ => ?_)
      exact chia_zero (MomentChiaAux.s2_ne_zero_of_mem_Ioo hθ)
    | succ j ih =>
      have hj1 : 1 ≤ j + 1 := by omega
      obtain ⟨hcs, hds⟩ := MomentChiaAux.CoefSummable ψ hdec (j + 1) hj1
      obtain ⟨hC2, hLzero⟩ :=
        MomentChiaAux.SeriesOde (MomentChiaAux.bco ψ (j + 1))
          (fun m => MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
          (fun m => rfl) hcs hds
      have hEqOn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          chia ψ (j + 1) θ = ∑' m : ℕ, MomentChiaAux.bco ψ (j + 1) m
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ :=
        fun θ hθ => MomentChiaAux.chia_eq_tsum_bco ψ hj1 hθ
      have hC2chia : ContDiffOn ℝ 2 (chia ψ (j + 1)) (Set.Ioo 0 (Real.pi / 2)) :=
        hC2.congr (fun θ hθ => hEqOn θ hθ)
      have hLzero' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          Work.Elliptic.Lzero (fun _ θ' => chia ψ (j + 1) θ') 0 θ
            = ∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m
                * Work.FTS.PhiStar.Gegenbauer.lam m)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
        intro θ hθ
        refine (MomentChiaAux.Lzero_congr_of_eventuallyEq ?_).trans (hLzero θ hθ)
        exact Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioo 0 (Real.pi / 2), isOpen_Ioo.mem_nhds hθ,
            fun θ' hθ' => hEqOn θ' hθ'⟩
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- level `1`: the source is `ψ` itself
        subst hj0
        have hsrc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
            (∑' m : ℕ, (MomentChiaAux.bco ψ 1 m * Work.FTS.PhiStar.Gegenbauer.lam m)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
          intro θ hθ
          have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ 1 m
                * Work.FTS.PhiStar.Gegenbauer.lam m)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
            refine tsum_congr (fun m => ?_)
            rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm
              simp only [MomentChiaAux.bco_apply_zero ψ le_rfl, zero_mul, hb0]
            · rw [MomentChiaAux.bco_one_mul_lam (ψ := ψ) hm]
          rw [htsum]
          exact hexp θ hθ
        exact chain hC2chia (hsm 6) (fun θ hθ => by rw [hLzero' θ hθ, hsrc θ hθ])
      · -- level `≥ 2`: the source is the previous profile
        have hsrc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
            (∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m
                * Work.FTS.PhiStar.Gegenbauer.lam m)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = chia ψ j θ := by
          intro θ hθ
          have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m
                * Work.FTS.PhiStar.Gegenbauer.lam m)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              = ∑' m : ℕ, MomentChiaAux.bco ψ j m
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
            refine tsum_congr (fun m => ?_)
            rcases Nat.eq_zero_or_pos m with hm | hm
            · subst hm
              simp only [MomentChiaAux.bco_apply_zero ψ hj1, zero_mul,
                MomentChiaAux.bco_apply_zero ψ hjpos]
            · rw [MomentChiaAux.bco_succ_mul_lam (ψ := ψ) (j := j) hm]
          rw [htsum]
          exact (MomentChiaAux.chia_eq_tsum_bco ψ hjpos hθ).symm
        exact chain hC2chia (ih.of_le (by norm_num))
          (fun θ hθ => by rw [hLzero' θ hθ, hsrc θ hθ])
  refine ⟨fun j _ => main j, hInt, hMom⟩

end Work.FTS.PhiStar.FlatWAux
