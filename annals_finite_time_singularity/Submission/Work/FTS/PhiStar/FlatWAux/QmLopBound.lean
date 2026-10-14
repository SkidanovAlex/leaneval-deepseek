import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstTendsto
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChia =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## The smoothness of the divided mode on the open quadrant -/

/-- Every Gegenbauer polynomial is `C^k` for every `k` (the recurrence only involves products
and divisions by a positive constant). -/
theorem gC_contDiff_all_fts : ∀ k n : ℕ, ContDiff ℝ k (Work.FTS.PhiStar.Gegenbauer.gC n) := by
  intro k n
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      exact contDiff_const
  | one =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
      exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x : ℝ =>
        (2 * ((n : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
          - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
      exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-- `Qm m` is `C^n` on the open quadrant, for every `n`. -/
theorem contDiffOn_Qm_fts (m n : ℕ) :
    ContDiffOn ℝ n (Qm m) (Set.Ioo 0 (Real.pi / 2)) := by
  have heFam : ContDiffOn ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam m)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.contDiff_cos.mul ((gC_contDiff_all_fts n (2 * m + 1)).comp Real.contDiff_sin)).contDiffOn
  have hs2 : ContDiffOn ℝ n (Work.Construction.s2) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) _
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Construction.s2 θ ≠ 0 := by
    intro θ hθ
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  show ContDiffOn ℝ n (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
    / Work.Construction.s2 θ) _
  exact heFam.div hs2 hne

/-- The angular derivative of the divided mode is `C^k` at every interior point, for every
`k`. -/
theorem contDiffAt_deriv_Qm_fts (m : ℕ) : ∀ k : ℕ, ∀ θ : ℝ,
    θ ∈ Set.Ioo 0 (Real.pi / 2) → ContDiffAt ℝ k (deriv (Qm m)) θ := by
  intro k θ hθ
  have h1 : ContDiffAt ℝ (k + 1) (Qm m) θ :=
    (contDiffOn_Qm_fts m (k + 1)).contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have h2 : ContDiffAt ℝ k (deriv (Qm m)) θ :=
    h1.derivWithin (m := (k : WithTop ℕ∞)) (by simp)
  exact h2

/-! ## The expansion of `Lop^[i]` in powers of `∂_θ` -/

/-- `Lop^[i] g` expanded in the plain derivatives of `g`, at a point where `g` is `C^∞`. -/
theorem Lop_iter_expansion (i : ℕ) (g : ℝ → ℝ) (θ : ℝ)
    (hg : ∀ k : ℕ, ContDiffAt ℝ k g θ) :
    (Work.Spaces.Lop^[i]) g θ = ∑ r ∈ Finset.range (i + 1),
      Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r g θ := by
  have hf : ∀ k : ℕ, ContDiffAt ℝ k
      (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (0, θ) := by
    intro k
    have hsnd : ContDiffAt ℝ k (Prod.snd : ℝ × ℝ → ℝ) ((0 : ℝ), θ) := contDiff_snd.contDiffAt
    have hgk : ContDiffAt ℝ k g (Prod.snd ((0 : ℝ), θ)) := hg k
    have hcomp : ContDiffAt ℝ k (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (0, θ) :=
      ContDiffAt.comp ((0 : ℝ), θ) hgk hsnd
    exact hcomp
  have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local i
    (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ hf
  have hL : Work.Spaces.DthIter i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = (Work.Spaces.Lop^[i]) g θ := by
    have h := congrFun
      (Work.Spaces.DthIter_eq_iterate_Lop i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0) θ
    simpa using h
  rw [← hL, hexp]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Work.FTS.EllipticEst.remov.selfdth.pthIter_eq_iteratedDeriv_slice]

/-- `|sin(2θ)|^r ≤ 1`. -/
theorem abs_sin_two_pow_le_one (r : ℕ) (θ : ℝ) : |Real.sin (2 * θ)| ^ r ≤ 1 :=
  pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)

/-! ## The bound -/

theorem QmLopBound : ∃ C : ℕ → ℝ, (∀ i : ℕ, 0 ≤ C i) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ (i : ℕ), i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ|
        ≤ C i * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
  -- uniform bounds for the coefficients of the expansion
  obtain ⟨KB, hKBpos, hKB⟩ : ∃ KB : ℕ × ℕ → ℝ, (∀ p : ℕ × ℕ, 0 < KB p) ∧
      ∀ (p : ℕ × ℕ) (θ : ℝ),
        |Work.FTS.EllipticEst.remov.selfdth.dthCoef p.1 p.2 θ|
          ≤ KB p * |Real.sin (2 * θ)| ^ p.2 := by
    choose KB hpos hbd using fun p : ℕ × ℕ =>
      Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound p.1 p.2
    exact ⟨KB, hpos, hbd⟩
  -- the derivative growth of the divided mode
  obtain ⟨C₀, hC₀nn, hC₀⟩ := QmDerivBound
  refine ⟨fun i => ∑ r ∈ Finset.range (i + 1), KB (i, r) * C₀ (r + 1), ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun r _ => mul_nonneg (le_of_lt (hKBpos (i, r))) (hC₀nn (r + 1))
  · intro m hm i hi θ hθ
    have hbase : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hexp := Lop_iter_expansion i (deriv (Qm m)) θ
      (fun k => contDiffAt_deriv_Qm_fts m k θ hθ)
    have hstep : ∀ r : ℕ,
        iteratedDeriv r (deriv (Qm m)) θ = iteratedDeriv (r + 1) (Qm m) θ :=
      fun r => congrFun (iteratedDeriv_succ' (n := r) (f := Qm m)).symm θ
    have hsum : (∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r (deriv (Qm m)) θ)
        = ∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) (Qm m) θ :=
      Finset.sum_congr rfl fun r _ => by rw [hstep r]
    rw [hexp, hsum]
    calc |∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) (Qm m) θ|
        ≤ ∑ r ∈ Finset.range (i + 1),
            |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
              * iteratedDeriv (r + 1) (Qm m) θ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range (i + 1),
            (KB (i, r) * C₀ (r + 1)) * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
          apply Finset.sum_le_sum
          intro r hr
          have hrle : r ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hr8 : r + 1 ≤ 8 := by omega
          rw [abs_mul]
          have h1 : |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ| ≤ KB (i, r) := by
            refine le_trans (hKB (i, r) θ) ?_
            exact mul_le_of_le_one_right (le_of_lt (hKBpos (i, r)))
              (abs_sin_two_pow_le_one r θ)
          have h2 : |iteratedDeriv (r + 1) (Qm m) θ|
              ≤ C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2) :=
            hC₀ m hm (r + 1) hr8 θ hθ
          have h3 : (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2)
              ≤ (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
            apply pow_le_pow_right₀ hbase
            omega
          calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ|
                * |iteratedDeriv (r + 1) (Qm m) θ|
              ≤ KB (i, r) * (C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2)) :=
                mul_le_mul h1 h2 (abs_nonneg _) (le_of_lt (hKBpos (i, r)))
            _ ≤ KB (i, r) * (C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * i + 4)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h3 (hC₀nn (r + 1)))
                  (le_of_lt (hKBpos (i, r)))
            _ = (KB (i, r) * C₀ (r + 1)) * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by ring
      _ = (∑ r ∈ Finset.range (i + 1), KB (i, r) * C₀ (r + 1))
            * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
          rw [Finset.sum_mul]

end Work.FTS.PhiStar.FlatWAux
end
end
