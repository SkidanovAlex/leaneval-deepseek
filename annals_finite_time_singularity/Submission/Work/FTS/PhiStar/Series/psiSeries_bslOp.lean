import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.BslOp.Setup
import Submission.Work.FTS.PhiStar.Series.Deleg.psiExpansion
import Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.Main
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ChiaContDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open scoped Real Topology BigOperators ContDiff
open MeasureTheory Set Filter

/-- **The `Lzero`-identity of two consecutive angular profiles.**

`Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ = -f''(θ) + (tan θ·f)'(θ) - 6 f(θ)`, and on
`(0, π/2)` one has

  `Lzero (chia ψ (j+1)) = chia ψ j`,

i.e. the resummed angular profiles are successively the `Lzero`-images of one another.  This is
the identity that lets `MomentChiaAux.LzeroBootstrap` upgrade the (finitely many) angular
derivatives of `MomentChia` to derivatives of every order.

The proof is the one used in `MomentChia`: on `(0, π/2)` the profile `chia ψ (j+1)` is the
`eFam`-series with coefficients `bco ψ (j+1) m = bmode m ψ·λ_m^{-(j+1)}`
(`MomentChiaAux.chia_eq_tsum_bco`), `Lzero` acts on that series as
`MomentChiaAux.SeriesOde` describes, and the resulting source series
`Σ_m (bco ψ (j+1) m · λ_m) e_m` is `chia ψ j` because `bco ψ (j+1) m·λ_m = bco ψ j m` for
`m ≥ 1` (`MomentChiaAux.bco_succ_mul_lam`) while the `m = 0` term vanishes on both sides
(`λ_0 = 0`, resp. `bmode 0 ψ = 0` from the vanishing moment); for `j = 0` the source is `ψ`
itself, by the expansion `MomentChiaAux.BmodeExpansionSelf`. -/
lemma chia_Lzero_succ (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ j : ℕ, j + 1 ≤ J → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Elliptic.Lzero (fun _ θ' => chia ψ (j + 1) θ') 0 θ = chia ψ j θ := by
  intro j _ θ hθ
  have hj1 : 1 ≤ j + 1 := by omega
  obtain ⟨hcs, hds⟩ := MomentChiaAux.CoefSummable ψ hdec (j + 1) hj1
  obtain ⟨-, hLzero⟩ := MomentChiaAux.SeriesOde (MomentChiaAux.bco ψ (j + 1))
    (fun m => MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
    (fun m => rfl) hcs hds
  have hEqOn : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      chia ψ (j + 1) θ' = ∑' m : ℕ,
        MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.eFam m θ' :=
    fun θ' hθ' => MomentChiaAux.chia_eq_tsum_bco ψ hj1 hθ'
  have hL : Work.Elliptic.Lzero (fun _ θ' => chia ψ (j + 1) θ') 0 θ
      = ∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
    refine (MomentChiaAux.Lzero_congr_of_eventuallyEq ?_).trans (hLzero θ hθ)
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨Set.Ioo 0 (Real.pi / 2), isOpen_Ioo.mem_nhds hθ, fun θ' hθ' => hEqOn θ' hθ'⟩
  rw [hL]
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 :=
      MomentChiaAux.bmode_zero_of_moment' hmom
    have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ 1 m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      refine tsum_congr (fun m => ?_)
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [MomentChiaAux.bco_apply_zero ψ le_rfl, zero_mul, hb0]
      · rw [MomentChiaAux.bco_one_mul_lam (ψ := ψ) hm]
    rw [htsum]
    exact (MomentChiaAux.BmodeExpansionSelf ψ hdec hgr (hsm 0).continuousOn hbdd hmom θ hθ).trans
      (chia_zero (MomentChiaAux.s2_ne_zero_of_mem_Ioo hθ)).symm
  · have htsum : (∑' m : ℕ, (MomentChiaAux.bco ψ (j + 1) m * Work.FTS.PhiStar.Gegenbauer.lam m)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = ∑' m : ℕ, MomentChiaAux.bco ψ j m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
      refine tsum_congr (fun m => ?_)
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp only [MomentChiaAux.bco_apply_zero ψ hj1, zero_mul,
          MomentChiaAux.bco_apply_zero ψ hjpos]
      · rw [MomentChiaAux.bco_succ_mul_lam (ψ := ψ) (j := j) hm]
    rw [htsum, ← MomentChiaAux.chia_eq_tsum_bco ψ hjpos hθ]

theorem ChiaContDiffOn (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ (j : ℕ), j ≤ Work.FTS.PhiStar.FlatWAux.J → ∀ (n : ℕ),
      ContDiffOn ℝ n (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
  -- `MomentChia` already gives `C^8`, which furnishes all the low orders
  obtain ⟨hC8, -, -⟩ := MomentChia ψ hdec hgr hsm hbdd hmom
  have hOde := chia_Lzero_succ ψ hdec hgr hsm hbdd hmom
  -- and the ODE `Lzero (chia ψ (j+1)) = chia ψ j` unlocks `LzeroBootstrap`
  have main : ∀ n : ℕ, ∀ j : ℕ, j ≤ J →
      ContDiffOn ℝ n (chia ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjJ
      by_cases hn : n ≤ 8
      · exact (hC8 j hjJ).of_le (by exact_mod_cast hn)
      · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · -- `j = 0`: `chia ψ 0 = ψ` on the open interval
          subst hj0
          exact (hsm n).congr
            (fun θ hθ => chia_zero (MomentChiaAux.s2_ne_zero_of_mem_Ioo hθ))
        · -- `j = j' + 1`: one more derivative from the ODE
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          have hj'J : j' + 1 ≤ J := by omega
          have hf : ContDiffOn ℝ (n - 1) (chia ψ (j' + 1)) (Set.Ioo 0 (Real.pi / 2)) :=
            ih (n - 1) (by omega) (j' + 1) (by omega)
          have hh : ContDiffOn ℝ ((n - 1) - 1) (chia ψ j') (Set.Ioo 0 (Real.pi / 2)) :=
            ih ((n - 1) - 1) (by omega) j' (by omega)
          have hb := MomentChiaAux.LzeroBootstrap (m := n - 1) (by omega) hf hh
            (fun θ hθ => hOde j' hj'J θ hθ)
          have hcast : (((n - 1 : ℕ)) : ℕ∞ω) + 1 = (n : ℕ∞ω) := by
            have h : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
            exact_mod_cast h
          rw [← hcast]
          exact hb
  intro j hjJ n
  exact main n j hjJ

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.Fam1Id =====
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

/-- `(∑' m, f m) / c = ∑' m, f m / c`. -/
private lemma tsum_div_tsum (f : ℕ → ℝ) (c : ℝ) : (∑' m : ℕ, f m) / c = ∑' m : ℕ, f m / c := by
  rw [div_eq_mul_inv]
  exact (tsum_mul_right (f := f) (a := c⁻¹)).symm

/-- **The identity of `Fam1Id` in the form in which it is proved**: the three ingredients that
are proved separately (`iteratedDeriv_resc_expansion` for the `1/λ_m`-expansion of the rescaled
radial Green function under `∂_z^k`, and the two summability criteria for the resummed angular
series) are carried as explicit hypotheses. -/
theorem Fam1Id_aux (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) (k : ℕ) (hk : k ≤ 7)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (VocabO.phiA α) z'') z'| ≤ C / Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z'') z'| ≤ C / Gegenbauer.lam m)
    (hD2 : ∀ m : ℕ, 1 ≤ m →
      iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
        = (∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
              * iteratedDeriv k (fun y => (y + 1) / y * Ajit α j (VocabO.phiA α) y) z)
          + (α ^ J / (Radial.lamR m) ^ J)
              * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
                  (Ajit α J (VocabO.phiA α)) y) z)
    (hSumLead : ∀ j : ℕ, 1 ≤ j → Summable (fun m : ℕ => Series.bmode m ψ
      * ((Radial.lamR m)⁻¹) ^ j * Qm m θ))
    (hSumTail : ∀ (Cg : ℝ), 0 < Cg → ∀ (G : ℕ → ℝ),
      (∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Radial.lamR m) →
      Summable (fun m : ℕ => Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ J * G m * Qm m θ)) :
    (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
  obtain ⟨CrJ, hCrJ, hrbJ'⟩ := hrbJ
  -- the termwise `z`-differentiation of the mode series (`P1`)
  have hMZ := ModeZDeriv α ψ z θ hz hθ hdec hgr hrb k hk
  -- pulling the constant `1/s2 θ` out of the `z`-derivative
  have hstep1 : Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Series.psiSeries α (RemSource α ψ) z' θ') z θ
          / Work.Construction.s2 θ := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
    rw [show (fun y : ℝ => (y + 1) / y * (Series.psiSeries α (RemSource α ψ) y θ
            / Work.Construction.s2 θ))
        = fun y : ℝ => ((y + 1) / y * Series.psiSeries α (RemSource α ψ) y θ)
            / Work.Construction.s2 θ from by funext y; ring]
    exact iteratedDeriv_div_const _ _
  -- the `m`-th summand, written through `bmode` and the rescaled radial Green function
  have hmode : ∀ m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
          * Gegenbauer.eFam m θ')) z θ / Work.Construction.s2 θ
      = (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
          * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
          * Qm m θ := by
    intro m
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    rw [show (fun y : ℝ => (y + 1) / y * (Series.acoeff α m (RemSource α ψ) y
            * Gegenbauer.eFam m θ))
        = fun y : ℝ => Gegenbauer.eFam m θ * ((y + 1) / y * Series.acoeff α m
            (RemSource α ψ) y) from by funext y; ring]
    rw [iteratedDeriv_const_mul_field]
    rw [show (fun y : ℝ => (y + 1) / y * Series.acoeff α m (RemSource α ψ) y)
        = fun y : ℝ => (α ^ 2 * Series.bmode m ψ) * ((y + 1) / y
            * Radial.radGreen α m (VocabO.phiA α) y) from by
          funext y; rw [Series.acoeff_RemSource]; ring]
    rw [iteratedDeriv_const_mul_field]
    simp only [Qm]
    ring
  -- the `λ_m^{-1}`-bound of the remainder radial slot, from the flat hypothesis `hrbJ`
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
          (Ajit α J (VocabO.phiA α)) y) z| ≤ CrJ / Radial.lamR m := by
    intro m hm
    have h := hrbJ' m hm k hk z hz
    have hpow : (1 : ℝ) ≤ (z + 1) ^ k := one_le_pow₀ (by linarith)
    have h1 : |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
          (Ajit α J (VocabO.phiA α)) y) z|
        ≤ |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
            (Ajit α J (VocabO.phiA α)) y) z| := by
      calc |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z|
          = 1 * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by ring
        _ ≤ (z + 1) ^ k * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| :=
              mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ = |(z + 1) ^ k| * |iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by
              rw [abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)]
        _ = |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) y) z| := by rw [abs_mul]
    exact le_trans h1 h
  -- summability of the `j`-th leading series, after multiplication by the constants
  have hSumF : ∀ j ∈ Finset.range J, Summable (fun m : ℕ =>
      (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
            * Ajit α j (VocabO.phiA α) y) z) * Qm m θ) := by
    intro j _
    have hj : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
    have h := hSumLead (j + 1) hj
    refine (h.mul_left ((z + 1) ^ k * α ^ 2 * iteratedDeriv k (fun y => (y + 1) / y
        * Ajit α j (VocabO.phiA α) y) z * α ^ j)).congr (fun m => ?_)
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  -- summability of the remainder series
  have hSumG : Summable (fun m : ℕ =>
      (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ) := by
    have h := hSumTail CrJ hCrJ (fun m => iteratedDeriv k (fun y => (y + 1) / y
        * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) hGbd
    refine (h.mul_left ((z + 1) ^ k * α ^ 2 * α ^ J)).congr (fun m => ?_)
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  -- the remainder series, in the shape of the target
  have htail : (∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
        * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
            * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)
      = α ^ 2 * (α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
    have h1 : ∀ m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
          * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ
        = α ^ 2 * (α ^ J * (Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ J
            * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
      intro m
      rw [div_eq_mul_inv, ← inv_pow]
      ring
    rw [tsum_congr h1, tsum_mul_left, tsum_mul_left]
    rfl
  -- the main chain
  calc (z + 1) ^ k * Work.Spaces.pzIter k
        (fun z' θ' => (z' + 1) / z' * (Series.psiSeries α (RemSource α ψ) z' θ'
          / Work.Construction.s2 θ')) z θ
      = (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * Series.psiSeries α (RemSource α ψ) z' θ') z θ
          / Work.Construction.s2 θ := by
        rw [hstep1]; ring
    _ = (∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
              * Gegenbauer.eFam m θ')) z θ) / Work.Construction.s2 θ := by
        rw [hMZ]
    _ = ∑' m : ℕ, (z + 1) ^ k * Work.Spaces.pzIter k
            (fun z' θ' => (z' + 1) / z' * (Series.acoeff α m (RemSource α ψ) z'
              * Gegenbauer.eFam m θ')) z θ / Work.Construction.s2 θ := by
        rw [tsum_div_tsum]
    _ = ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
            * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y) z
            * Qm m θ := by
        exact tsum_congr (fun m => hmode m)
    _ = ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
            * ((∑ j ∈ Finset.range J, (α ^ j / (Radial.lamR m) ^ (j + 1))
                  * iteratedDeriv k (fun y => (y + 1) / y * Ajit α j (VocabO.phiA α) y) z)
              + (α ^ J / (Radial.lamR m) ^ J)
                  * iteratedDeriv k (fun y => (y + 1) / y * Radial.radGreen α m
                      (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        refine tsum_congr (fun m => ?_)
        by_cases hm : m = 0
        · subst hm; rw [hb0]; ring
        · rw [hD2 m (Nat.one_le_iff_ne_zero.mpr hm)]
    _ = ∑' m : ℕ, ((∑ j ∈ Finset.range J, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
              + (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ) := by
        refine tsum_congr (fun m => ?_)
        rw [mul_add, Finset.mul_sum, add_mul, Finset.sum_mul]
    _ = (∑' m : ℕ, ∑ j ∈ Finset.range J, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rw [Summable.tsum_add (summable_sum hSumF) hSumG]
    _ = (∑ j ∈ Finset.range J, ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                      * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rw [Summable.tsum_finsetSum hSumF]
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z)
              * (∑' m : ℕ, Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ (j + 1) * Qm m θ)))
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
              * ((α ^ j / (Radial.lamR m) ^ (j + 1)) * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z) * Qm m θ)
            = (α ^ 2 * α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z))
                * (∑' m : ℕ, Series.bmode m ψ * ((Radial.lamR m)⁻¹) ^ (j + 1) * Qm m θ) from by
              rw [← tsum_mul_left]
              exact tsum_congr (fun m => by rw [div_eq_mul_inv, ← inv_pow]; ring)]
        ring
    _ = (∑ j ∈ Finset.range J, α ^ 2 * (α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                  * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ))
          + ∑' m : ℕ, (z + 1) ^ k * (α ^ 2 * Series.bmode m ψ)
                  * ((α ^ J / (Radial.lamR m) ^ J) * iteratedDeriv k (fun y => (y + 1) / y
                      * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ := by
        rfl
    _ = α ^ 2 * ((∑ j ∈ Finset.range J,
            α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Ajit α j (VocabO.phiA α) y) z) * Wt ψ (j + 1) θ)
          + α ^ J * (∑' m : ℕ, Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ J
              * ((z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
                * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) z) * Qm m θ)) := by
        rw [← Finset.mul_sum, htail]
        ring

/-- **The identity of the first family, `z`-differentiated.** -/
theorem Fam1Id (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ)
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (hrb : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m)
    (hexp : ∀ m : ℕ, 1 ≤ m → ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z') :
    ∀ k : ℕ, k ≤ 7 →
      (z + 1) ^ k * Work.Spaces.pzIter k
          (fun z' θ' => (z' + 1) / z' * (Work.FTS.PhiStar.Series.psiSeries α
            (Work.FTS.PhiStar.RemSource α ψ) z' θ' / Work.Construction.s2 θ')) z θ
        = α ^ 2 * ((∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
              α ^ j * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                  * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z'') z)
                * Work.FTS.PhiStar.FlatWAux.Wt ψ (j + 1) θ)
            + α ^ Work.FTS.PhiStar.FlatWAux.J
              * (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
                  * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
                  * ((z + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
                      * Work.FTS.PhiStar.Radial.radGreen α m
                          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                            (Work.FTS.VocabO.phiA α)) z'') z)
                  * Work.FTS.PhiStar.FlatWAux.Qm m θ)) := by
  intro k hk
  have hrbJ0 := hrbJ
  obtain ⟨CrJ, hCrJ, hrbJ'⟩ := hrbJ0
  have hGbd : ∀ m : ℕ, 1 ≤ m →
      |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) y) z|
        ≤ CrJ / Work.FTS.PhiStar.Gegenbauer.lam m := by
    intro m hm
    have h := hrbJ' m hm k hk z hz
    have hpow : (1 : ℝ) ≤ (z + 1) ^ k := one_le_pow₀ (by linarith)
    have h1 : |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) y) z|
        ≤ |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
            * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z| := by
      calc |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z|
          = 1 * |iteratedDeriv k (fun y => (y + 1) / y * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) y) z| := by ring
        _ ≤ (z + 1) ^ k * |iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| :=
              mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ = |(z + 1) ^ k| * |iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| := by
              rw [abs_of_pos (pow_pos (by linarith : (0 : ℝ) < z + 1) k)]
        _ = |(z + 1) ^ k * iteratedDeriv k (fun y => (y + 1) / y
              * Work.FTS.PhiStar.Radial.radGreen α m
                (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                  (Work.FTS.VocabO.phiA α)) y) z| := by rw [abs_mul]
    exact le_trans h1 h
  exact Fam1Id_aux α ψ z θ k hk hz hθ hb0 hdec hgr hrb hrbJ
    (fun m hm => Work.FTS.PhiStar.FlatWAux.iteratedDeriv_resc_expansion α m hm k hz
      (fun z' hz' => hexp m hm z' hz'))
    (fun j hj => Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_Qm ψ θ j hj hθ hb0 hdec hgr)
    (fun Cg hCg G hG => Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_G_Qm ψ θ
      Work.FTS.PhiStar.FlatWAux.J (by norm_num [Work.FTS.PhiStar.FlatWAux.J]) hθ hb0 hdec hgr
      Cg hCg G hG)

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.ModeMajorantLop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

noncomputable section

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeMajorantLop`

The `Lop`-weighted companion of `ModeMajorant`: the same `m`-series, but with the angular mode
bound carrying the factor `(2m+1)^(2i+4)` for an `i ≤ 6` (`Lop^i` costs two powers of
`(2m+1)` per application, and the mode bound itself carries `(2m+1)^4`).

With `λ_m = lam m = 2m(2m+5)` and `q_m = √(2m+1)` the `m`-th term of the series is

`Cd / (λ_m q_m) · λ_m^{-J} · (CRG / λ_m) · (CL i · (2m+1)^(2i+4))`
  `= Cd · CRG · CL i · λ_m^{-(J+2)} q_m^{-1} (2m+1)^(2i+4)`,

and since `λ_m ≥ 4m²`, `q_m ≥ 1` and `(2m+1)^(2i+4) ≤ (2m+1)^16 ≤ (3m)^16` for `i ≤ 6`,

`λ_m^{-(J+2)} q_m^{-1} (2m+1)^(2i+4) ≤ (3^16/4^10) · m^{-4} ≤ ((4·3^16/4^10)) · ((m+1)^2)^{-1}`,

so the series is dominated by the summable comparison series `Σ_m ((m+1)^2)^{-1}` with the
constant `Cmaj = 4·3^16/4^10`; the constant of the statement is `K i = Σ_m G i m`
(the supremum of the shape function), so no numerical sharpness is needed.
The term `m = 0` is handled by shifting the index by one (`λ_0 = 0`).
-/

/-- The shape function of the `Lop`-weighted majorant: the `m`-th term of the statement's
series with the three constants `Cd, CRG, CL i` stripped off. -/
private def Gmaj (i m : ℕ) : ℝ :=
  (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
    * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (2 * (m : ℝ) + 1) ^ (2 * i + 4)

/-- The (generous) comparison constant `4·3^16/4^10`. -/
private def Cmaj : ℝ := 4 * (3 : ℝ) ^ 16 / (4 : ℝ) ^ 10

private lemma lam_nonneg_prv (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

private lemma lam_ge_four_sq (m : ℕ) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith


private lemma Gmaj_nonneg (i m : ℕ) : 0 ≤ Gmaj i m := by
  have h0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg_prv m
  have h1 : (0 : ℝ) ≤
      (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹ :=
    inv_nonneg.mpr (mul_nonneg h0 (Real.sqrt_nonneg _))
  have h2 : (0 : ℝ) ≤ ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J :=
    pow_nonneg (inv_nonneg.mpr h0) J
  have h3 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr h0
  have h4 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ (2 * i + 4) :=
    pow_nonneg (by positivity) _
  simp only [Gmaj]
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-- `Gmaj` is the reciprocal-power form of the term: the product of the inverse `λ`-powers
collapses to `λ_m^{-10} = λ_m^{-(J+2)}`. -/
private lemma Gmaj_eq (i m : ℕ) :
    Gmaj i m = (2 * (m : ℝ) + 1) ^ (2 * i + 4)
      / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1)) := by
  simp only [Gmaj, J]
  rw [mul_inv, inv_pow]
  ring_nf

/-- The comparison series `Σ_m ((m+1)^2)^{-1}` is summable. -/
private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-- The pointwise comparison, for `m ≥ 1` and `i ≤ 6`. -/
private lemma Gmaj_le {i m : ℕ} (hm : 1 ≤ m) (hi : i ≤ 6) :
    Gmaj i m ≤ Cmaj * (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hbase : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hlam4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_ge_four_sq m
  have hlam0 : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg_prv m
  -- the numerator: `(2m+1)^(2i+4) ≤ (2m+1)^16 ≤ (3m)^16`
  have hnum : (2 * (m : ℝ) + 1) ^ (2 * i + 4) ≤ (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 := by
    have h1 : (2 * (m : ℝ) + 1) ^ (2 * i + 4) ≤ (2 * (m : ℝ) + 1) ^ 16 :=
      pow_le_pow_right₀ hbase (by omega)
    have h2 : (2 * (m : ℝ) + 1) ^ 16 ≤ (3 * (m : ℝ)) ^ 16 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 16
    rw [mul_pow] at h2
    linarith
  -- the denominator: `λ_m^10 √(2m+1) ≥ (4m²)^10`
  have hden : (4 * (m : ℝ) ^ 2) ^ 10 * 1
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h4 : (4 * (m : ℝ) ^ 2) ^ 10 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hlam4 10
    have h5 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := by positivity
    calc (4 * (m : ℝ) ^ 2) ^ 10 * 1 = (4 * (m : ℝ) ^ 2) ^ 10 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := h4
      _ = (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hs1 h5
  have hdpos1 : (0 : ℝ) < (4 * (m : ℝ) ^ 2) ^ 10 * 1 := by positivity
  have hdpos2 : (0 : ℝ) < (4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2 := by positivity
  have hstep1 : Gmaj i m
      ≤ (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) := by
    rw [Gmaj_eq]
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  -- `(m+1)² ≤ 4m⁴` for `m ≥ 1`
  have hq : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 4 := by
    have h3 : (0 : ℝ) ≤ (3 * (m : ℝ) + 1) * ((m : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hm4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by nlinarith
    nlinarith [h3, hm4]
  have hstep2 : (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1)
      ≤ 4 * (3 : ℝ) ^ 16 / ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2) := by
    rw [div_le_div_iff₀ hdpos1 hdpos2,
      show ((4 : ℝ) * (m : ℝ) ^ 2) ^ 10 * 1 = (4 : ℝ) ^ 10 * (m : ℝ) ^ 20 from by ring]
    have hq16 : (m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2
        ≤ (m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have hfinal : (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2)
        ≤ (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_left hq16 (by positivity)
    calc (3 : ℝ) ^ 16 * (m : ℝ) ^ 16 * ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2)
        = (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * ((m : ℝ) + 1) ^ 2) := by ring
      _ ≤ (3 : ℝ) ^ 16 * (4 : ℝ) ^ 10 * ((m : ℝ) ^ 16 * (4 * (m : ℝ) ^ 4)) := hfinal
      _ = 4 * (3 : ℝ) ^ 16 * ((4 : ℝ) ^ 10 * (m : ℝ) ^ 20) := by ring
  have hconv : Cmaj * (((m : ℝ) + 1) ^ 2)⁻¹
      = 4 * (3 : ℝ) ^ 16 / ((4 : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 2) := by
    simp only [Cmaj, div_eq_mul_inv]
    rw [mul_inv]
    ring
  rw [hconv]
  exact le_trans hstep1 hstep2

private lemma summable_Gmaj {i : ℕ} (hi : i ≤ 6) : Summable (fun m : ℕ => Gmaj i m) := by
  have hmaj : Summable (fun m : ℕ => Cmaj * ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹) := by
    have hsh : Summable (fun m : ℕ => ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹) :=
      (summable_nat_add_iff (f := fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) 1).mpr
        summable_inv_sq_shift
    exact hsh.mul_left Cmaj
  have hshift : Summable (fun m : ℕ => Gmaj i (m + 1)) := by
    refine Summable.of_nonneg_of_le
      (f := fun m : ℕ => Cmaj * ((((m + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹)
      (g := fun m : ℕ => Gmaj i (m + 1))
      (fun m => Gmaj_nonneg i (m + 1)) (fun m => ?_) hmaj
    exact Gmaj_le (m := m + 1) (by omega) hi
  exact (summable_nat_add_iff (f := fun m : ℕ => Gmaj i m) 1).mp hshift

theorem ModeMajorantLop : ∃ K : ℕ → ℝ, (∀ i : ℕ, 0 ≤ K i) ∧
    ∀ (Cd CRG : ℝ), 0 ≤ Cd → 0 ≤ CRG → ∀ (CL : ℕ → ℝ), (∀ i : ℕ, 0 ≤ CL i) →
    ∀ (i : ℕ), i ≤ 6 →
      Summable (fun m : ℕ =>
          Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4))) ∧
      (∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4)))
        ≤ K i * Cd * CRG * (CL i) := by
  refine ⟨fun i => ∑' m : ℕ, Gmaj i m, fun i => tsum_nonneg (fun m => Gmaj_nonneg i m), ?_⟩
  intro Cd CRG _ _ CL _ i hi
  have hGsum : Summable (fun m : ℕ => Gmaj i m) := summable_Gmaj hi
  have hEq : ∀ m : ℕ,
      Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CL i * (2 * (m : ℝ) + 1) ^ (2 * i + 4))
        = Cd * CRG * CL i * Gmaj i m := by
    intro m
    simp only [Gmaj, div_eq_mul_inv]
    ring
  refine ⟨?_, ?_⟩
  · exact (hGsum.mul_left (Cd * CRG * CL i)).congr (fun m => (hEq m).symm)
  · rw [tsum_congr (fun m => hEq m), tsum_mul_left]
    show Cd * CRG * CL i * (∑' m : ℕ, Gmaj i m)
        ≤ (∑' m : ℕ, Gmaj i m) * Cd * CRG * CL i
    exact le_of_eq (by ring)

end

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.psiSeries_bslOp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The mode series solves the elliptic equation.**  This is `psiSeries_bslOp` with the crux
estimates taken as explicit hypotheses. -/
theorem psiSeries_bslOp_of_facts (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : AngModel α ψ)
    (hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3)
    (hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m)
    (hODE : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (gammaFun α m)) z
        - α * (5 + α) * z * deriv (gammaFun α m) z
        + Gegenbauer.lam m * gammaFun α m z = VocabO.phiA α z)
    (hInt : (∀ m : ℕ, ContinuousOn (fun t => cmode m (RemSource α ψ) t) (Set.Ioi 0)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => cmode m (RemSource α ψ) t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)) ∧
      ContinuousOn (VocabO.phiA α) (Set.Ioi 0) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1)) ∧
      (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t => VocabO.phiA α t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)))
    (hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m)
    (hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m))
    (hExp : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) = ψ θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Elliptic.bslOp α (fun z θ => psiSeries α (RemSource α ψ) z θ) z θ
        = RemSource α ψ z θ := by
  intro z hz θ hθ hθ2
  obtain ⟨D, hDpos, hB0, hB1, hB2, hB3, hB4, hB5⟩ :=
    mode_bounds α ψ hα hψ.moment hAng hDec hGamma hInt hterm z hz θ hθ hθ2
  obtain ⟨hPz, hPz2, hPt, hPt2, hPtan, hLzero⟩ :=
    deriv_series α ψ hα hInt hmaj z hz θ hθ hθ2 D hB0 hB1 hB2 hB3 hB4 hB5
  rw [Elliptic.bslOp_apply, hLzero, hPz2, hPz, hPt2, hPtan,
    show psiSeries α (RemSource α ψ) z θ
        = ∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ from rfl]
  -- the mode coefficient of `ψ` vanishes
  have hb0 : bmode 0 ψ = 0 := by
    have hF : Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
      simpa only [Elliptic.Fstar] using hψ.moment
    rw [bmode_eq_cmode 0 ψ 0]
    exact eFam_zero_moment (fun _ θ => ψ θ) hF
  have hac0 : ∀ y : ℝ, acoeff α 0 (RemSource α ψ) y = 0 := by
    intro y
    rw [acoeff_RemSource, hb0]
    ring
  have hdiffA : ∀ m : ℕ,
      (∀ y, 0 < y → HasDerivAt (gammaFun α m) (rgiD1 α m (VocabO.phiA α) y) y) ∧
      (∀ y, 0 < y →
        HasDerivAt (deriv (gammaFun α m)) (deriv (rgiD1 α m (VocabO.phiA α)) y) y) :=
    fun m => hasDerivAt_gammaFun hα m hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m)
  set θu : ℝ := (θ + π / 2) / 2 with hθu
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hsum_of : ∀ (E : ℝ) (f : ℕ → ℝ), (∀ m, |f m| ≤ E * majPow m) → Summable f := by
    intro E f hf
    refine Summable.of_norm_bounded (hmaj E) fun m => ?_
    rw [Real.norm_eq_abs]
    exact hf m
  -- the pointwise identity of the summands
  have hpoint : ∀ m : ℕ,
      (-(α ^ 2 * z ^ 2)) * (deriv (deriv (acoeff α m (RemSource α ψ))) z
          * Gegenbauer.eFam m θ)
        + (-(α * (5 + α) * z)) * (deriv (acoeff α m (RemSource α ψ)) z
          * Gegenbauer.eFam m θ)
        + ((-1) * (acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
            + 1 * (acoeff α m (RemSource α ψ) z
              * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
            + (-6) * (acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ))
      = cmode m (RemSource α ψ) z * Gegenbauer.eFam m θ := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hz0 : acoeff α 0 (RemSource α ψ) = fun _ => (0 : ℝ) := funext hac0
      have hd1 : deriv (acoeff α 0 (RemSource α ψ)) = fun _ => (0 : ℝ) := by
        rw [hz0]; simp
      have hd2 : deriv (deriv (acoeff α 0 (RemSource α ψ))) = fun _ => (0 : ℝ) := by
        rw [hd1]; simp
      simp only [hz0, hd1, hd2, cmode_RemSource, hb0, Pi.zero_apply]
      simp
    · have h1 : deriv (acoeff α m (RemSource α ψ)) z
          = α ^ 2 * bmode m ψ * deriv (gammaFun α m) z := by
        rw [deriv_acoeff m (hdiffA m).1 z hz, (hdiffA m).1 z hz |>.deriv]
      have h2 : deriv (deriv (acoeff α m (RemSource α ψ))) z
          = α ^ 2 * bmode m ψ * deriv (deriv (gammaFun α m)) z := by
        rw [deriv_deriv_acoeff m (hdiffA m).1 (hdiffA m).2 z hz, (hdiffA m).2 z hz |>.deriv]
      have h3 : acoeff α m (RemSource α ψ) z = α ^ 2 * bmode m ψ * gammaFun α m z := by
        rw [acoeff_RemSource]
      rw [h1, h2, h3, cmode_RemSource]
      linear_combination (α ^ 2 * bmode m ψ * Gegenbauer.eFam m θ) * hODE m hm z hz
        + (α ^ 2 * bmode m ψ * gammaFun α m z)
          * eFam_lzero_deriv m hcosθ z
  -- summability of the five families
  have hsumF1 : Summable fun m : ℕ =>
      deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB2 m z hz)
  have hsumF2 : Summable fun m : ℕ =>
      deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB1 m z hz)
  have hsumF3 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ :=
    hsum_of D _ (fun m => by
      rw [abs_mul]
      exact hB4 m θ (by linarith [hθ]) (by linarith [hθ2]))
  have hsumF4 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ :=
    hsum_of D _ (fun m => by
      rw [abs_mul]
      exact hB5 m θ (by linarith [hθ]) (by linarith [hθ2]))
  have hsumF5 : Summable fun m : ℕ =>
      acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ :=
    hsum_of D _ (fun m => by rw [abs_mul]; exact hB0 m z hz)
  -- normalise the linear combination of sums
  have hnorm : (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ,
          deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
        - (α * (5 + α) * z) * (∑' m : ℕ,
            deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
        + (-(∑' m : ℕ, acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
            + (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
            - 6 * (∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ))
      = (-(α ^ 2 * z ^ 2)) * (∑' m : ℕ,
            deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
          + (-(α * (5 + α) * z)) * (∑' m : ℕ,
              deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
          + ((-1) * (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
              + 1 * (∑' m : ℕ, acoeff α m (RemSource α ψ) z
                  * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
              + (-6) * (∑' m : ℕ, acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ)) := by
    ring
  rw [hnorm,
    tsum_lincomb5 (-(α ^ 2 * z ^ 2)) (-(α * (5 + α) * z)) (-1) 1 (-6)
      (fun m => deriv (deriv (acoeff α m (RemSource α ψ))) z * Gegenbauer.eFam m θ)
      (fun m => deriv (acoeff α m (RemSource α ψ)) z * Gegenbauer.eFam m θ)
      (fun m => acoeff α m (RemSource α ψ) z * iteratedDeriv 2 (Gegenbauer.eFam m) θ)
      (fun m => acoeff α m (RemSource α ψ) z
        * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
      (fun m => acoeff α m (RemSource α ψ) z * Gegenbauer.eFam m θ)
      hsumF1 hsumF2 hsumF3 hsumF4 hsumF5,
    tsum_congr hpoint]
  -- identify the source
  rw [show (∑' m : ℕ, cmode m (RemSource α ψ) z * Gegenbauer.eFam m θ)
      = (α ^ 2 * VocabO.phiA α z) * (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) from by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => by rw [cmode_RemSource]; ring]
  rw [hExp θ hθ hθ2]
  rfl

/-- The mode series `psiSeries α (RemSource α ψ)` solves `bslOp α Ψ = RemSource α ψ`. -/
theorem psiSeries_bslOp :
    ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
        Work.Elliptic.bslOp α
            (fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
            z θ = Work.FTS.PhiStar.RemSource α ψ z θ := by
  intro α ψ hα hα5 hψ
  -- the angular bounds, re-associated
  have hAng : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Gegenbauer.eFam m θ| ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) ∧
      |deriv (Gegenbauer.eFam m) θ|
        ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2 ∧
      |iteratedDeriv 2 (Gegenbauer.eFam m) θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 4 ∧
      |deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ|
        ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3 :=
    fun m θ hθ => ⟨Deleg.psiAngBounds.1 m θ hθ, Deleg.psiAngBounds.2.1 m θ hθ,
      Deleg.psiAngBounds.2.2.1 m θ hθ, Deleg.psiAngBounds.2.2.2 m θ hθ⟩
  -- the coefficient decay
  obtain ⟨Cd, hCdpos, hCd⟩ := bmode_decay15
  have hDec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
    ⟨Cd, hCdpos, fun m hm => hCd α ψ hα hα5 hψ m hm⟩
  -- the integrability of the kernels
  have hInt := Deleg.psiSeriesIntegrability α hα ψ
  -- the radial facts
  obtain ⟨Kφ, hKφ0, hKφ⟩ := (Deleg.psiRadFacts α hα hα5).1
  obtain ⟨Crb, hCrbpos, hRadB⟩ := (Deleg.psiRadFacts α hα hα5).2.1
  have hRadODE := (Deleg.psiRadFacts α hα hα5).2.2
  have hphiAsmooth : ContDiffOn ℝ 22 (VocabO.phiA α) (Set.Ioi 0) :=
    fun z hz => (Work.FTS.PhiStar.contDiffAt_phiA_of α 22 hz).contDiffWithinAt
  have hGamma : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
      |iteratedDeriv k (gammaFun α m) z| ≤ C / Gegenbauer.lam m := by
    refine ⟨Crb * (Kφ + 1), by positivity, fun m hm k hk z hz => ?_⟩
    have h := hRadB m (VocabO.phiA α) Kφ hKφ0 hm hphiAsmooth hKφ k hk z hz
    have h2 : Crb * Kφ / Gegenbauer.lam m ≤ Crb * (Kφ + 1) / Gegenbauer.lam m := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt (lam_pos hm))
      linarith
    calc |iteratedDeriv k (gammaFun α m) z|
        = |iteratedDeriv k (Radial.radGreen α m (VocabO.phiA α)) z| := rfl
      _ ≤ Crb * Kφ / Gegenbauer.lam m := h
      _ ≤ Crb * (Kφ + 1) / Gegenbauer.lam m := h2
  have hODE : ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (gammaFun α m)) z
        - α * (5 + α) * z * deriv (gammaFun α m) z
        + Gegenbauer.lam m * gammaFun α m z = VocabO.phiA α z := by
    intro m hm z hz
    have h := hRadODE m (VocabO.phiA α) hInt.2.2.2.1 (hInt.2.2.2.2.1 m) (hInt.2.2.2.2.2 m) z hz
    simpa only [gammaFun, Radial.lamR, Gegenbauer.lam] using h
  -- the majorant
  have hmaj : ∀ D : ℝ, Summable fun m : ℕ => D * majPow m := by
    intro D
    exact (Deleg.rpowMajorant.2.1 D).congr (fun m => by rw [majPow])
  -- the arithmetic shapes
  have hterm : ∀ (Cdec CBz Kφ : ℝ), 0 < Cdec → 0 < CBz → 0 < Kφ → ∀ cθ : ℝ, 0 < cθ →
      ∃ D : ℝ, 0 < D ∧ ∀ m : ℕ, 1 ≤ m →
        let L := (Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
        (α ^ 2 * Cdec * CBz * Kφ / L * (3 * ((m : ℝ) + 1)) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (900 * ((m : ℝ) + 1) ^ 2 / cθ ^ 2) ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (27000 * ((m : ℝ) + 1) ^ 3 / cθ ^ 4)
            ≤ D * majPow m) ∧
        (α ^ 2 * Cdec * CBz * Kφ / L * (9000 * ((m : ℝ) + 1) ^ 2 / cθ ^ 3)
            ≤ D * majPow m) := by
    intro Cdec CBz Kφ h1 h2 h3 cθ h4
    obtain ⟨D, hDpos, hDsh⟩ := Deleg.termEstimates α hα Cdec CBz Kφ h1 h2 h3 cθ h4
    refine ⟨D, hDpos, fun m hm => ?_⟩
    have h := hDsh m hm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [majPow]; exact h.1
    · rw [majPow]; exact h.2.1
    · rw [majPow]; exact h.2.2.1
    · rw [majPow]; exact h.2.2.2
  -- the eigen-expansion of ψ
  have hExp : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      (∑' m : ℕ, bmode m ψ * Gegenbauer.eFam m θ) = ψ θ :=
    Deleg.psiExpansion α ψ hα hα5 hψ
      ⟨Cd, hCdpos, fun m hm => hCd α ψ hα hα5 hψ m hm⟩
      (fun m θ hθ => Deleg.psiAngBounds.1 m θ hθ)
  exact psiSeries_bslOp_of_facts α ψ hα hα5 hψ hAng hDec hGamma hODE hInt hmaj hterm hExp

end Work.FTS.PhiStar.Series
end
end
