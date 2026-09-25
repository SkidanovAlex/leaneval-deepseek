import Mathlib
import Submission.Work.Maximal.mstWideAux
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift
import Submission.Work.Maximal.mst_lrs_base
import Submission.Work.Maximal.mstWideLrBump_coeff_l1
import Submission.Work.Maximal.mstWideLrBump_fourierCoeff
import Submission.Work.BourgainPlan.Maximal.mstHat_decay
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff

/-!
# The unweighted wide arc sum `Π̃_s` is an `ℓʳ`-multiplier with a constant uniform in `s`

This module proves `Work.Maximal.mstWideLrPi_lr`: the multiplier with the symbol
`Π̃_s = Σ_{β ∈ 𝒰(s+1) ∖ 𝒰(s)} ϱ_s(· − β)` (the *unweighted* wide arc sum of MST
arXiv:1512.07518, `mstWidePi`) is bounded on `ℓʳ(ℤ)`, `1 < r < ∞`, with a constant `C`
**independent of the level `s`**.

The two regimes are distinct.

* For **large `s`** the wide bump `ϱ_s = η(c_s ·)`, `c_s = mstWideC P s = (Q_s)^{3d}`, is
  *narrower* than the Ionescu–Wainger ball `iwEps (mstRho l) ((s+1)^l) = exp(−(s+1)^{1/10})`
  (`mstWideLrPi_narrow`, from `mstLrScale ≤ mstWideC` and `inv_two_mul_two_rpow_lt_exp`), and its
  fundamental-domain lift has the Mikhlin data of `η` (`mstWideBump_mikhlin`, uniform in `s`).
  Hence `IWSupersetBoundLift` applies to the two supersets `𝒰(s+1) = iwSigma (mstRho l) ((s+1)^l)`
  and `𝒰(s) = iwSigma (mstRho l) (s^l)`, with the *same* small parameter `iwEps … ((s+1)^l)` and
  the *same* constant `Ciw · M`, and the annulus operator is the difference
  (`lrs_opArc_sdiff`): the bound is `2 · (Ciw · M)`, uniform in `s`.

* For **small `s`** (finitely many levels) no uniformity is needed: the operator is the
  convolution with the coefficient kernel of the arc symbol, so the trivial Young bound gives the
  constant `♯(𝒰(s+1) ∖ 𝒰(s)) · K`, with `K` the *uniform* `ℓ¹`-mass of the Fourier coefficients of
  a single wide bump (`mstWideLrBump_coeff_l1`, from the dilation dictionary
  `mstWideLrBump_fourierCoeff` and the shifted-lattice sampling bound `mstHat_sampling_bound`).
  These finitely many constants are absorbed into the final `C`.
-/

set_option maxHeartbeats 2000000

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

noncomputable section

open Work.BourgainPlan.Maximal (mstRho mstU mstLevel mstScale mstScale_pos mstScale_apply
  iwEps iwSigma iwRep mstEta mstHat mstU_apply mstLevel_succ mstLevel_mono mstRho_pow_eq
  norm_eq_abs_iwRep exists_rpow_ten_add_one_lt inv_two_mul_two_rpow_lt_exp mstHat_bound mstHat_decay)

/-- **The wide bump is supported in the Ionescu–Wainger ball of level `s`** for large `s`:
`ϱ_s = η(c_s ·)` vanishes off the ball of radius `1/(2c_s)` (`mstWideBump_memLp_and_narrow`), and
for large `s` one has `1/(2 c_s) ≤ exp(−(s+1)^{1/10}) = iwEps (mstRho l) ((s+1)^l)` because
`c_s = (Q_s)^{3d} ≥ 2^{s(d−χ)}` (`mstLr_mstScale_le_mstWideC`) and
`2^{−s(d−χ)} < 2 exp(−(s+1)^{1/10})` (`inv_two_mul_two_rpow_lt_exp`). -/
theorem mstWideLrPi_narrow (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (hl : 1 ≤ l)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ ξ : Circ,
      iwEps (mstRho l) ((s + 1) ^ l) < ‖ξ‖ → mstWideBump P χ η s ξ = 0 := by
  have hσ : 0 < (P.natDegree : ℝ) - χ := by
    have h1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.natDegree)
    linarith
  obtain ⟨s₁, hs₁⟩ := Work.BourgainPlan.Maximal.exists_rpow_ten_add_one_lt
    ((P.natDegree : ℝ) - χ) hσ
  have hχd : χ ≤ (P.natDegree : ℝ) := by
    have h1 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨s₂, hs₂⟩ := mstLr_mstScale_le_mstWideC P hd hχ0.le hχd
  refine ⟨max s₁ s₂, fun s hs ξ hξ => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : s₂ ≤ s := le_trans (le_max_right _ _) hs
  have hlt : 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)))
      < Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) :=
    Work.BourgainPlan.Maximal.inv_two_mul_two_rpow_lt_exp (hs₁ s hs1)
  have hE : iwEps (mstRho l) ((s + 1) ^ l)
      = Real.exp (-(((s : ℝ) + 1) ^ (1 / 10 : ℝ))) := by
    rw [iwEps, Work.BourgainPlan.Maximal.mstRho_pow_eq l hl (s + 1) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hE] at hξ
  rw [Work.BourgainPlan.Maximal.norm_eq_abs_iwRep] at hξ
  have hsc : mstScale P.natDegree χ s ≤ mstWideC P s := hs₂ s hs2
  have hms : 0 < mstScale P.natDegree χ s := mstScale_pos _ _ _
  have hwpos : 0 < mstWideC P s := lt_of_lt_of_le one_pos (one_le_mstWideC P s)
  rw [mstWideBump_apply]
  by_contra hne
  have hlt2 : |mstWideC P s * iwRep ξ| < 1 / 2 := by
    by_contra hcon
    exact hne (hηsup _ (not_lt.mp hcon))
  rw [abs_mul, abs_of_pos hwpos] at hlt2
  have hlt3 : |iwRep ξ| < 1 / (2 * mstWideC P s) := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * mstWideC P s)]
    nlinarith [hlt2]
  have hmono : 1 / (2 * mstWideC P s)
      ≤ 1 / (2 * (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h2 : (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) ≤ mstScale P.natDegree χ s := by
      rw [mstScale_apply]
    linarith
  linarith

theorem mstWideLrPi_lr (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℕ) (g : ℤ →₀ ℂ),
      MeasureTheory.eLpNorm (fun m : ℤ => Work.BourgainPlan.IonescuWainger.opMul
          (Work.Maximal.mstLrPiCls P l χ η hηc.continuous hηsup s)
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x hx.le
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχd : χ ≤ (P.natDegree : ℝ) := by
    have h1 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hρ : 0 < mstRho l := by
    rw [mstRho]
    have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 0 < l)
    positivity
  -- ## The three inputs
  -- the Ionescu–Wainger bound over the supersets `Σ_N`, uniformly in `N`
  obtain ⟨Ciw, hCiwpos, N₁, hN₁⟩ :=
    Work.BourgainPlan.Maximal.iwSupersetBoundLift_proof (mstRho l) hρ r hr
  -- the uniform `ℓ¹`-mass of the Fourier coefficients of the wide bump
  have hcd0 : ContDiff ℝ 2
      (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η 0)) := by
    rw [lrs_circleLift_mstEta_zero P.natDegree χ η hηsup]
    exact hηc.comp (by fun_prop)
  obtain ⟨Ec, hEc0, hdec⟩ :=
    Work.BourgainPlan.Maximal.mstHat_decay (d := P.natDegree) (χ := χ) η hcd0
  obtain ⟨K, hKpos, hK⟩ := mstWideLrBump_coeff_l1 P χ η hM.le hEc0
    (Work.BourgainPlan.Maximal.mstHat_bound hM.le hηbd) hdec
    (fun s m => by
      simpa only [mstWideBump_apply] using
        mstWideLrBump_fourierCoeff (c := mstWideC P s) (one_le_mstWideC P s) hη2 m)
  -- the narrowness of the wide bump in the large-scale regime
  obtain ⟨Sn, hSn⟩ := mstWideLrPi_narrow P hd l hl hχ0 hχ1 η hηsup
  -- ## The thresholds
  set S : ℕ := max (max N₁ Sn) 1 with hSdef
  have hSN₁ : N₁ ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
  have hSSn : Sn ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
  have hS1 : 1 ≤ S := le_max_right (max N₁ Sn) 1
  set Ck : ℝ := ∑ t ∈ Finset.range S, (((mstAnnulus l t).card : ℕ) : ℝ) * K with hCkdef
  have hCknn : 0 ≤ Ck := by
    rw [hCkdef]
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (Nat.cast_nonneg _) hKpos.le)
  have hClpos : 0 < 2 * (Ciw * M) := by positivity
  refine ⟨2 * (Ciw * M) + Ck + 1, by linarith, fun s g => ?_⟩
  have hgl : Memℓp (⇑g : ℤ → ℂ) 2 := Work.BourgainPlan.IonescuWainger.memℓp_finsupp g
  have hψml : MemLp (mstWideBump P χ η s) ⊤ haarT :=
    mstLrBump_memLp P χ η hηc.continuous hηsup s
  set Nf : ℝ≥0∞ :=
    MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count with hNfdef
  change MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
      hψml (mstAnnulus l s) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (Ciw * M) + Ck + 1) * Nf
  by_cases hs : S ≤ s
  · -- ===================== large scales: Ionescu–Wainger =====================
    have hsN₁ : N₁ ≤ s := le_trans hSN₁ hs
    have hsSn : Sn ≤ s := le_trans hSSn hs
    have hNle1 : N₁ ≤ (s + 1) ^ l :=
      le_trans (le_trans hsN₁ (Nat.le_succ s)) (Nat.le_self_pow (by omega : l ≠ 0) (s + 1))
    have hNle2 : N₁ ≤ s ^ l := le_trans hsN₁ (Nat.le_self_pow (by omega : l ≠ 0) s)
    obtain ⟨hcd, hbd, hder, hder2⟩ :=
      mstWideBump_mikhlin P χ η M hM.le hηc hηbd hder1 hder2 hηsup s
    have hsupp : ∀ ξ : Circ, iwEps (mstRho l) ((s + 1) ^ l) < ‖ξ‖ →
        mstWideBump P χ η s ξ = 0 := hSn s hsSn
    have hεmono : iwEps (mstRho l) ((s + 1) ^ l) ≤ iwEps (mstRho l) (s ^ l) := by
      rw [iwEps, iwEps, Real.exp_le_exp, neg_le_neg_iff]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (Nat.pow_le_pow_left (by omega) l)) hρ.le
    -- the superset bound, with the small parameter `ε = iwEps ρ ((s+1)^l)` in both cases
    have hstep : ∀ N : ℕ, N₁ ≤ N → iwEps (mstRho l) ((s + 1) ^ l) ≤ iwEps (mstRho l) N →
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
            hψml (iwSigma (mstRho l) N) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Ciw * M) * Nf := by
      intro N hN hεle
      have h := hN₁ N hN (ε := iwEps (mstRho l) ((s + 1) ^ l)) (Real.exp_pos _) hεle
        (mstWideBump P χ η s) hψml hcd (A := M) hM.le hbd hder hder2 hsupp (⇑g) hgl
      exact Work.BourgainPlan.Maximal.eLpNorm_le_of_lintegral_rpow_le_count (q := r) (C := Ciw * M)
        (lt_trans zero_lt_one hr) (mul_nonneg hCiwpos.le hM.le) h
    have hb1 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
        hψml (mstU l (s + 1)) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * M) * Nf := by
      simpa only [mstU_apply] using hstep ((s + 1) ^ l) hNle1 le_rfl
    have hb2 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
        hψml (mstU l s) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * M) * Nf := by
      simpa only [mstU_apply] using hstep (s ^ l) hNle2 hεmono
    have hb1' : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
        hψml (mstLevel l (s + 1)) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * M) * Nf := by
      rw [mstLevel_succ]; exact hb1
    have hb2' : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s)
        hψml (mstLevel l s) (⇑g) hgl) (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * M) * Nf := by
      have hsne : s ≠ 0 := by omega
      have hEs : mstLevel l s = mstU l s := by rw [mstLevel, if_neg hsne]
      rw [hEs]; exact hb2
    have hsdiff : Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s) hψml
        (mstAnnulus l s) (⇑g) hgl
        = Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s) hψml
            (mstLevel l (s + 1)) (⇑g) hgl
          - Work.BourgainPlan.IonescuWainger.opArc (mstWideBump P χ η s) hψml
            (mstLevel l s) (⇑g) hgl := by
      rw [mstAnnulus]
      exact lrs_opArc_sdiff hψml (mstLevel_mono l s) (⇑g) hgl
    rw [hsdiff]
    refine (eLpNorm_sub_le (ENNReal.one_le_ofReal.mpr hr.le)).trans ?_
    refine (add_le_add hb1' hb2').trans ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    linarith
  · -- ===================== small scales: the coefficient (Young) bound =====================
    have hslt : s < S := lt_of_not_ge hs
    obtain ⟨hcsum, hcK⟩ := hK s
    have hop := Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff (p := r) hr.le (φ := mstWideBump P χ η s)
      hψml (c := fun m : ℤ => ∫ ξ : Circ, mstWideBump P χ η s ξ * star (fourier m ξ) ∂haarT)
      hcsum (fun n => rfl) hcK (mstAnnulus l s) (⇑g) hgl
    refine hop.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hsingle : (((mstAnnulus l s).card : ℕ) : ℝ) * K ≤ Ck := by
      rw [hCkdef]
      refine Finset.single_le_sum (f := fun t : ℕ => (((mstAnnulus l t).card : ℕ) : ℝ) * K)
        (fun t _ => mul_nonneg (Nat.cast_nonneg _) hKpos.le) (Finset.mem_range.mpr hslt)
    linarith

end

end Work.Maximal
