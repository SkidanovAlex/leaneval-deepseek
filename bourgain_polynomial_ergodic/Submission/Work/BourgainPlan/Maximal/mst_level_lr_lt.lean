import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mst_lvl_assembly
import Submission.Work.BourgainPlan.Maximal.mst_lvl_triv
import Submission.Work.BourgainPlan.Maximal.mst_lvl_base_lp
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err
import Submission.Work.BourgainPlan.Maximal.mz_finsupp_sqfun
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

/-- MST Thm 7 (Mirek-Stein-Trojan, arXiv:1512.07518, §4.4): the `ℓᵖ` level bound for the level model `ν^s` on the small scales `k ≤ 2^{κ_s}`, conditional on the named input `MSTThetaBound` (`Maximal/mst_theta_defs.lean`, MST's `(C2)`): `‖sup_{k ≤ 2^{κ_s}}|F⁻¹(ν^s_{2^k}ĝ)|‖_{ℓᵖ} ≤ C (s+1) log(s+2) ‖g‖_{ℓᵖ}`.

`p > 1` is arbitrary and `r₀ ≥ 2` is the Ionescu–Wainger endpoint exponent with `p ∈ [(2r₀)', 2r₀]`, so that the arc-sum multiplier bound comes from `iwEndpoint2r`/`iwRangeBound` (`Maximal/iw_superset.lean`, proved in `iw_superset_bound.lean` / `iwRangeBound_of_endpoint.lean`), whose hypotheses are the multiplier norms `IWMult r₀` — supplied for the signed symbols by `MSTThetaBound` (with the bump data `ContDiff ℝ 2 η`, `‖η‖ ≤ M`, `|x|‖η'‖ ≤ M`, `|x|²‖η''‖ ≤ M`, `η = 0` for `|x| > 1/2` that the statement carries).

Route (`J := ⌊exp((s+1)^{1/2})⌋`, `μ_J := polyWeylKernel P J`): (i) `major_arc_nbd_bound` at scale `J` gives `‖μ_J(ξ) − G(a/q)‖ ≤ e^{−(s+1)^{1/2}/2}` on each level-`s` arc (with `polyProfile_sub_one_le` for `Φ_J(ξ−a/q) = 1 + O(e^{(s+1)^{1/2}}2^{−s(1−χ)})`); summing over the `≤ e^{(s+1)^{1/10}}` arcs and interpolating the `ℓ²`/`ℓᵖ` bounds gives `‖ν^s_{2^k} − μ_J Π^s_{2^k}‖_{ℓᵖ} ≲ e^{−c(s+1)^{1/2}}`, summable over `k ≤ 2^{κ_s}` since `2^{κ_s} = exp(O((s+1)^{1/10}))`; (ii) for `μ_J Π^s` use that `‖M_J‖_r ≤ 1` for all `r` (the discrete average is a contraction) and apply `rmELpNormSupLe` together with Khintchine (`khintchine_hilbert`) to reduce to the signed sums, which telescope (`Σ_{m∈I_j}(Φ_{2^{m+1}} − Φ_{2^m}) = Φ_{2^{(j+1)2^i}} − Φ_{2^{j2^i}}`) to the single operator with symbol `Θ_ε·η_s = mstThetaSym`; (iii) bound that operator on the annulus `mstU l (s+1) ∖ mstU l s` (a *difference* of two arc sums) by two applications of the Ionescu–Wainger range bound with the `IWMult` data from `MSTThetaBound` (and narrowness of `η_s` from `mstEta_support`), getting `log(s+2)`; (iv) the `≤ κ_s+1` Rademacher–Menshov levels give the factor `s+1` (for small `s` absorb into `C`). -/
theorem mst_level_lr_lt (hTheta : Work.BourgainPlan.Maximal.MSTThetaBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (M : ℝ) (hM : 0 < M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {p : ℝ} (hp : 1 < p) (r₀ : ℕ) (hr₀ : 2 ≤ r₀)
    (hp_hi : p ≤ 2 * (r₀ : ℝ))
    (hp_lo : (2 * (r₀ : ℝ)) / (2 * (r₀ : ℝ) - 1) ≤ p)
    (hML : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k ∈ Finset.range (2 ^ (mstKappa P s) + 1),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hηml : ∀ s : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1)) := by
    intro s
    have h := (memLp_mst_symbols P 0 (mstScale P.natDegree χ s) η hηc.continuous).2.2
    have heq : mstEta P.natDegree χ η s
        = fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
            η (mstScale P.natDegree χ s * iwRep ξ) := rfl
    rw [heq]
    exact h
  obtain ⟨K, hKpos, htriv⟩ :=
    mst_lvl_triv P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2 hML
  refine mst_lvl_assembly P hd l χ η p hp hML hηml
    (mst_lvl_level_bound hTheta P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2
      hp r₀ hr₀ hp_hi hp_lo hηml)
    (mst_lvl_base_lp P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2
      hp r₀ hr₀ hp_hi hp_lo hηml)
    (mst_lvl_err P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2 hp hML hηml)
    ⟨K, hKpos, fun s k g => ?_⟩
  have hcardle : (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)) ≤ ((mstU l (s + 1)).card : ℝ) := by
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro x hx
    rw [← mstLevel_succ]
    exact (Finset.mem_sdiff.mp hx).1
  refine (htriv s k g (r := p) hp.le).trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  exact mul_le_mul_of_nonneg_right hcardle hKpos.le


end

end Work.BourgainPlan.Maximal
