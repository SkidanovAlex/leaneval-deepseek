import Mathlib
import Submission.Work.Maximal.mst_canon_defs
import Submission.Work.BourgainPlan.Maximal.mst_theta_defs
import Submission.Work.Maximal.mstNuS_lr_large_aux_glue
import Submission.Work.BourgainPlan.Maximal.subtwoLat

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- **The large-scale `ℓʳ` level estimate** (the statement of the project's target
`Work.Maximal.mst_level_lr_large`, restated so that it can be proved on its own): for every
`1 < r < 2` there is `C` such that for every level `s` and every finitely supported `g`,
`‖ sup_{k ≥ 2^{mstKappa P s}} |𝓕⁻(ν^s_{2^k} ĝ)| ‖_{ℓʳ(ℤ)} ≤ C log(s+2) ‖g‖_{ℓʳ(ℤ)}`, where
`ν^s_{2^k} = mstNuS P l P.natDegree χ η k s` is the level-`s` major-arc model symbol of
Mirek–Stein–Trojan (arXiv:1512.07518, §4.2) — the large-scale half of their Theorem 8.

Route (MST §4.4; cf. `Submission/Work/BourgainPlan/Maximal/MST_ROUTE.md` §5 and the docstring of
`Submission/Work/BourgainPlan/Maximal/mst_level_lr.lean`).  Fix `s`, put `K := 2^{mstKappa P s}`,
`Q := mstQ' s`, `d := P.natDegree`, and let `ϱ_s (ξ) := η (Q'^{3dA} ξ)` be the *wide* bump.

1. *Narrow → wide replacement.*  On the margin between the supports of `η_s` and `ϱ_s` the profile is
   small (`polyProfile_decay_sharp`: the profile concentrates at scale `2^{-kd}`, the margin has width
   `≫ 2^{-kd}` for `k ≥ K`), so with the Gauss decay and the **disjointness** of the bumps
   (`sigmaN_separated`, `mstEta_narrow`) the pointwise symbol difference is
   `≤ D(s+1)^{-δl}2^{-k/(2d)}`.  Plancherel (ℓ²) plus the trivial bound `≲ ♯‖f‖_{ℓʳ}`
   (`♯ ≤ C e^{(s+1)^{1/10}}`, `mstU_card_le_exp`; each single-arc operator is
   `M_{2^k} ∘ (bump multiplier)`, `discAvgZC_lp_contraction` + bump-multiplier bound) and
   Riesz–Thorin (`ellp_interpolation`) give `≲ 2^{-c_rk}e^{c_r(s+1)^{1/10}}‖f‖_{ℓʳ}` for `k ≥ K`; the
   geometric sum over `k ≥ K` is `≤ 1` since `K = 2^{20d(⌊(s+1)^{1/10}⌋+1)}` dominates any
   exponential of `(s+1)^{1/10}` (`exists_rpow_ten_add_one_lt`).  So it suffices to bound the model
   `Ω^s_N` built with the wide bump.

2. *The wide-bump maximal bound* (MST Theorem `th:1`).  Every point of the annulus is `Q`-torsion
   (`mstTorsion`), so decomposing `ℤ` into residue classes mod `Q` gives, for `m < Q`,
   `𝓕⁻(Ω^s_N ĝ)(Q x + m) = 𝓕⁻(Φ_N ϱ_s F(·;m))(Q x + m)` with
   `F(ξ;m) = Σ_β star(G β) ĝ(ξ+β) star(fourier m β)`.  The bump `ϱ_s` has support radius `≤ 1/(4Q)`,
   so `x ↦ 𝓕⁻(Φ_N ϱ_s F(·;m))(Q x+m)` is band limited to `[-1/4,1/4]`; the two-sided lattice
   comparison (`Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_fourierInv_rpow`
   forward, `Maximal/fourierInv_band_strict_lattice_le_lr` backward) identifies the sampled `ℓʳ` norm
   with `∫_ℝ (sup_N|𝓕⁻(Φ_N ϱ_s F(·;m))|)^r`, up to `C/Q`.  The *continuous* maximal bound
   `∫_ℝ (sup_N|𝓕⁻(Φ_N w)|)^r ≤ B_r∫_ℝ|w|^r` for band-limited `w` follows from the curve identity
   (`Work.Maximal.mstMax_curve`, `polyProfile_fourier_dilation`), the HL-domination
   `Maximal/level_l2_mst_large_n_hl` and `Commons.Analysis.Maximal.lintegral_rpow_hlMax_le` (or
   directly from `Maximal/poly_dilation_lp_leading`).
   Summing over the residues and undoing the periodisation (the same torsion identity;
   `Work.Maximal.mstOrtho.range_fourier_sq_sum` for the `m`-sum) reduces everything to the *single*
   multiplier `Π̃^G_s = Σ_β star(G β) ϱ_s(·-β)`.

3. *The single weighted multiplier.*  Replace `G β` by `mstWeyl P J` (`J = ⌊exp √(s+1)⌋`) with
   `Maximal/mst_lvl_approx_pointwise` (error `e^{-√(s+1)/2}`, absorbed as in MST (94)/(112)/(79)) and
   bound the resulting *unweighted* sum of wide bumps over the annulus by the Ionescu–Wainger range
   bound (`iwRangeBound_of_endpoint` / `IWSupersetBoundLift`) applied twice, to `Σ_{β∈mstU l (s+1)}`
   and `Σ_{β∈mstU l s}` (`opArc_sdiff`; `Maximal/mstThetaBump_opArc_lp` is the template), together
   with `‖μ_J‖_{ℓʳ→ℓʳ} ≤ 1` (`discAvgZC_lp_contraction`).  This gives the `log(s+2)` loss
   (`iwRangeBound` gives an absolute constant and `log(s+2) ≥ log 2` converts it). -/
theorem mstNuS_lr_large_aux (hΘ : Work.BourgainPlan.Maximal.MSTThetaBound)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)))
    (hνsml : ∀ n s : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ⨆ (_ : 2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k),
          ‖Work.BourgainPlan.IonescuWainger.opMul
            (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hνsml k s))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count :=
  Work.Maximal.mstNuS_lr_large_aux_glue
    (Work.BourgainPlan.Maximal.mstLatticePrinciple (r := r) hr)
    hΘ P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hder1 hder2 hηsup hδ D hD hGauss hνsml hr hr2

end Work.Maximal
