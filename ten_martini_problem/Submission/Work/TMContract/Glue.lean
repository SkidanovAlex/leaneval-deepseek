import Submission.Work.TMContract.Defs
import Submission.Work.TMContract.Components
import Submission.Work.TMContract.Gluing.slope_bound_of_analytic_strictMono
import Submission.Work.TMContract.Gluing.liouville_of_aux
import Submission.Work.TMContract.Gluing.idsAnalytic_of

set_option maxHeartbeats 1000000

/-!
# Ten Martini contract: the glue

This file assembles the frozen components (`Components.lean`) into the challenge statement
of `Challenge.lean`.  It is the "§8" of `Submission/Work/TMPlan/Interfaces.lean`, with the
three glue lemmas that the design left as `sorry` (`idsAnalytic_of`, `liouville_of`,
`amoSpec_neg`) proved.  All names are in namespace `Work.TMContract`.

* `ids_lt_of_Icc_subset_amoSpec` — strict increase of `N` on a closed interval in the
  spectrum, from `P_RotBasics` (monotonicity) and `P_IDSSpectrum`.
* `idsAnalytic_of` — `N` is real-analytic on a spectral interval (proved in
  `Gluing/idsAnalytic_of.lean`, from `P_RotBasics` and `P_mAnalytic`).
* `slope_bound_of_spectral_interval` — uniform positive slope of `N` on a subinterval
  (combines `idsAnalytic_of`, `ids_lt_of_Icc_subset_amoSpec` and
  `Gluing/slope_bound_of_analytic_strictMono.lean`).
* `liouville_of` — AJ Thm 8.1(2) (`P_Liouville`), from `P_RotBasics`, `P_IDSSpectrum`,
  `P_mAnalytic`, `P_FictLip`, `P_GapBound` (assembly in `Gluing/liouville_of_aux.lean`).
* `beta0_of`, `diophSide_of`, `diophBelow_of_not_liouvilleAbove`,
  `liouvilleAbove_of_not_diophBelow`, `noInterval_of_inv`, `amoSpec_neg`,
  `noInterval_all`, `isTotallyDisconnected_of_real`, `tm_of_components`, `tm_challenge`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMContract

/-! ## Strict monotonicity of the IDS on a spectral interval -/

/-- On a closed interval contained in the spectrum, the IDS is strictly increasing. -/
theorem ids_lt_of_Icc_subset_amoSpec (h5 : P_RotBasics) (h6 : P_IDSSpectrum)
    {α lam x y : ℝ} (hα : Irrational α) (hxy : x < y) (hsub : Icc x y ⊆ amoSpec α lam) :
    ids α lam x < ids α lam y := by
  have hmono : Monotone (ids α lam) := h5.2.1 α lam
  have hm : (x + y) / 2 ∈ amoSpec α lam := hsub ⟨by linarith, by linarith⟩
  have hε : 0 < (y - x) / 4 := by linarith
  have hstep := h6 α lam hα ((x + y) / 2) hm ((y - x) / 4) hε
  have h1 : ids α lam x ≤ ids α lam ((x + y) / 2 - (y - x) / 4) := hmono (by linarith)
  have h2 : ids α lam ((x + y) / 2 + (y - x) / 4) ≤ ids α lam y := hmono (by linarith)
  linarith

/-- `P_RotBasics` + `P_IDSSpectrum`: `N` is strictly increasing on any interval whose
closure lies in the spectrum. -/
theorem ids_strictMonoOn_Ioo_of_subset (h5 : P_RotBasics) (h6 : P_IDSSpectrum)
    {α lam a b : ℝ} (hα : Irrational α) (hsub : Ioo a b ⊆ amoSpec α lam) :
    StrictMonoOn (ids α lam) (Ioo a b) := by
  intro x hx y hy hxy
  refine ids_lt_of_Icc_subset_amoSpec h5 h6 hα hxy ?_
  intro t ht
  exact hsub ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩

/-! ## Analyticity of the IDS on a spectral interval (glue lemma of the design) -/

/-- GLUE (`ROUTE_LEAD.md` §3.2).  `N` is real-analytic on a spectral interval: from C9 the
conjugacy `C_E` gives `rotLift = 2∫φ(E,·) + 2j(E)` (C5 part 4, `k = 0`); `j` is locally
constant because it is continuous (C5 part 3) and integer valued.

Proved in `Gluing/idsAnalytic_of.lean` (which uses `Gluing/analyticOnNhd_integral.lean` for
the analyticity of `E ↦ ∫₀¹ φ(E,x)dx`). -/
theorem idsAnalytic_of (h5 : P_RotBasics) (h9 : P_mAnalytic) :
    ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
      AnalyticOnNhd ℝ (ids α lam) (Ioo a b) :=
  Gluing.idsAnalytic_of h5 h9

/-- Uniform positive slope of `N` on a subinterval of a spectral interval.  This is the
quantitative form of "`N` is real-analytic and strictly increasing" that
`liouville_of` consumes. -/
theorem slope_bound_of_spectral_interval (h5 : P_RotBasics) (h6 : P_IDSSpectrum)
    (h9 : P_mAnalytic) :
    ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
      ∃ c d c₀ : ℝ, a < c ∧ c < d ∧ d < b ∧ 0 < c₀ ∧
        ∀ x ∈ Icc c d, ∀ y ∈ Icc c d, x < y →
          c₀ * (y - x) ≤ ids α lam y - ids α lam x := by
  intro α lam a b hα hl0 hl1 hab hsub
  exact Gluing.slope_bound_of_analytic_strictMono hab
    (idsAnalytic_of h5 h9 α lam a b hα hl0 hl1 hab hsub)
    (ids_strictMonoOn_Ioo_of_subset h5 h6 hα hsub)

/-! ## The three case statements (ROUTE_LEAD §1) -/

/-- GLUE (`ROUTE_LEAD.md` §3.3): AJ Remark 4.1 = Thm 4.2(1) + Lemma 4.3. -/
theorem beta0_of (h11 : P_Reducibility) (h12 : P_Puig) : P_Beta0 := by
  intro α hα hβ lam hl0 hl1
  rintro ⟨a, b, hab, hsub⟩
  exact h12 α lam hα hl0 hl1 a b hab hsub (h11.1 α hα hβ lam hl0 hl1 a b hab hsub)

/-- GLUE (`ROUTE_LEAD.md` §3.4): the proof of AJ Thm 8.1(2), with C14 in place of
Lemma 7.1 + Thm 7.2. -/
theorem liouville_of (h5 : P_RotBasics) (h6 : P_IDSSpectrum) (h9 : P_mAnalytic)
    (h13 : P_FictLip) (h14 : P_GapBound) : P_Liouville :=
  Gluing.liouville_of_aux h13 h14 (slope_bound_of_spectral_interval h5 h6 h9)

/-- GLUE: AJ Thm 8.1(1) = Thm 5.2 + Thm 5.1. -/
theorem diophSide_of (h16 : P_Loc) (h17 : P_LocCantor) : P_DiophSide := by
  intro α b lam hα hb hD hlam
  have h1 : (1 : ℝ) ≤ lam := by
    have : (1 : ℝ) ≤ Real.exp (16 * b / 9) := Real.one_le_exp (by linarith)
    linarith
  exact h17 α b lam hα hD h1 (h16 α b lam hα hb hD hlam)

/-! ## Arithmetic and sign glue -/

/-- `¬ LiouvilleAbove ↔ DiophBelow`. -/
theorem diophBelow_of_not_liouvilleAbove {α b : ℝ} (h : ¬ LiouvilleAbove α b) :
    DiophBelow α b := by
  unfold LiouvilleAbove at h
  unfold DiophBelow
  rw [Filter.not_frequently] at h
  filter_upwards [h] with k hk
  exact not_lt.mp hk

theorem liouvilleAbove_of_not_diophBelow {α b : ℝ} (h : ¬ DiophBelow α b) :
    LiouvilleAbove α b := by
  by_contra h'
  exact h (diophBelow_of_not_liouvilleAbove h')

/-- `DiophBelow α b` is exactly the negation of `LiouvilleAbove α b`: the two are the two
sides of `¬(∃ᶠ k, P k) ↔ ∀ᶠ k, ¬P k`. -/
theorem not_liouvilleAbove_iff_diophBelow {α b : ℝ} :
    ¬ LiouvilleAbove α b ↔ DiophBelow α b := by
  rw [LiouvilleAbove, DiophBelow, Filter.not_frequently]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun k => not_lt)

/-- The dichotomy of the case split, stated entirely in terms of `LiouvilleAbove`: AJ's
`β(α) = 0` is `∀ b > 0, ¬ LiouvilleAbove α b`.  (`¬ LiouvilleAbove ↔ DiophBelow` is
`not_liouvilleAbove_iff_diophBelow`, so this is the same hypothesis as the one consumed by
`P_Beta0`.) -/
theorem beta0_iff_no_liouvilleAbove (α : ℝ) :
    (∀ b : ℝ, 0 < b → DiophBelow α b) ↔ (∀ b : ℝ, 0 < b → ¬ LiouvilleAbove α b) := by
  simp only [not_liouvilleAbove_iff_diophBelow]

/-- Transport of `NoInterval` along duality, for `λ > 0`. -/
theorem noInterval_of_inv (hDual : P_Duality) {α lam : ℝ} (hα : Irrational α) (hl : 0 < lam)
    (h : NoInterval α lam⁻¹) : NoInterval α lam := by
  rintro ⟨a, b, hab, hsub⟩
  apply h
  refine ⟨a / lam, b / lam, div_lt_div_of_pos_right hab hl, ?_⟩
  intro E' hE'
  have hE : lam * E' ∈ Ioo a b := by
    constructor
    · have := hE'.1
      rw [div_lt_iff₀ hl] at this
      linarith
    · have := hE'.2
      rw [lt_div_iff₀ hl] at this
      linarith
  have hmem := (hDual α lam hα hl.ne' (lam * E')).1 (hsub hE)
  rwa [mul_div_cancel_left₀ E' hl.ne'] at hmem

/-- `amoPot` is invariant under `λ ↦ -λ` together with the half-turn phase shift. -/
theorem amoPot_neg_shift (α lam θ : ℝ) (n : ℤ) :
    amoPot α (-lam) θ n = amoPot α lam (θ + 1 / 2) n := by
  unfold amoPot
  have h : 2 * Real.pi * (θ + 1 / 2 + (n : ℝ) * α)
      = 2 * Real.pi * (θ + (n : ℝ) * α) + Real.pi := by ring
  rw [h, Real.cos_add_pi]
  ring

/-- The phase-shift identity for the operator: `H_{-λ,θ}` is `H_{λ,θ+1/2}`. -/
theorem isAMO_neg_shift (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) :
    IsAlmostMathieuOperator α (-lam) θ H ↔ IsAlmostMathieuOperator α lam (θ + 1 / 2) H := by
  have key : ∀ (u : EllTwo) (n : ℤ),
      amoAct α (-lam) θ (fun m => u m) n = amoAct α lam (θ + 1 / 2) (fun m => u m) n := by
    intro u n
    unfold amoAct
    rw [amoPot_neg_shift]
  rw [isAMO_iff, isAMO_iff]
  constructor <;> intro h u n
  · rw [h u n, key u n]
  · rw [h u n, ← key u n]

/-- `H_{-λ,θ} = H_{λ,θ+1/2}`, hence `Σ_{-λ} = Σ_λ` (phase independence). -/
theorem amoSpec_neg (hOp : P_OpBasics) {α : ℝ} (hα : Irrational α) (lam : ℝ) :
    amoSpec α (-lam) = amoSpec α lam := by
  ext E
  constructor
  · rintro ⟨H, hH, hspec⟩
    obtain ⟨H₀, hH₀⟩ := hOp.1 α lam 0
    refine ⟨H₀, hH₀, ?_⟩
    have hspec' : spectrum ℂ H = spectrum ℂ H₀ :=
      hOp.2.2 α lam (0 + 1 / 2) 0 hα H H₀ ((isAMO_neg_shift α lam 0 H).mp hH) hH₀
    rwa [hspec'] at hspec
  · rintro ⟨H₀, hH₀, hspec⟩
    obtain ⟨H, hH⟩ := hOp.1 α (-lam) 0
    refine ⟨H, hH, ?_⟩
    have hspec' : spectrum ℂ H = spectrum ℂ H₀ :=
      hOp.2.2 α lam (0 + 1 / 2) 0 hα H H₀ ((isAMO_neg_shift α lam 0 H).mp hH) hH₀
    rwa [hspec']

/-! ## The case split and the final assembly -/

/-- The case analysis of AJ §8 (with Remark 8.1 for `|λ| = 1`): every irrational `α` and
every `λ ≠ 0` is covered.  ROUTE_LEAD §1. -/
theorem noInterval_all (hOp : P_OpBasics) (hDual : P_Duality) (hB0 : P_Beta0)
    (hLiou : P_Liouville) (hDS : P_DiophSide) :
    ∀ α lam : ℝ, Irrational α → lam ≠ 0 → NoInterval α lam := by
  -- Step 1: the case `0 < λ ≤ 1`.
  have hsmall : ∀ α lam : ℝ, Irrational α → 0 < lam → lam ≤ 1 → NoInterval α lam := by
    intro α lam hα hl0 hl1
    -- AJ's `β = 0` case: no Liouville level at all (equivalently `DiophBelow` at every level).
    by_cases hβ : ∀ b : ℝ, 0 < b → ¬ LiouvilleAbove α b
    · exact hB0 α hα ((beta0_iff_no_liouvilleAbove α).mpr hβ) lam hl0 hl1
    push_neg at hβ
    -- Otherwise `β ≥ b₀ > 0` for some level `b₀`, and only `LiouvilleAbove` is used below.
    obtain ⟨b₀, hb₀, hL₀⟩ := hβ
    by_cases hA : ∃ b : ℝ, LiouvilleAbove α b ∧ Real.exp (-(2 * b)) < lam
    · obtain ⟨b, hb, hlt⟩ := hA
      exact hLiou α b lam hα hb hlt hl1
    push_neg at hA
    -- Now `λ ≤ e^{-2b}` whenever `LiouvilleAbove α b`.  Put `λ = e^{-2c}`.
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(Real.log lam) / 2 := ⟨_, rfl⟩
    have hlam : lam = Real.exp (-(2 * c)) := by
      have h2 : -(2 * c) = Real.log lam := by rw [hc]; ring
      rw [h2, Real.exp_log hl0]
    have hcb₀ : b₀ ≤ c := by
      have h1 : lam ≤ Real.exp (-(2 * b₀)) := hA b₀ hL₀
      rw [hlam] at h1
      have h3 := Real.exp_le_exp.mp h1
      linarith
    have hc0 : 0 < c := lt_of_lt_of_le hb₀ hcb₀
    -- `b = 17c/16 > c` is not a Liouville level, hence a Diophantine level.
    have hD : DiophBelow α (17 * c / 16) := by
      apply diophBelow_of_not_liouvilleAbove
      intro hL
      have h1 : lam ≤ Real.exp (-(2 * (17 * c / 16))) := hA (17 * c / 16) hL
      rw [hlam] at h1
      have h3 := Real.exp_le_exp.mp h1
      linarith
    -- Dual coupling `λ⁻¹ = e^{2c} > e^{16(17c/16)/9} = e^{17c/9}`.
    have hdual : Real.exp (16 * (17 * c / 16) / 9) < lam⁻¹ := by
      rw [hlam, ← Real.exp_neg, neg_neg]
      apply Real.exp_lt_exp.mpr
      linarith
    exact noInterval_of_inv hDual hα hl0
      (hDS α (17 * c / 16) lam⁻¹ hα (by linarith) hD hdual)
  -- Step 2: `λ > 1` by duality, `λ < 0` by the sign symmetry.
  have hpos : ∀ α lam : ℝ, Irrational α → 0 < lam → NoInterval α lam := by
    intro α lam hα hl0
    rcases le_or_gt lam 1 with h1 | h1
    · exact hsmall α lam hα hl0 h1
    · have hinv : NoInterval α lam⁻¹ :=
        hsmall α lam⁻¹ hα (inv_pos.mpr hl0) (inv_le_one_of_one_le₀ h1.le)
      exact noInterval_of_inv hDual hα hl0 hinv
  intro α lam hα hl
  rcases lt_or_gt_of_ne hl with hneg | hpos'
  · have h := hpos α (-lam) hα (neg_pos.mpr hneg)
    unfold NoInterval at h ⊢
    rwa [amoSpec_neg hOp hα lam] at h
  · exact hpos α lam hα hpos'

/-- Topology: a subset of `ℂ` lying on the real axis whose real trace contains no open
interval is totally disconnected. -/
theorem isTotallyDisconnected_of_real {S : Set ℂ} (hreal : ∀ z ∈ S, z = (z.re : ℂ))
    (hno : ¬ HasInterval {x : ℝ | (x : ℂ) ∈ S}) : IsTotallyDisconnected S := by
  intro t hts ht
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨z, hz, w, hw, hzw⟩ := hns
  have hre : IsPreconnected (Complex.re '' t) := ht.image Complex.re Complex.continuous_re.continuousOn
  have hzr : z = (z.re : ℂ) := hreal z (hts hz)
  have hwr : w = (w.re : ℂ) := hreal w (hts hw)
  have hne : z.re ≠ w.re := by
    intro h
    exact hzw (by rw [hzr, hwr, h])
  -- the real trace of `S` contains `Icc (min) (max)` for two points of `re '' t`
  have key : ∀ x y : ℝ, x ∈ Complex.re '' t → y ∈ Complex.re '' t → x < y →
      HasInterval {x : ℝ | (x : ℂ) ∈ S} := by
    intro x y hx hy hxy
    refine ⟨x, y, hxy, fun r hr => ?_⟩
    obtain ⟨u, hu, hur⟩ := hre.Icc_subset (a := x) (b := y) hx hy (Ioo_subset_Icc_self hr)
    have huS := hreal u (hts hu)
    show (r : ℂ) ∈ S
    rw [← hur, ← huS]
    exact hts hu
  rcases lt_or_gt_of_ne hne with h | h
  · exact hno (key _ _ ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩ h)
  · exact hno (key _ _ ⟨w, hw, rfl⟩ ⟨z, hz, rfl⟩ h)

/-- **The composition.**  The challenge statement from the operator basics, perfectness,
duality and the three case statements. -/
theorem tm_of_components (hOp : P_OpBasics) (hPerf : P_Perfect) (hDual : P_Duality)
    (hB0 : P_Beta0) (hLiou : P_Liouville) (hDS : P_DiophSide) :
    ∀ (α coupling θ : ℝ), Irrational α → coupling ≠ 0 →
      ∃ H : EllTwo →L[ℂ] EllTwo,
        IsAlmostMathieuOperator α coupling θ H ∧
          (spectrum ℂ H).Nonempty ∧
          IsCompact (spectrum ℂ H) ∧
          Perfect (spectrum ℂ H) ∧
          IsTotallyDisconnected (spectrum ℂ H) := by
  intro α lam θ hα hl
  obtain ⟨H, hH⟩ := hOp.1 α lam θ
  refine ⟨H, hH, spectrum.nonempty H, spectrum.isCompact H, hPerf α lam θ hα H hH, ?_⟩
  have hsa : IsSelfAdjoint H := hOp.2.1 α lam θ H hH
  apply isTotallyDisconnected_of_real (fun z hz => hsa.mem_spectrum_eq_re hz)
  -- the real trace of `spectrum ℂ H` is contained in `amoSpec α lam` (phase independence)
  obtain ⟨H₀, hH₀⟩ := hOp.1 α lam 0
  have hspec : spectrum ℂ H = spectrum ℂ H₀ := hOp.2.2 α lam θ 0 hα H H₀ hH hH₀
  have htrace : {x : ℝ | (x : ℂ) ∈ spectrum ℂ H} ⊆ amoSpec α lam := by
    intro x hx
    exact ⟨H₀, hH₀, hspec ▸ hx⟩
  rintro ⟨a, b, hab, hsub⟩
  exact noInterval_all hOp hDual hB0 hLiou hDS α lam hα hl ⟨a, b, hab, hsub.trans htrace⟩

/-- The challenge statement from the eighteen components. -/
theorem tm_challenge (h0 : P_UniqErg) (h1 : P_OpBasics) (h2 : P_Perfect) (h3 : P_Duality)
    (h4 : P_LEBasics) (h5 : P_RotBasics) (h6 : P_IDSSpectrum) (h7 : P_BJ) (h8 : P_Kotani)
    (h9 : P_mAnalytic) (h10 : P_RealCartan) (h11 : P_Reducibility) (h12 : P_Puig)
    (h13 : P_FictLip) (h14 : P_GapBound) (h15 : P_Schnol) (h16 : P_Loc)
    (h17 : P_LocCantor) :
    ∀ (α coupling θ : ℝ), Irrational α → coupling ≠ 0 →
      ∃ H : EllTwo →L[ℂ] EllTwo,
        IsAlmostMathieuOperator α coupling θ H ∧
          (spectrum ℂ H).Nonempty ∧
          IsCompact (spectrum ℂ H) ∧
          Perfect (spectrum ℂ H) ∧
          IsTotallyDisconnected (spectrum ℂ H) :=
  tm_of_components h1 h2 h3 (beta0_of h11 h12) (liouville_of h5 h6 h9 h13 h14)
    (diophSide_of h16 h17)

/-- The challenge statement in exactly the shape of `Challenge.lean`, from the eighteen
components. -/
theorem ten_martini_problem_of_components (h0 : P_UniqErg) (h1 : P_OpBasics)
    (h2 : P_Perfect) (h3 : P_Duality) (h4 : P_LEBasics) (h5 : P_RotBasics)
    (h6 : P_IDSSpectrum) (h7 : P_BJ) (h8 : P_Kotani) (h9 : P_mAnalytic) (h10 : P_RealCartan)
    (h11 : P_Reducibility) (h12 : P_Puig) (h13 : P_FictLip) (h14 : P_GapBound)
    (h15 : P_Schnol) (h16 : P_Loc) (h17 : P_LocCantor)
    (α coupling θ : ℝ) (hα : Irrational α) (hcoupling : coupling ≠ 0) :
    ∃ H : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α coupling θ H ∧
        (spectrum ℂ H).Nonempty ∧
        IsCompact (spectrum ℂ H) ∧
        Perfect (spectrum ℂ H) ∧
        IsTotallyDisconnected (spectrum ℂ H) :=
  tm_challenge h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    α coupling θ hα hcoupling

end Work.TMContract
