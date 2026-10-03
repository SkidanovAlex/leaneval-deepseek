/-
# The composition `exists_varEstHalfFin_Cv_of_areas` (`ROUTE_LEAD.md` §3.2)

This module proves the composition of the eight areas of the contract into the paper's
Theorem `end-var`, i.e. the single remaining hole `Submission.ShiftHole.exists_varEstHalfFin_Cv`:

`exists_varEstHalfFin_Cv_of_areas` — given the eight areas A1–A8 (as hypotheses, never as
axioms), for every `P` of degree `≥ 2`, every `1 < p₁, p₂ < ∞` with `p₁⁻¹ + p₂⁻¹ ≤ 1` and every
`r > 2`, there is a constant `Cv : ℝ≥0 → ℝ≥0` with

`VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹+p₂⁻¹)⁻¹ r Cv`.

The proof is the bookkeeping of §3.2 of `ROUTE_LEAD.md`:

* **A4** (via A1, A2, A3) gives the single-scale minor arc estimate `ImprovKMT P`;
* **A5** gives, for the height constant `C₀ = max C₀min 1` and some `ρ₅ > 0`, the single-scale
  minor-arc input `MinorArcInput (kmtPj ρ) P P.natDegree C₀ p₁ p₂ p` for every `ρ ≤ ρ₅`;
* **A6** gives the `(2,2,1)` paraproduct bound with gain `2^{-cL}`, **A7** the bound at the
  auxiliary exponents `(a₁,b₁)` with loss `2^{AρL}` (where `a₁ = 1/x'`, `b₁ = 1/y'` are the
  perturbations of the exponents by the small `ε` produced by `interpExponents_setup`);
* **A8** (`VarBilinInterp`) interpolates the two, and
  `CompositionAux.varpStatementΛ_of_pieceBounds` turns the interpolated bound into Theorem `varp`
  with the canonical gain `2^{-c'·L}`, `c' = (1-θ)c/2`, for the Ionescu--Wainger parameter
  `ρ = min (min ρ₅ ρ₆) (min ρ₇ ((1-θ)c/(2θ(A+1))))`;
* the capstone `exists_varEstHalfFin_of_varpΛ_minorArc` (of
  `Submission/Work/KMTContract/VarpLambda.lean`) assembles `varp` + the minor-arc input into
  `VarEstHalfFin`.

The two technical hypotheses that `varpStatementΛ_of_pieceBounds` takes from the Ionescu--Wainger
API are supplied here by the proved lemmas `Work.KMTContract.varpCol_finsupp_bilinear`,
`Work.KMTContract.varpCol_tendsto_truncZ` (with `kmtProj_tendsto_truncZ` + the kernel decay
`kmtKernel_decay`), and the vanishing of the columns on the zero function comes from
`Submission/Work/KMTContract/Defs.lean`.
-/
import Submission.Work.KMTContract.CompositionAux
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kmtProj_tendsto_truncZ
import Submission.Work.KMTContract.varpCol_finsupp_bilinear
import Submission.Work.KMTContract.varpCol_tendsto_truncZ
import Submission.Work.KMTContract.interpExponents_setup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTContract

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.Analysis.InverseTheory
open Work.Analysis.Paraproduct (IWProjections)

/-- **The composition, with the side conditions as explicit hypotheses.** -/
theorem exists_varEstHalfFin_Cv_of_areas_aux
    (h1 : AreaA1) (h2 : AreaA2) (h3 : AreaA3) (h4 : AreaA4) (h5 : AreaA5) (h6 : AreaA6)
    (h7 : AreaA7) (h8 : VarBilinInterp) (P : Polynomial ℤ) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0)
    (hPd : P.degree ≥ 2) (h1p₁ : 1 < p₁) (h1p₂ : 1 < p₂) (h2p₁ : p₁ < ⊤) (h2p₂ : p₂ < ⊤)
    (hH : p₁⁻¹ + p₂⁻¹ ≤ 1) (hr : 2 < r) :
    ∃ Cv : ℝ≥0 → ℝ≥0, VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv := by
  have hd : 2 ≤ P.natDegree := two_le_natDegree_of_degree hPd
  have hI : ImprovKMT P := h4 P hd h1 (h2 P hd)
    (h3 (P - X) (by rw [natDegree_P_sub_X hd]; exact hd))
    (h3 (X - P) (by rw [natDegree_X_sub_P hd]; exact hd))
  obtain ⟨C₀min, hC₀min⟩ := h5 P p₁ p₂ hd h1p₁ h2p₁ h1p₂ h2p₂ hH h1 hI
  set C₀ : ℕ := max C₀min 1 with hC₀def
  obtain ⟨ρ₅, hρ₅pos, hρ₅⟩ := hC₀min C₀ (le_max_left _ _)
  have hr1 : (1 : ℝ≥0) ≤ r := le_trans (by norm_num) hr.le
  by_cases h22 : p₁ = 2 ∧ p₂ = 2
  · -- ## the case `p₁ = p₂ = 2` (the `(2,2,1)` paraproduct bound of A6 alone)
    obtain ⟨hp₁, hp₂⟩ := h22
    obtain ⟨c, hc, ρ₆, hρ₆pos, h6'⟩ := h6 P hd h1 hI C₀ r (le_max_right _ _) hr
    set ρ : ℝ := min ρ₅ ρ₆ with hρdef
    have hρ0 : 0 < ρ := lt_min hρ₅pos hρ₆pos
    have hle₅ : ρ ≤ ρ₅ := min_le_left _ _
    have hle₆ : ρ ≤ ρ₆ := min_le_right _ _
    have hMinor : MinorArcInput (kmtPj ρ) P P.natDegree C₀ 2 2 1 := by
      have h := hρ₅ ρ hρ0 hle₅
      rw [MinorArcInput] at h
      rw [MinorArcInput]
      simpa [hp₁, hp₂, ENNReal.inv_two_add_inv_two, inv_one] using h
    have hvarp : VarpStatementΛ (kmtPj ρ) P P.natDegree C₀ 2 2 1 r := by
      obtain ⟨C, hC⟩ := h6' ρ hρ0 hle₆
      exact ⟨c, C, hc, hC⟩
    obtain ⟨Cv, hCv⟩ := exists_varEstHalfFin_of_varpΛ_minorArc (p₁ := 2) (p₂ := 2) (p := 1)
      hr1 le_rfl hvarp hMinor
    refine ⟨Cv, ?_⟩
    simpa [hp₁, hp₂, ENNReal.inv_two_add_inv_two, inv_one] using hCv
  · -- ## all other exponents: interpolate A6 and A7 with A8
    have hne : p₁ ≠ 2 ∨ p₂ ≠ 2 := by
      by_contra h
      push_neg at h
      exact h22 ⟨h.1, h.2⟩
    -- the exponents `x = 1/p₁`, `y = 1/p₂` and their perturbation
    obtain ⟨hx0, hx1⟩ := toReal_inv_pos_lt_one h1p₁ h2p₁
    obtain ⟨hy0, hy1⟩ := toReal_inv_pos_lt_one h1p₂ h2p₂
    have hxy : (p₁.toReal)⁻¹ + (p₂.toReal)⁻¹ ≤ 1 :=
      toReal_inv_add_le_one h1p₁ h2p₁ h1p₂ h2p₂ hH
    obtain ⟨ε, hε0, hθ0, hθ1, hx'0, hx'1, hy'0, hy'1, hx'y', hidx, hidy, hids⟩ :=
      interpExponents_setup hx0 hx1 hy0 hy1 hxy
    set θ : ℝ := 1 / (1 + ε) with hθdef
    set a₁ : ℝ≥0∞ := ENNReal.ofReal ((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2))⁻¹ with ha₁def
    set b₁ : ℝ≥0∞ := ENNReal.ofReal ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2))⁻¹ with hb₁def
    have h1a₁ : 1 < a₁ := by rw [ha₁def]; exact one_lt_ofReal_inv hx'0 hx'1
    have h2a₁ : a₁ < ⊤ := by rw [ha₁def]; exact ENNReal.ofReal_lt_top
    have h1b₁ : 1 < b₁ := by rw [hb₁def]; exact one_lt_ofReal_inv hy'0 hy'1
    have h2b₁ : b₁ < ⊤ := by rw [hb₁def]; exact ENNReal.ofReal_lt_top
    have hH' : a₁⁻¹ + b₁⁻¹ ≤ 1 := by
      rw [ha₁def, hb₁def, inv_ofReal_inv hx'0, inv_ofReal_inv hy'0,
        ← ENNReal.ofReal_add (le_of_lt hx'0) (le_of_lt hy'0), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hx'y'
    have h1q₁ : 1 ≤ (a₁⁻¹ + b₁⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hH'
    have h2q₁ : (a₁⁻¹ + b₁⁻¹)⁻¹ < ⊤ := by
      rw [ENNReal.inv_lt_top]
      exact lt_of_lt_of_le (ENNReal.inv_pos.mpr h2a₁.ne) (le_add_right le_rfl)
    -- the auxiliary exponents are `≠ (2,2)`
    have hne₁ : a₁ ≠ 2 ∨ b₁ ≠ 2 := by
      have hxy' : (p₁.toReal)⁻¹ ≠ 1 / 2 ∨ (p₂.toReal)⁻¹ ≠ 1 / 2 := by
        by_contra h
        push_neg at h
        have hp₁ : p₁ = 2 := inv_toReal_eq_half h2p₁ h.1
        have hp₂ : p₂ = 2 := inv_toReal_eq_half h2p₂ h.2
        rcases hne with hne | hne
        · exact hne hp₁
        · exact hne hp₂
      rcases hxy' with hxy' | hxy'
      · refine Or.inl fun hc => hxy' ?_
        rw [ha₁def] at hc
        exact (perturb_eq_half_iff hε0).mp ((ofReal_inv_eq_two_iff hx'0).mp hc)
      · refine Or.inr fun hc => hxy' ?_
        rw [hb₁def] at hc
        exact (perturb_eq_half_iff hε0).mp ((ofReal_inv_eq_two_iff hy'0).mp hc)
    -- A6 and A7 at the auxiliary exponents
    obtain ⟨c, hc, ρ₆, hρ₆pos, h6'⟩ := h6 P hd h1 hI C₀ r (le_max_right _ _) hr
    obtain ⟨A, hA0, ρ₇, hρ₇pos, h7'⟩ :=
      h7 P a₁ b₁ hd h1a₁ h2a₁ h1b₁ h2b₁ hH' hne₁ h1 C₀ r (le_max_right _ _) hr
    have hρsmall : 0 < (1 - θ) * c / (2 * θ * (A + 1)) := by
      have h1θ : 0 < 1 - θ := by linarith
      positivity
    set ρ : ℝ := min (min ρ₅ ρ₆) (min ρ₇ ((1 - θ) * c / (2 * θ * (A + 1)))) with hρdef
    have hρ0 : 0 < ρ := by
      rw [hρdef]
      exact lt_min (lt_min hρ₅pos hρ₆pos) (lt_min hρ₇pos hρsmall)
    have hle₅ : ρ ≤ ρ₅ := (min_le_left _ _).trans (min_le_left _ _)
    have hle₆ : ρ ≤ ρ₆ := (min_le_left _ _).trans (min_le_right _ _)
    have hle₇ : ρ ≤ ρ₇ := (min_le_right _ _).trans (min_le_left _ _)
    have hleθ : ρ ≤ (1 - θ) * c / (2 * θ * (A + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    -- the Ionescu--Wainger API needed by the interpolation
    have hconv_kmt : ∀ (l : ℕ) (k : ℤ) {p : ℝ≥0∞}, 1 < p → ∀ {f : ℤ → ℂ},
        MemLp f p Measure.count → ∀ n : ℤ,
        Tendsto (fun K : ℕ => kmtProj ρ l k (truncZ K f) n) atTop (𝓝 (kmtProj ρ l k f n)) :=
      fun l k p hp f hf n => kmtProj_tendsto_truncZ ρ l k (kmtKernel_decay ρ l k) hp hf n
    have hconv_varp : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) {f g : ℤ → ℂ},
        MemLp f p₁ Measure.count → MemLp g p₂ Measure.count → ∀ (n : ℕ) (x : ℤ),
        Tendsto (fun K : ℕ => varpCol (kmtPj ρ) P P.natDegree C₀ a (truncZ K f) (truncZ K g)
            l₁ l₂ k₁ k₂ n x)
          atTop (𝓝 (varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) :=
      fun a l₁ l₂ k₁ k₂ f g hf hg n x =>
        varpCol_tendsto_truncZ ρ P C₀ a l₁ l₂ k₁ k₂ hconv_kmt h1p₁ h1p₂ hf hg n x
    have hbil : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f f' g : ℤ → ℂ) (c' : ℂ),
        FinSupp f → FinSupp f' → FinSupp g →
        (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a (f + c' • f') g l₁ l₂ k₁ k₂ n x)
          = (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
              + c' • (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f' g l₁ l₂ k₁ k₂ n x) := by
      intro a l₁ l₂ k₁ k₂ f f' g c' hf hf' hg
      rw [(varpCol_finsupp_bilinear ρ P C₀ a l₁ l₂ k₁ k₂).1 f f' g c' hf hf']
      funext n x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have hbil' : ∀ (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g g' : ℤ → ℂ) (c' : ℂ),
        FinSupp f → FinSupp g → FinSupp g' →
        (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f (g + c' • g') l₁ l₂ k₁ k₂ n x)
          = (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
              + c' • (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g' l₁ l₂ k₁ k₂ n x) := by
      intro a l₁ l₂ k₁ k₂ f g g' c' hf hg hg'
      rw [(varpCol_finsupp_bilinear ρ P C₀ a l₁ l₂ k₁ k₂).2 f g g' c' hg hg']
      funext n x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    -- the three exponent relations of the interpolation
    have hminv : p₁⁻¹ = ENNReal.ofReal ((p₁.toReal)⁻¹) :=
      inv_eq_ofReal_inv_toReal (lt_trans one_pos h1p₁).ne'
    have hminv₂ : p₂⁻¹ = ENNReal.ofReal ((p₂.toReal)⁻¹) :=
      inv_eq_ofReal_inv_toReal (lt_trans one_pos h1p₂).ne'
    have ha₁inv : a₁⁻¹ = ENNReal.ofReal ((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2)) := by
      rw [ha₁def]; exact inv_ofReal_inv hx'0
    have hb₁inv : b₁⁻¹ = ENNReal.ofReal ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2)) := by
      rw [hb₁def]; exact inv_ofReal_inv hy'0
    have h21 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
      rw [inv_eq_ofReal_inv_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
      norm_num
    have hrel1 : p₁⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * a₁⁻¹ := by
      rw [hminv, ha₁inv, h21, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - θ),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ θ)]
      rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (1 - θ) * (1 / 2))
        (by positivity : (0 : ℝ) ≤ θ * ((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2)))]
      congr 1
      have h : (p₁.toReal)⁻¹ = (1 - θ) * (1 / 2) +
          θ * ((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2)) := by
        have h' := hidx
        have h2 : (1 - θ) / 2 = (1 - θ) * (1 / 2) := by ring
        rw [h2] at h'
        exact h'
      exact h
    have hrel2 : p₂⁻¹ = ENNReal.ofReal (1 - θ) * (2 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * b₁⁻¹ := by
      rw [hminv₂, hb₁inv, h21, ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - θ),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ θ)]
      rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (1 - θ) * (1 / 2))
        (by positivity : (0 : ℝ) ≤ θ * ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2)))]
      congr 1
      have h : (p₂.toReal)⁻¹ = (1 - θ) * (1 / 2) +
          θ * ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2)) := by
        have h' := hidy
        have h2 : (1 - θ) / 2 = (1 - θ) * (1 / 2) := by ring
        rw [h2] at h'
        exact h'
      exact h
    have hq₁inv : (a₁⁻¹ + b₁⁻¹)⁻¹⁻¹ =
        ENNReal.ofReal (((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2))
          + ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2))) := by
      rw [inv_inv, ha₁inv, hb₁inv, ← ENNReal.ofReal_add (le_of_lt hx'0) (le_of_lt hy'0)]
    have hrel3 : p₁⁻¹ + p₂⁻¹ =
        ENNReal.ofReal (1 - θ) * (1 : ℝ≥0∞)⁻¹ + ENNReal.ofReal θ * (a₁⁻¹ + b₁⁻¹)⁻¹⁻¹ := by
      rw [hminv, hminv₂, hq₁inv, inv_one, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 1 - θ),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ θ)]
      rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (1 - θ) * 1)
        (by positivity : (0 : ℝ) ≤ θ * (((p₁.toReal)⁻¹ + ε * ((p₁.toReal)⁻¹ - 1 / 2))
          + ((p₂.toReal)⁻¹ + ε * ((p₂.toReal)⁻¹ - 1 / 2))))]
      rw [← ENNReal.ofReal_add (le_of_lt hx0) (le_of_lt hy0)]
      congr 1
      rw [hids]
      ring
    -- conclude by the interpolation step and the capstone
    have hp1 : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hH
    have hvarp : VarpStatementΛ (kmtPj ρ) P P.natDegree C₀ p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r :=
      varpStatementΛ_of_pieceBounds h8 hbil hbil' hconv_varp
        (fun a l₁ l₂ k₁ k₂ f => varpCol_kmt_zero_right ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ f)
        (fun a l₁ l₂ k₁ k₂ g => varpCol_kmt_zero_left ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ g)
        hr1 hθ0 hθ1 hc hA0 hρ0 hleθ h1p₁ h2p₁ h1p₂ h2p₂ h1a₁ h2a₁ h1b₁ h2b₁ h1q₁ h2q₁ rfl
        hrel1 hrel2 hrel3 (h6' ρ hρ0 hle₆) (h7' ρ hρ0 hle₇)
    exact exists_varEstHalfFin_of_varpΛ_minorArc hr1 hp1 hvarp (hρ₅ ρ hρ0 hle₅)

/-- **The composition of the eight areas into the paper's Theorem `end-var`**
(`ROUTE_LEAD.md` §3.2).  Given the eight areas A1–A8, for every polynomial `P` and all exponents
`p₁, p₂, r` there is a constant `Cv` such that, under the hypotheses of Theorem 1.17,
`VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹+p₂⁻¹)⁻¹ r Cv` holds on the integer shift.  This is
the statement of the remaining hole `Submission.ShiftHole.exists_varEstHalfFin_Cv`, up to
supplying the eight areas as *theorems*. -/
theorem exists_varEstHalfFin_Cv_of_areas
    (h1 : AreaA1) (h2 : AreaA2) (h3 : AreaA3) (h4 : AreaA4) (h5 : AreaA5) (h6 : AreaA6)
    (h7 : AreaA7) (h8 : VarBilinInterp) (P : Polynomial ℤ) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) :
    ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv := by
  by_cases h : (P.degree ≥ 2) ∧ (1 < p₁) ∧ (1 < p₂) ∧ (p₁ < ⊤) ∧ (p₂ < ⊤) ∧
      (p₁⁻¹ + p₂⁻¹ ≤ 1) ∧ (2 < r)
  · obtain ⟨hPd, h1p₁, h1p₂, h2p₁, h2p₂, hH, hr⟩ := h
    obtain ⟨Cv, hCv⟩ := exists_varEstHalfFin_Cv_of_areas_aux h1 h2 h3 h4 h5 h6 h7 h8
      P p₁ p₂ r hPd h1p₁ h1p₂ h2p₁ h2p₂ hH hr
    exact ⟨Cv, fun _ _ _ _ _ _ _ => hCv⟩
  · exact ⟨0, fun hPd h1p₁ h1p₂ h2p₁ h2p₂ hH hr =>
      absurd ⟨hPd, h1p₁, h1p₂, h2p₁, h2p₂, hH, hr⟩ h⟩

/-- The composition in the shape of `Submission.ShiftHole.exists_varEstHalfFin_Cv`. -/
theorem exists_varEstHalfFin_Cv_of_areas_forall
    (h1 : AreaA1) (h2 : AreaA2) (h3 : AreaA3) (h4 : AreaA4) (h5 : AreaA5) (h6 : AreaA6)
    (h7 : AreaA7) (h8 : VarBilinInterp) :
    ∀ (P : Polynomial ℤ) (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0), ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv :=
  fun P p₁ p₂ r => exists_varEstHalfFin_Cv_of_areas h1 h2 h3 h4 h5 h6 h7 h8 P p₁ p₂ r

/-- The same, from the conjunction `AllAreas` of the eight areas. -/
theorem exists_varEstHalfFin_Cv_of_allAreas (h : AllAreas) (P : Polynomial ℤ)
    (p₁ p₂ : ℝ≥0∞) (r : ℝ≥0) : ∃ Cv : ℝ≥0 → ℝ≥0,
      (P.degree ≥ 2) → (1 < p₁) → (1 < p₂) → (p₁ < ⊤) → (p₂ < ⊤) →
        (p₁⁻¹ + p₂⁻¹ ≤ 1) → (2 < r) →
          VarEstHalfFin TZ Measure.count P p₁ p₂ (p₁⁻¹ + p₂⁻¹)⁻¹ r Cv :=
  exists_varEstHalfFin_Cv_of_areas h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 P p₁ p₂ r

end

end Work.KMTContract
