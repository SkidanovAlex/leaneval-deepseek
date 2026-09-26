/-
# The six `SL(2,ℤ)`-translates of the closure of `𝓕` lie in the closure of `𝒟`

CKMRV (proof of Prop. 3.2(1)) write the `Γ(2)`-fundamental domain `𝒟` (their (3.12)) as the
union of the six `SL(2,ℤ)`-translates of the standard fundamental domain `𝓕` (their (3.13)),
cut out by `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)`.  The present file verifies the *containment*

  `γ • closure 𝓕 ⊆ closure 𝒟`   for each of the six `γ = Mp i`,

which is the half of the tiling statement used to propagate bounds from `𝓕` to `𝒟`.

The route is: each `Mp i` is a composition of the two Möbius maps `S : z ↦ -1/z` and
`T : z ↦ z + 1`, and a closed set argument

  `{σ | Mp i • σ ∈ closure 𝒟}` is closed and contains `𝓕`, hence contains `closure 𝓕`.

For the containment of `𝓕` one shows the slightly stronger statement `Mp i • 𝓕 ⊆ 𝒟` (both
domains are *open* here), which is elementary geometry:

* `S • u ∈ 𝒟` whenever `-1 < Re u < 1` and `|u| > 1`;
* `T • z ∈ 𝒟` whenever `z ∈ 𝒟` and `-1 < Re z < 0`;
* `T⁻¹ • z ∈ 𝒟` whenever `z ∈ 𝒟` and `0 < Re z < 1`.

The three lemmas `re_S_smul_pos` / `re_S_smul_neg` then supply the sign information needed to
chain them, and `DomainF_subset_DomainD` (from `DomainD.lean`) covers the identity translate.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainTiling

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ### Auxiliary estimates for norms of complex numbers -/

/-- If the real part of `w : ℂ` exceeds `1/2`, then so does `‖w‖`. -/
private lemma half_lt_norm_of_re {w : ℂ} (h : (1 : ℝ) / 2 < w.re) : (1 : ℝ) / 2 < ‖w‖ := by
  have := Complex.abs_re_le_norm w
  rw [abs_of_pos (by linarith)] at this
  linarith

/-- If the real part of `w : ℂ` is below `-1/2`, then `‖w‖` exceeds `1/2`. -/
private lemma half_lt_norm_of_neg_re {w : ℂ} (h : w.re < -(1 : ℝ) / 2) : (1 : ℝ) / 2 < ‖w‖ := by
  have := Complex.abs_re_le_norm w
  rw [abs_of_neg (by linarith)] at this
  linarith

/-! ### The three elementary transports -/

/-- `S : z ↦ -1/z` sends the region `{-1 < Re u < 1, |u| > 1}` into `𝒟`.

Indeed `Re(-1/u) = -Re u/|u|²` has absolute value `< 1`, while
`| -1/u ∓ 1/2 | = |u ± 2| / (2|u|) > 1/2` because `|u+2| > |u| ↔ Re u > -1` and
`|u-2| > |u| ↔ Re u < 1`. -/
private theorem S_smul_mem_DomainD {u : ℍ} (h1 : -1 < u.re) (h2 : u.re < 1)
    (h3 : 1 < ‖(u : ℂ)‖) : S • u ∈ DomainD := by
  rw [Work.Asymptotics.mem_DomainD]
  have hcoe : ((S • u : ℍ) : ℂ) = (-(u : ℂ))⁻¹ :=
    congrArg UpperHalfPlane.coe (modular_S_smul u)
  have hne : (u : ℂ) ≠ 0 := u.ne_zero
  have hN : 1 < Complex.normSq (u : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (u : ℂ)]
  have hkey1 : ‖(u : ℂ)‖ < ‖(u : ℂ) + 2‖ := by
    have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) + 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      rw [Complex.add_re, Complex.add_im,
        show ((2 : ℂ)).re = 2 from by norm_num, show ((2 : ℂ)).im = 0 from by norm_num,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      nlinarith [h1]
    nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) + 2)]
  have hkey2 : ‖(u : ℂ)‖ < ‖(u : ℂ) - 2‖ := by
    have hsq : ‖(u : ℂ)‖ ^ 2 < ‖(u : ℂ) - 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      rw [Complex.sub_re, Complex.sub_im,
        show ((2 : ℂ)).re = 2 from by norm_num, show ((2 : ℂ)).im = 0 from by norm_num,
        UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      nlinarith [h2]
    nlinarith [hsq, norm_nonneg (u : ℂ), norm_nonneg ((u : ℂ) - 2)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← UpperHalfPlane.coe_re, hcoe, Complex.inv_re]
    simp only [Complex.neg_re, Complex.normSq_neg, UpperHalfPlane.coe_re]
    rw [neg_div, neg_lt_neg_iff, div_lt_one (UpperHalfPlane.normSq_pos u)]
    linarith
  · rw [← UpperHalfPlane.coe_re, hcoe, Complex.inv_re]
    simp only [Complex.neg_re, Complex.normSq_neg, UpperHalfPlane.coe_re]
    rw [div_lt_iff₀ (UpperHalfPlane.normSq_pos u)]
    linarith
  · rw [hcoe, show (-(u : ℂ))⁻¹ - (1 / 2 : ℂ) = -((u : ℂ) + 2) / (2 * (u : ℂ)) from by
      rw [inv_neg]; field_simp; ring,
      norm_div, norm_neg, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hkey1]
  · rw [hcoe, show (-(u : ℂ))⁻¹ + (1 / 2 : ℂ) = ((u : ℂ) - 2) / (2 * (u : ℂ)) from by
      rw [inv_neg]; field_simp; ring,
      norm_div, norm_mul, Complex.norm_ofNat]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hkey2]

/-- `T : z ↦ z + 1` sends `{z ∈ 𝒟 : -1 < Re z < 0}` into `𝒟`. -/
private theorem T_smul_mem_DomainD {z : ℍ} (hz : z ∈ DomainD) (h1 : -1 < z.re)
    (h2 : z.re < 0) : T • z ∈ DomainD := by
  rw [Work.Asymptotics.mem_DomainD] at hz ⊢
  obtain ⟨-, -, hz3, hz4⟩ := hz
  have hcoe : ((T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    have := ModularGroup.coe_T_zpow_smul_eq z (n := 1)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ModularGroup.re_T_smul]; linarith
  · rw [ModularGroup.re_T_smul]; linarith
  · rw [hcoe]
    have : (z : ℂ) + 1 - (1 / 2 : ℂ) = (z : ℂ) + (1 / 2 : ℂ) := by ring
    rw [this]; exact hz4
  · rw [hcoe]
    have h : (z : ℂ) + 1 + (1 / 2 : ℂ) = (z : ℂ) + ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    apply half_lt_norm_of_re
    rw [Complex.add_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
    linarith

/-- `T⁻¹ : z ↦ z - 1` sends `{z ∈ 𝒟 : 0 < Re z < 1}` into `𝒟`. -/
private theorem T_inv_smul_mem_DomainD {z : ℍ} (hz : z ∈ DomainD) (h1 : 0 < z.re)
    (h2 : z.re < 1) : T⁻¹ • z ∈ DomainD := by
  rw [Work.Asymptotics.mem_DomainD] at hz ⊢
  obtain ⟨-, -, hz3, hz4⟩ := hz
  have hcoe : ((T⁻¹ • z : ℍ) : ℂ) = (z : ℂ) - 1 := by
    have h := ModularGroup.coe_T_zpow_smul_eq z (n := -1)
    simpa [sub_eq_add_neg] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ModularGroup.re_T_inv_smul]; linarith
  · rw [ModularGroup.re_T_inv_smul]; linarith
  · rw [hcoe]
    have h : (z : ℂ) - 1 - (1 / 2 : ℂ) = (z : ℂ) - ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    apply half_lt_norm_of_neg_re
    rw [Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re]
    linarith
  · rw [hcoe]
    have : (z : ℂ) - 1 + (1 / 2 : ℂ) = (z : ℂ) - (1 / 2 : ℂ) := by ring
    rw [this]; exact hz3

/-- The real part of `S • u = -1/u`: `Re(-1/u) = -Re u / |u|²`. -/
private lemma re_S_smul {u : ℍ} : (S • u).re = -u.re / Complex.normSq (u : ℂ) := by
  rw [← UpperHalfPlane.coe_re, congrArg UpperHalfPlane.coe (modular_S_smul u), Complex.inv_re]
  simp only [Complex.neg_re, Complex.normSq_neg, UpperHalfPlane.coe_re]

/-- With `-1 < Re u < 0` and `|u| > 1`, the image `S • u` has real part in `(0,1)`. -/
private lemma re_S_smul_pos {u : ℍ} (h1 : -1 < u.re) (h2 : u.re < 0) (h3 : 1 < ‖(u : ℂ)‖) :
    0 < (S • u).re ∧ (S • u).re < 1 := by
  have hN : 1 < Complex.normSq (u : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (u : ℂ)]
  have hNpos := UpperHalfPlane.normSq_pos u
  rw [re_S_smul]
  constructor
  · exact div_pos (by linarith) hNpos
  · rw [div_lt_one hNpos]; linarith

/-- With `0 < Re u < 1` and `|u| > 1`, the image `S • u` has real part in `(-1,0)`. -/
private lemma re_S_smul_neg {u : ℍ} (h1 : 0 < u.re) (h2 : u.re < 1) (h3 : 1 < ‖(u : ℂ)‖) :
    -1 < (S • u).re ∧ (S • u).re < 0 := by
  have hN : 1 < Complex.normSq (u : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (u : ℂ)]
  have hNpos := UpperHalfPlane.normSq_pos u
  rw [re_S_smul]
  constructor
  · rw [neg_div, neg_lt_neg_iff, div_lt_one hNpos]; linarith
  · rw [neg_div, neg_lt_zero]; exact div_pos h1 hNpos

/-! ### The translate `𝓕` lies in `𝒟` -/

/-- Each of the six translates `Mp i • σ` of a point `σ ∈ 𝓕` lies in the open domain `𝒟`. -/
private lemma Mp_smul_mem_DomainD (i : Fin 6) {σ : ℍ} (hσ : σ ∈ DomainF) :
    Mp i • σ ∈ DomainD := by
  have hσD : σ ∈ DomainD := DomainF_subset_DomainD hσ
  rw [mem_DomainF] at hσ
  obtain ⟨hre0, hre1, hnorm, hnorm1⟩ := hσ
  fin_cases i
  · -- `Mp 0 = 1`
    change Mp (0 : Fin 6) • σ ∈ DomainD
    rw [show Mp (0 : Fin 6) = 1 by decide, one_smul]; exact hσD
  · -- `Mp 1 = T⁻¹`
    change Mp (1 : Fin 6) • σ ∈ DomainD
    rw [show Mp (1 : Fin 6) = T⁻¹ by decide]
    exact T_inv_smul_mem_DomainD hσD hre0 hre1
  · -- `Mp 2 = S * T * S = T⁻¹ * S * T⁻¹`
    change Mp (2 : Fin 6) • σ ∈ DomainD
    rw [show Mp (2 : Fin 6) = S * T * S by decide,
      show (S * T * S : SL(2, ℤ)) = T⁻¹ * S * T⁻¹ by decide, mul_smul, mul_smul]
    have hu1coe : ((T⁻¹ • σ : ℍ) : ℂ) = (σ : ℂ) - 1 := by
      have h := ModularGroup.coe_T_zpow_smul_eq σ (n := -1)
      simpa [sub_eq_add_neg] using h
    have h1u1 : -1 < (T⁻¹ • σ).re := by rw [ModularGroup.re_T_inv_smul]; linarith
    have h2u1 : (T⁻¹ • σ).re < 0 := by rw [ModularGroup.re_T_inv_smul]; linarith
    have h3u1 : 1 < ‖((T⁻¹ • σ : ℍ) : ℂ)‖ := by rw [hu1coe]; exact hnorm1
    have hS : S • (T⁻¹ • σ) ∈ DomainD := S_smul_mem_DomainD h1u1 (by linarith) h3u1
    have hpos := re_S_smul_pos h1u1 h2u1 h3u1
    exact T_inv_smul_mem_DomainD hS hpos.1 hpos.2
  · -- `Mp 3 = S`
    change Mp (3 : Fin 6) • σ ∈ DomainD
    rw [show Mp (3 : Fin 6) = S by decide]
    exact S_smul_mem_DomainD (by linarith) hre1 hnorm
  · -- `Mp 4 = S * T⁻¹`
    change Mp (4 : Fin 6) • σ ∈ DomainD
    rw [show Mp (4 : Fin 6) = S * T⁻¹ by decide, mul_smul]
    have hu1coe : ((T⁻¹ • σ : ℍ) : ℂ) = (σ : ℂ) - 1 := by
      have h := ModularGroup.coe_T_zpow_smul_eq σ (n := -1)
      simpa [sub_eq_add_neg] using h
    refine S_smul_mem_DomainD ?_ ?_ ?_
    · rw [ModularGroup.re_T_inv_smul]; linarith
    · rw [ModularGroup.re_T_inv_smul]; linarith
    · rw [hu1coe]; exact hnorm1
  · -- `Mp 5 = T * S`
    change Mp (5 : Fin 6) • σ ∈ DomainD
    rw [show Mp (5 : Fin 6) = T * S by decide, mul_smul]
    have hS : S • σ ∈ DomainD := S_smul_mem_DomainD (by linarith) hre1 hnorm
    have hneg := re_S_smul_neg hre0 hre1 hnorm
    exact T_smul_mem_DomainD hS hneg.1 hneg.2

/-! ### The closure statement -/

theorem Mp_smul_mem_closure_DomainD (i : Fin 6) {τ : UpperHalfPlane}
    (hτ : τ ∈ closure Work.Asymptotics.DomainF) :
    Work.Asymptotics.Mp i • τ ∈ closure Work.Asymptotics.DomainD := by
  -- `{σ | Mp i • σ ∈ closure 𝒟}` is closed (preimage of a closed set under a continuous map)
  -- and contains `𝓕`, hence contains `closure 𝓕`.
  have hcont : Continuous fun σ : ℍ => Mp i • σ := by
    haveI : ContinuousSMul SL(2, ℤ) ℍ :=
      MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
        continuous_of_discreteTopology
    exact continuous_const_smul (Mp i)
  have hclosed : IsClosed {σ : ℍ | Mp i • σ ∈ closure DomainD} :=
    isClosed_closure.preimage hcont
  refine closure_minimal ?_ hclosed hτ
  intro σ hσ
  exact subset_closure (Mp_smul_mem_DomainD i hσ)

end Work.Asymptotics
