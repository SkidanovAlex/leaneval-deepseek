/-
# Integrability of the modulated amplitudes `φ_{N,1}`, `φ̃_{N,-1}` (Area `A6`)

Krause--Mirek--Tao's integration-by-parts identity (`Work.KMTPlan.A6.MdlBumpIntegIdent`) absorbs
the singular factor `1/ξ` into the *modified* bumps of (pntj)/(tpntj),

  `φ_{N,t,k₁,j₁}(ξ) = (2^{-k₁}Nξ)^{j₁} φ_{N,t,k₁}(ξ)`,
  `φ̃_{N,t,k₂,j₂}(ξ) = (2^{-dk₂}N^dξ)^{j₂} φ̃_{N,t,k₂}(ξ)`,

so that the resulting identity can be fed into a Fubini identity
(`Work.KMTPlan.A6.CwFubiniWeight`, `Work.A7.cw_interval_integral_fubini`) whose hypotheses ask the
two bumps to be integrable on `ℝ`.  This file supplies exactly that, at `t = 0` and the two
exponents `j₁ = 1`, `j₂ = -1` (the two cases in which the paper's Lemma `integ-ident` produces
them), i.e. for the two functions

  `ξ ↦ (2^{-k₁}Nξ) · φ_N(ξ)`,      `ξ ↦ (2^{-dk₂}N^dξ)⁻¹ · φ̃_N(ξ)`

(`d = P.natDegree`, `φ_N = Work.KMTAreas.A7.varphiN N k₁`,
`φ̃_N = Work.KMTAreas.A7.varphitildeN d N k₂`).

## The mathematics

Both bumps are finite differences of rescalings `ξ ↦ η (cξ)` of the compactly supported KMT cutoff
`η = Work.KMTContract.kmtEta`:

* `φ_N(ξ) = η(2^{Λ-k₁}ξ) - η(2^{Λ-k₁+1}ξ)` (or `η(2^Λ ξ)` for `k₁ = 0`), `Λ = logN N`;
* `φ̃_N(ξ) = η(2^{d(Λ-k₂)}ξ) - η(2^{d(Λ-k₂)+1}ξ)` (the `if`-branch `k₂ = 0` being excluded by the
  hypothesis `1 ≤ k₂`).

Hence the amplitude `ξ φ_N(ξ)` is *continuous with compact support* (the factor `ξ` is continuous,
the bump is compactly supported), so it is integrable.

The reciprocal amplitude `ξ⁻¹ φ̃_N(ξ)` is not continuous by inspection, because `(cξ)⁻¹` blows up
at `ξ = 0`; what saves it is that `φ̃_N(0) = η(0) - η(0) = 0` **and** `η` is Lipschitz
(`Work.KMTPlan.A6.kmtEta_lipschitz`): for `ξ ≠ 0`,

  `‖(cξ)⁻¹(η(c₁ξ) - η(c₂ξ))‖ ≤ |cξ|⁻¹ · L|c₁ξ - c₂ξ| = L|c₁-c₂|/|c|`,

while at `ξ = 0` the function vanishes.  Together with the compact support of `φ̃_N` (the function
vanishes for `|ξ| > max (1/|c₁|) (1/|c₂|)`, by `kmtEta_zero`) this gives integrability through the
general criterion `integrable_of_bound_of_vanishing` below (a measurable function which is bounded
and vanishes outside a ball is Lebesgue-integrable).  The hypothesis `1 ≤ k₂` is what puts us in
the *difference* branch, where `φ̃_N(0) = 0`; at `k₂ = 0` the quotient would genuinely fail to be
integrable at the origin, which is why the paper's Lemma `integ-ident` excludes exactly the case
`(s,j) = (-u,-1)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTPlan.A6.kmtEta_lipschitz

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory

/-! ## A general integrability criterion -/

/-- **A measurable function on `ℝ` which is bounded and vanishes outside a ball is integrable.**
(On `ℝ` the closed balls have finite Lebesgue measure, so one restricts to `Icc (-R) R` and uses
`IntegrableOn.of_bound`, then removes the restriction using the vanishing.) -/
lemma integrable_of_bound_of_vanishing {f : ℝ → ℂ} {R K : ℝ} (hR : 0 ≤ R)
    (hmeas : AEStronglyMeasurable f volume) (hvan : ∀ ξ, R < |ξ| → f ξ = 0)
    (hbound : ∀ ξ, ‖f ξ‖ ≤ K) : Integrable f volume := by
  have hfin : volume (Set.Icc (-R) R) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hInt : IntegrableOn f (Set.Icc (-R) R) volume :=
    IntegrableOn.of_bound (s := Set.Icc (-R) R) hfin hmeas.restrict K
      (Filter.Eventually.of_forall hbound)
  refine hInt.integrable_of_forall_notMem_eq_zero (fun x hx => ?_)
  have hx1 : ¬ (-R ≤ x ∧ x ≤ R) := by simpa [Set.mem_Icc] using hx
  rcases lt_or_ge x (-R) with h | h
  · exact hvan x (by rw [abs_of_neg (by linarith)]; linarith)
  · have hx2 : R < x := not_le.mp (fun h' => hx1 ⟨h, h'⟩)
    exact hvan x (by rw [abs_of_nonneg (by linarith)]; linarith)

/-! ## Basic regularity of the KMT cutoff `η` -/

/-- The KMT cutoff `η` (the real `ContDiffBump` `kmtBump` cast to `ℂ`) has compact support. -/
lemma hasCompactSupport_kmtEta : HasCompactSupport Work.KMTContract.kmtEta :=
  (ContDiffBump.hasCompactSupport Work.KMTContract.kmtBump).comp_left
    (g := fun x : ℝ => (x : ℂ)) (by simp)

/-- The KMT cutoff `η` is continuous. -/
lemma continuous_kmtEta : Continuous Work.KMTContract.kmtEta :=
  Complex.continuous_ofReal.comp
    (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := 1)).continuous

/-- A nonzero rescaling `ξ ↦ η (c ξ)` of the KMT cutoff has compact support (transport along the
homeomorphism `ξ ↦ c ξ` of `ℝ`). -/
lemma hasCompactSupport_kmtEta_rescale (c : ℝ) (hc : c ≠ 0) :
    HasCompactSupport (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) := by
  have h := hasCompactSupport_kmtEta.comp_homeomorph (Homeomorph.mulLeft₀ c hc)
  rw [Homeomorph.coe_mulLeft₀] at h
  exact h

/-- A rescaling `ξ ↦ η (c ξ)` of the KMT cutoff is measurable. -/
lemma measurable_kmtEta_rescale (c : ℝ) :
    Measurable (fun ξ : ℝ => Work.KMTContract.kmtEta (c * ξ)) :=
  continuous_kmtEta.measurable.comp (measurable_const.mul measurable_id)

/-! ## The bumps `φ_N`, `φ̃_N` and their amplitudes -/

/-- The bump `φ_N` has compact support. -/
lemma hasCompactSupport_varphiN (N k₁ : ℕ) :
    HasCompactSupport (Work.KMTAreas.A7.varphiN N k₁) := by
  have hrpow : ∀ x : ℝ, (0 : ℝ) < (2 : ℝ) ^ x := fun x => Real.rpow_pos_of_pos (by norm_num) x
  by_cases h : k₁ = 0
  · rw [show Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ)
      from by simp only [Work.KMTAreas.A7.varphiN, h, if_true]]
    exact hasCompactSupport_kmtEta_rescale _ (ne_of_gt (hrpow _))
  · rw [show Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ))) * ξ)
              - Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1)) * ξ)
      from by simp only [Work.KMTAreas.A7.varphiN, h, if_false]]
    exact (hasCompactSupport_kmtEta_rescale _ (ne_of_gt (hrpow _))).sub
      (hasCompactSupport_kmtEta_rescale _ (ne_of_gt (hrpow _)))

/-- The bump `φ_N` is continuous. -/
lemma continuous_varphiN (N k₁ : ℕ) : Continuous (Work.KMTAreas.A7.varphiN N k₁) := by
  by_cases h : k₁ = 0
  · rw [show Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta (((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * ξ)
      from by simp only [Work.KMTAreas.A7.varphiN, h, if_true]]
    exact continuous_kmtEta.comp (continuous_const.mul continuous_id)
  · rw [show Work.KMTAreas.A7.varphiN N k₁
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ))) * ξ)
              - Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k₁ : ℝ) + 1)) * ξ)
      from by simp only [Work.KMTAreas.A7.varphiN, h, if_false]]
    exact (continuous_kmtEta.comp (continuous_const.mul continuous_id)).sub
      (continuous_kmtEta.comp (continuous_const.mul continuous_id))

/-- The bump `φ_N` is measurable. -/
lemma measurable_varphiN (N k₁ : ℕ) : Measurable (Work.KMTAreas.A7.varphiN N k₁) :=
  (continuous_varphiN N k₁).measurable

/-- The bump `φ̃_N` is measurable. -/
lemma measurable_varphitildeN (d N k₂ : ℕ) :
    Measurable (Work.KMTAreas.A7.varphitildeN d N k₂) := by
  by_cases h : k₂ = 0
  · rw [show Work.KMTAreas.A7.varphitildeN d N k₂
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) * ξ)
      from by simp only [Work.KMTAreas.A7.varphitildeN, h, if_true]]
    exact measurable_kmtEta_rescale _
  · rw [show Work.KMTAreas.A7.varphitildeN d N k₂
        = fun ξ : ℝ =>
            Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)))) * ξ)
              - Work.KMTContract.kmtEta
                (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1))) * ξ)
      from by simp only [Work.KMTAreas.A7.varphitildeN, h, if_false]]
    exact (measurable_kmtEta_rescale _).sub (measurable_kmtEta_rescale _)

/-- The linear amplitude factor `ξ ↦ 2^{-k₁}Nξ` is continuous. -/
lemma continuous_modAmp (N k₁ : ℕ) :
    Continuous (fun ξ : ℝ => ((((2 : ℝ) ^ (-(k₁ : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ)) := by
  fun_prop

/-- The reciprocal amplitude factor `ξ ↦ (cξ)⁻¹` is measurable. -/
lemma measurable_inv_real_mul (c : ℝ) :
    Measurable (fun ξ : ℝ => (((c * ξ : ℝ)) : ℂ)⁻¹) := by
  have h : Measurable (fun ξ : ℝ => (c * ξ)⁻¹) := (measurable_const.mul measurable_id).inv
  have h2 : Measurable (fun ξ : ℝ => (((c * ξ)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp h
  simpa only [Complex.ofReal_inv] using h2

/-! ## The reciprocal amplitude of a difference of rescalings -/

/-- Measurability of a reciprocal amplitude of a difference of two rescaled cutoffs. -/
lemma measurable_inv_mul_kmtEta_sub (c c₁ c₂ : ℝ) : Measurable (fun ξ : ℝ =>
    (((c * ξ : ℝ)) : ℂ)⁻¹
      * (Work.KMTContract.kmtEta (c₁ * ξ) - Work.KMTContract.kmtEta (c₂ * ξ))) :=
  (measurable_inv_real_mul c).mul
    ((measurable_kmtEta_rescale c₁).sub (measurable_kmtEta_rescale c₂))

/-- **Integrability of the reciprocal amplitude of a difference of two rescalings of `η`.**

For nonzero `c`, `c₁`, `c₂` the function `ξ ↦ (cξ)⁻¹ (η(c₁ξ) - η(c₂ξ))` is integrable on `ℝ`:
it is measurable, bounded by `max 1 (L|c₁-c₂|/|c|)` (`L` a Lipschitz constant of `η`, the difference
being `L|c₁-c₂||ξ| = O(|ξ|)` at the origin because the two values of `η` agree at `0`), and it
vanishes for `|ξ| > max (1/|c₁|) (1/|c₂|)` because each rescaled cutoff vanishes outside the unit
ball (`kmtEta_zero`). -/
lemma integrable_inv_mul_kmtEta_sub (c c₁ c₂ : ℝ) (hc : c ≠ 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    Integrable (fun ξ : ℝ => (((c * ξ : ℝ)) : ℂ)⁻¹
      * (Work.KMTContract.kmtEta (c₁ * ξ) - Work.KMTContract.kmtEta (c₂ * ξ))) := by
  obtain ⟨L₀, _hL₀, hlip⟩ := kmtEta_lipschitz
  refine integrable_of_bound_of_vanishing (R := max (1 / |c₁|) (1 / |c₂|))
    (K := max 1 (L₀ * |c₁ - c₂| / |c|)) ?_ ?_ ?_ ?_
  · positivity
  · exact (measurable_inv_mul_kmtEta_sub c c₁ c₂).aestronglyMeasurable
  · intro ξ hξ
    have h1 : Work.KMTContract.kmtEta (c₁ * ξ) = 0 := by
      apply Work.KMTContract.kmtEta_zero
      have hc1p : 0 < |c₁| := abs_pos.mpr hc₁
      have hlt : 1 / |c₁| < |ξ| := lt_of_le_of_lt (le_max_left _ _) hξ
      have hlt' : (1 : ℝ) < |c₁| * |ξ| := by
        have h := mul_lt_mul_of_pos_left hlt hc1p
        rw [mul_one_div, div_self (ne_of_gt hc1p)] at h
        exact h
      rw [abs_mul]
      exact le_of_lt hlt'
    have h2 : Work.KMTContract.kmtEta (c₂ * ξ) = 0 := by
      apply Work.KMTContract.kmtEta_zero
      have hc2p : 0 < |c₂| := abs_pos.mpr hc₂
      have hlt : 1 / |c₂| < |ξ| := lt_of_le_of_lt (le_max_right _ _) hξ
      have hlt' : (1 : ℝ) < |c₂| * |ξ| := by
        have h := mul_lt_mul_of_pos_left hlt hc2p
        rw [mul_one_div, div_self (ne_of_gt hc2p)] at h
        exact h
      rw [abs_mul]
      exact le_of_lt hlt'
    rw [h1, h2, sub_self, mul_zero]
  · intro ξ
    rcases eq_or_ne ξ 0 with hξ | hξ
    · subst hξ
      have h0 : (((c * (0 : ℝ) : ℝ)) : ℂ)⁻¹
          * (Work.KMTContract.kmtEta (c₁ * 0) - Work.KMTContract.kmtEta (c₂ * 0)) = 0 := by simp
      rw [h0, norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
    · calc ‖(((c * ξ : ℝ)) : ℂ)⁻¹
            * (Work.KMTContract.kmtEta (c₁ * ξ) - Work.KMTContract.kmtEta (c₂ * ξ))‖
          = ‖((((c * ξ : ℝ)) : ℂ))⁻¹‖
              * ‖Work.KMTContract.kmtEta (c₁ * ξ) - Work.KMTContract.kmtEta (c₂ * ξ)‖ :=
            norm_mul _ _
        _ = |c * ξ|⁻¹
              * ‖Work.KMTContract.kmtEta (c₁ * ξ) - Work.KMTContract.kmtEta (c₂ * ξ)‖ := by
            rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |c * ξ|⁻¹ * (L₀ * |c₁ * ξ - c₂ * ξ|) :=
            mul_le_mul_of_nonneg_left (hlip _ _) (by positivity)
        _ = L₀ * |c₁ - c₂| / |c| := by
            rw [show c₁ * ξ - c₂ * ξ = (c₁ - c₂) * ξ by ring, abs_mul, abs_mul,
              div_eq_mul_inv, mul_inv]
            field_simp
        _ ≤ max 1 (L₀ * |c₁ - c₂| / |c|) := le_max_right _ _

/-! ## The target -/

theorem VarpModAmpInt (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (hk₂ : 1 ≤ k₂) :
    (MeasureTheory.Integrable (fun ξ : ℝ => ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ : ℝ)) : ℂ) * Work.KMTAreas.A7.varphiN N k₁ ξ) ∧
     Measurable (fun ξ : ℝ => ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ : ℝ)) : ℂ) * Work.KMTAreas.A7.varphiN N k₁ ξ)) ∧
    (MeasureTheory.Integrable (fun ξ : ℝ =>
        ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ : ℝ)) : ℂ)⁻¹
          * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ ξ) ∧
     Measurable (fun ξ : ℝ =>
        ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ : ℝ)) : ℂ)⁻¹
          * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ ξ)) := by
  have hk₂ne : k₂ ≠ 0 := by omega
  -- the `φ̃`-side is the *difference* branch of `varphitildeN`, hence vanishes at the origin
  have hphit_f : ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ ξ
      = Work.KMTContract.kmtEta
          (((2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ))))
            * ξ)
        - Work.KMTContract.kmtEta
          (((2 : ℝ) ^ ((P.natDegree : ℝ)
              * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1))) * ξ) := by
    intro ξ
    by_cases hk : k₂ = 0
    · exact absurd hk hk₂ne
    · simp only [Work.KMTAreas.A7.varphitildeN, hk, if_false]
  have hrpow : ∀ x : ℝ, (0 : ℝ) < (2 : ℝ) ^ x := fun x => Real.rpow_pos_of_pos (by norm_num) x
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hc : ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ((N : ℝ)) ^ P.natDegree) ≠ 0 :=
    mul_ne_zero (ne_of_gt (hrpow _)) (pow_ne_zero _ (ne_of_gt hNpos))
  have hc₁ : ((2 : ℝ) ^ ((P.natDegree : ℝ)
      * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ)))) ≠ 0 := ne_of_gt (hrpow _)
  have hc₂ : ((2 : ℝ) ^ ((P.natDegree : ℝ)
      * ((Work.Analysis.EndVar.logN N : ℝ) - (k₂ : ℝ) + 1))) ≠ 0 := ne_of_gt (hrpow _)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- `Integrable` of the `φ`-amplitude: continuous with compact support
    exact ((continuous_modAmp N k₁).mul (continuous_varphiN N k₁)).integrable_of_hasCompactSupport
      ((hasCompactSupport_varphiN N k₁).mul_left)
  · -- `Measurable` of the `φ`-amplitude
    exact (continuous_modAmp N k₁).measurable.mul (measurable_varphiN N k₁)
  · -- `Integrable` of the `φ̃`-reciprocal amplitude: reduce to the difference form
    simp only [hphit_f]
    exact integrable_inv_mul_kmtEta_sub _ _ _ hc hc₁ hc₂
  · -- `Measurable` of the `φ̃`-reciprocal amplitude
    simp only [hphit_f]
    exact measurable_inv_mul_kmtEta_sub _ _ _

end Work.KMTPlan.A6
