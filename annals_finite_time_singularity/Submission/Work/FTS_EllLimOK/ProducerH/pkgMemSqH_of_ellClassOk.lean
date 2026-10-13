import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_chain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK.ProducerH.pkgMemSqH_of_ellClassOk`

The producer lemma: from the packages `EllClassOk 8`, `EllPkgGo Ce` and `EllPkgK 6 Ce` for `E g`
(whenever `g` is of class `C`), both `E g` and `E g / cos θ` are in `ℋ⁰` with all bounds.

The proof is a pure scaling argument on top of `pkgMemSqH_chain`.  Writing

* `Φ̃ := PhiTil α g (E g)` (smooth on the quadrant, `Φ̃ = psiP α Φ̃` by `kappa_eq_zero`),
* `Θ := Theta α g` (the singular part),

one has `E g = Φ̃ + Θ` and `E g / cos = Φ̃/cos + Θ/cos`, and `pkgMemSqH_chain` supplies the bounds

* `HkSq α 0 (E gg/cos) ≤ CC (1 + Xn6 α gg)²`, `HkSq α 0 (E gg) ≤ CC (1 + Xn6 α gg)²`,
* `∫_θ HkIntegrand α 0 (E gg/cos) z θ ≤ CC (1 + 1/z) (1 + Xn6 α gg)²`, and the same for `E gg`,

for each `gg` of class `C`, **with a constant `1` added to `Xn6 α gg`**.  The conclusion needs
`CC * (Xn6 α g)²` (no `1 +`).  The `1 +` is removed by homogeneity: `E` is linear
(`E (t • g) = t • E g`), `Xn6 α (t • g) = t Xn6 α g`, `HkSq α 0 (t•f) = t² HkSq α 0 f`, so applying
the chain to `t • g` for `t = n + 1` and dividing by `t²` gives `t² · S ≤ CC (1 + t X)²` for every
`t > 0`; dividing by `t²` and letting `t → ∞` gives `S ≤ CC X²`.  The slice bounds are handled the
same way (`integral_HkIntegrand_zero_smul`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem pkgMemSqH_of_ellClassOk :
    ∃ α₁ : ℝ, 0 < α₁ ∧ ∀ α : ℝ, 0 < α → α ≤ α₁ → ∀ Ce : ℝ,
      ∀ E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn,
        (∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
          Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
            Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce g (E g)) →
        ∃ Ce' : ℝ, 0 < Ce' ∧ Work.FTS_EllLimOK.RulingELF.PkgMemSqH α (max Ce Ce') E := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα1 Ce E hE
  obtain ⟨K, hKpos, hSlotBd⟩ := slotBd_phiTil (α := α) hα (by linarith)
  obtain ⟨CB, hCBpos, hPsiP⟩ := psiP_div_cos (α := α) hα (by linarith)
  obtain ⟨CT, hCTpos, hThetaB⟩ := Work.FTS_EllLimOK.PkgJets.thetaBound hα (by linarith)
  obtain ⟨CS, hCSpos, hThetaS⟩ := thetaDivCos_slice (α := α) hα (by linarith)
  set CC : ℝ := (2 * CB * Ce ^ 2 + 2 * CT) + (2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS) + 1
    with hCC
  have hCCpos : 0 < CC := by rw [hCC]; positivity
  have hCC1 : 2 * CB * Ce ^ 2 + 2 * CT ≤ CC := by
    rw [hCC]
    have h3 : 0 ≤ 2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS := by positivity
    linarith
  have hCC2 : 2 * CB * (K ^ 2 * Ce ^ 2 + Ce ^ 2) + 2 * CS ≤ CC := by
    rw [hCC]
    have h1 : 0 ≤ 2 * CB * Ce ^ 2 := by positivity
    have h2 : 0 ≤ 2 * CT := by positivity
    linarith
  have hchain := pkgMemSqH_chain (α := α) (Ce := Ce) (K := K) (CB := CB) (CT := CT) (CS := CS)
    (CC := CC) hα (by linarith) hKpos hCBpos hCTpos hCSpos hSlotBd hPsiP hThetaB hThetaS hCC1 hCC2
  refine ⟨CC, hCCpos, ?_⟩
  intro g hg
  obtain ⟨⟨hmemf, hsqf, hslicef⟩, hmemE, hsqE, hsliceE⟩ := hchain E hE g hg
  set X : ℝ := Work.FTS.StrongGlobal.Xn6 α g with hX
  have hXnn : 0 ≤ X := by rw [hX]; exact Work.Spaces.HkNorm_nonneg α 6 g
  have hXn : ∀ t : ℝ, 0 < t → Work.FTS.StrongGlobal.Xn6 α (t • g) = t * X := by
    intro t ht
    rw [Work.FTS.StrongGlobal.Xn6, Work.FTS.EllipticEst.HkNorm_smul, abs_of_pos ht, hX]
  -- the scaled `HkSq` bounds
  have hscaleHkE : Work.Spaces.HkSq α 0 (E g) ≤ CC * X ^ 2 := by
    refine scale_limit (C := CC) (X := X) ?_
    intro t ht
    obtain ⟨_, _, hsqEt, _⟩ := hchain E hE (t • g) (Work.FTS.ClassC.classC_smul t hg)
    have h2 : Work.Spaces.HkSq α 0 (E (t • g)) = t ^ 2 * Work.Spaces.HkSq α 0 (E g) := by
      rw [map_smul, Work.FTS.EllipticEst.HkSq_smul]
    rw [h2, hXn t ht] at hsqEt
    exact hsqEt
  have hscaleHkf : Work.Spaces.HkSq α 0 (fun z θ => E g z θ / Real.cos θ) ≤ CC * X ^ 2 := by
    refine scale_limit (C := CC) (X := X) ?_
    intro t ht
    obtain ⟨⟨_, hsqft, _⟩, _⟩ := hchain E hE (t • g) (Work.FTS.ClassC.classC_smul t hg)
    have hfun : (fun z θ => E (t • g) z θ / Real.cos θ)
        = t • (fun z θ => E g z θ / Real.cos θ) := by
      funext z θ
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : Work.Spaces.HkSq α 0 (fun z θ => E (t • g) z θ / Real.cos θ)
        = t ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => E g z θ / Real.cos θ) := by
      rw [hfun, Work.FTS.EllipticEst.HkSq_smul]
    rw [h2, hXn t ht] at hsqft
    exact hsqft
  -- the scaled slice bounds
  have hscaledE : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (E g) z θ) ≤ CC * (1 + 1 / z) * X ^ 2 := by
    intro z hz
    have hmain : ∀ t : ℝ, 0 < t → t ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (E g) z θ) ≤ CC * (1 + 1 / z) * (1 + t * X) ^ 2 := by
      intro t ht
      obtain ⟨⟨_, _, _⟩, _, _, hsliceEt⟩ := hchain E hE (t • g) (Work.FTS.ClassC.classC_smul t hg)
      have hz' := hsliceEt z hz
      have h2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E (t • g)) z θ)
          = t ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E g) z θ) := by
        rw [map_smul, integral_HkIntegrand_zero_smul]
      rw [h2, hXn t ht] at hz'
      exact hz'
    have hnat : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E g) z θ)
        ≤ CC * (1 + 1 / z) * (1 / ((n : ℝ) + 1) + X) ^ 2 := by
      intro n
      have ht : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := hmain _ ht
      have h3 : ((1 : ℝ) / ((n : ℝ) + 1) + X) = (1 + ((n : ℝ) + 1) * X) / ((n : ℝ) + 1) := by
        field_simp
      rw [h3, div_pow, show CC * (1 + 1 / z)
            * ((1 + ((n : ℝ) + 1) * X) ^ 2 / ((n : ℝ) + 1) ^ 2)
          = (CC * (1 + 1 / z) * (1 + ((n : ℝ) + 1) * X) ^ 2) / ((n : ℝ) + 1) ^ 2 from by ring]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mpr (by linarith)
    have hlim : Filter.Tendsto (fun n : ℕ => CC * (1 + 1 / z)
        * (1 / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop (𝓝 (CC * (1 + 1 / z) * X ^ 2)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h4 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) + X) Filter.atTop
          (𝓝 (0 + X)) := h1.add tendsto_const_nhds
      have h5 := (h4.pow 2).const_mul (CC * (1 + 1 / z))
      simpa using h5
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hnat
  have hscaledf : ∀ z : ℝ, 0 < z → (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ)
      ≤ CC * (1 + 1 / z) * X ^ 2 := by
    intro z hz
    have hmain : ∀ t : ℝ, 0 < t → t ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ)
        ≤ CC * (1 + 1 / z) * (1 + t * X) ^ 2 := by
      intro t ht
      obtain ⟨⟨_, _, hsliceft⟩, _⟩ := hchain E hE (t • g) (Work.FTS.ClassC.classC_smul t hg)
      have hfun : (fun z θ => E (t • g) z θ / Real.cos θ)
          = t • (fun z θ => E g z θ / Real.cos θ) := by
        funext z θ
        rw [map_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have h2 : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E (t • g) z θ / Real.cos θ) z θ)
          = t ^ 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ) := by
        rw [hfun, integral_HkIntegrand_zero_smul]
      have hz' := hsliceft z hz
      rw [h2, hXn t ht] at hz'
      exact hz'
    have hnat : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ)
        ≤ CC * (1 + 1 / z) * (1 / ((n : ℝ) + 1) + X) ^ 2 := by
      intro n
      have ht : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := hmain _ ht
      have h3 : ((1 : ℝ) / ((n : ℝ) + 1) + X) = (1 + ((n : ℝ) + 1) * X) / ((n : ℝ) + 1) := by
        field_simp
      rw [h3, div_pow, show CC * (1 + 1 / z)
            * ((1 + ((n : ℝ) + 1) * X) ^ 2 / ((n : ℝ) + 1) ^ 2)
          = (CC * (1 + 1 / z) * (1 + ((n : ℝ) + 1) * X) ^ 2) / ((n : ℝ) + 1) ^ 2 from by ring]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)).mpr (by linarith)
    have hlim : Filter.Tendsto (fun n : ℕ => CC * (1 + 1 / z)
        * (1 / ((n : ℝ) + 1) + X) ^ 2) Filter.atTop (𝓝 (CC * (1 + 1 / z) * X ^ 2)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h4 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) + X) Filter.atTop
          (𝓝 (0 + X)) := h1.add tendsto_const_nhds
      have h5 := (h4.pow 2).const_mul (CC * (1 + 1 / z))
      simpa using h5
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hnat
  -- conclusion
  have hle : CC ≤ max Ce CC := le_max_right _ _
  have hX2 : (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 = X ^ 2 := by rw [hX]
  have hkey := hchain E hE g hg
  intro Ψ hΨ
  rcases hΨ with hΨ | hΨ
  · subst hΨ
    exact ⟨hkey.2.1, by
        rw [hX2]; exact hscaleHkE.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)),
      fun z hz => by
        rw [hX2]
        have hc : (0 : ℝ) ≤ 1 + 1 / z := by positivity
        exact (hscaledE z hz).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle hc) (sq_nonneg _))⟩
  · subst hΨ
    exact ⟨hkey.1.1, by
        rw [hX2]; exact hscaleHkf.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)),
      fun z hz => by
        rw [hX2]
        have hc : (0 : ℝ) ≤ 1 + 1 / z := by positivity
        exact (hscaledf z hz).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle hc) (sq_nonneg _))⟩

end Work.FTS_EllLimOK.ProducerH
