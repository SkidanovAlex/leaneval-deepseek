/-
# ZeroFreeTables — HBRepZeroC_proof

`Work.ZeroFreeTables.HBRepZeroC`: for `q` large, if `(χ₁, ρ₁)` realises the minimum
`λ₁` of `λ` over the non-principal zeros of the strip `|Im| ≤ 10`, if `(χ₁, ρ₁)` is not a
real-real pair, if `ρ₁` is a **multiple** zero of `χ₁` (`2 ≤ zeroMult χ₁ ρ₁`) and
`λ₁ ≤ 7/10`, then `λ₁ ≥ 696/1000`.

Two independent routes are established here, both reducing `HBRepZeroC` to a single
deep input and leaving only elementary work to this file.

## Route 1 — HB Theorem 2 (`HBRepZeroC_of_thm2`)

HB Theorem 2 (p. 3): for `q` large, `∏_{χ mod q} L(s,χ)` has at most `2` zeros,
counted with multiplicity, in `σ ≥ 1 − 0.696/log q`, `|t| ≤ 1`.  A multiple zero
`ρ₁` of `χ₁` outside the real-real case produces **four** counted zeros of that
product as soon as `λ₁ ≤ 696/1000`: the pairs `(χ₁, ρ₁)` and `(χ₁⁻¹, conj ρ₁)` are
distinct, `zeroMult χ₁⁻¹ (conj ρ₁) = zeroMult χ₁ ρ₁ ≥ 2`
(`Work.A7.zeroMult_conj_inv`: the level-independent Schwarz reflection
`Λ(χ⁻¹)(conj s) = conj(Λ(χ)(s))`), `λ(conj ρ₁) = λ(ρ₁)` and
`|Im conj ρ₁| = |Im ρ₁|`.  See `HBRepZeroC_defs.HBThm2Count`.

## Route 2 — HB Lemma 9.1 at a repeated zero (`HBRepZeroC_of_rep`)

HB's §9 derivation is run at the *double* zero `ρ₁` (the test points `σ+iγ₀` and
`σ+iγ₁` coincide): the multiplicity `2` multiplies the near-zero terms
`Re P₃(α/((s−ρ₁)𝓛))` of the explicit formula, so the inequality obtained is
*stronger* than the distinct-zero one, and its lossy form is `ineq913 λ₁ λ₁ a K ε`.
Its numerical content is exactly the certificate row `(0.696, 0.696, a = 269/100)` of
HB's Table 8 — `Table8CertExtPrinted` already proves
`cond913 (696/1000) (696/1000) (269/100) (Kaff (696/1000))` and
`p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000)) < 0`, the tangency point of
(9.13) — and the rest is the monotonicity of `p913` along the diagonal and the choice
`ε = -p913(diag)/(2(a+0.696))`.  See `HBRepZeroC_defs.HBLemma9_1_rep`.

The real-real case (`χ₁² = 1`, `ρ₁.im = 0`), which `HBRepZeroC` excludes, is HB
Table 4's entry `(0.7, 1.724)` (`HBRepZero_red.hbRepZero_of_table4`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Work.ZeroFreeTables.HBRepZeroC_defs
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.ZeroFreeTables.HBLemma9_1_rep_proof

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Route 1: HB Theorem 2 implies `HBRepZeroC` -/

/-- **HB Theorem 2 ⇒ `HBRepZeroC`.**  A multiple zero `ρ₁` of `χ₁` outside the real-real
case contributes four counted zeros of the product `∏_χ L(s,χ)`: the pairs
`(χ₁, ρ₁)` and `(χ₁⁻¹, conj ρ₁)`, of equal multiplicity `≥ 2`, with
`λ(conj ρ₁) = λ(ρ₁)` and `|Im conj ρ₁| = |Im ρ₁|`; HB Theorem 2 allows at most two. -/
theorem HBRepZeroC_of_thm2 (h : HBThm2Count) : HBRepZeroC := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun q hq _ χ₁ ρ₁ hm hnr hmult hlam7 => ?_⟩
  by_cases hge : 696/1000 ≤ lamOf q ρ₁
  · exact hge
  · exfalso
    have hlt : lamOf q ρ₁ < 696/1000 := lt_of_not_ge hge
    have hZ : IsZ χ₁ ρ₁ := hm.1.1
    have hχ₁ : χ₁ ≠ 1 := hZ.1
    have hχ₂ : χ₁⁻¹ ≠ 1 := fun hc => hχ₁ (inv_eq_one.mp hc)
    have hzm : zeroMult χ₁⁻¹ ((starRingEnd ℂ) ρ₁) = zeroMult χ₁ ρ₁ :=
      Work.A7.zeroMult_conj_inv χ₁ ρ₁
    have hlam : lamOf q ((starRingEnd ℂ) ρ₁) = lamOf q ρ₁ := hbRZC_lamOf_conj q ρ₁
    have him : |((starRingEnd ℂ) ρ₁).im| ≤ 1 := by
      have h := hZ.2.2
      simpa [Complex.conj_im] using h
    -- the two pairs are distinct: otherwise `χ₁² = 1` and `ρ₁.im = 0`
    have hpair : (χ₁, ρ₁) ≠ (χ₁⁻¹, (starRingEnd ℂ) ρ₁) := by
      intro heq
      have h1 : χ₁ = χ₁⁻¹ := (Prod.ext_iff.mp heq).1
      have h2 : ρ₁ = (starRingEnd ℂ) ρ₁ := (Prod.ext_iff.mp heq).2
      apply hnr
      refine ⟨?_, ?_⟩
      · have h' := congrArg (fun g : DirichletCharacter ℂ q => g * χ₁) h1
        rw [pow_two, h']
        exact inv_mul_cancel χ₁
      · exact Complex.conj_eq_iff_im.mp h2.symm
    set S : Finset (DirichletCharacter ℂ q × ℂ) :=
      {(χ₁, ρ₁), (χ₁⁻¹, (starRingEnd ℂ) ρ₁)} with hSdef
    have hcond : ∀ p ∈ S, p.1 ≠ 1 ∧ lamOf q p.2 ≤ 696/1000 ∧ |p.2.im| ≤ 1 := by
      intro p hp
      rw [hSdef] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp
      · rw [hp]; exact ⟨hχ₁, le_of_lt hlt, hZ.2.2⟩
      · rw [hp]; exact ⟨hχ₂, by rw [hlam]; exact le_of_lt hlt, him⟩
    have hup : S.sum (fun p => zeroMult p.1 p.2) ≤ 2 := hN q hq S hcond
    have hsum : S.sum (fun p => zeroMult p.1 p.2)
        = zeroMult χ₁ ρ₁ + zeroMult χ₁⁻¹ ((starRingEnd ℂ) ρ₁) := by
      rw [hSdef, Finset.sum_insert (by simp [hpair]), Finset.sum_singleton]
    rw [hsum, hzm] at hup
    omega

/-! ## Route 2: HB Lemma 9.1 at the repeated zero -/

/-- **The diagonal row of HB Table 8 for a repeated zero**: from the repeated-zero
engine inequality (`HBLemma9_1_rep`) and the certified entry `(0.696, 0.696)`,
`λ₁ ≥ 696/1000` for every multiple zero outside the real-real case. -/
theorem hbRZC_repZero_row (h : HBLemma9_1_rep) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → 2 ≤ zeroMult χ₁ ρ₁ →
      lamOf q ρ₁ ≤ 696/1000 → 696/1000 ≤ lamOf q ρ₁ := by
  obtain ⟨hcond, hp⟩ := hbRZC_t8diag_cert
  have ha : (0 : ℝ) < 269/100 := by norm_num
  have hKpos : 0 < Kaff (696/1000) := by norm_num [Kaff]
  set ε : ℝ := -p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000))
      / (2 * (269/100 + 696/1000)) with hεdef
  have hεden : (0:ℝ) < 2 * (269/100 + 696/1000) := by norm_num
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) hεden
  obtain ⟨q₀, hq₀⟩ := h (269/100) (Kaff (696/1000)) ε ha hKpos hε
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hcx hmult hlam => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one hmem)
  have hlam1nn : 0 ≤ lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hmem
  -- the side condition, transported from the row `(0.696, 0.696)` to `(λ₁, λ₁)`
  have hcond' : cond913 (lamOf q ρ₁) (lamOf q ρ₁) (269/100) (Kaff (696/1000)) := by
    have ha1 : 0 < 269/100 + lamOf q ρ₁ := by linarith
    have hKnn : 0 ≤ Kond (Kaff (696/1000)) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Kond (Kaff (696/1000)) / (269/100 + 696/1000) ^ 3
        ≤ Kond (Kaff (696/1000)) / (269/100 + lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    have h4 : 1 / (269/100 + 696/1000) ^ 3 ≤ 1 / (269/100 + lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    unfold cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq χ₁ ρ₁ hm hcx hmem hmult hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ₁) (269/100) (Kaff (696/1000))
      + (269/100 + lamOf q ρ₁) * ε := hineq
  have hmono : p913 (lamOf q ρ₁) (lamOf q ρ₁) (269/100) (Kaff (696/1000))
      ≤ p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000)) :=
    hbRZC_p913_diag_mono (by linarith) hlam ha hKpos.le
  have hεval : (269/100 + 696/1000) * ε
      = -(p913 (696/1000) (696/1000) (269/100) (Kaff (696/1000))) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (269/100 + lamOf q ρ₁) * ε ≤ (269/100 + 696/1000) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', hmono, h5, hεval, hp]

/-- **HB Lemma 9.1 at a repeated zero ⇒ `HBRepZeroC`.** -/
theorem HBRepZeroC_of_rep (h : HBLemma9_1_rep) : HBRepZeroC := by
  obtain ⟨N, hN⟩ := hbRZC_repZero_row h
  refine ⟨N, fun q hq _ χ₁ ρ₁ hm hnr hmult hlam7 => ?_⟩
  by_cases hle : lamOf q ρ₁ ≤ 696/1000
  · exact hN q hq χ₁ ρ₁ hm hnr hmult hle
  · push_neg at hle
    linarith

/-- HBRepZeroC — Heath-Brown's repeated-zero bound outside
the real-real case, from HB Lemma 9.1 at the repeated zero (Route 2 above). -/
theorem HBRepZeroC_proof : Work.ZeroFreeTables.HBRepZeroC :=
  HBRepZeroC_of_rep HBLemma9_1_rep_proof

end Work.ZeroFreeTables
