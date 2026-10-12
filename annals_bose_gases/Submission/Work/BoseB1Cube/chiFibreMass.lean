import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB1Cube.fibreKWing
import Submission.Work.BoseB1Cube.fibreMassArith
import Submission.Work.BoseB1Cube.zetaQuarterLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fibre mass inequality `chiFibreMass`

The one-dimensional fibre kernel of the `chiSmall` bump is
`chiFibreK M A B t = (ζ(A − t)·ζ(B − t))^M`, where `ζ = zeta1d` is the cosine profile
`ζ(y) = cos(π y)·1_{|y| ≤ 1/2}` (`Submission.Work.ChiSmall`).  Two shifted bumps always
give a *product* of such fibres (`chiFibreFactor`), and FS's restriction step needs the
quantitative statement that, for `ν > 1/2`, `0 < δ' ≤ 1/8` and centres
`|A|, |B| ≤ ν − 1/2` with `|A − B| ≤ 1/16`, the two `δ'`-**wings** of the interval
`[−ν, ν]` carry only a small fraction of the total fibre mass:
`∫_{ν−δ'}^{ν} κ + ∫_{−ν}^{−(ν−δ')} κ ≤ (2/7)·∫_{−ν}^{ν} κ` and `∫_{−ν}^{ν} κ > 0`,
with `κ t = chiFibreK M A B t`.  This is the one-dimensional content of
`Submission.Work.BoseB1Cube.chiFibreGood` (the `σ_j = e_j/m_j ≤ 2/7` bound of its
recipe), in the sharp constants the caller needs.

## Proof

Both wings are of length `δ'` and on them each factor of `κ` is *small*: `t ∈ [ν − δ', ν]`
with `A ≤ ν − 1/2` gives `|A − t| ≥ 1/2 − δ'`, and the face decay
`ζ(y) ≤ 4·(1/2 − |y|)₊` of the cosine profile (`zeta1d_le_four_max`) gives `ζ(y) ≤ 4δ'`;
hence `κ t ≤ ((4δ')²)^M = (4δ')^{2M}` on the wings (`Work.BoseB1Cube.fibreKWing`), so each
wing is `≤ δ'(4δ')^{2M}`.  (The same argument applies to the left wing, where
`A − t ≥ 1/2 − δ' > 0` directly.)  The integral bounds are `integral_mono_on` against the
constant `(4δ')^{2M}` together with the length computation `∫_a^b c = (b − a)c`.

Conversely the central interval `I = [max A B − 1/4, min A B + 1/4]` has length
`1/2 − |A − B| ≥ 7/16` and on it both `|A − t|` and `|B − t|` are `≤ 1/4`, where
`ζ ≥ √2/2` (`Work.BoseB1Cube.zetaQuarterLower`); hence `κ ≥ ((√2/2)²)^M = (1/2)^M` on `I`
and, since `I ⊆ [−ν, ν]`, the total mass is `≥ (7/16)(1/2)^M > 0`
(`integral_mono_on` against `(1/2)^M`, then `integral_mono_interval`).

The two wings together are therefore `≤ 2δ'(4δ')^{2M} ≤ (1/8)(1/2)^M` by the sharp
arithmetic `Work.BoseB1Cube.fibreMassArith` — equality at `M = 1`, `δ' = 1/8`,
`|A − B| = 1/16` — while `(2/7)·(7/16)(1/2)^M = (1/8)(1/2)^M`.
-/

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

open Submission.BoseGases

/-- The integral of a constant over an interval: `∫_a^b c = (b − a)·c`.  (Stated at
`c : ℝ` so that the codomain of the integrand is determined, which is what makes the
rewrite usable in the interval-integral API.) -/
lemma integral_const_real {c a b : ℝ} : (∫ t in a..b, c) = (b - a) * c := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]

/-- **Pointwise mass lower bound on the central quarter interval**: if `t` is within `1/4`
of both centres, then `κ t ≥ (1/2)^M`.  On `|y| ≤ 1/4` the cosine profile satisfies
`ζ(y) ≥ √2/2`, so the product of the two factors is at least `(√2/2)² = 1/2`. -/
lemma chiFibreK_quarterLower {M : ℕ} {A B t : ℝ} (hAt : |A - t| ≤ 1 / 4)
    (hBt : |B - t| ≤ 1 / 4) : (1 / 2) ^ M ≤ chiFibreK M A B t := by
  have hζA := zetaQuarterLower hAt
  have hζB := zetaQuarterLower hBt
  have hhalf : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrs : (0 : ℝ) ≤ Real.sqrt 2 / 2 := div_nonneg (Real.sqrt_nonneg 2) (by norm_num)
  have hnn2 : (0 : ℝ) ≤ (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) := mul_nonneg hrs hrs
  have hprod : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) ≤ zeta1d (A - t) * zeta1d (B - t) :=
    mul_le_mul hζA hζB hrs (zeta1d_nonneg (A - t))
  have hpow : ((Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)) ^ M ≤
      (zeta1d (A - t) * zeta1d (B - t)) ^ M := pow_le_pow_left₀ hnn2 hprod M
  rw [hhalf] at hpow
  simpa only [chiFibreK] using hpow

theorem chiFibreMass {M : ℕ} (hM : 1 ≤ M) {ν δ' A B : ℝ} (hν : 1 / 2 < ν)
    (hδ' : 0 < δ') (hδ'8 : δ' ≤ 1 / 8) (hA : |A| ≤ ν - 1 / 2) (hB : |B| ≤ ν - 1 / 2)
    (hAB : |A - B| ≤ 1 / 16) :
    ((∫ t in (ν - δ')..ν, Work.BoseB1Cube.chiFibreK M A B t)
        + (∫ t in (-ν)..(-(ν - δ')), Work.BoseB1Cube.chiFibreK M A B t)
        ≤ (2 / 7) * (∫ t in (-ν)..ν, Work.BoseB1Cube.chiFibreK M A B t))
      ∧ 0 < ∫ t in (-ν)..ν, Work.BoseB1Cube.chiFibreK M A B t := by
  set κ : ℝ → ℝ := fun t => chiFibreK M A B t with hκdef
  change ((∫ t in (ν - δ')..ν, κ t) + (∫ t in (-ν)..(-(ν - δ')), κ t)
        ≤ (2 / 7) * (∫ t in (-ν)..ν, κ t)) ∧ 0 < ∫ t in (-ν)..ν, κ t
  have hκcont : Continuous κ := by
    rw [hκdef]
    unfold chiFibreK
    exact (((zeta1d_continuous.comp (continuous_const.sub continuous_id)).mul
      (zeta1d_continuous.comp (continuous_const.sub continuous_id))).pow M)
  have hκnn : ∀ t, 0 ≤ κ t := by
    intro t
    rw [hκdef]
    unfold chiFibreK
    exact pow_nonneg (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)) M
  -- the central interval `I = [lo, hi]`, on which both factors are large
  set lo : ℝ := max A B - 1 / 4 with hlodef
  set hi : ℝ := min A B + 1 / 4 with hhidef
  have hmaxmin : max A B - min A B ≤ 1 / 16 := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
    exact hAB
  have hlohi : lo ≤ hi := by rw [hlodef, hhidef]; linarith
  have hlen : 7 / 16 ≤ hi - lo := by rw [hlodef, hhidef]; linarith
  have hlo_ge : -ν ≤ lo := by
    rw [hlodef]
    have h1 := (abs_le.mp hA).1
    have h2 := (abs_le.mp hB).1
    have h3 := le_max_left A B
    have h4 := le_max_right A B
    linarith
  have hhi_le : hi ≤ ν := by
    rw [hhidef]
    have h1 := (abs_le.mp hA).2
    have h2 := (abs_le.mp hB).2
    have h3 := min_le_left A B
    have h4 := min_le_right A B
    linarith
  have hlow : ∀ t ∈ Set.Icc lo hi, (1 / 2) ^ M ≤ κ t := by
    intro t ht
    obtain ⟨htlo, hthi⟩ := ht
    rw [hlodef] at htlo
    rw [hhidef] at hthi
    have hAt : |A - t| ≤ 1 / 4 := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_max_left A B, min_le_left A B]
    have hBt : |B - t| ≤ 1 / 4 := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [le_max_right A B, min_le_right A B]
    rw [hκdef]
    exact chiFibreK_quarterLower hAt hBt
  have hintc1 : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ) ^ M) volume lo hi :=
    intervalIntegrable_const (E := ℝ) (c := (1 / 2 : ℝ) ^ M) (a := lo) (b := hi) (μ := volume)
  have hintκ1 : IntervalIntegrable κ volume lo hi :=
    Continuous.intervalIntegrable (E := ℝ) (μ := volume) hκcont lo hi
  have hlowInt : (1 / 2) ^ M * (hi - lo) ≤ ∫ t in lo..hi, κ t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hlohi hintc1 hintκ1 hlow
    have h4 : (∫ t in lo..hi, (1 / 2 : ℝ) ^ M) = (hi - lo) * (1 / 2) ^ M := by
      rw [integral_const_real]
    rw [h4] at hmono
    linarith
  have hintν : IntervalIntegrable κ volume (-ν) ν :=
    Continuous.intervalIntegrable (E := ℝ) (μ := volume) hκcont (-ν) ν
  have hcontain : ∫ t in lo..hi, κ t ≤ ∫ t in (-ν)..ν, κ t :=
    intervalIntegral.integral_mono_interval (μ := volume) hlo_ge hlohi hhi_le
      (ae_of_all _ (fun t => hκnn t)) hintν
  have hmass : (7 / 16) * (1 / 2) ^ M ≤ ∫ t in (-ν)..ν, κ t := by
    have h2 : (1 / 2) ^ M * (7 / 16) ≤ (1 / 2) ^ M * (hi - lo) :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    linarith
  -- the wings: `|A − t| ≥ 1/2 − δ'` on both of them
  have hptR : ∀ t ∈ Set.Icc (ν - δ') ν, κ t ≤ (4 * δ') ^ (2 * M) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hA't : 1 / 2 - δ' ≤ |A - t| := by
      have h : A - t ≤ 0 := by linarith [(abs_le.mp hA).2]
      rw [abs_of_nonpos h]
      linarith [(abs_le.mp hA).2]
    have hB't : 1 / 2 - δ' ≤ |B - t| := by
      have h : B - t ≤ 0 := by linarith [(abs_le.mp hB).2]
      rw [abs_of_nonpos h]
      linarith [(abs_le.mp hB).2]
    rw [hκdef]
    exact fibreKWing hM hδ' hA't hB't
  have hptL : ∀ t ∈ Set.Icc (-ν) (-(ν - δ')), κ t ≤ (4 * δ') ^ (2 * M) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hA't : 1 / 2 - δ' ≤ |A - t| := by
      have h : 0 ≤ A - t := by linarith [(abs_le.mp hA).1]
      rw [abs_of_nonneg h]
      linarith [(abs_le.mp hA).1]
    have hB't : 1 / 2 - δ' ≤ |B - t| := by
      have h : 0 ≤ B - t := by linarith [(abs_le.mp hB).1]
      rw [abs_of_nonneg h]
      linarith [(abs_le.mp hB).1]
    rw [hκdef]
    exact fibreKWing hM hδ' hA't hB't
  have hwingR : ∫ t in (ν - δ')..ν, κ t ≤ (4 * δ') ^ (2 * M) * δ' := by
    have hle : ν - δ' ≤ ν := by linarith
    have hint1 : IntervalIntegrable κ volume (ν - δ') ν :=
      Continuous.intervalIntegrable (E := ℝ) (μ := volume) hκcont (ν - δ') ν
    have hintc : IntervalIntegrable (fun _ : ℝ => (4 * δ') ^ (2 * M)) volume (ν - δ') ν :=
      intervalIntegrable_const (E := ℝ) (c := (4 * δ') ^ (2 * M)) (a := ν - δ') (b := ν)
        (μ := volume)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hle hint1 hintc hptR
    have h4 : (∫ t in (ν - δ')..ν, (4 * δ') ^ (2 * M)) = δ' * (4 * δ') ^ (2 * M) := by
      rw [integral_const_real]
      ring
    rw [h4] at hmono
    linarith
  have hwingL : ∫ t in (-ν)..(-(ν - δ')), κ t ≤ (4 * δ') ^ (2 * M) * δ' := by
    have hle : -ν ≤ -(ν - δ') := by linarith
    have hint1 : IntervalIntegrable κ volume (-ν) (-(ν - δ')) :=
      Continuous.intervalIntegrable (E := ℝ) (μ := volume) hκcont (-ν) (-(ν - δ'))
    have hintc : IntervalIntegrable (fun _ : ℝ => (4 * δ') ^ (2 * M)) volume (-ν) (-(ν - δ')) :=
      intervalIntegrable_const (E := ℝ) (c := (4 * δ') ^ (2 * M)) (a := -ν) (b := -(ν - δ'))
        (μ := volume)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hle hint1 hintc hptL
    have h4 : (∫ t in (-ν)..(-(ν - δ')), (4 * δ') ^ (2 * M)) = δ' * (4 * δ') ^ (2 * M) := by
      rw [integral_const_real]
      ring
    rw [h4] at hmono
    linarith
  have harith := fibreMassArith hM hδ' hδ'8
  constructor
  · have h1 : (∫ t in (ν - δ')..ν, κ t) + (∫ t in (-ν)..(-(ν - δ')), κ t)
        ≤ 2 * ((4 * δ') ^ (2 * M) * δ') := by linarith
    have h2 : (1 / 8) * (1 / 2) ^ M ≤ (2 / 7) * (∫ t in (-ν)..ν, κ t) := by
      have h3 : (2 / 7) * ((7 / 16) * (1 / 2) ^ M) ≤ (2 / 7) * (∫ t in (-ν)..ν, κ t) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      linarith
    linarith
  · have h0 : (0 : ℝ) < (7 / 16) * (1 / 2) ^ M := mul_pos (by norm_num) (pow_pos (by norm_num) M)
    linarith

end Work.BoseB1Cube
