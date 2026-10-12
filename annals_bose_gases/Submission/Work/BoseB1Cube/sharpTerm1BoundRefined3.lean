import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseFixB1B.sharpTerm1BoundRefined
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sharpTerm1BoundRefined3` — the SHARP (`R₄`-free) first-term bound of
the sliding Bogoliubov chain

With `A q := fsKinCoeff c ‖q‖/(N+2) + 2K_s·(a v)/V`, `B q := g q/V`, `|g| ≤ Kc·(a v)`,
`Kc ≤ 2K_s`, `a v·c ≤ 1/2`,

    (2π)⁻³∫ (A − √(A²−B²))/2
      ≤ (1+8ac)·((N+2)/(4V²))·(2π)⁻³∫g²/‖q‖²
        + (1/π²)·((N+2)c Kc²av²/V²)·(1 + log((av c)⁻¹))
        + (1/(3π²))·(Kc²av c³/(K_s V)) .

This is the three-row form consumed by `Work.BoseB1B.cubeRefinedRowArith3` /
`Work.BoseB1B.chainA2SharpRefined3` (the `R₄` row of
`Work.BoseFixB1B.sharpTerm1BoundRefined` is *not* available in the sharp port: its
`B⁴/A³` summand is spurious).

**Why it is not a corollary of the four-row sibling** (a direction trap already recorded in
`Submission/Work/BoseB1Cube/firstTerm3.lean`): the four-row statement is
`LHS ≤ R1+R2+R3+R4` with `R4 ≥ 0`, whose right-hand side is *larger*, so it does **not**
imply `LHS ≤ R1+R2+R3`.  The three-row form is strictly stronger.

**Proof.**  The same argument as the sibling, with the spurious row deleted: the sibling's
proof establishes exactly `LHS ≤ R1+R2+R3` (the `R₄` row is never used except to pad the
final `linarith`), so its body is replayed here with `R4`/`hR4nn` removed and the closing
`linarith` correspondingly shortened.  Route: the sharp per-mode bound
`Φ ≤ B²/(4A₀)`, `A₀ := fsKin/(N+2)`, valid because `|B| ≤ A₁ := 2K_s av/V` forces
`A² − B² ≥ (A₀+A₁)² − A₁² ≥ A₀²`; then the three regions `‖q‖ < 2c`,
`2c ≤ ‖q‖ < (av)⁻¹`, `(av)⁻¹ ≤ ‖q‖` with `inv_sq_sub_le` in the far region and
`sphShellInv3Integral` for the log shell.
-/

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

set_option maxHeartbeats 1600000

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sharpTerm1BoundRefined3 {N : ℕ} {V c Kc Ks av : ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV : 0 < V) (hc : 0 < c) (hKs : 0 < Ks) (hav : 0 < av) (hKc : 0 ≤ Kc)
    (hKsKc : Kc ≤ 2 * Ks) (hac : av * c ≤ 1 / 2)
    (hsup : ∀ q : EuclideanSpace ℝ (Fin 3), |g q| ≤ Kc * av)
    (hfin : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => g q ^ 2 / ‖q‖ ^ 2))
    (hIntQ : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
        - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * av / V) ^ 2
          - (g q / V) ^ 2)) / 2)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
        (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + 2 * Ks * av / V
          - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * av / V) ^ 2
            - (g q / V) ^ 2)) / 2
      ≤ (1 + 8 * (av * c)) * (((N : ℝ) + 2) / (4 * V ^ 2))
          * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3), g q ^ 2 / ‖q‖ ^ 2))
        + (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / V ^ 2)
            * (1 + Real.log ((av * c)⁻¹))
        + (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)) := by
  set β : ℝ := 2 * Ks * av / V with hβdef
  set δ : ℝ := av * c with hδdef
  set F : E3 → ℝ := fun q => 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + β
    with hFdef
  set G : E3 → ℝ := fun q => g q / V with hGdef
  set Φ : E3 → ℝ := fun q => (F q - Real.sqrt (F q ^ 2 - G q ^ 2)) / 2 with hΦdef
  have hInt : MeasureTheory.Integrable Φ := hIntQ
  have hβp : 0 < β := by rw [hβdef]; positivity
  have hδp : 0 < δ := by rw [hδdef]; positivity
  have hδnn : 0 ≤ δ := le_of_lt hδp
  have hδ1 : δ ≤ 1 / 2 := by rw [hδdef]; exact hac
  have hFq : ∀ q : E3, F q =
      1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ + β := fun q => by rw [hFdef]
  have hGle : ∀ q : E3, |G q| ≤ Kc * av / V := by
    intro q; rw [hGdef, abs_div, abs_of_pos hV]
    exact div_le_div_of_nonneg_right (hsup q) hV.le
  have hGβ : ∀ q : E3, |G q| ≤ β := by
    intro q
    have h1 := hGle q
    have h2 : Kc * av / V ≤ β := by
      rw [hβdef]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKsKc hav.le) hV.le
    linarith [h1, h2]
  have hGsq : ∀ q : E3, (G q) ^ 2 ≤ β ^ 2 := by
    intro q; nlinarith [abs_le.mp (hGβ q), sq_abs (G q), hβp]
  have hGKc : ∀ q : E3, (g q / V) ^ 2 ≤ (Kc * av / V) ^ 2 := by
    intro q; nlinarith [abs_le.mp (hGle q), sq_abs (g q / V)]
  have hFgeβ : ∀ q : E3, β ≤ F q := by
    intro q
    rw [hFq q]
    have h1 : 0 ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖ :=
      mul_nonneg (by positivity) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)
    linarith
  have hFpos : ∀ q : E3, 0 < F q := fun q => lt_of_lt_of_le hβp (hFgeβ q)
  have hsub : ∀ q : E3, 0 ≤ F q ^ 2 - G q ^ 2 := by
    intro q
    have h1 := hFgeβ q
    have h2 := hGsq q
    nlinarith [h1, h2]
  have hΦnn : ∀ q : E3, 0 ≤ Φ q := by
    intro q
    have hs := Real.sq_sqrt (hsub q)
    have hle : Real.sqrt (F q ^ 2 - G q ^ 2) ≤ F q :=
      (Real.sqrt_le_left (le_of_lt (hFpos q))).mpr (by nlinarith [hs])
    rw [hΦdef]
    linarith
  have hΦform : ∀ q : E3, Φ q = (G q) ^ 2 / (2 * (F q + Real.sqrt (F q ^ 2 - G q ^ 2))) := by
    intro q
    have hs2 : (Real.sqrt (F q ^ 2 - G q ^ 2)) ^ 2 = F q ^ 2 - G q ^ 2 := Real.sq_sqrt (hsub q)
    have hsp : 0 < F q + Real.sqrt (F q ^ 2 - G q ^ 2) := by
      linarith [Real.sqrt_nonneg (F q ^ 2 - G q ^ 2), hFpos q]
    rw [hΦdef, eq_div_iff (by positivity)]
    nlinarith [hs2]
  -- **Region A** (the ball `‖q‖ < 2c`): `Φ` is bounded by the constant `Kc²av/(4KsV)`.
  have hΦle1 : ∀ q : E3, Φ q ≤ Kc ^ 2 * av / (4 * Ks * V) := by
    intro q
    have h1 := hΦform q
    have hsp : 0 < F q + Real.sqrt (F q ^ 2 - G q ^ 2) := by
      linarith [Real.sqrt_nonneg (F q ^ 2 - G q ^ 2), hFpos q]
    have h2 : (G q) ^ 2 ≤ (Kc * av / V) ^ 2 := by
      nlinarith [abs_le.mp (hGle q), sq_abs (G q)]
    have h3 : (G q) ^ 2 / (2 * (F q + Real.sqrt (F q ^ 2 - G q ^ 2)))
        ≤ (Kc * av / V) ^ 2 / (2 * β) := by
      apply div_le_div₀ (sq_nonneg _) h2 (by positivity)
      linarith [hFgeβ q, Real.sqrt_nonneg (F q ^ 2 - G q ^ 2)]
    have h4 : (Kc * av / V) ^ 2 / (2 * β) = Kc ^ 2 * av / (4 * Ks * V) := by
      rw [hβdef]; field_simp <;> ring
    linarith [h1.le, h1.ge, h3, h4.le]
  -- **The sharp per-mode bound** for `2c ≤ ‖q‖`.
  have hΦleB : ∀ q : E3, 2 * c ≤ ‖q‖ →
      Φ q ≤ ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 / (‖q‖ - c) ^ 2) := by
    intro q h2c
    have hcq : c < ‖q‖ := by linarith [h2c, hc]
    have hγ : 0 < (‖q‖ - c) ^ 2 / ((N : ℝ) + 2) := by
      apply div_pos (pow_pos (by linarith : (0 : ℝ) < ‖q‖ - c) 2)
      positivity
    have hAeq : F q = (‖q‖ - c) ^ 2 / ((N : ℝ) + 2) + β := by
      rw [hFq q, Submission.BoseGases.fsKinCoeff_of_lt (le_of_lt hc) hcq]
      ring
    have hkey := Work.BoseFixB1B.bogCoeffSharpLe hβp hγ hAeq (hGsq q)
    have heq : (G q) ^ 2 / (4 * ((‖q‖ - c) ^ 2 / ((N : ℝ) + 2)))
        = ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 / (‖q‖ - c) ^ 2) := by
      rw [hGdef]; field_simp
    rw [heq] at hkey
    rw [hΦdef]
    exact hkey
  -- ### the three radial regions
  set S1 : Set E3 := Metric.ball 0 (2 * c) with hS1def
  set S2 : Set E3 := {q : E3 | 2 * c ≤ ‖q‖ ∧ ‖q‖ < (av)⁻¹} with hS2def
  set S3 : Set E3 := {q : E3 | (av)⁻¹ ≤ ‖q‖} with hS3def
  have h2cv : 2 * c ≤ (av)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hav]
    nlinarith [hac]
  have hS1m : MeasurableSet S1 := by rw [hS1def]; exact measurableSet_ball
  have hcomp : S1ᶜ = S2 ∪ S3 := by
    rw [hS1def, hS2def, hS3def]
    ext q
    simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt, Set.mem_setOf_eq,
      Set.mem_union]
    constructor
    · intro h
      rcases lt_or_ge ‖q‖ (av)⁻¹ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'
    · rintro (⟨h1, -⟩ | h2)
      · exact h1
      · linarith [h2cv]
  have hd : Disjoint S2 S3 := by
    rw [Set.disjoint_left]
    intro q h1 h2
    exact absurd h1.2 (not_lt.mpr h2)
  have hS3m : MeasurableSet S3 := by
    rw [hS3def]; exact measurableSet_le measurable_const continuous_norm.measurable
  have hsplit := integral_add_compl hS1m hInt
  rw [hcomp, setIntegral_union hd hS3m hInt.integrableOn hInt.integrableOn] at hsplit
  -- **The ball bound.**
  have hvol1 : (volume : Measure E3) S1 ≠ ⊤ := by
    rw [hS1def, EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hS1b : (∫ q in S1, Φ q) ≤ (4 / 3 * Real.pi * (2 * c) ^ 3) * (Kc ^ 2 * av / (4 * Ks * V)) := by
    have hmono : (∫ q in S1, Φ q)
        ≤ ∫ q in S1, (fun _ : E3 => Kc ^ 2 * av / (4 * Ks * V)) q :=
      setIntegral_mono_on hInt.integrableOn (integrableOn_const hvol1) hS1m (fun q _ => hΦle1 q)
    rw [setIntegral_const, Measure.real_def, hS1def, EuclideanSpace.volume_ball_fin_three,
      smul_eq_mul] at hmono
    have h : ((ENNReal.ofReal (2 * c) ^ 3 * ENNReal.ofReal (π * 4 / 3)).toReal)
        = 4 / 3 * Real.pi * (2 * c) ^ 3 := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
      simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π * 4 / 3),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * c)]
      ring
    rwa [h] at hmono
  -- **The middle annulus bound.**
  have hS2m : MeasurableSet S2 := by
    rw [hS2def]
    exact (measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hS2b : (∫ q in S2, Φ q)
      ≤ ((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
        + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (∫ q in S2, 1 / ‖q‖ ^ 3) := by
    have hpt : ∀ q ∈ S2, Φ q ≤ ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)
        + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (1 / ‖q‖ ^ 3) := by
      intro q hq
      have h2c : 2 * c ≤ ‖q‖ := hq.1
      have hr : 0 < ‖q‖ := by linarith [h2c, hc]
      have hstep1 : (g q / V) ^ 2 / (‖q‖ - c) ^ 2
          ≤ (g q / V) ^ 2 * (1 / ‖q‖ ^ 2 + 8 * c / ‖q‖ ^ 3) := by
        have h := Work.BoseFixB1B.invSqSubLeAdd hc h2c
        rw [one_div] at h
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
      have h1 : ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 / (‖q‖ - c) ^ 2)
          ≤ ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 * (1 / ‖q‖ ^ 2 + 8 * c / ‖q‖ ^ 3)) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
      have h2 : ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 * (1 / ‖q‖ ^ 2 + 8 * c / ‖q‖ ^ 3))
          = ((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)
            + (2 * c * ((N : ℝ) + 2)) * ((g q / V) ^ 2 / ‖q‖ ^ 3) := by
        rw [div_pow]; field_simp <;> ring
      have h3 : (2 * c * ((N : ℝ) + 2)) * ((g q / V) ^ 2 / ‖q‖ ^ 3)
          ≤ (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (1 / ‖q‖ ^ 3) := by
        have h4 : (g q / V) ^ 2 / ‖q‖ ^ 3 ≤ (Kc * av / V) ^ 2 * (1 / ‖q‖ ^ 3) := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (hGKc q) (by positivity)
        calc (2 * c * ((N : ℝ) + 2)) * ((g q / V) ^ 2 / ‖q‖ ^ 3)
            ≤ (2 * c * ((N : ℝ) + 2)) * ((Kc * av / V) ^ 2 * (1 / ‖q‖ ^ 3)) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (1 / ‖q‖ ^ 3) := by ring
      linarith [hΦleB q h2c, h1, h2.le, h3]
    have hshell : MeasureTheory.IntegrableOn (fun q : E3 => 1 / ‖q‖ ^ 3) S2 :=
      Work.BoseFixB1B.integrableOn_invCubeShell (a := 2 * c) (b := (av)⁻¹) (by positivity)
    have hmaj : MeasureTheory.Integrable (fun q : E3 => ((N : ℝ) + 2) / (4 * V ^ 2)
        * (g q ^ 2 / ‖q‖ ^ 2)
        + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (1 / ‖q‖ ^ 3))
        (volume.restrict S2) :=
      ((hfin.const_mul _).integrableOn).add (hshell.const_mul _)
    have hmono := MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict S2)
      (Filter.Eventually.of_forall fun q => hΦnn q) hmaj
      ((ae_restrict_iff' hS2m).mpr (Filter.Eventually.of_forall fun q => hpt q))
    have hsplit2 : (∫ q in S2, (((N : ℝ) + 2) / (4 * V ^ 2) * (g q ^ 2 / ‖q‖ ^ 2)
        + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (1 / ‖q‖ ^ 3)))
        = ((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
          + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (∫ q in S2, 1 / ‖q‖ ^ 3) := by
      rw [integral_add ((hfin.const_mul _).integrableOn) (hshell.const_mul _),
        integral_const_mul, integral_const_mul]
    rwa [hsplit2] at hmono
  -- **The far region bound.**
  have hS3b : (∫ q in S3, Φ q) ≤ (1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2))
      * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2) := by
    have hpt : ∀ q ∈ S3, Φ q
        ≤ (1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2)) * (g q ^ 2 / ‖q‖ ^ 2) := by
      intro q hq
      have h2c : 2 * c ≤ ‖q‖ := le_trans h2cv hq
      have hcd : c / δ ≤ ‖q‖ := by
        have he : c / δ = (av)⁻¹ := by rw [hδdef]; field_simp
        rw [he]; exact hq
      have hstep1 : (g q / V) ^ 2 / (‖q‖ - c) ^ 2
          ≤ (g q / V) ^ 2 * ((1 + 8 * δ) / ‖q‖ ^ 2) := by
        have h := Work.BoseFixB1B.inv_sq_sub_le hc hδp hδ1 hcd
        rw [one_div] at h
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
      have h1 : ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 / (‖q‖ - c) ^ 2)
          ≤ ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 * ((1 + 8 * δ) / ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
      have h2 : ((N : ℝ) + 2) / 4 * ((g q / V) ^ 2 * ((1 + 8 * δ) / ‖q‖ ^ 2))
          = (1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2)) * (g q ^ 2 / ‖q‖ ^ 2) := by
        rw [div_pow]; field_simp <;> ring
      linarith [hΦleB q h2c, h1, h2.le]
    have hmono : (∫ q in S3, Φ q)
        ≤ ∫ q in S3, (fun q : E3 =>
            (1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2)) * (g q ^ 2 / ‖q‖ ^ 2)) q :=
      setIntegral_mono_on hInt.integrableOn ((hfin.const_mul _).integrableOn) hS3m
        (fun q hq => hpt q hq)
    rwa [integral_const_mul] at hmono
  -- ### the four RHS terms
  set R1 : ℝ := (1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2))
    * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2)) with hR1def
  set R2 : ℝ := (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / V ^ 2)
    * (1 + Real.log δ⁻¹) with hR2def
  set R3 : ℝ := (1 / (3 * Real.pi ^ 2)) * (Kc ^ 2 * av * c ^ 3 / (Ks * V)) with hR3def
  -- the ball term is exactly `R3`
  have hA : ((2 * Real.pi) ^ 3)⁻¹ * ((4 / 3 * Real.pi * (2 * c) ^ 3) * (Kc ^ 2 * av / (4 * Ks * V)))
      = R3 := by
    rw [hR3def]; field_simp <;> ring
  -- the middle-annulus remainder is at most `R2`
  have hLval : (∫ q in S2, 1 / ‖q‖ ^ 3)
      = 4 * Real.pi * (Real.log (av)⁻¹ - Real.log (2 * c)) := by
    rw [hS2def]
    exact Work.BoseFixB1B.sphShellInv3Integral (a := 2 * c) (b := (av)⁻¹) (by positivity) h2cv
  have hlog : Real.log (av)⁻¹ - Real.log (2 * c) ≤ 1 + Real.log δ⁻¹ := by
    have h1 : Real.log (av)⁻¹ = -Real.log av := Real.log_inv av
    have h2 : Real.log (2 * c) = Real.log 2 + Real.log c :=
      Real.log_mul (by norm_num) (ne_of_gt hc)
    have h3 : Real.log δ⁻¹ = -(Real.log av + Real.log c) := by
      rw [hδdef, Real.log_inv, Real.log_mul (ne_of_gt hav) (ne_of_gt hc)]
    have h4 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [h1, h2, h3]
    linarith
  have hB : ((2 * Real.pi) ^ 3)⁻¹ * ((2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2)
      * (∫ q in S2, 1 / ‖q‖ ^ 3)) ≤ R2 := by
    rw [hLval, hR2def]
    have hkey : ((2 * Real.pi) ^ 3)⁻¹ * ((2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2)
        * (4 * Real.pi * (Real.log (av)⁻¹ - Real.log (2 * c))))
        = (1 / Real.pi ^ 2) * (((N : ℝ) + 2) * c * Kc ^ 2 * av ^ 2 / V ^ 2)
          * (Real.log (av)⁻¹ - Real.log (2 * c)) := by
      field_simp <;> ring
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  -- the `∫ g²/‖q‖²` terms are at most `R1`
  have hAB : (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2) + (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)
      ≤ ∫ q : E3, g q ^ 2 / ‖q‖ ^ 2 := by
    rw [← setIntegral_union hd hS3m hfin.integrableOn hfin.integrableOn]
    exact setIntegral_le_integral hfin (Filter.Eventually.of_forall fun q => by positivity)
  have hAnn : 0 ≤ (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2) :=
    integral_nonneg (fun q => by positivity)
  have hBnn : 0 ≤ (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2) :=
    integral_nonneg (fun q => by positivity)
  have hC : ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
        * ((∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
          + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2))) ≤ R1 := by
    have hmain : (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
        + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)
        ≤ (1 + 8 * δ) * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2) := by
      have h1 : (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
          + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)
          ≤ (1 + 8 * δ) * ((∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            + (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)) := by
        have hA1 : (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            ≤ (1 + 8 * δ) * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2) := by
          simpa using mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 1 + 8 * δ by linarith) hAnn
        have hexp : (1 + 8 * δ) * ((∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            + (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2))
            = (1 + 8 * δ) * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
              + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2) := by ring
        linarith [hA1, hexp.le, hexp.ge]
      exact le_trans h1 (mul_le_mul_of_nonneg_left hAB (by linarith))
    rw [hR1def]
    have hstep : ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
          * ((∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)))
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
          * ((1 + 8 * δ) * (∫ q : E3, g q ^ 2 / ‖q‖ ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hmain (by positivity)
    refine le_trans hstep ?_
    exact le_of_eq (by ring)
  -- ### assembly
  have e1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S1, Φ q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((4 / 3 * Real.pi * (2 * c) ^ 3) * (Kc ^ 2 * av / (4 * Ks * V))) :=
    mul_le_mul_of_nonneg_left hS1b (by positivity)
  have e2 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S2, Φ q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2) * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2))
        + R2 := by
    have h : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S2, Φ q)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
              * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            + (2 * c * ((N : ℝ) + 2) * (Kc * av / V) ^ 2) * (∫ q in S2, 1 / ‖q‖ ^ 3)) :=
      mul_le_mul_of_nonneg_left hS2b (by positivity)
    rw [mul_add] at h
    exact le_trans h (by linarith [hB])
  have e3 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S3, Φ q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2))
          * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hS3b (by positivity)
  have e23 : ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
        * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2))
      + ((2 * Real.pi) ^ 3)⁻¹ * ((1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2))
          * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2)) ≤ R1 := by
    have heq : ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
          * (∫ q in S2, g q ^ 2 / ‖q‖ ^ 2))
        + ((2 * Real.pi) ^ 3)⁻¹ * ((1 + 8 * δ) * (((N : ℝ) + 2) / (4 * V ^ 2))
            * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2))
        = ((2 * Real.pi) ^ 3)⁻¹ * (((N : ℝ) + 2) / (4 * V ^ 2)
          * ((∫ q in S2, g q ^ 2 / ‖q‖ ^ 2)
            + (1 + 8 * δ) * (∫ q in S3, g q ^ 2 / ‖q‖ ^ 2))) := by ring
    rw [heq]
    exact hC
  rw [← hsplit]
  have hexp : ((2 * Real.pi) ^ 3)⁻¹ * ((∫ q in S1, Φ q)
        + ((∫ q in S2, Φ q) + (∫ q in S3, Φ q)))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S1, Φ q)
        + (((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S2, Φ q)
          + ((2 * Real.pi) ^ 3)⁻¹ * (∫ q in S3, Φ q)) := by ring
  rw [hexp]
  linarith [e1, e2, e3, hA.le, hA.ge, e23]


end Work.BoseB1Cube
