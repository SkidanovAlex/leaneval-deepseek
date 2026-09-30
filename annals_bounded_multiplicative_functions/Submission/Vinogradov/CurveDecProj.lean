/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.TowerPhase
import Submission.Vinogradov.Projection
import Submission.Vinogradov.LocalisedDecouplingR
import Submission.Vinogradov.AsymFine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §3.4: decoupling for the reparametrised projected curve

This module derives the **global** `ℓ²`-decoupling inequality `CurveDec l D_I m' lam' C` for the
reparametrised projected moment curve

  `D_I := intervalCurve l a c (projCurveDeriv k l (torsionVec k l hlk ξ'))`,  `a = q/2^m`,
  `c = 1/2^m`,

from the tower (`TowerPhase.curveDec_towerM`), using the *anisotropic* torsion layer
(`PlateLower.lean`).  The two transports that make this work are

* `plateLower_intervalCurve` — the anisotropic torsion constant scales like `c^l`;
* `curveTaylorTop_intervalCurve_sharp` — the *top-order* Taylor constant of the reparametrised
  curve scales like `c^(l+1)`.

Both are genuinely needed: with the Gram-determinant torsion (which scales like `c^{l(l+1)}`) or
with the naive Taylor transport (constant `R` unchanged) the tube parameter `εt` of the tower
would have to grow like a negative power of `c = 2^{-m}`, i.e. with the scale, which is impossible
for a fixed induction hypothesis.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The sharp Taylor transport -/

/-- **The top-order Taylor remainder bound transports with the sharp constant `R * c^(l+1)`**:
the `i`-th remainder picks up `c^i · c^(l+1-i) = c^(l+1)` exactly.  This is the reason for
introducing `CurveTaylorTop`: the full `CurveTaylor` constant of `intervalCurve l a c D` is only
`R * c` (the `m = 0` case), which would not be enough for the tower. -/
lemma curveTaylorTop_intervalCurve_sharp {l : ℕ} {D : ℕ → ℝ → E l} {R a c : ℝ}
    (hD : CurveTaylorTop l D R) (hR : 0 ≤ R) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha0 : 0 ≤ a)
    (hac : a + c ≤ 1) : CurveTaylorTop l (intervalCurve l a c D) (R * c ^ (l + 1)) := by
  intro i σ u hi hσ hu
  have ht : a + c * σ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hσ.1, ha0], by nlinarith [hσ.2, hac]⟩
  have hcu : |c * u| ≤ 1 := by
    rw [abs_mul]
    calc |c| * |u| = c * |u| := by rw [abs_of_nonneg hc0]
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hu hc0
      _ = c := mul_one c
      _ ≤ 1 := hc1
  have hD' := hD i (a + c * σ) (c * u) hi ht hcu
  have hkey : (∑ j ∈ Finset.Icc i l, (u ^ (j - i) / ((j - i).factorial : ℝ))
        • (intervalCurve l a c D j σ))
      = c ^ i • (∑ j ∈ Finset.Icc i l, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
          • D j (a + c * σ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≤ j := (Finset.mem_Icc.mp hj).1
    have hci : c ^ i * c ^ (j - i) = c ^ j := by rw [← pow_add]; congr 1; omega
    have hscal : (u ^ (j - i) / ((j - i).factorial : ℝ)) * c ^ j
        = c ^ i * ((c * u) ^ (j - i) / ((j - i).factorial : ℝ)) := by
      rw [mul_pow, ← hci]
      ring
    show (u ^ (j - i) / ((j - i).factorial : ℝ)) • (c ^ j • D j (a + c * σ))
        = c ^ i • (((c * u) ^ (j - i) / ((j - i).factorial : ℝ)) • D j (a + c * σ))
    rw [smul_smul, hscal, smul_smul]
  rw [hkey]
  have hleft : intervalCurve l a c D i (σ + u) - c ^ i
      • (∑ j ∈ Finset.Icc i l, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
          • D j (a + c * σ))
      = c ^ i • (D i ((a + c * σ) + c * u)
          - ∑ j ∈ Finset.Icc i l, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
              • D j (a + c * σ)) := by
    rw [intervalCurve_apply, ← smul_sub, show a + c * (σ + u) = (a + c * σ) + c * u by ring]
  rw [hleft, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0 i)]
  have h2 : c ^ i * |c * u| ^ (l + 1 - i) = c ^ (l + 1) * |u| ^ (l + 1 - i) := by
    rw [abs_mul, abs_of_nonneg hc0, mul_pow, ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (by omega : i ≤ l + 1)]
  calc c ^ i * ‖D i ((a + c * σ) + c * u)
        - ∑ j ∈ Finset.Icc i l, (((c * u) ^ (j - i)) / ((j - i).factorial : ℝ))
            • D j (a + c * σ)‖
      ≤ c ^ i * (R * |c * u| ^ (l + 1 - i)) :=
        mul_le_mul_of_nonneg_left hD' (pow_nonneg hc0 i)
    _ = R * (c ^ i * |c * u| ^ (l + 1 - i)) := by ring
    _ = R * (c ^ (l + 1) * |u| ^ (l + 1 - i)) := by rw [h2]
    _ = R * c ^ (l + 1) * |u| ^ (l + 1 - i) := by ring

/-! ## 2. From the Gram-determinant torsion to `PlateLower` -/

/-- **The anisotropic torsion condition from the Gram-determinant one**, at a single point.  The
loss is the dimensional constant `tubeK l A` of `curvePlateLin_norm_lower_bound_at`. -/
lemma plateLowerAt_of_torsion {l : ℕ} (hl : 1 ≤ l) {A c t : ℝ} (hc : 0 < c) (hA : 1 ≤ A)
    {D : ℕ → ℝ → E l}
    (hbd : ∀ i : ℕ, i ≤ l + 1 → ∀ j : Fin l, |D i t j| ≤ A)
    (htor : c ≤ (Matrix.gram ℝ (fun i : Fin l => D (i.val + 1) t)).det) :
    PlateLowerAt l D (c / tubeK l A) t := by
  intro y
  have h := curvePlateLin_norm_lower_bound_at (D := D) (A := A) (c := c) (t := t)
    hl hc hA hbd htor 1 one_pos le_rfl y
  rw [curvePlateLin_one_apply] at h
  have he : (c / ((l : ℝ) * ((l - 1).factorial : ℝ) * (Real.sqrt l * A) ^ (2 * l - 1)
        * Real.sqrt l)) * 1 ^ l * ‖y‖ = (c / tubeK l A) * ‖y‖ := by
    rw [tubeK, one_pow, mul_one]
  rwa [he] at h

/-! ## 3. The tube gain and model enlargement of the tower for the projected curve -/

/-- The tube gain of the tower for the projected curve: with this `εt` the numerical hypothesis
`ha` of `curveDec_towerM` is automatic (it reduces to `c^(l+1) ≤ c^l`, i.e. `c ≤ 1`).  It is a
scale-free constant: it depends on `l`, on the torsion constant `cL`, on the Taylor constant `R`
and on the enlargement `lam'`, but not on the level. -/
noncomputable def tubeGainP (l : ℕ) (cL R lam' : ℝ) : ℝ :=
  2 ^ (l + 2) * R * ((l : ℝ) + 1) * lam' ^ (l + 1) * ((l.factorial : ℝ)) / (tubeCBP l * cL)

/-- The model enlargement used by the tower for the projected curve. -/
noncomputable def towerEnlP (l : ℕ) (cL R lam' : ℝ) : ℝ :=
  lam' * (1 + tubeGainP l cL R lam') * Ctube l

/-! ## 4. The global decoupling for the reparametrised projected curve -/

/-- **GLYZ §3.4, the reparametrisation step.**  For every coarse block `[a, a+c] = [q/2^m,
(q+1)/2^m]` whose points stay at distance `≥ 1/4` from `ξ'`, the reparametrised projected curve
`D_I` satisfies the global `ℓ²`-decoupling inequality at the fine level `2^(M-m)` and enlargement
`lam'`, with a constant that depends only on `a₀`, `εm` and `l` — in particular *not* on `m`.

The hypotheses are the geometric inputs available from `Projection`:

* `hplate` — the anisotropic torsion of the projected curve away from `ξ'`;
* `htay`   — the top-order Taylor-remainder bound of the projected curve;
* `hsepI`  — the whole block is at distance `≥ 1/4` from `ξ'` (derived from `sepLevel`);
* `hmMod`  — the degree-`l` induction hypothesis at the fixed enlargement
  `towerEnlP l cL R lam'`. -/
theorem curveDec_intervalCurve_proj {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm)
    {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (h4 : 4 ≤ 2 ^ (M - m))
    (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    {lam' : ℝ} (hlam'1 : 1 ≤ lam') (hlam'2 : lam' ≤ (2 : ℝ) ^ (M - m))
    (hmMod : ∀ M' : ℕ, 1 ≤ M' →
      DecLinScale l M' (towerEnlP l cL R lam')
        (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, CurveDec l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (2 ^ (M - m)) lam' C := by
  set cc : ℝ := 1 / (2 : ℝ) ^ m with hcc
  set aa : ℝ := ((q : ℕ) : ℝ) / (2 : ℝ) ^ m with haa
  set Dp : ℕ → ℝ → E l := projCurveDeriv k l (torsionVec k l hlk ξ') with hDp
  set DI : ℕ → ℝ → E l := intervalCurve l aa cc Dp with hDI
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 := by
    rw [hcc, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have haa0 : 0 ≤ aa := by rw [haa]; positivity
  have hac : aa + cc ≤ 1 := by
    rw [haa, hcc, ← add_div, div_le_one (by positivity)]
    have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
    have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
    linarith
  have hmtR : ((2 ^ (M - m) : ℕ) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  -- the anisotropic torsion of `D_I`
  have hplow : PlateLower l DI (cL * cc ^ l) := by
    refine plateLower_intervalCurve hcL hcc0 hcc1 (fun σ hσ => ?_)
    exact hplate _ ⟨by nlinarith [hσ.1, haa0, hcc0.le], by nlinarith [hσ.2, hcc0.le, hac]⟩
      (hsepI σ hσ)
  -- the sharp Taylor bound of `D_I`
  have htayI : CurveTaylorTop l DI (R * cc ^ (l + 1)) :=
    curveTaylorTop_intervalCurve_sharp htay hR.le hcc0.le hcc1 haa0 hac
  have htubeCP : 0 < tubeCBP l := tubeCBP_pos hl
  have hden : 0 < tubeCBP l * cL := mul_pos htubeCP hcL
  have heps_pos : 0 < tubeGainP l cL R lam' := by
    rw [tubeGainP]
    refine div_pos ?_ hden
    exact mul_pos (mul_pos (mul_pos (mul_pos (by positivity) hR) (by positivity))
      (pow_pos (lt_of_lt_of_le zero_lt_one hlam'1) _)) (by positivity)
  -- `ha` of the tower is automatic for this gain
  have ha : 2 * (2 ^ (l + 1) * (R * cc ^ (l + 1)) * ((l : ℝ) + 1) * lam' ^ (l + 1))
      ≤ tubeGainP l cL R lam' * tubeCGP l (cL * cc ^ l) := by
    have hne : tubeCBP l * cL ≠ 0 := ne_of_gt hden
    have heq : tubeGainP l cL R lam' * tubeCGP l (cL * cc ^ l)
        = 2 ^ (l + 2) * R * ((l : ℝ) + 1) * lam' ^ (l + 1) * cc ^ l := by
      rw [tubeGainP, tubeCGP]
      field_simp
    rw [heq]
    have h2 : 2 * (2 ^ (l + 1) * (R * cc ^ (l + 1)) * ((l : ℝ) + 1) * lam' ^ (l + 1))
        = 2 ^ (l + 2) * R * ((l : ℝ) + 1) * lam' ^ (l + 1) * cc ^ (l + 1) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc cc ^ (l + 1) = cc ^ l * cc := by rw [pow_succ]
      _ ≤ cc ^ l * 1 := mul_le_mul_of_nonneg_left hcc1 (pow_pos hcc0 l).le
      _ = cc ^ l := mul_one _
  -- the tower
  set mt : ℕ := 2 ^ (M - m) with hmt
  have hmt4 : 4 ≤ mt := by rw [hmt]; exact h4
  have hmtR' : (mt : ℝ) = (2 : ℝ) ^ (M - m) := by rw [hmt]; exact hmtR
  have hδ0 : 0 < lam' / (2 * (mt : ℝ)) := by
    have : (0 : ℝ) < (mt : ℝ) := by rw [hmtR']; positivity
    positivity
  have hδ1 : lam' / (2 * (mt : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h3 : lam' ≤ (mt : ℝ) := by rw [hmtR']; exact hlam'2
    linarith
  obtain ⟨C, hC, hdec⟩ := curveDec_towerM (l := l) hl DI
    (ct := cL * cc ^ l) (R := R * cc ^ (l + 1)) (mul_pos hcL (pow_pos hcc0 l)) hplow htayI
    (mul_nonneg hR.le (pow_nonneg hcc0.le _))
    (Λ := lam') hlam'1 (εt := tubeGainP l cL R lam') (Λ₁ := towerEnlP l cL R lam')
    heps_pos (le_of_eq rfl) ha
    (a := a₀) ha1 hεm hmMod
    (m := mt) hmt4 (δ := lam' / (2 * (mt : ℝ))) hδ0 hδ1 le_rfl
  refine ⟨ENNReal.ofReal C * (mt : ℝ≥0∞) ^ (2 * εm), ?_⟩
  intro f hf
  exact hdec hf

/-! ## 5. The two geometric constants of the projected curve -/

/-- **The geometric constants of the projected curve.**  Combining `torsion_projCurveDeriv`
(GLYZ Lemma 3.5 in Gram-determinant form) with the bridge `plateLowerAt_of_torsion`, and
`CurveTaylor_projCurveDeriv` with `curveTaylorTop_of_curveTaylor`, we obtain the two inputs of
`curveDec_intervalCurve_proj` in the form used by the §3.4 assembly. -/
theorem projConstants (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) (ξ' : ℝ)
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ cL R : ℝ, 0 < cL ∧ 0 < R ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
        PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t) ∧
      CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R := by
  obtain ⟨c, hc, htor⟩ := torsion_projCurveDeriv k l hl hlk ξ' hξ'
  obtain ⟨R, hR, htay⟩ :=
    CurveTaylor_projCurveDeriv k l hl hlk (orthonormal_torsionVec k l hlk ξ')
  refine ⟨c / tubeK l (Real.sqrt k * (k.factorial : ℝ)), R, ?_, hR, ?_, ?_⟩
  · refine div_pos hc (tubeK_pos hl ?_)
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr (by exact_mod_cast le_trans hl hlk))
      (by exact_mod_cast Nat.factorial_pos k)
  · intro t ht hsep
    refine plateLowerAt_of_torsion (D := projCurveDeriv k l (torsionVec k l hlk ξ')) hl hc
      (one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr (by exact_mod_cast le_trans hl hlk))
        (by exact_mod_cast Nat.factorial_pos k))
      (fun i hi j =>
        CurveBounded_projCurveDeriv k l hlk (orthonormal_torsionVec k l hlk ξ') i hi t ht j)
      (htor t ht hsep)
  · exact curveTaylorTop_of_curveTaylor htay

/-! ## 6. The localised decoupling of the sub-block sums (GLYZ Corollary 3.7 for §3.4) -/

/-- **The localised decoupling for the reparametrised projected curve.**  For every coarse block
`q` at level `m` whose points stay at distance `≥ 1/4` from `ξ'`, and for every enlargement `lam`
satisfying the (fixed) condition `2^(l+2) ≤ cL c^l (R₀/mt^l) lam^l` and `2 lam ≤ mt`, the
sub-block sums of the block satisfy the localised decoupling inequality `CurveDecLocR` at the fine
level `mt = 2^(M-m)`, with the ball radius threshold `R₀`.

The proof combines the global `CurveDec` of `curveDec_intervalCurve_proj` with
`LocalisedDecouplingR.curveDecLocR_of_curveDec`; this is step 4 of the §3.4 chain. -/
theorem curveDecLocR_intervalCurve_proj {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm lam : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hlam1 : 1 ≤ lam)
    {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (h4 : 4 ≤ 2 ^ (M - m))
    (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hlam2 : 2 * lam ≤ (2 : ℝ) ^ (M - m))
    {R₀ : ℝ} (hR0 : (((2 ^ (M - m) : ℕ) : ℝ)) ^ l ≤ R₀)
    (hρlR : (2 : ℝ) ^ (l + 2)
      ≤ (cL * (1 / (2 : ℝ) ^ m) ^ l) * (R₀ / (((2 ^ (M - m) : ℕ) : ℝ)) ^ l) * lam ^ l)
    {A : ℝ} (hA : 0 ≤ A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' →
      DecLinScale l M' (towerEnlP l cL R (2 * lam))
        (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, CurveDecLocR l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (2 ^ (M - m)) lam A R₀ C := by
  set cc : ℝ := 1 / (2 : ℝ) ^ m with hcc
  set aa : ℝ := ((q : ℕ) : ℝ) / (2 : ℝ) ^ m with haa
  set Dp : ℕ → ℝ → E l := projCurveDeriv k l (torsionVec k l hlk ξ') with hDp
  set DI : ℕ → ℝ → E l := intervalCurve l aa cc Dp with hDI
  set mt : ℕ := 2 ^ (M - m) with hmt
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 := by
    rw [hcc, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have haa0 : 0 ≤ aa := by rw [haa]; positivity
  have hac : aa + cc ≤ 1 := by
    rw [haa, hcc, ← add_div, div_le_one (by positivity)]
    have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
    have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
    linarith
  have hmt4 : 4 ≤ mt := by rw [hmt]; exact h4
  have hmtR : (mt : ℝ) = (2 : ℝ) ^ (M - m) := by rw [hmt]; push_cast; ring
  have hmtpos : (0 : ℝ) < (mt : ℝ) := by rw [hmtR]; positivity
  have hct : 0 < cL * cc ^ l := mul_pos hcL (pow_pos hcc0 l)
  -- the anisotropic torsion of `D_I`
  have hplow : PlateLower l DI (cL * cc ^ l) := by
    refine plateLower_intervalCurve hcL hcc0 hcc1 (fun σ hσ => ?_)
    exact hplate _ ⟨by nlinarith [hσ.1, haa0, hcc0.le], by nlinarith [hσ.2, hcc0.le, hac]⟩
      (hsepI σ hσ)
  -- the global decoupling at the doubled enlargement
  have hdec : ∃ C : ℝ≥0∞, CurveDec l DI mt (2 * lam) C := by
    refine curveDec_intervalCurve_proj hl hlk hξ' hcL hR hplate htay ha1 hεm hm hmM h4 q hsepI
      ?_ hlam2 hmMod
    have h2 : (1 : ℝ) ≤ 2 * lam := by linarith
    exact h2
  obtain ⟨C₁, hC₁⟩ := hdec
  -- the ball inside the plate
  have hmtR2 : ((mt : ℕ) : ℝ) ^ l = (((2 ^ (M - m) : ℕ) : ℝ)) ^ l := by rw [hmt]
  have hlamle : lam ≤ (mt : ℝ) := by
    rw [hmtR]; linarith
  have hrad : ∀ j : Fin mt, Metric.ball (DI 0 (pieceCenter mt j))
        ((cL * cc ^ l) * (lam / (2 * mt)) ^ l)
      ⊆ curvePlate l DI (lam / (2 * mt)) (pieceCenter mt j) := by
    intro j
    have hpj : pieceCenter mt j ∈ Set.Icc (0 : ℝ) 1 := pieceCenter_mem_Icc mt (by omega) j
    have hδ0 : 0 < lam / (2 * mt) := by positivity
    have hδ1 : lam / (2 * mt) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    refine ball_subset_curvePlate_of_lower_at (D := DI) (t := pieceCenter mt j) hct
      (fun δ hδ0' hδ1' w => ?_) (lam / (2 * mt)) hδ0 hδ1
    have hw : ‖w‖ ≤ ‖coordVec l w‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      simpa only [coordVec_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (coordVec l w) i
    have h1 : (cL * cc ^ l) * δ ^ l * ‖w‖ ≤ (cL * cc ^ l) * δ ^ l * ‖coordVec l w‖ :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 := curvePlateLin_lower_of_plateLowerAt hct (hplow _ hpj) hδ0' hδ1' (coordVec l w)
    rw [curvePlateLin_apply] at h2
    refine h1.trans ?_
    refine h2.trans (le_of_eq ?_)
    have hsum : (∑ i : Fin l, coordVec l w i • (δ ^ (i.val + 1) • DI (i.val + 1) (pieceCenter mt j)))
        = ∑ i : Fin l, w i • (δ ^ (i.val + 1) • DI (i.val + 1) (pieceCenter mt j)) :=
      Finset.sum_congr rfl fun i _ => by rw [coordVec_apply]
    rw [hsum]
  -- Corollary 3.7
  obtain ⟨K, hK⟩ := curveDecLocR_of_curveDec hl DI (Nat.one_le_iff_ne_zero.mpr (by omega))
    (lam := lam) (lam' := 2 * lam) (ρ := cL * cc ^ l) (A := A) (R₀ := R₀)
    hlam1 hct (by rw [hmtR2]; exact hR0) hρlR hrad hA hC₁ (le_refl (2 * lam))
  exact ⟨C₁ * K, hK⟩

end Submission.Vinogradov
