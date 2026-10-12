import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseB1Cube.chiFibreArith
import Submission.Work.BoseB1Cube.chiFibreFactor
import Submission.Work.BoseB1Cube.chiFibreMass
import Submission.Work.BoseB1Cube.chiFibreProd
import Submission.Work.BoseB1Cube.chiFibreWing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseB1Cube

open Submission.BoseGases

/-- The coordinate cube `{u | ∀ j, |u.ofLp j| ≤ s}` in `EuclideanSpace ℝ (Fin 3)`. -/
abbrev chiFibreCube (s : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {u | ∀ j : Fin 3, |u.ofLp j| ≤ s}

lemma chiFibreK_nonneg (M : ℕ) (A B t : ℝ) : 0 ≤ chiFibreK M A B t := by
  unfold chiFibreK
  exact pow_nonneg (mul_nonneg (zeta1d_nonneg _) (zeta1d_nonneg _)) M

lemma chiFibreK_continuous (M : ℕ) (A B : ℝ) : Continuous (chiFibreK M A B) := by
  unfold chiFibreK
  exact ((zeta1d_continuous.comp (continuous_const.sub continuous_id)).mul
    (zeta1d_continuous.comp (continuous_const.sub continuous_id))).pow M

lemma chiFibreK_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) (A B : ℝ) :
    HasCompactSupport (chiFibreK M A B) := by
  change IsCompact (tsupport (chiFibreK M A B))
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := A - 1 / 2) (b := A + 1 / 2))
    isClosed_closure ?_
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  rw [Function.mem_support] at ht
  have h1 : zeta1d (A - t) ≠ 0 := by
    intro h0
    apply ht
    unfold chiFibreK
    rw [h0, zero_mul]
    exact zero_pow (by omega : M ≠ 0)
  have h2 : |A - t| ≤ 1 / 2 := zeta1d_ne_zero_abs_le h1
  rw [Set.mem_Icc]
  obtain ⟨hlo, hhi⟩ := abs_le.mp h2
  exact ⟨by linarith, by linarith⟩

lemma chiFibreK_integrable {M : ℕ} (hM : 1 ≤ M) (A B : ℝ) : Integrable (chiFibreK M A B) :=
  (chiFibreK_continuous M A B).integrable_of_hasCompactSupport
    (chiFibreK_hasCompactSupport hM A B)

lemma chiFibreK_eq_zero_of_lt_abs {M : ℕ} (hM : 1 ≤ M) {ν A B : ℝ}
    (hA : |A| ≤ ν - 1 / 2) {t : ℝ} (ht : ν < |t|) : chiFibreK M A B t = 0 := by
  have htri : |t| - |A| ≤ |A - t| := by
    rw [← abs_sub_comm t A]
    exact abs_sub_abs_le_abs_sub t A
  have hhalf : 1 / 2 < |A - t| := by linarith
  have hz : zeta1d (A - t) = 0 := zeta1d_of_one_half_lt hhalf
  unfold chiFibreK
  rw [hz]
  simp only [zero_mul]
  exact zero_pow (by omega : M ≠ 0)

lemma chiFibreCube_measurable (s : ℝ) : MeasurableSet (chiFibreCube s) := by
  have h : chiFibreCube s = ⋂ j : Fin 3, {u : EuclideanSpace ℝ (Fin 3) | |u.ofLp j| ≤ s} := by
    ext u; simp [chiFibreCube]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_le
    (measurable_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).measurable)
    measurable_const

/-- Bridge: the set integral over `Icc a b` is the interval integral `a..b`. -/
lemma setIntegral_Icc_eq_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Icc a b, f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]

lemma interval_two {f : ℝ → ℝ} (hf : Continuous f) (a b c : ℝ) :
    (∫ t in a..b, f t) + (∫ t in b..c, f t) = ∫ t in a..c, f t :=
  intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a b)
    (hf.intervalIntegrable b c)

lemma interval_four {f : ℝ → ℝ} (hf : Continuous f) (a b c d e : ℝ) :
    (∫ t in a..e, f t)
      = (∫ t in a..b, f t) + (∫ t in b..c, f t) + (∫ t in c..d, f t)
        + (∫ t in d..e, f t) := by
  have h1 := interval_two hf a b c
  have h2 := interval_two hf a c d
  have h3 := interval_two hf a d e
  linarith

-- more local helpers -------------------------------------------------------------

lemma chiFibreG_integrable {M : ℕ} (hM : 1 ≤ M) (a b : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun u : EuclideanSpace ℝ (Fin 3) => chiSmall M (a - u) * chiSmall M (b - u)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((chiSmall_continuous hM).comp (continuous_const.sub continuous_id)).mul
      ((chiSmall_continuous hM).comp (continuous_const.sub continuous_id))
  · change IsCompact (tsupport (fun u : EuclideanSpace ℝ (Fin 3) =>
      chiSmall M (a - u) * chiSmall M (b - u)))
    refine IsCompact.of_isClosed_subset (isCompact_closedBall a 1) isClosed_closure ?_
    refine closure_minimal ?_ (isCompact_closedBall a 1).isClosed
    intro u hu
    rw [Function.mem_support] at hu
    have h1 : chiSmall M (a - u) ≠ 0 := by
      intro h
      exact hu (by rw [h, zero_mul])
    have h2 : chiSmallBase M (a - u) ≠ 0 := by
      intro h
      apply h1
      dsimp [chiSmall]
      rw [h]
      simp
    have h3 : ‖a - u‖ ≤ 1 := chiSmallBase_support_norm_le hM h2
    have h4 : dist u a ≤ 1 := by
      rw [dist_eq_norm, norm_sub_rev]
      exact h3
    simpa [Metric.mem_closedBall] using h4

/-- **The `chiSmall` bump fibre inequality (FS's restriction step at the good set).**

Import `Submission.Work.BoseB1Cube.chiBumpDefs` (which re-exports `Submission.Work.ChiSmall`:
`χ_M = Submission.BoseGases.chiSmall M`, `zeta1d`, `chiSmallNormFactor`, `chiSmallBase`, …) plus
Mathlib.  No other corpus module is needed.

For `M ≥ 1`, `ν > 1/2`, `0 < δ' ≤ 1/8` and `a, b ∈ ℝ³` with `|a_j|, |b_j| ≤ ν − 1/2` and
`|a_j − b_j| ≤ 1/16` for every coordinate `j`: the full `u`-integral of the product of the two
shifted bumps `χ_M(a−u)·χ_M(b−u)` is dominated by the same integral restricted to the cube
`{|u_j| ≤ ν − δ'}`, plus *three times* the integral over the layer
`{ν − 2δ' < ‖u‖_∞ ≤ ν − δ'}`.

PROOF RECIPE (elementary; the constant `3` is what the algebra gives):
* `χ_M` factors coordinatewise: `chiSmall M z = chiSmallNormFactor M * ∏_j (zeta1d z_j)^M`, so the
  integrand is a positive constant times `∏_j κ_j(u.ofLp j)` with
  `κ_j(t) := (zeta1d (a.ofLp j − t) * zeta1d (b.ofLp j − t))^M`; the constant cancels;
* `κ_j` vanishes off `[−ν, ν]` because `κ_j t ≠ 0` forces `|a.ofLp j − t| ≤ 1/2` and
  `|b.ofLp j − t| ≤ 1/2`;
* **Fubini/product structure**: for `s ≥ 0`,
  `∫ u in {u | ∀ j, |u.ofLp j| ≤ s}, ∏_j κ_j (u.ofLp j) = ∏_j ∫ t in (−s)..s, κ_j t`.
  Use `MeasureTheory.integral_fintype_prod_volume_eq_prod` (which is `Measure.pi`-based) on
  `Fin 3 → ℝ` and transport along `PiLp.volume_preserving_ofLp (Fin 3)`
  (`Submission/NeumannBasics.lean:60–95` is the same pattern for `volume` on
  `EuclideanSpace ℝ (Fin 3)`); the functions `t ↦ κ_j t · 1_{|t| ≤ s}` are continuous with compact
  support;
* **1D facts** (`ψ := fun y => (zeta1d y)^M` is even, nonnegative and nonincreasing on `[0, ∞)`;
  see `zeta1d_neg`, `zeta1d_nonneg`, `zeta1d_le_four_max`, `zeta1d_ge_sqrt2_div_two`):
  with `m_j := ∫_{|t| ≤ ν} κ_j`, `e_j := ∫_{ν−δ' < |t| ≤ ν} κ_j`,
  `d_j := ∫_{ν−2δ' < |t| ≤ ν−δ'} κ_j`,
  - on `[ν − 2δ', ν]` (and on `[−ν, −ν + 2δ']`) one has `κ_j t = ψ (|t − a_j|) ψ (|t − b_j|)` with
    the two arguments `≥ 1/4`, so `κ_j` is monotone there; comparing the two wings of equal length
    `δ'` gives `e_j ≤ d_j`;
  - the face decay `zeta1d y ≤ 4·max (1/2 − |y|) 0` gives `e_j ≤ 2 δ' (4 δ')^{2M}`;
  - the support of `κ_j` is an interval of length `1 − |a_j − b_j| ≥ 15/16` on which `κ_j ≥ 2^{−M}`
    on a subinterval of length `≥ 7/16` (`zeta1d y ≥ √2/2` for `|y| ≤ 1/4`), so
    `m_j ≥ (7/16)·2^{−M}` and hence `e_j / m_j ≤ (32/7)·32^M δ'^{2M+1} ≤ 2/7` for `δ' ≤ 1/8`;
* **algebra**: dividing by `∏_j m_j` and setting `σ_j := e_j/m_j ∈ [0, 2/7]`,
  `τ_j := d_j/m_j ≥ σ_j`, the goal becomes `1 + 3∏_j(1 − σ_j − τ_j) ≤ 4∏_j(1 − σ_j)`, which
  follows from `1 + 3∏_j(1 − 2σ_j) ≤ 4∏_j(1 − σ_j)` (multilinear in `σ`, hence its minimum on the
  cube is attained at a vertex; the eight vertex cases are `0, 4/7, 24/49, 76/343, …` and are all
  `≥ 0`). -/
theorem chiFibreGood {M : ℕ} (hM : 1 ≤ M) {ν δ' : ℝ} (hν : 1 / 2 < ν)
    (hδ' : 0 < δ') (hδ'8 : δ' ≤ 1 / 8) (a b : EuclideanSpace ℝ (Fin 3))
    (hab : ∀ j : Fin 3, |(a - b).ofLp j| ≤ 1 / 16)
    (ha : ∀ j : Fin 3, |a.ofLp j| ≤ ν - 1 / 2)
    (hb : ∀ j : Fin 3, |b.ofLp j| ≤ ν - 1 / 2) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmall M (a - u) *
        Submission.BoseGases.chiSmall M (b - u))
      ≤ (∫ u in {u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ ν - δ'},
            Submission.BoseGases.chiSmall M (a - u) * Submission.BoseGases.chiSmall M (b - u))
        + 3 * (∫ u in ({u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ ν - δ'}
              \ {u : EuclideanSpace ℝ (Fin 3) | ∀ j : Fin 3, |u.ofLp j| ≤ ν - 2 * δ'}),
            Submission.BoseGases.chiSmall M (a - u) * Submission.BoseGases.chiSmall M (b - u)) := by
  have hν0 : 0 < ν := by linarith
  have hab' : ∀ j : Fin 3, |a.ofLp j - b.ofLp j| ≤ 1 / 16 := by
    intro j
    simpa using hab j
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun u => chiSmall M (a - u) * chiSmall M (b - u) with hg
  let mF : Fin 3 → ℝ := fun j => ∫ t in (-ν)..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t
  let bF : Fin 3 → ℝ := fun j => ∫ t in (-(ν - δ'))..(ν - δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t
  let cF : Fin 3 → ℝ := fun j => ∫ t in (-(ν - 2 * δ'))..(ν - 2 * δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t
  let eF : Fin 3 → ℝ := fun j =>
    (∫ t in (ν - δ')..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
      + (∫ t in (-ν)..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t)
  let dF : Fin 3 → ℝ := fun j =>
    (∫ t in (ν - 2 * δ')..(ν - δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t)
      + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t)
  have hfac : g = fun u => (chiSmallNormFactor M) ^ 2
      * ∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j) := by
    funext u
    rw [hg]
    exact chiFibreFactor hM a b u
  -- the "restricted integral of c^2 * P" step
  have hIntSet : ∀ s : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet s →
      (∫ u in s, g u) = (chiSmallNormFactor M) ^ 2
        * ∫ u in s, (∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)) := by
    intro s hs
    rw [← MeasureTheory.integral_indicator hs, ← MeasureTheory.integral_indicator hs,
      ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [hfac]
    by_cases hu : u ∈ s <;> simp [hu]
  have hIntUniv : (∫ u : EuclideanSpace ℝ (Fin 3), g u) = (chiSmallNormFactor M) ^ 2
      * ∫ u : EuclideanSpace ℝ (Fin 3),
          (∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)) := by
    rw [hfac]
    exact MeasureTheory.integral_const_mul _ _
  have hGzero : ∀ u : EuclideanSpace ℝ (Fin 3), u ∉ chiFibreCube ν →
      (∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)) = 0 := by
    intro u hu
    simp only [chiFibreCube, Set.mem_ofPred_eq, not_forall, not_le] at hu
    obtain ⟨j, hj⟩ := hu
    exact Finset.prod_eq_zero (Finset.mem_univ j) (chiFibreK_eq_zero_of_lt_abs hM (ha j) hj)
  have hfull : (∫ u : EuclideanSpace ℝ (Fin 3), g u)
      = (chiSmallNormFactor M) ^ 2 * ∏ j : Fin 3, mF j := by
    calc (∫ u : EuclideanSpace ℝ (Fin 3), g u)
        = (chiSmallNormFactor M) ^ 2
            * ∫ u : EuclideanSpace ℝ (Fin 3),
                (∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)) := hIntUniv
      _ = (chiSmallNormFactor M) ^ 2
            * ∫ u in chiFibreCube ν,
                (∏ j : Fin 3, chiFibreK M (a.ofLp j) (b.ofLp j) (u.ofLp j)) := by
            rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hGzero]
      _ = (chiSmallNormFactor M) ^ 2
            * ∏ j : Fin 3, (∫ t in Set.Icc (-ν) ν, chiFibreK M (a.ofLp j) (b.ofLp j) t) := by
            rw [chiFibreProd M (fun j => a.ofLp j) (fun j => b.ofLp j) ν]
      _ = (chiSmallNormFactor M) ^ 2 * ∏ j : Fin 3, mF j := by
            congr 1
            apply Finset.prod_congr rfl
            intro j _
            exact setIntegral_Icc_eq_interval (by linarith : (-ν : ℝ) ≤ ν)
  have hmid : (∫ u in chiFibreCube (ν - δ'), g u)
      = (chiSmallNormFactor M) ^ 2 * ∏ j : Fin 3, bF j := by
    rw [hIntSet (chiFibreCube (ν - δ')) (chiFibreCube_measurable _)]
    congr 1
    rw [chiFibreProd M (fun j => a.ofLp j) (fun j => b.ofLp j) (ν - δ')]
    apply Finset.prod_congr rfl
    intro j _
    exact setIntegral_Icc_eq_interval (by linarith : -(ν - δ') ≤ ν - δ')
  have hpc : (∫ u in chiFibreCube (ν - 2 * δ'), g u)
      = (chiSmallNormFactor M) ^ 2 * ∏ j : Fin 3, cF j := by
    rw [hIntSet (chiFibreCube (ν - 2 * δ')) (chiFibreCube_measurable _)]
    congr 1
    rw [chiFibreProd M (fun j => a.ofLp j) (fun j => b.ofLp j) (ν - 2 * δ')]
    apply Finset.prod_congr rfl
    intro j _
    exact setIntegral_Icc_eq_interval (by linarith : -(ν - 2 * δ') ≤ ν - 2 * δ')
  have hsub : chiFibreCube (ν - 2 * δ') ⊆ chiFibreCube (ν - δ') := by
    intro u hu j
    have hle : ν - 2 * δ' ≤ ν - δ' := by linarith
    exact le_trans (hu j) hle
  have hlay : (∫ u in (chiFibreCube (ν - δ') \ chiFibreCube (ν - 2 * δ')), g u)
      = (chiSmallNormFactor M) ^ 2 * ((∏ j : Fin 3, bF j) - ∏ j : Fin 3, cF j) := by
    rw [MeasureTheory.setIntegral_sdiff (chiFibreCube_measurable _)
      ((chiFibreG_integrable hM a b).integrableOn) hsub, hmid, hpc]
    ring
  change (∫ u, g u) ≤ (∫ u in chiFibreCube (ν - δ'), g u)
      + 3 * (∫ u in (chiFibreCube (ν - δ') \ chiFibreCube (ν - 2 * δ')), g u)
  rw [hfull, hmid, hlay]
  -- now the 1D arithmetic
  have hmpos : ∀ j : Fin 3, 0 < mF j := fun j => (chiFibreMass hM hν hδ' hδ'8 (ha j) (hb j) (hab' j)).2
  have hele : ∀ j : Fin 3, eF j ≤ (2 / 7) * mF j :=
    fun j => (chiFibreMass hM hν hδ' hδ'8 (ha j) (hb j) (hab' j)).1
  have he0 : ∀ j : Fin 3, 0 ≤ eF j := by
    intro j
    have h1 : 0 ≤ ∫ t in (ν - δ')..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => chiFibreK_nonneg M (a.ofLp j) (b.ofLp j) t)
    have h2 : 0 ≤ ∫ t in (-ν)..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => chiFibreK_nonneg M (a.ofLp j) (b.ofLp j) t)
    exact add_nonneg h1 h2
  have hbF : ∀ j : Fin 3, bF j = mF j - eF j := by
    intro j
    have hc := chiFibreK_continuous M (a.ofLp j) (b.ofLp j)
    have s1 := interval_two hc (-ν) (-(ν - δ')) ν
    have s2 := interval_two hc (-(ν - δ')) (ν - δ') ν
    show (∫ t in (-(ν - δ'))..(ν - δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t)
        = (∫ t in (-ν)..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
          - ((∫ t in (ν - δ')..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
            + (∫ t in (-ν)..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t))
    linarith
  have hbFprod : (∏ j : Fin 3, bF j) = ∏ j : Fin 3, (mF j - eF j) :=
    Finset.prod_congr rfl (fun j _ => hbF j)
  have hcFle : ∀ j : Fin 3, cF j ≤ mF j - 2 * eF j := by
    intro j
    have hc := chiFibreK_continuous M (a.ofLp j) (b.ofLp j)
    have hmc : mF j - cF j = dF j + eF j := by
      have r1 := interval_two hc (-ν) (-(ν - 2 * δ')) ν
      have r2 := interval_two hc (-(ν - 2 * δ')) (ν - 2 * δ') (ν - δ')
      have r3 := interval_two hc (-(ν - 2 * δ')) (ν - δ') ν
      have r4 := interval_two hc (-ν) (-(ν - 2 * δ')) (-(ν - δ'))
      have r5 : (∫ t in (-(ν - 2 * δ'))..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t)
          + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t) = 0 := by
        simpa using interval_two hc (-(ν - 2 * δ')) (-(ν - δ')) (-(ν - 2 * δ'))
      show (∫ t in (-ν)..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
          - (∫ t in (-(ν - 2 * δ'))..(ν - 2 * δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t)
          = ((∫ t in (ν - 2 * δ')..(ν - δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t)
              + (∫ t in (-(ν - δ'))..(-(ν - 2 * δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t))
            + ((∫ t in (ν - δ')..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
              + (∫ t in (-ν)..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t))
      linarith
    have hwing := chiFibreWing (M := M) hν hδ' hδ'8 (ha j) (hb j)
    show (∫ t in (-(ν - 2 * δ'))..(ν - 2 * δ'), chiFibreK M (a.ofLp j) (b.ofLp j) t)
        ≤ (∫ t in (-ν)..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
          - 2 * ((∫ t in (ν - δ')..ν, chiFibreK M (a.ofLp j) (b.ofLp j) t)
              + (∫ t in (-ν)..(-(ν - δ')), chiFibreK M (a.ofLp j) (b.ofLp j) t))
    linarith
  have hcFnonneg : ∀ j : Fin 3, 0 ≤ cF j :=
    fun j => intervalIntegral.integral_nonneg (by linarith) (fun t _ => chiFibreK_nonneg M (a.ofLp j) (b.ofLp j) t)
  have hcFprod : (∏ j : Fin 3, cF j) ≤ ∏ j : Fin 3, (mF j - 2 * eF j) :=
    Finset.prod_le_prod₀ (fun j _ => hcFnonneg j) (fun j _ => hcFle j)
  have harith := chiFibreArith mF eF hmpos he0 hele
  have hkey : (∏ j : Fin 3, mF j) ≤ 4 * (∏ j : Fin 3, bF j) - 3 * (∏ j : Fin 3, cF j) := by
    rw [← hbFprod] at harith
    linarith
  have hc2pos : 0 < (chiSmallNormFactor M) ^ 2 := by
    have hS : 0 < Real.sqrt (chiSmallNormSq M) := Real.sqrt_pos.mpr (chiSmallNormSq_pos hM)
    have : 0 < chiSmallNormFactor M := by
      dsimp [chiSmallNormFactor]
      exact inv_pos.mpr hS
    positivity
  have hstep := mul_le_mul_of_nonneg_left hkey (le_of_lt hc2pos)
  have hexp : (chiSmallNormFactor M) ^ 2 * (4 * (∏ j : Fin 3, bF j) - 3 * (∏ j : Fin 3, cF j))
      = (chiSmallNormFactor M) ^ 2 * (∏ j : Fin 3, bF j)
        + 3 * ((chiSmallNormFactor M) ^ 2 * ((∏ j : Fin 3, bF j) - (∏ j : Fin 3, cF j))) := by
    ring
  linarith

end Work.BoseB1Cube
