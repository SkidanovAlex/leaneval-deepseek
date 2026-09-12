import Submission.Serre
import Submission.SerreExample
import Submission.SerreHolder
import Submission.MuAtomFree
import Submission.PotentialContinuity
import Submission.SupportConcentration
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Quantile points of the Serre measure (`defn:approx` of Smith's paper)

For `μ = serreMeasure gSerre aSerre bSerre` (atom-free, `1/2`-Hölder on
`[aSerre,bSerre]`), define the cumulative distribution function
`cdf x := μ(Iic x)` and the quantiles `α_i := qpoint (i/n)` — the minimal
`α ∈ [aSerre,bSerre]` with `cdf α = i/n`.  We prove the facts needed by the
"approximating polynomial" `P_{n,μ} = ∏_i (X − α_i)` machinery
(paper `defn:approx`, `prop:three_pages`):

* `cdf` is monotone, `cdf aSerre = 0`, `cdf bSerre = 1`, and is
  `1/2`-Hölder on `[aSerre,bSerre]` (from the Hölder bound on interval mass);
* the quantile map inverts `cdf` on `[0,1]`;
* consecutive quantiles are spaced: `α_{i+1} − α_i ≥ (C·n)^{-2}` (from
  Hölder + `μ((α_i, α_{i+1}]) = 1/n`);
* the counting estimate (`notelescope`): for the point-mass counting measure
  `ν_n = (1/n)·Σ_{i ≤ n} δ_{α_i}`, `|ν_n(Icc u v) − μ(Icc u v)| ≤ C/n`
  for `[u,v] ⊆ [aSerre,bSerre]`;
* short intervals contain at most one quantile.

All lemmas below are proved in this module; helper lemmas have been added
as needed.  The statements are exactly as given (two of the original
quantile-map statements, `qpoint_mono` and `lt_qpoint_of_cdf_lt`, were
missing a hypothesis `· ≤ 1` and were false as stated; they have been
corrected as documented at their declarations).  Work in the
namespace `Submission.Quantile`.  The measure is the Serre measure
`serreMeasure gSerre aSerre bSerre` (an abbrev `PotentialContinuity.muS`).
HINTS: (1) `MuAtomFree.serre_atom_free (r)` : `serreMeasure gSerre aSerre
bSerre {r} = 0`; (2) `SerreHolder.serre_holder (a:=aSerre) (b:=bSerre)
(γ:=gSerre) aSerre_pos (by norm_num [aSerre,bSerre]) gSerre_pos.le
gSerre_le_one hu huv hv : serreMeasure gSerre aSerre bSerre (Set.Icc u v) ≤
ENNReal.ofReal ((4*(aSerre+bSerre)/(aSerre*√(bSerre−aSerre)))*√(v−u))`;
(3) `PotentialContinuity.muS_Icc`, `muS_univ`, `muS_compl_Icc`,
`SupportConcentration.serre_compl_Icc`; (4) for `cdf aSerre = 0` note
`Iic aSerre ⊆ {x < aSerre} ∪ {aSerre}` and the sub-aSerre set has zero
measure (it is contained in the complement of `Icc aSerre bSerre`);
(5) `cdf bSerre = 1` via `Iic bSerre = Icc aSerre bSerre ∪ (Iic bSerre \
Icc aSerre bSerre)` (disjoint) and the second piece ⊆ complement of the
interval; use `measure_union`, `measure_mono`, `ENNReal.toReal`.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Real ENNReal

namespace Submission.Quantile

open Submission.Serre
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.MuAtomFree
open Submission.SerreHolder

/-- The cumulative distribution function `μ((−∞, x])`. -/
noncomputable def cdf (x : ℝ) : ℝ := (muS (Set.Iic x)).toReal

/-- The quantile at level `v`: the minimal `α ∈ [aSerre,bSerre]` with
`cdf α ≥ v` (for `0 ≤ v ≤ 1`). -/
noncomputable def qpoint (v : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc aSerre bSerre ∧ v ≤ cdf x}

/-- The `i`-th root of the approximating polynomial of degree `n`
(paper: `α_i` with `cdf α_i = i/n`, `1 ≤ i ≤ n`). -/
noncomputable def alpha (n : ℕ) (i : ℕ) : ℝ := qpoint ((i : ℝ) / (n : ℝ))

/-- The count `#{i ∈ [1..n] : α_i ≤ x}`. -/
noncomputable def countRoots (n : ℕ) (x : ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i ≤ x).card


-- ---------------------------------------------------------------------
-- (0) elementary measure facts used throughout
-- ---------------------------------------------------------------------

/-- μ is finite (in fact a probability measure). -/
lemma muS_lt_top (S : Set ℝ) : muS S < ∞ := by
  have hle : muS S ≤ muS Set.univ := measure_mono (Set.subset_univ S)
  rw [muS_univ] at hle
  exact lt_of_le_of_lt hle (by norm_num)

lemma muS_ne_top (S : Set ℝ) : muS S ≠ ∞ := ne_of_lt (muS_lt_top S)

/-- real-valued monotonicity of the mass on nested sets -/
lemma toReal_mono {S T : Set ℝ} (h : S ⊆ T) : (muS S).toReal ≤ (muS T).toReal := by
  exact (ENNReal.toReal_le_toReal (muS_ne_top S) (muS_ne_top T)).2 (measure_mono h)

/-- `cdf` is nonnegative and at most 1. -/
lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf x := by
  exact ENNReal.toReal_nonneg

lemma cdf_le_one (x : ℝ) : cdf x ≤ 1 := by
  have hle : muS (Set.Iic x) ≤ muS Set.univ := measure_mono (Set.subset_univ _)
  have hconv : (muS (Set.Iic x)).toReal ≤ (muS Set.univ).toReal :=
    (ENNReal.toReal_le_toReal (muS_ne_top _) (muS_ne_top _)).2 hle
  rw [muS_univ] at hconv
  simpa [cdf] using hconv

/-- `cdf y − cdf x = μ((x, y])` for `x ≤ y`. -/
lemma cdf_sub_eq_Ioc {x y : ℝ} (hxy : x ≤ y) :
    cdf y - cdf x = (muS (Set.Ioc x y)).toReal := by
  have hsub : Set.Iic x ⊆ Set.Iic y := Set.Iic_subset_Iic.mpr hxy
  have hset : Set.Iic y \ Set.Iic x = Set.Ioc x y := by
    ext t
    constructor
    · intro ht
      exact ⟨lt_of_not_ge ht.2, ht.1⟩
    · intro ht
      exact ⟨ht.2, not_le.mpr ht.1⟩
  have hdiffm : muS (Set.Ioc x y) = muS (Set.Iic y) - muS (Set.Iic x) := by
    rw [← hset]
    exact measure_diff hsub (nullMeasurableSet_Iic) (muS_ne_top (Set.Iic x))
  calc
    cdf y - cdf x = (muS (Set.Iic y)).toReal - (muS (Set.Iic x)).toReal := rfl
    _ = (muS (Set.Iic y) - muS (Set.Iic x)).toReal := by
      rw [ENNReal.toReal_sub_of_le (measure_mono hsub) (muS_ne_top (Set.Iic y))]
    _ = (muS (Set.Ioc x y)).toReal := by rw [hdiffm]

/-- Hölder inequality for the `cdf` difference (from interval mass bound) -/
lemma cdf_sub_le_holder {C : ℝ}
    (hC : ∀ ⦃u v : ℝ⦄, aSerre ≤ u → u ≤ v → v ≤ bSerre →
      (muS (Set.Icc u v)).toReal ≤ C * Real.sqrt (v - u))
    {x y : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) (hy : y ∈ Set.Icc aSerre bSerre)
    (hxy : x ≤ y) : cdf y - cdf x ≤ C * Real.sqrt (y - x) := by
  calc
    cdf y - cdf x = (muS (Set.Ioc x y)).toReal := cdf_sub_eq_Ioc hxy
    _ ≤ (muS (Set.Icc x y)).toReal := toReal_mono (Set.Ioc_subset_Icc_self)
    _ ≤ C * Real.sqrt (y - x) := hC hx.1 hxy hy.2

-- ---------------------------------------------------------------------
-- (1) basic facts: endpoints and Hölder regularity of the cdf
-- ---------------------------------------------------------------------

/-- `μ` gives no mass to `{aSerre}` and `{bSerre}` (atom-free). -/
lemma mu_singleton_a : muS {aSerre} = 0 := by
  exact serre_atom_free aSerre

lemma mu_singleton_b : muS {bSerre} = 0 := by
  exact serre_atom_free bSerre

/-- `cdf aSerre = 0` and `cdf bSerre = 1`. -/
lemma cdf_a : cdf aSerre = 0 := by
  have hsub : Set.Iic aSerre ⊆ Set.Iio aSerre ∪ ({aSerre} : Set ℝ) := by
    intro x hx
    by_cases hxeq : x = aSerre
    · exact Or.inr hxeq
    · exact Or.inl (lt_of_le_of_ne hx hxeq)
  have hIio : muS (Set.Iio aSerre) = 0 := by
    apply le_antisymm
    · have hsub2 : Set.Iio aSerre ⊆ (Set.Icc aSerre bSerre)ᶜ := by
        intro x hx hmem
        exact (not_le_of_gt hx) hmem.1
      calc
        muS (Set.Iio aSerre) ≤ muS ((Set.Icc aSerre bSerre)ᶜ) := measure_mono hsub2
        _ = 0 := muS_compl_Icc
    · exact zero_le
  have hdisj : Disjoint (Set.Iio aSerre) ({aSerre} : Set ℝ) := by
    rw [Set.disjoint_singleton_right]
    intro h
    exact (lt_irrefl aSerre) h
  have hunion : muS (Set.Iio aSerre ∪ ({aSerre} : Set ℝ)) = 0 := by
    rw [measure_union hdisj (measurableSet_singleton aSerre)]
    simp [hIio, mu_singleton_a]
  have hmain : muS (Set.Iic aSerre) = 0 := by
    apply le_antisymm
    · calc
        muS (Set.Iic aSerre) ≤ muS (Set.Iio aSerre ∪ ({aSerre} : Set ℝ)) := measure_mono hsub
        _ = 0 := hunion
    · exact zero_le
  simp [cdf, hmain]

lemma cdf_b : cdf bSerre = 1 := by
  have hIoi : muS (Set.Ioi bSerre) = 0 := by
    apply le_antisymm
    · have hsub : Set.Ioi bSerre ⊆ (Set.Icc aSerre bSerre)ᶜ := by
        intro x hx hmem
        exact (not_le_of_gt hx) hmem.2
      calc
        muS (Set.Ioi bSerre) ≤ muS ((Set.Icc aSerre bSerre)ᶜ) := measure_mono hsub
        _ = 0 := muS_compl_Icc
    · exact zero_le
  have hcomp : (Set.Iic bSerre)ᶜ = Set.Ioi bSerre := by
    ext x
    simp
  have hsum := measure_add_measure_compl (μ := muS) (measurableSet_Iic : MeasurableSet (Set.Iic bSerre))
  rw [hcomp, hIoi, muS_univ] at hsum
  have hmain : muS (Set.Iic bSerre) = 1 := by
    simpa using hsum
  simp [cdf, hmain]

/-- `cdf` is monotone. -/
lemma cdf_mono {x y : ℝ} (hxy : x ≤ y) : cdf x ≤ cdf y := by
  exact toReal_mono (Set.Iic_subset_Iic.mpr hxy)

/-- Hölder bound on interval mass (real form): there is `C > 0` such that for
`aSerre ≤ u ≤ v ≤ bSerre`, `μ(Icc u v) ≤ C·√(v−u)`. -/
lemma exists_interval_holder :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃u v : ℝ⦄, aSerre ≤ u → u ≤ v → v ≤ bSerre →
      (muS (Set.Icc u v)).toReal ≤ C * Real.sqrt (v - u) := by
  refine ⟨4 * (aSerre + bSerre) / (aSerre * Real.sqrt (bSerre - aSerre)), ?hpos, ?hbd⟩
  · have hba : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
    have hsqrt : 0 < Real.sqrt (bSerre - aSerre) := Real.sqrt_pos.mpr hba
    exact div_pos (mul_pos (by norm_num) (add_pos aSerre_pos bSerre_pos)) (mul_pos aSerre_pos hsqrt)
  · intro u v hu huv hv
    have hC_nonneg : 0 ≤ 4 * (aSerre + bSerre) / (aSerre * Real.sqrt (bSerre - aSerre)) := by
      have hba : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
      have hsqrt : 0 < Real.sqrt (bSerre - aSerre) := Real.sqrt_pos.mpr hba
      exact le_of_lt (div_pos (mul_pos (by norm_num) (add_pos aSerre_pos bSerre_pos))
        (mul_pos aSerre_pos hsqrt))
    have h := serre_holder (a := aSerre) (b := bSerre) (γ := gSerre) (u := u) (v := v)
      aSerre_pos a_lt_b (le_of_lt gSerre_pos) gSerre_le_one hu huv hv
    have hreal := (ENNReal.toReal_le_toReal (muS_ne_top (Set.Icc u v))
      (ENNReal.ofReal_lt_top.ne)).2 h
    rw [ENNReal.toReal_ofReal (mul_nonneg hC_nonneg (Real.sqrt_nonneg (v - u)))] at hreal
    simpa using hreal

/-- `cdf` is `1/2`-Hölder on `[aSerre,bSerre]`: there is `C ≥ 0` with
`|cdf x − cdf y| ≤ C·√|x−y|` on the interval. -/
lemma exists_cdf_half_holder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |cdf x - cdf y| ≤ C * Real.sqrt |x - y| := by
  rcases exists_interval_holder with ⟨C0, hC0pos, hC0⟩
  refine ⟨C0, le_of_lt hC0pos, ?_⟩
  intro x y hx hy
  by_cases hxy : x ≤ y
  · have hmain : cdf y - cdf x ≤ C0 * Real.sqrt (y - x) :=
      cdf_sub_le_holder hC0 hx hy hxy
    have habs : |cdf x - cdf y| = cdf y - cdf x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (cdf_mono hxy))]
      ring
    have hsq : Real.sqrt (y - x) = Real.sqrt |x - y| := by
      rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    calc
      |cdf x - cdf y| = cdf y - cdf x := habs
      _ ≤ C0 * Real.sqrt (y - x) := hmain
      _ = C0 * Real.sqrt |x - y| := by rw [hsq]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmain : cdf x - cdf y ≤ C0 * Real.sqrt (x - y) :=
      cdf_sub_le_holder hC0 hy hx hyx
    have habs : |cdf x - cdf y| = cdf x - cdf y := by
      rw [abs_of_nonneg (sub_nonneg.mpr (cdf_mono hyx))]
    have hsq : Real.sqrt (x - y) = Real.sqrt |x - y| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    calc
      |cdf x - cdf y| = cdf x - cdf y := habs
      _ ≤ C0 * Real.sqrt (x - y) := hmain
      _ = C0 * Real.sqrt |x - y| := by rw [hsq]

/-- `cdf` is continuous on `[aSerre,bSerre]`. -/
lemma cdf_continuousOn : ContinuousOn cdf (Set.Icc aSerre bSerre) := by
  rcases exists_cdf_half_holder with ⟨C, hC0, hC⟩
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  by_cases hCz : C = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy hyx
    have hb := hC y x hy hx
    rw [hCz] at hb
    have h0 : |cdf y - cdf x| = 0 := by
      have hle : |cdf y - cdf x| ≤ 0 := by simpa using hb
      exact le_antisymm hle (abs_nonneg _)
    rw [Real.dist_eq]
    simpa [h0] using hε
  · have hCpos : 0 < C := by
      rcases lt_or_eq_of_le hC0 with hpos | heq
      · exact hpos
      · exfalso
        exact hCz heq.symm
    let δ : ℝ := (ε / C) ^ 2
    refine ⟨δ, ?hδpos, ?_⟩
    · dsimp [δ]
      exact sq_pos_of_pos (div_pos hε hCpos)
    · intro y hy hyx
      have hdist : |y - x| < δ := by
        simpa [Real.dist_eq] using hyx
      have hle := hC y x hy hx
      have hlt : C * Real.sqrt |y - x| < ε := by
        have hnonneg : 0 ≤ |y - x| := abs_nonneg _
        have hlt2 : Real.sqrt |y - x| < Real.sqrt δ := Real.sqrt_lt_sqrt hnonneg hdist
        have hsqrtδ : Real.sqrt δ = ε / C := by
          dsimp [δ]
          rw [Real.sqrt_sq_eq_abs]
          rw [abs_of_pos (div_pos hε hCpos)]
        calc
          C * Real.sqrt |y - x| < C * Real.sqrt δ := mul_lt_mul_of_pos_left hlt2 hCpos
          _ = C * (ε / C) := by rw [hsqrtδ]
          _ = ε := by field_simp [ne_of_gt hCpos]
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hle hlt

/-- the set whose infimum defines the quantile -/
noncomputable def qS (v : ℝ) : Set ℝ := {x : ℝ | x ∈ Set.Icc aSerre bSerre ∧ v ≤ cdf x}

/-- the defining set is bounded below by `aSerre` -/
lemma qS_bddBelow (v : ℝ) : BddBelow (qS v) :=
  ⟨aSerre, by intro x hx; exact hx.1.1⟩

/-- for `v ≤ 1` the defining set contains `bSerre` -/
lemma qS_nonempty {v : ℝ} (hv1 : v ≤ 1) : (qS v).Nonempty := by
  refine ⟨bSerre, ?_⟩
  constructor
  · exact ⟨a_le_b, le_rfl⟩
  · rw [cdf_b]
    exact hv1

-- ---------------------------------------------------------------------
-- (2) quantile map
-- ---------------------------------------------------------------------

/-- For `0 ≤ v ≤ 1`, the quantile lies in `[aSerre,bSerre]`. -/
lemma qpoint_mem_Icc {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    qpoint v ∈ Set.Icc aSerre bSerre := by
  have hle : aSerre ≤ qpoint v := by
    simpa [qpoint, qS] using
      (le_csInf (qS_nonempty hv1) (by intro x hx; exact hx.1.1))
  have hge : qpoint v ≤ bSerre := by
    simpa [qpoint, qS] using
      (csInf_le (qS_bddBelow v) (by
        constructor
        · exact ⟨a_le_b, le_rfl⟩
        · rw [cdf_b]
          exact hv1))
  exact ⟨hle, hge⟩

/-- For `0 ≤ v ≤ 1`, `cdf (qpoint v) = v` (the quantile inverts `cdf`). -/
lemma qpoint_cdf_eq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    cdf (qpoint v) = v := by
  let q : ℝ := qpoint v
  have hqIcc : q ∈ Set.Icc aSerre bSerre := by
    simpa [q] using (qpoint_mem_Icc hv0 hv1)
  have hcont : ContinuousWithinAt cdf (Set.Icc aSerre bSerre) q :=
    cdf_continuousOn.continuousWithinAt hqIcc
  have hs : sInf (qS v) = q := by
    dsimp [q, qpoint, qS]
  have hge : v ≤ cdf q := by
    by_contra hnot
    have hlt : cdf q < v := lt_of_not_ge hnot
    let ε : ℝ := (v - cdf q) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    rcases (Metric.continuousWithinAt_iff.mp hcont ε hε) with ⟨δ, hδpos, hδbd⟩
    have hlt2 : sInf (qS v) < q + δ := by
      rw [hs]
      linarith
    rcases exists_lt_of_csInf_lt (qS_nonempty hv1) hlt2 with ⟨a, haS, ha⟩
    have hqa : q ≤ a := by
      rw [← hs]
      exact csInf_le (qS_bddBelow v) haS
    have haIcc : a ∈ Set.Icc aSerre bSerre := haS.1
    have habs : |a - q| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hqa)]
      linarith
    have hdistc : dist (cdf a) (cdf q) < ε := hδbd haIcc habs
    have hcsub : cdf a - cdf q < ε := (abs_lt.mp (by simpa [Real.dist_eq] using hdistc)).2
    have hcv : cdf a < v := by
      have hbound : cdf q + ε < v := by dsimp [ε]; linarith
      linarith
    exact (not_le_of_gt hcv) haS.2
  have hle : cdf q ≤ v := by
    by_contra hnot
    have hlt : v < cdf q := lt_of_not_ge hnot
    by_cases hqa : q = aSerre
    · have hcq : cdf q = 0 := by rw [hqa, cdf_a]
      linarith
    · have hqa' : aSerre < q := lt_of_le_of_ne hqIcc.1 (by exact fun h => hqa h.symm)
      let ε : ℝ := (cdf q - v) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      rcases (Metric.continuousWithinAt_iff.mp hcont ε hε) with ⟨δ, hδpos, hδbd⟩
      let η : ℝ := min (δ / 2) ((q - aSerre) / 2)
      have hη : 0 < η := by
        dsimp [η]
        exact lt_min (div_pos hδpos (by norm_num)) (div_pos (sub_pos.mpr hqa') (by norm_num))
      let y : ℝ := q - η
      have hyIcc : y ∈ Set.Icc aSerre bSerre := by
        constructor
        · have h1 : η ≤ (q - aSerre) / 2 := min_le_right _ _
          have h2 : aSerre ≤ q - (q - aSerre) / 2 := by linarith
          dsimp [y]
          linarith
        · dsimp [y]
          linarith [hqIcc.2]
      have hyq : |y - q| < δ := by
        have hmin : η ≤ δ / 2 := min_le_left _ _
        have hηlt : η < δ := by linarith
        have habs : |y - q| = η := by
          dsimp [y]
          have hneg : q - η - q = -η := by ring
          rw [hneg, abs_neg]
          rw [abs_of_nonneg hη.le]
        rw [habs]
        exact hηlt
      have hdistc : dist (cdf y) (cdf q) < ε := hδbd hyIcc hyq
      have hcgt : cdf q - cdf y < ε := by
        have htmp := abs_lt.mp (by simpa [Real.dist_eq] using hdistc)
        -- htmp : -(ε) < cdf y - cdf q ∧ cdf y - cdf q < ε
        linarith
      have hcv : v < cdf y := by
        have hbound : cdf q - ε > v := by dsimp [ε]; linarith
        linarith
      have hyS : y ∈ qS v := ⟨hyIcc, le_of_lt hcv⟩
      have hqy : q ≤ y := by
        rw [← hs]
        exact csInf_le (qS_bddBelow v) hyS
      dsimp [y] at hqy
      linarith
  exact le_antisymm hle hge

/-- `qpoint` is monotone for `0 ≤ v ≤ w ≤ 1`.

The originally given hypotheses `(v ≤ 1) (0 ≤ w) (v ≤ w)` made the statement
FALSE: for `w > 1` the set `{x ∈ Icc | w ≤ cdf x}` is empty and
`qpoint w = sInf ∅ = 0 < aSerre ≤ qpoint v`.  The correct hypotheses, which
are all one ever has (both levels lie in `[0,1]`), are `0 ≤ w`, `w ≤ 1`. -/
lemma qpoint_mono {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hvw : v ≤ w) :
    qpoint v ≤ qpoint w := by
  have hwqIcc : qpoint w ∈ Set.Icc aSerre bSerre := qpoint_mem_Icc hw0 hw1
  have hcq : cdf (qpoint w) = w := qpoint_cdf_eq hw0 hw1
  have hmem : qpoint w ∈ qS v := by
    constructor
    · exact hwqIcc
    · rw [hcq]
      exact hvw
  simpa [qpoint, qS] using (csInf_le (qS_bddBelow v) hmem)

/-- Minimality: if `x ∈ [aSerre,bSerre]` and `cdf x ≥ v`, then `qpoint v ≤ x`. -/
lemma qpoint_le_of_cdf_ge {v x : ℝ} (hv1 : v ≤ 1) (hx : x ∈ Set.Icc aSerre bSerre)
    (h : v ≤ cdf x) : qpoint v ≤ x := by
  have hmem : x ∈ qS v := ⟨hx, h⟩
  simpa [qpoint, qS] using (csInf_le (qS_bddBelow v) hmem)

/-- If `cdf x < v` then `x < qpoint v` (provided both are in range).

Needs `v ≤ 1`: without it (e.g. `v = 2`) the set defining `qpoint v` is
empty, `qpoint v = 0`, and the claim would fail at `x = aSerre`. -/
lemma lt_qpoint_of_cdf_lt {v x : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hx : x ∈ Set.Icc aSerre bSerre) (h : cdf x < v) : x < qpoint v := by
  by_contra hnot
  have hge : qpoint v ≤ x := le_of_not_gt hnot
  have hcq : cdf (qpoint v) = v := qpoint_cdf_eq hv0 hv1
  have hmono := cdf_mono hge
  rw [hcq] at hmono
  exact (not_le_of_gt h) hmono

/-- Roots are in the closed interval. -/
lemma alpha_mem_Icc {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    alpha n i ∈ Set.Icc aSerre bSerre := by
  change qpoint ((i : ℝ) / (n : ℝ)) ∈ Set.Icc aSerre bSerre
  apply qpoint_mem_Icc
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    exact div_nonneg (by positivity : 0 ≤ (i : ℝ)) (le_of_lt hn0)
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    rw [div_le_iff₀ hn0]
    nlinarith [show (i : ℝ) ≤ (n : ℝ) by exact_mod_cast hin]

/-- Root levels: `cdf (alpha n i) = i/n` for `1 ≤ i ≤ n`. -/
lemma alpha_cdf_eq {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    cdf (alpha n i) = (i : ℝ) / (n : ℝ) := by
  change cdf (qpoint ((i : ℝ) / (n : ℝ))) = (i : ℝ) / (n : ℝ)
  apply qpoint_cdf_eq
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    exact div_nonneg (by positivity : 0 ≤ (i : ℝ)) (le_of_lt hn0)
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    rw [div_le_iff₀ hn0]
    nlinarith [show (i : ℝ) ≤ (n : ℝ) by exact_mod_cast hin]

/-- Roots are strictly increasing. -/
lemma alpha_strict_mono {n i j : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n) :
    alpha n i < alpha n j := by
  by_contra hnot
  have hle : alpha n j ≤ alpha n i := le_of_not_gt hnot
  have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) :=
    alpha_cdf_eq hn hi (le_trans (le_of_lt hij) hjn)
  have hcj : cdf (alpha n j) = (j : ℝ) / (n : ℝ) :=
    alpha_cdf_eq hn (le_trans hi (le_of_lt hij)) hjn
  have hmono : cdf (alpha n j) ≤ cdf (alpha n i) := cdf_mono hle
  have hrat : (j : ℝ) / (n : ℝ) ≤ (i : ℝ) / (n : ℝ) := by
    rw [← hcj, ← hci]
    exact hmono
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hineq : (j : ℝ) ≤ (i : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_right hrat (le_of_lt hn0)
    field_simp [ne_of_gt hn0] at hprod
    exact hprod
  have hji : j ≤ i := by exact_mod_cast hineq
  exact (lt_irrefl i) (lt_of_lt_of_le hij hji)

-- ---------------------------------------------------------------------
-- (3a) real/measure machinery for the spacing and margin estimates
-- ---------------------------------------------------------------------

/-- `cdf v − cdf u ≤ μ(Icc u v)` for `u ≤ v`. -/
lemma cdf_diff_le_Icc {u v : ℝ} (huv : u ≤ v) :
    cdf v - cdf u ≤ (muS (Set.Icc u v)).toReal := by
  calc
    cdf v - cdf u = (muS (Set.Ioc u v)).toReal := cdf_sub_eq_Ioc huv
    _ ≤ (muS (Set.Icc u v)).toReal := toReal_mono (Set.Ioc_subset_Icc_self)

/-- From a linear-in-`√d` upper bound `L ≤ C0·√d` get the quadratic lower bound
`L²/C0² ≤ d` (all quantities nonnegative). -/
lemma lower_bound_from_holder {d L C0 : ℝ} (hC0 : 0 < C0) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (h : L ≤ C0 * Real.sqrt d) : L ^ 2 / C0 ^ 2 ≤ d := by
  have hdiv : L / C0 ≤ Real.sqrt d := by
    exact (div_le_iff₀ hC0).2 (by simpa [mul_comm] using h)
  have hnonneg : 0 ≤ L / C0 := div_nonneg hL (le_of_lt hC0)
  have hpow : (L / C0) ^ 2 ≤ (Real.sqrt d) ^ 2 := pow_le_pow_left₀ hnonneg hdiv 2
  have hd' : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd
  have h' : (L / C0) ^ 2 ≤ d := by rwa [hd'] at hpow
  calc
    L ^ 2 / C0 ^ 2 = (L / C0) ^ 2 := by field_simp [ne_of_gt hC0]
    _ ≤ d := h'

/-- If `1/n ≤ C0·√d` then `(max C0 1 · n)⁻¹² ≤ d` (for `n > 0`). -/
lemma one_over_n_le_of_holder {C0 : ℝ} {d : ℝ} {n : ℕ} (hC0 : 0 < C0)
    (hn0 : 0 < (n : ℝ)) (hd : 0 ≤ d) (h : (1 : ℝ) / (n : ℝ) ≤ C0 * Real.sqrt d) :
    (max C0 1 * (n : ℝ))⁻¹ ^ 2 ≤ d := by
  have hlib := lower_bound_from_holder hC0 (by positivity : 0 ≤ (1 : ℝ) / (n : ℝ)) hd h
  have heq : ((1 : ℝ) / (n : ℝ)) ^ 2 / C0 ^ 2 = (C0 * (n : ℝ))⁻¹ ^ 2 := by
    field_simp [ne_of_gt hC0, ne_of_gt hn0]
  have hb1 : (C0 * (n : ℝ))⁻¹ ^ 2 ≤ d := by
    calc
      (C0 * (n : ℝ))⁻¹ ^ 2 = ((1 : ℝ) / (n : ℝ)) ^ 2 / C0 ^ 2 := by rw [heq]
      _ ≤ d := hlib
  have hC0le : C0 ≤ max C0 1 := le_max_left C0 1
  have hCpos : 0 < max C0 1 := lt_of_lt_of_le hC0 hC0le
  have hCin : 0 < C0 * (n : ℝ) := mul_pos hC0 hn0
  have hCnin : 0 < max C0 1 * (n : ℝ) := mul_pos hCpos hn0
  have hmult : C0 * (n : ℝ) ≤ max C0 1 * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hC0le (le_of_lt hn0)
  have hinv : (max C0 1 * (n : ℝ))⁻¹ ≤ (C0 * (n : ℝ))⁻¹ :=
    (inv_le_inv₀ hCnin hCin).2 hmult
  have hsq : (max C0 1 * (n : ℝ))⁻¹ ^ 2 ≤ (C0 * (n : ℝ))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hCnin.le) hinv 2
  exact le_trans hsq hb1

-- ---------------------------------------------------------------------
-- (3) spacing of consecutive quantiles
-- ---------------------------------------------------------------------

/-- Consecutive quantiles are polynomially spaced:
`∃ C ≥ 1, ∀ n ≥ 2, ∀ i, 1 ≤ i → i < n → (C·n)^{-2} ≤ alpha n (i+1) − alpha n i`. -/
lemma exists_spacing :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, 1 ≤ i → i < n →
      (C * (n : ℝ))⁻¹ ^ 2 ≤ alpha n (i + 1) - alpha n i := by
  rcases exists_interval_holder with ⟨C0, hC0pos, hC0⟩
  refine ⟨max C0 1, le_max_right C0 1, ?_⟩
  intro n hn i hi hin
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmi : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn1 hi (by omega)
  have hmi1 : alpha n (i + 1) ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn1 (by omega) (by omega)
  have hst : alpha n i < alpha n (i + 1) := alpha_strict_mono hn1 hi (by omega) (by omega)
  have hcdf : cdf (alpha n (i + 1)) - cdf (alpha n i) = (1 : ℝ) / (n : ℝ) := by
    have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) := alpha_cdf_eq hn1 hi (by omega)
    have hci1 : cdf (alpha n (i + 1)) = ((i + 1 : ℕ) : ℝ) / (n : ℝ) :=
      alpha_cdf_eq hn1 (by omega) (by omega)
    rw [hci1, hci]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hn0]
    ring
  have hLn : (1 : ℝ) / (n : ℝ) ≤ (muS (Set.Icc (alpha n i) (alpha n (i + 1)))).toReal := by
    calc
      (1 : ℝ) / (n : ℝ) = cdf (alpha n (i + 1)) - cdf (alpha n i) := hcdf.symm
      _ ≤ (muS (Set.Icc (alpha n i) (alpha n (i + 1)))).toReal :=
        cdf_diff_le_Icc (le_of_lt hst)
  have hbd : (muS (Set.Icc (alpha n i) (alpha n (i + 1)))).toReal ≤
      C0 * Real.sqrt (alpha n (i + 1) - alpha n i) :=
    hC0 hmi.1 (le_of_lt hst) hmi1.2
  have hlin : (1 : ℝ) / (n : ℝ) ≤ C0 * Real.sqrt (alpha n (i + 1) - alpha n i) :=
    le_trans hLn hbd
  exact one_over_n_le_of_holder hC0pos hn0
    (sub_nonneg.mpr (le_of_lt hst)) hlin

/-- Quantiles are separated from the boundary at a polynomial rate on the
left: `∃ C ≥ 1, ∀ n ≥ 2, ∀ i, 2 ≤ i → i ≤ n → (C·n)^{-2} ≤ alpha n i − aSerre`. -/
lemma exists_left_margin :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, 2 ≤ i → i ≤ n →
      (C * (n : ℝ))⁻¹ ^ 2 ≤ alpha n i - aSerre := by
  rcases exists_interval_holder with ⟨C0, hC0pos, hC0⟩
  refine ⟨max C0 1, le_max_right C0 1, ?_⟩
  intro n hn i hi hin
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmi : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn1 (by omega) hin
  have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) := alpha_cdf_eq hn1 (by omega) hin
  have hcdf : cdf (alpha n i) - cdf aSerre = (i : ℝ) / (n : ℝ) := by
    rw [hci, cdf_a]
    ring
  have hi1R : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ i)
  have hfrac : (1 : ℝ) / (n : ℝ) ≤ (i : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hn0 hn0]
    nlinarith
  have hLn : (1 : ℝ) / (n : ℝ) ≤ (muS (Set.Icc aSerre (alpha n i))).toReal := by
    calc
      (1 : ℝ) / (n : ℝ) ≤ (i : ℝ) / (n : ℝ) := hfrac
      _ = cdf (alpha n i) - cdf aSerre := hcdf.symm
      _ ≤ (muS (Set.Icc aSerre (alpha n i))).toReal := cdf_diff_le_Icc hmi.1
  have hbd : (muS (Set.Icc aSerre (alpha n i))).toReal ≤
      C0 * Real.sqrt (alpha n i - aSerre) :=
    hC0 (le_rfl : aSerre ≤ aSerre) hmi.1 hmi.2
  have hlin : (1 : ℝ) / (n : ℝ) ≤ C0 * Real.sqrt (alpha n i - aSerre) :=
    le_trans hLn hbd
  exact one_over_n_le_of_holder hC0pos hn0 (sub_nonneg.mpr hmi.1) hlin

/-- Quantiles are separated from the boundary on the right:
`∃ C ≥ 1, ∀ n ≥ 2, ∀ i, 1 ≤ i → i + 1 ≤ n → (C·n)^{-2} ≤ bSerre − alpha n i`. -/
lemma exists_right_margin :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ i : ℕ, 1 ≤ i → i + 1 ≤ n →
      (C * (n : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha n i := by
  rcases exists_interval_holder with ⟨C0, hC0pos, hC0⟩
  refine ⟨max C0 1, le_max_right C0 1, ?_⟩
  intro n hn i hi hin
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hin' : i ≤ n := by omega
  have hmi : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn1 hi hin'
  have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) := alpha_cdf_eq hn1 hi hin'
  have hcdf : cdf bSerre - cdf (alpha n i) = ((n : ℝ) - (i : ℝ)) / (n : ℝ) := by
    rw [cdf_b, hci]
    field_simp [ne_of_gt hn0]
  have hni1R : 1 ≤ (n : ℝ) - (i : ℝ) := by
    have hR : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hin
    nlinarith
  have hfrac : (1 : ℝ) / (n : ℝ) ≤ ((n : ℝ) - (i : ℝ)) / (n : ℝ) := by
    rw [div_le_div_iff₀ hn0 hn0]
    nlinarith
  have hLn : (1 : ℝ) / (n : ℝ) ≤ (muS (Set.Icc (alpha n i) bSerre)).toReal := by
    calc
      (1 : ℝ) / (n : ℝ) ≤ ((n : ℝ) - (i : ℝ)) / (n : ℝ) := hfrac
      _ = cdf bSerre - cdf (alpha n i) := hcdf.symm
      _ ≤ (muS (Set.Icc (alpha n i) bSerre)).toReal := cdf_diff_le_Icc hmi.2
  have hbd : (muS (Set.Icc (alpha n i) bSerre)).toReal ≤
      C0 * Real.sqrt (bSerre - alpha n i) :=
    hC0 hmi.1 hmi.2 (le_rfl : bSerre ≤ bSerre)
  have hlin : (1 : ℝ) / (n : ℝ) ≤ C0 * Real.sqrt (bSerre - alpha n i) :=
    le_trans hLn hbd
  exact one_over_n_le_of_holder hC0pos hn0 (sub_nonneg.mpr hmi.2) hlin

-- ---------------------------------------------------------------------
-- (4a) counting the roots on a ray and inside an interval
-- ---------------------------------------------------------------------

/-- For `x ∈ [aSerre,bSerre]` and `1 ≤ n`, `alpha n i ≤ x` iff `i ≤ n·cdf x`
(for `i ∈ [1..n]`), so `countRoots n x` counts `i` in `[1..n]` with
`(i : ℝ) ≤ (n : ℝ) * cdf x`. -/
lemma countRoots_eq {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    countRoots n x = ((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ (n : ℝ) * cdf x).card := by
  unfold countRoots
  congr 1
  apply Finset.ext
  intro i
  by_cases hmem : i ∈ Finset.Icc 1 n
  · have hrange : 1 ≤ i ∧ i ≤ n := (Finset.mem_Icc).mp hmem
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    have hiff1 : alpha n i ≤ x ↔ (i : ℝ) / (n : ℝ) ≤ cdf x := by
      constructor
      · intro hle
        have hmono := cdf_mono hle
        have hci : cdf (alpha n i) = (i : ℝ) / (n : ℝ) := alpha_cdf_eq hn hrange.1 hrange.2
        rwa [hci] at hmono
      · intro hle
        exact qpoint_le_of_cdf_ge (v := (i : ℝ) / (n : ℝ))
          (by rw [div_le_iff₀ hn0]; norm_num; exact_mod_cast hrange.2) hx hle
    have hiff2 : (i : ℝ) / (n : ℝ) ≤ cdf x ↔ (i : ℝ) ≤ (n : ℝ) * cdf x := by
      rw [div_le_iff₀ hn0]
      constructor <;> intro h
      · simpa [mul_comm] using h
      · simpa [mul_comm] using h
    simpa [hmem] using (hiff1.trans hiff2)
  · simp [hmem]

/-- `filter(α ≤ v) = filter(α ≤ u) ∪ filter(u < α ∧ α ≤ v)` (for `u ≤ v`). -/
lemma filter_le_union {n : ℕ} {u v : ℝ} (huv : u ≤ v) :
    (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ v) =
      ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ u) ∪
        (Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)) := by
  ext i
  by_cases hmem : i ∈ Finset.Icc 1 n
  · have hiff : (alpha n i ≤ v) ↔ (alpha n i ≤ u) ∨ (u < alpha n i ∧ alpha n i ≤ v) := by
      constructor
      · intro hcv
        by_cases hcu : alpha n i ≤ u
        · exact Or.inl hcu
        · exact Or.inr ⟨lt_of_not_ge hcu, hcv⟩
      · intro h
        rcases h with hcu | hfu
        · exact le_trans hcu huv
        · exact hfu.2
    simp [Finset.mem_union, Finset.mem_filter, hmem]
    exact hiff
  · simp [Finset.mem_union, Finset.mem_filter, hmem]

/-- `filter(u ≤ α ≤ v) = filter(u < α ∧ α ≤ v) ∪ filter(α = u)` (for `u ≤ v`). -/
lemma filter_interval_union {n : ℕ} {u v : ℝ} (huv : u ≤ v) :
    (Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v) =
      ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) ∪
        (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i = u)) := by
  ext i
  by_cases hmem : i ∈ Finset.Icc 1 n
  · have hiff : (u ≤ alpha n i ∧ alpha n i ≤ v) ↔
        (u < alpha n i ∧ alpha n i ≤ v) ∨ alpha n i = u := by
      constructor
      · intro hb
        by_cases hlt : u < alpha n i
        · exact Or.inl ⟨hlt, hb.2⟩
        · exact Or.inr (le_antisymm (le_of_not_gt hlt) hb.1)
      · intro h
        rcases h with hf | hg
        · exact ⟨le_of_lt hf.1, hf.2⟩
        · rw [hg]
          exact ⟨le_rfl, huv⟩
    simp [Finset.mem_union, Finset.mem_filter, hmem]
    exact hiff
  · simp [Finset.mem_union, Finset.mem_filter, hmem]

/-- Bounding the number of roots in `[u,v]` by the number `F.card` of roots in
`(u,v]` (purely index-level): `countRoots n v = countRoots n u + F.card` and
`F.card ≤ S.card ≤ F.card + 1`.  Requires `1 ≤ n` (for strict monotonicity
of the roots in the proof that at most one root equals `u`). -/
lemma between_countRoots {n : ℕ} (hn1 : 1 ≤ n) {u v : ℝ} (huv : u ≤ v) :
    countRoots n v = countRoots n u +
        ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card ∧
      ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card ≤
        ((Finset.Icc 1 n).filter fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v).card ∧
      ((Finset.Icc 1 n).filter fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v).card ≤
        ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card + 1 := by
  have hCEF' := filter_le_union (n := n) (u := u) (v := v) huv
  have hSFG' := filter_interval_union (n := n) (u := u) (v := v) huv
  have hdisjEF : Disjoint ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i ≤ u)
      ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) := by
    rw [Finset.disjoint_filter]
    intro i hmem hcu hfu
    exact (not_lt_of_ge hcu) hfu.1
  have hdisjFG : Disjoint ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)
      ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i = u) := by
    rw [Finset.disjoint_filter]
    intro i hmem hf hg
    rw [hg] at hf
    exact (lt_irrefl u) hf.1
  have hcardC : ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ v)).card =
      ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ u)).card +
        ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card := by
    have h1 := Finset.card_union_add_card_inter
      ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i ≤ u)
      ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)
    have hint : (((Finset.Icc 1 n).filter fun i : ℕ => alpha n i ≤ u) ∩
        ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card = 0 := by
      have h2 : ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i ≤ u) ∩
          ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) = ∅ :=
        (Finset.disjoint_iff_inter_eq_empty).mp hdisjEF
      rw [h2]
      simp
    rw [← hCEF'] at h1
    rw [hint] at h1
    simpa using h1
  have hcardS : ((Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v)).card =
      ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card +
        ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i = u)).card := by
    have h1 := Finset.card_union_add_card_inter
      ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)
      ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i = u)
    have hint : (((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) ∩
        ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i = u)).card = 0 := by
      have h2 : ((Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) ∩
          ((Finset.Icc 1 n).filter fun i : ℕ => alpha n i = u) = ∅ :=
        (Finset.disjoint_iff_inter_eq_empty).mp hdisjFG
      rw [h2]
      simp
    rw [← hSFG'] at h1
    rw [hint] at h1
    simpa using h1
  have hGle1 : ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i = u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hne
    exfalso
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmemI : i ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hi).1
      have hmemJ : j ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hj).1
      have hri : 1 ≤ i ∧ i ≤ n := (Finset.mem_Icc).mp hmemI
      have hrj : 1 ≤ j ∧ j ≤ n := (Finset.mem_Icc).mp hmemJ
      have hgi : alpha n i = u := (Finset.mem_filter.mp hi).2
      have hgj : alpha n j = u := (Finset.mem_filter.mp hj).2
      have hst : alpha n i < alpha n j := alpha_strict_mono hn1 hri.1 hlt hrj.2
      rw [hgi, hgj] at hst
      exact (lt_irrefl u) hst
    · have hmemI : i ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hi).1
      have hmemJ : j ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hj).1
      have hri : 1 ≤ i ∧ i ≤ n := (Finset.mem_Icc).mp hmemI
      have hrj : 1 ≤ j ∧ j ≤ n := (Finset.mem_Icc).mp hmemJ
      have hgi : alpha n i = u := (Finset.mem_filter.mp hi).2
      have hgj : alpha n j = u := (Finset.mem_filter.mp hj).2
      have hst : alpha n j < alpha n i := alpha_strict_mono hn1 hrj.1 hgt hri.2
      rw [hgi, hgj] at hst
      exact (lt_irrefl u) hst
  have hEuC : ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ u)).card ≤
      ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ v)).card := by
    have hsub : (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ u) ⊆
        (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ≤ v) := by
      intro i hi
      have hmemI : i ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hi).1
      have hleu : alpha n i ≤ u := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨hmemI, le_trans hleu huv⟩
    exact Finset.card_le_card hsub
  have hFuS : ((Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v)).card ≤
      ((Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v)).card := by
    have hsub : (Finset.Icc 1 n).filter (fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v) ⊆
        (Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v) := by
      intro i hi
      have hmemI : i ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hi).1
      have hf : u < alpha n i ∧ alpha n i ≤ v := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨hmemI, ⟨le_of_lt hf.1, hf.2⟩⟩
    exact Finset.card_le_card hsub
  constructor
  · -- countRoots n v = countRoots n u + F.card
    unfold countRoots
    rw [hcardC]
  · constructor
    · exact hFuS
    · rw [hcardS]
      omega

/-- the number of `i ∈ [1..n]` with `i ≤ m` is between `m−1` and `m`
(for `0 ≤ m ≤ n`). -/
lemma card_filter_le_real {n : ℕ} {m : ℝ} (_hn0 : 0 < (n : ℝ)) (hm0 : 0 ≤ m) (hmn : m ≤ (n : ℝ)) :
    (((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card : ℝ) ≤ m ∧
      m ≤ (((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card : ℝ) + 1 := by
  let f : ℕ := Nat.floor m
  let A : Finset ℕ := (Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m
  have hfl : A = Finset.Icc 1 (min n f) := by
    apply Finset.ext
    intro i
    by_cases hmem : i ∈ Finset.Icc 1 n
    · have hiff : (i : ℝ) ≤ m ↔ i ≤ f := by
        constructor
        · intro hiR
          exact Nat.le_floor hiR
        · intro hif
          exact le_trans (by exact_mod_cast hif : (i : ℝ) ≤ (f : ℝ)) (Nat.floor_le hm0)
      change i ∈ (Finset.Icc 1 n).filter (fun i : ℕ => (i : ℝ) ≤ m) ↔ i ∈ Finset.Icc 1 (min n f)
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, hiff]
      constructor
      · intro h
        exact ⟨h.1.1, le_min h.1.2 h.2⟩
      · intro h
        exact ⟨⟨h.1, le_trans h.2 (min_le_left n f)⟩, le_trans h.2 (min_le_right n f)⟩
    · have hmem' : ¬ (1 ≤ i ∧ i ≤ n) := by simpa [Finset.mem_Icc] using hmem
      change i ∈ (Finset.Icc 1 n).filter (fun i : ℕ => (i : ℝ) ≤ m) ↔ i ∈ Finset.Icc 1 (min n f)
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      constructor
      · intro h
        exact (hmem' h.1).elim
      · intro h
        exact (hmem' ⟨h.1, le_trans h.2 (min_le_left n f)⟩).elim
  have hcard : A.card = min n f := by
    rw [hfl]
    rw [Nat.card_Icc]
    omega
  constructor
  · have hA : (A.card : ℝ) ≤ (f : ℝ) := by
      rw [hcard]
      exact_mod_cast (min_le_right n f)
    calc
      (A.card : ℝ) ≤ (f : ℝ) := hA
      _ ≤ m := Nat.floor_le hm0
  · by_cases hfn : f ≤ n
    · have hcf : A.card = f := by rw [hcard]; exact min_eq_right hfn
      have hlt : m < (f : ℝ) + 1 := by
        simpa [f] using (Nat.lt_floor_add_one m)
      have : m < (A.card : ℝ) + 1 := by
        rw [hcf]
        exact hlt
      exact le_of_lt this
    · have hnf : n < f := lt_of_not_ge hfn
      have hcn : A.card = n := by
        rw [hcard]
        exact min_eq_left (le_of_lt hnf)
      have : m ≤ (A.card : ℝ) + 1 := by
        rw [hcn]
        nlinarith
      exact this

-- ---------------------------------------------------------------------
-- (4) no-telescope counting estimates
-- ---------------------------------------------------------------------

/-- Pointwise no-telescope: for `x ∈ [aSerre,bSerre]` and `n ≥ 1`,
`countRoots n x / n ≤ cdf x` and `cdf x ≤ (countRoots n x + 1) / n`. -/
lemma no_telescope {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    (countRoots n x : ℝ) / (n : ℝ) ≤ cdf x ∧
      cdf x ≤ ((countRoots n x : ℝ) + 1) / (n : ℝ) := by
  let m : ℝ := (n : ℝ) * cdf x
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hcdf0 : 0 ≤ cdf x := cdf_nonneg x
  have hcdf1 : cdf x ≤ 1 := cdf_le_one x
  have hm0 : 0 ≤ m := by dsimp [m]; exact mul_nonneg (le_of_lt hn0) hcdf0
  have hmn : m ≤ (n : ℝ) := by
    dsimp [m]
    calc
      (n : ℝ) * cdf x ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hcdf1 (le_of_lt hn0)
      _ = (n : ℝ) := by ring
  have hcr : countRoots n x = ((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card := by
    simpa [m] using countRoots_eq hn hx
  rcases card_filter_le_real (n := n) (m := m) hn0 hm0 hmn with ⟨hA, hB⟩
  constructor
  · calc
      (countRoots n x : ℝ) / (n : ℝ) =
          (((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card : ℝ) / (n : ℝ) := by
            rw [hcr]
      _ ≤ cdf x := by
        rw [div_le_iff₀ hn0]
        calc
          (((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card : ℝ) ≤ m := hA
          _ = cdf x * (n : ℝ) := by dsimp [m]; ring
  · rw [le_div_iff₀ hn0]
    calc
      cdf x * (n : ℝ) = m := by dsimp [m]; ring
      _ ≤ (((Finset.Icc 1 n).filter fun i : ℕ => (i : ℝ) ≤ m).card : ℝ) + 1 := hB
      _ = (countRoots n x : ℝ) + 1 := by rw [hcr]

/-- Interval no-telescope: `∃ C > 0, ∀ n ≥ 2, ∀ u v` with
`aSerre ≤ u ≤ v ≤ bSerre`:
`| #{i ∈ [1..n] : u ≤ alpha n i ≤ v} / n − (cdf v − cdf u) | ≤ C / n`. -/
lemma exists_interval_no_telescope :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ u v : ℝ, aSerre ≤ u → u ≤ v → v ≤ bSerre →
      |(((Finset.Icc 1 n).filter fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v).card : ℝ) /
          (n : ℝ) - (cdf v - cdf u)| ≤ C / (n : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n hn u v hu huv hv
  have hn1 : 1 ≤ n := by omega
  set nR : ℝ := (n : ℝ)
  have hn0 : 0 < nR := by dsimp [nR]; exact_mod_cast (by omega : 0 < n)
  have huI : u ∈ Set.Icc aSerre bSerre := ⟨hu, le_trans huv hv⟩
  have hvI : v ∈ Set.Icc aSerre bSerre := ⟨le_trans hu huv, hv⟩
  set Sf : Finset ℕ := (Finset.Icc 1 n).filter fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v
  set Ff : Finset ℕ := (Finset.Icc 1 n).filter fun i : ℕ => u < alpha n i ∧ alpha n i ≤ v
  set cu : ℕ := countRoots n u
  set cv : ℕ := countRoots n v
  set rS : ℝ := (Sf.card : ℝ)
  set rF : ℝ := (Ff.card : ℝ)
  set rcu : ℝ := (cu : ℝ)
  set rcv : ℝ := (cv : ℝ)
  set Z : ℝ := cdf v - cdf u
  rcases between_countRoots hn1 huv with ⟨hcvN, hlowN, hhighN⟩
  have hcv : rcv = rcu + rF := by
    dsimp [rcv, rcu, rF, cu, cv]
    rw [hcvN]
    rw [Nat.cast_add]
  have hlowR : rF ≤ rS := by
    dsimp [rF, rS]
    exact (Nat.cast_le.mpr hlowN : (Ff.card : ℝ) ≤ (Sf.card : ℝ))
  have hhighR : rS ≤ rF + 1 := by
    dsimp [rS, rF]
    have h' : (Sf.card : ℝ) ≤ ((Ff.card + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hhighN
    simpa [Nat.cast_add, Nat.cast_one] using h'
  have htelu := no_telescope hn1 huI
  have htelv := no_telescope hn1 hvI
  have hcvle : rcv ≤ nR * cdf v := by
    have h := (div_le_iff₀ hn0).mp htelv.1
    dsimp [rcv]
    simpa [mul_comm] using h
  have hcv2 : nR * cdf v ≤ rcv + 1 := by
    have h := (le_div_iff₀ hn0).mp htelv.2
    dsimp [rcv]
    simpa [mul_comm] using h
  have hcule : rcu ≤ nR * cdf u := by
    have h := (div_le_iff₀ hn0).mp htelu.1
    dsimp [rcu]
    simpa [mul_comm] using h
  have hcu2 : nR * cdf u ≤ rcu + 1 := by
    have h := (le_div_iff₀ hn0).mp htelu.2
    dsimp [rcu]
    simpa [mul_comm] using h
  have hnum1 : rS - nR * Z ≤ 2 := by
    dsimp [Z]
    nlinarith [hhighR, hcv, hcvle, hcu2]
  have hnum2 : nR * Z - rS ≤ 2 := by
    dsimp [Z]
    nlinarith [hlowR, hcv, hcv2, hcule]
  have hnum : |rS - nR * Z| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith
    · exact hnum1
  have hfinal : |rS / nR - Z| ≤ 2 / nR := by
    have hident : |rS / nR - Z| = |rS - nR * Z| / nR := by
      have hdiv : rS / nR - Z = (rS - Z * nR) / nR := by
        field_simp [ne_of_gt hn0]
      rw [hdiv, abs_div]
      have hnabs : |nR| = nR := abs_of_pos hn0
      rw [hnabs]
      congr 1
      ring_nf
    rw [hident]
    have hmul := mul_le_mul_of_nonneg_right hnum (le_of_lt hn0)
    rw [div_le_div_iff₀ hn0 hn0]
    exact hmul
  simpa [nR, Sf, Ff, cu, cv, rS, rF, rcu, rcv, Z] using hfinal

-- ---------------------------------------------------------------------
-- (5) short intervals contain at most one quantile
-- ---------------------------------------------------------------------

/-- From the spacing bound: an interval of length smaller than the minimal
gap contains at most one of the `α_i`.  Concretely: with the spacing
constant `C` of `exists_spacing`, for `n ≥ 2` and any interval
`[x, x+s]` with `0 ≤ s` and `s < (C·n)^{-2}`, at most one root lies inside. -/
lemma at_most_one_root_in_short_interval :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x s : ℝ, 0 ≤ s → s < (C * (n : ℝ))⁻¹ ^ 2 →
      ((Finset.Icc 1 n).filter fun i : ℕ => x ≤ alpha n i ∧ alpha n i ≤ x + s).card ≤ 1 := by
  rcases exists_spacing with ⟨Csp, hC1sp, hCsp⟩
  refine ⟨Csp, hC1sp, ?_⟩
  intro n hn x s hs hshort
  have hn1 : 1 ≤ n := by omega
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hne
  exfalso
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hmemA : a ∈ Finset.Icc 1 n := (Finset.mem_filter.mp ha).1
    have hmemB : b ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hb).1
    have hri : 1 ≤ a ∧ a ≤ n := (Finset.mem_Icc).mp hmemA
    have hrj : 1 ≤ b ∧ b ≤ n := (Finset.mem_Icc).mp hmemB
    have hintA : x ≤ alpha n a ∧ alpha n a ≤ x + s := (Finset.mem_filter.mp ha).2
    have hintB : x ≤ alpha n b ∧ alpha n b ≤ x + s := (Finset.mem_filter.mp hb).2
    have hsp : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ alpha n (a + 1) - alpha n a :=
      hCsp n hn a hri.1 (by omega)
    have hmono2 : alpha n (a + 1) ≤ alpha n b := by
      by_cases hEq : a + 1 = b
      · rw [hEq]
      · have hlt' : a + 1 < b := by omega
        exact le_of_lt (alpha_strict_mono hn1 (by omega : 1 ≤ a + 1) hlt' hrj.2)
    have hsub : alpha n (a + 1) - alpha n a ≤ alpha n b - alpha n a :=
      sub_le_sub_right hmono2 (alpha n a)
    have hbig : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ alpha n b - alpha n a := le_trans hsp hsub
    have hsmall : alpha n b - alpha n a ≤ s := by linarith [hintA.1, hintB.2]
    have hbad : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ s := le_trans hbig hsmall
    exact (lt_irrefl ((Csp * (n : ℝ))⁻¹ ^ 2)) (lt_of_le_of_lt hbad hshort)
  · have hmemA : a ∈ Finset.Icc 1 n := (Finset.mem_filter.mp ha).1
    have hmemB : b ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hb).1
    have hri : 1 ≤ a ∧ a ≤ n := (Finset.mem_Icc).mp hmemA
    have hrj : 1 ≤ b ∧ b ≤ n := (Finset.mem_Icc).mp hmemB
    have hintA : x ≤ alpha n a ∧ alpha n a ≤ x + s := (Finset.mem_filter.mp ha).2
    have hintB : x ≤ alpha n b ∧ alpha n b ≤ x + s := (Finset.mem_filter.mp hb).2
    have hsp : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ alpha n (b + 1) - alpha n b :=
      hCsp n hn b hrj.1 (by omega)
    have hmono2 : alpha n (b + 1) ≤ alpha n a := by
      by_cases hEq : b + 1 = a
      · rw [hEq]
      · have hlt' : b + 1 < a := by omega
        exact le_of_lt (alpha_strict_mono hn1 (by omega : 1 ≤ b + 1) hlt' hri.2)
    have hsub : alpha n (b + 1) - alpha n b ≤ alpha n a - alpha n b :=
      sub_le_sub_right hmono2 (alpha n b)
    have hbig : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ alpha n a - alpha n b := le_trans hsp hsub
    have hsmall : alpha n a - alpha n b ≤ s := by linarith [hintB.1, hintA.2]
    have hbad : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ s := le_trans hbig hsmall
    exact (lt_irrefl ((Csp * (n : ℝ))⁻¹ ^ 2)) (lt_of_le_of_lt hbad hshort)

end Submission.Quantile
