import Mathlib
import Submission.Work.KMTAreas.A8.vNormK_defs
import Submission.Port.Aesm

set_option autoImplicit false

/-!
# `Work.KMTAreas.A8.limit_step`

This module proves the Fatou/liminf step of area A8 (`VarBilinInterp`):

if a family `u : ℕ → ℕ → ℤ → ℂ` of sequences on `ℤ` converges pointwise, coordinate by
coordinate, to a sequence `v : ℕ → ℤ → ℂ`, and if the `L^q`-norm (in the counting measure on
`ℤ`) of the `r`-variational norm of `u K (·) x` is bounded by a constant `C` uniformly in `K`,
then the same bound holds for `v`:

  `‖x ↦ V^r(v (·) x)‖_q ≤ C`.

The mathematical content is:

* **pointwise liminf bound** (`variationalNorm_le_liminf`): for every `x`,
  `V^r(v (·) x) ≤ liminf_K V^r(u K (·) x)`.  The variational norm is the sum of the supremum
  norm `⨆ n, ‖a n‖ₑ` and the variation part `varPart`, and each of the two is a supremum over
  (countably many, resp. arbitrary) "finite-dimensional" quantities: the supremum norm is a
  supremum of `‖·‖` of coordinates, and the variation part is a supremum over monotone chains
  of the `ℓ^r`-norm of the increments.  Each of those finitely-many-coordinate quantities is a
  continuous function of the coordinates, hence converges; taking the supremum gives the
  liminf bound.  The two summands are added with the lattice inequality
  `liminf u + liminf v ≤ liminf (u + v)` for `ℝ≥0∞`-valued sequences
  (`liminf_add_le_ennreal`), which follows from `ℝ≥0∞` being a complete lattice in which
  addition preserves suprema;
* **Fatou** (`lintegral_liminf_le`): from the pointwise bound and the commutation of
  `x ↦ x ^ q.toReal` with `liminf` (`ENNReal.orderIsoRpow`), the `q.toReal`-th power integral of
  `V^r(v)` is bounded by the liminf of those of `V^r(u K)`, hence by `C ^ q.toReal`; taking
  `q.toReal`-th roots gives the claim.

Everything is stated for the counting measure on `ℤ`, so all functions involved are measurable
without any regularity assumption.
-/

namespace Work.KMTAreas.A8

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology

/-- **`liminf` is superadditive for `ℝ≥0∞`-valued sequences.**
`liminf u + liminf v ≤ liminf (u + v)`; this is the addition instance of Fatou's inequality, and
it holds for `ℝ≥0∞` because addition there preserves suprema (`ENNReal.iSup_add`,
`ENNReal.add_iSup`) and `liminf u atTop = ⨆ n, ⨅ i ≥ n, u i`. -/
theorem liminf_add_le_ennreal {u v : ℕ → ℝ≥0∞} :
    Filter.liminf u atTop + Filter.liminf v atTop ≤ Filter.liminf (fun k => u k + v k) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat,
    Filter.liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le (f := fun n => ⨅ i, ⨅ (_ : i ≥ n), u i)
    (g := fun m => ⨅ i, ⨅ (_ : i ≥ m), v i) fun n m => ?_
  refine le_iSup_of_le (max n m) ?_
  refine le_iInf fun i0 => le_iInf fun h0 => ?_
  have hn : n ≤ i0 := le_trans (le_max_left n m) h0
  have hm : m ≤ i0 := le_trans (le_max_right n m) h0
  exact add_le_add (le_trans (iInf_le (fun i => ⨅ (_ : i ≥ n), u i) i0) (iInf_le _ hn))
    (le_trans (iInf_le (fun i => ⨅ (_ : i ≥ m), v i) i0) (iInf_le _ hm))

/-- **The supremum part of the variational norm is lower semicontinuous along pointwise
convergence.**  For every `x`, `⨆ n, ‖v n x‖ₑ ≤ liminf_K ⨆ n, ‖u K n x‖ₑ`. -/
theorem iSup_enorm_le_liminf {u : ℕ → ℕ → ℤ → ℂ} {v : ℕ → ℤ → ℂ}
    (hlim : ∀ (n : ℕ) (x : ℤ), Tendsto (fun K : ℕ => u K n x) atTop (nhds (v n x))) (x : ℤ) :
    (⨆ n, ‖v n x‖ₑ) ≤ Filter.liminf (fun K => ⨆ n, ‖u K n x‖ₑ) atTop := by
  have h1 : (⨆ n, ‖v n x‖ₑ) = ⨆ n, Filter.liminf (fun K => ‖u K n x‖ₑ) atTop := by
    congr 1 with n
    exact (Filter.Tendsto.liminf_eq
      ((continuous_enorm.tendsto (v n x)).comp (hlim n x))).symm
  rw [h1]
  exact Filter.iSup_liminf_le_liminf_iSup

/-- **The variation part of the variational norm is lower semicontinuous along pointwise
convergence.**  For every `x`, `varPart r (v · x) ≤ liminf_K varPart r (u K · x)`.

Indeed, for a fixed chain `(J, N)` the increment vector
`i ↦ u K (N (i+1)) x - u K (N i) x` is a continuous function of the `J + 1` coordinates
`u K (N 0) x, …, u K (N J) x`, and its `ℓ^r`-norm is computed by the `rpow`-sum formula
`ofReal_norm_toLp_eq_sum`; the sum of `rpow`s of the coordinate norms is a finite sum of
convergent sequences, and `x ↦ x ^ (1/r)` is continuous on `ℝ≥0∞`.  Taking the supremum over all
chains gives the claim. -/
theorem varPart_le_liminf {r : NNReal} (hr : 1 ≤ r) {u : ℕ → ℕ → ℤ → ℂ} {v : ℕ → ℤ → ℂ}
    (hlim : ∀ (n : ℕ) (x : ℤ), Tendsto (fun K : ℕ => u K n x) atTop (nhds (v n x))) (x : ℤ) :
    varPart r (fun n => v n x) ≤ Filter.liminf (fun K => varPart r (fun n => u K n x)) atTop := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  set F : ℕ → Fin J → ℂ := fun K i => u K (N (i + 1)) x - u K (N i) x
  set G : Fin J → ℂ := fun i => v (N (i + 1)) x - v (N i) x
  have hterm : ∀ i : Fin J,
      Tendsto (fun K => ‖F K i‖ₑ ^ (r : ℝ)) atTop (nhds (‖G i‖ₑ ^ (r : ℝ))) := by
    intro i
    have h1 : Tendsto (fun K => ‖F K i‖ₑ) atTop (nhds ‖G i‖ₑ) :=
      (continuous_enorm.tendsto (G i)).comp ((hlim (N (i + 1)) x).sub (hlim (N i) x))
    exact (ENNReal.continuous_rpow_const.tendsto _).comp h1
  have hsum : Tendsto (fun K => ∑ i : Fin J, ‖F K i‖ₑ ^ (r : ℝ)) atTop
      (nhds (∑ i : Fin J, ‖G i‖ₑ ^ (r : ℝ))) :=
    tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  have hone : Tendsto (fun K => (∑ i : Fin J, ‖F K i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))) atTop
      (nhds ((∑ i : Fin J, ‖G i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)))) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp hsum
  have key : (∑ i : Fin J, ‖G i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      = ENNReal.ofReal ‖WithLp.toLp r G‖ := (ofReal_norm_toLp_eq_sum hr G).symm
  rw [key] at hone
  rw [← Filter.Tendsto.liminf_eq hone]
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun K => ?_)
  have hb : ENNReal.ofReal ‖WithLp.toLp r (F K)‖ ≤ varPart r (fun n => u K n x) :=
    le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  rwa [ofReal_norm_toLp_eq_sum hr (F K)] at hb

/-- **The pointwise liminf bound for the variational norm.**  If `u K (·) x → v (·) x` for every
`x` (and every coordinate `n`), then `V^r(v (·) x) ≤ liminf_K V^r(u K (·) x)` for every `x`. -/
theorem variationalNorm_le_liminf {r : NNReal} (hr : 1 ≤ r) {u : ℕ → ℕ → ℤ → ℂ}
    {v : ℕ → ℤ → ℂ}
    (hlim : ∀ (n : ℕ) (x : ℤ), Tendsto (fun K : ℕ => u K n x) atTop (nhds (v n x))) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => v n x) ≤
      Filter.liminf (fun K => PointwiseErgodicTheorems.variationalNorm r
        (fun n => u K n x)) atTop := by
  have hA := iSup_enorm_le_liminf hlim x
  have hB := varPart_le_liminf hr hlim x
  have h2 : ∀ K, PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)
      = (⨆ n, ‖u K n x‖ₑ) + varPart r (fun n => u K n x) :=
    fun K => variationalNorm_eq_add r _
  calc PointwiseErgodicTheorems.variationalNorm r (fun n => v n x)
      = (⨆ n, ‖v n x‖ₑ) + varPart r (fun n => v n x) := variationalNorm_eq_add r _
    _ ≤ Filter.liminf (fun K => ⨆ n, ‖u K n x‖ₑ) atTop
          + Filter.liminf (fun K => varPart r (fun n => u K n x)) atTop := add_le_add hA hB
    _ ≤ Filter.liminf (fun K => (⨆ n, ‖u K n x‖ₑ) + varPart r (fun n => u K n x)) atTop :=
        liminf_add_le_ennreal
    _ = Filter.liminf (fun K => PointwiseErgodicTheorems.variationalNorm r
          (fun n => u K n x)) atTop := by
        simp only [h2]

/-- **The Fatou step of area A8.**  If the `L^q`-norms of the `r`-variational norms of the
sequences `u K (·) x` are bounded by `C` uniformly in `K`, and `u K n x → v n x` for every `n`
and `x`, then the `L^q`-norm of the `r`-variational norm of `v (·) x` is bounded by `C` as well
(`1 ≤ q < ∞`). -/
theorem limit_step {r : NNReal} (hr : 1 ≤ r) {q : ENNReal} (hq : 1 ≤ q) (hqfin : q < ⊤)
    {u : ℕ → ℕ → ℤ → ℂ} {v : ℕ → ℤ → ℂ} {C : ENNReal}
    (hK : ∀ K : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u K n x)) q MeasureTheory.Measure.count ≤ C)
    (hlim : ∀ (n : ℕ) (x : ℤ), Filter.Tendsto (fun K : ℕ => u K n x) Filter.atTop (nhds (v n x))) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x)) q MeasureTheory.Measure.count ≤ C := by
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n => v n x) ≤
      Filter.liminf (fun K => PointwiseErgodicTheorems.variationalNorm r
        (fun n => u K n x)) atTop := fun x => variationalNorm_le_liminf hr hlim x
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hqt : q ≠ ⊤ := ne_of_lt hqfin
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  -- `x ↦ x ^ q.toReal` commutes with `liminf`
  have hpowlim : ∀ x : ℤ,
      (Filter.liminf (fun K => PointwiseErgodicTheorems.variationalNorm r
        (fun n => u K n x)) atTop) ^ q.toReal
      = Filter.liminf (fun K => (PointwiseErgodicTheorems.variationalNorm r
        (fun n => u K n x)) ^ q.toReal) atTop := by
    intro x
    exact OrderIso.liminf_apply (ENNReal.orderIsoRpow q.toReal hqpos)
      (f := Filter.atTop)
      (u := fun K => PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x))
  -- the `q.toReal`-th power integral of `V^r(u K)` is bounded by `C ^ q.toReal`
  have hAK : ∀ K : ℕ, ∫⁻ x : ℤ,
      (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal
        ∂Measure.count ≤ C ^ q.toReal := by
    intro K
    have h1 : (∫⁻ x : ℤ,
        (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal
          ∂Measure.count) ^ (1 / q.toReal) ≤ C := by
      have hh := hK K
      rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt] at hh
    calc ∫⁻ x : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal
          ∂Measure.count
        = ((∫⁻ x : ℤ,
            (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal
              ∂Measure.count) ^ (1 / q.toReal)) ^ q.toReal := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hqpos.ne', ENNReal.rpow_one]
      _ ≤ C ^ q.toReal := ENNReal.rpow_le_rpow h1 hqpos.le
  -- Fatou
  have hA : ∫⁻ x : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n => v n x)) ^ q.toReal
      ∂Measure.count ≤ C ^ q.toReal := by
    calc ∫⁻ x : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n => v n x)) ^ q.toReal
            ∂Measure.count
        ≤ ∫⁻ x : ℤ, Filter.liminf (fun K =>
            (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal)
              atTop ∂Measure.count :=
          lintegral_mono (fun x => by
            rw [← hpowlim x]
            exact ENNReal.rpow_le_rpow (hpt x) hqpos.le)
      _ ≤ Filter.liminf (fun K => ∫⁻ x : ℤ,
            (PointwiseErgodicTheorems.variationalNorm r (fun n => u K n x)) ^ q.toReal
              ∂Measure.count) atTop :=
          lintegral_liminf_le (fun K => measurable_of_countable _)
      _ ≤ C ^ q.toReal := by
          refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
          obtain ⟨K, hbK⟩ := hb.exists
          exact le_trans hbK (hAK K)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hq0 hqt]
  calc ((∫⁻ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n => v n x)‖ₑ ^ q.toReal
          ∂Measure.count) ^ (1 / q.toReal))
      ≤ (C ^ q.toReal) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow hA (le_of_lt (one_div_pos.mpr hqpos))
    _ = C := by rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hqpos.ne', ENNReal.rpow_one]

end Work.KMTAreas.A8
