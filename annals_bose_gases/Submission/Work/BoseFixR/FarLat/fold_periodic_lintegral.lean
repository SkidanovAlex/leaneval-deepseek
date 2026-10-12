import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarLat.cellProdLintegralSplit
import Submission.Work.BoseFixR.FarLat.ofRealMulAeEq
import Submission.Work.BoseFixR.FarLat.ofRealPeriodAeEqLatticeSum
import Submission.Work.BoseFixR.FarLat.tileLatticeLintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.fold_periodic_lintegral`

**The cell integral of the periodised pair density is the full-space integral.**  For `ℓ > 0`, an
integrable charge `W ≥ 0` a.e. whose lattice translates are pointwise summable, and a measurable
`ℓℤ³`-periodic `φ ≥ 0` a.e.,

`∫⁻_{cell ℓ × cell ℓ} ofReal (P x · P y · φ (x − y)) = ∫⁻_{ℝ³ × ℝ³} ofReal (W x · W y · φ (x − y))`

where `P = LatGreen.period W ℓ = Σ'_n W (· − ℓn)` is the `ℓ`-periodisation of `W`.

The mathematical content is the unfolding of the two periodisations: the translates `cell ℓ − ℓn`
tile `ℝ³`, and on each of them `φ (x − y)` is unchanged by the periodicity of `φ`, so both cell
integrals unfold to full-space integrals.  Formally the proof is organised as

* `ofRealPeriodAeEqLatticeSum` — pull `ENNReal.ofReal` through the (real) periodisation a.e.;
* `period_nonneg_ae` — the periodisation of an a.e. nonnegative charge is a.e. nonnegative, which
  is what allows `ofReal` of the *product* of the two periodisations to be split;
* `cellProdLintegralSplit` — Tonelli for the restricted product measure, `volume` on the product
  being `volume.prod volume`;
* `fold_innerValue` / `fold_outerValue` + `tileLatticeLintegral` — unfolding the two cell
  integrals along the lattice tiling, using only the periodicity of `φ`;
* `ofRealMulAeEq` — the reverse `ofReal`-split on the right-hand side.

The statement is counted in `Submission.Work.BoseFixR.FarLat` because it is consumed by the
cell-Parseval/far-lattice chapter of the `farLatParseval` route.
-/

noncomputable section

open scoped Real BigOperators Pointwise ENNReal
open MeasureTheory Set Filter

namespace Work.BoseFixR.FarLat

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## elementary helpers -/

lemma measurableSet_cellBox (ℓ : ℝ) : MeasurableSet (Work.BoseFixR.cell ℓ) := by
  rw [Work.BoseFixR.cell_eq_boxL]
  exact Work.BoseFixR.measurableSet_boxL ℓ

/-- Translation of an a.e. measurable `ℝ≥0∞`-valued function is a.e. measurable. -/
lemma aemeasurable_lat_translate {ℓ : ℝ} {f : E3 → ENNReal} (hf : AEMeasurable f volume)
    (n : Fin 3 → ℤ) : AEMeasurable (fun x : E3 => f (x - Work.BoseFixR.lat ℓ n)) volume := by
  have hmap : Measure.map (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume = volume := by
    have h := map_add_right_eq_self volume (-(Work.BoseFixR.lat ℓ n))
    simpa only [sub_eq_add_neg] using h
  have hf' : AEMeasurable (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume :=
    (measurable_id.sub_const _).aemeasurable
  have hg : AEMeasurable f (Measure.map (fun x : E3 => x - Work.BoseFixR.lat ℓ n) volume) := by
    rw [hmap]
    exact hf
  simpa only [Function.comp_def] using AEMeasurable.comp_aemeasurable (g := f) hg hf'

/-- The lattice sum of an a.e. measurable function is a.e. measurable. -/
lemma aemeasurable_latticeSum {ℓ : ℝ} {f : E3 → ENNReal} (hf : AEMeasurable f volume) :
    AEMeasurable (fun x : E3 => ∑' n : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ n)) volume := by
  refine AEMeasurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ))
    (f := fun (n : Fin 3 → ℤ) (x : E3) => f (x - Work.BoseFixR.lat ℓ n)) (fun n => ?_)
  exact aemeasurable_lat_translate hf n

/-- Shifting a periodic `Φ` by a lattice vector on the negative side. -/
lemma periodic_sub {ℓ : ℝ} {Φ : E3 → ENNReal}
    (hΦper : ∀ (z : E3) (n : Fin 3 → ℤ), Φ (z + Work.BoseFixR.lat ℓ n) = Φ z)
    (z : E3) (n : Fin 3 → ℤ) : Φ (z - Work.BoseFixR.lat ℓ n) = Φ z := by
  rw [show z - Work.BoseFixR.lat ℓ n = z + Work.BoseFixR.lat ℓ (-n) by
    rw [Work.BoseFixR.LatGreen.lat_neg]
    abel]
  exact hΦper z (-n)

/-- The periodisation of an a.e. nonnegative charge is a.e. nonnegative. -/
lemma period_nonneg_ae {ℓ : ℝ} {W : E3 → ℝ} (hWnn : 0 ≤ᵐ[volume] W) :
    0 ≤ᵐ[volume] fun x : E3 => Work.BoseFixR.LatGreen.period W ℓ x :=
  (ae_forall_nonneg_sub_lat (ℓ := ℓ) hWnn).mono fun x hx => by
    simp only [Work.BoseFixR.LatGreen.period]
    exact tsum_nonneg hx

/-! ## the two unfoldings -/

/-- **The inner cell integral unfolds**: the integral over one cell of the periodisation against
`Φ (x - ·)` equals the full-space integral of `f` against `Φ (x - ·)`. -/
theorem fold_innerValue {ℓ : ℝ} (hℓ : 0 < ℓ) {f Φ : E3 → ENNReal}
    (hf : AEMeasurable f volume) (hΦm : Measurable Φ)
    (hΦper : ∀ (z : E3) (n : Fin 3 → ℤ), Φ (z + Work.BoseFixR.lat ℓ n) = Φ z) (x : E3) :
    (∫⁻ y in Work.BoseFixR.cell ℓ,
        (∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n)) * Φ (x - y))
      = ∫⁻ v, f v * Φ (x - v) := by
  have hstep1 : (∫⁻ y in Work.BoseFixR.cell ℓ,
        (∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n)) * Φ (x - y))
      = ∑' n : Fin 3 → ℤ, ∫⁻ y in Work.BoseFixR.cell ℓ,
          f (y - Work.BoseFixR.lat ℓ n) * Φ (x - y) := by
    rw [show (fun y : E3 => (∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n)) * Φ (x - y))
        = fun y : E3 => ∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n) * Φ (x - y) from
      funext fun y => (ENNReal.tsum_mul_right).symm]
    exact lintegral_tsum (fun n => ((aemeasurable_lat_translate hf n).mul
      ((hΦm.comp (measurable_const_sub x)).aemeasurable)).mono_measure Measure.restrict_le_self)
  have hstep2 : (∑' n : Fin 3 → ℤ, ∫⁻ y in Work.BoseFixR.cell ℓ,
          f (y - Work.BoseFixR.lat ℓ n) * Φ (x - y))
      = ∑' n : Fin 3 → ℤ, ∫⁻ y in Work.BoseFixR.cell ℓ,
          f (y - Work.BoseFixR.lat ℓ n) * Φ (x - (y - Work.BoseFixR.lat ℓ n)) :=
    tsum_congr fun n => setLIntegral_congr_fun (measurableSet_cellBox ℓ) fun y _ => by
      show f (y - Work.BoseFixR.lat ℓ n) * Φ (x - y)
        = f (y - Work.BoseFixR.lat ℓ n) * Φ (x - (y - Work.BoseFixR.lat ℓ n))
      congr 1
      rw [show x - (y - Work.BoseFixR.lat ℓ n) = (x - y) + Work.BoseFixR.lat ℓ n by abel,
        hΦper (x - y) n]
  have hstep3 : (∑' n : Fin 3 → ℤ, ∫⁻ y in Work.BoseFixR.cell ℓ,
          f (y - Work.BoseFixR.lat ℓ n) * Φ (x - (y - Work.BoseFixR.lat ℓ n)))
      = ∫⁻ v, f v * Φ (x - v) :=
    (tileLatticeLintegral hℓ (fun v : E3 => f v * Φ (x - v))).symm
  exact hstep1.trans (hstep2.trans hstep3)

/-- **The outer cell integral unfolds**: the same, for the outer slot, using the periodicity of the
folded inner integral. -/
theorem fold_outerValue {ℓ : ℝ} (hℓ : 0 < ℓ) {f Φ : E3 → ENNReal}
    (hf : AEMeasurable f volume) (hΦm : Measurable Φ)
    (hΦper : ∀ (z : E3) (n : Fin 3 → ℤ), Φ (z + Work.BoseFixR.lat ℓ n) = Φ z) :
    (∫⁻ x in Work.BoseFixR.cell ℓ,
        (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
          * (∫⁻ v, f v * Φ (x - v)))
      = ∫⁻ u, f u * ∫⁻ v, f v * Φ (u - v) := by
  have hG : AEMeasurable (fun x : E3 => ∫⁻ v, f v * Φ (x - v)) volume := by
    have hjoint : AEMeasurable (fun p : E3 × E3 => f p.2 * Φ (p.1 - p.2)) (volume.prod volume) :=
      (hf.comp_snd).mul ((hΦm.comp (measurable_fst.sub measurable_snd)).aemeasurable)
    exact hjoint.lintegral_prod_right
  have hGper : ∀ (x : E3) (n : Fin 3 → ℤ),
      (∫⁻ v, f v * Φ ((x - Work.BoseFixR.lat ℓ n) - v)) = ∫⁻ v, f v * Φ (x - v) := by
    intro x n
    refine lintegral_congr fun v => ?_
    congr 1
    rw [show (x - Work.BoseFixR.lat ℓ n) - v = (x - v) - Work.BoseFixR.lat ℓ n by abel]
    exact periodic_sub hΦper (x - v) n
  have hstep1 : (∫⁻ x in Work.BoseFixR.cell ℓ,
        (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
          * (∫⁻ v, f v * Φ (x - v)))
      = ∑' m : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cell ℓ,
          f (x - Work.BoseFixR.lat ℓ m) * (∫⁻ v, f v * Φ (x - v)) := by
    rw [show (fun x : E3 => (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
          * (∫⁻ v, f v * Φ (x - v)))
        = fun x : E3 => ∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m)
            * (∫⁻ v, f v * Φ (x - v)) from funext fun x => (ENNReal.tsum_mul_right).symm]
    exact lintegral_tsum (fun m => ((aemeasurable_lat_translate hf m).mul hG).mono_measure
      Measure.restrict_le_self)
  have hstep2 : (∑' m : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cell ℓ,
          f (x - Work.BoseFixR.lat ℓ m) * (∫⁻ v, f v * Φ (x - v)))
      = ∑' m : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cell ℓ,
          f (x - Work.BoseFixR.lat ℓ m)
            * (∫⁻ v, f v * Φ ((x - Work.BoseFixR.lat ℓ m) - v)) :=
    tsum_congr fun m => setLIntegral_congr_fun (measurableSet_cellBox ℓ) fun x _ => by
      show f (x - Work.BoseFixR.lat ℓ m) * (∫⁻ v, f v * Φ (x - v))
        = f (x - Work.BoseFixR.lat ℓ m)
            * (∫⁻ v, f v * Φ ((x - Work.BoseFixR.lat ℓ m) - v))
      congr 1
      exact (hGper x m).symm
  have hstep3 : (∑' m : Fin 3 → ℤ, ∫⁻ x in Work.BoseFixR.cell ℓ,
          f (x - Work.BoseFixR.lat ℓ m)
            * (∫⁻ v, f v * Φ ((x - Work.BoseFixR.lat ℓ m) - v)))
      = ∫⁻ u, f u * (∫⁻ v, f v * Φ (u - v)) :=
    (tileLatticeLintegral hℓ (fun u : E3 => f u * (∫⁻ v, f v * Φ (u - v)))).symm
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## the core fold identity (at the level of the `ℝ≥0∞` lattice sums) -/

set_option maxHeartbeats 1000000 in
/-- The folding identity for the pair functional, with the periodisations written as their
`ℝ≥0∞` lattice sums. -/
theorem foldPairCore {ℓ : ℝ} (hℓ : 0 < ℓ) {f Φ : E3 → ENNReal}
    (hf : AEMeasurable f volume) (hΦm : Measurable Φ)
    (hΦper : ∀ (z : E3) (n : Fin 3 → ℤ), Φ (z + Work.BoseFixR.lat ℓ n) = Φ z) :
    (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        (∑' m : Fin 3 → ℤ, f (p.1 - Work.BoseFixR.lat ℓ m))
          * (∑' n : Fin 3 → ℤ, f (p.2 - Work.BoseFixR.lat ℓ n)) * Φ (p.1 - p.2))
      = ∫⁻ q : E3 × E3, f q.1 * f q.2 * Φ (q.1 - q.2) := by
  have hF : AEMeasurable (fun x : E3 => ∑' n : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ n)) volume :=
    aemeasurable_latticeSum hf
  have hsplit : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        (∑' m : Fin 3 → ℤ, f (p.1 - Work.BoseFixR.lat ℓ m))
          * (∑' n : Fin 3 → ℤ, f (p.2 - Work.BoseFixR.lat ℓ n)) * Φ (p.1 - p.2))
      = ∫⁻ x in Work.BoseFixR.cell ℓ,
          (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
            * (∫⁻ y in Work.BoseFixR.cell ℓ,
                (∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n)) * Φ (x - y)) :=
    cellProdLintegralSplit hℓ hF hΦm.aemeasurable
  have hinner : (∫⁻ x in Work.BoseFixR.cell ℓ,
          (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
            * (∫⁻ y in Work.BoseFixR.cell ℓ,
                (∑' n : Fin 3 → ℤ, f (y - Work.BoseFixR.lat ℓ n)) * Φ (x - y)))
      = ∫⁻ x in Work.BoseFixR.cell ℓ,
          (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
            * (∫⁻ v, f v * Φ (x - v)) :=
    lintegral_congr fun x => congrArg
      (fun z => (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m)) * z)
      (fold_innerValue hℓ hf hΦm hΦper x)
  have houter : (∫⁻ x in Work.BoseFixR.cell ℓ,
          (∑' m : Fin 3 → ℤ, f (x - Work.BoseFixR.lat ℓ m))
            * (∫⁻ v, f v * Φ (x - v)))
      = ∫⁻ u, f u * (∫⁻ v, f v * Φ (u - v)) :=
    fold_outerValue hℓ hf hΦm hΦper
  have hconst : (∫⁻ u : E3, f u * (∫⁻ v : E3, f v * Φ (u - v)))
      = ∫⁻ u : E3, ∫⁻ v : E3, f u * (f v * Φ (u - v)) := by
    refine lintegral_congr fun u => ?_
    exact (lintegral_const_mul'' (f u)
      (hf.mul ((hΦm.comp (measurable_const_sub u)).aemeasurable))).symm
  have hassoc : (∫⁻ u : E3, ∫⁻ v : E3, f u * (f v * Φ (u - v)))
      = ∫⁻ u : E3, ∫⁻ v : E3, f u * f v * Φ (u - v) :=
    lintegral_congr fun u => lintegral_congr fun v => (mul_assoc _ _ _).symm
  have hprod : (∫⁻ u : E3, ∫⁻ v : E3, f u * f v * Φ (u - v))
      = ∫⁻ q : E3 × E3, f q.1 * f q.2 * Φ (q.1 - q.2) := by
    rw [Measure.volume_eq_prod E3 E3]
    exact (lintegral_prod (fun q : E3 × E3 => f q.1 * f q.2 * Φ (q.1 - q.2))
      (((hf.comp_fst).mul (hf.comp_snd)).mul
        ((hΦm.comp (measurable_fst.sub measurable_snd)).aemeasurable))).symm
  exact hsplit.trans (hinner.trans (houter.trans (hconst.trans (hassoc.trans hprod))))

/-! ## the main theorem -/

-- imports used below: Submission.Work.BoseFixR.FarLatDefs, Submission.Work.BoseFixR.LatGreen.integrableOn_period
set_option maxHeartbeats 1000000 in
theorem fold_periodic_lintegral {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hφm : Measurable φ) (hφnn : 0 ≤ᵐ[MeasureTheory.volume] φ)
    (hφper : ∀ (z : EuclideanSpace ℝ (Fin 3)) (n : Fin 3 → ℤ),
      φ (z + Work.BoseFixR.lat ℓ n) = φ z) :
    (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2 * φ (p.1 - p.2)))
      = ∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          ENNReal.ofReal (W q.1 * W q.2 * φ (q.1 - q.2)) := by
  have hf_aem : AEMeasurable (fun u : E3 => ENNReal.ofReal (W u)) volume :=
    hW.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hΦm : Measurable (fun z : E3 => ENNReal.ofReal (φ z)) := hφm.ennreal_ofReal
  have hΦper : ∀ (z : E3) (n : Fin 3 → ℤ),
      ENNReal.ofReal (φ (z + Work.BoseFixR.lat ℓ n)) = ENNReal.ofReal (φ z) :=
    fun z n => by rw [hφper z n]
  -- Step A: rewrite the left-hand side integrand as a pair of `ℝ≥0∞` lattice sums
  have hstepA : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
        ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2 * φ (p.1 - p.2)))
      = ∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
          (∑' m : Fin 3 → ℤ, ENNReal.ofReal (W (p.1 - Work.BoseFixR.lat ℓ m)))
            * (∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (p.2 - Work.BoseFixR.lat ℓ n)))
            * ENNReal.ofReal (φ (p.1 - p.2)) := by
    have hAF : (fun x : E3 => ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ x))
        =ᵐ[volume] fun x : E3 =>
          ∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (x - Work.BoseFixR.lat ℓ n)) :=
      ofRealPeriodAeEqLatticeSum hWnn hper
    have hpos : 0 ≤ᵐ[volume] fun x : E3 => Work.BoseFixR.LatGreen.period W ℓ x :=
      period_nonneg_ae hWnn
    have hpt : (fun p : E3 × E3 => ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1
          * Work.BoseFixR.LatGreen.period W ℓ p.2 * φ (p.1 - p.2)))
        =ᵐ[(volume.prod volume).restrict (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)]
        fun p : E3 × E3 =>
          (∑' m : Fin 3 → ℤ, ENNReal.ofReal (W (p.1 - Work.BoseFixR.lat ℓ m)))
            * (∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (p.2 - Work.BoseFixR.lat ℓ n)))
            * ENNReal.ofReal (φ (p.1 - p.2)) := by
      have h1 : ∀ᵐ p : E3 × E3 ∂(volume.prod volume),
          ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.1)
            = ∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (p.1 - Work.BoseFixR.lat ℓ n)) :=
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hAF
      have h2 : ∀ᵐ p : E3 × E3 ∂(volume.prod volume),
          ENNReal.ofReal (Work.BoseFixR.LatGreen.period W ℓ p.2)
            = ∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (p.2 - Work.BoseFixR.lat ℓ n)) :=
        (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hAF
      have h3 : ∀ᵐ p : E3 × E3 ∂(volume.prod volume), 0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.1 :=
        (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae hpos
      have h4 : ∀ᵐ p : E3 × E3 ∂(volume.prod volume), 0 ≤ Work.BoseFixR.LatGreen.period W ℓ p.2 :=
        (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae hpos
      filter_upwards [(((h1.and h2).and h3).and h4).filter_mono
        (ae_mono Measure.restrict_le_self)] with p hp
      obtain ⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩ := hp
      rw [ENNReal.ofReal_mul (mul_nonneg hp3 hp4), ENNReal.ofReal_mul hp3, hp1, hp2]
    rw [Measure.volume_eq_prod E3 E3]
    exact lintegral_congr_ae hpt
  -- Step B: the core folding identity
  have hstepB : (∫⁻ p in (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ),
          (∑' m : Fin 3 → ℤ, ENNReal.ofReal (W (p.1 - Work.BoseFixR.lat ℓ m)))
            * (∑' n : Fin 3 → ℤ, ENNReal.ofReal (W (p.2 - Work.BoseFixR.lat ℓ n)))
            * ENNReal.ofReal (φ (p.1 - p.2)))
      = ∫⁻ q : E3 × E3,
          ENNReal.ofReal (W q.1) * ENNReal.ofReal (W q.2) * ENNReal.ofReal (φ (q.1 - q.2)) :=
    foldPairCore hℓ hf_aem hΦm hΦper
  -- Step C: rewrite the right-hand side integrand
  have hstepC : (∫⁻ q : E3 × E3,
          ENNReal.ofReal (W q.1) * ENNReal.ofReal (W q.2) * ENNReal.ofReal (φ (q.1 - q.2)))
      = ∫⁻ q : E3 × E3,
          ENNReal.ofReal (W q.1 * W q.2 * φ (q.1 - q.2)) := by
    rw [Measure.volume_eq_prod E3 E3]
    exact lintegral_congr_ae (ofRealMulAeEq hWnn)
  exact hstepA.trans (hstepB.trans hstepC)

end Work.BoseFixR.FarLat
