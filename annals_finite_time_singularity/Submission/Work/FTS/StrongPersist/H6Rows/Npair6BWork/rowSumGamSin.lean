import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowAux
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-! ## Two elementary helpers -/

/-- `CoefTh` is nonnegative (each summand is a supremum of absolute values). -/
theorem coefTh_nonneg (l : ℕ) (A : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.VocabO.CoefTh l A := by
  rw [Work.FTS.VocabO.CoefTh]
  refine Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact supAbsO_nonneg _
  · exact le_rfl

/-- **The integral engine.**  A pointwise domination of `|F|` by `M · HkIntegrand α 6 g` on the
open quadrant gives integrability of `F` against the product measure `PM` and the bound
`|∫ F| ≤ M · HkSq α 6 g`. -/
theorem abs_integral_le_pointwise {α M : ℝ} {F g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 6 g) (hM : 0 ≤ M)
    (haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2) PM)
    (hpt : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ M * Work.Spaces.HkIntegrand α 6 g z θ) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => F p.1 p.2) PM ∧
      |∫ p, F p.1 p.2 ∂PM| ≤ M * Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, hle⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm hpt
  obtain ⟨-, hle2⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.integrable_of_pointwise hg hmemg hM haesm.neg
      (fun z θ hz hθ hθ2 => by rw [abs_neg]; exact hpt z θ hz hθ hθ2)
  rw [MeasureTheory.integral_neg] at hle2
  exact ⟨hint, abs_le.mpr ⟨by linarith, hle⟩⟩

/-- **Leibniz summand, the `σ`-gain (mismatch) case: `a₁ = a ≥ 1`, `ρ = leafGam α`, `a + b₁ ≤ 2`.**

Route (all on the open quadrant, which is conull for `PM`).  `Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat`
gives `|mixed b₁ a A| ≤ 4 · Kf · sin(2θ)` whenever `Kf` bounds `|mixed b i (pth A)|` for `b+i ≤ 1`; by
`Npair6BWork.coefTh_pointwise` (from `CoefThMem 1 A` and `CoefTh 1 A ≤ K1`) one may take `Kf = K1`.
Hence `leafGam α · |mixed b₁ a A| · |D_z^{b-b₁+1} f| · |mixed b a f|
  ≤ (4K1) · (w²σ^{1-γ}) · |D_z^{b-b₁+1} f| · |mixed b a f|`
and `w²σ^{1-γ} ≤ √(canonW η · (D_z^{b-b₁+1} f)²) · √(canonW (gam α) · (mixed b a f)²)` because
`σ^{1-γ} ≤ σ^{-η/2}·σ^{-γ/2}` (`2 - γ + η ≥ 0`, true for `α ≤ 1`); both slots lie in
`HkIntegrand α 6 f` (`b-b₁+1 ≤ 6` because `a ≥ 1`; `1 ≤ a`, `a+b ≤ 6` for the mixed slot).
Conclude `≤ 4K1·HkSq α 6 f` by `cs_sqrt`/`rowSummand_core`. -/
theorem rowSumGamSin : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 K1 M : ℝ) (a b b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.VocabO.CoefThMem 1 A → Work.FTS.VocabO.CoefTh 1 A ≤ K1 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → 1 ≤ a → b₁ ≤ b → a + b₁ ≤ 2 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a A p.1 p.2
          * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a A p.1 p.2
            * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * K1 * Work.Spaces.HkSq α 6 f := by
  -- the flat `∂_θ`-price is converted into the `sin(2θ)`-gain
  obtain ⟨Csin, hCsin, hgain⟩ := Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
  refine ⟨Csin, hCsin, ?_⟩
  intro α hα A f K0 K4 K6 K1 M a b b₁ hcoef hctmem hctle hdat hab ha hb1 hab1
  obtain ⟨hα0, hα1⟩ := hα
  -- `K1` is nonnegative, because it dominates `CoefTh 1 A ≥ 0`
  have hK1 : 0 ≤ K1 := le_trans (coefTh_nonneg 1 A) hctle
  have hKX0 : 0 ≤ Csin * K1 := mul_nonneg hCsin.le hK1
  -- the index facts
  have hq0 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hqγ : Work.Spaces.gam α - 1 ≤ Work.Spaces.gam α := by linarith
  have hqη : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- the `sin(2θ)`-gain
  have hX : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a A z θ| ≤ Csin * K1 * Real.sin (2 * θ) :=
    hgain A K1 hK1 hcoef.sm (coefTh_pointwise hctmem hctle) a b₁ ha hab1
  -- a.e. strong measurability of the summand
  have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.TransportS.leafGam α p.1 p.2 * Work.Spaces.mixed b₁ a A p.1 p.2
        * Work.Spaces.DzIter (b - b₁ + 1) f p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2) PM :=
    (((aesm_leafW (α := α) (a := a) (Or.inr (Or.inr ⟨ha, rfl⟩))).mul
      (aesm_mixed hcoef.sm b₁ a)).mul
      (aesm_of_smoothOpen (hdat.sm.DzIter (b - b₁ + 1)))).mul
      (aesm_mixed hdat.sm b a)
  refine abs_integral_le_pointwise (M := Csin * K1)
    (F := fun z θ => Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b₁ a A z θ
        * Work.Spaces.DzIter (b - b₁ + 1) f z θ * Work.Spaces.mixed b a f z θ)
    hdat.sm hdat.h6 hKX0 haesm ?_
  intro z θ hz hθ hθ2
  have hs : 0 ≤ Real.sin (2 * θ) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
  -- the pair of `f`-slots, with the exponent `γ - 1` (which `σ` supplies)
  have hpair := Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := f)
    (q := Work.Spaces.gam α - 1) (j := b - b₁ + 1) (i := 0) (b := b) (a := a)
    hq0 hqγ (fun _ => hqη) (fun h => absurd h (by omega))
    (by omega : 0 + (b - b₁ + 1) ≤ 6) hab hz.le hθI
  simp only [Work.Spaces.mixed_zero_right] at hpair
  -- the `σ`-shift `leafGam α · sin(2θ) = canonW (gam α - 1)`
  have hshift : Work.FTS.TransportS.leafGam α z θ * Real.sin (2 * θ)
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
    have hsp : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hpow : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sin (2 * θ)
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) + 1) :=
            (Real.rpow_add hsp (-(Work.Spaces.gam α)) 1).symm
        _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by congr 1; ring
    rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.leafGam, mul_assoc, hpow]
  have hlnn : 0 ≤ Work.FTS.TransportS.leafGam α z θ :=
    Work.FTS.TransportS.leafGam_nonneg α hs
  have hYnn : 0 ≤ |Work.Spaces.DzIter (b - b₁ + 1) f z θ| := abs_nonneg _
  have hZnn : 0 ≤ |Work.Spaces.mixed b a f z θ| := abs_nonneg _
  calc |Work.FTS.TransportS.leafGam α z θ * Work.Spaces.mixed b₁ a A z θ
        * Work.Spaces.DzIter (b - b₁ + 1) f z θ * Work.Spaces.mixed b a f z θ|
      = Work.FTS.TransportS.leafGam α z θ * |Work.Spaces.mixed b₁ a A z θ|
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hlnn]
    _ ≤ Work.FTS.TransportS.leafGam α z θ * (Csin * K1 * Real.sin (2 * θ))
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hX z θ hz hθ hθ2) hlnn) hYnn) hZnn
    _ = Csin * K1 * (Work.FTS.TransportS.leafGam α z θ * Real.sin (2 * θ)
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        ring
    _ = Csin * K1 * (Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
          * |Work.Spaces.DzIter (b - b₁ + 1) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
        rw [hshift]
    _ ≤ Csin * K1 * Work.Spaces.HkIntegrand α 6 f z θ :=
        mul_le_mul_of_nonneg_left hpair hKX0

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
