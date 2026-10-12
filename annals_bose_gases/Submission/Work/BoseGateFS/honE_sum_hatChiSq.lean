import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.HonRowsDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.honE_sum_hatChiSq`

The first K2 χ-sum (`Q3Kernel.sum_hatChiSq`, the `sum_hatChiSq` row of
`HonestRows`) at the **honest** model:

    ∑_{s ∈ excited} |χ̂²_s| ≤ K₀,

from the corpus χ-decay (`Work.BoseK15.ChiReg`) together with the *uniform*
lattice-weight bound `hsuminv` supplied by the caller — instead of the
`K15Input.sum_geom` row, which has no honest instance (finding F1/F7).

The argument is the one of `Work.BoseK15.K15Input.sum_hatChiSq_le_Csum`:

* the χ-pin `honE_hatChiSq` writes `E.hatChiSq s = χ̂²(ℓ • kmom s)`;
* the dual-lattice geometry `honE_onDualLattice` identifies `ℓ • kmom s =
  vec (lift s)`, so the modes label lattice points;
* `ChiReg` bounds each term by `Cchi·(1+‖vec n‖²)^{-decayOrder}`;
* the sum over the injective `lift`-image is dominated by `hsuminv`, and
  `Cchi·Csum ≤ K₀` finishes.
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

theorem honE_sum_hatChiSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (S : Work.BoseGateFS.HonSetup v h fc fu HM μ) {Cchi Csum K₀ : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum)
    (hK : Cchi * Csum ≤ K₀) :
    ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
      |(Work.BoseGateFS.honE v h fc fu HM μ).hatChiSq s| ≤ K₀ := by
  classical
  have hlat : Work.BoseK15.OnDualLattice (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N) :=
    honE_onDualLattice S
  -- the `χ̂²`-decay (`ChiReg`), in the reciprocal form used below
  have hdecay : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseK15.corpusBox.hatChiSq p|
        ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹ := by
    intro p
    have h1 := hchi.2 p
    have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder := by positivity
    rw [le_mul_inv_iff₀ hpos]
    exact h1
  -- the lattice label of a mode: `ℓ • kmom s = vec (lift s)`
  have hell_kmom : ∀ s : Work.BoseBoxFock.Lab (HM μ).N,
      (honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom s
        = Work.BoseB4.vec (hlat.lift s) := by
    intro s
    rw [honE_ell S, honF_kmom, hlat.lift_spec s, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)), one_smul]
  -- the χ-pin at the lattice label
  have hpin : ∀ s : Work.BoseBoxFock.Lab (HM μ).N,
      (honE v h fc fu HM μ).hatChiSq s
        = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (hlat.lift s)) := by
    intro s
    have h1 : (honE v h fc fu HM μ).hatChiSq s
        = Work.BoseK15.corpusBox.hatChiSq
            ((honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom s) :=
      honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N s
    rw [h1, hell_kmom s]
  -- the lattice-weight sum over the excited modes
  have hsum_le : (∑ s ∈ excited (Work.BoseBoxFock.Lab (HM μ).N),
      (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹)
      ≤ Csum := by
    have h := hsuminv ((excited (Work.BoseBoxFock.Lab (HM μ).N)).image hlat.lift)
    rwa [Finset.sum_image (fun a _ b _ hab => hlat.lift_injective hab)] at h
  calc ∑ s ∈ excited (Work.BoseBoxFock.Lab (HM μ).N),
        |(honE v h fc fu HM μ).hatChiSq s|
      ≤ ∑ s ∈ excited (Work.BoseBoxFock.Lab (HM μ).N),
          Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ :=
        Finset.sum_le_sum (fun s _ => by rw [hpin s]; exact hdecay _)
    _ = Cchi * ∑ s ∈ excited (Work.BoseBoxFock.Lab (HM μ).N),
          (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi * Csum := mul_le_mul_of_nonneg_left hsum_le hCchi
    _ ≤ K₀ := hK

end Work.BoseGateFS
