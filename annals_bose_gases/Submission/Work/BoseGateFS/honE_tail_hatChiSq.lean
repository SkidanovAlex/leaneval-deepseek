import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.HonRowsDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.honE_tail_hatChiSq`

The second K2 χ-sum (`Q3Kernel.tail_hatChiSq`, the `tail_hatChiSq` row of
`HonestRows`) at the **honest** model:

    ∑_{s ∈ excited} |χ̂²_s| · (1 - f_L(s)) ≤ K₀ · (K_ℓK_L)^{-M},

from the corpus χ-decay (`Work.BoseK15.ChiReg`) together with the *truncated*
lattice-weight bound `htailinv` supplied by the caller — instead of the
`K15Input.sum_geom_tail` row, which has no honest instance (finding F1/F7).
This is the sibling of `honE_sum_hatChiSq`, and the argument is the one of
`Work.BoseK15.K15Input.tail_hatChiSq_le_of_one_le`:

* the χ-pin `honE_hatChiSq` writes `E.hatChiSq s = χ̂²(ℓ • kmom s)`, and the
  dual-lattice geometry `honE_onDualLattice` identifies `ℓ • kmom s =
  vec (lift s)`, so the modes label lattice points;
* `ChiReg` bounds each term by `Cchi·(1+‖vec n‖²)^{-decayOrder}`;
* the terms with `f_L s = 1` vanish (`f_L(s) = 1` for `‖kmom s‖ ≤ K_L√(μa)`,
  `honE_fL_eq_one`), and every remaining term labels a lattice point of norm
  `> K_ℓK_L` (the `ℓ K_L√(μa) = K_ℓK_L` identity `honE_ellKL`);
* the sum over the injective `lift`-image is dominated by `htailinv` at the
  radius `R = K_ℓK_L ≥ 1`, and `Cchi·Ctail ≤ K₀` (`hK`) finishes, using
  `intM = 48` (the concrete regularisation integer `Work.BoseBox.mValue` of
  `fsParams`, so that the exponent of `htailinv` *is* `intM`).
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

theorem honE_tail_hatChiSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (S : Work.BoseGateFS.HonSetup v h fc fu HM μ) {Cchi Csum Ctail K₀ : ℝ} (hCchi : 0 ≤ Cchi)
    (hCtail : 0 ≤ Ctail)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum)
    (htailinv : ∀ (R : ℝ) (S' : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S', R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹)
        ≤ Ctail / R ^ 48)
    (hKL : 1 ≤ (Work.BoseGateFS.honE v h fc fu HM μ).Kl
      * (Work.BoseGateFS.honE v h fc fu HM μ).KL)
    (hM : (Work.BoseGateFS.honE v h fc fu HM μ).intM + 3
      ≤ 2 * Work.BoseK15.decayOrder)
    (hK : Cchi * (Csum + Ctail) ≤ K₀) :
    ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
      |(Work.BoseGateFS.honE v h fc fu HM μ).hatChiSq s|
        * (1 - (Work.BoseGateFS.honE v h fc fu HM μ).fL s)
      ≤ K₀ * ((Work.BoseGateFS.honE v h fc fu HM μ).Kl
          * (Work.BoseGateFS.honE v h fc fu HM μ).KL)
        ^ (-((Work.BoseGateFS.honE v h fc fu HM μ).intM : ℝ)) := by
  classical
  -- (0) the honest cube is a dual lattice
  have hlat : Work.BoseK15.OnDualLattice (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N) :=
    honE_onDualLattice S
  have hℓpos : 0 < (honE v h fc fu HM μ).ell := by
    rw [honE_ell S]; exact Work.BoseBoxFock.ellH_pos v μ
  -- (1) the `χ̂²`-decay (`ChiReg`) in the reciprocal form used below
  have hdecay : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseK15.corpusBox.hatChiSq p|
        ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹ := by
    intro p
    have h1 := hchi.2 p
    have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder := by positivity
    rw [le_mul_inv_iff₀ hpos]
    exact h1
  -- (2) the lattice label of a mode: `ℓ • kmom s = vec (lift s)`
  have hell_kmom : ∀ s : Lab (HM μ).N,
      (honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom s
        = Work.BoseB4.vec (hlat.lift s) := by
    intro s
    rw [honE_ell S, honF_kmom, hlat.lift_spec s, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)), one_smul]
  -- the `honE`-data are those of the bundled `KzEnvHon` (definitional pins)
  have hellbridge : (KzEnvHon v h μ (honF v h fc fu HM μ) fc fu (HM μ).N).ell
      = (honE v h fc fu HM μ).ell := rfl
  have hbridge : ∀ s : Lab (HM μ).N,
      (honE v h fc fu HM μ).hatChiSq s
        = (KzEnvHon v h μ (honF v h fc fu HM μ) fc fu (HM μ).N).hatChiSq s :=
    fun s => rfl
  -- (3) the χ-pin at the lattice label
  have hpin : ∀ s : Lab (HM μ).N,
      (honE v h fc fu HM μ).hatChiSq s
        = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (hlat.lift s)) := by
    intro s
    rw [hbridge s, honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N s,
      hellbridge, hell_kmom s]
  have hchiSq_le : ∀ s : Lab (HM μ).N,
      |(honE v h fc fu HM μ).hatChiSq s|
        ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := by
    intro s
    rw [hpin s]
    exact hdecay _
  -- (4) `f_L ≥ 0` (`LowCut.anti` + `zero`)
  have hfLnn : ∀ s : Lab (HM μ).N, 0 ≤ (honE v h fc fu HM μ).fL s := by
    intro s
    rw [show (honE v h fc fu HM μ).fL s
        = fc.f (‖(honF v h fc fu HM μ).kmom s‖
            / ((honE v h fc fu HM μ).KL
                * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        from rfl]
    exact fc.nonneg _
  -- (5) the terms with `f_L s = 1` vanish
  have hred : (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s))
      = ∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
          (fun s => (honE v h fc fu HM μ).fL s ≠ 1),
        |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have h1 : (honE v h fc fu HM μ).fL s = 1 := by
      by_contra hne
      exact hns (Finset.mem_filter.mpr ⟨hs, hne⟩)
    simp [h1]
  -- (6) each remaining term is at most the pointwise `χ̂²`-decay
  have hterm : ∀ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
        (fun s => (honE v h fc fu HM μ).fL s ≠ 1),
      |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s)
        ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := by
    intro s _
    calc |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s)
        ≤ |(honE v h fc fu HM μ).hatChiSq s| * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hfLnn s]) (abs_nonneg _)
      _ = |(honE v h fc fu HM μ).hatChiSq s| := by ring
      _ ≤ _ := hchiSq_le s
  -- (7) the radius `R = K_ℓK_L` and the surviving lattice points
  set R : ℝ := (honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; exact hKL
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  set S' : Finset (Fin 3 → ℤ) :=
    ((Work.BoseB7.excited (Lab (HM μ).N)).filter
      (fun s => (honE v h fc fu HM μ).fL s ≠ 1)).image hlat.lift with hS'def
  have hnorm : ∀ n ∈ S', R ≤ ‖Work.BoseB4.vec n‖ := by
    intro n hn
    rw [hS'def] at hn
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
    have hfLs : (honE v h fc fu HM μ).fL s ≠ 1 := (Finset.mem_filter.mp hs).2
    have hgt : (honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)
        < ‖(honF v h fc fu HM μ).kmom s‖ := by
      by_contra hle
      exact hfLs (honE_fL_eq_one S (le_of_not_gt hle))
    have h3 : (honE v h fc fu HM μ).ell
        * ((honE v h fc fu HM μ).KL
            * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
        = R := by
      rw [hRdef, ← mul_assoc]
      exact honE_ellKL S
    rw [← hell_kmom s, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos, ← h3]
    exact le_of_lt (mul_lt_mul_of_pos_left hgt hℓpos)
  -- (8) the truncated lattice row
  have htail : (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2)
        ^ Work.BoseK15.decayOrder)⁻¹) ≤ Ctail / R ^ 48 :=
    htailinv R S' hR1 hnorm
  have hCsum0 : 0 ≤ Csum := by
    have hh := hsuminv (∅ : Finset (Fin 3 → ℤ))
    simpa using hh
  have hCchiCtail : Cchi * Ctail ≤ K₀ := by
    calc Cchi * Ctail ≤ Cchi * (Csum + Ctail) :=
          mul_le_mul_of_nonneg_left (by linarith) hCchi
      _ ≤ K₀ := hK
  -- the regularisation integer of the honest parameters is `48`
  have hm48 : (((honE v h fc fu HM μ).intM : ℕ) : ℝ) = (((48 : ℕ)) : ℝ) := by
    rw [show (honE v h fc fu HM μ).intM = 48 from rfl]
  calc ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s)
      = ∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
          (fun s => (honE v h fc fu HM μ).fL s ≠ 1),
          |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s) := hred
    _ ≤ ∑ s ∈ (Work.BoseB7.excited (Lab (HM μ).N)).filter
          (fun s => (honE v h fc fu HM μ).fL s ≠ 1),
          Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift s)‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := Finset.sum_le_sum hterm
    _ = Cchi * ∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := by
        rw [hS'def, Finset.mul_sum]
        exact (Finset.sum_image
          (f := fun n => Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2)
              ^ Work.BoseK15.decayOrder)⁻¹)
          (fun a _ b _ hab => hlat.lift_injective hab)).symm
    _ ≤ Cchi * (Ctail / R ^ 48) := mul_le_mul_of_nonneg_left htail hCchi
    _ = (Cchi * Ctail) / R ^ 48 := by ring
    _ ≤ K₀ / R ^ 48 := div_le_div_of_nonneg_right hCchiCtail (by positivity)
    _ = K₀ * ((honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL)
          ^ (-((honE v h fc fu HM μ).intM : ℝ)) := by
        rw [hm48, ← hRdef, div_eq_mul_inv, Real.rpow_neg (le_of_lt hRpos),
          Real.rpow_natCast R 48]

end Work.BoseGateFS
