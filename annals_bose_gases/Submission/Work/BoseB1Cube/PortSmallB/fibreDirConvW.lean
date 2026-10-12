import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.PortSmallB.WinW
import Submission.Work.BoseFixB1B.B1Bfix2.fibreDirI_diff_tendstoB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PortSmallB.fibreDirConvW`

The port of `Work.BoseFixB1B.B1Bfix.fibreDirI_diff_tendstoB` to the **cube** window
`Submission.BoseGases.chiSmallB M L d u`: the summed cube-windowed fibre Dirichlet energy of the
difference state `slotDiffState L d u (γ δ) ψ` is `O(δ)`, hence tends to `0` as `δ → 0⁺`.

The whole analytic content of the ball-window theorem is reused through the `chiSmallB` window
layer of `Submission.Work.BoseB1Cube.Winchk` and of `Submission.Work.BoseB1Cube.PortSmallB.WinW`:

* `Winchk.chiSmallB_abs_le_boxMargin` — the linear vanishing of the window in the box margin;
* `PortSmallB.exists_bound_fderiv_chiSmallB_coord` — the global bound on the window derivative;
* `PortSmallB.fibre_deriv_sum_sq_leW` — the pointwise bound on the derivative of the windowed slot
  fibre (`27 Λ²` with `Λ = max (kappaS M · Cψ) (max (C1·K·Cb) (2·Cχ·Cb))`);
* `PortSmallB.{setIntegral_le_of_le_aeW, integrableOn_acube_of_boundW, integrableOn_abox_of_boundW}`
  — the measure-theoretic helpers.

-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube.PortSmallB

open Submission.BoseGases
open Work.BoseFixB1B
open Work.BoseFixB1B.B1Bfix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The position-space convergence of the fibre Dirichlet energy at the cube window** — the
`chiSmallB`-twin of the PROVED `Work.BoseFixB1B.B1Bfix.fibreDirI_diff_tendstoB`
(`Submission/Work/BoseFixB1B/B1Bfix2/fibreDirI_diff_tendstoB.lean`, §8, lines 721–1213): the summed
cube-windowed fibre Dirichlet energy of the difference state `slotDiffState L d u (γ δ) ψ` is `O(δ)`
and tends to `0` as `δ → 0⁺`.  This is one half of the two `Prop`s requested by the holder of
`Submission/Work/BoseB1Cube/PortSmallB/fibreDirDiffSmallB.lean`.

PORT RECIPE (mechanical): copy that theorem's proof into the new file and
* replace `chiB L d u ↦ chiSmallB M L d u` and add the parameter `{M : ℕ} (hM : 4 ≤ M)`;
* replace the linear-margin input `chiB_abs_le_boxMargin hL hd u` by
  `Work.BoseB1Cube.Winchk.chiSmallB_abs_le_boxMargin M (by omega) hL hd u`;
* replace the derivative input `exists_bound_fderiv_chiB` by
  `Work.BoseB1Cube.PortSmallB.exists_bound_fderiv_chiSmallB_coord hM hL hd u`;
* replace the pointwise bound `fibre_deriv_sum_sq_le` by
  `Work.BoseB1Cube.PortSmallB.fibre_deriv_sum_sq_leW` (identical statement at the cube window, with
  the parameter `hM : 4 ≤ M`); its constant `chiSup ^ 2 * Cψ` becomes `kappaS M * Cψ`, so the
  theorem's `A0` is `27 * (max (Work.BoseB1Cube.Winchk.kappaS M * Cψ) (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2`;
* replace the ball-window `private` helpers by their public cube-window copies
  `Work.BoseB1Cube.PortSmallB.{setIntegral_le_of_le_aeW, integrableOn_acube_of_boundW, integrableOn_abox_of_boundW}`;
* note `Work.BoseFixB1B.fibreDirI` and `Work.BoseFixB1B.cutFibreDir` are definitionally equal, so
  the conclusion is exactly the target `Prop`.  -/
theorem fibreDirConvW {n : ℕ} {L d : ℝ} (hL : 0 < L) (hd : 0 < d) {M : ℕ} (hM : 4 ≤ M)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : Submission.BoseGases.X (n+1) → ℝ} {K Cb : ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox (n+1) L, |ψ x| ≤ Cb) :
    Work.BoseB1Cube.PortSmallB.FibreDirDiffConvS L d M u ψ K Cb γ := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := Work.BoseB1Cube.Winchk.chiSmallB_abs_le_boxMargin M (by omega) hL hd u
  obtain ⟨Cχ, hCχ0, hCχ⟩ := Work.BoseB1Cube.PortSmallB.exists_bound_fderiv_chiSmallB_coord hM hL hd u
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_fderiv_psi (L := L) hψ
  set Ca : ℝ := 12 * L ^ 2 * (1 + d ^ 2) with hCadef
  have hCa0 : 0 ≤ Ca := by rw [hCadef]; positivity
  have hCa : ∀ δ : ℝ, 0 < δ →
      (∫ y in acube L, collarInd L d u δ y) ≤ Ca * δ := by
    intro δ hδ
    rw [hCadef]
    exact integral_collarInd_acube_le hL hd u hδ
  choose Cj hCj0 hCj using fun j : Fin n => integral_collarInd_abox (L := L) (d := d) hL hd u n j
  have hnormk : ∀ k : Fin 3, ‖Submission.BoseGases.kcStdBasis k‖ = 1 := by
    intro k
    simp [Submission.BoseGases.kcStdBasis]
  have hCχcoord : ∀ y : E3, ∀ k : Fin 3,
      |fderiv ℝ (Submission.BoseGases.chiSmallB M L d u) y (Submission.BoseGases.kcStdBasis k)| ≤ Cχ :=
    hCχ
  set Cab : ℝ := ∑ j : Fin n, Cj j with hCab
  have hCab0 : 0 ≤ Cab := by rw [hCab]; exact Finset.sum_nonneg (fun j _ => hCj0 j)
  set Cm : ℝ := max 1 (Work.SmallBoxSliding.boxMass L d u)⁻¹ with hCm
  have hCm0 : 0 ≤ Cm := by rw [hCm]; exact le_trans zero_le_one (le_max_left _ _)
  set A0 : ℝ := 27 * (max (Work.BoseB1Cube.Winchk.kappaS M * Cψ)
    (max (C1 * K * Cb) (2 * Cχ * Cb))) ^ 2 with hA0
  have hA00 : 0 ≤ A0 := by rw [hA0]; positivity
  have hvolc : (volume : Measure E3).real (acube L) = L ^ 3 := volume_real_acube hL.le
  have hvolb : (volume : Measure (Submission.BoseGases.X n)).real (Submission.BoseGases.abox n L)
      = (L ^ 3) ^ n := volume_real_abox n hL.le
  have hboxmass0 : 0 ≤ Work.SmallBoxSliding.boxMass L d u := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
    positivity
  have hVac : ∀ δ : ℝ, (∫ z in acube L, collarInd L d u δ z) = ∫ z : E3, collarInd L d u δ z := by
    intro δ
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun z : E3 => collarInd L d u δ z) (s := acube L)
      (fun z hz => by
        rw [collarInd_eq_indicator]
        exact Set.indicator_of_notMem
          (fun hmem => hz (Work.SmallBoxSliding.dlBox_subset_acube L d u hmem.1)) _)
  have hVle : ∀ δ : ℝ, 0 < δ → (∫ z : E3, collarInd L d u δ z) ≤ Ca * δ := by
    intro δ hδ
    have h := hCa δ hδ
    rwa [hVac δ] at h
  have hSint : ∀ δ : ℝ, 0 < δ →
      (∫ r in Submission.BoseGases.abox n L, ∑ j : Fin n, collarInd L d u δ (r j))
        ≤ Cab * δ := by
    intro δ hδ
    have hsum_eq : (∫ r in Submission.BoseGases.abox n L, ∑ j : Fin n, collarInd L d u δ (r j))
        = ∑ j : Fin n, ∫ r in Submission.BoseGases.abox n L, collarInd L d u δ (r j) := by
      rw [MeasureTheory.integral_finset_sum]
      intro j _
      exact Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) hL
        ((Work.BoseFixB1B.measurable_collarInd L d u δ).comp
          (measurable_pi_apply j)).aestronglyMeasurable
        (by
          rw [ae_restrict_iff' (abox_measurable n L)]
          refine ae_of_all _ (fun r _ => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (collarInd_nonneg L d u δ (r j))]
          exact collarInd_le_one L d u δ (r j))
    rw [hsum_eq]
    calc ∑ j : Fin n, ∫ r in Submission.BoseGases.abox n L, collarInd L d u δ (r j)
        ≤ ∑ j : Fin n, Cj j * δ := Finset.sum_le_sum (fun j _ => hCj j δ hδ)
      _ = Cab * δ := by rw [hCab, Finset.sum_mul]
  -- the per-slot estimate
  have hslot : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → ∀ i : Fin (n+1),
      fibreDirI L (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i (slotDiffState L d u (γ δ) ψ)
      ≤ (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
          + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ := by
    intro δ hδ hδ1 i
    set V : ℝ := ∫ z : E3, collarInd L d u δ z with hV
    set b : ℝ := V / Work.SmallBoxSliding.boxMass L d u with hb
    have hV0 : 0 ≤ V := by
      rw [hV]; exact integral_nonneg (fun z => collarInd_nonneg L d u δ z)
    have hb0 : 0 ≤ b := by rw [hb]; exact div_nonneg hV0 hboxmass0
    have hVle' : V ≤ Ca * δ := by rw [hV]; exact hVle δ hδ
    have hble : b ≤ Ca * Cm * δ := by
      rw [hb, div_eq_mul_inv]
      calc V * (Work.SmallBoxSliding.boxMass L d u)⁻¹
          ≤ (Ca * δ) * (Work.SmallBoxSliding.boxMass L d u)⁻¹ :=
            mul_le_mul_of_nonneg_right hVle' (inv_nonneg.mpr hboxmass0)
        _ ≤ (Ca * δ) * Cm :=
            mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) _) (mul_nonneg hCa0 hδ.le)
        _ = Ca * Cm * δ := by ring
    have hS0' : ∀ r : Submission.BoseGases.X n, 0 ≤ ∑ j : Fin n, collarInd L d u δ (r j) :=
      fun r => Finset.sum_nonneg (fun j _ => collarInd_nonneg L d u δ (r j))
    have hSle : ∀ r : Submission.BoseGases.X n,
        (∑ j : Fin n, collarInd L d u δ (r j)) ≤ (n : ℝ) := by
      intro r
      calc ∑ j : Fin n, collarInd L d u δ (r j) ≤ ∑ _j : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => collarInd_le_one L d u δ (r j))
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hSsq : ∀ r : Submission.BoseGases.X n,
        (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          ≤ (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := by
      intro r
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hSle r, hS0' r, hn]
    -- the a.e. bound on the fibre derivative, integrated over the slot variable
    have hpp : ∀ r ∈ Submission.BoseGases.abox n L,
        (∫ y in acube L, ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
            (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
        ≤ ∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
            + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := by
      intro r hr
      have hc : Measurable (fun y : E3 => collarInd L d u δ y) :=
        Work.BoseFixB1B.measurable_collarInd L d u δ
      have hsum : Measurable (fun y : E3 => (collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) :=
        ((hc.pow_const 2).add measurable_const).add measurable_const
      have hprod : Measurable (fun y : E3 => A0 * 3 * ((collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2)) :=
        (measurable_const : Measurable (fun _ : E3 => A0 * 3)).mul hsum
      have hβint : IntegrableOn (fun y : E3 => A0 * 3 * ((collarInd L d u δ y) ^ 2
          + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2)) (acube L) volume :=
        Work.BoseB1Cube.PortSmallB.integrableOn_acube_of_boundW (C := A0 * 3 * (1 + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
          hL hprod.aestronglyMeasurable
          (by
            rw [ae_restrict_iff' (acube_measurable L)]
            refine ae_of_all _ (fun y _ => ?_)
            rw [Real.norm_of_nonneg (by positivity)]
            refine mul_le_mul_of_nonneg_left (a := A0 * 3) ?_ (mul_nonneg hA00 (by norm_num))
            have h1 : (collarInd L d u δ y) ^ 2 ≤ 1 := by
              have h2 := collarInd_le_one L d u δ y
              have h3 := collarInd_nonneg L d u δ y
              nlinarith
            linarith [h1, sq_nonneg (∑ j : Fin n, collarInd L d u δ (r j)), sq_nonneg b])
      refine Work.BoseB1Cube.PortSmallB.setIntegral_le_of_le_aeW (acube_measurable L) hβint ?_ ?_
      · intro y _
        exact mul_nonneg (by positivity)
          (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
      · have hae : ∀ᵐ y ∂(volume : Measure E3), boxMargin L d u y ≠ 0 := by
          rw [MeasureTheory.ae_iff]
          simpa only [not_ne_iff] using Work.BoseFixB1B.cutFibreMass_boxMargin_eq_zero_null L d u
        rw [MeasureTheory.ae_restrict_iff' (acube_measurable L)]
        filter_upwards [hae] with y hym hyac
        have hder := Work.BoseB1Cube.PortSmallB.fibre_deriv_sum_sq_leW (M := M) (L := L) (d := d) hL hd u hM (hcut := hcut) hδ
          (ψ := ψ) hψ hCb hψb hC10 hC1 hCχcoord hCψ0 hCψ i hyac hr hym
        rw [← hA0, ← hV, ← hb] at hder
        refine hder.trans ?_
        have hmid : (collarInd L d u δ y + ∑ j : Fin n, collarInd L d u δ (r j) + b) ^ 2
            ≤ 3 * ((collarInd L d u δ y) ^ 2 + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := by
          nlinarith [sq_nonneg (collarInd L d u δ y - ∑ j : Fin n, collarInd L d u δ (r j)),
            sq_nonneg (collarInd L d u δ y - b),
            sq_nonneg ((∑ j : Fin n, collarInd L d u δ (r j)) - b),
            collarInd_nonneg L d u δ y, hS0' r, hb0]
        refine (mul_le_mul_of_nonneg_left hmid hA00).trans ?_
        exact le_of_eq (by ring)
    -- the value of the slot integral
    have hyval : ∀ r ∈ Submission.BoseGases.abox n L,
        (∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
            + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
        = A0 * 3 * V + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2 := by
      intro r _
      have h1 : (∫ y in acube L, (collarInd L d u δ y) ^ 2) = V := by
        rw [MeasureTheory.setIntegral_congr_fun (acube_measurable L)
          (fun y _ => collarInd_sq L d u δ y)]
        rw [hV]
        exact hVac δ
      have hI1 : IntegrableOn (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2) (acube L) volume := by
        have hc : Measurable (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2) :=
          (measurable_const : Measurable (fun _ : E3 => A0 * 3)).mul
            ((Work.BoseFixB1B.measurable_collarInd L d u δ).pow_const 2)
        refine Work.BoseB1Cube.PortSmallB.integrableOn_acube_of_boundW (C := A0 * 3) hL hc.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (acube_measurable L)]
        refine ae_of_all _ (fun y _ => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have hle : (collarInd L d u δ y) ^ 2 ≤ 1 := by
          have h3 := collarInd_le_one L d u δ y
          have h4 := collarInd_nonneg L d u δ y
          nlinarith
        calc A0 * 3 * (collarInd L d u δ y) ^ 2 ≤ A0 * 3 * 1 :=
              mul_le_mul_of_nonneg_left hle (mul_nonneg hA00 (by norm_num))
          _ = A0 * 3 := by ring
      have hI2 : IntegrableOn (fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          (acube L) volume :=
        Work.BoseB1Cube.PortSmallB.integrableOn_acube_of_boundW (C := |A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2|)
          hL (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
              (volume.restrict (acube L)))
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]))
      have hI3 : IntegrableOn (fun _ : E3 => A0 * 3 * b ^ 2) (acube L) volume :=
        Work.BoseB1Cube.PortSmallB.integrableOn_acube_of_boundW (C := |A0 * 3 * b ^ 2|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : E3 => A0 * 3 * b ^ 2) (volume.restrict (acube L)))
          (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]))
      calc (∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
              + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2))
          = ∫ y in acube L, (A0 * 3 * (collarInd L d u δ y) ^ 2
              + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + A0 * 3 * b ^ 2) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
            ring
        _ = (∫ y in acube L, A0 * 3 * (collarInd L d u δ y) ^ 2)
            + (∫ y in acube L, A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (∫ y in acube L, A0 * 3 * b ^ 2) := by
            have hI12 : Integrable (fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2
                + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                ((volume : Measure E3).restrict (acube L)) :=
              (hI1.add hI2).congr (Filter.Eventually.of_forall (fun y => by
                simp only [Pi.add_apply]))
            rw [MeasureTheory.integral_add (μ := (volume : Measure E3).restrict (acube L))
                (f := fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2
                  + A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (g := fun _ : E3 => A0 * 3 * b ^ 2) hI12 hI3,
              MeasureTheory.integral_add (μ := (volume : Measure E3).restrict (acube L))
                (f := fun y : E3 => A0 * 3 * (collarInd L d u δ y) ^ 2)
                (g := fun _ : E3 => A0 * 3 * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                hI1 hI2]
        _ = A0 * 3 * V + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2 := by
            simp only [MeasureTheory.integral_const_mul, setIntegral_const, h1, hvolc, smul_eq_mul]
            ring
    -- the per-slot bound
    have hstep : fibreDirI L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ)
        ≤ ∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
            + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2) := by
      have hβ2int : IntegrableOn (fun r : Submission.BoseGases.X n => A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2) (Submission.BoseGases.abox n L) volume := by
        have hs : Measurable (fun r : Submission.BoseGases.X n =>
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) :=
          (Finset.measurable_sum _ (fun j _ =>
            (Work.BoseFixB1B.measurable_collarInd L d u δ).comp
              (measurable_pi_apply j))).pow_const 2
        have hm : Measurable (fun r : Submission.BoseGases.X n => A0 * 3 * V
            + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
            + (A0 * 3 * (L ^ 3)) * b ^ 2) :=
          (measurable_const.add ((measurable_const : Measurable (fun _ : Submission.BoseGases.X n =>
            A0 * 3 * (L ^ 3))).mul hs)).add measurable_const
        refine Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) (C := A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * ((n : ℝ) ^ 2) + (A0 * 3 * (L ^ 3)) * b ^ 2)
          hL hm.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (abox_measurable n L)]
        refine ae_of_all _ (fun r _ => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have hS2 : (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 ≤ (n : ℝ) ^ 2 := by
          have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hSle r, hS0' r, hn]
        have hA0L : 0 ≤ A0 * 3 * (L ^ 3) := by positivity
        nlinarith [hS2, hV0, sq_nonneg b, hA00, hA0L, hδ.le, hCa0, hCm0]
      rw [fibreDirI_eq]
      refine setIntegral_le_of_le_ae (abox_measurable n L) hβ2int ?_ ?_
      · intro r _
        positivity
      · intro r hr
        calc (∫ y in acube L, ∑ k : Fin 3, (fderiv ℝ (slotFibreFun (Submission.BoseGases.dlBox L d u)
              (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
              (slotDiffState L d u (γ δ) ψ) r) y (Submission.BoseGases.kcStdBasis k)) ^ 2)
            ≤ ∫ y in acube L, A0 * 3 * ((collarInd L d u δ y) ^ 2
              + (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2 + b ^ 2) := hpp r hr
          _ = _ := hyval r hr
    -- the value of the outer integral
    have hrval : (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
          + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
          + (A0 * 3 * (L ^ 3)) * b ^ 2))
        = A0 * 3 * V * (L ^ 3) ^ n
          + (A0 * 3 * (L ^ 3))
            * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          + (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n := by
      have hVint : IntegrableOn (fun _ : Submission.BoseGases.X n => A0 * 3 * V)
          (Submission.BoseGases.abox n L) volume :=
        Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) (C := |A0 * 3 * V|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Submission.BoseGases.X n => A0 * 3 * V)
              (volume.restrict (Submission.BoseGases.abox n L)))
          (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]))
      have hS2int : IntegrableOn (fun r : Submission.BoseGases.X n =>
          (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          (Submission.BoseGases.abox n L) volume := by
        have hs : Measurable (fun r : Submission.BoseGases.X n =>
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) :=
          (Finset.measurable_sum _ (fun j _ =>
            (Work.BoseFixB1B.measurable_collarInd L d u δ).comp
              (measurable_pi_apply j))).pow_const 2
        refine Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) (C := (n : ℝ) ^ 2) hL
          hs.aestronglyMeasurable ?_
        rw [ae_restrict_iff' (abox_measurable n L)]
        refine ae_of_all _ (fun r _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hSle r, hS0' r, hn]
      have hb2int : IntegrableOn (fun _ : Submission.BoseGases.X n => b ^ 2)
          (Submission.BoseGases.abox n L) volume :=
        Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) (C := |b ^ 2|) hL
          (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Submission.BoseGases.X n => b ^ 2)
              (volume.restrict (Submission.BoseGases.abox n L)))
          (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]))
      calc (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
              + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
              + (A0 * 3 * (L ^ 3)) * b ^ 2))
          = ∫ r in Submission.BoseGases.abox n L, (A0 * 3 * V
              + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2
              + (A0 * 3 * (L ^ 3)) * (b ^ 2)) := by
            rfl
        _ = (∫ r in Submission.BoseGases.abox n L, A0 * 3 * V)
            + (∫ r in Submission.BoseGases.abox n L,
                (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (∫ r in Submission.BoseGases.abox n L, (A0 * 3 * (L ^ 3)) * b ^ 2) := by
            have hb2c : IntegrableOn (fun _ : Submission.BoseGases.X n => (A0 * 3 * (L ^ 3)) * b ^ 2)
                (Submission.BoseGases.abox n L) volume := hb2int.const_mul (A0 * 3 * (L ^ 3))
            have hS2c : IntegrableOn (fun r : Submission.BoseGases.X n =>
                (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (Submission.BoseGases.abox n L) volume := hS2int.const_mul (A0 * 3 * (L ^ 3))
            have hV12 : IntegrableOn (fun r : Submission.BoseGases.X n => A0 * 3 * V
                + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (Submission.BoseGases.abox n L) volume :=
              (hVint.add hS2c).congr (Filter.Eventually.of_forall (fun r => by
                simp only [Pi.add_apply]))
            rw [MeasureTheory.integral_add
                (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n L))
                (f := fun r : Submission.BoseGases.X n => A0 * 3 * V
                  + (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                (g := fun _ : Submission.BoseGases.X n => (A0 * 3 * (L ^ 3)) * b ^ 2)
                hV12 hb2c,
              MeasureTheory.integral_add
                (μ := (volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n L))
                (f := fun _ : Submission.BoseGases.X n => A0 * 3 * V)
                (g := fun r : Submission.BoseGases.X n =>
                  (A0 * 3 * (L ^ 3)) * (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
                hVint hS2c]
        _ = A0 * 3 * V * (L ^ 3) ^ n
            + (A0 * 3 * (L ^ 3))
              * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
            + (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n := by
            simp only [MeasureTheory.integral_const_mul, setIntegral_const, hvolb, smul_eq_mul]
            ring
    -- the bound on the collar integral of the squared count
    have hS2b : (∫ r in Submission.BoseGases.abox n L,
          (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2) ≤ ((n : ℝ) * Cab) * δ := by
      have hmono : (∫ r in Submission.BoseGases.abox n L,
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          ≤ ∫ r in Submission.BoseGases.abox n L,
              (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := by
        have hint : IntegrableOn (fun r : Submission.BoseGases.X n =>
            (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j))
            (Submission.BoseGases.abox n L) volume := by
          have hs : Measurable (fun r : Submission.BoseGases.X n =>
              ∑ j : Fin n, collarInd L d u δ (r j)) :=
            Finset.measurable_sum _ (fun j _ =>
              (Work.BoseFixB1B.measurable_collarInd L d u δ).comp (measurable_pi_apply j))
          refine Work.BoseB1Cube.PortSmallB.integrableOn_abox_of_boundW (n := n) (C := (n : ℝ) * (n : ℝ)) hL
            (measurable_const.mul hs).aestronglyMeasurable ?_
          rw [ae_restrict_iff' (abox_measurable n L)]
          refine ae_of_all _ (fun r _ => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (hS0' r))]
          exact mul_le_mul_of_nonneg_left (hSle r) (Nat.cast_nonneg n)
        refine setIntegral_le_of_le_ae (abox_measurable n L) hint ?_ ?_
        · intro r _
          exact mul_nonneg (Nat.cast_nonneg n) (hS0' r)
        · intro r _
          exact hSsq r
      calc (∫ r in Submission.BoseGases.abox n L,
            (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
          ≤ ∫ r in Submission.BoseGases.abox n L,
              (n : ℝ) * ∑ j : Fin n, collarInd L d u δ (r j) := hmono
        _ = (n : ℝ) * ∫ r in Submission.BoseGases.abox n L,
              ∑ j : Fin n, collarInd L d u δ (r j) := by
            rw [MeasureTheory.integral_const_mul]
        _ ≤ (n : ℝ) * (Cab * δ) :=
            mul_le_mul_of_nonneg_left (hSint δ hδ) (Nat.cast_nonneg n)
        _ = ((n : ℝ) * Cab) * δ := by ring
    -- the bound on the squared normalised collar volume
    have hb2 : b ^ 2 ≤ (Ca * Cm) ^ 2 * δ := by
      have h1 : b ^ 2 ≤ (Ca * Cm * δ) ^ 2 := by
        rw [sq_le_sq]
        refine abs_le.mpr ⟨by linarith [hb0, abs_nonneg (Ca * Cm * δ)], ?_⟩
        rwa [abs_of_nonneg (mul_nonneg (mul_nonneg hCa0 hCm0) hδ.le)]
      have h2 : (Ca * Cm * δ) ^ 2 ≤ (Ca * Cm) ^ 2 * δ := by
        have h3 : δ ^ 2 ≤ δ := by nlinarith [hδ.le, hδ1]
        nlinarith [h3, mul_nonneg (mul_nonneg hCa0 hCm0) hδ.le, sq_nonneg (Ca * Cm)]
      linarith
    -- assembling
    refine hstep.trans (hrval.le.trans ?_)
    have hY1 : A0 * 3 * V * (L ^ 3) ^ n ≤ A0 * 3 * (Ca * (L ^ 3) ^ n) * δ := by
      have h1 : V * (L ^ 3) ^ n ≤ Ca * (L ^ 3) ^ n * δ := by
        have h2 : V * (L ^ 3) ^ n ≤ Ca * δ * (L ^ 3) ^ n :=
          mul_le_mul_of_nonneg_right hVle' (pow_nonneg (pow_nonneg hL.le 3) n)
        calc V * (L ^ 3) ^ n ≤ Ca * δ * (L ^ 3) ^ n := h2
          _ = Ca * (L ^ 3) ^ n * δ := by ring
      calc A0 * 3 * V * (L ^ 3) ^ n = (A0 * 3) * (V * (L ^ 3) ^ n) := by ring
        _ ≤ (A0 * 3) * (Ca * (L ^ 3) ^ n * δ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = A0 * 3 * (Ca * (L ^ 3) ^ n) * δ := by ring
    have hY2 : (A0 * 3 * (L ^ 3))
          * (∫ r in Submission.BoseGases.abox n L, (∑ j : Fin n, collarInd L d u δ (r j)) ^ 2)
        ≤ (A0 * 3 * (L ^ 3)) * (((n : ℝ) * Cab) * δ) :=
      mul_le_mul_of_nonneg_left hS2b (by positivity)
    have hY3 : (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n
        ≤ (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ := by
      have h1 : b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ := by
        have h2 : b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * δ * (L ^ 3) ^ n :=
          mul_le_mul_of_nonneg_right hb2 (pow_nonneg (pow_nonneg hL.le 3) n)
        calc b ^ 2 * (L ^ 3) ^ n ≤ (Ca * Cm) ^ 2 * δ * (L ^ 3) ^ n := h2
          _ = (Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ := by ring
      calc (A0 * 3 * (L ^ 3)) * b ^ 2 * (L ^ 3) ^ n
          = (A0 * 3 * (L ^ 3)) * (b ^ 2 * (L ^ 3) ^ n) := by ring
        _ ≤ (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n * δ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ := by ring
    have hsumY : A0 * 3 * (Ca * (L ^ 3) ^ n) * δ
          + (A0 * 3 * (L ^ 3)) * (((n : ℝ) * Cab) * δ)
          + (A0 * 3 * (L ^ 3)) * ((Ca * Cm) ^ 2 * (L ^ 3) ^ n) * δ
        = (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ := by ring
    linarith [hY1, hY2, hY3, hsumY]
  -- the summed estimate
  have hsum : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∑ i : Fin (n+1), fibreDirI L
        (Submission.BoseGases.dlBox L d u) (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.chiSmallB M L d u) i (slotDiffState L d u (γ δ) ψ))
      ≤ ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
          + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ := by
    intro δ hδ hδ1
    calc ∑ i : Fin (n+1), fibreDirI L (Submission.BoseGases.dlBox L d u)
          (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
          (slotDiffState L d u (γ δ) ψ)
        ≤ ∑ _i : Fin (n+1), (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)) * δ :=
          Finset.sum_le_sum (fun i _ => hslot δ hδ hδ1 i)
      _ = ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hev1 : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ≤ 1 :=
    nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hev : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ ∧ δ ≤ 1 :=
    Filter.Eventually.and self_mem_nhdsWithin hev1
  refine ⟨⟨(↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
      + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)), by positivity, ?_⟩, ?_⟩
  · filter_upwards [hev] with δ hδ
    exact hsum δ hδ.1 hδ.2
  · refine squeeze_zero'
      (f := fun δ : ℝ => ∑ i : Fin (n+1), fibreDirI L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiSmallB M L d u) i
        (slotDiffState L d u (γ δ) ψ))
      (g := fun δ : ℝ => ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
        + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ) ?_ ?_ ?_
    · filter_upwards with δ
      exact Finset.sum_nonneg (fun i _ => by
        rw [fibreDirI_eq]
        refine integral_nonneg (fun r => integral_nonneg (fun y => ?_))
        exact Finset.sum_nonneg (fun k _ => sq_nonneg _))
    · filter_upwards [hev] with δ hδ
      exact hsum δ hδ.1 hδ.2
    · have hcont : Filter.Tendsto (fun δ : ℝ =>
          ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n))) * δ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h2 : Filter.Tendsto (fun δ : ℝ => δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using h2.const_mul
          ((↑(n+1) : ℝ) * (A0 * 3 * (Ca * (L ^ 3) ^ n + (L ^ 3) * ((n : ℝ) * Cab)
            + (L ^ 3) * (Ca * Cm) ^ 2 * (L ^ 3) ^ n)))
      exact hcont

end Work.BoseB1Cube.PortSmallB
