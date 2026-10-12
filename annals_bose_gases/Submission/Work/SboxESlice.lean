import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.EneuSuperadd
import Submission.Work.SmallBoxSuperadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Slice/kinetic identities for the small-box energy (e_B superadditivity, II)

Continuation of `SmallBoxSuperadd.lean`: the *expectation-level* slice
identities of the corpus small-box analysis energy
`sboxE N s μ w w1 Φ = kinWord N s Φ + qLHSword(N,s,μ,w,w1)Φ` over the
centred box `abox N s`:

  * `qLHSden2_expect_eq_slice` — the block-2 mirror of
    `qLHSden1_expect_eq_slice` (frozen first block, `aboxFubini` u-outer);
  * the kinetic slice identities
    `kin_slice1_integral` / `kin_slice2_integral`:
    the block-`g` kinetic part of `sboxE_g` equals the integral (over the
    frozen other block) of `kinWord N_g` of the block-`g` slices —
    `aboxFubini` + the domain-free derivative identities of `EneuSuperadd`
    (`es_fderiv_slice1/2`, `es_sliceL/R_kcDir`, `es_kinB1/B2_merge`);
  * the sum/interchange atoms used there (`fderivSq_integrableOn_abox`,
    `kinWord_eq_integral_es_kinAll`, `es_kinB1/B2_integrableOn_abox`).

All statements are kernel-agnostic (the integrability hypotheses that the
concrete chosen-branch kernels discharge via `PotChosen` are kept explicit,
as in `SmallBoxSuperadd.qLHSden1_expect_eq_slice`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Block-2 potential slice identity -/

/-- Slice integral identity for the potential part of the block-2 energy: the
expectation of the block-2 diagonal density over the full box equals the
integral (over the frozen first block) of the `qLHSword` of the second-block
slices. -/
lemma qLHSden2_expect_eq_slice {N1 N2 : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : X (N1+N2) → ℝ)
    (hG : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume) :
    (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
      = ∫ u in abox N1 s, qLHSword (N := N2) s μ w w1 (sbs_slice2 Φ u) := by
  have hF := aboxFubini (N1 := N1) (N2 := N2) s
    (fun x : X (N1+N2) => (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x) hG
  calc
    (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
        = ∫ u in abox N1 s, ∫ wv in abox N2 s,
            (Φ (mergeBlock N1 N2 (u, wv))) ^ 2
              * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 (mergeBlock N1 N2 (u, wv)) := hF.symm
    _ = ∫ u in abox N1 s, ∫ wv in abox N2 s,
        (sbs_slice2 Φ u wv) ^ 2 * qLHSden N2 s μ w w1 wv := by
          apply integral_congr_ae
          filter_upwards with u
          apply integral_congr_ae
          filter_upwards with wv
          rw [qLHSden2_merge (N1 := N1) (N2 := N2) s μ w w1 u wv]
          rfl
    _ = ∫ u in abox N1 s, qLHSword (N := N2) s μ w w1 (sbs_slice2 Φ u) := by
          apply integral_congr_ae
          filter_upwards with u
          exact (qLHSword_eq_integral_qLHSden (N := N2) s μ w w1 (sbs_slice2 Φ u)).symm

/-! ## Kinetic slice identities -/

/-- A single squared directional derivative is integrable over the centred box. -/
lemma fderivSq_integrableOn_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) (k : Fin 3)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ) :
    IntegrableOn (fun x : X N => (fderiv ℝ Φ x (kcDir N i k)) ^ 2) (abox N ℓ) volume := by
  exact integrableOn_abox_of_continuous hℓ
    ((firstDir_contDiff (f := Φ) hΦc (kcDir N i k)).continuous.pow 2)

/-- The block-1 kinetic density is integrable over the centred box. -/
lemma es_kinB1_integrableOn_abox {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (es_kinB1 N1 N2 Φ) (abox (N1+N2) s) volume := by
  unfold es_kinB1
  change Integrable (fun x : X (N1+N2) => ∑ i₁ : Fin N1, ∑ k : Fin 3,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k))^2)
      (volume.restrict (abox (N1+N2) s))
  exact integrable_finsetSum Finset.univ (fun i₁ _ => by
    change Integrable (fun x : X (N1+N2) => ∑ k : Fin 3,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k))^2)
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact fderivSq_integrableOn_abox hs (Fin.castAdd N2 i₁) k hΦ))

/-- The block-2 kinetic density is integrable over the centred box. -/
lemma es_kinB2_integrableOn_abox {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    IntegrableOn (es_kinB2 N1 N2 Φ) (abox (N1+N2) s) volume := by
  unfold es_kinB2
  change Integrable (fun x : X (N1+N2) => ∑ j₂ : Fin N2, ∑ k : Fin 3,
      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k))^2)
      (volume.restrict (abox (N1+N2) s))
  exact integrable_finsetSum Finset.univ (fun j₂ _ => by
    change Integrable (fun x : X (N1+N2) => ∑ k : Fin 3,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k))^2)
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact fderivSq_integrableOn_abox hs (Fin.natAdd N1 j₂) k hΦ))

/-- The full kinetic density is integrable over the centred box. -/
lemma es_kinAll_integrableOn_abox {N : ℕ} {s : ℝ} (hs : 0 < s) {ψ : X N → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : IntegrableOn (es_kinAll N ψ) (abox N s) volume := by
  unfold es_kinAll
  change Integrable (fun x : X N => ∑ i : Fin N, ∑ k : Fin 3,
      (fderiv ℝ ψ x (kcDir N i k))^2) (volume.restrict (abox N s))
  exact integrable_finsetSum Finset.univ (fun i _ => by
    change Integrable (fun x : X N => ∑ k : Fin 3,
        (fderiv ℝ ψ x (kcDir N i k))^2) (volume.restrict (abox N s))
    exact integrable_finsetSum Finset.univ (fun k _ => by
      exact fderivSq_integrableOn_abox hs i k hψ))

/-- The kinetic word is the integral of the kinetic density over the centred
box (finite-sum/integral interchange). -/
lemma kinWord_eq_integral_es_kinAll {N : ℕ} {s : ℝ} (hs : 0 < s) {ψ : X N → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    kinWord N s ψ = ∫ x in abox N s, es_kinAll N ψ x := by
  calc
    kinWord N s ψ
        = (∑ i : Fin N, ∑ k : Fin 3, ∫ x in abox N s,
            (fderiv ℝ ψ x (kcDir N i k)) ^ 2) := rfl
    _ = (∑ i : Fin N, ∫ x in abox N s, (∑ k : Fin 3,
            (fderiv ℝ ψ x (kcDir N i k)) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X N)).restrict (abox N s))
            (f := fun k : Fin 3 => fun x : X N => (fderiv ℝ ψ x (kcDir N i k)) ^ 2)
            (fun k _ => fderivSq_integrableOn_abox hs i k hψ)).symm
    _ = ∫ x in abox N s, (∑ i : Fin N, ∑ k : Fin 3,
            (fderiv ℝ ψ x (kcDir N i k)) ^ 2) := by
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X N)).restrict (abox N s))
            (f := fun i : Fin N => fun x : X N => ∑ k : Fin 3,
              (fderiv ℝ ψ x (kcDir N i k)) ^ 2)
            (fun i _ => by
              exact integrable_finsetSum Finset.univ (fun k _ =>
                fderivSq_integrableOn_abox hs i k hψ))).symm
    _ = ∫ x in abox N s, es_kinAll N ψ x := rfl

/-- Pointwise: the block-1 kinetic density of the merged configuration equals
the full kinetic density of the first-block slice. -/
lemma slice1_kinAll_eq {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) (w : X N2) :
    es_kinAll N1 (sbs_slice Φ w) u = es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  have hM := es_kinB1_merge (N1 := N1) (N2 := N2) (Φ := Φ) hΦ u w
  change (∑ i : Fin N1, ∑ k : Fin 3, (fderiv ℝ (es_slice1 N1 N2 Φ w) u (kcDir N1 i k)) ^ 2)
      = es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))
  exact hM

/-- Pointwise: the block-2 kinetic density of the merged configuration equals
the full kinetic density of the second-block slice. -/
lemma slice2_kinAll_eq {N1 N2 : ℕ} {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (u : X N1) (w : X N2) :
    es_kinAll N2 (sbs_slice2 Φ u) w = es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
  have hM := es_kinB2_merge (N1 := N1) (N2 := N2) (Φ := Φ) hΦ u w
  change (∑ j : Fin N2, ∑ k : Fin 3, (fderiv ℝ (es_slice2 N1 N2 Φ u) w (kcDir N2 j k)) ^ 2)
      = es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))
  exact hM

/-- The block-1 kinetic part of `sboxE1` equals the integral over the frozen
second block of the `kinWord` of the first-block slices. -/
lemma kin_slice1_integral {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {Φ : X (N1+N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
      = ∫ w in abox N2 s, kinWord N1 s (sbs_slice Φ w) := by
  have hK1 : IntegrableOn (es_kinB1 N1 N2 Φ) (abox (N1+N2) s) volume :=
    es_kinB1_integrableOn_abox hs hΦ
  calc
    (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
        = ∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x := by
          calc
            (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
                (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
                = (∑ i₁ : Fin N1, ∫ x in abox (N1+N2) s, (∑ k : Fin 3,
                    (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)) := by
                  apply Finset.sum_congr rfl
                  intro i₁ _
                  exact (integral_finsetSum (s := Finset.univ)
                    (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
                    (f := fun k : Fin 3 => fun x : X (N1+N2) =>
                      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
                    (fun k _ => fderivSq_integrableOn_abox hs (Fin.castAdd N2 i₁) k hΦ)).symm
            _ = ∫ x in abox (N1+N2) s, (∑ i₁ : Fin N1, ∑ k : Fin 3,
                    (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2) := by
                  exact (integral_finsetSum (s := Finset.univ)
                    (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
                    (f := fun i₁ : Fin N1 => fun x : X (N1+N2) => ∑ k : Fin 3,
                      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
                    (fun i₁ _ => by
                      exact integrable_finsetSum Finset.univ (fun k _ =>
                        fderivSq_integrableOn_abox hs (Fin.castAdd N2 i₁) k hΦ))).symm
            _ = ∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x := rfl
    _ = ∫ w in abox N2 s, ∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
          exact (aboxFubini_swapped (N1 := N1) (N2 := N2) s (es_kinB1 N1 N2 Φ) hK1).symm
    _ = ∫ w in abox N2 s, kinWord N1 s (sbs_slice Φ w) := by
          apply integral_congr_ae
          filter_upwards with w
          calc
            ∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))
                = ∫ u in abox N1 s, es_kinAll N1 (sbs_slice Φ w) u := by
                  apply integral_congr_ae
                  filter_upwards with u
                  exact (slice1_kinAll_eq hΦ u w).symm
            _ = kinWord N1 s (sbs_slice Φ w) := by
                  exact (kinWord_eq_integral_es_kinAll (N := N1) (s := s) hs
                    (ψ := sbs_slice Φ w) (es_slice1_contDiff hΦ w)).symm

/-- The block-2 kinetic part of `sboxE2` equals the integral over the frozen
first block of the `kinWord` of the second-block slices. -/
lemma kin_slice2_integral {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {Φ : X (N1+N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
      = ∫ u in abox N1 s, kinWord N2 s (sbs_slice2 Φ u) := by
  have hK2 : IntegrableOn (es_kinB2 N1 N2 Φ) (abox (N1+N2) s) volume :=
    es_kinB2_integrableOn_abox hs hΦ
  calc
    (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
        = ∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x := by
          calc
            (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
                (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
                = (∑ j₂ : Fin N2, ∫ x in abox (N1+N2) s, (∑ k : Fin 3,
                    (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)) := by
                  apply Finset.sum_congr rfl
                  intro j₂ _
                  exact (integral_finsetSum (s := Finset.univ)
                    (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
                    (f := fun k : Fin 3 => fun x : X (N1+N2) =>
                      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
                    (fun k _ => fderivSq_integrableOn_abox hs (Fin.natAdd N1 j₂) k hΦ)).symm
            _ = ∫ x in abox (N1+N2) s, (∑ j₂ : Fin N2, ∑ k : Fin 3,
                    (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2) := by
                  exact (integral_finsetSum (s := Finset.univ)
                    (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
                    (f := fun j₂ : Fin N2 => fun x : X (N1+N2) => ∑ k : Fin 3,
                      (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
                    (fun j₂ _ => by
                      exact integrable_finsetSum Finset.univ (fun k _ =>
                        fderivSq_integrableOn_abox hs (Fin.natAdd N1 j₂) k hΦ))).symm
            _ = ∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x := rfl
    _ = ∫ u in abox N1 s, ∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)) := by
          exact (aboxFubini (N1 := N1) (N2 := N2) s (es_kinB2 N1 N2 Φ) hK2).symm
    _ = ∫ u in abox N1 s, kinWord N2 s (sbs_slice2 Φ u) := by
          apply integral_congr_ae
          filter_upwards with u
          calc
            ∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))
                = ∫ w in abox N2 s, es_kinAll N2 (sbs_slice2 Φ u) w := by
                  apply integral_congr_ae
                  filter_upwards with w
                  exact (slice2_kinAll_eq hΦ u w).symm
            _ = kinWord N2 s (sbs_slice2 Φ u) := by
                  exact (kinWord_eq_integral_es_kinAll (N := N2) (s := s) hs
                    (ψ := sbs_slice2 Φ u) (es_slice2_contDiff hΦ u)).symm


/-- The block-1 kinetic sum (the kinetic part of `sboxE1`) is the integral of
the block-1 kinetic density over the merged centred box. -/
lemma block1kin_eq_integral_es_kinB1 {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
      = ∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x := by
  calc
    (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
        = (∑ i₁ : Fin N1, ∫ x in abox (N1+N2) s, (∑ k : Fin 3,
            (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i₁ _
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
            (f := fun k : Fin 3 => fun x : X (N1+N2) =>
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
            (fun k _ => fderivSq_integrableOn_abox hs (Fin.castAdd N2 i₁) k hΦ)).symm
    _ = ∫ x in abox (N1+N2) s, (∑ i₁ : Fin N1, ∑ k : Fin 3,
            (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2) := by
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
            (f := fun i₁ : Fin N1 => fun x : X (N1+N2) => ∑ k : Fin 3,
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
            (fun i₁ _ => by
              exact integrable_finsetSum Finset.univ (fun k _ =>
                fderivSq_integrableOn_abox hs (Fin.castAdd N2 i₁) k hΦ))).symm
    _ = ∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x := rfl

/-- The block-2 kinetic sum (the kinetic part of `sboxE2`) is the integral of
the block-2 kinetic density over the merged centred box. -/
lemma block2kin_eq_integral_es_kinB2 {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (N1+N2) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
      = ∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x := by
  calc
    (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
        (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
        = (∑ j₂ : Fin N2, ∫ x in abox (N1+N2) s, (∑ k : Fin 3,
            (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro j₂ _
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
            (f := fun k : Fin 3 => fun x : X (N1+N2) =>
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
            (fun k _ => fderivSq_integrableOn_abox hs (Fin.natAdd N1 j₂) k hΦ)).symm
    _ = ∫ x in abox (N1+N2) s, (∑ j₂ : Fin N2, ∑ k : Fin 3,
            (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2) := by
          exact (integral_finsetSum (s := Finset.univ)
            (μ := (volume : Measure (X (N1+N2))).restrict (abox (N1+N2) s))
            (f := fun j₂ : Fin N2 => fun x : X (N1+N2) => ∑ k : Fin 3,
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
            (fun j₂ _ => by
              exact integrable_finsetSum Finset.univ (fun k _ =>
                fderivSq_integrableOn_abox hs (Fin.natAdd N1 j₂) k hΦ))).symm
    _ = ∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x := rfl

/-! ## Product-restricted integrability of merged functions -/

/-- A function integrable over the merged centred box is integrable (as a
merged function) over the product of the block-restricted measures. -/
lemma abox_prod_integrable {N1 N2 : ℕ} (s : ℝ) (G : X (N1+N2) → ℝ)
    (hG : IntegrableOn G (abox (N1+N2) s) volume) :
    Integrable (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
  have hmp : MeasurePreserving (blockSplitEquiv N1 N2)
      (volume.restrict (abox (N1 + N2) s))
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) :=
    aboxSplit_measurePreserving_restrict N1 N2 s
  have hif := (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
    (g := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)))
  apply hif.1
  change Integrable (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x)))
      (volume.restrict (abox (N1 + N2) s))
  have hpt : (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) = G := by
    funext x
    rw [blockSplitEquiv_apply]
    exact congrArg G (mergeBlock_eq N1 N2 x)
  rw [hpt]
  exact hG

/-! ## Block-split of the full small-box energy -/

/-- The full `qLHSword` density integral over the merged box is at least the
sum of the two within-block density integrals (the cross-block density is
nonnegative for `w ≥ 0`). -/
lemma pot_blocks_le_full {N1 N2 : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ)
    (hw : ∀ x y : ℝ³, 0 ≤ w x y) {Φ : X (N1+N2) → ℝ}
    (hD1 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume)
    (hD2 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume)
    (hD : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden (N1+N2) s μ w w1 x) (abox (N1+N2) s) volume) :
    (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
      + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
      ≤ ∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden (N1+N2) s μ w w1 x := by
  have hle : (∫ x in abox (N1+N2) s,
        ((Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x
          + (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x))
      ≤ ∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden (N1+N2) s μ w w1 x := by
    refine integral_mono ?_ ?_ ?_
    · exact IntegrableOn.add hD1 hD2
    · exact hD
    · intro x
      have hd := qLHSden_blocks_le (N1 := N1) (N2 := N2) s μ w w1 hw x
      have hx : 0 ≤ (Φ x) ^ 2 := sq_nonneg (Φ x)
      nlinarith
  have hsum : (∫ x in abox (N1+N2) s,
        ((Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x
          + (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x))
      = (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
        + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x) := by
    exact integral_add hD1 hD2
  rw [← hsum]
  exact hle

/-- The full small-box energy of the merged state dominates the sum of the
block-1 and block-2 small-box energies (`sboxE1`, `sboxE2` are the kinetic
block + within-block potential pieces of the merged expectation).  Kernel
`w`-nonnegativity makes the cross-block pair contribution nonnegative. -/
lemma sboxE_ge_sboxE1_add_sboxE2 {N1 N2 : ℕ} {s μ : ℝ} (w w1 : ℝ³ → ℝ³ → ℝ)
    (hw : ∀ x y : ℝ³, 0 ≤ w x y) {Φ : X (N1+N2) → ℝ} (_hΦ : ContDiff ℝ ∞ Φ)
    (hD1 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume)
    (hD2 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x) (abox (N1+N2) s) volume)
    (hD : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden (N1+N2) s μ w w1 x) (abox (N1+N2) s) volume) :
    sboxE1 (N1 := N1) (N2 := N2) s μ w w1 Φ
      + sboxE2 (N1 := N1) (N2 := N2) s μ w w1 Φ
      ≤ sboxE (N1+N2) s μ w w1 Φ := by
  have hP := pot_blocks_le_full (N1 := N1) (N2 := N2) (s := s) (μ := μ) w w1 hw hD1 hD2 hD
  have hKS := kinWord_block_split (N1 := N1) (N2 := N2) s Φ
  unfold sboxE sboxE1 sboxE2
  rw [qLHSword_eq_integral_qLHSden (N := N1+N2) s μ w w1 Φ]
  -- the potential integral of the full density is ≥ A + B (hP), kin splits (hKS)
  nlinarith [hKS, hP]
end BoseGases

end Submission
