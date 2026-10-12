import ChallengeDeps
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1.boxProjBoundsReal
import Submission.Work.BoseFixB1.chooseAboxBounds
import Submission.Work.BoseFixB1S.boxPQw_mass_le
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxPairBlockIntegrable`

The three per-pair integrands of the box-projected `lm:appinteractionestimate` rung —
`pairBlock`, `pairSq`, `pairCross` at the localised kernels `wSmallPair M ℓ d u v` /
`wSmall1Pair h M ℓ d u` and the chosen `ω = Classical.choose h` — are `IntegrableOn` the
centred `N`-particle box `abox N ℓ`.

Every one of them has the shape `(prefactor) · (kernel at the slot pair (x_{p.1}, x_{p.2}))`
with a prefactor built from the box projections of `Φ` (measurable and bounded on the compact
box) and from `ω`, which is bounded by `1` a.e. on the box (`Work.BoseFixB3.Eps.abs_choose_le_one`
pulled back along `x ↦ x_i − x_j` by `Submission.BoseGases.ae_pair_pullback`).  The localised
kernel slot is handled by `Work.BoseFixB1.integrableOn_slot_wSmallPair`, which dominates it by
a constant times `|f (x_i − x_j)|` with `f` the numerator (`v`, `g₀`) — integrable with support
in `‖z‖ ≤ R0` in the dilute regime.

The projection bounds at the *measure-real* box volume (`volA = volume.real A`, dropping the
positivity requirement of `abs_boxPInd_le`, which fails for degenerate `B(u)`) are
`Work.BoseFixB1.boxProjBoundsReal`; the a.e. bounds of `ω` are
`Work.BoseFixB1.chooseAboxBounds`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases
open Work.UBBInputs8
open Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The prefactors of the three pair integrands

`pairSq = pBig·pBig · w`, `pairBlock = (pBig·pBig + 2(1−ω)·pQsum·pPP) · w` and
`pairCross = (pQsum·pPP) · w₁`, where `pDD = Q_{p.2}Q_{p.1}Φ`, `pQsum = P_{p.1}Q_{p.2}Φ +
P_{p.2}Q_{p.1}Φ`, `pPP = P_{p.1}P_{p.2}Φ`. -/

private noncomputable def pDD (volA : ℝ) (A : Set E3) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  boxQInd volA A p.2 (boxQInd volA A p.1 Φ) x

private noncomputable def pQsum (volA : ℝ) (A : Set E3) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
    + boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x

private noncomputable def pPP (volA : ℝ) (A : Set E3) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x

private noncomputable def pBig (volA : ℝ) (A : Set E3) (om : E3 → E3 → ℝ) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  pDD volA A Φ p x + pQsum volA A Φ p x + om (x p.1) (x p.2) * pPP volA A Φ p x

private noncomputable def pSqPref (volA : ℝ) (A : Set E3) (om : E3 → E3 → ℝ) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  pBig volA A om Φ p x * pBig volA A om Φ p x

private noncomputable def pBlkPref (volA : ℝ) (A : Set E3) (om : E3 → E3 → ℝ) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  pBig volA A om Φ p x * pBig volA A om Φ p x
    + (2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x * pPP volA A Φ p x

private noncomputable def pCrPref (volA : ℝ) (A : Set E3) {N : ℕ}
    (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) : ℝ :=
  pQsum volA A Φ p x * pPP volA A Φ p x

/-! ## The factorisations `pairX = pref · kernel` -/

private lemma pairSq_eq_pref (volA : ℝ) (A : Set E3) (w om : E3 → E3 → ℝ)
    {N : ℕ} (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) :
    pairSq volA A w om Φ p x = pSqPref volA A om Φ p x * w (x p.1) (x p.2) := by
  simp only [pairSq, pSqPref, pBig, pDD, pQsum, pPP]
  ring

private lemma pairBlock_eq_pref (volA : ℝ) (A : Set E3) (w om : E3 → E3 → ℝ)
    {N : ℕ} (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) :
    pairBlock volA A w om Φ p x = pBlkPref volA A om Φ p x * w (x p.1) (x p.2) := by
  simp only [pairBlock, pBlkPref, pBig, pDD, pQsum, pPP]
  ring

private lemma pairCross_eq_pref (volA : ℝ) (A : Set E3) (w₁ om : E3 → E3 → ℝ)
    {N : ℕ} (Φ : X N → ℝ) (p : Fin N × Fin N) (x : X N) :
    pairCross volA A w₁ Φ p x = pCrPref volA A Φ p x * w₁ (x p.1) (x p.2) := by
  simp only [pairCross, pCrPref, pQsum, pPP]

/-! ## A.e. measurability of the prefactors -/

private lemma pBig_aesm {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ}
    (hA : MeasurableSet A) (hΦm : Measurable Φ) {om : E3 → E3 → ℝ} (p : Fin N × Fin N)
    (hom : AEStronglyMeasurable (fun x : X N => om (x p.1) (x p.2))
      (volume.restrict (abox N ℓ))) :
    AEStronglyMeasurable (pBig volA A om Φ p) (volume.restrict (abox N ℓ)) := by
  have h1 : Measurable (fun x : X N => pDD volA A Φ p x) :=
    Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.2
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.1 hΦm)
  have h2 : Measurable (fun x : X N => boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.2 hΦm)
  have h3 : Measurable (fun x : X N => boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.2
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.1 hΦm)
  have h4 : Measurable (fun x : X N => pPP volA A Φ p x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxPInd volA A hA p.2 hΦm)
  have h2' : AEStronglyMeasurable (fun x : X N => boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x)
      (volume.restrict (abox N ℓ)) := h2.aestronglyMeasurable
  have h3' : AEStronglyMeasurable (fun x : X N => boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x)
      (volume.restrict (abox N ℓ)) := h3.aestronglyMeasurable
  have hQ : AEStronglyMeasurable (fun x : X N => pQsum volA A Φ p x)
      (volume.restrict (abox N ℓ)) := h2'.add h3'
  have hmain : AEStronglyMeasurable
      (fun x : X N => pDD volA A Φ p x + pQsum volA A Φ p x
        + om (x p.1) (x p.2) * pPP volA A Φ p x) (volume.restrict (abox N ℓ)) :=
    (h1.aestronglyMeasurable.add hQ).add (hom.mul h4.aestronglyMeasurable)
  exact hmain

private lemma pSqPref_aesm {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ}
    (hA : MeasurableSet A) (hΦm : Measurable Φ) {om : E3 → E3 → ℝ} (p : Fin N × Fin N)
    (hom : AEStronglyMeasurable (fun x : X N => om (x p.1) (x p.2))
      (volume.restrict (abox N ℓ))) :
    AEStronglyMeasurable (pSqPref volA A om Φ p) (volume.restrict (abox N ℓ)) := by
  have h := pBig_aesm (volA := volA) (A := A) (Φ := Φ) hA hΦm p hom
  have hmain : AEStronglyMeasurable
      (fun x : X N => pBig volA A om Φ p x * pBig volA A om Φ p x)
      (volume.restrict (abox N ℓ)) := h.mul h
  exact hmain

private lemma pCrPref_aesm {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ}
    (hA : MeasurableSet A) (hΦm : Measurable Φ) (p : Fin N × Fin N) :
    AEStronglyMeasurable (pCrPref volA A Φ p) (volume.restrict (abox N ℓ)) := by
  have h2 : Measurable (fun x : X N => boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.2 hΦm)
  have h3 : Measurable (fun x : X N => boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.2
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.1 hΦm)
  have h4 : Measurable (fun x : X N => pPP volA A Φ p x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxPInd volA A hA p.2 hΦm)
  have hQ : AEStronglyMeasurable (fun x : X N => pQsum volA A Φ p x)
      (volume.restrict (abox N ℓ)) :=
    h2.aestronglyMeasurable.add h3.aestronglyMeasurable
  have hmain : AEStronglyMeasurable (fun x : X N => pQsum volA A Φ p x * pPP volA A Φ p x)
      (volume.restrict (abox N ℓ)) := hQ.mul h4.aestronglyMeasurable
  exact hmain

private lemma pBlkPref_aesm {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ}
    (hA : MeasurableSet A) (hΦm : Measurable Φ) {om : E3 → E3 → ℝ} (p : Fin N × Fin N)
    (hom : AEStronglyMeasurable (fun x : X N => om (x p.1) (x p.2))
      (volume.restrict (abox N ℓ))) :
    AEStronglyMeasurable (pBlkPref volA A om Φ p) (volume.restrict (abox N ℓ)) := by
  have hbig := pBig_aesm (volA := volA) (A := A) (Φ := Φ) hA hΦm p hom
  have h1 : AEStronglyMeasurable (fun x : X N => (2 : ℝ) * (1 - om (x p.1) (x p.2)))
      (volume.restrict (abox N ℓ)) :=
    (aestronglyMeasurable_const.sub hom).const_mul 2
  have h2 : Measurable (fun x : X N => boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.2 hΦm)
  have h3 : Measurable (fun x : X N => boxPInd volA A p.2 (boxQInd volA A p.1 Φ) x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.2
      (Work.BoseFixB1S.measurable_boxQInd volA (A := A) hA p.1 hΦm)
  have h4 : Measurable (fun x : X N => pPP volA A Φ p x) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA p.1
      (Work.BoseFixB1S.measurable_boxPInd volA A hA p.2 hΦm)
  have hQ : AEStronglyMeasurable (fun x : X N => pQsum volA A Φ p x)
      (volume.restrict (abox N ℓ)) :=
    h2.aestronglyMeasurable.add h3.aestronglyMeasurable
  have h5 : AEStronglyMeasurable
      (fun x : X N => (2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x
        * pPP volA A Φ p x) (volume.restrict (abox N ℓ)) :=
    (h1.mul hQ).mul h4.aestronglyMeasurable
  have hmain : AEStronglyMeasurable
      (fun x : X N => pBig volA A om Φ p x * pBig volA A om Φ p x
        + (2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x * pPP volA A Φ p x)
      (volume.restrict (abox N ℓ)) := (hbig.mul hbig).add h5
  exact hmain

/-! ## A.e. bounds of the prefactors -/

private lemma ae_restrict_abox_of_forall {N : ℕ} {ℓ : ℝ} {p : X N → Prop}
    (hp : ∀ x ∈ abox N ℓ, p x) : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), p x :=
  (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ hp)

private lemma pBig_ae_bound {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ} {C : ℝ}
    {om : E3 → E3 → ℝ} (p : Fin N × Fin N)
    (hD : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pDD volA A Φ p x| ≤ 4 * C)
    (hQ : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pQsum volA A Φ p x| ≤ 4 * C)
    (hP : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pPP volA A Φ p x| ≤ C)
    (hom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |om (x p.1) (x p.2)| ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pBig volA A om Φ p x| ≤ 9 * C := by
  filter_upwards [hD, hQ, hP, hom] with x hDx hQx hPx homx
  show |pDD volA A Φ p x + pQsum volA A Φ p x + om (x p.1) (x p.2) * pPP volA A Φ p x|
      ≤ 9 * C
  calc |pDD volA A Φ p x + pQsum volA A Φ p x + om (x p.1) (x p.2) * pPP volA A Φ p x|
      ≤ |pDD volA A Φ p x + pQsum volA A Φ p x|
        + |om (x p.1) (x p.2) * pPP volA A Φ p x| := abs_add_le _ _
    _ ≤ (|pDD volA A Φ p x| + |pQsum volA A Φ p x|)
        + |om (x p.1) (x p.2)| * |pPP volA A Φ p x| := by
          rw [abs_mul]
          exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (4 * C + 4 * C) + 1 * C := by
          refine add_le_add (add_le_add hDx hQx) ?_
          exact mul_le_mul homx hPx (abs_nonneg _) (by norm_num)
    _ = 9 * C := by ring

private lemma pSqPref_ae_bound {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ} {C : ℝ}
    {om : E3 → E3 → ℝ} (p : Fin N × Fin N)
    (hbig : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pBig volA A om Φ p x| ≤ 9 * C) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pSqPref volA A om Φ p x| ≤ 9 * C * (9 * C) := by
  filter_upwards [hbig] with x hx
  show |pBig volA A om Φ p x * pBig volA A om Φ p x| ≤ 9 * C * (9 * C)
  rw [abs_mul]
  exact mul_le_mul hx hx (abs_nonneg _) (le_trans (abs_nonneg _) hx)

private lemma pCrPref_ae_bound {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ} {C : ℝ}
    (p : Fin N × Fin N) (hC : 0 ≤ C)
    (hQ : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pQsum volA A Φ p x| ≤ 4 * C)
    (hP : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pPP volA A Φ p x| ≤ C) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pCrPref volA A Φ p x| ≤ 4 * C * C := by
  filter_upwards [hQ, hP] with x hQx hPx
  show |pQsum volA A Φ p x * pPP volA A Φ p x| ≤ 4 * C * C
  rw [abs_mul]
  exact mul_le_mul hQx hPx (abs_nonneg _) (by linarith)

private lemma pBlkPref_ae_bound {N : ℕ} {ℓ volA : ℝ} {A : Set E3} {Φ : X N → ℝ} {C : ℝ}
    {om : E3 → E3 → ℝ} (p : Fin N × Fin N) (hC : 0 ≤ C)
    (hD : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pDD volA A Φ p x| ≤ 4 * C)
    (hQ : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pQsum volA A Φ p x| ≤ 4 * C)
    (hP : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pPP volA A Φ p x| ≤ C)
    (hom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |om (x p.1) (x p.2)| ≤ 1) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |pBlkPref volA A om Φ p x| ≤ 97 * C * C := by
  have hbig := pBig_ae_bound p hD hQ hP hom
  filter_upwards [hbig, hQ, hP, hom] with x hbigx hQx hPx homx
  show |pBig volA A om Φ p x * pBig volA A om Φ p x
      + (2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x * pPP volA A Φ p x|
      ≤ 97 * C * C
  have h1 : |pBig volA A om Φ p x * pBig volA A om Φ p x| ≤ 9 * C * (9 * C) := by
    rw [abs_mul]
    exact mul_le_mul hbigx hbigx (abs_nonneg _) (le_trans (abs_nonneg _) hbigx)
  have h2 : |((2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x) * pPP volA A Φ p x|
      ≤ (4 * (4 * C)) * C := by
    rw [abs_mul]
    refine mul_le_mul ?_ hPx (abs_nonneg _) (by nlinarith [hC])
    rw [abs_mul]
    refine mul_le_mul ?_ hQx (abs_nonneg _) (by linarith)
    have hsub : |1 - om (x p.1) (x p.2)| ≤ 2 := by
      have h := abs_le.mp homx
      rw [abs_sub_le_iff]
      exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
    calc |(2 : ℝ) * (1 - om (x p.1) (x p.2))| = 2 * |1 - om (x p.1) (x p.2)| := by
          rw [abs_mul]
          norm_num
      _ ≤ 2 * 2 := by linarith
      _ = 4 := by norm_num
  calc |pBig volA A om Φ p x * pBig volA A om Φ p x
        + (2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x * pPP volA A Φ p x|
      ≤ |pBig volA A om Φ p x * pBig volA A om Φ p x|
        + |((2 * (1 - om (x p.1) (x p.2))) * pQsum volA A Φ p x) * pPP volA A Φ p x| :=
        abs_add_le _ _
    _ ≤ 9 * C * (9 * C) + (4 * (4 * C)) * C := add_le_add h1 h2
    _ = 97 * C * C := by ring

/-! ## The target -/

theorem boxPairBlockIntegrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairBlock (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairSq (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    ∧ (∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
        (fun x : Submission.BoseGases.X N =>
          Work.BoseFixB1.pairCross (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ p x)
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) := by
  classical
  have hA : MeasurableSet (dlBox ℓ d u) := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : dlBox ℓ d u ⊆ acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolAeq : Work.SmallBoxSliding.boxMass ℓ d u
      = (volume : Measure E3).real (dlBox ℓ d u) :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  obtain ⟨Bf, hBf⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |Bf| := by
    intro x hx
    have hh := hBf x hx
    rw [Real.norm_eq_abs] at hh
    exact le_trans hh (le_abs_self Bf)
  have hΦm : Measurable Φ := hΦc.measurable
  -- the numerator profiles
  have hvInt : Integrable v := Submission.BoseGases.v_integrable hv1
  have hvZero : ∀ z : E3, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  have hg0Int : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0Zero : ∀ z : E3, R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have main : ∀ volA : ℝ, volA = (volume : Measure E3).real (dlBox ℓ d u) →
      (∀ p ∈ pairSet N, IntegrableOn (fun x : X N => pairBlock volA (dlBox ℓ d u)
          (wSmallPair M ℓ d u v) (omC (Classical.choose h)) Φ p x) (abox N ℓ) volume)
    ∧ (∀ p ∈ pairSet N, IntegrableOn (fun x : X N => pairSq volA (dlBox ℓ d u)
          (wSmallPair M ℓ d u v) (omC (Classical.choose h)) Φ p x) (abox N ℓ) volume)
    ∧ (∀ p ∈ pairSet N, IntegrableOn (fun x : X N => pairCross volA (dlBox ℓ d u)
          (wSmall1Pair h M ℓ d u) Φ p x) (abox N ℓ) volume) := by
    intro volA hvolA
    have hbd : ∀ i j : Fin N,
        (∀ x ∈ abox N ℓ, |boxPInd volA (dlBox ℓ d u) i Φ x| ≤ |Bf|)
      ∧ (∀ x ∈ abox N ℓ, |boxQInd volA (dlBox ℓ d u) i Φ x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ abox N ℓ,
          |boxPInd volA (dlBox ℓ d u) i (boxPInd volA (dlBox ℓ d u) j Φ) x| ≤ |Bf|)
      ∧ (∀ x ∈ abox N ℓ,
          |boxPInd volA (dlBox ℓ d u) i (boxQInd volA (dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ abox N ℓ,
          |boxQInd volA (dlBox ℓ d u) i (boxPInd volA (dlBox ℓ d u) j Φ) x| ≤ 2 * |Bf|)
      ∧ (∀ x ∈ abox N ℓ,
          |boxQInd volA (dlBox ℓ d u) i (boxQInd volA (dlBox ℓ d u) j Φ) x| ≤ 4 * |Bf|) := by
      intro i j
      simpa only [← hvolA] using boxProjBoundsReal (N := N) hℓ hA hAc hΦb i j
    have three : ∀ p ∈ pairSet N,
        IntegrableOn (fun x : X N => pairBlock volA (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (omC (Classical.choose h)) Φ p x) (abox N ℓ) volume
        ∧ IntegrableOn (fun x : X N => pairSq volA (dlBox ℓ d u)
            (wSmallPair M ℓ d u v) (omC (Classical.choose h)) Φ p x) (abox N ℓ) volume
        ∧ IntegrableOn (fun x : X N => pairCross volA (dlBox ℓ d u)
            (wSmall1Pair h M ℓ d u) Φ p x) (abox N ℓ) volume := by
      intro p hp
      have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      obtain ⟨hP1Φ, hQ1Φ, hP1P2, hP1Q2, hQ1P2, hQ1Q2⟩ := hbd p.1 p.2
      obtain ⟨hP2Φ, hQ2Φ, hP2P1, hP2Q1, hQ2P1, hQ2Q1⟩ := hbd p.2 p.1
      -- a.e. bounds for the elementary pieces
      have hDDae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pDD volA (dlBox ℓ d u) Φ p x| ≤ 4 * |Bf| :=
        ae_restrict_abox_of_forall (fun x hx => hQ2Q1 x hx)
      have hQsumae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pQsum volA (dlBox ℓ d u) Φ p x| ≤ 4 * |Bf| :=
        ae_restrict_abox_of_forall (fun x hx => by
          show |boxPInd volA (dlBox ℓ d u) p.1 (boxQInd volA (dlBox ℓ d u) p.2 Φ) x
              + boxPInd volA (dlBox ℓ d u) p.2 (boxQInd volA (dlBox ℓ d u) p.1 Φ) x|
            ≤ 4 * |Bf|
          calc |boxPInd volA (dlBox ℓ d u) p.1 (boxQInd volA (dlBox ℓ d u) p.2 Φ) x
                + boxPInd volA (dlBox ℓ d u) p.2 (boxQInd volA (dlBox ℓ d u) p.1 Φ) x|
              ≤ |boxPInd volA (dlBox ℓ d u) p.1 (boxQInd volA (dlBox ℓ d u) p.2 Φ) x|
                + |boxPInd volA (dlBox ℓ d u) p.2 (boxQInd volA (dlBox ℓ d u) p.1 Φ) x| :=
                abs_add_le _ _
            _ ≤ 2 * |Bf| + 2 * |Bf| := add_le_add (hP1Q2 x hx) (hP2Q1 x hx)
            _ = 4 * |Bf| := by ring)
      have hPPae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pPP volA (dlBox ℓ d u) Φ p x| ≤ |Bf| :=
        ae_restrict_abox_of_forall (fun x hx => hP1P2 x hx)
      -- the `ω`-slot facts
      obtain ⟨hom_bd', hom_sm'⟩ := chooseAboxBounds (N := N) hv_supp hR0 hv hvrad h hℓ hij
      have hom_bd : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |omC (Classical.choose h) (x p.1) (x p.2)| ≤ 1 := by
        simpa only [Submission.BoseGases.omC] using hom_bd'
      have hom_sm : AEStronglyMeasurable
          (fun x : X N => omC (Classical.choose h) (x p.1) (x p.2))
          (volume.restrict (abox N ℓ)) := by
        simpa only [Submission.BoseGases.omC] using hom_sm'
      -- the prefactor facts
      have hbigae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pBig volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p x| ≤ 9 * |Bf| :=
        pBig_ae_bound p hDDae hQsumae hPPae hom_bd
      have hSqae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pSqPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p x|
            ≤ 9 * |Bf| * (9 * |Bf|) := pSqPref_ae_bound p hbigae
      have hCrae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pCrPref volA (dlBox ℓ d u) Φ p x| ≤ 4 * |Bf| * |Bf| :=
        pCrPref_ae_bound p (abs_nonneg Bf) hQsumae hPPae
      have hBlkae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
          |pBlkPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p x|
            ≤ 97 * |Bf| * |Bf| :=
        pBlkPref_ae_bound p (abs_nonneg Bf) hDDae hQsumae hPPae hom_bd
      have hSqsm : AEStronglyMeasurable
          (pSqPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p)
          (volume.restrict (abox N ℓ)) :=
        pSqPref_aesm hA hΦm p hom_sm
      have hBlksm : AEStronglyMeasurable
          (pBlkPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p)
          (volume.restrict (abox N ℓ)) :=
        pBlkPref_aesm hA hΦm p hom_sm
      have hCrsm : AEStronglyMeasurable (pCrPref volA (dlBox ℓ d u) Φ p)
          (volume.restrict (abox N ℓ)) := pCrPref_aesm hA hΦm p
      -- integrability of the three prefactor-times-kernel integrands
      have hSqInt : IntegrableOn (fun x : X N =>
          pSqPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p x
            * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume :=
        integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0) hℓ hd hvInt hvZero
          hM hR hRχ u hij hSqsm (B := 9 * |Bf| * (9 * |Bf|)) (by positivity) hSqae
      have hBlkInt : IntegrableOn (fun x : X N =>
          pBlkPref volA (dlBox ℓ d u) (omC (Classical.choose h)) Φ p x
            * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume :=
        integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0) hℓ hd hvInt hvZero
          hM hR hRχ u hij hBlksm (B := 97 * |Bf| * |Bf|) (by positivity) hBlkae
      have hCrInt : IntegrableOn (fun x : X N =>
          pCrPref volA (dlBox ℓ d u) Φ p x
            * wSmall1Pair h M ℓ d u (x p.1) (x p.2)) (abox N ℓ) volume := by
        have h := integrableOn_slot_wSmallPair (N := N) (ℓ := ℓ) (d := d) (R := R0) hℓ hd
          hg0Int hg0Zero hM hR hRχ u hij hCrsm (B := 4 * |Bf| * |Bf|) (by positivity) hCrae
        simpa only [Submission.BoseGases.wSmall1Pair] using h
      refine ⟨?_, ?_, ?_⟩
      · exact hBlkInt.congr_fun
          (fun x hx => (pairBlock_eq_pref volA (dlBox ℓ d u) (wSmallPair M ℓ d u v)
            (omC (Classical.choose h)) Φ p x).symm) (abox_measurable N ℓ)
      · exact hSqInt.congr_fun
          (fun x hx => (pairSq_eq_pref volA (dlBox ℓ d u) (wSmallPair M ℓ d u v)
            (omC (Classical.choose h)) Φ p x).symm) (abox_measurable N ℓ)
      · exact hCrInt.congr_fun
          (fun x hx => (pairCross_eq_pref volA (dlBox ℓ d u) (wSmall1Pair h M ℓ d u)
            (omC (Classical.choose h)) Φ p x).symm) (abox_measurable N ℓ)
    exact ⟨fun p hp => (three p hp).1, fun p hp => (three p hp).2.1,
      fun p hp => (three p hp).2.2⟩
  exact main (Work.SmallBoxSliding.boxMass ℓ d u) hvolAeq

end Work.BoseFixB1
