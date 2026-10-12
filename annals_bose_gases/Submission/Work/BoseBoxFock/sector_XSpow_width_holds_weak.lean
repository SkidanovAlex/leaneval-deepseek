import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_sliceF_pointwise
import Submission.Work.BoseBoxFock.sector_XSpow_width_holds_kf
import Submission.Work.BoseBoxFock.weakJointProj_aP_ite
import Submission.Work.MB.slotFacts_boxSlotSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sector_XSpow_width_holds_weak`

The width form of the sector spectral bound in the **measurable/bounded** state class: the
strong form `Work.BoseBoxFock.sector_XSpow_width_holds_kf` assumes `Continuous Φ` with
`tsupport Φ ⊆ abox n ℓ`, hypotheses that
(`FINDING_continuous_hypotheses_UNSATISFIABLE.md`, `FINDING_stateClass_RESOLVED_s17.md` §1.2)
are *unsatisfiable* for the states of the box ↔ model bridge — the box restriction `Φ·1_abox`
of a smooth state is discontinuous.  Here only `Measurable Φ` and a global sup-bound are needed.

## The proof

`sector_XSpow_width` reduces the claim to the two mode-theoretic inputs **(comm)** (the sector
projection is `XSpow`-equivariant, `Work.BoseBoxFock.Kf.XSpow_slotExact_comm_box`) and
**(contr)** (the sector projection is an `L²` contraction,
`Work.BoseBoxFock.Kf.slotExact_contract_box`) — both of which need only `MemLp ⊤` of the state —
together with the *geometry half* `∫ ‖XSpow ℓ S j Φc‖² ≤ 𝓜^{2j}∫Φ²`
(`Work.BoseBoxFock.XSpow_L2_le`, which assumes `Continuous Φ`).

The content of this file is the weak-class re-run of the geometry half, i.e. of the chain

    `XSrp_L2_le` ← `jointProj_vanish` ← `moment_expansion` ← `jointProj_resolution`,
    `jointProj_orthogonal`, `nPlusPow_sector_expansion`

of `XSrpSector.lean`/`thetaSector_vanish.lean`/`jointProj_vanish.lean`, with `Continuous Φ`
replaced by `Measurable Φ` + `∀ x, |Φ x| ≤ C` (the bound is *global*: the fibre integrals
`y ↦ Φ (x[i↦y])` with `x` outside the box need it):

* `Work.BoseBoxFock.Weak` (module `weakAux`) supplies the slot-mean algebra for bounded
  measurable states (`aP_comm`, `aP_aQ_comm`, `aQ_comm`, `aP_sym_box`, `aP_finset_sum`, …);
* `Work.BoseBoxFock.weakJointProj_aP_ite` supplies the eigen-relation
  `Pₖ E_W = 0` (`k ∈ W`) / `= E_W` (`k ∉ W`) in the same class;
* the present file derives from these the eigen-relation for `Qₖ` (`aQ_jointProj_ite`), the
  orthogonality `∫ E_WΦ · E_VΨ = 0` of distinct sectors (`jointProj_orthogonal`), the sector
  expansions `nPlusPow_expansion` (`n₊^m Φ = Σ_W |W|^m E_WΦ`) and `XSrp_expansion`
  (`XS^j Φ = Σ_W (sectorCount S W)^j E_WΦ`), the pairing `∫ E_WΦ·Φ = ∫ (E_WΦ)²`
  (`jointProj_pairing`), the Parseval identity (`parseval_XSrp`), the moment expansion
  (`moment_expansion_weak`), the vanishing of the sectors beyond the window
  (`jointProj_vanish_weak`) and finally `XSrp_L2_le_weak` / `XSpow_L2_le_weak`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock
namespace Weak

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-! ## Measurability and boundedness of the joint sectors -/

theorem jointProj_measurable {n : ℕ} {ℓ : ℝ} (W : Finset ℕ) {Φ : X n → ℝ}
    (hΦm : Measurable Φ) : Measurable (Work.BoseFixB2.jointProj ℓ W Φ) :=
  blockOp_measurable W hΦm n le_rfl

theorem jointProj_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (W : Finset ℕ) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦb : ∀ x, |Φ x| ≤ C) :
    ∀ x, |Work.BoseFixB2.jointProj ℓ W Φ x| ≤ 2 ^ n * C := fun x =>
  sectorXSpow_decomp_blockOp_abs_le (ℓ := ℓ) hℓ W hC hΦb n le_rfl x

/-! ## The eigenvalue of the complementary slot -/

theorem aQ_jointProj_ite {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : k < n)
    (W : Finset ℕ) {Φ : X n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ)
    (hΦb : ∀ x, |Φ x| ≤ C) :
    aQ ℓ ⟨k, hk⟩ (Work.BoseFixB2.jointProj ℓ W Φ)
      = if k ∈ W then Work.BoseFixB2.jointProj ℓ W Φ else 0 := by
  have hP := weakJointProj_aP_ite hℓ hk W hC hΦm hΦb
  rw [show aQ ℓ ⟨k, hk⟩ (Work.BoseFixB2.jointProj ℓ W Φ)
      = Work.BoseFixB2.jointProj ℓ W Φ - aP ℓ ⟨k, hk⟩ (Work.BoseFixB2.jointProj ℓ W Φ)
      from rfl, hP]
  by_cases h : k ∈ W <;> simp [h]

/-! ## Orthogonality of distinct joint sectors -/

theorem jointProj_orthogonal {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {S T : Finset ℕ}
    (hST : S ∩ Finset.range n ≠ T ∩ Finset.range n) (Φ Ψ : X n → ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C)
    (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) :
    (∫ x in abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * Work.BoseFixB2.jointProj ℓ T Ψ x) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, (k ∈ S ∩ Finset.range n ∧ k ∉ T ∩ Finset.range n) ∨
      (k ∈ T ∩ Finset.range n ∧ k ∉ S ∩ Finset.range n) := by
    by_contra h
    push Not at h
    exact hST (Finset.ext fun k => ⟨fun hk => (h k).1 hk, fun hk => (h k).2 hk⟩)
  have hkn : k < n := by
    rcases hk with h | h
    · exact Finset.mem_range.mp (Finset.mem_inter.mp h.1).2
    · exact Finset.mem_range.mp (Finset.mem_inter.mp h.1).2
  have hmem : (k ∈ S ∧ k ∉ T) ∨ (k ∈ T ∧ k ∉ S) := by
    rcases hk with h | h
    · exact Or.inl ⟨(Finset.mem_inter.mp h.1).1,
        fun hc => h.2 (Finset.mem_inter.mpr ⟨hc, Finset.mem_range.mpr hkn⟩)⟩
    · exact Or.inr ⟨(Finset.mem_inter.mp h.1).1,
        fun hc => h.2 (Finset.mem_inter.mpr ⟨hc, Finset.mem_range.mpr hkn⟩)⟩
  have hsym := aP_sym_box hℓ ⟨k, hkn⟩
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) hC)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) hD)
    (jointProj_measurable S hΦm) (jointProj_abs_le hℓ S hC hΦb)
    (jointProj_measurable T hΨm) (jointProj_abs_le hℓ T hD hΨb)
  rcases hmem with ⟨hkS, hkT⟩ | ⟨hkT, hkS⟩
  · have h1 : aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ S Φ) = 0 := by
      rw [weakJointProj_aP_ite hℓ hkn S hC hΦm hΦb]
      simp [hkS]
    have h2 : aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ T Ψ)
        = Work.BoseFixB2.jointProj ℓ T Ψ := by
      rw [weakJointProj_aP_ite hℓ hkn T hD hΨm hΨb]
      simp [hkT]
    rw [h1, h2] at hsym
    simpa using hsym.symm
  · have h1 : aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ T Ψ) = 0 := by
      rw [weakJointProj_aP_ite hℓ hkn T hD hΨm hΨb]
      simp [hkT]
    have h2 : aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.jointProj ℓ S Φ)
        = Work.BoseFixB2.jointProj ℓ S Φ := by
      rw [weakJointProj_aP_ite hℓ hkn S hC hΦm hΦb]
      simp [hkS]
    rw [h2, h1] at hsym
    simpa using hsym


/-! ## Linearity of the complementary slot over a finite sum -/

theorem aQ_finset_sum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (f : ι → X n → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ W ∈ s, 0 ≤ c W) (hfm : ∀ W ∈ s, Measurable (f W))
    (hfb : ∀ W ∈ s, ∀ x, |f W x| ≤ C) (x : X n) :
    aQ ℓ i (fun y => ∑ W ∈ s, c W * f W y) x = ∑ W ∈ s, c W * aQ ℓ i (f W) x := by
  rw [show aQ ℓ i (fun y => ∑ W ∈ s, c W * f W y) x
      = (∑ W ∈ s, c W * f W x) - aP ℓ i (fun y => ∑ W ∈ s, c W * f W y) x from rfl,
    aP_finset_sum hℓ i s c f hC hc hfm hfb x]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [show aQ ℓ i (f W) x = f W x - aP ℓ i (f W) x from rfl]
  ring

/-! ## The sector expansion of the excitation count -/

theorem jointProj_resolution_weak {n : ℕ} (ℓ : ℝ) {Φ : X n → ℝ} (x : X n) :
    (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x) = Φ x := by
  have h := congrFun (Work.BoseFixB2.Sector.blockOp_sum_powerset ℓ Φ n le_rfl) x
  simpa only [Work.BoseFixB2.jointProj_eq_blockOp, Finset.sum_apply] using h

theorem nPlusPow_expansion {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (m : ℕ) :
    Work.BoseBox.nPlusPow ℓ n m Φ
      = fun x => ∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ m * Work.BoseFixB2.jointProj ℓ W Φ x := by
  induction m with
  | zero =>
      funext x
      rw [show Work.BoseBox.nPlusPow ℓ n 0 Φ = Φ from rfl]
      rw [show (∑ W ∈ (Finset.range n).powerset, (W.card : ℝ) ^ 0 *
            Work.BoseFixB2.jointProj ℓ W Φ x)
          = ∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x from
        Finset.sum_congr rfl fun W _ => by rw [pow_zero, one_mul],
        jointProj_resolution_weak ℓ x]
  | succ m ih =>
      rw [show Work.BoseBox.nPlusPow ℓ n (m + 1) Φ
          = Work.BoseBox.nPlusFun ℓ (Work.BoseBox.nPlusPow ℓ n m Φ) from rfl, ih]
      funext x
      show (∑ i : Fin n, aQ ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
              (W.card : ℝ) ^ m * Work.BoseFixB2.jointProj ℓ W Φ y) x)
          = ∑ W ∈ (Finset.range n).powerset,
              (W.card : ℝ) ^ (m + 1) * Work.BoseFixB2.jointProj ℓ W Φ x
      have hterm : ∀ i : Fin n,
          aQ ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
              (W.card : ℝ) ^ m * Work.BoseFixB2.jointProj ℓ W Φ y) x
            = ∑ W ∈ (Finset.range n).powerset, (W.card : ℝ) ^ m *
                (if (i : ℕ) ∈ W then Work.BoseFixB2.jointProj ℓ W Φ x else 0) := by
        intro i
        rw [aQ_finset_sum hℓ i _ (fun W => (W.card : ℝ) ^ m)
          (fun W y => Work.BoseFixB2.jointProj ℓ W Φ y)
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) hC)
          (fun W _ => by positivity) (fun W _ => jointProj_measurable W hΦm)
          (fun W _ => jointProj_abs_le hℓ W hC hΦb) x]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [aQ_jointProj_ite hℓ i.isLt W hC hΦm hΦb]
        by_cases h : (i : ℕ) ∈ W <;> simp [h]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun W hW => ?_
      have hWsub : W ⊆ Finset.range n := Finset.mem_powerset.mp hW
      have hBool : (∑ i : Fin n, (if (i : ℕ) ∈ W then (1 : ℝ) else 0)) = (W.card : ℝ) := by
        rw [Finset.sum_boole]
        rw [show (Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ W) = tsPreS n W from rfl,
          tsPreS_card_of_subset_range hWsub]
      have hcount : (∑ i : Fin n, (W.card : ℝ) ^ m * (if (i : ℕ) ∈ W then
            Work.BoseFixB2.jointProj ℓ W Φ x else 0))
          = (W.card : ℝ) ^ (m + 1) * Work.BoseFixB2.jointProj ℓ W Φ x := by
        rw [← Finset.mul_sum, show (∑ i : Fin n, (if (i : ℕ) ∈ W then
              Work.BoseFixB2.jointProj ℓ W Φ x else 0))
            = (∑ i : Fin n, (if (i : ℕ) ∈ W then (1 : ℝ) else 0)) *
              Work.BoseFixB2.jointProj ℓ W Φ x from by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : (i : ℕ) ∈ W <;> simp [h],
          hBool, pow_succ]
        ring
      rw [hcount]

/-! ## The sector expansion of the restricted excitation count -/

theorem XSrp_expansion {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (j : ℕ) :
    XSrp ℓ S j Φ
      = fun x => ∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x := by
  induction j with
  | zero =>
      funext x
      rw [XSrp_zero]
      rw [show (∑ W ∈ (Finset.range n).powerset, (sectorCount S W) ^ 0 *
            Work.BoseFixB2.jointProj ℓ W Φ x)
          = ∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x from
        Finset.sum_congr rfl fun W _ => by rw [pow_zero, one_mul],
        jointProj_resolution_weak ℓ x]
  | succ j ih =>
      rw [show XSrp ℓ S (j + 1) Φ = XSr ℓ S (XSrp ℓ S j Φ) from rfl, ih]
      funext x
      show (∑ i ∈ S, ((∑ W ∈ (Finset.range n).powerset,
              (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x)
            - aP ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
                (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ y) x))
          = ∑ W ∈ (Finset.range n).powerset,
              (sectorCount S W) ^ (j + 1) * Work.BoseFixB2.jointProj ℓ W Φ x
      have hterm : ∀ i ∈ S,
          ((∑ W ∈ (Finset.range n).powerset,
              (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x)
            - aP ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
                (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ y) x)
            = ∑ W ∈ (Finset.range n).powerset, (sectorCount S W) ^ j *
                (if (i : ℕ) ∈ W then Work.BoseFixB2.jointProj ℓ W Φ x else 0) := by
        intro i _
        rw [show ((∑ W ∈ (Finset.range n).powerset,
                (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x)
              - aP ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
                  (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ y) x)
            = aQ ℓ i (fun y => ∑ W ∈ (Finset.range n).powerset,
                  (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ y) x from rfl]
        rw [aQ_finset_sum hℓ i _ (fun W => (sectorCount S W) ^ j)
          (fun W y => Work.BoseFixB2.jointProj ℓ W Φ y)
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n) hC)
          (fun W _ => pow_nonneg (sectorCount_nonneg S W) _)
          (fun W _ => jointProj_measurable W hΦm)
          (fun W _ => jointProj_abs_le hℓ W hC hΦb) x]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [aQ_jointProj_ite hℓ i.isLt W hC hΦm hΦb]
        by_cases h : (i : ℕ) ∈ W <;> simp [h]
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun W hW => ?_
      have hBool : (∑ i ∈ S, (if (i : ℕ) ∈ W then (1 : ℝ) else 0)) = sectorCount S W := by
        rw [Finset.sum_boole, sectorCount_eq]
      have hcount : (∑ i ∈ S, (sectorCount S W) ^ j * (if (i : ℕ) ∈ W then
            Work.BoseFixB2.jointProj ℓ W Φ x else 0))
          = (sectorCount S W) ^ (j + 1) * Work.BoseFixB2.jointProj ℓ W Φ x := by
        rw [← Finset.mul_sum, show (∑ i ∈ S, (if (i : ℕ) ∈ W then
              Work.BoseFixB2.jointProj ℓ W Φ x else 0))
            = (∑ i ∈ S, (if (i : ℕ) ∈ W then (1 : ℝ) else 0)) *
              Work.BoseFixB2.jointProj ℓ W Φ x from by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : (i : ℕ) ∈ W <;> simp [h],
          hBool, pow_succ]
        ring
      rw [hcount]

/-! ## Integrability of products of a joint sector with a state -/

theorem integrableOn_jointProj_mul {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (W : Finset ℕ)
    (Φ Ψ : X n → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hΦm : Measurable Φ)
    (hΦb : ∀ x, |Φ x| ≤ C) (hΨm : Measurable Ψ) (hΨb : ∀ x, |Ψ x| ≤ D) :
    IntegrableOn (fun x => Work.BoseFixB2.jointProj ℓ W Φ x * Ψ x) (abox n ℓ) volume := by
  have hB : (0 : ℝ) ≤ 2 ^ n * C := mul_nonneg (by positivity) hC
  refine IntegrableOn.of_bound (s := abox n ℓ) (abox_lt_top n ℓ hℓ.le) ?_
    ((2 ^ n * C) * D) ?_
  · exact ((jointProj_measurable W hΦm).aestronglyMeasurable.restrict).mul
      (hΨm.aestronglyMeasurable.restrict)
  · filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (jointProj_abs_le hℓ W hC hΦb x) (hΨb x) (abs_nonneg _)
      (le_trans (abs_nonneg _) (jointProj_abs_le hℓ W hC hΦb x))

/-! ## The pairing of a joint sector with the state -/

theorem jointProj_pairing {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {W : Finset ℕ}
    (hW : W ⊆ Finset.range n) {Φ : X n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ)
    (hΦb : ∀ x, |Φ x| ≤ C) :
    (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ W Φ x * Φ x)
      = ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have hEm : Measurable (Work.BoseFixB2.jointProj ℓ W Φ) := jointProj_measurable W hΦm
  have hEb : ∀ x, |Work.BoseFixB2.jointProj ℓ W Φ x| ≤ 2 ^ n * C :=
    jointProj_abs_le hℓ W hC hΦb
  have hC' : 0 ≤ 2 ^ n * C := mul_nonneg (by positivity) hC
  have h1 : (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ W Φ x * Φ x)
      = ∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ W Φ x *
          (∑ V ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ V Φ x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [jointProj_resolution_weak ℓ x]
  rw [h1]
  have h2 : (fun x => Work.BoseFixB2.jointProj ℓ W Φ x *
        (∑ V ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ V Φ x))
      = fun x => ∑ V ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x *
          Work.BoseFixB2.jointProj ℓ V Φ x := by
    funext x
    simp only [Finset.mul_sum]
  rw [h2]
  rw [MeasureTheory.integral_finsetSum _ (fun V _ =>
    integrableOn_jointProj_mul hℓ W Φ (Work.BoseFixB2.jointProj ℓ V Φ) hC hC' hΦm hΦb
      (jointProj_measurable V hΦm) (jointProj_abs_le hℓ V hC hΦb))]
  rw [Finset.sum_eq_single W]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  · intro V hV hVne
    have hST : W ∩ Finset.range n ≠ V ∩ Finset.range n := by
      intro h
      have h1 : W ∩ Finset.range n = W := Finset.inter_eq_left.mpr hW
      have h2 : V ∩ Finset.range n = V :=
        Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hV)
      rw [h1, h2] at h
      exact hVne h.symm
    exact jointProj_orthogonal hℓ hST Φ Φ hC hC hΦm hΦb hΦm hΦb
  · intro hWm
    exact absurd (Finset.mem_powerset.mpr hW) hWm

/-! ## The resolution identity for the `L²` norm -/

theorem normSq_resolution {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    (∫ x in abox n ℓ, (Φ x) ^ 2)
      = ∑ W ∈ (Finset.range n).powerset,
          ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have h1 : (∫ x in abox n ℓ, (Φ x) ^ 2)
      = ∫ x in abox n ℓ,
          (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [jointProj_resolution_weak ℓ x]
    ring
  rw [h1]
  have h2 : (fun x => (∑ W ∈ (Finset.range n).powerset,
        Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x)
      = fun x => ∑ W ∈ (Finset.range n).powerset,
          Work.BoseFixB2.jointProj ℓ W Φ x * Φ x := by
    funext x
    simp only [Finset.sum_mul]
  rw [h2]
  rw [MeasureTheory.integral_finsetSum _ (fun W _ =>
    integrableOn_jointProj_mul hℓ W Φ Φ hC hC hΦm hΦb hΦm hΦb)]
  exact Finset.sum_congr rfl fun W hW =>
    jointProj_pairing hℓ (Finset.mem_powerset.mp hW) hC hΦm hΦb

/-! ## The moment expansion -/

theorem moment_expansion_weak {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (k : ℕ) :
    (∫ x in abox n ℓ, Work.BoseBox.nPlusPow ℓ n (2 * k) Φ x * Φ x)
      = ∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ (2 * k) *
            ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have h1 : (fun x => Work.BoseBox.nPlusPow ℓ n (2 * k) Φ x * Φ x)
      = fun x => (∑ W ∈ (Finset.range n).powerset,
          (W.card : ℝ) ^ (2 * k) * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x := by
    funext x
    simp only [congrFun (nPlusPow_expansion ℓ hℓ hC hΦm hΦb (2 * k)) x]
  rw [h1]
  have h2 : (fun x => (∑ W ∈ (Finset.range n).powerset,
        (W.card : ℝ) ^ (2 * k) * Work.BoseFixB2.jointProj ℓ W Φ x) * Φ x)
      = fun x => ∑ W ∈ (Finset.range n).powerset, (W.card : ℝ) ^ (2 * k) *
          (Work.BoseFixB2.jointProj ℓ W Φ x * Φ x) := by
    funext x
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun W _ => by ring
  rw [h2]
  rw [MeasureTheory.integral_finsetSum _ (fun W _ =>
    (integrableOn_jointProj_mul hℓ W Φ Φ hC hC hΦm hΦb hΦm hΦb).const_mul _)]
  exact Finset.sum_congr rfl fun W hW => by
    rw [MeasureTheory.integral_const_mul,
      jointProj_pairing hℓ (Finset.mem_powerset.mp hW) hC hΦm hΦb]

/-! ## Parseval for the restricted excitation count -/

theorem parseval_XSrp {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) (j : ℕ) :
    (∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2)
      = ∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ (2 * j) *
            ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 := by
  have hC' : 0 ≤ 2 ^ n * C := mul_nonneg (by positivity) hC
  have hInt : ∀ W ∈ (Finset.range n).powerset, ∀ V ∈ (Finset.range n).powerset,
      IntegrableOn (fun x => ((sectorCount S W) ^ j * (sectorCount S V) ^ j) *
        (Work.BoseFixB2.jointProj ℓ W Φ x * Work.BoseFixB2.jointProj ℓ V Φ x))
        (abox n ℓ) volume := fun W _ V _ =>
    (integrableOn_jointProj_mul hℓ W Φ (Work.BoseFixB2.jointProj ℓ V Φ) hC hC' hΦm hΦb
      (jointProj_measurable V hΦm) (jointProj_abs_le hℓ V hC hΦb)).const_mul _
  have h1 : (fun x => (XSrp ℓ S j Φ x) ^ 2)
      = fun x => (∑ W ∈ (Finset.range n).powerset,
            (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x) *
          (∑ V ∈ (Finset.range n).powerset,
            (sectorCount S V) ^ j * Work.BoseFixB2.jointProj ℓ V Φ x) := by
    funext x
    simp only [congrFun (XSrp_expansion hℓ S hC hΦm hΦb j) x, sq]
  rw [h1]
  have h2 : (fun x => (∑ W ∈ (Finset.range n).powerset,
          (sectorCount S W) ^ j * Work.BoseFixB2.jointProj ℓ W Φ x) *
        (∑ V ∈ (Finset.range n).powerset,
          (sectorCount S V) ^ j * Work.BoseFixB2.jointProj ℓ V Φ x))
      = fun x => ∑ W ∈ (Finset.range n).powerset, ∑ V ∈ (Finset.range n).powerset,
          ((sectorCount S W) ^ j * (sectorCount S V) ^ j) *
            (Work.BoseFixB2.jointProj ℓ W Φ x * Work.BoseFixB2.jointProj ℓ V Φ x) := by
    funext x
    simp only [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun V _ => by ring
  rw [h2]
  rw [MeasureTheory.integral_finsetSum _ (fun W hW =>
    MeasureTheory.integrable_finsetSum _ (fun V hV => hInt W hW V hV))]
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun V hV => hInt W hW V hV)]
  rw [Finset.sum_eq_single W]
  · have hself : (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ W Φ x *
          Work.BoseFixB2.jointProj ℓ W Φ x)
        = ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [MeasureTheory.integral_const_mul, hself, ← pow_add, ← two_mul]
  · intro V hV hVne
    have hzero : (∫ x in abox n ℓ, Work.BoseFixB2.jointProj ℓ W Φ x *
          Work.BoseFixB2.jointProj ℓ V Φ x) = 0 :=
      jointProj_orthogonal hℓ
        (by
          intro h
          have h1 : W ∩ Finset.range n = W :=
            Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hW)
          have h2 : V ∩ Finset.range n = V :=
            Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hV)
          rw [h1, h2] at h
          exact hVne h.symm)
        Φ Φ hC hC hΦm hΦb hΦm hΦb
    rw [MeasureTheory.integral_const_mul, hzero]
    ring
  · intro hWm
    exact absurd hW hWm

/-! ## Vanishing of the joint sectors outside the window -/

theorem jointProj_vanish_weak {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) {W : Finset ℕ} (hW : W ⊆ Finset.range n)
    (hcard : M < (W.card : ℝ)) :
    ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 = 0 := by
  set a : ℝ := ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 with hadef
  set B : ℝ := ∫ x in abox n ℓ, (Φ x) ^ 2 with hBdef
  have ha_nonneg : 0 ≤ a := integral_nonneg (fun x => sq_nonneg _)
  have hpos : 0 < (W.card : ℝ) := lt_of_le_of_lt hM hcard
  have hkey : ∀ k : ℕ, a ≤ B * (M / (W.card : ℝ)) ^ (2 * k) := by
    intro k
    have hm := hmom (2 * k)
    rw [moment_expansion_weak hℓ hC hΦm hΦb k] at hm
    have hsingle := Finset.single_le_sum
      (s := (Finset.range n).powerset)
      (f := fun V => (V.card : ℝ) ^ (2 * k) *
        ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ V Φ x) ^ 2)
      (fun V _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg V.card) _)
        (integral_nonneg (fun x => sq_nonneg _)))
      (Finset.mem_powerset.mpr hW)
    have h1 : (W.card : ℝ) ^ (2 * k) * a ≤ M ^ (2 * k) * B := le_trans hsingle hm
    have hdiv : a ≤ M ^ (2 * k) * B / (W.card : ℝ) ^ (2 * k) :=
      (le_div_iff₀ (pow_pos hpos _)).mpr (by rw [mul_comm]; exact h1)
    calc a ≤ M ^ (2 * k) * B / (W.card : ℝ) ^ (2 * k) := hdiv
      _ = B * (M / (W.card : ℝ)) ^ (2 * k) := by rw [div_pow]; ring
  have hr : (M / (W.card : ℝ)) ^ 2 < 1 := by
    have h0 : 0 ≤ M / (W.card : ℝ) := div_nonneg hM (le_of_lt hpos)
    have h1 : M / (W.card : ℝ) < 1 := (div_lt_one hpos).mpr hcard
    nlinarith
  have hpow : Filter.Tendsto (fun k : ℕ => ((M / (W.card : ℝ)) ^ 2) ^ k)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg (div_nonneg hM (le_of_lt hpos)) 2) hr
  have hlim : Filter.Tendsto (fun k : ℕ => B * ((M / (W.card : ℝ)) ^ 2) ^ k)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have hle : a ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun k => by simpa [pow_mul] using hkey k)
  exact le_antisymm hle ha_nonneg

/-! ## The `L²` spectral bound, weak class -/

theorem XSrp_L2_le_weak {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) (j : ℕ) :
    (∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2) ≤ M ^ (2 * j) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  rw [parseval_XSrp hℓ S hC hΦm hΦb j, normSq_resolution hℓ hC hΦm hΦb, Finset.mul_sum]
  refine Finset.sum_le_sum fun W hW => ?_
  have hI : 0 ≤ ∫ x in abox n ℓ, (Work.BoseFixB2.jointProj ℓ W Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  by_cases hcard : (W.card : ℝ) ≤ M
  · have h1 : sectorCount S W ≤ M := le_trans (sectorCount_le_card S W) hcard
    have h2 : (sectorCount S W) ^ (2 * j) ≤ M ^ (2 * j) :=
      pow_le_pow_left₀ (sectorCount_nonneg S W) h1 _
    exact mul_le_mul_of_nonneg_right h2 hI
  · have hlt : M < (W.card : ℝ) := not_le.mp hcard
    rw [jointProj_vanish_weak hℓ hC hΦm hΦb hM hmom (Finset.mem_powerset.mp hW) hlt]
    simp

theorem XSpow_L2_le_weak {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin n)) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) {M : ℝ} (hM : 0 ≤ M)
    (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ) (j : ℕ) :
    (∫ x in abox n ℓ, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2)
      ≤ M ^ (2 * j) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
  have hpt : ∀ x : X n, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2
      = (XSrp ℓ S j Φ x) ^ 2 := by
    intro x
    rw [congrFun (XSpow_ofReal ℓ S j Φ) x, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_ofReal, sq]
  rw [show (∫ x in abox n ℓ, ‖XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ)) x‖ ^ 2)
      = ∫ x in abox n ℓ, (XSrp ℓ S j Φ x) ^ 2 from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact XSrp_L2_le_weak hℓ S hC hΦm hΦb hM hmom j


end Weak

/-- **The width form of the sector spectral bound, for measurable bounded states** (the weak
twin of `Work.BoseBoxFock.sector_XSpow_width_holds_kf`). -/
theorem sector_XSpow_width_holds_weak {n : ℕ} (ℓ : ℝ) (hℓ : 0 < ℓ) (S : Finset (Fin n))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦm : Measurable Φ)
    (hΦb : ∃ C : ℝ, ∀ x, |Φ x| ≤ C)
    {M : ℝ} (hM : 0 ≤ M) (hmom : Work.BoseBox.SpectralNPlusLe ℓ M Φ)
    {m : ℕ} [NeZero m] {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x)) (j : ℕ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ‖Work.BoseBoxFock.XSpow ℓ S j
          (Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      ≤ M ^ (2 * j) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  obtain ⟨C, hΦb⟩ := hΦb
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hΦb' : ∀ x, |Φ x| ≤ max C 0 := fun x => le_trans (hΦb x) (le_max_left _ _)
  have hΨm : Measurable (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hΦm
  have hΨbd : ∀ᵐ x ∂(MeasureTheory.volume : Measure (Submission.BoseGases.X n)),
      ‖((Φ x : ℝ) : ℂ)‖ ≤ max C 0 :=
    Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hΦb' x
  have hΨmem : MeasureTheory.MemLp
      (fun x : Submission.BoseGases.X n => ((Φ x : ℝ) : ℂ)) ⊤ :=
    MeasureTheory.memLp_top_of_bound hΨm.aestronglyMeasurable (max C 0) hΨbd
  have hcomm := Kf.XSpow_slotExact_comm_box (ℓ := ℓ) hℓ he hbdd hsupp hc S j hΨmem
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
        ‖Work.BoseBoxFock.XSpow ℓ S j
          (Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.BoseBoxFock.slotExact e S
            (Work.BoseBoxFock.XSpow ℓ S j (fun x => ((Φ x : ℝ) : ℂ))) x‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hcomm] with x hx
    rw [hx]
  rw [h1]
  refine le_trans ?_ (Weak.XSpow_L2_le_weak hℓ S hC0 hΦm hΦb' hM hmom j)
  obtain ⟨hXaesm, CX, hXbdd⟩ :=
    Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ S
      hΨm.aestronglyMeasurable ⟨max C 0, hΨbd⟩ j
  exact Kf.slotExact_contract_box (ℓ := ℓ) hℓ he hbdd hsupp S
    (MeasureTheory.memLp_top_of_bound hXaesm CX hXbdd)

end Work.BoseBoxFock
