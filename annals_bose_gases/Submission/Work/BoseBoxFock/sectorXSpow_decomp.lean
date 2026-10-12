import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotExact_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sectorXSpow_decomp` — the joint-sector decomposition of an `S`-sector

Step (1) of the `sector_XSpow` chain (`FINDING_sector_XSpow_le.md`, `…_s11.md`): the mode-sector
projection `slotExact e S` of a box state `Φ` splits over the joint `n₊`-sectors
`E_W Φ = ∏_{i∈W} Qᵢ ∏_{j∉W} Pⱼ Φ` of the excitation number:

    slotExact e S (↑Φ) =ᵐ Σ_{W ⊆ {0,…,n−1}} slotExact e S (↑(E_W Φ))    on `abox n ℓ`.

Nothing analytic is needed beyond the two ingredients

* `Work.BoseFixB2.Sector.jointProj_resolution` — the resolution of the identity
  `Σ_{W ⊆ {0,…,n−1}} E_W Φ = Φ` as functions (it uses only `Pᵢ + Qᵢ = 1` at every slot, hence
  **no** continuity is required, although the hypothesis is carried in the signature);
* `Work.BoseBoxFock.slotExact_finsetSum_ae` — the `S`-sector is finitely additive in the state a.e.
  on the box, which needs the summands to be `L^∞`.

The `L^∞` of the joint sectors `E_W Φ` (`MemLp ⊤`) is supplied by
`jointProj_memLp_top` of `sector_XSpow_le`; that module cannot be imported here (its cone
re-declares `exists_ae_bound_of_memLp_top` of `_helpers`, a duplicate-declaration landmine), so the
short proof is reconstructed below: a global sup-bound (valid on *all* of `Ω^n`, unlike
`aP_abs_le`) propagates through the iterated slot operators with a factor `2^k`, one factor `2` per
slot carrying `Q = 1 − P`.

The two facts are combined by turning the real identity into an identity of `ℂ`-valued functions
(`Complex.ofReal_sum`) and transporting `slotExact e S` along it.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-! ## The `L^∞` regularity of the joint sectors

A self-contained copy of the three helpers of `sectorXSpow_membership` (there `private`, and the
public version lives in `sector_XSpow_le`, whose import cone cannot be combined with this one).
-/

/-- The global sup-bound for the slot mean: if `|Ψ| ≤ B` everywhere then `|Pᵢ Ψ| ≤ B`
everywhere (in particular outside the box, where a pointwise box statement is unavailable). -/
lemma sectorXSpow_decomp_aP_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΨ : ∀ x, |Ψ x| ≤ B) :
    ∀ x, |Submission.BoseGases.aP ℓ i Ψ x| ≤ B := by
  intro x
  haveI : IsFiniteMeasure
      ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have h1 : ‖∫ y, Ψ (Function.update x i y)
        ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))‖ ≤ B * ℓ ^ 3 := by
    have hb : ∀ᵐ y ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)),
        ‖Ψ (Function.update x i y)‖ ≤ B :=
      Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΨ _
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))
      (f := fun y => Ψ (Function.update x i y)) (C := B) hb
    rwa [Measure.real, Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)] at h
  unfold Submission.BoseGases.aP
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ℓ ^ 3)]
  calc (1 / ℓ ^ 3) * |∫ y, Ψ (Function.update x i y)
        ∂((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ))|
      ≤ (1 / ℓ ^ 3) * (B * ℓ ^ 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.norm_eq_abs]; exact h1
    _ = B := by field_simp

/-- The iterated slot operators preserve a global sup-bound (with a factor `2^k`). -/
lemma sectorXSpow_decomp_blockOp_abs_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (W : Finset ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΦB : ∀ x, |Φ x| ≤ B) :
    ∀ k, k ≤ n → ∀ x, |Work.BoseFixB2.blockOp ℓ W k Φ x| ≤ 2 ^ k * B := by
  intro k
  induction k with
  | zero => intro _ x; simpa using hΦB x
  | succ k ih =>
      intro hk x
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hprev : ∀ y, |Work.BoseFixB2.blockOp ℓ W k Φ y| ≤ 2 ^ k * B :=
        ih (Nat.le_of_lt hkn)
      have h2k : 0 ≤ (2 : ℝ) ^ k * B := mul_nonneg (by positivity) hB
      rw [Work.BoseFixB2.blockOp_succ W hkn Φ]
      by_cases hmem : k ∈ W
      · rw [if_pos hmem]
        have h1 : |Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ W k Φ) x|
            ≤ 2 ^ k * B := sectorXSpow_decomp_aP_abs_le hℓ ⟨k, hkn⟩ h2k hprev x
        rw [show Submission.BoseGases.aQ ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ W k Φ) x
            = Work.BoseFixB2.blockOp ℓ W k Φ x
              - Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ W k Φ) x from rfl,
          abs_le]
        have h0 := abs_le.mp (hprev x)
        have h0' := abs_le.mp h1
        rw [pow_succ]
        constructor <;> linarith
      · rw [if_neg hmem]
        have h1 : |Submission.BoseGases.aP ℓ ⟨k, hkn⟩ (Work.BoseFixB2.blockOp ℓ W k Φ) x|
            ≤ 2 ^ k * B := sectorXSpow_decomp_aP_abs_le hℓ ⟨k, hkn⟩ h2k hprev x
        refine le_trans h1 ?_
        rw [pow_succ]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ k) hB]

/-- **The joint sector is bounded everywhere**, hence `MemLp ⊤`. -/
lemma sectorXSpow_decomp_jointProj_memLp_top {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (W : Finset ℕ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ) :
    MeasureTheory.MemLp (fun x => ((Work.BoseFixB2.jointProj ℓ W Φ x : ℝ) : ℂ)) ⊤ := by
  have hcs : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact n hℓ)
      (isClosed_tsupport Φ) hΦc
  obtain ⟨B, hB⟩ := hΦ.bounded_above_of_compact_support hcs
  have hB' : 0 ≤ max B 0 := le_max_right _ _
  have hΦB : ∀ x, |Φ x| ≤ max B 0 := fun x => le_trans (by simpa using hB x) (le_max_left _ _)
  refine MeasureTheory.memLp_top_of_bound ?_ (2 ^ n * max B 0)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact (Complex.continuous_ofReal.comp
      (Work.BoseFixB2.Sector.jointProj_continuous hℓ W hΦ)).aestronglyMeasurable
  · rw [Complex.norm_real, Real.norm_eq_abs, Work.BoseFixB2.jointProj_eq_blockOp ℓ W Φ]
    exact sectorXSpow_decomp_blockOp_abs_le (ℓ := ℓ) hℓ W hB' hΦB n le_rfl x

/-! ## The decomposition -/

theorem sectorXSpow_decomp (ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hΦc : tsupport Φ ⊆ Submission.BoseGases.abox n ℓ)
    {m : ℕ} [NeZero m] {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) :
    (fun x => Work.BoseBoxFock.slotExact e S (fun x => ((Φ x : ℝ) : ℂ)) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => ∑ W ∈ (Finset.range n).powerset,
        Work.BoseBoxFock.slotExact e S
          (fun y => ((Work.BoseFixB2.jointProj ℓ W Φ y : ℝ) : ℂ)) x) := by
  classical
  -- the resolution of the identity by the joint sectors, as real functions on `X n`
  have hres : (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ) = Φ :=
    Work.BoseFixB2.Sector.jointProj_resolution hℓ Φ hΦ
  -- the two states agree as complex-valued functions
  have hstate : (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ))
      = (fun y : Submission.BoseGases.X n => ∑ W ∈ (Finset.range n).powerset,
          ((Work.BoseFixB2.jointProj ℓ W Φ y : ℝ) : ℂ)) := by
    funext y
    have hy : (∑ W ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ W Φ y) = Φ y := by
      have h := congrFun hres y
      simpa only [Finset.sum_apply] using h
    rw [← hy, Complex.ofReal_sum]
  -- hence the `S`-sectors of the two states agree as functions
  have hfun : Work.BoseBoxFock.slotExact e S (fun y => ((Φ y : ℝ) : ℂ))
      = Work.BoseBoxFock.slotExact e S (fun y => ∑ W ∈ (Finset.range n).powerset,
          ((Work.BoseFixB2.jointProj ℓ W Φ y : ℝ) : ℂ)) :=
    congrArg (Work.BoseBoxFock.slotExact e S) hstate
  -- additivity of the `S`-sector in the state, a.e. on the box
  have hsplit := Work.BoseBoxFock.slotExact_finsetSum_ae (ℓ := ℓ) hbdd hsupp S
      ((Finset.range n).powerset)
      (Θ := fun W => fun y : Submission.BoseGases.X n =>
        ((Work.BoseFixB2.jointProj ℓ W Φ y : ℝ) : ℂ))
      (fun W _ => sectorXSpow_decomp_jointProj_memLp_top hℓ W hΦ hΦc)
  have h1 : (fun x => Work.BoseBoxFock.slotExact e S (fun y => ((Φ y : ℝ) : ℂ)) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin n → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox n ℓ)]
      (fun x => Work.BoseBoxFock.slotExact e S
        (fun y => ∑ W ∈ (Finset.range n).powerset,
          ((Work.BoseFixB2.jointProj ℓ W Φ y : ℝ) : ℂ)) x) :=
    Filter.Eventually.of_forall (fun x => congrFun hfun x)
  exact h1.trans hsplit

end Work.BoseBoxFock
