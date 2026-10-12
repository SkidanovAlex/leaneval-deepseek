import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.lowProviderFinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.lowProviderBand` — the bad-set interface of `lowCountBound`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

The residual `OffGoodCrudeLow` of `Submission/Work/BoseFixB1B/lowProviderDefs.lean` (FS `eq:badset`
off the good set) is split here into its two geometrically distinct parts:

* the **far set** `cubeᶜ`, where the localised kernels vanish identically and hence
  `sbWord = sbKin ≥ 0` — this part is *proved*, unconditionally, below
  (`piece_far` inside `offGoodCrudeLow_of_band`);
* the **bad band** `bandSet ∖ goodSet`, the genuine input — FS handle it by applying
  `thm:smallbox` at the *doubled* chemical potential `4μ` (`final_v2.tex` l.4081–4100), where the
  resulting bound `H_B(4μ) ≥ −Cμ²a∫χ_B² − Cμa` is **particle-number free**.

So `OffGoodCrudeLow` is equivalent to its band restriction `BandCrudeLow` (the statement
`Work.BoseFixB1S.BandPerBoxCrudeB1` targets on the band).

## TRAP — do not feed the band bound from the count window

`Submission/Work/BoseFixB1S/BandPerBoxCrudeB1.lean` derives its band bound from the `n`-linear fibre
bound plus the **count window** `n ≤ Cμℓ³` (`Work.BoseFixB1S.LowCountWindowB1` = this very node).
That route is **circular** when used to discharge `BandCrudeLow` here.  The band bound must come
from FS's `thm:smallbox` at `4μ` instead (the "condensed arm" of the per-box chapter,
`Work.BoseFixR.SlabCondensedHalf` / `Work.BoseFixB1B.PerSectorBoundGCondensed`).

Everything in this file is `sorry`-free and rests only on `propext`, `Classical.choice`,
`Quot.sound`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The sliding geometry -/

/-- `interiorSet ⊆ goodSet` (`μ^{-1/3} ≤ 2μ^{-1/3}`). -/
lemma interiorSet_subset_goodSet' {ℓ d μ : ℝ} (hμ : 0 < μ) :
    interiorSet ℓ d μ ⊆ goodSet ℓ d μ := by
  intro u hu
  simp only [interiorSet, goodSet, Set.mem_setOf_eq] at hu ⊢
  intro j
  have hδ : 0 ≤ μ ^ (-1 / 3 : ℝ) := Real.rpow_nonneg hμ.le _
  linarith [hu j]

/-- **`goodSetᶜ ⊆ farSet ∪ bandSet`**: outside the good set either some face-coordinate exceeds the
outer half-side (the far set, where the kernels vanish) or the point lies in the bad band. -/
lemma goodSet_compl_subset_farSet_union_bandSet {ℓ d μ : ℝ} (hμ : 0 < μ) :
    (goodSet ℓ d μ)ᶜ ⊆ farSet ℓ d μ ∪ bandSet ℓ d μ := by
  intro u hu
  by_cases hfar : u ∈ farSet ℓ d μ
  · exact Or.inl hfar
  · refine Or.inr ?_
    have hall : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) := by
      intro j
      by_contra hcon
      exact hfar ⟨j, lt_of_not_ge hcon⟩
    simp only [goodSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall] at hu
    obtain ⟨j, hj⟩ := hu
    have hδ : 0 ≤ μ ^ (-1 / 3 : ℝ) := Real.rpow_nonneg hμ.le _
    have hle : (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)
        ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ) := by linarith
    exact ⟨⟨j, le_trans hle (le_of_lt (not_le.mp hj))⟩, hall⟩

/-- `goodSetᶜ ∩ cube ⊆ bandSet`. -/
lemma goodSet_compl_inter_cube_subset_bandSet {ℓ d μ : ℝ} (hμ : 0 < μ) :
    (goodSet ℓ d μ)ᶜ ∩ cube ℓ d ⊆ bandSet ℓ d μ := by
  intro u hu
  rcases goodSet_compl_subset_farSet_union_bandSet hμ hu.1 with hfar | hband
  · exfalso
    obtain ⟨j, hj⟩ := hfar
    exact absurd (hu.2 j) (not_le.mpr hj)
  · exact hband

/-! ## 2. The bad-set interface -/

/-- **The band-restricted crude per-box bound** (for low states of positive norm): FS `eq:badset`
on `bandSet ∖ goodSet` only.  This is the shape `Work.BoseFixB1S.BandPerBoxCrudeB1` targets, except
that it must be *proved* FS's way (`thm:smallbox` at `4μ`) and not from the count window. -/
def BandCrudeLow (v : E3 → ℝ) (h : ScatSol v) (J : ℝ) (C : ℝ) (ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ →
    J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      0 < normB v μ n (Φ : X n → ℝ) →
      IsLowB v h J μ n Φ →
      ∀ u : E3,
        u ∈ bandSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        u ∉ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        -(C * (μ ^ 2 * (a v)
                * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              + μ * (a v)))
            * normB v μ n (Φ : X n → ℝ)
          ≤ sbWord h μ u (Φ : X n → ℝ)

/-- **`OffGoodCrudeLow` from `BandCrudeLow`**: off the good set the far part is free (there
`sbWord = sbKin ≥ 0`) and the cube part lies in the band. -/
theorem offGoodCrudeLow_of_band {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {J C ε₀ : ℝ} (hC : 0 ≤ C)
    (hband : BandCrudeLow v h J C ε₀) :
    OffGoodCrudeLow v h J C ε₀ := by
  intro μ hAdm hJK n Φ hN hlow u hu
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ha : 0 ≤ _root_.BoseGases.a v := (Work.BoseFixB1.adm_a_pos hAdm).le
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hXnn : 0 ≤ μ ^ 2 * (a v)
      * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
      + μ * (a v) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _))
      (mul_nonneg hμ.le ha)
  by_cases hcube : u ∈ cube (sideAt μ (a v)) (paramsAt μ (a v)).d
  · exact hband μ hAdm hJK n Φ hN hlow u
      (goodSet_compl_inter_cube_subset_bandSet hμ ⟨hu, hcube⟩) hu
  · -- the far set: the localised potential vanishes and the kinetic word is nonnegative
    have hfar : u ∈ farSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ :=
      cube_compl_subset_farSet hcube
    have hz : sbPot h μ u (Φ : X n → ℝ) = 0 :=
      sbPot_eq_zero_of_mem_farSet hℓ hd hfar (Φ : X n → ℝ)
    have hword : sbWord h μ u (Φ : X n → ℝ) = sbKin (v := v) μ (paramsAt μ (a v)).M u
        (Φ : X n → ℝ) := by
      rw [sbWord_eq_add, hz, add_zero]
    have hnn : 0 ≤ sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ) :=
      sbKin_nonneg_local hAdm u (Φ : X n → ℝ)
    rw [hword]
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg hC hXnn)) (Work.BoseFixB1.normB_nonneg _)) hnn

/-! ## 3. The frozen node from the minimised residual -/

/-- **The frozen node's conclusion from `{FlatBranchLow, BandCrudeLow}`** — the minimal residual:
FS `thm:smallbox` at the sliding box in the flat branch for low states, and FS `eq:badset` on the
bad band only. -/
theorem lowCountBound_of_flatBand {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) {J : ℝ}
    (hJ : Work.UBB.lhyC ≤ J) (hflat : FlatBranchLow v h R J)
    (hband : ∃ εf Cbad : ℝ, 0 < εf ∧ 0 ≤ Cbad ∧ BandCrudeLow v h J Cbad εf) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        J ≤ (paramsAt μ (a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
          0 < normB v μ n (Φ : X n → ℝ) →
          IsLowB v h J μ n Φ →
            (n : ℝ) ≤ C * μ * (sideAt μ (a v)) ^ 3 := by
  obtain ⟨εf, Cbad, hεf, hCbad, hb⟩ := hband
  exact lowCountBound_of_residual h hv hv1 hvrad hR hv_supp hav hJ hflat
    ⟨εf, Cbad, hεf, hCbad, offGoodCrudeLow_of_band h hv hvrad hCbad hb⟩

end Work.BoseFixB1B
