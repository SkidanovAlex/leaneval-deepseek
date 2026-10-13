/-
# `H6Row6/RowFKfAux` — prices for the `(f,K)`-coefficient rows

Auxiliary estimates for `Work.FTS.StrongPersist.H6Row6.rowFKf`: the pointwise and `L²` prices
of the radial slot `D_z^b (FK f)` of the angular moment, the `L²` price of an arbitrary
`ℋ⁶`-slot against any leaf weight, and the pointwise/slice prices of the low-order slots of
the datum.  All of them are assembled from the proved assets of `Npair6BWork/FkAux`
(`fkDzdIterSqLe`, `fk_radial_shift`), `OpenPkg/ProdOpen` (`sliceAvg_le`, `sliceAng_le`,
`PwAny`), `TransportS` (`sup_dz_le_hk`, `n5_FK_abs_le`) and the level-six slot dominations.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-- Almost every `θ ∈ Iθ` lies in the open interval. -/
private theorem ae_Ioo_Iθ_row :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## §1. Monotonicity of the `ℋᵏ`-integrand in the level -/

/-- Every slot occurring at level `m` also occurs at level `m' ≥ m`. -/
theorem HkIntegrand_mono_row {α : ℝ} {m m' : ℕ} (h : m ≤ m') (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α m' g z θ := by
  unfold Work.Spaces.HkIntegrand
  have hpure : (∑ i ∈ Finset.range (m + 1), (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (∑ i ∈ Finset.range (m' + 1), (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => sq_nonneg _)
  have hterm : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ (if 1 ≤ i ∧ i + j ≤ m' then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
    · rw [if_neg hc]
      split_ifs with hp
      · exact sq_nonneg _
      · exact le_rfl
  have hin : ∀ i : ℕ,
      (∑ j ∈ Finset.range (m + 1), (if 1 ≤ i ∧ i + j ≤ m then
          (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ j ∈ Finset.range (m' + 1), (if 1 ≤ i ∧ i + j ≤ m' then
          (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    intro i
    refine le_trans (Finset.sum_le_sum fun j _ => hterm i j) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro j _ _
    split_ifs with hp
    · exact sq_nonneg _
    · exact le_rfl
  have hmix : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (∑ i ∈ Finset.range (m' + 1), ∑ j ∈ Finset.range (m' + 1),
        (if 1 ≤ i ∧ i + j ≤ m' then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)) := by
    refine le_trans (Finset.sum_le_sum fun i _ => hin i) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro i _ _
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs with hp
    · exact sq_nonneg _
    · exact le_rfl
  exact add_le_add hpure hmix

/-- `η ≤ γ`, so on the open interval `σ^{-η} ≤ σ^{-γ}`. -/
theorem rpow_eta_le_gam_row {α : ℝ} (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- **The leaf weights are dominated by the slot weight of the `ℋ⁶`-integrand**, for an
arbitrary slot of the compatible type: a slot with an angular derivative accepts any leaf
weight, a `D_z`-only slot accepts any weight other than the `γ`-leaf. -/
theorem slot_dom_row {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : ℝ → ℝ → ℝ} {j i n : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (htyp : 1 ≤ i ∨ ρ ≠ Work.FTS.TransportS.leafGam α) (hij : i + j ≤ n) :
    ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ := by
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])).le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hWhzWm := Work.FTS.H2.Whz_Wm_sq α hα z θ hθI
  have hWm : ρ z θ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rcases hρ with h | h | ⟨-, h⟩
    · subst h
      exact mul_le_mul_of_nonneg_left (rpow_eta_le_gam_row hα hθ) (sq_nonneg _)
    · subst h
      refine le_mul_of_one_le_right (sq_nonneg _) ?_
      exact Work.FTS.TransportS.one_le_rpow_neg (by rw [Work.Spaces.gam]; linarith) hθ
    · subst h; exact le_rfl
  by_cases hi : 1 ≤ i
  · -- a slot with an angular derivative: use the `γ`-weight
    have h1 : ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2
        ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            * (Work.Spaces.mixed j i f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hWm (sq_nonneg _)
    have h2 : ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [← hWhzWm.2, Work.FTS.H2.Wm_eq]
      ring
    exact (h1.trans (le_of_eq h2)).trans
      (Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ i j hi hij)
  · -- a `D_z`-only slot: `ρ` is the `η`- or the `σ`-free leaf
    have hi0 : i = 0 := by omega
    have hne : ρ ≠ Work.FTS.TransportS.leafGam α := by
      rcases htyp with h | h
      · omega
      · exact h
    have hWhz : ρ z θ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rcases hρ with h | h | ⟨ha, h⟩
      · subst h; exact le_rfl
      · subst h
        refine le_mul_of_one_le_right (sq_nonneg _) ?_
        exact Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
      · exact absurd h hne
    subst hi0
    simp only [Work.Spaces.mixed_zero_right]
    have h1 : ρ z θ * (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            * (Work.Spaces.DzIter j f z θ) ^ 2 :=
      mul_le_mul_of_nonneg_right hWhz (sq_nonneg _)
    have h2 : ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        * (Work.Spaces.DzIter j f z θ) ^ 2
        = (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [← hWhzWm.1, Work.FTS.H2.Whz_eq]
      ring
    exact (h1.trans (le_of_eq h2)).trans
      (Work.Spaces.sq_le_HkIntegrand_z α n f z θ j (by omega))

/-- **The `L²` price of an arbitrary slot against a weight of leaf type.** -/
theorem slotL2_row {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f : ℝ → ℝ → ℝ} {j i m : ℕ}
    (hmem : Work.Spaces.HkMem α m f) (hα : 0 < α)
    (htyp : 1 ≤ i ∨ ρ ≠ Work.FTS.TransportS.leafGam α) (hij : i + j ≤ m) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2) ≤ Work.Spaces.HkSq α m f := by
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · filter_upwards [ae_Ioo_Iθ_row] with θ hθ
      exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [ae_Ioo_Iθ_row] with θ hθ
      exact slot_dom_row hα hρ hθ htyp hij
  have hmain : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * (Work.Spaces.mixed j i f z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α m f z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hmem.2 ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [ae_Ioo_Iθ_row] with θ hθ
      exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ z
        ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
      exact hslice z hz
  rw [Work.Spaces.HkSq]
  exact hmain

/-! ## §3. Prices of the radial slots `D_z^k (FK f)` -/

/-- The one-variable and two-variable iterates agree on radial functions. -/
theorem dzdIter_fk_eq {f : ℝ → ℝ → ℝ} {k : ℕ} {z θ : ℝ} :
    Work.Spaces.DzIter k (fun z _ => Work.Construction.FK f z) z θ
      = Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z :=
  Work.Elliptic.DzIter_rad _ k z θ

/-- **Pointwise price of the radial slots of the angular moment** (a.e. in `z`). -/
theorem fkPt_row : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f → ∀ k : ℕ, k ≤ 6 →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ C * Work.Spaces.HkSq α (k + 1) f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨C, hCpos, ?_⟩
  intro α f hα hO hmem6 hmem7 k hk
  filter_upwards [hC hα hO hmem6 hmem7 k hk] with z hz
  simpa only [dzdIter_fk_eq] using hz

/-- **The angular moment is bounded by `C·M` pointwise on `(0,∞)`.** -/
theorem fkAbs_row : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ∀ z : ℝ, 0 < z → |Work.Construction.FK f z| ≤ C * M := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  refine ⟨4 * Real.sqrt C₀, by positivity, ?_⟩
  intro α hαmem f M hQ h7 hM z hz
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hO : Work.FTS.EllipticEst.SmoothOpen f := hQ.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hQ.2
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.IPGen.HkMem_mono_le hO 4 (by norm_num) hmem6
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hO.continuousOn hz
  have hsqint : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
    have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
      one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
    refine MeasureTheory.Integrable.mono' (hmem6.1 z (Set.mem_Ici.mpr hz.le))
      (haesm.pow 2) ?_
    filter_upwards [ae_Ioo_Iθ_row] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hWhzWm := Work.FTS.H2.Whz_Wm_sq α hα z θ ⟨hθ.1.le, hθ.2.le⟩
    have hsin1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    calc (f z θ) ^ 2 = 1 * (f z θ) ^ 2 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hw1 (sq_nonneg _)
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (f z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact le_mul_of_one_le_right (sq_nonneg _) hsin1
      _ = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            * (f z θ) ^ 2 := by ring
      _ = (Work.FTS.H2.Whz z θ) ^ 2 * (f z θ) ^ 2 := by rw [hWhzWm.1]
      _ = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.H2.Whz_eq]; ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
          have hh := Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ 0 (by norm_num)
          simpa only [Work.Spaces.DzIter_zero] using hh
  have hslice := hC₀ α f 0 hα hα1 hO hmem4 (by norm_num) z hz
  have hFK := Work.FTS.Nonlinear.Pieces.Rl1.n5_FK_abs_le hz hsqint haesm
  have hXn : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
  have h1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      ≤ Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hslice
  have h2 : Real.sqrt (C₀ * Work.Spaces.HkSq α 4 f)
      = Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hC₀pos.le, hXn]
  calc |Work.Construction.FK f z|
      ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) := hFK
    _ ≤ 4 * (Real.sqrt C₀ * Work.FTS.Nonlin.Xn α f) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 4 * (Real.sqrt C₀ * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM
          (Real.sqrt_nonneg _)) (by norm_num)
    _ = (4 * Real.sqrt C₀) * M := by ring

/-! ## §4. Auxiliary: the `sin²θ`-shift of the `D_θ`-iterates -/

/-- `D_θ`-iterates commute with the shift `f ↦ D_θf`. -/
theorem dthIter_succ_shift (a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter a (Work.Spaces.Dth f) = Work.Spaces.DthIter (a + 1) f := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, ← Work.Spaces.DthIter_succ]

end

end Work.FTS.StrongPersist.H6Row6

