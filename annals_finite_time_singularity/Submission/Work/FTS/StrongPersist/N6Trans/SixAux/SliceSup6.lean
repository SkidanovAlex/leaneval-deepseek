/-
# `SliceSup6`: the first rung of the level-six pointwise ladder

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` with honest `Work.Spaces.HkMem α 6 f`, and
for `b ≤ 5`, the `θ`-slice of `D_z^b f` is bounded pointwise in `θ` by `201/(γ-1)` times the
angular integral of the `ℋ⁶`-integrand *at the same radius*:

  `|D_z^b f z θ|² ≤ C / (γ - 1) · ∫_{Iθ} HkIntegrand α 6 f z θ'`   (`b ≤ 5`, `z > 0`, `0 < θ < π/2`).

This is the level-six, `b ≤ 5` instance of the slicewise Agmon inequality
`Work.H2.T1Q.SliceSupOpen`, whose two `θ`-integrals are dominated by
`∫_{Iθ} HkIntegrand α 6 f z θ` through the two level-six slot dominations
(`Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6` in its `a = 0` instance for the mean term,
and `Work.Spaces.sq_le_HkIntegrand_mixed` at `(j,i) = (b,1)` for the Dirichlet term, the latter
combined with the weight identity `Work.FTS.TransportS.SlotT2.supOpen_pth_weight` and `w ≥ 1`).

It is the first rung of the level-six `L^∞` ladder, and is the verbatim level-six analogue of
the *proved* `Work.FTS.NonlinRows.Rl1.angSupHk` (which is the `b = 0`, `ℋ⁴` case).  What still
separates it from `Work.FTS.StrongPersist.N6Trans.SixAux.supDzSix` is the removal of the *fixed
radius* from the right-hand side — a uniform-in-`z` bound of that slice integral, which is the
two-variable pairing problem described in `NOTES_supDzSix.md`; it cannot be reached by the
one-variable Agmon calculus alone (the slice integral in question is genuinely unbounded in `z`,
see §2 of the notes).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.H2.T1Q.SliceSupOpen
import Submission.Work.FTS.StrongPersist.N6.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1. The pointwise domination of the two slice integrands -/

/-- **The Dirichlet-slice domination at level six.**  For `b ≤ 5` and `z > 0`, `0 < θ < π/2`,

  `(∂_θD_z^bf z θ)² · sin(2θ)^{2-γ} ≤ HkIntegrand α 6 f z θ`.

The proof multiplies by `1 ≤ w(z)²`, uses the weight identity
`(∂_θD_z^bf z θ)² w² sin(2θ)^{2-γ} = (mixed b 1 f z θ · Wt α z θ)²`
(`Work.FTS.TransportS.SlotT2.supOpen_pth_weight`) and then the `(b,1)`-summand domination
`Work.Spaces.sq_le_HkIntegrand_mixed` (`1 + b ≤ 6`). -/
theorem pth_sq_sin_le_Hk6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hα : 0 < α) (hα1 : α ≤ 1) {b : ℕ} (hb : b ≤ 5)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have hsin : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))) _
  calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.w z) ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hsin) hw2
    _ = (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by ring
    _ = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        Work.FTS.TransportS.SlotT2.supOpen_pth_weight hF hα hα1 b hz hθ
    _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 b le_rfl (by omega)

/-! ## §2. Integrability of the two angular slices -/

/-- The `θ`-slice of the pure `D_z`-slot `D_z^bf`, `b ≤ 6`, is integrable, given `HkMem α 6 f`. -/
theorem integrableOn_sq6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) {b : ℕ}
    (hb : b ≤ 6) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hkey : Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine Integrable.mono' ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
      ((((hF.DzIter b).curry_θ hz).continuousOn.aestronglyMeasurable
        measurableSet_Ioo).pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα f b 0 (by omega) hz hθ.1 hθ.2
  show Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hkey

/-- The weighted angular slice `(∂_θD_z^bf z ·)² sin(2·)^{2-γ}`, `b ≤ 5`, is integrable, given
`HkMem α 6 f`. -/
theorem integrableOn_pth_weight6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) {b : ℕ}
    (hb : b ≤ 5) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := Work.FTS.TransportS.SlotT2.supOpen_w_sq_ne_zero hz
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hderiv_cont : ContinuousOn
      (fun θ => deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hF.DzIter b).curry_θ hz).of_le
      (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hsincont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hkey : Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine Integrable.mono'
      (((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self).const_mul
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (hderiv_cont.pow 2).mul hsincont
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
      calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = ((Work.Spaces.w z) ^ 2)⁻¹
              * (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            rw [← Work.FTS.TransportS.SlotT2.supOpen_pth_weight hF hα hα1 b hz hθ]
            rw [show ((Work.Spaces.w z) ^ 2)⁻¹
                  * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                      * (Work.Spaces.w z) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2)
                    * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) from by ring]
            rw [inv_mul_cancel₀ hw2, one_mul]
        _ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_left
              (Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 b le_rfl (by omega))
              (inv_nonneg.mpr (sq_nonneg _))
  show Integrable (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hkey

/-! ## §3. The two block estimates: the slice integrals at the same radius -/

/-- The mean block at level six: `∫_θ (D_z^bf z θ)² ≤ ∫_θ HkIntegrand α 6 f z θ` for `b ≤ 6`. -/
theorem block_z6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hmem : Work.Spaces.HkMem α 6 f)
    {b : ℕ} (hb : b ≤ 6) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hIoo : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.DzIter b f z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq
  have hIoo' : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Spaces.HkIntegrand α 6 f z θ :=
    MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq
  rw [hIoo, hIoo']
  refine MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => sq_nonneg _))
    ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_))
  exact Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα f b 0 (by omega) hz hθ.1 hθ.2

/-- The Dirichlet block at level six: `∫_θ (∂_θD_z^bf z θ)² sin(2θ)^{2-γ} ≤ ∫_θ HkIntegrand`
for `b ≤ 5`. -/
theorem block_pth6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α 6 f) {b : ℕ} (hb : b ≤ 5)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hIoo : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq
  have hIoo' : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Spaces.HkIntegrand α 6 f z θ :=
    MeasureTheory.setIntegral_congr_set Work.FTS.TransportS.SlotT2.supOpen_Iθ_ae_eq
  have hintp : IntegrableOn (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (integrableOn_pth_weight6 hα hα1 hF hmem hb hz).mono_set Set.Ioo_subset_Icc_self
  rw [hIoo, hIoo']
  refine MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))) _)))
    ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      pth_sq_sin_le_Hk6 hF hα hα1 hb hz hθ))

/-! ## §4. The first rung: the slicewise bound at level six -/

/-- **The level-six slicewise Agmon bound (`b ≤ 5`).**  For `f` of class `SmoothOpen` with
honest `HkMem α 6 f`, every pure `D_z`-derivative of order `≤ 5` is bounded on each angular
slice by `201/(γ-1)` times the angular integral of the `ℋ⁶`-integrand at the same radius. -/
theorem supTheta_slice6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ b : ℕ, b ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ C / (Work.Spaces.gam α - 1) * ∫ θ' in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 f z θ' := by
  refine ⟨201, by norm_num, ?_⟩
  intro α f hα hα1 hF hmem b hb z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hHknn : 0 ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ' :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ' _ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ')
  have hslice : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.DzIter b f z θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hF.DzIter b).curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have hint2 : IntegrableOn (fun θ' => (Work.Spaces.DzIter b f z θ') ^ 2) Work.Spaces.Iθ :=
    integrableOn_sq6 hα hF hmem (by omega) hz
  have hintp : IntegrableOn (fun θ' => (deriv (fun θ'' => Work.Spaces.DzIter b f z θ'') θ') ^ 2
      * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth] using integrableOn_pth_weight6 hα hα1 hF hmem hb hz
  have hag := Work.H2.T1Q.SliceSupOpen α (fun θ' => Work.Spaces.DzIter b f z θ') hα hα1
    hslice hint2 hintp θ hθ
  have hz1 := block_z6 hα hmem (b := b) (by omega) hz
  have hz2 := block_pth6 hF hα hα1 hmem hb hz
  have hpre : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ')
      ≤ 201 / (Work.Spaces.gam α - 1)
      * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ') := by
    apply mul_le_mul_of_nonneg_right _ hHknn
    have hγ10 : Work.Spaces.gam α - 1 ≤ 1 / 10 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    have hinv10 : (10 : ℝ) ≤ 1 / (Work.Spaces.gam α - 1) := by
      rw [le_div_iff₀ hγ]; linarith
    have hpi : 4 / Real.pi ≤ 1 / (Work.Spaces.gam α - 1) := by
      have hp : (4 : ℝ) / Real.pi ≤ 4 / 3 := by
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 3)]
        nlinarith [Real.pi_gt_three]
      linarith
    have h201 : (201 : ℝ) / (Work.Spaces.gam α - 1)
        = 1 / (Work.Spaces.gam α - 1) + 200 / (Work.Spaces.gam α - 1) := by
      rw [← add_div]; norm_num
    rw [h201]
    linarith
  calc (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * ∫ θ' in Work.Spaces.Iθ, (deriv (fun θ'' => Work.Spaces.DzIter b f z θ'') θ') ^ 2
                * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := hag
    _ = (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ') ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * ∫ θ' in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ') ^ 2
                * (Real.sin (2 * θ')) ^ (2 - Work.Spaces.gam α) := by
        simp only [Work.Spaces.pth]
    _ ≤ (4 / Real.pi) * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ')
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ') :=
        add_le_add
          (mul_le_mul_of_nonneg_left hz1 (by positivity))
          (mul_le_mul_of_nonneg_left hz2 (div_nonneg (by norm_num) hγ.le))
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ') := by ring
    _ ≤ 201 / (Work.Spaces.gam α - 1)
          * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ') := hpre

end

end Work.FTS.StrongPersist.N6Trans.SixAux
