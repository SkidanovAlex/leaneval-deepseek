import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers

These are the (slightly generalised) slot facts needed for the `L₁₂(f)·D_θ f` row: the two
factors that occur after the Leibniz expansion carry the slot indices `a` and `a + 1`, while
the leaf weight `ρ` belongs to the slot `a`. -/

/-- A leaf weight of the slot `a` is dominated by the slot weight of any slot index `a' ≥ a`. -/
theorem leaf_le_slotW_of_le {α : ℝ} (hα : 0 < α) {a a' : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a ≤ a') :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      ρ z θ ≤ Work.FTS.TransportS.slotW α a' z θ := by
  rcases hleaf with rfl | rfl | ⟨ha1, rfl⟩
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafEta_le_slotW α hα hθ
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafOne_le_slotW α hα hθ
  · exact fun z θ _ hθ => Work.FTS.TransportS.leafGam_le_slotW α hα (by omega) hθ

/-- A single slot of `f` is dominated by the level-`m` integrand. -/
theorem slotW_slot_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b m : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ m) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ, Work.Spaces.mixed_zero_right]
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have heq : (Work.Spaces.DzIter b f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter b f z θ) ^ 2 := by
      rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hs (ne_of_gt Work.Spaces.eta_pos)]
      ring
    have h := Work.Spaces.sq_le_HkIntegrand_z α m f z θ b (by omega)
    rwa [heq] at h
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    have heq : (Work.Spaces.mixed b a f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      ring
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α m f z θ a b ha1 (by omega)
    rwa [heq] at h

/-- The `ρ`-weighted product of two slots of `f` (of indices `a₁ ≥ a`, `a₂ ≥ a`, both of
order at most `m`) is dominated by the level-`m` integrand. -/
theorem leaf_mixed_le {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a a₁ a₂ b₁ b₂ m : ℕ}
    {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (ha₁ : a ≤ a₁) (ha₂ : a ≤ a₂) (hb₁ : a₁ + b₁ ≤ m) (hb₂ : a₂ + b₂ ≤ m)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  have hρ0 : 0 ≤ ρ z θ := (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz hθ.1 hθ.2
  have h1 : ρ z θ * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ :=
    (mul_le_mul_of_nonneg_right (leaf_le_slotW_of_le hα hleaf ha₁ z θ hz hθ)
      (sq_nonneg _)).trans (slotW_slot_le hα hθ hb₁)
  have h2 : ρ z θ * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α m f z θ :=
    (mul_le_mul_of_nonneg_right (leaf_le_slotW_of_le hα hleaf ha₂ z θ hz hθ)
      (sq_nonneg _)).trans (slotW_slot_le hα hθ hb₂)
  have h3 : |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      ≤ (1 / 2) * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2
        + (1 / 2) * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2 := by
    rw [← abs_mul]
    exact abs_mul_le_half _ _
  calc ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|
      = ρ z θ * (|Work.Spaces.mixed b₁ a₁ f z θ| * |Work.Spaces.mixed b₂ a₂ f z θ|) := by
        ring
    _ ≤ ρ z θ * ((1 / 2) * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2
          + (1 / 2) * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hρ0
    _ = (1 / 2) * (ρ z θ * (Work.Spaces.mixed b₁ a₁ f z θ) ^ 2)
          + (1 / 2) * (ρ z θ * (Work.Spaces.mixed b₂ a₂ f z θ) ^ 2) := by ring
    _ ≤ Work.Spaces.HkIntegrand α m f z θ := by linarith

/-- The three leaf weights are continuous on the open quadrant. -/
theorem continuousOn_leaf {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with rfl | rfl | ⟨-, rfl⟩
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta)).congr
      (fun p _ => rfl)
  · exact Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.congr (fun p _ => rfl)
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0
        (Work.Spaces.gam α))).congr (fun p _ => rfl)

/-- The mixed angular derivative of the second factor: `D_z^jD_θ^a (D_θ f) = D_z^jD_θ^{a+1} f`. -/
theorem mixed_Dth_eq (j a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j a (Work.Spaces.Dth f) = Work.Spaces.mixed j (a + 1) f := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.Dth f))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (a + 1) f)
  rw [show Work.Spaces.Dth f = Work.Spaces.DthIter 1 f from rfl,
    Work.Spaces.DthIter_add_right a 1 f]

/-- A property holding for every `z > 0` holds a.e. for the measure restricted to `Iz`. -/
theorem ae_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), p z := by
  rw [Work.Spaces.Iz]
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => h z hz)

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` and to `(0,∞)` agree. -/
theorem Iz_restrict_eq : volume.restrict Work.Spaces.Iz
    = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm

/-! ## Measurability and integrability of the `θ`-slices of one slot of the expansion -/

/-- The `z`-jets of the radial coefficient `L₁₂(f)` are a.e. strongly measurable on `Iz`. -/
theorem aesm_DzdIter_L12 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f)
    (k : ℕ) (hk : k ≤ 6) :
    AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (volume.restrict Work.Spaces.Iz) := by
  have hCd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  have hEq : (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      = fun z => (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) z := by
    funext z
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  have hcont : ContinuousOn
      (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) (Set.Ioi 0) :=
    (Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' k (6 - k) (by
      have h : k + (6 - k) = 6 := by omega
      rw [← Nat.cast_add, h]
      exact hCd)).continuousOn
  have h1 : AEStronglyMeasurable
      (fun z => (Work.Spaces.Zop^[k] (fun z => Work.Construction.L12 f z)) z)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  rw [hEq, Iz_restrict_eq]
  exact h1

/-- The `θ`-slice of a single slot pairing of the expansion is integrable. -/
theorem Psi_slice_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    Integrable (fun θ => ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
      * Work.Spaces.mixed b a f z θ) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_leaf hleaf).mul
      ((hso.mixed (b - k) (a + 1)).continuousOn)).mul ((hso.mixed b a).continuousOn)
  refine MeasureTheory.Integrable.mono' (hm7.1 z (le_of_lt hz)) ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show ‖ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ‖ ≤ Work.Spaces.HkIntegrand α 7 f z θ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

/-- The `θ`-integral of a single slot pairing of the expansion is dominated by the level-seven
slice integrand. -/
theorem Psi_le_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm7.1 z (le_of_lt hz)) ?_
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show (0 : ℝ) ≤ |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 7 f z θ
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

/-- The `θ`-integral of a single slot pairing of the expansion is integrable in `z`. -/
theorem Psi_intz {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ
      * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      Work.Spaces.Iz := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2
      * Work.Spaces.mixed (b - k) (a + 1) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_leaf hleaf).mul
      ((hso.mixed (b - k) (a + 1)).continuousOn)).mul ((hso.mixed b a).continuousOn)
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ
      * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ)
      (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  refine MeasureTheory.Integrable.mono' hm7.2 haesm ?_
  filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
  rw [Real.norm_eq_abs]
  exact Psi_le_int hα hso hleaf hm7 hab hz

/-- The `z`-integrand `D_z^k(L₁₂f)·(θ-slot integral)` is integrable. -/
theorem DzdX_Psi_int {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ} {K : ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm7 : Work.Spaces.HkMem α 7 f)
    (hab : a + b ≤ 6) (hk : k ≤ 6) (hK : 0 ≤ K)
    (hbound : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ K) :
    IntegrableOn (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
      * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ)) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' (hm7.2.const_mul K) ?_ ?_
  · exact (aesm_DzdIter_L12 hso hm7 k hk).mul (Psi_intz (k := k) hα hso hleaf hm7 hab).aestronglyMeasurable
  · filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    have h2 := Psi_le_int (k := k) hα hso hleaf hm7 hab hz
    have h1 := hbound z hz
    have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 7 f z θ :=
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 7 f z θ
    exact mul_le_mul h1 h2 (abs_nonneg _) hK

theorem Psi_le_int6 {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hm6 : Work.Spaces.HkMem α 6 f)
    (hab : a + b ≤ 6) (hk : 1 ≤ k) (hkb : k ≤ b) {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ := by
  refine le_trans abs_integral_le_integral_abs ?_
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm6.1 z (le_of_lt hz)) ?_
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show (0 : ℝ) ≤ |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ|
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact mul_nonneg (mul_nonneg hρ0 (abs_nonneg _)) (abs_nonneg _)
  · refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
    have hρ0 : 0 ≤ ρ z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hleaf).1 z θ hz h1 h2
    show |ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
        * Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
    exact leaf_mixed_le hα hleaf (by omega) (le_refl a) (by omega) (by omega)
      hz ⟨h1, h2⟩

end Work.FTS.StrongPersist.H6Pair6Aux
