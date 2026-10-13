import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The two-level Cauchy–Schwarz slot bound `slotCS_z`

For every leaf weight `ρ` of a slot `(a,b)`, the mixed slot pairing
`∫_z ∫_θ ρ · |D_z^{b-k}D_θ^a f| · |D_z^bD_θ^a f|` is bounded by
`|f|_{ℋ⁴}·|f|_{ℋ⁶}` as soon as `k ≤ b`, `a + b ≤ 6` and `a + (b-k) ≤ 4`.

The two factors of the integrand are a slot of order at most four and a slot of order at most
six; each of them is pointwise dominated by the corresponding `HkIntegrand`
(`leaf_sq_le4`, `leaf_sq_le6`), so the pointwise form of Cauchy–Schwarz turns the integrand into
a product of the two square roots, and two applications of `cs_sqrt_le_fts` (first on the
angular slice, then in `z`) produce `√(HkSq α 4 f) · √(HkSq α 6 f)`.

The constant is therefore `1`.
-/

/-! ## 1. Pointwise domination of a slot square by the `ℋ^k`-integrand -/

/-- The `η`-weighted square of a pure `D_z`-slot at level four: a summand of `HkIntegrand α 4 f`
written in the raw weight form `w(z)² sin(2θ)^{-η}`. -/
theorem zSlot_le4 (α : ℝ) {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * (Work.Spaces.DzIter i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have heq : (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Work.Spaces.DzIter i f z θ) ^ 2 := by
    rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hs (by norm_num [Work.Spaces.eta])]
    ring
  rw [← heq]
  exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ i hi

/-- The `γ`-weighted square of a mixed slot at level four: a summand of `HkIntegrand α 4 f`
written in the raw weight form `w(z)² sin(2θ)^{-γ}`. -/
theorem mSlot_le4 (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have heq : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f z θ) ^ 2 := by
    rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
    ring
  rw [← heq]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij

/-- The slot weight of `ℋ⁴` times the square of a slot of `ℋ⁴` is dominated by
`HkIntegrand α 4 f`. -/
theorem slotW_mul_le4 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {a b : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ 4) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ, Work.Spaces.mixed_zero_right]
    exact zSlot_le4 α hθI b (by omega)
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    exact mSlot_le4 α hα hθI b a ha1 hab

/-- The slot weight of `ℋ⁶` times the square of a slot of `ℋ⁶` is dominated by
`HkIntegrand α 6 f`. -/
theorem slotW_mul_le6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) {a b : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hab : a + b ≤ 6) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ, Work.Spaces.mixed_zero_right]
    exact sq_le_HkIntegrand_pure6 α hθI b (by omega)
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    exact sq_le_HkIntegrand_mixed6 α hα hθI b a ha1 hab

/-- The three leaf weights are nonnegative on the closed angular interval. -/
theorem leaf_nonneg_Iθ {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ ρ z θ := by
  rcases hleaf with rfl | rfl | ⟨-, rfl⟩
  · exact Work.FTS.TransportS.leafEta_nonneg (sin_two_nonneg_Iθ hθ)
  · exact Work.FTS.TransportS.leafOne_nonneg z θ
  · exact Work.FTS.TransportS.leafGam_nonneg α (sin_two_nonneg_Iθ hθ)

/-- A leaf weight times the square of a slot of order at most four is dominated by
`HkIntegrand α 4 f` (on the open quadrant). -/
theorem leaf_sq_le4 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
  le_trans (mul_le_mul_of_nonneg_right
    ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).2 z θ hz hθ.1 hθ.2) (sq_nonneg _))
    (slotW_mul_le4 α hα f hθ hab)

/-- A leaf weight times the square of a slot of order at most six is dominated by
`HkIntegrand α 6 f` (on the open quadrant). -/
theorem leaf_sq_le6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
  le_trans (mul_le_mul_of_nonneg_right
    ((Work.FTS.TransportS.IsLeafW_le α hα hleaf).2 z θ hz hθ.1 hθ.2) (sq_nonneg _))
    (slotW_mul_le6 α hα f hθ hab)

/-! ## 2. The two elementary analytic inputs -/

/-- **The square-root form of the Cauchy–Schwarz inequality on a set** (restated from
`Work.FTS.TransportS.SlotT2.cs_sqrt_le`). -/
theorem cs_sqrt_le_fts {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-- The pointwise square-root factorisation of a leaf-weighted slot product: if the two
weighted slot squares are dominated by `A` resp. `B`, then the weighted product of the two
slots is dominated by `√A·√B`. -/
theorem leaf_prod_sqrt_le {ρ X Y A B : ℝ} (hρ : 0 ≤ ρ)
    (hX : ρ * X ^ 2 ≤ A) (hY : ρ * Y ^ 2 ≤ B) :
    ρ * |X| * |Y| ≤ Real.sqrt A * Real.sqrt B := by
  have h1 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ
  calc ρ * |X| * |Y| = (Real.sqrt ρ * Real.sqrt ρ) * |X| * |Y| := by rw [h1]
    _ = Real.sqrt (ρ * X ^ 2) * Real.sqrt (ρ * Y ^ 2) := by
        rw [Real.sqrt_mul hρ, Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
        ring
    _ ≤ Real.sqrt A * Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)

/-! ## 3. The two-level Cauchy–Schwarz bound -/

theorem slotCS_z : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ∀ (a b k : ℕ) (ρ : ℝ → ℝ → ℝ), Work.FTS.TransportS.IsLeafW α a ρ →
      k ≤ b → a + b ≤ 6 → a + (b - k) ≤ 4 →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * |Work.Spaces.mixed (b - k) a f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ C * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
  refine ⟨1, one_pos, ?_⟩
  intro α f hα hα1 hso hmem a b k ρ hleaf hkb hab habk
  -- the level-four honesty of `f`, which is what the level-four slot needs
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hmem
  -- the two slots
  let X : ℝ → ℝ → ℝ := Work.Spaces.mixed (b - k) a f
  let Y : ℝ → ℝ → ℝ := Work.Spaces.mixed b a f
  change (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      ρ z θ * |X z θ| * |Y z θ|)
    ≤ 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have h4nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have h6nn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 6 f z θ
  -- ## the marginal integrability of the two integrands
  have hAint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iz := hmem4.2
  have hBint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ) Work.Spaces.Iz := hmem.2
  have hAnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z => MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h4nn z θ))
  have hBnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ :=
    fun z => MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => h6nn z θ))
  -- ## the angular slice estimate
  have hsliceAll : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * |X z θ| * |Y z θ|)
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- at `z = 0` every leaf weight vanishes
      subst h0
      have hρ0 : ∀ θ : ℝ, ρ 0 θ = 0 := fun θ => by
        rcases hleaf with rfl | rfl | ⟨-, rfl⟩ <;>
          simp [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafOne,
            Work.FTS.TransportS.leafGam, Work.Spaces.w]
      have hzero : (fun θ : ℝ => ρ 0 θ * |X 0 θ| * |Y 0 θ|) = fun _ => (0 : ℝ) := by
        funext θ
        rw [hρ0 θ]
        ring
      rw [hzero, integral_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · -- the open quadrant: pointwise domination plus Cauchy–Schwarz on the slice
      have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          ρ z θ * |X z θ| * |Y z θ|
            ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) :=
        Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => by
          refine leaf_prod_sqrt_le (leaf_nonneg_Iθ hleaf z θ ⟨le_of_lt h1, le_of_lt h2⟩)
            ?_ ?_
          · exact leaf_sq_le4 hα hleaf habk hz0 ⟨h1, h2⟩
          · exact leaf_sq_le6 hα hleaf hab hz0 ⟨h1, h2⟩)
      have h4_meas : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmem4.1 z hz).aestronglyMeasurable
      have h6_meas : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmem.1 z hz).aestronglyMeasurable
      have h4_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmem4.1 z hz).congr (Filter.Eventually.of_forall
          (fun θ => (Real.sq_sqrt (h4nn z θ)).symm))
      have h6_sq : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmem.1 z hz).congr (Filter.Eventually.of_forall
          (fun θ => (Real.sq_sqrt (h6nn z θ)).symm))
      have h4_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h4_meas).mpr h4_sq
      have h6_lp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq h6_meas).mpr h6_sq
      have hprod : Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        memLp_one_iff_integrable.mp (h4_lp.mul h6_lp)
      have hstep1 : (∫ θ in Work.Spaces.Iθ, ρ z θ * |X z θ| * |Y z θ|)
          ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ) :=
        MeasureTheory.integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθm (fun θ hθ =>
            mul_nonneg (mul_nonneg (leaf_nonneg_Iθ hleaf z θ hθ) (abs_nonneg _))
              (abs_nonneg _)))
          hprod hpt
      have hstep2 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 6 f z θ))
          ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ) :=
        cs_sqrt_le_fts (hmem4.1 z hz) (hmem.1 z hz)
          (fun θ => h4nn z θ) (fun θ => h6nn z θ)
      exact le_trans hstep1 hstep2
  -- ## the radial Cauchy–Schwarz
  have houter_int : IntegrableOn (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 f z θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 f z θ)) Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable
    have h1sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hAint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hAnn z)).symm))
    have h2sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hBint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hBnn z)).symm))
    have h1lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => MeasureTheory.integral_nonneg_of_ae
        (ae_restrict_of_forall_mem hIθm (fun θ hθ =>
          mul_nonneg (mul_nonneg (leaf_nonneg_Iθ hleaf z θ hθ) (abs_nonneg _))
            (abs_nonneg _)))))
      houter_int (ae_restrict_of_forall_mem hIzm hsliceAll)
  have hCS : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 6 f z θ))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ) :=
    cs_sqrt_le_fts hAint hBint hAnn hBnn
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * |X z θ| * |Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ) := houter
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 6 f z θ) := hCS
    _ = 1 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq, one_mul]

end Work.FTS.StrongPersist.H6Pair6Aux
