import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WB.integral_abs_wSmall1Pair_u_le
import Submission.Work.BoseFixB1.WB.wbU_aemeasurable
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1B.sbWordMuShift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for `Work.BoseB1Cube.fibSumFibreGood`

The localised one-body kernel factors pointwise as

    wSmall1Pair h M ℓ d u z y = Kf h M ℓ d z y * Bl M ℓ d u z y ,

where `Kf` is the `u`-independent factor (the two `χ(x/ℓ)` cutoffs and the renormalised
numerator `g₀(z−y)/((χ_M⋆χ_M)((z−y)/(ℓd))·(χ⋆χ)((z−y)/ℓ))`) and `Bl` is the product of the two
`u`-dependent `χ_M` factors.  This is what makes the `u`-integral of `wSmall1Pair` a constant
times the `u`-integral of `Bl`, so that the `χ_M`-level fibre inequality
(`Work.BoseB1Cube.chiFibreGood`, taken here as a hypothesis `hF1`) transfers to `wSmall1Pair`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseB1Cube

open Submission.BoseGases

/-- The `u`-independent factor of the localised one-body kernel
`wSmall1Pair h M ℓ d u z y`. -/
noncomputable def Kf {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (z y : E3) : ℝ :=
  chiScale ℓ z * chiScale ℓ y *
    (g0 v h (z - y) / (convScaleSmall M (ℓ * d) (z - y) * convScale ℓ (z - y)))

/-- The `u`-dependent factor of the localised one-body kernel: the product of the two
`(ℓd)`-scale bumps. -/
noncomputable def Bl (M : ℕ) (ℓ d : ℝ) (u z y : E3) : ℝ :=
  chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)

theorem Bl_nonneg (M : ℕ) (ℓ d : ℝ) (u z y : E3) : 0 ≤ Bl M ℓ d u z y :=
  mul_nonneg (chiSmall_nonneg M _) (chiSmall_nonneg M _)

theorem wSmall1Pair_eq_Kf_mul_Bl {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (u z y : E3) :
    wSmall1Pair h M ℓ d u z y = Kf h M ℓ d z y * Bl M ℓ d u z y := by
  simp only [Kf, Bl, wSmall1Pair, wSmallPair, wSmallScaled, chiSmallB]
  ring

theorem Kf_nonneg_of_g0_nonneg {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ} {ℓ d : ℝ}
    {z y : E3} (hg : 0 ≤ g0 v h (z - y)) : 0 ≤ Kf h M ℓ d z y := by
  rw [Kf, div_eq_mul_inv]
  exact mul_nonneg (mul_nonneg (chiScale_nonneg ℓ z) (chiScale_nonneg ℓ y))
    (mul_nonneg hg (inv_nonneg.mpr
      (mul_nonneg (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (z - y))
        (convScale_nonneg ℓ (z - y)))))

theorem Kf_eq_zero_of_R_le {v : E3 → ℝ} {R : ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    {h : Work.UBB.ScatSol v} {M : ℕ} {ℓ d : ℝ} {z y : E3} (hz : R ≤ ‖z - y‖) :
    Kf h M ℓ d z y = 0 := by
  rw [Kf, g0_zero_of_norm_ge hv_supp hz h]
  ring

/-- **The `u`-integral of the localised kernel factorises**: for any set `s`,

    ∫ u in s, wSmall1Pair h M ℓ d u z y = Kf h M ℓ d z y * ∫ u in s, Bl M ℓ d u z y . -/
theorem uint_eq {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (s : Set E3)
    (z y : E3) :
    (∫ u in s, wSmall1Pair h M ℓ d u z y)
      = Kf h M ℓ d z y * (∫ u in s, Bl M ℓ d u z y) := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun u => wSmall1Pair_eq_Kf_mul_Bl h M ℓ d u z y))

/-! ## The `χ_M`-level fibre inequality transferred to the localised kernel -/

/-- **The pointwise (in `z,y`) fibre inequality at the localised kernel.**  `hF1` is the
`χ_M`-level restriction step (`Work.BoseB1Cube.chiFibreGood`) in the interface form: the
`u`-integral of the two-bump product over the complement of `goodSet ℓ d μ` is dominated by three
times its integral over the boundary layer `goodSet ℓ d μ \ interiorSet ℓ d μ`, for `z,y` in the
small box with `|z_j − y_j| ≤ ℓd/16`.

Given `0 ≤ Kf h M ℓ d z y`, the same inequality holds for the localised one-body kernel
`wSmall1Pair`, because the `u`-integral factorises as `Kf · (∫ u in s, Bl u z y)`. -/
theorem uint_le_of_hF1 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} {ℓ d μ : ℝ}
    (hF1 : ∀ z y : E3, z ∈ Submission.BoseGases.acube ℓ →
      y ∈ Submission.BoseGases.acube ℓ →
      (∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16) →
      (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Bl M ℓ d u z y)
        ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                        \ Work.SmallBoxSliding.interiorSet ℓ d μ), Bl M ℓ d u z y))
    {R : ℝ} (hRd : R ≤ ℓ * d / 16) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    {z y : E3} (hz : z ∈ Submission.BoseGases.acube ℓ)
    (hy : y ∈ Submission.BoseGases.acube ℓ) (hK : 0 ≤ Kf h M ℓ d z y) :
    (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      ≤ 3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
                      \ Work.SmallBoxSliding.interiorSet ℓ d μ),
          Submission.BoseGases.wSmall1Pair h M ℓ d u z y) := by
  rw [uint_eq h M ℓ d _ z y, uint_eq h M ℓ d _ z y]
  by_cases hlt : ‖z - y‖ < R
  · have hcoord : ∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16 := by
      intro j
      calc |(z - y).ofLp j| ≤ ‖z - y‖ := PiLp.norm_apply_le (z - y) j
        _ ≤ R := le_of_lt hlt
        _ ≤ ℓ * d / 16 := hRd
    have hI := hF1 z y hz hy hcoord
    calc Kf h M ℓ d z y * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Bl M ℓ d u z y)
        ≤ Kf h M ℓ d z y * (3 * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
              \ Work.SmallBoxSliding.interiorSet ℓ d μ), Bl M ℓ d u z y)) :=
          mul_le_mul_of_nonneg_left hI hK
      _ = 3 * (Kf h M ℓ d z y * (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ
              \ Work.SmallBoxSliding.interiorSet ℓ d μ), Bl M ℓ d u z y)) := by ring
  · have hz0 : Kf h M ℓ d z y = 0 :=
      Kf_eq_zero_of_R_le hv_supp (le_of_not_gt hlt)
    rw [hz0]
    simp

/-- **The `u`-integral of the localised kernel, swapped with the `y`-integral** (`z` fixed). -/
theorem uy_swap {v : E3 → ℝ} {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R0)
    (hR0 : 0 < R0) (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (s : Set E3) (z : E3) :
    (∫ u in s, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      = ∫ y in Submission.BoseGases.acube ℓ, ∫ u in s,
          Submission.BoseGases.wSmall1Pair h M ℓ d u z y := by
  have hj := Work.SmallBoxSliding.integrable_wSmall1Pair_prod hv_supp hR0 h hM hℓ hd hRd hRχ z
  have hle : ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict s).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ))
      ≤ (MeasureTheory.volume : MeasureTheory.Measure E3).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self le_rfl
  have hmono := hj.mono_measure hle
  simpa only [Function.uncurry] using
    (MeasureTheory.integral_integral_swap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict s)
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun (u y : E3) => Submission.BoseGases.wSmall1Pair h M ℓ d u z y) hmono)

/-- **A.e. nonnegativity of the `u`-independent factor** (in the `y` variable, `z` fixed), from
the a.e. nonnegativity of `g₀`. -/
theorem ae_Kf_nonneg {v : E3 → ℝ} (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    {M : ℕ} {ℓ d : ℝ} (z : E3) : ∀ᵐ y : E3, 0 ≤ Kf h M ℓ d z y :=
  (Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR h z).mono
    (fun y hy => Kf_nonneg_of_g0_nonneg hy)

/-! ## The `u`-support of the localised kernel -/

/-- **The `u`-support of `χ_{B(u)}`**: if `u` lies outside the cube `acube ((1+d)/d)` then
`χ_{B(u)}(z)` vanishes for **every** `z`.

The `(ℓd)`-containment `χ_{B(u)}(z) ≠ 0 → |z_j/(ℓd) − u_j| ≤ 1/2` together with the big-box
containment `→ |z_j| ≤ ℓ/2` gives `|u_j| ≤ 1/(2d) + 1/2 = (1+d)/(2d)`; and if some `|z_j| > ℓ/2`
then `‖z‖ > ℓ/2` and the `ℓ`-scale cutoff vanishes as well. -/
theorem chiSmallB_eq_zero_of_notMem_acube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {u : E3} (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) (z : E3) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  by_contra hne
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hzb : ∀ j : Fin 3, |z.ofLp j| ≤ ℓ / 2 :=
    fun j => Submission.BoseGases.chiSmallB_support_big_box (M := M) hM hℓ hne j
  have hsm : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z - u).ofLp j| ≤ 1 / 2 :=
    fun j => Submission.BoseGases.chiSmallB_support_small_box (M := M) hM hne j
  have hlb : ∀ j : Fin 3, |u.ofLp j| ≤ (1 + d) / d / 2 := by
    intro j
    have hsc : ((ℓ * d)⁻¹ • z).ofLp j = (ℓ * d)⁻¹ * z.ofLp j := by simp
    have h1 : |((ℓ * d)⁻¹ • z).ofLp j| ≤ 1 / (2 * d) := by
      rw [hsc, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hcpos))]
      have h2 : (ℓ * d)⁻¹ * (ℓ / 2) = 1 / (2 * d) := by
        rw [inv_mul_eq_iff_eq_mul₀ (ne_of_gt hcpos)]
        field_simp
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (hzb j) (inv_nonneg.mpr (le_of_lt hcpos))
    have htri : |u.ofLp j| ≤ |((ℓ * d)⁻¹ • z).ofLp j| + |((ℓ * d)⁻¹ • z - u).ofLp j| := by
      calc |u.ofLp j|
          = |((ℓ * d)⁻¹ • z).ofLp j + (-((((ℓ * d)⁻¹ • z - u).ofLp j)))| := by
            congr 1
            change u.ofLp j
              = ((ℓ * d)⁻¹ • z).ofLp j + (-((((ℓ * d)⁻¹ • z).ofLp j) - u.ofLp j))
            ring
        _ ≤ |((ℓ * d)⁻¹ • z).ofLp j| + |-((((ℓ * d)⁻¹ • z - u).ofLp j))| := abs_add_le _ _
        _ = |((ℓ * d)⁻¹ • z).ofLp j| + |((ℓ * d)⁻¹ • z - u).ofLp j| := by rw [abs_neg]
    calc |u.ofLp j| ≤ |((ℓ * d)⁻¹ • z).ofLp j| + |((ℓ * d)⁻¹ • z - u).ofLp j| := htri
      _ ≤ 1 / (2 * d) + 1 / 2 := add_le_add h1 (hsm j)
      _ = (1 + d) / d / 2 := by field_simp
  apply hu
  intro j
  rw [Set.mem_Icc]
  exact ⟨by linarith [neg_abs_le (u.ofLp j), hlb j],
    by linarith [le_abs_self (u.ofLp j), hlb j]⟩


/-- **The localised one-body kernel vanishes off the `u`-cube**: for `u ∉ acube ((1+d)/d)` the
kernel `wSmall1Pair h M ℓ d u z y` vanishes for all `z, y`. -/
theorem wSmall1Pair_eq_zero_of_notMem_acube {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) (z y : E3) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u z y = 0 := by
  rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    chiSmallB_eq_zero_of_notMem_acube (M := M) hM hℓ hd hu z]
  ring

/-- **`fibSum` is supported in the `u`-cube `acube ((1+d)/d)`.** -/
theorem fibSum_eq_zero_of_notMem_acube {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : u ∉ Submission.BoseGases.acube ((1 + d) / d)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1.fibSum h M ℓ d u Φ = 0 := by
  rw [Work.BoseFixB1.fibSum]
  have hzero : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      Φ x ^ 2 * ∑ i : Fin n,
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y = 0 := by
    intro x _
    have hone : ∀ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) = 0 := by
      intro i
      rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun y => wSmall1Pair_eq_zero_of_notMem_acube h hM hℓ hd hu (x i) y)), integral_zero]
    rw [Finset.sum_eq_zero (fun i _ => hone i), mul_zero]
  rw [integral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem
    (Submission.BoseGases.abox_measurable n ℓ) hzero), integral_zero]

/-! ## Pointwise bounds -/

/-- **The `u`-integral of the localised kernel over any set is dominated by `2χ²|g₀|`.** -/
theorem abs_uint_le {v : E3 → ℝ} {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R0)
    (hR0 : 0 < R0) (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (s : Set E3) (z y : E3) :
    |∫ u in s, Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * |Submission.BoseGases.g0 v h (z - y)| := by
  set C : ℝ := 2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      * |Submission.BoseGases.g0 v h (z - y)| / Work.SmallBoxSliding.smallConvLower M with hC
  have hdom0 : MeasureTheory.Integrable (fun u : E3 =>
      C * (Submission.BoseGases.chiSupAbs
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)))
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    ((Work.SmallBoxSliding.integrable_chiSmall_shift (M := M) hM ((ℓ * d)⁻¹ • z)).const_mul
      Submission.BoseGases.chiSupAbs).const_mul C
  have hdom : MeasureTheory.Integrable (fun u : E3 =>
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
        * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * |Submission.BoseGases.g0 v h (z - y)|) / Work.SmallBoxSliding.smallConvLower M)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    hdom0.congr (Filter.Eventually.of_forall (fun u => by rw [hC]; ring))
  have hcont : Continuous (fun u : E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u z y) := by
    have h1 : Continuous (fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) := by
      have hEq : (fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u z)
          = fun u : E3 => Submission.BoseGases.chiScale ℓ z
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) := rfl
      rw [hEq]
      exact continuous_const.mul ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    have h2 : Continuous (fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u y) := by
      have hEq : (fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u y)
          = fun u : E3 => Submission.BoseGases.chiScale ℓ y
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u) := rfl
      rw [hEq]
      exact continuous_const.mul ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
    have hEq : (fun u : E3 => Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
        = fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u z
            * (Submission.BoseGases.g0 v h (z - y)
                / (Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)
                  * Submission.BoseGases.convScale ℓ (z - y)))
            * Submission.BoseGases.chiSmallB M ℓ d u y := by
      funext u
      simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
        Submission.BoseGases.wSmallScaled, div_div]
    rw [hEq]
    exact (h1.mul continuous_const).mul h2
  have hint : MeasureTheory.Integrable
      (fun u : E3 => |Submission.BoseGases.wSmall1Pair h M ℓ d u z y|)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    Integrable.mono' hdom (hcont.abs.aestronglyMeasurable) (Filter.Eventually.of_forall
      (fun u => by
        rw [Real.norm_eq_abs, abs_abs]
        exact Work.SmallBoxSliding.abs_wSmall1Pair_le hv_supp hR0 h hM hℓ hd hRd hRχ u z y))
  have hfin : (∫ u : E3, |Submission.BoseGases.wSmall1Pair h M ℓ d u z y|)
      ≤ Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y
          * (|Submission.BoseGases.g0 v h (z - y)|
            * (Submission.BoseGases.convScale ℓ (z - y))⁻¹) :=
    Work.BoseFixB1.WB.integral_abs_wSmall1Pair_u_le hM hℓ hd z y
  have hcS : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  calc |∫ u in s, Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
      ≤ ∫ u in s, |Submission.BoseGases.wSmall1Pair h M ℓ d u z y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : E3, |Submission.BoseGases.wSmall1Pair h M ℓ d u z y| :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall (fun u => abs_nonneg _))
    _ ≤ Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y
          * (|Submission.BoseGases.g0 v h (z - y)|
            * (Submission.BoseGases.convScale ℓ (z - y))⁻¹) := hfin
    _ ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * |Submission.BoseGases.g0 v h (z - y)| := by
        rcases le_or_gt ‖z - y‖ R0 with hlt | hgt
        · have h1 : (Submission.BoseGases.convScale ℓ (z - y))⁻¹ ≤ 2 :=
            le_trans (le_abs_self _)
              (Submission.BoseGases.abs_inv_convScale_le_two hℓ hRχ hlt)
          have h2 : Submission.BoseGases.chiScale ℓ z ≤ Submission.BoseGases.chiSupAbs :=
            le_trans (le_abs_self _) (Submission.BoseGases.chiScale_abs_le_sup ℓ z)
          have h3 : Submission.BoseGases.chiScale ℓ y ≤ Submission.BoseGases.chiSupAbs :=
            le_trans (le_abs_self _) (Submission.BoseGases.chiScale_abs_le_sup ℓ y)
          have h4 : 0 ≤ (Submission.BoseGases.convScale ℓ (z - y))⁻¹ :=
            inv_nonneg.mpr (Submission.BoseGases.convScale_nonneg ℓ (z - y))
          have h5 : 0 ≤ Submission.BoseGases.chiScale ℓ y :=
            Submission.BoseGases.chiScale_nonneg ℓ y
          have h8 : 0 ≤ |Submission.BoseGases.g0 v h (z - y)| := abs_nonneg _
          have hstep : Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y
              ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSupAbs :=
            mul_le_mul h2 h3 h5 (le_trans (Submission.BoseGases.chiScale_nonneg ℓ z) h2)
          calc Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y
                * (|Submission.BoseGases.g0 v h (z - y)|
                  * (Submission.BoseGases.convScale ℓ (z - y))⁻¹)
              = Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y
                * |Submission.BoseGases.g0 v h (z - y)|
                * (Submission.BoseGases.convScale ℓ (z - y))⁻¹ := by ring
            _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSupAbs
                  * |Submission.BoseGases.g0 v h (z - y)|) * 2 :=
                mul_le_mul (mul_le_mul hstep le_rfl h8 (mul_nonneg hcS hcS)) h1 h4
                  (mul_nonneg (mul_nonneg hcS hcS) h8)
            _ = 2 * Submission.BoseGases.chiSupAbs ^ 2
                  * |Submission.BoseGases.g0 v h (z - y)| := by ring
        · have hz0 : Submission.BoseGases.g0 v h (z - y) = 0 :=
            Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_lt hgt) h
          rw [hz0, abs_zero]
          simp

/-- **The uniform `(u,y)`-bound of the fibre sum**: for any set `s` and any `z`,

    |∫ u in s, ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y| ≤ 2·χ²·8πa(v) . -/
theorem abs_uint_uint_le {v : E3 → ℝ} {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R0)
    (hR0 : 0 < R0) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (s : Set E3) (z : E3) :
    |∫ u in s, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) := by
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hg0nn : ∀ᵐ y : E3, 0 ≤ Submission.BoseGases.g0 v h y :=
    Submission.BoseGases.g0_nonneg_ae hR0 hv hvrad hv_supp h
  have habs : (∫ y : E3, |Submission.BoseGases.g0 v h y|)
      = 8 * Real.pi * _root_.BoseGases.a v := by
    rw [← Submission.BoseGases.g0_integral hR0 hv_supp h]
    exact integral_congr_ae (hg0nn.mono (fun y hy => abs_of_nonneg hy))
  have hdom : MeasureTheory.Integrable (fun y : E3 =>
      2 * Submission.BoseGases.chiSupAbs ^ 2 * |Submission.BoseGases.g0 v h (z - y)|)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
        (Submission.BoseGases.acube ℓ)) :=
    ((hg0int.abs.comp_sub_left z).integrableOn).const_mul _
  have hmain : (∫ y in Submission.BoseGases.acube ℓ,
      |∫ u in s, Submission.BoseGases.wSmall1Pair h M ℓ d u z y|)
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          2 * Submission.BoseGases.chiSupAbs ^ 2 * |Submission.BoseGases.g0 v h (z - y)| :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hdom
      (Filter.Eventually.of_forall (fun y => abs_uint_le hv_supp hR0 h hM hℓ hd hRd hRχ s z y))
  have hb : (∫ y in Submission.BoseGases.acube ℓ,
        2 * Submission.BoseGases.chiSupAbs ^ 2 * |Submission.BoseGases.g0 v h (z - y)|)
      ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) := by
    rw [integral_const_mul]
    have h2 : (∫ y in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (z - y)|)
        ≤ 8 * Real.pi * _root_.BoseGases.a v := by
      refine le_trans (setIntegral_le_integral (hg0int.abs.comp_sub_left z)
        (Filter.Eventually.of_forall (fun y => abs_nonneg _))) ?_
      rw [Submission.BoseGases.integral_comp_sub_left
        (fun y : E3 => |Submission.BoseGases.g0 v h y|) z, habs]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc |∫ u in s, ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y|
      = |∫ y in Submission.BoseGases.acube ℓ, ∫ u in s,
          Submission.BoseGases.wSmall1Pair h M ℓ d u z y| := by
        rw [uy_swap hv_supp hR0 h hM hℓ hd hRd hRχ s z]
    _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
          |∫ u in s, Submission.BoseGases.wSmall1Pair h M ℓ d u z y| :=
        abs_integral_le_integral_abs
    _ ≤ 2 * Submission.BoseGases.chiSupAbs ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) :=
        le_trans hmain hb

/-! ## A.e. strong measurability of the partial integrals -/

/-- **Joint a.e. strong measurability of `(u,y) ↦ wSmall1Pair h M ℓ d u z y`** (`z` fixed). -/
theorem aestronglyMeasurable_w1_slice {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (z : E3) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d p.1 z p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) := by
  have hmp : MeasurePreserving (fun y : E3 => z - y)
      (MeasureTheory.volume : MeasureTheory.Measure E3)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have h1 : (fun y : E3 => z - y)
        = (fun w : E3 => z + w) ∘ (fun y : E3 => -y) := by
      funext y; simp [sub_eq_add_neg]
    rw [h1]
    exact (measurePreserving_add_left (MeasureTheory.volume : MeasureTheory.Measure E3) z).comp
      (Measure.measurePreserving_neg (MeasureTheory.volume : MeasureTheory.Measure E3))
  have hgy : MeasureTheory.AEStronglyMeasurable
      (fun y : E3 => Submission.BoseGases.g0 v h (z - y))
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (Work.BoseFixB1.WB.aestronglyMeasurable_g0 (v := v) (h := h)).comp_quasiMeasurePreserving
      hmp.quasiMeasurePreserving
  have hKf_y : AEMeasurable (fun y : E3 => Kf h M ℓ d z y)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hden : Continuous (fun y : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)
        * Submission.BoseGases.convScale ℓ (z - y)) :=
      ((Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)).mul
        ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop))
    have h1 : AEMeasurable (fun y : E3 =>
        Submission.BoseGases.chiScale ℓ z * Submission.BoseGases.chiScale ℓ y)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      ((Submission.BoseGases.chiScale_continuous ℓ).aemeasurable).const_mul
        (Submission.BoseGases.chiScale ℓ z)
    have h2 : AEMeasurable (fun y : E3 =>
        Submission.BoseGases.g0 v h (z - y)
          * (Submission.BoseGases.convScaleSmall M (ℓ * d) (z - y)
            * Submission.BoseGases.convScale ℓ (z - y))⁻¹)
        (MeasureTheory.volume : MeasureTheory.Measure E3) :=
      hgy.aemeasurable.mul hden.aemeasurable.inv
    refine (h1.mul h2).congr ?_
    filter_upwards with y
    simp only [Pi.mul_apply, Kf, div_eq_mul_inv]
    try ring_nf
  have hKf : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => Kf h M ℓ d z p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    (hKf_y.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aestronglyMeasurable
  have hBl : Continuous (fun p : E3 × E3 => Bl M ℓ d p.1 z p.2) := by
    have h1 : Continuous (fun p : E3 × E3 =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - p.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    have h2 : Continuous (fun p : E3 × E3 =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact h1.mul h2
  refine (hKf.mul hBl.aestronglyMeasurable).congr ?_
  filter_upwards with p
  exact (wSmall1Pair_eq_Kf_mul_Bl h M ℓ d p.1 z p.2).symm

/-- **A.e. strong measurability of `y ↦ ∫ u in s, wSmall1Pair h M ℓ d u z y`** (`z` fixed). -/
theorem aestronglyMeasurable_uint_y {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (s : Set E3) (z : E3) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : E3 => ∫ u in s, Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d p.2 z p.1)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) :=
    (aestronglyMeasurable_w1_slice h hM (ℓ := ℓ) (d := d) z).prod_swap
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d p.2 z p.1)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict s)) :=
    h1.mono_measure (MeasureTheory.Measure.prod_mono le_rfl
      MeasureTheory.Measure.restrict_le_self)
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' h2

/-- **A.e. strong measurability of `u ↦ ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y`**. -/
theorem aestronglyMeasurable_int_y_u {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (z : E3) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : E3 => ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d p.1 z p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ))) :=
    (aestronglyMeasurable_w1_slice h hM z).mono_measure
      (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' h1

/-- **Joint a.e. strong measurability of the `(u,z)`-parametrised `y`-slice.** -/
theorem aestronglyMeasurable_int_y_uz {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} :
    MeasureTheory.AEStronglyMeasurable
      (fun p : E3 × E3 => ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2 y)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun q : (E3 × E3) × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d q.1.1 q.1.2 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume : MeasureTheory.Measure E3)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube ℓ))) :=
    (Work.BoseFixB1.WB.aestronglyMeasurable_wSmall1Pair_vol (v := v) (h := h) (M := M) hM
      ℓ d).mono_measure (MeasureTheory.Measure.prod_mono le_rfl
        MeasureTheory.Measure.restrict_le_self)
  exact MeasureTheory.AEStronglyMeasurable.integral_prod_right' h1

/-- **The `u`-slice `u ↦ ∫ y in acube ℓ, wSmall1Pair h M ℓ d u z y` is integrable** for every
set `s` of `u`'s: the slice vanishes off the fixed cube `acube ((1+d)/d)` and is bounded there by
the uniform fibre bound `wSmall1Pair_fibre_abs_le`. -/
theorem integrable_uint_y {v : E3 → ℝ} {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball 0 R0)
    (hR0 : 0 < R0) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hRd : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (s : Set E3) (z : E3) :
    MeasureTheory.Integrable (fun u : E3 =>
      ∫ y in Submission.BoseGases.acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict s) := by
  set C : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
    * (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      / Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * _root_.BoseGases.a v)) with hC
  set K : Set E3 := Submission.BoseGases.acube ((1 + d) / d) with hK
  have hKfin : ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict s) K ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_
      (Submission.BoseGases.acube_lt_top ((1 + d) / d) (by positivity)))
    rw [MeasureTheory.Measure.restrict_apply (Submission.BoseGases.acube_measurable ((1 + d) / d))]
    exact MeasureTheory.measure_mono (Set.inter_subset_left : (K ∩ s) ⊆ K)
  have hdom : MeasureTheory.Integrable
      (fun u : E3 => |C| * (K.indicator (fun _ => (1 : ℝ)) u))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict s) := by
    rw [show (fun u : E3 => |C| * (K.indicator (fun _ => (1 : ℝ)) u))
        = |C| • (K.indicator (fun _ => (1 : ℝ))) from by
      funext u; rw [Pi.smul_apply, smul_eq_mul]]
    refine MeasureTheory.Integrable.const_mul ?_ |C|
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable _)]
    exact MeasureTheory.integrableOn_const hKfin
  refine Integrable.mono' hdom
    ((aestronglyMeasurable_int_y_u h hM (ℓ := ℓ) (d := d) z).mono_measure
      MeasureTheory.Measure.restrict_le_self) (Filter.Eventually.of_forall (fun u => ?_))
  by_cases hu : u ∈ K
  · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, mul_one, hC]
    exact le_trans (Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0
      hv hvrad h hM hℓ hd hRd hRχ u z) (le_abs_self _)
  · rw [Set.indicator_of_notMem hu]
    have hone : (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u z y) = 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun y => wSmall1Pair_eq_zero_of_notMem_acube h hM hℓ hd hu z y)), integral_zero]
    rw [hone, norm_zero]
    exact mul_nonneg (abs_nonneg _) (by norm_num)

end Work.BoseB1Cube
