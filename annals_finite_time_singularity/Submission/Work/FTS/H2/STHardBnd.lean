/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "hard" part of the `SpecialTransport` pairing: integrability of the slots

For each of the five order-five slots of `HardF` (one `D_z`-slot with weight `sin(2θ)^{-η}`
and four mixed slots with weight `sin(2θ)^{-γ}`) we record here

* the measurability of the plain `θ`-derivative (`aestronglyMeasurable_pth`, which is
  `measurable_deriv`),
* the generic integrability of a slot integrand
  `θ ↦ sin(2θ)^{-q}·f(z,θ)·∂_θv(z,θ)·v(z,θ)`
  (`hardSlotIntegrable`), from the pointwise bounds
  `|f| ≤ K sin(2θ)`, `|v| ≤ C sin(2θ)^p`, `|sin(2θ)·∂_θv| ≤ C'` and `q < 1 + p`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.H2.STHardSlot
import Submission.Work.FTS.H2.mixed_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The plain `θ`-derivative of a slice is (almost everywhere) strongly measurable: it is
`deriv` of the slice, and `deriv` of *any* function is measurable. -/
theorem aestronglyMeasurable_pth (v : ℝ → ℝ → ℝ) (z : ℝ) {s : Set ℝ} :
    AEStronglyMeasurable (fun θ => Work.Spaces.pth v z θ) (volume.restrict s) := by
  have h : (fun θ => Work.Spaces.pth v z θ) = deriv (fun θ' => v z θ') := rfl
  rw [h]
  exact ((measurable_deriv _).aestronglyMeasurable).restrict

/-- **Integrability of a single order-five slot integrand.**  If `|f z θ| ≤ K sin(2θ)`,
`|v z θ| ≤ C sin(2θ)^p`, `|sin(2θ)·∂_θv(z,θ)| ≤ C'` on `Iθ` and `q < 1 + p`, then
`θ ↦ sin(2θ)^{-q}·f(z,θ)·∂_θv(z,θ)·v(z,θ)` is integrable on `Iθ`. -/
theorem hardSlotIntegrable {q K C C' p : ℝ} (hq : 0 < q) (hq4 : 0 < 1 + p - q)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hfm : ContinuousOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hvm : ContinuousOn (fun θ => v z θ) Work.Spaces.Iθ)
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p)
    (hv2 : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin (2 * θ) * Work.Spaces.pth v z θ| ≤ C') :
    MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ)
      Work.Spaces.Iθ := by
  have hpi : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  change MeasureTheory.IntegrableOn
    (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ)
    (Set.Icc (0 : ℝ) (π / 2))
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hpi]
  refine intervalIntegrable_of_sin_bound (p := p - q) (C := K * C * C') (by linarith) ?_ ?_
  · have hIθ : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have h1 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const (-q)
    exact ((h1.aestronglyMeasurable.mul (hfm.aestronglyMeasurable hIθ)).mul
      (aestronglyMeasurable_pth v z)).mul (hvm.aestronglyMeasurable hIθ)
  · intro θ hθ
    have hbase : ∀ x : ℝ, 0 ≤ x * (Real.sin (2 * θ)) ^ (p - q) → 0 ≤ K * C * C' * x *
        (Real.sin (2 * θ)) ^ (p - q) := by
      intro x hx
      have : 0 ≤ K * C * C' * (x * (Real.sin (2 * θ)) ^ (p - q)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hK hC) hC') hx
      linarith [this]
    rcases eq_or_lt_of_le (sin_two_nonneg_Iθ hθ) with hs | hs
    · have hz : (Real.sin (2 * θ)) ^ (-q) = 0 := by
        rw [← hs, Real.zero_rpow (by linarith : (-q : ℝ) ≠ 0)]
      rw [hz]
      have : (0 : ℝ) ≤ K * C * C' * (Real.sin (2 * θ)) ^ (p - q) :=
        mul_nonneg (mul_nonneg (mul_nonneg hK hC) hC')
          (Real.rpow_nonneg (le_of_eq hs) _)
      simpa using this
    · have hs1 := rpow_neg_sub_one_mul q hs
      have h1 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) :=
        abs_of_nonneg (Real.rpow_nonneg hs.le _)
      have hpv : Real.sin (2 * θ) * |Work.Spaces.pth v z θ| ≤ C' := by
        have h := hv2 θ hθ
        rwa [abs_mul, abs_of_pos hs] at h
      rw [abs_mul, abs_mul, abs_mul, h1]
      calc (Real.sin (2 * θ)) ^ (-q) * |f z θ| * |Work.Spaces.pth v z θ| * |v z θ|
          = (Real.sin (2 * θ)) ^ (-q - 1) * |f z θ|
              * (Real.sin (2 * θ) * |Work.Spaces.pth v z θ|) * |v z θ| := by
            rw [show (Real.sin (2 * θ)) ^ (-q)
                = (Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ) from hs1.symm]
            ring
        _ ≤ (Real.sin (2 * θ)) ^ (-q - 1) * (K * Real.sin (2 * θ)) * C'
              * (C * (Real.sin (2 * θ)) ^ p) := by
            gcongr
            · exact hf1 θ hθ
            · exact hv1 θ hθ
        _ = K * C * C' * (Real.sin (2 * θ)) ^ (p - q) := by
            rw [show (Real.sin (2 * θ)) ^ (-q - 1) * (K * Real.sin (2 * θ)) * C'
                  * (C * (Real.sin (2 * θ)) ^ p)
                = K * C * C' * ((Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ)
                    * (Real.sin (2 * θ)) ^ p) from by ring,
              hs1, ← Real.rpow_add hs]
            congr 1
            ring_nf


/-! ## The five slots of `HardF` -/

/-- The `g`-block of the `k`-th slot of `HardF` (`k = 0` is the `D_z`-slot with weight
`sin(2θ)^{-η}`; `k = 1,…,4` are the mixed slots with weight `sin(2θ)^{-γ}`). -/
def slotV (g : ℝ → ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0 => Work.Spaces.DzIter 4 g
  | 1 => Work.Spaces.mixed 3 1 g
  | 2 => Work.Spaces.mixed 2 2 g
  | 3 => Work.Spaces.mixed 1 3 g
  | _ => Work.Spaces.mixed 0 4 g

/-- The singular exponent of the `k`-th slot of `HardF`. -/
def slotQ (α : ℝ) : ℕ → ℝ
  | 0 => Work.Spaces.eta
  | _ => Work.Spaces.gam α

/-- The integrand of a single slot of `HardF`. -/
def slotTerm (f v : ℝ → ℝ → ℝ) (q : ℝ) (z θ : ℝ) : ℝ :=
  (Real.sin (2 * θ)) ^ (-q) * f z θ * Work.Spaces.pth v z θ * v z θ

/-- `HardF` is `(w z)^2` times the sum of the five slot integrands. -/
theorem HardF_eq_sum (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HardF α f g z θ = (Work.Spaces.w z) ^ 2 *
      ∑ k ∈ Finset.range 5, slotTerm f (slotV g k) (slotQ α k) z θ := by
  rw [HardF]
  simp only [slotTerm, slotV, slotQ, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-! ## The pointwise data of the two kinds of slot -/

/-- The `θ`-slice of a `SmoothNbhd` function is continuous on `Iθ`. -/
theorem continuousOn_slice_of_smoothNbhd {G : ℝ → ℝ → ℝ} (hG : Work.Spaces.SmoothNbhd G)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => G z θ) Work.Spaces.Iθ := by
  have hG' : ContDiffOn ℝ ⊤ (Function.uncurry G)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := hG
  have hc := contDiffOn_thslice_of_uncurry
    (V := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1))
    (isOpen_Ioi.prod isOpen_Ioo) hG' isOpen_Ioo
    (fun θ' hθ' => ⟨Set.mem_Ioi.mpr (by have hz0 : (0:ℝ) ≤ z := hz; linarith), hθ'⟩)
  exact hc.continuousOn.mono
    (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- The `θ`-slice of a mixed derivative of a `SmoothNbhd` function is continuous. -/
theorem continuousOn_mixed_slice (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g)
    (j i : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => Work.Spaces.mixed j i g z θ) Work.Spaces.Iθ :=
  continuousOn_slice_of_smoothNbhd (Work.Spaces.smoothNbhd_mixed hg j i) hz

/-- The data of the `D_z`-slot (`v = D_z^4 g`, `p = 0`, `q = η`). -/
theorem dzSlot_data (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧
      ContinuousOn (fun θ => Work.Spaces.DzIter 4 g z θ) Work.Spaces.Iθ ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter 4 g z θ|
        ≤ C * (Real.sin (2 * θ)) ^ (0 : ℝ)) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
        |Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ| ≤ C') := by
  have hsmv : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter 4 g) :=
    Work.Spaces.smoothNbhd_DzIter hg 4
  have hbdd : BddAbove (Work.Spaces.boxSet z (Work.Spaces.DzIter 4 g)) :=
    Work.Spaces.bddAbove_boxSup_of_continuousOn
      (Work.Spaces.continuousOn_box_of_contDiffOn hsmv)
  obtain ⟨C', hC'nn, hC'b⟩ := mixed_sin_bound g hg z hz 4 1 (by norm_num)
  refine ⟨Work.Spaces.boxSup z (Work.Spaces.DzIter 4 g), C',
    Work.Spaces.boxSup_nonneg hz hbdd, hC'nn, ?_, ?_, ?_⟩
  · exact continuousOn_slice_of_smoothNbhd hsmv hz
  · intro θ hθ
    have h := Work.Spaces.le_boxSup hbdd ⟨hz, le_refl z⟩ hθ
    rw [Real.rpow_zero]
    simpa using h
  · intro θ hθ
    have hstrp : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
    have h1 : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
        = Work.Spaces.mixed 4 1 g z θ := by
      have hident := sin_mul_pth_mixed g hg 4 0 hstrp
      simpa using hident
    rw [h1]
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    calc |Work.Spaces.mixed 4 1 g z θ| ≤ C' * Real.sin (2 * θ) := hC'b θ hθ
      _ ≤ C' := by nlinarith [hs, Real.sin_le_one (2 * θ), hC'nn]

/-- The data of a mixed slot (`v = D_z^j D_θ^i g`, `i ≥ 1`, `p = 1`, `q = γ`). -/
theorem mixedSlot_data (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j i : ℕ) (hi : 1 ≤ i)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧
      ContinuousOn (fun θ => Work.Spaces.mixed j i g z θ) Work.Spaces.Iθ ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.mixed j i g z θ|
        ≤ C * (Real.sin (2 * θ)) ^ (1 : ℝ)) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
        |Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i g) z θ| ≤ C') := by
  obtain ⟨C, hCnn, hCb⟩ := mixed_sin_bound g hg z hz j i hi
  obtain ⟨C', hC'nn, hC'b⟩ := mixed_sin_bound g hg z hz j (i + 1) (by omega)
  refine ⟨C, C', hCnn, hC'nn, continuousOn_mixed_slice g hg j i hz, ?_, ?_⟩
  · intro θ hθ
    rw [Real.rpow_one]
    exact hCb θ hθ
  · intro θ hθ
    have hstrp : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
    have h1 := sin_mul_pth_mixed g hg j i hstrp
    rw [h1]
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
    calc |Work.Spaces.mixed j (i + 1) g z θ| ≤ C' * Real.sin (2 * θ) := hC'b θ hθ
      _ ≤ C' := by nlinarith [hs, Real.sin_le_one (2 * θ), hC'nn]

/-! ## The energy of a slot is bounded by the `ℋ⁴`-energy -/

/-- Each slot energy is bounded by `HkSq`: the pointwise AM–GM/square comparison, integrated. -/
theorem slot_energy {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hHk : Work.Spaces.HkMem α 4 g) (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) (k : ℕ) (hk : k ∈ Finset.range 5) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (-slotQ α k) * (slotV g k z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have hk4 : k ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hIθ : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  interval_cases k
  · rw [show slotQ α 0 = Work.Spaces.eta from rfl,
      show slotV g 0 = Work.Spaces.DzIter 4 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).1
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
            * (Work.Spaces.DzIter 4 g z θ) ^ 2)
          = (Work.Spaces.DzIter 4 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by ring
        _ = (Work.Spaces.DzIter 4 g z θ * Whz z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl
  · rw [show slotQ α 1 = Work.Spaces.gam α from rfl,
      show slotV g 1 = Work.Spaces.mixed 3 1 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
          = (Work.Spaces.mixed 3 1 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 3 1 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 3 (by norm_num) (by norm_num)
  · rw [show slotQ α 2 = Work.Spaces.gam α from rfl,
      show slotV g 2 = Work.Spaces.mixed 2 2 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 2 2 g z θ) ^ 2)
          = (Work.Spaces.mixed 2 2 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 2 2 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 2 2 (by norm_num) (by norm_num)
  · rw [show slotQ α 3 = Work.Spaces.gam α from rfl,
      show slotV g 3 = Work.Spaces.mixed 1 3 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 1 3 g z θ) ^ 2)
          = (Work.Spaces.mixed 1 3 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 1 3 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 3 1 (by norm_num) (by norm_num)
  · rw [show slotQ α 4 = Work.Spaces.gam α from rfl,
      show slotV g 4 = Work.Spaces.mixed 0 4 g from rfl, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hHk.1 z hz) ?_
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _) (sq_nonneg _))
    · filter_upwards [ae_restrict_mem hIθ] with θ hθ
      have hW := (Whz_Wm_sq α hα z θ hθ).2
      calc (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 0 4 g z θ) ^ 2)
          = (Work.Spaces.mixed 0 4 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ = (Work.Spaces.mixed 0 4 g z θ * Wm α z θ) ^ 2 := by rw [← hW]; ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 4 0 (by norm_num) (by norm_num)

end Work.FTS.H2
