import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Local vanishing of a function of two variables -/

/-- `F : ℝ → ℝ → ℝ` vanishes on a square neighbourhood of `(z,θ)`. -/
def LocZero (F : ℝ → ℝ → ℝ) (z θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ z' θ', |z' - z| < ε → |θ' - θ| < ε → F z' θ' = 0

/-- A function vanishing near `(z,θ)` vanishes at `(z,θ)`. -/
theorem LocZero.eq {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) : F z θ = 0 := by
  obtain ⟨ε, hε, hF⟩ := h
  exact hF z θ (by rw [sub_self, abs_zero]; exact hε)
    (by rw [sub_self, abs_zero]; exact hε)

/-- Local vanishing is preserved by `∂_z`. -/
theorem LocZero.pz {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    LocZero (Work.Spaces.pz F) z θ := by
  obtain ⟨ε, hε, hF⟩ := h
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z' θ' hz' hθ'
  rw [Work.Spaces.pz]
  have h1 := abs_lt.mp hz'
  have h2 := abs_lt.mp hθ'
  have hev : (fun z'' => F z'' θ') =ᶠ[𝓝 z'] (fun _ => (0 : ℝ)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds z' (by positivity : (0:ℝ) < ε / 2))
    intro z'' hz''
    rw [Metric.mem_ball, Real.dist_eq] at hz''
    have h3 := abs_lt.mp hz''
    have hzsum : |z'' - z| < ε := by
      rw [show z'' - z = (z'' - z') + (z' - z) by ring]
      exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [h3.1, h3.2, h1.1, h1.2])
    exact hF z'' θ' hzsum (by linarith [h2.1, h2.2])
  have := Filter.EventuallyEq.deriv_eq hev
  rw [deriv_const] at this
  exact this

/-- Local vanishing is preserved by `∂_θ`. -/
theorem LocZero.pth {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    LocZero (Work.Spaces.pth F) z θ := by
  obtain ⟨ε, hε, hF⟩ := h
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z' θ' hz' hθ'
  rw [Work.Spaces.pth]
  have h1 := abs_lt.mp hz'
  have h2 := abs_lt.mp hθ'
  have hev : (fun θ'' => F z' θ'') =ᶠ[𝓝 θ'] (fun _ => (0 : ℝ)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds θ' (by positivity : (0:ℝ) < ε / 2))
    intro θ'' hθ''
    rw [Metric.mem_ball, Real.dist_eq] at hθ''
    have h3 := abs_lt.mp hθ''
    have hthsum : |θ'' - θ| < ε := by
      rw [show θ'' - θ = (θ'' - θ') + (θ' - θ) by ring]
      exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [h3.1, h3.2, h2.1, h2.2])
    exact hF z' θ'' (by linarith [h1.1, h1.2]) hthsum
  have := Filter.EventuallyEq.deriv_eq hev
  rw [deriv_const] at this
  exact this

/-- The product of a locally vanishing function with *any* function vanishes locally. -/
theorem LocZero.mul_left {F G : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    LocZero (fun z θ => G z θ * F z θ) z θ := by
  obtain ⟨ε, hε, hF⟩ := h
  exact ⟨ε, hε, fun z' θ' hz' hθ' => by
    show G z' θ' * F z' θ' = 0
    rw [hF z' θ' hz' hθ', mul_zero]⟩

/-- The product of a locally vanishing function with *any* function vanishes locally. -/
theorem LocZero.mul_right {F G : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero G z θ) :
    LocZero (fun z θ => F z θ * G z θ) z θ := by
  obtain ⟨ε, hε, hF⟩ := h
  exact ⟨ε, hε, fun z' θ' hz' hθ' => by
    show F z' θ' * G z' θ' = 0
    rw [hF z' θ' hz' hθ', mul_zero]⟩

/-- All iterated `∂_z`-derivatives of a locally vanishing function vanish locally. -/
theorem LocZero.pzIter {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    ∀ i, LocZero (Work.Spaces.pzIter i F) z θ
  | 0 => h
  | i + 1 => (h.pzIter i).pz

/-- All iterated `D_z`-derivatives of a locally vanishing function vanish locally. -/
theorem LocZero.DzIter {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    ∀ i, LocZero (Work.Spaces.DzIter i F) z θ
  | 0 => h
  | i + 1 => LocZero.mul_right (F := fun z _ => z) ((h.DzIter i).pz)

/-- All iterated `D_θ`-derivatives of a locally vanishing function vanish locally. -/
theorem LocZero.DthIter {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) :
    ∀ i, LocZero (Work.Spaces.DthIter i F) z θ
  | 0 => h
  | i + 1 =>
      LocZero.mul_right (F := fun _ θ => Real.sin (2 * θ)) ((h.DthIter i).pth)

/-- All mixed `D`-derivatives of a locally vanishing function vanish locally. -/
theorem LocZero.mixed {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : LocZero F z θ) (j i : ℕ) :
    LocZero (Work.Spaces.mixed j i F) z θ :=
  (h.DthIter i).DzIter j

/-! ## The far part is locally zero for `0 < z < Z` -/

/-- For `0 < z < Z` the far part `zfar Z f` vanishes on a neighbourhood of `(z,θ)`: indeed
`chi(z'/Z) = 1` for every `z'` near `z` (and all `θ'`). -/
theorem locZero_zfar {Z : ℝ} (hZ : 0 < Z) (f : F2) {z θ : ℝ} (hz : 0 < z) (hzZ : z < Z) :
    LocZero (zfar Z f) z θ := by
  refine ⟨min z (Z - z), lt_min hz (by linarith), ?_⟩
  intro z' θ' hz' _
  have h1 : |z' - z| < z := lt_of_lt_of_le hz' (min_le_left _ _)
  have h2 : |z' - z| < Z - z := lt_of_lt_of_le hz' (min_le_right _ _)
  have hz'0 : 0 ≤ z' := by have := (abs_lt.mp h1).1; linarith
  have hz'Z : z' ≤ Z := by have := (abs_lt.mp h2).2; linarith
  exact zfar_eq_zero hZ hz'0 hz'Z f θ'

/-- **The far part is locally zero, with all its `D`-derivatives, for `0 < z < Z`.** -/
theorem HkIntegrand_zfar_eq_zero {α : ℝ} {k : ℕ} {Z : ℝ} {f : F2} (hZ : 0 < Z)
    {z θ : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) Z) :
    Work.Spaces.HkIntegrand α k (zfar Z f) z θ = 0 := by
  obtain ⟨hz0, hzZ⟩ := hz
  have hloc : LocZero (zfar Z f) z θ := locZero_zfar hZ f hz0 hzZ
  have hDz : ∀ i, Work.Spaces.DzIter i (zfar Z f) z θ = 0 := fun i => (hloc.DzIter i).eq
  have hmixed : ∀ j i, Work.Spaces.mixed j i (zfar Z f) z θ = 0 :=
    fun j i => (hloc.mixed j i).eq
  rw [Work.Spaces.HkIntegrand]
  simp [hDz, hmixed]

/-- **The `ℋ^k`-integrand of the far part is zero at `z = 0`.**  This is a consequence of the
junk values of Lean's division: the radial weight `w z = (1+z)²/z²` vanishes at `z = 0`, and
every term of the integrand carries a factor `w z`. -/
theorem HkIntegrand_zfar_zero_left (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k F 0 θ = 0 := by
  simp [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]

/-- **The `θ`-integrated `ℋ^k`-integrand of the far part vanishes for `0 ≤ z < Z`.** -/
theorem integral_HkIntegrand_zfar_eq_zero {α : ℝ} {k : ℕ} {Z : ℝ} {f : F2} (hZ : 0 < Z)
    {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) Z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (zfar Z f) z θ) = 0 := by
  rcases eq_or_lt_of_le hz.1 with h | h
  · subst h
    rw [funext (fun θ => HkIntegrand_zfar_zero_left α k (zfar Z f) θ), integral_zero]
  · rw [funext (fun θ => HkIntegrand_zfar_eq_zero hZ ⟨h, hz.2⟩), integral_zero]

/-! ## The elementary integral `∫_Z^∞ M² dz/z² = M²/Z` -/

/-- `M²/z² = M²·z^{-2}` for `z > 0`. -/
theorem div_sq_eq_mul_rpow (M z : ℝ) (hz : 0 < z) :
    M ^ 2 / z ^ 2 = M ^ 2 * z ^ (-2 : ℝ) := by
  rw [div_eq_mul_inv]
  have h : z ^ (-2 : ℝ) = (z ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hz.le (2 : ℝ), Real.rpow_two]
  rw [h]

/-- **The tail integral**: `∫_{z ≥ Z} M²/z² dz = M²/Z` for `Z > 0`. -/
theorem integral_Ici_div_sq {M Z : ℝ} (hZ : 0 < Z) :
    ∫ z in Set.Ici Z, M ^ 2 * z ^ (-2 : ℝ) = M ^ 2 / Z := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  rw [show (fun z => M ^ 2 * z ^ (-2 : ℝ)) = fun z => M ^ 2 • z ^ (-2 : ℝ) from by
    funext z; rw [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hZ]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [smul_eq_mul, div_eq_mul_inv]
  ring

/-! ## The far-tail bound -/

/-- **The `ℋ^k` far-tail bound.**  If the `θ`-integrated `ℋ^k`-integrand of the far part
`zfar Z f = (1 - chi(z/Z))·f` is dominated by `M²/z²` on `z ≥ Z` (`FarTailDom`), then
`|zfar Z f|_{ℋ^k}² ≤ M²/Z`, i.e. `|zfar Z f|_{ℋ^k} ≤ M·Z^{-1/2}`.

In the application `M = O(α + |g₀|_{ℋ⁴})` and `Z = L^α`, so the bound reads
`O((α + |g₀|_{ℋ⁴})·L^{-α/2})` — the `Z^{-1/2}` of the design. -/
theorem HkSqZfar {α : ℝ} {k : ℕ} {M Z : ℝ} {f : F2} (hZ : 0 < Z) (hM : 0 ≤ M)
    (h : FarTailDom α k M Z f) :
    Work.Spaces.HkSq α k (zfar Z f) ≤ M ^ 2 / Z := by
  have hZn : (0 : ℝ) ≤ Z := le_of_lt hZ
  -- the two comparison functions
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (zfar Z f) z θ
    with hG
  set H : ℝ → ℝ := (Set.Ici Z).indicator (fun z => M ^ 2 * z ^ (-2 : ℝ)) with hH
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (zfar Z f) z θ
  have hHmem : ∀ z, Z ≤ z → H z = M ^ 2 * z ^ (-2 : ℝ) := fun z hz => by
    rw [hH]
    exact Set.indicator_of_mem (by simpa [Set.mem_Ici] using hz) _
  have hHnot : ∀ z, ¬ (Z ≤ z) → H z = 0 := fun z hz => by
    rw [hH]
    exact Set.indicator_of_notMem (by simpa [Set.mem_Ici] using hz) _
  -- pointwise comparison on `Iz`
  have hpt : ∀ z ∈ Work.Spaces.Iz, G z ≤ H z := by
    intro z hz
    rcases le_or_gt Z z with hZz | hzZ
    · rw [hHmem z hZz]
      refine le_trans (h z hz hZz) (le_of_eq (div_sq_eq_mul_rpow M z ?_))
      exact lt_of_lt_of_le hZ hZz
    · rw [hHnot z (not_le.mpr hzZ)]
      have hzlt : z < Z := hzZ
      have hz0 : 0 ≤ z := hz
      have : G z = 0 := by
        simp only [hG]
        exact integral_HkIntegrand_zfar_eq_zero hZ ⟨hz0, hzlt⟩
      rw [this]
  -- integrability of the comparison function
  have hIntH : IntegrableOn H Work.Spaces.Iz volume := by
    have hg : IntegrableOn (fun z => M ^ 2 * z ^ (-2 : ℝ)) (Set.Ioi Z) volume :=
      (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hZ).const_mul (M ^ 2)
    have hgIci : IntegrableOn (fun z => M ^ 2 * z ^ (-2 : ℝ)) (Set.Ici Z) volume :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr hg
    have hHI : Integrable H volume := by
      rw [hH]
      exact hgIci.integrable_indicator measurableSet_Ici
    exact hHI.integrableOn (s := Work.Spaces.Iz)
  -- the comparison of the integrals
  have hcmp : ∫ z in Work.Spaces.Iz, G z ≤ ∫ z in Work.Spaces.Iz, H z := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hGnn) hIntH ?_
    show ∀ᵐ z ∂(volume.restrict (Set.Ici (0 : ℝ))), G z ≤ H z
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    exact Filter.Eventually.of_forall fun z hz => hpt z hz
  -- the value of the comparison integral
  have hval : ∫ z in Work.Spaces.Iz, H z = M ^ 2 / Z := by
    have hIci : Work.Spaces.Iz ∩ Set.Ici Z = Set.Ici Z := by
      ext z
      constructor
      · rintro ⟨-, h2⟩; exact h2
      · intro h2; exact ⟨le_trans hZn h2, h2⟩
    rw [hH, MeasureTheory.setIntegral_indicator measurableSet_Ici, hIci]
    exact integral_Ici_div_sq hZ
  have hmain : ∫ z in Work.Spaces.Iz, G z ≤ M ^ 2 / Z := le_trans hcmp (le_of_eq hval)
  simpa only [Work.Spaces.HkSq, hG] using hmain

end Work.Stability
