/-
# `Work.FTS_RegExport.RX0.RecutAux` — the re-cut `hRQ`-consumers of `GalMinConv`

The bundle `Work.FTS.RegExportIface.GalMin'` is `Work.FTS.RegPkgGal.GalMin` with the field

  `hRQ : ∀ τ ∈ Icc 0 S, RegQ (pExp α) 4 (gSlice g τ)`

replaced by the weaker (and producible) interior order-`≤ 2` sup bound `hIS`.  The proof of
`GalMinConv.galHyp_of_galMin` uses `hRQ` in exactly four places:

| use | consumer | replacement here |
|---|---|---|
| `BdryTraces` (only its `a = b = 0` conjunct, for the endpoint vanishing) | `Der.endpoint_cont` | the `θ`-Hölder modulus `St1Class.hhθ` (`endpoint_cont_of_holder`) |
| `mixed 0 0`, `mixed 1 0` pointwise | `Der.sup_extG_ext` | `hIS` at the slots `(0,0)`, `(1,0)` (`sup_extG_ext_hIS`) |
| `mixed 1 0`, `mixed 2 0` pointwise, plus `SmoothQuad` | `Der.sup2_extG_ext` | `hIS` at `(1,0)`, `(2,0)` and `RegPkgMin.c4` (`sup2_extG_ext_hIS`, separate file) |
| `SmoothQuad` (slice regularity only) | `Der.hzmodp_ext` | `RegPkgMin.c4` (`hzmodp_ext_c4`, separate file) |

This file contains the two replacement lemmas that are proved here (the other two are proved by
colleagues in `RX0/sup2_extG_ext_hIS.lean` and `RX0/hzmodp_ext_c4.lean`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS_RegExport.RX0

open Work.FTS.Regularity
open Work.FTS.RegPkgGal (extG extG_of_pos extG_of_nonpos extG_hquad)

set_option autoImplicit false

/-! ## §1 Endpoint continuity of `g̃` from the `θ`-Hölder modulus

`Der.endpoint_cont` obtains the vanishing of the slice `θ ↦ g z θ τ` at `θ = 0` and at
`θ = π/2` from the `a = b = 0` conjunct of `BdryTraces`:  `sin(2θ)^{1-γ}·g² → 0`.
The *same conclusion* follows from the `θ`-Hölder modulus `St1Class.hhθ` of the perturbation
(`|g(z,θ) - g(z,θ')| ≤ Lθ·|θ-θ'|^α`, together with the boundary values `g(z,0) = g(z,π/2) = 0`),
since `|g(z,θ)| ≤ Lθ·|θ|^α → 0`: no boundary trace is needed. -/

/-- `|θ - a|^α → 0` as `θ → a` from either side, for `α > 0`. -/
private lemma tendsto_abs_sub_rpow_zero {α a : ℝ} (hα : 0 < α) {l : Filter ℝ}
    (hl : l ≤ 𝓝 a) : Tendsto (fun θ : ℝ => |θ - a| ^ α) l (𝓝 0) := by
  have hcomp : Tendsto (fun x : ℝ => |x| ^ α) (𝓝 0) (𝓝 0) := by
    have hc := (continuous_abs.continuousAt (x := (0 : ℝ))).rpow_const (Or.inr hα.le)
    simpa [Real.zero_rpow (ne_of_gt hα)] using hc.tendsto
  have hid : Tendsto (fun θ : ℝ => θ - a) l (𝓝 0) := by
    have h1 : Tendsto (fun θ : ℝ => θ - a) (𝓝 a) (𝓝 (a - a)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using (h1.mono_left hl)
  exact hcomp.comp hid

/-- **Endpoint continuity of `g̃` from the `θ`-Hölder modulus** (the replacement of
`Der.endpoint_cont` used by the re-cut assembly).  The hypothesis `hhθ` is
`St1Class.hhθ` verbatim. -/
theorem endpoint_cont_of_holder {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hhθ : ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      ∀ θ' ∈ Work.Spaces.Iθ,
        |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α) :
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (extG g z 0 τ))) ∧
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (extG g z (Real.pi / 2) τ))) := by
  obtain ⟨L, _hL0, hL⟩ := hhθ
  have hpi2 : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  constructor
  · -- `θ → 0⁺`
    intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, extG g z θ τ = 0 := fun θ => extG_of_nonpos hz0
      rw [he 0]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, extG g z θ τ = g z θ τ := fun θ => extG_of_pos hzpos hτ0
      have he0 : extG g z 0 τ = 0 := by rw [hge 0, (hvan τ hτ z (le_of_lt hzpos)).1]
      rw [he0]
      -- the bound `|g z θ τ| ≤ L·|θ|^α` on a neighbourhood of `0` inside `Ioi 0`
      have hle : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ‖g z θ τ‖ ≤ L * |θ - 0| ^ α := by
        have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
          have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := self_mem_nhdsWithin
          have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
            nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hpi2))
          have h3 := inter_mem h1 h2
          rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2)
            = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
        filter_upwards [hmem] with θ hθ
        have h1 := hL τ hτ z (le_of_lt hzpos) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ 0
          ⟨le_refl 0, le_of_lt hpi2⟩
        have heq : |g z θ τ| = |extG g z θ τ - extG g z 0 τ| := by
          rw [hge θ, he0, sub_zero]
        rw [Real.norm_eq_abs, heq]
        exact h1
      have hbound : Tendsto (fun θ : ℝ => L * |θ - 0| ^ α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h0 : Tendsto (fun θ : ℝ => |θ - 0| ^ α) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
          tendsto_abs_sub_rpow_zero (a := 0) hα nhdsWithin_le_nhds
        simpa using h0.const_mul L
      have habs : Tendsto (fun θ : ℝ => ‖g z θ τ‖)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) hle hbound
      have hmain : Tendsto (fun θ : ℝ => g z θ τ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr habs
      exact hmain.congr' (Filter.Eventually.of_forall fun θ => (hge θ).symm)
  · -- `θ → (π/2)⁻`
    intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, extG g z θ τ = 0 := fun θ => extG_of_nonpos hz0
      rw [he (Real.pi / 2)]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, extG g z θ τ = g z θ τ := fun θ => extG_of_pos hzpos hτ0
      have he0 : extG g z (Real.pi / 2) τ = 0 := by
        rw [hge (Real.pi / 2), (hvan τ hτ z (le_of_lt hzpos)).2]
      rw [he0]
      have hle : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
          ‖g z θ τ‖ ≤ L * |θ - Real.pi / 2| ^ α := by
        have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
            nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
          have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
            self_mem_nhdsWithin
          have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
            nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hpi2))
          have h3 := inter_mem h2 h1
          rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2)
            = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
        filter_upwards [hmem] with θ hθ
        have h1 := hL τ hτ z (le_of_lt hzpos) θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (Real.pi / 2)
          ⟨le_of_lt hpi2, le_refl _⟩
        have heq : |g z θ τ| = |extG g z θ τ - extG g z (Real.pi / 2) τ| := by
          rw [hge θ, he0, sub_zero]
        rw [Real.norm_eq_abs, heq]
        exact h1
      have hbound : Tendsto (fun θ : ℝ => L * |θ - Real.pi / 2| ^ α)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
        have h0 : Tendsto (fun θ : ℝ => |θ - Real.pi / 2| ^ α)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
          tendsto_abs_sub_rpow_zero (a := Real.pi / 2) hα nhdsWithin_le_nhds
        simpa using h0.const_mul L
      have habs : Tendsto (fun θ : ℝ => ‖g z θ τ‖)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
        squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) hle hbound
      have hmain : Tendsto (fun θ : ℝ => g z θ τ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr habs
      exact hmain.congr' (Filter.Eventually.of_forall fun θ => (hge θ).symm)

/-! ## §2 The sup bound of `g̃` and `∂_zg̃` from the interior order-`≤ 2` bound

`Der.sup_extG_ext` derives these two bounds from `RegQ (pExp α) 4 (gSlice g τ)` (through the
pointwise trade-off `abs_mixed_le_HkNorm_RegQ`) and the uniform `ℋ⁴` bound.  The interior class
`RegQ` is *not* available in the re-cut bundle, but the two slots that are actually consumed,
`mixed 0 0` and `mixed 1 0`, are bounded by `hIS` outright. -/

/-- **The sup bound of `g̃` and `∂_zg̃` from `hIS`** (the re-cut `Der.sup_extG_ext`).  The
hypothesis `hquad` is `StData.quad`'s second clause for the *extension* slice, verbatim the shape
`GalMinConv` passes. -/
theorem sup_extG_ext_hIS {S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (_hS : 0 < S)
    (hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (gSlice g τ) z θ| ≤ M)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    (hquad : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := hIS
  obtain ⟨Q, hQ0, hQext⟩ := hquad
  -- the near-axis clause for the slice of `g` (transported through `pz_gSlice_extG_eq`)
  have hQ : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ Q * z := by
    intro τ hτ θ hθ z hz hz2
    rw [← Work.FTS.RegPkgGal.Der.pz_gSlice_extG_eq hτ hz]
    exact hQext τ hτ θ hθ z (le_of_lt hz) hz2
  -- the `z`-slot `mixed 1 0 = D_z = z·∂_z`, at every interior point
  have h10 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz (gSlice g τ) z θ| ≤ M / z := by
    intro τ hτ z θ hz hθ hθ'
    have h1 := hM τ hτ 1 0 (by norm_num) z θ hz hθ hθ'
    have h2 : Work.Spaces.mixed 1 0 (gSlice g τ) z θ
        = z * Work.Spaces.pz (gSlice g τ) z θ := rfl
    rw [h2, abs_mul, abs_of_pos hz] at h1
    rw [le_div_iff₀ hz, mul_comm]
    exact h1
  refine ⟨max M (2 * Q), le_trans hM0 (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθ
  have hM1 : M ≤ max M (2 * Q) := le_max_left _ _
  have hM2 : 2 * Q ≤ max M (2 * Q) := le_max_right _ _
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  constructor
  · -- the value bound
    by_cases hz0 : z ≤ 0
    · rw [extG_of_nonpos hz0, abs_zero]
      exact le_trans hM0 (le_max_left _ _)
    · simp only [not_le] at hz0
      rw [extG_of_pos hz0 hτ0]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · rw [← hθz, (hvan τ hτ z (le_of_lt hz0)).1, abs_zero]
        exact le_trans hM0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · rw [hθp, (hvan τ hτ z (le_of_lt hz0)).2, abs_zero]
          exact le_trans hM0 (le_max_left _ _)
        · exact le_trans (hM τ hτ 0 0 (by norm_num) z θ hz0 hθz hθp) hM1
  · -- the derivative bound
    by_cases hz0 : z = 0
    · rw [hz0, extG_hquad g τ θ, abs_zero]
      exact le_trans hM0 (le_max_left _ _)
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hderiv : Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
          = Work.Spaces.pz (gSlice g τ) z θ := by
        have hev : (fun z' => extG g z' θ τ) =ᶠ[𝓝 z] (fun z' => gSlice g τ z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          simp [gSlice, extG_of_pos hz' hτ0]
        exact hev.deriv_eq
      rw [hderiv]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · have hpz0 : Work.Spaces.pz (gSlice g τ) z 0 = 0 := by
          show deriv (fun z' => gSlice g τ z' 0) z = 0
          have hev : (fun z' => gSlice g τ z' 0) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
            exact (hvan τ hτ z' (le_of_lt hz')).1
          rw [hev.deriv_eq]
          exact deriv_const z 0
        rw [← hθz, hpz0, abs_zero]
        exact le_trans hM0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · have hpz0 : Work.Spaces.pz (gSlice g τ) z (Real.pi / 2) = 0 := by
            show deriv (fun z' => gSlice g τ z' (Real.pi / 2)) z = 0
            have hev : (fun z' => gSlice g τ z' (Real.pi / 2)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
              filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
              exact (hvan τ hτ z' (le_of_lt hz')).2
            rw [hev.deriv_eq]
            exact deriv_const z 0
          rw [hθp, hpz0, abs_zero]
          exact le_trans hM0 (le_max_left _ _)
        · by_cases hz2 : z ≤ 2
          · have h1 := hQ τ hτ θ hθ z hzpos hz2
            have h2 : Q * z ≤ 2 * Q := by nlinarith [hQ0, hz, hz2]
            exact le_trans h1 (le_trans h2 hM2)
          · simp only [not_le] at hz2
            have h1 := h10 τ hτ z θ hzpos hθz hθp
            have h2 : M / z ≤ M := by
              have h4 : (1 : ℝ) / z ≤ 1 := by
                rw [div_le_one hzpos]; linarith
              calc M / z = M * (1 / z) := by ring
                _ ≤ M * 1 := mul_le_mul_of_nonneg_left h4 hM0
                _ = M := by ring
            exact le_trans h1 (le_trans h2 hM1)

end Work.FTS_RegExport.RX0
