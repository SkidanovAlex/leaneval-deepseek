/-
# `Work.FTS.RegPkgGal.Der.endpoint_cont` — continuity of `g̃` at the two angular endpoints

The extension `g̃ = Work.FTS.RegPkgGal.extG g` of design §4 is, by construction, `0` on the closed
left half-plane `{z ≤ 0}` and agrees with `g` on `{z > 0} × {τ ≥ 0}`.  Consequently the *only*
content of the requested endpoint continuity in `θ` is:

* at `z ≤ 0` both endpoint values are `0` and the whole slice is identically `0`;
* at `z > 0` the two endpoint values vanish (`hvan`), and the slice `θ ↦ g z θ τ` must tend to `0`
  at `θ → 0⁺` and at `θ → π/2⁻`.

The second point is exactly the `a = b = 0` instance of the *second* family of conjuncts of
`BdryTraces (pExp α) 4 (gSlice g τ)`, which says

  `sin(2θ)^{1-γ} · g(z,θ,τ)² → 0`  at `θ → 0⁺` and at `θ → π/2⁻`  (`γ = gam (pExp α)`).

Since `γ = 1 + α/10 > 1` (so `1 - γ ≤ 0`) and `0 < sin(2θ) ≤ 1` for `θ ∈ (0, π/2)`, the
`sin`-weight is `≥ 1` there, whence `g² ≤ sin(2θ)^{1-γ}·g² → 0` by squeezing; `Real.sqrt` of
`(g)²` is `|g|`, and `|g| → 0` is `g → 0`.

**File-level note.**  As delivered, the statement could not elaborate at all: the bare `π` of the
statement is not the notation for `Real.pi` unless the `Real` scope is open, and this file (with
`autoImplicit` off, inherited from the imports) reported `Unknown identifier 'π'`.  The addition of
`open scoped Real` below makes that `π` mean `Real.pi` — the only reading under which the two
occurrences of `π` in the statement (in `hvan` and in the conclusion) are compatible with the
`Real.pi / 2` which the other conjunct of the statement displays.  Nothing in the statement itself
is changed.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-! ## Elementary `θ`-facts at the two endpoints -/

/-- For `θ ∈ (0, π/2)`, `sin (2θ)` lies in `(0,1]`. -/
lemma sin_two_pos_and_le_one {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 :=
  ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]),
   Real.sin_le_one (2 * θ)⟩

/-- For `0 < s ≤ 1` and `1 ≤ γ` one has `1 ≤ s ^ (1 - γ)`: the (negative) exponent `1 - γ` makes
`s ^ (1 - γ) = (s ^ (γ - 1))⁻¹ ≥ 1⁻¹ = 1`. -/
lemma one_le_rpow_one_sub {γ s : ℝ} (hγ : 1 ≤ γ) (hs : 0 < s) (hs1 : s ≤ 1) :
    1 ≤ s ^ (1 - γ) := by
  have hpos : 0 < s ^ (γ - 1) := Real.rpow_pos_of_pos hs _
  have hle : s ^ (γ - 1) ≤ 1 := by
    have h := Real.rpow_le_rpow (le_of_lt hs) hs1 (by linarith : (0 : ℝ) ≤ γ - 1)
    rwa [Real.one_rpow] at h
  have h1 : s ^ (1 - γ) = (s ^ (γ - 1))⁻¹ := by
    have h1' : (1 : ℝ) - γ = -(γ - 1) := by ring
    rw [h1', Real.rpow_neg (le_of_lt hs)]
  rw [h1]
  exact (one_le_inv₀ hpos).mpr hle

/-- **Squeezing through a `sin`-weight.**  If `s θ ∈ (0,1]` eventually and `u ≥ 0` eventually,
then `s θ ^ (1-γ) · u θ → 0` with `γ ≥ 1` forces `u θ → 0` (the weight is eventually `≥ 1`, so
`0 ≤ u ≤ s^{1-γ}·u`). -/
lemma tendsto_zero_of_rpow_mul {γ : ℝ} (hγ : 1 ≤ γ) {l : Filter ℝ} {s u : ℝ → ℝ}
    (hs : ∀ᶠ θ in l, 0 < s θ ∧ s θ ≤ 1) (hu : ∀ᶠ θ in l, 0 ≤ u θ)
    (h : Tendsto (fun θ => s θ ^ (1 - γ) * u θ) l (𝓝 0)) : Tendsto u l (𝓝 0) := by
  refine squeeze_zero' hu ?_ h
  filter_upwards [hs, hu] with θ hθ huθ
  exact le_mul_of_one_le_left huθ (one_le_rpow_one_sub hγ hθ.1 hθ.2)

/-! ## Vanishing of a slice at both angular endpoints, from the boundary traces -/

/-- **The `a = b = 0` conjunct of `BdryTraces` gives endpoint vanishing of the slice.**  If `f`
carries the order-`4` boundary traces with exponent `pExp α`, then for every `z > 0` the slice
`θ ↦ f z θ` tends to `0` both at `θ → 0⁺` and at `θ → π/2⁻`. -/
lemma tendsto_slice_zero_of_bdryTraces {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hb : Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 f) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) ∧
      Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
  have hγ : (1 : ℝ) ≤ Work.Spaces.gam (Work.FTS.Regularity.pExp α) :=
    le_of_lt (Work.Spaces.one_lt_gam (Work.FTS.Regularity.pExp_pos hα))
  obtain ⟨h0, hπ⟩ := (hb 0 0 (by norm_num)).2 z hz
  have h0' : Tendsto (fun θ => Real.sin (2 * θ) ^
        (1 - Work.Spaces.gam (Work.FTS.Regularity.pExp α)) * f z θ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by simpa using h0
  have hπ' : Tendsto (fun θ => Real.sin (2 * θ) ^
        (1 - Work.Spaces.gam (Work.FTS.Regularity.pExp α)) * f z θ ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by simpa using hπ
  have hsmall₀ : ∀ᶠ θ in nhdsWithin 0 (Set.Ioi 0),
      0 < Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
    have hm : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin 0 (Set.Ioi 0) := by
      have h1 : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := self_mem_nhdsWithin
      have h2 : Set.Iio (Real.pi / 2) ∈ nhdsWithin 0 (Set.Ioi 0) :=
        nhdsWithin_le_nhds
          (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr (by linarith [Real.pi_pos])))
      have h3 := inter_mem h1 h2
      rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
    filter_upwards [hm] with θ hθ
    exact sin_two_pos_and_le_one hθ
  have hsmall₁ : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      0 < Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1 := by
    have hm : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
        nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
      have h1 : Set.Iio (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
        self_mem_nhdsWithin
      have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
        nhdsWithin_le_nhds
          (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith [Real.pi_pos])))
      have h3 := inter_mem h2 h1
      rwa [show Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) from rfl] at h3
    filter_upwards [hm] with θ hθ
    exact sin_two_pos_and_le_one hθ
  have key : ∀ {l : Filter ℝ},
      (∀ᶠ θ in l, 0 < Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 1) →
      Tendsto (fun θ => Real.sin (2 * θ) ^
        (1 - Work.Spaces.gam (Work.FTS.Regularity.pExp α)) * f z θ ^ 2) l (𝓝 0) →
      Tendsto (fun θ => f z θ) l (𝓝 0) := by
    intro l hs h
    have hsq : Tendsto (fun θ => f z θ ^ 2) l (𝓝 0) :=
      tendsto_zero_of_rpow_mul hγ hs (Filter.Eventually.of_forall fun θ => sq_nonneg _) h
    have h2 : Tendsto (fun θ => Real.sqrt (f z θ ^ 2)) l (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hsq
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using h2
  exact ⟨key hsmall₀ h0', key hsmall₁ hπ'⟩

/-! ## The target -/

theorem endpoint_cont {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hS : 0 < S)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hBT : ∀ τ ∈ Set.Icc 0 S,
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Regularity.gSlice g τ)) :
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => Work.FTS.RegPkgGal.extG g z θ τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (Work.FTS.RegPkgGal.extG g z 0 τ))) ∧
    (∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => Work.FTS.RegPkgGal.extG g z θ τ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (Work.FTS.RegPkgGal.extG g z (Real.pi / 2) τ))) := by
  constructor
  · intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, Work.FTS.RegPkgGal.extG g z θ τ = 0 :=
        fun θ => Work.FTS.RegPkgGal.extG_of_nonpos hz0
      rw [he 0]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, Work.FTS.RegPkgGal.extG g z θ τ = g z θ τ :=
        fun θ => Work.FTS.RegPkgGal.extG_of_pos hzpos hτ0
      have he0 : Work.FTS.RegPkgGal.extG g z 0 τ = 0 := by
        rw [hge 0, (hvan τ hτ z (le_of_lt hzpos)).1]
      rw [he0]
      exact (tendsto_slice_zero_of_bdryTraces hα (hBT τ hτ) hzpos).1.congr'
        (Filter.Eventually.of_forall fun θ => (hge θ).symm)
  · intro τ hτ z hz
    rcases le_or_gt z 0 with hz0 | hzpos
    · have he : ∀ θ : ℝ, Work.FTS.RegPkgGal.extG g z θ τ = 0 :=
        fun θ => Work.FTS.RegPkgGal.extG_of_nonpos hz0
      rw [he (Real.pi / 2)]
      exact Tendsto.congr' (Filter.Eventually.of_forall fun θ => (he θ).symm) tendsto_const_nhds
    · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
      have hge : ∀ θ : ℝ, Work.FTS.RegPkgGal.extG g z θ τ = g z θ τ :=
        fun θ => Work.FTS.RegPkgGal.extG_of_pos hzpos hτ0
      have he0 : Work.FTS.RegPkgGal.extG g z (Real.pi / 2) τ = 0 := by
        rw [hge (Real.pi / 2), (hvan τ hτ z (le_of_lt hzpos)).2]
      rw [he0]
      exact (tendsto_slice_zero_of_bdryTraces hα (hBT τ hτ) hzpos).2.congr'
        (Filter.Eventually.of_forall fun θ => (hge θ).symm)

end Work.FTS.RegPkgGal.Der
