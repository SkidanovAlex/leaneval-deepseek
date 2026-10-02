import Submission.Work.Landing.Land
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.Landing.Rays.image_dynRay_subset
import Submission.Work.Landing.Rays.preimage_mem_dynRay
import Submission.Work.Landing.Rays.dynRay_sublevel_infinite
import Submission.Work.Landing.Rays.isBounded_dynRay_sublevel
import Submission.Work.Landing.Rays.radialRay_norm
import Submission.Work.Landing.Family.tantibar_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The ray transfer and the landing theorem for the tricorn

This file assembles the leaves of the landing area into the statements the rest of the project
consumes:

* `Work.Landing.trunc` : the truncation `{z ∈ R_c(θ) : ‖φ z‖ ≤ ρ}` of a dynamic ray;
* `Work.Landing.rayAccum_image` : `T_c` maps the accumulation set of the ray at angle `θ` onto
  the accumulation set of the ray at angle `angDouble θ = -2θ mod 1`;
* `Work.Landing.RayLands_image`, `Work.Landing.rayAccum_iterate`, `Work.Landing.RayLands_periodic`,
  `Work.Landing.landsAt_image`, `Work.Landing.landsAt_periodic`, `Work.Landing.landsAt_unique` :
  the induced statements at the level of landing, including the fundamental one: **the landing
  point of a periodic ray is a periodic point**;
* `Work.Landing.landsAt_repelling_or_parabolic` : **Milnor 18.10**, the landing point of a
  periodic ray of odd period is repelling or parabolic.

The transfer is proved from the characterisation `IsDynBottcher` alone.  The critical value `c`
(whose only preimage is the critical point `0`) is the only exceptional point, and it is handled
explicitly.
-/

noncomputable section

open Classical
open Filter

namespace Work.Landing

open Function
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet)
open scoped Topology ComplexConjugate

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The truncation of the dynamic ray `R_c(θ)` at Böttcher modulus `ρ`. -/
def trunc (c : ℂ) (φ : ℂ → ℂ) (θ ρ : ℝ) : Set ℂ := {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ ρ}

@[simp]
theorem mem_trunc {z : ℂ} {θ ρ : ℝ} :
    z ∈ trunc c φ θ ρ ↔ z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ ρ := Iff.rfl

theorem trunc_mono {θ ρ ρ' : ℝ} (h : ρ ≤ ρ') : trunc c φ θ ρ ⊆ trunc c φ θ ρ' :=
  fun _ hz => ⟨hz.1, le_trans hz.2 h⟩

theorem rayAccum_def (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    rayAccum c φ θ = {x : ℂ | ∀ ρ : ℝ, 1 < ρ → x ∈ closure (trunc c φ θ ρ)} := rfl

theorem rayAccum_mono {θ : ℝ} {x : ℂ} (hx : x ∈ rayAccum c φ θ) {ρ : ℝ} (hρ : 1 < ρ) :
    x ∈ closure (trunc c φ θ ρ) := hx ρ hρ

/-! ## The three ingredients of the transfer -/

/-- The image of a truncation lies in the truncation of the image ray at the squared modulus. -/
theorem image_trunc_subset (h : IsDynBottcher c φ) (θ : ℝ) {ρ : ℝ} :
    Tantibar c '' trunc c φ θ ρ ⊆ trunc c φ (angDouble θ) (ρ ^ 2) := by
  rintro w ⟨z, hz, rfl⟩
  refine ⟨Work.Landing.Rays.image_dynRay_subset h θ ⟨z, hz.1, rfl⟩, ?_⟩
  have hfe : φ (Tantibar c z) = conj (φ z) ^ 2 := h.2.1 z hz.1.1
  rw [hfe, Complex.norm_pow, Complex.norm_conj]
  nlinarith [norm_nonneg (φ z), hz.2]

/-- Every point of a truncation of a ray, except the critical value, has a preimage on the
truncation of the source ray. -/
theorem trunc_subset_image_trunc (h : IsDynBottcher c φ) (θ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    trunc c φ (angDouble θ) σ \ {c} ⊆ Tantibar c '' trunc c φ θ (Real.sqrt σ) := by
  rintro w ⟨hw, hwc⟩
  obtain ⟨z, hz, hzw⟩ := Work.Landing.Rays.preimage_mem_dynRay h hw.1 hwc
  refine ⟨z, ⟨hz, ?_⟩, hzw⟩
  have hfe : φ (Tantibar c z) = conj (φ z) ^ 2 := h.2.1 z hz.1
  rw [hzw] at hfe
  have hn : ‖φ w‖ = ‖φ z‖ ^ 2 := by rw [hfe, Complex.norm_pow, Complex.norm_conj]
  rw [Real.le_sqrt (norm_nonneg _) (zero_le_one.trans hσ.le), ← hn]
  exact hw.2

/-- The closure of the image of a truncation is the image of its closure (the truncation is
bounded, so its closure is compact). -/
theorem closure_image_trunc (h : IsDynBottcher c φ) (θ ρ : ℝ) :
    closure (Tantibar c '' trunc c φ θ ρ) = Tantibar c '' closure (trunc c φ θ ρ) := by
  have hcont : Continuous (Tantibar c) := Work.Landing.Family.tantibar_continuous c
  have hclosed : IsClosed (Tantibar c '' closure (trunc c φ θ ρ)) :=
    ((Work.Landing.Rays.isBounded_dynRay_sublevel h θ ρ).isCompact_closure.image hcont).isClosed
  exact Set.Subset.antisymm
    (hclosed.closure_subset_iff.mpr (Set.image_mono subset_closure))
    (image_closure_subset_closure_image hcont)

/-- A point of the closure of a set which is not the point `a` lies in the closure of the set
with `a` removed. -/
theorem mem_closure_sdiff_singleton {s : Set ℂ} {a y : ℂ} (hy : y ∈ closure s) (hne : y ≠ a) :
    y ∈ closure (s \ {a}) := by
  rw [Metric.mem_closure_iff] at hy ⊢
  intro ε hε
  have hδ : 0 < dist y a := dist_pos.mpr hne
  obtain ⟨x, hx, hxd⟩ := hy (min ε (dist y a / 2)) (lt_min hε (by linarith))
  have hxa : x ≠ a := by
    intro hxa
    have h1 : dist y x < dist y a / 2 := lt_of_lt_of_le hxd (min_le_right _ _)
    rw [hxa] at h1
    linarith
  exact ⟨x, ⟨hx, hxa⟩, lt_of_lt_of_le hxd (min_le_left _ _)⟩

/-- A point of the closure of a set which does not belong to the set lies in the closure of the
set with itself removed. -/
theorem mem_closure_sdiff_of_notMem {s : Set ℂ} {y : ℂ} (hy : y ∈ closure s) (hns : y ∉ s) :
    y ∈ closure (s \ {y}) := by
  rw [Metric.mem_closure_iff] at hy ⊢
  intro ε hε
  obtain ⟨x, hx, hxd⟩ := hy ε hε
  exact ⟨x, ⟨hx, fun hxy => hns (hxy ▸ hx)⟩, hxd⟩

/-! ## The transfer -/

/-- **The ray transfer.**  The accumulation set of the dynamic ray at angle `θ` is mapped by
`T_c` onto the accumulation set of the ray at angle `angDouble θ = -2θ mod 1`. -/
theorem rayAccum_image (h : IsDynBottcher c φ) (θ : ℝ) :
    Tantibar c '' rayAccum c φ θ = rayAccum c φ (angDouble θ) := by
  have hcont : Continuous (Tantibar c) := Work.Landing.Family.tantibar_continuous c
  refine Set.Subset.antisymm ?_ ?_
  · -- forward: images of accumulation points are accumulation points
    rintro y ⟨x, hx, rfl⟩ σ hσ
    have hρ1 : 1 < Real.sqrt σ := by
      nlinarith [Real.sq_sqrt (x := σ) (zero_le_one.trans hσ.le), Real.sqrt_nonneg σ]
    have h1 : Tantibar c '' closure (trunc c φ θ (Real.sqrt σ)) ⊆
        closure (Tantibar c '' trunc c φ θ (Real.sqrt σ)) :=
      image_closure_subset_closure_image hcont
    have h2 : closure (Tantibar c '' trunc c φ θ (Real.sqrt σ)) ⊆
        closure (trunc c φ (angDouble θ) σ) := by
      refine closure_mono ?_
      have hsq : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt (x := σ) (zero_le_one.trans hσ.le)
      simpa [hsq] using image_trunc_subset (ρ := Real.sqrt σ) h θ
    exact h2 (h1 ⟨x, rayAccum_mono hx hρ1, rfl⟩)
  · -- backward: prescribe preimages on the source ray
    intro y hy
    by_cases hyc : y = c
    · -- the critical value is the image of the critical point
      rw [hyc] at hy ⊢
      have h0 : (0 : ℂ) ∈ rayAccum c φ θ := by
        -- a radius at which the critical value is not on the image ray
        obtain ⟨σ₀, hσ₀1, hσ₀c⟩ :
            ∃ σ₀ : ℝ, 1 < σ₀ ∧ c ∉ trunc c φ (angDouble θ) σ₀ := by
          by_cases hnc : 1 < ‖φ c‖
          · refine ⟨(1 + ‖φ c‖) / 2, by linarith, fun hmem => ?_⟩
            exact absurd hmem.2 (by linarith)
          · refine ⟨2, one_lt_two, fun hmem => ?_⟩
            exact hnc (Work.Landing.Rays.radialRay_norm hmem.1.2)
        intro ρ hρ
        have hρ1 : 1 < ρ ^ 2 := by nlinarith
        set σ : ℝ := (1 + min (ρ ^ 2) σ₀) / 2 with hσdef
        have hσ1 : 1 < σ := by
          rw [hσdef]
          have hmin : 1 < min (ρ ^ 2) σ₀ := lt_min hρ1 hσ₀1
          linarith
        have hσσ₀ : σ < σ₀ := by
          rw [hσdef]; nlinarith [min_le_right (ρ ^ 2) σ₀]
        have hσρ : Real.sqrt σ ≤ ρ := by
          have hlt : σ < ρ ^ 2 := by
            rw [hσdef]; nlinarith [min_le_left (ρ ^ 2) σ₀]
          nlinarith [Real.sq_sqrt (x := σ) (zero_le_one.trans hσ1.le), Real.sqrt_nonneg σ]
        -- the critical value is a limit of ray points distinct from it, and those have preimages
        have hnotmem : c ∉ trunc c φ (angDouble θ) σ := fun hmem =>
          hσ₀c ⟨hmem.1, le_trans hmem.2 hσσ₀.le⟩
        have hcl : c ∈ closure (Tantibar c '' trunc c φ θ (Real.sqrt σ)) :=
          closure_mono (trunc_subset_image_trunc h θ hσ1)
            (mem_closure_sdiff_of_notMem (hy σ hσ1) hnotmem)
        have hcimg : c ∈ Tantibar c '' closure (trunc c φ θ (Real.sqrt σ)) := by
          rw [← closure_image_trunc h θ (Real.sqrt σ)]
          exact hcl
        obtain ⟨z, hz, hzc⟩ := hcimg
        have hz0 : z = 0 := by
          have h2 : (starRingEnd ℂ z) ^ 2 = 0 := by
            have hc_eq : (starRingEnd ℂ z) ^ 2 + c = c := hzc
            exact add_right_cancel (show (starRingEnd ℂ z) ^ 2 + c = 0 + c by simpa using hc_eq)
          have h3 : starRingEnd ℂ z = 0 := pow_eq_zero_iff (by norm_num) |>.mp h2
          simpa using h3
        rw [hz0] at hz
        exact closure_mono (trunc_mono hσρ) hz
      exact ⟨0, h0, by simp [Tantibar]⟩
    · -- a non-critical point of the image ray: pull it back along the ray
      have hseq : ∀ n : ℕ, ∃ x : ℂ, x ∈ closure (trunc c φ θ (Real.sqrt (1 + 1/((n:ℝ)+1)))) ∧
          Tantibar c x = y := by
        intro n
        have hσ1 : 1 < 1 + 1/((n:ℝ)+1) := by
          have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
          linarith
        have hmemc : y ∈ closure (trunc c φ (angDouble θ) (1 + 1/((n:ℝ)+1)) \ {c}) :=
          mem_closure_sdiff_singleton (hy _ hσ1) hyc
        have hy' : y ∈ closure (Tantibar c '' trunc c φ θ (Real.sqrt (1 + 1/((n:ℝ)+1)))) :=
          closure_mono (trunc_subset_image_trunc h θ hσ1) hmemc
        rw [closure_image_trunc h θ (Real.sqrt (1 + 1/((n:ℝ)+1)))] at hy'
        exact hy'
      choose x hx hTx using hseq
      -- the sequence of preimages is bounded, so it has a convergent subsequence
      have hmem : ∀ n : ℕ, x n ∈ closure (trunc c φ θ (Real.sqrt 2)) := by
        intro n
        refine closure_mono (trunc_mono ?_) (hx n)
        have hle : 1 + 1/((n:ℝ)+1) ≤ 2 := by
          have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
          have hnpos : (0:ℝ) ≤ (n:ℝ) := by positivity
          have h1 : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
            rw [div_le_one hpos]
            linarith
          linarith
        exact Real.sqrt_le_sqrt hle
      have hbd : Bornology.IsBounded (trunc c φ θ (Real.sqrt 2)) :=
        Work.Landing.Rays.isBounded_dynRay_sublevel h θ (Real.sqrt 2)
      obtain ⟨x₀, -, ψf, hψmono, hψtend⟩ :=
        hbd.isCompact_closure.tendsto_subseq (fun n => hmem n)
      refine ⟨x₀, ?_, ?_⟩
      · -- the limit lies in the accumulation set of the source ray
        intro ρ hρ
        have htend : Tendsto (fun n : ℕ => Real.sqrt (1 + 1/((n:ℝ)+1))) atTop (𝓝 1) := by
          have hcst : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
          have hdiv : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have hone : Tendsto (fun n : ℕ => (1:ℝ) + 1/((n:ℝ)+1)) atTop (𝓝 1) := by
            simpa using hcst.add hdiv
          have hcomp : Tendsto (fun n : ℕ => Real.sqrt (1 + 1/((n:ℝ)+1))) atTop (𝓝 (Real.sqrt 1)) :=
            (Real.continuous_sqrt.tendsto 1).comp hone
          rwa [Real.sqrt_one] at hcomp
        have hev : ∀ᶠ n : ℕ in atTop, Real.sqrt (1 + 1/((n:ℝ)+1)) ≤ ρ :=
          (htend.eventually_lt tendsto_const_nhds hρ).mono fun n hn => hn.le
        have hψ : Tendsto (fun n : ℕ => x (ψf n)) atTop (𝓝 x₀) := hψtend
        have hmono : Tendsto ψf atTop atTop := hψmono.tendsto_atTop
        have hev₂ : ∀ᶠ n : ℕ in atTop, Real.sqrt (1 + (1:ℝ)/(((ψf n):ℝ)+1)) ≤ ρ :=
          hmono.eventually hev
        refine (isClosed_closure).mem_of_tendsto hψ ?_
        filter_upwards [hev₂] with n hn
        exact closure_mono (trunc_mono hn) (hx (ψf n))
      · -- and it maps to `y`
        have h1 : Tendsto (fun n : ℕ => Tantibar c (x (ψf n))) atTop (𝓝 (Tantibar c x₀)) :=
          hcont.continuousAt.tendsto.comp hψtend
        have h2 : Tendsto (fun n : ℕ => Tantibar c (x (ψf n))) atTop (𝓝 y) := by
          simpa only [hTx] using tendsto_const_nhds
        exact tendsto_nhds_unique h1 h2

end Work.Landing
