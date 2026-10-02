import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.exists_preimage_rayAccum
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.rayAccum_mem_of_limit
import Submission.Work.LandLeaves.rayAccum_subset_of_limit_alt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Pointwise
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The type is invariant under the second-return angle map -/

/-- The second-return angle map `σ = (angDouble)^[2k]` maps the type of `y` into itself: this is
the ray transfer `τ '' R_θ = R_{σθ}` together with `τ y = y`. -/
theorem rayAccum_angDouble_singleton {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] θ) = {y} := by
  obtain ⟨hper, -⟩ := hrep
  have h2k : (Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hper.2, hper.2]
  rw [Work.Landing.rayAccum_iterate hφ θ (2 * k), h, Set.image_singleton, h2k]

/-! ## The type depends on the angle only modulo `1` -/

/-- The type `{ψ | rayAccum c φ ψ = {y}}` is invariant under `ψ ↦ ψ + m`, `m ∈ ℤ`. -/
theorem rayAccum_add_int_type (c : ℂ) (φ : ℂ → ℂ) (y : ℂ) (m : ℤ) :
    {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}}
      = {ψ : ℝ | Work.Landing.rayAccum c φ (ψ + m) = {y}} := by
  ext ψ
  simp only [Set.mem_setOf_eq]
  rw [Work.FSeed.rayAccum_add_int]

/-- Finiteness of the type on the fundamental domain `[0,1)` gives closedness of the type: the
type is the `ℤ`-orbit of its trace on `[0,1)`. -/
theorem isClosed_of_finite_type {c : ℂ} {φ : ℂ → ℂ} {y : ℂ}
    (hfin : ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite) :
    IsClosed {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} := by
  set S : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} with hS
  have hZ : IsClosed (Set.range ((↑) : ℤ → ℝ)) := by
    rw [← isOpen_compl_iff]
    have hcompl : (Set.range ((↑) : ℤ → ℝ))ᶜ
        = Set.iUnion (fun n : ℤ => Set.Ioo (n : ℝ) ((n : ℝ) + 1)) := by
      ext x
      constructor
      · intro hx
        refine Set.mem_iUnion.mpr ⟨⌊x⌋, ?_⟩
        have hlt : ((⌊x⌋ : ℤ) : ℝ) < x :=
          lt_of_le_of_ne (Int.floor_le x) (fun h => hx ⟨⌊x⌋, h⟩)
        exact ⟨hlt, Int.lt_floor_add_one x⟩
      · intro hx1 hx2
        obtain ⟨n, hn1, hn2⟩ := Set.mem_iUnion.mp hx1
        obtain ⟨m, hm⟩ := hx2
        rw [← hm] at hn1 hn2
        have hn1' : n < m := by exact_mod_cast hn1
        have hn2' : m < n + 1 := by exact_mod_cast hn2
        omega
    rw [hcompl]
    exact isOpen_iUnion fun n => isOpen_Ioo
  have hper : ∀ ψ : ℝ, ψ ∈ S ↔ Int.fract ψ ∈ S := by
    intro ψ
    have h : ψ = Int.fract ψ + ((⌊ψ⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor ψ
      linarith
    conv_lhs => rw [h]
    rw [hS]
    simp only [Set.mem_ofPred_eq]
    rw [Work.FSeed.rayAccum_add_int]
  have hS_eq : S = ⋃ s ∈ hfin.toFinset, (⋃ m : ℤ, ({s + ((m : ℤ) : ℝ)} : Set ℝ)) := by
    ext ψ
    constructor
    · intro hψ
      have h1 : Int.fract ψ ∈ S := (hper ψ).mp hψ
      have h2 : Int.fract ψ ∈ ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1) :=
        ⟨h1, Int.fract_nonneg ψ, Int.fract_lt_one ψ⟩
      rw [Set.mem_iUnion]
      refine ⟨Int.fract ψ, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨?_, ?_⟩
      · rwa [Set.Finite.mem_toFinset]
      · rw [Set.mem_iUnion]
        refine ⟨⌊ψ⌋, ?_⟩
        simp only [Set.mem_singleton_iff]
        have h := Int.fract_add_floor ψ
        linarith
    · intro hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨s, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨hs, hmem⟩ := hmem
      rw [Set.Finite.mem_toFinset] at hs
      obtain ⟨hsS, -⟩ := hs
      rw [Set.mem_iUnion] at hmem
      obtain ⟨m, hmem⟩ := hmem
      simp only [Set.mem_singleton_iff] at hmem
      rw [hmem]
      exact (hper (s + ((m : ℤ) : ℝ))).mpr
        (by rw [Int.fract_add_intCast]; exact (hper s).mp hsS)
  rw [hS_eq]
  refine isClosed_biUnion_finset fun s _ => ?_
  have htrans : (⋃ m : ℤ, ({s + ((m : ℤ) : ℝ)} : Set ℝ))
      = (fun ψ : ℝ => ψ - s) ⁻¹' (Set.range ((↑) : ℤ → ℝ)) := by
    ext ψ
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, by push_cast; ring⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, by push_cast at hm ⊢; linarith⟩
  rw [htrans]
  exact hZ.preimage (continuous_id.sub continuous_const)

/-! ## Sequential closedness -/

/-- **The type of a repelling periodic point is sequentially closed.**

A limit `θ` of angles whose rays accumulate exactly at `y` is again an angle of the type: the two
halves are

* `rayAccum c φ θ ⊆ {y}` (`Work.LandLeaves.rayAccum_subset_of_limit_alt`, the "no jump-up" half,
  which goes through the Goldberg-Milnor finiteness of the type together with the Douady-Yoccoz
  anchor `Work.LandLeaves.V2Anchor.periodicTypeAngle_of_landingRay`), and
* `y ∈ rayAccum c φ θ` (`Work.LandLeaves.rayAccum_mem_of_limit`, which combines the previous
  point with the nonemptiness of the accumulation set). -/
theorem mem_type_of_tendsto_type {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ} {u : ℕ → ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (hu : Filter.Tendsto u Filter.atTop (nhds θ))
    (h : ∀ n : ℕ, Work.Landing.rayAccum c φ (u n) = {y}) :
    Work.Landing.rayAccum c φ θ = {y} :=
  le_antisymm (rayAccum_subset_of_limit_alt hφ hrep hu h)
    (Set.singleton_subset_iff.mpr (rayAccum_mem_of_limit hφ hrep hu h))

/-! ## The statement -/

/-- **Closedness of the set of angles of rays landing at a repelling periodic point.**

`φ` a Bottcher coordinate of `T_c`, `y` a repelling periodic point of odd period `k`.  Then the
set of angles whose dynamic ray has accumulation set exactly the singleton `{y}` is closed in `ℝ`:
if `ψ_n → ψ` and each ray `R_{ψ_n}` accumulates at `y` and nowhere else, then so does `R_ψ`.

The two halves are `Work.LandLeaves.rayAccum_subset_of_limit_alt` (no jump-up) and
`Work.LandLeaves.rayAccum_mem_of_limit` (`y` is a limit point); the sequential criterion for
closedness in the first countable space `ℝ` finishes the proof.

The statement is phrased with the set-builder so that it can be imported by the module that
defines the type of `y` (no dependency cycle). -/
theorem isClosed_rayAccum_singleton {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y) :
    IsClosed {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} := by
  rw [← closure_subset_iff_isClosed]
  intro θ hθ
  have hseq : ∀ n : ℕ, ∃ z : ℝ, Work.Landing.rayAccum c φ z = {y} ∧
      dist z θ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.mp hθ (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨z, hz, by rwa [dist_comm] at hzd⟩
  let u : ℕ → ℝ := fun n => Classical.choose (hseq n)
  have hu_type : ∀ n : ℕ, Work.Landing.rayAccum c φ (u n) = {y} :=
    fun n => (Classical.choose_spec (hseq n)).1
  have hu_dist : ∀ n : ℕ, dist (u n) θ < 1 / ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (hseq n)).2
  have hu : Filter.Tendsto u Filter.atTop (nhds θ) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    refine lt_of_lt_of_le (lt_of_lt_of_le (hu_dist n) ?_) hN.le
    exact one_div_le_one_div_of_le (by positivity) (by
      have h1 : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have : N + 1 ≤ n + 1 := by omega
        exact_mod_cast this
      linarith)
  exact mem_type_of_tendsto_type hφ hrep hu hu_type

end Work.LandLeaves
