import Mathlib
import Submission.Work.LandLeaves.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# From a finite type to a closed type

Auxiliary module (kept deliberately light so that the set-theoretic arguments elaborate quickly):
`Work.LandLeaves.rayAccum_fract_alt` (the type is `1`-periodic) and
`Work.LandLeaves.isClosed_of_finite_type_alt` (a finite type is a finite union of integral
translates of its trace on `[0,1)`, hence closed).
-/

namespace Work.LandLeaves

open Filter Set

/-- `rayAccum` depends on the angle only modulo `1`. -/
theorem rayAccum_fract_alt (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.rayAccum c φ (Int.fract θ) = Work.Landing.rayAccum c φ θ := by
  have h : θ = Int.fract θ + ((⌊θ⌋ : ℤ) : ℝ) := by
    have := Int.fract_add_floor θ
    linarith
  conv_rhs => rw [h]
  exact (Work.FSeed.rayAccum_add_int c φ (Int.fract θ) ⌊θ⌋).symm

/-- **A finite type is closed.**  The type `{ψ | rayAccum c φ ψ = {y}}` is invariant under
`ψ ↦ ψ + m` (`m ∈ ℤ`, `Work.FSeed.rayAccum_add_int`); hence it is the finite union of the integral
translates of its trace on `[0,1)`, and each of these translates is closed. -/
theorem isClosed_of_finite_type_alt {c : ℂ} {φ : ℂ → ℂ} {y : ℂ}
    (hfin : ({ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1).Finite) :
    IsClosed {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} := by
  set T : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1 with hT
  set S : Set ℝ := {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} with hS
  -- the integers form a closed subset of `ℝ`
  have hZ : IsClosed (Set.range ((↑) : ℤ → ℝ)) := by
    rw [← isOpen_compl_iff]
    have hcompl : (Set.range ((↑) : ℤ → ℝ))ᶜ
        = ⋃ n : ℤ, Set.Ioo (n : ℝ) ((n : ℝ) + 1) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_range, Set.mem_iUnion, Set.mem_Ioo]
      constructor
      · intro hx
        refine ⟨⌊x⌋, ?_, Int.lt_floor_add_one x⟩
        refine lt_of_le_of_ne (Int.floor_le x) ?_
        intro h
        exact hx ⟨⌊x⌋, h⟩
      · rintro ⟨n, hn1, hn2⟩ ⟨m, hm⟩
        rw [← hm] at hn1 hn2
        have h1 : n < m := by exact_mod_cast hn1
        have h2 : m < n + 1 := by exact_mod_cast hn2
        omega
    rw [hcompl]
    exact isOpen_iUnion fun n => isOpen_Ioo
  -- the type is `1`-periodic
  have hper : ∀ ψ : ℝ, ψ ∈ S ↔ Int.fract ψ ∈ S := by
    intro ψ
    have h : ψ = Int.fract ψ + ((⌊ψ⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor ψ
      linarith
    conv_lhs => rw [h]
    rw [hS]
    simp only [Set.mem_ofPred_eq]
    rw [Work.FSeed.rayAccum_add_int]
  -- the type is exactly the union of the integral translates of its trace on `[0,1)`
  have hS_eq : S = ⋃ s ∈ T, (fun ψ : ℝ => ψ - s) ⁻¹' (Set.range ((↑) : ℤ → ℝ)) := by
    ext ψ
    constructor
    · intro hψ
      have h1 : Int.fract ψ ∈ S := (hper ψ).mp hψ
      have h2 : Int.fract ψ ∈ T := by
        rw [hT]; exact ⟨h1, Int.fract_nonneg ψ, Int.fract_lt_one ψ⟩
      refine Set.mem_iUnion.mpr ⟨Int.fract ψ, Set.mem_iUnion.mpr ⟨h2, ?_⟩⟩
      refine Set.mem_preimage.mpr (Set.mem_range.mpr ⟨⌊ψ⌋, ?_⟩)
      have h := Int.fract_add_floor ψ
      linarith
    · intro hψ
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hψ
      obtain ⟨hsT, hm⟩ := Set.mem_iUnion.mp hs
      obtain ⟨m, hm'⟩ := Set.mem_range.mp (Set.mem_preimage.mp hm)
      have hsT' : s ∈ {ψ : ℝ | Work.Landing.rayAccum c φ ψ = {y}} ∩ Set.Ico 0 1 := by
        rw [← hT]; exact hsT
      have hsS : s ∈ S := by rw [hS]; exact hsT'.1
      have hm'' : ψ = s + (m : ℝ) := by linarith
      rw [hm'', hper]
      have hfr : Int.fract (s + (m : ℝ)) = s := by
        rw [Int.fract_add_intCast, Int.fract_eq_self.mpr hsT'.2]
      rw [hfr]
      exact hsS
  rw [hS_eq]
  exact hfin.isClosed_biUnion fun s _ =>
    hZ.preimage (continuous_id.sub continuous_const)

end Work.LandLeaves
