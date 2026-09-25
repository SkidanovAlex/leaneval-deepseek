import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

/-- **`constrainedE S A ≤ N_{L/K} 𝕀_L`.**

Let `L / K` be a finite extension of number fields, `S` a finite set of places of `K`, `A v ≤ K_vˣ`
for `v ∈ S`, and `g` a choice of a place `g v` of `L` above each place `v` of `K`.  Suppose
`Φ v : L_{g v}ˣ →* K_vˣ` computes the local idèlic norm at `v`:

`normIdeleFun K L (singleIdele (g v) u) v = Φ v u`,

that `A v ≤ (Φ v).range` for `v ∈ S`, and that `Φ v` maps the local units of `L_{g v}` onto the
local units of `K_v` for `v ∉ S`.  Then every idèle of `K` which lies in `A v` for `v ∈ S` and is
a local unit outside `S` is an idèlic norm from `L`.

The proof is place-by-place: each component `x v` is `Φ v u_v` for a suitable `u_v`, and the
idèle of `L` with value `u_v` at `g v` (and `1` elsewhere, except that distinct `g v` may
coincide when `L ≠ K` — this is handled by `yValue`, which realises *all* the conditions at
once) has the prescribed norm.  Outside the finite set `g '' S` the constructed idèle is a unit,
by the unit-surjectivity hypothesis. -/
theorem constrainedE_le_normImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.GlobalCFT.Place K)) (A : (v : S) → Subgroup ((NK.GlobalCFT.Place.localField K v)ˣ)) (g : NK.GlobalCFT.Place K → NK.GlobalCFT.Place L) (hg : ∀ v, NK.GlobalCFT.Place.LiesOver (g v) v) (Φ : (v : NK.GlobalCFT.Place K) → (NK.GlobalCFT.Place.localField L (g v))ˣ →* (NK.GlobalCFT.Place.localField K v)ˣ) (hbridge : ∀ (v : NK.GlobalCFT.Place K) (u : (NK.GlobalCFT.Place.localField L (g v))ˣ), NK.GlobalCFT.Idele.normIdeleFun K L (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (g v) u) v = Φ v u) (hA : ∀ v : S, A v ≤ (Φ v).range) (hunit : ∀ (v : NK.GlobalCFT.Place K), v ∉ S → ∀ a ∈ NK.GlobalCFT.Place.localUnits K v, ∃ u ∈ NK.GlobalCFT.Place.localUnits L (g v), Φ v u = a) : NK.GlobalCFTdeep.constrainedE S A ≤ NK.GlobalCFT.Idele.normImage K L := by
  intro x hx
  rw [Idele.mem_normImage]
  rw [mem_constrainedE] at hx
  obtain ⟨hxS, hxU⟩ := hx
  -- ### A local preimage for every component of `x`, a unit outside `S`
  have hhex : ∀ v : Place K, ∃ u : (Place.localField L (g v))ˣ,
      Φ v u = x v ∧ (v ∉ S → u ∈ Place.localUnits L (g v)) := by
    intro v
    by_cases hvS : v ∈ S
    · obtain ⟨u, hu⟩ := hA ⟨v, hvS⟩ (hxS ⟨v, hvS⟩)
      exact ⟨u, hu, fun h => absurd hvS h⟩
    · obtain ⟨u, hu, hun⟩ := hunit v hvS (x v) (hxU v hvS)
      exact ⟨u, hun, fun _ => hu⟩
  choose hval hvalnorm hvalunit using hhex
  -- ### The idèle of `L` realising all the local norms at once
  have hyeventually : ∀ᶠ w in Filter.cofinite, SecondInequality.KummerCase.yValue g hval w ∈ Place.localUnits L w :=
    Filter.eventually_cofinite.mpr
      (SecondInequality.KummerCase.finite_yValue_not_mem_localUnits (S := S) (T' := ∅) hg
        (fun v hvS _ => hvalunit v hvS))
  let y : Idele L := ⟨SecondInequality.KummerCase.yValue g hval, hyeventually⟩
  refine ⟨y, fun v => ?_⟩
  have hsingle : ∀ w : Place L, Place.LiesOver w v →
      y w = SecondInequality.KummerCase.singleIdele (g v) (hval v) w := by
    intro w hw
    by_cases h : w = g v
    · rw [h, show y (g v) = SecondInequality.KummerCase.yValue g hval (g v) from rfl,
        SecondInequality.KummerCase.yValue_pickW hg v, SecondInequality.KummerCase.singleIdele_apply_self]
    · rw [show y w = SecondInequality.KummerCase.yValue g hval w from rfl,
        SecondInequality.KummerCase.yValue_eq_one_of_liesOver_ne hw h,
        SecondInequality.KummerCase.singleIdele_apply_of_ne (w' := w) h (hval v)]
  rw [SecondInequality.KummerCase.normIdeleFun_congr_of_liesOver hsingle, hbridge v (hval v)]
  exact (hvalnorm v).symm

end NK.GlobalCFTdeep.NormIndex
