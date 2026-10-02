import Mathlib
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The punctured parabolic basin is open

`puncturedBasin F z₀` is the set of points whose forward orbit converges to the (fixed) point
`z₀` and never attains it.  This file proves that, in the presence of a Leau--Fatou flower
(`ParabolicFlowerFix`), this set is **open**: the flower supplies an `F`-invariant half-petal
`Pg` on which `z₀` is absent and which every orbit converging to `z₀` eventually enters.

The argument is purely topological.  If `z` lies in the punctured basin, its orbit enters `Pg`
at some time `n`.  Then `U := (F^[n]) ⁻¹' Pg` is an open neighbourhood of `z` (continuity of
`F^[n]`), and for every `w ∈ U`:

* the orbit of `w` stays in the `F`-invariant `Pg` from time `n` on, hence converges to `z₀`;
* it never attains `z₀`: at times `k ≥ n` this is because `F^k w ∈ Pg` and `z₀ ∉ Pg`; at times
  `k ≤ n` because otherwise `F^n w = (F^[n-k]) z₀ = z₀` (the fixedness of `z₀` iterated),
  contradicting `F^n w ∈ Pg`.
-/

open scoped Topology
open Filter

namespace Work.FatouParabolic.Core

theorem isOpen_puncturedBasin {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀) (hfix : F z₀ = z₀)
    (hF : Differentiable ℂ F) :
    IsOpen (Work.FatouParabolic.puncturedBasin F z₀) := by
  -- the fixed point `z₀` is fixed by every iterate of `F`
  have hfix_iter : ∀ m : ℕ, (F^[m]) z₀ = z₀ := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rw [Work.FatouParabolic.mem_puncturedBasin] at hz
  obtain ⟨hzne, hzconv⟩ := hz
  -- the orbit of `z` enters the `F`-invariant half-petal `Pg`
  obtain ⟨n, hn⟩ := fl.enters_Pg z hzconv hzne
  -- the neighbourhood `U := (F^[n]) ⁻¹' Pg` of `z` is contained in the punctured basin
  have hU : (F^[n]) ⁻¹' fl.Pg ∈ 𝓝 z := by
    have hopen : IsOpen ((F^[n]) ⁻¹' fl.Pg) :=
      (hF.continuous.iterate n).isOpen_preimage fl.Pg fl.isOpen_Pg
    exact hopen.mem_nhds hn
  refine Filter.mem_of_superset hU ?_
  intro w hw
  rw [Work.FatouParabolic.mem_puncturedBasin]
  refine ⟨?_, ?_⟩
  · -- the orbit of `w` never hits `z₀`
    intro k
    rcases lt_or_ge n k with hk | hk
    · -- `n < k`: the orbit already lies in the `F`-invariant `Pg`
      have h2 : (F^[k]) w ∈ fl.Pg := by
        have hstep : (F^[k]) w = (F^[k - n]) ((F^[n]) w) := by
          conv_lhs => rw [← Nat.sub_add_cancel (le_of_lt hk)]
          rw [Function.iterate_add_apply]
        rw [hstep]
        exact Work.FatouCoordFix.ParabolicFlowerFix.mapsTo_iterate_F_Pg fl (k - n) hw
      intro hcon
      exact Work.FatouCoordFix.ParabolicFlowerFix.z₀_not_mem_Pg fl (hcon ▸ h2)
    · -- `k ≤ n`: hitting `z₀` at time `k` forces hitting it at time `n` too
      intro hcon
      have h1 : (F^[n]) w = z₀ := by
        conv_lhs => rw [← Nat.sub_add_cancel hk]
        rw [Function.iterate_add_apply, hcon, hfix_iter]
      exact Work.FatouCoordFix.ParabolicFlowerFix.z₀_not_mem_Pg fl (h1 ▸ hw)
  · -- the orbit of `w` converges to `z₀`
    rw [Work.FatouParabolic.mem_basin]
    have hconv : Tendsto (fun m : ℕ => (F^[m + n]) w) atTop (𝓝 z₀) := by
      have he : (fun m : ℕ => (F^[m + n]) w) = fun m : ℕ => (F^[m]) ((F^[n]) w) := by
        funext m
        exact Function.iterate_add_apply F m n w
      rw [he]
      exact fl.tendsto_Pa _ (fl.Pg_sub hw)
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) w) n).mp hconv

end Work.FatouParabolic.Core
