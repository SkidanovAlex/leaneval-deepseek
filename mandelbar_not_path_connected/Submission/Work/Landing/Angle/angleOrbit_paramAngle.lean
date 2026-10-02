import Mathlib
import Submission.Work.Landing.Angles

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The angle orbit of `paramAngle = 23/63`

`paramAngle = 23/63` is periodic of period `6` under angle doubling
`angDouble θ = Int.fract (-2 * θ)` (`θ ↦ -2θ mod 1`, angles normalised to `[0,1)`), with cycle

  23/63 → 17/63 → 29/63 → 5/63 → 53/63 → 20/63 → 23/63.

Consequently its **forward orbit** (`angleOrbit`, the set of all `angDouble^[n] paramAngle`,
`n ∈ ℕ`, i.e. the orbit of the map `angDouble` starting at `paramAngle`) is exactly the
six-element set `{23/63, 17/63, 29/63, 5/63, 53/63, 20/63}`.  That is the statement of
`angleOrbit_paramAngle`.

## Proof shape

The argument is a purely rational computation, arranged so that no `mod`-arithmetic on
exponents is needed:

* `angDouble_paramAngle_cycle`: the six-element set is **invariant** under `angDouble`; this is
  the six-step cycle, each step an `Int.fract` computation on a rational (`norm_num`).
* Hence the orbit of `paramAngle` is contained in the six-element set: the orbit is generated
  from `paramAngle` by repeatedly applying `angDouble`, and invariance is preserved by
  induction on the iterate.
* Conversely `paramAngle_cycle_mem`: each of the six angles is an explicit iterate
  `angDouble^[k] paramAngle`, `k = 0,…,5`, so the six-element set is contained in the orbit.

## Degenerate cases / conventions

`angleOrbit θ` collects the iterates starting at `n = 0`, so it always contains the base point
`θ` itself; correspondingly `paramAngle = 23/63` is the first member of the displayed set, and
no non-degeneracy hypothesis is needed.  Nothing here depends on the mod-`1` normalisation
*not* being applied at step `0`: the only property of `angDouble` used is that the six listed
values cycle.
-/

namespace Work.Landing.Angle

/-- The six elements of the period-`6` cycle of `paramAngle = 23/63`,
`{23/63, 17/63, 29/63, 5/63, 53/63, 20/63}`, are invariant under angle doubling
`angDouble θ = Int.fract (-2 * θ)`: each of the six rational computations
`23/63 ↦ 17/63 ↦ 29/63 ↦ 5/63 ↦ 53/63 ↦ 20/63 ↦ 23/63` is decided by `norm_num`. -/
theorem angDouble_paramAngle_cycle :
    ∀ v ∈ ({23/63, 17/63, 29/63, 5/63, 53/63, 20/63} : Set ℝ),
      Work.Landing.angDouble v ∈ ({23/63, 17/63, 29/63, 5/63, 53/63, 20/63} : Set ℝ) := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
  rcases hv with h | h | h | h | h | h <;> subst h <;>
    norm_num [Work.Landing.angDouble, Int.fract]

/-- Each of the six angles of the cycle of `paramAngle = 23/63` is an explicit iterate of
`paramAngle` under angle doubling: `angDouble^[k] paramAngle` for `k = 0, 1, …, 5` is
`23/63, 17/63, 29/63, 5/63, 53/63, 20/63` respectively. -/
theorem paramAngle_cycle_mem :
    ∀ v ∈ ({23/63, 17/63, 29/63, 5/63, 53/63, 20/63} : Set ℝ),
      v ∈ Work.Landing.angleOrbit Work.Landing.paramAngle := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with h | h | h | h | h | h <;> subst h
  · exact ⟨0, by norm_num [Work.Landing.paramAngle, Function.iterate_zero_apply]⟩
  · exact ⟨1, by norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]⟩
  · exact ⟨2, by norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]⟩
  · exact ⟨3, by norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]⟩
  · exact ⟨4, by norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]⟩
  · exact ⟨5, by norm_num [Work.Landing.paramAngle, Work.Landing.angDouble, Int.fract,
      Function.iterate_succ_apply', Function.iterate_zero_apply]⟩

/-- **The forward orbit of `paramAngle = 23/63` under angle doubling is the six-element cycle**
`{23/63, 17/63, 29/63, 5/63, 53/63, 20/63}`.

Since `23/63` is periodic of period `6` for `θ ↦ -2θ mod 1`, the orbit is finite; the two
inclusions come from the invariance of the displayed set under `angDouble`
(`angDouble_paramAngle_cycle`) and from the fact that all six of its elements are reached from
`paramAngle` (`paramAngle_cycle_mem`). -/
theorem angleOrbit_paramAngle :
    Work.Landing.angleOrbit Work.Landing.paramAngle =
      {23/63, 17/63, 29/63, 5/63, 53/63, 20/63} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact angDouble_paramAngle_cycle _ ih
  · intro hx
    exact paramAngle_cycle_mem x hx

end Work.Landing.Angle
