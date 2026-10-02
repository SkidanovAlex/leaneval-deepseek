import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.extFatou_independent

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

open Set Function

/-- The self-map of the punctured basin: `F` maps the punctured basin of a point `z₀` into
itself.  The corresponding lemma `Work.FatouParabolic.Basin.mapsTo_puncturedBasin` carries a
fixed-point hypothesis which its proof does not use; here it is stated without it, since the
fixed-point property of `z₀` is not available at this point of the development. -/
theorem mapsTo_puncturedBasin' {F : ℂ → ℂ} {z₀ : ℂ} :
    MapsTo F (Work.FatouParabolic.puncturedBasin F z₀)
      (Work.FatouParabolic.puncturedBasin F z₀) := by
  intro z hz
  simp only [Work.FatouParabolic.mem_puncturedBasin, Work.FatouParabolic.mem_basin] at hz ⊢
  obtain ⟨hne, hconv⟩ := hz
  refine ⟨?_, ?_⟩
  · intro n
    rw [← Function.iterate_succ_apply F n z]
    exact hne (n + 1)
  · rw [show (fun n : ℕ => F^[n] (F z)) = (fun n : ℕ => F^[n + 1] z) from
      funext fun n => (Function.iterate_succ_apply F n z).symm]
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun n => F^[n] z) 1).mpr hconv

/-- **The extended Fatou coordinate is injective on the punctured basin as soon as `F` is.**

If `x, y` lie in the punctured basin and `φ x = φ y`, run both orbits to a common large time
`N` at which they both lie in the petal `fl.Pa`; the extended coordinate does not depend on the
tap time (`extFatou_independent`), so `φa (F^N x) = φa (F^N y)`.  The Fatou coordinate `φa` is
injective on the petal, hence `F^N x = F^N y`, and since `F` is injective on the (forward
invariant) punctured basin, its iterates are injective there too, giving `x = y`. -/
theorem extFatou_injective_of_injOn {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀)
    (hinj : Set.InjOn F (Work.FatouParabolic.puncturedBasin F z₀)) :
    Set.InjOn (Work.FatouParabolic.extFatou fl) (Work.FatouParabolic.puncturedBasin F z₀) := by
  have hmaps := mapsTo_puncturedBasin' (F := F) (z₀ := z₀)
  -- iterates of `F` are injective on the punctured basin
  have hinj_iter : ∀ n : ℕ,
      Set.InjOn (F^[n]) (Work.FatouParabolic.puncturedBasin F z₀) := by
    intro n
    induction n with
    | zero => intro x _ y _ h; simpa using h
    | succ n ih =>
      intro x hx y hy h
      have h2 : F ((F^[n]) x) = F ((F^[n]) y) := by
        simpa only [Function.iterate_succ_apply'] using h
      exact ih hx hy (hinj (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmaps n hx)
        (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmaps n hy) h2)
  intro x hx y hy heq
  set n := Work.FatouParabolic.entryTime fl x hx with hn
  set m := Work.FatouParabolic.entryTime fl y hy with hm
  -- the two orbits reach the petal at times `n` and `m`
  have hxn : (F^[n]) x ∈ fl.Pa := by
    rw [hn]; exact Work.FatouParabolic.entryTime_spec fl x hx
  have hym : (F^[m]) y ∈ fl.Pa := by
    rw [hm]; exact Work.FatouParabolic.entryTime_spec fl y hy
  -- both orbits then stay in the petal (it is forward invariant)
  have hxp : (F^[max n m]) x ∈ fl.Pa := by
    have h := Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa (max n m - n) hxn
    rwa [← Function.iterate_add_apply F (max n m - n) n x,
      Nat.sub_add_cancel (le_max_left n m)] at h
  have hyp : (F^[max n m]) y ∈ fl.Pa := by
    have h := Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa (max n m - m) hym
    rwa [← Function.iterate_add_apply F (max n m - m) m y,
      Nat.sub_add_cancel (le_max_right n m)] at h
  -- the extended coordinate is the tap-time-independent expression at time `max n m`
  have hfx : Work.FatouParabolic.extFatou fl x
      = fl.φa ((F^[n]) x) - (n : ℂ) := by
    rw [hn]; exact Work.FatouParabolic.extFatou_eq fl hx
  have hfy : Work.FatouParabolic.extFatou fl y
      = fl.φa ((F^[m]) y) - (m : ℂ) := by
    rw [hm]; exact Work.FatouParabolic.extFatou_eq fl hy
  have hxval : Work.FatouParabolic.extFatou fl x
      = fl.φa ((F^[max n m]) x) - ((max n m : ℕ) : ℂ) := by
    rw [hfx, extFatou_independent fl hx hxn hxp]
  have hyval : Work.FatouParabolic.extFatou fl y
      = fl.φa ((F^[max n m]) y) - ((max n m : ℕ) : ℂ) := by
    rw [hfy, extFatou_independent fl hy hym hyp]
  -- compare the two expressions and use injectivity of `φa` on the petal
  have hpa : fl.φa ((F^[max n m]) x) = fl.φa ((F^[max n m]) y) := by
    have h := heq
    rw [hxval, hyval] at h
    exact sub_left_inj.mp h
  have hiter_eq : (F^[max n m]) x = (F^[max n m]) y := fl.φa_fatou.2 hxp hyp hpa
  exact hinj_iter (max n m) hx hy hiter_eq

end Work.FatouParabolic.Core
