import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.HP2

/-- If the `b i` generate the unit ideal in `ZMod W`, then for every prime `p ∣ W`
some `b i` is not divisible by `p` (its canonical representative in `[0, W)` is not
a multiple of `p`).  Equivalently, the `b i` are not all contained in the prime ideal
`(p) ⊆ ZMod W`. -/
lemma primes_span_top (n W : ℕ) [NeZero W] (b : Fin (n + 1) → ZMod W)
    (hspan : Ideal.span (Set.range b) = ⊤) :
    ∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ ((b i).val : ℤ) := by
  intro p hp hpW
  by_contra hcon
  push Not at hcon
  -- Reduction modulo `p`, as a ring homomorphism `ZMod W →+* ZMod p`.
  let f : ZMod W →+* ZMod p := ZMod.castHom hpW (ZMod p)
  -- Each `b i` maps to zero under reduction mod `p`.
  have hle : Ideal.span (Set.range b) ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    show f (b i) = 0
    have hfx : f (b i) = ((b i).val : ZMod p) := by
      rw [ZMod.castHom_apply]
      exact (ZMod.natCast_val (b i)).symm
    rw [hfx, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcon i
  rw [hspan] at hle
  have hker : RingHom.ker f = ⊤ := le_antisymm le_top hle
  -- But `1 ∉ ker f`, so `ker f ≠ ⊤`: contradiction.
  have h1 : (1 : ZMod p) = 0 := by
    have : (1 : ZMod W) ∈ RingHom.ker f := by rw [hker]; trivial
    rwa [RingHom.mem_ker, map_one] at this
  have hone : (1 : ZMod p) ≠ 0 := by
    intro h
    rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_zero_iff] at h
    exact hp.not_dvd_one h
  exact hone h1

end Work.HP.HP2
