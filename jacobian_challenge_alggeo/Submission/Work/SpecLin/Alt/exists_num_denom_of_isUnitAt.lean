import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt


/-!
HINT (from the requester).  `Work.SpecLin.Alt.InLocalization u N` is
`∃ b s, s ∉ N ∧ u * algebraMap B (FractionRing B) s = algebraMap B (FractionRing B) b`, i.e.
"`u ∈ B_N`".  The hypothesis `u ≠ 0` is **essential**: `IsUnitAt 0 N` holds because `0⁻¹ = 0`
(the reviewers found the counterexample `B = ℤ`, `N = (2)`, `u = 0`, `A = 0`, `B' = 1`).

Proof (short).  `hu.1` gives `u·σ s = σ b` with `s ∉ N`, `hu.2` gives `u⁻¹·σ t = σ b'` with
`t ∉ N`.  Multiply: `σ (b·b') = σ (s·t)` (using `u·u⁻¹ = 1`, which needs `u ≠ 0`), hence
`b·b' = s·t ∉ N` by injectivity of `algebraMap B (FractionRing B)` and primeness of `N`, so
`b ∉ N`; finally `σ (A·s) = σ A · σ s = u σ B' σ s = σ B' σ b = σ (B'·b)`, so `A·s = B'·b`.
Thus `p := b`, `q := s` work.

This removes the last bookkeeping step from the crux: a colleague who proves
`Work.SpecLin.Alt.IsUnitAt u N` for the correction element `u = h'·∏g/∏f ∈ FractionRing B` can
feed it straight into the hypothesis `hcrux` of `Work.SpecLin.Alt.chartCoreDiv_of_reading`
(`Submission/Work/SpecLin/Alt/chartCoreAssembly.lean`).
-/

theorem exists_num_denom_of_isUnitAt {B : Type _} [CommRing B] [IsDomain B]
    (N : Ideal B) [N.IsPrime] (u : FractionRing B) (A B' : B)
    (hu0 : u ≠ 0)
    (hu : Work.SpecLin.Alt.IsUnitAt u N)
    (hAB : algebraMap B (FractionRing B) A = u * algebraMap B (FractionRing B) B') :
    ∃ p q : B, p ∉ N ∧ q ∉ N ∧ A * q = B' * p := by
  obtain ⟨b, s, hsN, hbs⟩ := hu.1
  obtain ⟨b', t, htN, hbt⟩ := hu.2
  have hinj : Function.Injective (algebraMap B (FractionRing B)) :=
    IsFractionRing.injective B (FractionRing B)
  -- multiply the two localisation witnesses: `b * b' = s * t`
  have hbb' : b * b' = s * t := by
    apply hinj
    rw [map_mul, map_mul, ← hbs, ← hbt]
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hu0, one_mul]
  have hst_not : s * t ∉ N := by
    intro h
    rcases (show N.IsPrime from inferInstance).mem_or_mem h with h | h
    · exact hsN h
    · exact htN h
  have hbN : b ∉ N := by
    intro hb
    exact hst_not (hbb' ▸ Ideal.mul_mem_right b' N hb)
  -- `σ A = u * σ B'` and `σ b = u * σ s`, so `σ (A * s) = σ (B' * b)`
  have hAs : A * s = B' * b := by
    apply hinj
    rw [map_mul, map_mul, hAB, ← hbs]
    ring
  exact ⟨b, s, hbN, hsN, hAs⟩

end Work.SpecLin.Alt
