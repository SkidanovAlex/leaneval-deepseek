/-
Copyright (c) 2025. All rights reserved.

# Square classes and the localisation map

This file isolates the *arithmetic* form of Grünwald's theorem in degree `2`, which is the input
used by the embedding-problem arguments:

* `Work.AbsoluteKummer.SqClass K = Kˣ/(Kˣ)²`, the group of square classes of a field `K`;
* `Work.AbsoluteKummer.sqClassLocalize p : SqClass ℚ →* SqClass ℚ_[p]`, induced by the localisation
  map `ℚˣ → ℚ_[p]ˣ`;
* `Work.AbsoluteKummer.sqClassLocalize_surjective` (in `SqClass/surjective.lean`):
  for finitely many **distinct** primes `q i` and prescribed local square classes `c i`, there is a
  global square class `x` with `x ↦ c i` — this is `Work.QuadraticLocalGlobal.grunwald_degree_two`.

`SqClass K` is the arithmetic shadow of `H¹(G_K, μ_2)` (see `Work.AbsoluteKummer.Kummer` for the
Kummer isomorphism `H¹(G_K, μ₂) ≃ Kˣ/(Kˣ)²` when `μ₂ ⊆ K`).
-/
import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.QuadraticLocalGlobal.grunwald_degree_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.AbsoluteKummer

open scoped Classical

noncomputable section

/-- The group `Kˣ/(Kˣ)²` of square classes of a field `K`. -/
abbrev SqClass (K : Type u) [Field K] := Kˣ ⧸ Work.Kummer.nthPowerSubgroup 2 Kˣ

/-- The localisation map on square classes at a prime `p`: a rational square class is sent to its
class in `ℚ_[p]`. -/
noncomputable def sqClassLocalize (p : ℕ) [Fact p.Prime] : SqClass ℚ →* SqClass ℚ_[p] :=
  QuotientGroup.map (Work.Kummer.nthPowerSubgroup 2 ℚˣ)
    (Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) (Units.map (algebraMap ℚ ℚ_[p])) (by
      intro x hx
      obtain ⟨z, hz⟩ := hx
      exact ⟨Units.map (algebraMap ℚ ℚ_[p]) z, by rw [← hz, ← map_pow]⟩)

@[simp] theorem sqClassLocalize_mk (p : ℕ) [Fact p.Prime] (x : ℚˣ) :
    sqClassLocalize p (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (Units.map (algebraMap ℚ ℚ_[p]) x) :=
  QuotientGroup.map_mk' _ _ _ _ x

end

end Work.AbsoluteKummer
