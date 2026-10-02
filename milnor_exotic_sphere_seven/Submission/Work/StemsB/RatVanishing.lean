import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.StemsB.TorsionBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Route B for the stable stems: the rational interface

`Work.Drive.StableStemsTorsion` says that every element of `π_{n+i+1}(Sⁿ)` has finite order, for
`0 ≤ i ≤ 7` and `n ≥ i + 3`.  This file isolates *what route B has to prove*: the rational
vanishing of those homotopy groups (Serre's theorem in the stable range), together with the
(proved) reduction from the rational statement to the contract.

* `Work.StemsB.Sph n` — the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`.
* `Work.StemsB.RatTriv G` — "`G` is rationally trivial": `Additive G ⊗[ℤ] ℚ` is a subsingleton.
* `Work.StemsB.RatVanishesStems` — **the interface**: for every `i ≤ 7`, `n ≥ i + 3`, base point
  `x₀`, the group `π_{n+i+1}(Sⁿ, x₀)` is rationally trivial.  This is Serre's theorem restricted to
  stems `1..8` in the stable range, and it is *the* deep input of route B; see
  `Submission/Work/StemsB/PLAN.md` §4 for its honest dependency list.  The index argument
  `Nontrivial (Fin _)` of the groups (which the `CommGroup` structure on `HomotopyGroup` needs) is
  an explicit instance argument of the interface, so that no instance-matching subtlety can arise
  when the interface is used.
* `Work.StemsB.RatVanishesStemsRange` — the same statement in the "stem" shape `n + 1 ≤ d ≤ 2n - 2`.
* `Work.StemsB.stableStemsTorsion_of_ratVanishes` — **the reduction** (proved): the interface
  implies the contract.

The only ingredient of the reduction is the rational-to-torsion bridge
`Work.StemsB.exists_pow_eq_one_of_subsingleton_tensorRat` of `TorsionBridge.lean`. -/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology TensorProduct

namespace Work.StemsB

noncomputable section

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as a type.  This is the space whose homotopy groups
`Work.Drive.StableStemsTorsion` is about. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- A commutative group is **rationally trivial** if its `ℤ`-module rationalisation is trivial.
For an abelian group this is equivalent to being a torsion group (the bridge
`exists_pow_eq_one_of_subsingleton_tensorRat`). -/
def RatTriv (G : Type*) [CommGroup G] : Prop := Subsingleton (Additive G ⊗[ℤ] ℚ)

/-- **The interface of route B.**  Every homotopy group `π_{n+i+1}(Sⁿ)` in the stable range
`0 ≤ i ≤ 7`, `n ≥ i + 3` is rationally trivial.

This is Serre's theorem (torsion of the stable stems) in the range the contract needs.  It is what
the rational Hurewicz theorem applied to `Sⁿ` (via the comparison with `K(ℤ,n)`, or via the free
simplicial abelian group `ℤ[Sⁿ]` together with Dold–Thom) has to produce; see
`Work.StemsB.RatHurewiczRange` for the decomposition of this input along route B. -/
def RatVanishesStems : Prop :=
  ∀ (i : ℕ) (hi : i ≤ 7) (n : ℕ) (hn : i + 3 ≤ n) [Nontrivial (Fin (n + i + 1))] (x₀ : Sph n),
    RatTriv (HomotopyGroup (Fin (n + i + 1)) (Sph n) x₀)

/-- The interface in the "stem" shape: for `n ≥ 2` and `n + 1 ≤ d ≤ 2n - 2` the group `π_d(Sⁿ)` is
rationally trivial.  This is `RatVanishesStems` with the index `d = n + i + 1`, phrased in the
spirit of Serre's theorem (`π_d(Sⁿ) ≅ π_{d+i}(S^{n+i})` is the stable stem `π_{d-n}(𝕊)`). -/
def RatVanishesStemsRange : Prop :=
  ∀ (n d : ℕ) (hd : n + 1 ≤ d) (hd2 : 2 ≤ d) (hd3 : d ≤ 2 * n - 2) [Nontrivial (Fin d)]
    (x₀ : Sph n),
    RatTriv (HomotopyGroup (Fin d) (Sph n) x₀)

/-- **The reduction: the rational interface implies the contract.**  Every element of
`π_{n+i+1}(Sⁿ)` has finite order, because its rationalisation is trivial
(`Work.StemsB.exists_pow_eq_one_of_subsingleton_tensorRat`). -/
theorem stableStemsTorsion_of_ratVanishes (h : RatVanishesStems) :
    Work.Drive.StableStemsTorsion := by
  intro i hi n hn x₀ α
  haveI : Nontrivial (Fin (n + i + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  exact exists_pow_eq_one_of_subsingleton_tensorRat (h i hi n hn x₀) α

/-- The range-shaped interface implies the "stem"-shaped one (with `i = d - n - 1`); this is the
direction in which Serre's theorem is naturally proved. -/
theorem ratVanishesStems_of_range (h : RatVanishesStemsRange) : RatVanishesStems := by
  intro i hi n hn hN x₀
  exact h n (n + i + 1) (by omega) (by omega) (by omega) x₀

/-- The range-shaped interface also implies the contract. -/
theorem stableStemsTorsion_of_ratVanishesRange (h : RatVanishesStemsRange) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_ratVanishes (ratVanishesStems_of_range h)

end

end Work.StemsB
