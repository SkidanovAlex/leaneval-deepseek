import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RatHurewicz

/-- **Homotopy excision for open triads: the comparison map is an isomorphism in the range.**

Let `X = B ∪ C` with `B`, `C` open (`hB`, `hC`, `hBC`) and `x₀ ∈ B ∩ C`.  Let `F_B` be the homotopy
fibre of `B ∩ C ↪ B` at `x₀` (`RelHomotopyGroup (interInclLeft B C) x₀ k` is its `k`-th homotopy
group) and `F = homotopyFibre (setIncl C) ⟨x₀.1, x₀.2.2⟩` the homotopy fibre of `C ↪ X` at `x₀`.
Assume the hypotheses of `Work.RatHurewicz.HomotopyExcision` at the base point `x₀`:
`π_k(F_B) = 0` for `k ≤ p` and `π_k(F_C) = 0` for `k ≤ q`, where `F_C` is the homotopy fibre of
`B ∩ C ↪ C`.  Then the comparison map `excisionComparison B C x₀ : F_B → F` (the canonical map of
homotopy fibres of the square of inclusions, `Submission/Work/RatHurewicz/ExcisionSetup.lean`)
induces an isomorphism `π_k(F_B) → π_k(F)` for every `k` with `k + 1 ≤ p + q`.

This is the classical Blakers–Massey excision statement for an open triad (tom Dieck, *Algebraic
Topology*, (6.4.1), proved by Puppe's elementary argument in §6.9).  With `m_B = p+1` and
`m_C = q+1` the classical isomorphism range is degree `≤ m_B + m_C - 1 = p+q+1`, i.e.
`RelHomotopyGroup` index `≤ p+q`, i.e. `πmap … k` with `k+1 ≤ p+q`; the range is sharp.

The present form assumes the hypotheses at the single base point `x₀`, whereas tom Dieck's
(6.4.1) assumes them at every base point of `B∩C`.  The two agree in effect: `π₀(F_B) = 0`
(the case `k = 0`) forces the points of `B∩C` that are reachable from `x₀` inside `B` to lie in a
single path component of `B∩C`, and only that component is seen by the fibres at `x₀`; the proof
should be run on the path component of `x₀` in `X` (the reduction of Problem 1 after tom Dieck's
(6.4.1)); the basepoint transfer along a path in `B∩C` is `subsingleton_relPiVanishing_of_path`
(`Submission/Work/RatHurewicz/ExcisionReachable.lean`).  Note that the vanishing at `x₀` does
*not* give the compression property of the pair `(B, B∩C)` at all base points of `B∩C`: with
`X = (-2,1) ∪ (2,7)`, `B = (-2,0) ∪ (2,7)`, `C = (-1,1) ∪ (2,3) ∪ (4,5)`, `x₀ = -1/2` the fibre at
`x₀` is contractible, yet a path in `B` joining the components `(2,3)` and `(4,5)` of `B∩C` cannot
be deformed relative to its endpoints into `B∩C`.

Proof route (tom Dieck §6.7, §6.9):
1. On the relevant part of the triad, the compression property `CompressRel ↥B {y | (y:X) ∈ B∩C} d`
   for `d ≤ p+1` and `CompressRel ↥C ... d` for `d ≤ q+1` (6.7.5: the compression property is
   equivalent to the vanishing of the relative groups).
2. Subdivide the cube by the Lebesgue number argument into small boxes each mapped into `B` or `C`
   (`Work.ThomBordism.TwoSet.Subdivision`).
3. Preparation result 6.9.2 (using 6.9.1 for the high-dimensional boxes): a homotopy putting the
   map into normal form, so that the boxes mapped into `B` have their `B∖(B∩C)`-preimage inside
   `K_{p+2}`, those mapped into `C` their `C∖(B∩C)`-preimage inside `G_{q+2}`.
4. Dimension count and Urysohn function (6.9.3): the two bad sets have `≥ p+1` resp. `≥ q+1`
   distinguished coordinates, hence are disjoint when `n ≤ p+q`; a continuous `φ` separating them
   gives the homotopy into `B`.
5. Transfer to the fibres (6.7.7) and translate the compression statement into the isomorphism on
   homotopy groups (6.7.5). -/
theorem excisionRelPiVanishing {X : Type} [TopologicalSpace X] {B C : Set X}
    (hB : IsOpen B) (hC : IsOpen C) (hBC : B ∪ C = Set.univ) (x₀ : ↥(B ∩ C)) (p q : ℕ)
    (hBvan : ∀ k, k ≤ p → Subsingleton (RelHomotopyGroup (interInclLeft B C) x₀ k))
    (hCvan : ∀ k, k ≤ q → Subsingleton (RelHomotopyGroup (interInclRight B C) x₀ k)) :
    ∀ k, k + 1 ≤ p + q →
      Function.Bijective (Work.StemsB.πmap (excisionComparison B C x₀) k
        (homotopyFibreBasepoint (interInclLeft B C) x₀)) := by
  exact excisionRelPiVanishing_aux hB hC hBC x₀ p q hBvan hCvan

end Work.RatHurewicz
