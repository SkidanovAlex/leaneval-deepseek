import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.RatHurewicz.ConnectivityBridge
import Submission.Work.StemsB.basepoint_transport
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.Pi6.SQASM

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-!
# Connectivity implies vanishing of integral reduced homology

The statement is `Work.Pi6.SQASM.connHomology`: for a space `X` that is `n`-connected at a point
`x₀` (every `π_j(X,x₀)`, `j ≤ n`, is trivial, `π₀` included), the integral singular homology
`H_i(X;ℤ)` vanishes for `0 < i ≤ n`.

The proof is the sharp integral range Whitehead theorem `Work.Serre.Assembly.serreK2IntSharp`
applied to the *constant* map `c : X → PUnit` with `N = n + 1`:

* `serreK2IntSharp` needs `π_j(c)` to be bijective at *every* base point `x : X` for `j < n + 1`.
  Since both `π_j(X,x)` (`j ≤ n`, by hypothesis transported to `x`) and `π_j(PUnit,-)` (a point)
  are trivial, this is immediate;
* the base-point transfer is the content of `hall` below: for `j = 0` it uses the equivalence
  `π₀ ≃ ZerothHomotopy`, for `j ≥ 1` the base-point change `Work.StemsB.basepoint_transport`
  along a path from `x₀` to `x` (which exists because `π₀` is trivial, so `X` is path connected);
* the target `PUnit` has `H_i(PUnit;ℤ) = 0` for `i > 0`
  (`Work.Cohomology.homologyContractible`), so the homology isomorphism forces `H_i(X;ℤ) = 0`.
-/

/-- The homotopy groups of a subsingleton space are trivial: the cubes collapse because all maps
into a subsingleton space are equal. -/
theorem subsingleton_homotopyGroup_of_subsingleton (i : ℕ) (X : Type) [TopologicalSpace X]
    [Subsingleton X] (x : X) : Subsingleton (HomotopyGroup (Fin i) X x) := by
  haveI : Subsingleton (GenLoop (Fin i) X x) :=
    ⟨fun a b => Subtype.ext (ContinuousMap.ext (fun t => Subsingleton.elim _ _))⟩
  exact Quotient.mk_surjective.subsingleton

/-- **Connectivity gives vanishing integral reduced homology.** For a space `X` which is
`n`-connected at `x₀` (`π_j(X,x₀)` trivial for all `j ≤ n`, `π₀` included) and `0 < i ≤ n` one has
`H_i(X;ℤ) = 0`.  Apply `Work.Serre.Assembly.serreK2IntSharp` to the constant map `X → PUnit` with
`N = n + 1`: it requires bijectivity of `π_j` at EVERY base point, which for the constant map is
triviality of `π_j(X,x)` at every `x` — obtainable from the given point `x₀` along a path
(`Work.StemsB.basepoint_transport`, and `Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`
for `j = 0`).  The target `PUnit` has `H_j(PUnit;ℤ) = 0` for `j > 0`
(`Work.Cohomology.homologyContractible`). -/
theorem connHomology {X : Type} [TopologicalSpace X] (x₀ : X) (n i : ℕ)
    (h : ∀ j : ℕ, j ≤ n → Subsingleton (HomotopyGroup (Fin j) X x₀))
    (hi : 0 < i) (hin : i ≤ n) :
    CategoryTheory.Limits.IsZero (Work.Pi6.HR ℤ X i) := by
  classical
  haveI : Nonempty X := ⟨x₀⟩
  -- `π₀` triviality makes `X` path connected, so paths to `x₀` are available
  have hpc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (h 0 (by omega))
  -- the hypothesis, transported to every base point
  have hall : ∀ j : ℕ, j ≤ n → ∀ x : X, Subsingleton (HomotopyGroup (Fin j) X x) := by
    intro j hj x
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      haveI := h 0 (by omega)
      have hZ : Subsingleton (ZerothHomotopy X) :=
        ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x₀)).symm.injective
          (Subsingleton.elim _ _)⟩
      exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective
        (hZ.elim _ _)⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      obtain ⟨e⟩ := Work.StemsB.basepoint_transport k (hpc.joined x₀ x).some
      haveI := h (k + 1) hj
      exact ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  -- the constant map to the point
  let c : C(X, PUnit) := ContinuousMap.const X PUnit.unit
  -- `π_j(c)` is bijective at every base point, for `j < n + 1`
  have hbij : ∀ i : ℕ, i < n + 1 → ∀ x : X, Function.Bijective (Work.Serre.piMapN c i x) := by
    intro i hi x
    haveI hsrc : Subsingleton (HomotopyGroup (Fin i) X x) := hall i (by omega) x
    haveI htgt : Subsingleton (HomotopyGroup (Fin i) PUnit (c x)) :=
      subsingleton_homotopyGroup_of_subsingleton i PUnit (c x)
    exact ⟨fun a b _ => Subsingleton.elim a b,
      fun y => ⟨⟦(GenLoop.const : GenLoop (Fin i) X x)⟧, Subsingleton.elim _ _⟩⟩
  -- the range Whitehead theorem: `c` is an integral homology isomorphism in degrees `< n + 1`
  have hiso : IsIso (Work.Pi6.hmap ℤ c i) :=
    Work.Serre.Assembly.serreK2IntSharp c (n + 1) hbij i hi (by omega)
  -- and the target homology vanishes
  exact IsZero.of_iso (Work.Cohomology.homologyContractible (X := TopCat.of PUnit) i hi)
    (asIso (Work.Pi6.hmap ℤ c i))

end

end Work.Pi6.SQASM
