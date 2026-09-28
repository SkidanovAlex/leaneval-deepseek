import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic

/-!
# The compression property of a pair, and its use for the two-set theorem

`Work.ThomBordism.TwoSet.Compress Y A d` is the *compression property* of the pair `(Y, A)` in
dimension `d`: every map of pairs `(Iᵈ, ∂Iᵈ) → (Y, A)` is homotopic, relative to the boundary,
into `A` (the compression form of the vanishing of the relative homotopy groups `π_e(Y,A)`,
`e ≤ d`; tom Dieck, *Algebraic Topology*, (6.7.5)).

`Compress.toSubsingleton` is the passage from the *pair* statement to the statement about the
union that the target theorem needs: if the pair `(X, U)` has the compression property in
dimension `j`, then `π_j(X)` is trivial at every point of `U` provided it is trivial at that point
for `U` itself.
-/

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

/-- **The compression property of the pair `(Y, A)` in dimension `d`.**  Every continuous map
`f : Iᵈ → Y` whose boundary lands in `A` is homotopic, relative to the boundary, to a map with
values in `A`. -/
def Compress (Y : Type*) [TopologicalSpace Y] (A : Set Y) (d : ℕ) : Prop :=
  ∀ f : C(IC d, Y), (∀ x, x ∈ Cube.boundary (Fin d) → f x ∈ A) →
    ∃ G : C(IC d × I, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ Cube.boundary (Fin d)) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A)

/-- **Compression of `(X, U)` forces the triviality of `π_j(X)` on `U`.**

If every map `(Iᵈ, ∂Iᵈ) → (X, U)` is homotopic relative to the boundary into `U`, and `π_j(U)` is
trivial at `x ∈ U`, then `π_j(X)` is trivial at `x`: compress a based `j`-cube map into `U` and
use the triviality of `π_j(U)` there. -/
theorem Compress.toSubsingleton {X : Type*} [TopologicalSpace X] {U : Set X} {j : ℕ}
    (h : Compress X U j) {x : X} (hx : x ∈ U)
    (hU : Subsingleton (HomotopyGroup (Fin j) ↥U ⟨x, hx⟩)) :
    Subsingleton (HomotopyGroup (Fin j) X x) := by
  have key : ∀ p : GenLoop (Fin j) X x,
      (⟦p⟧ : HomotopyGroup (Fin j) X x) = ⟦GenLoop.const⟧ := by
    intro p
    -- compress the underlying map of `p` into `U`
    have hbU : ∀ y, y ∈ Cube.boundary (Fin j) → p.1 y ∈ U := by
      intro y hy
      rw [p.2 y hy]
      exact hx
    obtain ⟨G, hG0, hGbd, hG1⟩ := h p.1 hbU
    -- the compressed map, as a map into `U`
    let g : C(IC j, ↥U) :=
      ⟨fun y => ⟨G (y, 1), hG1 y⟩,
        Continuous.subtype_mk (G.continuous.comp (continuous_id.prodMk continuous_const)) hG1⟩
    have hgbd : ∀ y, y ∈ Cube.boundary (Fin j) → g y = ⟨x, hx⟩ := by
      intro y hy
      apply Subtype.ext
      show G (y, 1) = x
      rw [hGbd y hy 1, p.2 y hy]
    let qu : GenLoop (Fin j) ↥U ⟨x, hx⟩ := ⟨g, hgbd⟩
    -- the triviality of `π_j(U)` gives a homotopy of `qu` to the constant loop
    have hqu1 : (⟦qu⟧ : HomotopyGroup (Fin j) ↥U ⟨x, hx⟩) = ⟦GenLoop.const⟧ :=
      hU.allEq _ _
    have hqu : GenLoop.Homotopic qu GenLoop.const := Quotient.exact hqu1
    obtain ⟨Hrel, hprop⟩ := hqu
    -- transport to `X`
    let gX : C(IC j, X) := ⟨fun y => (g y : X), continuous_subtype_val.comp g.continuous⟩
    have hgXbd : ∀ y, y ∈ Cube.boundary (Fin j) → gX y = x := by
      intro y hy
      show (g y : X) = x
      rw [show g y = ⟨x, hx⟩ from hgbd y hy]
    -- first homotopy: from `p` to `gX`, relative to the boundary
    have h1 : GenLoop.Homotopic p ⟨gX, hgXbd⟩ := by
      refine ⟨⟨{ toContinuousMap :=
                    ⟨fun q : I × IC j => G (q.2, q.1),
                      G.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,
                  map_zero_left := fun y => hG0 y,
                  map_one_left := fun y => rfl }, ?_⟩⟩
      intro t y hy
      exact hGbd y hy t
    -- second homotopy: from `gX` to the constant loop, relative to the boundary
    have h2 : GenLoop.Homotopic ⟨gX, hgXbd⟩ GenLoop.const := by
      refine ⟨⟨{ toContinuousMap :=
                    ⟨fun q : I × IC j => (Hrel (q.1, q.2) : X),
                      continuous_subtype_val.comp Hrel.continuous⟩,
                  map_zero_left := fun y => congrArg Subtype.val (Hrel.map_zero_left y),
                  map_one_left := fun y => congrArg Subtype.val (Hrel.map_one_left y) }, ?_⟩⟩
      intro t y hy
      show (Hrel (t, y) : X) = gX y
      rw [show Hrel (t, y) = g y from hprop t y hy]
      rfl
    exact Quotient.sound (h1.trans h2)
  exact ⟨fun a b => by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact (key p).trans (key q).symm⟩

end Work.ThomBordism.TwoSet
