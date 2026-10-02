import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Surjectivity of `π₁(A) → π₁(X)` from compression in dimension `1`

The CW model of a space in a homotopy range (`Submission/Work/Serre/CWModel/`) needs, on the
`1`-skeleton, that the inclusion of the `0`-cells `A` into the space `X` hits every class of
`π₁(X)`.  The classical input is the *compression property* of the pair `(X, A)`
(`Work.RatHurewicz.CompressRel`, tom Dieck, *Algebraic Topology*, Proposition 6.7.5) in dimension
`1`: every map of pairs `(I¹, ∂I¹) → (X, A)` is homotopic relative to `∂I¹` into `A`.

Compression in dimension `d + 1` is exactly what surjectivity of `π_{d+1}(A) → π_{d+1}(X)` needs:
a class of `π_{d+1}(X)` is represented by a based cube `f : (I^{d+1}, ∂I^{d+1}) → (X, a₀)`, whose
boundary lies in `A` because it is constantly `a₀ ∈ A`; compressing `f` relative to the boundary
exhibits it as homotopic, relative to the boundary, to the image of the based cube `G(·, 1)` of
`A`.  No compression is needed in any other dimension — note in particular that
`Work.Serre.surjective_pimap_setIncl_of_compressRel` asks for compression in *all* dimensions
`≤ n`, an over-strong hypothesis which cannot be weakened to a single dimension inside that
statement (`CompressRel X A 1` does **not** imply `CompressRel X A 0`; take `X` the disjoint union
of a circle and an isolated point `A`).  The helper proved here isolates the sharp hypothesis.

`piOneSurjective` is the case `d = 0`: `π₁(A, a₀) → π₁(X, a₀)` is surjective as soon as the pair
`(X, A)` compresses `1`-dimensional relative cubes.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre.CWModel

noncomputable section

/-- **Compression in dimension `d + 1` makes the inclusion surjective on `π_{d+1}`.**

If every map of pairs `(I^{d+1}, ∂I^{d+1}) → (X, A)` is homotopic relative to `∂I^{d+1}` into `A`,
then the map `π_{d+1}(A, a₀) → π_{d+1}(X, a₀)` induced by the inclusion `A ↪ X` is surjective.

This is the surjectivity half of `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel`, with the
compression hypothesis required only in the single dimension `d + 1` (compare the remark in the
module docstring). -/
theorem πmap_setIncl_surjective_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (d : ℕ) (h : Work.RatHurewicz.CompressRel X A (d + 1)) (a₀ : ↥A) :
    Function.Surjective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) d a₀) := by
  intro y
  induction y using Quotient.inductionOn with
  | h f =>
    -- a based `(d+1)`-cube of `X`, whose boundary is the base point `a₀ ∈ A`
    have hbdf : ∀ x, x ∈ Cube.boundary (Fin (d + 1)) → f.1 x ∈ A := by
      intro x hx
      rw [f.2 x hx]
      exact a₀.2
    -- compress it relative to the boundary into `A`
    obtain ⟨G, hG0, hGb, hG1⟩ := h f.1 hbdf
    -- the end map of the compression, read as a based cube of `A`
    let g : Ω^ (Fin (d + 1)) ↥A a₀ :=
      ⟨⟨fun x => ⟨G (x, 1), hG1 x⟩, by fun_prop⟩, by
        intro x hx
        apply Subtype.ext
        show G (x, 1) = (a₀ : X)
        rw [hGb x hx 1]
        exact f.2 x hx⟩
    refine ⟨⟦g⟧, ?_⟩
    rw [Work.StemsB.πmap_apply_mk]
    apply Quotient.sound
    -- the compression, with its two coordinates swapped, is a homotopy from `f` to the image of `g`
    have hhom : (f.1).HomotopicRel
        ((Work.StemsB.genLoopMap (Work.RatHurewicz.setIncl A) (d + 1) g).1)
        (Cube.boundary (Fin (d + 1))) := by
      refine ⟨{ toHomotopy := { toFun := fun p => G (p.2, p.1), continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
      · fun_prop
      · intro x
        show G (x, 0) = f.1 x
        exact hG0 x
      · intro x
        show G (x, 1) = (Work.RatHurewicz.setIncl A) (g x)
        rfl
      · intro t x hx
        show G (x, t) = f.1 x
        exact hGb x hx t
    exact hhom.symm

/-- **The inclusion of the cells of dimension `0` hits every element of `π₁`.**

If the pair `(X, A)` has the compression property in dimension `1`, then every class in `π₁(X, a₀)`
is the image of a class in `π₁(A, a₀)` under the map induced by the inclusion `A ↪ X`. -/
theorem piOneSurjective {X : Type} [TopologicalSpace X] {A : Set X}
    (h : Work.RatHurewicz.CompressRel X A 1) (a₀ : ↥A) :
    Function.Surjective (fun x => Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀ x) :=
  πmap_setIncl_surjective_of_compressRel 0 h a₀

end

end Work.Serre.CWModel
