import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.excisionTransfer

/-!
# Surjectivity of the inclusion on `π_{≤ n}` from compression in dimensions `≤ n`

This is the surjectivity half of `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel`,
separated out because it uses the compression hypothesis only in dimension `j + 1`, whereas the
injectivity half needs it in dimension `j + 2` as well.  Concretely, given a based cube
`f : (I^{j+1}, ∂I^{j+1}) → (X, A)` (a class in `π_{j+1}(X, a₀)`), compression in dimension `j + 1`
provides a homotopy of `f` into `A` relative to the boundary; reading that homotopy at time `1`
gives a based cube of `A` whose image is homotopic to `f` relative to the boundary, i.e. the
sought-for preimage in `π_{j+1}(A, a₀)`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

/-- **Compression in dimensions `≤ n` makes the inclusion surjective on `π_{≤ n}`.**

If every map of pairs `(I^d, ∂I^d) → (X, A)` with `d ≤ n` is homotopic relative to `∂I^d` into `A`
(`Work.RatHurewicz.CompressRel`), then for every `j` with `j + 1 ≤ n` the map
`π_{j+1}(A, a₀) → π_{j+1}(X, a₀)` induced by the inclusion `A ↪ X` is *surjective*.

This is exactly the surjectivity half of the existing
`Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel` (whose injectivity half additionally needs
compression in dimension `j + 2`), separated out so that it can be used in the top degree
`j + 1 = n`, where the bijective form is unavailable. -/
theorem surjective_pimap_setIncl_of_compressRel {X : Type} [TopologicalSpace X] {A : Set X}
    (a₀ : ↥A) (n : ℕ) (h : ∀ d, d ≤ n → Work.RatHurewicz.CompressRel X A d) (j : ℕ)
    (hj : j + 1 ≤ n) :
    Function.Surjective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) j a₀) := by
  intro y
  induction y using Quotient.inductionOn with
  | h f =>
    -- `f` is a based cube of `X` at `a₀`; its boundary lies in `A`.
    have hbdf : ∀ x, x ∈ Cube.boundary (Fin (j + 1)) → f.1 x ∈ A := by
      intro x hx
      rw [f.2 x hx]
      exact a₀.2
    -- Compress `f` into `A` relative to the boundary, in dimension `j + 1 ≤ n`.
    obtain ⟨G, hG0, hGb, hG1⟩ := h (j + 1) hj f.1 hbdf
    -- The compression at time `1`, read as a based cube of `A`.
    let g : Ω^ (Fin (j + 1)) ↥A a₀ :=
      ⟨⟨fun x => ⟨G (x, 1), hG1 x⟩, by fun_prop⟩, by
        intro x hx
        apply Subtype.ext
        show G (x, 1) = (a₀ : X)
        rw [hGb x hx 1]
        exact f.2 x hx⟩
    refine ⟨⟦g⟧, ?_⟩
    rw [Work.StemsB.πmap_apply_mk]
    apply Quotient.sound
    -- The homotopy `G` with its two coordinates swapped is a homotopy relative to the boundary
    -- between `f` and the image of the based cube `g`.
    have hhom : (f.1).HomotopicRel ((Work.StemsB.genLoopMap (setIncl A) (j + 1) g).1) (Cube.boundary (Fin (j + 1))) := by
      refine ⟨{ toHomotopy := { toFun := fun p => G (p.2, p.1), continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
      · fun_prop
      · intro x
        show G (x, 0) = f.1 x
        exact hG0 x
      · intro x
        show G (x, 1) = (setIncl A) (g x)
        rfl
      · intro t x hx
        show G (x, t) = f.1 x
        exact hGb x hx t
    exact hhom.symm

end

end Work.Serre
