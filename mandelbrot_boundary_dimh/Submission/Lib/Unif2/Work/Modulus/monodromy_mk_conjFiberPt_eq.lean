import Mathlib
import Submission.Lib.Unif2.Work.Modulus.Defs

/-!
# The monodromy of the conjugate covering map along a graph path

Let `p : X × ℝ → X` be the projection, made a covering map by a topology `htop` on `X × ℝ`
(e.g. the "conjugate" topology `Submission.conjTopology h` of a harmonic function `h : X → ℝ`).
If `B ⊆ X` carries a continuous section `u ↦ (u, (F u).im)` of `p`, then along any path `η` in `B`
the monodromy of `p` moves the point `(x, (F x).im)` of the fibre over `x = η 0` to the point
`(z, (F z).im)` of the fibre over `z = η 1`: the section *is* the lift of `η`.

The mathematical content is plain uniqueness of path liftings: the composition `t ↦ (η t, (F (η t)).im)`
is a continuous path in `X × ℝ` lifting `η` and starting at `(x, y)`, `y = (F x).im`; hence it agrees
with `IsCoveringMap.liftPath`, and the monodromy is its endpoint.
-/

open Path.Homotopic

namespace Work.Modulus

/-- The value of the monodromy of a covering map along the class of a path is the endpoint of the
lift of that path.  (Local copy of the special case `E = X × ℝ`; `Submission.monodromy_mk_liftPath`
has the same content but is stated under charted-space hypotheses we do not want to assume.) -/
theorem monodromy_mk_val_eq_liftPath {E : Type*} [TopologicalSpace E] {X : Type*}
    [TopologicalSpace X] {p : E → X} (cov : IsCoveringMap p) {a b : X} (γ : Path a b)
    (e : p ⁻¹' {a}) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) e).1
      = cov.liftPath γ e.1 (γ.source.trans e.2.symm) 1 := rfl

theorem monodromy_mk_conjFiberPt_eq
    {X : Type*} [TopologicalSpace X] [htop : TopologicalSpace (X × ℝ)]
    (cov : @IsCoveringMap (X × ℝ) X htop _ Prod.fst)
    {x z : X} (η : Path x z) (y : ℝ) {B : Set X} {F : X → ℂ}
    (hgraph : @Continuous B (X × ℝ) _ htop (fun u : B => ((u : X), (F u).im)))
    (hηB : ∀ t, η t ∈ B) (hy : y = (F x).im) :
    cov.monodromy (Path.Homotopic.Quotient.mk η) (Submission.conjFiberPt x y)
      = Submission.conjFiberPt z ((F z).im) := by
  -- The graph of `η` is a continuous path in `X × ℝ` lifting `η`.
  have hcont : @Continuous unitInterval (X × ℝ) _ htop
      (fun t => ((η t : X), (F (η t)).im)) :=
    hgraph.comp (η.continuous.subtype_mk hηB)
  have hcomp : (Prod.fst : X × ℝ → X) ∘ (fun t => ((η t : X), (F (η t)).im)) = ⇑η := rfl
  have hzero : (fun t => ((η t : X), (F (η t)).im)) 0 = (x, y) := by
    refine Prod.ext ?_ ?_
    · exact η.source
    · change (F (η 0)).im = y
      rw [η.source]; exact hy.symm
  have hzero' : (fun t => ((η t : X), (F (η t)).im)) 0
      = (Submission.conjFiberPt x y).1 :=
    hzero.trans rfl
  -- Hence it is *the* lift of `η` starting at `(x, (F x).im)`.
  have hΓ : (fun t => ((η t : X), (F (η t)).im))
      = ⇑(cov.liftPath η (Submission.conjFiberPt x y).1
            (η.source.trans (Submission.conjFiberPt x y).2.symm)) :=
    (cov.eq_liftPath_iff (γ := η) (e := (Submission.conjFiberPt x y).1)
      (γ_0 := η.source.trans (Submission.conjFiberPt x y).2.symm)).mpr
        ⟨hcont, hcomp, hzero'⟩
  refine Subtype.ext ?_
  rw [monodromy_mk_val_eq_liftPath cov η (Submission.conjFiberPt x y)]
  rw [← hΓ]
  change ((η 1 : X), (F (η 1)).im) = ((z : X), (F z).im)
  exact congrArg (fun w : X => ((w : X), (F w).im)) η.target

end Work.Modulus
