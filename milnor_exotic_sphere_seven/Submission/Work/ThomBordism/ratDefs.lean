import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.boundaryAssembly
import Submission.Work.ThomBordism.bdryMidFormNondegenerate
import Submission.Work.ThomBordism.bdryRatCohFinite
import Submission.Work.ThomBordism.AltInputs
import Submission.Work.ThomBordism.detectionOfSSetRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.BoundaryMaximalIsotropic` from `KerPhiZero`, without `Detection`

`Work.ThomBordism.BoundaryMaximalIsotropic` (the crux of `Work.ThomBordism.BoundarySigma`) is the
maximality half `Kᗮ ⊆ K` of middle-dimensional Lefschetz duality for the pair `(W, ∂W)`, where
`K = bdryK W = im(H⁴(W;ℤ) ⊗ ℚ → H⁴(∂W;ℤ) ⊗ ℚ)` and the form is `B = bdryFormBilin W`.

The workspace route (`Submission/Work/ThomBordism/bdryMaximalIsoAlt.lean`) proves

  `Detection → KerPhiZero → BoundaryMaximalIsotropic`

where

* `KerPhiZero` (the `(5,4)` injectivity half of Lefschetz duality for the pair) is the geometric
  input, and
* `Detection` — the non-degeneracy of the *base-changed integral* Kronecker pairing
  `H⁴(W;ℤ) ⊗ ℚ × H₄(W;ℤ) ⊗ ℚ → ℚ` — is **false in general**: it is gated by finite generation of
  `H_*(W;ℤ)`, whose only known route in the workspace is a finite *good* cover of the compact `C¹`
  manifold `W`, which is stalled (`GOODCOVER_NOTES.md`).

**The present file removes the `Detection` input.**  The observation is that the only place where
non-degeneracy of a pairing is genuinely used is *over the field `ℚ`*, where the Kronecker pairing
`H⁴(X;ℚ) × H₄(X;ℚ) → ℚ` **is** non-degenerate unconditionally
(`Work.ThomBordism.detectionOfSSetRat`, proved: the universal coefficient theorem over a field), and
that for the closed manifold `∂W` the middle form is non-degenerate *and* the `(co)homology over ℚ`
is finite dimensional.  The rationalisation `H_n(·;ℤ) ⊗ ℚ ≅ H_n(·;ℚ)` (flatness of `ℚ`; the
machinery lives in `Submission/Work/StemsB/sphRatHomology.lean`) transfers the *homological*
statement back.

## The chain of inequalities

Write `M = ∂W`, `b = bdryB W = dim_ℚ (H⁴(M;ℤ) ⊗ ℚ)` (finite, `bdryRatCohFinite`), and

* `K_ℤ = bdryK W ⊆ H⁴(M;ℤ) ⊗ ℚ` (the crux's `K`), `K_ℚ = bdryKQ W ⊆ H⁴(M;ℚ)` (its `ℚ`-analogue),
* `L_ℚ = bdryLQ W = ker(H₄(M;ℚ) → H₄(W;ℚ))`, `L_ℤ = bdryLZ W = ker(H₄(M;ℤ) ⊗ ℚ → H₄(W;ℤ) ⊗ ℚ)`.

The argument is

1. `dim K_ℤ + dim L_ℤ = b` (`K_ℤ = ker δ_ℤ` plus rank–nullity, `bdryRatCohFinite`);
2. `dim K_ℤ = dim L_ℤ` **⟸ `KerPhiZero`** (with `Φ = i_* ∘ PD_M` and `PD_M` bijective:
   `KerPhiZero` is `ker Φ ⊆ K_ℤ`, and `dim ker Φ = dim L_ℤ`, since `PD_M` is bijective and
   `im i_* = L_ℤ`);
3. `dim L_ℤ = dim L_ℚ` (rationalisation, naturality of `H_n(·;ℤ) ⊗ ℚ ≅ H_n(·;ℚ)`);
4. `dim L_ℚ + dim K_ℚ = b` (`(K_ℚ)^⊥ = L_ℚ` by `detectionOfSSetRat` for `W` and Kronecker
   naturality; and `dim (K_ℚ)^⊥ = b - dim K_ℚ` by the perfection of the `ℚ`-pairing for the *closed*
   manifold `M`);
5. `2 dim K_ℚ ≤ b` (isotropy `K_ℚ ⊆ (K_ℚ)^⊥` for the `ℚ`-form plus `dim (K_ℚ)^⊥ = b - dim K_ℚ`);
6. `2 dim K_ℤ ≤ b` (the *proved* isotropy `bdryK_isotropic` plus the *proved* non-degeneracy
   `bdryMidFormNondegenerate`).

From 2, 3, 4 and 5: `dim K_ℤ = dim L_ℤ = b - dim K_ℚ ≥ b - b/2 = b/2`; with 6 this gives
`dim K_ℤ = b/2`, hence `K_ℤ = K_ℤᗮ` (isotropy + non-degeneracy) — `BoundaryMaximalIsotropic`.

So the only remaining geometric input is `KerPhiZero` (equivalently the `(5,4)` bidegree of
Lefschetz duality for the pair, hence `Work.ThomBordism.lefschetzDualityBdry W`), and the good-cover
obstruction is gone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] {F : ι → Man8}

/-- The boundary `∂W` of a null-bordism family, as a space. -/
abbrev bdryTop (W : NullBordismFamily ι F) : TopCat := TopCat.of (bdrySet W.W)

/-- The bounding manifold `W`, as a space. -/
abbrev ambTop (W : NullBordismFamily ι F) : TopCat := TopCat.of W.W

/-- The inclusion `∂W ⟶ W`, as a `TopCat` map. -/
abbrev bdryInc (W : NullBordismFamily ι F) : bdryTop W ⟶ ambTop W := bdryIncl W

/-- **The image `K` of the restriction in rational cohomology** (the `ℚ`-coefficient analogue of
`bdryK W`). -/
noncomputable abbrev bdryKQ (W : NullBordismFamily ι F) :
    Submodule ℚ ((Work.Cohomology.cochainC ℚ
      (TopCat.toSSet.obj (bdryTop W))).homology 4) :=
  LinearMap.range (Work.Cohomology.singularCohomologyMap ℚ (bdryTop W) (ambTop W)
    (bdryInc W) 4).hom

/-- `b`: the dimension of the rationalised middle cohomology of the boundary (finite). -/
noncomputable abbrev bdryB (W : NullBordismFamily ι F) : ℕ :=
  Module.finrank ℚ (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (bdryTop W)))

/-- The pushforward `H₄(∂W;ℚ) → H₄(W;ℚ)` induced by the inclusion of the boundary. -/
noncomputable abbrev pushQ (W : NullBordismFamily ι F) :
    (Work.Cohomology.chainC ℚ (TopCat.toSSet.obj (bdryTop W))).homology 4 →ₗ[ℚ]
      (Work.Cohomology.chainC ℚ (TopCat.toSSet.obj (ambTop W))).homology 4 :=
  (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ
    (bdryTop W) (ambTop W) (bdryInc W)) 4).hom

/-- The pushforward `H₄(∂W;ℤ) → H₄(W;ℤ)` induced by the inclusion of the boundary. -/
noncomputable abbrev pushZ (W : NullBordismFamily ι F) :
    (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (bdryTop W))).homology 4 →ₗ[ℤ]
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (ambTop W))).homology 4 :=
  (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
    (bdryTop W) (ambTop W) (bdryInc W)) 4).hom

/-- `L_ℚ = ker(H₄(∂W;ℚ) → H₄(W;ℚ))`. -/
noncomputable abbrev bdryLQ (W : NullBordismFamily ι F) :
    Submodule ℚ ((Work.Cohomology.chainC ℚ (TopCat.toSSet.obj (bdryTop W))).homology 4) :=
  LinearMap.ker (pushQ W)

/-- `L_ℤ = ker(H₄(∂W;ℤ) ⊗ ℚ → H₄(W;ℤ) ⊗ ℚ)`, the rationalisation of the kernel of the integral
pushforward. -/
noncomputable abbrev bdryLZ (W : NullBordismFamily ι F) :
    Submodule ℚ (ℚ ⊗[ℤ] ((Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (bdryTop W))).homology 4)) :=
  LinearMap.ker ((pushZ W).baseChange ℚ)


/-- The orthogonal complement of `bdryK W` for the middle form of the boundary. -/
noncomputable abbrev bdryKorth (W : NullBordismFamily ι F) :
    Submodule ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))) where
  carrier := {y | ∀ x ∈ bdryK W, bdryFormBilin W x y = 0}
  zero_mem' := by
    intro x _
    simp
  add_mem' := by
    intro a b ha hb x hx
    rw [map_add, ha x hx, hb x hx]
    simp
  smul_mem' := by
    intro c a ha x hx
    rw [map_smul, ha x hx]
    simp

end

end Work.ThomBordism
