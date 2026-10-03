/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (node B6 of `P311_DESIGN_LEAD.md`, twist-hypothesis form)

# The core of Proposition 3.11 with `TwistData N t` as the only hypothesis

The design's node B6 asks for the unit statement

  `IsUnit (1 + A · ι (single t 1))`

for a matrix `A` over `U(G)` all of whose entries lie in the image of the transparent inclusion
`U(↥N) ↪ U(G)` (`Work.ORP311.P311.liftUN N`), where — and this is the point — the only
hypotheses on `(N, t)` are `Work.ORP311.P311.TwistData N t`, i.e. that `t` normalises `N` and has
infinite order modulo `N`.  In particular **`G = N ⋊ ⟨t⟩` is not assumed**; that is the shape in
which the consumers (`Work.ORP311.prop311OnComplex`, `Work.ORP311.prop311`) can supply the data,
where `N` is an arbitrary normal subgroup of a finitely generated subgroup `H₀ ≤ H ≤ G` and `t`
an arbitrary element of `H₀`.

## Proof

The algebraic half of the argument is that of `Work.ORP311.isUnit_onePlus_of_range` and is
reproduced verbatim:

* clear denominators (`Work.ORP311.exists_common_denom`): there are a non-zero-divisor
  `e ∈ N(↥N)` and `B ∈ Mₙ(N(↥N))` with `numG G (Φ_N e) * A i j = numG G (Φ_N (B i j))`;
* `Z := Matrix.scalar (Fin n) (Φ_N e) + (B.map (Φ_N)) * Matrix.scalar (Fin n) (λ t)` over `N(G)`
  satisfies `matOp Z = twoTerm n t (matOp (scalar (Φ_N e))) (matOp (B.map (Φ_N)))`
  (`Work.ORP311.matOp_add`, `Work.ORVonNeumann.Rep.vnMatOpMul`,
  `Work.ORP311.matOp_scalar_leftReg`);
* `Work.ORP311.isUnit_map_numOf` upgrades injectivity of `matOp Z` to `IsUnit (Z.map (numG G))`;
* `Work.ORP311.map_numG_denom` rewrites that as a denominator times `1 + A · ι (single t 1)`, and
  the denominator is a unit (`Work.ORP311.P311.isUnit_numG_PhiN`);
* `Work.ORP311.iota_single_eq_numG` identifies `ι (single t 1)` with `numG G (λ t)`.

The analytic half is the only place where the twist hypothesis matters, and it is where this file
differs from `isUnit_onePlus_of_range`.  The injectivity of the two-term operator is obtained from
`Work.ORP311.twoTerm_injective_equivariant`, whose hypotheses are exactly the ones available here:
equivariance of `matOp` operators (`Work.ORVonNeumann.Rep.vnMatOpEquivariant`) and block
diagonality of `matOp Z` **and of its adjoint** over the right `N`-cosets.

* Block diagonality of `matOp (B.map (Φ_N))` is `Work.ORP311.isBlockDiag_matOp_PhiN` (which needs
  only `TwistData`).
* Block diagonality of its adjoint is *not* the general lemma `isBlockDiag_adjoint_twist` (which
  does need `G = N ⋊ ⟨t⟩`, since the adjoint of a general block diagonal operator is block
  diagonal only if that operator preserves the complement of the cosets).  For the specific
  operators coming from `Φ_N` it follows from the `∗`-compatibility of `Φ_N`:
  `matOp (B.map Φ_N)† = matOp (conjTranspose (B.map Φ_N)) = matOp ((conjTranspose B).map Φ_N)`
  (`Work.ORVonNeumann.Rep.vnMatOpAdjoint` and `conjTranspose_map_PhiN` below), and the latter is
  block diagonal again by `isBlockDiag_matOp_PhiN`.  The reason this is a *sufficient* substitute
  is structural: `Φ_N b` preserves `ℓ²(N q)` for every **left** coset `N q`, and each left coset
  is contained in `N⟨t⟩` or disjoint from it, so `Φ_N b` preserves the complement of the union of
  the right cosets as well.
* The scalar case `matOp (scalar (Φ_N e))` is the same with `B := Matrix.scalar (Fin n) e`, using
  `Work.ORP311.map_scalar_eq` to replace `Matrix.scalar (Fin n) (Φ_N e)` by
  `(Matrix.scalar (Fin n) e).map Φ_N`, and `Work.ORP311.injective_matOp_scalar` (with
  `Work.ORP311.P311.PhiN_mem_nonZeroDivisors`) for the injectivity of the constant part.

## Main results

* `Work.ORP311.conjTranspose_map_PhiN`;
* `Work.ORP311.isBlockDiag_adjoint_map_PhiN`, `Work.ORP311.isBlockDiag_adjoint_scalar_PhiN`;
* `Work.ORP311.isUnit_onePlus_of_range_twist`.
-/
import Mathlib
import Submission.Work.ORP311.isUnit_onePlus_of_range
import Submission.Work.ORP311.twoTerm_injective_equivariant
import Submission.Work.ORP311.exists_common_denom
import Submission.Work.ORP311.isUnit_map_numOf
import Submission.Work.ORP311.isBlockDiag_matOp_PhiN
import Submission.Work.ORP311.map_numG_denom
import Submission.Work.ORP311.DenomClearing
import Submission.Work.ORP311.injective_matOp_scalar
import Submission.Work.ORP311.matOp_scalar_leftReg
import Submission.Work.ORP311.matOp_add

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **`conjTranspose` commutes with the entrywise map `B ↦ B.map (Φ_N)`**: `Φ_N` is
`∗`-preserving (`Work.ORP311.P311.PhiN_spec N`), so taking adjoints of a matrix over `N(↥N)`
commutes with applying `Φ_N` entrywise. -/
theorem conjTranspose_map_PhiN {N : Subgroup G} {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ↥(groupVonNeumann ↥N)) :
    Matrix.conjTranspose (B.map (P311.PhiN N)) = (Matrix.conjTranspose B).map (P311.PhiN N) := by
  have h : Matrix.conjTranspose ((Matrix.conjTranspose B).map (P311.PhiN N))
      = B.map (P311.PhiN N) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (Matrix.conjTranspose_map (A := Matrix.conjTranspose B) (P311.PhiN N)
        (fun x => (P311.PhiN_spec N).2.1 x)).symm
  rw [← h, Matrix.conjTranspose_conjTranspose]

/-- **The adjoint of `matOp (B.map (Φ_N))` is block diagonal** over the right `N`-cosets, for
*every* matrix `B` over `N(↥N)` and with no hypothesis on `(N, t)` beyond `TwistData N t`.

Indeed `matOp (B.map Φ_N)† = matOp (conjTranspose (B.map Φ_N)) = matOp ((conjTranspose B).map Φ_N)`
by `Work.ORVonNeumann.Rep.vnMatOpAdjoint` and `Work.ORP311.conjTranspose_map_PhiN`, and
`matOp` of a `Φ_N`-matrix is block diagonal (`Work.ORP311.isBlockDiag_matOp_PhiN`). -/
theorem isBlockDiag_adjoint_map_PhiN {N : Subgroup G} {t : G} (h : P311.TwistData N t) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ↥(groupVonNeumann ↥N)) :
    IsBlockDiag N t n
      (ContinuousLinearMap.adjoint (Rep.matOp (G := G) (B.map (P311.PhiN N)))) := by
  rw [Rep.vnMatOpAdjoint, conjTranspose_map_PhiN (N := N)]
  exact isBlockDiag_matOp_PhiN h (Matrix.conjTranspose B)

/-- **The adjoint of `matOp (scalar (Φ_N a))` is block diagonal** over the right `N`-cosets, for
every `a ∈ N(↥N)`, again with `TwistData N t` as the only hypothesis.  This is
`isBlockDiag_adjoint_map_PhiN` at `B := Matrix.scalar (Fin n) a`, with
`Work.ORP311.map_scalar_eq` converting `Matrix.scalar (Fin n) (Φ_N a)` into
`(Matrix.scalar (Fin n) a).map Φ_N`. -/
theorem isBlockDiag_adjoint_scalar_PhiN {N : Subgroup G} {t : G} (h : P311.TwistData N t) {n : ℕ}
    (a : ↥(groupVonNeumann ↥N)) :
    IsBlockDiag N t n
      (ContinuousLinearMap.adjoint (Rep.matOp (G := G)
        (Matrix.scalar (Fin n) (P311.PhiN N a)))) := by
  rw [Rep.vnMatOpAdjoint, ← map_scalar_eq (a := a) (f := P311.PhiN N) (map_zero _),
    conjTranspose_map_PhiN (N := N)]
  exact isBlockDiag_matOp_PhiN h (Matrix.conjTranspose (Matrix.scalar (Fin n) a))

/-- **The core of [JZLA20, Proposition 3.11], twist form** (node B6 of `P311_DESIGN_LEAD.md`):
`1 + A · ι (single t 1)` is a unit of `Mₙ(U(G))` for every matrix `A` whose entries lie in the
image of `U(↥N) ↪ U(G)`, where `(N, t)` only satisfies `TwistData N t` (`t` normalises `N` and
has infinite order modulo `N`). -/
theorem isUnit_onePlus_of_range_twist {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) (t : G) (h : Work.ORP311.P311.TwistData N t) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Work.ORP311.concreteEnvelope G).U) (hA : ∀ i j, A i j ∈ Set.range (Work.ORP311.P311.liftUN N)) : IsUnit (1 + A * Matrix.scalar (Fin n) (Work.ORP311.iota G (MonoidAlgebra.single t (1 : ℂ)))) := by
  classical
  -- Clear denominators in `Mₙ(U_N)`.
  obtain ⟨e, he, B, hB⟩ := exists_common_denom (G := G) N n A hA
  -- The two-term operator `Z = scalar (Φ e) + (B.map Φ) · λ(t)` over `N(G)`.
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G),
      Z = Matrix.scalar (Fin n) (P311.PhiN N e)
        + B.map (P311.PhiN N) * Matrix.scalar (Fin n)
            (⟨Rep.leftRegOp t, Rep.leftRegOp_mem_groupVonNeumann t⟩ :
              ↥(groupVonNeumann G)) :=
    ⟨_, rfl⟩
  -- ### `matOp Z` is the two-term operator of the analytic core
  have hmatOp : Rep.matOp (G := G) Z
      = twoTerm (G := G) n t (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e)))
          (Rep.matOp (G := G) (B.map (P311.PhiN N))) := by
    rw [hZ, matOp_add, Rep.vnMatOpMul, matOp_scalar_leftReg]
    rfl
  -- ### the hypotheses of `twoTerm_injective_equivariant`
  have hinjS : Function.Injective
      (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e))) :=
    injective_matOp_scalar (P311.PhiN N e)
      (Work.Rep.Ore.injective_of_mem_nonZeroDivisors _
        (P311.PhiN_mem_nonZeroDivisors (G := G) N he))
  have hSb : IsBlockDiag (G := G) N t n
      (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e))) := by
    rw [← map_scalar_eq (a := e) (f := P311.PhiN N) (map_zero _)]
    exact isBlockDiag_matOp_PhiN h (Matrix.scalar (Fin n) e)
  have hSb' : IsBlockDiag (G := G) N t n
      (ContinuousLinearMap.adjoint
        (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e)))) :=
    isBlockDiag_adjoint_scalar_PhiN (G := G) (N := N) (t := t) h e
  have hCb : IsBlockDiag (G := G) N t n (Rep.matOp (G := G) (B.map (P311.PhiN N))) :=
    isBlockDiag_matOp_PhiN h B
  have hCb' : IsBlockDiag (G := G) N t n
      (ContinuousLinearMap.adjoint (Rep.matOp (G := G) (B.map (P311.PhiN N)))) :=
    isBlockDiag_adjoint_map_PhiN (G := G) (N := N) (t := t) h B
  -- ### injectivity of `matOp Z`
  have hEinj : Function.Injective (Rep.matOp (G := G) Z) := by
    rw [hmatOp]
    exact twoTerm_injective_equivariant (G := G) (N := N) (t := t) h n _ _
      (Rep.vnMatOpEquivariant _) (Rep.vnMatOpEquivariant _)
      hSb hSb' hCb hCb' hinjS
  -- ### the unit of `Mₙ(U(G))` attached to `Z`
  have hunitZ : IsUnit (Z.map (P311.numG G)) := isUnit_map_numOf (G := G) Z hEinj
  -- ### the matrix identity relating `Z` to `1 + A·ι t`
  have hiden : Z.map (P311.numG G)
      = Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e))
        * (1 + A * Matrix.scalar (Fin n)
            (iota G (MonoidAlgebra.single t (1 : ℂ)))) := by
    rw [hZ, iota_single_eq_numG]
    exact map_numG_denom (G := G) N t A e B hB
  -- ### the denominator is a unit, so the remaining factor is a unit
  have hunitσ : IsUnit (Matrix.scalar (Fin n) (P311.numG G (P311.PhiN N e))) :=
    (P311.isUnit_numG_PhiN (G := G) N e he).map (Matrix.scalar (Fin n))
  obtain ⟨u, hu⟩ := hunitσ
  obtain ⟨w, hw⟩ := hunitZ
  have h2 : (↑u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
      * (1 + A * Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single t (1 : ℂ))))
      = (↑w : Matrix (Fin n) (Fin n) (concreteEnvelope G).U) := by
    rw [hu, hw, ← hiden]
  have h1 : ((u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
        Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
      * (↑u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U) = 1 := Units.inv_mul u
  have hcalc : (1 + A * Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single t (1 : ℂ))))
      = ((u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
            Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
        * (↑w : Matrix (Fin n) (Fin n) (concreteEnvelope G).U) := by
    calc (1 + A * Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single t (1 : ℂ))))
        = ((u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
              Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
          * ((↑u : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
            * (1 + A * Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single t (1 : ℂ))))) := by
          rw [← mul_assoc, h1, one_mul]
      _ = ((u⁻¹ : (Matrix (Fin n) (Fin n) (concreteEnvelope G).U)ˣ) :
              Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
          * (↑w : Matrix (Fin n) (Fin n) (concreteEnvelope G).U) := by rw [h2]
  rw [hcalc]
  exact IsUnit.mul ⟨u⁻¹, rfl⟩ ⟨w, rfl⟩

end Work.ORP311
