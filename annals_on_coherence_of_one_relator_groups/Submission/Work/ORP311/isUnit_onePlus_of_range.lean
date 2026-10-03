/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (node B6 of `P311_DESIGN_LEAD.md`)

# The core of Proposition 3.11: `1 + A·ι(t)` is a unit for `A` in the range of `liftUN N`

This is node B6, the algebraic heart of [JZLA20, Proposition 3.11].  For `N ⊴ G` normal,
`t : G` with `G = N ⋊ ⟨t⟩` (`Work.ORP311.IsExtensionByZ G N t`) and a square matrix `A` over
`U(G)` whose entries lie in the image of the transparent inclusion `U(↥N) ↪ U(G)`
(`Work.ORP311.P311.liftUN N`, cf. node B1), the matrix

  `1 + A · ι (single t 1)`

is a unit of `Mₙ(U(G))`.

## Proof

* Clear denominators (node B2/`Work.ORP311.exists_common_denom`): there are a non-zero-divisor
  `e ∈ N(↥N)` and `B ∈ Mₙ(N(↥N))` with `numG G (Φ_N e) * A i j = numG G (Φ_N (B i j))`.
* Let `Z := Matrix.scalar (Fin n) (Φ_N e) + (B.map (Φ_N)) * Matrix.scalar (Fin n) (λ t)` over
  `N(G)`.  Then (`Work.ORP311.matOp_add`, `Work.ORVonNeumann.Rep.vnMatOpMul`,
  `Work.ORP311.matOp_scalar_leftReg`)

    `matOp Z = twoTerm n t (matOp (Matrix.scalar (Fin n) (Φ_N e))) (matOp (B.map (Φ_N)))`,

  and the analytic core `Work.ORP311.twoTerm_injective` — whose hypotheses are
  block-diagonality (`Work.ORP311.isBlockDiag_matOp_PhiN`), `ρ(N)`- and `ρ(t)`-equivariance
  (`Work.ORVonNeumann.Rep.vnMatOpEquivariant`) and injectivity of the constant part
  (`Work.ORP311.injective_matOp_scalar` with `Work.ORP311.P311.PhiN_mem_nonZeroDivisors`) —
  shows that `matOp Z` is injective.
* Node B4d (`Work.ORP311.isUnit_map_numOf`) upgrades this to `IsUnit (Z.map (numG G))`.
* The matrix identity `Work.ORP311.map_numG_denom` rewrites that as
  `Matrix.scalar (Fin n) (numG G (Φ_N e)) * (1 + A · numG G (λ t))`, and
  `numG G (λ t) = ι (single t 1)` (`Work.ORP311.iota_single_eq_numG_leftReg`); the
  denominator factor is a unit (`Work.ORP311.P311.isUnit_numG_PhiN`), so the remaining factor
  `1 + A · ι (single t 1)` is a unit as well.

## Main results

* `Work.ORP311.iota_single_eq_numG_leftReg`;
* `Work.ORP311.isUnit_onePlus_of_range`.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.DenomClearing
import Submission.Work.ORP311.exists_common_denom
import Submission.Work.ORP311.isUnit_map_numOf
import Submission.Work.ORP311.isBlockDiag_matOp_PhiN
import Submission.Work.ORP311.matOp_scalar_leftReg
import Submission.Work.ORP311.matOp_add
import Submission.Work.ORP311.injective_matOp_scalar
import Submission.Work.ORP311.map_numG_denom
import Submission.Work.ORP311.twoTerm_injective
import Submission.Work.ORP311.BlockShift

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **`ι (single t 1)` is `numG G` of the left regular operator `λ(t)`.**  (The left regular
operator is written out as the element `⟨λ(t), _⟩` of `N(G)` to avoid the clash of the
workspace namespace `Work.ORVonNeumann.Rep` with Mathlib's `Rep`.) -/
theorem iota_single_eq_numG (t : G) :
    iota G (MonoidAlgebra.single t (1 : ℂ))
      = P311.numG G (⟨Rep.leftRegOp t, Rep.leftRegOp_mem_groupVonNeumann t⟩ :
          ↥(groupVonNeumann G)) := by
  show VonNeumannAlgebra.toU (countableModel G) (MonoidAlgebra.single t (1 : ℂ))
    = VonNeumannAlgebra.numOf (countableModel G)
        (⟨Rep.leftRegOp t, Rep.leftRegOp_mem_groupVonNeumann t⟩ : ↥(groupVonNeumann G))
  rw [VonNeumannAlgebra.toU_single (countableModel G) t 1, one_smul]
  exact congrArg (VonNeumannAlgebra.numOf (countableModel G))
    (Subtype.ext (Rep.leftRegularHom_coe t))

/-- `Matrix.map` of a scalar matrix is the scalar matrix of the image. -/
theorem map_scalar_eq {R S : Type*} [Ring R] [Ring S] {n : ℕ} (a : R) (f : R → S)
    (hf : f 0 = 0) :
    (Matrix.scalar (Fin n) a).map f = Matrix.scalar (Fin n) (f a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, hf]

/-- **The core of [JZLA20, Proposition 3.11]** (node B6): `1 + A · ι (single t 1)` is a unit of
`Mₙ(U(G))` for every matrix `A` whose entries lie in the image of `U(↥N) ↪ U(G)`. -/
theorem isUnit_onePlus_of_range (N : Subgroup G) (hN : N.Normal) (t : G)
    (hext : IsExtensionByZ G N t) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
    (hA : ∀ i j, A i j ∈ Set.range (P311.liftUN N)) :
    IsUnit (1 + A * Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single t (1 : ℂ)))) := by
  classical
  -- The twist data needed by the block-diagonality lemmas follows from normality.
  have hT : P311.TwistData N t :=
    ⟨fun x hx => hN.conj_mem x hx t,
      fun x hx => by simpa using hN.conj_mem x hx t⁻¹,
      fun k hk => hext.2 k hk⟩
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
  -- ### the hypotheses of `twoTerm_injective`
  have hinjD : Function.Injective
      (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e))) :=
    injective_matOp_scalar (P311.PhiN N e)
      (Work.Rep.Ore.injective_of_mem_nonZeroDivisors _
        (P311.PhiN_mem_nonZeroDivisors (G := G) N he))
  have hD : IsBlockDiag (G := G) N t n
      (Rep.matOp (G := G) (Matrix.scalar (Fin n) (P311.PhiN N e))) := by
    have h := isBlockDiag_matOp_PhiN (G := G) hT (Matrix.scalar (Fin n) e)
    rwa [map_scalar_eq (a := e) (f := P311.PhiN N) (map_zero _)] at h
  have hC : IsBlockDiag (G := G) N t n (Rep.matOp (G := G) (B.map (P311.PhiN N))) :=
    isBlockDiag_matOp_PhiN (G := G) hT B
  -- ### injectivity of `matOp Z`
  have hEinj : Function.Injective (Rep.matOp (G := G) Z) := by
    rw [hmatOp]
    exact twoTerm_injective (G := G) N hN t hext n _ _
      hD hC
      (fun k => Rep.vnMatOpEquivariant _ (k : G))
      (fun k => Rep.vnMatOpEquivariant _ (k : G))
      (Rep.vnMatOpEquivariant _ t) (Rep.vnMatOpEquivariant _ t) hinjD
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
