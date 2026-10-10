import Mathlib
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

open MvPolynomial

/-! ## Implementation note (to the route recorded in the docstring below)

The two ingredients of the recorded route are

* `R' ≅ R[y₁,…,y_k]` (`stabAlgEquiv`, from `MvPolynomial.sumAlgEquiv` and `finSumFinEquiv`),
* `R_F[y₁,…,y_k] = (R[y₁,…,y_k])_F` (localisation commutes with adjoining variables).

The second one is available in Mathlib as `MvPolynomial.isLocalization`: for a submonoid `M` of a
commutative ring `R` and a commutative `R`-algebra `S` that is the localisation of `R` at `M`, the
`MvPolynomial σ R`-algebra `MvPolynomial σ S` is the localisation of `MvPolynomial σ R` at
`M.map (C (σ := σ))`.  The `MvPolynomial σ R`-algebra structure used there is
`MvPolynomial.algebraMvPolynomial`, which is deliberately not a global instance (it creates a
diamond), so it is enabled locally in this file.  With `M = Submonoid.powers F` and
`Submonoid.map_powers` this is exactly `IsLocalization.Away (C F) (MvPolynomial σ R_F)`, and the
statement of this file is obtained by transporting the localisation structure along `stabAlgEquiv`
(`IsLocalization.algEquivOfAlgEquiv`), passing to `MvPolynomial (Fin k)` of the isomorphism `Φ` of
coefficients (`MvPolynomial.mapAlgEquiv`) and transporting back. -/

-- The `MvPolynomial σ R`-algebra structure on `MvPolynomial σ S` (used by
-- `MvPolynomial.isLocalization`) is not a global instance; enable it for this file.
attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable section

namespace Work.MotA

/-- `Fin (n + k) ≃ Fin k ⊕ Fin n`; the inverse of the canonical identification
`Fin k ⊕ Fin n ≃ Fin (n + k)` composed with `Sum.swap`, so that `Fin.castAdd k` corresponds to
`Sum.inr`. -/
private def finCastAddEquiv (n k : ℕ) : Fin (n + k) ≃ Fin k ⊕ Fin n :=
  (finSumFinEquiv (m := n) (n := k)).symm.trans (Equiv.sumComm (Fin n) (Fin k))

/-- The `𝕜`-algebra isomorphism `𝕜[x₁,…,x_{n+k}] ≃ₐ[𝕜] 𝕜[x₁,…,x_k][x₁,…,x_n]` which views the
last `k` variables as the coefficients variables. -/
private noncomputable def stabAlgEquiv (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) :
    MvPolynomial (Fin (n + k)) 𝕜 ≃ₐ[𝕜] MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜) :=
  (MvPolynomial.renameEquiv 𝕜 (finCastAddEquiv n k)).trans
    (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n))

/-- `stabAlgEquiv` sends a polynomial in the first `n` variables to the corresponding constant
polynomial. -/
private theorem stabAlgEquiv_rename_castAdd (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ)
    (r : MvPolynomial (Fin n) 𝕜) :
    stabAlgEquiv 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r) = MvPolynomial.C r := by
  simp only [stabAlgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply]
  have hfun : (⇑(finCastAddEquiv n k) ∘ Fin.castAdd k) = (Sum.inr : Fin n → Fin k ⊕ Fin n) := by
    funext j; simp [finCastAddEquiv]
  have h : MvPolynomial.rename (finCastAddEquiv n k) (MvPolynomial.rename (Fin.castAdd k) r)
      = MvPolynomial.rename Sum.inr r := by
    rw [MvPolynomial.rename_rename (Fin.castAdd k) (finCastAddEquiv n k) r, hfun]
  rw [h]
  have h2 : (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n)) (MvPolynomial.rename Sum.inr r)
      = MvPolynomial.C r := by
    simpa [MvPolynomial.algebraMap_eq] using
      congrArg (fun f => f r) (MvPolynomial.sumAlgEquiv_comp_rename_inr 𝕜 (Fin k) (Fin n))
  rw [h2]

/-- Adjoining `k` polynomial variables commutes with localising in the coefficients: the
localisation of `R[y₁,…,y_k]` away from `F` (viewed as a constant polynomial) is
`(R_F)[y₁,…,y_k]`. -/
private theorem awayPolyEquiv (𝕜 : Type) [Field 𝕜] (n k : ℕ) (F : MvPolynomial (Fin n) 𝕜) :
    Nonempty (Localization.Away (MvPolynomial.C F :
        MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) ≃ₐ[𝕜]
      MvPolynomial (Fin k) (Localization.Away F)) := by
  haveI hScal : IsScalarTower 𝕜 (MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))
      (MvPolynomial (Fin k) (Localization.Away F)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show algebraMap 𝕜 (MvPolynomial (Fin k) (Localization.Away F)) a =
      (MvPolynomial.map (algebraMap (MvPolynomial (Fin n) 𝕜) (Localization.Away F)))
        (algebraMap 𝕜 (MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) a)
    have h1 : algebraMap 𝕜 (MvPolynomial (Fin k) (Localization.Away F)) a =
        MvPolynomial.C (algebraMap 𝕜 (Localization.Away F) a) := by
      rw [IsScalarTower.algebraMap_eq 𝕜 (Localization.Away F)
        (MvPolynomial (Fin k) (Localization.Away F)), MvPolynomial.algebraMap_eq]
      rfl
    have h2 : algebraMap 𝕜 (MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) a =
        MvPolynomial.C (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜) a) := by
      rw [IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin n) 𝕜)
        (MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)), MvPolynomial.algebraMap_eq]
      rfl
    rw [h1, h2, MvPolynomial.map_C, IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial (Fin n) 𝕜)
      (Localization.Away F)]
  haveI hLoc : IsLocalization.Away (MvPolynomial.C F :
      MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))
      (MvPolynomial (Fin k) (Localization.Away F)) := by
    haveI := MvPolynomial.isLocalization (σ := Fin k) (M := Submonoid.powers F)
      (S := Localization.Away F)
    rwa [Submonoid.map_powers] at this
  exact ⟨AlgEquiv.restrictScalars 𝕜
    (IsLocalization.algEquiv
      (Submonoid.powers (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (Localization.Away (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (MvPolynomial (Fin k) (Localization.Away F)))⟩

/-- **`A3`, algebraic stabilisation.**  An isomorphism of the localisations of `𝕜[x₁,…,xₙ]` away
from `F` and `G` persists after adjoining `k` further variables: `Localization.Away (rename F)` and
`Localization.Away (rename G)` in `𝕜[x₁,…,x_{n+k}]` are isomorphic as `𝕜`-algebras, where
`MvPolynomial.rename (Fin.castAdd k)` views a polynomial in `n` variables as one in `n + k` variables
not involving the last `k`.

Route (do not trust the tensor-product names; use the second route below).  Write `R = 𝕜[Fin n]`,
`R' = 𝕜[Fin (n+k)]`, and view `R'` as the polynomial ring `R[y₁,…,y_k]` — a `𝕜`-algebra and an
`R`-algebra — via `MvPolynomial.sumAlgEquiv` composed with `finSumFinEquiv`
(that identification sends `MvPolynomial.rename (Fin.castAdd k) F` to `F`).  Then
`Localization.Away F` over `R'` is a localisation of `R'`, and `Φ : R_F ≃ₐ[𝕜] R_G` extends
uniquely to an isomorphism of the localisations of `R'` by the universal property of localisation:
the composite `R' → R → R_F → Localization.Away (rename F)` (first arrow the `R`-algebra structure,
second `Φ⁻¹`, third the canonical map) inverts `rename F`, so it factors through
`Localization.Away (rename F) → Localization.Away (rename G)` by `IsLocalization.lift` (or
`IsLocalization.awayLift` if present), and symmetrically in the other direction; the two composites
are equal on the image of `R'` and on the inverse of `rename F` (a unit), hence equal by
`IsLocalization.ringHom_ext`.  Degenerate cases do not need separate treatment (for `F = 0` both
sides are the zero ring — `Subsingleton`), but a `Subsingleton.elim`-based shortcut is acceptable.

Useful existing material: the scratch files `_chk_stab.lean` and `_check_stab.lean` at the workspace
root construct `stabAlgEquiv : 𝕜[x₁..x_{n+k}] ≃ₐ[𝕜] MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)`
from `MvPolynomial.sumAlgEquiv` and `finSumFinEquiv` and prove
`stabAlgEquiv (rename (Fin.castAdd k) r) = C r`; they can be adapted (they are not imported by
anything). -/
theorem awayAlgEquiv_stab (𝕜 : Type) [Field 𝕜] (n k : ℕ) (F G : MvPolynomial (Fin n) 𝕜)
    (Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G) :
    Nonempty (Localization.Away (MvPolynomial.rename (Fin.castAdd k) F) ≃ₐ[𝕜]
      Localization.Away (MvPolynomial.rename (Fin.castAdd k) G)) := by
  have hθF : stabAlgEquiv 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) F) = MvPolynomial.C F :=
    stabAlgEquiv_rename_castAdd 𝕜 n k F
  have hθG : stabAlgEquiv 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) G) = MvPolynomial.C G :=
    stabAlgEquiv_rename_castAdd 𝕜 n k G
  -- `stabAlgEquiv` carries the submonoid of powers of `rename F` to the submonoid of powers of
  -- the constant polynomial `C F` (and similarly for `G`).
  have HF : Submonoid.map (stabAlgEquiv 𝕜 n k)
      (Submonoid.powers (MvPolynomial.rename (Fin.castAdd k) F)) =
      Submonoid.powers (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) := by
    rw [Submonoid.map_powers, hθF]
  have HG : Submonoid.map (stabAlgEquiv 𝕜 n k)
      (Submonoid.powers (MvPolynomial.rename (Fin.castAdd k) G)) =
      Submonoid.powers (MvPolynomial.C G : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) := by
    rw [Submonoid.map_powers, hθG]
  -- Transport of the localisation structure along `stabAlgEquiv`.
  let eF1 : Localization.Away (MvPolynomial.rename (Fin.castAdd k) F) ≃ₐ[𝕜]
      Localization.Away (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) :=
    IsLocalization.algEquivOfAlgEquiv
      (A := 𝕜) (R := MvPolynomial (Fin (n + k)) 𝕜)
      (M := Submonoid.powers (MvPolynomial.rename (Fin.castAdd k) F))
      (S := Localization.Away (MvPolynomial.rename (Fin.castAdd k) F))
      (P := MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))
      (T := Submonoid.powers (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (Q := Localization.Away (MvPolynomial.C F : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (stabAlgEquiv 𝕜 n k) HF
  let eG1 : Localization.Away (MvPolynomial.rename (Fin.castAdd k) G) ≃ₐ[𝕜]
      Localization.Away (MvPolynomial.C G : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) :=
    IsLocalization.algEquivOfAlgEquiv
      (A := 𝕜) (R := MvPolynomial (Fin (n + k)) 𝕜)
      (M := Submonoid.powers (MvPolynomial.rename (Fin.castAdd k) G))
      (S := Localization.Away (MvPolynomial.rename (Fin.castAdd k) G))
      (P := MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))
      (T := Submonoid.powers (MvPolynomial.C G : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (Q := Localization.Away (MvPolynomial.C G : MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)))
      (stabAlgEquiv 𝕜 n k) HG
  -- `R_F[y₁,…,y_k] ≅ (R[y₁,…,y_k])_F` and its analogue for `G`.
  obtain ⟨eF2⟩ := awayPolyEquiv 𝕜 n k F
  obtain ⟨eG2⟩ := awayPolyEquiv 𝕜 n k G
  -- The isomorphism `Φ` of the coefficients, extended to the polynomial ring in `k` variables.
  let eΦ : MvPolynomial (Fin k) (Localization.Away F) ≃ₐ[𝕜]
      MvPolynomial (Fin k) (Localization.Away G) := MvPolynomial.mapAlgEquiv (Fin k) Φ
  exact ⟨eF1.trans (eF2.trans (eΦ.trans (eG2.symm.trans eG1.symm)))⟩

end Work.MotA
