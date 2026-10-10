import Mathlib
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

open MvPolynomial

/-- The index identification `Fin (n + k) ≃ Fin k ⊕ Fin n` which sends the first `k` indices
(the `y`-variables) to `inl` and the last `n` indices (the `x`-variables) to `inr`. -/
noncomputable def castAddFinEquiv (n k : ℕ) : Fin (n + k) ≃ Fin k ⊕ Fin n :=
  (finSumFinEquiv (m := n) (n := k)).symm.trans (Equiv.sumComm (Fin n) (Fin k))

/-- The `𝕜`-algebra equivalence exhibiting `𝕜[Fin (n + k)]` as the polynomial ring in `k` new
variables `y₁,…,y_k` over `𝕜[Fin n]`: the first `k` variables `x_{n+1},…,x_{n+k}` become the new
variables, the first `n` variables become the coefficients.  The map `MvPolynomial.rename (Fin.castAdd
k)` (viewing `𝕜[Fin n]` inside `𝕜[Fin (n+k)]`) becomes `MvPolynomial.C`. -/
noncomputable def castAddStabAlgEquiv (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ) :
    MvPolynomial (Fin (n + k)) 𝕜 ≃ₐ[𝕜] MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜) :=
  (MvPolynomial.renameEquiv 𝕜 (castAddFinEquiv n k)).trans
    (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n))

/-- The defining property of `castAddStabAlgEquiv`: on polynomials not involving the last `k`
variables it is `MvPolynomial.C`. -/
theorem castAddStabAlgEquiv_rename_castAdd (𝕜 : Type) [CommSemiring 𝕜] (n k : ℕ)
    (r : MvPolynomial (Fin n) 𝕜) :
    castAddStabAlgEquiv 𝕜 n k (MvPolynomial.rename (Fin.castAdd k) r) = MvPolynomial.C r := by
  simp only [castAddStabAlgEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply]
  have hfun : (⇑(castAddFinEquiv n k) ∘ Fin.castAdd k) = (Sum.inr : Fin n → Fin k ⊕ Fin n) := by
    funext j; simp [castAddFinEquiv]
  have h : MvPolynomial.rename (castAddFinEquiv n k) (MvPolynomial.rename (Fin.castAdd k) r)
      = MvPolynomial.rename Sum.inr r := by
    rw [MvPolynomial.rename_rename (Fin.castAdd k) (castAddFinEquiv n k) r, hfun]
  rw [h]
  have h2 : (MvPolynomial.sumAlgEquiv 𝕜 (Fin k) (Fin n)) (MvPolynomial.rename Sum.inr r)
      = MvPolynomial.C r := by
    simpa [MvPolynomial.algebraMap_eq] using
      congrArg (fun f => f r) (MvPolynomial.sumAlgEquiv_comp_rename_inr 𝕜 (Fin k) (Fin n))
  rw [h2]

/-- **`A3`, residue rings under stabilisation.**  If `p` is a prime ideal of `𝕜[x₁,…,xₙ]`, then
the quotient of `𝕜[x₁,…,x_{n+k}]` by the extension of `p` along
`MvPolynomial.rename (Fin.castAdd k)` is the polynomial ring in `k` new variables over
`𝕜[x₁,…,xₙ] ⧸ p`:
`𝕜[Fin (n+k)] ⧸ p.map (rename (Fin.castAdd k)) ≃ₐ[𝕜] MvPolynomial (Fin k) (𝕜[Fin n] ⧸ p)`.

This is the algebraic half of the residue-field computation `κ(renamed point) = κ(x)(y₁,…,y_k)` used
in the stabilisation census `Work.MotA.divCount_rename` (`A3`); combined with
`Work.MotA.resEquiv_iff_fractionRing` it identifies the residue field of the point with ideal
`p.map (rename (Fin.castAdd k))` as `FractionRing (MvPolynomial (Fin k) (𝕜[Fin n] ⧸ p))` (and
`Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv` transports this to fraction fields).

Route.  `rename (Fin.castAdd k)` exhibits `𝕜[Fin (n+k)]` as the polynomial ring in the `k` new
variables over `𝕜[Fin n]` — use the `𝕜`-algebra equivalence
`Work.Twist`/scratch `stabAlgEquiv` (see `_chk_stab.lean`, `_zz_renamechk.lean` at the workspace
root) or `MvPolynomial.sumAlgEquiv` with `finSumFinEquiv`.  Under it, `p.map (rename (Fin.castAdd k))`
corresponds to `Ideal.span (p.map MvPolynomial.C)` in `MvPolynomial (Fin k) (𝕜[Fin n])`, and
`MvPolynomial (Fin k) R ⧸ Ideal.span (p.map C) ≅ MvPolynomial (Fin k) (R ⧸ p)` is the standard
quotient-by-extension isomorphism (Mathlib: `Ideal.quotientEquiv` with
`MvPolynomial.quotientMap`/`MvPolynomial.aeval`, or `AlgEquiv` built from the universal property:
the composite `R[y] → (R ⧸ p)[y]` is surjective with kernel `p.map C`).  The `𝕜`-algebra structures
are the canonical ones, so an `AlgEquiv` (wrapped in `Nonempty`) is what is produced. -/
theorem quotient_map_rename (𝕜 : Type) [Field 𝕜] (n k : ℕ)
    (p : Ideal (MvPolynomial (Fin n) 𝕜)) [p.IsPrime] :
    Nonempty ((MvPolynomial (Fin (n + k)) 𝕜 ⧸
        p.map (MvPolynomial.rename (Fin.castAdd k))) ≃ₐ[𝕜]
      MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜 ⧸ p)) := by
  classical
  -- The comparison of ring homs `R' → R[y]` underlying the whole computation.
  have hcomp : ((castAddStabAlgEquiv 𝕜 n k : MvPolynomial (Fin (n + k)) 𝕜 →+*
        MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))).comp
      (MvPolynomial.rename (Fin.castAdd k)).toRingHom
      = (MvPolynomial.C : MvPolynomial (Fin n) 𝕜 →+*
        MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) := by
    apply RingHom.ext
    intro r
    simpa using castAddStabAlgEquiv_rename_castAdd 𝕜 n k r
  -- Under `castAddStabAlgEquiv`, the extension of `p` becomes `p.map C`.
  have hmap : (p.map (MvPolynomial.rename (Fin.castAdd k))).map
        (castAddStabAlgEquiv 𝕜 n k : MvPolynomial (Fin (n + k)) 𝕜 →+*
          MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜))
      = p.map (MvPolynomial.C : MvPolynomial (Fin n) 𝕜 →+*
          MvPolynomial (Fin k) (MvPolynomial (Fin n) 𝕜)) := by
    -- turn the `AlgHom`-indexed `Ideal.map` into a `RingHom`-indexed one
    rw [show p.map (MvPolynomial.rename (Fin.castAdd k))
        = Ideal.map (MvPolynomial.rename (Fin.castAdd k)).toRingHom p from rfl]
    rw [Ideal.map_map, hcomp]
  refine ⟨(Ideal.quotientEquivAlg _ _ (castAddStabAlgEquiv 𝕜 n k) hmap.symm).trans ?_⟩
  exact (AlgEquiv.restrictScalars 𝕜
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin k) p)).symm

end Work.MotA
