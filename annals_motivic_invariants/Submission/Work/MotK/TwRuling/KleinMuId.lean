import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Ring
import Submission.Work.MotTDG.rhoVW_eq_zero
import Submission.Work.MotTDG.muMat_det_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `μ`-identity of a Klein datum over an arbitrary field extension

**TDG-c/d/e, in the form needed for the comparison of two Klein data.**  Node TDG proves, for a
Klein datum `D` whose Klein coordinates satisfy the Pfaffian equations (`klein_eq`) and which
satisfies `spans`, the identity

  `p_k (C v) = ∑_j μ_{k j} · vwQuad_j (v)`,   `C = cL D L`, `μ = muMat D L`,

for `v` in the base field `L`.  Because `quad_reduce` (TDG-c) is a polynomial identity over an
arbitrary commutative ring and `rhoVW_eq_zero` (TDG-d) is an identity of constants, the same
identity holds for `v` in *every* field `R ⊇ 𝕜`, with the coefficients pushed to `R`.  That is the
form in which the construction of an isomorphism `L(E) ≅ L(E')` between two Klein data with the
same Klein parameters uses it: there `R` is the function field of the first curve and
`v = C'⁻¹ C · bas`.

## Main results

* `Work.MotK.TwRuling.kleinP_coord_eq_muMat` — the identity over any field `R ⊇ 𝕜`.
* `Work.MotK.TwRuling.vwQuad_eq_zero_of_kleinP` — if `p_k (a, b, C' · v) = 0` for all `k` (with
  `C'` the Klein matrix of a second Klein datum `D'` with `ab ≠ 0`, `klein_eq` and `spans`), then
  the Veronese--Weierstrass quadrics of `D'` vanish at `v` (this is the invertibility of `μ`,
  TDG-e).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜]

/-- **The `μ`-identity of a Klein datum over an arbitrary field extension.**  For a Klein datum
`D` whose Klein coordinates satisfy the Pfaffian equations, the reduction identity
`p_k (C v) = ∑_j μ_{k j} vwQuad_j v` (nodes TDG-c and TDG-d) holds with `v` in *any* field
`R ⊇ 𝕜`, with the coefficients of `D` pushed to `R`. -/
theorem kleinP_coord_eq_muMat (D : Work.MotV.KleinData 𝕜)
    (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0)
    (R : Type) [Field R] [Algebra 𝕜 R] (v : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap 𝕜 R D.a) (algebraMap 𝕜 R D.b)
        (fun i => ∑ m, (Work.MotTDG.cL D R) i m * v m) k
      = ∑ j, (Work.MotTDG.muMat D R) k j *
          Work.MotTDG.vwQuad (D.E.baseChange R).a₁ (D.E.baseChange R).a₂ (D.E.baseChange R).a₃
            (D.E.baseChange R).a₄ (D.E.baseChange R).a₆ v j := by
  set P : Fin 5 → R :=
    Work.MotTDG.colP (algebraMap 𝕜 R D.a) (algebraMap 𝕜 R D.b) (Work.MotTDG.cL D R) k with hP
  set B : Fin 5 → Fin 5 → R :=
    Work.MotTDG.colB (algebraMap 𝕜 R D.a) (algebraMap 𝕜 R D.b) (Work.MotTDG.cL D R) k with hB
  have hquad : Work.MotK.kleinP (algebraMap 𝕜 R D.a) (algebraMap 𝕜 R D.b)
      (fun i => ∑ m, (Work.MotTDG.cL D R) i m * v m) k = Work.MotTDG.quadForm P B v :=
    Work.MotTDG.kleinP_mulVec_expand _ _ _ _ _
  rw [hquad, Work.MotTDG.quad_reduce (D.E.baseChange R).a₁ (D.E.baseChange R).a₂
    (D.E.baseChange R).a₃ (D.E.baseChange R).a₄ (D.E.baseChange R).a₆ P B v]
  rw [show (∑ t, Work.MotTDG.rhoVW (D.E.baseChange R).a₁ (D.E.baseChange R).a₂
      (D.E.baseChange R).a₃ (D.E.baseChange R).a₄ (D.E.baseChange R).a₆ P B t
      * Work.MotTDG.goodMon v t) = 0 from
    Finset.sum_eq_zero fun t _ => by rw [Work.MotTDG.rhoVW_eq_zero D hkl R k t, zero_mul]]
  rw [add_zero]
  rfl

/-- **Consequence.**  If the Klein equations `p_k (a, b, C' · v) = 0` hold for all `k` (with `C'`
the Klein matrix of a Klein datum `D'` having `ab ≠ 0`, `klein_eq` and `spans`), then the
Veronese--Weierstrass quadrics of `D'` vanish at `v`: the `μ`-matrix of TDG-e is invertible, so the
identity of `kleinP_coord_eq_muMat` can be solved for `vwQuad v`. -/
theorem vwQuad_eq_zero_of_kleinP (D D' : Work.MotV.KleinData 𝕜)
    (hab : D'.a * D'.b ≠ 0)
    (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D'.a) (algebraMap 𝕜 _ D'.b)
        (Work.MotV.kleinCoord D' L) k = 0)
    (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D' L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D' L i)
    (R : Type) [Field R] [Algebra 𝕜 R] (v : Fin 5 → R)
    (hv : ∀ k : Fin 5,
      Work.MotK.kleinP (algebraMap 𝕜 R D'.a) (algebraMap 𝕜 R D'.b)
        (fun i => ∑ m, (Work.MotTDG.cL D' R) i m * v m) k = 0) :
    Work.MotTDG.vwQuad (D'.E.baseChange R).a₁ (D'.E.baseChange R).a₂ (D'.E.baseChange R).a₃
      (D'.E.baseChange R).a₄ (D'.E.baseChange R).a₆ v = 0 := by
  have hdet : (Work.MotTDG.muMat D' R).det ≠ 0 :=
    Work.MotTDG.muMat_det_ne_zero D' hab hkl hsp R
  have hsum : ∀ k : Fin 5,
      ∑ j, (Work.MotTDG.muMat D' R) k j *
        Work.MotTDG.vwQuad (D'.E.baseChange R).a₁ (D'.E.baseChange R).a₂
          (D'.E.baseChange R).a₃ (D'.E.baseChange R).a₄ (D'.E.baseChange R).a₆ v j = 0 := by
    intro k
    rw [← kleinP_coord_eq_muMat D' hkl R v k, hv k]
  have hmul : (Work.MotTDG.muMat D' R).mulVec
      (Work.MotTDG.vwQuad (D'.E.baseChange R).a₁ (D'.E.baseChange R).a₂
        (D'.E.baseChange R).a₃ (D'.E.baseChange R).a₄ (D'.E.baseChange R).a₆ v)
      = (Work.MotTDG.muMat D' R).mulVec 0 := by
    funext k
    simpa [Matrix.mulVec, dotProduct] using hsum k
  exact (Matrix.mulVec_injective_of_det_ne_zero (M := Work.MotTDG.muMat D' R) hdet) hmul

end Work.MotK.TwRuling
