import Mathlib
import Submission.Work.Pi6.MSSK.Defs
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.ezSimplexZero_chain_class
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The induction statement of the cap/transport lemma

`Work.Pi6.MSSK.Aux` is the *canonical form* of the main induction hypothesis of
`Work.Pi6.MSSK.capPieceTransport` (see `REFS/NOTES_LEAD_MSSK.md` §1):  for every *relative* cycle `c`
of `T_σ` of degree `s + k` (i.e. the projection of `c` to the σ-piece is a cycle), the chain
`thetaTop ⌢ c` is a cycle lying over the last vertex of `Δ[s]`, and the class of its lift through
`fibreInc`, read in the fibre over the last vertex through the canonical identification
`vertexIso`, is `capSign R s` times the `triv`-image of the class of `π c` under `serreE1PieceIso`.

`capSign R s = (-1)^(s(s+1)/2)` is the accumulated sign of the iterated last-face connecting map
(formulated recursively so that its recursion is definitional).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- The accumulated sign `(-1)^(s(s+1)/2)` of the iterated last-face connecting map, defined
recursively: `capSign 0 = 1` and `capSign (s+1) = (-1)^(s+1) * capSign s`. -/
def capSign (R : Type) [CommRing R] : ℕ → R :=
  fun s => Nat.rec 1 (fun k acc => (-1 : R) ^ (k+1) * acc) s

variable {R : Type} [CommRing R]

lemma capSign_zero : capSign R 0 = (1 : R) := rfl

lemma capSign_succ (s : ℕ) : capSign R (s+1) = (-1 : R) ^ (s+1) * capSign R s := rfl

lemma neg_one_pow_eq_one_or_neg_one (R : Type) [Ring R] (n : ℕ) :
    ((-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1) := by
  induction n with
  | zero => exact Or.inl (pow_zero _)
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h] <;> simp

/-- `capSign` is `±1`. -/
lemma capSign_eq_one_or_neg_one (s : ℕ) : capSign R s = 1 ∨ capSign R s = -1 := by
  induction s with
  | zero => exact Or.inl rfl
  | succ s ih =>
    rw [capSign_succ]
    have h := neg_one_pow_eq_one_or_neg_one R (s+1)
    rcases h with h | h <;> rcases ih with ih | ih <;> rw [h, ih] <;> norm_num


variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The induction statement of the cap/transport lemma.**  For a simplex `σ : Δ[s] ⟶ Sing B`, a
number `k`, and every relative cycle `c` of `T_σ` of degree `s + k` (i.e. such that the projection
of `c` to the σ-piece is a cycle), there is a cycle `z'` of the part of `T_σ` over the last vertex
whose `fibreInc`-image is `thetaTop ⌢ c`, and whose class, read in the fibre over the last vertex
through `vertexIso` and then in the coefficient module through `triv`, is `capSign R s` times the
`triv`-image of the class of `π c` under the E¹ isomorphism `serreE1PieceIso`. -/
def Aux (R : Type) [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (s k : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B) : Prop :=
  ∀ (c : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)).X (s + k))
    (hcrel : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).d (s+k)
        ((ComplexShape.down ℕ).next (s+k))))
      ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
        (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c) = 0),
    ∃ z' : (Work.SSSR.sCC R (Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (Work.Pi6.MSSK.lastV s ≫ σ))).cycles k,
      (ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.Pi6.MSSK.fibreInc p σ)).f k)
          ((ModuleCat.Hom.hom ((Work.SSSR.sCC R _).iCycles k)) z'))
        = Work.Cohomology.cap R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
            (Work.Pi6.MSSK.thetaTop R p σ) k c
      ∧ (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert (Work.Pi6.MSSK.lastV s ≫ σ))).hom.hom
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.SSSR.sCCMap R (Work.Pi6.MSSK.vertexIso p (Work.Pi6.MSSK.lastV s ≫ σ)).hom) k))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCC R _).homologyπ k)) z'))
        = capSign R s • (Work.SSSR.triv p e₀ hfib hsconn k (Work.SSSR.sigmaVert σ)).hom.hom
            ((Work.SSSR.serreE1PieceIso p hfib s k σ).hom.hom
              ((ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).homologyπ (s+k)))
                ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p) σ).cyclesMk
                  ((ModuleCat.Hom.hom ((CategoryTheory.Limits.cokernel.π
                    (Work.SSSR.sCCMap R (Work.SSSR.bdryAlong (Work.SSSR.sSingP p) σ).ι)).f (s+k))) c)
                  ((ComplexShape.down ℕ).next (s+k)) rfl hcrel)))

end

end Work.Pi6.MSSK
