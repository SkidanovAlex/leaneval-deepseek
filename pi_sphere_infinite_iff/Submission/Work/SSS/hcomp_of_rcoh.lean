import Mathlib
import Submission.Work.SSS.coherentLiftR

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

-- The hypothesis `hid` of `hcomp_of_rcoh` below is *not* used in its proof.  As it is written, the
-- `SSet.stdSimplex.δ`s occurring in its statement live in a *free* universe `SSet.{u}`: the
-- definition `SSet.stdSimplex : CosimplicialObject SSet.{u}` (with
-- `CosimplicialObject C := SimplexCategory ⥤ C` a plain `def`, moreover) is universe polymorphic,
-- and nothing in `hid`'s statement pins that universe down, so `hid` becomes a hypothesis at an
-- arbitrary, unrelated universe `u` and says nothing about the universe-zero cofaces of
-- `SSet.stdSimplex` that occur in `RCoh`/`HComp` (which are forced to universe zero by `stdSimp`
-- and `sSing`).  The identity `hid` is meant to encode is nevertheless available, and is supplied
-- below as `delta_pred_castPred`, from the (universe polymorphic) cosimplicial identity
-- `CosimplicialObject.δ_comp_δ'`.  This is why the linter for unused variables is switched off.
set_option linter.unusedVariables false

/-- **A codimension-two face of `Δ[m+2]`, in the two possible ways.**  For `j < k` the composite of
the coface `δ_{k.pred}` of `Δ[m]` with the coface `δ_j` of `Δ[m+1]` equals the composite of
`δ_{j.castPred}` with `δ_k`: both are the inclusion of the face of `Δ[m+2]` spanned by the vertices
other than `j` and `k`.  This is the universe-zero instance of
`Work.SSS.stdSimplex_delta_pred_castPred`, proved here from
`CosimplicialObject.δ_comp_δ'` for the cosimplicial object `SSet.stdSimplex` together with
`Fin.castSucc_castPred`. -/
private lemma delta_pred_castPred {m : ℕ} (j k : Fin (m + 3)) (hjk : j < k) :
    SSet.stdSimplex.δ (n := m) (k.pred (Fin.ne_zero_of_lt hjk)) ≫
        SSet.stdSimplex.δ (n := m + 1) j
      = SSet.stdSimplex.δ (n := m) (j.castPred (Fin.ne_last_of_lt hjk)) ≫
        SSet.stdSimplex.δ (n := m + 1) k := by
  have H : Fin.castSucc (j.castPred (Fin.ne_last_of_lt hjk)) < k := by
    rw [Fin.castSucc_castPred]; exact hjk
  exact (CosimplicialObject.δ_comp_δ' (X := SSet.stdSimplex) H).symm

/-- **Constructing the compatibility hypothesis for the next level from the coherence of two
consecutive levels.**  Given the level `m+1` data `Dn`, the level `m` data `Dprev` and the
coherence `RCoh p m Dprev Dn` (the restriction of `Dn` to the `i`-th face, `i ≠ 0`, is `Dprev`
of the corresponding face simplex), the pieces `Dn.Φ b' (δ_j ≫ σ)` (`j ≠ 0`, `σ` an `(m+2)`-simplex
of `Sing B` based at `b'`) are compatible over the horn, in the sense of
`Work.SSS.HComp p (m+1) Dn`.

Indeed both restrictions to the intersection of the `j`-th and the `k`-th faces (`j < k`) are
`Dprev` applied to the corresponding codimension-two face of `σ`; the two codimension-two faces
agree by the identity `hid` (the composition of the two cofaces in the two possible orders), which
is `Work.SSS.stdSimplex_delta_pred_castPred`.  The hypotheses of `RCoh` are available because
`j ≥ 1` and `j < k` imply that `k.pred` and `j.castPred` are nonzero, and because
`Work.SSS.sigmaVert_face` gives `sigmaVert (δ_j ≫ σ) = sigmaVert σ = b'`. -/
theorem hcomp_of_rcoh {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (m : ℕ) (Dn : Work.SSS.RLevel p (m + 1)) (Dprev : Work.SSS.RLevel p m)
    (hid : ∀ (j k : Fin (m + 3)) (hjk : j < k),
      SSet.stdSimplex.δ (n := m) (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SSet.stdSimplex.δ (n := m + 1) j
        = SSet.stdSimplex.δ (n := m) (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SSet.stdSimplex.δ (n := m + 1) k)
    (hcoh : Work.SSS.RCoh p m Dprev Dn) :
    Work.SSS.HComp p (m + 1) Dn := by
  -- Unfold the goal: the horn-compatibility of the pieces `Dn.Φ b' (δ_j ≫ σ)` over `Λ[m+2,0]`.
  simp only [Work.SSS.HComp]
  intro b' σ hσ
  simp only [Work.SSS.HornTensorCompatible]
  intro j k hj hk hjk
  -- The two indices at which `RCoh` has to be applied are nonzero: `j ≠ 0` and `j < k` give
  -- `1 < k`, hence `k.pred` (of value `k.val - 1`) is nonzero, and `j.castPred` has value
  -- `j.val ≠ 0`.
  have hk0 : k.pred (Fin.ne_zero_of_lt hjk) ≠ 0 := by
    intro h0
    have hval : (k.pred (Fin.ne_zero_of_lt hjk)).val = 0 := congrArg Fin.val h0
    rw [Fin.val_pred] at hval
    have hjv : 0 < j.val := by
      have : j.val ≠ 0 := fun hv => hj (Fin.ext (by simpa using hv))
      omega
    have hkv : j.val < k.val := hjk
    omega
  have hjc : j.castPred (Fin.ne_last_of_lt hjk) ≠ 0 :=
    Fin.castPred_ne_zero (Fin.ne_last_of_lt hjk) hj
  -- The faces are based at `b'`, by `sigmaVert_face`.
  have hσj : sigmaVert (SSet.stdSimplex.δ (n := m + 1) j ≫ σ) = b' := by
    rw [sigmaVert_face j hj σ, hσ]
  have hσk : sigmaVert (SSet.stdSimplex.δ (n := m + 1) k ≫ σ) = b' := by
    rw [sigmaVert_face k hk σ, hσ]
  have hσjk : sigmaVert (SSet.stdSimplex.δ (n := m) (k.pred (Fin.ne_zero_of_lt hjk)) ≫
      (SSet.stdSimplex.δ (n := m + 1) j ≫ σ)) = b' := by
    rw [sigmaVert_face (t := m) (k.pred (Fin.ne_zero_of_lt hjk)) hk0
          (SSet.stdSimplex.δ (n := m + 1) j ≫ σ),
        sigmaVert_face j hj σ, hσ]
  have hσkj : sigmaVert (SSet.stdSimplex.δ (n := m) (j.castPred (Fin.ne_last_of_lt hjk)) ≫
      (SSet.stdSimplex.δ (n := m + 1) k ≫ σ)) = b' := by
    rw [sigmaVert_face (t := m) (j.castPred (Fin.ne_last_of_lt hjk)) hjc
          (SSet.stdSimplex.δ (n := m + 1) k ≫ σ),
        sigmaVert_face k hk σ, hσ]
  -- `RCoh` identifies each restriction with `Dprev` applied to the appropriate codimension-two
  -- face of `σ`.
  have e1 := hcoh b' (SSet.stdSimplex.δ (n := m + 1) j ≫ σ) hσj
    (k.pred (Fin.ne_zero_of_lt hjk)) hk0 hσjk
  have e2 := hcoh b' (SSet.stdSimplex.δ (n := m + 1) k ≫ σ) hσk
    (j.castPred (Fin.ne_last_of_lt hjk)) hjc hσkj
  rw [e1, e2]
  congr 1
  -- The two codimension-two faces agree by the simplicial identity.
  rw [← Category.assoc, delta_pred_castPred j k hjk, Category.assoc]

end Work.SSS
