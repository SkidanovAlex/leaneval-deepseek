import Mathlib
import Submission.Work.WilC4aU.ClusterDefs

namespace Work.WilC4aU

open Work.WilC0

/-- Hyperplanes `{z | z i ≠ 0}` are existentially definable: they are the `hR`-complement of the
zero set of the variable `X i`. -/
theorem rexExistI_ne_zero {k : ℕ} (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)),
    WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) (i : BB7 k) :
    RExpExistI {z : BB7 k → ℝ | z i ≠ 0} := by
  refine (RExpExistI.compl hR (RExpExistI.rexPoly
    (MvPolynomial.X (Sum.inl i) : MvPolynomial (BB7 k ⊕ BB7 k) ℝ))).of_eq ?_
  ext z
  simp [Work.WilC0.RExPoly]

theorem Dset_rexExist {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : WilkiesDesign.RExpExist Y)
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) :
    Work.WilC0.RExpExistI (Work.WilC4aU.Dset k Y) := by
  have hYI : RExpExistI Y := (rexExistI_iff_rexExist Y).mpr hY
  -- the seven pieces of the body
  have h1 : RExpExistI {z : BB7 k → ℝ | z ∘ selY k ∈ Y} :=
    RExpExistI.pullback (selY k) hYI
  have h2 : RExpExistI {z : BB7 k → ℝ | z ∘ selU k ∈ Y} :=
    RExpExistI.pullback (selU k) hYI
  have h3 : RExpExistI {z : BB7 k → ℝ | rexpEval z (PZpoly k) = 0} :=
    RExpExistI.rexPoly (PZpoly k)
  have h4 : RExpExistI {z : BB7 k → ℝ | rexpEval z (PUpoly k) = 0} :=
    RExpExistI.rexPoly (PUpoly k)
  have h5 : RExpExistI {z : BB7 k → ℝ | rexpEval z (PWpoly k) = 0} :=
    RExpExistI.rexPoly (PWpoly k)
  have h6 : RExpExistI {z : BB7 k → ℝ | z (iY k) ≠ 0} := rexExistI_ne_zero hR (iY k)
  have h7 : RExpExistI {z : BB7 k → ℝ | z (iW k) ≠ 0} := rexExistI_ne_zero hR (iW k)
  have hBody : RExpExistI (Body k Y) := by
    unfold Body
    exact ((((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7)
  -- project away the six slack coordinates `w`, `z`, `y'`, `y`, `u`, `x`
  have hProj : RExpExistI (Proj6 k (Body k Y)) :=
    RExpExistI.projLast (RExpExistI.projLast (RExpExistI.projLast (RExpExistI.projLast
      (RExpExistI.projLast (RExpExistI.projLast hBody)))))
  exact hProj.of_eq (Set.ext fun z => proj6_body_mem Y z)

end Work.WilC4aU
