/-
AREA DERFORMAL — B1 and B2 without auxiliary hypotheses.

`Cofibrant.lean` proves B1(b) and B2 under an explicit hypothesis `hproj` (the K-projectivity of
`solC` on solid-cofibrant complexes), which is proved unconditionally in `B1KProjective.lean`.
This file records the resulting unconditional statements, which are the versions meant to be
used by callers.  It also provides `ResData.ofResolution`, building the resolution data of the
area from the resolution part of `Submission.Blueprint.ResolutionProp` alone.
-/
import Submission.Work.DERFORMAL.Cofibrant
import Submission.Work.DERFORMAL.B1KProjective
import Submission.Work.DERFORMAL.Lift

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-- The K-projectivity hypothesis used in `Cofibrant.lean`, proved in `B1KProjective`. -/
theorem kProjective_hyp : ∀ K : Cpx, Cofibrant K → CochainComplex.IsKProjective (solC.obj K) :=
  fun K hK => B1KProjective K hK

/-- **B1(a)**, restated: degreewise solidification of a solid-cofibrant complex is K-projective
in the category of solid objects. -/
theorem isKProjective_solC (K : Cpx) (hK : Cofibrant K) :
    CochainComplex.IsKProjective (solC.obj K) := B1KProjective K hK

/-- **B1(b)**, unconditional form: for `K` solid-cofibrant and `N` a complex of solid objects,
`Hom_D(Q(solC K), Q N) ≃ Hom_D(Q K, Q(incC N))`. -/
noncomputable def homDEquiv' (K : Cpx) (hK : Cofibrant K) (N : SCpx) :
    (Qh.obj (hs (solC.obj K)) ⟶ Qh.obj (hs N)) ≃
      (Qh.obj (hq K) ⟶ Qh.obj (hq (incC.obj N))) :=
  homDEquiv kProjective_hyp K hK N

/-- Naturality of `homDEquiv'` in the first variable. -/
lemma homDEquiv'_naturality {K K' : Cpx} (hK : Cofibrant K) (hK' : Cofibrant K') (f : K ⟶ K')
    (N : SCpx) (g : Qh.obj (hs (solC.obj K')) ⟶ Qh.obj (hs N)) :
    homDEquiv' K hK N (Qh.map (qs.map (solC.map f)) ≫ g) =
      Qh.map (qc.map f) ≫ homDEquiv' K' hK' N g :=
  homDEquiv_naturality kProjective_hyp hK hK' f N g

/-- **B2**, unconditional form: quasi-isomorphisms between solid-cofibrant complexes are sent to
quasi-isomorphisms by degreewise solidification. -/
theorem solC_quasiIso {K K' : Cpx} (hK : Cofibrant K) (hK' : Cofibrant K') {f : K ⟶ K'}
    (hf : QuasiIso f) : QuasiIso (solC.map f) :=
  B2 kProjective_hyp hK hK' hf

/-- The resolution data of the area, built from a functorial solid-cofibrant resolution (the
first conjunct of `Submission.Blueprint.ResolutionProp`). -/
noncomputable def ResData.ofResolution (ρ : Cpx ⥤ Cpx) (ε : ρ ⟶ 𝟭 Cpx)
    (hcof : ∀ K, Cofibrant (ρ.obj K)) (hqiso : ∀ K, QuasiIso (ε.app K)) : ResData :=
  ⟨ρ, ε, hcof, hqiso, kProjective_hyp⟩

end Work.DERFORMAL
