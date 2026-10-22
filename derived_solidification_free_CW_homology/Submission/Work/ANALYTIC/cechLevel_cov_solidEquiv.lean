import Mathlib
import Submission.Work.ANALYTIC.HICond
import Submission.Work.ANALYTIC.HISetup
import Submission.Work.ANALYTIC.isIso_coprodPullbackMap
import Submission.Work.ANALYTIC.cech_descent_light
import Submission.Work.ANALYTIC.widePullbackCoproductDesc_isIso
import Submission.Work.ANALYTIC.widePullbackTensorI_isIso
import Submission.Work.ANALYTIC.isIso_sigmaWhiskerRight
import Submission.Work.ANALYTIC.prodProj_lc_solidEquiv
import Submission.Work.ANALYTIC.covPiece_isLightProfinite
import Submission.Work.ANALYTIC.solidEquiv_single_free_sigma
import Submission.Work.TOOLKIT.Main

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

attribute [local instance] lightCondSetHasCoproduct

set_option maxHeartbeats 1000000

noncomputable section

/-!
# The levelwise step of AN6

For the cover `covMap Y : cov Y ⟶ Y.toLightCondSet` of
`Submission/Work/ANALYTIC/HISetup.lean` (a coproduct of light profinite sets, indexed by
`CovIdx Y`) we show that the induced map of `p`-th Čech levels of the cover with the interval
adjoined to the `p`-th Čech level of the cover itself is a solid-equivalence.

The proof decomposes the `n`-fold fibre power of the cover into the coproduct, over tuples
`x : Fin n → CovIdx Y`, of the fibre powers of the individual pieces — light profinite sets, since
`Y` is Hausdorff.  The comparison map is then the coproduct of the projections
`ℤ[P ⊗ [0,1]] ⟶ ℤ[P]`, a solid-equivalence by AN5 (`Work.ANALYTIC.profinite_HI`), and
`ToolkitProp.sigma` concludes.
-/

/-- The light condensed set of a light profinite set. -/
abbrev lcs (S : LightProfinite.{0}) : LightCondSet.{0} := lightProfiniteToLightCondSet.obj S

/-- The `y`-th piece of the cover `cov Y`. -/
noncomputable abbrev czPiece (Y : TopCat.{0}) (y : CovIdx Y) : LightCondSet.{0} := lcs (skel y.1)

/-- The wide-pullback piece of the `n`-fold fibre power of the cover, indexed by a tuple of
indices `x`. -/
noncomputable abbrev czQ (Y : TopCat.{0}) (n : ℕ) (x : Fin n → CovIdx Y) : LightCondSet.{0} :=
  Limits.widePullback Y.toLightCondSet (fun i : Fin n => czPiece Y (x i))
    (fun i : Fin n => covComp Y (x i))

/-- The same, with the interval adjoined. -/
noncomputable abbrev czQI (Y : TopCat.{0}) (n : ℕ) (x : Fin n → CovIdx Y) : LightCondSet.{0} :=
  Limits.widePullback (Y.toLightCondSet ⊗ Icond) (fun i : Fin n => czPiece Y (x i) ⊗ Icond)
    (fun i : Fin n => covComp Y (x i) ▷ Icond)

/-- The `n`-th Čech level of the cover. -/
noncomputable abbrev czW (Y : TopCat.{0}) (n : ℕ) : LightCondSet.{0} :=
  Limits.widePullback Y.toLightCondSet (fun _ : Fin n => cov Y) (fun _ : Fin n => covMap Y)

/-- The `n`-th Čech level of the cover with the interval adjoined. -/
noncomputable abbrev czWI (Y : TopCat.{0}) (n : ℕ) : LightCondSet.{0} :=
  Limits.widePullback (Y.toLightCondSet ⊗ Icond) (fun _ : Fin n => cov Y ⊗ Icond)
    (fun _ : Fin n => covMapI Y)

/-- The projection `X ⊗ Icond ⟶ X` is natural. -/
lemma prodProj_naturality {X Y : LightCondSet.{0}} (f : X ⟶ Y) :
    (f ▷ Icond) ≫ prodProj Y = prodProj X ≫ f := by
  rw [prodProj, prodProj, ← Category.assoc, ← MonoidalCategory.whisker_exchange f
    (SemiCartesianMonoidalCategory.toUnit Icond), Category.assoc]
  erw [MonoidalCategory.rightUnitor_naturality]
  rw [Category.assoc]

/-- The canonical map `czQ ⊗ Icond ⟶ czQI`. -/
noncomputable def czEta (Y : TopCat.{0}) (n : ℕ) (x : Fin n → CovIdx Y) :
    czQ Y n x ⊗ Icond ⟶ czQI Y n x :=
  Limits.WidePullback.lift (Limits.WidePullback.base (fun i => covComp Y (x i)) ▷ Icond)
    (fun i => Limits.WidePullback.π (fun i => covComp Y (x i)) i ▷ Icond)
    (by intro j; rw [← MonoidalCategory.comp_whiskerRight, Limits.WidePullback.π_arrow])

/-- The piecewise comparison map `czQI ⟶ czQ`. -/
noncomputable def czG (Y : TopCat.{0}) (n : ℕ) (x : Fin n → CovIdx Y) : czQI Y n x ⟶ czQ Y n x :=
  Limits.WidePullback.lift
    (Limits.WidePullback.base (fun i => covComp Y (x i) ▷ Icond) ≫ prTopI Y)
    (fun i => Limits.WidePullback.π (fun i => covComp Y (x i) ▷ Icond) i ≫ prodProj (czPiece Y (x i)))
    (by
      intro i
      rw [Category.assoc, ← prodProj_naturality (covComp Y (x i)), ← Category.assoc,
        Limits.WidePullback.π_arrow])

section Piecewise

variable {Y : TopCat.{0}} {n : ℕ} {x : Fin n → CovIdx Y}

lemma czEta_inv_pi [IsIso (czEta Y n x)] (i : Fin n) :
    inv (czEta Y n x) ≫ (Limits.WidePullback.π (fun i => covComp Y (x i)) i ▷ Icond) =
      Limits.WidePullback.π (fun i => covComp Y (x i) ▷ Icond) i := by
  refine (IsIso.inv_comp_eq (czEta Y n x)).mpr ?_
  rw [czEta, Limits.WidePullback.lift_π]

lemma czEta_inv_base [IsIso (czEta Y n x)] :
    inv (czEta Y n x) ≫ (Limits.WidePullback.base (fun i => covComp Y (x i)) ▷ Icond) =
      Limits.WidePullback.base (fun i => covComp Y (x i) ▷ Icond) := by
  refine (IsIso.inv_comp_eq (czEta Y n x)).mpr ?_
  rw [czEta, Limits.WidePullback.lift_base]

/-- The piecewise comparison is, up to the isomorphism `czEta`, the projection of the fibre
power with the interval. -/
lemma czG_eq [IsIso (czEta Y n x)] :
    czG Y n x = inv (czEta Y n x) ≫ prodProj (czQ Y n x) := by
  refine Limits.WidePullback.hom_ext (fun i : Fin n => covComp Y (x i)) _ _ (fun i => ?_) ?_
  · calc czG Y n x ≫ Limits.WidePullback.π (fun i => covComp Y (x i)) i
        = Limits.WidePullback.π (fun i => covComp Y (x i) ▷ Icond) i ≫ prodProj (czPiece Y (x i)) := by
          rw [czG, Limits.WidePullback.lift_π]
      _ = (inv (czEta Y n x) ≫ (Limits.WidePullback.π (fun i => covComp Y (x i)) i ▷ Icond)) ≫
            prodProj (czPiece Y (x i)) := by rw [← czEta_inv_pi]
      _ = inv (czEta Y n x) ≫ ((Limits.WidePullback.π (fun i => covComp Y (x i)) i ▷ Icond) ≫
            prodProj (czPiece Y (x i))) := by rw [Category.assoc]
      _ = inv (czEta Y n x) ≫ (prodProj (czQ Y n x) ≫
            Limits.WidePullback.π (fun i => covComp Y (x i)) i) := by
          rw [prodProj_naturality]
      _ = (inv (czEta Y n x) ≫ prodProj (czQ Y n x)) ≫
            Limits.WidePullback.π (fun i => covComp Y (x i)) i := by rw [← Category.assoc]
  · calc czG Y n x ≫ Limits.WidePullback.base (fun i => covComp Y (x i))
        = Limits.WidePullback.base (fun i => covComp Y (x i) ▷ Icond) ≫ prTopI Y := by
          rw [czG, Limits.WidePullback.lift_base]
      _ = (inv (czEta Y n x) ≫ (Limits.WidePullback.base (fun i => covComp Y (x i)) ▷ Icond)) ≫
            prTopI Y := by rw [← czEta_inv_base]
      _ = inv (czEta Y n x) ≫ ((Limits.WidePullback.base (fun i => covComp Y (x i)) ▷ Icond) ≫
            prTopI Y) := by rw [Category.assoc]
      _ = inv (czEta Y n x) ≫ (prodProj (czQ Y n x) ≫
            Limits.WidePullback.base (fun i => covComp Y (x i))) := by rw [prodProj_naturality]
      _ = (inv (czEta Y n x) ≫ prodProj (czQ Y n x)) ≫
            Limits.WidePullback.base (fun i => covComp Y (x i)) := by rw [← Category.assoc]

end Piecewise

/-- The raw Čech level with the interval adjoined, indexed by the *coproduct* of the pieces
`P_y ⊗ Icond` (before transporting along `czEtaCov`). -/
noncomputable abbrev czWIraw (Y : TopCat.{0}) (n : ℕ) : LightCondSet.{0} :=
  Limits.widePullback (Y.toLightCondSet ⊗ Icond)
    (fun _ : Fin n => ∐ fun y : CovIdx Y => czPiece Y y ⊗ Icond)
    (fun _ : Fin n => Sigma.desc (fun y => covComp Y y ▷ Icond))

/-- The canonical isomorphism `∐_y (P_y ⊗ Icond) ⟶ (∐_y P_y) ⊗ Icond`. -/
noncomputable def czEtaCov (Y : TopCat.{0}) :
    (∐ fun y : CovIdx Y => czPiece Y y ⊗ Icond) ⟶ (∐ fun y : CovIdx Y => czPiece Y y) ⊗ Icond :=
  Sigma.desc (fun y => Sigma.ι (fun y : CovIdx Y => czPiece Y y) y ▷ Icond)

lemma czEtaCov_comp (Y : TopCat.{0}) :
    czEtaCov Y ≫ covMapI Y = Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond) := by
  refine Sigma.hom_ext _ _ (fun y => ?_)
  rw [← Category.assoc, czEtaCov, Sigma.ι_comp_desc]
  show (Sigma.ι (fun y : CovIdx Y => czPiece Y y) y ▷ Icond) ≫
      ((Sigma.desc (fun y : CovIdx Y => covComp Y y)) ▷ Icond) =
    Sigma.ι (fun y : CovIdx Y => czPiece Y y ⊗ Icond) y ≫
      Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)
  rw [← MonoidalCategory.comp_whiskerRight, Sigma.ι_comp_desc, Sigma.ι_comp_desc]

lemma czEtaCov_inv_comp (Y : TopCat.{0}) [IsIso (czEtaCov Y)] :
    inv (czEtaCov Y) ≫ Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond) = covMapI Y := by
  rw [IsIso.inv_comp_eq, czEtaCov_comp]

/-- Transport along `czEtaCov` on the Čech level. -/
noncomputable def czTransport (Y : TopCat.{0}) (n : ℕ) [IsIso (czEtaCov Y)] :
    czWIraw Y n ⟶ czWI Y n :=
  Limits.WidePullback.lift
    (Limits.WidePullback.base (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)))
    (fun i => Limits.WidePullback.π
      (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) i ≫ czEtaCov Y)
    (by intro i; rw [Category.assoc, czEtaCov_comp, Limits.WidePullback.π_arrow])

/-- Its inverse. -/
noncomputable def czTransportInv (Y : TopCat.{0}) (n : ℕ) [IsIso (czEtaCov Y)] :
    czWI Y n ⟶ czWIraw Y n :=
  Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin n => covMapI Y))
    (fun i => Limits.WidePullback.π (fun _ : Fin n => covMapI Y) i ≫ inv (czEtaCov Y))
    (by intro i; rw [Category.assoc, czEtaCov_inv_comp, Limits.WidePullback.π_arrow])

section Transport

variable {Y : TopCat.{0}} {n : ℕ} [IsIso (czEtaCov Y)]

lemma czTransport_comp_inv : czTransport Y n ≫ czTransportInv Y n = 𝟙 (czWIraw Y n) := by
  refine Limits.WidePullback.hom_ext
    (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) _ _ (fun i => ?_) ?_
  · slice_lhs 2 3 => rw [czTransportInv, Limits.WidePullback.lift_π]
    slice_lhs 1 2 => rw [czTransport, Limits.WidePullback.lift_π]
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · slice_lhs 2 3 => rw [czTransportInv, Limits.WidePullback.lift_base]
    slice_lhs 1 2 => rw [czTransport, Limits.WidePullback.lift_base]
    rw [Category.id_comp]

lemma czTransport_inv_comp : czTransportInv Y n ≫ czTransport Y n = 𝟙 (czWI Y n) := by
  refine Limits.WidePullback.hom_ext (fun _ : Fin n => covMapI Y) _ _ (fun i => ?_) ?_
  · slice_lhs 2 3 => rw [czTransport, Limits.WidePullback.lift_π]
    slice_lhs 1 2 => rw [czTransportInv, Limits.WidePullback.lift_π]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
  · slice_lhs 2 3 => rw [czTransport, Limits.WidePullback.lift_base]
    slice_lhs 1 2 => rw [czTransportInv, Limits.WidePullback.lift_base]
    rw [Category.id_comp]

lemma isIso_czTransport : IsIso (czTransport Y n) := by
  refine ⟨czTransportInv Y n, ?_, ?_⟩
  · exact czTransport_comp_inv
  · exact czTransport_inv_comp

end Transport

/-- The comparison map of Čech levels: the component at `n` of `Arrow.mapCechNerve` for the
morphism of arrows `covMapI Y ⟶ covMap Y`. -/
noncomputable def czLevelMap (Y : TopCat.{0}) (n : ℕ) : czWI Y n ⟶ czW Y n :=
  Limits.WidePullback.lift (Limits.WidePullback.base (fun _ : Fin n => covMapI Y) ≫ prTopI Y)
    (fun i => Limits.WidePullback.π (fun _ : Fin n => covMapI Y) i ≫ covProj Y)
    (by intro j; rw [Category.assoc, cov_square, ← Category.assoc, Limits.WidePullback.π_arrow])

/-- The decomposition map `∐_x czQ x ⟶ czW`. -/
noncomputable def czPhi (Y : TopCat.{0}) (n : ℕ) :
    (∐ fun x : Fin n → CovIdx Y => czQ Y n x) ⟶ czW Y n :=
  Sigma.desc (fun x => Limits.WidePullback.lift
    (Limits.WidePullback.base (fun i : Fin n => covComp Y (x i)))
    (fun i => Limits.WidePullback.π (fun i : Fin n => covComp Y (x i)) i ≫
      Sigma.ι (fun y : CovIdx Y => czPiece Y y) (x i))
    (by simp))

/-- The decomposition map for the interval side (into `czWIraw`). -/
noncomputable def czPhiRaw (Y : TopCat.{0}) (n : ℕ) :
    (∐ fun x : Fin n → CovIdx Y => czQI Y n x) ⟶ czWIraw Y n :=
  Sigma.desc (fun x => Limits.WidePullback.lift
    (Limits.WidePullback.base (fun i : Fin n => covComp Y (x i) ▷ Icond))
    (fun i => Limits.WidePullback.π (fun i : Fin n => covComp Y (x i) ▷ Icond) i ≫
      Sigma.ι (fun y : CovIdx Y => czPiece Y y ⊗ Icond) (x i))
    (by simp))

/-- The decomposition map for the interval side, into `czWI`. -/
noncomputable def czPhiI (Y : TopCat.{0}) (n : ℕ) [IsIso (czEtaCov Y)] :
    (∐ fun x : Fin n → CovIdx Y => czQI Y n x) ⟶ czWI Y n :=
  czPhiRaw Y n ≫ czTransport Y n

section Components

variable {Y : TopCat.{0}} {n : ℕ}

@[reassoc]
lemma czPhi_π (x : Fin n → CovIdx Y) (i : Fin n) :
    Sigma.ι (fun x : Fin n → CovIdx Y => czQ Y n x) x ≫ czPhi Y n ≫
        Limits.WidePullback.π (fun _ : Fin n => covMap Y) i =
      Limits.WidePullback.π (fun i : Fin n => covComp Y (x i)) i ≫
        Sigma.ι (fun y : CovIdx Y => czPiece Y y) (x i) := by
  rw [← Category.assoc, czPhi, Sigma.ι_comp_desc, Limits.WidePullback.lift_π]

@[reassoc]
lemma czPhi_base (x : Fin n → CovIdx Y) :
    Sigma.ι (fun x : Fin n → CovIdx Y => czQ Y n x) x ≫ czPhi Y n ≫
        Limits.WidePullback.base (fun _ : Fin n => covMap Y) =
      Limits.WidePullback.base (fun i : Fin n => covComp Y (x i)) := by
  rw [← Category.assoc, czPhi, Sigma.ι_comp_desc, Limits.WidePullback.lift_base]

@[reassoc]
lemma czPhiRaw_π (x : Fin n → CovIdx Y) (i : Fin n) :
    Sigma.ι (fun x : Fin n → CovIdx Y => czQI Y n x) x ≫ czPhiRaw Y n ≫
        Limits.WidePullback.π
          (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) i =
      Limits.WidePullback.π (fun i : Fin n => covComp Y (x i) ▷ Icond) i ≫
        Sigma.ι (fun y : CovIdx Y => czPiece Y y ⊗ Icond) (x i) := by
  rw [← Category.assoc, czPhiRaw, Sigma.ι_comp_desc, Limits.WidePullback.lift_π]

@[reassoc]
lemma czPhiRaw_base (x : Fin n → CovIdx Y) :
    Sigma.ι (fun x : Fin n → CovIdx Y => czQI Y n x) x ≫ czPhiRaw Y n ≫
        Limits.WidePullback.base
          (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) =
      Limits.WidePullback.base (fun i : Fin n => covComp Y (x i) ▷ Icond) := by
  rw [← Category.assoc, czPhiRaw, Sigma.ι_comp_desc, Limits.WidePullback.lift_base]

@[reassoc]
lemma czTransport_π [IsIso (czEtaCov Y)] (i : Fin n) :
    czTransport Y n ≫ Limits.WidePullback.π (fun _ : Fin n => covMapI Y) i =
      Limits.WidePullback.π
          (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) i ≫ czEtaCov Y := by
  rw [czTransport, Limits.WidePullback.lift_π]

@[reassoc]
lemma czTransport_base [IsIso (czEtaCov Y)] :
    czTransport Y n ≫ Limits.WidePullback.base (fun _ : Fin n => covMapI Y) =
      Limits.WidePullback.base
        (fun _ : Fin n => Sigma.desc (fun y : CovIdx Y => covComp Y y ▷ Icond)) := by
  rw [czTransport, Limits.WidePullback.lift_base]

@[reassoc]
lemma czLevelMap_π (i : Fin n) :
    czLevelMap Y n ≫ Limits.WidePullback.π (fun _ : Fin n => covMap Y) i =
      Limits.WidePullback.π (fun _ : Fin n => covMapI Y) i ≫ covProj Y := by
  rw [czLevelMap, Limits.WidePullback.lift_π]

@[reassoc]
lemma czLevelMap_base :
    czLevelMap Y n ≫ Limits.WidePullback.base (fun _ : Fin n => covMap Y) =
      Limits.WidePullback.base (fun _ : Fin n => covMapI Y) ≫ prTopI Y := by
  rw [czLevelMap, Limits.WidePullback.lift_base]

@[reassoc]
lemma czEtaCov_comp_covProj (y : CovIdx Y) :
    Sigma.ι (fun y : CovIdx Y => czPiece Y y ⊗ Icond) y ≫ czEtaCov Y ≫ covProj Y =
      prodProj (czPiece Y y) ≫ Sigma.ι (fun y : CovIdx Y => czPiece Y y) y := by
  rw [czEtaCov, ← Category.assoc, Sigma.ι_comp_desc, prodProj_naturality]

@[reassoc]
lemma czG_π (x : Fin n → CovIdx Y) (i : Fin n) :
    czG Y n x ≫ Limits.WidePullback.π (fun i : Fin n => covComp Y (x i)) i =
      Limits.WidePullback.π (fun i : Fin n => covComp Y (x i) ▷ Icond) i ≫
        prodProj (czPiece Y (x i)) := by
  rw [czG, Limits.WidePullback.lift_π]

@[reassoc]
lemma czG_base (x : Fin n → CovIdx Y) :
    czG Y n x ≫ Limits.WidePullback.base (fun i : Fin n => covComp Y (x i)) =
      Limits.WidePullback.base (fun i : Fin n => covComp Y (x i) ▷ Icond) ≫ prTopI Y := by
  rw [czG, Limits.WidePullback.lift_base]

/-- `Sigma.ι` commutes with `Sigma.map`, in the form used for composition. -/
lemma cz_sigma_ι_map {ι : Type} {X Y : ι → LightCondSet.{0}} [HasCoproduct X] [HasCoproduct Y]
    (g : ∀ x, X x ⟶ Y x) (x : ι) {Z : LightCondSet.{0}} (h : (∐ Y) ⟶ Z) :
    Sigma.ι X x ≫ Limits.Sigma.map g ≫ h = g x ≫ (Sigma.ι Y x ≫ h) := by
  rw [← Category.assoc, Sigma.ι_map, Category.assoc]

/-- Transport a solid-equivalence along the conjugation of `single ∘ free` by isomorphisms. -/
lemma solidEquiv_single_free_conj {A B A' B' : LightCondSet.{0}} (f : A ⟶ B) (a : A' ⟶ A)
    (b : B ⟶ B') [IsIso a] [IsIso b] {f' : A' ⟶ B'} (h : f' = a ≫ f ≫ b)
    (hf : Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map ((LightCondensed.free (R := ℤ)).map f))) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map ((LightCondensed.free (R := ℤ)).map f')) := by
  rw [h, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  exact (Work.TOOLKIT.toolkit_prop).comp _ _
    ((Work.TOOLKIT.toolkit_prop).of_iso _ (by infer_instance))
    ((Work.TOOLKIT.toolkit_prop).comp _ _ hf
      ((Work.TOOLKIT.toolkit_prop).of_iso _ (by infer_instance)))

end Components

/-- **The comparison of Čech levels is the coproduct of the piecewise comparisons.** -/
lemma czPhiI_comp_levelMap (Y : TopCat.{0}) (n : ℕ) [IsIso (czEtaCov Y)] :
    czPhiI Y n ≫ czLevelMap Y n = Limits.Sigma.map (czG Y n) ≫ czPhi Y n := by
  refine Sigma.hom_ext _ _ (fun x => ?_)
  simp only [czPhiI, Category.assoc]
  refine Limits.WidePullback.hom_ext (fun _ : Fin n => covMap Y) _ _ (fun i => ?_) ?_
  · simp only [Category.assoc]
    rw [czLevelMap_π, czTransport_π_assoc, czPhiRaw_π_assoc,
      czEtaCov_comp_covProj, cz_sigma_ι_map, czPhi_π, czG_π_assoc, prodProj, Category.assoc]
  · simp only [Category.assoc]
    rw [czLevelMap_base, czTransport_base_assoc, czPhiRaw_base_assoc, cz_sigma_ι_map, czPhi_base,
      czG_base]


/-- **The levelwise step of AN6.**  For the cover `covMap Y : cov Y ⟶ Y` of
`Submission/Work/ANALYTIC/HISetup.lean` and its product with the interval `Icond`, the induced
map of `p`-th Čech levels (from the `Y × [0,1]`-side to the `Y`-side) is a solid-equivalence.

Each Čech level is the `(p+1)`-fold fibre power; over the Hausdorff space `Y` it is a disjoint
union (coproduct in `LightCondSet`) of light profinite sets `P`, and the comparison map is then
the coproduct of the projections `ℤ[P × [0,1]] ⟶ ℤ[P]`, each of which is a solid-equivalence by
AN5 (`Work.ANALYTIC.profinite_HI`); `ToolkitProp.sigma` concludes. -/
theorem cechLevel_cov_solidEquiv (Y : TopCat.{0}) [T2Space Y] (p : ℕ) :
    Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((free ℤ).map
          ((Arrow.mapCechNerve
            (Arrow.homMk (f := Arrow.mk (Work.ANALYTIC.covMapI Y))
              (g := Arrow.mk (Work.ANALYTIC.covMap Y))
              (Work.ANALYTIC.covProj Y) (Work.ANALYTIC.prTopI Y)
              (Work.ANALYTIC.cov_square Y))).app
            (Opposite.op (SimplexCategory.mk p))))) := by
  haveI hEtaCov : IsIso (czEtaCov Y) :=
    isIso_sigmaWhiskerRight (fun y : CovIdx Y => czPiece Y y)
  haveI hTransport : IsIso (czTransport Y (p + 1)) := isIso_czTransport
  haveI hPhi : IsIso (czPhi Y (p + 1)) :=
    widePullbackCoproductDesc_isIso (fun y : CovIdx Y => czPiece Y y) Y.toLightCondSet
      (fun y => covComp Y y) (p + 1)
  haveI hPhiRaw : IsIso (czPhiRaw Y (p + 1)) :=
    widePullbackCoproductDesc_isIso (fun y : CovIdx Y => czPiece Y y ⊗ Icond)
      (Y.toLightCondSet ⊗ Icond) (fun y => covComp Y y ▷ Icond) (p + 1)
  haveI hPhiI : IsIso (czPhiI Y (p + 1)) := by
    rw [czPhiI]
    infer_instance
  have hflevel : czLevelMap Y (p + 1) =
      inv (czPhiI Y (p + 1)) ≫ Limits.Sigma.map (czG Y (p + 1)) ≫ czPhi Y (p + 1) :=
    (IsIso.eq_inv_comp (czPhiI Y (p + 1))).mpr (czPhiI_comp_levelMap Y (p + 1))
  have hpiece : ∀ x : Fin (p + 1) → CovIdx Y, Submission.Blueprint.SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((LightCondensed.free (R := ℤ)).map (czG Y (p + 1) x))) := by
    intro x
    obtain ⟨S, ⟨eQ⟩⟩ := covPiece_isLightProfinite Y p x
    haveI hEta : IsIso (czEta Y (p + 1) x) :=
      widePullbackTensorI_isIso (fun i : Fin (p + 1) => covComp Y (x i))
    have hconj : prodProj (czQ Y (p + 1) x) = (eQ.hom ▷ Icond) ≫ prodProj (lcs S) ≫ eQ.inv := by
      rw [← Category.assoc, prodProj_naturality eQ.hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h2 : Submission.Blueprint.SolidEquiv
        ((DerivedCategory.singleFunctor LightCondAb 0).map
          ((LightCondensed.free (R := ℤ)).map (prodProj (czQ Y (p + 1) x)))) :=
      solidEquiv_single_free_conj (f := prodProj (lcs S)) (a := eQ.hom ▷ Icond) (b := eQ.inv)
        hconj (prodProj_lc_solidEquiv S)
    exact solidEquiv_single_free_conj (f := prodProj (czQ Y (p + 1) x))
      (a := inv (czEta Y (p + 1) x)) (b := 𝟙 _) (by rw [czG_eq, Category.comp_id]) h2
  rw [show (Arrow.mapCechNerve
      (Arrow.homMk (f := Arrow.mk (Work.ANALYTIC.covMapI Y))
        (g := Arrow.mk (Work.ANALYTIC.covMap Y)) (Work.ANALYTIC.covProj Y)
        (Work.ANALYTIC.prTopI Y) (Work.ANALYTIC.cov_square Y))).app
        (Opposite.op (SimplexCategory.mk p)) = czLevelMap Y (p + 1) from rfl]
  rw [hflevel, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  exact (Work.TOOLKIT.toolkit_prop).comp _ _
    ((Work.TOOLKIT.toolkit_prop).of_iso _ (by infer_instance))
    ((Work.TOOLKIT.toolkit_prop).comp _ _
      (solidEquiv_single_free_sigma (fun x : Fin (p + 1) → CovIdx Y => czQI Y (p + 1) x)
        (fun x : Fin (p + 1) → CovIdx Y => czQ Y (p + 1) x) (czG Y (p + 1)) hpiece)
      ((Work.TOOLKIT.toolkit_prop).of_iso _ (by infer_instance)))

end

end Work.ANALYTIC
