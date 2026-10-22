import Mathlib
import Submission.Work.ANALYTIC.isIso_coprodPullbackMap
import Submission.Work.ANALYTIC.isIso_sigmaDesc_pullbackMap
import Submission.Work.ANALYTIC.isIso_widePullback_base_of_isEmpty
import Submission.Work.ANALYTIC.isColimit_of_equiv_index
import Submission.Work.ANALYTIC.isColimit_cofan_subsingleton
import Submission.Work.ANALYTIC.isPullback_widePullback_succ

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-! ## Small coproducts in `LightCondSet` -/

/-- Small coproducts in `LightCondSet`, built as sheafifications of presheaf coproducts.  (Instance
search for this does not terminate in reasonable time, so it is recorded as a definition and
installed locally where needed.) -/
noncomputable def lcsCoprod {ι : Type} (F : ι → LightCondSet.{0}) : HasCoproduct F :=
  HasColimit.mk
    ⟨Sheaf.sheafifyCocone (colimit.cocone (Discrete.functor F ⋙ sheafToPresheaf _ (Type 0))),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩

section Setting

variable {ι : Type}

/-! ## The fibre power of the coproduct -/

/-- The coproduct `∐ F`. -/
abbrev coprodObj (F : ι → LightCondSet.{0}) [HasCoproduct F] : LightCondSet.{0} := ∐ F

/-- The structure map `∐ F ⟶ Z` of the coproduct. -/
abbrev coprodMap (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] : coprodObj F ⟶ Z := Sigma.desc φ

/-- The constant family `Fin n → LightCondSet` at `∐ F`. -/
abbrev fibFam (F : ι → LightCondSet.{0}) [HasCoproduct F] (n : ℕ) : Fin n → LightCondSet.{0} :=
  fun _ => coprodObj F

/-- The constant family of structure maps `∐ F ⟶ Z`. -/
abbrev fibArr (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) : ∀ _ : Fin n, coprodObj F ⟶ Z := fun _ => coprodMap F Z φ

/-- The `n`-fold fibre power of `∐ F` over `Z`. -/
abbrev fibPower (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) : LightCondSet.{0} :=
  Limits.widePullback Z (fibFam F n) (fibArr F Z φ n)

/-- The base map of the fibre power. -/
abbrev fibBase (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) : fibPower F Z φ n ⟶ Z :=
  Limits.WidePullback.base (fibArr F Z φ n)

/-- The `i`-th projection of the fibre power. -/
abbrev fibπ (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) (i : Fin n) : fibPower F Z φ n ⟶ coprodObj F :=
  Limits.WidePullback.π (fibArr F Z φ n) i

/-- The recursion map `W_{n+1} ⟶ W_n` for the fibre powers of the coproduct. -/
abbrev fibStep (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) : fibPower F Z φ (n + 1) ⟶ fibPower F Z φ n :=
  Limits.WidePullback.lift (fibBase F Z φ (n + 1)) (fun i : Fin n => fibπ F Z φ (n + 1) i.succ)
    (by simp)

/-! ## The fibre powers of the pieces -/

/-- The family of pieces. -/
abbrev pieceFam (F : ι → LightCondSet.{0}) (n : ℕ) (x : Fin n → ι) : Fin n → LightCondSet.{0} :=
  fun i => F (x i)

/-- The family of structure maps of the pieces. -/
abbrev pieceArr (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin n → ι) : ∀ i : Fin n, F (x i) ⟶ Z := fun i => φ (x i)

/-- The `n`-fold fibre power of the pieces `F (x i)`. -/
abbrev pieceObj (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin n → ι) : LightCondSet.{0} :=
  Limits.widePullback Z (pieceFam F n x) (pieceArr F Z φ n x)

/-- The base map of a piece. -/
abbrev wpcPieceBase (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin n → ι) : pieceObj F Z φ n x ⟶ Z :=
  Limits.WidePullback.base (pieceArr F Z φ n x)

/-- The `i`-th projection of a piece. -/
abbrev pieceπ (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin n → ι) (i : Fin n) : pieceObj F Z φ n x ⟶ F (x i) :=
  Limits.WidePullback.π (pieceArr F Z φ n x) i

/-- The fibre power of the tail of a piece family. -/
abbrev pieceTailObj (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) : LightCondSet.{0} :=
  Limits.widePullback Z (fun i : Fin n => F (x i.succ)) (fun i : Fin n => φ (x i.succ))

/-- The `i`-th projection of the tail fibre power. -/
abbrev pieceTailπ (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) (i : Fin n) : pieceTailObj F Z φ n x ⟶ F (x i.succ) :=
  Limits.WidePullback.π (fun i : Fin n => φ (x i.succ)) i

/-- The base map of the tail fibre power. -/
abbrev pieceTailBase (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) : pieceTailObj F Z φ n x ⟶ Z :=
  Limits.WidePullback.base (fun i : Fin n => φ (x i.succ))

/-- The recursion map `Q_{n+1} x ⟶ Q_n (tail x)`. -/
abbrev pieceStep (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) : pieceObj F Z φ (n + 1) x ⟶ pieceTailObj F Z φ n x :=
  Limits.WidePullback.lift (wpcPieceBase F Z φ (n + 1) x)
    (fun i : Fin n => pieceπ F Z φ (n + 1) x i.succ) (by simp)

/-- The canonical map from the fibre power of the pieces to the fibre power of the coproduct. -/
abbrev pieceMap (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) (x : Fin n → ι) : pieceObj F Z φ n x ⟶ fibPower F Z φ n :=
  Limits.WidePullback.lift (wpcPieceBase F Z φ n x)
    (fun i : Fin n => pieceπ F Z φ n x i ≫ Sigma.ι F (x i)) (by simp)

/-- The equivalence `(Fin n → ι) × ι ≃ (Fin (n+1) → ι)`, `(y, y') ↦ Fin.cons y' y`, whose inverse
is `x ↦ (Fin.tail x, x 0)`.  It is an `abbrev` so that its application reduces on the nose. -/
abbrev consEquiv (n : ℕ) (ι : Type) : (Fin n → ι) × ι ≃ (Fin (n + 1) → ι) where
  toFun p := Fin.cons p.2 p.1
  invFun x := (Fin.tail x, x 0)
  left_inv p := by ext <;> simp [Fin.tail_cons, Fin.cons_zero]
  right_inv x := by exact Fin.cons_self_tail x

/-- The apex isomorphism `(∐_y Q_n y) ×_Z (∐ F) ⟶ W_{n+1}` given by the recursion for wide
pullbacks. -/
abbrev psi2 (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) : pullback (fibBase F Z φ n) (coprodMap F Z φ) ⟶ fibPower F Z φ (n + 1) :=
  (isPullback_widePullback_succ (X := fibFam F (n + 1)) (φ := fibArr F Z φ (n + 1))).isoPullback.inv

/-- The component isomorphism `Q_n y ×_Z F y' ≅ Q_{n+1} (cons y' y)` given by the recursion for
wide pullbacks. -/
abbrev thetaE (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ)
    (p : (Fin n → ι) × ι) : pullback (wpcPieceBase F Z φ n p.1) (φ p.2) ≅
      pieceObj F Z φ (n + 1) (consEquiv n ι p) :=
  ((isPullback_widePullback_succ (X := pieceFam F (n + 1) (consEquiv n ι p))
    (φ := pieceArr F Z φ (n + 1) (consEquiv n ι p)))).isoPullback.symm

/-! ## Projection formulas -/

lemma fibStep_base (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) :
    fibStep F Z φ n ≫ fibBase F Z φ n = fibBase F Z φ (n + 1) := by
  rw [WidePullback.lift_base]

lemma fibStep_π (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) (j : Fin n) :
    fibStep F Z φ n ≫ fibπ F Z φ n j = fibπ F Z φ (n + 1) j.succ := by
  rw [WidePullback.lift_π]

lemma pieceStep_tailBase (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) :
    pieceStep F Z φ n x ≫ pieceTailBase F Z φ n x = wpcPieceBase F Z φ (n + 1) x := by
  rw [WidePullback.lift_base]

lemma pieceStep_tailπ (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    (n : ℕ) (x : Fin (n + 1) → ι) (j : Fin n) :
    pieceStep F Z φ n x ≫ pieceTailπ F Z φ n x j = pieceπ F Z φ (n + 1) x j.succ := by
  rw [WidePullback.lift_π]

lemma pieceTailObj_consEquiv (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0})
    (φ : ∀ y, F y ⟶ Z) (n : ℕ) (p : (Fin n → ι) × ι) :
    pieceTailObj F Z φ n (consEquiv n ι p) = pieceObj F Z φ n p.1 := rfl

lemma pieceTailπ_consEquiv (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0})
    (φ : ∀ y, F y ⟶ Z) (n : ℕ) (p : (Fin n → ι) × ι) (j : Fin n) :
    pieceTailπ F Z φ n (consEquiv n ι p) j = pieceπ F Z φ n p.1 j := rfl

lemma psi2_fst (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) :
    psi2 F Z φ n ≫ fibStep F Z φ n = pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) := by
  dsimp only [psi2]
  exact IsPullback.isoPullback_inv_fst _

lemma psi2_snd (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) :
    psi2 F Z φ n ≫ fibπ F Z φ (n + 1) 0 = pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) := by
  dsimp only [psi2]
  exact IsPullback.isoPullback_inv_snd _

lemma psi2_base (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z)
    [HasCoproduct F] (n : ℕ) :
    psi2 F Z φ n ≫ fibBase F Z φ (n + 1) =
      pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) ≫ coprodMap F Z φ := by
  rw [← fibStep_base F Z φ n, ← Category.assoc, psi2_fst, pullback.condition]

lemma thetaE_fst (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ)
    (p : (Fin n → ι) × ι) :
    (thetaE F Z φ n p).hom ≫ pieceStep F Z φ n (consEquiv n ι p) =
      pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) := by
  dsimp only [thetaE]
  exact IsPullback.isoPullback_inv_fst _

lemma thetaE_snd (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ)
    (p : (Fin n → ι) × ι) :
    (thetaE F Z φ n p).hom ≫ pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 =
      pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) := by
  dsimp only [thetaE]
  exact IsPullback.isoPullback_inv_snd _

lemma thetaE_base (F : ι → LightCondSet.{0}) (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ)
    (p : (Fin n → ι) × ι) :
    (thetaE F Z φ n p).hom ≫ wpcPieceBase F Z φ (n + 1) (consEquiv n ι p) =
      pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ φ p.2 := by
  rw [show wpcPieceBase F Z φ (n + 1) (consEquiv n ι p) =
      pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 ≫ φ ((consEquiv n ι p) 0) from
    (WidePullback.π_arrow (pieceArr F Z φ (n + 1) (consEquiv n ι p)) 0).symm,
    ← Category.assoc, thetaE_snd]
  rfl

/-! ## The induction -/

/-- **Auxiliary induction.**  For every `n`, the cofan of the pieces maps is a colimit cofan. -/
theorem widePullbackCoproductDesc_aux (F : ι → LightCondSet.{0}) [HasCoproduct F]
    (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ) :
    Nonempty (IsColimit (Cofan.mk (fibPower F Z φ n) (pieceMap F Z φ n))) := by
  induction n with
  | zero =>
    haveI hb : IsIso (fibBase F Z φ 0) := isIso_widePullback_base_of_isEmpty (fibArr F Z φ 0)
    haveI : Subsingleton (Fin 0 → ι) := ⟨fun f g => funext fun x => isEmptyElim x⟩
    haveI : Nonempty (Fin 0 → ι) := ⟨fun x => isEmptyElim x⟩
    refine isColimit_cofan_subsingleton (pieceMap F Z φ 0) (fun x => ?_)
    haveI hbQ : IsIso (wpcPieceBase F Z φ 0 x) := isIso_widePullback_base_of_isEmpty (pieceArr F Z φ 0 x)
    have hq : pieceMap F Z φ 0 x = wpcPieceBase F Z φ 0 x ≫ inv (fibBase F Z φ 0) := by
      refine Limits.WidePullback.hom_ext (fibArr F Z φ 0) _ _ (fun i => isEmptyElim i) ?_
      rw [Limits.WidePullback.lift_base, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hq]
    infer_instance
  | succ n ih =>
    -- ### Step 1: the induction hypothesis, as an isomorphism `∐_y Q_n y ≅ W_n`.
    haveI hQ : HasCoproduct (pieceObj F Z φ n) := lcsCoprod _
    haveI hι : IsIso (Sigma.desc (pieceMap F Z φ n)) :=
      (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
        (c := Cofan.mk (fibPower F Z φ n) (pieceMap F Z φ n))).mp ih
    let e₁ : (∐ pieceObj F Z φ n) ≅ fibPower F Z φ n := asIso (Sigma.desc (pieceMap F Z φ n))
    have he₁ : e₁.hom = Sigma.desc (pieceMap F Z φ n) := by
      dsimp only [e₁]
      rw [asIso_hom]
    have hb₁ : e₁.hom ≫ fibBase F Z φ n = Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y) := by
      refine Sigma.hom_ext _ _ (fun y => ?_)
      rw [he₁, ← Category.assoc, Sigma.ι_comp_desc, Limits.WidePullback.lift_base, Sigma.ι_comp_desc]
    -- ### Step 2: binary distributivity `∐_p (Q_n y ×_Z F y') ≅ (∐_y Q_n y) ×_Z (∐ F)`.
    haveI hP : HasCoproduct (fun p : (Fin n → ι) × ι =>
        pullback (wpcPieceBase F Z φ n p.1) (φ p.2)) := lcsCoprod _
    let binMap : ∀ p : (Fin n → ι) × ι,
        pullback (wpcPieceBase F Z φ n p.1) (φ p.2) ⟶
          pullback (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) :=
      fun p => pullback.map (wpcPieceBase F Z φ n p.1) (φ p.2)
        (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ)
        (Sigma.ι (pieceObj F Z φ n) p.1) (Sigma.ι F p.2) (𝟙 Z) (by simp) (by simp)
    haveI hbin : IsIso (Sigma.desc binMap) :=
      isIso_sigmaDesc_pullbackMap_lightCondSet
        (X := pieceObj F Z φ n) (Y := F) (fun y => wpcPieceBase F Z φ n y) φ
    let dbin : Cofan (fun p : (Fin n → ι) × ι => pullback (wpcPieceBase F Z φ n p.1) (φ p.2)) :=
      Cofan.mk (pullback (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ)) binMap
    haveI hdbinIso : IsIso (Sigma.desc dbin.inj) := by
      show IsIso (Sigma.desc binMap)
      exact hbin
    have hdbin : IsColimit dbin := Cofan.isColimitOfIsIsoSigmaDesc dbin
    -- ### Step 3: the apex isomorphism `(∐_y Q_n y) ×_Z (∐ F) ≅ W_{n+1}`.
    let ψ₁ : pullback (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ⟶
        pullback (fibBase F Z φ n) (coprodMap F Z φ) :=
      pullback.map (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ)
        (fibBase F Z φ n) (coprodMap F Z φ) e₁.hom (𝟙 (coprodObj F)) (𝟙 Z)
        (by rw [Category.comp_id, hb₁]) (by simp)
    haveI hψ₁ : IsIso ψ₁ := inferInstance
    let ψ : dbin.pt ≅ fibPower F Z φ (n + 1) := asIso ψ₁ ≪≫ asIso (psi2 F Z φ n)
    -- ### Step 4: transport the colimit along the index equivalence `(Fin n → ι) × ι ≃ Fin (n+1) → ι`.
    refine isColimit_of_equiv_index dbin
      (Cofan.mk (fibPower F Z φ (n + 1)) (pieceMap F Z φ (n + 1)))
      (consEquiv n ι) (thetaE F Z φ n) ψ ?_ hdbin
    intro p
    -- ### Step 5: the compatibility of the canonical maps.
    change binMap p ≫ (ψ₁ ≫ psi2 F Z φ n) =
      (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p)
    have hψ₁fst : ψ₁ ≫ pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) =
        pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫ e₁.hom := by
      dsimp only [ψ₁, pullback.map]
      rw [pullback.lift_fst]
    have hψ₁snd : ψ₁ ≫ pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) =
        pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
          𝟙 (coprodObj F) := by
      dsimp only [ψ₁, pullback.map]
      rw [pullback.lift_snd]
    have hbinFst : binMap p ≫ pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
          (Sigma.desc φ) =
        pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι (pieceObj F Z φ n) p.1 := by
      dsimp only [binMap, pullback.map]
      rw [pullback.lift_fst]
    have hbinSnd : binMap p ≫ pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
          (Sigma.desc φ) =
        pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 := by
      dsimp only [binMap, pullback.map]
      rw [pullback.lift_snd]
    have hιQ : Sigma.ι (pieceObj F Z φ n) p.1 ≫ e₁.hom = pieceMap F Z φ n p.1 := by
      rw [he₁, Sigma.ι_comp_desc]
    -- the `assoc`ed forms of the projection formulas
    have hS1 : ∀ {X : LightCondSet.{0}} (g : fibPower F Z φ n ⟶ X),
        ψ₁ ≫ pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) ≫ g =
          pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
            e₁.hom ≫ g := by
      intro X g
      calc ψ₁ ≫ pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) ≫ g
          = (ψ₁ ≫ pullback.fst (fibBase F Z φ n) (coprodMap F Z φ)) ≫ g :=
            (Category.assoc _ _ _).symm
        _ = (pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
              e₁.hom) ≫ g := by rw [hψ₁fst]
        _ = pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
              e₁.hom ≫ g := Category.assoc _ _ _
    have hS2 : ∀ {X : LightCondSet.{0}} (g : coprodObj F ⟶ X),
        ψ₁ ≫ pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) ≫ g =
          pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
            𝟙 (coprodObj F) ≫ g := by
      intro X g
      calc ψ₁ ≫ pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) ≫ g
          = (ψ₁ ≫ pullback.snd (fibBase F Z φ n) (coprodMap F Z φ)) ≫ g :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
              𝟙 (coprodObj F)) ≫ g := by rw [hψ₁snd]
        _ = pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y)) (Sigma.desc φ) ≫
              𝟙 (coprodObj F) ≫ g := Category.assoc _ _ _
    have hB1 : ∀ {X : LightCondSet.{0}} (g : (∐ pieceObj F Z φ n) ⟶ X),
        binMap p ≫ pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
            (Sigma.desc φ) ≫ g =
          pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι (pieceObj F Z φ n) p.1 ≫ g := by
      intro X g
      calc binMap p ≫ pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
              (Sigma.desc φ) ≫ g
          = (binMap p ≫ pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
              (Sigma.desc φ)) ≫ g := (Category.assoc _ _ _).symm
        _ = (pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
              Sigma.ι (pieceObj F Z φ n) p.1) ≫ g := by rw [hbinFst]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
              Sigma.ι (pieceObj F Z φ n) p.1 ≫ g := Category.assoc _ _ _
    have hB2 : ∀ {X : LightCondSet.{0}} (g : coprodObj F ⟶ X),
        binMap p ≫ pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
            (Sigma.desc φ) ≫ g =
          pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 ≫ g := by
      intro X g
      calc binMap p ≫ pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
              (Sigma.desc φ) ≫ g
          = (binMap p ≫ pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
              (Sigma.desc φ)) ≫ g := (Category.assoc _ _ _).symm
        _ = (pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2) ≫ g := by rw [hbinSnd]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 ≫ g := Category.assoc _ _ _
    have hI : ∀ {X : LightCondSet.{0}} (g : fibPower F Z φ n ⟶ X),
        Sigma.ι (pieceObj F Z φ n) p.1 ≫ e₁.hom ≫ g = pieceMap F Z φ n p.1 ≫ g := by
      intro X g
      calc Sigma.ι (pieceObj F Z φ n) p.1 ≫ e₁.hom ≫ g
          = (Sigma.ι (pieceObj F Z φ n) p.1 ≫ e₁.hom) ≫ g := (Category.assoc _ _ _).symm
        _ = pieceMap F Z φ n p.1 ≫ g := by rw [hιQ]
    have hθFst3 : ∀ {X : LightCondSet.{0}} (g : pieceTailObj F Z φ n (consEquiv n ι p) ⟶ X),
        (thetaE F Z φ n p).hom ≫ pieceStep F Z φ n (consEquiv n ι p) ≫ g =
          pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ g := by
      intro X g
      calc (thetaE F Z φ n p).hom ≫ pieceStep F Z φ n (consEquiv n ι p) ≫ g
          = ((thetaE F Z φ n p).hom ≫ pieceStep F Z φ n (consEquiv n ι p)) ≫ g :=
            (Category.assoc _ _ _).symm
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ g := by rw [thetaE_fst]
    have hθSnd3 : ∀ {X : LightCondSet.{0}} (g : F p.2 ⟶ X),
        (thetaE F Z φ n p).hom ≫ pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 ≫ g =
          pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ g := by
      intro X g
      calc (thetaE F Z φ n p).hom ≫ pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 ≫ g
          = ((thetaE F Z φ n p).hom ≫ pieceπ F Z φ (n + 1) (consEquiv n ι p) 0) ≫ g :=
            (Category.assoc _ _ _).symm
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ g := by rw [thetaE_snd]
    -- the three computations on the `ψ` side
    have keySucc : ∀ j : Fin n,
        binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibπ F Z φ (n + 1) j.succ =
          pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ pieceπ F Z φ n p.1 j ≫ Sigma.ι F (p.1 j) := by
      intro j
      have h1 : psi2 F Z φ n ≫ fibπ F Z φ (n + 1) j.succ =
          pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) ≫ fibπ F Z φ n j := by
        rw [← fibStep_π F Z φ n j, ← Category.assoc, psi2_fst]
      have h2 : pieceMap F Z φ n p.1 ≫ fibπ F Z φ n j =
          pieceπ F Z φ n p.1 j ≫ Sigma.ι F (p.1 j) := by
        rw [WidePullback.lift_π]
      calc binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibπ F Z φ (n + 1) j.succ
          = binMap p ≫ (ψ₁ ≫ (pullback.fst (fibBase F Z φ n) (coprodMap F Z φ) ≫
                fibπ F Z φ n j)) := by rw [h1]
        _ = binMap p ≫ (pullback.fst (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
                (Sigma.desc φ) ≫ e₁.hom ≫ fibπ F Z φ n j) := by rw [hS1]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
                Sigma.ι (pieceObj F Z φ n) p.1 ≫ e₁.hom ≫ fibπ F Z φ n j := by rw [hB1]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ pieceMap F Z φ n p.1 ≫
                fibπ F Z φ n j := by rw [hI]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
                pieceπ F Z φ n p.1 j ≫ Sigma.ι F (p.1 j) := by rw [h2]
    have keyZero : binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibπ F Z φ (n + 1) 0 =
        pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 := by
      calc binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibπ F Z φ (n + 1) 0
          = binMap p ≫ (ψ₁ ≫ pullback.snd (fibBase F Z φ n) (coprodMap F Z φ)) := by rw [psi2_snd]
        _ = binMap p ≫ (pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
                (Sigma.desc φ) ≫ 𝟙 (coprodObj F)) := by rw [hψ₁snd]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 ≫ 𝟙 (coprodObj F) := by
              rw [hB2]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 := by rw [Category.comp_id]
    have keyBase : binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibBase F Z φ (n + 1) =
        pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ φ p.2 := by
      have h3 : Sigma.ι F p.2 ≫ coprodMap F Z φ = φ p.2 := by rw [Sigma.ι_comp_desc]
      calc binMap p ≫ ψ₁ ≫ psi2 F Z φ n ≫ fibBase F Z φ (n + 1)
          = binMap p ≫ (ψ₁ ≫ (pullback.snd (fibBase F Z φ n) (coprodMap F Z φ) ≫
                coprodMap F Z φ)) := by rw [psi2_base]
        _ = binMap p ≫ (pullback.snd (Sigma.desc (fun y : Fin n → ι => wpcPieceBase F Z φ n y))
                (Sigma.desc φ) ≫ 𝟙 (coprodObj F) ≫ coprodMap F Z φ) := by rw [hS2]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 ≫
                (𝟙 (coprodObj F) ≫ coprodMap F Z φ) := by rw [hB2]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 ≫ coprodMap F Z φ := by
              rw [Category.id_comp]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ φ p.2 := by rw [h3]
    -- the same computations on the `θ` side
    have thSucc : ∀ j : Fin n,
        (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
            fibπ F Z φ (n + 1) j.succ =
          pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ pieceπ F Z φ n p.1 j ≫ Sigma.ι F (p.1 j) := by
      intro j
      have hp : pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫ fibπ F Z φ (n + 1) j.succ =
          pieceπ F Z φ (n + 1) (consEquiv n ι p) j.succ ≫ Sigma.ι F (p.1 j) := by
        rw [WidePullback.lift_π]
        rfl
      have hπX : pieceπ F Z φ (n + 1) (consEquiv n ι p) j.succ =
          pieceStep F Z φ n (consEquiv n ι p) ≫ pieceTailπ F Z φ n (consEquiv n ι p) j :=
        (pieceStep_tailπ F Z φ n (consEquiv n ι p) j).symm
      calc (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
              fibπ F Z φ (n + 1) j.succ
          = (thetaE F Z φ n p).hom ≫ (pieceπ F Z φ (n + 1) (consEquiv n ι p) j.succ ≫
              Sigma.ι F (p.1 j)) := by rw [hp]
        _ = (thetaE F Z φ n p).hom ≫ ((pieceStep F Z φ n (consEquiv n ι p) ≫
              pieceTailπ F Z φ n (consEquiv n ι p) j) ≫ Sigma.ι F (p.1 j)) := by rw [hπX]
        _ = (thetaE F Z φ n p).hom ≫ (pieceStep F Z φ n (consEquiv n ι p) ≫
              (pieceTailπ F Z φ n (consEquiv n ι p) j ≫ Sigma.ι F (p.1 j))) := by rw [Category.assoc]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
              (pieceTailπ F Z φ n (consEquiv n ι p) j ≫ Sigma.ι F (p.1 j)) := by rw [hθFst3]
        _ = pullback.fst (wpcPieceBase F Z φ n p.1) (φ p.2) ≫
              (pieceπ F Z φ n p.1 j ≫ Sigma.ι F (p.1 j)) := by rw [pieceTailπ_consEquiv]
    have thZero : (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
            fibπ F Z φ (n + 1) 0 =
        pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F p.2 := by
      have hp : pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫ fibπ F Z φ (n + 1) 0 =
          pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 ≫ Sigma.ι F (p.2) := by
        rw [WidePullback.lift_π]
        rfl
      calc (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
              fibπ F Z φ (n + 1) 0
          = (thetaE F Z φ n p).hom ≫
              (pieceπ F Z φ (n + 1) (consEquiv n ι p) 0 ≫ Sigma.ι F (p.2)) := by rw [hp]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ Sigma.ι F (p.2) := by rw [hθSnd3]
    have thBase : (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
            fibBase F Z φ (n + 1) =
        pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ φ p.2 := by
      have hp : pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫ fibBase F Z φ (n + 1) =
          wpcPieceBase F Z φ (n + 1) (consEquiv n ι p) := by
        rw [WidePullback.lift_base]
      calc (thetaE F Z φ n p).hom ≫ pieceMap F Z φ (n + 1) (consEquiv n ι p) ≫
              fibBase F Z φ (n + 1)
          = (thetaE F Z φ n p).hom ≫ wpcPieceBase F Z φ (n + 1) (consEquiv n ι p) := by rw [hp]
        _ = pullback.snd (wpcPieceBase F Z φ n p.1) (φ p.2) ≫ φ p.2 := by rw [thetaE_base]
    -- ### Step 6: conclude by the universal property of the fibre power.
    refine Limits.WidePullback.hom_ext (fibArr F Z φ (n + 1)) _ _ ?_ ?_
    · intro i
      induction i using Fin.cases with
      | zero =>
        simp only [Category.assoc]
        rw [keyZero, thZero]
      | succ j =>
        simp only [Category.assoc]
        rw [keySucc j, thSucc j]
    · simp only [Category.assoc]
      rw [keyBase, thBase]

end Setting

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed in
/-- **Van Kampen for wide pullbacks.**  Let `A := ∐ F` be a small coproduct in `LightCondSet` with
structure maps `φ y : F y ⟶ Z`.  Then the `n`-fold fibre power `A ×_Z ⋯ ×_Z A` is the coproduct,
over all tuples `x : Fin n → ι`, of the fibre powers of the pieces `F (x i)`; the canonical map
(given by the universal property of the coproduct and `WidePullback.lift`) is an isomorphism.

Route: induce on `n`.  The wide pullback of `n+1` copies is the pullback of that of `n` copies along
the base with `A`; the pieces are the pullbacks `Q x ×_Z F y` (universality of the coproduct `∐ F`,
`Work.ANALYTIC.isIso_coprodPullbackMap`), and universality of the coproduct `∐ Q x` gives the
induction step (Mathlib: `IsUniversalColimit.nonempty_isColimit_prod_of_isPullback` in
`Mathlib/CategoryTheory/Limits/VanKampen.lean`, using
`Work.ANALYTIC.isUniversalColimit_colimitCocone_lightCondSet` for the coproduct cocones).  The index
sets `Fin (n+1) → ι` and `(Fin n → ι) × ι` are identified via `Fin.cons`/`Fin.succ`. -/
theorem widePullbackCoproductDesc_isIso {ι : Type} (F : ι → LightCondSet.{0}) [HasCoproduct F]
    (Z : LightCondSet.{0}) (φ : ∀ y, F y ⟶ Z) (n : ℕ)
    [HasCoproduct (fun x : Fin n → ι =>
      Limits.widePullback Z (fun i : Fin n => F (x i)) (fun i : Fin n => φ (x i)))] :
    IsIso (Sigma.desc (fun x : Fin n → ι =>
      (Limits.WidePullback.lift (Limits.WidePullback.base (fun i : Fin n => φ (x i)))
        (fun i : Fin n => Limits.WidePullback.π (fun i : Fin n => φ (x i)) i ≫ Sigma.ι F (x i))
        (by simp) :
        Limits.widePullback Z (fun i : Fin n => F (x i)) (fun i : Fin n => φ (x i)) ⟶
          Limits.widePullback Z (fun _ : Fin n => ∐ F) (fun _ : Fin n => Sigma.desc φ)))) := by
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (c := Cofan.mk (fibPower F Z φ n) (pieceMap F Z φ n))).mp ?_
  exact widePullbackCoproductDesc_aux F Z φ n

end

end Work.ANALYTIC
