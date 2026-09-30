import Mathlib
import Submission.Work.SSSR.grFAux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
noncomputable section

variable {X Y : SSet.{0}}

/-- The shifted Serre filtration, whose `d`-th term is the chain complex of `f ⁻¹' (sk (d+1))`. -/
abbrev serF (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) : ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  natShift ⋙ Work.SSSR.StemsB.serreChainFiltration f R

/-- In degree `n`, the structure map `C(R_{P+1}) ⟶ C(R_{P+2})` of the shifted Serre filtration
sends the generator of a simplex `a` of `R_{P+1}` to the generator of the same simplex. -/
lemma incF_iota_f (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (P n : ℕ)
    (a : (((Work.SSSR.StemsB.serreSubcomplex f (P+1) : X.Subcomplex)) : SSet) _⦋n⦌) :
    ((Work.SSSR.StemsB.serreSubcomplex f (P+1) : X.Subcomplex) : SSet).ιChainComplex
        (R := ModuleCat.of R R) a ≫ (incF (serF R f) P).f n =
      ((Work.SSSR.StemsB.serreSubcomplex f (P+2) : X.Subcomplex) : SSet).ιChainComplex
        (R := ModuleCat.of R R)
        (⟨a.1, Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (P+1)) (op ⦋n⦌) a.2⟩ :
          (((Work.SSSR.StemsB.serreSubcomplex f (P+2) : X.Subcomplex)) : SSet) _⦋n⦌) :=
  SSet.ι_chainComplexMap_f (C := ModuleCat R)
    (X := ((Work.SSSR.StemsB.serreSubcomplex f (P+1) : X.Subcomplex) : SSet))
    (Y := ((Work.SSSR.StemsB.serreSubcomplex f (P+2) : X.Subcomplex) : SSet))
    (R := ModuleCat.of R R)
    (Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (P+1)))) a

/-- The projection `C(f ⁻¹' (sk (d+1))) ⟶ grF` onto the `d`-th graded piece of the Serre
filtration (the quotient by the chains on `f ⁻¹' (sk d)`, and the identity for `d = 0`). -/
def grFι (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) : (serF R f).obj d ⟶ grF (serF R f) d :=
  match d with
  | 0 => 𝟙 ((serF R f).obj 0)
  | k + 1 => cokernel.π (incF (serF R f) k)

@[simp] lemma grFι_zero (f : X ⟶ Y) : grFι R f 0 = 𝟙 _ := rfl

@[simp] lemma grFι_succ (f : X ⟶ Y) (k : ℕ) :
    grFι R f (k+1) = cokernel.π (incF (serF R f) k) := rfl

lemma incF_comp_grFι (f : X ⟶ Y) (k : ℕ) :
    incF (serF R f) k ≫ grFι R f (k+1) = 0 := by
  rw [grFι_succ]
  exact cokernel.condition (incF (serF R f) k)

set_option backward.isDefEq.respectTransparency false in
/-- A generator of `C(R_{k+2})` whose simplex already lies in `R_{k+1}` has zero image under
`grFι R f (k+1)`. -/
lemma iota_comp_grFι_eq_zero (f : X ⟶ Y) {k n : ℕ}
    (x : (((Work.SSSR.StemsB.serreSubcomplex f (k+2) : X.Subcomplex)) : SSet) _⦋n⦌)
    (hx : x.1 ∈ (Work.SSSR.StemsB.serreSubcomplex f (k+1)).obj (op ⦋n⦌)) :
    ((Work.SSSR.StemsB.serreSubcomplex f (k+2) : X.Subcomplex) : SSet).ιChainComplex
      (R := ModuleCat.of R R) x ≫ (grFι R f (k+1)).f n = 0 := by
  have h2 : (incF (serF R f) k).f n ≫ (grFι R f (k+1)).f n = 0 := by
    rw [← HomologicalComplex.comp_f (incF (serF R f) k) (grFι R f (k+1)) n, incF_comp_grFι,
      HomologicalComplex.zero_f]
  have hstep := incF_iota_f R f k n
    (⟨x.1, hx⟩ : (((Work.SSSR.StemsB.serreSubcomplex f (k+1) : X.Subcomplex)) : SSet) _⦋n⦌)
  have hx2 : (⟨x.1, Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (k+1)) (op ⦋n⦌) hx⟩ :
      (((Work.SSSR.StemsB.serreSubcomplex f (k+2) : X.Subcomplex)) : SSet) _⦋n⦌) = x :=
    Subtype.ext rfl
  rw [← hx2, ← hstep]
  simp only [Category.assoc, h2, comp_zero]

/-- The image of the second projection `T_y ⟶ X` lies in `f ⁻¹' (sk (d+1))`. -/
lemma T_range_le (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    SSet.Subcomplex.range (pullback.snd (nIndexSigma Y d y) f) ≤
      Work.SSSR.StemsB.serreSubcomplex f (d+1) := by
  rw [Subfunctor.le_def]
  intro n w hw
  rw [Subfunctor.range_obj] at hw
  obtain ⟨w₀, rfl⟩ := hw
  exact T_snd_mem f y n.unop.len w₀

/-- The second projection `T_y ⟶ f ⁻¹' (sk (d+1))`. -/
def sndToR (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    pullAlong f (nIndexSigma Y d y) ⟶
      ((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex) : SSet) :=
  SSet.Subcomplex.lift (pullback.snd (nIndexSigma Y d y) f) (T_range_le f y)

lemma sndToR_ι (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    sndToR f y ≫ (Work.SSSR.StemsB.serreSubcomplex f (d+1)).ι =
      pullback.snd (nIndexSigma Y d y) f :=
  SSet.Subcomplex.lift_ι _ _

/-- The inclusion `∂T_y ⟶ T_y` followed by the second projection, which lands in
`f ⁻¹' (sk d)`. -/
lemma bd_range_le (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    SSet.Subcomplex.range ((bdryAlong f (nIndexSigma Y d y)).ι ≫
        pullback.snd (nIndexSigma Y d y) f) ≤ Work.SSSR.StemsB.serreSubcomplex f d := by
  rw [Subfunctor.le_def]
  intro n w hw
  rw [Subfunctor.range_obj] at hw
  obtain ⟨w₀, rfl⟩ := hw
  exact bdry_snd_mem f y n.unop.len w₀

/-- The composite `∂T_y ⟶ T_y ⟶ f ⁻¹' (sk (d+1))`, as a map into `f ⁻¹' (sk d)`. -/
def bdToR (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    (bdryAlong f (nIndexSigma Y d y) : SSet) ⟶
      ((Work.SSSR.StemsB.serreSubcomplex f d : X.Subcomplex) : SSet) :=
  SSet.Subcomplex.lift ((bdryAlong f (nIndexSigma Y d y)).ι ≫ pullback.snd (nIndexSigma Y d y) f)
    (bd_range_le f y)

lemma bdToR_ι (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    bdToR f y ≫ (Work.SSSR.StemsB.serreSubcomplex f d).ι =
      (bdryAlong f (nIndexSigma Y d y)).ι ≫ pullback.snd (nIndexSigma Y d y) f :=
  SSet.Subcomplex.lift_ι _ _

lemma bdToR_comp (f : X ⟶ Y) {d : ℕ} (y : nIndex Y d) :
    (bdryAlong f (nIndexSigma Y d y)).ι ≫ sndToR f y =
      bdToR f y ≫ Subfunctor.homOfLe (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ d)) := by
  apply (cancel_mono (Work.SSSR.StemsB.serreSubcomplex f (d+1)).ι).1
  simp only [Category.assoc, sndToR_ι, bdToR_ι, Subfunctor.homOfLe_ι]


/-- The quotient projection `C(T_y) ⟶ C(T_y)/C(∂T_y)` of the σ-piece over `y`. -/
def pieceπ (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    sCC R (pullAlong f (nIndexSigma Y d y)) ⟶ pieceAlong R f (nIndexSigma Y d y) :=
  cokernel.π (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι)

lemma pieceπ_eq (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    pieceπ R f d y = cokernel.π (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι) := rfl

/-- The generator of `C(T_y)` attached to a simplex of `∂T_y` factors through `C(∂T_y)`. -/
lemma bd_iota_eq (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌))
    (hw : w ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    (pullAlong f (nIndexSigma Y d y)).ιChainComplex (R := ModuleCat.of R R) w =
      (((bdryAlong f (nIndexSigma Y d y) : (pullAlong f (nIndexSigma Y d y)).Subcomplex)) : SSet).ιChainComplex
          (R := ModuleCat.of R R) ⟨w, hw⟩ ≫
        (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι).f n :=
  (SSet.ι_chainComplexMap_f (C := ModuleCat R)
    (X := (((bdryAlong f (nIndexSigma Y d y) : (pullAlong f (nIndexSigma Y d y)).Subcomplex)) : SSet))
    (Y := pullAlong f (nIndexSigma Y d y)) (R := ModuleCat.of R R)
    ((bdryAlong f (nIndexSigma Y d y)).ι) ⟨w, hw⟩).symm

/-- A generator of `C(T_y)` whose simplex lies in `∂T_y` is killed by the projection to the
σ-piece. -/
lemma iota_bdry_comp_pi_eq_zero (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌))
    (hw : w ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌)) :
    (pullAlong f (nIndexSigma Y d y)).ιChainComplex (R := ModuleCat.of R R) w ≫
      (pieceπ R f d y).f n = 0 := by
  rw [bd_iota_eq f y w hw]
  have h2 : (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι).f n ≫ (pieceπ R f d y).f n = 0 := by
    have hc : sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι ≫ pieceπ R f d y = 0 := by
      rw [pieceπ_eq]
      exact cokernel.condition _
    have h3 : ((sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι) ≫ pieceπ R f d y).f n = 0 := by
      rw [hc, HomologicalComplex.zero_f]
    rw [HomologicalComplex.comp_f] at h3
    exact h3
  simp only [Category.assoc, h2, comp_zero]

/-- The degreewise components of the Eilenberg–Zilber section `Theta R`. -/
def ThetaF (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d n : ℕ) :
    ((serF R f).obj d).X n ⟶ (∐ (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y))).X n :=
  Sigma.desc fun x : (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet) _⦋n⦌ =>
    if h : (SSet.S.mk (f.app (op ⦋n⦌) x.1)).toN.dim = d then
      (pullAlong f (nIndexSigma Y d (ezY f x.1 h))).ιChainComplex (R := ModuleCat.of R R)
          (ezPoint f x.1 h) ≫
        (pieceπ R f d (ezY f x.1 h)).f n ≫
        (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f x.1 h)).f n
    else 0

/-- The value of the Eilenberg–Zilber section on a generator. -/
lemma ThetaF_apply (f : X ⟶ Y) (d n : ℕ)
    (x : (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet) _⦋n⦌) :
    ((((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet).ιChainComplex
        (R := ModuleCat.of R R) x) ≫ ThetaF R f d n =
      (if h : (SSet.S.mk (f.app (op ⦋n⦌) x.1)).toN.dim = d then
        (pullAlong f (nIndexSigma Y d (ezY f x.1 h))).ιChainComplex (R := ModuleCat.of R R)
            (ezPoint f x.1 h) ≫
          (pieceπ R f d (ezY f x.1 h)).f n ≫
          (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f x.1 h)).f n
      else 0) := by
  rw [SSet.ιChainComplex, ThetaF]
  exact Sigma.ι_desc _ _

lemma toN_dim_f_δ_le {X Y : SSet.{0}} (f : X ⟶ Y) {k : ℕ} (z : X _⦋k+1⦌) (i : Fin (k+2)) :
    (SSet.S.mk (f.app (op ⦋k⦌) (X.δ i z))).toN.dim ≤
      (SSet.S.mk (f.app (op ⦋k+1⦌) z)).toN.dim := by
  rw [SSet.δ_naturality_apply]
  exact toN_dim_δ_le (f.app (op ⦋k+1⦌) z) i

lemma pullPt_mor_eq {X Y : SSet.{0}} (f : X ⟶ Y) (d m : ℕ)
    (y y' : nIndex Y d) (v v' : ⦋m⦌ ⟶ ⦋d⦌) (x : X _⦋m⦌)
    (h : Y.map v.op (nBase y) = f.app (op ⦋m⦌) x)
    (h' : Y.map v'.op (nBase y') = f.app (op ⦋m⦌) x)
    (hy : y' = y) (hv : v' = v) :
    (pullAlong f (nIndexSigma Y d y')).ιChainComplex (pullPt f y' v' x h') ≫
      (pieceπ R f d y').f m ≫ (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y').f m
    = (pullAlong f (nIndexSigma Y d y)).ιChainComplex (pullPt f y v x h) ≫
      (pieceπ R f d y).f m ≫ (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y).f m := by
  subst hy
  subst hv
  rw [pullPt_proof_irrel f y' v' x h' h]

lemma face_term {X Y : SSet.{0}} (f : X ⟶ Y) (d m : ℕ)
    (x : X _⦋m+1⦌) (h : (SSet.S.mk (f.app (op ⦋m+1⦌) x)).toN.dim = d)
    (i : Fin (m+2)) :
    (pullAlong f (nIndexSigma Y d (ezY f x h))).ιChainComplex
        ((pullAlong f (nIndexSigma Y d (ezY f x h))).δ i (ezPoint f x h)) ≫
      (pieceπ R f d (ezY f x h)).f m ≫
      (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f x h)).f m
    = (if h' : (SSet.S.mk (f.app (op ⦋m⦌) (X.δ i x))).toN.dim = d then
        (pullAlong f (nIndexSigma Y d (ezY f (X.δ i x) h'))).ιChainComplex
            (ezPoint f (X.δ i x) h') ≫
          (pieceπ R f d (ezY f (X.δ i x) h')).f m ≫
          (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f (X.δ i x) h')).f m
       else 0) := by
  have h_i : Y.map (SimplexCategory.δ i ≫ ezU f x h).op (nBase (ezY f x h)) =
      f.app (op ⦋m⦌) (X.δ i x) := (ez_face_val f x h i).symm
  rw [show ezPoint f x h = pullPt f (ezY f x h) (ezU f x h) x (ez_compat f x h) from rfl,
      pullPt_δ f (ezY f x h) (ezU f x h) x (ez_compat f x h) i h_i]
  by_cases h' : (SSet.S.mk (f.app (op ⦋m⦌) (X.δ i x))).toN.dim = d
  · rw [dif_pos h']
    have hv : Epi (SimplexCategory.δ i ≫ ezU f x h) := by
      by_contra hne
      have hlt := ezFaceNonEpi (nBase (ezY f x h)) (nBase_mem (ezY f x h))
        (SimplexCategory.δ i ≫ ezU f x h) hne
      rw [← ez_face_val f x h i] at hlt
      exact absurd h' (ne_of_lt hlt)
    exact (pullPt_mor_eq f d m (ezY f x h) (ezY f (X.δ i x) h')
        (SimplexCategory.δ i ≫ ezU f x h) (ezU f (X.δ i x) h') (X.δ i x) h_i
        (ez_compat f (X.δ i x) h') (ezY_δ f x h i h' hv) (ezU_δ f x h i h' hv)).symm
  · rw [dif_neg h']
    have hnev : ¬ Epi (SimplexCategory.δ i ≫ ezU f x h) := by
      intro hv
      have hthis := ezFaceEpi (nBase (ezY f x h)) (nBase_mem (ezY f x h))
        (SimplexCategory.δ i ≫ ezU f x h) hv
      rw [← ez_face_val f x h i] at hthis
      exact h' (by rw [hthis]; rfl)
    rw [← Category.assoc,
      iota_bdry_comp_pi_eq_zero f (ezY f x h)
        (pullPt f (ezY f x h) (SimplexCategory.δ i ≫ ezU f x h) (X.δ i x) h_i)
        ((pullPt_mem_bdry_iff f (ezY f x h) (SimplexCategory.δ i ≫ ezU f x h) (X.δ i x) h_i).mpr hnev),
      zero_comp]

/-- The Eilenberg–Zilber section is a chain map. -/
lemma Theta_comm (f : X ⟶ Y) (d : ℕ) {n m : ℕ} (hn : (ComplexShape.down ℕ).Rel n m) :
    ThetaF R f d n ≫ (∐ (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y))).d n m =
      ((serF R f).obj d).d n m ≫ ThetaF R f d m := by
  have hmn : m + 1 = n := hn
  subst hmn
  apply SSet.chainComplex_hom_ext
    (X := ((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex) : SSet))
    (R := ModuleCat.of R R)
  intro x
  rw [← Category.assoc, ← Category.assoc]
  rw [ThetaF_apply]
  by_cases h : (SSet.S.mk (f.app (op ⦋m+1⦌) x.1)).toN.dim = d
  · rw [dif_pos h]
    rw [show ((Work.SSSR.serF R f).obj d).d (m+1) m =
      (Work.SSSR.sCC R (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet)).d (m+1) m from rfl]
    rw [SSet.ιChainComplex_d]
    rw [Category.assoc, Category.assoc]
    rw [(Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f x.1 h)).comm (m+1) m]
    conv_lhs => enter [2]; rw [← Category.assoc]
    rw [(pieceπ R f d (ezY f x.1 h)).comm (m+1) m]
    conv_lhs => enter [2]; rw [Category.assoc]
    rw [← Category.assoc]
    rw [SSet.ιChainComplex_d]
    rw [Preadditive.sum_comp]
    rw [Preadditive.sum_comp (Finset.univ : Finset (Fin (m+2)))
        (fun i => (-1:ℤ)^(i:ℕ) • ((((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet).ιChainComplex
          ((((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet).δ i x)))
        (ThetaF R f d m)]
    simp only [Linear.smul_comp]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [face_term f d m x.1 h i]
    rw [ThetaF_apply]
    rw [show (( (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet)).δ i x).1 = X.δ i x.1 from rfl]
  · rw [dif_neg h]
    rw [zero_comp]
    symm
    rw [show ((Work.SSSR.serF R f).obj d).d (m+1) m =
      (Work.SSSR.sCC R (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet)).d (m+1) m from rfl]
    rw [SSet.ιChainComplex_d]
    rw [Preadditive.sum_comp]
    simp only [Linear.smul_comp]
    apply Finset.sum_eq_zero
    intro i _
    have hbad : ¬ ((SSet.S.mk (f.app (op ⦋m⦌)
        (((((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet)).δ i x).1)).toN.dim = d) := by
      intro hbd
      have hbd' : (SSet.S.mk (f.app (op ⦋m⦌) (X.δ i x.1))).toN.dim = d := hbd
      have h1 : (SSet.S.mk (f.app (op ⦋m⦌) (X.δ i x.1))).toN.dim ≤
          (SSet.S.mk (f.app (op ⦋m+1⦌) x.1)).toN.dim := toN_dim_f_δ_le f x.1 i
      have h2 : (SSet.S.mk (f.app (op ⦋m+1⦌) x.1)).toN.dim ≤ d := by
        have h3 := (serreSubcomplexToN f x.1).mp x.2
        omega
      have h4 : (SSet.S.mk (f.app (op ⦋m+1⦌) x.1)).toN.dim = d := by omega
      exact h h4
    rw [ThetaF_apply, dif_neg hbad]
    simp


/-- **The Eilenberg–Zilber section.** The chain map `C(f ⁻¹' (sk (d+1))) ⟶ ∐_y C(T_y)/C(∂T_y)`
sending a simplex `x` whose image has nondegenerate part of dimension exactly `d` to the point of
`T_y` whose `Δ[d]`-component is the Eilenberg–Zilber epimorphism of `f x` (`y` being the
nondegenerate part of `f x`), and all other simplices to `0`. -/
def Theta (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) :
    (serF R f).obj d ⟶ ∐ (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) where
  f := ThetaF R f d
  comm' := fun _ _ hn => Theta_comm f d hn

/-- The inclusion `f ⁻¹' (sk (k+1)) ⟶ f ⁻¹' (sk (k+2))` followed by the projection onto the
`(k+1)`-st graded piece of the Serre filtration is zero. -/
lemma sCCMap_homOfLe_comp_grFι (f : X ⟶ Y) (k : ℕ) :
    sCCMap R (Subfunctor.homOfLe
        (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (k+1)))) ≫
      grFι R f (k+1) = 0 := by
  change incF (serF R f) k ≫ grFι R f (k+1) = 0
  exact incF_comp_grFι f k

/-- The boundary of `T_y` over a nondegenerate `0`-simplex `y` is empty. -/
lemma bdryAlong_zero_eq_bot (f : X ⟶ Y) (y : nIndex Y 0) :
    bdryAlong f (nIndexSigma Y 0 y) = ⊥ := by
  ext U w
  change (pullback.fst (nIndexSigma Y 0 y) f).app U w ∈ (SSet.boundary 0).obj U ↔
    w ∈ (⊥ : (pullAlong f (nIndexSigma Y 0 y)).Subcomplex).obj U
  rw [SSet.boundary_zero]
  simp

/-- The σ-piece over `y` receives `C(T_y)`, and the second projection `T_y ⟶ f ⁻¹' (sk (d+1))`
composed with the projection to the graded piece kills `C(∂T_y)`. -/
lemma mapPhiY_zero (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι ≫ (sCCMap R (sndToR f y) ≫ grFι R f d) = 0 := by
  cases d with
  | zero =>
    erw [grFι_zero, Category.comp_id, bdryAlong_zero_eq_bot f y]
    apply HomologicalComplex.hom_ext
    intro n
    apply SSet.chainComplex_hom_ext
    intro a
    obtain ⟨w, hw⟩ := a
    rw [Subfunctor.bot_obj] at hw
    exact hw.elim
  | succ k =>
    have key : sCCMap R (Subfunctor.homOfLe
          (Work.SSSR.StemsB.serreSubcomplex_mono f (Nat.le_succ (k+1)))) ≫
        grFι R f (k+1) = 0 := sCCMap_homOfLe_comp_grFι f k
    erw [← Category.assoc, ← Functor.map_comp, bdToR_comp f y, Functor.map_comp,
      Category.assoc]
    erw [key, comp_zero]

/-- The component of `Phi` over the nondegenerate simplex `y`. -/
def mapPhiY (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    pieceAlong R f (nIndexSigma Y d y) ⟶ grF (serF R f) d :=
  cokernel.desc (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι)
    (sCCMap R (sndToR f y) ≫ grFι R f d) (mapPhiY_zero f d y)

/-- The coproduct of the second projections `T_y ⟶ f ⁻¹' (sk (d+1))`, followed by the projection
to the graded piece. -/
def mapPhi (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) :
    (∐ (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y))) ⟶ grF (serF R f) d :=
  Sigma.desc (mapPhiY R f d)

/-- The image of `PhiY` in the graded piece. -/
lemma mapPhiY_apply (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    (cokernel.π (sCCMap R (bdryAlong f (nIndexSigma Y d y)).ι)) ≫ mapPhiY R f d y =
      sCCMap R (sndToR f y) ≫ grFι R f d :=
  cokernel.π_desc _ _ _

/-- **The composite `incF ≫ ThetaF R` vanishes degreewise.**  Both sides are maps out of the chains
`C(f ⁻¹' sk (k+1))`, so it suffices to check the equality on the generators `ιChainComplex a`,
`a` an `n`-simplex of `f ⁻¹' sk (k+1)`: the structure map of the Serre filtration sends it to the
same generator in `C(f ⁻¹' sk (k+2))`, and the defining case distinction of `ThetaF R f (k+1)` is
trivial on it because its image has nondegenerate part of dimension `< k+1`. -/
lemma incF_comp_ThetaF (f : X ⟶ Y) (k n : ℕ) :
    (incF (serF R f) k).f n ≫ ThetaF R f (k + 1) n = 0 := by
  apply SSet.chainComplex_hom_ext
    (X := ((Work.SSSR.StemsB.serreSubcomplex f (k + 1) : X.Subcomplex) : SSet))
    (R := ModuleCat.of R R)
  intro a
  rw [← Category.assoc]
  rw [incF_iota_f R f k n a]
  rw [ThetaF_apply]
  rw [comp_zero]
  have hlt : (SSet.S.mk (f.app (op ⦋n⦌) a.1)).toN.dim < k + 1 :=
    (serreSubcomplexToN f a.1).mp a.2
  refine dif_neg ?_
  dsimp only []
  omega

lemma mapPsi_descent {X Y : SSet.{0}} (f : X ⟶ Y) (k : ℕ) :
    incF (serF R f) k ≫ Theta R f (k + 1) = 0 := by
  refine HomologicalComplex.hom_ext _ _ ?_
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  exact incF_comp_ThetaF f k n


/-- The inverse of `Theta R` on the `d`-th graded piece. -/
def mapPsi (R : Type) [CommRing R] [Nontrivial R] (f : X ⟶ Y) (d : ℕ) : grF (serF R f) d ⟶
    ∐ (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) :=
  match d with
  | 0 => Theta R f 0
  | k + 1 => cokernel.desc (incF (serF R f) k) (Theta R f (k+1)) (mapPsi_descent f k)

/-- `Psi` inverts the projection `grFι R`. -/
lemma mapPsi_toTheta (f : X ⟶ Y) (d : ℕ) : grFι R f d ≫ mapPsi R f d = Theta R f d := by
  cases d with
  | zero =>
    rw [grFι_zero]
    exact Category.id_comp _
  | succ k =>
    rw [grFι_succ]
    exact cokernel.π_desc (incF (serF R f) k) (Theta R f (k+1)) (mapPsi_descent f k)

/-- The `n`-th component of the second projection `T_y ⟶ f ⁻¹' (sk (d+1))` on the
Eilenberg–Zilber point of `x` is `x` itself (as a simplex of `f ⁻¹' (sk (d+1))`). -/
lemma thetaPhi_sndToR_app_ezPoint (f : X ⟶ Y) {d n : ℕ}
    (x : (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet) _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x.1)).toN.dim = d) :
    (sndToR f (ezY f x.1 h)).app (op ⦋n⦌) (ezPoint f x.1 h) = x := by
  apply Subtype.ext
  erw [sndToR, SSet.Subcomplex.lift_app_coe, ezPoint, pullPt_snd]

/-- The coprojection of the σ-piece over `y` composed with `mapPhi R` is `mapPhiY R`, in degree `n`. -/
lemma thetaPhi_mapPhi_iota_f (f : X ⟶ Y) (d n : ℕ) (y : nIndex Y d) :
    (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y).f n ≫
      (mapPhi R f d).f n = (mapPhiY R f d y).f n := by
  rw [← HomologicalComplex.comp_f, mapPhi, Sigma.ι_desc]

/-- The degreewise form of `mapPhiY_apply`: the quotient projection `C(T_y) ⟶ C(T_y)/C(∂T_y)`
followed by `mapPhiY R` is the second projection followed by `grFι R`. -/
lemma thetaPhi_mapPhiY_apply_f (f : X ⟶ Y) (d n : ℕ) (y : nIndex Y d) :
    (pieceπ R f d y).f n ≫ (mapPhiY R f d y).f n =
      (sCCMap R (sndToR f y)).f n ≫ (grFι R f d).f n := by
  erw [← HomologicalComplex.comp_f (pieceπ R f d y) (mapPhiY R f d y) n,
    pieceπ_eq, mapPhiY_apply, HomologicalComplex.comp_f]

/-- The generator of `C(T_y)` at the Eilenberg–Zilber point of `x`, pushed forward by the second
projection, is the generator of `C(f ⁻¹' (sk (d+1)))` attached to `x`. -/
lemma thetaPhi_iota_sCCMap_sndToR (f : X ⟶ Y) {d n : ℕ}
    (x : (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet) _⦋n⦌)
    (h : (SSet.S.mk (f.app (op ⦋n⦌) x.1)).toN.dim = d) :
    (pullAlong f (nIndexSigma Y d (ezY f x.1 h))).ιChainComplex
        (R := ModuleCat.of R R) (ezPoint f x.1 h) ≫
      (sCCMap R (sndToR f (ezY f x.1 h))).f n =
    (((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex)) : SSet).ιChainComplex
      (R := ModuleCat.of R R) x := by
  rw [SSet.ι_chainComplexMap_f, thetaPhi_sndToR_app_ezPoint f x h]

/-- `Theta R` followed by `Phi` is the projection to the graded piece. -/
lemma Theta_comp_mapPhi (f : X ⟶ Y) (d : ℕ) : Theta R f d ≫ mapPhi R f d = grFι R f d := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f]
  refine SSet.chainComplex_hom_ext
    (X := ((Work.SSSR.StemsB.serreSubcomplex f (d+1) : X.Subcomplex) : SSet))
    (R := ModuleCat.of R R) ?_
  intro x
  erw [← Category.assoc, ThetaF_apply f d n x]
  by_cases h : (SSet.S.mk (f.app (op ⦋n⦌) x.1)).toN.dim = d
  · rw [dif_pos h]
    erw [Category.assoc, Category.assoc,
      thetaPhi_mapPhi_iota_f f d n (ezY f x.1 h),
      thetaPhi_mapPhiY_apply_f f d n (ezY f x.1 h),
      ← Category.assoc, thetaPhi_iota_sCCMap_sndToR f x h]
  · rw [dif_neg h, zero_comp]
    symm
    cases d with
    | zero =>
      exfalso
      have hx := (serreSubcomplexToN f x.1).mp x.2
      exact h (by omega)
    | succ k =>
      apply iota_comp_grFι_eq_zero f x
      rw [serreSubcomplexToN]
      have hx := (serreSubcomplexToN f x.1).mp x.2
      omega


open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
lemma ezUnique {X Y : SSet.{0}} (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d)
    (v : ⦋n⦌ ⟶ ⦋d⦌) (x : X _⦋n⦌) (h : Y.map v.op (nBase y) = f.app (op ⦋n⦌) x)
    (hv : Epi v) (hd : (SSet.S.mk (f.app (op ⦋n⦌) x)).toN.dim = d) :
    ezY f x hd = y ∧ ezU f x hd = v := by
  haveI : Epi (ezU f x hd) := ezU_epi f x hd
  -- The two epimorphisms `ezU f x hd` and `v` present the same simplex `f x` over the
  -- nondegenerate simplices `nBase (ezY f x hd)` and `nBase y`, both of dimension `d`.
  have hbase : nBase (ezY f x hd) = nBase y := by
    have hh := SSet.unique_nonDegenerate_simplex Y (f.app (op ⦋n⦌) x) (ezU f x hd)
      ⟨nBase (ezY f x hd), nBase_mem (ezY f x hd)⟩ (ez_compat f x hd).symm
      v ⟨nBase y, nBase_mem y⟩ h.symm
    simpa using hh
  have hmap : ezU f x hd = v :=
    SSet.unique_nonDegenerate_map Y (f.app (op ⦋n⦌) x) (ezU f x hd)
      ⟨nBase (ezY f x hd), nBase_mem (ezY f x hd)⟩ (ez_compat f x hd).symm
      v ⟨nBase y, nBase_mem y⟩ h.symm
  refine ⟨?_, hmap⟩
  -- Equality of the underlying nondegenerate simplices follows from `hbase`, since a
  -- nondegenerate simplex is determined by the subcomplex it generates.
  apply Subtype.ext
  rw [show (ezY f x hd).1 = (SSet.S.mk (f.app (op ⦋n⦌) x)).toN from rfl]
  rw [← SSet.N.cast_eq_self (SSet.S.mk (f.app (op ⦋n⦌) x)).toN hd,
      ← SSet.N.cast_eq_self y.1 y.2]
  exact SSet.N.subcomplex_injective (by
    rw [show ((SSet.S.mk (f.app (op ⦋n⦌) x)).toN.cast hd).subcomplex =
        SSet.Subcomplex.ofSimplex (nBase (ezY f x hd)) from rfl,
      show (y.1.cast y.2).subcomplex = SSet.Subcomplex.ofSimplex (nBase y) from rfl, hbase])

/-- A simplex `w` of `T_y` written through its two components: `w` is the point `pullPt` of `T_y`
with `Δ[d]`-component `objEquiv (fst w)` and `X`-component `snd w`. -/
lemma pullPt_self (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d)
    (w : (pullAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌))
    (hcomp : Y.map (SSet.stdSimplex.objEquiv
        ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w)).op (nBase y) =
      f.app (op ⦋n⦌) ((pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w)) :
    pullPt f y (SSet.stdSimplex.objEquiv ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w))
      ((pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w) hcomp = w := by
  apply pullPt_ext f y
  · rw [pullPt_fst, Equiv.symm_apply_apply]
  · rw [pullPt_snd]

/-- **The "good" case of the generator check.**  If the `Δ[d]`-component `v` of a point
`w = pullPt f y v xs hcomp` of `T_y` is an epimorphism, then the Eilenberg–Zilber data of the
image of `w` in `f ⁻¹' (sk (d+1))` is `(y, v)`, hence the generator `ezPoint` of `ThetaF R` and the
generator `pullPt` of `C(T_y)` project to the same element of the σ-piece of `y`.  The two sides
are *not* comparable as elements of the same simplicial set (they live in `T_{ezY}` and in `T_y`
respectively), so the statement is expressed directly for the two composites; the hypothesis
`ezY f xs hd = y` is what makes them comparable, and `subst` performs the transport. -/
lemma genId_aux (f : X ⟶ Y) {d n : ℕ} (y : nIndex Y d)
    (v : ⦋n⦌ ⟶ ⦋d⦌) (xs : X _⦋n⦌) (hcomp : Y.map v.op (nBase y) = f.app (op ⦋n⦌) xs)
    (hd : (SSet.S.mk (f.app (op ⦋n⦌) xs)).toN.dim = d)
    (hY : ezY f xs hd = y) (hU : ezU f xs hd = v) :
    (pullAlong f (nIndexSigma Y d (ezY f xs hd))).ιChainComplex (R := ModuleCat.of R R)
        (ezPoint f xs hd) ≫
      (pieceπ R f d (ezY f xs hd)).f n ≫
        (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) (ezY f xs hd)).f n =
    (pullAlong f (nIndexSigma Y d y)).ιChainComplex (R := ModuleCat.of R R)
        (pullPt f y v xs hcomp) ≫
      (pieceπ R f d y).f n ≫
        (Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y).f n := by
  subst y
  -- After the transport, both sides live over `ezY f xs hd`, and `ezPoint` and `pullPt` agree
  -- because their two components do.
  have hp : ezPoint f xs hd = pullPt f (ezY f xs hd) v xs hcomp := by
    apply pullPt_ext f (ezY f xs hd)
    · rw [show ezPoint f xs hd =
          pullPt f (ezY f xs hd) (ezU f xs hd) xs (ez_compat f xs hd) from rfl]
      rw [pullPt_fst, pullPt_fst, hU]
    · rw [show ezPoint f xs hd =
          pullPt f (ezY f xs hd) (ezU f xs hd) xs (ez_compat f xs hd) from rfl]
      rw [pullPt_snd, pullPt_snd]
  rw [hp]

open CategoryTheory CategoryTheory.Limits Simplicial Opposite in
lemma genId {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) (y : nIndex Y d) :
    sCCMap R (sndToR f y) ≫ Theta R f d =
      pieceπ R f d y ≫
        Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y := by
  refine HomologicalComplex.hom_ext _ _ ?_
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply SSet.chainComplex_hom_ext
  intro w
  rw [← Category.assoc]
  rw [SSet.ι_chainComplexMap_f]
  rw [show (Theta R f d).f n = ThetaF R f d n from rfl]
  rw [ThetaF_apply]
  have hval : ↑((sndToR f y).app (op ⦋n⦌) w) =
      (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w :=
    SSet.Subcomplex.lift_app_coe _ _ w
  rw [hval]
  set xs : X _⦋n⦌ := (pullback.snd (nIndexSigma Y d y) f).app (op ⦋n⦌) w with hxs_def
  set v : ⦋n⦌ ⟶ ⦋d⦌ := SSet.stdSimplex.objEquiv
    ((pullback.fst (nIndexSigma Y d y) f).app (op ⦋n⦌) w) with hv_def
  have hcomp : Y.map v.op (nBase y) = f.app (op ⦋n⦌) xs := by
    rw [← nIndexSigma_app y v, hv_def, Equiv.symm_apply_apply]
    exact pullback_condition_apply f y n w
  by_cases hE : Epi v
  · -- Good case: the Eilenberg–Zilber data of `f xs` is `(y, v)`, so both sides are `[w]`.
    have hpos : (SSet.S.mk (f.app (op ⦋n⦌) xs)).toN.dim = d := by
      rw [← hcomp, ezFaceEpi (nBase y) (nBase_mem y) v hE]
      rfl
    rw [dif_pos hpos]
    obtain ⟨hY, hU⟩ := ezUnique f y v xs hcomp hE hpos
    have hw : pullPt f y v xs hcomp = w := pullPt_self f y w hcomp
    rw [← hw]
    exact genId_aux f y v xs hcomp hpos hY hU
  · -- Bad case: `w` lies in `∂T_y` and the `if` of `ThetaF R` is false.
    have hneg : ¬ ((SSet.S.mk (f.app (op ⦋n⦌) xs)).toN.dim = d) := by
      intro hcon
      rw [← hcomp] at hcon
      exact absurd hcon (Nat.ne_of_lt (ezFaceNonEpi (nBase y) (nBase_mem y) v hE))
    rw [dif_neg hneg]
    have hmem : w ∈ (bdryAlong f (nIndexSigma Y d y)).obj (op ⦋n⦌) := (mem_bdry_iff y w).mpr hE
    rw [← Category.assoc, iota_bdry_comp_pi_eq_zero f y w hmem, zero_comp]


/-- `Phi` is a section of `Psi`. -/
lemma mapPhi_comp_mapPsi (f : X ⟶ Y) (d : ℕ) : mapPhi R f d ≫ mapPsi R f d = 𝟙 _ := by
  apply Sigma.hom_ext
  intro y
  rw [← Category.assoc, Category.comp_id]
  rw [show Sigma.ι (fun y : nIndex Y d => pieceAlong R f (nIndexSigma Y d y)) y ≫ mapPhi R f d =
      mapPhiY R f d y from by rw [mapPhi]; exact Sigma.ι_desc _ _]
  haveI : Epi (pieceπ R f d y) := by rw [pieceπ_eq]; infer_instance
  apply (cancel_epi (pieceπ R f d y)).1
  rw [← Category.assoc, pieceπ_eq f d y, mapPhiY_apply, Category.assoc, mapPsi_toTheta]
  exact genId f d y

/-- `Psi` is a section of `Phi`. -/
lemma mapPsi_comp_mapPhi (f : X ⟶ Y) (d : ℕ) : mapPsi R f d ≫ mapPhi R f d = 𝟙 _ := by
  cases d with
  | zero =>
    rw [show mapPsi R f 0 = Theta R f 0 from rfl]
    rw [show (𝟙 _ : grF (serF R f) 0 ⟶ grF (serF R f) 0) = grFι R f 0 from by rw [grFι_zero]; rfl]
    exact Theta_comp_mapPhi f 0
  | succ k =>
    haveI : Epi (grFι R f (k+1)) := by rw [grFι_succ]; infer_instance
    apply (cancel_epi (grFι R f (k+1))).1
    rw [Category.comp_id, ← Category.assoc, mapPsi_toTheta, Theta_comp_mapPhi]

end

end Work.SSSR
