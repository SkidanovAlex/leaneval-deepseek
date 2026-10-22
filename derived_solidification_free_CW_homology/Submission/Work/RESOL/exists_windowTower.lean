import Mathlib
import Submission.Work.RESOL.Basic

/-!
# Window towers of complexes

For every complex `K` of light condensed abelian groups we construct a tower of *bounded*
complexes `W 0 K ⟶ W 1 K ⟶ ⋯ ⟶ K` such that for every degree `k`, the map `W n K ⟶ K`
is a quasi-isomorphism in degree `k` as soon as `n` is large enough (uniformly in `K`).

The window `W n` is the composite of two truncations of `K`:

* `lo (-n)`: the "stupid" lower truncation, which kills all terms in degrees `< -n`
  (this is a subcomplex of `K`, hence comes with a map to `K`);
* `TL n`: Mathlib's canonical (good) truncation `≤ n`, which is bounded above and comes
  with a map `TL n K ⟶ K` which is a quasi-isomorphism in degrees `≤ n`.

The comparison maps of the tower are built from the inverses of the (canonical)
isomorphisms `TL m' (TL m K) ≅ TL m K` for `m ≤ m'`.

-/

open CategoryTheory Limits
open scoped ZeroObject

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

/-! ## Composition toolkit -/

lemma hom_comm_chain {K L : Cpx} (φ : K ⟶ L) {i j : ℤ} (hij : (ComplexShape.up ℤ).Rel i j)
    {A : LightCondAb} (f : L.X j ⟶ A) : K.d i j ≫ (φ.f j ≫ f) = φ.f i ≫ (L.d i j ≫ f) := by
  rw [← Category.assoc, ← φ.comm' i j hij, Category.assoc]

lemma d_comp_d_chain {K : Cpx} {i j k : ℤ} {A : LightCondAb} (f : K.X k ⟶ A) :
    K.d i j ≫ (K.d j k ≫ f) = 0 := by
  rw [← Category.assoc, K.d_comp_d, zero_comp]

lemma natTrans_chain {F : Cpx ⥤ Cpx} (α : F ⟶ 𝟭 Cpx) {X Y W : Cpx} (f : X ⟶ Y)
    (g : Y ⟶ W) : F.map f ≫ (α.app Y ≫ g) = α.app X ≫ (f ≫ g) := by
  rw [← Category.assoc, α.naturality, Category.assoc, Functor.id_map]

lemma inv_hom_chain {D : Type*} [Category* D] {A B Z : D} (f : A ⟶ B) [IsIso f]
    (g : B ⟶ Z) : inv f ≫ (f ≫ g) = g := by
  rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-! ## The stupid lower truncation -/

/-- The `i`-th term of the stupid lower truncation at level `a`. -/
noncomputable abbrev loX (a : ℤ) (K : Cpx) (i : ℤ) : LightCondAb :=
  if a ≤ i then K.X i else 0

/-- The transport from the truncated term to the original one. -/
noncomputable def loT (a : ℤ) (K : Cpx) (i : ℤ) : loX a K i ⟶ K.X i :=
  if h : a ≤ i then eqToHom (ite_eq_left h) else 0

/-- The transport from the original term to the truncated one. -/
noncomputable def loTi (a : ℤ) (K : Cpx) (i : ℤ) : K.X i ⟶ loX a K i :=
  if h : a ≤ i then eqToHom ((ite_eq_left h).symm) else 0

lemma loT_eq (a : ℤ) (K : Cpx) (i : ℤ) (h : a ≤ i) :
    loT a K i = eqToHom (ite_eq_left h) := dite_eq_left h

lemma loT_eq_zero (a : ℤ) (K : Cpx) (i : ℤ) (h : ¬ a ≤ i) : loT a K i = 0 :=
  dite_eq_right h

lemma loTi_eq (a : ℤ) (K : Cpx) (i : ℤ) (h : a ≤ i) :
    loTi a K i = eqToHom ((ite_eq_left h).symm) := dite_eq_left h

lemma loTi_eq_zero (a : ℤ) (K : Cpx) (i : ℤ) (h : ¬ a ≤ i) : loTi a K i = 0 :=
  dite_eq_right h

lemma isIso_loT (a : ℤ) (K : Cpx) {i : ℤ} (h : a ≤ i) : IsIso (loT a K i) := by
  rw [loT_eq a K i h]
  exact (eqToIso (ite_eq_left h)).isIso_hom

lemma loT_loTi_id (a : ℤ) (K : Cpx) {i : ℤ} (h : a ≤ i) :
    loT a K i ≫ loTi a K i = 𝟙 (loX a K i) := by
  rw [loT_eq a K i h, loTi_eq a K i h]
  exact Iso.hom_inv_id (eqToIso (ite_eq_left h))

lemma loTi_loT_id (a : ℤ) (K : Cpx) {i : ℤ} (h : a ≤ i) :
    loTi a K i ≫ loT a K i = 𝟙 (K.X i) := by
  rw [loTi_eq a K i h, loT_eq a K i h]
  exact Iso.inv_hom_id (eqToIso (ite_eq_left h))

lemma loTi_loT_chain (a : ℤ) (K : Cpx) {i : ℤ} (h : a ≤ i) {B : LightCondAb}
    (g : K.X i ⟶ B) : loTi a K i ≫ (loT a K i ≫ g) = g := by
  rw [← Category.assoc, loTi_loT_id a K h, Category.id_comp]

/-- The stupid lower truncation of a cochain complex at level `a`: the subcomplex consisting
of the terms in degrees `≥ a`. -/
noncomputable abbrev loObj (a : ℤ) (K : Cpx) : Cpx where
  X i := loX a K i
  d i j := loT a K i ≫ (K.d i j ≫ loTi a K j)
  shape i j hij := by
    rw [K.shape i j hij]
    simp
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hle : i ≤ j := by omega
    by_cases h : a ≤ i
    · have hj : a ≤ j := le_trans h hle
      simp only [Category.assoc]
      rw [loTi_loT_chain a K hj (K.d j k ≫ loTi a K k),
        d_comp_d_chain (K := K) (i := i) (j := j) (k := k) (loTi a K k), comp_zero]
    · simp only [loT_eq_zero a K i h, Category.assoc, zero_comp, comp_zero]

lemma loObj_d (a : ℤ) (K : Cpx) (i j : ℤ) :
    (loObj a K).d i j = loT a K i ≫ (K.d i j ≫ loTi a K j) := rfl

lemma isZero_loObj_X (a : ℤ) (K : Cpx) {i : ℤ} (h : i < a) :
    IsZero ((loObj a K).X i) := by
  show IsZero (loX a K i)
  rw [show (loX a K i) = 0 from dite_eq_right (by omega)]
  exact Limits.isZero_zero _

/-- The map of stupid lower truncations induced by a morphism of complexes. -/
noncomputable abbrev loMap {a : ℤ} {K L : Cpx} (f : K ⟶ L) : loObj a K ⟶ loObj a L where
  f i := loT a K i ≫ (f.f i ≫ loTi a L i)
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    have hle : i ≤ j := by omega
    by_cases h : a ≤ i
    · have hj : a ≤ j := le_trans h hle
      show (loT a K i ≫ (f.f i ≫ loTi a L i)) ≫ (loT a L i ≫ (L.d i j ≫ loTi a L j)) =
        (loT a K i ≫ (K.d i j ≫ loTi a K j)) ≫ (loT a K j ≫ (f.f j ≫ loTi a L j))
      simp only [Category.assoc]
      rw [loTi_loT_chain a L h (L.d i j ≫ loTi a L j),
        loTi_loT_chain a K hj (f.f j ≫ loTi a L j),
        ← hom_comm_chain f hij (loTi a L j)]
    · simp only [loT_eq_zero a K i h, Category.assoc, zero_comp, comp_zero]

lemma loMap_f {a : ℤ} {K L : Cpx} (f : K ⟶ L) (i : ℤ) :
    (loMap f).f i = loT a K i ≫ (f.f i ≫ loTi a L i) := rfl

/-- The stupid lower truncation, as an endofunctor of complexes. -/
noncomputable abbrev lo (a : ℤ) : Cpx ⥤ Cpx where
  obj K := loObj a K
  map f := loMap f
  map_id K := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [loMap_f, HomologicalComplex.id_f, HomologicalComplex.id_f]
    by_cases h : a ≤ i
    · rw [Category.id_comp]
      exact loT_loTi_id a K h
    · simp only [loT_eq_zero a K i h, zero_comp]
      exact (isZero_loObj_X a K (by omega)).eq_of_src _ _
  map_comp {K L M} f g := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [HomologicalComplex.comp_f, loMap_f, loMap_f, loMap_f, HomologicalComplex.comp_f]
    by_cases h : a ≤ i
    · simp only [Category.assoc]
      rw [loTi_loT_chain a L h (g.f i ≫ loTi a M i)]
    · simp only [loT_eq_zero a K i h, zero_comp, comp_zero]

/-- The canonical map `lo a K ⟶ K` (the inclusion of the subcomplex). -/
noncomputable def loId (a : ℤ) : lo a ⟶ 𝟭 Cpx where
  app K :=
    { f i := loT a K i
      comm' i j hij := by
        have hij' : i + 1 = j := hij
        have hle : i ≤ j := by omega
        by_cases h : a ≤ i
        · have hj : a ≤ j := le_trans h hle
          show loT a K i ≫ K.d i j = (loT a K i ≫ (K.d i j ≫ loTi a K j)) ≫ loT a K j
          simp only [Category.assoc]
          rw [loTi_loT_id a K hj, Category.comp_id]
        · simp only [loT_eq_zero a K i h, Category.assoc, zero_comp, comp_zero] }
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases h : a ≤ i
    · show (loT a K i ≫ (f.f i ≫ loTi a L i)) ≫ loT a L i = loT a K i ≫ f.f i
      simp only [Category.assoc]
      rw [loTi_loT_id a L h, Category.comp_id]
    · show (loT a K i ≫ (f.f i ≫ loTi a L i)) ≫ loT a L i = loT a K i ≫ f.f i
      simp only [loT_eq_zero a K i h, zero_comp, comp_zero]

lemma loId_f (a : ℤ) (K : Cpx) (i : ℤ) : ((loId a).app K).f i = loT a K i := rfl

/-- The canonical map `lo a K ⟶ lo b K` for `b ≤ a`. -/
noncomputable def loLe (a b : ℤ) (h : b ≤ a) : lo a ⟶ lo b where
  app K :=
    { f i := loT a K i ≫ loTi b K i
      comm' i j hij := by
        have hij' : i + 1 = j := hij
        have hle : i ≤ j := by omega
        by_cases h' : a ≤ i
        · have hj : a ≤ j := le_trans h' hle
          show (loT a K i ≫ loTi b K i) ≫ (loT b K i ≫ (K.d i j ≫ loTi b K j)) =
            (loT a K i ≫ (K.d i j ≫ loTi a K j)) ≫ (loT a K j ≫ loTi b K j)
          simp only [Category.assoc]
          rw [loTi_loT_chain b K (le_trans h h') (K.d i j ≫ loTi b K j),
            loTi_loT_chain a K hj (loTi b K j)]
        · simp only [loT_eq_zero a K i h', Category.assoc, zero_comp, comp_zero] }
  naturality K L f := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases h' : a ≤ i
    · show (loT a K i ≫ (f.f i ≫ loTi a L i)) ≫ (loT a L i ≫ loTi b L i) =
        (loT a K i ≫ loTi b K i) ≫ (loT b K i ≫ (f.f i ≫ loTi b L i))
      simp only [Category.assoc]
      rw [loTi_loT_chain a L h' (loTi b L i),
        loTi_loT_chain b K (le_trans h h') (f.f i ≫ loTi b L i)]
    · show (loT a K i ≫ (f.f i ≫ loTi a L i)) ≫ (loT a L i ≫ loTi b L i) =
        (loT a K i ≫ loTi b K i) ≫ (loT b K i ≫ (f.f i ≫ loTi b L i))
      simp only [loT_eq_zero a K i h', zero_comp, comp_zero]

lemma loLe_f (a b : ℤ) (h : b ≤ a) (K : Cpx) (i : ℤ) :
    ((loLe a b h).app K).f i = loT a K i ≫ loTi b K i := rfl

lemma loLe_loId (a b : ℤ) (h : b ≤ a) : loLe a b h ≫ loId b = loId a := by
  apply NatTrans.ext
  funext K
  rw [NatTrans.comp_app]
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h' : a ≤ i
  · show (loT a K i ≫ loTi b K i) ≫ loT b K i = loT a K i
    simp only [Category.assoc]
    rw [loTi_loT_id b K (le_trans h h'), Category.comp_id]
  · show (loT a K i ≫ loTi b K i) ≫ loT b K i = loT a K i
    simp only [loT_eq_zero a K i h', zero_comp, comp_zero]

lemma loLe_loId_app (a b : ℤ) (h : b ≤ a) (K : Cpx) :
    ((loLe a b h).app K) ≫ ((loId b).app K) = (loId a).app K :=
  congrArg (fun (f : lo a ⟶ 𝟭 Cpx) => f.app K) (loLe_loId a b h)

lemma isBoundedBelow_lo (a : ℤ) (K : Cpx) : IsBoundedBelow ((lo a).obj K) :=
  ⟨a, fun i hi => isZero_loObj_X a K hi⟩

/-! ## Quasi-isomorphisms in one degree -/

/-- A morphism of complexes which is an isomorphism in degrees `k - 1`, `k` and `k + 1` is a
quasi-isomorphism in degree `k`. -/
lemma quasiIsoAt_of_isIso_f {K L : Cpx} (f : K ⟶ L) (k : ℤ)
    (h1 : IsIso (f.f (k-1))) (h2 : IsIso (f.f k)) (h3 : IsIso (f.f (k+1))) :
    QuasiIsoAt f k := by
  rw [quasiIsoAt_iff' f (k-1) k (k+1)
    (ComplexShape.prev_eq' (ComplexShape.up ℤ) (ComplexShape.up_mk (k-1) k (by omega)))
    (ComplexShape.next_eq' (ComplexShape.up ℤ) (ComplexShape.up_mk k (k+1) rfl))]
  have hφ : IsIso ((HomologicalComplex.shortComplexFunctor' LightCondAb
      (ComplexShape.up ℤ) (k-1) k (k+1)).map f) := by
    rw [ShortComplex.isIso_iff]
    refine ⟨?_, ?_, ?_⟩
    · change IsIso (f.f (k-1)); exact h1
    · change IsIso (f.f k); exact h2
    · change IsIso (f.f (k+1)); exact h3
  exact ShortComplex.quasiIso_of_isIso _

lemma quasiIsoAt_loId (a : ℤ) (K : Cpx) (k : ℤ) (h : a < k) :
    QuasiIsoAt ((loId a).app K) k := by
  refine quasiIsoAt_of_isIso_f _ k ?_ ?_ ?_
  · rw [loId_f]; exact isIso_loT a K (by omega)
  · rw [loId_f]; exact isIso_loT a K (by omega)
  · rw [loId_f]; exact isIso_loT a K (by omega)

/-! ## Mathlib's canonical truncation `≤ m` -/

noncomputable abbrev TLF (m : ℤ) : Cpx ⥤ Cpx :=
  ComplexShape.Embedding.truncLEFunctor (ComplexShape.embeddingUpIntLE m) LightCondAb

noncomputable abbrev TLNat (m : ℤ) : TLF m ⟶ 𝟭 Cpx :=
  ComplexShape.Embedding.ιTruncLENatTrans (ComplexShape.embeddingUpIntLE m) LightCondAb

lemma isStrictlySupported_TLF (m m' : ℤ) (h : m ≤ m') (X : Cpx) :
    HomologicalComplex.IsStrictlySupported ((TLF m).obj X)
      (ComplexShape.embeddingUpIntLE m') := by
  refine HomologicalComplex.IsStrictlySupported.mk (fun i' hi' => ?_)
  rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hi'
  exact HomologicalComplex.isZero_X_of_isStrictlySupported (X.truncLE m)
    (ComplexShape.embeddingUpIntLE m) i'
    (fun k => by rw [ComplexShape.embeddingUpIntLE_f]; omega)

noncomputable abbrev TLWh (m m' : ℤ) : TLF m ⋙ TLF m' ⟶ TLF m :=
  Functor.whiskerLeft (TLF m) (TLNat m')

lemma isIso_TLWh (m m' : ℤ) (h : m ≤ m') : IsIso (TLWh m m') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  haveI : HomologicalComplex.IsStrictlySupported ((TLF m).obj X)
      (ComplexShape.embeddingUpIntLE m') :=
    isStrictlySupported_TLF m m' h X
  rw [TLWh, Functor.whiskerLeft_app, ComplexShape.Embedding.ιTruncLENatTrans_app]
  exact inferInstance

lemma whiskerRight_TLNat (m m' : ℤ) :
    (Functor.whiskerRight (TLNat m) (TLF m') : TLF m ⋙ TLF m' ⟶ TLF m') ≫ TLNat m' =
      TLWh m m' ≫ TLNat m := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, TLWh,
    Functor.id_obj, Functor.id_map]
  exact (TLNat m').naturality ((TLNat m).app X)

/-- The canonical map `TLF m ⟶ TLF m'` for `m ≤ m'`, which is a section of `TLNat m'`. -/
noncomputable def TLup (m m' : ℤ) (h : m ≤ m') : TLF m ⟶ TLF m' :=
  haveI := isIso_TLWh m m' h
  inv (TLWh m m') ≫ Functor.whiskerRight (TLNat m) (TLF m')

lemma TLup_TLNat (m m' : ℤ) (h : m ≤ m') : TLup m m' h ≫ TLNat m' = TLNat m := by
  haveI := isIso_TLWh m m' h
  rw [TLup, Category.assoc, whiskerRight_TLNat, inv_hom_chain]

lemma TLup_TLNat_chain (m m' : ℤ) (h : m ≤ m') {X W : Cpx} (Y : X ⟶ W) :
    (TLup m m' h).app X ≫ ((TLNat m').app X ≫ Y) = (TLNat m).app X ≫ Y := by
  rw [← Category.assoc, ← NatTrans.comp_app, TLup_TLNat]

lemma isStrictlyLE_TLF (m : ℤ) (X : Cpx) : CochainComplex.IsStrictlyLE ((TLF m).obj X) m :=
  inferInstanceAs (HomologicalComplex.IsStrictlySupported (X.truncLE m)
    (ComplexShape.embeddingUpIntLE m))

lemma isZero_TLF_le (m : ℤ) (X : Cpx) {i : ℤ} (hi : m < i) :
    IsZero ((TLF m).obj X |>.X i) := by
  haveI := isStrictlyLE_TLF m X
  exact CochainComplex.isZero_of_isStrictlyLE ((TLF m).obj X) m i hi

lemma isZero_TLF_below (a m : ℤ) (K : Cpx) (ha : a ≤ m) {i : ℤ} (hi : i < a) :
    IsZero ((TLF m).obj ((lo a).obj K) |>.X i) := by
  have hi' : i < m := by omega
  exact IsZero.of_iso (isZero_loObj_X a K hi)
    (CochainComplex.truncLEXIso ((lo a).obj K) m i hi')

/-! ## The tower -/

/-- The `n`-th window functor. -/
noncomputable abbrev W (n : ℕ) : Cpx ⥤ Cpx := lo (-(n:ℤ)) ⋙ TLF (n:ℤ)

/-- The map from the `n`-th window to `K`. -/
noncomputable def wto (n : ℕ) : W n ⟶ 𝟭 Cpx :=
  Functor.whiskerLeft (lo (-(n:ℤ))) (TLNat (n:ℤ)) ≫ loId (-(n:ℤ))

/-- The transition maps of the tower. -/
noncomputable def wtr (n : ℕ) : W n ⟶ W (n+1) :=
  Functor.whiskerRight (loLe (-(n:ℤ)) (-((n+1:ℕ):ℤ)) (by push_cast; omega)) (TLF (n:ℤ)) ≫
    Functor.whiskerLeft (lo (-((n+1:ℕ):ℤ)))
      (TLup (n:ℤ) ((n+1:ℕ):ℤ) (by push_cast; omega))

lemma wto_app (n : ℕ) (K : Cpx) :
    (wto n).app K = (TLNat (n:ℤ)).app ((lo (-(n:ℤ))).obj K) ≫ (loId (-(n:ℤ))).app K := by
  rw [wto, NatTrans.comp_app, Functor.whiskerLeft_app]

lemma wtr_app (n : ℕ) (K : Cpx) :
    (wtr n).app K =
      (TLF (n:ℤ)).map ((loLe (-(n:ℤ)) (-((n+1:ℕ):ℤ)) (by push_cast; omega)).app K) ≫
        (TLup (n:ℤ) ((n+1:ℕ):ℤ) (by push_cast; omega)).app ((lo (-((n+1:ℕ):ℤ))).obj K) := by
  rw [wtr, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]

lemma wtr_wto (n : ℕ) : wtr n ≫ wto (n+1) = wto n := by
  apply NatTrans.ext
  funext K
  rw [NatTrans.comp_app, wto_app, wto_app, wtr_app]
  simp only [Category.assoc]
  rw [TLup_TLNat_chain (n:ℤ) ((n+1:ℕ):ℤ) (by push_cast; omega)
      ((loId (-((n+1:ℕ):ℤ))).app K),
    natTrans_chain (TLNat (n:ℤ))
      ((loLe (-(n:ℤ)) (-((n+1:ℕ):ℤ)) (by push_cast; omega)).app K)
      ((loId (-((n+1:ℕ):ℤ))).app K),
    loLe_loId_app]

lemma isBoundedAbove_W (n : ℕ) (K : Cpx) : IsBoundedAbove ((W n).obj K) :=
  ⟨(n:ℤ), fun i hi => isZero_TLF_le (n:ℤ) ((lo (-(n:ℤ))).obj K) hi⟩

lemma isBoundedBelow_W (n : ℕ) (K : Cpx) : IsBoundedBelow ((W n).obj K) :=
  ⟨-(n:ℤ), fun i hi => isZero_TLF_below (-(n:ℤ)) (n:ℤ) K (by omega) hi⟩

lemma quasiIsoAt_wto (n : ℕ) (K : Cpx) (k : ℤ) (h1 : k ≤ (n:ℤ)) (h2 : -(n:ℤ) < k) :
    QuasiIsoAt ((wto n).app K) k := by
  rw [wto_app]
  haveI : QuasiIsoAt ((TLNat (n:ℤ)).app ((lo (-(n:ℤ))).obj K)) k := by
    show QuasiIsoAt (HomologicalComplex.ιTruncLE ((lo (-(n:ℤ))).obj K)
      (ComplexShape.embeddingUpIntLE (n:ℤ))) k
    exact CochainComplex.quasiIsoAt_ιTruncLE ((lo (-(n:ℤ))).obj K) (n:ℤ) k h1
  haveI : QuasiIsoAt ((loId (-(n:ℤ))).app K) k := quasiIsoAt_loId (-(n:ℤ)) K k h2
  infer_instance

theorem exists_windowTower :
    ∃ (W : ℕ → CategoryTheory.Functor Work.RESOL.Cpx Work.RESOL.Cpx)
      (wtr : ∀ n : ℕ, W n ⟶ W (n+1))
      (wto : ∀ n : ℕ, W n ⟶ CategoryTheory.Functor.id Work.RESOL.Cpx),
      (∀ (n : ℕ) (K : Work.RESOL.Cpx),
        Work.RESOL.IsBoundedAbove ((W n).obj K) ∧ Work.RESOL.IsBoundedBelow ((W n).obj K)) ∧
      (∀ (n : ℕ) (K : Work.RESOL.Cpx),
        CategoryTheory.CategoryStruct.comp ((wtr n).app K) ((wto (n+1)).app K) =
          (wto n).app K) ∧
      (∀ k : ℤ, ∃ N : ℕ, ∀ n ≥ N, ∀ K : Work.RESOL.Cpx, QuasiIsoAt ((wto n).app K) k) := by
  refine ⟨Work.RESOL.W, Work.RESOL.wtr, Work.RESOL.wto, ?_, ?_, ?_⟩
  · intro n K
    exact ⟨Work.RESOL.isBoundedAbove_W n K, Work.RESOL.isBoundedBelow_W n K⟩
  · intro n K
    have h := Work.RESOL.wtr_wto n
    exact congrArg (fun (f : Work.RESOL.W n ⟶ CategoryTheory.Functor.id Work.RESOL.Cpx) =>
      f.app K) h
  · intro k
    refine ⟨k.natAbs + 2, fun n hn K => ?_⟩
    have hc : ((k.natAbs : ℤ) + 2 ≤ (n : ℤ)) := by
      have h : ((k.natAbs + 2 : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      simpa using h
    refine Work.RESOL.quasiIsoAt_wto n K k ?_ ?_
    · have h1 : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
      omega
    · have h1 : -k ≤ (k.natAbs : ℤ) := by
        have h2 : -k ≤ ((-k).natAbs : ℤ) := Int.le_natAbs
        rwa [Int.natAbs_neg] at h2
      omega

end Work.RESOL
