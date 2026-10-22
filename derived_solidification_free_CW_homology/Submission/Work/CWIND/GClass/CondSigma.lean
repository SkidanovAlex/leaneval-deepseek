import Mathlib
import Submission.Work.CWIND.GClass.condOf_sigma

/-!
# CWIND/GClass — decomposing a section along a clopen disjoint union

Helpers for the proof that the light condensed set of a topological space presented as a clopen
disjoint union `Zt = ⋃ j, range (ι j)` is the coproduct of the light condensed sets of the pieces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightProfinite LightCondensed
open Opposite

namespace Work.CWIND.GClass

variable {J : Type} {Zt : TopCat.{0}} {Z : J → TopCat.{0}} {ι : ∀ j, Z j ⟶ Zt}

/-- The `j`-th piece of a continuous map `f` into a space presented as a clopen disjoint union. -/
def cpiece {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) (j : J) : Set (↥S) :=
  ⇑f ⁻¹' Set.range ⇑(ι j)

lemma mem_cpiece {S : LightProfinite.{0}} {f : C(↥S, ↥Zt)} {j : J} {x : ↥S} :
    x ∈ cpiece (ι := ι) f j ↔ f x ∈ Set.range ⇑(ι j) := Iff.rfl

lemma cpiece_isClopen (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) (j : J) :
    IsClopen (cpiece (ι := ι) f j) := by
  constructor
  · rw [← isOpen_compl_iff]
    have hcompl : (cpiece (ι := ι) f j)ᶜ = ⋃ k : {k : J // k ≠ j}, cpiece (ι := ι) f k.1 := by
      ext x
      rw [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (by rw [hcov]; exact Set.mem_univ (f x))
        exact ⟨⟨k, fun hkj => hx (hkj ▸ hk)⟩, hk⟩
      · rintro ⟨k, hk⟩ hj
        exact Set.disjoint_left.mp (hdisj k.2) hk hj
    rw [hcompl]
    exact isOpen_iUnion fun k => (hopen k.1).isOpen_range.preimage f.continuous
  · exact (hopen j).isOpen_range.preimage f.continuous

/-- **A section of a disjoint union restricts to a section of a piece.**  The map `condCorestrict`
below is characterised by the equation `(ι j) ∘ condCorestrict = f`. -/
lemma exists_condCorestrict (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    {T : Type*} [TopologicalSpace T] (f : C(T, ↥Zt)) (j : J)
    (h : ∀ t, f t ∈ Set.range ⇑(ι j)) : ∃ g : C(T, ↥(Z j)), (ι j).hom.comp g = f := by
  by_cases hne : Nonempty ↥(Z j)
  · haveI := hne
    have hι : Topology.IsInducing (⇑(ι j)) := (hopen j).toIsEmbedding.toIsInducing
    refine ⟨(⟨fun t => Function.invFun (⇑(ι j)) (f t), ?_⟩ : C(T, ↥(Z j))), ?_⟩
    · refine hι.continuous_iff.2 ?_
      have heq : ⇑(ι j) ∘ (fun t => Function.invFun (⇑(ι j)) (f t)) = ⇑f := by
        funext t
        exact Function.invFun_eq (h t)
      rw [heq]
      exact f.continuous
    · ext t
      exact Function.invFun_eq (h t)
  · have hT : IsEmpty T := ⟨fun t => by
      obtain ⟨z, hz⟩ := h t
      exact hne ⟨z⟩⟩
    have hcont : Continuous (fun t : T => (hT.false t).elim : T → ↥(Z j)) := by
      rw [continuous_def]
      intro s hs
      have hpre : (fun t : T => (hT.false t).elim) ⁻¹' s = (∅ : Set T) := by
        ext t
        exact (hT.false t).elim
      rw [hpre]
      exact isOpen_empty
    refine ⟨(⟨(fun t : T => (hT.false t).elim : T → ↥(Z j)), hcont⟩ : C(T, ↥(Z j))), ?_⟩
    ext t
    exact (hT.false t).elim

/-- The restriction of a section into a disjoint union to one piece. -/
noncomputable def condCorestrict (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    {T : Type*} [TopologicalSpace T] (f : C(T, ↥Zt)) (j : J)
    (h : ∀ t, f t ∈ Set.range ⇑(ι j)) : C(T, ↥(Z j)) :=
  Classical.choose (exists_condCorestrict hopen f j h)

lemma condCorestrict_spec (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    {T : Type*} [TopologicalSpace T] (f : C(T, ↥Zt)) (j : J)
    (h : ∀ t, f t ∈ Set.range ⇑(ι j)) :
    (ι j).hom.comp (condCorestrict hopen f j h) = f :=
  Classical.choose_spec (exists_condCorestrict hopen f j h)

/-- Two maps into `Z j` with the same composite with `ι j` are equal: the restriction is unique. -/
lemma condCorestrict_unique (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    {T : Type*} [TopologicalSpace T] (f : C(T, ↥Zt)) (j : J)
    (h : ∀ t, f t ∈ Set.range ⇑(ι j)) (g : C(T, ↥(Z j))) (hg : (ι j).hom.comp g = f) :
    g = condCorestrict hopen f j h := by
  ext t
  exact (hopen j).toIsEmbedding.injective
    (congrFun (congrArg DFunLike.coe (hg.trans (condCorestrict_spec hopen f j h).symm)) t)

/-- Corestriction is natural in the map: composing (on the right) with a continuous map. -/
lemma condCorestrict_comp (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']
    (f : C(T, ↥Zt)) (j : J) (h : ∀ t, f t ∈ Set.range ⇑(ι j)) (v : C(T', T)) :
    condCorestrict hopen (f.comp v) j (fun t' => h (v t')) =
      (condCorestrict hopen f j h).comp v := by
  refine (condCorestrict_unique hopen (f.comp v) j (fun t' => h (v t'))
    ((condCorestrict hopen f j h).comp v) ?_).symm
  ext t'
  exact congrFun (congrArg DFunLike.coe (condCorestrict_spec hopen f j h)) (v t')

/-- The inclusion of a piece of a section, as a continuous map. -/
def pieceIncl (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) (j : J) :
    C(↥(clopenLP S (cpiece (ι := ι) f j)
      (cpiece_isClopen hopen hdisj hcov f j)), ↥S) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The restriction of a section to one piece of its clopen decomposition. -/
noncomputable def pieceRestrict (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) (j : J) :
    C(↥(clopenLP S (cpiece (ι := ι) f j)
      (cpiece_isClopen hopen hdisj hcov f j)), ↥(Z j)) :=
  condCorestrict hopen (f.comp (pieceIncl hopen hdisj hcov f j)) j (fun x => x.2)

/-- The pieces of a section of a clopen disjoint union are covered by finitely many of them. -/
lemma exists_finset_cover (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) :
    ∃ F : Finset J, ∀ x : ↥S, ∃ j ∈ F, x ∈ cpiece (ι := ι) f j := by
  obtain ⟨F, hF⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := ↥S))
    (fun j => cpiece (ι := ι) f j) (fun j => (cpiece_isClopen hopen hdisj hcov f j).2)
    (fun x _ => by
      have hmem : f x ∈ ⋃ j, Set.range ⇑(ι j) := by rw [hcov]; exact Set.mem_univ _
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
      exact Set.mem_iUnion.2 (show ∃ j, f x ∈ Set.range ⇑(ι j) from ⟨j, hj⟩))
  refine ⟨F, fun x => ?_⟩
  have hx := hF (Set.mem_univ x)
  simpa only [Set.mem_iUnion, exists_prop] using hx

/-- The `j`-th piece of a section is empty for `j` outside a finite cover. -/
lemma cpiece_eq_empty_of_notMem (hdisj : Pairwise fun j k =>
      Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    {S : LightProfinite.{0}} {f : C(↥S, ↥Zt)} {F : Finset J}
    (hF : ∀ x : ↥S, ∃ j ∈ F, x ∈ cpiece (ι := ι) f j) {j : J} (hj : j ∉ F) :
    cpiece (ι := ι) f j = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨k, hkF, hxk⟩ := hF x
  have hkj : k ≠ j := fun h => hj (h ▸ hkF)
  exact Set.disjoint_left.mp (hdisj hkj) hxk hx

/-- **The universal property of the decomposition.**  Given sections of a light condensed set over
the pieces of a clopen disjoint union, they glue to a section over the whole space, uniquely. -/
lemma exists_glue (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) :
    ∃ y : W.obj.obj (op S), ∀ j, W.obj.map
        (clopenIncl S (cpiece (ι := ι) f j) (cpiece_isClopen hopen hdisj hcov f j)).op y =
      (φ j).hom.app (op (clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j)))
        (pieceRestrict hopen hdisj hcov f j) := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_cover hopen hdisj hcov f
  have hA : ∀ i : {j : J // j ∈ F},
      IsClopen (cpiece (ι := ι) f i.1) := fun i => cpiece_isClopen hopen hdisj hcov f i.1
  have hdisj' : Pairwise fun i k : {j : J // j ∈ F} =>
      Disjoint (cpiece (ι := ι) f i.1) (cpiece (ι := ι) f k.1) := by
    intro i k hik
    exact (hdisj (fun h => hik (Subtype.ext h))).preimage f
  have hcov' : (⋃ i : {j : J // j ∈ F}, cpiece (ι := ι) f i.1) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hjF, hxj⟩ := hF x
    exact ⟨⟨j, hjF⟩, hxj⟩
  let fam : (i : {j : J // j ∈ F}) → W.obj.obj (op (clopenLP S (cpiece (ι := ι) f i.1)
      (hA i))) := fun i => (φ i.1).hom.app (op (clopenLP S (cpiece (ι := ι) f i.1) (hA i)))
        (pieceRestrict hopen hdisj hcov f i.1)
  obtain ⟨y, hy⟩ := (restrict_bijective_of_clopen_partition
    (fun i : {j : J // j ∈ F} => cpiece (ι := ι) f i.1) hA hdisj' hcov' W).2 fam
  refine ⟨y, fun j => ?_⟩
  by_cases hj : j ∈ F
  · exact congrFun hy ⟨j, hj⟩
  · have hempty := cpiece_eq_empty_of_notMem hdisj hF hj
    haveI hE : IsEmpty ↥(clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j)) := by
      rw [show (clopenLP S (cpiece (ι := ι) f j) (cpiece_isClopen hopen hdisj hcov f j) :
        Type) = ↥(cpiece (ι := ι) f j) from rfl, hempty]
      exact ⟨fun x => x.2⟩
    haveI : Subsingleton (W.obj.obj (op (clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j)))) := subsingleton_of_isEmpty W hE
    exact Subsingleton.elim _ _

/-- Uniqueness of the glued element: two elements of `W(S)` restricting to the same sections on
the pieces of a section `f` are equal. -/
lemma glue_unique (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) {y y' : W.obj.obj (op S)}
    (hy : ∀ j, W.obj.map
        (clopenIncl S (cpiece (ι := ι) f j) (cpiece_isClopen hopen hdisj hcov f j)).op y =
      (φ j).hom.app (op (clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j))) (pieceRestrict hopen hdisj hcov f j))
    (hy' : ∀ j, W.obj.map
        (clopenIncl S (cpiece (ι := ι) f j) (cpiece_isClopen hopen hdisj hcov f j)).op y' =
      (φ j).hom.app (op (clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j))) (pieceRestrict hopen hdisj hcov f j)) :
    y = y' := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_cover hopen hdisj hcov f
  have hA : ∀ i : {j : J // j ∈ F},
      IsClopen (cpiece (ι := ι) f i.1) := fun i => cpiece_isClopen hopen hdisj hcov f i.1
  have hdisj' : Pairwise fun i k : {j : J // j ∈ F} =>
      Disjoint (cpiece (ι := ι) f i.1) (cpiece (ι := ι) f k.1) := by
    intro i k hik
    exact (hdisj (fun h => hik (Subtype.ext h))).preimage f
  have hcov' : (⋃ i : {j : J // j ∈ F}, cpiece (ι := ι) f i.1) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨j, hjF, hxj⟩ := hF x
    exact ⟨⟨j, hjF⟩, hxj⟩
  refine (restrict_bijective_of_clopen_partition
    (fun i : {j : J // j ∈ F} => cpiece (ι := ι) f i.1) hA hdisj' hcov' W).1 ?_
  funext i
  exact (hy i.1).trans (hy' i.1).symm

/-- The glued section associated to a family of sections over the pieces. -/
noncomputable def glueSec (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) : W.obj.obj (op S) :=
  Classical.choose (exists_glue hopen hdisj hcov W φ f)

lemma glueSec_spec (hopen : ∀ j, Topology.IsOpenEmbedding ⇑(ι j))
    (hdisj : Pairwise fun j k => Disjoint (Set.range ⇑(ι j)) (Set.range ⇑(ι k)))
    (hcov : (⋃ j, Set.range ⇑(ι j)) = Set.univ)
    (W : LightCondSet.{0}) (φ : ∀ j, topCatToLightCondSet.obj (Z j) ⟶ W)
    {S : LightProfinite.{0}} (f : C(↥S, ↥Zt)) (j : J) :
    W.obj.map (clopenIncl S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j)).op (glueSec hopen hdisj hcov W φ f) =
      (φ j).hom.app (op (clopenLP S (cpiece (ι := ι) f j)
        (cpiece_isClopen hopen hdisj hcov f j))) (pieceRestrict hopen hdisj hcov f j) :=
  Classical.choose_spec (exists_glue hopen hdisj hcov W φ f) j

end Work.CWIND.GClass
