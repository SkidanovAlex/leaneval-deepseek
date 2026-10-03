import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.CovAux.union_sum_homeomorph

namespace Work.L61.CovAux

open MandelDim
open Set

/-!
# Lemma 6.1 (Shishikura §6) — `E` is a covering map on `B^u ∪ B^ℓ`

`HornData` gives the lifted horn map `d.E = Φ₀ ∘ φ₀` as a covering map over `ℂ ∖ {v + ℤ}` on
each of the two ends `Bu`, `Bl` separately (`cov_u`, `cov_l`).  Since `Bu` and `Bl` are open and
disjoint, the subspace `Bu ∪ Bl` is the topological disjoint union of the two ends, so the two
coverings glue to a covering of the same base set.

Ingredients (the first is proved here, the second in `Work.L61.CovAux.union_sum_homeomorph`):

* `isOpen_preimage_of_isEvenlyCovered`: an even covering restricts to a smaller open base set
  (this is what makes the two local trivializations above `U_u ∩ U_l` comparable);
* `union_sum_homeomorph`: `↥A ⊕ ↥B ≃ₜ ↥(A ∪ B)` for disjoint open `A B`;
* `sum_covering_surj_aux`: a coproduct of two covering maps over a common base set is again a
  covering map.

Together with `IsCoveringMapOn.comp_homeomorph_iff` (transport along the homeomorphism
`↥Bu ⊕ ↥Bl ≃ₜ ↥(Bu ∪ Bl)`) this gives the statement.
-/

/-- An even covering restricts to a smaller open base set: the preimage of the smaller set is
open.  (`H` is the homeomorphism of the even covering over `V`; the first coordinate of `H` is
`f`, so `f ⁻¹' U` is the image under the open map `↥(f ⁻¹' V) → E` of the open set of points
whose first coordinate lies in `U`.) -/
theorem isOpen_preimage_of_isEvenlyCovered {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {I : Type*} [TopologicalSpace I] {V U : Set X}
    (H : ↥(f ⁻¹' V) ≃ₜ ↥V × I) (hH : ∀ p, (H p).1.1 = f p)
    (hV : IsOpen (f ⁻¹' V)) (hU : IsOpen U) (hUV : U ⊆ V) : IsOpen (f ⁻¹' U) := by
  have hc : Continuous fun q : ↥V × I => (q.1 : X) := continuous_subtype_val.comp continuous_fst
  have hW : IsOpen {q : ↥V × I | (q.1 : X) ∈ U} := hc.isOpen_preimage U hU
  have hS : {p : ↥(f ⁻¹' V) | f p ∈ U} = H ⁻¹' {q : ↥V × I | (q.1 : X) ∈ U} := by
    ext p; rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_ofPred_eq, hH p]
  have hSimpl : IsOpen {p : ↥(f ⁻¹' V) | f p ∈ U} :=
    hS.symm ▸ (H.continuous.isOpen_preimage _ hW)
  have himg : f ⁻¹' U = Subtype.val '' {p : ↥(f ⁻¹' V) | f p ∈ U} := by
    ext a; constructor
    · intro ha; exact ⟨⟨a, hUV ha⟩, ha, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact hp
  rw [himg]
  exact hV.isOpenMap_subtype_val _ hSimpl

/-- A coproduct of two covering maps over a common base set is a covering map, assuming both
maps are surjective onto `s` (so that no fiber considered below is empty). -/
theorem sum_covering_surj_aux {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X] {f : A → X} {g : B → X} {s : Set X}
    (hf : IsCoveringMapOn f s) (hg : IsCoveringMapOn g s)
    (hf' : ∀ y ∈ s, y ∈ Set.range f) (hg' : ∀ y ∈ s, y ∈ Set.range g) :
    IsCoveringMapOn (Sum.elim f g) s := by
  intro y hy
  obtain ⟨a₀, ha₀⟩ := Set.mem_range.mp (hf' y hy)
  obtain ⟨b₀, hb₀⟩ := Set.mem_range.mp (hg' y hy)
  haveI hnf : Nonempty ↥(f ⁻¹' {y}) := ⟨⟨a₀, by simpa using ha₀⟩⟩
  haveI hng : Nonempty ↥(g ⁻¹' {y}) := ⟨⟨b₀, by simpa using hb₀⟩⟩
  have hdf : DiscreteTopology ↥(f ⁻¹' {y}) := (hf y hy).1
  have hdg : DiscreteTopology ↥(g ⁻¹' {y}) := (hg y hy).1
  set tf : Bundle.Trivialization ↥(f ⁻¹' {y}) f := (hf y hy).toTrivialization with htfdef
  set tg : Bundle.Trivialization ↥(g ⁻¹' {y}) g := (hg y hy).toTrivialization with htgdef
  have htf : y ∈ tf.baseSet := (hf y hy).mem_toTrivialization_baseSet
  have htg : y ∈ tg.baseSet := (hg y hy).mem_toTrivialization_baseSet
  set U : Set X := tf.baseSet ∩ tg.baseSet with hUdef
  have hUopen : IsOpen U := tf.open_baseSet.inter tg.open_baseSet
  have hyU : y ∈ U := ⟨htf, htg⟩
  have hUf : U ⊆ tf.baseSet := Set.inter_subset_left
  have hUg : U ⊆ tg.baseSet := Set.inter_subset_right
  have hopenVf : IsOpen (f ⁻¹' tf.baseSet) := tf.source_eq ▸ tf.open_source
  have hopenVg : IsOpen (g ⁻¹' tg.baseSet) := tg.source_eq ▸ tg.open_source
  have hpreUf : IsOpen (f ⁻¹' U) :=
    isOpen_preimage_of_isEvenlyCovered (f := f) (V := tf.baseSet) (U := U)
      (tf.preimageHomeomorph subset_rfl) (by intro p; simp) hopenVf hUopen hUf
  have hpreUg : IsOpen (g ⁻¹' U) :=
    isOpen_preimage_of_isEvenlyCovered (f := g) (V := tg.baseSet) (U := U)
      (tg.preimageHomeomorph subset_rfl) (by intro p; simp) hopenVg hUopen hUg
  set V1 : Set (A ⊕ B) := Sum.inl '' (f ⁻¹' U) with hV1def
  set V2 : Set (A ⊕ B) := Sum.inr '' (g ⁻¹' U) with hV2def
  have hV1open : IsOpen V1 := isOpenMap_inl _ hpreUf
  have hV2open : IsOpen V2 := isOpenMap_inr _ hpreUg
  have hdisj : Disjoint V1 V2 := by
    rw [Set.disjoint_left]
    rintro z ⟨a, -, rfl⟩ ⟨b, -, h⟩
    exact Sum.inl_ne_inr h.symm
  obtain ⟨e, he1, he2⟩ := union_sum_homeomorph hV1open hV2open hdisj
  have hset : V1 ∪ V2 = (Sum.elim f g) ⁻¹' U := by
    ext z; constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩) <;> assumption
    · intro hz; rcases z with a | b
      · exact Or.inl ⟨a, hz, rfl⟩
      · exact Or.inr ⟨b, hz, rfl⟩
  set e2 : ↥(V1 ∪ V2) ≃ₜ ↥((Sum.elim f g) ⁻¹' U) := Homeomorph.setCongr hset with he2def
  have hpre1 : Sum.inl ⁻¹' V1 = f ⁻¹' U := by
    ext a; constructor
    · rintro ⟨x, hx, hxa⟩
      rwa [Sum.inl_injective hxa] at hx
    · intro ha; exact ⟨a, ha, rfl⟩
  have hpre2 : Sum.inr ⁻¹' V2 = g ⁻¹' U := by
    ext b; constructor
    · rintro ⟨x, hx, hxb⟩
      rwa [Sum.inr_injective hxb] at hx
    · intro hb; exact ⟨b, hb, rfl⟩
  have hrange1 : V1 ⊆ Set.range (Sum.inl : A → A ⊕ B) := by
    rintro z ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  have hrange2 : V2 ⊆ Set.range (Sum.inr : B → A ⊕ B) := by
    rintro z ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  set q1 : ↥(f ⁻¹' U) ≃ₜ ↥V1 := (Homeomorph.setCongr hpre1.symm).trans
    (Topology.IsEmbedding.inl.homeomorphOfSubsetRange hrange1) with hq1def
  set q2 : ↥(g ⁻¹' U) ≃ₜ ↥V2 := (Homeomorph.setCongr hpre2.symm).trans
    (Topology.IsEmbedding.inr.homeomorphOfSubsetRange hrange2) with hq2def
  set p1 : ↥V1 ≃ₜ ↥(f ⁻¹' U) := q1.symm with hp1def
  set p2 : ↥V2 ≃ₜ ↥(g ⁻¹' U) := q2.symm with hp2def
  have hq1val : ∀ x : ↥(f ⁻¹' U), ((q1 x : ↥V1) : A ⊕ B) = Sum.inl (x : A) := by
    intro x
    rw [hq1def, Homeomorph.trans_apply]
    rfl
  have hq2val : ∀ x : ↥(g ⁻¹' U), ((q2 x : ↥V2) : A ⊕ B) = Sum.inr (x : B) := by
    intro x
    rw [hq2def, Homeomorph.trans_apply]
    rfl
  have hp1val : ∀ (a : A) (ha : a ∈ f ⁻¹' U),
      p1 (⟨Sum.inl a, ⟨a, ha, rfl⟩⟩ : ↥V1) = (⟨a, ha⟩ : ↥(f ⁻¹' U)) := by
    intro a ha
    rw [hp1def, Homeomorph.symm_apply_eq]
    apply Subtype.ext
    rw [hq1val]
  have hp2val : ∀ (b : B) (hb : b ∈ g ⁻¹' U),
      p2 (⟨Sum.inr b, ⟨b, hb, rfl⟩⟩ : ↥V2) = (⟨b, hb⟩ : ↥(g ⁻¹' U)) := by
    intro b hb
    rw [hp2def, Homeomorph.symm_apply_eq]
    apply Subtype.ext
    rw [hq2val]
  set Hf : ↥(f ⁻¹' U) ≃ₜ ↥U × ↥(f ⁻¹' {y}) := tf.preimageHomeomorph hUf with hHfdef
  set Hg : ↥(g ⁻¹' U) ≃ₜ ↥U × ↥(g ⁻¹' {y}) := tg.preimageHomeomorph hUg with hHgdef
  set e3 : (↥V1 ⊕ ↥V2) ≃ₜ (↥U × ↥(f ⁻¹' {y}) ⊕ ↥U × ↥(g ⁻¹' {y})) :=
    Homeomorph.sumCongr (p1.trans Hf) (p2.trans Hg) with he3def
  set e5 : (↥U × ↥(f ⁻¹' {y}) ⊕ ↥U × ↥(g ⁻¹' {y})) ≃ₜ
      ↥U × (↥(f ⁻¹' {y}) ⊕ ↥(g ⁻¹' {y})) := Homeomorph.prodSumDistrib.symm with he5def
  set H : ↥((Sum.elim f g) ⁻¹' U) ≃ₜ ↥U × (↥(f ⁻¹' {y}) ⊕ ↥(g ⁻¹' {y})) :=
    e2.symm.trans (e.symm.trans (e3.trans e5)) with hHdef
  have hproj : ∀ p : ↥((Sum.elim f g) ⁻¹' U), (H p).1.1 = Sum.elim f g p := by
    intro p
    rcases p with ⟨z, hz⟩
    rcases z with a | b
    · have hxm : e2.symm (⟨Sum.inl a, hz⟩ : ↥((Sum.elim f g) ⁻¹' U)) =
          (⟨Sum.inl a, Or.inl (⟨a, hz, rfl⟩ : Sum.inl a ∈ V1)⟩ : ↥(V1 ∪ V2)) := by
        apply Subtype.ext; rfl
      have hym : e.symm (⟨Sum.inl a, Or.inl (⟨a, hz, rfl⟩ : Sum.inl a ∈ V1)⟩ :
            ↥(V1 ∪ V2)) =
          (Sum.inl (⟨Sum.inl a, ⟨a, hz, rfl⟩⟩ : ↥V1) : ↥V1 ⊕ ↥V2) := by
        rw [Homeomorph.symm_apply_eq, he1]
      have he3a : e3 (Sum.inl (⟨Sum.inl a, ⟨a, hz, rfl⟩⟩ : ↥V1)) =
          (Sum.inl (Hf (⟨a, hz⟩ : ↥(f ⁻¹' U))) : (↥U × ↥(f ⁻¹' {y})) ⊕
            (↥U × ↥(g ⁻¹' {y}))) := by
        rw [he3def]
        show (Sum.inl ((p1.trans Hf) (⟨Sum.inl a, ⟨a, hz, rfl⟩⟩ : ↥V1)) : _) = _
        rw [Homeomorph.trans_apply, hp1val a hz]
      have he5a : (e5 (e3 (Sum.inl (⟨Sum.inl a, ⟨a, hz, rfl⟩⟩ : ↥V1)))).1.1 =
          (Hf (⟨a, hz⟩ : ↥(f ⁻¹' U))).1.1 := by
        rw [he3a, he5def]; rfl
      have hcompose : H (⟨Sum.inl a, hz⟩ : ↥((Sum.elim f g) ⁻¹' U)) =
          e5 (e3 (e.symm (e2.symm (⟨Sum.inl a, hz⟩ : ↥((Sum.elim f g) ⁻¹' U))))) := by
        simp only [hHdef, Homeomorph.trans_apply]
      rw [hcompose, hxm, hym, he5a, hHfdef]
      simp
    · have hxm : e2.symm (⟨Sum.inr b, hz⟩ : ↥((Sum.elim f g) ⁻¹' U)) =
          (⟨Sum.inr b, Or.inr (⟨b, hz, rfl⟩ : Sum.inr b ∈ V2)⟩ : ↥(V1 ∪ V2)) := by
        apply Subtype.ext; rfl
      have hym : e.symm (⟨Sum.inr b, Or.inr (⟨b, hz, rfl⟩ : Sum.inr b ∈ V2)⟩ :
            ↥(V1 ∪ V2)) =
          (Sum.inr (⟨Sum.inr b, ⟨b, hz, rfl⟩⟩ : ↥V2) : ↥V1 ⊕ ↥V2) := by
        rw [Homeomorph.symm_apply_eq, he2]
      have he3b : e3 (Sum.inr (⟨Sum.inr b, ⟨b, hz, rfl⟩⟩ : ↥V2)) =
          (Sum.inr (Hg (⟨b, hz⟩ : ↥(g ⁻¹' U))) : (↥U × ↥(f ⁻¹' {y})) ⊕
            (↥U × ↥(g ⁻¹' {y}))) := by
        rw [he3def]
        show (Sum.inr ((p2.trans Hg) (⟨Sum.inr b, ⟨b, hz, rfl⟩⟩ : ↥V2)) : _) = _
        rw [Homeomorph.trans_apply, hp2val b hz]
      have he5b : (e5 (e3 (Sum.inr (⟨Sum.inr b, ⟨b, hz, rfl⟩⟩ : ↥V2)))).1.1 =
          (Hg (⟨b, hz⟩ : ↥(g ⁻¹' U))).1.1 := by
        rw [he3b, he5def]; rfl
      have hcompose : H (⟨Sum.inr b, hz⟩ : ↥((Sum.elim f g) ⁻¹' U)) =
          e5 (e3 (e.symm (e2.symm (⟨Sum.inr b, hz⟩ : ↥((Sum.elim f g) ⁻¹' U))))) := by
        simp only [hHdef, Homeomorph.trans_apply]
      rw [hcompose, hxm, hym, he5b, hHgdef]
      simp
  have hpreopen : IsOpen ((Sum.elim f g) ⁻¹' U) := by
    rw [← hset]; exact hV1open.union hV2open
  have hev : IsEvenlyCovered (Sum.elim f g) y (↥(f ⁻¹' {y}) ⊕ ↥(g ⁻¹' {y})) :=
    ⟨inferInstance, U, hyU, hUopen, hpreopen, H, hproj⟩
  exact IsEvenlyCovered.of_fiber_homeomorph hev.fiberHomeomorph hev

theorem E_covering_union {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    (hd : MandelDim.HornData d) :
    IsCoveringMapOn (fun w : {w : ℂ // w ∈ hd.Bu ∪ hd.Bl} => d.E (w : ℂ))
      {y : ℂ | ∀ k : ℤ, y ≠ hd.v + k} := by
  obtain ⟨e, he1, he2⟩ := union_sum_homeomorph hd.Bu_open hd.Bl_open hd.disj
  have hsum : IsCoveringMapOn (Sum.elim (fun x : ↥hd.Bu => d.E x) (fun x : ↥hd.Bl => d.E x))
      {y : ℂ | ∀ k : ℤ, y ≠ hd.v + k} :=
    sum_covering_surj_aux hd.cov_u hd.cov_l
      (fun y _ => by obtain ⟨w, hw, hwy⟩ := hd.surj_u y; exact ⟨⟨w, hw⟩, hwy⟩)
      (fun y _ => by obtain ⟨w, hw, hwy⟩ := hd.surj_l y; exact ⟨⟨w, hw⟩, hwy⟩)
  have hcomp : (fun w : {w : ℂ // w ∈ hd.Bu ∪ hd.Bl} => d.E (w : ℂ)) ∘ e
      = Sum.elim (fun x : ↥hd.Bu => d.E x) (fun x : ↥hd.Bl => d.E x) := by
    funext p
    rcases p with x | x
    · simp only [Function.comp_apply, Sum.elim_inl, he1 x]
    · simp only [Function.comp_apply, Sum.elim_inr, he2 x]
  exact (IsCoveringMapOn.comp_homeomorph_iff e).mp (hcomp.symm ▸ hsum)

end Work.L61.CovAux
