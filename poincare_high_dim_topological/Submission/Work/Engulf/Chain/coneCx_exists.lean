import Mathlib
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Basic
import Submission.Work.PL.Generic.domDim_join_step

/-!
# `Work.Engulf.Chain.coneCx_exists` — the cone complex `Γ ∪ a ∗ σ` of Newman §12

The target lemma is `coneCx_exists` at the bottom of this file: if `σ` is a face of the
simplicial complex `Γ` and `a` lies outside `⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)`, then the
collection `coneFaces Γ σ a` of finsets (`Γ.faces` together with the cones `insert a s` over the
faces `s ⊆ σ`, `s = ∅` giving the apex `{a}`) is the face set of a simplicial complex.

The proof is the elementary one sketched in the statement's docstring, assembled from

* affine independence of a simplex plus an outside apex (`affineIndependent_insert`);
* the two "glue nicely" facts for cones (`simp_insert_inter_simp_of_notMem`,
  `simp_insert_inter_simp_insert`) — a point common to two cones must have equal apex weights,
  else the apex lies in the affine span of the two bases;
* downward closure of `coneFaces Γ σ a ∪ {∅}`.

The construction itself is `Geometry.SimplicialComplex.ofErase` (the empty face is adjoined
precisely so that `ofErase`, which removes it again, applies).
-/

open Set Metric PL

namespace Work.Engulf.Chain

variable {N : ℕ}

/-! ## The glue lemmas for cones

(These are `H1`/`H2` of the cone development; `Work.PL.Generic.mem_affineSpan_union_of_mem_simp_insert`
is the join-decomposition input, `Work.Engulf.simp_inter` the inherited glue condition.) -/

theorem insert_eq_union_singleton (u : Finset (E N)) (a : E N) : insert a u = u ∪ {a} := by
  rw [Finset.insert_eq, Finset.union_comm]

theorem simp_insert_eq_simp_union_singleton (u : Finset (E N)) (a : E N) :
    simp (insert a u) = simp (u ∪ {a}) := by
  rw [insert_eq_union_singleton]

/-- **H1** (cone vs old face): if `u` and `s` glue nicely and the apex `a` is outside
`affineSpan (u ∪ s)`, then the cone on `u` with apex `a` meets `simp s` in `simp (u ∩ s)`. -/
theorem simp_insert_inter_simp_of_notMem {u s : Finset (E N)} {a : E N}
    (hglue : simp u ∩ simp s ⊆ simp (u ∩ s))
    (ha : a ∉ affineSpan ℝ ((u ∪ s : Finset (E N)) : Set (E N))) :
    simp (insert a u) ∩ simp s ⊆ simp (u ∩ s) := by
  intro x hx
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  by_cases hxu : x ∈ simp u
  · exact hglue ⟨hxu, hx2⟩
  · exfalso
    have hx1' : x ∈ simp (u ∪ {a}) := by
      rw [← simp_insert_eq_simp_union_singleton]; exact hx1
    have hmem := Work.PL.Generic.mem_affineSpan_union_of_mem_simp_insert
      (s := u) (σ := s) (y := a) (x := x) hx1' hxu hx2
    exact ha (by simpa [Finset.coe_union] using hmem)

/-- **H2** (cone vs cone): two cones with the same apex over nicely gluing bases meet in the cone
over the intersection of the bases. -/
theorem simp_insert_inter_simp_insert {u v : Finset (E N)} {a : E N}
    (hglue : simp u ∩ simp v ⊆ simp (u ∩ v))
    (ha : a ∉ affineSpan ℝ ((u ∪ v : Finset (E N)) : Set (E N))) :
    simp (insert a u) ∩ simp (insert a v) ⊆ simp (insert a (u ∩ v)) := by
  intro x hx
  rw [Set.mem_inter_iff] at hx
  obtain ⟨hxu, hxv⟩ := hx
  have hmono : simp (u ∩ v) ⊆ simp (insert a (u ∩ v)) :=
    simp_mono (Finset.subset_insert a (u ∩ v))
  rcases eq_or_ne u ∅ with rfl | hu0
  · rw [Finset.empty_inter]
    exact hxu
  rcases eq_or_ne v ∅ with rfl | hv0
  · rw [Finset.inter_empty]
    exact hxv
  have hun : u.Nonempty := Finset.nonempty_iff_ne_empty.2 hu0
  have hvn : v.Nonempty := Finset.nonempty_iff_ne_empty.2 hv0
  have hxu' : x ∈ simp (u ∪ {a}) := by
    rw [← simp_insert_eq_simp_union_singleton]; exact hxu
  have hxv' : x ∈ simp (v ∪ {a}) := by
    rw [← simp_insert_eq_simp_union_singleton]; exact hxv
  by_cases hxu'' : x ∈ simp u
  · have hglue' : simp v ∩ simp u ⊆ simp (v ∩ u) := by
      rw [Set.inter_comm (simp v) (simp u),
        show v ∩ u = u ∩ v from Finset.inter_comm v u]
      exact hglue
    have ha' : a ∉ affineSpan ℝ ((v ∪ u : Finset (E N)) : Set (E N)) := by
      rw [Finset.union_comm v u]; exact ha
    have hmem : x ∈ simp (v ∩ u) :=
      simp_insert_inter_simp_of_notMem (u := v) (s := u) hglue' ha' ⟨hxv, hxu''⟩
    rw [show v ∩ u = u ∩ v from Finset.inter_comm v u] at hmem
    exact hmono hmem
  by_cases hxv'' : x ∈ simp v
  · exact hmono (simp_insert_inter_simp_of_notMem (u := u) (s := v) hglue ha ⟨hxu, hxv''⟩)
  · obtain ⟨μ, hμ, p, hp, hxp⟩ :=
      Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert (s := u) (y := a) hun hxu' hxu''
    obtain ⟨ν, hν, q, hq, hxq⟩ :=
      Work.PL.Generic.exists_ioc_smul_add_of_mem_convexHull_insert (s := v) (y := a) hvn hxv' hxv''
    rcases eq_or_ne μ ν with hμν | hμν
    · have hpq : (1 - ν) • p = (1 - ν) • q := by
        have h0 : (1 - μ) • p + μ • a = (1 - ν) • q + ν • a := by rw [← hxp, ← hxq]
        rw [hμν] at h0
        exact add_right_cancel h0
      rcases eq_or_ne ν 1 with hν1 | hν1
      · have hxa : x = a := by rw [hxq, hν1]; simp
        rw [hxa]
        exact subset_convexHull ℝ ((insert a (u ∩ v) : Finset (E N)) : Set (E N)) (by simp)
      · have h1ν : (1 - ν) ≠ 0 := fun h => hν1 (by linarith)
        have hpq' : p = q := by
          have hc := congrArg (fun z => (1 - ν)⁻¹ • z) hpq
          rw [smul_smul, smul_smul, inv_mul_cancel₀ h1ν, one_smul, one_smul] at hc
          exact hc
        have hpuv : p ∈ simp (u ∩ v) := hglue ⟨hp, by rw [hpq']; exact hq⟩
        have hp' : p ∈ simp (insert a (u ∩ v)) := hmono hpuv
        have ha' : a ∈ simp (insert a (u ∩ v)) :=
          subset_convexHull ℝ ((insert a (u ∩ v) : Finset (E N)) : Set (E N)) (by simp)
        have hν0 : 0 ≤ ν := le_of_lt hν.1
        have h1ν' : 0 ≤ 1 - ν := by linarith [hν.2]
        have hsum : ν + (1 - ν) = 1 := by ring
        have hmem : ν • a + (1 - ν) • p ∈ simp (insert a (u ∩ v)) :=
          (convex_convexHull ℝ ((insert a (u ∩ v) : Finset (E N)) : Set (E N)))
            ha' hp' hν0 h1ν' hsum
        have hxp' : x = (1 - ν) • p + ν • a := by rw [hxp, hμν]
        rw [hxp', add_comm]
        exact hmem
    · exfalso
      have h0 : (1 - μ) • p + μ • a = (1 - ν) • q + ν • a := by rw [← hxp, ← hxq]
      have hrel : (μ - ν) • a = (1 - ν) • q - (1 - μ) • p := by
        have h1 : μ • a - ν • a = (1 - ν) • q - (1 - μ) • p := by
          calc μ • a - ν • a
              = ((1 - μ) • p + μ • a) - ((1 - μ) • p + ν • a) := by abel
            _ = ((1 - ν) • q + ν • a) - ((1 - μ) • p + ν • a) := by rw [h0]
            _ = (1 - ν) • q - (1 - μ) • p := by abel
        rw [sub_smul]; exact h1
      have hca : μ - ν ≠ 0 := sub_ne_zero.mpr hμν
      have hkey : (μ - ν) • (p +ᵥ (((1 - ν) / (μ - ν)) • (q -ᵥ p)))
          = (1 - ν) • q - (1 - μ) • p := by
        rw [vsub_eq_sub, vadd_eq_add]
        simp only [smul_add, smul_sub, smul_smul]
        match_scalars <;> field_simp <;> ring
      have hfin : a = p +ᵥ (((1 - ν) / (μ - ν)) • (q -ᵥ p)) :=
        (smul_right_inj (r := μ - ν) hca).mp (by rw [hkey, hrel])
      have hpQ : p ∈ affineSpan ℝ ((u : Set (E N)) ∪ (v : Set (E N))) :=
        (affineSpan_mono ℝ (Set.subset_union_left)) (simp_subset_affineSpan u hp)
      have hqQ : q ∈ affineSpan ℝ ((u : Set (E N)) ∪ (v : Set (E N))) :=
        (affineSpan_mono ℝ (Set.subset_union_right)) (simp_subset_affineSpan v hq)
      have hmem := Work.PL.Generic.affineSubspace_add_smul_vsub_mem
        (affineSpan ℝ ((u : Set (E N)) ∪ (v : Set (E N)))) hpQ hqQ ((1 - ν) / (μ - ν))
      rw [← hfin] at hmem
      exact ha (by simpa [Finset.coe_union] using hmem)

/-! ## Affine independence of a simplex plus an apex outside its affine span -/

/-- A simplex together with an apex outside its affine span is affinely independent. -/
theorem affineIndependent_insert {u : Finset (E N)} {a : E N}
    (hu : AffineIndependent ℝ (fun v : u => (v : E N)))
    (ha : a ∉ affineSpan ℝ (u : Set (E N))) :
    AffineIndependent ℝ (fun v : (insert a u : Finset (E N)) => (v : E N)) := by
  have hau : a ∉ u := by
    intro h
    exact ha (subset_affineSpan ℝ (u : Set (E N)) (by simpa using h))
  let i : (insert a u : Finset (E N)) := ⟨a, Finset.mem_insert_self a u⟩
  let e : u ≃ { y : (insert a u : Finset (E N)) // y ≠ i } :=
    { toFun := fun t => ⟨⟨t.1, Finset.mem_insert_of_mem t.2⟩,
        fun h => hau (by
          have h' : (t : E N) = a := by simpa [i] using Subtype.ext_iff.mp h
          exact h' ▸ t.2)⟩
      invFun := fun y => ⟨y.1.1, by
        rcases Finset.mem_insert.mp y.1.2 with h | h
        · exact absurd (Subtype.ext h) y.2
        · exact h⟩
      left_inv := fun t => by ext; rfl
      right_inv := fun y => by ext; rfl }
  have h1 : AffineIndependent ℝ
      (fun x : { y : (insert a u : Finset (E N)) // y ≠ i } => (x : E N)) :=
    (affineIndependent_equiv e
      (p := fun x : { y : (insert a u : Finset (E N)) // y ≠ i } => (x : E N))).mp hu
  have hset : (fun v : (insert a u : Finset (E N)) => (v : E N)) '' {x | x ≠ i}
      = (u : Set (E N)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Finset.mem_insert.mp x.2 with h | h
      · exact absurd (Subtype.ext h) hx
      · exact h
    · intro hy
      exact ⟨⟨y, Finset.mem_insert_of_mem hy⟩, fun h => hau (by
        have h' : y = a := by simpa [i] using Subtype.ext_iff.mp h
        exact h' ▸ hy), rfl⟩
  refine AffineIndependent.affineIndependent_of_notMem_span (k := ℝ) (i := i) h1 ?_
  rw [hset]
  simpa using ha

/-! ## Downward closure of `coneFaces Γ σ a ∪ {∅}` -/

theorem subsingleton_finset_of_card_le_one {s : Finset (E N)} (h : s.card ≤ 1) :
    Subsingleton ↥s :=
  ⟨fun a b => Subtype.ext (Finset.card_le_one.mp h (a : E N) a.2 (b : E N) b.2)⟩

theorem mem_coneFaces_of_subset {Γ : Cx N} {σ : Finset (E N)} {a : E N}
    {s x : Finset (E N)} (hs : s ∈ Γ.faces ∨ s = ∅) (hsub : s ⊆ σ)
    (hxs : x ⊆ insert a s) : x ∈ coneFaces Γ σ a ∪ {∅} := by
  rcases Finset.eq_empty_or_nonempty x with rfl | hx
  · exact Or.inr rfl
  by_cases hax : a ∈ x
  · have hxe : x.erase a ⊆ s := by
      intro z hz
      have hz' : z ∈ insert a s := hxs (Finset.erase_subset a x hz)
      rcases Finset.mem_insert.mp hz' with h | h
      · exact absurd (h ▸ hz) (Finset.notMem_erase a x)
      · exact h
    rcases Finset.eq_empty_or_nonempty (x.erase a) with hemp | hne
    · exact Or.inl (Or.inr ⟨∅, Or.inr rfl, Finset.empty_subset σ,
        by rw [← Finset.insert_erase hax, hemp]⟩)
    · have hs' : x.erase a ∈ Γ.faces := by
        rcases hs with hs | hs
        · exact Γ.down_closed hs hxe hne
        · rw [hs] at hxe
          exact absurd (Finset.subset_empty.mp hxe) hne.ne_empty
      exact Or.inl (Or.inr ⟨x.erase a, Or.inl hs', hxe.trans hsub,
        (Finset.insert_erase hax).symm⟩)
  · have hxs' : x ⊆ s := by
      intro z hz
      have hz' : z ∈ insert a s := hxs hz
      rcases Finset.mem_insert.mp hz' with h | h
      · exact absurd (h ▸ hz) hax
      · exact h
    rcases hs with hs | hs
    · exact Or.inl (Or.inl (Γ.down_closed hs hxs' hx))
    · rw [hs] at hxs'
      exact absurd (Finset.subset_empty.mp hxs') hx.ne_empty

/-- The face set of the cone complex, with the empty face adjoined, is downward closed. -/
theorem coneFaces_isLowerSet (Γ : Cx N) (σ : Finset (E N)) (a : E N) :
    IsLowerSet (coneFaces Γ σ a ∪ {∅}) := by
  intro big small hle hmem
  rcases hmem with hmem | hmem
  · simp only [coneFaces, Set.mem_union, Set.mem_ofPred_eq] at hmem
    rcases hmem with hmem | ⟨s, hs, hsub, rfl⟩
    · rcases Finset.eq_empty_or_nonempty small with rfl | hne
      · exact Or.inr rfl
      · exact Or.inl (Or.inl (Γ.down_closed hmem hle hne))
    · exact mem_coneFaces_of_subset hs hsub hle
  · rw [Set.mem_singleton_iff] at hmem
    subst hmem
    rw [Finset.subset_empty] at hle
    exact Or.inr (by simp [hle])

/-- **The cone complex of Newman §12**: if `σ` is a face of `Γ : PL.Cx N` and `a` is outside
`⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)` (in particular `a ∉ Γ.space`), then `Γ.faces` together with
the cones `insert a s` over the faces `s ⊆ σ` (and, for `s = ∅`, the apex `{a}`) are the faces of a
simplicial complex.  This is `Γ ∪ a ∗ σ`.

`Work.Engulf.Chain.coneFaces Γ σ a = Γ.faces ∪ {insert a s | s ∈ Γ.faces, s ⊆ σ} ∪ {{a}}`
(`{a}` arises because the faces of a simplicial complex are closed under nonempty subsets).

Proof ingredients: `AffineIndependent.affineIndependent_of_notMem_span` (a simplex plus an apex
outside its affine span is affinely independent); down-closure (a nonempty subset of `insert a s`
is either a subset of `s`, hence a face of `Γ`, or of the form `insert a u` with `u ⊆ s ⊆ σ`);
and the "glue nicely" condition `inter_subset_convexHull`: for two cone faces
`convexHull (insert a s) ∩ convexHull (insert a t) = convexHull (insert a (s ∩ t))` (any common
point decomposes along the two cone structures; if the cone coefficients differ one gets
`a ∈ affineSpan (σ ∪ σ)`), and for a cone face against a face `t ∈ Γ.faces` one gets
`convexHull (insert a s) ∩ convexHull t ⊆ convexHull (s ∩ t)` because a point of the cone lying in
`Γ.space` cannot use the apex with positive coefficient (`a ∉ affineSpan (s ∪ t)`, since
`a ∉ affineSpan (σ ∪ t)`).  Note the empty set is a subset of any face, so `SimplicialComplex.ofErase`
can be applied to `coneFaces Γ σ a ∪ {∅}`; alternatively build the structure directly. -/
theorem coneCx_exists {N : ℕ} (Γ : PL.Cx N) (σ : Finset (PL.E N)) (a : PL.E N)
    (hσ : σ ∈ Γ.faces)
    (hgen : ∀ s ∈ Γ.faces,
      a ∉ (affineSpan ℝ (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))) : Set (PL.E N))) :
    ∃ Γ' : PL.Cx N, Γ'.faces = Work.Engulf.Chain.coneFaces Γ σ a := by
  classical
  -- the apex is outside the affine span of `σ` itself
  have hass : a ∉ (affineSpan ℝ ((σ : Set (E N))) : Set (E N)) := by
    have h := hgen σ hσ
    rwa [Finset.union_self] at h
  -- the empty face is not a face of the cone complex
  have hempty : (∅ : Finset (E N)) ∉ coneFaces Γ σ a := by
    intro h
    simp only [coneFaces, Set.mem_union, Set.mem_ofPred_eq] at h
    rcases h with h | ⟨u, hu, hsub, hins⟩
    · exact Γ.empty_notMem h
    · have hmem : a ∈ (insert a u : Finset (E N)) := Finset.mem_insert_self a u
      rw [← hins] at hmem
      exact Finset.notMem_empty a hmem
  refine ⟨Geometry.SimplicialComplex.ofErase (coneFaces Γ σ a ∪ {∅}) ?_ ?_ ?_, ?_⟩
  · -- affine independence of every face
    intro s hs
    simp only [coneFaces, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hs
    rcases hs with (hs | ⟨u, hu, hsu, rfl⟩) | rfl
    · exact Γ.indep hs
    · rcases hu with hu | hu
      · refine affineIndependent_insert (Γ.indep hu) ?_
        refine fun ha => hgen u hu (affineSpan_mono ℝ ?_ ha)
        exact Finset.coe_subset.mpr Finset.subset_union_right
      · subst hu
        haveI : Subsingleton ↥(insert a (∅ : Finset (E N))) :=
          subsingleton_finset_of_card_le_one (by simp)
        exact affineIndependent_of_subsingleton ℝ _
    · haveI : Subsingleton ↥(∅ : Finset (E N)) := subsingleton_finset_of_card_le_one (by simp)
      exact affineIndependent_of_subsingleton ℝ _
  · -- downward closure
    exact coneFaces_isLowerSet Γ σ a
  · -- the glue condition
    intro s hs t ht
    have hcoe : ((s : Set (E N)) ∩ (t : Set (E N))) = ((s ∩ t : Finset (E N)) : Set (E N)) :=
      (Finset.coe_inter s t).symm
    rw [hcoe]
    change simp s ∩ simp t ⊆ simp (s ∩ t)
    simp only [coneFaces, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hs ht
    rcases hs with (hs | ⟨u, hu, hsu, rfl⟩) | rfl
    · rcases ht with (ht | ⟨v, hv, hsv, rfl⟩) | rfl
      · -- old face vs old face
        intro x hx
        have h := Γ.inter_subset_convexHull hs ht (by simpa [PL.simp, Finset.coe_inter] using hx)
        simpa [PL.simp, Finset.coe_inter] using h
      · -- old face vs cone
        have hglue : simp v ∩ simp s ⊆ simp (v ∩ s) := by
          rcases hv with hv | hv
          · rw [simp_inter hv hs]
          · subst hv; simp [PL.simp]
        have ha' : a ∉ affineSpan ℝ ((v ∪ s : Finset (E N)) : Set (E N)) := by
          refine fun hc => hgen s hs (affineSpan_mono ℝ ?_ hc)
          exact Finset.coe_subset.mpr (Finset.union_subset
            (fun z hz => Finset.mem_union_left s (hsv hz))
            (fun z hz => Finset.mem_union_right σ hz))
        have h := simp_insert_inter_simp_of_notMem (u := v) (s := s) hglue ha'
        intro x hx
        refine simp_mono ?_ (h ⟨hx.2, hx.1⟩)
        intro z hz
        obtain ⟨hzv, hzs⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨hzs, Finset.mem_insert_of_mem hzv⟩
      · -- old face vs the empty face
        simp [PL.simp]
    · rcases ht with (ht | ⟨v, hv, hsv, rfl⟩) | rfl
      · -- cone vs old face
        have hglue : simp u ∩ simp t ⊆ simp (u ∩ t) := by
          rcases hu with hu | hu
          · rw [simp_inter hu ht]
          · subst hu; simp [PL.simp]
        have ha' : a ∉ affineSpan ℝ ((u ∪ t : Finset (E N)) : Set (E N)) := by
          refine fun hc => hgen t ht (affineSpan_mono ℝ ?_ hc)
          exact Finset.coe_subset.mpr (Finset.union_subset
            (fun z hz => Finset.mem_union_left t (hsu hz))
            (fun z hz => Finset.mem_union_right σ hz))
        have h := simp_insert_inter_simp_of_notMem (u := u) (s := t) hglue ha'
        intro x hx
        refine simp_mono ?_ (h hx)
        intro z hz
        obtain ⟨hzu, hzt⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hzu, hzt⟩
      · -- cone vs cone
        have hglue : simp u ∩ simp v ⊆ simp (u ∩ v) := by
          rcases hu with hu | hu
          · rcases hv with hv | hv
            · rw [simp_inter hu hv]
            · subst hv; simp [PL.simp]
          · subst hu; simp [PL.simp]
        have ha' : a ∉ affineSpan ℝ ((u ∪ v : Finset (E N)) : Set (E N)) := by
          refine fun hc => hass (affineSpan_mono ℝ ?_ hc)
          exact Finset.coe_subset.mpr (Finset.union_subset hsu hsv)
        rw [← Finset.insert_inter_distrib u v a]
        exact simp_insert_inter_simp_insert hglue ha'
      · -- cone vs the empty face
        simp [PL.simp]
    · -- the empty face
      rcases ht with (ht | ⟨v, hv, hsv, rfl⟩) | rfl <;> simp [PL.simp]
  · -- the face set of the constructed complex is `coneFaces Γ σ a`
    rw [Geometry.SimplicialComplex.ofErase_faces]
    ext u
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h, hne⟩
      · exact h
      · exact absurd h hne
    · intro h
      exact ⟨Or.inl h, fun hc => hempty (hc ▸ h)⟩

end Work.Engulf.Chain
