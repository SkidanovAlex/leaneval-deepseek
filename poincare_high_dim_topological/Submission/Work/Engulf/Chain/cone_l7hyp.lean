import Mathlib
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Chain.ConeSetup

namespace Work.Engulf.Chain

/-- **`L7Hyp` for the cone configuration (Newman §12)**: from the `C1` data for the bad face `σ`
of `Γ`, a generic apex `a ∉ Γ.space`, a complex `Γ'` with `Γ'.faces = coneFaces Γ σ a` and an
extension `f₁` of `f` over the cone which maps `coneBd a σ` into `V`, conclude that the pair
`(τ₀, τ₁) = ({a}, σ)`, the subcomplex `K = coneK Γ H σ a` and the function `f₁` satisfy the
hypotheses `L7Hyp n p q V X Γ' K L f₁ {a} σ` of Lemma 7.

Points to check: `K ∩ PL.simp ({a} ∪ σ) = floorOf {a} σ = coneBd a σ` (a face `s ∈ Γ.faces` with
`PL.simp s ⊆ H`, `s ≠ σ` meets the cone only in `PL.simp (s ∩ σ)` with `s ∩ σ ⊊ σ`, hence in
`coneBd a σ`; here principality of `σ` is used); `X ∪ f₁ '' K ⊆ V` (the old faces by `hoth`, the
lateral boundary by `hf₁V`, `X` by `hX`); `Disjoint (f₁ '' (L ∩ PL.simp (insert a σ))) X` because
`L ⊆ Γ.space` and `PL.simp (insert a σ) ∩ Γ.space = PL.simp σ`; `free` with
`A := affineSpan ℝ (σ : Set (PL.E N))` and `finrank A.direction ≤ q` (affine independence and
`σ.card = q + 1`); `clean` from `hclean` (`(K ∪ PL.simp (insert a σ)) ∩ L ⊆ H ∩ L`);
`K ∪ topOf {a} σ = K ∪ PL.simp σ = H ∪ coneBd a σ`, so `Cfg.dimH`, `Cfg.dimΓ`, `Cfg.cpt`
(`f₁ '' coneBd a σ ⊆ V` makes the extra part collapse), `Cfg.tame` (the new faces are not `⊆ L`)
and `Cfg.ov` (with `C ∩ H ∩ L`) transfer from `Γ`, as do `Cfg.subL`, `Cfg.Xc`, `Cfg.room`,
`Cfg.cont`, `Cfg.fin`, `L7Hyp.subK` and `L7Hyp.mem`. -/
theorem cone_l7hyp {n p q : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}
    {V X : Set M} {Γ : PL.Cx N} {H L : Set (PL.E N)} {f : PL.E N → M} {σ : Finset (PL.E N)}
    {a : PL.E N} {Γ' : PL.Cx N} {f₁ : PL.E N → M}
    (hAmb : Work.Engulf.Amb n p M V) (hCfg : Work.Engulf.Cfg n p V X Γ H L f)
    (hX : X ⊆ V) (hσ : σ ∈ Γ.faces) (hcard : σ.card = q + 1) (hq : q ≤ p)
    (hσH : PL.simp σ ⊆ H)
    (hprinc : ∀ s ∈ Γ.faces, PL.simp s ⊆ H → σ ⊆ s → s = σ)
    (hoth : ∀ s ∈ Γ.faces, PL.simp s ⊆ H → s ≠ σ → f '' PL.simp s ⊆ V)
    (hdisj : Disjoint (f '' PL.simp σ) X)
    (hclean : ∀ x ∈ PL.simp σ ∩ L, ∀ y ∈ H ∩ L, f x = f y → x = y)
    (ha : a ∉ Γ.space)
    (hΓ' : Γ'.faces = Work.Engulf.Chain.coneFaces Γ σ a)
    (hf₁c : ContinuousOn f₁ Γ'.space) (hf₁f : Set.EqOn f₁ f Γ.space)
    (hf₁V : f₁ '' Work.Engulf.Chain.coneBd a σ ⊆ V) :
    Work.Engulf.L7Hyp n p q V X Γ' (Work.Engulf.Chain.coneK Γ H σ a) L f₁ {a} σ := by
  have hane : a ∉ σ := a_notMem_sigma hσ ha
  have hGfaces : Γ.faces ⊆ Γ'.faces := by rw [hΓ']; exact faces_subset_coneFaces σ a
  have hKtop : coneK Γ H σ a ∪ Work.Engulf.topOf {a} σ = H ∪ coneBd a σ :=
    coneK_union_topOf hCfg.subH hσ hσH hane
  -- `(coneK ∪ topOf) ∩ L ⊆ H ∩ L`
  have hKL : (H ∪ coneBd a σ) ∩ L ⊆ H ∩ L := by
    rintro x ⟨hxHL, hxL⟩
    have hxG : x ∈ Γ.space := hCfg.subL.subset_space hxL
    refine ⟨?_, hxL⟩
    rcases hxHL with hxH | hxB
    · exact hxH
    · exact hσH (coneBd_inter_space_subset hΓ' ha hσ ⟨hxB, hxG⟩)
  -- `(coneK ∪ simp (insert a σ)) ∩ L ⊆ H ∩ L`
  have hKL' : (coneK Γ H σ a ∪ PL.simp (insert a σ)) ∩ L ⊆ H ∩ L := by
    rintro y ⟨hy, hyL⟩
    have hyG : y ∈ Γ.space := hCfg.subL.subset_space hyL
    refine ⟨?_, hyL⟩
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · obtain ⟨s, ⟨hs, hsH, -⟩, hys⟩ := Set.mem_iUnion₂.mp hy
        exact hsH hys
      · exact hσH (coneBd_inter_space_subset hΓ' ha hσ ⟨hy, hyG⟩)
    · have h1 := cone_face_inter_space hΓ' ha (Or.inl hσ) (le_refl σ)
      exact hσH (by rw [← h1]; exact ⟨hy, hyG⟩)
  -- `L ∩ simp (insert a σ) = L ∩ simp σ`
  have hLσ : L ∩ PL.simp (insert a σ) = L ∩ PL.simp σ := by
    have h1 := cone_face_inter_space hΓ' ha (Or.inl hσ) (le_refl σ)
    ext x
    constructor
    · rintro ⟨hxL, hx⟩
      exact ⟨hxL, by rw [← h1]; exact ⟨hx, hCfg.subL.subset_space hxL⟩⟩
    · rintro ⟨hxL, hx⟩
      exact ⟨hxL, Work.Engulf.simp_mono (Finset.subset_insert a σ) hx⟩
  -- `simp ({a} ∪ σ) ∩ L = simp σ ∩ L`
  have hLσ'' : PL.simp ({a} ∪ σ) ∩ L = PL.simp σ ∩ L := by
    rw [Finset.singleton_union]
    exact (Set.inter_comm _ _).trans (hLσ.trans (Set.inter_comm _ _))
  refine ⟨?_, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Cfg n p V X Γ' (coneK ∪ topOf {a} σ) L f₁`
    refine ⟨?_, ?_, hCfg.room, ?_, ?_, ?_, hf₁c, hCfg.Xc, ?_, ?_, ?_⟩
    · rw [hΓ']; exact coneFaces_finite hCfg.fin
    · exact dimLE_of_faces_eq hΓ' hCfg.dimΓ hcard hq
    · rw [hKtop]
      exact Work.Engulf.isSubSp_union (isSubSp_mono_faces hGfaces hCfg.subH)
        (isSubSp_coneBd hΓ' hσ hane)
    · exact isSubSp_mono_faces hGfaces hCfg.subL
    · intro t ht hsub
      rw [hΓ'] at ht
      rcases ht with ht | ⟨u, hu, huσ, rfl⟩
      · refine hCfg.dimH t ht ?_
        rw [hKtop] at hsub
        exact subset_H_of_subset_union hΓ' hCfg.subH ha hσ hσH ht hsub
      · have hne : u ≠ σ := by
          intro hues
          rw [hues, hKtop] at hsub
          exact not_simp_insert_sigma_subset hΓ' hCfg.subH ha hσ hsub
        have hlt : u.card < σ.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨huσ, hne⟩)
        have hucard : u.card ≤ q := by omega
        have hau : a ∉ u := by
          rcases hu with hu | rfl
          · exact fun h => ha (Γ.subset_space hu (by simpa using h))
          · simp
        rw [Finset.card_insert_of_notMem hau]
        omega
    · rw [hKtop]
      have hEq : (X ∪ f₁ '' (H ∪ coneBd a σ)) \ V = (X ∪ f '' H) \ V := by
        ext x
        constructor
        · rintro ⟨hx, hxV⟩
          refine ⟨?_, hxV⟩
          rcases hx with hx | hx
          · exact Or.inl hx
          · rcases hx with ⟨y, hy, rfl⟩
            rcases hy with hy | hy
            · exact Or.inr ⟨y, hy, (hf₁f (hCfg.subH.subset_space hy)).symm⟩
            · exact absurd (hf₁V ⟨y, hy, rfl⟩) hxV
        · rintro ⟨hx, hxV⟩
          refine ⟨?_, hxV⟩
          rcases hx with hx | hx
          · exact Or.inl hx
          · rcases hx with ⟨y, hy, rfl⟩
            exact Or.inr ⟨y, Or.inl hy, hf₁f (hCfg.subH.subset_space hy)⟩
      rw [hEq]
      exact hCfg.cpt
    · intro x
      obtain ⟨ψ, hxψ, hψ⟩ := hCfg.tame x
      refine ⟨ψ, hxψ, hψ.1, ?_⟩
      intro t ht htL y hy hyc
      have htG : t ∈ Γ.faces := by
        rw [hΓ'] at ht
        rcases ht with ht | ⟨u, hu, huσ, rfl⟩
        · exact ht
        · exfalso
          have : a ∈ L := htL (Work.Engulf.subset_simp (Finset.mem_insert_self a u))
          exact ha (hCfg.subL.subset_space this)
      have hyc' : f y ∈ ψ.toFun '' PL.closedCube (3 / 4 : ℝ) := by
        rw [← hf₁f (Γ.convexHull_subset_space htG hy)]
        exact hyc
      obtain ⟨δ, hδ, hlin⟩ := hψ.2 t htG htL y hy hyc'
      obtain ⟨A, hA⟩ := hlin
      exact ⟨δ, hδ, A, fun z hz =>
        ⟨(hA z hz).1, by rw [hf₁f (Γ.convexHull_subset_space htG hz.1)]; exact (hA z hz).2⟩⟩
    · rw [hKtop]
      obtain ⟨C, hCcomp, hCV, hC1, hC2⟩ := hCfg.ov
      refine ⟨C ∩ H ∩ L, ?_, ?_, ?_, ?_⟩
      · exact (hCcomp.inter_right (Work.Engulf.isClosed_of_isSubSp hCfg.fin hCfg.subH)).inter_right
          (Work.Engulf.isClosed_of_isSubSp hCfg.fin hCfg.subL)
      · rintro z ⟨y, ⟨⟨hyC, hyH⟩, hyL⟩, rfl⟩
        exact hCV ⟨y, hyC, (hf₁f (hCfg.subH.subset_space hyH)).symm⟩
      · intro x hx y hy hfxy hxy
        have hxHL : x ∈ H ∩ L := hKL hx
        have hyHL : y ∈ H ∩ L := hKL hy
        have hf : f x = f y := by
          rw [← hf₁f (hCfg.subH.subset_space hxHL.1),
            ← hf₁f (hCfg.subH.subset_space hyHL.1)]
          exact hfxy
        exact ⟨⟨hC1 x hxHL y hyHL hf hxy, hxHL.1⟩, hxHL.2⟩
      · intro x hx hfxX
        have hxHL : x ∈ H ∩ L := hKL hx
        have hfxX' : f x ∈ X := by
          rw [← hf₁f (hCfg.subH.subset_space hxHL.1)]
          exact hfxX
        exact ⟨⟨hC2 x hxHL hfxX', hxHL.1⟩, hxHL.2⟩
  · rw [hΓ', Finset.singleton_union]
    exact mem_coneFaces_insert (Or.inl hσ) (le_refl σ)
  · exact Finset.singleton_nonempty a
  · exact Γ.nonempty_of_mem_faces hσ
  · rw [Finset.disjoint_left]
    intro x hx hxσ
    rw [Finset.mem_singleton] at hx
    exact hane (hx ▸ hxσ)
  · rw [Finset.singleton_union, Finset.card_insert_of_notMem hane, hcard]
  · exact isSubSp_coneK hΓ' hσ hane
  · rw [Finset.singleton_union, ← coneBd_eq_floorOf]
    exact coneK_inter_simp_insert hΓ' ha hσ hσH hprinc
  · intro x hx
    rcases hx with hx | hx
    · exact hX hx
    · obtain ⟨y, hy, rfl⟩ := hx
      rcases hy with hy | hy
      · obtain ⟨s, ⟨hs, hsH, hsne⟩, hys⟩ := Set.mem_iUnion₂.mp hy
        exact hoth s hs hsH hsne ⟨y, hys, (hf₁f (Γ.convexHull_subset_space hs hys)).symm⟩
      · exact hf₁V ⟨y, hy, rfl⟩
  · rw [Finset.singleton_union, hLσ, Set.disjoint_left]
    rintro z ⟨y, ⟨hyL, hyσ⟩, rfl⟩ hzX
    exact (Set.disjoint_left.mp hdisj) ⟨y, hyσ, (hf₁f (hCfg.subL.subset_space hyL)).symm⟩ hzX
  · refine ⟨affineSpan ℝ (σ : Set (PL.E N)), ?_, ?_⟩
    · rw [direction_affineSpan]
      have hi : AffineIndependent ℝ (fun v : ↥σ => (v : PL.E N)) := Γ.indep hσ
      have hcq : Fintype.card ↥σ = q + 1 := by rw [Fintype.card_coe]; exact hcard
      rw [← Subtype.range_coe (s := (σ : Set (PL.E N)))]
      exact le_of_eq (hi.finrank_vectorSpan (n := q) hcq)
    · intro x hx
      rw [Finset.singleton_union, hLσ] at hx
      have hsub : PL.simp σ ⊆ (affineSpan ℝ (σ : Set (PL.E N)) : Set (PL.E N)) :=
        convexHull_min (subset_affineSpan ℝ (σ : Set (PL.E N)))
          (AffineSubspace.convex (affineSpan ℝ (σ : Set (PL.E N))))
      exact hsub hx.2
  · intro x hx y hy hfxy
    have hx' : x ∈ PL.simp σ ∩ L := by
      rw [hLσ''] at hx
      exact hx
    have hy' : y ∈ H ∩ L := hKL' ⟨hy.1, hy.2⟩
    have hfx : f x = f y := by
      rw [← hf₁f (hCfg.subL.subset_space hx'.2), ← hf₁f (hCfg.subH.subset_space hy'.1)]
      exact hfxy
    exact hclean x hx' y hy' hfx

end Work.Engulf.Chain
