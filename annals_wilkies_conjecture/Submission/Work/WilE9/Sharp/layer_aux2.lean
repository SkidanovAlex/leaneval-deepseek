import Mathlib
import Submission.Work.WilE9.Sharp.layer_aux

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-!
  **Auxiliary material (part 2) for the layer specification**: order independence of `Gset` and
  `Eset`, and the two specifications `SecSpec` and `LimSpec`.
-/

/-! ## 6. Order independence -/

/-- A point of `Gset n S L` is a point of `Gset n S L'` for any `L ~ L'`. -/
theorem Gset_subset_of_perm {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S)
    {L L' : List (Fin n)} (hperm : List.Perm L L') :
    Gset n S L ⊆ Gset n S L' := by
  intro ζ hζ
  have hspec := Gset_spec H hζ
  have hgl : ζ (Fin.last n) = Work.WilE9.glDeriv L f (Fin.init ζ) := hspec.1
  have hCt : ContDiffAt ℝ ⊤ f (Fin.init ζ) := hspec.2
  simp only [Gset, Set.mem_preimage, Tset, Set.mem_iUnion] at hζ
  obtain ⟨A, hA, hζA⟩ := hζ
  obtain ⟨z, hz, hzout⟩ :=
    (Set.mem_image exOut (exComp n A.1 A.E A.q L) (WilkiesDesign.E.psiV ζ)).mp hζA
  have hpsiζ : WilkiesDesign.E.psiV ζ =
      Fin.snoc (WilkiesDesign.E.psiV (Fin.init ζ))
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Fin.init ζ))) := by
    conv_lhs => rw [← Fin.snoc_init_self ζ]
    rw [psiV_snoc, hgl]
  have hexL : ∃ z ∈ exComp n A.1 A.E A.q L,
      exOut z = Fin.snoc (WilkiesDesign.E.psiV (Fin.init ζ))
        (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Fin.init ζ))) :=
    ⟨z, hz, by rw [hzout, hpsiζ]⟩
  obtain ⟨w, hw, hwproj⟩ := H.hbase A hA L
    (WilkiesDesign.E.psiV (Fin.init ζ))
    (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Fin.init ζ))) hexL
  simp only [psiInvV_psiV] at hwproj
  obtain ⟨z', hz', hz'out⟩ :=
    H.hfst A hA L' (Fin.init ζ) w hw hwproj
  have hpermgl : Work.WilE9.glDeriv L' f (Fin.init ζ) = Work.WilE9.glDeriv L f (Fin.init ζ) :=
    H.hglperm (Fin.init ζ) hCt L' L hperm.symm
  have hzv : WilkiesDesign.E.psiV ζ = exOut z' := by
    rw [hz'out, hpermgl, ← hpsiζ]
  simp only [Gset, Set.mem_preimage, Tset, Set.mem_iUnion]
  refine ⟨A, hA, ?_⟩
  rw [exTsetC_eq_image]
  exact (Set.mem_image exOut (exComp n A.1 A.E A.q L') (WilkiesDesign.E.psiV ζ)).mpr
    ⟨z', hz', hzv.symm⟩

/-- **Order independence of `Eset`.** -/
theorem Eset_perm {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S)
    {L L' : List (Fin n)} (hperm : List.Perm L L') :
    Eset n S L = Eset n S L' := by
  have hG : Gset n S L = Gset n S L' :=
    Set.Subset.antisymm (Gset_subset_of_perm H hperm)
      (Gset_subset_of_perm H hperm.symm)
  show closure (Gset n S L) = closure (Gset n S L')
  rw [hG]

/-! ## 7. The two specifications -/

/-- **Section correctness of `Eset`** on the `C^{|L|}` locus. -/
theorem secSpec_of {n k : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S) :
    SecSpec n k S f := by
  intro L hL x t hC
  constructor
  · intro hmem
    have hp : Fin.snoc x t ∈ closure (Gset n S L) := hmem
    have hg : ContinuousAt (Work.WilE9.glDeriv L f) x := glDeriv_continuousAt hC le_rfl
    have hφ : ContinuousAt (fun u : Fin (n + 1) → ℝ =>
        u (Fin.last n) - Work.WilE9.glDeriv L f (Fin.init u)) (Fin.snoc x t) := by
      refine ContinuousAt.sub (continuous_apply (Fin.last n)).continuousAt ?_
      have hfin : ContinuousAt (fun u : Fin (n + 1) → ℝ => Fin.init u) (Fin.snoc x t) :=
        continuous_init.continuousAt
      have h3 : ContinuousAt (Work.WilE9.glDeriv L f)
          ((fun u : Fin (n + 1) → ℝ => Fin.init u) (Fin.snoc x t)) := by
        have hpt : (fun u : Fin (n + 1) → ℝ => Fin.init u) (Fin.snoc x t) = x := by simp
        rw [hpt]
        exact hg
      exact h3.comp hfin
    have hcl := mem_closure_image hφ hp
    have hsub : (fun u : Fin (n + 1) → ℝ =>
        u (Fin.last n) - Work.WilE9.glDeriv L f (Fin.init u)) '' Gset n S L ⊆
        ({0} : Set ℝ) := by
      rintro v ⟨u, hu, rfl⟩
      obtain ⟨h1, -⟩ := Gset_spec H hu
      rw [Set.mem_singleton_iff]
      exact sub_eq_zero.mpr h1
    have h0 := closure_minimal hsub isClosed_singleton hcl
    rw [Set.mem_singleton_iff, Fin.snoc_last, Fin.init_snoc] at h0
    linarith
  · intro ht
    rw [ht]
    have hxcl : x ∈ closure (Base n S f L) := base_mem_closure H hC
    have hg : ContinuousAt (Work.WilE9.glDeriv L f) x := glDeriv_continuousAt hC le_rfl
    have hΦ : ContinuousAt (fun y : Fin n → ℝ =>
        (Fin.snoc y (Work.WilE9.glDeriv L f y) : Fin (n + 1) → ℝ)) x := by
      rw [continuousAt_pi]
      refine Fin.lastCases ?_ ?_
      · simp only [Fin.snoc_last]
        exact hg
      · intro j
        simp only [Fin.snoc_castSucc]
        exact (continuous_apply j).continuousAt
    have hcl := mem_closure_image hΦ hxcl
    have himg : (fun y : Fin n → ℝ => Fin.snoc y (Work.WilE9.glDeriv L f y)) '' Base n S f L
        = Gset n S L := (Gset_eq_image_Base H).symm
    rw [himg] at hcl
    show Fin.snoc x (Work.WilE9.glDeriv L f x) ∈ closure (Gset n S L)
    exact hcl

/-- **Closedness of the projections of `Eset`** relative to the `C^{|L|}` locus. -/
theorem limSpec_of {n k : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    {S : List (AEStratum n)} (H : LayerHyp n f Z S) :
    LimSpec n k S f := by
  intro L hL x hx
  have hx1 : x ∈ Fin.init '' Eset n S L := by
    rw [← projLast_eq_image_init (Eset n S L)]
    exact hx
  obtain ⟨p, hp, hpinit⟩ := hx1
  have hpcl : p ∈ closure (Gset n S L) := hp
  have hxcl : x ∈ closure (Fin.init '' Gset n S L) := by
    rw [← hpinit]
    exact mem_closure_image continuous_init.continuousAt hpcl
  rw [image_init_Gset H L] at hxcl
  refine closure_mono (fun y hy => ?_) hxcl
  exact (base_contDiff H hy).of_le (le_top : (((L.length : ℕ)) : WithTop ℕ∞) ≤ ⊤)

end Work.WilE9.Sharp
