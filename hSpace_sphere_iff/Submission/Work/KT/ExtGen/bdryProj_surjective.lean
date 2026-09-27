import Mathlib
import Submission.Work.KT.ExtGen.TripleBdry

namespace Work.KT.ExtGen

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-! ## The projection `(v,w,z) ↦ (v,z)` and the pulled-back copy of `prodAlg V Z` -/

/-- `(v,w,z) ↦ (v,z)` as a map of balls. -/
def projTripleVZ : C(Ball (V × (W × Z)), Ball (V × Z)) where
  toFun z := ⟨((z : V × (W × Z)).1, (z : V × (W × Z)).2.2),
    mem_closedBall_zero_iff.mpr (by
      rw [Prod.norm_def]
      exact max_le (norm_fst_le' V W Z z) (norm_zc_le V W Z z))⟩
  continuous_toFun := by fun_prop

@[simp] lemma projTripleVZ_apply (z : Ball (V × (W × Z))) :
    (projTripleVZ V W Z z : V × Z) = ((z : V × (W × Z)).1, (z : V × (W × Z)).2.2) := rfl

/-- The inclusion `prodAlg V Z ⊆ tripleAlg V W Z`. -/
def tripleInclPZ : prodAlg V Z →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict
    ((pullAlg (projTripleVZ V W Z)).comp (prodAlg V Z).val) (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨?_, ?_, ?_⟩
    · intro z z' h1 h2 h3 h4
      exact hF1 (projTripleVZ V W Z z) (projTripleVZ V W Z z') h1 h2 h4
    · intro z z' h1 h2 h3 h4
      have h : projTripleVZ V W Z z = projTripleVZ V W Z z' :=
        Subtype.ext (by rw [projTripleVZ_apply, projTripleVZ_apply, h4, h3])
      exact congrArg (fun w => (F : C(Ball (V × Z), ℂ)) w) h
    · intro z z' h1 h2 h3 h4
      exact hF2 (projTripleVZ V W Z z) (projTripleVZ V W Z z') h1 h2 h4)

@[simp] lemma tripleInclPZ_apply (F : prodAlg V Z) :
    ((tripleInclPZ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projTripleVZ V W Z)) (F : C(Ball (V × Z), ℂ)) := rfl

/-! ## Values of the slice maps -/

@[simp] lemma sliceW_apply' (v0 : Ball V) (hv0 : v0 ∈ bdry V) (F : prodAlg V W)
    (y : Ball W) :
    (sliceW V W v0 hv0 F : C(Ball W, ℂ)) y
      = (F : C(Ball (V × W), ℂ)) (pairPtD V W v0 hv0 y) := rfl

@[simp] lemma sliceV_apply' (w0 : Ball W) (hw0 : w0 ∈ bdry W) (F : prodAlg V W)
    (x : Ball V) :
    (sliceV V W w0 hw0 F : C(Ball V, ℂ)) x
      = (F : C(Ball (V × W), ℂ)) (pairPtC V W w0 hw0 x) := rfl

/-! ## The raw formula and its value -/

/-- The explicit preimage
`F(v,w,z) = f₁(w,z) + f₂(v,z) + f₃(v,w) - f₁₂(z) - f₁₃(w) - f₂₃(v) + c`. -/
def bdryLiftFun (f₁ : prodAlg W Z) (f₂ : prodAlg V Z) (f₃ : prodAlg V W)
    (g₁₂ : Kpair Z) (g₁₃ : Kpair W) (g₂₃ : Kpair V) (c : ℂ) :
    C(Ball (V × (W × Z)), ℂ) :=
  (pullAlg (prSnd V (W × Z))) (f₁ : C(Ball (W × Z), ℂ))
  + (pullAlg (projTripleVZ V W Z)) (f₂ : C(Ball (V × Z), ℂ))
  + (pullAlg (projTripleVW V W Z)) (f₃ : C(Ball (V × W), ℂ))
  - (pullAlg (projTripleZ V W Z)) (g₁₂ : C(Ball Z, ℂ))
  - (pullAlg (projTripleW V W Z)) (g₁₃ : C(Ball W, ℂ))
  - (pullAlg (prFst V (W × Z))) (g₂₃ : C(Ball V, ℂ))
  + algebraMap ℂ C(Ball (V × (W × Z)), ℂ) c

@[simp] lemma bdryLiftFun_apply (f₁ : prodAlg W Z) (f₂ : prodAlg V Z) (f₃ : prodAlg V W)
    (g₁₂ : Kpair Z) (g₁₃ : Kpair W) (g₂₃ : Kpair V) (c : ℂ)
    (z : Ball (V × (W × Z))) :
    bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c z
      = (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z)
        + (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z)
        + (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z)
        - (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z)
        - (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z)
        - (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z)
        + c := by
  have halg : ((algebraMap ℂ C(Ball (V × (W × Z)), ℂ)) c) z = c := by simp
  simp only [bdryLiftFun, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.comp_apply, pullAlg, StarAlgHom.coe_toAlgHom,
    ContinuousMap.compStarAlgHom'_apply, halg]

/-! ## Membership of the raw formula in `tripleAlg` -/

lemma bdryLiftFun_mem (f₁ : prodAlg W Z) (f₂ : prodAlg V Z) (f₃ : prodAlg V W)
    (g₁₂ : Kpair Z) (g₁₃ : Kpair W) (g₂₃ : Kpair V) (c : ℂ) :
    bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c ∈ tripleAlg V W Z := by
  rw [mem_tripleAlg_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro z z' h1 h2 h3 h4
    simp only [bdryLiftFun_apply]
    have hA : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z)
        = (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z') := by
      congr 1; exact Subtype.ext (Prod.ext h3 h4)
    have hB : (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z)
        = (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z') :=
      f₂.2.1 _ _ h1 h2 h4
    have hC : (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z)
        = (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z') :=
      f₃.2.1 _ _ h1 h2 h3
    have hD : (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z)
        = (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z') :=
      congrArg _ (Subtype.ext h4)
    have hE : (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z)
        = (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z') :=
      congrArg _ (Subtype.ext h3)
    have hF : (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z)
        = (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z') :=
      g₂₃.2 _ h1 _ h2
    rw [hA, hB, hC, hD, hE, hF]
  · intro z z' h1 h2 h3 h4
    simp only [bdryLiftFun_apply]
    have hA : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z)
        = (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z') :=
      f₁.2.1 _ _ h1 h2 h3
    have hB : (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z)
        = (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z') :=
      congrArg _ (Subtype.ext (Prod.ext h4 h3))
    have hC : (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z)
        = (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z') :=
      f₃.2.2 _ _ h1 h2 h4
    have hD : (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z)
        = (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z') :=
      congrArg _ (Subtype.ext h3)
    have hE : (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z)
        = (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z') :=
      g₁₃.2 _ h1 _ h2
    have hF : (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z)
        = (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z') :=
      congrArg _ (Subtype.ext h4)
    rw [hA, hB, hC, hD, hE, hF]
  · intro z z' h1 h2 h3 h4
    simp only [bdryLiftFun_apply]
    have hA : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z)
        = (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) z') :=
      f₁.2.2 _ _ h1 h2 h3
    have hB : (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z)
        = (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z z') :=
      f₂.2.2 _ _ h1 h2 h4
    have hC : (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z)
        = (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z z') :=
      congrArg _ (Subtype.ext (Prod.ext h4 h3))
    have hD : (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z)
        = (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z z') :=
      g₁₂.2 _ h1 _ h2
    have hE : (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z)
        = (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z z') :=
      congrArg _ (Subtype.ext h3)
    have hF : (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z)
        = (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) z') :=
      congrArg _ (Subtype.ext h4)
    rw [hA, hB, hC, hD, hE, hF]


/-- `bdryProj V W Z v₀ hv₀ w₀ hw₀ z₀ hz₀ : tripleAlg V W Z →ₐ[ℂ] bdryAlg` (see
`Submission.Work.KT.ExtGen.TripleBdry`) is the map `F ↦ (F|_{|v|=1}, F|_{|w|=1}, F|_{|z|=1})` onto
the fibre product of the three chart algebras `prodAlg W Z`, `prodAlg V Z`, `prodAlg V W`.  An
explicit preimage of `(f₁,f₂,f₃)` uses the three pairwise common restrictions `f₁₂ ∈ Kpair Z`,
`f₁₃ ∈ Kpair W`, `f₂₃ ∈ Kpair V` and the corner value `u₀`:
`F(v,w,z) := f₁(w,z) + f₂(v,z) + f₃(v,w) - f₁₂(z) - f₁₃(w) - f₂₃(v) + u₀`. -/
theorem bdryProj_surjective (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    Function.Surjective (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0) := by
  intro y
  obtain ⟨⟨f₁, f₂, f₃⟩, hy⟩ := y
  have hy1 : sliceW W Z w0 hw0 f₁ = sliceW V Z v0 hv0 f₂ :=
    congrArg (fun t : Kpair Z × Kpair W × Kpair V => t.1) hy
  have hy2 : sliceV W Z z0 hz0 f₁ = sliceW V W v0 hv0 f₃ :=
    congrArg (fun t : Kpair Z × Kpair W × Kpair V => t.2.1) hy
  have hy3 : sliceV V Z z0 hz0 f₂ = sliceV V W w0 hw0 f₃ :=
    congrArg (fun t : Kpair Z × Kpair W × Kpair V => t.2.2) hy
  set g₁₂ : Kpair Z := sliceW V Z v0 hv0 f₂ with hg12
  set g₁₃ : Kpair W := sliceW V W v0 hv0 f₃ with hg13
  set g₂₃ : Kpair V := sliceV V Z z0 hz0 f₂ with hg23
  set c : ℂ := (f₂ : C(Ball (V × Z), ℂ)) (pairPtC V Z z0 hz0 v0) with hc
  have hc_eq : (g₂₃ : C(Ball V, ℂ)) v0 = c := by
    simp only [hg23, hc, sliceV_apply']
  let F : ↥(tripleAlg V W Z) :=
    ⟨bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c,
      bdryLiftFun_mem V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c⟩
  refine ⟨F, ?_⟩
  apply Subtype.ext
  rw [bdryProj_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- restriction to `{v₀} × D_W × D_Z` is `f₁`
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    rw [sliceV0_apply]
    set p' : Ball (V × (W × Z)) := sliceMapV0 V W Z v0 hv0 p with hp'
    change bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c p' = (f₁ : C(Ball (W × Z), ℂ)) p
    rw [bdryLiftFun_apply]
    have hpp : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) p')
        = (f₁ : C(Ball (W × Z), ℂ)) p := by
      exact congrArg (fun q => (f₁ : C(Ball (W × Z), ℂ)) q) (Subtype.ext rfl)
    have hgz : (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z p')
        = (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z p') := by
      rw [hg12, sliceW_apply']
      exact congrArg (fun q => (f₂ : C(Ball (V × Z), ℂ)) q)
        (Subtype.ext (by rw [pairPtD_apply, projTripleVZ_apply]; rfl))
    have hgz3 : (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z p')
        = (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z p') := by
      rw [hg13, sliceW_apply']
      exact congrArg (fun q => (f₃ : C(Ball (V × W), ℂ)) q)
        (Subtype.ext (by rw [pairPtD_apply, projTripleVW_apply]; rfl))
    have hgz2 : (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) p') = c := by
      have h : prFst V (W × Z) p' = v0 := Subtype.ext rfl
      rw [h]
      exact hc_eq
    rw [hpp, hgz, hgz3, hgz2]
    ring
  · -- restriction to `D_V × {w₀} × D_Z` is `f₂`
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    rw [sliceW0_apply]
    set p' : Ball (V × (W × Z)) := sliceMapW0 V W Z w0 hw0 p with hp'
    change bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c p' = (f₂ : C(Ball (V × Z), ℂ)) p
    rw [bdryLiftFun_apply]
    have hAD : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) p')
        = (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z p') := by
      have h : prSnd V (W × Z) p' = pairPtD W Z w0 hw0 (projTripleZ V W Z p') :=
        Subtype.ext rfl
      rw [h, ← hy1, sliceW_apply']
    have hB : (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z p')
        = (f₂ : C(Ball (V × Z), ℂ)) p := by
      exact congrArg (fun q => (f₂ : C(Ball (V × Z), ℂ)) q)
        (Subtype.ext (by rw [projTripleVZ_apply]; rfl))
    have hCF : (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z p')
        = (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) p') := by
      have h : projTripleVW V W Z p' = pairPtC V W w0 hw0 (prFst V (W × Z) p') :=
        Subtype.ext rfl
      rw [h, hy3, sliceV_apply']
    have hE : (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z p') = c := by
      rw [hg13, sliceW_apply']
      have h : pairPtD V W v0 hv0 (projTripleW V W Z p') = pairPtC V W w0 hw0 v0 :=
        Subtype.ext rfl
      rw [h]
      have h2 : (f₃ : C(Ball (V × W), ℂ)) (pairPtC V W w0 hw0 v0) = c := by
        rw [← sliceV_apply', ← hy3]
        exact hc_eq
      exact h2
    rw [hAD, hB, hCF, hE]
    ring
  · -- restriction to `D_V × D_W × {z₀}` is `f₃`
    apply Subtype.ext
    apply ContinuousMap.ext
    intro p
    rw [sliceZ0_apply]
    set p' : Ball (V × (W × Z)) := sliceMapZ0 V W Z z0 hz0 p with hp'
    change bdryLiftFun V W Z f₁ f₂ f₃ g₁₂ g₁₃ g₂₃ c p' = (f₃ : C(Ball (V × W), ℂ)) p
    rw [bdryLiftFun_apply]
    have hAE : (f₁ : C(Ball (W × Z), ℂ)) (prSnd V (W × Z) p')
        = (g₁₃ : C(Ball W, ℂ)) (projTripleW V W Z p') := by
      have h : prSnd V (W × Z) p' = pairPtC W Z z0 hz0 (projTripleW V W Z p') :=
        Subtype.ext rfl
      rw [h, ← hy2, sliceV_apply']
    have hBF : (f₂ : C(Ball (V × Z), ℂ)) (projTripleVZ V W Z p')
        = (g₂₃ : C(Ball V, ℂ)) (prFst V (W × Z) p') := by
      have h : projTripleVZ V W Z p' = pairPtC V Z z0 hz0 (prFst V (W × Z) p') :=
        Subtype.ext rfl
      rw [h, hg23, sliceV_apply']
    have hC : (f₃ : C(Ball (V × W), ℂ)) (projTripleVW V W Z p')
        = (f₃ : C(Ball (V × W), ℂ)) p := by
      exact congrArg (fun q => (f₃ : C(Ball (V × W), ℂ)) q)
        (Subtype.ext (by rw [projTripleVW_apply]; rfl))
    have hD : (g₁₂ : C(Ball Z, ℂ)) (projTripleZ V W Z p') = c := by
      rw [hg12, sliceW_apply']
      have h : pairPtD V Z v0 hv0 (projTripleZ V W Z p') = pairPtC V Z z0 hz0 v0 :=
        Subtype.ext rfl
      rw [h, hc]
    rw [hAE, hBF, hC, hD]
    ring

end

end Work.KT.ExtGen
