import Mathlib

/-!
# The corrected form of `Work.Drive.PushDisc.localInverseFamilyTwoSided`

The statement of `Work.Drive.PushDisc.localInverseFamilyTwoSided` (in the file
`Submission/Work/Drive/PushDisc/localInverseFamilyTwoSided.lean`) is **false**: see that file for a
formal counterexample.  This file records the **minimal repair**, namely the same statement with the
single conjunct `G (s, y) ∈ W` deleted from the first clause.

## Why that conjunct is the culprit

The two clauses of the target, applied to `s ∈ O`, say

* `G (s, y) ∈ W` for all `y ∈ U`, i.e. `G (s, U) ⊆ W`, and
* `h s z ∈ U` and `G (s, h s z) = z` for all `z ∈ W`, which gives `W = G (s, h s '' W) ⊆ G (s, U)`.

So the two clauses together force `G (s, U) = W` for every `s ∈ O`: the image of the fixed set `U`
must not depend on `s`.  Since `O` is open, this is incompatible with `U ⊆ V` for a bounded `V`.

`G (s, h s z) = z` (the surjectivity of the inverse family) is the genuine inverse-function content;
`G (s, U) ⊆ W` is a *strengthening* that the inverse function theorem cannot supply (and that is
false in general).  Deleting it leaves exactly the two-sided inverse property: for each `s ∈ O`, `h s`
is a left inverse of `G (s, ·)` on `U` and a right inverse of `G (s, ·)` on `W`, with the graph of
`h` over `W` contained in the prescribed neighbourhood `U ⊆ V`.

## The proof

`Φ (s, y) = (s, G (s, y))` has invertible derivative at `(s₀, p)` (the hypothesis `hbij` says the
partial derivative in `y` is bijective, and the first coordinate passes through unchanged), so the
inverse function theorem produces an open partial homeomorphism `Φo` with `⇑Φo = Φ`, whose inverse
`Φo.symm` is `C^∞` at `(s₀, G (s₀, p))` and, by the inverse function theorem, on every point whose
`Φ`-preimage is a point where `fderiv Φ` is invertible.  That set is open (the invertible elements of
a Banach algebra of operators form an open set, transported here along the fixed linear equivalence
`e₀`), so it contains an open neighbourhood `V'` of `(s₀, p)`; then
`Z = Φo.target ∩ Φo.symm ⁻¹' V'` is an open neighbourhood of `(s₀, G (s₀, p))` on which `Φo.symm` is
`C^∞`.  Finally one takes a product box `O_A × U_A ⊆ Φo.source` with `U_A ⊆ V`, the open set
`R = Φo.target ∩ Φo.symm ⁻¹' (O_A × U_A)` and a product box `O × W ⊆ R ∩ Z`; then
`h s z := (Φo.symm (s, z)).2` does the job.  This is exactly the construction used here.

Note that the openness of the invertibility locus is *not* a formality: the hypotheses only make
`fderiv Φ` invertible at the single point `(s₀, p)`, so without it the `C^∞`-on-a-box conclusion
could not be reached.
-/

namespace Work.Drive.PushDisc

open scoped Topology

/-- For `A : ℝ × E →L F` whose restriction to the second factor is bijective, the map
`x ↦ (x.1, A x)` is a continuous linear equivalence `ℝ × E ≃L ℝ × F`. -/
private lemma prodEquiv_of_bijective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : ℝ × E →L[ℝ] F} (hA : Function.Bijective (A.comp (ContinuousLinearMap.inr ℝ ℝ E))) :
    ∃ e : (ℝ × E) ≃L[ℝ] (ℝ × F),
      (e : ℝ × E →L[ℝ] ℝ × F) = (ContinuousLinearMap.fst ℝ ℝ E).prod A := by
  set A₂ : E →L[ℝ] F := A.comp (ContinuousLinearMap.inr ℝ ℝ E) with hA₂
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : E ≃L[ℝ] F, (e₂ : E →L[ℝ] F) = A₂ :=
    ⟨ContinuousLinearEquiv.ofBijective A₂ (LinearMap.ker_eq_bot.mpr hA.1)
      (LinearMap.range_eq_top.mpr hA.2), ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hA0 : ∀ y : E, A (0, y) = e₂ y := by
    intro y
    have h1 : A₂ y = (e₂ : E →L[ℝ] F) y := by rw [← he₂]
    rw [hA₂] at h1
    simpa [ContinuousLinearEquiv.coe_coe] using h1
  have hsplit : ∀ (s : ℝ) (y : E), A (s, y) = A (s, 0) + A (0, y) := by
    intro s y
    have h : (s, y) = (s, 0) + ((0 : ℝ), y) := by ext <;> simp
    rw [h, map_add]
  set L : (ℝ × E) →L[ℝ] (ℝ × F) := (ContinuousLinearMap.fst ℝ ℝ E).prod A with hL
  set M : (ℝ × F) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ F).prod
      ((e₂.symm : F →L[ℝ] E).comp ((ContinuousLinearMap.snd ℝ ℝ F) -
        (A.comp ((ContinuousLinearMap.inl ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ ℝ F)))))
    with hM
  have hLapp : ∀ (s : ℝ) (y : E), L (s, y) = (s, A (s, y)) := fun s y => by
    simp [L, ContinuousLinearMap.prod_apply]
  have hMapp : ∀ (s : ℝ) (z : F), M (s, z) = (s, e₂.symm (z - A (s, 0))) := fun s z => by
    simp [M, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  have hML : Function.LeftInverse M L := by
    intro x
    obtain ⟨s, y⟩ := x
    rw [hLapp, hMapp, hsplit s y, hA0 y]
    rw [show A (s, 0) + e₂ y - A (s, 0) = e₂ y by abel,
      ContinuousLinearEquiv.symm_apply_apply]
  have hMR : Function.RightInverse M L := by
    intro z
    obtain ⟨s, z⟩ := z
    rw [hMapp, hLapp, hsplit s (e₂.symm (z - A (s, 0))), hA0 (e₂.symm (z - A (s, 0))),
      ContinuousLinearEquiv.apply_symm_apply]
    rw [show A (s, 0) + (z - A (s, 0)) = z by abel]
  exact ⟨ContinuousLinearEquiv.equivOfInverse L M hML hMR, rfl⟩

/-- A continuous linear map between complete spaces is invertible iff it is bijective. -/
private lemma isInvertible_iff_bijective_clm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {T : E →L[ℝ] F} : T.IsInvertible ↔ Function.Bijective T :=
  ⟨fun ⟨A, hA⟩ => hA ▸ A.bijective,
   fun h => ⟨ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr h.1)
     (LinearMap.range_eq_top.mpr h.2), rfl⟩⟩

/-- The invertible elements of `E →L[ℝ] F` form an open set (transported from the open set of units
of the Banach algebra `E →L[ℝ] E` along a fixed linear equivalence `E ≃L F`). -/
private lemma isOpen_isInvertible_clm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E ≃L[ℝ] F) : IsOpen {T : E →L[ℝ] F | T.IsInvertible} := by
  have hcont : Continuous (fun T : E →L[ℝ] F => (e.symm : F →L[ℝ] E).comp T) :=
    (ContinuousLinearMap.compL ℝ E F E (e.symm : F →L[ℝ] E)).continuous
  have hset : {T : E →L[ℝ] F | T.IsInvertible} =
      (fun T : E →L[ℝ] F => (e.symm : F →L[ℝ] E).comp T) ⁻¹'
        {S : E →L[ℝ] E | IsUnit S} := by
    ext T
    rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_ofPred_eq,
      ContinuousLinearMap.isUnit_iff_bijective, isInvertible_iff_bijective_clm]
    constructor
    · intro hT
      exact (e.symm.bijective).comp hT
    · intro hT
      have h2 : Function.Bijective (fun x : E => e (e.symm (T x))) := e.bijective.comp hT
      rwa [show (fun x : E => e (e.symm (T x))) = (fun x : E => T x) from
        funext fun x => by simp] at h2
  rw [hset]
  exact Units.isOpen.preimage hcont

/-- A neighbourhood of a point of a product contains a product of open neighbourhoods. -/
private lemma box_subset_of_mem_nhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {t : Set (X × Y)} (ht : t ∈ 𝓝 (x, y)) :
    ∃ O : Set X, ∃ W : Set Y, IsOpen O ∧ x ∈ O ∧ IsOpen W ∧ y ∈ W ∧ O ×ˢ W ⊆ t := by
  rcases mem_nhds_prod_iff.mp ht with ⟨u, hu, v, hv, huv⟩
  obtain ⟨O, hOu, hOo, hxO⟩ := mem_nhds_iff.mp hu
  obtain ⟨W, hWv, hWo, hyW⟩ := mem_nhds_iff.mp hv
  exact ⟨O, W, hOo, hxO, hWo, hyW, (Set.prod_mono hOu hWv).trans huv⟩

/-- **The repaired local inverse function theorem.**

This is the statement of `Work.Drive.PushDisc.localInverseFamilyTwoSided` with the conjunct
`G (s, y) ∈ W` deleted from the first clause; it is the minimal true repair of that statement (see
the module docstring for why that conjunct is exactly what fails). -/
theorem localInverseFamilyTwoSided_repair {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : ℝ × E → F) (U₀ : Set (ℝ × E)) (hU₀ : IsOpen U₀) (s₀ : ℝ) (p : E)
    (hmem : (s₀, p) ∈ U₀) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U₀)
    (hbij : Function.Bijective (fun v : E => fderiv ℝ G (s₀, p) (0, v)))
    (V : Set E) (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ (O : Set ℝ) (U : Set E) (W : Set F) (h : ℝ → F → E),
      IsOpen O ∧ s₀ ∈ O ∧ IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧ IsOpen W ∧ G (s₀, p) ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry h) (O ×ˢ W) ∧
      (∀ s ∈ O, ∀ y ∈ U, h s (G (s, y)) = y) ∧
      (∀ s ∈ O, ∀ z ∈ W, h s z ∈ U ∧ G (s, h s z) = z) := by
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hn1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hG_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (s₀, p) :=
    hG.contDiffAt (hU₀.mem_nhds hmem)
  have hΦon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × E => (x.1, G x)) U₀ :=
    contDiffOn_fst.prodMk hG
  have hΦcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × E => (x.1, G x)) (s₀, p) :=
    hΦon.contDiffAt (hU₀.mem_nhds hmem)
  have hGderiv : HasFDerivAt G (fderiv ℝ G (s₀, p)) (s₀, p) :=
    (hG_at.differentiableAt hn0).hasFDerivAt
  have hΦderiv : HasFDerivAt (fun x : ℝ × E => (x.1, G x))
      ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ G (s₀, p))) (s₀, p) :=
    (hasFDerivAt_fst (p := (s₀, p))).prodMk hGderiv
  have hbij' : Function.Bijective
      ((fderiv ℝ G (s₀, p)).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    have hfe : ⇑((fderiv ℝ G (s₀, p)).comp (ContinuousLinearMap.inr ℝ ℝ E)) =
        fun v : E => fderiv ℝ G (s₀, p) (0, v) := by
      funext v
      simp [ContinuousLinearMap.comp_apply]
    rwa [hfe]
  obtain ⟨e₀, he₀⟩ : ∃ e : (ℝ × E) ≃L[ℝ] (ℝ × F),
      (e : ℝ × E →L[ℝ] ℝ × F) =
        (ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ G (s₀, p)) :=
    prodEquiv_of_bijective hbij'
  have hΦstrict : HasStrictFDerivAt (fun x : ℝ × E => (x.1, G x))
      (e₀ : ℝ × E →L[ℝ] ℝ × F) (s₀, p) :=
    hΦcd.hasStrictFDerivAt' (by rw [he₀]; exact hΦderiv) hn0
  let Φo : OpenPartialHomeomorph (ℝ × E) (ℝ × F) :=
    hΦstrict.toOpenPartialHomeomorph (fun x : ℝ × E => (x.1, G x))
  have hΦo_coe : (⇑Φo : ℝ × E → ℝ × F) = (fun x : ℝ × E => (x.1, G x)) :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hΦstrict
  have hsrc : (s₀, p) ∈ Φo.source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hΦstrict
  have htgt : (s₀, G (s₀, p)) ∈ Φo.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hΦstrict
  have hΨq : Φo.symm (s₀, G (s₀, p)) = (s₀, p) := Φo.leftInvOn hsrc
  have hΦfderiv : fderiv ℝ (fun x : ℝ × E => (x.1, G x)) (s₀, p) =
      (e₀ : ℝ × E →L[ℝ] ℝ × F) := by
    rw [hΦderiv.fderiv, ← he₀]
  have hInvOpen : IsOpen {T : (ℝ × E) →L[ℝ] (ℝ × F) | T.IsInvertible} :=
    isOpen_isInvertible_clm e₀
  have hfdcont : ContinuousOn (fun x : ℝ × E => fderiv ℝ (fun x : ℝ × E => (x.1, G x)) x) U₀ :=
    hΦon.continuousOn_fderiv_of_isOpen hU₀ hn1
  -- the open locus where `fderiv Φ` is invertible
  let V' : Set (ℝ × E) := U₀ ∩
    (fun x : ℝ × E => fderiv ℝ (fun x : ℝ × E => (x.1, G x)) x) ⁻¹'
      {T : (ℝ × E) →L[ℝ] (ℝ × F) | T.IsInvertible}
  have hV'open : IsOpen V' := hfdcont.isOpen_inter_preimage hU₀ hInvOpen
  have hV'nhds : V' ∈ 𝓝 (s₀, p) := by
    refine Filter.inter_mem (hU₀.mem_nhds hmem) ?_
    refine ContinuousAt.preimage_mem_nhds (hΦcd.continuousAt_fderiv hn0) ?_
    refine hInvOpen.mem_nhds ?_
    change fderiv ℝ (fun x : ℝ × E => (x.1, G x)) (s₀, p) ∈
      {T : (ℝ × E) →L[ℝ] (ℝ × F) | T.IsInvertible}
    rw [hΦfderiv]
    exact ⟨e₀, rfl⟩
  -- the target region on which `Φo.symm` is `C^∞`
  let Z : Set (ℝ × F) := Φo.target ∩ Φo.symm ⁻¹' V'
  have hZopen : IsOpen Z :=
    Φo.continuousOn_invFun.isOpen_inter_preimage Φo.open_target hV'open
  have hq0Z : (s₀, G (s₀, p)) ∈ Z := by
    refine ⟨htgt, ?_⟩
    show Φo.symm (s₀, G (s₀, p)) ∈ V'
    rw [hΨq]
    refine ⟨hmem, ?_⟩
    change fderiv ℝ (fun x : ℝ × E => (x.1, G x)) (s₀, p) ∈
      {T : (ℝ × E) →L[ℝ] (ℝ × F) | T.IsInvertible}
    rw [hΦfderiv]
    exact ⟨e₀, rfl⟩
  have hΨcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Φo.symm : ℝ × F → ℝ × E) Z := by
    rw [hZopen.contDiffOn_iff]
    intro y hy
    have hyt : y ∈ Φo.target := hy.1
    obtain ⟨hyU, hyInv⟩ := hy.2
    obtain ⟨ey, hey⟩ := hyInv
    have hey' : (ey : ℝ × E →L[ℝ] ℝ × F) =
        fderiv ℝ (fun x : ℝ × E => (x.1, G x)) (Φo.symm y) := hey
    have h2 : HasFDerivAt (fun x : ℝ × E => (x.1, G x))
        (ey : ℝ × E →L[ℝ] ℝ × F) (Φo.symm y) := by
      have h3 : HasFDerivAt (fun x : ℝ × E => (x.1, G x))
          (fderiv ℝ (fun x : ℝ × E => (x.1, G x)) (Φo.symm y)) (Φo.symm y) :=
        ((hΦon.contDiffAt (hU₀.mem_nhds hyU)).differentiableAt hn0).hasFDerivAt
      simpa [hey'] using h3
    have hF : HasFDerivAt (⇑Φo) (ey : ℝ × E →L[ℝ] ℝ × F) (Φo.symm y) := by
      rw [hΦo_coe]
      exact h2
    have hG' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Φo) (Φo.symm y) := by
      rw [hΦo_coe]
      exact hΦon.contDiffAt (hU₀.mem_nhds hyU)
    exact Φo.contDiffAt_symm hyt hF hG'
  -- a product box inside the source, with `U_A ⊆ V`
  obtain ⟨O_A, U_A, hO_A, hU_A, hs0_A, hp_A, hU_A_V, hbox_src⟩ :
      ∃ (O_A : Set ℝ) (U_A : Set E), IsOpen O_A ∧ IsOpen U_A ∧ s₀ ∈ O_A ∧ p ∈ U_A ∧
        U_A ⊆ V ∧ O_A ×ˢ U_A ⊆ Φo.source := by
    obtain ⟨O₁, U₁, hO₁, hs0_1, hU₁, hp_1, hbox₁⟩ :=
      box_subset_of_mem_nhds (Φo.open_source.mem_nhds hsrc)
    refine ⟨O₁, U₁ ∩ V, hO₁, hU₁.inter hV, hs0_1, ⟨hp_1, hpV⟩, Set.inter_subset_right, ?_⟩
    exact (Set.prod_mono subset_rfl Set.inter_subset_left).trans hbox₁
  let Abox : Set (ℝ × E) := O_A ×ˢ U_A
  have hAbox_open : IsOpen Abox := hO_A.prod hU_A
  let R : Set (ℝ × F) := Φo.target ∩ Φo.symm ⁻¹' Abox
  have hRopen : IsOpen R := Φo.isOpen_inter_preimage_symm hAbox_open
  have hq0R : (s₀, G (s₀, p)) ∈ R := by
    refine ⟨htgt, ?_⟩
    show Φo.symm (s₀, G (s₀, p)) ∈ Abox
    rw [hΨq]
    exact ⟨hs0_A, hp_A⟩
  -- the final box
  obtain ⟨O₁, W, hO₁, hs0_1, hW, hg0W, hbox1⟩ :=
    box_subset_of_mem_nhds (Filter.inter_mem (hRopen.mem_nhds hq0R) (hZopen.mem_nhds hq0Z))
  refine ⟨O₁ ∩ O_A, U_A, W, fun s z => (Φo.symm (s, z)).2,
    hO₁.inter hO_A, ⟨hs0_1, hs0_A⟩, hU_A, hp_A, hU_A_V, hW, hg0W, ?_, ?_, ?_⟩
  · -- smoothness
    refine (hΨcd.snd).mono ?_
    intro z hz
    exact (hbox1 ⟨hz.1.1, hz.2⟩).2
  · -- `h s` is a left inverse of `G (s, ·)` on `U`
    intro s hs y hy
    have hsy : (s, y) ∈ Φo.source := hbox_src ⟨hs.2, hy⟩
    have h1 : Φo.symm (Φo (s, y)) = (s, y) := Φo.leftInvOn hsy
    rw [hΦo_coe] at h1
    exact congrArg Prod.snd h1
  · -- `h s` is a right inverse of `G (s, ·)` on `W`, with values in `U`
    intro s hs z hz
    have hmem1 : (s, z) ∈ R ∩ Z := hbox1 ⟨hs.1, hz⟩
    have hR : (s, z) ∈ R := hmem1.1
    have h1 : Φo (Φo.symm (s, z)) = (s, z) := Φo.rightInvOn hR.1
    rw [hΦo_coe] at h1
    have h1' : ((Φo.symm (s, z)).1, G ((Φo.symm (s, z)).1, (Φo.symm (s, z)).2)) = (s, z) := h1
    have hfst : (Φo.symm (s, z)).1 = s := congrArg Prod.fst h1'
    have h2 : G ((Φo.symm (s, z)).1, (Φo.symm (s, z)).2) = z := congrArg Prod.snd h1'
    rw [hfst] at h2
    exact ⟨hR.2.2, h2⟩

end Work.Drive.PushDisc

namespace Work.Drive.PushDisc

open scoped Topology

/-- **A second form of the repair, which keeps every clause of the target.**

If one insists on both the surjectivity clause `G (s, y) ∈ W` for the *left* inverse and the
containment `h s z ∈ U` for the right inverse, then the single neighbourhood `U` has to be split into
two: the set `U` which receives the values of `h` (and which is contained in the prescribed `V`), and
a smaller open set `U'` on which `G (s, ·)` is a left inverse of `h s`.  This is the statement proved
here; `localInverseFamilyTwoSided_repair` is the version obtained instead by deleting the clause
`G (s, y) ∈ W`.

Both statements come from the same inverse-function-theorem construction; this one is deduced from
`localInverseFamilyTwoSided_repair` by shrinking the "left" neighbourhood to one that the continuous
map `G` sends into `W`. -/
theorem localInverseFamilyTwoSided_repair_twoSets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : ℝ × E → F) (U₀ : Set (ℝ × E)) (hU₀ : IsOpen U₀) (s₀ : ℝ) (p : E)
    (hmem : (s₀, p) ∈ U₀) (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U₀)
    (hbij : Function.Bijective (fun v : E => fderiv ℝ G (s₀, p) (0, v)))
    (V : Set E) (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ (O : Set ℝ) (U U' : Set E) (W : Set F) (h : ℝ → F → E),
      IsOpen O ∧ s₀ ∈ O ∧ IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧ IsOpen U' ∧ p ∈ U' ∧ U' ⊆ U ∧
      IsOpen W ∧ G (s₀, p) ∈ W ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry h) (O ×ˢ W) ∧
      (∀ s ∈ O, ∀ y ∈ U', G (s, y) ∈ W ∧ h s (G (s, y)) = y) ∧
      (∀ s ∈ O, ∀ z ∈ W, h s z ∈ U ∧ G (s, h s z) = z) := by
  obtain ⟨O, U, W, h, hO, hs0O, hU, hpU, hUV, hW, hg0W, hsm, hleft, hright⟩ :=
    localInverseFamilyTwoSided_repair G U₀ hU₀ s₀ p hmem hG hbij V hV hpV
  have hGc : ContinuousAt G (s₀, p) :=
    (hG.contDiffAt (hU₀.mem_nhds hmem)).continuousAt
  obtain ⟨O₂, U₂, hO₂o, hs0₂, hU₂o, hp₂, hsub⟩ :=
    box_subset_of_mem_nhds (hGc (hW.mem_nhds hg0W))
  refine ⟨O ∩ O₂, U, U₂ ∩ U, W, h, hO.inter hO₂o, ⟨hs0O, hs0₂⟩, hU, hpU, hUV,
    hU₂o.inter hU, ⟨hp₂, hpU⟩, Set.inter_subset_right, hW, hg0W, ?_, ?_,
    fun s hs z hz => hright s hs.1 z hz⟩
  · exact hsm.mono (Set.prod_mono Set.inter_subset_left subset_rfl)
  · intro s hs y hy
    exact ⟨hsub ⟨hs.2, hy.1⟩, hleft s hs.1 y hy.2⟩

end Work.Drive.PushDisc
