import Mathlib
import Submission.Work.Noncompact.parity_sum
import Submission.Work.Noncompact.reduce_steps_on
import Submission.Work.Noncompact.exists_local_map
import Submission.Work.Noncompact.exists_bounded_injective_map
import Submission.Work.Noncompact.exists_proper_contMDiff_nonneg
import Submission.Work.Noncompact.exists_pack_data
import Submission.Work.Projection.exists_good_direction_ne_zero
import Submission.Work.Projection.immersion
import Submission.Work.Embedding.Proper
import Submission.Work.Projection.compact_embedding

/-!
# The weak Whitney embedding theorem for second countable manifolds

Every smooth `n`-manifold `M` (Hausdorff, second countable) embeds smoothly and immersively into
`ℝ^{2n+1}`.  The proof:

1. a nonnegative proper smooth `f : M → ℝ` (`exists_proper_contMDiff_nonneg`),
2. for every `i`, a smooth map `φ i : M → ℝ^{2n+1}` injective and immersive on the band
   `bandCore f i = f⁻¹'[i, i+1]` (`exists_local_map`, `reduce_steps_on`),
3. the parity (band) sum of step 2 gives an injective immersion `Φ : M → ℝ^{2n+1} × ℝ^{2n+1} × ℝ`
   (`exists_injective_immersion_of_local_maps`),
4. dimension reduction to `ℝ^{2n+1}` (`reduce_steps`),
5. bounding the image (`exists_bounded_injective_map`), adding the `f` coordinate and applying the
   projection argument with a *nonzero* direction (`exists_good_direction_ne_zero`): this preserves
   properness, since the projection `projVec u` of the packed pair `(e, f)` is `e - f • u` and `u`
   is nonzero.  A proper injective immersion is an embedding (`isEmbedding_of_isProperMap_injective`).
-/

open scoped Manifold ContDiff BigOperators
open Topology Set Function

namespace Work.Noncompact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]

/-- Chain rule: composing a smooth map with a continuous linear map between arbitrary normed
spaces. -/
lemma mfderiv_comp_clm_of {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) (e : M → F)
    (hsm : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ e) (x : M) :
    mfderiv (𝓡 n) 𝓘(ℝ, G) (⇑L ∘ e) x = L ∘L mfderiv (𝓡 n) 𝓘(ℝ, F) e x := by
  rw [mfderiv_comp x (f := e) (g := ⇑L) (L.differentiableAt.mdifferentiableAt)
    (hsm.mdifferentiableAt (by simp))]
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- **Weak Whitney embedding theorem, proper form**: a Hausdorff, second countable nonempty
smooth `n`-manifold embeds into `ℝ^{2n+1}` by a map which is proper (hence a closed embedding) and
an immersion. -/
theorem exists_proper_embedding_euclidean_weak [SecondCountableTopology M] [Nonempty M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2*n+1)),
      ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ e ∧ IsProperMap e ∧ Function.Injective e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) e x) := by
  classical
  haveI : SigmaCompactSpace M := by
    haveI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    exact sigmaCompactSpace_of_locallyCompact_secondCountable
  -- a nonnegative proper smooth function
  obtain ⟨f, hfsm, hfprop, hfnonneg⟩ := exists_proper_contMDiff_nonneg (I := 𝓡 n) (M := M)
  -- injective immersions on the bands
  have hbands : ∀ i : ℕ, ∃ φ : M → EuclideanSpace ℝ (Fin (2*n+1)),
      ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ φ ∧ Set.InjOn φ (bandCore f i) ∧
      ∀ x ∈ bandCore f i, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) φ x) := by
    intro i
    obtain ⟨m, φ, hsm, hinj, himm⟩ :=
      exists_local_map (n := n) (M := M) (bandCore f i)
        (hfprop.isCompact_preimage isCompact_Icc)
    exact reduce_steps_on m (bandCore f i) φ hsm hinj himm
  choose φ hφsm hφinj hφimm using hbands
  -- the parity sum
  obtain ⟨Φ, hΦsm, hΦinj, hΦimm⟩ :=
    exists_injective_immersion_of_local_maps (n := n) (f := f) hfsm hfnonneg φ hφsm hφinj hφimm
  -- dimension reduction
  obtain ⟨e₁, he₁sm, he₁inj, he₁imm⟩ :=
    Work.Projection.reduce_steps (n := n) (M := M) (2*n+2) Φ hΦsm hΦinj hΦimm
  -- bound the image, then add the height function
  obtain ⟨g, hgsm, hginj, hgimm, hgbdd⟩ := exists_bounded_injective_map (2*n+1)
  set e₂ : M → EuclideanSpace ℝ (Fin (2*n+1)) := fun x => g (e₁ x) with he₂
  have he₂sm : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ e₂ := hgsm.comp he₁sm
  have he₂inj : Function.Injective e₂ := hginj.comp he₁inj
  have he₂imm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) e₂ x) := by
    intro x
    have h := mfderiv_comp x (f := e₁) (g := g)
      (hgsm.mdifferentiableAt (by simp)) (he₁sm.mdifferentiableAt (by simp))
    change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) (g ∘ e₁) x)
    rw [h]
    exact (hgimm (e₁ x)).comp (he₁imm x)
  obtain ⟨P, hPinj, hPproj⟩ := exists_pack_data n
  set pairM : M → (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) := fun x => (e₂ x, f x) with hpairM
  have hpairMsm : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) ∞ pairM :=
    ContMDiff.prodMk_space he₂sm hfsm
  set Φ' : M → EuclideanSpace ℝ (Fin (2*n+2)) := fun x => P (pairM x) with hΦ'
  have hΦ'sm : ContMDiff (𝓡 n) (𝓡 (2*n+2)) ∞ Φ' := P.contMDiff.comp hpairMsm
  have hΦ'inj : Function.Injective Φ' := by
    intro x y hxy
    have h1 : pairM x = pairM y := hPinj hxy
    exact he₂inj (Prod.ext_iff.1 h1).1
  have hΦ'imm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+2)) Φ' x) := by
    intro x
    have hchain := mfderiv_comp_clm_of (n := n) (M := M) P pairM hpairMsm x
    have hzero : ∀ z : TangentSpace (𝓡 n) x,
        mfderiv (𝓡 n) (𝓡 (2*n+2)) Φ' x z = 0 → z = 0 := by
      intro z hz
      have h2 : (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z = 0 := by
        have hz' : (P ∘L mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z = 0 := by
          rw [← hchain]
          exact hz
        exact hPinj (hz'.trans (map_zero P).symm)
      have hfst := mfderiv_comp_clm_of (n := n) (M := M)
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ) pairM hpairMsm x
      have h4 : mfderiv (𝓡 n) (𝓡 (2*n+1)) e₂ x z = 0 := by
        change ((mfderiv (𝓡 n) (𝓡 (2*n+1))
          (⇑(ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ) ∘ pairM) x) z) = 0
        rw [hfst]
        change (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ)
          ((mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n+1)) × ℝ) pairM x) z) = 0
        rw [h2]
        exact map_zero _
      exact he₂imm x (by rw [h4, map_zero])
    intro z w hzw
    exact sub_eq_zero.mp (hzero (z - w) (by rw [map_sub, hzw, sub_self]))
  -- a nonzero good direction
  obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover n M
  obtain ⟨u, hu0, hu1, hu2⟩ :=
    Work.Projection.exists_good_direction_ne_zero (n := n) (k := 2*n+1) (le_refl _)
      Φ' hΦ'sm hΦ'inj hΦ'imm p hcov
  have hcpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hsm : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (fun x => Work.Projection.projVec u (Φ' x)) :=
    Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) Φ' hΦ'sm
  -- properness of the projected map
  have hproper : IsProperMap (fun x => Work.Projection.projVec u (Φ' x)) := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hsm.continuous, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine IsCompact.of_isClosed_subset
      (hfprop.isCompact_preimage (isCompact_Icc (a := (0:ℝ)) (b := (R+1)/‖u‖))) ?_ ?_
    · exact hK.isClosed.preimage hsm.continuous
    · intro x hx
      rw [mem_preimage, mem_Icc]
      refine ⟨hfnonneg x, ?_⟩
      have h1 : ‖Work.Projection.projVec u (Φ' x)‖ ≤ R := hR _ hx
      have h2 : Work.Projection.projVec u (Φ' x) = e₂ x - f x • u := by
        rw [hΦ', hpairM]
        exact hPproj u (e₂ x) (f x)
      rw [h2] at h1
      have h3 : ‖f x • u‖ - ‖e₂ x‖ ≤ ‖e₂ x - f x • u‖ := by
        have h := abs_norm_sub_norm_le (f x • u) (e₂ x)
        have h' : ‖f x • u - e₂ x‖ = ‖e₂ x - f x • u‖ := by
          rw [show f x • u - e₂ x = -(e₂ x - f x • u) by abel, norm_neg]
        rw [h'] at h
        exact le_trans (le_abs_self _) h
      have h4 : ‖f x‖ * ‖u‖ ≤ R + 1 := by
        have h5 : ‖f x • u‖ = ‖f x‖ * ‖u‖ := norm_smul _ _
        have h6 : ‖e₂ x‖ ≤ 1 := hgbdd (e₁ x)
        rw [h5] at h3
        linarith
      have h7 : ‖f x‖ ≤ (R+1)/‖u‖ := (le_div_iff₀ hcpos).2 h4
      rwa [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)] at h7
  exact ⟨fun x => Work.Projection.projVec u (Φ' x), hsm, hproper, hu1, fun x => by
      change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1))
        (⇑(Work.Projection.projVec u) ∘ Φ') x)
      rw [Work.Projection.mfderiv_comp_clm (Work.Projection.projVec u) Φ' hΦ'sm x]
      exact hu2 x⟩

/-- **Weak Whitney embedding theorem**: a Hausdorff, second countable smooth `n`-manifold embeds
smoothly and immersively into `ℝ^{2n+1}`. -/
theorem exists_embedding_euclidean_weak [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2*n+1)),
      ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ e ∧ IsEmbedding e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) e x) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x,
      ⟨⟨Subsingleton.elim _ _⟩, fun x => isEmptyElim x⟩, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨e, hsm, hprop, hinj, himm⟩ := exists_proper_embedding_euclidean_weak (n := n) (M := M)
    exact ⟨e, hsm, Work.Embedding.isEmbedding_of_isProperMap_injective hprop hinj, himm⟩

/-- **Whitney immersion theorem**: a Hausdorff, second countable smooth `n`-manifold immerses into
`ℝ^{2n}`.  The bad directions for the immersion condition have Hausdorff dimension at most
`2n - 1 < 2n`, so a projection direction avoiding them exists. -/
theorem exists_immersion_euclidean (hn : 1 ≤ n) [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2*n)),
      ContMDiff (𝓡 n) (𝓡 (2*n)) ∞ e ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n)) e x) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty M := hM
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · haveI := hM
    obtain ⟨e, hsm, -, -, himm⟩ := exists_proper_embedding_euclidean_weak (n := n) (M := M)
    obtain ⟨p, hcov⟩ := Work.Projection.exists_countable_chart_cover n M
    obtain ⟨u, hu⟩ :=
      Work.Projection.exists_good_direction_immersion (n := n) (k := 2*n) hn le_rfl e hsm himm p hcov
    refine ⟨fun x => Work.Projection.projVec u (e x),
      Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) e hsm, ?_⟩
    intro x
    change Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n)) (⇑(Work.Projection.projVec u) ∘ e) x)
    rw [Work.Projection.mfderiv_comp_clm (Work.Projection.projVec u) e hsm x]
    exact hu x

end

end Work.Noncompact
