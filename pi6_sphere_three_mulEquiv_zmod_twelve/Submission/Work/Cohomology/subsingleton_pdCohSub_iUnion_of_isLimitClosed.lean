import Mathlib
import Submission.Work.Cohomology.wsfDefs
import Submission.Work.Cohomology.rcSet_homology_succ_subsingleton_iff
import Submission.Work.Cohomology.rcSet_homology_zero_subsingleton_iff
import Submission.Work.Cohomology.rcResLM_surjective
import Submission.Work.Cohomology.rcKern_iUnion_limit

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The differential squared is zero on the relative cochain complex. -/
theorem rc_diff_comp_zero (A : Set X) (U : Set X) (n : ℕ) :
    (rcDiff A U (n+1)).comp (rcDiff A U n) = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.d_comp_d (rcSet A U) n (n+1) (n+2))
  simp only [rcSet_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero] at h
  exact h

/-- Restriction of relative cochains factorises through an intermediate set. -/
theorem rcResLM_trans {S S' T : Set X} (A : Set X) (h : S ⊆ S') (h' : S' ⊆ T) (n : ℕ)
    (x : ↥(rcKern A T n)) :
    rcResLM A (h.trans h') n x = rcResLM A h n (rcResLM A h' n x) := by
  rw [← LinearMap.comp_apply, rcResLM_comp A h h' n]

/-- The restriction of relative cochains along a self-inclusion is the identity. -/
theorem rcResLM_self (A : Set X) {S : Set X} (h : S ⊆ S) (n : ℕ) (x : ↥(rcKern A S n)) :
    rcResLM A h n x = x := by
  apply Subtype.ext
  rw [rcResLM_coe, pdIncl_self (TopCat.of X) S h, dualChainMap_id]
  rfl

/-- **The correction step.**  If `U ⊆ T`, `e` is a relative `(k+1)`-cocycle on `T` vanishing on
`U`, and `H^k(U) = H^{k+1}(T) = 0`, then `e` has a primitive on `T` that still vanishes on `U`. -/
theorem rc_patch_corr (A : Set X) {T U : Set X} (hUT : U ⊆ T) (k : ℕ)
    (hU : Subsingleton ((rcSet A U).homology k))
    (hT : Subsingleton ((rcSet A T).homology (k+1)))
    (e : ↥(rcKern A T (k+1))) (he : rcDiff A T (k+1) e = 0)
    (hre : rcResLM A hUT (k+1) e = 0) :
    ∃ z'' : ↥(rcKern A T k), rcDiff A T k z'' = e ∧ rcResLM A hUT k z'' = 0 := by
  rcases k with _ | k'
  · obtain ⟨z', hz'⟩ := (rcSet_homology_succ_subsingleton_iff A T 0).mp hT e he
    refine ⟨z', hz', ?_⟩
    have h1 : rcDiff A U 0 (rcResLM A hUT 0 z') = 0 := by
      rw [← rcResLM_comm A hUT 0 z', hz', hre]
    exact (rcSet_homology_zero_subsingleton_iff A U).mp hU _ h1
  · obtain ⟨z', hz'⟩ := (rcSet_homology_succ_subsingleton_iff A T (k'+1)).mp hT e he
    have h1 : rcDiff A U (k'+1) (rcResLM A hUT (k'+1) z') = 0 := by
      rw [← rcResLM_comm A hUT (k'+1) z', hz', hre]
    obtain ⟨th, hth⟩ := (rcSet_homology_succ_subsingleton_iff A U k').mp hU _ h1
    obtain ⟨tht, htht⟩ := rcResLM_surjective A hUT k' th
    refine ⟨z' - rcDiff A T k' tht, ?_, ?_⟩
    · rw [map_sub, hz', show rcDiff A T (k'+1) (rcDiff A T k' tht) = 0 from by
        rw [← LinearMap.comp_apply, rc_diff_comp_zero A T k', LinearMap.zero_apply], sub_zero]
    · rw [map_sub, rcResLM_comm A hUT k' tht, htht, hth, sub_self]

/-- A partial solution of the patching problem: the graph of a partially defined family of
primitives, whose domain is a down-set, whose values are primitives of the restrictions of `z` to
the pieces, and which is compatible with the restrictions. -/
abbrev RCSol (A : Set X) {Γ : Type} [LinearOrder Γ]
    (W : Γ → Set X) (hmono : Monotone W) {k : ℕ} (zW : (i : Γ) → ↥(rcKern A (W i) (k+1)))
    (G : Set (Σ γ : Γ, ↥(rcKern A (W γ) k))) : Prop :=
  (∀ γ (x y : ↥(rcKern A (W γ) k)),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G →
      (⟨γ, y⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G → x = y) ∧
  (∀ γ γ' (h : γ' ≤ γ) (x : ↥(rcKern A (W γ) k)),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G →
      ∃ y : ↥(rcKern A (W γ') k), (⟨γ', y⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G) ∧
  (∀ γ (x : ↥(rcKern A (W γ) k)),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G → rcDiff A (W γ) k x = zW γ) ∧
  (∀ γ γ' (h : γ' ≤ γ) (x : ↥(rcKern A (W γ) k)) (y : ↥(rcKern A (W γ') k)),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G →
      (⟨γ', y⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ G →
      rcResLM A (hmono h) k x = y)

/-- **The patching lemma.**  Let `W : Γ → Set X` be an increasing family of open sets, continuous
at limit indices, and let `z` be a relative `(k+1)`-cocycle on `⋃ i, W i`.  If the relative
cohomology of every piece vanishes in degrees `≤ k+1`, then `z` is a coboundary on the union.

The primitive is built as a compatible family on the pieces by a transfinite argument (Zorn's
lemma applied to the partially defined compatible families of primitives), and then glued to the
union by `rcKern_iUnion_limit`. -/
theorem rc_patch (A : Set X) {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (W : Γ → Set X)
    (hopen : ∀ i, IsOpen (W i)) (hmono : Monotone W)
    (hcont : ∀ γ, (∃ δ, δ < γ) → (∀ δ, δ < γ → ∃ ε, δ < ε ∧ ε < γ) →
      W γ = ⋃ δ < γ, W δ)
    (k : ℕ) (hsub : ∀ i j, j ≤ k+1 → Subsingleton ((rcSet A (W i)).homology j))
    (z : ↥(rcKern A (⋃ i, W i) (k+1))) (hz : rcDiff A (⋃ i, W i) (k+1) z = 0) :
    ∃ w : ↥(rcKern A (⋃ i, W i) k), rcDiff A (⋃ i, W i) k w = z := by
  classical
  -- the restrictions of `z` to the pieces, and their compatibility
  let zW : (i : Γ) → ↥(rcKern A (W i) (k+1)) :=
    fun i => rcResLM A (Set.subset_iUnion W i) (k+1) z
  have hzW : ∀ i, rcDiff A (W i) (k+1) (zW i) = 0 := by
    intro i
    show rcDiff A (W i) (k+1) (rcResLM A (Set.subset_iUnion W i) (k+1) z) = 0
    rw [← rcResLM_comm A (Set.subset_iUnion W i) (k+1) z, hz, map_zero]
  have hzWres : ∀ {δ γ : Γ} (h : δ ≤ γ), rcResLM A (hmono h) (k+1) (zW γ) = zW δ := by
    intro δ γ h
    show rcResLM A (hmono h) (k+1) (rcResLM A (Set.subset_iUnion W γ) (k+1) z)
        = rcResLM A (Set.subset_iUnion W δ) (k+1) z
    rw [rcResLM_trans A (hmono h) (Set.subset_iUnion W γ) (k+1) z]
  -- Zorn: maximal partial solution
  have hchain : ∀ c ⊆ {G | RCSol A W hmono zW G}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {G | RCSol A W hmono zW G}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc
    have hcomp2 : ∀ ⦃s t⦄, s ∈ c → t ∈ c → s ⊆ t ∨ t ⊆ s := by
      intro s t hs ht
      rcases eq_or_ne s t with rfl | hne
      · exact Or.inl (Set.Subset.refl _)
      · exact hcc hs ht hne
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro γ x y hx hy
      obtain ⟨s, hsc, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨t, htc, hyt⟩ := Set.mem_sUnion.mp hy
      rcases hcomp2 hsc htc with hst | hts
      · exact (hc htc).1 γ x y (hst hxs) hyt
      · exact (hc hsc).1 γ x y hxs (hts hyt)
    · intro γ γ' h x hx
      obtain ⟨s, hsc, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨y, hy⟩ := (hc hsc).2.1 γ γ' h x hxs
      exact ⟨y, Set.subset_sUnion_of_mem hsc hy⟩
    · intro γ x hx
      obtain ⟨s, hsc, hxs⟩ := Set.mem_sUnion.mp hx
      exact (hc hsc).2.2.1 γ x hxs
    · intro γ γ' h x y hx hy
      obtain ⟨s, hsc, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨t, htc, hyt⟩ := Set.mem_sUnion.mp hy
      rcases hcomp2 hsc htc with hst | hts
      · exact (hc htc).2.2.2 γ γ' h x y (hst hxs) hyt
      · exact (hc hsc).2.2.2 γ γ' h x y hxs (hts hyt)
  obtain ⟨m, hmmem, hmmax⟩ := zorn_subset {G | RCSol A W hmono zW G} hchain
  obtain ⟨hmm1, hmm2, hmm3, hmm4⟩ := hmmem
  -- the domain of `m` is all of `Γ`
  have htotal : ∀ γ : Γ, ∃ x : ↥(rcKern A (W γ) k),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨γ, hγ⟩ := hcon
    -- `γ` is the least index without a value
    have hne : (∃ γ' : Γ, ∀ x : ↥(rcKern A (W γ') k),
        (⟨γ', x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m → False) := ⟨γ, hγ⟩
    obtain ⟨γ₀, hγ₀, hγ₀min⟩ := WellFounded.has_min wellFounded_lt
      {γ' : Γ | ∀ x : ↥(rcKern A (W γ') k),
        (⟨γ', x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m → False} hne
    -- every index below `γ₀` has a value
    have hδ : ∀ δ, δ < γ₀ → ∃ x : ↥(rcKern A (W δ) k),
        (⟨δ, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m := by
      intro δ hδ
      by_contra hh
      exact hγ₀min δ (fun x hx => hh ⟨x, hx⟩) hδ
    -- the family of values below `γ₀`
    let f : (δ : ↥(Set.Iio γ₀)) → ↥(rcKern A (W δ.1) k) :=
      fun δ => Classical.choose (hδ δ.1 δ.2)
    have hfm : ∀ δ : ↥(Set.Iio γ₀),
        (⟨δ.1, f δ⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m :=
      fun δ => Classical.choose_spec (hδ δ.1 δ.2)
    have hfcomp : ∀ (i j : ↥(Set.Iio γ₀)) (hij : i ≤ j),
        rcResLM A (hmono hij) k (f j) = f i := by
      intro i j hij
      exact hmm4 j.1 i.1 hij (f j) (f i) (hfm j) (hfm i)
    -- a value at `γ₀`, compatible with the family below
    have hnew : ∃ v : ↥(rcKern A (W γ₀) k), rcDiff A (W γ₀) k v = zW γ₀ ∧
        ∀ δ : ↥(Set.Iio γ₀), rcResLM A (hmono (le_of_lt δ.2)) k v = f δ := by
      by_cases hpred : ∃ δ : Γ, δ < γ₀
      · -- there are predecessors: glue the family, lift it, correct it
        have hmono' : Monotone (fun δ : ↥(Set.Iio γ₀) => W δ.1) := fun a b hab => hmono hab
        obtain ⟨g, hg, -⟩ := (rcKern_iUnion_limit A (fun δ : ↥(Set.Iio γ₀) => W δ.1)
          (fun δ => hopen δ.1) hmono' k f).mpr hfcomp
        have hUsub : (⋃ δ : ↥(Set.Iio γ₀), W δ.1) ⊆ W γ₀ := by
          intro x hx
          obtain ⟨δ, hxδ⟩ := Set.mem_iUnion.mp hx
          exact hmono (le_of_lt δ.2) hxδ
        obtain ⟨v0, hv0⟩ := rcResLM_surjective A hUsub k g
        -- vanishing of `H^k` on the union of the pieces below `γ₀`
        have hU : Subsingleton ((rcSet A (⋃ δ : ↥(Set.Iio γ₀), W δ.1)).homology k) := by
          by_cases hsucc : ∃ δ, δ < γ₀ ∧ ∀ ε, ε < γ₀ → ε ≤ δ
          · obtain ⟨δ0, hδ0γ, hδ0max⟩ := hsucc
            have hUeq : (⋃ δ : ↥(Set.Iio γ₀), W δ.1) = W δ0 := by
              apply Set.Subset.antisymm
              · intro x hx
                obtain ⟨δ, hxδ⟩ := Set.mem_iUnion.mp hx
                exact hmono (hδ0max δ.1 δ.2) hxδ
              · intro x hx
                exact Set.mem_iUnion.mpr ⟨⟨δ0, hδ0γ⟩, hx⟩
            exact hUeq.symm ▸ (hsub δ0 k (Nat.le_succ k))
          · -- no maximal predecessor: `hcont` applies
            have hlim : ∀ δ, δ < γ₀ → ∃ ε, δ < ε ∧ ε < γ₀ := by
              intro δ hδ
              by_contra hcon
              exact hsucc ⟨δ, hδ, fun ε hε => le_of_not_gt (fun hlt => hcon ⟨ε, hlt, hε⟩)⟩
            have hUeq : (⋃ δ : ↥(Set.Iio γ₀), W δ.1) = W γ₀ := by
              rw [Set.iUnion_subtype]
              exact (hcont γ₀ hpred hlim).symm
            exact hUeq.symm ▸ (hsub γ₀ k (Nat.le_succ k))
        -- the obstruction is a cocycle vanishing on the pieces below `γ₀`
        have he : rcDiff A (W γ₀) (k+1) (rcDiff A (W γ₀) k v0 - zW γ₀) = 0 := by
          rw [map_sub, show rcDiff A (W γ₀) (k+1) (rcDiff A (W γ₀) k v0) = 0 from by
            rw [← LinearMap.comp_apply, rc_diff_comp_zero A (W γ₀) k, LinearMap.zero_apply],
            hzW γ₀, sub_zero]
        have hre : rcResLM A hUsub (k+1) (rcDiff A (W γ₀) k v0 - zW γ₀) = 0 := by
          apply rcRestrict_injective A (fun δ : ↥(Set.Iio γ₀) => W δ.1)
            (fun δ => hopen δ.1) hmono' (k+1)
          intro δ
          have h2 : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub) k v0
              = f δ := by
            rw [rcResLM_trans A _ hUsub k, hv0]
            exact hg δ
          have h3 : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub)
              (k+1) (zW γ₀) = zW δ.1 :=
            hzWres (le_of_lt δ.2)
          have hmain : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub)
                (k+1) (rcDiff A (W γ₀) k v0 - zW γ₀) = 0 := by
            rw [map_sub, rcResLM_comm A _ k v0, h2, h3, hmm3 δ.1 (f δ) (hfm δ), sub_self]
          have hcongr : rcResLM A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ) (k+1)
                (rcResLM A hUsub (k+1) (rcDiff A (W γ₀) k v0 - zW γ₀))
              = rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub)
                  (k+1) (rcDiff A (W γ₀) k v0 - zW γ₀) :=
            (rcResLM_trans A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ) hUsub (k+1)
              (rcDiff A (W γ₀) k v0 - zW γ₀)).symm
          rw [hcongr, hmain]
        obtain ⟨z'', hz''1, hz''2⟩ := rc_patch_corr A hUsub k hU (hsub γ₀ (k+1) le_rfl)
          (rcDiff A (W γ₀) k v0 - zW γ₀) he hre
        refine ⟨v0 - z'', ?_, ?_⟩
        · rw [map_sub, hz''1, sub_sub_cancel]
        · intro δ
          have hA : rcResLM A (hmono (le_of_lt δ.2)) k (v0 - z'')
              = rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub) k
                  (v0 - z'') :=
            congrArg (fun g => g (v0 - z''))
              (rcResLM_proof_irrel (hmono (le_of_lt δ.2))
                ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ).trans hUsub) k)
          rw [hA, rcResLM_trans A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => W δ.1) δ) hUsub k]
          rw [map_sub, map_sub, hv0, hz''2, map_zero, sub_zero, hg δ]
      · -- no predecessors: any primitive works
        have hv : ∃ v : ↥(rcKern A (W γ₀) k), rcDiff A (W γ₀) k v = zW γ₀ :=
          (rcSet_homology_succ_subsingleton_iff A (W γ₀) k).mp (hsub γ₀ (k+1) le_rfl)
            (zW γ₀) (hzW γ₀)
        obtain ⟨v, hv1⟩ := hv
        exact ⟨v, hv1, fun δ => absurd ⟨δ.1, δ.2⟩ hpred⟩
    obtain ⟨v, hv1, hv2⟩ := hnew
    -- the extended partial solution
    have hγ₀f : ∀ x : ↥(rcKern A (W γ₀) k),
        (⟨γ₀, x⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m → False := hγ₀
    have hm' : (m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k))}) ∈
        {G | RCSol A W hmono zW G} := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- `m'` is the graph of a partial function
        rintro γ' x y (hx | hx) (hy | hy)
        · exact hmm1 γ' x y hx hy
        · rw [Set.mem_singleton_iff] at hy
          rw [Sigma.mk.injEq] at hy
          obtain ⟨hγ', -⟩ := hy
          subst hγ'
          exact absurd hx (hγ₀f x)
        · rw [Set.mem_singleton_iff] at hx
          rw [Sigma.mk.injEq] at hx
          obtain ⟨hγ', -⟩ := hx
          subst hγ'
          exact absurd hy (hγ₀f y)
        · rw [Set.mem_singleton_iff] at hx hy
          rw [Sigma.mk.injEq] at hx
          obtain ⟨hγ', hxv⟩ := hx
          subst hγ'
          rw [Sigma.mk.injEq] at hy
          obtain ⟨-, hyv⟩ := hy
          rw [eq_of_heq hxv, eq_of_heq hyv]
      · -- the domain is still a down-set
        rintro γ' γ'' h x (hx | hx)
        · obtain ⟨y, hy⟩ := hmm2 γ' γ'' h x hx
          exact ⟨y, Or.inl hy⟩
        · rw [Set.mem_singleton_iff] at hx
          rw [Sigma.mk.injEq] at hx
          obtain ⟨hγ', -⟩ := hx
          rw [hγ'] at h
          rcases lt_or_eq_of_le h with hlt | heq
          · exact ⟨_, Or.inl (Classical.choose_spec (hδ γ'' hlt))⟩
          · rw [heq]
            exact ⟨v, Or.inr (Set.mem_singleton _)⟩
      · -- the new value is a primitive
        rintro γ' x (hx | hx)
        · exact hmm3 γ' x hx
        · rw [Set.mem_singleton_iff] at hx
          rw [Sigma.mk.injEq] at hx
          obtain ⟨hγ', hxv⟩ := hx
          subst hγ'
          rw [eq_of_heq hxv]
          exact hv1
      · -- the new value is compatible with the family below `γ₀`
        rintro γ' γ'' h x y (hx | hx) (hy | hy)
        · exact hmm4 γ' γ'' h x y hx hy
        · -- `y` is the new element and `x ∈ m`
          rw [Set.mem_singleton_iff] at hy
          rw [Sigma.mk.injEq] at hy
          obtain ⟨hγ'', -⟩ := hy
          rw [hγ''] at h
          obtain ⟨z, hz⟩ := hmm2 γ' γ₀ h x hx
          exact absurd hz (hγ₀f z)
        · -- `x` is the new element and `y ∈ m`
          rw [Set.mem_singleton_iff] at hx
          rw [Sigma.mk.injEq] at hx
          obtain ⟨hγ', hxv⟩ := hx
          rw [hγ'] at h
          subst hγ'
          rcases lt_or_eq_of_le h with hlt | heq
          · have hyf : y = f ⟨γ'', hlt⟩ := hmm1 γ'' y (f ⟨γ'', hlt⟩) hy (hfm ⟨γ'', hlt⟩)
            rw [eq_of_heq hxv, hyf]
            exact hv2 ⟨γ'', hlt⟩
          · subst heq
            exact absurd hy (hγ₀f y)
        · -- both are the new element
          rw [Set.mem_singleton_iff] at hx hy
          rw [Sigma.mk.injEq] at hx hy
          obtain ⟨hγ', hxv⟩ := hx
          obtain ⟨hγ'', hyv⟩ := hy
          rw [hγ'] at h
          subst hγ'
          subst hγ''
          rw [eq_of_heq hxv, eq_of_heq hyv]
          exact rcResLM_self A (hmono h) k v
    -- contradiction with maximality
    have hle : m ⊆ m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k))} := Set.subset_union_left
    have hsub' : m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k))} ⊆ m :=
      hmmax (y := m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k))}) hm' hle
    exact hγ₀f v (hsub' (Or.inr (Set.mem_singleton _)))
  -- the global family and its gluing
  let fFin : (γ : Γ) → ↥(rcKern A (W γ) k) := fun γ => Classical.choose (htotal γ)
  have hfFin : ∀ γ, (⟨γ, fFin γ⟩ : Σ γ : Γ, ↥(rcKern A (W γ) k)) ∈ m :=
    fun γ => Classical.choose_spec (htotal γ)
  have hfFincomp : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (fFin j) = fFin i :=
    fun i j hij => hmm4 j i hij (fFin j) (fFin i) (hfFin j) (hfFin i)
  obtain ⟨w, hw, -⟩ := (rcKern_iUnion_limit A W hopen hmono k fFin).mpr hfFincomp
  refine ⟨w, ?_⟩
  have hzero : rcDiff A (⋃ i, W i) k w - z = 0 := by
    refine rcRestrict_injective A W hopen hmono (k+1) (rcDiff A (⋃ i, W i) k w - z) ?_
    intro i
    show rcResLM A (Set.subset_iUnion W i) (k+1) (rcDiff A (⋃ i, W i) k w - z) = 0
    rw [map_sub, rcResLM_comm A (Set.subset_iUnion W i) k w, hw i]
    show rcDiff A (W i) k (fFin i) - rcResLM A (Set.subset_iUnion W i) (k+1) z = 0
    rw [hmm3 i (fFin i) (hfFin i)]
    exact sub_self _
  exact sub_eq_zero.mp hzero

/-- **Transfinite limit step for the relative cohomology of the honest relative cochain complex,
for a family that is continuous at its limit indices.**  Let `Γ` be a well-founded linear order and
`W : Γ → Set X` an increasing family of open sets which is *limit-continuous*: every `γ` that has
predecessors but no maximal predecessor satisfies `W γ = ⋃ δ < γ, W δ`.  If for every `γ` and every
`j ≤ d` the relative cohomology `H^j(W γ, W γ ∩ A) = pdCohSub X A (W γ) j` vanishes, then so does
`H^j(⋃ γ, W γ, ·)` for every `j ≤ d`.

This is the "limit case" of the transfinite exhaustion argument; unlike
`Work.Cohomology.subsingleton_pdCohSub_union_of_wellFounded` it does **not** claim the result for
families that jump at limit indices.

PROOF PLAN (patching of primitives, by well-founded recursion on `γ`).

For `j = 0`: a relative `0`-cocycle on `⋃ γ, W γ` restricts to `0` on each `W γ` by hypothesis
(`H^0(W γ) = 0`), and every vertex of the union lies in some `W γ`, so it is `0`.

For `j ≥ 1`, fix a relative `j`-cocycle `α` on `Z := ⋃ γ, W γ`; we must produce a relative
`(j-1)`-cochain `β` on `Z` with `dβ = α`.  Note `C^*(Z) = lim_γ C^*(W γ)` (a singular simplex of
`Z` has compact image, hence lies in some `W γ` by monotonicity), and the restrictions
`ρ_{δ,γ} : C^*(W γ) → C^*(W δ)` are cochain maps.  Build a *compatible* family
`β γ ∈ C^{j-1}(W γ, W γ ∩ A)` with `ρ_{δ,γ}(β γ) = β δ` and `d(β γ) = α|_{W γ}`:

* if `γ` has no predecessor, take any primitive of `α|_{W γ}` (exists as `H^j(W γ) = 0`);
* if `γ` has a maximal predecessor `δ`: take any primitive `β'` of `α|_{W γ}`; then
  `c := ρ_{δ,γ}(β') - β δ` is a relative `(j-1)`-cocycle on `W δ`, hence `c = dη` for some
  relative `(j-2)`-cochain `η` on `W δ` (as `H^{j-1}(W δ) = 0`); take any *section* `η̃` of the
  restriction `C^{j-2}(W γ) → C^{j-2}(W δ)` on relative cochains — the dual of
  `Work.Cohomology.chainRetract` (`cf. Work.Cohomology.surjective_restr`) preserves relative
  cochains, since a simplex of `W γ` mapping into `W δ ∩ A` is an `A`-simplex of `W δ` — and set
  `β γ := β' - dη̃`; then `ρ_{δ,γ}(β γ) = ρ(β') - d(ρ(η̃)) = ρ(β') - dη = β δ` because `ρ` is a
  cochain map.  Compatibility with all smaller indices follows from `≤ δ`;
* if `γ` has predecessors but no maximal one: for a singular `(j-1)`-simplex `σ` of `W γ` the
  image of `σ` is compact and contained in `W γ = ⋃ δ < γ, W δ`, so by monotonicity and
  `IsCompact.elim_finite_subcover` it is contained in some single `W δ`, `δ < γ`; set
  `β γ(σ) := β δ(σ)` (well defined by compatibility of the `β δ`), which is a relative cochain
  because a simplex with image in `A` lying in `W δ` is an `A`-simplex of `W δ`.  Then
  `d(β γ) = α|_{W γ}`: for a `j`-simplex `τ` of `W γ` contained in `W δ` all faces
  `∂_i τ` are contained in `W δ`, so `(d β γ)(τ) = (d β δ)(τ) = α(τ)`.

Finally `β` on `Z` is defined by `β(σ) := β γ(σ)` for any `γ` with the image of `σ` inside `W γ`
(well defined by compatibility), and `dβ = α` by the same face argument on a `j`-simplex of `Z`,
using that its image lies in some `W γ`. -/
theorem subsingleton_pdCohSub_iUnion_of_isLimitClosed {X : Type} [TopologicalSpace X] (A : Set X)
    {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (W : Γ → Set X)
    (hopen : ∀ i, IsOpen (W i)) (hmono : Monotone W)
    (hcont : ∀ γ, (∃ δ, δ < γ) → (∀ δ, δ < γ → ∃ ε, δ < ε ∧ ε < γ) →
      W γ = ⋃ δ < γ, W δ)
    (d : ℕ)
    (h : ∀ i j, j ≤ d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (W i) j)) :
    ∀ j, j ≤ d → Subsingleton (Work.Cohomology.pdCohSub (TopCat.of X) A (⋃ i, W i) j) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [← rcSet_homology_eq A (⋃ i, W i) 0]
    rw [rcSet_homology_zero_subsingleton_iff]
    intro z hz
    refine rcRestrict_injective A W hopen hmono 0 z ?_
    intro i
    have h1 : rcDiff A (W i) 0 (rcResLM A (Set.subset_iUnion W i) 0 z) = 0 := by
      rw [← rcResLM_comm A (Set.subset_iUnion W i) 0 z, hz, map_zero]
    exact (rcSet_homology_zero_subsingleton_iff A (W i)).mp (h i 0 (Nat.zero_le d)) _ h1
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
    rw [← rcSet_homology_eq A (⋃ i, W i) (k+1)]
    rw [rcSet_homology_succ_subsingleton_iff]
    intro z hz
    exact rc_patch A W hopen hmono hcont k (fun i j' hj' => h i j' (le_trans hj' hj)) z hz

end

end Work.Cohomology
