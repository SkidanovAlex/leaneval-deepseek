import Mathlib
import Submission.Work.Cohomology.wsfDefs
import Submission.Work.Cohomology.rcKern_iUnion_limit
import Submission.Work.Cohomology.rcResLM_surjective
import Submission.Work.Cohomology.rcSet_homology_succ_subsingleton_iff
import Submission.Work.Cohomology.rcSet_homology_zero_subsingleton_iff
import Submission.Work.Cohomology.subsingleton_pdCohSub_iUnion_of_isLimitClosed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.Thom

noncomputable section

/-- **Correction of a primitive.**  Let `U ⊆ T`, let `e` be a relative `(k+1)`-cochain on `T`
vanishing on `U` and let `z'` be a relative `k`-cochain on `T` with `dz' = e`.  If
`H^k(U, U ∩ A) = 0`, then `e` has a primitive on `T` which still vanishes on `U`: `z'` is adjusted
by the differential of a lift of a primitive of its own restriction to `U`.

This is the correction step of the patching argument, with the vanishing hypothesis
`H^{k+1}(T) = 0` of `Work.Cohomology.rc_patch_corr` replaced by the *given* primitive `z'` of `e`. -/
theorem rc_correction_of_primitive {X : Type} [TopologicalSpace X] (A : Set X) {T U : Set X}
    (hUT : U ⊆ T) (k : ℕ) (hU : Subsingleton ((rcSet A U).homology k))
    (e : ↥(rcKern A T (k+1))) (hre : rcResLM A hUT (k+1) e = 0)
    (z' : ↥(rcKern A T k)) (hz' : rcDiff A T k z' = e) :
    ∃ z'' : ↥(rcKern A T k), rcDiff A T k z'' = e ∧ rcResLM A hUT k z'' = 0 := by
  rcases k with _ | k'
  · -- the restriction of `z'` to `U` is a `0`-cocycle, hence vanishes
    have h1 : rcDiff A U 0 (rcResLM A hUT 0 z') = 0 := by
      rw [← rcResLM_comm A hUT 0 z', hz', hre]
    exact ⟨z', hz', (rcSet_homology_zero_subsingleton_iff A U).mp hU _ h1⟩
  · -- kill the restriction of `z'` to `U` by the differential of a lifted primitive
    have h1 : rcDiff A U (k'+1) (rcResLM A hUT (k'+1) z') = 0 := by
      rw [← rcResLM_comm A hUT (k'+1) z', hz', hre]
    obtain ⟨th, hth⟩ := (rcSet_homology_succ_subsingleton_iff A U k').mp hU _ h1
    obtain ⟨tht, htht⟩ := rcResLM_surjective A hUT k' th
    refine ⟨z' - rcDiff A T k' tht, ?_, ?_⟩
    · rw [map_sub, hz', show rcDiff A T (k'+1) (rcDiff A T k' tht) = 0 from by
        rw [← LinearMap.comp_apply, rc_diff_comp_zero A T k', LinearMap.zero_apply], sub_zero]
    · rw [map_sub, rcResLM_comm A hUT k' tht, htht, hth, sub_self]

/-- **Primitives over a transfinite union of pieces.**  Let `V : Γ → Set X` be an increasing family
of open sets, continuous at limit indices, let `k : ℕ` and let `H^k(V i, V i ∩ A) = 0` for every
`i`.  If a relative `(k+1)`-cocycle `z` on `⋃ i, V i` restricts to a coboundary on *every piece*
`V i`, then `z` is a coboundary on the union.

The primitive is built as a compatible family of primitives on the pieces by the transfinite patching
argument (Zorn on partial solutions), and then glued to the union by
`Work.Cohomology.rcKern_iUnion_limit`. -/
theorem rcPrimitive_of_piece_primitives {X : Type} [TopologicalSpace X] (A : Set X)
    {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (V : Γ → Set X)
    (hopen : ∀ i, IsOpen (V i)) (hmono : Monotone V)
    (hcont : ∀ γ, (∃ δ, δ < γ) → (∀ δ, δ < γ → ∃ ε, δ < ε ∧ ε < γ) → V γ = ⋃ δ < γ, V δ)
    (k : ℕ) (hvan : ∀ i, Subsingleton ((Work.Cohomology.rcSet A (V i)).homology k))
    (z : ↥(Work.Cohomology.rcKern A (⋃ i, V i) (k + 1)))
    (hz : Work.Cohomology.rcDiff A (⋃ i, V i) (k + 1) z = 0)
    (hprim : ∀ i, ∃ w : ↥(Work.Cohomology.rcKern A (V i) k),
        Work.Cohomology.rcDiff A (V i) k w =
          Work.Cohomology.rcResLM A (Set.subset_iUnion V i) (k + 1) z) :
    ∃ w : ↥(Work.Cohomology.rcKern A (⋃ i, V i) k),
      Work.Cohomology.rcDiff A (⋃ i, V i) k w = z := by
  classical
  -- the restrictions of `z` to the pieces, and their compatibility
  let zW : (i : Γ) → ↥(rcKern A (V i) (k+1)) :=
    fun i => rcResLM A (Set.subset_iUnion V i) (k+1) z
  have hzW : ∀ i, rcDiff A (V i) (k+1) (zW i) = 0 := by
    intro i
    show rcDiff A (V i) (k+1) (rcResLM A (Set.subset_iUnion V i) (k+1) z) = 0
    rw [← rcResLM_comm A (Set.subset_iUnion V i) (k+1) z, hz, map_zero]
  have hzWres : ∀ {δ γ : Γ} (h : δ ≤ γ), rcResLM A (hmono h) (k+1) (zW γ) = zW δ := by
    intro δ γ h
    show rcResLM A (hmono h) (k+1) (rcResLM A (Set.subset_iUnion V γ) (k+1) z)
        = rcResLM A (Set.subset_iUnion V δ) (k+1) z
    rw [rcResLM_trans A (hmono h) (Set.subset_iUnion V γ) (k+1) z]
  -- Zorn: maximal partial solution
  have hchain : ∀ c ⊆ {G | RCSol A V hmono zW G}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {G | RCSol A V hmono zW G}, ∀ s ∈ c, s ⊆ ub := by
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
  obtain ⟨m, hmmem, hmmax⟩ := zorn_subset {G | RCSol A V hmono zW G} hchain
  obtain ⟨hmm1, hmm2, hmm3, hmm4⟩ := hmmem
  -- the domain of `m` is all of `Γ`
  have htotal : ∀ γ : Γ, ∃ x : ↥(rcKern A (V γ) k),
      (⟨γ, x⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨γ, hγ⟩ := hcon
    -- `γ` is the least index without a value
    have hne : (∃ γ' : Γ, ∀ x : ↥(rcKern A (V γ') k),
        (⟨γ', x⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m → False) := ⟨γ, hγ⟩
    obtain ⟨γ₀, hγ₀, hγ₀min⟩ := WellFounded.has_min wellFounded_lt
      {γ' : Γ | ∀ x : ↥(rcKern A (V γ') k),
        (⟨γ', x⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m → False} hne
    -- every index below `γ₀` has a value
    have hδ : ∀ δ, δ < γ₀ → ∃ x : ↥(rcKern A (V δ) k),
        (⟨δ, x⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m := by
      intro δ hδ
      by_contra hh
      exact hγ₀min δ (fun x hx => hh ⟨x, hx⟩) hδ
    -- the family of values below `γ₀`
    let f : (δ : ↥(Set.Iio γ₀)) → ↥(rcKern A (V δ.1) k) :=
      fun δ => Classical.choose (hδ δ.1 δ.2)
    have hfm : ∀ δ : ↥(Set.Iio γ₀),
        (⟨δ.1, f δ⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m :=
      fun δ => Classical.choose_spec (hδ δ.1 δ.2)
    have hfcomp : ∀ (i j : ↥(Set.Iio γ₀)) (hij : i ≤ j),
        rcResLM A (hmono hij) k (f j) = f i := by
      intro i j hij
      exact hmm4 j.1 i.1 hij (f j) (f i) (hfm j) (hfm i)
    -- a value at `γ₀`, compatible with the family below
    have hnew : ∃ v : ↥(rcKern A (V γ₀) k), rcDiff A (V γ₀) k v = zW γ₀ ∧
        ∀ δ : ↥(Set.Iio γ₀), rcResLM A (hmono (le_of_lt δ.2)) k v = f δ := by
      by_cases hpred : ∃ δ : Γ, δ < γ₀
      · -- there are predecessors: glue the family, lift it, correct it
        have hmono' : Monotone (fun δ : ↥(Set.Iio γ₀) => V δ.1) := fun a b hab => hmono hab
        obtain ⟨g, hg, -⟩ := (rcKern_iUnion_limit A (fun δ : ↥(Set.Iio γ₀) => V δ.1)
          (fun δ => hopen δ.1) hmono' k f).mpr hfcomp
        have hUsub : (⋃ δ : ↥(Set.Iio γ₀), V δ.1) ⊆ V γ₀ := by
          intro x hx
          obtain ⟨δ, hxδ⟩ := Set.mem_iUnion.mp hx
          exact hmono (le_of_lt δ.2) hxδ
        obtain ⟨v0, hv0⟩ := rcResLM_surjective A hUsub k g
        -- vanishing of `H^k` on the union of the pieces below `γ₀`
        have hU : Subsingleton ((rcSet A (⋃ δ : ↥(Set.Iio γ₀), V δ.1)).homology k) := by
          by_cases hsucc : ∃ δ, δ < γ₀ ∧ ∀ ε, ε < γ₀ → ε ≤ δ
          · obtain ⟨δ0, hδ0γ, hδ0max⟩ := hsucc
            have hUeq : (⋃ δ : ↥(Set.Iio γ₀), V δ.1) = V δ0 := by
              apply Set.Subset.antisymm
              · intro x hx
                obtain ⟨δ, hxδ⟩ := Set.mem_iUnion.mp hx
                exact hmono (hδ0max δ.1 δ.2) hxδ
              · intro x hx
                exact Set.mem_iUnion.mpr ⟨⟨δ0, hδ0γ⟩, hx⟩
            exact hUeq.symm ▸ (hvan δ0)
          · -- no maximal predecessor: `hcont` applies
            have hlim : ∀ δ, δ < γ₀ → ∃ ε, δ < ε ∧ ε < γ₀ := by
              intro δ hδ
              by_contra hcon
              exact hsucc ⟨δ, hδ, fun ε hε => le_of_not_gt (fun hlt => hcon ⟨ε, hlt, hε⟩)⟩
            have hUeq : (⋃ δ : ↥(Set.Iio γ₀), V δ.1) = V γ₀ := by
              rw [Set.iUnion_subtype]
              exact (hcont γ₀ hpred hlim).symm
            exact hUeq.symm ▸ (hvan γ₀)
        -- the obstruction is a cocycle vanishing on the pieces below `γ₀`
        have he : rcDiff A (V γ₀) (k+1) (rcDiff A (V γ₀) k v0 - zW γ₀) = 0 := by
          rw [map_sub, show rcDiff A (V γ₀) (k+1) (rcDiff A (V γ₀) k v0) = 0 from by
            rw [← LinearMap.comp_apply, rc_diff_comp_zero A (V γ₀) k, LinearMap.zero_apply],
            hzW γ₀, sub_zero]
        have hre : rcResLM A hUsub (k+1) (rcDiff A (V γ₀) k v0 - zW γ₀) = 0 := by
          apply rcRestrict_injective A (fun δ : ↥(Set.Iio γ₀) => V δ.1)
            (fun δ => hopen δ.1) hmono' (k+1)
          intro δ
          have h2 : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub) k v0
              = f δ := by
            rw [rcResLM_trans A _ hUsub k, hv0]
            exact hg δ
          have h3 : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub)
              (k+1) (zW γ₀) = zW δ.1 :=
            hzWres (le_of_lt δ.2)
          have hmain : rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub)
                (k+1) (rcDiff A (V γ₀) k v0 - zW γ₀) = 0 := by
            rw [map_sub, rcResLM_comm A _ k v0, h2, h3, hmm3 δ.1 (f δ) (hfm δ), sub_self]
          have hcongr : rcResLM A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ) (k+1)
                (rcResLM A hUsub (k+1) (rcDiff A (V γ₀) k v0 - zW γ₀))
              = rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub)
                  (k+1) (rcDiff A (V γ₀) k v0 - zW γ₀) :=
            (rcResLM_trans A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ) hUsub (k+1)
              (rcDiff A (V γ₀) k v0 - zW γ₀)).symm
          rw [hcongr, hmain]
        obtain ⟨v1, hv1⟩ := hprim γ₀
        have hzv : rcDiff A (V γ₀) k (v0 - v1) = rcDiff A (V γ₀) k v0 - zW γ₀ := by
          rw [map_sub, hv1]
        obtain ⟨z'', hz''1, hz''2⟩ := rc_correction_of_primitive A hUsub k hU
          (rcDiff A (V γ₀) k v0 - zW γ₀) hre (v0 - v1) hzv
        clear he
        refine ⟨v0 - z'', ?_, ?_⟩
        · rw [map_sub, hz''1, sub_sub_cancel]
        · intro δ
          have hA : rcResLM A (hmono (le_of_lt δ.2)) k (v0 - z'')
              = rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub) k
                  (v0 - z'') :=
            congrArg (fun g => g (v0 - z''))
              (rcResLM_proof_irrel (hmono (le_of_lt δ.2))
                ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ).trans hUsub) k)
          rw [hA, rcResLM_trans A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V δ.1) δ) hUsub k]
          rw [map_sub, map_sub, hv0, hz''2, map_zero, sub_zero, hg δ]
      · -- no predecessors: any primitive works
        obtain ⟨v, hv1⟩ := hprim γ₀
        exact ⟨v, hv1, fun δ => absurd ⟨δ.1, δ.2⟩ hpred⟩
    obtain ⟨v, hv1, hv2⟩ := hnew
    -- the extended partial solution
    have hγ₀f : ∀ x : ↥(rcKern A (V γ₀) k),
        (⟨γ₀, x⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m → False := hγ₀
    have hm' : (m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k))}) ∈
        {G | RCSol A V hmono zW G} := by
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
    have hle : m ⊆ m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k))} := Set.subset_union_left
    have hsub' : m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k))} ⊆ m :=
      hmmax (y := m ∪ {(⟨γ₀, v⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k))}) hm' hle
    exact hγ₀f v (hsub' (Or.inr (Set.mem_singleton _)))
  -- the global family and its gluing
  let fFin : (γ : Γ) → ↥(rcKern A (V γ) k) := fun γ => Classical.choose (htotal γ)
  have hfFin : ∀ γ, (⟨γ, fFin γ⟩ : Σ γ : Γ, ↥(rcKern A (V γ) k)) ∈ m :=
    fun γ => Classical.choose_spec (htotal γ)
  have hfFincomp : ∀ i j (hij : i ≤ j), rcResLM A (hmono hij) k (fFin j) = fFin i :=
    fun i j hij => hmm4 j i hij (fFin j) (fFin i) (hfFin j) (hfFin i)
  obtain ⟨w, hw, -⟩ := (rcKern_iUnion_limit A V hopen hmono k fFin).mpr hfFincomp
  refine ⟨w, ?_⟩
  have hzero : rcDiff A (⋃ i, V i) k w - z = 0 := by
    refine rcRestrict_injective A V hopen hmono (k+1) (rcDiff A (⋃ i, V i) k w - z) ?_
    intro i
    show rcResLM A (Set.subset_iUnion V i) (k+1) (rcDiff A (⋃ i, V i) k w - z) = 0
    rw [map_sub, rcResLM_comm A (Set.subset_iUnion V i) k w, hw i]
    show rcDiff A (V i) k (fFin i) - rcResLM A (Set.subset_iUnion V i) (k+1) z = 0
    rw [hmm3 i (fFin i) (hfFin i)]
    exact sub_self _
  exact sub_eq_zero.mp hzero

end

end Work.Thom
