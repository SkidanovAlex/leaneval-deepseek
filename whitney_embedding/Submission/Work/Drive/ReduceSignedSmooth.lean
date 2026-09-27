import Mathlib
import Submission.Work.Drive.CancelSignedSmooth
import Submission.Work.Drive.SmoothArcs
import Submission.Work.Whitney.InsertSigned
import Submission.Work.Whitney.CancelSigned
import Submission.Work.Whitney.EndgameNFTrans

/-!
# The smooth-arc signed reduction step

This is `Work.Whitney.exists_reduce_double_points_signed` with the *smooth* cancellation interface
`Work.Drive.HasCancelSignedSmooth` in place of `Work.Whitney.HasCancelSigned`: the two arcs of the
bigon are now chosen `C^∞` and immersive on `[0,1]` by
`Work.Drive.exists_smooth_disjoint_arcs_avoiding_finite`, and the sign alternative of the signed
insertion is applied to those smooth arcs (its arc hypothesis only needs continuity, which the
smooth arcs have).

Mathematically nothing changes: the arcs only have to avoid the finite set of double point
preimages, which the smooth arc selection achieves in the same way.
-/



open scoped Manifold ContDiff
open Topology Work.Whitney

namespace Work.Drive

set_option linter.unusedVariables false

/-- The finite set of points of `M` which are preimages of a double point of `f`, together with the
two points `p'`, `q'` of the freshly inserted pair.  Copy of `Work.Whitney.doublePreimages`. -/
def doublePreimages {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M) :
    Set M :=
  Prod.fst '' (doubleSet f ∪ ({(p', q'), (q', p')} : Set (M × M)))

/-- **The reduction step, once the candidate and the arcs are fixed.**  Given one of the two signed
insertion candidates `F` (with its full `InsertedDP`/`SimpleDP`/`TransDP'` structure), a pair of
arcs `γ₁ : p₁ → p'`, `γ₂ : p₂ → q'` avoiding all double point preimages (except at their endpoints),
and the framing hypothesis `OppositeType F γ₁ γ₂ p₁ p₂ p' q'`, the cancellation interface
`HasCancelSigned` removes the pair and the invariants survive.

`D` is the set of double point preimages: it is passed as a parameter together with its description
`hDmem` so that the same pair of arcs can be used for both candidates. -/
private theorem reduce_of_candidate_smooth {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hcancel : Work.Drive.HasCancelSignedSmooth n M)
    (f F : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ p' q' : M)
    (hfp : f p₁ = f p₂)
    (hins' : InsertedDP f p₁ p₂ F p' q') (hsimple' : SimpleDP F) (htrans' : TransDP' F)
    (D : Set M) (hDfin : D.Finite)
    (hDmem : ∀ y : M, y ∈ D ↔ ∃ z : M, z ≠ y ∧ F z = F y)
    (γ₁ γ₂ : ℝ → M) (hγ₁c : Continuous γ₁) (hγ₂c : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = p') (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q')
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1)) (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁sm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₁) (hγ₂sm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₂ t))
    (hγ₁D : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ D → t = 0 ∨ t = 1)
    (hγ₂D : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ D → t = 0 ∨ t = 1)
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : OppositeType F γ₁ γ₂ p₁ p₂ p' q') :
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f'' ∧
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f'' y)) ∧
      (doubleSet f'').Finite ∧
      (doubleSet f'').ncard + 2 = (doubleSet f).ncard ∧
      SimpleDP f'' ∧ TransDP' f'' := by
  classical
  have hf'c := hins'.contMDiff
  have hf'imm := hins'.injective_mfderiv
  have hds := hins'.doubleSet_eq
  have hf'fin := hins'.finite_doubleSet
  have hnewold := hins'.new_not_old
  have hfin : (doubleSet f).Finite :=
    hf'fin.subset (by rw [hds]; exact Set.subset_union_left)
  obtain ⟨hp'q', hp'p₁, hp'p₂, hq'p₁, hq'p₂, hp₁p₂⟩ := hins'.distinct
  -- `(p₁,p₂)` and `(p',q')` are double points of `F`
  have hmem₁₂ : (p₁, p₂) ∈ doubleSet F := by
    rw [hds]; left; rw [mem_doubleSet]; exact ⟨hp₁p₂, hfp⟩
  have hmem' : (p', q') ∈ doubleSet F := by rw [hds]; right; simp
  have hfp' : F p₁ = F p₂ := (mem_doubleSet.mp hmem₁₂).2
  have hfq' : F p' = F q' := (mem_doubleSet.mp hmem').2
  have hs₁ : ∀ z : M, F z = F p₁ → z = p₁ ∨ z = p₂ := fun z hz => hsimple' _ hmem₁₂ z hz
  have hs₂ : ∀ z : M, F z = F p' → z = p' ∨ z = q' := fun z hz => hsimple' _ hmem' z hz
  -- the four endpoints lie in `D`
  have hp₁D : p₁ ∈ D := (hDmem p₁).mpr ⟨p₂, hp₁p₂.symm, hfp'.symm⟩
  have hp₂D : p₂ ∈ D := (hDmem p₂).mpr ⟨p₁, hp₁p₂, hfp'⟩
  have hp'D : p' ∈ D := (hDmem p').mpr ⟨q', hp'q'.symm, hfq'.symm⟩
  have hq'D : q' ∈ D := (hDmem q').mpr ⟨p', hp'q', hfq'⟩
  -- the endpoints are the only points of the arcs which lie in `D`
  have hend₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p₁ → t = 0 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₁D
    rcases hγ₁D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₁1] at h
      exact hp'p₁ h
  have hend₁' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t = p' → t = 1 := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp'D
    rcases hγ₁D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₁0] at h
      exact hp'p₁ h.symm
    · exact h1
  have hne₁p₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ p₂ := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hp₁p₂ h
    · subst h1; rw [hγ₁1] at h; exact hp'p₂ h
  have hne₁q' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ≠ q' := by
    intro t ht h
    have hD : γ₁ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₁D t ht hD with h0 | h1
    · subst h0; rw [hγ₁0] at h; exact hq'p₁ h.symm
    · subst h1; rw [hγ₁1] at h; exact hp'q' h
  have hend₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = p₂ → t = 0 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hp₂D
    rcases hγ₂D t ht hD with h0 | h1
    · exact h0
    · exfalso
      subst h1
      rw [hγ₂1] at h
      exact hq'p₂ h
  have hend₂' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t = q' → t = 1 := by
    intro t ht h
    have hD : γ₂ t ∈ D := by rw [h]; exact hq'D
    rcases hγ₂D t ht hD with h0 | h1
    · exfalso
      subst h0
      rw [hγ₂0] at h
      exact hq'p₂ h.symm
    · exact h1
  -- ## Step 3: the clean region containing the arcs.
  obtain ⟨W, hWopen, hWcpt, hW₁, hW₂, hW₃, hW₄, hWchar, hWclean, hWsep, _⟩ :=
    exists_clean_region F hf'fin p₁ p₂ p' q'
      hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq'
      (fun z hz => hs₁ z hz) (fun z hz => hs₂ z hz)
  -- ## Step 4: the arcs lie in the clean region.
  have hmemW : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₁0]; exact hW₁
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₁1]; exact hW₃
    have hnotD : γ₁ t ∉ D := by
      intro hD
      rcases hγ₁D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (fun hcon => hnotD ((hDmem _).mpr hcon))
  have hmemW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W := by
    intro t ht
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hγ₂0]; exact hW₂
    rcases eq_or_ne t 1 with h1 | h1
    · rw [h1, hγ₂1]; exact hW₄
    have hnotD : γ₂ t ∉ D := by
      intro hD
      rcases hγ₂D t ht hD with h | h
      · exact h0 h
      · exact h1 h
    rw [hWchar]
    exact Or.inl (fun hcon => hnotD ((hDmem _).mpr hcon))
  -- ## Step 5: the two image arcs meet only in the two double points (`hγend`).
  have hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      F (γ₁ s) = F (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s hs t ht heq
    rcases hWclean (γ₁ s) (γ₂ t) (hmemW s hs) (hmemW₂ t ht) heq with
      h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hγdisj s hs t ht h
    · exact Or.inl ⟨hend₁ s hs h1, hend₂ t ht h2⟩
    · exact absurd h1 (hne₁p₂ s hs)
    · exact Or.inr ⟨hend₁' s hs h1, hend₂' t ht h2⟩
    · exact absurd h1 (hne₁q' s hs)
  -- ## Step 6: cancel the pair `((p₁,p₂), (p',q'))`.
  have htransP' : (mfderiv (𝓡 n) (𝓡 (2 * n)) F p₁).range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) F p₂).range = ⊤ :=
    trans_of_transDP' hf'c htrans' (p₁, p₂) hmem₁₂
  have htransQ' : (mfderiv (𝓡 n) (𝓡 (2 * n)) F p').range ⊔
      (mfderiv (𝓡 n) (𝓡 (2 * n)) F q').range = ⊤ :=
    trans_of_transDP' hf'c htrans' (p', q') hmem'
  obtain ⟨f'', hf''c, hf''imm, hout, hds'', hagree⟩ :=
    hcancel hn F hf'c hf'imm W hWopen hWcpt p₁ p₂ p' q'
      hW₁ hW₂ hW₃ hW₄ hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
      hfp' hfq' hWclean hWsep htransP' htransQ' γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hmemW hmemW₂ hγ₁inj hγ₂inj hγ₁sm hγ₂sm hγ₁imm hγ₂imm hγdisj hγend hsign
  -- ## Step 7: the invariants survive.
  have hsub : doubleSet f'' ⊆ doubleSet F := by rw [hds'']; exact Set.sdiff_subset
  have hsimple'' : SimpleDP f'' := by
    intro p hp z hz
    by_cases hzp : z = p.1
    · exact Or.inl hzp
    have hmem : (z, p.1) ∈ doubleSet f'' := by
      rw [mem_doubleSet]; exact ⟨hzp, hz⟩
    exact hsimple' p (hsub hp) z (mem_doubleSet.mp (hsub hmem)).2
  -- the double points of `f''` lie outside the clean region
  have hfst : ∀ a b : M, (a, b) ∈ doubleSet f'' → a ∉ W := by
    intro a b hab hW
    have hab' : (a, b) ∈ doubleSet F := hsub hab
    obtain ⟨habne, habeq⟩ := mem_doubleSet.mp hab'
    have hnot4 : (a, b) ∉ ({(p₁, p₂), (p₂, p₁), (p', q'), (q', p')} : Set (M × M)) := by
      intro h4
      rw [hds''] at hab
      exact hab.2 h4
    rw [hWchar] at hW
    rcases hW with hW | hW | hW | hW | hW
    · exact hW ⟨b, habne.symm, habeq.symm⟩
    · -- `a = p₁`
      have h := hs₁ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = p₂`
      have h := hs₁ b (by rw [← habeq, hW, hfp'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
    · -- `a = p'`
      have h := hs₂ b (by rw [← habeq, hW])
      rcases h with h2 | h2
      · exact habne (by rw [hW, h2])
      · exact hnot4 (by simp [hW, h2])
    · -- `a = q'`
      have h := hs₂ b (by rw [← habeq, hW, hfq'])
      rcases h with h2 | h2
      · exact hnot4 (by simp [hW, h2])
      · exact habne (by rw [hW, h2])
  have hnotW : ∀ p : M × M, p ∈ doubleSet f'' → p.1 ∉ W ∧ p.2 ∉ W := fun p hp =>
    ⟨hfst p.1 p.2 hp, hfst p.2 p.1 (by rw [mem_doubleSet] at hp ⊢; exact ⟨hp.1.symm, hp.2.symm⟩)⟩
  have htrans'' : TransDP' f'' := by
    intro p hp
    obtain ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c, hpd⟩ := htrans' p (hsub hp)
    obtain ⟨hnotW₁, hnotW₂⟩ := hnotW p hp
    exact ⟨c₁, c₂, hc₁, hc₂, hp₁c, hp₂c,
      by rw [hagree p.1 p.2 hnotW₁ hnotW₂ c₁ c₂ hp₁c hp₂c]; exact hpd⟩
  -- ## Step 8: the cardinality bookkeeping.
  refine ⟨f'', hf''c, hf''imm, ?_, ?_, hsimple'', htrans''⟩
  · rw [hds'']; exact hf'fin.sdiff
  · have h1 : (doubleSet f'').ncard + 4 = (doubleSet F).ncard :=
      ncard_doubleSet_cancel F f'' p₁ p₂ p' q'
        hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm hfp' hfq' hf'fin hds''
    have h2 : (doubleSet F).ncard = (doubleSet f).ncard + 2 :=
      ncard_doubleSet_insert f F p' q' hp'q' hnewold hfin hds
    omega

theorem exists_reduce_double_points_signed_smooth {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hins : Work.Whitney.HasInsertionSigned n M) (hcancel : Work.Drive.HasCancelSignedSmooth n M)
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (hsimple : Work.Whitney.SimpleDP f) (htrans : Work.Whitney.TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂) :
    ∃ f'' : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f'' ∧
      (∀ y, Function.Injective (mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f'' y)) ∧
      (Work.Whitney.doubleSet f'').Finite ∧
      (Work.Whitney.doubleSet f'').ncard + 2 = (Work.Whitney.doubleSet f).ncard ∧
      Work.Whitney.SimpleDP f'' ∧ Work.Whitney.TransDP' f'' := by
  classical
  -- ## Step 0: the two signed insertion candidates.
  obtain ⟨fp, fm, p', q', hins_fp, hsimple_fp, htrans_fp, hins_fm, hsimple_fm, htrans_fm,
    harcs⟩ :=
    hins f hf himm hfin hsimple htrans p₁ p₂ hp₁p₂ hfp
  obtain ⟨hp'q', hp'p₁, hp'p₂, hq'p₁, hq'p₂, -⟩ := hins_fp.distinct
  -- ## Step 1: the finite set avoided by the arcs (the same for both candidates).
  have hpair : ({(p', q'), (q', p')} : Set (M × M)).Finite :=
    (Set.finite_singleton (q', p')).insert (p', q')
  have hDfin : (doublePreimages f p' q').Finite := (hfin.union hpair).image Prod.fst
  -- ## Step 2: the two arcs of the bigon.
  obtain ⟨γ₁, γ₂, hγ₁sm, hγ₂sm, hγ₁imm, hγ₂imm, hγ₁0, hγ₁1, hγ₂0, hγ₂1, hγ₁inj, hγ₂inj,
    hγ₁D, hγ₂D, hγdisj⟩ :=
    Work.Drive.exists_smooth_disjoint_arcs_avoiding_finite (n := n) hn (doublePreimages f p' q')
      hDfin p₁ p₂ p' q' hp₁p₂ hp'q' hp'p₁.symm hq'p₁.symm hp'p₂.symm hq'p₂.symm
  have hγ₁c : Continuous γ₁ := hγ₁sm.continuous
  have hγ₂c : Continuous γ₂ := hγ₂sm.continuous
  -- ## Step 3: the sign alternative chooses the candidate.
  have hDmem_fp : ∀ y : M, y ∈ doublePreimages f p' q' ↔
      ∃ z : M, z ≠ y ∧ fp z = fp y := by
    intro y
    have hD : doublePreimages f p' q' = Prod.fst '' (doubleSet fp) := by
      unfold doublePreimages
      rw [hins_fp.doubleSet_eq]
    rw [hD]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw.1.symm, hw.2.symm⟩
    · rintro ⟨z, hzy, hfz⟩
      exact ⟨(y, z), ⟨hzy.symm, hfz.symm⟩, rfl⟩
  have hDmem_fm : ∀ y : M, y ∈ doublePreimages f p' q' ↔
      ∃ z : M, z ≠ y ∧ fm z = fm y := by
    intro y
    have hD : doublePreimages f p' q' = Prod.fst '' (doubleSet fm) := by
      unfold doublePreimages
      rw [hins_fm.doubleSet_eq]
    rw [hD]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw.1.symm, hw.2.symm⟩
    · rintro ⟨z, hzy, hfz⟩
      exact ⟨(y, z), ⟨hzy.symm, hfz.symm⟩, rfl⟩
  rcases harcs γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1 with hsign | hsign
  · exact reduce_of_candidate_smooth hn hcancel f fp p₁ p₂ p' q' hfp hins_fp hsimple_fp htrans_fp
      (doublePreimages f p' q') hDfin hDmem_fp γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγ₁inj hγ₂inj hγ₁sm hγ₂sm (fun t _ => hγ₁imm t) (fun t _ => hγ₂imm t)
      hγ₁D hγ₂D hγdisj hsign
  · exact reduce_of_candidate_smooth hn hcancel f fm p₁ p₂ p' q' hfp hins_fm hsimple_fm htrans_fm
      (doublePreimages f p' q') hDfin hDmem_fm γ₁ γ₂ hγ₁c hγ₂c hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγ₁inj hγ₂inj hγ₁sm hγ₂sm (fun t _ => hγ₁imm t) (fun t _ => hγ₂imm t)
      hγ₁D hγ₂D hγdisj hsign

end Work.Drive
