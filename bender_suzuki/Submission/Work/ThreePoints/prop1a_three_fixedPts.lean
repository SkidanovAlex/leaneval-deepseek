import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.prop1a_descent_aux
import Submission.Work.ThreePoints.ch1_lem2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

/-- **Step 2 of Peterfalvi I Ch. II §4 Prop. 1(a).**  Let `H` be strongly embedded in the finite
group `G`, `M = H^g` a conjugate of `H` containing `X`, and `P ≤ X ⊓ F1` a subgroup.  If `X` fixes
at least three points of `G ⧸ H` and `F1 ⊓ M'` has even order for every conjugate `M' ⊇ X` of `H`,
then `P` fixes at least three points of `↥F1 ⧸ (F1 ⊓ M)`.

The `≥ 3` points are the cosets of elements `t ∈ ↥F1` with `t M t⁻¹ = M'` for three distinct fixed
points `M' = H^{g'}` of `X` (`ch1_lem2`); distinctness follows because `F1 ⊓ M' ≤ M' ⊓ M''` has
even order while `M' ⊓ M''` has odd order for `M' ≠ M''`. -/
theorem prop1a_three_fixedPts {G : Type} [Group G] [Finite G] {H X M F1 P : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H)
    (hXM : X ≤ M)
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hPF1 : P ≤ F1) (hPX : P ≤ X)
    (hev : ∀ {M' : Subgroup G}, (∃ g : G, M' = Submission.Blueprint.conj g H) → X ≤ M' →
      Even (Nat.card (F1 ⊓ M' : Subgroup G))) :
    3 ≤ (Submission.Blueprint.fixedPts ((F1 ⊓ M).subgroupOf F1) (P.subgroupOf F1)).ncard := by
  classical
  set K : Subgroup ↥F1 := (F1 ⊓ M).subgroupOf F1 with hKdef
  -- three distinct points of `G ⧸ H` fixed by `X`
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard (s := Submission.Blueprint.fixedPts H X) (Set.toFinite _)).mp
      (show 2 < (Submission.Blueprint.fixedPts H X).ncard by omega)
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective a
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective b
  obtain ⟨g₃, hg₃⟩ := QuotientGroup.mk_surjective c
  have hXa : X ≤ Submission.Blueprint.conj g₁ H := by
    have h := mem_fixedPts_iff_le_stabilizer.mp ha
    rwa [← hg₁, Work.ThreePoints.stabilizer_mk H g₁] at h
  have hXb : X ≤ Submission.Blueprint.conj g₂ H := by
    have h := mem_fixedPts_iff_le_stabilizer.mp hb
    rwa [← hg₂, Work.ThreePoints.stabilizer_mk H g₂] at h
  have hXc : X ≤ Submission.Blueprint.conj g₃ H := by
    have h := mem_fixedPts_iff_le_stabilizer.mp hc
    rwa [← hg₃, Work.ThreePoints.stabilizer_mk H g₃] at h
  -- for every conjugate `M' ⊇ X` of `H`, an element of `↥F1` conjugating `M` to `M'`
  have key : ∀ (M' : Subgroup G), (∃ g' : G, M' = Submission.Blueprint.conj g' H) → X ≤ M' →
      ∃ t : ↥F1, Submission.Blueprint.conj (t : G) M = M' := by
    intro M' hM' hXM'
    rcases eq_or_ne M' M with h | h
    · subst h; exact ⟨1, by simp⟩
    · have hevM : Even (Nat.card (F1 ⊓ M : Subgroup G)) := hev hM hXM
      have hevM' : Even (Nat.card (F1 ⊓ M' : Subgroup G)) := hev hM' hXM'
      obtain ⟨g, hg⟩ := hM
      obtain ⟨g', hg'⟩ := hM'
      have hne : Submission.Blueprint.conj g H ≠ Submission.Blueprint.conj g' H := by
        intro heq
        exact h (by rw [hg, hg', heq])
      have hev1 : Even (Nat.card (F1 ⊓ Submission.Blueprint.conj g H : Subgroup G)) := by
        rw [← hg]; exact hevM
      have hev2 : Even (Nat.card (F1 ⊓ Submission.Blueprint.conj g' H : Subgroup G)) := by
        rw [← hg']; exact hevM'
      obtain ⟨t, ht, ht2⟩ := (ch1_lem2 hH hne hev1 hev2).1
      refine ⟨⟨t, ht.1⟩, ?_⟩
      rw [hg, hg']
      simpa using ht2
  obtain ⟨t₁, ht₁⟩ := key (Submission.Blueprint.conj g₁ H) ⟨g₁, rfl⟩ hXa
  obtain ⟨t₂, ht₂⟩ := key (Submission.Blueprint.conj g₂ H) ⟨g₂, rfl⟩ hXb
  obtain ⟨t₃, ht₃⟩ := key (Submission.Blueprint.conj g₃ H) ⟨g₃, rfl⟩ hXc
  -- distinctness of the corresponding points of `↥F1 ⧸ K`
  have key2 : ∀ (g' g'' : G) (t' t'' : ↥F1), X ≤ Submission.Blueprint.conj g' H →
      X ≤ Submission.Blueprint.conj g'' H →
      Submission.Blueprint.conj (t' : G) M = Submission.Blueprint.conj g' H →
      Submission.Blueprint.conj (t'' : G) M = Submission.Blueprint.conj g'' H →
      (t' : ↥F1 ⧸ K) = (t'' : ↥F1 ⧸ K) → (g' : G ⧸ H) = (g'' : G ⧸ H) := by
    intro g' g'' t' t'' hX' hX'' ht' ht'' heq
    have hstab : MulAction.stabilizer (↥F1) (t' : ↥F1 ⧸ K) =
        MulAction.stabilizer (↥F1) (t'' : ↥F1 ⧸ K) := by rw [heq]
    rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.stabilizer_mk] at hstab
    have h4 : Submission.Blueprint.conj t' K =
        (F1 ⊓ Submission.Blueprint.conj g' H).subgroupOf F1 := by
      rw [hKdef]; exact conj_subgroupOf_inf ht'
    have h5 : Submission.Blueprint.conj t'' K =
        (F1 ⊓ Submission.Blueprint.conj g'' H).subgroupOf F1 := by
      rw [hKdef]; exact conj_subgroupOf_inf ht''
    have h3 : (F1 ⊓ Submission.Blueprint.conj g' H).subgroupOf F1 =
        (F1 ⊓ Submission.Blueprint.conj g'' H).subgroupOf F1 := by
      rw [← h4, ← h5]; exact hstab
    have h4' : F1 ⊓ Submission.Blueprint.conj g' H =
        F1 ⊓ Submission.Blueprint.conj g'' H := by
      have h5' := congrArg (Subgroup.map F1.subtype) h3
      rwa [map_subtype_subgroupOf_inf, map_subtype_subgroupOf_inf] at h5'
    by_contra hne
    have hne' : Submission.Blueprint.conj g' H ≠ Submission.Blueprint.conj g'' H := by
      intro heq'
      exact hne (mk_eq_of_conj_eq hH heq')
    have hodd : Odd (Nat.card (Submission.Blueprint.conj g' H ⊓ Submission.Blueprint.conj g'' H
        : Subgroup G)) := card_inf_conj_odd hH hne'
    have hev' : Even (Nat.card (F1 ⊓ Submission.Blueprint.conj g' H : Subgroup G)) :=
      hev ⟨g', rfl⟩ hX'
    have hle : F1 ⊓ Submission.Blueprint.conj g' H ≤
        Submission.Blueprint.conj g' H ⊓ Submission.Blueprint.conj g'' H :=
      le_inf inf_le_right (by rw [h4']; exact inf_le_right)
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd (Subgroup.card_dvd_of_le hle) hodd)) hev'
  -- the three points of `↥F1 ⧸ K`
  have hpoint : ∀ (t : ↥F1) (g' : G), Submission.Blueprint.conj (t : G) M =
      Submission.Blueprint.conj g' H → X ≤ Submission.Blueprint.conj g' H →
      (t : ↥F1 ⧸ K) ∈ Submission.Blueprint.fixedPts K (P.subgroupOf F1) := by
    intro t g' ht' hX'
    rw [mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk]
    have hconj : Submission.Blueprint.conj t K =
        (F1 ⊓ Submission.Blueprint.conj g' H).subgroupOf F1 := by
      rw [hKdef]; exact conj_subgroupOf_inf ht'
    rw [hconj]
    intro q hq
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact ⟨hPF1 hq, hX' (hPX hq)⟩
  have hmem₁ := hpoint t₁ g₁ ht₁ hXa
  have hmem₂ := hpoint t₂ g₂ ht₂ hXb
  have hmem₃ := hpoint t₃ g₃ ht₃ hXc
  have hne₁₂ : (t₁ : ↥F1 ⧸ K) ≠ (t₂ : ↥F1 ⧸ K) := fun h =>
    hab (hg₁.symm.trans ((key2 g₁ g₂ t₁ t₂ hXa hXb ht₁ ht₂ h).trans hg₂))
  have hne₁₃ : (t₁ : ↥F1 ⧸ K) ≠ (t₃ : ↥F1 ⧸ K) := fun h =>
    hac (hg₁.symm.trans ((key2 g₁ g₃ t₁ t₃ hXa hXc ht₁ ht₃ h).trans hg₃))
  have hne₂₃ : (t₂ : ↥F1 ⧸ K) ≠ (t₃ : ↥F1 ⧸ K) := fun h =>
    hbc (hg₂.symm.trans ((key2 g₂ g₃ t₂ t₃ hXb hXc ht₂ ht₃ h).trans hg₃))
  have hcard : ({(t₁ : ↥F1 ⧸ K), (t₂ : ↥F1 ⧸ K), (t₃ : ↥F1 ⧸ K)} :
      Set (↥F1 ⧸ K)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨_, _, _, hne₁₂, hne₁₃, hne₂₃, rfl⟩
  have hsub : ({(t₁ : ↥F1 ⧸ K), (t₂ : ↥F1 ⧸ K), (t₃ : ↥F1 ⧸ K)} : Set (↥F1 ⧸ K)) ⊆
      Submission.Blueprint.fixedPts K (P.subgroupOf F1) := by
    intro ω hω
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
    rcases hω with rfl | rfl | rfl
    · exact hmem₁
    · exact hmem₂
    · exact hmem₃
  have := Set.ncard_le_ncard hsub
  omega

end Work.ThreePoints
