import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.SdSubdiv
import Submission.Work.PL.Approx.Ex.Defs

namespace Work.PL.Approx.Ex

noncomputable section

/-!
# `RestrictsTo` is not automatic

We exhibit the two-point counterexample described in `Submission/Work/PL/Approx/Ex/Defs.lean`:
`K` is the complex on `{0, one₁}` with all nonempty subsets as faces (so `K.space` is the whole
segment `[0, one₁]`), and `L` is the subcomplex with the two singleton faces (so `L.space` is the
two-element set `{0, one₁}`).  Then the `r = 0` face `s = {0, one₁}` of `K` already violates the
first clause of `RestrictsTo (sdSubdiv 1)`: all of its vertices lie in `L.space`, so
`simp (frozenPart L s) = simp s` is the whole segment, whereas `simp s ∩ L.space = {0, one₁}`.
-/

/-- The vertex set `{0, one₁}` of `E 1` is affinely independent. -/
lemma nrt_affineIndependent :
    AffineIndependent ℝ (Subtype.val : (↑twoVerts : Set (PL.E 1)) → PL.E 1) := by
  have hne : (0 : PL.E 1) ≠ one₁ := one₁_ne_zero.symm
  have h1 : AffineIndependent ℝ
      (Subtype.val : Set.range (![0, one₁] : Fin 2 → PL.E 1) → PL.E 1) :=
    (affineIndependent_of_ne ℝ hne).range
  rw [show Set.range (![0, one₁] : Fin 2 → PL.E 1) = (↑twoVerts : Set (PL.E 1)) from by
    ext x; simp [twoVerts]; tauto] at h1
  exact h1

/-- The full simplex on `{0, one₁}`: all nonempty subsets of `twoVerts` are faces. -/
def nrtK : PL.Cx 1 where
  faces := {s | s ⊆ twoVerts ∧ s.Nonempty}
  isRelLowerSet_faces := by
    intro a ha
    refine ⟨ha.2, ?_⟩
    intro b hba hb
    exact ⟨hba.trans ha.1, hb⟩
  indep := by
    intro s hs
    exact nrt_affineIndependent.mono (Finset.coe_subset.mpr hs.1)
  inter_subset_convexHull := by
    intro s t hs ht
    rw [nrt_affineIndependent.convexHull_inter hs.1 ht.1]

/-- The subcomplex on `{0, one₁}` with only the two vertices: the nonempty *proper* subsets of
`twoVerts`. -/
def nrtL : PL.Cx 1 where
  faces := {s | s ⊆ twoVerts ∧ s ≠ twoVerts ∧ s.Nonempty}
  isRelLowerSet_faces := by
    intro a ha
    refine ⟨ha.2.2, ?_⟩
    intro b hba hb
    refine ⟨hba.trans ha.1, ?_, hb⟩
    intro hbt
    exact ha.2.1 (Finset.Subset.antisymm ha.1 (hbt ▸ hba))
  indep := by
    intro s hs
    exact nrt_affineIndependent.mono (Finset.coe_subset.mpr hs.1)
  inter_subset_convexHull := by
    intro s t hs ht
    rw [nrt_affineIndependent.convexHull_inter hs.1 ht.1]

lemma nrtK_mem (s : Finset (PL.E 1)) :
    s ∈ nrtK.faces ↔ s ⊆ twoVerts ∧ s.Nonempty := Iff.rfl

lemma nrtL_mem (s : Finset (PL.E 1)) :
    s ∈ nrtL.faces ↔ s ⊆ twoVerts ∧ s ≠ twoVerts ∧ s.Nonempty := Iff.rfl

/-- `nrtK.faces` is finite (it is contained in the powerset of the two-point set). -/
lemma nrtK_finite : nrtK.faces.Finite := by
  refine (Finset.finite_toSet twoVerts.powerset).subset ?_
  intro s hs
  rw [nrtK_mem] at hs
  exact Finset.mem_powerset.mpr hs.1

/-- The midpoint of the segment `[0, one₁]`. -/
def nrtP : PL.E 1 := ((1 : ℝ) / 2) • one₁

lemma nrtP_ne_zero : nrtP ≠ (0 : PL.E 1) := by
  unfold nrtP
  exact smul_ne_zero (by norm_num) one₁_ne_zero

lemma nrtP_ne_one : nrtP ≠ one₁ := by
  unfold nrtP
  intro he
  have h0 : ((1 : ℝ) / 2) • one₁ - one₁ = (0 : PL.E 1) := by rw [he, sub_self]
  have h : ((1 : ℝ) / 2) • one₁ - one₁ = ((1 : ℝ) / 2 - 1) • one₁ := by
    rw [sub_smul, one_smul]
  rw [h] at h0
  have hc : ((1 : ℝ) / 2 - 1) = 0 := (smul_eq_zero.mp h0).resolve_right one₁_ne_zero
  norm_num at hc

/-- The only nonempty proper subsets of the two-point set `twoVerts` are the two singletons. -/
lemma nrt_subset_twoVerts_eq (s : Finset (PL.E 1)) (hsub : s ⊆ twoVerts)
    (hne : s ≠ twoVerts) (hnon : s.Nonempty) : s = {0} ∨ s = {one₁} := by
  have hcard2 : twoVerts.card = 2 := by
    unfold twoVerts
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [one₁_ne_zero.symm]
  have hle : s.card ≤ 2 := by
    have := Finset.card_le_card hsub
    rwa [hcard2] at this
  have hge : 1 ≤ s.card := Finset.card_pos.mpr hnon
  have hne2 : s.card ≠ 2 := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le hsub (by simp [hcard2, h]))
  have hcard : s.card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hamem : a ∈ twoVerts := by
    rw [ha] at hsub
    exact hsub (Finset.mem_singleton_self a)
  simp [twoVerts] at hamem
  rcases hamem with h | h
  · left; rw [ha, h]
  · right; rw [ha, h]

/-- The two vertices of `L` lie in `L.space`. -/
lemma nrt_zero_mem_L_space : (0 : PL.E 1) ∈ nrtL.space := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  refine ⟨{0}, ?_, ?_⟩
  · show ({0} : Finset (PL.E 1)) ∈
      ({s : Finset (PL.E 1) | s ⊆ twoVerts ∧ s ≠ twoVerts ∧ s.Nonempty})
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.singleton_subset_iff.mpr (by simp [twoVerts])
    · intro h
      have h2 : one₁ ∈ ({0} : Finset (PL.E 1)) := by rw [h]; simp [twoVerts]
      simp at h2
      exact one₁_ne_zero h2
    · exact Finset.singleton_nonempty 0
  · rw [Finset.coe_singleton, convexHull_singleton]
    simp

lemma nrt_one_mem_L_space : one₁ ∈ nrtL.space := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  refine ⟨{one₁}, ?_, ?_⟩
  · show ({one₁} : Finset (PL.E 1)) ∈
      ({s : Finset (PL.E 1) | s ⊆ twoVerts ∧ s ≠ twoVerts ∧ s.Nonempty})
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.singleton_subset_iff.mpr (by simp [twoVerts])
    · intro h
      have h2 : (0 : PL.E 1) ∈ ({one₁} : Finset (PL.E 1)) := by rw [h]; simp [twoVerts]
      simp at h2
      exact one₁_ne_zero h2.symm
    · exact Finset.singleton_nonempty one₁
  · rw [Finset.coe_singleton, convexHull_singleton]
    simp

/-- `nrtP` lies in the simplex spanned by `twoVerts`. -/
lemma nrtP_mem_simp : nrtP ∈ PL.simp twoVerts := by
  have htwo : (↑twoVerts : Set (PL.E 1)) = ({0, one₁} : Set (PL.E 1)) := by
    ext x; simp [twoVerts]
  rw [PL.simp, htwo, convexHull_pair, segment_eq_image]
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  simp [nrtP]

/-- `nrtP` does not lie in `L.space = {0, one₁}`. -/
lemma nrtP_not_mem_L_space : nrtP ∉ nrtL.space := by
  intro hp
  rw [Geometry.SimplicialComplex.mem_space_iff] at hp
  obtain ⟨s, hs, hps⟩ := hp
  rw [nrtL_mem] at hs
  obtain ⟨hsub, hne, hnon⟩ := hs
  rcases nrt_subset_twoVerts_eq s hsub hne hnon with h | h
  · rw [h, Finset.coe_singleton, convexHull_singleton] at hps
    simp at hps
    exact nrtP_ne_zero hps
  · rw [h, Finset.coe_singleton, convexHull_singleton] at hps
    simp at hps
    exact nrtP_ne_one hps

/-- The `r = 0` face `twoVerts` of `nrtK` already refutes the first clause of `RestrictsTo`. -/
lemma nrt_ne :
    PL.simp twoVerts ∩ nrtL.space ≠ PL.simp (frozenPart nrtL twoVerts) := by
  classical
  intro heq
  have hfrozen : frozenPart nrtL twoVerts = twoVerts := by
    unfold frozenPart
    exact Finset.filter_true_of_mem (by
      intro x hx
      simp [twoVerts] at hx
      rcases hx with rfl | rfl
      · exact nrt_zero_mem_L_space
      · exact nrt_one_mem_L_space)
  have hmem : nrtP ∈ PL.simp (frozenPart nrtL twoVerts) := by
    rw [hfrozen]; exact nrtP_mem_simp
  rw [← heq] at hmem
  exact nrtP_not_mem_L_space hmem.2

theorem not_restrictsTo :
    ∃ (K L : PL.Cx 1) (hK : K.faces.Finite),
      (∀ s : Finset (PL.E 1), s ∈ K.faces ↔ s ⊆ Ex.twoVerts ∧ s.Nonempty) ∧
      (∀ s : Finset (PL.E 1), s ∈ L.faces ↔ s ⊆ Ex.twoVerts ∧ s ≠ Ex.twoVerts ∧ s.Nonempty) ∧
      ¬ RestrictsTo (sdSubdiv 1) K hK L := by
  refine ⟨nrtK, nrtL, nrtK_finite, ?_, ?_, ?_⟩
  · intro s; exact nrtK_mem s
  · intro s; exact nrtL_mem s
  · intro h
    have hmem : twoVerts ∈ ((sdSubdiv 1).iter 0 nrtK nrtK_finite).faces := by
      show twoVerts ∈ nrtK.faces
      rw [nrtK_mem]
      exact ⟨subset_rfl, ⟨0, by simp [twoVerts]⟩⟩
    exact nrt_ne (h.1 0 twoVerts hmem)

end

end Work.PL.Approx.Ex
