import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.Profinite
import Submission.Commons.Topology.Jordan.square_sets_top_bottom_continuum

set_option linter.style.haveILetI false

open Set

namespace Commons.Topology.Strip

/-- **Decomposition lemma.** In a compact Hausdorff space, if two closed sets `C`, `D` are such
that no connected component meets both, then there is a clopen set `U` with `C ⊆ U` and
`U ∩ D = ∅`. -/
theorem exists_clopen_separating_of_no_component {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] {C D : Set X} (hC : IsClosed C) (hD : IsClosed D)
    (h : ∀ z : X, ¬ ((connectedComponent z ∩ C).Nonempty ∧ (connectedComponent z ∩ D).Nonempty)) :
    ∃ U : Set X, IsClopen U ∧ C ⊆ U ∧ U ∩ D = ∅ := by
  classical
  let π : X → ConnectedComponents X := ConnectedComponents.mk
  have hπ : Continuous π := ConnectedComponents.continuous_coe
  have hCimg_closed : IsClosed (π '' C) := (hC.isCompact.image hπ).isClosed
  have hDimg_closed : IsClosed (π '' D) := (hD.isCompact.image hπ).isClosed
  have hsub : (π '' C) ⊆ ((π '' D))ᶜ := by
    rintro y ⟨c, hc, rfl⟩
    rw [Set.mem_compl_iff]
    rintro ⟨d, hd, hcd⟩
    rw [ConnectedComponents.coe_eq_coe] at hcd
    have h2 : (connectedComponent c ∩ D).Nonempty := by
      refine ⟨d, ?_, hd⟩
      rw [← hcd]; exact mem_connectedComponent
    exact h c ⟨⟨c, mem_connectedComponent, hc⟩, h2⟩
  obtain ⟨V, hVcl, hCV, hVD⟩ :=
    exists_clopen_of_closed_subset_open hCimg_closed hDimg_closed.isOpen_compl hsub
  refine ⟨π ⁻¹' V, hVcl.preimage hπ, ?_, ?_⟩
  · intro z hz; exact hCV ⟨z, hz, rfl⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzV, hzD⟩
    exact hVD hzV ⟨z, hzD, rfl⟩

/-! ## The affine identification of the strip with the unit square -/

/-- Affine map `[0,p] × [a,b] → [-1,1]² ⊂ ℂ`, exchanging the roles of the coordinates. -/
noncomputable def toSq (p a b : ℝ) (q : ℝ × ℝ) : ℂ :=
  ((2 * (q.2 - a) / (b - a) - 1 : ℝ) : ℂ) + ((2 * q.1 / p - 1 : ℝ) : ℂ) * Complex.I

/-- Inverse of `toSq`. -/
noncomputable def ofSq (p a b : ℝ) (z : ℂ) : ℝ × ℝ :=
  (p * (z.im + 1) / 2, a + (b - a) * (z.re + 1) / 2)

lemma toSq_re (p a b : ℝ) (q : ℝ × ℝ) :
    (toSq p a b q).re = 2 * (q.2 - a) / (b - a) - 1 := by
  simp only [toSq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

lemma toSq_im (p a b : ℝ) (q : ℝ × ℝ) :
    (toSq p a b q).im = 2 * q.1 / p - 1 := by
  simp only [toSq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

lemma ofSq_fst (p a b : ℝ) (z : ℂ) : (ofSq p a b z).1 = p * (z.im + 1) / 2 := rfl
lemma ofSq_snd (p a b : ℝ) (z : ℂ) : (ofSq p a b z).2 = a + (b - a) * (z.re + 1) / 2 := rfl

lemma continuous_toSq (p a b : ℝ) : Continuous (toSq p a b) := by unfold toSq; fun_prop
lemma continuous_ofSq (p a b : ℝ) : Continuous (ofSq p a b) := by unfold ofSq; fun_prop

lemma toSq_ofSq {p a b : ℝ} (hp : p ≠ 0) (hab : b ≠ a) (z : ℂ) :
    toSq p a b (ofSq p a b z) = z := by
  rw [toSq, ofSq_fst, ofSq_snd]
  have him : 2 * (p * (z.im + 1) / 2) / p - 1 = z.im := by
    field_simp; ring
  have hre : 2 * ((a + (b - a) * (z.re + 1) / 2) - a) / (b - a) - 1 = z.re := by
    field_simp; ring
  rw [him, hre]; simp

lemma ofSq_toSq {p a b : ℝ} (hp : p ≠ 0) (hab : b ≠ a) (q : ℝ × ℝ) :
    ofSq p a b (toSq p a b q) = q := by
  ext
  · rw [ofSq_fst, toSq_im]
    field_simp; ring
  · rw [ofSq_snd, toSq_re]
    field_simp; ring

lemma toSq_mem_square {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {q : ℝ × ℝ} (hq : q ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) :
    (toSq p a b q).re ∈ Set.Icc (-1:ℝ) 1 ∧ (toSq p a b q).im ∈ Set.Icc (-1:ℝ) 1 := by
  obtain ⟨h1,h2,h3,h4⟩ := hq
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [toSq_re, toSq_im]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have : 0 ≤ 2 * (q.2 - a) / (b - a) := by positivity
    linarith
  · have : 2 * (q.2 - a) / (b - a) ≤ 2 := by rw [div_le_iff₀ hba]; linarith
    linarith
  · have : 0 ≤ 2 * q.1 / p := by positivity
    linarith
  · have : 2 * q.1 / p ≤ 2 := by rw [div_le_iff₀ hp]; linarith
    linarith

end Commons.Topology.Strip

namespace Commons.Topology.Strip


lemma ofSq_mem_strip {p a b : ℝ} (hp : 0 < p) (hab : a < b) {z : ℂ}
    (hz : z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1) :
    ofSq p a b z ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b} := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hz
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [Set.mem_ofPred_eq, ofSq_fst, ofSq_snd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : 0 ≤ p * (z.im + 1) / 2 := by
      apply div_nonneg (mul_nonneg hp.le (by linarith)) (by norm_num)
    linarith
  · have : p * (z.im + 1) / 2 ≤ p := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  · have : 0 ≤ (b - a) * (z.re + 1) / 2 := by
      apply div_nonneg (mul_nonneg hba.le (by linarith)) (by norm_num)
    linarith
  · have : (b - a) * (z.re + 1) / 2 ≤ b - a := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith

/-- **Barrier lemma.** If a closed subset `K` of the closed strip `[0,p] × [a,b]` meets every path
in the strip from the left side `{q.1 = 0}` to the right side `{q.1 = p}`, then `K` contains a
preconnected subset meeting the two horizontal boundary lines `{q.2 = a}` and `{q.2 = b}`. -/
theorem barrier_bottom_top_of_no_left_right {p a b : ℝ} (hp : 0 < p) (hab : a < b)
    {K : Set (ℝ × ℝ)}
    (hKsub : K ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b})
    (hK : IsClosed K)
    (hno : ∀ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b}) →
      (γ 0 ∈ ({q : ℝ × ℝ | q.1 = 0} : Set (ℝ × ℝ))) →
      (γ 1 ∈ ({q : ℝ × ℝ | q.1 = p} : Set (ℝ × ℝ))) →
      (∀ t, γ t ∉ K) → False) :
    ∃ C : Set (ℝ × ℝ), C ⊆ K ∧ IsPreconnected C ∧
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty ∧ (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty := by
  classical
  set S : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ p ∧ a ≤ q.2 ∧ q.2 ≤ b} with hS
  have hKsubS : K ⊆ S := by rw [hS]; exact hKsub
  by_contra hcon
  have hbdc : ∀ C : Set (ℝ × ℝ), C ⊆ K → IsPreconnected C →
      (C ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty →
      (C ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty → False :=
    fun C h1 h2 h3 h4 => hcon ⟨C, h1, h2, h3, h4⟩
  have hSeq : S = (Icc (0:ℝ) p) ×ˢ (Icc a b) := by
    rw [hS]; ext q; simp only [mem_ofPred_eq, mem_prod, mem_Icc]; tauto
  -- compactness
  have hSconv : Convex ℝ S := by
    rw [hSeq]; exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hbox : IsCompact S := by
    rw [hSeq]; exact isCompact_Icc.prod isCompact_Icc
  have hKcpt : IsCompact K := hbox.of_isClosed_subset hK hKsubS
  haveI : CompactSpace {q : ℝ × ℝ // q ∈ K} := isCompact_iff_compactSpace.mp hKcpt
  -- K meets the two horizontal boundary lines
  have htpath : ∀ z : {q : ℝ × ℝ // q ∈ K}, z.1 = ((z.1.1 / p) * p, z.1.2) := by
    intro z; rw [div_mul_cancel₀]; exact ne_of_gt hp
  have hKtop : (K ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    let γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) := ⟨fun t : Set.Icc (0:ℝ) 1 => ((t:ℝ)*p, b), by fun_prop⟩
    refine hno γ ?_ ?_ ?_ ?_
    · intro t
      have h1 : 0 ≤ (t : ℝ) * p := mul_nonneg t.2.1 hp.le
      have h2 : (t : ℝ) * p ≤ p := by
        have := mul_le_mul_of_nonneg_right t.2.2 hp.le
        rwa [one_mul] at this
      exact ⟨h1, h2, hab.le, le_rfl⟩
    · show (((0:Set.Icc (0:ℝ) 1) : ℝ)*p, b) ∈ {q : ℝ × ℝ | q.1 = 0}; simp
    · show (((1:Set.Icc (0:ℝ) 1) : ℝ)*p, b) ∈ {q : ℝ × ℝ | q.1 = p}; simp
    · intro t ht
      exact (Set.eq_empty_iff_forall_notMem.mp h _) ⟨ht, rfl⟩
  have hKbot : (K ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    let γ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) := ⟨fun t : Set.Icc (0:ℝ) 1 => ((t:ℝ)*p, a), by fun_prop⟩
    refine hno γ ?_ ?_ ?_ ?_
    · intro t
      have h1 : 0 ≤ (t : ℝ) * p := mul_nonneg t.2.1 hp.le
      have h2 : (t : ℝ) * p ≤ p := by
        have := mul_le_mul_of_nonneg_right t.2.2 hp.le
        rwa [one_mul] at this
      exact ⟨h1, h2, le_rfl, hab.le⟩
    · show (((0:Set.Icc (0:ℝ) 1) : ℝ)*p, a) ∈ {q : ℝ × ℝ | q.1 = 0}; simp
    · show (((1:Set.Icc (0:ℝ) 1) : ℝ)*p, a) ∈ {q : ℝ × ℝ | q.1 = p}; simp
    · intro t ht
      exact (Set.eq_empty_iff_forall_notMem.mp h _) ⟨ht, rfl⟩
  -- decomposition into top part and bottom part
  set Ct : Set {q : ℝ × ℝ // q ∈ K} := {z | (z : ℝ × ℝ).2 = b} with hCt
  set Db : Set {q : ℝ × ℝ // q ∈ K} := {z | (z : ℝ × ℝ).2 = a} with hDb
  have hCt_closed : IsClosed Ct := by rw [hCt]; exact isClosed_eq (by fun_prop) continuous_const
  have hDb_closed : IsClosed Db := by rw [hDb]; exact isClosed_eq (by fun_prop) continuous_const
  have hCtne : Ct.Nonempty := by
    obtain ⟨q, hqK, hqb⟩ := hKtop; exact ⟨⟨q, hqK⟩, hqb⟩
  have hDbne : Db.Nonempty := by
    obtain ⟨q, hqK, hqa⟩ := hKbot; exact ⟨⟨q, hqK⟩, hqa⟩
  have hdecomp : ∀ z : {q : ℝ × ℝ // q ∈ K},
      ¬ ((connectedComponent z ∩ Ct).Nonempty ∧ (connectedComponent z ∩ Db).Nonempty) := by
    intro z ⟨h1, h2⟩
    obtain ⟨w, hw1, hw2⟩ := h1
    obtain ⟨v, hv1, hv2⟩ := h2
    refine hbdc (Subtype.val '' (connectedComponent z)) ?_ ?_ ?_ ?_
    · rintro _ ⟨a', _, rfl⟩; exact a'.2
    · exact (isPreconnected_connectedComponent).image _ continuous_subtype_val.continuousOn
    · exact ⟨v.1, ⟨⟨v, hv1, rfl⟩, hv2⟩⟩
    · exact ⟨w.1, ⟨⟨w, hw1, rfl⟩, hw2⟩⟩
  obtain ⟨U, hUcl, hCtU, hUjDb⟩ :=
    exists_clopen_separating_of_no_component hCt_closed hDb_closed hdecomp
  set A : Set (ℝ × ℝ) := Subtype.val '' U with hA
  set B : Set (ℝ × ℝ) := Subtype.val '' Uᶜ with hB
  have hA_closed : IsClosed A := by
    rw [hA]; exact (hUcl.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hB_closed : IsClosed B := by
    rw [hB]; exact (hUcl.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hA_sub : A ⊆ K := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hB_sub : B ⊆ K := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hAB : A ∪ B = K := by
    ext q; constructor
    · rintro (h | h) <;> [exact hA_sub h; exact hB_sub h]
    · intro hq
      by_cases h : (⟨q, hq⟩ : {q : ℝ × ℝ // q ∈ K}) ∈ U
      · left; rw [hA]; exact ⟨⟨q,hq⟩, h, rfl⟩
      · right; rw [hB]; exact ⟨⟨q,hq⟩, h, rfl⟩
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro q ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    have hz : z1 = z2 := Subtype.ext (by rw [h1, h2])
    rw [hz] at hz1; exact hz2 hz1
  have hAbot : A ∩ {q : ℝ × ℝ | q.2 = a} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqA, hqa⟩
    obtain ⟨z, hzU, rfl⟩ := hqA
    have hzDb : z ∈ Db := by rw [hDb]; exact hqa
    have : z ∈ U ∩ Db := ⟨hzU, hzDb⟩
    rw [hUjDb] at this; exact this
  have hBtop : B ∩ {q : ℝ × ℝ | q.2 = b} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqB, hqb⟩
    obtain ⟨z, hzUc, rfl⟩ := hqB
    have hzCt : z ∈ Ct := by rw [hCt]; exact hqb
    exact hzUc (hCtU hzCt)
  have hB_lt : ∀ q ∈ B, q.2 < b := by
    intro q hq
    obtain ⟨-, -, -, hqb⟩ := hKsubS (hB_sub hq)
    rcases lt_or_eq_of_le hqb with h | h
    · exact h
    · exact absurd (by rw [Set.eq_empty_iff_forall_notMem] at hBtop; exact hBtop q ⟨hq, h⟩) (by simp)
  have hA_gt : ∀ q ∈ A, a < q.2 := by
    intro q hq
    obtain ⟨-, -, ha, -⟩ := hKsubS (hA_sub hq)
    rcases lt_or_eq_of_le ha with h | h
    · exact h
    · exact absurd (by rw [Set.eq_empty_iff_forall_notMem] at hAbot; exact hAbot q ⟨hq, h.symm⟩) (by simp)
  have hAtop : (A ∩ {q : ℝ × ℝ | q.2 = b}).Nonempty := by
    obtain ⟨z, hz⟩ := hCtne
    exact ⟨z.1, ⟨by rw [hA]; exact ⟨z, hCtU hz, rfl⟩, hz⟩⟩
  have hBbot : (B ∩ {q : ℝ × ℝ | q.2 = a}).Nonempty := by
    obtain ⟨z, hz⟩ := hDbne
    have hzUc : z ∉ U := by
      intro h
      have hmem : z ∈ U ∩ Db := ⟨h, hz⟩
      rw [hUjDb] at hmem
      exact hmem
    exact ⟨z.1, ⟨by rw [hB]; exact ⟨z, hzUc, rfl⟩, hz⟩⟩
  -- transport to the unit square
  set E : Set ℂ := toSq p a b '' B with hE
  set F : Set ℂ := toSq p a b '' A with hF
  have hBcpt : IsCompact B := hbox.of_isClosed_subset hB_closed (hB_sub.trans hKsubS)
  have hAcpt : IsCompact A := hbox.of_isClosed_subset hA_closed (hA_sub.trans hKsubS)
  have hE_closed : IsClosed E := by
    rw [hE]; exact (hBcpt.image (continuous_toSq p a b)).isClosed
  have hF_closed : IsClosed F := by
    rw [hF]; exact (hAcpt.image (continuous_toSq p a b)).isClosed
  have hE_sub : E ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    rintro _ ⟨q, hq, rfl⟩; exact toSq_mem_square hp hab (hKsubS (hB_sub hq))
  have hF_sub : F ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} := by
    rintro _ ⟨q, hq, rfl⟩; exact toSq_mem_square hp hab (hKsubS (hA_sub hq))
  have hEF_disj : Disjoint E F := by
    rw [Set.disjoint_left]
    rintro z ⟨q1, hq1, h1⟩ ⟨q2, hq2, h2⟩
    have hq : q1 = q2 := by
      have hab' : b ≠ a := hab.ne'
      have h1' := ofSq_toSq (p := p) (a := a) (b := b) (ne_of_gt hp) hab' q1
      have h2' := ofSq_toSq (p := p) (a := a) (b := b) (ne_of_gt hp) hab' q2
      have h'' : ofSq p a b (toSq p a b q1) = ofSq p a b (toSq p a b q2) := by rw [h1, h2]
      rw [h1', h2'] at h''
      exact h''
    rw [hq] at hq1
    exact Set.disjoint_left.mp hdisjAB hq2 hq1
  have hE_right : ∀ z ∈ E, z.re < 1 := by
    rintro z ⟨q, hq, rfl⟩
    rw [toSq_re]
    have hba : 0 < b - a := sub_pos.mpr hab
    have : 2 * (q.2 - a) / (b - a) < 2 := by rw [div_lt_iff₀ hba]; linarith [hB_lt q hq]
    linarith
  have hF_left : ∀ z ∈ F, -1 < z.re := by
    rintro z ⟨q, hq, rfl⟩
    rw [toSq_re]
    have hba : 0 < b - a := sub_pos.mpr hab
    have : 0 < 2 * (q.2 - a) / (b - a) := div_pos (by linarith [hA_gt q hq]) hba
    linarith
  have hE_left : ∃ z ∈ E, z.re = -1 := by
    obtain ⟨q, hqB, hqa⟩ := hBbot
    refine ⟨toSq p a b q, ⟨q, hqB, rfl⟩, ?_⟩
    rw [toSq_re, hqa]; ring_nf
  have hF_right : ∃ z ∈ F, z.re = 1 := by
    obtain ⟨q, hqA, hqb⟩ := hAtop
    refine ⟨toSq p a b q, ⟨q, hqA, rfl⟩, ?_⟩
    rw [toSq_re, hqb]
    have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    rw [mul_div_assoc, div_self hba]
    ring
  -- the planar square lemma
  have hsq : ∃ K' : Set ℂ,
      K' ⊆ {z : ℂ | z.re ∈ Set.Icc (-1:ℝ) 1 ∧ z.im ∈ Set.Icc (-1:ℝ) 1} ∧
      Disjoint K' E ∧ Disjoint K' F ∧ IsPreconnected K' ∧ IsCompact K' ∧
      (∃ z ∈ K', z.im = 1) ∧ (∃ z ∈ K', z.im = -1) := by
    exact Commons.Topology.Jordan.square_sets_top_bottom_continuum
      hE_closed hF_closed hE_sub hF_sub hEF_disj hE_right hF_left hE_left hF_right
  obtain ⟨K', hK'sub, hK'E, hK'F, hK'pc, hK'cpt, hK'top, hK'bot⟩ := hsq
  -- push the separating continuum back into the strip
  set Cc : Set (ℝ × ℝ) := ofSq p a b '' K' with hCc
  have hCc_Kc : Cc ∩ K = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqC, hqK⟩
    obtain ⟨z, hzK', rfl⟩ := hqC
    have hmemK : ofSq p a b z ∈ A ∪ B := by rw [hAB]; exact hqK
    have hzFE : z ∈ F ∪ E := by
      have h1 : toSq p a b (ofSq p a b z) ∈ toSq p a b '' (A ∪ B) := Set.mem_image_of_mem _ hmemK
      rw [toSq_ofSq (ne_of_gt hp) hab.ne'] at h1
      rw [Set.image_union] at h1
      simpa only [← hF, ← hE] using h1
    rcases hzFE with hzF | hzE
    · exact (Set.disjoint_left.mp hK'F hzK') hzF
    · exact (Set.disjoint_left.mp hK'E hzK') hzE
  have hCc_sub_S : Cc ⊆ S := by
    rintro q ⟨z, hzK', rfl⟩
    rw [hS]
    exact ofSq_mem_strip hp hab (hK'sub hzK')
  have hCc_pc : IsPreconnected Cc := by
    rw [hCc]; exact hK'pc.image _ (continuous_ofSq p a b).continuousOn
  have hCc_left : (Cc ∩ {q : ℝ × ℝ | q.1 = 0}).Nonempty := by
    obtain ⟨z, hzK', hzim⟩ := hK'bot
    refine ⟨ofSq p a b z, ⟨⟨z, hzK', rfl⟩, ?_⟩⟩
    show (ofSq p a b z).1 = 0
    rw [ofSq_fst, hzim]; ring
  have hCc_right : (Cc ∩ {q : ℝ × ℝ | q.1 = p}).Nonempty := by
    obtain ⟨z, hzK', hzim⟩ := hK'top
    refine ⟨ofSq p a b z, ⟨⟨z, hzK', rfl⟩, ?_⟩⟩
    show (ofSq p a b z).1 = p
    rw [ofSq_fst, hzim]; ring
  -- convert the separating continuum into an actual path inside the strip
  haveI hLPC : LocallyPathConnectedSpace S := hSconv.locallyPathConnectedSpace
  obtain ⟨cL, hcLC, hcL0⟩ := hCc_left
  obtain ⟨cR, hcRC, hcRp⟩ := hCc_right
  haveI hpcC : PreconnectedSpace Cc := isPreconnected_iff_preconnectedSpace.mp hCc_pc
  let φ : Cc → S := fun q => ⟨q.1, hCc_sub_S q.2⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  let Ff : Set S := {x | (x : ℝ × ℝ) ∉ K}
  have hFf_open : IsOpen Ff := by
    have : Ff = Subtype.val ⁻¹' (Kᶜ) := rfl
    rw [this]; exact hK.isOpen_compl.preimage continuous_subtype_val
  have hrange_sub : Set.range φ ⊆ Ff := by
    rintro _ ⟨q, rfl⟩
    intro hk
    exact (Set.eq_empty_iff_forall_notMem.mp hCc_Kc q.1) ⟨q.2, hk⟩
  have hrange_pc : IsPreconnected (Set.range φ) := by
    rw [← Set.image_univ]
    exact (isPreconnected_univ (α := Cc)).image φ hφ.continuousOn
  let D : Set S := connectedComponentIn Ff (φ ⟨cL, hcLC⟩)
  have hφL : φ ⟨cL, hcLC⟩ ∈ Ff := hrange_sub ⟨⟨cL, hcLC⟩, rfl⟩
  have hφR : φ ⟨cR, hcRC⟩ ∈ Ff := hrange_sub ⟨⟨cR, hcRC⟩, rfl⟩
  have hDsub_range : Set.range φ ⊆ D :=
    hrange_pc.subset_connectedComponentIn ⟨⟨cL, hcLC⟩, rfl⟩ hrange_sub
  have hφLD : φ ⟨cL, hcLC⟩ ∈ D := mem_connectedComponentIn hφL
  have hφRD : φ ⟨cR, hcRC⟩ ∈ D := hDsub_range ⟨⟨cR, hcRC⟩, rfl⟩
  have hDpc : IsPreconnected D := isPreconnected_connectedComponentIn
  have hDopen : IsOpen D := hFf_open.connectedComponentIn
  have hDpath : IsPathConnected D := by
    rw [← IsOpen.isConnected_iff_isPathConnected hDopen]
    exact ⟨⟨_, hφLD⟩, hDpc⟩
  have hjoinD : JoinedIn D (φ ⟨cL, hcLC⟩) (φ ⟨cR, hcRC⟩) :=
    hDpath.joinedIn (φ ⟨cL, hcLC⟩) hφLD (φ ⟨cR, hcRC⟩) hφRD
  have hpath_mem : ∀ t, hjoinD.somePath t ∈ D := hjoinD.somePath_mem
  have hpath_F : ∀ t, hjoinD.somePath t ∈ Ff :=
    fun t => connectedComponentIn_subset Ff _ (hpath_mem t)
  let γℝ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ) :=
    ⟨fun t => (hjoinD.somePath t : ℝ × ℝ),
      continuous_subtype_val.comp hjoinD.somePath.continuous⟩
  have hγℝ : ∀ t, γℝ t = (hjoinD.somePath t : ℝ × ℝ) := fun t => rfl
  refine hno γℝ ?_ ?_ ?_ ?_
  · intro t
    rw [hγℝ t]
    exact (hjoinD.somePath t).2
  · rw [hγℝ 0, hjoinD.somePath.source]
    exact hcL0
  · rw [hγℝ 1, hjoinD.somePath.target]
    exact hcRp
  · intro t
    rw [hγℝ t]
    exact (hpath_F t)

end Commons.Topology.Strip