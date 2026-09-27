import Mathlib
import Submission.Work.Noncompact.CompressionTube.SpineDefs

namespace Work.Noncompact.CompressionTube

open Set Topology

theorem exists_disjoint_spines_with_arcs {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    (B : Set M) (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (K : ℕ → Set M) (hKc : ∀ i, IsCompact (K i)) (hK0 : K 0 = ∅)
    (hKsub : ∀ i, K i ⊆ interior (K (i+1))) (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M)
    (h : SpineData K B lev q γ) :
    ∃ A : B → Set M,
      (∀ b, IsClosed (A b)) ∧ (∀ b, IsPreconnected (A b)) ∧ (∀ b, (b : M) ∈ A b) ∧
      (∀ b, ¬ IsCompact (A b)) ∧ (∀ b b', b ≠ b' → Disjoint (A b) (A b')) ∧
      (∀ K' : Set M, IsCompact K' → {b : B | (A b ∩ K').Nonempty}.Finite) ∧
      (∀ b i, lev b ≤ i → γ b i '' Set.Icc (0:ℝ) 1 ⊆ A b) := by
  classical
  have hKmono : Monotone K := monotone_K K hKsub
  set arc : B → ℕ → Set M := fun b i => γ b i '' Set.Icc (0:ℝ) 1 with harcdef
  set A : B → Set M := fun b => ({(b : M)} : Set M) ∪ ⋃ i, ⋃ (_ : lev b ≤ i), arc b i
    with hAdef
  have hAle : ∀ b : B, A b = ({(b : M)} : Set M) ∪ ⋃ i, ⋃ (_ : lev b ≤ i), arc b i :=
    fun b => rfl
  have harcA : ∀ (b : B) (i : ℕ), lev b ≤ i → arc b i ⊆ A b := by
    intro b i hi x hx
    rw [hAle]
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  have hbA : ∀ b : B, (b : M) ∈ A b := by
    intro b; rw [hAle]; exact Or.inl rfl
  have harcle : ∀ (b : B) (i : ℕ) (hi : lev b ≤ i), q b (i+1) ∈ arc b i := by
    intro b i hi
    exact ⟨1, Set.right_mem_Icc.mpr zero_le_one, (h.ends b i hi).2⟩
  have hblev : ∀ b : B, (b : M) ∈ arc b (lev b) := by
    intro b
    refine ⟨0, Set.left_mem_Icc.mpr zero_le_one, ?_⟩
    exact ((h.ends b (lev b) le_rfl).1).trans (h.q_lev b)
  have hsub : ∀ (b : B) (i : ℕ), lev b ≤ i → arc b i ⊆ interior (K (i+2)) := by
    intro b i hi x hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact h.image_sub b i hi t ht
  have hdisjK : ∀ (b : B) (i : ℕ), lev b ≤ i → Disjoint (arc b i) (K i) := fun b i hi =>
    h.disjoint_K b i hi
  -- every point of the manifold meets only the shells of bounded level
  have hshellfin : ∀ (b : B) (N i : ℕ), lev b ≤ i → N + 2 < i →
      Disjoint (arc b i) (interior (K (N+2))) := by
    intro b N i hlev hNi
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact Set.disjoint_left.mp (hdisjK b i hlev) hx
      (hKmono (by omega) (interior_subset hx'))
  -- IsClosed
  have hGclosed : ∀ (b : B) (i : ℕ), IsClosed (⋃ (_ : lev b ≤ i), arc b i) := by
    intro b i
    by_cases hi : lev b ≤ i
    · have h1 : (⋃ (_ : lev b ≤ i), arc b i) = arc b i := by simp [hi]
      rw [h1]
      exact (isCompact_Icc.image (h.cont b i hi)).isClosed
    · have h1 : (⋃ (_ : lev b ≤ i), arc b i) = ∅ := by simp [hi]
      rw [h1]
      exact isClosed_empty
  have hlf : ∀ b : B, LocallyFinite (fun i : ℕ => ⋃ (_ : lev b ≤ i), arc b i) := by
    intro b x
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp
      (show x ∈ ⋃ i, K i from by rw [hKuniv]; exact Set.mem_univ x)
    have hx : x ∈ interior (K (N+2)) := interior_mono (hKmono (by omega)) (hKsub N hN)
    refine ⟨interior (K (N+2)), (isOpen_interior : IsOpen (interior (K (N+2)))).mem_nhds hx, ?_⟩
    refine Set.Finite.subset (Set.finite_Iic (N+2)) ?_
    rintro i ⟨y, hy1, hy2⟩
    simp only [] at hy1
    show i ≤ N + 2
    by_contra hlt
    push_neg at hlt
    have hleb : lev b ≤ i := by
      by_contra hc
      rw [show (⋃ (_ : lev b ≤ i), arc b i) = ∅ from by simp [hc]] at hy1
      exact hy1
    have hyarc : y ∈ arc b i := by
      rwa [show (⋃ (_ : lev b ≤ i), arc b i) = arc b i from by simp [hleb]] at hy1
    exact Set.disjoint_left.mp (hshellfin b N i hleb (by omega)) hyarc hy2
  have hAclosed : ∀ b : B, IsClosed (A b) := by
    intro b
    rw [hAle]
    exact isClosed_singleton.union ((hlf b).isClosed_iUnion (hGclosed b))
  -- IsPreconnected
  have hpre : ∀ b : B, IsPreconnected (A b) := by
    intro b
    set H : ℕ → Set M := fun m => arc b (lev b + m) with hH
    have hHpre : ∀ m : ℕ, IsPreconnected (H m) := fun m =>
      isPreconnected_Icc.image _ (h.cont b (lev b + m) (by omega)).continuousOn
    have hHne : ∀ m : ℕ, (H m ∩ H (m+1)).Nonempty := by
      intro m
      refine ⟨q b (lev b + m + 1), harcle b (lev b + m) (by omega), ?_⟩
      exact ⟨0, Set.left_mem_Icc.mpr zero_le_one, (h.ends b (lev b + m + 1) (by omega)).1⟩
    have hchain : ∀ i j : ℕ, Relation.ReflTransGen (fun i j => (H i ∩ H j).Nonempty) i j := by
      have hup : ∀ d i : ℕ, Relation.ReflTransGen (fun i j => (H i ∩ H j).Nonempty) i (i + d) := by
        intro d
        induction d with
        | zero => intro i; simpa using Relation.ReflTransGen.refl
        | succ d ih =>
            intro i
            have h1 : i + (d+1) = (i+d) + 1 := by omega
            rw [h1]
            exact (ih i).tail (hHne (i+d))
      have hdown : ∀ d i : ℕ, Relation.ReflTransGen (fun i j => (H i ∩ H j).Nonempty) (i + d) i := by
        intro d
        induction d with
        | zero => intro i; simpa using Relation.ReflTransGen.refl
        | succ d ih =>
            intro i
            have h1 : i + (d+1) = (i+1) + d := by omega
            rw [h1]
            refine (ih (i+1)).tail ?_
            exact ⟨(hHne i).choose, (hHne i).choose_spec.2, (hHne i).choose_spec.1⟩
      intro i j
      rcases le_total i j with hle | hle
      · have h1 : j = i + (j - i) := (Nat.add_sub_cancel' hle).symm
        rw [h1]; exact hup (j - i) i
      · have h1 : i = j + (i - j) := (Nat.add_sub_cancel' hle).symm
        rw [h1]; exact hdown (i - j) j
    have hbig : IsPreconnected (⋃ m : ℕ, H m) :=
      IsPreconnected.iUnion_of_reflTransGen hHpre hchain
    have hbU : (b : M) ∈ ⋃ m : ℕ, H m :=
      Set.mem_iUnion.mpr ⟨0, by simpa [hH] using hblev b⟩
    have hAeq : A b = ({(b : M)} : Set M) ∪ ⋃ m : ℕ, H m := by
      rw [hAle]
      congr 1
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩
        refine ⟨i - lev b, ?_⟩
        show x ∈ arc b (lev b + (i - lev b))
        rw [Nat.add_sub_cancel' hi]
        exact hx
      · rintro ⟨m, hx⟩
        exact ⟨lev b + m, by omega, hx⟩
    have hfin2 : IsPreconnected (({(b : M)} : Set M) ∪ ⋃ m : ℕ, H m) :=
      IsPreconnected.union (b : M) (Set.mem_singleton (b : M)) hbU
        isPreconnected_singleton hbig
    rw [hAeq]
    exact hfin2
  -- non-compactness
  have hnc : ∀ b : B, ¬ IsCompact (A b) := by
    intro b hc
    obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun i => interior (K i)) (fun i => isOpen_interior)
      (fun x _ => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (show x ∈ ⋃ i, K i from by rw [hKuniv]; exact Set.mem_univ x)
        exact Set.mem_iUnion.mpr ⟨i+1, hKsub i hi⟩)
    set N₀ := t.sup id with hN₀
    have hsubK : A b ⊆ K N₀ := ht.trans fun x hx => by
      obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact hKmono (Finset.le_sup (f := id) hit) (interior_subset hxi)
    have hle : lev b ≤ max N₀ (lev b) := le_max_right _ _
    have hqA : q b (max N₀ (lev b) + 1) ∈ A b :=
      harcA b (max N₀ (lev b)) hle (harcle b (max N₀ (lev b)) hle)
    have hqK : q b (max N₀ (lev b) + 1) ∉ K (max N₀ (lev b)) := by
      have hs := (h.q_shell b (max N₀ (lev b) + 1) (Nat.lt_succ_of_le hle)).2
      exact fun hc => hs (hKmono (Nat.le_succ _) hc)
    exact hqK (hKmono (le_max_left N₀ (lev b)) (hsubK hqA))
  -- disjointness of arcs of different strands
  have harcdisj : ∀ (b b' : B) (i j : ℕ), lev b ≤ i → lev b' ≤ j → b ≠ b' →
      Disjoint (arc b i) (arc b' j) := by
    intro b b' i j hi hj hne
    rcases lt_trichotomy i j with hlt | heq | hgt
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with h2 | h2
      · subst h2
        refine Set.disjoint_left.mpr fun x hx hx' => ?_
        by_cases hxK : x ∈ K (i+1)
        · exact Set.disjoint_left.mp (hdisjK b' (i+1) (by omega)) hx' hxK
        · exact Set.disjoint_left.mp (h.disjoint_foot b b' i hi (by omega) hne)
            ⟨hx, hsub b i hi hx, hxK⟩ hx'
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        exact Set.disjoint_left.mp (hdisjK b' j hj) hx'
          (hKmono (by omega) (interior_subset (hsub b i hi hx)))
    · subst heq
      exact h.disjoint_same b b' i hi hj hne
    · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with h2 | h2
      · subst h2
        refine Set.disjoint_left.mpr fun x hx hx' => ?_
        by_cases hxK : x ∈ K (j+1)
        · exact Set.disjoint_left.mp (hdisjK b (j+1) (by omega)) hx hxK
        · exact Set.disjoint_left.mp (h.disjoint_foot b' b j hj (by omega) hne.symm)
            ⟨hx', hsub b' j hj hx', hxK⟩ hx
      · refine Set.disjoint_left.mpr fun x hx hx' => ?_
        exact Set.disjoint_left.mp (hdisjK b i hi) hx
          (hKmono (by omega) (interior_subset (hsub b' j hj hx')))
  -- base points are not on other strands
  have hbnotmem : ∀ b b' : B, b ≠ b' → (b : M) ∉ A b' := by
    intro b b' hne hx
    rw [hAle] at hx
    rcases hx with hx | hx
    · exact hne (Subtype.ext (Set.mem_singleton_iff.mp hx))
    · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact h.avoids_base b' b j hj hne.symm hxj
  have hdisj : ∀ b b' : B, b ≠ b' → Disjoint (A b) (A b') := by
    intro b b' hne
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rw [hAle] at hx hx'
    rcases hx with hx | hx
    · have hxb : x = b := Set.mem_singleton_iff.mp hx
      rw [hxb] at hx'
      exact hbnotmem b b' hne hx'
    · rcases hx' with hx' | hx'
      · have hxb : x = b' := Set.mem_singleton_iff.mp hx'
        rw [hxb] at hx
        exact hbnotmem b' b hne.symm (by rw [hAle]; exact Or.inr hx)
      · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx'
        exact Set.disjoint_left.mp (harcdisj b b' i j hi hj hne) hxi hxj
  -- local finiteness of the family
  have hfin : ∀ K' : Set M, IsCompact K' → {b : B | (A b ∩ K').Nonempty}.Finite := by
    intro K' hK'
    obtain ⟨t, ht⟩ := hK'.elim_finite_subcover (fun i => interior (K i)) (fun i => isOpen_interior)
      (fun x _ => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (show x ∈ ⋃ i, K i from by rw [hKuniv]; exact Set.mem_univ x)
        exact Set.mem_iUnion.mpr ⟨i+1, hKsub i hi⟩)
    set N₀ := t.sup id with hN₀
    have hK'sub : K' ⊆ K N₀ := ht.trans fun x hx => by
      obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact hKmono (Finset.le_sup (f := id) hit) (interior_subset hxi)
    have hbig : {b : B | (b : M) ∈ K (N₀ + 1)}.Finite := by
      refine ((hB (K (N₀+1)) (hKc (N₀+1))).preimage
        (fun a _ c _ hh => Subtype.ext hh)).subset ?_
      intro b hb
      exact ⟨b.2, hb⟩
    refine Set.Finite.subset hbig ?_
    intro b hb
    show (b : M) ∈ K (N₀ + 1)
    by_contra hcon
    have hN₀lev : N₀ < lev b := by
      by_contra hle
      push_neg at hle
      exact hcon (hKmono (by omega) (h.lev_mem_succ b))
    obtain ⟨x, hxA, hxK⟩ := hb
    rw [hAle] at hxA
    rcases hxA with hxA | hxA
    · have hxb : x = b := Set.mem_singleton_iff.mp hxA
      rw [hxb] at hxK
      exact hcon (hKmono (Nat.le_succ N₀) (hK'sub hxK))
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxA
      exact Set.disjoint_left.mp (hdisjK b i hi) hxi
        (hKmono (by omega) (hK'sub hxK))
  exact ⟨A, hAclosed, hpre, hbA, hnc, hdisj, hfin, harcA⟩

end Work.Noncompact.CompressionTube
