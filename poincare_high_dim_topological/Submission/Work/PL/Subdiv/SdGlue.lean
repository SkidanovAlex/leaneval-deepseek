import Submission.Work.PL.Subdiv.SdIndep

/-!
# The gluing axiom of the barycentric subdivision (blueprint G3, third Mathlib axiom)

The faces of `sd K` are the barycenters of chains of faces of `K`.  The content of this file is
that two such simplices meet in the simplex of the intersection of the two chains:
`convexHull b(C) ∩ convexHull b(D) ⊆ convexHull b(C ∩ D)` (`inter_subset_bary`).
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

variable {N : ℕ}

/-- Convex combination of two points of a convex set. -/
lemma convex_combo_mem {S : Set (E N)} (hS : Convex ℝ S) {a b : E N} (ha : a ∈ S) (hb : b ∈ S)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • a + (1 - t) • b ∈ S :=
  (hS.starConvex ha) hb ht0 (sub_nonneg.mpr ht1) (by ring)

/-- There is a vertex of the top of a chain that is not in the top of the chain minus that top. -/
lemma exists_mem_chainTop_notMem_erase {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (hne : C.Nonempty) : ∃ v ∈ chainTop C, v ∉ chainTop (C.erase (chainTop C)) := by
  have hτC : chainTop C ∈ C := chainTop_mem_chain hC.2 hne
  rcases Finset.eq_empty_or_nonempty (C.erase (chainTop C)) with hempty | hne'
  · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hC.1 _ hτC)
    exact ⟨v, le_chainTop hτC hv, by rw [hempty]; exact Finset.notMem_empty v⟩
  · have hmem' : chainTop (C.erase (chainTop C)) ∈ C.erase (chainTop C) :=
      chainTop_mem_chain (fun ρ hρ ρ' hρ' => hC.2 ρ (Finset.mem_of_mem_erase hρ) ρ'
        (Finset.mem_of_mem_erase hρ')) hne'
    refine Finset.exists_of_ssubset (ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · exact chainTop_le_iff.mpr fun ρ hρ => le_chainTop (Finset.mem_of_mem_erase hρ)
    · intro hcon
      exact Finset.notMem_erase _ _ (hcon ▸ hmem')

/-- A convex combination of barycenters along a chain lies in the simplex of the top of the chain. -/
lemma sum_smul_bary_mem_simp_chainTop {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (_hne : C.Nonempty) {m : Finset (E N) → ℝ} (hm0 : ∀ ρ ∈ C, 0 ≤ m ρ)
    (hmsum : (∑ ρ ∈ C, m ρ) = 1) : (∑ ρ ∈ C, m ρ • bary ρ) ∈ simp (chainTop C) := by
  refine (convex_convexHull ℝ (↑(chainTop C) : Set (E N))).sum_mem hm0 hmsum fun ρ hρ => ?_
  exact convexHull_mono (Finset.coe_subset.mpr (le_chainTop hρ))
    (bary_mem_simp (K.nonempty_of_mem_faces (hC.1 ρ hρ)))

/-- If `v` is a vertex of the top `σ` of a chain `C` which is in no other element of `C`, then the
coordinate of `v` in the barycentric coordinates of any point supported on `C` is `m σ / |σ|`. -/
lemma coord_filter_eq_top {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (hne : C.Nonempty) {v : E N} (hv : v ∈ chainTop C)
    (hvnot : v ∉ chainTop (C.erase (chainTop C))) (m : Finset (E N) → ℝ) :
    (∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), m ρ / (ρ.card : ℝ))
      = m (chainTop C) / ((chainTop C).card : ℝ) := by
  have hτC : chainTop C ∈ C := chainTop_mem_chain hC.2 hne
  have hfilter : C.filter (fun ρ => v ∈ ρ) = {chainTop C} := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hρC, hvρ⟩
      by_contra hne'
      exact hvnot (le_chainTop (Finset.mem_erase.mpr ⟨hne', hρC⟩) hvρ)
    · rintro rfl
      exact ⟨hτC, hv⟩
  rw [hfilter, Finset.sum_singleton]

/-- The coordinate of a vertex of the top of a chain is at least the top coefficient. -/
lemma le_coord_filter {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (hne : C.Nonempty) {m : Finset (E N) → ℝ} (hm0 : ∀ ρ ∈ C, 0 ≤ m ρ) {v : E N}
    (hv : v ∈ chainTop C) :
    m (chainTop C) / ((chainTop C).card : ℝ)
      ≤ ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), m ρ / (ρ.card : ℝ) := by
  have hτC : chainTop C ∈ C := chainTop_mem_chain hC.2 hne
  exact Finset.single_le_sum (f := fun ρ => m ρ / (ρ.card : ℝ))
    (fun ρ hρ => div_nonneg (hm0 ρ (Finset.mem_filter.mp hρ).1) (Nat.cast_nonneg _))
    (Finset.mem_filter.mpr ⟨hτC, hv⟩)

/-- **The minimal face containing a point is at least the top of any chain representing it.** -/
lemma chainTop_subset_of_mem_simp {K : Cx N} {C : Finset (Finset (E N))} (hC : IsChain K C)
    (hne : C.Nonempty) {m : Finset (E N) → ℝ} (hm0 : ∀ ρ ∈ C, 0 < m ρ)
    (hmsum : (∑ ρ ∈ C, m ρ) = 1) {x : E N} (hx : x = ∑ ρ ∈ C, m ρ • bary ρ)
    {τ : Finset (E N)} (hτ : τ ∈ K.faces) (hxτ : x ∈ simp τ) : chainTop C ⊆ τ := by
  have hσC : chainTop C ∈ C := chainTop_mem_chain hC.2 hne
  have hσfaces : chainTop C ∈ K.faces := hC.1 _ hσC
  have hxσ : x ∈ simp (chainTop C) := by
    rw [hx]
    exact sum_smul_bary_mem_simp_chainTop hC hne (fun ρ hρ => (hm0 ρ hρ).le) hmsum
  have hinter : x ∈ simp (τ ∩ chainTop C) := by
    have h := K.convexHull_inter_convexHull hτ hσfaces
    have hmem : x ∈ simp τ ∩ simp (chainTop C) := ⟨hxτ, hxσ⟩
    simpa [PL.simp] using h.le hmem
  set α : E N → ℝ := fun v => ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), m ρ / (ρ.card : ℝ) with hα
  have hαsum : (∑ v ∈ chainTop C, α v) = 1 := by
    rw [hα]
    rw [sum_coeff_filter C (chainTop C) (fun ρ hρ => le_chainTop hρ)
      (fun ρ hρ => K.nonempty_of_mem_faces (hC.1 ρ hρ)) m, hmsum]
  have hαpt : (∑ v ∈ chainTop C, α v • v) = x := by
    rw [hα, ← sum_smul_bary_eq_sum_smul C (chainTop C) (fun ρ hρ => le_chainTop hρ) m, hx]
  have hα0 : ∀ v ∈ chainTop C, 0 ≤ α v := by
    intro v _
    rw [hα]
    exact Finset.sum_nonneg fun ρ hρ =>
      div_nonneg (le_of_lt (hm0 ρ (Finset.mem_filter.mp hρ).1)) (Nat.cast_nonneg _)
  intro v hvσ
  by_contra hvτ
  have hzero := coords_eq_zero_of_mem_simp_subset (B := chainTop C) (B' := τ ∩ chainTop C)
    Finset.inter_subset_right (K.indep hσfaces) hα0 hαsum hαpt hinter v hvσ
    (fun hc => hvτ (Finset.mem_of_mem_inter_left hc))
  have hcardσ : (0 : ℝ) < ((chainTop C).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (K.nonempty_of_mem_faces hσfaces)
  have hpos : 0 < α v := by
    have hle := le_coord_filter hC hne (fun ρ hρ => le_of_lt (hm0 ρ hρ)) hvσ
    have hαv : α v = ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), m ρ / (ρ.card : ℝ) := by simp only [hα]
    rw [hαv]
    exact lt_of_lt_of_le (div_pos (hm0 _ hσC) hcardσ) hle
  exact absurd hzero (ne_of_gt hpos)

/-- The top coefficient of a chain, read off from the barycentric coordinates of the point. -/
lemma top_coeff_eq_of_eq {K : Cx N} {C D : Finset (Finset (E N))} (hC : IsChain K C)
    (hD : IsChain K D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    {m n : Finset (E N) → ℝ} (hm0 : ∀ ρ ∈ C, 0 < m ρ) (hn0 : ∀ ρ ∈ D, 0 < n ρ)
    (hmsum : (∑ ρ ∈ C, m ρ) = 1) (hnsum : (∑ ρ ∈ D, n ρ) = 1)
    (hσeq : chainTop C = chainTop D) {x : E N}
    (hx : x = ∑ ρ ∈ C, m ρ • bary ρ) (hx' : x = ∑ ρ ∈ D, n ρ • bary ρ) :
    m (chainTop C) = n (chainTop D) := by
  have hσfaces : chainTop C ∈ K.faces := hC.1 _ (chainTop_mem_chain hC.2 hCne)
  set α : E N → ℝ := fun v => ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), m ρ / (ρ.card : ℝ) with hα
  set β : E N → ℝ := fun v => ∑ ρ ∈ D.filter (fun ρ => v ∈ ρ), n ρ / (ρ.card : ℝ) with hβ
  have hαsum : (∑ v ∈ chainTop C, α v) = 1 := by
    rw [hα, sum_coeff_filter C (chainTop C) (fun ρ hρ => le_chainTop hρ)
      (fun ρ hρ => K.nonempty_of_mem_faces (hC.1 ρ hρ)) m, hmsum]
  have hαpt : (∑ v ∈ chainTop C, α v • v) = x := by
    rw [hα, ← sum_smul_bary_eq_sum_smul C (chainTop C) (fun ρ hρ => le_chainTop hρ) m, hx]
  have hβsum' : (∑ v ∈ chainTop D, β v) = 1 := by
    rw [hβ, sum_coeff_filter D (chainTop D) (fun ρ hρ => le_chainTop hρ)
      (fun ρ hρ => K.nonempty_of_mem_faces (hD.1 ρ hρ)) n, hnsum]
  have hβpt' : (∑ v ∈ chainTop D, β v • v) = x := by
    rw [hβ, ← sum_smul_bary_eq_sum_smul D (chainTop D) (fun ρ hρ => le_chainTop hρ) n, hx']
  have hβsum : (∑ v ∈ chainTop C, β v) = 1 := by rw [hσeq]; exact hβsum'
  have hβpt : (∑ v ∈ chainTop C, β v • v) = x := by rw [hσeq]; exact hβpt'
  have hαβ : ∀ v ∈ chainTop C, α v = β v :=
    coords_unique_of_affineIndependent (K.indep hσfaces) (a := α) (a' := β)
      (by rw [hαsum, hβsum]) (by rw [hαpt, hβpt])
  obtain ⟨v₁, hv₁, hv₁not⟩ := exists_mem_chainTop_notMem_erase hC hCne
  obtain ⟨v₂, hv₂, hv₂not⟩ := exists_mem_chainTop_notMem_erase hD hDne
  have hcardC : (0 : ℝ) < ((chainTop C).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (K.nonempty_of_mem_faces hσfaces)
  have hσcard : ((chainTop D).card : ℝ) = ((chainTop C).card : ℝ) := by rw [hσeq]
  have hle1 : n (chainTop D) / ((chainTop D).card : ℝ) ≤ m (chainTop C) / ((chainTop C).card : ℝ) := by
    have hα1 : α v₁ = m (chainTop C) / ((chainTop C).card : ℝ) := by
      rw [hα]
      exact coord_filter_eq_top hC hCne hv₁ hv₁not m
    have hβ1 : β v₁ = ∑ ρ ∈ D.filter (fun ρ => v₁ ∈ ρ), n ρ / (ρ.card : ℝ) := by simp only [hβ]
    have hle := le_coord_filter (C := D) hD hDne (fun ρ hρ => le_of_lt (hn0 ρ hρ)) (hσeq ▸ hv₁)
    calc n (chainTop D) / ((chainTop D).card : ℝ)
        ≤ ∑ ρ ∈ D.filter (fun ρ => v₁ ∈ ρ), n ρ / (ρ.card : ℝ) := hle
      _ = β v₁ := hβ1.symm
      _ = α v₁ := (hαβ v₁ hv₁).symm
      _ = m (chainTop C) / ((chainTop C).card : ℝ) := hα1
  have hle2 : m (chainTop C) / ((chainTop C).card : ℝ) ≤ n (chainTop D) / ((chainTop D).card : ℝ) := by
    have hβ2 : β v₂ = n (chainTop D) / ((chainTop D).card : ℝ) := by
      rw [hβ]
      exact coord_filter_eq_top hD hDne hv₂ hv₂not n
    have hα2 : α v₂ = ∑ ρ ∈ C.filter (fun ρ => v₂ ∈ ρ), m ρ / (ρ.card : ℝ) := by simp only [hα]
    have hle := le_coord_filter hC hCne (fun ρ hρ => le_of_lt (hm0 ρ hρ)) (hσeq.symm ▸ hv₂)
    calc m (chainTop C) / ((chainTop C).card : ℝ)
        ≤ ∑ ρ ∈ C.filter (fun ρ => v₂ ∈ ρ), m ρ / (ρ.card : ℝ) := hle
      _ = α v₂ := hα2.symm
      _ = β v₂ := hαβ v₂ (hσeq.symm ▸ hv₂)
      _ = n (chainTop D) / ((chainTop D).card : ℝ) := hβ2
  have e1 : n (chainTop D) / ((chainTop C).card : ℝ) ≤ m (chainTop C) / ((chainTop C).card : ℝ) := by
    have h := hle1
    rwa [hσcard] at h
  have e2 : m (chainTop C) / ((chainTop C).card : ℝ) ≤ n (chainTop D) / ((chainTop C).card : ℝ) := by
    have h := hle2
    rwa [hσcard] at h
  have hcne : ((chainTop C).card : ℝ) ≠ 0 := ne_of_gt hcardC
  have hmul1 := mul_le_mul_of_nonneg_right e1 hcardC.le
  have hmul2 := mul_le_mul_of_nonneg_right e2 hcardC.le
  rw [div_mul_cancel₀ _ hcne, div_mul_cancel₀ _ hcne] at hmul1 hmul2
  exact le_antisymm hmul2 hmul1

/-- **The gluing property of the barycentric subdivision, positive-coefficient form.** -/
lemma inter_subset_bary_aux {K : Cx N} :
    ∀ (a : ℕ) (C D : Finset (Finset (E N))), C.card + D.card ≤ a → IsChain K C → IsChain K D →
      ∀ (m n : Finset (E N) → ℝ), (∀ ρ ∈ C, 0 < m ρ) → (∀ ρ ∈ D, 0 < n ρ) →
      (∑ ρ ∈ C, m ρ) = 1 → (∑ ρ ∈ D, n ρ) = 1 → ∀ x : E N,
      x = (∑ ρ ∈ C, m ρ • bary ρ) → x = (∑ ρ ∈ D, n ρ • bary ρ) →
      x ∈ convexHull ℝ (((C ∩ D).image bary : Finset (E N)) : Set (E N)) := by
  intro a
  induction a with
  | zero =>
    intro C D hcard hC hD m n hm0 hn0 hmsum hnsum x hx hx'
    have hC0 : C = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hC0, Finset.sum_empty] at hmsum
    exact absurd hmsum.symm one_ne_zero
  | succ a ih =>
    intro C D hcard hC hD m n hm0 hn0 hmsum hnsum x hx hx'
    have hCne : C.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hmsum
      exact one_ne_zero hmsum.symm
    have hDne : D.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hnsum
      exact one_ne_zero hnsum.symm
    have hσC : chainTop C ∈ C := chainTop_mem_chain hC.2 hCne
    have hσD : chainTop D ∈ D := chainTop_mem_chain hD.2 hDne
    have hfacesC : chainTop C ∈ K.faces := hC.1 _ hσC
    have hσeq : chainTop C = chainTop D := by
      refine le_antisymm ?_ ?_
      · refine chainTop_subset_of_mem_simp hC hCne hm0 hmsum hx (hD.1 _ hσD) ?_
        rw [hx']
        exact sum_smul_bary_mem_simp_chainTop hD hDne (fun ρ hρ => le_of_lt (hn0 ρ hρ)) hnsum
      · refine chainTop_subset_of_mem_simp hD hDne hn0 hnsum hx' hfacesC ?_
        rw [hx]
        exact sum_smul_bary_mem_simp_chainTop hC hCne (fun ρ hρ => le_of_lt (hm0 ρ hρ)) hmsum
    have hσCD : chainTop C ∈ C ∩ D := Finset.mem_inter.mpr ⟨hσC, hσeq ▸ hσD⟩
    have hle_t : m (chainTop C) ≤ 1 := by
      rw [← hmsum]
      exact Finset.single_le_sum (f := m) (fun ρ hρ => le_of_lt (hm0 ρ hρ)) hσC
    have hle_s : n (chainTop D) ≤ 1 := by
      rw [← hnsum]
      exact Finset.single_le_sum (f := n) (fun ρ hρ => le_of_lt (hn0 ρ hρ)) hσD
    rcases lt_or_eq_of_le hle_t with ht1 | ht1
    · rcases lt_or_eq_of_le hle_s with hs1 | hs1
      · -- general case
        have h1mt : (1 : ℝ) - m (chainTop C) ≠ 0 := by linarith
        have h1ns : (1 : ℝ) - n (chainTop D) ≠ 0 := by linarith
        have h1mtpos : (0 : ℝ) < 1 - m (chainTop C) := by linarith
        have htop : m (chainTop C) = n (chainTop D) :=
          top_coeff_eq_of_eq hC hD hCne hDne hm0 hn0 hmsum hnsum hσeq hx hx'
        set m' : Finset (E N) → ℝ := fun ρ => m ρ / (1 - m (chainTop C)) with hm'
        set n' : Finset (E N) → ℝ := fun ρ => n ρ / (1 - n (chainTop D)) with hn'
        set y : E N := ∑ ρ ∈ C.erase (chainTop C), m' ρ • bary ρ with hy
        have hC'sum : (∑ ρ ∈ C.erase (chainTop C), m ρ) = 1 - m (chainTop C) := by
          have h := Finset.sum_erase_add C m hσC
          linarith
        have hD'sum : (∑ ρ ∈ D.erase (chainTop D), n ρ) = 1 - n (chainTop D) := by
          have h := Finset.sum_erase_add D n hσD
          linarith
        have hsplitC : x = m (chainTop C) • bary (chainTop C) + (1 - m (chainTop C)) • y := by
          have hsum' : (∑ ρ ∈ C, m ρ • bary ρ) =
              (∑ ρ ∈ C.erase (chainTop C), m ρ • bary ρ) + m (chainTop C) • bary (chainTop C) :=
            (Finset.sum_erase_add C (fun ρ => m ρ • bary ρ) hσC).symm
          have hy' : (∑ ρ ∈ C.erase (chainTop C), m ρ • bary ρ) = (1 - m (chainTop C)) • y := by
            rw [hy, Finset.smul_sum]
            refine Finset.sum_congr rfl fun ρ _ => ?_
            rw [hm', smul_smul]
            congr 1
            field_simp
          rw [hx, hsum', hy', add_comm]
        have hsplitD : x = n (chainTop D) • bary (chainTop D) +
            (1 - n (chainTop D)) • (∑ ρ ∈ D.erase (chainTop D), n' ρ • bary ρ) := by
          have hsum' : (∑ ρ ∈ D, n ρ • bary ρ) =
              (∑ ρ ∈ D.erase (chainTop D), n ρ • bary ρ) + n (chainTop D) • bary (chainTop D) :=
            (Finset.sum_erase_add D (fun ρ => n ρ • bary ρ) hσD).symm
          have hy' : (∑ ρ ∈ D.erase (chainTop D), n ρ • bary ρ) =
              (1 - n (chainTop D)) • (∑ ρ ∈ D.erase (chainTop D), n' ρ • bary ρ) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun ρ _ => ?_
            rw [hn', smul_smul]
            congr 1
            field_simp
          rw [hx', hsum', hy', add_comm]
        have hyeq : y = ∑ ρ ∈ D.erase (chainTop D), n' ρ • bary ρ := by
          have h := hsplitC.symm.trans hsplitD
          have hb : bary (chainTop D) = bary (chainTop C) := by rw [hσeq]
          rw [hb, ← htop] at h
          have h2 := add_left_cancel h
          have h3 := congrArg (fun z => (1 - m (chainTop C))⁻¹ • z) h2
          simpa [smul_smul, inv_mul_cancel₀ h1mt, one_smul] using h3
        have hcard' : (C.erase (chainTop C)).card + (D.erase (chainTop D)).card ≤ a := by
          rw [Finset.card_erase_of_mem hσC, Finset.card_erase_of_mem hσD]
          omega
        have hm'0 : ∀ ρ ∈ C.erase (chainTop C), 0 < m' ρ := by
          intro ρ hρ
          rw [hm']
          exact div_pos (hm0 ρ (Finset.mem_of_mem_erase hρ)) h1mtpos
        have hn'0 : ∀ ρ ∈ D.erase (chainTop D), 0 < n' ρ := by
          intro ρ hρ
          rw [hn']
          exact div_pos (hn0 ρ (Finset.mem_of_mem_erase hρ)) (by rw [← htop]; linarith)
        have hm'sum : (∑ ρ ∈ C.erase (chainTop C), m' ρ) = 1 := by
          rw [hm', ← Finset.sum_div, hC'sum, div_self h1mt]
        have hn'sum : (∑ ρ ∈ D.erase (chainTop D), n' ρ) = 1 := by
          rw [hn', ← Finset.sum_div, hD'sum, div_self h1ns]
        have hyC : y ∈ convexHull ℝ
            ((((C.erase (chainTop C)) ∩ (D.erase (chainTop D))).image bary : Finset (E N)) :
              Set (E N)) :=
          ih _ _ hcard' (hC.erase _) (hD.erase _) m' n' hm'0 hn'0 hm'sum hn'sum y hy.symm
            (hyeq ▸ hy.symm)
        have hyD : y ∈ convexHull ℝ (((C ∩ D).image bary : Finset (E N)) : Set (E N)) :=
          convexHull_mono (Finset.coe_subset.mpr fun b hb => by
            obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hb
            exact Finset.mem_image.mpr ⟨ρ, Finset.mem_inter.mpr
              ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hρ).1,
               Finset.mem_of_mem_erase (Finset.mem_inter.mp hρ).2⟩, rfl⟩) hyC
        have hbσ : bary (chainTop C) ∈ convexHull ℝ (((C ∩ D).image bary : Finset (E N)) :
            Set (E N)) :=
          subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_image.mpr ⟨chainTop C, hσCD, rfl⟩))
        rw [hsplitC]
        exact convex_combo_mem (convex_convexHull ℝ _) hbσ hyD (le_of_lt (hm0 _ hσC)) ht1.le
      · -- the top coefficient of `D` is `1`
        have hDsub : D ⊆ {chainTop D} := by
          intro ρ hρ
          by_contra hρσ
          have hlt := Finset.single_lt_sum (f := n) (fun h => hρσ (Finset.mem_singleton.mpr h))
            hσD hρ (hn0 ρ hρ) (fun k hk _ => le_of_lt (hn0 k hk))
          rw [hnsum] at hlt
          rw [hs1] at hlt
          exact lt_irrefl _ hlt
        have hDeq : D = {chainTop D} := Finset.Subset.antisymm hDsub
          (Finset.singleton_subset_iff.mpr hσD)
        have hxσ : x = bary (chainTop D) := by
          have hconst : ∀ ρ ∈ D, n ρ • bary ρ = n ρ • bary (chainTop D) := by
            intro ρ hρ
            rw [Finset.mem_singleton.mp (hDsub hρ)]
          rw [hx', Finset.sum_congr rfl hconst, ← Finset.sum_smul, hnsum, one_smul]
        have hxσC : x = bary (chainTop C) := by rw [hxσ, ← hσeq]
        exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨chainTop C, hσCD, hxσC.symm⟩))
    · -- the top coefficient of `C` is `1`
      have hCsub : C ⊆ {chainTop C} := by
        intro ρ hρ
        by_contra hρσ
        have hlt := Finset.single_lt_sum (f := m) (fun h => hρσ (Finset.mem_singleton.mpr h))
          hσC hρ (hm0 ρ hρ) (fun k hk _ => le_of_lt (hm0 k hk))
        rw [hmsum] at hlt
        rw [ht1] at hlt
        exact lt_irrefl _ hlt
      have hCeq : C = {chainTop C} := Finset.Subset.antisymm hCsub
        (Finset.singleton_subset_iff.mpr hσC)
      have hxσ : x = bary (chainTop C) := by
        have hconst : ∀ ρ ∈ C, m ρ • bary ρ = m ρ • bary (chainTop C) := by
          intro ρ hρ
          rw [Finset.mem_singleton.mp (hCsub hρ)]
        rw [hx, Finset.sum_congr rfl hconst, ← Finset.sum_smul, hmsum, one_smul]
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨chainTop C, hσCD, hxσ.symm⟩))

/-- **The gluing property of the barycentric subdivision.**  The faces of `sd K` are the
barycenters of chains; two of them meet in the simplex of the intersection of the chains. -/
theorem inter_subset_bary {K : Cx N} {C D : Finset (Finset (E N))} (hC : IsChain K C)
    (hD : IsChain K D) :
    convexHull ℝ ((C.image bary : Finset (E N)) : Set (E N)) ∩
      convexHull ℝ ((D.image bary : Finset (E N)) : Set (E N)) ⊆
      convexHull ℝ (((C ∩ D).image bary : Finset (E N)) : Set (E N)) := by
  intro x hx
  obtain ⟨hxC, hxD⟩ := hx
  obtain ⟨μ, hμ0, hμsum, hμx, -⟩ := exists_sum_smul_of_mem_simp hxC
  obtain ⟨ν, hν0, hνsum, hνx, -⟩ := exists_sum_smul_of_mem_simp hxD
  set m : Finset (E N) → ℝ := fun ρ => μ (bary ρ) with hm
  set n : Finset (E N) → ℝ := fun ρ => ν (bary ρ) with hn
  have hinjC : ∀ ρ ∈ C, ∀ ρ' ∈ C, bary ρ = bary ρ' → ρ = ρ' :=
    fun ρ hρ ρ' hρ' h => bary_eq_of_chain hC hρ hρ' h
  have hinjD : ∀ ρ ∈ D, ∀ ρ' ∈ D, bary ρ = bary ρ' → ρ = ρ' :=
    fun ρ hρ ρ' hρ' h => bary_eq_of_chain hD hρ hρ' h
  have hmsum : (∑ ρ ∈ C, m ρ) = 1 := by
    have h1 : (∑ ρ ∈ C, m ρ) = ∑ ρ ∈ C, μ (bary ρ) :=
      Finset.sum_congr rfl fun ρ _ => by simp only [hm]
    have h2 : (∑ b ∈ C.image bary, μ b) = ∑ ρ ∈ C, μ (bary ρ) := Finset.sum_image hinjC
    rw [h1, ← h2, hμsum]
  have hnsum : (∑ ρ ∈ D, n ρ) = 1 := by
    have h1 : (∑ ρ ∈ D, n ρ) = ∑ ρ ∈ D, ν (bary ρ) :=
      Finset.sum_congr rfl fun ρ _ => by simp only [hn]
    have h2 : (∑ b ∈ D.image bary, ν b) = ∑ ρ ∈ D, ν (bary ρ) := Finset.sum_image hinjD
    rw [h1, ← h2, hνsum]
  have hmpt : (∑ ρ ∈ C, m ρ • bary ρ) = x := by
    have h1 : (∑ ρ ∈ C, m ρ • bary ρ) = ∑ ρ ∈ C, μ (bary ρ) • bary ρ :=
      Finset.sum_congr rfl fun ρ _ => by simp only [hm]
    have h2 : (∑ b ∈ C.image bary, μ b • b) = ∑ ρ ∈ C, μ (bary ρ) • bary ρ :=
      Finset.sum_image hinjC
    rw [h1, ← h2, hμx]
  have hnpt : (∑ ρ ∈ D, n ρ • bary ρ) = x := by
    have h1 : (∑ ρ ∈ D, n ρ • bary ρ) = ∑ ρ ∈ D, ν (bary ρ) • bary ρ :=
      Finset.sum_congr rfl fun ρ _ => by simp only [hn]
    have h2 : (∑ b ∈ D.image bary, ν b • b) = ∑ ρ ∈ D, ν (bary ρ) • bary ρ :=
      Finset.sum_image hinjD
    rw [h1, ← h2, hνx]
  set Cs : Finset (Finset (E N)) := C.filter (fun ρ => m ρ ≠ 0) with hCs
  set Ds : Finset (Finset (E N)) := D.filter (fun ρ => n ρ ≠ 0) with hDs
  have hCssub : Cs ⊆ C := by rw [hCs]; exact Finset.filter_subset _ _
  have hDssub : Ds ⊆ D := by rw [hDs]; exact Finset.filter_subset _ _
  have hchainCs : IsChain K Cs := hC.mono hCssub
  have hchainDs : IsChain K Ds := hD.mono hDssub
  have hposC : ∀ ρ ∈ Cs, 0 < m ρ := by
    intro ρ hρ
    obtain ⟨hρC, hne⟩ := Finset.mem_filter.mp hρ
    refine lt_of_le_of_ne (hμ0 (bary ρ) (Finset.mem_image.mpr ⟨ρ, hρC, rfl⟩)) ?_
    rw [hm] at hne
    exact fun h => hne h.symm
  have hposD : ∀ ρ ∈ Ds, 0 < n ρ := by
    intro ρ hρ
    obtain ⟨hρD, hne⟩ := Finset.mem_filter.mp hρ
    refine lt_of_le_of_ne (hν0 (bary ρ) (Finset.mem_image.mpr ⟨ρ, hρD, rfl⟩)) ?_
    rw [hn] at hne
    exact fun h => hne h.symm
  have hsumCs : (∑ ρ ∈ Cs, m ρ) = 1 := by
    rw [← hmsum]
    refine Finset.sum_subset hCssub fun ρ hρ hρ' => ?_
    by_contra hne
    exact hρ' (by rw [hCs]; exact Finset.mem_filter.mpr ⟨hρ, hne⟩)
  have hsumDs : (∑ ρ ∈ Ds, n ρ) = 1 := by
    rw [← hnsum]
    refine Finset.sum_subset hDssub fun ρ hρ hρ' => ?_
    by_contra hne
    exact hρ' (by rw [hDs]; exact Finset.mem_filter.mpr ⟨hρ, hne⟩)
  have hptCs : (∑ ρ ∈ Cs, m ρ • bary ρ) = x := by
    rw [← hmpt]
    refine Finset.sum_subset hCssub fun ρ hρ hρ' => ?_
    have hz : m ρ = 0 := by
      by_contra hne
      exact hρ' (by rw [hCs]; exact Finset.mem_filter.mpr ⟨hρ, hne⟩)
    rw [hz, zero_smul]
  have hptDs : (∑ ρ ∈ Ds, n ρ • bary ρ) = x := by
    rw [← hnpt]
    refine Finset.sum_subset hDssub fun ρ hρ hρ' => ?_
    have hz : n ρ = 0 := by
      by_contra hne
      exact hρ' (by rw [hDs]; exact Finset.mem_filter.mpr ⟨hρ, hne⟩)
    rw [hz, zero_smul]
  have hmain := inter_subset_bary_aux (K := K) (Cs.card + Ds.card) Cs Ds le_rfl hchainCs
    hchainDs m n hposC hposD hsumCs hsumDs x hptCs.symm hptDs.symm
  exact convexHull_mono (Finset.coe_subset.mpr
    (Finset.image_subset_image (Finset.inter_subset_inter hCssub hDssub))) hmain

end

end Work.PL.Subdiv
