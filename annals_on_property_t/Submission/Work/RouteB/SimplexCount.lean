import Submission.Work.RouteB.SimplexTrans

open scoped BigOperators

set_option autoImplicit false

/-!
# Counting edges of a sub-simplex

For `r ≤ m` we consider the sub-simplex of the standard `(m-1)`-simplex spanned by the first
`r` vertices, its edges (`Esub m r`), and the ordered pairs of such edges which are diagonal,
adjacent or opposite (`Dsub`, `Psub`, `Qsub`).  We compute the cardinalities needed by the
symmetrisation argument of Kaluba–Kielak–Nowak.
-/

namespace Submission.RouteB

namespace Edge

variable {m r : ℕ}

/-- The set of the first `r` vertices, as a finset of `Fin m`. -/
def Vsub (m r : ℕ) : Finset (Fin m) := Finset.univ.filter (fun k => k.val < r)

@[simp] lemma mem_Vsub {k : Fin m} : k ∈ Vsub m r ↔ k.val < r := by
  simp [Vsub]

lemma card_Vsub (h : r ≤ m) : (Vsub m r).card = r := by
  have hv : Vsub m r = (Finset.univ : Finset (Fin r)).image
      (fun k : Fin r => (⟨k.val, lt_of_lt_of_le k.isLt h⟩ : Fin m)) := by
    apply Finset.ext
    intro k
    rw [Finset.mem_image]
    constructor
    · intro hk
      rw [mem_Vsub] at hk
      exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨a, _, ha⟩
      rw [mem_Vsub, ← ha]
      exact a.isLt
  rw [hv, Finset.card_image_of_injOn (fun a _ b _ hab => Fin.ext (by simpa using hab)),
    Finset.card_univ, Fintype.card_fin]

/-- The edges of the sub-simplex spanned by the first `r` vertices. -/
def Esub (m r : ℕ) : Finset (Edge m) :=
  Finset.univ.filter (fun p => p.1.1.val < r ∧ p.1.2.val < r)

@[simp] lemma mem_Esub {p : Edge m} : p ∈ Esub m r ↔ p.1.1.val < r ∧ p.1.2.val < r := by
  simp [Esub]

lemma mem_Esub_iff {p : Edge m} : p ∈ Esub m r ↔ p.toFinset ⊆ Vsub m r := by
  rw [mem_Esub, toFinset, Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_Vsub,
    mem_Vsub]

lemma Esub_toFinset_subset {p : Edge m} (hp : p ∈ Esub m r) : p.toFinset ⊆ Vsub m r :=
  mem_Esub_iff.mp hp

lemma image_toFinset_Esub (m r : ℕ) :
    (Esub m r).image toFinset = (Vsub m r).powersetCard 2 := by
  apply Finset.ext
  intro s
  rw [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Esub_toFinset_subset hp, toFinset_card p⟩
  · rintro ⟨hsub, hcard⟩
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp hcard
    refine ⟨edgeOf i j hij, ?_, ?_⟩
    · rw [mem_Esub_iff, toFinset_edgeOf]
      intro k hk
      exact hsub (by rw [hs]; exact hk)
    · rw [toFinset_edgeOf, hs]

lemma card_Esub (h : r ≤ m) : (Esub m r).card = r.choose 2 := by
  rw [← Finset.card_image_of_injOn (f := toFinset) (s := Esub m r)
      (fun a _ b _ hab => toFinset_injective hab),
    image_toFinset_Esub, Finset.card_powersetCard, card_Vsub h]

/-- The ordered pairs of equal edges of the sub-simplex. -/
noncomputable def Dsub (m r : ℕ) : Finset (Edge m × Edge m) := by
  classical
  exact Finset.univ.filter (fun x => x.1 = x.2 ∧ x.1 ∈ Esub m r)

lemma mem_Dsub {x : Edge m × Edge m} :
    x ∈ Dsub m r ↔ x.1 = x.2 ∧ x.1 ∈ Esub m r := by
  classical simp [Dsub]

/-- The ordered pairs of adjacent edges of the sub-simplex. -/
noncomputable def Psub (m r : ℕ) : Finset (Edge m × Edge m) := by
  classical
  exact Finset.univ.filter (fun x => Adj x.1 x.2 ∧ x.1 ∈ Esub m r ∧ x.2 ∈ Esub m r)

lemma mem_Psub {x : Edge m × Edge m} :
    x ∈ Psub m r ↔ Adj x.1 x.2 ∧ x.1 ∈ Esub m r ∧ x.2 ∈ Esub m r := by
  classical simp [Psub]

/-- The ordered pairs of opposite edges of the sub-simplex. -/
noncomputable def Qsub (m r : ℕ) : Finset (Edge m × Edge m) := by
  classical
  exact Finset.univ.filter (fun x => Op x.1 x.2 ∧ x.1 ∈ Esub m r ∧ x.2 ∈ Esub m r)

lemma mem_Qsub {x : Edge m × Edge m} :
    x ∈ Qsub m r ↔ Op x.1 x.2 ∧ x.1 ∈ Esub m r ∧ x.2 ∈ Esub m r := by
  classical simp [Qsub]

lemma card_Dsub (m r : ℕ) : (Dsub m r).card = (Esub m r).card := by
  have hinj : Set.InjOn (fun x : Edge m × Edge m => x.1)
      ((Dsub m r : Finset (Edge m × Edge m)) : Set (Edge m × Edge m)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_Dsub] at ha hb
    exact Prod.ext hab (ha.1.symm.trans (hab.trans hb.1))
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  apply Finset.ext
  intro p
  simp only [Finset.mem_image, mem_Dsub]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, hx⟩
    rw [← hx]
    exact h2
  · intro hp
    exact ⟨(p, p), ⟨rfl, hp⟩, rfl⟩

/-! ## Auxiliary finset identities -/

lemma inter_union_sdiff (s t : Finset (Fin m)) : (s ∩ t) ∪ (s \ t) = s := by
  ext k
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

lemma union_inter_eq_left {S T p : Finset (Fin m)} (hS : S ⊆ p) (hT : T ∩ p = ∅) :
    (S ∪ T) ∩ p = S := by
  ext k
  rw [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hk | hk, hkp⟩
    · exact hk
    · have hmem : k ∈ T ∩ p := Finset.mem_inter.mpr ⟨hk, hkp⟩
      rw [hT] at hmem
      exact absurd hmem (Finset.notMem_empty k)
  · intro hk
    exact ⟨Or.inl hk, hS hk⟩

lemma union_sdiff_eq_right {S T p : Finset (Fin m)} (hS : S ⊆ p) (hT : T ∩ p = ∅) :
    (S ∪ T) \ p = T := by
  ext k
  rw [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hk | hk, hkp⟩
    · exact absurd (hS hk) hkp
    · exact hk
  · intro hk
    refine ⟨Or.inr hk, fun hkp => ?_⟩
    have hmem : k ∈ T ∩ p := Finset.mem_inter.mpr ⟨hk, hkp⟩
    rw [hT] at hmem
    exact absurd hmem (Finset.notMem_empty k)

lemma disjoint_of_subset_inter_eq_empty {S T p : Finset (Fin m)} (hS : S ⊆ p)
    (hT : T ∩ p = ∅) : Disjoint S T := by
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [Finset.mem_inter] at hk
  have hmem : k ∈ T ∩ p := Finset.mem_inter.mpr ⟨hk.2, hS hk.1⟩
  rw [hT] at hmem
  exact Finset.notMem_empty k hmem

lemma card_sdiff_two {p : Edge m} (hp : p ∈ Esub m r) :
    (Vsub m r \ p.toFinset).card = (Vsub m r).card - 2 := by
  have h := Finset.card_sdiff_add_card_eq_card (Esub_toFinset_subset (r := r) hp)
  rw [toFinset_card] at h
  omega

/-! ## Per-edge counts -/

lemma image_filter_op (m r : ℕ) (p : Edge m) :
    ((Esub m r).filter (fun q => Op p q)).image toFinset
      = (Vsub m r \ p.toFinset).powersetCard 2 := by
  classical
  apply Finset.ext
  intro s
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqs⟩
    rw [Finset.mem_filter] at hq
    obtain ⟨hqE, hop⟩ := hq
    rw [Finset.mem_powersetCard, ← hqs]
    refine ⟨?_, toFinset_card q⟩
    intro k hk
    exact Finset.mem_sdiff.mpr ⟨Esub_toFinset_subset hqE hk,
      fun hkp => (Finset.disjoint_left.mp hop hkp) hk⟩
  · intro hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hcard⟩ := hs
    obtain ⟨i, j, hij, hs'⟩ := Finset.card_eq_two.mp hcard
    refine ⟨edgeOf i j hij, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [mem_Esub_iff, toFinset_edgeOf]
        intro k hk
        exact (Finset.mem_sdiff.mp (hsub (by rw [hs']; exact hk))).1
      · rw [Op, toFinset_edgeOf, ← hs']
        refine Finset.disjoint_left.mpr fun k hk hk2 => ?_
        exact (Finset.mem_sdiff.mp (hsub hk2)).2 hk
    · rw [toFinset_edgeOf, hs']

lemma filter_op_card (m r : ℕ) (p : Edge m) :
    ((Esub m r).filter (fun q => Op p q)).card
      = (Vsub m r \ p.toFinset).card.choose 2 := by
  classical
  rw [← Finset.card_image_of_injOn (f := toFinset)
      (s := (Esub m r).filter (fun q => Op p q)) (fun a _ b _ hab => toFinset_injective hab),
    image_filter_op, Finset.card_powersetCard]

lemma filter_op_card' {p : Edge m} (hp : p ∈ Esub m r) :
    ((Esub m r).filter (fun q => Op p q)).card = ((Vsub m r).card - 2).choose 2 := by
  classical
  rw [filter_op_card, card_sdiff_two hp]

lemma image_filter_adj (m r : ℕ) (p : Edge m) :
    ((Esub m r).filter (fun q => Adj p q)).image toFinset
      = ((Vsub m r).powersetCard 2).filter (fun s => (s ∩ p.toFinset).card = 1) := by
  classical
  apply Finset.ext
  intro s
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, hqs⟩
    rw [Finset.mem_filter] at hq
    obtain ⟨hqE, hne, hnd⟩ := hq
    rw [Finset.mem_filter, Finset.mem_powersetCard, ← hqs]
    refine ⟨⟨Esub_toFinset_subset hqE, toFinset_card q⟩, ?_⟩
    have hle : (q.toFinset ∩ p.toFinset).card ≤ 2 := by
      rw [← toFinset_card q]
      exact Finset.card_le_card Finset.inter_subset_left
    have hpos : 0 < (q.toFinset ∩ p.toFinset).card := by
      rw [Finset.card_pos]
      obtain ⟨k, hk1, hk2⟩ := Finset.not_disjoint_iff.mp hnd
      exact ⟨k, Finset.mem_inter.mpr ⟨hk2, hk1⟩⟩
    have hne2 : (q.toFinset ∩ p.toFinset).card ≠ 2 := by
      intro h2
      have h1 : q.toFinset ∩ p.toFinset = q.toFinset :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h2, toFinset_card])
      have hsub' : q.toFinset ⊆ p.toFinset := h1 ▸ Finset.inter_subset_right
      have hpeq : q.toFinset = p.toFinset :=
        Finset.eq_of_subset_of_card_le hsub' (by rw [toFinset_card, toFinset_card])
      exact hne.symm (toFinset_injective hpeq)
    omega
  · intro hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsub, hcard⟩, hinter⟩ := hs
    obtain ⟨i, j, hij, hs'⟩ := Finset.card_eq_two.mp hcard
    refine ⟨edgeOf i j hij, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_Esub_iff, toFinset_edgeOf]
        intro k hk
        exact hsub (by rw [hs']; exact hk)
      · intro heq
        have hcardp : (s ∩ p.toFinset).card = 1 := hinter
        rw [heq, toFinset_edgeOf, ← hs', Finset.inter_self] at hcardp
        omega
      · rw [toFinset_edgeOf, ← hs']
        intro hd
        have hcardp : (s ∩ p.toFinset).card = 1 := hinter
        have h0 : (s ∩ p.toFinset).card = 0 := by
          rw [Finset.inter_comm, Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty]
        omega
    · rw [toFinset_edgeOf, hs']

/-- The number of `2`-element subsets of `V` meeting a fixed `2`-element set `p ⊆ V` in exactly
one element. -/
lemma card_powersetCard_two_inter_one (V p : Finset (Fin m)) (hpV : p ⊆ V) (hpc : p.card = 2) :
    ((V.powersetCard 2).filter (fun s => (s ∩ p).card = 1)).card = 2 * (V \ p).card := by
  classical
  have hcard : (p.powersetCard 1 ×ˢ (V \ p).powersetCard 1).card = 2 * (V \ p).card := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Nat.choose_one_right, Nat.choose_one_right, hpc]
  rw [← hcard]
  refine Finset.card_bij (fun s _ => (s ∩ p, s \ p)) ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨hsV, hscard⟩, hinter⟩ := hs
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨Finset.inter_subset_right, hinter⟩, ?_, ?_⟩
    · intro k hk
      rw [Finset.mem_sdiff] at hk
      exact Finset.mem_sdiff.mpr ⟨hsV hk.1, hk.2⟩
    · rw [Finset.card_sdiff, Finset.inter_comm, hinter, hscard]
  · intro s _ t _ hst
    rw [Prod.mk.injEq] at hst
    rw [← inter_union_sdiff s p, ← inter_union_sdiff t p, hst.1, hst.2]
  · intro y hy
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hy
    obtain ⟨⟨hSp, hScard⟩, hTV, hTcard⟩ := hy
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hScard
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hTcard
    have haS : a ∈ y.1 := by rw [ha]; exact Finset.mem_singleton_self a
    have hbT : b ∈ y.2 := by rw [hb]; exact Finset.mem_singleton_self b
    have hap : a ∈ p := hSp haS
    have hbVp : b ∈ V \ p := hTV hbT
    have hbp : b ∉ p := (Finset.mem_sdiff.mp hbVp).2
    have hbV : b ∈ V := (Finset.mem_sdiff.mp hbVp).1
    have hTp : y.2 ∩ p = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      rw [Finset.mem_inter] at hk
      rw [hb] at hk
      rw [Finset.mem_singleton] at hk
      exact hbp (hk.1 ▸ hk.2)
    refine ⟨y.1 ∪ y.2, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro k hk
        rw [Finset.mem_union] at hk
        rcases hk with hk | hk
        · exact hpV (hSp hk)
        · rw [hb, Finset.mem_singleton] at hk
          exact hk ▸ hbV
      · have hdisj := disjoint_of_subset_inter_eq_empty hSp hTp
        rw [Finset.card_union_of_disjoint hdisj, ha, hb]
        simp
      · rw [union_inter_eq_left hSp hTp, ha, Finset.card_singleton]
    · rw [Prod.mk.injEq]
      exact ⟨union_inter_eq_left hSp hTp, union_sdiff_eq_right hSp hTp⟩

lemma card_filter_adj {p : Edge m} (hpV : p.toFinset ⊆ Vsub m r) :
    ((Esub m r).filter (fun q => Adj p q)).card = 2 * (Vsub m r \ p.toFinset).card := by
  classical
  rw [← Finset.card_image_of_injOn (f := toFinset)
      (s := (Esub m r).filter (fun q => Adj p q)) (fun a _ b _ hab => toFinset_injective hab),
    image_filter_adj,
    card_powersetCard_two_inter_one (Vsub m r) p.toFinset hpV (toFinset_card p)]

lemma card_filter_adj' {p : Edge m} (hp : p ∈ Esub m r) :
    ((Esub m r).filter (fun q => Adj p q)).card = 2 * ((Vsub m r).card - 2) := by
  rw [card_filter_adj (Esub_toFinset_subset hp), card_sdiff_two hp]

/-! ## Cardinalities of `Dsub`, `Psub`, `Qsub` -/

lemma biUnion_Psub (m r : ℕ) :
    (Esub m r).biUnion (fun p => ((Esub m r).filter (fun q => Adj p q)).image (fun q => (p, q)))
      = Psub m r := by
  classical
  apply Finset.ext
  intro x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Finset.mem_filter] at hq
    rw [mem_Psub]
    exact ⟨hq.2, hp, hq.1⟩
  · intro hx
    rw [mem_Psub] at hx
    exact ⟨x.1, hx.2.1, Finset.mem_image.mpr
      ⟨x.2, Finset.mem_filter.mpr ⟨hx.2.2, hx.1⟩, rfl⟩⟩

set_option maxHeartbeats 800000 in
lemma card_Psub_sigma (m r : ℕ) :
    (Psub m r).card = ∑ p ∈ Esub m r, ((Esub m r).filter (fun q => Adj p q)).card := by
  classical
  rw [← biUnion_Psub m r, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun p _ => Finset.card_image_of_injOn
      (fun a _ b _ hab => by simpa using hab))
  · intro a _ b _ hab
    show Disjoint (((Esub m r).filter (fun q => Adj a q)).image (fun q => (a, q)))
      (((Esub m r).filter (fun q => Adj b q)).image (fun q => (b, q)))
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨q1, _, h1⟩ := hx1
    obtain ⟨q2, _, h2⟩ := hx2
    have : (a, q1) = (b, q2) := h1.trans h2.symm
    simp only [Prod.mk.injEq] at this
    exact hab this.1

lemma biUnion_Qsub (m r : ℕ) :
    (Esub m r).biUnion (fun p => ((Esub m r).filter (fun q => Op p q)).image (fun q => (p, q)))
      = Qsub m r := by
  classical
  apply Finset.ext
  intro x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [Finset.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Finset.mem_filter] at hq
    rw [mem_Qsub]
    exact ⟨hq.2, hp, hq.1⟩
  · intro hx
    rw [mem_Qsub] at hx
    exact ⟨x.1, hx.2.1, Finset.mem_image.mpr
      ⟨x.2, Finset.mem_filter.mpr ⟨hx.2.2, hx.1⟩, rfl⟩⟩

set_option maxHeartbeats 800000 in
lemma card_Qsub_sigma (m r : ℕ) :
    (Qsub m r).card = ∑ p ∈ Esub m r, ((Esub m r).filter (fun q => Op p q)).card := by
  classical
  rw [← biUnion_Qsub m r, Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun p _ => Finset.card_image_of_injOn
      (fun a _ b _ hab => by simpa using hab))
  · intro a _ b _ hab
    show Disjoint (((Esub m r).filter (fun q => Op a q)).image (fun q => (a, q)))
      (((Esub m r).filter (fun q => Op b q)).image (fun q => (b, q)))
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨q1, _, h1⟩ := hx1
    obtain ⟨q2, _, h2⟩ := hx2
    have : (a, q1) = (b, q2) := h1.trans h2.symm
    simp only [Prod.mk.injEq] at this
    exact hab this.1

lemma card_Dsub' (m r : ℕ) : (Dsub m r).card = (Esub m r).card := card_Dsub m r

lemma card_Psub' (m r : ℕ) (hr : r ≤ m) :
    (Psub m r).card = (Esub m r).card * (2 * (r - 2)) := by
  rw [card_Psub_sigma]
  have hterm : ∀ p ∈ Esub m r,
      ((Esub m r).filter (fun q => Adj p q)).card = 2 * (r - 2) := by
    intro p hp
    rw [card_filter_adj' hp, card_Vsub hr]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

lemma card_Qsub' (m r : ℕ) (hr : r ≤ m) :
    (Qsub m r).card = (Esub m r).card * ((r - 2).choose 2) := by
  rw [card_Qsub_sigma]
  have hterm : ∀ p ∈ Esub m r,
      ((Esub m r).filter (fun q => Op p q)).card = ((r - 2).choose 2) := by
    intro p hp
    rw [filter_op_card' hp, card_Vsub hr]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]

/-- The `r`-vertex sub-simplex has positive many edges as soon as `2 ≤ r ≤ m`. -/
lemma card_Esub_pos (h : 2 ≤ r) (hr : r ≤ m) : 0 < (Esub m r).card := by
  rw [card_Esub hr]
  exact Nat.choose_pos h

lemma card_Psub_pos (hm : 3 ≤ m) : 0 < (Psub m m).card := by
  rw [card_Psub' m m le_rfl]
  exact Nat.mul_pos (card_Esub_pos (by omega) le_rfl) (by omega)

lemma card_Qsub_pos (hm : 4 ≤ m) : 0 < (Qsub m m).card := by
  rw [card_Qsub' m m le_rfl]
  exact Nat.mul_pos (card_Esub_pos (by omega) le_rfl) (Nat.choose_pos (by omega))

end Edge

end Submission.RouteB
