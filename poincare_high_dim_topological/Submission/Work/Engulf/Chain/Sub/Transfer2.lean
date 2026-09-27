import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.Sub.Basic
import Submission.Work.Engulf.Chain.Sub.RelInt
import Submission.Work.Engulf.Chain.Sub.Skel
import Submission.Work.Engulf.Chain.Sub.Transfer
import Submission.Work.Engulf.Chain.Sub.exists_coarse_face_superset

/-!
# `Submission.Work.Engulf.Chain.Sub.Transfer2`

More transfer lemmas for the outer loop of `Work.Engulf.Chain.E5`:

* `exists_relInt_coarse` : every point of a coarse simplex lies in the relative interior of some
  coarse subface;
* `simp_subset_coarse_of_relInt` : the simplex of a fine face whose relative interior meets a
  coarse simplex is contained in that coarse simplex (LEMMA M of the `E5` design);
* `card_le_of_simp_subset_loop` : the vertex bound `Cfg.dimH` for the pushed configuration of the
  outer loop.
-/

open Set Metric PL

set_option maxHeartbeats 1000000

namespace Work.Engulf.Chain

variable {N : ℕ}

/-- Every point of a coarse simplex lies in the relative interior of a coarse subface. -/
theorem exists_relInt_coarse {Γ : PL.Cx N} {u : Finset (PL.E N)} (hu : u ∈ Γ.faces) {p : PL.E N}
    (hp : p ∈ PL.simp u) : ∃ e ∈ Γ.faces, e ⊆ u ∧ RelInt Γ e p := by
  classical
  obtain ⟨a, ha0, ha1, ha2⟩ := mem_simp_iff.1 hp
  have hfilt : ∀ v ∈ u, v ∉ u.filter (fun v => 0 < a v) → a v = 0 := by
    intro v hv hvf
    by_contra hne
    exact hvf (Finset.mem_filter.mpr ⟨hv, lt_of_le_of_ne (ha0 v hv) (Ne.symm hne)⟩)
  have hne : (u.filter fun v => 0 < a v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hzero : ∀ v ∈ u, a v = 0 := by
      intro v hv
      exact hfilt v hv (by rw [hemp]; simp)
    have := Finset.sum_eq_zero hzero
    rw [ha1] at this
    norm_num at this
  refine ⟨u.filter (fun v => 0 < a v), Γ.down_closed hu (Finset.filter_subset _ _) hne,
    Finset.filter_subset _ _, ?_⟩
  rw [relInt_iff_weights (Γ.down_closed hu (Finset.filter_subset _ _) hne)]
  refine ⟨a, fun v hv => (Finset.mem_filter.1 hv).2, ?_, ?_⟩
  · rw [Finset.sum_subset (Finset.filter_subset _ _) hfilt, ha1]
  · rw [Finset.sum_subset (Finset.filter_subset _ _)
      (fun v hv hvf => by rw [hfilt v hv hvf, zero_smul]), ha2]

/-- **LEMMA M.**  If the relative interior of a fine face `t` meets a coarse simplex `simp u`, then
the whole simplex of `t` is contained in `simp u`. -/
theorem simp_subset_coarse_of_relInt {Γ Γ₁ : PL.Cx N} (hsub : PL.Subdivides Γ₁ Γ)
    {t : Finset (PL.E N)} (ht : t ∈ Γ₁.faces) {u : Finset (PL.E N)} (hu : u ∈ Γ.faces)
    {p : PL.E N} (hp : RelInt Γ₁ t p) (hpu : p ∈ PL.simp u) : PL.simp t ⊆ PL.simp u := by
  obtain ⟨e, he, heu, hpe⟩ := exists_relInt_coarse hu hpu
  obtain ⟨-, hsub'⟩ := hsub
  obtain ⟨e₀, he₀, hse₀⟩ := hsub' t ht
  have hpe₀ : p ∈ PL.simp e₀ := hse₀ hp.1
  have hee₀ : e ⊆ e₀ := subset_of_relInt_mem he he₀ hpe hpe₀
  have hpos : ∀ v ∈ t, p ∉ PL.simp (t.erase v) := by
    intro v hv hmem
    rcases Finset.eq_empty_or_nonempty (t.erase v) with hemp | hne
    · rw [hemp, simp_empty] at hmem
      exact hmem
    · exact hp.2 _ (Γ₁.down_closed ht (Finset.erase_subset v t) hne) (Finset.erase_ssubset hv) hmem
  exact (Work.Engulf.Chain.Sub.simp_subset_of_mem_simp_of_positive_weights (Γ.indep he₀) hse₀
    hp.1 hpos hee₀ hpe.1).trans (simp_mono heu)

/-- Membership in `⋃ w ∈ τ, simp (σ.erase w)`. -/
theorem mem_iUnion₂_erase {σ τ : Finset (PL.E N)} {y : PL.E N} :
    y ∈ (⋃ w ∈ τ, PL.simp (σ.erase w)) ↔ ∃ w ∈ τ, y ∈ PL.simp (σ.erase w) := by
  simp only [Set.mem_iUnion, exists_prop]

/-- The vertex bound for the pushed configuration of the outer loop. -/
theorem card_le_of_simp_subset_loop {Γ Γ₁ : PL.Cx N} (hsub : PL.Subdivides Γ₁ Γ)
    {K : Set (PL.E N)} (hK : Work.Engulf.IsSubSp Γ K) {p q : ℕ}
    (hbound : ∀ t ∈ Γ.faces, PL.simp t ⊆ K → t.card ≤ p + 1) (hqp : q + 1 ≤ p + 1)
    {ord : List (Finset (PL.E N))} {i : ℕ} (hi : i ≤ ord.length)
    (hfaces : ∀ j (hj : j < ord.length), ord.get ⟨j, hj⟩ ∈ Γ₁.faces)
    (hcards : ∀ j (hj : j < ord.length), (ord.get ⟨j, hj⟩).card = q + 2)
    {σ τ : Finset (PL.E N)} (hτσ : τ ⊆ σ) (hσcard : σ.card = q + 2) (hσface : σ ∈ Γ₁.faces)
    {s : Finset (PL.E N)} (hs : s ∈ Γ₁.faces)
    (h : PL.simp s ⊆ K ∪ skel ord i ∪ ⋃ w ∈ τ, PL.simp (σ.erase w)) : s.card ≤ p + 1 := by
  classical
  obtain ⟨b, hbs, hbpos⟩ := Work.Engulf.Chain.Sub.exists_relint_point hs
  have hbrel : RelInt Γ₁ s b := by
    refine ⟨hbs, fun s' hs' hss' hmem => ?_⟩
    obtain ⟨v, hvs, hvs'⟩ := Finset.exists_of_ssubset hss'
    have hsub' : s' ⊆ s.erase v := fun y hy =>
      Finset.mem_erase.mpr ⟨fun hyv => hvs' (hyv ▸ hy), hss'.1 hy⟩
    exact hbpos v hvs (simp_mono hsub' hmem)
  have hb := h hbs
  rw [skel_eq_range] at hb
  have hard : ∀ (t : Finset (PL.E N)), t ∈ Γ₁.faces → t.card = q + 1 → b ∈ PL.simp t → s.card ≤ p + 1 := by
    intro t ht htc hbt
    have hst : s ⊆ t := subset_of_relInt_mem hs ht hbrel hbt
    calc s.card ≤ t.card := Finset.card_le_card hst
      _ = q + 1 := htc
      _ ≤ p + 1 := hqp
  rw [Set.mem_union] at hb
  rcases hb with hbKA | hbτ
  · rw [Set.mem_union] at hbKA
    rcases hbKA with hbK | hbSkel
    · obtain ⟨u, hu, hbu, huK⟩ := hK.2 b hbK
      exact card_le_of_simp_subset_subdivides hsub hK hbound hs (Subset.trans
        (simp_subset_coarse_of_relInt hsub hs hu hbrel hbu) huK)
    · -- the fine skeleton
      rw [mem_range_erase_union] at hbSkel
      obtain ⟨j, hj, w, hw, hbw⟩ := hbSkel
      have hjl : j < ord.length := by
        have h1 := Finset.mem_range.1 hj
        omega
      have hget : ord.getD j ∅ = ord.get ⟨j, hjl⟩ := List.getD_eq_get ord ∅ ⟨j, hjl⟩
      rw [hget] at hw hbw
      have hcard : (ord.get ⟨j, hjl⟩).card = q + 2 := hcards j hjl
      have hne : ((ord.get ⟨j, hjl⟩).erase w).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have h1 := Finset.card_erase_of_mem hw
        rw [hemp, Finset.card_empty] at h1
        omega
      exact hard _ (Γ₁.down_closed (hfaces j hjl) (Finset.erase_subset w _) hne)
        (by rw [Finset.card_erase_of_mem hw, hcard]; omega) hbw
  · -- the top facets of the current simplex
    rw [mem_iUnion₂_erase] at hbτ
    obtain ⟨w, hwτ, hbw⟩ := hbτ
    have hwσ : w ∈ σ := hτσ hwτ
    have hne : (σ.erase w).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have h1 := Finset.card_erase_of_mem hwσ
      rw [hemp, Finset.card_empty] at h1
      omega
    exact hard _ (Γ₁.down_closed hσface (Finset.erase_subset w σ) hne)
      (by rw [Finset.card_erase_of_mem hwσ, hσcard]; omega) hbw

end Work.Engulf.Chain
