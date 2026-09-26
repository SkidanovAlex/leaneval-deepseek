import Mathlib
import Submission.Work.Smooth.JordanSeparation.janiszewski_disjoint

/-!
# A compact plane set with disconnected complement contains a continuum

We prove the classical plane-topology fact (Sierpiński): if `F ⊆ ℂ` is compact and its complement
`Fᶜ` is **not** preconnected, then `F` contains a **continuum**, i.e. a non-degenerate preconnected
subset: some `C` with `C ⊆ F`, `IsPreconnected C` and `C.Nontrivial`.

Equivalently (contrapositive): a compact set whose every preconnected subset is a subsingleton
(Mathlib's `IsTotallyDisconnected`) has preconnected complement; see
`Submission/Work/Smooth/JordanSeparation/isPreconnected_compl_of_totallyDisconnected.lean`.

## The argument

Fix `p, q ∉ F` and suppose `q` is not in the connected component of `p` in `Fᶜ`.  We show that
`F` contains a non-degenerate continuum.

* **Zorn.**  By Zorn's lemma (`zorn_superset_nonempty`) applied to the family
  `sepFamily F p q` of compact `L ⊆ F` whose complement still separates `p` from `q`, there is a
  *minimal* such `L`.  The chain condition is where local path-connectedness of `ℂ` enters: if
  `p` and `q` were in one component of `(⋂₀ 𝓒)ᶜ` they would be joined there by a *path* (that
  component is open, hence path connected), the path has compact image, and by Cantor's
  intersection theorem for the directed family `(range γ ∩ L)_{L ∈ 𝓒}` (all these are nonempty
  compact, decreasing along the chain) some `L ∈ 𝓒` already misses the image of the path, so
  `p, q` would be in one component of `Lᶜ` — contradiction.

* **Minimality forces `L` preconnected.**  If not, `L` is the union of two disjoint nonempty
  compact pieces `A = u ∩ L`, `B = v ∩ L`.  Minimality (applied to the proper subsets `A`, `B`)
  gives that `q` is in a component of `p` both in `Aᶜ` and in `Bᶜ`; Janiszewski's theorem
  (`Work.Smooth.JordanSeparation.janiszewski_disjoint`) then puts `q` in the same component of
  `(A ∪ B)ᶜ = Lᶜ` as `p`, contradicting the separating property of `L`.

* **Conclusion.**  A preconnected subset of `F` is a subsingleton, so `L = ∅` or `L = {x}`;
  in both cases `Lᶜ` is preconnected (`isPreconnected_compl_singleton_complex`), so `p` and `q`
  are in one component of `Lᶜ`, again contradicting the separating property.  Hence no such `L`
  exists, i.e. `q ∈ connectedComponentIn Fᶜ p`; as `p, q` were arbitrary, `Fᶜ` is preconnected.

## Legacy material

The file also contains (unused by the argument above) the theory of convex bodies used by an
earlier approach to the same theorem: the frontier of a convex body with nonempty interior in the
plane is a circle, hence preconnected (`isPreconnected_frontier_of_convex`), and removing the
interior of a convex body from a preconnected set keeps it preconnected
(`isPreconnected_diff_interior_of_convex`).
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The complement of one point of the plane is preconnected -/

/-- The complement of one point of the plane is preconnected: it is the image of the preconnected
set `(0,∞) × S¹` under the polar-coordinate map `(r, u) ↦ x + r • u`. -/
theorem isPreconnected_compl_singleton_complex (x : ℂ) : IsPreconnected ({x}ᶜ : Set ℂ) := by
  have hr : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hprod : IsPreconnected ((Set.Ioi (0:ℝ)) ×ˢ (Metric.sphere (0:ℂ) 1)) :=
    isPreconnected_Ioi.prod (isPreconnected_sphere hr 0 1)
  have hcont : Continuous (fun q : ℝ × ℂ => x + q.1 • q.2) := by fun_prop
  have himg := hprod.image _ hcont.continuousOn
  have heq : (fun q : ℝ × ℂ => x + q.1 • q.2) '' ((Set.Ioi (0:ℝ)) ×ˢ (Metric.sphere (0:ℂ) 1))
      = {x}ᶜ := by
    ext y
    constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have hru : r • u = 0 := by
        have h2 : x + r • u - x = 0 := by rw [h]; ring
        simpa using h2
      rcases smul_eq_zero.mp hru with h3 | h3
      · exact absurd h3 (ne_of_gt hr)
      · rw [Metric.mem_sphere, dist_zero_right] at hu
        rw [h3] at hu
        norm_num at hu
    · intro hy
      rw [mem_compl_iff, mem_singleton_iff] at hy
      have hne : x ≠ y := fun h => hy h.symm
      have hpos : (0:ℝ) < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
      refine ⟨(‖y - x‖, (‖y - x‖)⁻¹ • (y - x)), ⟨?_, ?_⟩, ?_⟩
      · exact hpos
      · rw [Metric.mem_sphere, dist_zero_right]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
        exact inv_mul_cancel₀ (ne_of_gt hpos)
      · show x + ‖y - x‖ • ((‖y - x‖)⁻¹ • (y - x)) = y
        have h1 : ‖y - x‖ * (‖y - x‖)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
        rw [smul_smul, h1, one_smul]
        ring
  rwa [heq] at himg

/-! ## Compact sets whose complement keeps `p` and `q` apart -/

/-- `sepFamily F p q` is the family of compact subsets `L ⊆ F` whose complement still keeps `p`
and `q` in different connected components, i.e. `q ∉ connectedComponentIn Lᶜ p`.  It is the
partially ordered set on which Zorn's lemma is applied below. -/
def sepFamily (F : Set ℂ) (p q : ℂ) : Set (Set ℂ) :=
  {L | L ⊆ F ∧ IsCompact L ∧ q ∉ connectedComponentIn Lᶜ p}

/-! ## The frontier of a convex body is preconnected -/

/-- The frontier of a convex set with nonempty interior in the plane is preconnected: it is
homeomorphic to the unit circle. -/
theorem isPreconnected_frontier_of_convex {C : Set ℂ} (hC : Convex ℝ C)
    (hint : (interior C).Nonempty) (hb : Bornology.IsBounded C) :
    IsPreconnected (frontier C) := by
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hC hint hb
  have hr : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) := isPreconnected_sphere hr 0 1
  rw [← h.isInducing.isPreconnected_image, hfr]
  exact hsphere

/-! ## Removing the interior of a convex body -/

/-- Auxiliary step: `frontier C` cannot lie entirely in `u` when `u`, `v` is a two-open-set cover
of `W \ interior C` which is disjoint on it. -/
private lemma frontier_not_subset_of_cover {W C u v : Set ℂ} (hWp : IsPreconnected W)
    (hCk : IsCompact C) (hu : IsOpen u) (hv : IsOpen v)
    (hsub : W \ interior C ⊆ u ∪ v)
    (hsu : ((W \ interior C) ∩ u).Nonempty) (hsv : ((W \ interior C) ∩ v).Nonempty)
    (hdisj : ((W \ interior C) ∩ (u ∩ v)).Nonempty → False)
    (hfru : frontier C ⊆ u) : False := by
  have hA : IsOpen (u ∪ interior C) := hu.union isOpen_interior
  have hB : IsOpen (v \ C) := hv.sdiff hCk.isClosed
  have hcover : W ⊆ (u ∪ interior C) ∪ (v \ C) := by
    intro x hx
    by_cases hxu : x ∈ u
    · exact Or.inl (Or.inl hxu)
    · by_cases hxi : x ∈ interior C
      · exact Or.inl (Or.inr hxi)
      · have hxs : x ∈ W \ interior C := ⟨hx, hxi⟩
        rcases hsub hxs with h | h
        · exact absurd h hxu
        · exact Or.inr ⟨h, fun hxC => hxu (hfru (hCk.isClosed.frontier_eq ▸ ⟨hxC, hxi⟩))⟩
  have hinter : ∀ x ∈ W, x ∈ (u ∪ interior C) ∩ (v \ C) → False := by
    rintro x hxW ⟨hxu | hxi, hxv, hxC⟩
    · exact hdisj ⟨x, ⟨⟨hxW, fun h => hxC (interior_subset h)⟩, hxu, hxv⟩⟩
    · exact hxC (interior_subset hxi)
  have hAne : (W ∩ (u ∪ interior C)).Nonempty := by
    obtain ⟨z, hz⟩ := hsu
    exact ⟨z, hz.1.1, Or.inl hz.2⟩
  have hBne : (W ∩ (v \ C)).Nonempty := by
    obtain ⟨z, hz⟩ := hsv
    refine ⟨z, hz.1.1, hz.2, ?_⟩
    intro hzC
    rcases hsub hz.1 with h | h
    · exact hdisj ⟨z, ⟨hz.1, h, hz.2⟩⟩
    · exact hdisj ⟨z, ⟨hz.1, hfru (hCk.isClosed.frontier_eq ▸ ⟨hzC, hz.1.2⟩), hz.2⟩⟩
  haveI : PreconnectedSpace ↥W := isPreconnected_iff_preconnectedSpace.mp hWp
  have hcompl : (Subtype.val ⁻¹' (u ∪ interior C) : Set ↥W)ᶜ = Subtype.val ⁻¹' (v \ C) := by
    ext x
    constructor
    · intro hx
      rcases hcover x.2 with h | h
      · exact absurd h hx
      · exact h
    · intro hx hxA
      exact hinter x.1 x.2 ⟨hxA, hx⟩
  have hcl : IsClopen (Subtype.val ⁻¹' (u ∪ interior C) : Set ↥W) := by
    refine ⟨isOpen_compl_iff.mp ?_, hA.preimage continuous_subtype_val⟩
    rw [hcompl]
    exact hB.preimage continuous_subtype_val
  rcases isClopen_iff.mp hcl with h0 | h1
  · obtain ⟨z, hzW, hzA⟩ := hAne
    have : (⟨z, hzW⟩ : ↥W) ∈ Subtype.val ⁻¹' (u ∪ interior C) := hzA
    rw [h0] at this
    exact this
  · obtain ⟨z, hzW, hzB⟩ := hBne
    have hzA : (⟨z, hzW⟩ : ↥W) ∈ Subtype.val ⁻¹' (u ∪ interior C) := by rw [h1]; trivial
    exact hinter z hzW ⟨hzA, hzB⟩

/-- **Removal lemma.**  If `W` is a preconnected subset of `ℂ` and `C ⊆ W` is a compact convex set
with nonempty interior, then `W \ interior C` is preconnected. -/
theorem isPreconnected_diff_interior_of_convex {W C : Set ℂ}
    (hWp : IsPreconnected W) (hCW : C ⊆ W) (hCc : Convex ℝ C)
    (hint : (interior C).Nonempty) (hCk : IsCompact C) :
    IsPreconnected (W \ interior C) := by
  have hfr : IsPreconnected (frontier C) :=
    isPreconnected_frontier_of_convex hCc hint hCk.isBounded
  have hfr_sub : frontier C ⊆ W \ interior C := by
    intro x hx
    refine ⟨hCW (hCk.isClosed.frontier_subset hx), ?_⟩
    intro hxi
    rw [frontier_eq_closure_inter_closure] at hx
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hxi
    obtain ⟨y, hyc, hyε⟩ := Metric.mem_closure_iff.mp hx.2 (ε / 2) (by linarith)
    have hyball : y ∈ ball x ε := by
      have : dist y x < ε := by rw [dist_comm]; linarith
      simpa [Metric.mem_ball] using this
    exact hyc (interior_subset (hεsub hyball))
  intro u v hu hv huv hsu hsv
  by_cases hgood : ((W \ interior C) ∩ (u ∩ v)).Nonempty
  · exact hgood
  · haveI : PreconnectedSpace ↥(frontier C) := isPreconnected_iff_preconnectedSpace.mp hfr
    have hcov : (univ : Set ↥(frontier C)) ⊆ Subtype.val ⁻¹' u ∪ Subtype.val ⁻¹' v := by
      intro x _
      rcases huv (hfr_sub x.2) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hdisj' : Disjoint (Subtype.val ⁻¹' u : Set ↥(frontier C)) (Subtype.val ⁻¹' v) := by
      rw [Set.disjoint_left]
      intro x hxu hxv
      exact hgood ⟨x.1, hfr_sub x.2, hxu, hxv⟩
    rcases isPreconnected_univ.subset_or_subset (hu.preimage continuous_subtype_val)
      (hv.preimage continuous_subtype_val) hdisj' hcov with hle | hle
    · exact (frontier_not_subset_of_cover hWp hCk hu hv huv hsu hsv hgood
        (fun x hx => hle (Set.mem_univ ⟨x, hx⟩))).elim
    · exact (frontier_not_subset_of_cover hWp hCk hv hu
        (fun x hx => (Set.union_comm u v ▸ huv hx)) hsv hsu
        (fun ⟨x, hx, hvx, hux⟩ => hgood ⟨x, hx, hux, hvx⟩)
        (fun x hx => hle (Set.mem_univ ⟨x, hx⟩))).elim

/-! ## Removing the interiors of finitely many convex bodies -/

/-- The complement of the interiors of finitely many compact convex bodies with pairwise disjoint
interiors is preconnected. -/
theorem isPreconnected_compl_iUnion_interior {m : ℕ} (C : Fin m → Set ℂ)
    (hck : ∀ i, IsCompact (C i)) (hcc : ∀ i, Convex ℝ (C i))
    (hci : ∀ i, (interior (C i)).Nonempty)
    (hd : ∀ i j, i ≠ j → C i ∩ interior (C j) = ∅) :
    IsPreconnected (Set.univ \ ⋃ i, interior (C i)) := by
  have key : ∀ s : Finset (Fin m),
      (∀ i ∈ s, IsCompact (C i)) → (∀ i ∈ s, Convex ℝ (C i)) →
      (∀ i ∈ s, (interior (C i)).Nonempty) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → C i ∩ interior (C j) = ∅) →
      IsPreconnected (Set.univ \ ⋃ i ∈ (s : Set (Fin m)), interior (C i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ _ _ _
      simpa using (isPreconnected_univ : IsPreconnected (Set.univ : Set ℂ))
    | insert a t ha ih =>
      intro h1 h2 h3 h4
      rw [Finset.coe_insert, Set.biUnion_insert]
      have hWp : IsPreconnected (Set.univ \ ⋃ i ∈ (t : Set (Fin m)), interior (C i)) :=
        ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h2 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h3 i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj hij => h4 i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj) hij)
      have hCaW : C a ⊆ Set.univ \ ⋃ i ∈ (t : Set (Fin m)), interior (C i) := by
        intro x hx
        refine ⟨trivial, ?_⟩
        intro hmem
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hmem
        have hempty : C a ∩ interior (C i) = ∅ :=
          h4 a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
            (fun h => ha (h ▸ hi))
        have : x ∈ (∅ : Set ℂ) := by
          rw [← hempty]
          exact ⟨hx, hxi⟩
        exact this
      have hstep := isPreconnected_diff_interior_of_convex hWp hCaW
        (h2 a (Finset.mem_insert_self a t)) (h3 a (Finset.mem_insert_self a t))
        (h1 a (Finset.mem_insert_self a t))
      have heq : (Set.univ : Set ℂ) \ (interior (C a) ∪ ⋃ i ∈ (t : Set (Fin m)), interior (C i))
          = (Set.univ \ ⋃ i ∈ (t : Set (Fin m)), interior (C i)) \ interior (C a) := by
        ext x
        simp only [mem_diff, mem_univ, true_and, mem_union, mem_iUnion, not_or, not_exists]
        tauto
      rw [heq]
      exact hstep
  have := key Finset.univ (fun i _ => hck i) (fun i _ => hcc i) (fun i _ => hci i)
    (fun i _ j _ hij => hd i j hij)
  rwa [Finset.coe_univ, Set.biUnion_univ] at this

/-! ## The main theorem -/

/-- **A compact plane set with disconnected complement contains a continuum** (Sierpiński).

If `F ⊆ ℂ` is compact and `Fᶜ` is not preconnected, then `F` contains a preconnected set with more
than one point. -/
theorem continuum_of_compl_not_preconnected {F : Set ℂ} (hF : IsCompact F)
    (h : ¬ IsPreconnected Fᶜ) :
    ∃ C : Set ℂ, C ⊆ F ∧ IsPreconnected C ∧ C.Nontrivial := by
  by_contra hcon
  push_neg at hcon
  have htd : IsTotallyDisconnected F := fun t ht hpre => hcon t ht hpre
  apply h
  have hkey : ∀ p ∈ Fᶜ, ∀ q ∈ Fᶜ, q ∈ connectedComponentIn Fᶜ p := by
    intro p hp q hq
    by_contra hpq
    have hFmem : F ∈ sepFamily F p q := ⟨Subset.rfl, hF, hpq⟩
    have chainCond : ∀ c ⊆ sepFamily F p q, IsChain (· ⊆ ·) c → c.Nonempty →
        ∃ lb ∈ sepFamily F p q, ∀ s ∈ c, lb ⊆ s := by
      intro c hc hchain hcne
      obtain ⟨t₀, ht₀⟩ := hcne
      have hclosed : IsClosed (⋂₀ c) :=
        isClosed_sInter fun t ht => (hc ht).2.1.isClosed
      refine ⟨⋂₀ c, ⟨(sInter_subset_of_mem ht₀).trans (hc ht₀).1,
        IsCompact.of_isClosed_subset (hc ht₀).2.1 hclosed (sInter_subset_of_mem ht₀), ?_⟩,
        fun s hs => sInter_subset_of_mem hs⟩
      intro hconI
      have hopen : IsOpen (connectedComponentIn ((⋂₀ c)ᶜ) p) :=
        hclosed.isOpen_compl.connectedComponentIn
      have hpI : p ∈ (⋂₀ c)ᶜ := by
        rw [mem_compl_iff]
        intro hpmem
        exact hp ((hc ht₀).1 (sInter_subset_of_mem ht₀ hpmem))
      have hpath : IsPathConnected (connectedComponentIn ((⋂₀ c)ᶜ) p) :=
        hopen.isConnected_iff_isPathConnected.mp
          (isConnected_connectedComponentIn_iff.mpr hpI)
      obtain ⟨γ, hγ⟩ := hpath.joinedIn p (mem_connectedComponentIn hpI) q hconI
      have hγc : IsCompact (Set.range (⇑γ)) := isCompact_range (f := ⇑γ) γ.continuous
      have hγrange : Set.range (⇑γ) ⊆ connectedComponentIn ((⋂₀ c)ᶜ) p :=
        Set.range_subset_iff.mpr hγ
      have hdisj : Set.range (⇑γ) ∩ (⋂₀ c) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxr, hxI⟩
        have hxγ : x ∈ connectedComponentIn ((⋂₀ c)ᶜ) p := hγrange hxr
        exact connectedComponentIn_subset ((⋂₀ c)ᶜ) p hxγ hxI
      obtain ⟨s, hs, hse⟩ : ∃ s ∈ c, Set.range (⇑γ) ∩ s = ∅ := by
        by_contra H
        push_neg at H
        haveI : Nonempty c := Set.Nonempty.to_subtype ⟨t₀, ht₀⟩
        have hdir : Directed (· ⊇ ·) (fun i : c => Set.range (⇑γ) ∩ (i : Set ℂ)) := by
          intro i j
          by_cases hij : (i : Set ℂ) ⊆ (j : Set ℂ)
          · exact ⟨i, Subset.rfl, inter_subset_inter Subset.rfl hij⟩
          · have hne : (i : Set ℂ) ≠ (j : Set ℂ) := fun h => hij (le_of_eq h)
            rcases hchain i.2 j.2 hne with h | h
            · exact absurd h hij
            · exact ⟨j, inter_subset_inter Subset.rfl h, Subset.rfl⟩
        have hnei : ∀ i : c, (Set.range (⇑γ) ∩ (i : Set ℂ)).Nonempty :=
          fun i => H _ i.2
        have hcompi : ∀ i : c, IsCompact (Set.range (⇑γ) ∩ (i : Set ℂ)) :=
          fun i => hγc.inter (hc i.2).2.1
        obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          (fun i : c => Set.range (⇑γ) ∩ (i : Set ℂ)) hdir hnei hcompi
          (fun i => (hcompi i).isClosed)
        have hxr : x ∈ Set.range (⇑γ) := (mem_iInter.mp hx ⟨t₀, ht₀⟩).1
        have hxI : x ∈ ⋂₀ c := by
          rw [mem_sInter]
          intro t ht
          exact (mem_iInter.mp hx ⟨t, ht⟩).2
        have hmem : x ∈ Set.range (⇑γ) ∩ (⋂₀ c) := ⟨hxr, hxI⟩
        rw [hdisj] at hmem
        exact hmem
      have hgs : Set.range (⇑γ) ⊆ (sᶜ : Set ℂ) := by
        intro x hxr
        rw [mem_compl_iff]
        intro hxs
        have hmem : x ∈ Set.range (⇑γ) ∩ s := ⟨hxr, hxs⟩
        rw [hse] at hmem
        exact hmem
      have hps : p ∈ Set.range (⇑γ) := Path.source_mem_range γ
      have hqs : q ∈ Set.range (⇑γ) := Path.target_mem_range γ
      have hsub' : Set.range (⇑γ) ⊆ connectedComponentIn (sᶜ) p :=
        (isPreconnected_range (f := ⇑γ) γ.continuous).subset_connectedComponentIn hps hgs
      exact (hc hs).2.2 (hsub' hqs)
    obtain ⟨L, hLF, hLmin⟩ := zorn_superset_nonempty (sepFamily F p q) chainCond F hFmem
    have hLcomp : IsCompact L := hLmin.1.2.1
    have hLsep : q ∉ connectedComponentIn Lᶜ p := hLmin.1.2.2
    have hLpre : IsPreconnected L := by
      rw [isPreconnected_iff_subset_of_fully_disjoint_closed hLcomp.isClosed]
      intro u v hu hv hLuv huv
      by_contra hcon2
      push_neg at hcon2
      obtain ⟨hLu, hLv⟩ := hcon2
      have hAcomp : IsCompact (u ∩ L) :=
        hLcomp.of_isClosed_subset (hu.inter hLcomp.isClosed) inter_subset_right
      have hBcomp : IsCompact (v ∩ L) :=
        hLcomp.of_isClosed_subset (hv.inter hLcomp.isClosed) inter_subset_right
      have hAsep : q ∈ connectedComponentIn (u ∩ L)ᶜ p := by
        by_contra hAs
        have hmem : u ∩ L ∈ sepFamily F p q := ⟨inter_subset_right.trans hLF, hAcomp, hAs⟩
        exact hLu ((hLmin.2 hmem inter_subset_right).trans inter_subset_left)
      have hBsep : q ∈ connectedComponentIn (v ∩ L)ᶜ p := by
        by_contra hBs
        have hmem : v ∩ L ∈ sepFamily F p q := ⟨inter_subset_right.trans hLF, hBcomp, hBs⟩
        exact hLv ((hLmin.2 hmem inter_subset_right).trans inter_subset_left)
      have hpd : Disjoint (u ∩ L) (v ∩ L) := by
        rw [Set.disjoint_left]
        rintro x ⟨hxu, -⟩ ⟨hxv, -⟩
        exact Set.disjoint_left.mp huv hxu hxv
      have hunion : (u ∩ L) ∪ (v ∩ L) = L := by
        refine Subset.antisymm (union_subset inter_subset_right inter_subset_right) ?_
        intro x hx
        rcases hLuv hx with h | h
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr ⟨h, hx⟩
      have hpL : p ∉ (u ∩ L) ∪ (v ∩ L) := by
        rintro (⟨-, hxL⟩ | ⟨-, hxL⟩)
        · exact hp (hLF hxL)
        · exact hp (hLF hxL)
      have hqL : q ∉ (u ∩ L) ∪ (v ∩ L) := by
        rintro (⟨-, hxL⟩ | ⟨-, hxL⟩)
        · exact hq (hLF hxL)
        · exact hq (hLF hxL)
      have hjan := janiszewski_disjoint hAcomp hBcomp hpd hpL hqL hAsep hBsep
      rw [hunion] at hjan
      exact hLsep hjan
    have hLsub : L.Subsingleton := htd L hLF hLpre
    rcases hLsub.eq_empty_or_singleton with hL0 | ⟨x, hLx⟩
    · rw [hL0, compl_empty] at hLsep
      exact hLsep (isPreconnected_univ.subset_connectedComponentIn (mem_univ p)
        (subset_univ _) (mem_univ q))
    · rw [hLx] at hLsep
      have hxL : x ∈ L := by rw [hLx]; exact mem_singleton x
      have hxE : x ∈ F := hLF hxL
      have hpx : p ∈ ({x}ᶜ : Set ℂ) := by
        rw [mem_compl_iff, mem_singleton_iff]
        exact fun hh => hp (hh ▸ hxE)
      have hqx : q ∈ ({x}ᶜ : Set ℂ) := by
        rw [mem_compl_iff, mem_singleton_iff]
        exact fun hh => hq (hh ▸ hxE)
      exact hLsep ((isPreconnected_compl_singleton_complex x).subset_connectedComponentIn
        hpx subset_rfl hqx)
  rcases Fᶜ.eq_empty_or_nonempty with hem | ⟨p, hp⟩
  · rw [hem]; exact isPreconnected_empty
  · have hEq : Fᶜ = connectedComponentIn Fᶜ p :=
      Subset.antisymm (fun q hq => hkey p hp q hq) (connectedComponentIn_subset Fᶜ p)
    rw [hEq]
    exact isPreconnected_connectedComponentIn

end

end Work.Smooth.JordanSeparation
