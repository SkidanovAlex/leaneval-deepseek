import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent

set_option maxHeartbeats 1000000

namespace Work.Engulf.E4Aux

open Set Finset

/-- **Weights of a point in the convex hull of a finite vertex set.**  A point of
`convexHull ℝ ↑S` is a convex combination of the vertices in `S`, i.e. there are nonnegative
weights `wt` on `S`, summing to one, with `∑ y ∈ S, wt y • y = x`. -/
lemma exists_weights_of_mem_convexHull {N : ℕ} {S : Finset (PL.E N)} {x : PL.E N}
    (hx : x ∈ convexHull ℝ (↑S)) :
    ∃ wt : PL.E N → ℝ, (∀ y ∈ S, 0 ≤ wt y) ∧ (∑ y ∈ S, wt y = 1) ∧
      (∑ y ∈ S, wt y • y = x) := by
  rw [Finset.convexHull_eq] at hx
  obtain ⟨wt, h0, h1, hcm⟩ := hx
  exact ⟨wt, h0, h1, by rw [← hcm, Finset.centerMass_eq_of_sum_1 S id h1]; simp⟩

/-- The range of the vertex-coercion of a finset subtype is the finset itself. -/
lemma range_subtype_val_coe {N : ℕ} (S : Finset (PL.E N)) :
    Set.range (fun v : ↥S => (v : PL.E N)) = (↑S : Set (PL.E N)) := by
  ext v
  constructor
  · rintro ⟨vv, rfl⟩; exact vv.2
  · intro hv; exact ⟨⟨v, hv⟩, rfl⟩

/-- **A convex combination of a finite vertex set lies in its convex hull.** -/
lemma mem_convexHull_of_weights {N : ℕ} {S : Finset (PL.E N)} {wt : PL.E N → ℝ}
    (h0 : ∀ y ∈ S, 0 ≤ wt y) (h1 : ∑ y ∈ S, wt y = 1) :
    (∑ y ∈ S, wt y • y) ∈ convexHull ℝ (↑S) := by
  rw [Finset.convexHull_eq]
  refine ⟨wt, h0, h1, ?_⟩
  rw [Finset.centerMass_eq_of_sum_1 S id h1]; simp

/-- **A facet of a simplex is covered by the facets of any full-dimensional cover of the simplex.**  If `ord` is a finite family of full-dimensional (`t.card = s.card`) simplices of the same dimension as `simp s`, each contained in `simp s`, whose union is `simp s`, then for every vertex `w ∈ s` the facet `simp (s.erase w)` is contained in the union of the facets `simp (t.erase w')`, `w' ∈ t`, of the members of `ord`.  (Geometrically: a point of the facet of `s` is not in the relative interior of `s`, hence not in the relative interior of the full-dimensional simplex `t` containing it, hence lies in one of the facets of `t`.) -/
theorem facets_cover_frontier {N : ℕ} {s : Finset (PL.E N)} (ord : List (Finset (PL.E N)))
    (hne : s.Nonempty) (hind : AffineIndependent ℝ (fun v : ↥s => (v : PL.E N)))
    (hfin : ∀ t ∈ ord, AffineIndependent ℝ (fun v : ↥t => (v : PL.E N)))
    (hsub : ∀ t ∈ ord, PL.simp t ⊆ PL.simp s)
    (hcard : ∀ t ∈ ord, t.card = s.card)
    (hcover : PL.simp s ⊆ ⋃ t ∈ ord, PL.simp t)
    (w : PL.E N) (hw : w ∈ s) :
    PL.simp (s.erase w) ⊆ ⋃ t ∈ ord, ⋃ w' ∈ t, PL.simp (t.erase w') := by
  classical
  intro x hx
  -- `x` lies in the simplex on `s`.
  have hxs : x ∈ PL.simp s :=
    convexHull_mono (𝕜 := ℝ) (fun y hy => Finset.mem_of_mem_erase hy) hx
  -- pick a member `t` of the cover containing `x`
  obtain ⟨t, htord, hxt⟩ := Set.mem_iUnion₂.1 (hcover hxs)
  -- a side fact: vertices of `t` lie in `PL.simp t`
  have hmemt : ∀ u ∈ t, u ∈ PL.simp t := by
    intro u hu
    rw [PL.simp]
    exact subset_convexHull ℝ (t : Set (PL.E N)) (by simpa using hu)
  -- it suffices to find a facet of `t` containing `x`
  suffices ∃ w' ∈ t, x ∈ PL.simp (t.erase w') by
    obtain ⟨w', hw't, hxw'⟩ := this
    exact Set.mem_iUnion₂.2 ⟨t, htord, Set.mem_iUnion₂.2 ⟨w', hw't, hxw'⟩⟩
  by_contra hcon
  push_neg at hcon
  -- # weights of `x` on `t`: all strictly positive
  obtain ⟨lam, hlam0, hlam1, hlamsum⟩ := exists_weights_of_mem_convexHull hxt
  have hlampos : ∀ y ∈ t, 0 < lam y := by
    intro y hy
    rcases lt_or_eq_of_le (hlam0 y hy) with h | h
    · exact h
    · exfalso
      have hl : lam y = 0 := h.symm
      have hsum_erase : ∑ z ∈ t.erase y, lam z = 1 := by
        have hstep := Finset.sum_erase_add t lam hy
        rw [hlam1, hl, add_zero] at hstep
        exact hstep
      have hvec : ∑ z ∈ t.erase y, lam z • z = x := by
        have hstep := Finset.sum_erase_add t (fun z => lam z • z) hy
        rw [hlamsum, hl, zero_smul, add_zero] at hstep
        exact hstep
      exact hcon y hy (by
        rw [PL.simp, ← hvec]
        exact mem_convexHull_of_weights (fun z hz => hlam0 z (Finset.mem_of_mem_erase hz)) hsum_erase)
  -- # weights of `x` on the facet of `s`, extended by zero on `s`
  obtain ⟨mu0, hmu0, hmu1, hmusum⟩ := exists_weights_of_mem_convexHull hx
  set mu : PL.E N → ℝ := fun y => if y ∈ s.erase w then mu0 y else 0 with hmu
  have hmu_sum : ∑ y ∈ s, mu y = 1 := by
    have h2 : ∑ y ∈ s, mu y = ∑ y ∈ s.erase w, mu y :=
      (Finset.sum_subset (Finset.erase_subset w s)
        (fun y _ hynot => by simp only [hmu, if_neg hynot])).symm
    have h1 : ∑ y ∈ s.erase w, mu y = ∑ y ∈ s.erase w, mu0 y :=
      Finset.sum_congr rfl (fun y hy => by simp only [hmu, if_pos hy])
    rw [h2, h1, hmu1]
  have hmu_vec : ∑ y ∈ s, mu y • y = x := by
    have h2 : ∑ y ∈ s, mu y • y = ∑ y ∈ s.erase w, mu y • y :=
      (Finset.sum_subset (Finset.erase_subset w s)
        (fun y _ hynot => by simp only [hmu, if_neg hynot, zero_smul])).symm
    have h1 : ∑ y ∈ s.erase w, mu y • y = ∑ y ∈ s.erase w, mu0 y • y :=
      Finset.sum_congr rfl (fun y hy => by simp only [hmu, if_pos hy])
    rw [h2, h1, hmusum]
  have hmu_w : mu w = 0 := by
    have hw_not : w ∉ s.erase w := fun hmem => (Finset.mem_erase.mp hmem).1 rfl
    simp only [hmu, if_neg hw_not]
  -- # weights of each vertex `u` of `t` on `s`
  have hnu_ex : ∀ u ∈ t, ∃ nu_u : PL.E N → ℝ, (∀ y ∈ s, 0 ≤ nu_u y) ∧
      (∑ y ∈ s, nu_u y = 1) ∧ (∑ y ∈ s, nu_u y • y = u) := by
    intro u hu
    exact exists_weights_of_mem_convexHull (hsub t htord (hmemt u hu))
  let nu : PL.E N → PL.E N → ℝ :=
    fun u => dite (u ∈ t) (fun hu => Classical.choose (hnu_ex u hu)) (fun _ => 0)
  have hnu : ∀ u ∈ t, (∀ y ∈ s, 0 ≤ nu u y) ∧ (∑ y ∈ s, nu u y = 1) ∧
      (∑ y ∈ s, nu u y • y = u) := by
    intro u hu
    have hnuval : nu u = Classical.choose (hnu_ex u hu) := by
      simp only [nu, dif_pos hu]
    rw [hnuval]
    exact Classical.choose_spec (hnu_ex u hu)
  -- # combining: the weights of `x` on `s` and the combination of the `nu u`
  have hbeta_sum : ∑ y ∈ s, (∑ u ∈ t, lam u * nu u y) = 1 := by
    rw [Finset.sum_comm]
    have hcongr : ∀ u ∈ t, (∑ y ∈ s, lam u * nu u y) = lam u := by
      intro u hu
      rw [← Finset.mul_sum, (hnu u hu).2.1, mul_one]
    rw [Finset.sum_congr rfl hcongr, hlam1]
  have hbeta_vec : ∑ y ∈ s, (∑ u ∈ t, lam u * nu u y) • y = x := by
    calc ∑ y ∈ s, (∑ u ∈ t, lam u * nu u y) • y
        = ∑ y ∈ s, ∑ u ∈ t, (lam u * nu u y) • y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [Finset.sum_smul]
      _ = ∑ u ∈ t, ∑ y ∈ s, (lam u * nu u y) • y := Finset.sum_comm
      _ = ∑ u ∈ t, ∑ y ∈ s, lam u • (nu u y • y) := by
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [mul_smul]
      _ = ∑ u ∈ t, lam u • (∑ y ∈ s, nu u y • y) := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.smul_sum]
      _ = ∑ u ∈ t, lam u • u := by
          refine Finset.sum_congr rfl (fun u hu => ?_)
          rw [(hnu u hu).2.2]
      _ = x := hlamsum
  -- # uniqueness of the barycentric coordinates with respect to `s`
  have huniq : ∀ y ∈ s, mu y = ∑ u ∈ t, lam u * nu u y :=
    Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent (n := N) (ι := PL.E N)
      (y := fun z => z) (s := s) hind hmu_sum hbeta_sum (by rw [hmu_vec, hbeta_vec])
  -- # the `w`-coordinate of every vertex of `t` vanishes
  have hnu_w : ∀ u ∈ t, nu u w = 0 := by
    have h0 : ∑ u ∈ t, lam u * nu u w = 0 := by
      rw [← huniq w hw, hmu_w]
    have hnn : ∀ u ∈ t, 0 ≤ lam u * nu u w :=
      fun u hu => mul_nonneg (le_of_lt (hlampos u hu)) ((hnu u hu).1 w hw)
    intro u hu
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 u hu
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hlampos u hu))
  -- # the affine spans of `t` and `s` coincide
  have hle_aff : affineSpan ℝ (↑t : Set (PL.E N)) ≤ affineSpan ℝ (↑s : Set (PL.E N)) := by
    rw [affineSpan_le]
    intro y hy
    exact convexHull_subset_affineSpan (𝕜 := ℝ) (s := (↑s : Set (PL.E N)))
      (hsub t htord (hmemt y hy))
  have hs1 : 1 ≤ s.card := Finset.card_pos.mpr hne
  have ht1 : 1 ≤ t.card := by rw [hcard t htord]; exact hs1
  have hfr_s : Module.finrank ℝ (vectorSpan ℝ (↑s : Set (PL.E N))) = s.card - 1 := by
    have hc : Fintype.card ↥s = (s.card - 1) + 1 := by
      rw [Fintype.card_coe, Nat.sub_add_cancel hs1]
    have h := hind.finrank_vectorSpan (n := s.card - 1) hc
    rw [range_subtype_val_coe] at h
    exact h
  have hfr_t : Module.finrank ℝ (vectorSpan ℝ (↑t : Set (PL.E N))) = s.card - 1 := by
    have hc : Fintype.card ↥t = (t.card - 1) + 1 := by
      rw [Fintype.card_coe, Nat.sub_add_cancel ht1]
    have h := (hfin t htord).finrank_vectorSpan (n := t.card - 1) hc
    rw [range_subtype_val_coe] at h
    rw [h, hcard t htord]
  have hdir_eq : (affineSpan ℝ (↑t : Set (PL.E N))).direction
      = (affineSpan ℝ (↑s : Set (PL.E N))).direction := by
    rw [direction_affineSpan, direction_affineSpan]
    have hle_vs : vectorSpan ℝ (↑t : Set (PL.E N)) ≤ vectorSpan ℝ (↑s : Set (PL.E N)) := by
      rw [← direction_affineSpan, ← direction_affineSpan]
      exact AffineSubspace.direction_le hle_aff
    refine Submodule.eq_of_le_of_finrank_eq hle_vs ?_
    rw [hfr_s, hfr_t]
  have ht_ne : (↑t : Set (PL.E N)).Nonempty := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hcard t htord]; exact Finset.card_pos.mpr hne)
    exact ⟨u, by simpa using hu⟩
  have ht_ne_aff : ((affineSpan ℝ (↑t : Set (PL.E N))) : Set (PL.E N)).Nonempty := by
    obtain ⟨u, hu⟩ := ht_ne
    exact ⟨u, mem_affineSpan ℝ hu⟩
  have haff : affineSpan ℝ (↑t : Set (PL.E N)) = affineSpan ℝ (↑s : Set (PL.E N)) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq ht_ne_aff hle_aff
  have hw_at : w ∈ affineSpan ℝ (↑t : Set (PL.E N)) := by
    rw [haff]
    exact mem_affineSpan ℝ (by simpa using hw)
  -- # `w` as an affine combination of the vertices of `t`
  obtain ⟨fs, alp, hfs_sub, halp_sum, halp_eq⟩ :=
    eq_affineCombination_of_mem_affineSpan_image (p := (id : PL.E N → PL.E N))
      (s := (↑t : Set (PL.E N))) (p₁ := w) (by rwa [Set.image_id])
  have hfs_t : fs ⊆ t := Finset.coe_subset.mp hfs_sub
  set alpha : PL.E N → ℝ := fun y => if y ∈ fs then alp y else 0 with halpha
  have halpha_sum : ∑ y ∈ t, alpha y = 1 := by
    have h2 : ∑ y ∈ t, alpha y = ∑ y ∈ fs, alpha y :=
      (Finset.sum_subset hfs_t
        (fun y _ hynot => by simp only [halpha, if_neg hynot])).symm
    have h1 : ∑ y ∈ fs, alpha y = ∑ y ∈ fs, alp y :=
      Finset.sum_congr rfl (fun y hy => by simp only [halpha, if_pos hy])
    rw [h2, h1, halp_sum]
  have halpha_vec : ∑ y ∈ t, alpha y • y = w := by
    have h2 : ∑ y ∈ t, alpha y • y = ∑ y ∈ fs, alpha y • y :=
      (Finset.sum_subset hfs_t
        (fun y _ hynot => by simp only [halpha, if_neg hynot, zero_smul])).symm
    have h1 : ∑ y ∈ fs, alpha y • y = ∑ y ∈ fs, alp y • y :=
      Finset.sum_congr rfl (fun y hy => by simp only [halpha, if_pos hy])
    have h3 : ∑ y ∈ fs, alp y • y = w := by
      rw [halp_eq, Finset.affineCombination_eq_linear_combination fs id alp halp_sum]
      simp
    rw [h2, h1, h3]
  -- # the two affine combinations of `s` giving `w`
  have hdelta_sum : ∑ y ∈ s, (if y = w then (1 : ℝ) else 0) = 1 := by
    have h := Finset.sum_eq_single (s := s) (f := fun y => if y = w then (1 : ℝ) else 0) w
      (fun b _ hbw => by simp [hbw]) (fun hws => absurd hw hws)
    simpa using h
  have hdelta_vec : ∑ y ∈ s, (if y = w then (1 : ℝ) else 0) • y = w := by
    have h := Finset.sum_eq_single (s := s)
      (f := fun y => (if y = w then (1 : ℝ) else 0) • y) w
      (fun b _ hbw => by simp [hbw]) (fun hws => absurd hw hws)
    simpa using h
  have hbeta2_sum : ∑ y ∈ s, (∑ u ∈ t, alpha u * nu u y) = 1 := by
    rw [Finset.sum_comm]
    have hcongr : ∀ u ∈ t, (∑ y ∈ s, alpha u * nu u y) = alpha u := by
      intro u hu
      rw [← Finset.mul_sum, (hnu u hu).2.1, mul_one]
    rw [Finset.sum_congr rfl hcongr, halpha_sum]
  have hbeta2_vec : ∑ y ∈ s, (∑ u ∈ t, alpha u * nu u y) • y = w := by
    calc ∑ y ∈ s, (∑ u ∈ t, alpha u * nu u y) • y
        = ∑ y ∈ s, ∑ u ∈ t, (alpha u * nu u y) • y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [Finset.sum_smul]
      _ = ∑ u ∈ t, ∑ y ∈ s, (alpha u * nu u y) • y := Finset.sum_comm
      _ = ∑ u ∈ t, ∑ y ∈ s, alpha u • (nu u y • y) := by
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [mul_smul]
      _ = ∑ u ∈ t, alpha u • (∑ y ∈ s, nu u y • y) := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [Finset.smul_sum]
      _ = ∑ u ∈ t, alpha u • u := by
          refine Finset.sum_congr rfl (fun u hu => ?_)
          rw [(hnu u hu).2.2]
      _ = w := halpha_vec
  have hdel := Work.PL.Generic.eq_of_sum_smul_eq_of_affineIndependent (n := N) (ι := PL.E N)
    (y := fun z => z) (s := s) hind hdelta_sum hbeta2_sum (by rw [hdelta_vec, hbeta2_vec])
  have hw_val : (if w = w then (1 : ℝ) else 0) = ∑ u ∈ t, alpha u * nu u w := hdel w hw
  have hzero : ∑ u ∈ t, alpha u * nu u w = 0 :=
    Finset.sum_eq_zero (fun u hu => by rw [hnu_w u hu, mul_zero])
  rw [hzero] at hw_val
  rw [if_pos rfl] at hw_val
  exact absurd hw_val (by norm_num)

end Work.Engulf.E4Aux
