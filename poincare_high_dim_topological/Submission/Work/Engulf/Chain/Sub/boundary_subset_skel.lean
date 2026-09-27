import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.Sub.Basic
import Submission.Work.PL.Subdiv.Simplex.sum_smul_mem_convexHull_compl_iff
import Submission.Work.PL.Subdiv.Simplex.sum_smul_unique

/-!
# `Submission.Work.Engulf.Chain.Sub.boundary_subset_skel`

`Work.Engulf.Chain.Sub.boundary_subset_skel`: in a subdivision `Γ₁` of `Γ`, the boundary
`⋃_{w ∈ Δ} simp (Δ.erase w)` of a face `Δ ∈ Γ.faces` is covered by the boundaries
`⋃_{w ∈ s} simp (s.erase w)` of any list `ord` of same-dimensional faces `s ∈ Γ₁.faces`
with `simp s ⊆ simp Δ` whose simplices cover `simp Δ`.

The geometric content is the following.  Let `p ∈ simp (Δ.erase w) ⊆ simp Δ` and let
`s ∈ Γ₁.faces` with `simp s ⊆ simp Δ`, `s.card = Δ.card`, `p ∈ simp s`.  Writing `p` as a
convex combination of the vertices of `s`, if every coefficient is nonzero then for each
vertex `x` of `s` its barycentric coordinates with respect to the affinely independent set
`Δ` (which exist because `x ∈ simp Δ`) have vanishing `w`-coordinate: composing the
barycentric coordinates of `s` with those of `Δ` produces, by uniqueness of barycentric
coordinates, the coordinates of `p` in `Δ`, whose `w`-coordinate is `0` since
`p ∈ simp (Δ.erase w)`.  Thus every vertex of `s` lies in `simp (Δ.erase w)`, so — `s`
being affinely independent with `s.card = Δ.card` and `Δ.erase w` having one vertex less —
`AffineIndependent.card_le_card_of_subset_affineSpan` gives a contradiction.  Hence some
coefficient of the representation of `p` over `s` vanishes, i.e. `p ∈ simp (s.erase v)` for
some `v ∈ s`.
-/

namespace Work.Engulf.Chain.Sub


variable {N : ℕ}

/-- The vertices of `s` other than `i`, seen as a subset of the ambient space, form the
`Finset` `s.erase i`. -/
theorem val_image_compl_eq_erase (s : Finset (PL.E N)) (i : ↥s) :
    (Subtype.val '' ({i}ᶜ : Set ↥s)) = ((s.erase (i : PL.E N) : Finset (PL.E N)) : Set (PL.E N)) := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_coe, Finset.mem_erase]
    exact ⟨fun h => hj (Subtype.ext h), j.2⟩
  · intro hx
    rw [Finset.mem_coe, Finset.mem_erase] at hx
    exact ⟨⟨x, hx.2⟩, fun h => hx.1 (Subtype.ext_iff.mp h), rfl⟩

/-- Every point of `simp Δ` is a convex combination of the vertices of `Δ`. -/
theorem exists_weights_of_mem_simp {Δ : Finset (PL.E N)} {x : PL.E N} (hx : x ∈ PL.simp Δ) :
    ∃ c : ↥Δ → ℝ, (∀ j, 0 ≤ c j) ∧ (∑ j, c j = 1) ∧ ∑ j, c j • (j : PL.E N) = x := by
  have hx' : x ∈ Work.PL.Generic.hullOf (Subtype.val : ↥Δ → PL.E N) (Finset.univ : Finset ↥Δ) := by
    show x ∈ convexHull ℝ (Subtype.val '' ((Finset.univ : Finset ↥Δ) : Set ↥Δ))
    rw [Finset.coe_univ, Set.image_univ, Subtype.range_coe]
    exact hx
  obtain ⟨c, hc0, hc1, hc2⟩ :=
    (Work.PL.Generic.mem_hullOf (Subtype.val : ↥Δ → PL.E N) (Finset.univ : Finset ↥Δ) x).mp hx'
  exact ⟨c, fun j => hc0 j (Finset.mem_univ j), by simpa using hc1, by simpa using hc2⟩

/-- If a convex combination of the vertices of `s` has a vanishing coefficient at `i ∈ s`,
the point already lies in the simplex on the remaining vertices of `s`. -/
theorem mem_simp_erase_of_weight_zero {s : Finset (PL.E N)} {p : PL.E N} {a : ↥s → ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∑ j, a j = 1) (hap : ∑ j, a j • (j : PL.E N) = p)
    (i : ↥s) (hai : a i = 0) : p ∈ PL.simp (s.erase (i : PL.E N)) := by
  have hset : PL.simp (s.erase (i : PL.E N)) = convexHull ℝ (Subtype.val '' ({i}ᶜ : Set ↥s)) := by
    show convexHull ℝ (((s.erase (i : PL.E N) : Finset (PL.E N))) : Set (PL.E N)) = _
    rw [val_image_compl_eq_erase s i]
  rw [hset, ← hap]
  exact
    (Work.PL.Subdiv.Simplex.mem_convexHull_compl_iff_exists_weights (Subtype.val : ↥s → PL.E N) i
      (∑ j, a j • (j : PL.E N))).mpr ⟨a, ha0, hai, ha1, rfl⟩

/-- A point of a facet `simp (Δ.erase w)` of the face `Δ` which is covered by a
same-dimensional face `s` inside `Δ` lies on a facet `simp (s.erase v)` of `s`. -/
theorem exists_v_erase_mem {Δ s : Finset (PL.E N)} {w p : PL.E N}
    (hΔi : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    (hsi : AffineIndependent ℝ ((↑) : s → PL.E N))
    (hcard : s.card = Δ.card) (hw : w ∈ Δ) (hsub : PL.simp s ⊆ PL.simp Δ)
    (hpΔ : p ∈ PL.simp (Δ.erase w)) (hps : p ∈ PL.simp s) :
    ∃ v ∈ s, p ∈ PL.simp (s.erase v) := by
  classical
  obtain ⟨a, ha0, ha1, hap⟩ := exists_weights_of_mem_simp hps
  by_contra hcon
  -- All barycentric coefficients of `p` with respect to `s` are nonzero.
  have hne : ∀ i : ↥s, a i ≠ 0 := by
    intro i hai
    exact hcon ⟨i.1, i.2, mem_simp_erase_of_weight_zero ha0 ha1 hap i hai⟩
  have hlt : ∀ i : ↥s, 0 < a i := fun i => lt_of_le_of_ne (ha0 i) (Ne.symm (hne i))
  -- Barycentric coordinates of each vertex of `s` inside `Δ`.
  have hrep : ∀ i : ↥s, ∃ c : ↥Δ → ℝ, (∀ j, 0 ≤ c j) ∧ (∑ j, c j = 1) ∧
      ∑ j, c j • (j : PL.E N) = (i : PL.E N) :=
    fun i => exists_weights_of_mem_simp (hsub (Work.Engulf.subset_simp i.2))
  choose c hc0 hc1 hci using hrep
  -- Barycentric coordinates of `p` inside `Δ`, normalised with `w`-coefficient `0`.
  have hpΔ' : p ∈ convexHull ℝ (Subtype.val '' ({⟨w, hw⟩}ᶜ : Set ↥Δ)) := by
    rw [val_image_compl_eq_erase Δ ⟨w, hw⟩]
    exact hpΔ
  obtain ⟨b, hb0, hbw, hb1, hbp⟩ :=
    (Work.PL.Subdiv.Simplex.mem_convexHull_compl_iff_exists_weights (Subtype.val : ↥Δ → PL.E N)
      ⟨w, hw⟩ p).mp hpΔ'
  -- Composed coordinates: the coordinates of `p` in `Δ` obtained by going through `s`.
  set B : ↥Δ → ℝ := fun j => ∑ i : ↥s, a i * c i j with hB
  have hB1 : ∑ j : ↥Δ, B j = 1 := by
    calc ∑ j : ↥Δ, B j = ∑ j : ↥Δ, ∑ i : ↥s, a i * c i j := by rw [hB]
      _ = ∑ i : ↥s, ∑ j : ↥Δ, a i * c i j := Finset.sum_comm
      _ = ∑ i : ↥s, a i := Finset.sum_congr rfl (fun i _ => by rw [← Finset.mul_sum, hc1 i, mul_one])
      _ = 1 := ha1
  have hBp : ∑ j : ↥Δ, B j • (j : PL.E N) = p := by
    calc ∑ j : ↥Δ, B j • (j : PL.E N)
        = ∑ j : ↥Δ, (∑ i : ↥s, a i * c i j) • (j : PL.E N) := by rw [hB]
      _ = ∑ j : ↥Δ, ∑ i : ↥s, (a i * c i j) • (j : PL.E N) :=
            Finset.sum_congr rfl (fun j _ => Finset.sum_smul)
      _ = ∑ i : ↥s, ∑ j : ↥Δ, (a i * c i j) • (j : PL.E N) := Finset.sum_comm
      _ = ∑ i : ↥s, a i • (i : PL.E N) := Finset.sum_congr rfl (fun i _ => by
            rw [show (∑ j : ↥Δ, (a i * c i j) • (j : PL.E N))
                  = ∑ j : ↥Δ, a i • (c i j • (j : PL.E N)) from
                Finset.sum_congr rfl (fun j _ => by rw [mul_smul])]
            rw [← Finset.smul_sum, hci i])
      _ = p := hap
  have hBb : B = b := Work.PL.Subdiv.Simplex.sum_smul_unique hΔi hB1 hb1 (by rw [hBp, hbp])
  -- The `w`-coordinate of every vertex of `s` vanishes.
  have hcw : ∀ i : ↥s, c i ⟨w, hw⟩ = 0 := by
    intro i
    have hz : ∑ i' : ↥s, a i' * c i' ⟨w, hw⟩ = 0 := by
      have h1 : B ⟨w, hw⟩ = ∑ i' : ↥s, a i' * c i' ⟨w, hw⟩ := by rw [hB]
      rw [← h1, hBb, hbw]
    have hnn : ∀ j ∈ (Finset.univ : Finset ↥s), 0 ≤ a j * c j ⟨w, hw⟩ :=
      fun j _ => mul_nonneg (le_of_lt (hlt j)) (hc0 j ⟨w, hw⟩)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz i (Finset.mem_univ i)
    exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hlt i))
  -- Hence every vertex of `s` lies in `simp (Δ.erase w)`.
  have hmem : ∀ i : ↥s, (i : PL.E N) ∈ PL.simp (Δ.erase w) := by
    intro i
    have h' : (i : PL.E N) ∈ convexHull ℝ (Subtype.val '' ({⟨w, hw⟩}ᶜ : Set ↥Δ)) :=
      (Work.PL.Subdiv.Simplex.mem_convexHull_compl_iff_exists_weights (Subtype.val : ↥Δ → PL.E N)
        ⟨w, hw⟩ (i : PL.E N)).mpr ⟨c i, hc0 i, hcw i, hc1 i, hci i⟩
    rwa [val_image_compl_eq_erase Δ ⟨w, hw⟩] at h'
  -- Cardinality contradiction.
  have hsub_aff : ((s : Set (PL.E N))) ⊆
      (affineSpan ℝ (((Δ.erase w : Finset (PL.E N))) : Set (PL.E N)) : Set (PL.E N)) := by
    intro x hx
    exact PL.simp_subset_affineSpan (Δ.erase w) (hmem ⟨x, hx⟩)
  have hle : s.card ≤ (Δ.erase w).card :=
    AffineIndependent.card_le_card_of_subset_affineSpan hsi hsub_aff
  rw [Finset.card_erase_of_mem hw, ← hcard] at hle
  have hcpos : 0 < s.card := by rw [hcard]; exact Finset.card_pos.mpr ⟨w, hw⟩
  omega

theorem boundary_subset_skel {N : ℕ} {Γ Γ₁ : PL.Cx N} (hsub : PL.Subdivides Γ₁ Γ)
    {Δ : Finset (PL.E N)} (hΔ : Δ ∈ Γ.faces) {ord : List (Finset (PL.E N))}
    (hcard : ∀ s ∈ ord, s ∈ Γ₁.faces ∧ s.card = Δ.card ∧ PL.simp s ⊆ PL.simp Δ)
    (hcov : (⋃ s ∈ ord, PL.simp s) = PL.simp Δ) :
    (⋃ w ∈ Δ, PL.simp (Δ.erase w))
      ⊆ ⋃ s ∈ ord, ⋃ w ∈ s, PL.simp (s.erase w) := by
  have _ : PL.Subdivides Γ₁ Γ := hsub
  intro p hp
  rw [Set.mem_iUnion₂] at hp
  obtain ⟨w, hw, hpw⟩ := hp
  have hpΔ : p ∈ PL.simp Δ := PL.simp_mono (Finset.erase_subset w Δ) hpw
  have hcovp : p ∈ ⋃ s ∈ ord, PL.simp s := by rw [hcov]; exact hpΔ
  rw [Set.mem_iUnion₂] at hcovp
  obtain ⟨s, hsord, hps⟩ := hcovp
  obtain ⟨hsface, hscard, hssub⟩ := hcard s hsord
  obtain ⟨v, hvs, hpv⟩ :=
    exists_v_erase_mem (Γ.indep hΔ) (Γ₁.indep hsface) hscard hw hssub hpw hps
  refine Set.mem_iUnion₂.mpr ⟨s, hsord, ?_⟩
  exact Set.mem_iUnion₂.mpr ⟨v, hvs, hpv⟩

end Work.Engulf.Chain.Sub
