import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.CellBoundaryJordan.GridCycleDefs

/-!
# Auxiliary facts about the polygonal curve of a cyclic grid walk

This module collects the elementary geometry of unit grid segments (`adjSeg`, `hSeg`, `vSeg`) and
the elementary analysis of the parametrisation `gridCurve` that are used by
`exists_injective_circle_map_of_grid_cycle`:

* `adjSeg_east`, `adjSeg_west`, `adjSeg_north`, `adjSeg_south`: the four descriptions of a unit
  grid segment (`adjSeg u (u ± e)` is `hSeg`/`vSeg` of the appropriate corner);
* `eq_lpt_of_mem_adjSeg`: the lattice points of a unit grid segment are its two endpoints;
* `adjSeg_eq_of_mem_of_not_lattice`: two unit grid segments sharing a point which is not a lattice
  point coincide;
* `vertex_eq_iff`: for a `k`-periodic grid cycle with pairwise distinct vertices, two vertices with
  indices in `[0,k]` coincide exactly when the indices agree up to the identification `0 = k`;
* `continuousOn_gridCurve`: `gridCurve u k` is continuous on `[0,1]`;
* `range_gridCurve_eq`: the range of `gridCurve u k` on `[0,1]` is the union of the edges.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The four descriptions of a unit grid segment -/

lemma lpt_add_east (u : ℤ × ℤ) : lpt (u.1 + 1, u.2) = lpt u + 1 := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_add_west (u : ℤ × ℤ) : lpt (u.1 - 1, u.2) = lpt u - 1 := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_add_north (u : ℤ × ℤ) : lpt (u.1, u.2 + 1) = lpt u + Complex.I := by
  apply Complex.ext <;> simp [lpt]

lemma lpt_add_south (u : ℤ × ℤ) : lpt (u.1, u.2 - 1) = lpt u - Complex.I := by
  apply Complex.ext <;> simp [lpt]

lemma lineMap_east (u : ℤ × ℤ) (t : ℝ) :
    AffineMap.lineMap (lpt u) (lpt (u.1 + 1, u.2)) t = lpt u + (t : ℂ) := by
  rw [lpt_add_east, AffineMap.lineMap_apply_module]
  apply Complex.ext <;> simp [lpt] <;> ring

lemma lineMap_north (u : ℤ × ℤ) (t : ℝ) :
    AffineMap.lineMap (lpt u) (lpt (u.1, u.2 + 1)) t = lpt u + (t : ℂ) * Complex.I := by
  rw [lpt_add_north, AffineMap.lineMap_apply_module]
  apply Complex.ext <;> simp [lpt] <;> ring

lemma adjSeg_east (u : ℤ × ℤ) : adjSeg u (u.1 + 1, u.2) = hSeg u := by
  ext z
  rw [adjSeg, segment_eq_image_lineMap, hSeg]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [lineMap_east]
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpt] <;> linarith [ht.1, ht.2]
  · rintro ⟨him, h1, h2⟩
    refine ⟨z.re - (u.1 : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    rw [lineMap_east]
    apply Complex.ext <;> simp [lpt, him] <;> ring

lemma adjSeg_north (u : ℤ × ℤ) : adjSeg u (u.1, u.2 + 1) = vSeg u := by
  ext z
  rw [adjSeg, segment_eq_image_lineMap, vSeg]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [lineMap_north]
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpt] <;> linarith [ht.1, ht.2]
  · rintro ⟨hre, h1, h2⟩
    refine ⟨z.im - (u.2 : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    rw [lineMap_north]
    apply Complex.ext <;> simp [lpt, hre] <;> ring

lemma adjSeg_west (u : ℤ × ℤ) : adjSeg u (u.1 - 1, u.2) = hSeg (u.1 - 1, u.2) := by
  have hsymm : adjSeg u (u.1 - 1, u.2) = adjSeg (u.1 - 1, u.2) u := by
    simp only [adjSeg, segment_symm]
  rw [hsymm]
  have h2 := adjSeg_east (u.1 - 1, u.2)
  convert h2 using 2
  simp

lemma adjSeg_south (u : ℤ × ℤ) : adjSeg u (u.1, u.2 - 1) = vSeg (u.1, u.2 - 1) := by
  have hsymm : adjSeg u (u.1, u.2 - 1) = adjSeg (u.1, u.2 - 1) u := by
    simp only [adjSeg, segment_symm]
  rw [hsymm]
  have h2 := adjSeg_north (u.1, u.2 - 1)
  convert h2 using 2
  simp

/-! ## Lattice points of a unit grid segment -/

lemma eq_lpt_of_mem_hSeg {p r : ℤ × ℤ} {z : ℂ} (hz : z ∈ hSeg p) (hzp : z = lpt r) :
    r = p ∨ r = (p.1 + 1, p.2) := by
  subst hzp
  obtain ⟨h1, h2, h3⟩ := hz
  have hi : r.2 = p.2 := by
    have : (r.2 : ℝ) = (p.2 : ℝ) := by simpa [lpt] using h1
    exact_mod_cast this
  have h2' : p.1 ≤ r.1 := by
    have : (p.1 : ℝ) ≤ (r.1 : ℝ) := by simpa [lpt] using h2
    exact_mod_cast this
  have h3' : r.1 ≤ p.1 + 1 := by
    have : (r.1 : ℝ) ≤ (p.1 : ℝ) + 1 := by simpa [lpt] using h3
    exact_mod_cast this
  rcases eq_or_lt_of_le h2' with h | h
  · exact Or.inl (Prod.ext h.symm hi)
  · exact Or.inr (Prod.ext (by omega) hi)

lemma eq_lpt_of_mem_vSeg {p r : ℤ × ℤ} {z : ℂ} (hz : z ∈ vSeg p) (hzp : z = lpt r) :
    r = p ∨ r = (p.1, p.2 + 1) := by
  subst hzp
  obtain ⟨h1, h2, h3⟩ := hz
  have hi : r.1 = p.1 := by
    have : (r.1 : ℝ) = (p.1 : ℝ) := by simpa [lpt] using h1
    exact_mod_cast this
  have h2' : p.2 ≤ r.2 := by
    have : (p.2 : ℝ) ≤ (r.2 : ℝ) := by simpa [lpt] using h2
    exact_mod_cast this
  have h3' : r.2 ≤ p.2 + 1 := by
    have : (r.2 : ℝ) ≤ (p.2 : ℝ) + 1 := by simpa [lpt] using h3
    exact_mod_cast this
  rcases eq_or_lt_of_le h2' with h | h
  · exact Or.inl (Prod.ext hi h.symm)
  · exact Or.inr (Prod.ext hi (by omega))

/-- Two horizontal unit grid segments sharing a non-lattice point coincide. -/
lemma hSeg_eq_of_mem_of_not_lattice {p q : ℤ × ℤ} {z : ℂ} (hz1 : z ∈ hSeg p)
    (hz2 : z ∈ hSeg q) (hz : ∀ r : ℤ × ℤ, z ≠ lpt r) : hSeg p = hSeg q := by
  obtain ⟨him1, h11, h12⟩ := hz1
  obtain ⟨him2, h21, h22⟩ := hz2
  have hpq2 : p.2 = q.2 := by
    have : (p.2 : ℝ) = (q.2 : ℝ) := by linarith [him1, him2]
    exact_mod_cast this
  have hpq1 : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · exfalso
      have hq : (p.1 : ℝ) + 1 ≤ (q.1 : ℝ) := by
        exact_mod_cast (show p.1 + 1 ≤ q.1 by omega)
      have hzre : z.re = (p.1 : ℝ) + 1 := le_antisymm h12 (le_trans (le_trans hq h21) le_rfl)
      have hzeq : z = lpt (p.1 + 1, p.2) := by
        apply Complex.ext
        · simpa [lpt] using hzre
        · simpa [lpt] using him1
      exact hz _ hzeq
    · exact heq
    · exfalso
      have hq : (q.1 : ℝ) + 1 ≤ (p.1 : ℝ) := by
        exact_mod_cast (show q.1 + 1 ≤ p.1 by omega)
      have hzre : z.re = (q.1 : ℝ) + 1 := le_antisymm h22 (le_trans (le_trans hq h11) le_rfl)
      have hzeq : z = lpt (q.1 + 1, q.2) := by
        apply Complex.ext
        · simpa [lpt] using hzre
        · simpa [lpt] using him2
      exact hz _ hzeq
  rw [Prod.ext hpq1 hpq2]

/-- Two vertical unit grid segments sharing a non-lattice point coincide. -/
lemma vSeg_eq_of_mem_of_not_lattice {p q : ℤ × ℤ} {z : ℂ} (hz1 : z ∈ vSeg p)
    (hz2 : z ∈ vSeg q) (hz : ∀ r : ℤ × ℤ, z ≠ lpt r) : vSeg p = vSeg q := by
  obtain ⟨hre1, h11, h12⟩ := hz1
  obtain ⟨hre2, h21, h22⟩ := hz2
  have hpq1 : p.1 = q.1 := by
    have : (p.1 : ℝ) = (q.1 : ℝ) := by linarith [hre1, hre2]
    exact_mod_cast this
  have hpq2 : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
    · exfalso
      have hq : (p.2 : ℝ) + 1 ≤ (q.2 : ℝ) := by
        exact_mod_cast (show p.2 + 1 ≤ q.2 by omega)
      have hzim : z.im = (p.2 : ℝ) + 1 := le_antisymm h12 (le_trans (le_trans hq h21) le_rfl)
      have hzeq : z = lpt (p.1, p.2 + 1) := by
        apply Complex.ext
        · simpa [lpt] using hre1
        · simpa [lpt] using hzim
      exact hz _ hzeq
    · exact heq
    · exfalso
      have hq : (q.2 : ℝ) + 1 ≤ (p.2 : ℝ) := by
        exact_mod_cast (show q.2 + 1 ≤ p.2 by omega)
      have hzim : z.im = (q.2 : ℝ) + 1 := le_antisymm h22 (le_trans (le_trans hq h11) le_rfl)
      have hzeq : z = lpt (q.1, q.2 + 1) := by
        apply Complex.ext
        · simpa [lpt] using hre2
        · simpa [lpt] using hzim
      exact hz _ hzeq
  rw [Prod.ext hpq1 hpq2]

/-- A point common to a horizontal and a vertical unit grid segment is a lattice point. -/
lemma isLattice_of_mem_hSeg_vSeg {p q : ℤ × ℤ} {z : ℂ} (hz1 : z ∈ hSeg p)
    (hz2 : z ∈ vSeg q) : ∃ r : ℤ × ℤ, z = lpt r := by
  obtain ⟨him, -, -⟩ := hz1
  obtain ⟨hre, -, -⟩ := hz2
  refine ⟨(q.1, p.2), ?_⟩
  apply Complex.ext
  · simpa [lpt] using hre
  · simpa [lpt] using him

/-! ## The lattice points of a unit grid segment are its endpoints -/

theorem eq_lpt_of_mem_adjSeg {a b p : ℤ × ℤ} {z : ℂ} (hab : IsUnitAdj a b)
    (hz : z ∈ adjSeg a b) (hzp : z = lpt p) : p = a ∨ p = b := by
  rcases hab with h | h | h | h
  · rw [h, adjSeg_east] at hz
    rcases eq_lpt_of_mem_hSeg hz hzp with h1 | h1
    · left; exact h1
    · right; rw [h, h1]
  · rw [h, adjSeg_west] at hz
    rcases eq_lpt_of_mem_hSeg hz hzp with h1 | h1
    · right; rw [h, h1]
    · left; rw [h1]; simp
  · rw [h, adjSeg_north] at hz
    rcases eq_lpt_of_mem_vSeg hz hzp with h1 | h1
    · left; exact h1
    · right; rw [h, h1]
  · rw [h, adjSeg_south] at hz
    rcases eq_lpt_of_mem_vSeg hz hzp with h1 | h1
    · right; rw [h, h1]
    · left; rw [h1]; simp

/-- Two unit grid segments which share a point that is not a lattice point coincide. -/
theorem adjSeg_eq_of_mem_of_not_lattice {a b c d : ℤ × ℤ} {z : ℂ}
    (hab : IsUnitAdj a b) (hcd : IsUnitAdj c d)
    (hz1 : z ∈ adjSeg a b) (hz2 : z ∈ adjSeg c d)
    (hz : ∀ p : ℤ × ℤ, z ≠ lpt p) : adjSeg a b = adjSeg c d := by
  rcases hab with hb | hb | hb | hb <;> rcases hcd with hd | hd | hd | hd <;>
    rw [hb] at hz1 ⊢ <;> rw [hd] at hz2 ⊢ <;>
    simp only [adjSeg_east, adjSeg_west, adjSeg_north, adjSeg_south] at hz1 hz2 ⊢
  · exact hSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · exact hSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz1 hz2
    exact absurd hr (hz r)
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz1 hz2
    exact absurd hr (hz r)
  · exact hSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · exact hSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz1 hz2
    exact absurd hr (hz r)
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz1 hz2
    exact absurd hr (hz r)
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz2 hz1
    exact absurd hr (hz r)
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz2 hz1
    exact absurd hr (hz r)
  · exact vSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · exact vSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz2 hz1
    exact absurd hr (hz r)
  · obtain ⟨r, hr⟩ := isLattice_of_mem_hSeg_vSeg hz2 hz1
    exact absurd hr (hz r)
  · exact vSeg_eq_of_mem_of_not_lattice hz1 hz2 hz
  · exact vSeg_eq_of_mem_of_not_lattice hz1 hz2 hz

/-! ## Vertices of a periodic grid cycle -/

theorem vertex_eq_iff {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j) {α β : ℕ}
    (hα : α ≤ k) (hβ : β ≤ k) :
    u α = u β ↔ α = β ∨ (α = 0 ∧ β = k) ∨ (α = k ∧ β = 0) := by
  have huk : u k = u 0 := by simpa using hper 0
  constructor
  · intro h
    rcases eq_or_lt_of_le hα with hαk | hαk
    · rcases eq_or_lt_of_le hβ with hβk | hβk
      · exact Or.inl (by omega)
      · have h0 : u 0 = u β := by
          have h' := h
          rw [hαk, huk] at h'
          exact h'
        exact Or.inr (Or.inr ⟨hαk, (hinj 0 β hk hβk h0).symm⟩)
    · rcases eq_or_lt_of_le hβ with hβk | hβk
      · have h0 : u α = u 0 := by
          have h' := h
          rw [hβk, huk] at h'
          exact h'
        exact Or.inr (Or.inl ⟨(hinj α 0 hαk hk h0), hβk⟩)
      · exact Or.inl (hinj α β hαk hβk h)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [huk]
    · rw [huk]

/-! ## Continuity of the parametrisation -/

theorem continuousOn_gridCurve {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℤ × ℤ) :
    ContinuousOn (gridCurve u k) (Set.Icc (0 : ℝ) 1) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpiece : ∀ i < k, ContinuousOn (gridCurve u k)
      (Set.Icc ((i : ℝ) / k) (((i + 1 : ℕ) : ℝ) / k)) := by
    intro i hi
    have hcont : Continuous fun t : ℝ =>
        AffineMap.lineMap (lpt (u i)) (lpt (u (i + 1))) (t * (k : ℝ) - (i : ℝ)) := by
      fun_prop
    refine hcont.continuousOn.congr ?_
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    have hτ0 : 0 ≤ t * (k : ℝ) - (i : ℝ) := by
      have h1' : (i : ℝ) ≤ t * (k : ℝ) := by
        rw [div_le_iff₀ hk0] at h1
        exact h1
      linarith
    have hτ1 : t * (k : ℝ) - (i : ℝ) ≤ 1 := by
      have h2' : t * (k : ℝ) ≤ (i : ℝ) + 1 := by
        rw [le_div_iff₀ hk0] at h2
        push_cast at h2
        exact h2
      linarith
    exact gridCurve_eq_of_mul_eq (hk := hk) (u := u) (i := i) hi (τ := t * (k : ℝ) - (i : ℝ))
      (t := t) hτ0 hτ1 (by ring)
  have key : ∀ m ≤ k, ContinuousOn (gridCurve u k) (Set.Icc (0 : ℝ) ((m : ℝ) / k)) := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [Nat.cast_zero, zero_div]
        simpa using continuousOn_singleton (gridCurve u k) (0 : ℝ)
    | succ m ih =>
        intro hm
        have hm' : m ≤ k := by omega
        have hmk : m < k := by omega
        have hmono : (m : ℝ) / k ≤ (((m + 1 : ℕ)) : ℝ) / k := by
          have hle : (m : ℝ) ≤ (((m + 1 : ℕ)) : ℝ) := by push_cast; linarith
          exact div_le_div_of_nonneg_right hle (le_of_lt hk0)
        have h0m : (0 : ℝ) ≤ (m : ℝ) / k := by positivity
        have hunion : Set.Icc (0 : ℝ) (((m + 1 : ℕ) : ℝ) / k) =
            Set.Icc 0 ((m : ℝ) / k) ∪ Set.Icc ((m : ℝ) / k) (((m + 1 : ℕ) : ℝ) / k) := by
          ext x
          simp only [Set.mem_Icc, Set.mem_union]
          constructor
          · intro hx
            by_cases h : x ≤ (m : ℝ) / k
            · exact Or.inl ⟨hx.1, h⟩
            · exact Or.inr ⟨le_of_lt (lt_of_not_ge h), hx.2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, le_trans h2 hmono⟩
            · exact ⟨le_trans h0m h1, h2⟩
        rw [hunion]
        exact (ih hm').union_of_isClosed (hpiece m hmk) isClosed_Icc isClosed_Icc
  have hkr : ((k : ℕ) : ℝ) / k = 1 := by rw [div_self (by positivity)]
  have := key k le_rfl
  rwa [hkr] at this

/-! ## The range of the parametrisation -/

theorem range_gridCurve_eq {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℤ × ℤ) :
    Set.range (fun t : unitInterval => gridCurve u k (t : ℝ))
      = ⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine mem_iUnion₂.mpr ⟨cIdx k (t : ℝ), ?_, ?_⟩
    · simpa using cIdx_lt hk (t : ℝ)
    · exact gridCurve_mem_adjSeg hk t.2.1 t.2.2
  · intro hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
    have hi' : i < k := hi
    rw [adjSeg, segment_eq_image_lineMap] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    have ht1 : ((i : ℝ) + τ) / k ≤ 1 := by
      rw [div_le_one hk0]
      have : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (show i + 1 ≤ k by omega)
      linarith [hτ.2]
    have ht0 : 0 ≤ ((i : ℝ) + τ) / k := by
      have : (0 : ℝ) ≤ (i : ℝ) + τ := by
        linarith [hτ.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
      exact div_nonneg this (le_of_lt hk0)
    refine ⟨⟨((i : ℝ) + τ) / k, ht0, ht1⟩, ?_⟩
    have htk : (((i : ℝ) + τ) / k) * (k : ℝ) = (i : ℝ) + τ := by
      field_simp
    exact gridCurve_eq_of_mul_eq (hk := hk) (u := u) (i := i) hi' (τ := τ)
      (t := ((i : ℝ) + τ) / k) hτ.1 hτ.2 htk

end

end Work.HornSC.CellBoundaryJordan
