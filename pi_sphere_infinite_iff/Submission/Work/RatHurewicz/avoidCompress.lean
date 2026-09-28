import Mathlib
import Submission.Work.RatHurewicz.Cofibre.path_compress_twoSet

/-!
# Compressing a path into an open set of a two-set cover

`Work.RatHurewicz.Cofibre.path_compress_twoSet` requires both sets of the cover to be open.  For the
push-off argument of `Work.RatHurewicz.modelAvoidOrigin` the set `U` is the complement of a point,
which is not known to be open as a subset of `Model D`; however, the *preimage* `p ⁻¹' U` along the
path being compressed is open (because limits are unique in `I`).  This module provides the same
compression with the openness hypothesis moved from `U` to `p ⁻¹' U`.

The proof is the subdivision part of `path_compress_twoSet` followed by the induction
`Work.RatHurewicz.Cofibre.pcAux_all`, which does not use the openness of `U` at all.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- If `p` is a path and `U` is a set whose pullback along `p` is open, then a two-set cover
`U ∪ V = univ` with `V` open, `U ∩ V` path connected and `V` simply connected in the path sense
allows one to compress `p` into `U`. -/
theorem path_compress_twoSet' {X : Type} [TopologicalSpace X] {U V : Set X}
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b))
    (hVsc : ∀ {x y : X} (p q : Path x y), (∀ t, p t ∈ V) → (∀ t, q t ∈ V) →
      Nonempty (Path.Homotopic p q))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (p : Path x y)
    (hpU : IsOpen (p ⁻¹' U)) :
    ∃ q : Path x y, (∀ t, q t ∈ U) ∧ Nonempty (Path.Homotopic p q) := by
  classical
  -- ### Step 1: the Lebesgue number of the pulled-back cover of `I`
  have hcopen : ∀ i : Bool, IsOpen (p ⁻¹' (cond i V U) : Set I) := by
    intro i
    cases i
    · exact hpU
    · exact hV.preimage p.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ i : Bool, (p ⁻¹' (cond i V U) : Set I) := by
    intro t _
    rcases (show p t ∈ U ∨ p t ∈ V from by
      have := Set.eq_univ_iff_forall.mp hcov (p t)
      simpa [Set.mem_union] using this) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set I)) isCompact_univ hcopen hcover
  obtain ⟨mn, hmn⟩ := exists_nat_one_div_lt hδpos
  -- ### Step 2: the uniform grid of mesh `1/N`
  let N : ℕ := mn + 1
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNd : (1 : ℝ) / N < δ := by
    have hcast : ((mn : ℝ) + 1) = (N : ℝ) := by simp [N]
    rw [← hcast]; exact hmn
  let g : ℕ → ℝ := fun k => (k : ℝ) / N
  have hg0 : g 0 = 0 := by simp [g]
  have hgN : g N = 1 := by
    show (N : ℝ) / N = 1
    field_simp
  have hmono : ∀ k < N, g k < g (k + 1) := by
    intro k hk
    show (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N
    have h2 : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact div_lt_div_of_pos_right h2 hNR
  -- ### Step 3: classify each leg
  let mid : ∀ k : ℕ, k < N → I := fun k hk => ⟨((k : ℝ) + 1 / 2) / N, by
    have hk1 : k + 1 ≤ N := by omega
    have h1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1
    constructor
    · exact div_nonneg (by positivity) (le_of_lt hNR)
    · rw [div_le_one hNR]; linarith⟩
  let b : ℕ → Bool := fun k =>
    if hk : k < N then Classical.choose (hδ (mid k hk) (Set.mem_univ _)) else false
  have hleg : ∀ k < N, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) →
      p.extend t ∈ cond (b k) V U := by
    intro k hk t ht1 ht2
    have hspec := Classical.choose_spec (hδ (mid k hk) (Set.mem_univ _))
    have hk1 : k + 1 ≤ N := by omega
    have hc1 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hc2 : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
      rw [div_le_one hNR]
      exact_mod_cast hk1
    have htI : t ∈ I :=
      ⟨le_trans (by simpa [g] using hc1) ht1, le_trans ht2 (by simpa [g] using hc2)⟩
    have hball : (⟨t, htI⟩ : I) ∈ Metric.ball (mid k hk) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have hm1 : (k : ℝ) ≤ N * t := by
        have h1 : (k : ℝ) / N ≤ t := ht1
        rw [div_le_iff₀ hNR] at h1
        linarith
      have hm2 : N * t ≤ (k : ℝ) + 1 := by
        have h2 : t ≤ ((k + 1 : ℕ) : ℝ) / N := ht2
        rw [le_div_iff₀ hNR] at h2
        push_cast at h2
        linarith
      have hkey : |N * t - (k : ℝ) - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have heq : t - ((k : ℝ) + 1 / 2) / N = (N * t - (k : ℝ) - 1 / 2) / N := by
        field_simp
        ring
      have hlt : (1 : ℝ) / (2 * N) < δ := by
        have hh : (1 : ℝ) / (2 * N) = (1 / 2) / N := by field_simp
        have hle : (1 : ℝ) / (2 * N) < 1 / N := by
          rw [hh, div_lt_div_iff_of_pos_right hNR]; norm_num
        linarith
      have hkey' : |N * t - (k : ℝ) - 1 / 2| / N ≤ (1 / 2) / N :=
        div_le_div_of_nonneg_right hkey (le_of_lt hNR)
      have hhalf2 : (1 / 2) / N = (1 : ℝ) / (2 * N) := by field_simp
      rw [heq, abs_div, abs_of_pos hNR]
      linarith
    have hmem : p ⟨t, htI⟩ ∈ cond (Classical.choose (hδ (mid k hk) (Set.mem_univ _))) V U :=
      hspec hball
    simpa [b, dif_pos hk, Path.extend_apply p htI] using hmem
  -- ### Step 4: apply the compression induction
  have h0g : p.extend (g 0) ∈ U := by rw [hg0, p.extend_zero]; exact hx
  have hNg : p.extend (g N) ∈ U := by rw [hgN, p.extend_one]; exact hy
  obtain ⟨q, hqU, hqHom⟩ := Cofibre.pcAux_all hUV hVsc N p.extend g hmono b hleg h0g hNg
  have hxg : x = p.extend (g 0) := by rw [hg0, p.extend_zero]
  have hyg : y = p.extend (g N) := by rw [hgN, p.extend_one]
  refine ⟨q.cast hxg hyg, ?_, ?_⟩
  · intro s
    rw [Path.cast_coe]
    exact hqU s
  · obtain ⟨hqh⟩ := hqHom
    have hseg : (Cofibre.pcSeg p.extend (g 0) (g N)).cast hxg hyg = p := by
      ext s
      rw [Path.cast_coe]
      change p.extend (g 0 + (g N - g 0) * (s : ℝ)) = p s
      rw [hg0, hgN]
      simp only [zero_add, sub_zero, one_mul]
      exact (p.extend_apply s.2).trans (congrArg p (Subtype.ext rfl))
    have h2 := Path.Homotopic.pathCast hqh hxg hyg
    rw [hseg] at h2
    exact ⟨h2.symm⟩

end

end Work.RatHurewicz
