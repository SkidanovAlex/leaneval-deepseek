import Mathlib
import Submission.Work.Smooth.JordanSeparation.isCompact_convexHull_of_isCompact
import Submission.Work.BoxShrink.Pinch.good_of_small_cell_decomposition

/-!
# `Work.BoxShrink.Pinch.small_cell_decomposition_of_selfSimilar`

A compact attractor `K ⊆ ℂ` of a self-similar system `z ↦ λ i * z + c i` (`0 < λ i < 1`) whose
level-one cells `f i '' K` have pairwise disjoint convex hulls admits, for every `δ > 0`, a finite
cover by pairwise disjoint compact convex cells of diameter `< δ`.

The proof is the standard "level-`n` cells" argument.  Let `q = max i, λ i < 1` and
`D = diam (convexHull ℝ K)`.  By induction on `n` there is a finite family `s n` of pairwise
disjoint compact convex sets, each contained in `convexHull ℝ K` and of diameter
`≤ q ^ n * D`, covering `K`:

* level `0` is the single cell `convexHull ℝ K` (compact since `K` is compact);
* level `n + 1` consists of the images `f i '' C` of the level-`n` cells.
  * Two cells with different first digit `i ≠ j` are disjoint because they are contained in the
    disjoint level-one cells `f i '' convexHull ℝ K`, `f j '' convexHull ℝ K`;
  * two cells with the same digit have disjoint images because `f i` is injective;
  * the diameter shrinks by the factor `λ i ≤ q`, using
    `diam (f i '' C) ≤ λ i * diam C`;
  * `f i '' convexHull ℝ K ⊆ convexHull ℝ K` because the affine image of a convex hull is the
    convex hull of the image, and `f i '' K ⊆ K` by self-similarity, so each new cell stays in
    `convexHull ℝ K` and the refinement covers `K = ⋃ i, f i '' K`.

Choosing `n` with `q ^ n * D < δ` and re-indexing the finset by `Fin s.card` gives the claim.
-/

namespace Work.BoxShrink.Pinch

open Set Metric

noncomputable section

/-- The affine identity behind every computation with `z ↦ r * z + c`:
a convex combination of two images is the image of the convex combination. -/
lemma smul_add_mul_eq (r : ℝ) (c u v : ℂ) {a b : ℝ} (hab : a + b = 1) :
    (r : ℂ) * (a • u + b • v) + c = a • ((r : ℂ) * u + c) + b • ((r : ℂ) * v + c) := by
  simp only [Complex.real_smul]
  have hb : (b : ℂ) = 1 - (a : ℂ) := by
    have h : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    linear_combination h
  rw [hb]
  ring

/-- The image of a convex set under `z ↦ r * z + c` is convex. -/
lemma convex_image_mul_add {S : Set ℂ} (hS : Convex ℝ S) (r : ℝ) (c : ℂ) :
    Convex ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨a • u + b • v, hS hu hv ha hb hab, ?_⟩
  exact smul_add_mul_eq r c u v hab

/-- The affine image of a convex hull is the convex hull of the image. -/
lemma image_convexHull_mul_add (S : Set ℂ) (r : ℝ) (c : ℂ) :
    (fun z : ℂ => (r : ℂ) * z + c) '' convexHull ℝ S
      = convexHull ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S) := by
  refine subset_antisymm ?_ ?_
  · have hconv : Convex ℝ {u : ℂ | (r : ℂ) * u + c ∈
        convexHull ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S)} := by
      intro u hu v hv a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hu hv ⊢
      rw [smul_add_mul_eq r c u v hab]
      exact (convex_convexHull ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S)) hu hv ha hb hab
    have hsub : S ⊆ {u : ℂ | (r : ℂ) * u + c ∈
        convexHull ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S)} := by
      intro z hz
      exact subset_convexHull ℝ ((fun z : ℂ => (r : ℂ) * z + c) '' S) ⟨z, hz, rfl⟩
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact convexHull_min hsub hconv hu
  · intro x hx
    exact convexHull_min (Set.image_mono (subset_convexHull ℝ S))
      (convex_image_mul_add (convex_convexHull ℝ S) r c) hx

/-- Distances along `z ↦ r * z + c` scale by the factor `r ≥ 0`. -/
lemma dist_mul_add_mul_add (r : ℝ) (hr : 0 ≤ r) (c u v : ℂ) :
    dist ((r : ℂ) * u + c) ((r : ℂ) * v + c) = r * dist u v := by
  rw [dist_eq_norm, dist_eq_norm]
  have h2 : (r : ℂ) * u + c - ((r : ℂ) * v + c) = r • (u - v) := by
    rw [Complex.real_smul]; ring
  rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, ← dist_eq_norm]

/-- The diameter of a bounded set is scaled by at most `r` under `z ↦ r * z + c`. -/
lemma diam_image_mul_add_le {S : Set ℂ} (hS : Bornology.IsBounded S) (r : ℝ) (hr : 0 ≤ r)
    (c : ℂ) : Metric.diam ((fun z : ℂ => (r : ℂ) * z + c) '' S) ≤ r * Metric.diam S := by
  refine Metric.diam_le_of_forall_dist_le (mul_nonneg hr Metric.diam_nonneg) ?_
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  rw [dist_mul_add_mul_add r hr c u v]
  exact mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hS hu hv) hr

/-- `z ↦ r * z + c` is injective for `r ≠ 0`. -/
lemma injective_mul_add {r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    Function.Injective (fun z : ℂ => (r : ℂ) * z + c) := by
  intro x y hxy
  have hr' : (r : ℂ) ≠ 0 := fun h0 => hr (Complex.ofReal_injective h0)
  have h : (r : ℂ) * (x - y) = 0 := by
    have := sub_eq_zero.mpr hxy
    rwa [show (r : ℂ) * x + c - ((r : ℂ) * y + c) = (r : ℂ) * (x - y) by ring] at this
  rcases mul_eq_zero.mp h with h3 | h3
  · exact absurd h3 hr'
  · exact sub_eq_zero.mp h3

theorem small_cell_decomposition_of_selfSimilar {K : Set ℂ} (hK : IsCompact K)
    {N : ℕ} (hN : 0 < N) {lam : Fin N → ℝ} (hlam : ∀ i, 0 < lam i ∧ lam i < 1) (c : Fin N → ℂ)
    (hfix : K = ⋃ i, (fun z : ℂ => (lam i : ℂ) * z + c i) '' K)
    (hdisj : ∀ i j, i ≠ j → Disjoint ((fun z : ℂ => (lam i : ℂ) * z + c i) '' convexHull ℝ K)
      ((fun z : ℂ => (lam j : ℂ) * z + c j) '' convexHull ℝ K)) :
    ∀ δ : ℝ, 0 < δ → ∃ (m : ℕ) (C : Fin m → Set ℂ),
      (∀ i, IsCompact (C i)) ∧ (∀ i, Convex ℝ (C i)) ∧ (∀ i, Metric.diam (C i) < δ) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧ K ⊆ ⋃ i, C i := by
  classical
  intro δ hδ
  let f : Fin N → ℂ → ℂ := fun i z => (lam i : ℂ) * z + c i
  -- the uniform contraction factor and the initial diameter
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N)) lam
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  set q : ℝ := lam i₀ with hq
  have hqpos : 0 < q := by rw [hq]; exact (hlam i₀).1
  have hqlt : q < 1 := by rw [hq]; exact (hlam i₀).2
  have hle : ∀ i, lam i ≤ q := by intro i; rw [hq]; exact hi₀ i (Finset.mem_univ i)
  set D : ℝ := Metric.diam (convexHull ℝ K) with hD
  have hDnn : 0 ≤ D := Metric.diam_nonneg
  have hKconv : IsCompact (convexHull ℝ K) :=
    Work.Smooth.JordanSeparation.isCompact_convexHull_of_isCompact hK
  -- elementary facts about the maps `f i`
  have hfcont : ∀ i, Continuous (f i) := fun i => by fun_prop
  have hfiK : ∀ i, f i '' K ⊆ K := by
    intro i y hy
    rw [hfix]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hfconv : ∀ i, f i '' convexHull ℝ K ⊆ convexHull ℝ K := by
    intro i
    have h : f i '' convexHull ℝ K = convexHull ℝ (f i '' K) :=
      image_convexHull_mul_add K (lam i) (c i)
    rw [h]
    exact convexHull_min (fun z hz => subset_convexHull ℝ K (hfiK i hz))
      (convex_convexHull ℝ K)
  have hfinj : ∀ i, Function.Injective (f i) :=
    fun i => injective_mul_add (ne_of_gt (hlam i).1) (c i)
  have hfdiam : ∀ i (S : Set ℂ), Bornology.IsBounded S →
      Metric.diam (f i '' S) ≤ lam i * Metric.diam S :=
    fun i S hS => diam_image_mul_add_le hS (lam i) (le_of_lt (hlam i).1) (c i)
  have hfconvex : ∀ i {S : Set ℂ}, Convex ℝ S → Convex ℝ (f i '' S) :=
    fun i S hS => convex_image_mul_add hS (lam i) (c i)
  -- the inductive family of cells
  have key : ∀ n : ℕ, ∃ s : Finset (Set ℂ),
      (∀ C ∈ s, IsCompact C) ∧ (∀ C ∈ s, Convex ℝ C) ∧
      (∀ C ∈ s, Metric.diam C ≤ q ^ n * D) ∧
      (∀ C ∈ s, C ⊆ convexHull ℝ K) ∧
      (∀ C ∈ s, ∀ C' ∈ s, C ≠ C' → Disjoint C C') ∧
      (∀ x ∈ K, ∃ C ∈ s, x ∈ C) := by
    intro n
    induction n with
    | zero =>
        refine ⟨({convexHull ℝ K} : Finset (Set ℂ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro C hC
          rw [Finset.mem_singleton] at hC
          rw [hC]
          exact hKconv
        · intro C hC
          rw [Finset.mem_singleton] at hC
          rw [hC]
          exact convex_convexHull ℝ K
        · intro C hC
          rw [Finset.mem_singleton] at hC
          subst hC
          have h : Metric.diam (convexHull ℝ K) ≤ D := le_of_eq hD.symm
          simpa only [pow_zero, one_mul] using h
        · intro C hC
          rw [Finset.mem_singleton] at hC
          subst hC
          exact subset_rfl
        · intro C hC C' hC' hne
          rw [Finset.mem_singleton] at hC hC'
          exact absurd (hC.trans hC'.symm) hne
        · intro x hx
          exact ⟨convexHull ℝ K, Finset.mem_singleton.mpr rfl, subset_convexHull ℝ K hx⟩
    | succ n ih =>
        obtain ⟨s, hIc, hCvx, hdia, hsub, hdis, hcov⟩ := ih
        set s' : Finset (Set ℂ) :=
          s.biUnion (fun C => Finset.univ.image (fun i => f i '' C)) with hs'
        have hmem : ∀ x : Set ℂ, x ∈ s' ↔ ∃ C ∈ s, ∃ i : Fin N, f i '' C = x := by
          intro x
          rw [hs']
          simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro C hC
          obtain ⟨C₀, hC₀, i, rfl⟩ := (hmem C).mp hC
          exact (hIc C₀ hC₀).image (hfcont i)
        · intro C hC
          obtain ⟨C₀, hC₀, i, rfl⟩ := (hmem C).mp hC
          exact hfconvex i (hCvx C₀ hC₀)
        · intro C hC
          obtain ⟨C₀, hC₀, i, rfl⟩ := (hmem C).mp hC
          calc Metric.diam (f i '' C₀) ≤ lam i * Metric.diam C₀ :=
                hfdiam i C₀ ((hIc C₀ hC₀).isBounded)
            _ ≤ lam i * (q ^ n * D) :=
                mul_le_mul_of_nonneg_left (hdia C₀ hC₀) (le_of_lt (hlam i).1)
            _ ≤ q * (q ^ n * D) :=
                mul_le_mul_of_nonneg_right (hle i)
                  (mul_nonneg (pow_nonneg (le_of_lt hqpos) n) hDnn)
            _ = q ^ (n + 1) * D := by rw [pow_succ]; ring
        · intro C hC
          obtain ⟨C₀, hC₀, i, rfl⟩ := (hmem C).mp hC
          exact subset_trans (Set.image_mono (hsub C₀ hC₀)) (hfconv i)
        · intro C hC C' hC' hne
          obtain ⟨C₀, hC₀, i, rfl⟩ := (hmem C).mp hC
          obtain ⟨C₁, hC₁, j, rfl⟩ := (hmem C').mp hC'
          by_cases hij : i = j
          · subst hij
            have hne' : C₀ ≠ C₁ := by rintro rfl; exact hne rfl
            have hd : Disjoint C₀ C₁ := hdis C₀ hC₀ C₁ hC₁ hne'
            rw [Set.disjoint_left] at hd ⊢
            intro z hz hz'
            obtain ⟨u, hu, rfl⟩ := hz
            obtain ⟨v, hv, hv'⟩ := hz'
            exact hd hu (by rw [← hfinj i hv']; exact hv)
          · exact Disjoint.mono (Set.image_mono (hsub C₀ hC₀)) (Set.image_mono (hsub C₁ hC₁))
              (hdisj i j hij)
        · intro x hx
          have hxU : x ∈ ⋃ i : Fin N, f i '' K := by rw [← hfix]; exact hx
          obtain ⟨i, y, hyK, rfl⟩ := mem_iUnion.mp hxU
          obtain ⟨C, hCs, hyC⟩ := hcov y hyK
          refine ⟨f i '' C, ?_, ⟨y, hyC, rfl⟩⟩
          exact Finset.mem_biUnion.mpr ⟨C, hCs, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  -- choose the level at which the cells are smaller than `δ`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q ^ n * D < δ := by
    rcases eq_or_lt_of_le hDnn with hD0 | hDpos
    · exact ⟨0, by rw [pow_zero, one_mul, ← hD0]; exact hδ⟩
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hDpos) hqlt
      exact ⟨n, (lt_div_iff₀ hDpos).mp hn⟩
  obtain ⟨s, hIc, hCvx, hdia, -, hdis, hcov⟩ := key n
  refine ⟨s.card, fun j => ((Finset.equivFin s).symm j : Set ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hIc _ ((Finset.equivFin s).symm j).property
  · intro j
    exact hCvx _ ((Finset.equivFin s).symm j).property
  · intro j
    exact lt_of_le_of_lt (hdia _ ((Finset.equivFin s).symm j).property) hn
  · intro i j hij
    refine hdis _ ((Finset.equivFin s).symm i).property _ ((Finset.equivFin s).symm j).property ?_
    intro h
    exact hij ((Finset.equivFin s).symm.injective (Subtype.ext h))
  · intro x hx
    obtain ⟨C, hCs, hxC⟩ := hcov x hx
    refine mem_iUnion.mpr ⟨Finset.equivFin s ⟨C, hCs⟩, ?_⟩
    show x ∈ ((Finset.equivFin s).symm (Finset.equivFin s ⟨C, hCs⟩) : Set ℂ)
    rw [Equiv.symm_apply_apply]
    exact hxC

end

end Work.BoxShrink.Pinch
