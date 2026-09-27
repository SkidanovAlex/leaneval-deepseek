import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_enum_critical

/-!
# The critical-value cover for a Morse function with distinct critical values on a surface

This file proves `Work.Drive.N2.criticalValueCover`: for a Morse function `f` with distinct critical
values on a compact surface `M`, the image `f '' M` is covered by finitely many open value bands, each
of which is either

* a *window* `(f p - ε, f p + ε)` around the value of a critical point `p`, or
* a *regular band* `(a, b)` whose **closed** interval `[a, b]` carries no critical point,

with a single `ε > 0` which is at most half the minimal distance between two distinct critical values
(so each window contains the value of exactly one critical point, and no endpoint `f p ± ε` is a
critical value).

The construction is: enumerate the critical points, let `CV` be the (finite, nonempty) set of critical
values, sort it as a strictly monotone `s : Fin n ↪o ℝ`, pick `ε` with `2ε ≤ |s i - s j|` for `i ≠ j`
(`exists_gap_eps`), and take the family consisting of the windows `(s j - ε, s j + ε)`, the bands
`(s j + ε/2, s (j+1) - ε/2)` between consecutive critical values, and one auxiliary band
`(s 0 - 1, s 0 - ε/2)` below the smallest critical value.  Every value of `f` lies between the
smallest and the largest critical value, because the minimum and the maximum of `f` on the compact `M`
are attained and are critical points (Fermat: `isCritical_of_forall_le'`, `isCritical_of_forall_ge`).

No disjointness of the bands is claimed (and none is true).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **Fermat at a maximum.**  Every maximiser of a smooth function is a critical point. -/
theorem isCritical_of_forall_ge {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {y : M} (hy : ∀ w, f w ≤ f y) :
    Work.Drive.Morse.IsCritical f y := by
  rw [Work.Drive.Morse.IsCritical,
    mfderiv_eq_zero_iff_chartRep f hf y y (mem_extChartAt_source y)]
  refine IsLocalMax.fderiv_eq_zero ?_
  rw [IsLocalMax, IsMaxFilter]
  filter_upwards with t
  show f ((extChartAt (𝓡 2) y).symm t) ≤ f ((extChartAt (𝓡 2) y).symm ((extChartAt (𝓡 2) y) y))
  rw [(extChartAt (𝓡 2) y).left_inv (mem_extChartAt_source y)]
  exact hy _

/-- **Fermat at a minimum.**  Every minimiser of a smooth function is a critical point. -/
theorem isCritical_of_forall_le' {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {y : M} (hy : ∀ w, f y ≤ f w) :
    Work.Drive.Morse.IsCritical f y := by
  rw [Work.Drive.Morse.IsCritical,
    mfderiv_eq_zero_iff_chartRep f hf y y (mem_extChartAt_source y)]
  refine IsLocalMin.fderiv_eq_zero ?_
  rw [IsLocalMin, IsMinFilter]
  filter_upwards with t
  show f ((extChartAt (𝓡 2) y).symm ((extChartAt (𝓡 2) y) y)) ≤ f ((extChartAt (𝓡 2) y).symm t)
  rw [(extChartAt (𝓡 2) y).left_inv (mem_extChartAt_source y)]
  exact hy _

/-- **The separation constant.**  For a finite injective family of reals there is `ε > 0` with
`ε ≤ 1/2` and `2ε ≤ |s i - s j|` for all `i ≠ j`. -/
lemma exists_gap_eps {n : ℕ} (s : Fin n → ℝ) (hinj : Function.Injective s) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ∀ i j : Fin n, i ≠ j → 2 * ε ≤ |s i - s j| := by
  classical
  set T : Finset ℝ := (Finset.univ.filter (fun q : Fin n × Fin n => q.1 ≠ q.2)).image
    (fun q => |s q.1 - s q.2|) with hT
  have hmem : ∀ i j : Fin n, i ≠ j → |s i - s j| ∈ T := by
    intro i j hij
    rw [hT]
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
  by_cases hne : T.Nonempty
  · refine ⟨min (T.min' hne / 2) (1 / 2), ?_, min_le_right _ _, ?_⟩
    · rcases le_total (T.min' hne / 2) (1 / 2) with h | h
      · rw [min_eq_left h]
        have hpos : 0 < T.min' hne := by
          obtain ⟨q, hq, hqmem⟩ := Finset.mem_image.mp (Finset.min'_mem T hne)
          have hq2 : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
          rw [← hqmem]
          exact abs_pos.mpr (sub_ne_zero.mpr (fun hc => hq2 (hinj hc)))
        linarith
      · rw [min_eq_right h]; norm_num
    · intro i j hij
      have h1 : T.min' hne ≤ |s i - s j| := Finset.min'_le T _ (hmem i j hij)
      have h2 : min (T.min' hne / 2) (1 / 2) ≤ T.min' hne / 2 := min_le_left _ _
      calc 2 * min (T.min' hne / 2) (1 / 2) ≤ 2 * (T.min' hne / 2) := by linarith
        _ = T.min' hne := by ring
        _ ≤ |s i - s j| := h1
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    intro i j hij
    exact absurd ⟨_, hmem i j hij⟩ hne

open scoped Manifold ContDiff Topology in
open Work.Drive.Morse in
/-- **The critical-value cover: windows and regular bands (item (i) of the H7 plan).**

`f` is a Morse function with distinct critical values on a compact surface.  Then `f '' M` is covered by
finitely many **open** value bands, each of one of the two kinds the assembly consumes:

* a *window*: `A i = (f p - ε, f p + ε)` for a critical point `p`;
* a *regular band*: `A i = (a, b)` whose **closed** interval `[a,b]` carries no critical point — so that
  `Work.Drive.N2.hasLevelFlow_of_noCritical` applies to `[a,b]` and the band carries the parked picture
  via the proved `Work.Drive.N2.goodDrawingOn_band`.

Moreover `ε > 0` is bounded by half the minimal distance between two distinct critical values, so each
window contains the value of *exactly one* critical point (if `f q ∈ (f p - ε, f p + ε)` with `p, q`
critical and `f q ≠ f p`, the gap condition gives `2ε ≤ |f q - f p| < ε`, absurd); in particular no
endpoint `f p ± ε` is a critical value, which is what makes the complementary intervals critical-free on
their *closures*.

**No disjointness is asked for, and it must not be**: it was refuted by the prover's machine-checked
counterexample (`criticalValueCover_false`, in `Submission/Work/Drive/N2/criticalValueCover.lean`).  For
a Morse function on a connected component `C`, if `x₀` minimises and `x₁` maximises `f` on `C` then both
are critical with `f x₀ ≠ f x₁` and, by connectedness, `[f x₀, f x₁] ⊆ f '' M`; a *connected* set covered
by *disjoint* open sets lies in one of them, and that single band would have to contain two distinct
critical values — impossible for a window (one critical value) and for a regular band (none).

Nothing is lost: `Work.Drive.N2.goodDrawing_of_family` needs the drawings to *agree on the pairwise
overlaps*, not the bands to be disjoint, and that agreement is discharged by
`Work.Drive.N2.drawingAgreement_holonomy` (pictures matched up to the holonomy of the two flows at a fixed
top level) — the overlap of a window with a neighbouring regular band is exactly where the collar
isotopies act. -/
theorem criticalValueCover {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : IsMorseDistinct f) :
    ∃ (m : ℕ) (A : Fin m → Set ℝ) (ε : ℝ),
      0 < ε ∧
        (∀ i, IsOpen (A i)) ∧
        (∀ x : M, ∃ i, f x ∈ A i) ∧
        (∀ p q : M, IsCritical f p → IsCritical f q → f p ≠ f q → 2 * ε ≤ |f p - f q|) ∧
        (∀ i : Fin m,
          (∃ p : M, IsCritical f p ∧ A i = Set.Ioo (f p - ε) (f p + ε)) ∨
            (∃ a b : ℝ, A i = Set.Ioo a b ∧ ∀ x : M, f x ∈ Set.Icc a b → ¬ IsCritical f x)) := by
  classical
  by_cases hM : Nonempty M
  · obtain ⟨k, p, hp_crit, hp_all⟩ := exists_enum_critical f hf.1 hf.2.1
    have hcont : Continuous f := hf.1.continuous
    obtain ⟨xmin, -, hxmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hcont.continuousOn
    obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
    have hminf : ∀ y, f xmin ≤ f y := fun y => hxmin (mem_univ y)
    have hmaxf : ∀ y, f y ≤ f xmax := fun y => hxmax (mem_univ y)
    have hcrit_min : IsCritical f xmin := isCritical_of_forall_le' hf.1 hminf
    have hcrit_max : IsCritical f xmax := isCritical_of_forall_ge hf.1 hmaxf
    let CV : Finset ℝ := (Finset.univ : Finset (Fin k)).image (fun i => f (p i))
    have hmemCV : ∀ t : ℝ, t ∈ CV ↔ ∃ x : M, IsCritical f x ∧ f x = t := by
      intro t
      constructor
      · intro ht
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ht
        exact ⟨p i, hp_crit i, hi⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, hi⟩ := hp_all x hx
        refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
        rw [← hi]
    have hCVne : CV.Nonempty := ⟨f xmin, (hmemCV _).mpr ⟨xmin, hcrit_min, rfl⟩⟩
    have hn : 0 < CV.card := Finset.card_pos.mpr hCVne
    let n : ℕ := CV.card
    have hn' : 0 < n := hn
    have hcard : CV.card = n := rfl
    let s : Fin n ↪o ℝ := CV.orderEmbOfFin hcard
    have hs_mono : StrictMono s := OrderEmbedding.strictMono s
    have hs_inj : Function.Injective s := hs_mono.injective
    have hs_mem : ∀ i : Fin n, s i ∈ CV := fun i => Finset.orderEmbOfFin_mem CV hcard i
    have hs_surj : ∀ t ∈ CV, ∃ i : Fin n, s i = t := by
      intro t ht
      have hr : t ∈ Set.range s := by
        rw [show Set.range s = (↑CV : Set ℝ) from Finset.range_orderEmbOfFin CV hcard]
        exact ht
      obtain ⟨i, hi⟩ := hr
      exact ⟨i, hi⟩
    have hs_min : ∀ t ∈ CV, s ⟨0, hn'⟩ ≤ t := by
      intro t ht
      rw [Finset.orderEmbOfFin_zero hcard hn']
      exact Finset.min'_le CV t ht
    have hlast : n - 1 < n := by omega
    have hs_max : ∀ t ∈ CV, t ≤ s ⟨n - 1, hlast⟩ := by
      intro t ht
      rw [Finset.orderEmbOfFin_last hcard hn']
      exact Finset.le_max' CV t ht
    obtain ⟨ε, hεpos, hεhalf, hεgap⟩ := exists_gap_eps s hs_inj
    let W : Fin n → Set ℝ := fun j => Set.Ioo (s j - ε) (s j + ε)
    let B : Fin n → Set ℝ := fun j =>
      if h : (j : ℕ) + 1 < n then Set.Ioo (s j + ε / 2) (s ⟨(j : ℕ) + 1, h⟩ - ε / 2)
      else Set.Ioo (s j + ε / 2) (s j + 1)
    let L : Set ℝ := Set.Ioo (s ⟨0, hn'⟩ - 1) (s ⟨0, hn'⟩ - ε / 2)
    let g : Fin n × Fin 3 → Set ℝ := fun q =>
      if (q.2 : ℕ) = 0 then W q.1 else if (q.2 : ℕ) = 1 then B q.1 else L
    let A : Fin (n * 3) → Set ℝ := fun i => g (finProdFinEquiv.symm i)
    have hA : ∀ (j : Fin n) (b : Fin 3), A (finProdFinEquiv (j, b)) = g (j, b) := by
      intro j b
      show g (finProdFinEquiv.symm (finProdFinEquiv (j, b))) = g (j, b)
      rw [Equiv.symm_apply_apply]
    have hg0 : ∀ j : Fin n, g (j, 0) = W j := by intro j; simp [g]
    have hg1 : ∀ j : Fin n, g (j, 1) = B j := by intro j; simp [g]
    have hg2 : ∀ j : Fin n, g (j, 2) = L := by intro j; simp [g]
    refine ⟨n * 3, A, ε, hεpos, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨j, b, rfl⟩ : ∃ j b, i = finProdFinEquiv (j, b) :=
        ⟨_, _, (Equiv.apply_symm_apply _ i).symm⟩
      rw [hA]
      rcases b with ⟨bval, hbval⟩
      interval_cases bval
      · rw [show (⟨0, hbval⟩ : Fin 3) = 0 from rfl, hg0]; exact isOpen_Ioo
      · rw [show (⟨1, hbval⟩ : Fin 3) = 1 from rfl, hg1]; unfold B; split_ifs <;> exact isOpen_Ioo
      · rw [show (⟨2, hbval⟩ : Fin 3) = 2 from rfl, hg2]; exact isOpen_Ioo
    · intro x
      have hxlo : s ⟨0, hn'⟩ ≤ f x :=
        le_trans (hs_min (f xmin) ((hmemCV _).mpr ⟨xmin, hcrit_min, rfl⟩)) (hminf x)
      have hxhi : f x ≤ s ⟨n - 1, hlast⟩ :=
        le_trans (hmaxf x) (hs_max (f xmax) ((hmemCV _).mpr ⟨xmax, hcrit_max, rfl⟩))
      let J : Finset (Fin n) := Finset.univ.filter (fun j => s j ≤ f x)
      have hJne : J.Nonempty :=
        ⟨⟨0, hn'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxlo⟩⟩
      let jm : Fin n := J.max' hJne
      have hjm_mem : s jm ≤ f x := (Finset.mem_filter.mp (Finset.max'_mem J hJne)).2
      have hjm_max : ∀ j : Fin n, s j ≤ f x → j ≤ jm := fun j hj =>
        Finset.le_max' J j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      by_cases hlt : f x < s jm + ε
      · refine ⟨finProdFinEquiv (jm, 0), ?_⟩
        rw [hA, hg0]
        exact ⟨by linarith, hlt⟩
      · have hge : s jm + ε ≤ f x := not_lt.mp hlt
        by_cases hj : (jm : ℕ) + 1 < n
        · by_cases h2 : f x < s ⟨(jm : ℕ) + 1, hj⟩ - ε / 2
          · refine ⟨finProdFinEquiv (jm, 1), ?_⟩
            rw [hA, hg1]
            unfold B
            rw [dif_pos hj]
            exact ⟨by linarith, h2⟩
          · have h2' : f x ≥ s ⟨(jm : ℕ) + 1, hj⟩ - ε / 2 := not_lt.mp h2
            refine ⟨finProdFinEquiv (⟨(jm : ℕ) + 1, hj⟩, 0), ?_⟩
            rw [hA, hg0]
            have hb : f x < s ⟨(jm : ℕ) + 1, hj⟩ + ε := by
              have hnot : ¬ (s ⟨(jm : ℕ) + 1, hj⟩ ≤ f x) := by
                intro hsle
                have hle := hjm_max ⟨(jm : ℕ) + 1, hj⟩ hsle
                have hlt2 : (jm : ℕ) + 1 ≤ (jm : ℕ) := by
                  simpa using (Fin.le_def.mp hle)
                omega
              linarith
            exact ⟨by linarith, hb⟩
        · exfalso
          have hjm_last : (jm : ℕ) = n - 1 := by have := jm.isLt; omega
          have hjeq : jm = (⟨n - 1, hlast⟩ : Fin n) := Fin.ext (by simpa using hjm_last)
          rw [← hjeq] at hxhi
          linarith
    · intro q r hq hr hqr
      obtain ⟨i, hi⟩ := hs_surj (f q) ((hmemCV (f q)).mpr ⟨q, hq, rfl⟩)
      obtain ⟨j, hj⟩ := hs_surj (f r) ((hmemCV (f r)).mpr ⟨r, hr, rfl⟩)
      have hij : i ≠ j := by
        intro h
        exact hqr (by rw [← hi, h, hj])
      have := hεgap i j hij
      rwa [hi, hj] at this
    · intro i
      obtain ⟨j, b, rfl⟩ : ∃ j b, i = finProdFinEquiv (j, b) :=
        ⟨_, _, (Equiv.apply_symm_apply _ i).symm⟩
      rw [hA]
      rcases b with ⟨bval, hbval⟩
      interval_cases bval
      · rw [show (⟨0, hbval⟩ : Fin 3) = 0 from rfl, hg0]
        obtain ⟨x0, hx0c, hx0v⟩ := (hmemCV (s j)).mp (hs_mem j)
        refine Or.inl ⟨x0, hx0c, ?_⟩
        show Set.Ioo (s j - ε) (s j + ε) = Set.Ioo (f x0 - ε) (f x0 + ε)
        rw [← hx0v]
      · rw [show (⟨1, hbval⟩ : Fin 3) = 1 from rfl, hg1]
        by_cases hj : (j : ℕ) + 1 < n
        · refine Or.inr ⟨s j + ε / 2, s ⟨(j : ℕ) + 1, hj⟩ - ε / 2, ?_, ?_⟩
          · unfold B; rw [dif_pos hj]
          · intro y hy hyc
            obtain ⟨m, hm⟩ := hs_surj (f y) ((hmemCV (f y)).mpr ⟨y, hyc, rfl⟩)
            rw [← hm] at hy
            obtain ⟨hy1, hy2⟩ := hy
            have h1 : j < m := (OrderEmbedding.lt_iff_lt s).mp (by linarith)
            have h2 : m < (⟨(j : ℕ) + 1, hj⟩ : Fin n) :=
              (OrderEmbedding.lt_iff_lt s).mp (by linarith)
            have h1' : (j : ℕ) < (m : ℕ) := Fin.lt_def.mp h1
            have h2' : (m : ℕ) < (j : ℕ) + 1 := by simpa using (Fin.lt_def.mp h2)
            omega
        · refine Or.inr ⟨s j + ε / 2, s j + 1, ?_, ?_⟩
          · unfold B; rw [dif_neg hj]
          · intro y hy hyc
            obtain ⟨m, hm⟩ := hs_surj (f y) ((hmemCV (f y)).mpr ⟨y, hyc, rfl⟩)
            rw [← hm] at hy
            obtain ⟨hy1, hy2⟩ := hy
            have h1 : j < m := (OrderEmbedding.lt_iff_lt s).mp (by linarith)
            have hjm_last : (j : ℕ) = n - 1 := by have := j.isLt; omega
            have hm' : (m : ℕ) < n := m.isLt
            have h1' : (j : ℕ) < (m : ℕ) := Fin.lt_def.mp h1
            omega
      · rw [show (⟨2, hbval⟩ : Fin 3) = 2 from rfl, hg2]
        refine Or.inr ⟨s ⟨0, hn'⟩ - 1, s ⟨0, hn'⟩ - ε / 2, rfl, ?_⟩
        intro y hy hyc
        obtain ⟨m, hm⟩ := hs_surj (f y) ((hmemCV (f y)).mpr ⟨y, hyc, rfl⟩)
        rw [← hm] at hy
        obtain ⟨hy1, hy2⟩ := hy
        have hle : s ⟨0, hn'⟩ ≤ s m :=
          (OrderEmbedding.le_iff_le s).mpr (by simp [Fin.le_def])
        linarith
  · refine ⟨0, fun _ : Fin 0 => (∅ : Set ℝ), 1, one_pos, ?_, ?_, ?_, ?_⟩
    · intro i; exact isOpen_empty
    · intro x; exact absurd ⟨x⟩ hM
    · intro q r hq hr hqr; exact absurd ⟨q⟩ hM
    · intro i; exact Fin.elim0 i

end Work.Drive.N2
