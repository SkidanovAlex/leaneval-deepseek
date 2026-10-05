import Mathlib
import Submission.Work.RPB.B3.EsTauAux
import Submission.Work.RPB.B3.esTauJetMatch
import Submission.Work.RPB.B3.esTauMultiLin
import Submission.Work.RPB.B3.esTauReflectCoeffs

/-!
# Extension of a `C^N` function from the closed `τ`-slab (evenness-free)

`Work.RPB.B5.tauSlabExtend`: a function `f` which is `C^N` on the closed strip
`[0,1] × ℝ × (-δ,δ)` admits an extension `F` of class `C^N` on `(-1,2) × ℝ × (-δ,δ)` agreeing
with `f` on the strip.  No evenness (in the last variable) is assumed or concluded; this is the
evenness-free form of `Work.RPB.B3.es_tau_extend`.

The extension is built from the finite reflection `∑ j, a j • f (c j • τ, ·, ·)` across `τ = 0`
and the analogous reflection across `τ = 1`; the seams are glued by `EsTauAux.halfspaces` and
the matching of the jets by `esTauJetMatchR` / `esTauJetMatchL`.
-/

open scoped ContDiff Topology Pointwise
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

open Work.RPB.B3

private def box1 (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioo 0 2 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

private def s1L (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := box1 δ ∩ {z | z.1 ≤ 1}

private def s1R (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := box1 δ ∩ {z | 1 ≤ z.1}

private theorem mem_box1 {δ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ box1 δ ↔ z.1 ∈ Set.Ioo (0:ℝ) 2 ∧ z.2.2 ∈ Set.Ioo (-δ) δ := by
  simp [box1, and_assoc]

private theorem isOpen_box1 (δ : ℝ) : IsOpen (box1 δ) :=
  isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)

private theorem convex_box1 (δ : ℝ) : Convex ℝ (box1 δ) :=
  (convex_Ioo (0:ℝ) 2).prod (convex_univ.prod (convex_Ioo (-δ) δ))

private theorem uniqueDiffOn_box1 (δ : ℝ) : UniqueDiffOn ℝ (box1 δ) :=
  (isOpen_box1 δ).uniqueDiffOn

private theorem s1L_eq (δ : ℝ) :
    s1L δ = Set.Ioc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  ext z
  simp only [s1L, box1, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_univ,
    Set.mem_setOf_eq, Set.mem_Ioc, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1.1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, by linarith [h2]⟩, h3⟩, h2⟩

private theorem s1R_eq (δ : ℝ) :
    s1R δ = Set.Ico (1:ℝ) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  ext z
  simp only [s1R, box1, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_univ,
    Set.mem_setOf_eq, Set.mem_Ico, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h3, h1.2⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by linarith [h1], h2⟩, h3⟩, h1⟩

private theorem uniqueDiffOn_s1L {δ : ℝ} (hδ : 0 < δ) : UniqueDiffOn ℝ (s1L δ) := by
  rw [s1L_eq]
  exact uniqueDiffOn_convex
    ((convex_Ioc (0:ℝ) 1).prod (convex_univ.prod (convex_Ioo (-δ) δ)))
    ⟨(1/2, 0, 0), by
      rw [mem_interior_iff_mem_nhds]
      refine mem_of_superset (((isOpen_Ioo (a := (0:ℝ)) (b := 1)).prod
        (isOpen_univ.prod (isOpen_Ioo (a := -δ) (b := δ)))).mem_nhds ?_) ?_
      · exact ⟨⟨by norm_num, by norm_num⟩, trivial, ⟨by linarith, by linarith⟩⟩
      · intro z hz
        exact ⟨⟨hz.1.1, hz.1.2.le⟩, trivial, hz.2.2⟩⟩

private theorem uniqueDiffOn_s1R {δ : ℝ} (hδ : 0 < δ) : UniqueDiffOn ℝ (s1R δ) := by
  rw [s1R_eq]
  exact uniqueDiffOn_convex
    ((convex_Ico (1:ℝ) 2).prod (convex_univ.prod (convex_Ioo (-δ) δ)))
    ⟨(3/2, 0, 0), by
      rw [mem_interior_iff_mem_nhds]
      refine mem_of_superset (((isOpen_Ioo (a := (1:ℝ)) (b := 2)).prod
        (isOpen_univ.prod (isOpen_Ioo (a := -δ) (b := δ)))).mem_nhds ?_) ?_
      · exact ⟨⟨by norm_num, by norm_num⟩, trivial, ⟨by linarith, by linarith⟩⟩
      · intro z hz
        exact ⟨⟨hz.1.1.le, hz.1.2⟩, trivial, hz.2.2⟩⟩


private def esExt {E : Type*} (A g B : ℝ × (ℝ × ℝ) → E) : ℝ × (ℝ × ℝ) → E :=
  fun z => if z.1 ≤ 0 then A z else if z.1 ≤ 1 then g z else B z

private theorem esHalfR_subset_T {δ : ℝ} :
    esHalfR δ ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_esBox] at hz1
  exact ⟨⟨hz2, le_of_lt hz1.1.2⟩, trivial, hz1.2⟩

private theorem s1L_subset_T {δ : ℝ} :
    s1L δ ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  intro z hz
  rw [s1L_eq] at hz
  exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, trivial, hz.2.2⟩

private theorem refl_maps_halfL {δ c : ℝ} (hc : c ∈ Set.Ioo (-1) 0) {z : ℝ × (ℝ × ℝ)}
    (hz : z ∈ esHalfL δ) : reflLin c z ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_esBox] at hz1
  rw [reflLin_apply']
  refine ⟨⟨?_, ?_⟩, trivial, hz1.2⟩
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hc.2) hz2
  · nlinarith [hc.1, hc.2, hz1.1.1, hz2]

private theorem s1R_maps_T {δ c : ℝ} (hc : c ∈ Set.Ioo (-1) 0) {z : ℝ × (ℝ × ℝ)}
    (hz : z ∈ s1R δ) :
    (1 + c * (z.1 - 1), z.2.1, z.2.2) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  rw [s1R_eq] at hz
  refine ⟨⟨?_, ?_⟩, trivial, hz.2.2⟩
  · nlinarith [hc.1, hc.2, hz.1.1, hz.1.2]
  · nlinarith [hc.2, hz.1.1]

private theorem esHalfL_shift_subset_T {δ : ℝ} :
    ∀ w ∈ esHalfL δ, w + (1, 0, 0) ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  rw [mem_esBox] at hw1
  have hw2' : w.1 ≤ 0 := hw2
  have hwv : w + (1, 0, 0) = (w.1 + 1, w.2.1, w.2.2) := by ext <;> simp [vadd_eq_add]
  rw [hwv]
  refine ⟨⟨?_, ?_⟩, trivial, hw1.2⟩
  · linarith [hw1.1.1]
  · linarith [hw2']

private theorem eq_add_e (z : ℝ × (ℝ × ℝ)) : z + (1, 0, 0) = (z.1 + 1, z.2.1, z.2.2) := by
  ext <;> simp [vadd_eq_add]

private theorem neg_e_vadd_s1L {δ : ℝ} :
    (-(1, 0, 0) : ℝ × (ℝ × ℝ)) +ᵥ (s1L δ) = esHalfL δ := by
  ext z
  rw [Set.mem_vadd_set, esHalfL_eq_halfBand, mem_halfBand]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rw [s1L_eq] at hy
    have hz1v : z.1 = -1 + y.1 := by
      have := congrArg (fun w : ℝ × (ℝ × ℝ) => w.1) hyz
      simpa using this.symm
    have hz2v : z.2.2 = y.2.2 := by
      have := congrArg (fun w : ℝ × (ℝ × ℝ) => w.2.2) hyz
      simpa using this.symm
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hz1v]; linarith [hy.1.1]
    · rw [hz1v]; linarith [hy.1.2]
    · rw [hz2v]; exact hy.2.2
  · intro hz
    refine ⟨z + (1, 0, 0), ?_, ?_⟩
    · rw [s1L_eq]
      simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo, Set.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h : (z + (1, 0, 0)).1 = z.1 + 1 := by simp [vadd_eq_add]
        rw [h]; linarith [hz.1.1]
      · have h : (z + (1, 0, 0)).1 = z.1 + 1 := by simp [vadd_eq_add]
        rw [h]; linarith [hz.1.2]
      · have h : (z + (1, 0, 0)).2.2 = z.2.2 := by simp [vadd_eq_add]
        rw [h]; exact hz.2
    · ext <;> simp [vadd_eq_add]

private theorem neg_e_vadd_s1R {δ : ℝ} :
    (-(1, 0, 0) : ℝ × (ℝ × ℝ)) +ᵥ (s1R δ) = esHalfR δ := by
  ext z
  rw [Set.mem_vadd_set]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rw [s1R_eq] at hy
    have hz1v : z.1 = -1 + y.1 := by
      have := congrArg (fun w : ℝ × (ℝ × ℝ) => w.1) hyz
      simpa using this.symm
    have hz2v : z.2.2 = y.2.2 := by
      have := congrArg (fun w : ℝ × (ℝ × ℝ) => w.2.2) hyz
      simpa using this.symm
    rw [esHalfR, Set.mem_inter_iff, mem_esBox]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hz1v]; linarith [hy.1.1]
    · rw [hz1v]; linarith [hy.1.2]
    · rw [hz2v]; exact hy.2.2
    · show (0:ℝ) ≤ z.1; rw [hz1v]; linarith [hy.1.1]
  · intro hz
    obtain ⟨hz1, hz2⟩ := hz
    rw [mem_esBox] at hz1
    have hz2' : (0:ℝ) ≤ z.1 := hz2
    refine ⟨z + (1, 0, 0), ?_, ?_⟩
    · rw [s1R_eq]
      simp only [Set.mem_prod, Set.mem_Ico, Set.mem_Ioo, Set.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h : (z + (1, 0, 0)).1 = z.1 + 1 := by simp [vadd_eq_add]
        rw [h]; linarith [hz2']
      · have h : (z + (1, 0, 0)).1 = z.1 + 1 := by simp [vadd_eq_add]
        rw [h]; linarith [hz1.1.2]
      · have h : (z + (1, 0, 0)).2.2 = z.2.2 := by simp [vadd_eq_add]
        rw [h]; exact hz1.2
    · ext <;> simp [vadd_eq_add]

/-- **Extension of a `C^N` function from the closed `τ`-slab.**  If `f : ℝ → ℝ → ℝ → E` is `C^N` on the closed slab `[0,1] × ℝ × (-δ,δ)`, then it extends to a `C^N` function on the larger slab `(-1,2) × ℝ × (-δ,δ)` (Seeley reflection in the `τ` variable). -/
theorem tauSlabExtend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiffOn ℝ N (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ)) :
    ∃ F : ℝ → ℝ → ℝ → E,
      ContDiffOn ℝ N (fun z : ℝ × (ℝ × ℝ) => F z.1 z.2.1 z.2.2)
        (Set.Ioo (-1 : ℝ) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, r ∈ Set.Ioo (-δ) δ → F τ t r = f τ t r) := by
  classical
  obtain ⟨c, a, hc, hcinj, hid⟩ := esTauReflectCoeffs N
  have ha1 : (∑ j, a j) = 1 := by simpa using hid 0 (Nat.zero_le N)
  set g : ℝ × (ℝ × ℝ) → E := fun z => f z.1 z.2.1 z.2.2 with hgdef
  have hgval : ∀ x : ℝ × (ℝ × ℝ), g x = f x.1 x.2.1 x.2.2 := fun x => by rw [hgdef]
  set A : ℝ × (ℝ × ℝ) → E := fun z => ∑ j, a j • g (reflLin (c j) z) with hAdef
  have hAval : ∀ x : ℝ × (ℝ × ℝ), A x = ∑ j, a j • g (reflLin (c j) x) := fun x => rfl
  set B : ℝ × (ℝ × ℝ) → E :=
    fun z => ∑ j, a j • g (1 + c j * (z.1 - 1), z.2.1, z.2.2) with hBdef
  have hBval : ∀ x : ℝ × (ℝ × ℝ), B x =
      ∑ j, a j • g (1 + c j * (x.1 - 1), x.2.1, x.2.2) := fun x => rfl
  have hT : ContDiffOn ℝ N g (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) := hf
  refine ⟨fun τ t r => esExt A g B (τ, t, r), ?_, ?_⟩
  · -- smoothness
    have hmain : ContDiffOn ℝ N (esExt A g B)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ) := by
      have hAcd : ContDiffOn ℝ N A (esHalfL δ) := by
        have h1 : ContDiffOn ℝ N (fun z => ∑ j, a j • g (reflLin (c j) z)) (esHalfL δ) := by
          refine ContDiffOn.sum (fun j _ => ?_)
          refine ContDiffOn.const_smul (a j) ?_
          exact (hT.comp_continuousLinearMap (reflLin (c j))).mono
            (fun z hz => refl_maps_halfL (hc j) hz)
        exact h1.congr (fun z _ => (hAval z).symm)
      have hgR : ContDiffOn ℝ N g (esHalfR δ) := hT.mono esHalfR_subset_T
      have hBcd : ContDiffOn ℝ N B (s1R δ) := by
        have h1 : ContDiffOn ℝ N
            (fun z => ∑ j, a j • g (1 + c j * (z.1 - 1), z.2.1, z.2.2)) (s1R δ) := by
          refine ContDiffOn.sum (fun j _ => ?_)
          refine ContDiffOn.const_smul (a j) ?_
          refine hT.comp ?_ ?_
          · exact (by fun_prop :
              ContDiffOn ℝ N (fun z : ℝ × (ℝ × ℝ) => (1 + c j * (z.1 - 1), z.2.1, z.2.2)) (s1R δ))
          · intro z hz; exact s1R_maps_T (hc j) hz
        exact h1.congr (fun z _ => (hBval z).symm)
      have hgL1 : ContDiffOn ℝ N g (s1L δ) := hT.mono s1L_subset_T
      have hA_seam : ∀ t r, A (0, t, r) = g (0, t, r) := by
        intro t r
        rw [hAval]
        simp only [reflLin_apply', mul_zero]
        rw [← Finset.sum_smul, ha1, one_smul]
      have hjm0 : ∀ z ∈ esBox δ, z.1 = 0 → ∀ m : ℕ, m ≤ N →
          iteratedFDerivWithin ℝ m A (esHalfL δ) z
            = iteratedFDerivWithin ℝ m g (esHalfR δ) z := by
        intro z hz hz0 m hm
        rw [hAdef]
        exact esTauJetMatchR g N hδ hgR c a hc hid z hz hz0 m hm
      set p0 : ℝ × (ℝ × ℝ) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E :=
        fun z => if z.1 ≤ 0 then ftaylorSeriesWithin ℝ A (esHalfL δ) z
          else ftaylorSeriesWithin ℝ g (esHalfR δ) z with hp0def
      have hL0 : HasFTaylorSeriesUpToOn N A p0 (esHalfL δ) := by
        refine (hAcd.ftaylorSeriesWithin (uniqueDiffOn_esHalfL hδ)).congr_series (fun m hm => ?_)
        intro z hz
        have hp : p0 z = ftaylorSeriesWithin ℝ A (esHalfL δ) z := by
          rw [hp0def]; exact if_pos (show z.1 ≤ 0 from hz.2)
        dsimp only
        rw [hp]
      have hR0 : HasFTaylorSeriesUpToOn N g p0 (esHalfR δ) := by
        refine (hgR.ftaylorSeriesWithin (uniqueDiffOn_esHalfR hδ)).congr_series (fun m hm => ?_)
        intro z hz
        have hz0' : 0 ≤ z.1 := hz.2
        rcases lt_or_eq_of_le hz0' with h | h
        · have hp : p0 z = ftaylorSeriesWithin ℝ g (esHalfR δ) z := by
            rw [hp0def]; exact if_neg (show ¬ (z.1 ≤ 0) from by linarith)
          dsimp only
          rw [hp]
        · have hp : p0 z = ftaylorSeriesWithin ℝ A (esHalfL δ) z := by
            rw [hp0def]; exact if_pos (show z.1 ≤ 0 from le_of_eq h.symm)
          dsimp only
          rw [hp]
          exact (hjm0 z hz.1 h.symm m (by exact_mod_cast hm)).symm
      have hbox0 : ContDiffOn ℝ N (esExt A g B) (esBox δ) := by
        have hF0 : HasFTaylorSeriesUpToOn N (esExt A g B) p0 (esBox δ) := by
          refine hasFTaylorSeriesUpToOn_of_halfspaces (esExt A g B) N (isOpen_esBox δ) (a := 0) ?_ ?_
          · refine hL0.congr (fun z hz => ?_)
            simp only [esExt]; rw [if_pos (show z.1 ≤ 0 from hz.2)]
          · refine hR0.congr (fun z hz => ?_)
            have hz0' : 0 ≤ z.1 := hz.2
            rcases lt_or_eq_of_le hz0' with h | h
            · simp only [esExt]; rw [if_neg (not_le.mpr h), if_pos (le_of_lt hz.1.1.2)]
            · have hz_eq : z = (0, z.2.1, z.2.2) := by
                ext <;> simp [show z.1 = 0 from h.symm]
              simp only [esExt]
              rw [if_pos (show z.1 ≤ 0 from le_of_eq h.symm), hz_eq, hA_seam]
        exact hF0.contDiffOn
      -- the seam at τ = 1
      have hjm1 : ∀ z ∈ s1L δ, z.1 = 1 → ∀ m : ℕ, m ≤ N →
          iteratedFDerivWithin ℝ m g (s1L δ) z
            = iteratedFDerivWithin ℝ m B (s1R δ) z := by
        intro z hzL hz1 m hm
        rw [s1L_eq] at hzL
        set g1 : ℝ × (ℝ × ℝ) → E := fun w => g (w + (1, 0, 0)) with hg1def
        set B1 : ℝ × (ℝ × ℝ) → E := fun w => B (w + (1, 0, 0)) with hB1def
        have hg1L : ContDiffOn ℝ N g1 (esHalfL δ) := by
          rw [hg1def]
          refine hT.comp ?_ ?_
          · exact (by fun_prop :
              ContDiffOn ℝ N (fun w : ℝ × (ℝ × ℝ) => w + (1, 0, 0)) (esHalfL δ))
          · intro w hw; exact esHalfL_shift_subset_T w hw
        have hB1_reflect : B1 = fun w => ∑ j, a j • g1 (reflLin (c j) w) := by
          funext w
          change B (w + (1, 0, 0)) = ∑ j, a j • g1 (reflLin (c j) w)
          rw [hBval]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hX : (1 + c j * ((w + (1,0,0)).1 - 1), (w + (1,0,0)).2.1, (w + (1,0,0)).2.2)
              = (reflLin (c j) w) + (1, 0, 0) := by
            rw [reflLin_apply']
            ext <;> simp [vadd_eq_add]
            ring
          rw [hX]
        have hjm := esTauJetMatchL g1 N hδ hg1L c a hc hid
        have hze_eq : z - (1,0,0) = (z.1 - 1, z.2.1, z.2.2) := by ext <;> simp [vadd_eq_add]
        have hzeM : z - (1, 0, 0) ∈ esBox δ := by
          rw [hze_eq, mem_esBox]
          exact ⟨⟨by linarith [hzL.1.1, hz1], by linarith [hz1]⟩, hzL.2.2⟩
        have hze0 : (z - (1, 0, 0)).1 = 0 := by rw [hze_eq]; linarith
        have hkey : iteratedFDerivWithin ℝ m (fun w => ∑ j, a j • g1 (reflLin (c j) w))
              (esHalfR δ) (z - (1, 0, 0))
            = iteratedFDerivWithin ℝ m g1 (esHalfL δ) (z - (1, 0, 0)) :=
          hjm (z - (1, 0, 0)) hzeM hze0 m hm
        have hfun_g : (fun z : ℝ × (ℝ × ℝ) => g1 (z - (1, 0, 0))) = g := by
          funext z
          change g ((z - (1,0,0)) + (1,0,0)) = g z
          rw [show (z - (1,0,0)) + (1,0,0) = z from by ext <;> simp [vadd_eq_add]]
        have hfun_B : (fun z : ℝ × (ℝ × ℝ) => B1 (z - (1, 0, 0))) = B := by
          funext z
          change B ((z - (1,0,0)) + (1,0,0)) = B z
          rw [show (z - (1,0,0)) + (1,0,0) = z from by ext <;> simp [vadd_eq_add]]
        have hstepg : iteratedFDerivWithin ℝ m g (s1L δ) z
            = iteratedFDerivWithin ℝ m g1 (esHalfL δ) (z - (1, 0, 0)) := by
          conv_lhs => rw [← hfun_g]
          rw [iteratedFDerivWithin_comp_sub m ((1, 0, 0) : ℝ × (ℝ × ℝ)), neg_e_vadd_s1L]
        have hstepB : iteratedFDerivWithin ℝ m B (s1R δ) z
            = iteratedFDerivWithin ℝ m B1 (esHalfR δ) (z - (1, 0, 0)) := by
          conv_lhs => rw [← hfun_B]
          rw [iteratedFDerivWithin_comp_sub m ((1, 0, 0) : ℝ × (ℝ × ℝ)), neg_e_vadd_s1R]
        rw [hstepg, hstepB, hB1_reflect]
        exact hkey.symm
      set p1 : ℝ × (ℝ × ℝ) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E :=
        fun z => if z.1 ≤ 1 then ftaylorSeriesWithin ℝ g (s1L δ) z
          else ftaylorSeriesWithin ℝ B (s1R δ) z with hp1def
      have hg_seam1 : ∀ t r, B (1, t, r) = g (1, t, r) := by
        intro t r
        rw [hBval]
        rw [show (fun j => a j • g (1 + c j * ((1:ℝ) - 1), t, r))
            = fun j => a j • g (1, t, r) from by
          funext j; rw [sub_self, mul_zero, add_zero]]
        rw [← Finset.sum_smul, ha1, one_smul, hgval]
      have hL1 : HasFTaylorSeriesUpToOn N g p1 (s1L δ) := by
        refine (hgL1.ftaylorSeriesWithin (uniqueDiffOn_s1L hδ)).congr_series (fun m hm => ?_)
        intro z hz
        rw [s1L_eq] at hz
        have hp : p1 z = ftaylorSeriesWithin ℝ g (s1L δ) z := by
          rw [hp1def]; exact if_pos hz.1.2
        dsimp only
        rw [hp]
      have hR1 : HasFTaylorSeriesUpToOn N B p1 (s1R δ) := by
        refine (hBcd.ftaylorSeriesWithin (uniqueDiffOn_s1R hδ)).congr_series (fun m hm => ?_)
        intro z hz
        rw [s1R_eq] at hz
        rcases lt_or_eq_of_le hz.1.1 with h | h
        · have hp : p1 z = ftaylorSeriesWithin ℝ B (s1R δ) z := by
            rw [hp1def]; exact if_neg (show ¬ (z.1 ≤ 1) from by linarith)
          dsimp only
          rw [hp]
        · have hp : p1 z = ftaylorSeriesWithin ℝ g (s1L δ) z := by
            rw [hp1def]; exact if_pos (le_of_eq h.symm)
          dsimp only
          rw [hp]
          exact (hjm1 z (by rw [s1L_eq]; exact ⟨⟨by linarith [hz.1.1], by linarith [h]⟩, trivial, hz.2.2⟩)
            h.symm m (by exact_mod_cast hm)).symm
      have hbox1 : ContDiffOn ℝ N (esExt A g B) (box1 δ) := by
        have hF1 : HasFTaylorSeriesUpToOn N (esExt A g B) p1 (box1 δ) := by
          refine hasFTaylorSeriesUpToOn_of_halfspaces (esExt A g B) N (isOpen_box1 δ) (a := 1) ?_ ?_
          · refine hL1.congr (fun z hz => ?_)
            rw [s1L_eq] at hz
            simp only [esExt]
            rw [if_neg (not_le.mpr (by linarith [hz.1.1])), if_pos hz.1.2]
          · refine hR1.congr (fun z hz => ?_)
            rw [s1R_eq] at hz
            rcases lt_or_eq_of_le hz.1.1 with h | h
            · simp only [esExt]
              rw [if_neg (not_le.mpr (by linarith)), if_neg (not_le.mpr h)]
            · have hz_eq : z = (1, z.2.1, z.2.2) := by
                ext <;> simp [show z.1 = 1 from h.symm]
              simp only [esExt]
              rw [if_neg (not_le.mpr (by linarith)), if_pos (le_of_eq h.symm), hz_eq]
              exact (hg_seam1 z.2.1 z.2.2).symm
        exact hF1.contDiffOn
      have hunion : esBox δ ∪ box1 δ = Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ := by
        rw [esBox, box1]
        ext z
        simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, true_and]
        constructor
        · rintro (h | h)
          · exact ⟨⟨h.1.1, by linarith [h.1.2]⟩, h.2⟩
          · exact ⟨⟨by linarith [h.1.1], h.1.2⟩, h.2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          rcases lt_or_ge z.1 1 with h | h
          · exact Or.inl ⟨⟨h1, h⟩, h3⟩
          · exact Or.inr ⟨⟨by linarith, h2⟩, h3⟩
      rw [← hunion]
      exact ContDiffOn.union_of_isOpen hbox0 hbox1 (isOpen_esBox δ) (isOpen_box1 δ)
    exact hmain
  · -- agreement on the strip
    intro τ hτ t r hr
    show esExt A g B (τ, t, r) = f τ t r
    simp only [esExt]
    by_cases h1 : τ ≤ 0
    · rw [if_pos h1]
      have hτ0 : τ = 0 := le_antisymm h1 hτ.1
      subst hτ0
      have : A (0, t, r) = g (0, t, r) := by
        rw [hAval]
        simp only [reflLin_apply', mul_zero]
        rw [← Finset.sum_smul, ha1, one_smul]
      rw [this, hgval]
    · rw [if_neg h1, if_pos hτ.2, hgval]

end Work.RPB.B5
