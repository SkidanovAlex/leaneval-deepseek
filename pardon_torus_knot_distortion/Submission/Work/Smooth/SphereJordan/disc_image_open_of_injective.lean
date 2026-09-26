import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.no_retraction_disc
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.brouwer_disc
import Submission.Work.Smooth.SphereJordan.volume_image_sphere_of_lipschitz
import Submission.Work.Smooth.SphereJordan.exists_lipschitz_approx

/-!
# Invariance of domain for an embedded disc in the plane

Let `F : 𝔻 → ℂ` be a continuous injection of the closed unit disc.  Then the image of the open
unit disc is open in `ℂ` (Brouwer's invariance of domain in dimension two).

## The route

The proof follows Kulpa's proof of invariance of domain (recorded by Tao), using only the
Brouwer fixed point theorem for the disc (`Work.Smooth.SphereJordan.brouwer_disc`).

Write `g` for the given injection, `K = g '' 𝔻` (compact) and let `G : ℂ → ℂ` be a continuous
extension of the inverse homeomorphism `g⁻¹ : K → 𝔻` (Tietze extension theorem,
`ContinuousMap.exists_restrict_eq`).  Two facts about `G` are used.

* **Stability of the zero.**  If `G' : K → ℂ` is continuous with `‖G' y - G y‖ ≤ 1` for all
  `y ∈ K`, then `G'` has a zero: otherwise `x ↦ x - G'(g x)` is a fixed-point-free self-map of
  `𝔻`, contradicting Brouwer (`exists_zero_of_close`).
* **A zero-free perturbation.**  If `g 0` is not an interior point of `K`, then there *is* a
  zero-free continuous `G' : K → ℂ` with `‖G' y - G y‖ ≤ 1`.  The construction pushes `K` away
  from a point `c ∉ K` close to `g 0` (the map `Φ`), approximates `G` on the pushed set by a
  function `P` which is Lipschitz on a ball (`exists_lipschitz_approx`), and shifts `P` by a
  small constant chosen outside `P` of the circle — possible because the Lipschitz image of a
  circle is Lebesgue-null (`volume_image_sphere_of_lipschitz`).

Together these contradict each other unless `g 0` is an interior point of `K`; a translation of
the argument handles every point of the open disc.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Metric Filter
open scoped NNReal Topology

/-- **Stability of the zero** (Tao's Lemma 6, dimension two).  If `g : 𝔻 → ℂ` is injective and
`G'` is a continuous function on `K = range g` with `‖G'(g z) - z‖ ≤ 1` for every `z`, then `G'`
has a zero.  Otherwise `x ↦ x - G'(g x)` is a continuous fixed-point-free self-map of the disc,
contradicting Brouwer's theorem. -/
theorem exists_zero_of_close {g : C(Disc, ℂ)} (hg : Function.Injective g)
    {G' : Set.range (g : Disc → ℂ) → ℂ} (hG' : Continuous G')
    (hclose : ∀ z : Disc, ‖G' ⟨g z, ⟨z, rfl⟩⟩ - (z : ℂ)‖ ≤ 1) :
    ∃ z : Disc, G' ⟨g z, ⟨z, rfl⟩⟩ = 0 := by
  have hcont : Continuous fun x : Disc => (x : ℂ) - G' ⟨g x, ⟨x, rfl⟩⟩ :=
    continuous_subtype_val.sub (hG'.comp (g.continuous.subtype_mk fun x => ⟨x, rfl⟩))
  have hmem : ∀ x : Disc, (x : ℂ) - G' ⟨g x, ⟨x, rfl⟩⟩ ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right, norm_sub_rev]
    exact hclose x
  let Φ : C(Disc, Disc) :=
    ⟨fun x => ⟨(x : ℂ) - G' ⟨g x, ⟨x, rfl⟩⟩, hmem x⟩, hcont.subtype_mk hmem⟩
  obtain ⟨x, hx⟩ := brouwer_disc Φ
  refine ⟨x, ?_⟩
  have h1 : (x : ℂ) - G' ⟨g x, ⟨x, rfl⟩⟩ = (x : ℂ) := by
    have h2 := congrArg (fun y : Disc => (y : ℂ)) hx
    simpa [Φ] using h2
  have h3 : -(G' ⟨g x, ⟨x, rfl⟩⟩) = 0 := by
    have h4 : (x : ℂ) - G' ⟨g x, ⟨x, rfl⟩⟩ - (x : ℂ) = 0 := by rw [h1]; ring
    simpa using h4
  exact neg_eq_zero.mp h3

/-- **A zero-free perturbation of the extension of the inverse.**  Let `g : 𝔻 → ℂ` be injective
and let `G : ℂ → ℂ` extend `g⁻¹` (so `G (g z) = z`).  If `g 0` is not an interior point of the
compact disc `K = range g`, then there is a continuous zero-free `G' : K → ℂ` with
`‖G' y - G y‖ ≤ 1` for all `y ∈ K`.

This is Kulpa's construction: push `K` away from a point `c ∉ K` near `g 0`, approximate `G`
on the pushed compact set, and shift the approximation by a small generic constant. -/
theorem exists_zerofree_of_failure {g : C(Disc, ℂ)} (hg : Function.Injective g)
    (G : C(ℂ, ℂ)) (hGx : ∀ z : Disc, G (g z) = (z : ℂ))
    (hfail : ∀ ε : ℝ, 0 < ε → ∃ c : ℂ, c ∉ Set.range (g : Disc → ℂ) ∧ ‖c - g 0‖ < ε) :
    ∃ G' : C(Set.range (g : Disc → ℂ), ℂ), (∀ y, G' y ≠ 0) ∧
      (∀ y, ‖G' y - G (y : ℂ)‖ ≤ 1) := by
  set K : Set ℂ := Set.range (g : Disc → ℂ) with hKdef
  have hKc : IsCompact K := isCompact_range g.continuous
  have hx₀K : g 0 ∈ K := ⟨0, rfl⟩
  have hGx₀ : G (g 0) = 0 := by simpa using hGx 0
  -- ## Step 1: a compact region on which `G` is uniformly continuous
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ y ∈ K ∪ Metric.closedBall (g 0) 2, ∀ y' ∈ K ∪ Metric.closedBall (g 0) 2,
        ‖y - y'‖ ≤ δ₁ → ‖G y - G y'‖ ≤ 1 / 4 := by
    have hcpt : IsCompact (K ∪ Metric.closedBall (g 0) 2) :=
      hKc.union (isCompact_closedBall _ _)
    have huco : UniformContinuousOn (G : ℂ → ℂ) (K ∪ Metric.closedBall (g 0) 2) :=
      hcpt.uniformContinuousOn_of_continuous G.continuous.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huco
    obtain ⟨δ, hδpos, hδ⟩ := huco (1 / 4) (by norm_num)
    refine ⟨δ / 2, by linarith, ?_⟩
    intro y hy y' hy' h
    have h1 : dist y y' < δ := by rw [dist_eq_norm]; linarith
    have h2 := hδ y hy y' hy' h1
    rw [dist_eq_norm] at h2
    linarith
  -- ## Step 2: `G` is small near `g 0`
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ y : ℂ, ‖y - g 0‖ ≤ δ₂ → ‖G y‖ ≤ 1 / 4 := by
    have hcont : ContinuousAt (G : ℂ → ℂ) (g 0) := G.continuous.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδpos, hδ⟩ := hcont (1 / 4) (by norm_num)
    refine ⟨δ / 2, by linarith, ?_⟩
    intro y hy
    have h1 : dist y (g 0) < δ := by rw [dist_eq_norm]; linarith
    have h2 : dist (G y) (G (g 0)) < 1 / 4 := hδ h1
    rw [dist_eq_norm, hGx₀, sub_zero] at h2
    exact le_of_lt h2
  -- ## Step 3: the parameters `ε` and `c`
  set ε : ℝ := min (min δ₁ (δ₂ / 2)) 1 with hεdef
  have hεpos : 0 < ε := lt_min (lt_min hδ₁pos (by linarith)) one_pos
  have hεδ₁ : ε ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ₂ : ε ≤ δ₂ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε1 : ε ≤ 1 := min_le_right _ _
  obtain ⟨c, hcK, hcε⟩ := hfail ε hεpos
  -- ## Step 4: the pushed set
  set S₂ : Set ℂ := Metric.sphere c ε with hS₂def
  set S₁ : Set ℂ := {y ∈ K | ε ≤ ‖y - c‖} with hS₁def
  set S : Set ℂ := S₁ ∪ S₂ with hSdef
  have hS₂c : IsCompact S₂ := isCompact_sphere c ε
  have hS₁c : IsCompact S₁ := by
    have hcl : IsClosed {y : ℂ | ε ≤ ‖y - c‖} :=
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
    have h1 : S₁ = K ∩ {y : ℂ | ε ≤ ‖y - c‖} := by ext y; simp [S₁, and_comm]
    rw [h1]
    exact hKc.inter_right hcl
  have hSc : IsCompact S := hS₁c.union hS₂c
  -- ## Step 5: the pushing map
  have hne' : ∀ y : K, (y : ℂ) - c ≠ 0 :=
    fun y => sub_ne_zero.mpr (fun h => hcK (h ▸ y.2))
  have hNnorm : ∀ y : K, 0 < ‖(y : ℂ) - c‖ := fun y => norm_pos_iff.mpr (hne' y)
  have hpush : Continuous fun y : K => c + (max (ε / ‖(y : ℂ) - c‖) 1 : ℝ) • ((y : ℂ) - c) := by
    refine continuous_const.add ?_
    refine (Continuous.max (continuous_const.div
      (continuous_subtype_val.sub continuous_const).norm
      (fun y => norm_ne_zero_iff.mpr (hne' y))) continuous_const).smul
      (continuous_subtype_val.sub continuous_const)
  let Φ : C(K, ℂ) := ⟨fun y => c + (max (ε / ‖(y : ℂ) - c‖) 1 : ℝ) • ((y : ℂ) - c), hpush⟩
  have hΦapply : ∀ y : K, Φ y = c + (max (ε / ‖(y : ℂ) - c‖) 1 : ℝ) • ((y : ℂ) - c) := fun y => rfl
  have hmax1 : ∀ y : K, ε ≤ ‖(y : ℂ) - c‖ → max (ε / ‖(y : ℂ) - c‖) 1 = 1 := by
    intro y h
    apply max_eq_right
    rw [div_le_one (hNnorm y)]
    exact h
  have hmax2 : ∀ y : K, ‖(y : ℂ) - c‖ < ε →
      max (ε / ‖(y : ℂ) - c‖) 1 = ε / ‖(y : ℂ) - c‖ := by
    intro y h
    apply max_eq_left
    rw [le_div_iff₀ (hNnorm y)]
    simpa using le_of_lt h
  have hΦeq : ∀ y : K, ε ≤ ‖(y : ℂ) - c‖ → Φ y = (y : ℂ) := by
    intro y h
    rw [hΦapply, hmax1 y h, one_smul, add_sub_cancel]
  have hΦdist : ∀ y : K, ‖(y : ℂ) - c‖ < ε → ‖Φ y - c‖ = ε := by
    intro y h
    rw [hΦapply, hmax2 y h, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hεpos (hNnorm y)), div_mul_cancel₀ ε (ne_of_gt (hNnorm y))]
  have hΦclose : ∀ y : K, ‖Φ y - (y : ℂ)‖ ≤ ε := by
    intro y
    rcases le_or_gt ε ‖(y : ℂ) - c‖ with h | h
    · rw [hΦeq y h, sub_self, norm_zero]; exact hεpos.le
    · have h1 : Φ y - (y : ℂ) = (ε / ‖(y : ℂ) - c‖ - 1) • ((y : ℂ) - c) := by
        rw [hΦapply, hmax2 y h, sub_smul, one_smul]
        abel
      rw [h1, norm_smul, Real.norm_eq_abs]
      have habs : |ε / ‖(y : ℂ) - c‖ - 1| = ε / ‖(y : ℂ) - c‖ - 1 := by
        rw [abs_of_nonneg]
        rw [sub_nonneg, one_le_div (hNnorm y)]
        exact le_of_lt h
      rw [habs]
      have h3 : (ε / ‖(y : ℂ) - c‖ - 1) * ‖(y : ℂ) - c‖ = ε - ‖(y : ℂ) - c‖ := by
        rw [sub_mul, one_mul, div_mul_cancel₀ ε (ne_of_gt (hNnorm y))]
      rw [h3]
      linarith [hNnorm y]
  have hΦL : ∀ y : K, Φ y ∈ K ∪ Metric.closedBall (g 0) 2 := by
    intro y
    rcases le_or_gt ε ‖(y : ℂ) - c‖ with h | h
    · exact Or.inl (by rw [hΦeq y h]; exact y.2)
    · refine Or.inr ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖Φ y - g 0‖ ≤ ‖Φ y - c‖ + ‖c - g 0‖ := by
        calc ‖Φ y - g 0‖ = ‖(Φ y - c) + (c - g 0)‖ := by ring_nf
          _ ≤ ‖Φ y - c‖ + ‖c - g 0‖ := norm_add_le _ _
      have h2 : ‖Φ y - c‖ = ε := hΦdist y h
      have h3 : ‖c - g 0‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hcε hε1)
      linarith [h1, h2, h3]
  have hΦmem : ∀ y : K, Φ y ∈ S := by
    intro y
    rcases le_or_gt ε ‖(y : ℂ) - c‖ with h | h
    · refine Or.inl ⟨?_, ?_⟩
      · rw [hΦeq y h]; exact y.2
      · rw [hΦeq y h]; exact h
    · exact Or.inr (by rw [Metric.mem_sphere, dist_eq_norm]; exact hΦdist y h)
  have hΦmemS₂ : ∀ y : K, ‖(y : ℂ) - c‖ < ε → Φ y ∈ S₂ := by
    intro y h
    rw [Metric.mem_sphere, dist_eq_norm]
    exact hΦdist y h
  -- a large ball containing `K` and the pushed set
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y ∈ K, ‖y‖ ≤ M := by
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKc.isBounded
    exact ⟨C + ‖g 0‖, fun y hy => by
      have h1 : dist y (g 0) ≤ C := hC hy hx₀K
      rw [dist_eq_norm] at h1
      calc ‖y‖ = ‖(y - g 0) + g 0‖ := by ring_nf
        _ ≤ ‖y - g 0‖ + ‖g 0‖ := norm_add_le _ _
        _ ≤ C + ‖g 0‖ := by linarith⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (g 0) hx₀K)
  set R : ℝ := M + ‖c‖ + ε + 1 with hRdef
  have hR₁ : ε ≤ R := by rw [hRdef]; linarith [norm_nonneg c, hM0]
  have hR₂ : ∀ y ∈ K, ‖y - c‖ ≤ R := by
    intro y hy
    have h1 : ‖y - c‖ ≤ ‖y‖ + ‖c‖ := by
      calc ‖y - c‖ = ‖y + (-c)‖ := by ring_nf
        _ ≤ ‖y‖ + ‖-c‖ := norm_add_le _ _
        _ = ‖y‖ + ‖c‖ := by rw [norm_neg]
    linarith [hM y hy, hRdef]
  have hΦmemR : ∀ y : K, Φ y ∈ Metric.closedBall c R := by
    intro y
    rcases le_or_gt ε ‖(y : ℂ) - c‖ with h | h
    · rw [Metric.mem_closedBall, dist_eq_norm, hΦeq y h]
      exact le_trans (hR₂ y y.2) le_rfl
    · rw [Metric.mem_closedBall, dist_eq_norm, hΦdist y h]
      exact hR₁
  -- ## Step 6: a positive lower bound for `‖G‖` on `S₁`
  have hGzero : ∀ y ∈ K, G y = 0 → y = g 0 := by
    intro y hy h0
    obtain ⟨z, hz⟩ := hy
    have h1 : (z : ℂ) = 0 := by
      have h2 := hGx z
      rw [hz, h0] at h2
      exact h2.symm
    have hz0 : z = 0 := Subtype.ext (by simpa using h1)
    rw [← hz, hz0]
  have hx₀notS₁ : g 0 ∉ S₁ := by
    intro h
    have h1 := h.2
    rw [norm_sub_rev] at h1
    exact absurd h1 (not_le.mpr hcε)
  obtain ⟨δ, hδpos, hδle, hδbd⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ y ∈ S₁, δ ≤ ‖G y‖ := by
    by_cases hne : S₁.Nonempty
    · obtain ⟨y₀, hy₀, hmin⟩ := hS₁c.exists_isMinOn hne (f := fun y => ‖G y‖) (G.continuous.continuousOn.norm)
      have hy₀K : y₀ ∈ K := hy₀.1
      have hpos : 0 < ‖G y₀‖ := by
        refine norm_pos_iff.mpr (fun h0 => ?_)
        have h1 : y₀ = g 0 := hGzero y₀ hy₀K h0
        exact hx₀notS₁ (h1 ▸ hy₀)
      refine ⟨min (1 / 4) ‖G y₀‖, lt_min (by norm_num) hpos, min_le_left _ _, ?_⟩
      intro y hy
      exact le_trans (min_le_right _ _) (hmin hy)
    · exact ⟨1 / 4, by norm_num, le_rfl, fun y hy => absurd ⟨y, hy⟩ hne⟩
  -- ## Step 7: the approximation and the shift
  obtain ⟨P, ⟨L, hPL⟩, hPclose⟩ := exists_lipschitz_approx hSc G c R (by linarith : 0 < δ / 4)
  have hLipsphere : LipschitzOnWith L P (Metric.sphere c ε) := hPL.mono
    (Subset.trans Metric.sphere_subset_closedBall
      (Metric.closedBall_subset_closedBall hR₁))
  have hvol : MeasureTheory.volume (P '' Metric.sphere c ε) = 0 :=
    volume_image_sphere_of_lipschitz hεpos.le hLipsphere
  have hinter : interior (P '' Metric.sphere c ε) = ∅ := by
    have h0 : MeasureTheory.volume (interior (P '' Metric.sphere c ε)) = 0 := by
      exact MeasureTheory.measure_mono_null interior_subset hvol
    exact IsOpen.eq_empty_of_measure_zero isOpen_interior h0
  have hdense : Dense (P '' Metric.sphere c ε)ᶜ := interior_eq_empty_iff_dense_compl.mp hinter
  have h0cl : (0 : ℂ) ∈ closure (P '' Metric.sphere c ε)ᶜ := by
    rw [hdense.closure_eq]; trivial
  rw [Metric.mem_closure_iff] at h0cl
  obtain ⟨w, hw, hwlt⟩ := h0cl (δ / 4) (by linarith)
  have hwnot : ∀ z : ℂ, z ∈ Metric.sphere c ε → P z ≠ w := by
    intro z hz hzw
    exact hw ⟨z, hz, hzw⟩
  set v : ℂ := -w with hvdef
  have hvnorm : ‖v‖ ≤ δ / 4 := by
    rw [hvdef, norm_neg]
    simpa [dist_eq_norm] using le_of_lt hwlt
  -- ## Step 8: the zero-free map
  let G' : C(K, ℂ) := ⟨fun y => P (Φ y) + v,
    ((hPL.continuousOn).comp_continuous Φ.continuous hΦmemR).add continuous_const⟩
  have G'apply : ∀ y : K, G' y = P (Φ y) + v := fun y => rfl
  refine ⟨G', ?_, ?_⟩
  · -- zero-freeness
    intro y
    rcases le_or_gt ε ‖(y : ℂ) - c‖ with h | h
    · have hyS₁ : (y : ℂ) ∈ S₁ := ⟨y.2, h⟩
      have hΦy : Φ y = (y : ℂ) := hΦeq y h
      rw [G'apply, hΦy]
      have h1 : δ / 2 ≤ ‖P (y : ℂ) + v‖ := by
        have h3 := hδbd (y : ℂ) hyS₁
        have h4 := hPclose (y : ℂ) (Or.inl hyS₁)
        have h5 : ‖G (y : ℂ)‖ ≤ ‖P (y : ℂ)‖ + δ / 4 := by
          calc ‖G (y : ℂ)‖ = ‖P (y : ℂ) + (G (y : ℂ) - P (y : ℂ))‖ := by ring_nf
            _ ≤ ‖P (y : ℂ)‖ + ‖G (y : ℂ) - P (y : ℂ)‖ := norm_add_le _ _
            _ ≤ ‖P (y : ℂ)‖ + δ / 4 := by
                rw [norm_sub_rev]; linarith
        have h6 : 3 * δ / 4 ≤ ‖P (y : ℂ)‖ := by linarith
        have h7 : ‖P (y : ℂ)‖ - ‖v‖ ≤ ‖P (y : ℂ) + v‖ := by
          rw [← norm_neg v, ← sub_neg_eq_add]
          exact le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
        linarith
      intro hzero
      have h8 : ‖P (y : ℂ) + v‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith) h1)
      exact h8 (by rw [hzero, norm_zero])
    · intro hzero
      rw [G'apply] at hzero
      have h1 : P (Φ y) = w := by
        have h2 : P (Φ y) = -v := eq_neg_of_add_eq_zero_left hzero
        rw [h2, hvdef, neg_neg]
      exact hwnot (Φ y) (hΦmemS₂ y h) h1
  · -- closeness
    intro y
    rw [G'apply]
    change ‖P (Φ y) + v - G (y : ℂ)‖ ≤ 1
    have h1 : ‖P (Φ y) + v - G (y : ℂ)‖
        ≤ ‖P (Φ y) - G (Φ y)‖ + ‖v‖ + ‖G (Φ y) - G (y : ℂ)‖ := by
      have hkey : P (Φ y) + v - G (y : ℂ)
          = (P (Φ y) - G (Φ y)) + v + (G (Φ y) - G (y : ℂ)) := by ring
      rw [hkey]
      calc ‖(P (Φ y) - G (Φ y)) + v + (G (Φ y) - G (y : ℂ))‖
          ≤ ‖(P (Φ y) - G (Φ y)) + v‖ + ‖G (Φ y) - G (y : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖P (Φ y) - G (Φ y)‖ + ‖v‖) + ‖G (Φ y) - G (y : ℂ)‖ := by
            linarith [norm_add_le (P (Φ y) - G (Φ y)) v]
    have h2 : ‖P (Φ y) - G (Φ y)‖ ≤ δ / 4 := hPclose (Φ y) (hΦmem y)
    have h3 : ‖G (Φ y) - G (y : ℂ)‖ ≤ 1 / 4 :=
      hδ₁ (Φ y) (hΦL y) (y : ℂ) (Or.inl y.2) (le_trans (hΦclose y) hεδ₁)
    linarith [h1, h2, h3, hvnorm, hδle]

/-- **Invariance of domain at the centre of the disc.**  The image of the open disc under an
embedding `g` of the closed disc is a neighbourhood of `g 0`. -/
theorem center_mem_interior (g : C(Disc, ℂ)) (hg : Function.Injective g) :
    g 0 ∈ interior (openImage g) := by
  by_contra hcon
  have hnotnhds : ¬ (openImage g ∈ nhds (g 0)) :=
    fun h => hcon (mem_interior_iff_mem_nhds.mpr h)
  -- ## Points outside the open image accumulate at `g 0`
  have hclose : ∀ r : ℝ, 0 < r → ∃ y : ℂ, ‖y - g 0‖ < r ∧ y ∉ openImage g := by
    intro r hr
    by_contra hcon2
    push_neg at hcon2
    apply hnotnhds
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (g 0) hr)
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hcon2 y hy
  -- ## The boundary curve misses a neighbourhood of `g 0`
  have hrange_sph : Set.range (circlePoint : ℝ → Disc) = {z : Disc | ‖(z : ℂ)‖ = 1} := by
    ext z
    constructor
    · rintro ⟨θ, rfl⟩
      exact NoRetraction.coreNormCirclePoint θ
    · intro hz
      exact Work.Smooth.Jordan.exists_circlePoint_eq z hz
  have hmiss : ∃ δ > 0, ∀ y : ℂ, ‖y - g 0‖ < δ → y ∉ g '' Set.range (circlePoint : ℝ → Disc) := by
    haveI : CompactSpace Disc := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
    have hcomp : IsCompact (g '' Set.range (circlePoint : ℝ → Disc)) := by
      rw [hrange_sph]
      exact ((isClosed_eq (continuous_norm.comp continuous_subtype_val)
        continuous_const).isCompact).image g.continuous
    have hnotmem : g 0 ∉ g '' Set.range (circlePoint : ℝ → Disc) := by
      rintro ⟨u, ⟨θ, rfl⟩, hu⟩
      have h1 : circlePoint θ = 0 := hg hu
      have h2 : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := NoRetraction.coreNormCirclePoint θ
      exact absurd (h1 ▸ h2) (by norm_num)
    have hopen : IsOpen ((g '' Set.range (circlePoint : ℝ → Disc))ᶜ) := hcomp.isClosed.isOpen_compl
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨δ, hδpos, hδ⟩ := hopen (g 0) hnotmem
    exact ⟨δ, hδpos, fun y hy hyS => hδ (by rwa [Metric.mem_ball, dist_eq_norm]) hyS⟩
  -- ## Points outside `range g` accumulate at `g 0`
  have hfail : ∀ ε : ℝ, 0 < ε → ∃ c : ℂ, c ∉ Set.range (g : Disc → ℂ) ∧ ‖c - g 0‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδpos, hδdisj⟩ := hmiss
    obtain ⟨y, hy1, hy2⟩ := hclose (min ε δ) (lt_min hε hδpos)
    refine ⟨y, ?_, ?_⟩
    · intro hy
      rw [range_eq_openImage_union (c := fun θ : ℝ => g (circlePoint θ)) (fun θ => rfl)] at hy
      rcases hy with h | h
      · exact hy2 h
      · obtain ⟨θ, hθ⟩ := h
        exact hδdisj y (lt_of_lt_of_le hy1 (min_le_right _ _))
          ⟨circlePoint θ, ⟨θ, rfl⟩, hθ⟩
    · exact lt_of_lt_of_le hy1 (min_le_left _ _)
  -- ## Tietze: extend the inverse homeomorphism
  have hemp : Topology.IsEmbedding (g : Disc → ℂ) :=
    (g.continuous.isClosedEmbedding hg).toIsEmbedding
  let e : Disc ≃ₜ Set.range (g : Disc → ℂ) := hemp.toHomeomorph
  have he : ∀ z : Disc, ((e z : Set.range (g : Disc → ℂ)) : ℂ) = g z :=
    fun z => hemp.toHomeomorph_apply_coe z
  let hK : C(Set.range (g : Disc → ℂ), ℂ) :=
    ⟨fun y => ((e.symm y : Disc) : ℂ), continuous_subtype_val.comp e.symm.continuous⟩
  have hh : ∀ z : Disc, hK ⟨g z, ⟨z, rfl⟩⟩ = (z : ℂ) := by
    intro z
    have h1 : e.symm ⟨g z, ⟨z, rfl⟩⟩ = z := by
      apply e.injective
      rw [Homeomorph.apply_symm_apply]
      exact Subtype.ext (he z)
    show ((e.symm ⟨g z, ⟨z, rfl⟩⟩ : Disc) : ℂ) = (z : ℂ)
    rw [h1]
  obtain ⟨G, hG⟩ :=
    ContinuousMap.exists_restrict_eq (Y := ℂ) (isCompact_range g.continuous).isClosed hK
  have hGx : ∀ z : Disc, G (g z) = (z : ℂ) := by
    intro z
    have h1 : ContinuousMap.restrict (Set.range (g : Disc → ℂ)) G ⟨g z, ⟨z, rfl⟩⟩
        = hK ⟨g z, ⟨z, rfl⟩⟩ :=
      congrArg (fun f : C(Set.range (g : Disc → ℂ), ℂ) => f ⟨g z, ⟨z, rfl⟩⟩) hG
    rw [ContinuousMap.restrict_apply, hh z] at h1
    exact h1
  -- ## Contradiction
  obtain ⟨G', hG'ne, hG'close⟩ := exists_zerofree_of_failure hg G hGx hfail
  obtain ⟨z, hz⟩ := exists_zero_of_close (g := g) hg G'.continuous (fun z => by
    rw [← hGx z]
    exact hG'close ⟨g z, ⟨z, rfl⟩⟩)
  exact hG'ne ⟨g z, ⟨z, rfl⟩⟩ hz

/-- **Invariance of domain for an embedded disc in the plane.**  The image of the open unit disc
under a continuous injection `F : 𝔻 → ℂ` is open in `ℂ`. -/
theorem openImage_isOpen_of_injective (F : C(Disc, ℂ)) (hF : Function.Injective F) :
    IsOpen (openImage F) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨z₀, hz₀, hxz⟩ := hx
  rw [← hxz]
  have hz₀lt : ‖(z₀ : ℂ)‖ < 1 := hz₀
  -- ## reduce to the centre of a smaller disc around `z₀`
  set ρ : ℝ := (1 - ‖(z₀ : ℂ)‖) / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; linarith
  have hρsum : ‖(z₀ : ℂ)‖ + ρ < 1 := by
    rw [hρdef]; linarith
  have hmem : ∀ z : Disc, (z₀ : ℂ) + ρ * (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z
    have hz1 : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(z₀ : ℂ) + ρ * (z : ℂ)‖ ≤ ‖(z₀ : ℂ)‖ + ‖ρ * (z : ℂ)‖ := norm_add_le _ _
      _ = ‖(z₀ : ℂ)‖ + ρ * ‖(z : ℂ)‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
      _ ≤ ‖(z₀ : ℂ)‖ + ρ := by
          linarith [mul_le_mul_of_nonneg_left hz1 hρpos.le]
      _ ≤ 1 := le_of_lt hρsum
  have hcont : Continuous fun z : Disc => (z₀ : ℂ) + ρ * (z : ℂ) :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  let c : C(Disc, Disc) := ⟨fun z => ⟨(z₀ : ℂ) + ρ * (z : ℂ), hmem z⟩, hcont.subtype_mk hmem⟩
  have hcapply : ∀ z : Disc, ((c z : Disc) : ℂ) = (z₀ : ℂ) + ρ * (z : ℂ) := fun z => rfl
  have hc0 : c 0 = z₀ := by
    apply Subtype.ext
    rw [hcapply]
    simp
  have hcinj : Function.Injective c := by
    intro a b hab
    have h2 : (a : ℂ) = (b : ℂ) := by
      have h3 := congrArg (fun w : Disc => (w : ℂ)) hab
      rw [hcapply, hcapply] at h3
      have h4 : ρ * (a : ℂ) = ρ * (b : ℂ) := by linear_combination h3
      have hρne : (ρ : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        exact ne_of_gt hρpos
      exact mul_left_cancel₀ hρne h4
    exact Subtype.ext h2
  let g' : C(Disc, ℂ) := F.comp c
  have hg' : Function.Injective g' := fun a b hab => hcinj (hF hab)
  have hg'0 : g' 0 = F z₀ := by
    show F (c 0) = F z₀
    rw [hc0]
  have hclt : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ‖(c z : ℂ)‖ < 1 := by
    intro z hz
    rw [hcapply]
    calc ‖(z₀ : ℂ) + ρ * (z : ℂ)‖ ≤ ‖(z₀ : ℂ)‖ + ‖ρ * (z : ℂ)‖ := norm_add_le _ _
      _ = ‖(z₀ : ℂ)‖ + ρ * ‖(z : ℂ)‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
      _ < ‖(z₀ : ℂ)‖ + ρ := by
          have h9 : ρ * ‖(z : ℂ)‖ < ρ * 1 := mul_lt_mul_of_pos_left hz hρpos
          linarith
      _ < 1 := hρsum
  have hsub : openImage g' ⊆ openImage F := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨c z, hclt z hz, rfl⟩
  have h1 : g' 0 ∈ interior (openImage g') := center_mem_interior g' hg'
  have h2 : g' 0 ∈ interior (openImage F) := interior_mono hsub h1
  rw [hg'0] at h2
  exact mem_interior_iff_mem_nhds.mp h2

/-- **Invariance of domain for an injective disc in the plane**, in the exact form requested by
the sibling files: the image of the open unit disc under a continuous injection `F : 𝔻 → ℂ` is
open in `ℂ`. -/
theorem disc_image_open_of_injective {F : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hF : Function.Injective F) :
    IsOpen (F '' {z : Work.Smooth.SphereJordan.Disc |
      ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1}) :=
  openImage_isOpen_of_injective F hF

end

end Work.Smooth.SphereJordan
