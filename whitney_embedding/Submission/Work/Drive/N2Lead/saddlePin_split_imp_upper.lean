import Mathlib
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.pinFlow
import Submission.Work.Drive.N2Lead.pinComplex
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2Lead.landingWide_band
import Submission.Work.Drive.N2Lead.exists_continuous_arcLift
import Submission.Work.Drive.N2Lead.range_eq_connectedComponentIn
import Submission.Work.Drive.N2Lead.saddlePinDefs
import Submission.Work.Drive.N2Lead.levelCurvesReparam
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2Lead.pinUpEqArcs

/-!
# The saddle-pin dichotomy: the split case implies the merge case

`Work.Drive.N2Lead.saddlePin_split_imp_upper`: if the anchor pin (`f p - 3η/2`) is *not* contained in
one connected component of its level, then the upper pin (`f p + 3η/2`) *is*.

The proof is the split/merge dichotomy of Morse theory, with the machinery of `Work.Drive.N2Lead`:

* the anchor pin is the union of the two arcs `arcU`, `arcD` (`SaddleChart.pin_eq_arcs`), so the
  hypothesis gives two distinct components `K ≠ K'` of the anchor level;
* cutting a component by the strip `{|Im (Zc ·)²| < cλ²}` removes exactly an open arc
  (`strip_mem_arc` + the classification `pin_eq_arcs`), and the complement of a liftable arc in one
  component curve is preconnected (`isPreconnected_range_sdiff_arc`);
* every point off the strip is a *box point* of the wide band, so the two-sided landing
  (`landingWide_band`) carries it to the upper level; the flow rows (`flow_arcIds`) identify the
  images of the endpoints, which shows that the two upper branches are joined;
* the upper pin is covered by `arcR`, `arcL` (the upper classification `pinUpEqArcs`).

-/

set_option maxHeartbeats 1600000

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

/-! ## 1. The topological core -/

section Topology

/-- **The complement of an arc in a periodic curve is preconnected** (the strictly monotone case).
Let `γ` be a continuous `1`-periodic curve, `α` an arc lifted by a continuous `τ` which is strictly
monotone on `[-u,u]`, and suppose the lift spans less than one period.  Then the complement of the
open arc `α '' (-u,u)` in the range of `γ` is the image of the closed interval
`[τ u, τ (-u) + 1]`, hence preconnected. -/
lemma isPreconnected_sdiff_arc_of_strictMonoOn {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X} {α : ℝ → X} {τ : ℝ → ℝ} {u : ℝ}
    (hγc : Continuous γ) (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hγα : ∀ w ∈ Icc (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u))
    (hmono : StrictMonoOn τ (Icc (-u) u)) (hu : 0 < u) (hspan : τ u - τ (-u) < 1) :
    IsPreconnected (Set.range γ \ α '' Ioo (-u) u) := by
  have hule : -u < u := by linarith
  have huI : u ∈ Icc (-u) u := ⟨le_of_lt hule, le_rfl⟩
  have hnuI : -u ∈ Icc (-u) u := ⟨le_rfl, le_of_lt hule⟩
  have F1 : ∀ w ∈ Ioo (-u) u, τ w ∈ Ioo (τ (-u)) (τ u) := fun w hw =>
    ⟨hmono hnuI ⟨le_of_lt hw.1, le_of_lt hw.2⟩ hw.1,
      hmono ⟨le_of_lt hw.1, le_of_lt hw.2⟩ huI hw.2⟩
  have F2 : ∀ θ ∈ Ioo (τ (-u)) (τ u), ∃ w ∈ Ioo (-u) u, τ w = θ := by
    intro θ hθ
    obtain ⟨w, hw, hwθ⟩ := intermediate_value_Icc (le_of_lt hule) hτc
      (show τ (-u) ≤ θ ∧ θ ≤ τ u from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    have hw2 : w ∈ Ioo (-u) u := by
      constructor
      · by_contra hcon
        push_neg at hcon
        have hweq : w = -u := le_antisymm hcon hw.1
        rw [hweq] at hwθ
        linarith [hwθ, hθ.1]
      · by_contra hcon
        push_neg at hcon
        have hweq : w = u := le_antisymm hw.2 hcon
        rw [hweq] at hwθ
        linarith [hwθ, hθ.2]
    exact ⟨w, hw2, hwθ⟩
  have hstrip1 : α '' Ioo (-u) u ⊆ γ '' Ioo (τ (-u)) (τ u) := by
    rintro x ⟨w, hw, rfl⟩
    exact ⟨τ w, F1 w hw, hγα w ⟨le_of_lt hw.1, le_of_lt hw.2⟩⟩
  have hstrip2 : γ '' Ioo (τ (-u)) (τ u) ⊆ α '' Ioo (-u) u := by
    rintro x ⟨θ, hθ, rfl⟩
    obtain ⟨w, hw, hwθ⟩ := F2 θ hθ
    exact ⟨w, hw, by rw [← hwθ]; exact (hγα w ⟨le_of_lt hw.1, le_of_lt hw.2⟩).symm⟩
  have hcompl : Set.range γ \ α '' Ioo (-u) u = γ '' Icc (τ u) (τ (-u) + 1) := by
    refine Subset.antisymm ?_ ?_
    · -- a point not in the arc meets the interval `[τ u, τ (-u) + 1]` up to an integer shift
      rintro x ⟨⟨t, rfl⟩, hx⟩
      set t' : ℝ := Int.fract (t - τ u) + τ u with ht'def
      have ht'1 : τ u ≤ t' := by simp [ht'def, Int.fract_nonneg]
      have ht'2 : t' < τ u + 1 := by have := Int.fract_lt_one (t - τ u); rw [ht'def]; linarith
      have hγt' : γ t' = γ t := by
        have hkey : t' = t + (-(⌊t - τ u⌋ : ℤ) : ℝ) := by
          rw [ht'def, Int.fract]; push_cast; ring
        rw [hkey]
        simpa using eq_of_add_intCast_of_periodic hγper t (-(⌊t - τ u⌋ : ℤ))
      by_cases hle : t' ≤ τ (-u) + 1
      · exact ⟨t', ⟨ht'1, hle⟩, hγt'⟩
      · push_neg at hle
        have hmem : t' - 1 ∈ Ioo (τ (-u)) (τ u) := ⟨by linarith, by linarith⟩
        obtain ⟨w, hw, hwt⟩ := F2 (t' - 1) hmem
        refine absurd ⟨w, hw, ?_⟩ hx
        calc α w = γ (τ w) := (hγα w ⟨le_of_lt hw.1, le_of_lt hw.2⟩).symm
          _ = γ (t' - 1) := by rw [hwt]
          _ = γ (t' - 1 + 1) := (hγper (t' - 1)).symm
          _ = γ t' := by rw [show t' - 1 + 1 = t' from by ring]
          _ = γ t := hγt'
    · -- conversely every point of the interval is outside the arc
      rintro x ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, fun hmem => ?_⟩
      obtain ⟨θ, hθ, hγθ⟩ := hstrip1 hmem
      obtain ⟨k, hk⟩ := hγmod t θ hγθ.symm
      have h1 : (0 : ℝ) < (k : ℝ) := by linarith [hk, ht.1, hθ.2]
      have h2 : (k : ℝ) < 1 := by linarith [hk, ht.2, hθ.1, hspan]
      have hk1 : (0 : ℤ) < k := by exact_mod_cast h1
      have hk2 : k < 1 := by exact_mod_cast h2
      omega
  rw [hcompl]
  exact (isPreconnected_Icc (a := τ u) (b := τ (-u) + 1)).image γ hγc.continuousOn

/-- **The complement of a liftable arc in a periodic curve is preconnected.**  As
`isPreconnected_sdiff_arc_of_strictMonoOn`, but the monotonicity is only assumed on the open interval
(and either orientation), which is how the lift `exists_continuous_arcLift` is produced. -/
lemma isPreconnected_sdiff_arc_of_lift {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {α : ℝ → X}
    {τ : ℝ → ℝ} {u : ℝ}
    (hγc : Continuous γ) (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγmod : ∀ x y : ℝ, γ x = γ y → ∃ k : ℤ, x = y + k)
    (hγα : ∀ w ∈ Icc (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u))
    (hτm : StrictMonoOn τ (Icc (-u) u) ∨ StrictAntiOn τ (Icc (-u) u))
    (hu : 0 < u) (hspan : |τ u - τ (-u)| < 1) :
    IsPreconnected (Set.range γ \ α '' Ioo (-u) u) := by
  rcases hτm with hmono | hanti
  · exact isPreconnected_sdiff_arc_of_strictMonoOn hγc hγper hγmod hγα hτc
      hmono hu (abs_lt.mp hspan).2
  · have hτ'm : StrictMonoOn (fun w : ℝ => τ (-w)) (Icc (-u) u) := by
      intro x hx y hy hxy
      have hx' : -y ∈ Icc (-u) u := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have hy' : -x ∈ Icc (-u) u := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      exact hanti hx' hy' (by linarith)
    have hτ'c : ContinuousOn (fun w : ℝ => τ (-w)) (Icc (-u) u) :=
      hτc.comp continuous_neg.continuousOn (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have hγα' : ∀ w ∈ Icc (-u) u, γ ((fun w : ℝ => τ (-w)) w) = (fun w : ℝ => α (-w)) w :=
      fun w hw => hγα (-w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hspan' : (fun w : ℝ => τ (-w)) u - (fun w : ℝ => τ (-w)) (-u) < 1 := by
      have h : τ (-u) - τ u < 1 := by linarith [(abs_lt.mp hspan).1]
      simpa using h
    have hkey := isPreconnected_sdiff_arc_of_strictMonoOn hγc hγper hγmod hγα' hτ'c
      hτ'm hu hspan'
    have hneg : (fun w : ℝ => -w) '' Ioo (-u) u = Ioo (-u) u := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨by linarith [hw.2], by linarith [hw.1]⟩
      · intro hy
        exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp⟩
    have himg : (fun w : ℝ => α (-w)) '' Ioo (-u) u = α '' Ioo (-u) u := by
      rw [show (fun w : ℝ => α (-w)) = α ∘ (fun w : ℝ => -w) from rfl, Set.image_comp, hneg]
    rwa [himg] at hkey

/-- **The lift of an injective arc spans less than one period.**  If the arc `α` is injective on
`[-u,u]` and is lifted by the continuous `τ`, then the two lifts of the endpoints differ by less
than `1` (otherwise the intermediate value theorem produces a coincidence contradicting
injectivity). -/
lemma span_lt_one_of_lift {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {α : ℝ → X} {τ : ℝ → ℝ}
    {u : ℝ} (hγper : ∀ x : ℝ, γ (x + 1) = γ x)
    (hγα : ∀ w ∈ Icc (-u) u, γ (τ w) = α w)
    (hτc : ContinuousOn τ (Icc (-u) u))
    (hαinj : Set.InjOn α (Icc (-u) u)) (hu : 0 < u) :
    τ u - τ (-u) < 1 ∧ τ (-u) - τ u < 1 := by
  have hul : -u ≤ u := by linarith
  have hnegI : -u ∈ Icc (-u) u := ⟨le_rfl, by linarith⟩
  have hposI : u ∈ Icc (-u) u := ⟨by linarith, le_rfl⟩
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw, hwτ⟩ := intermediate_value_Icc hul hτc
      (show τ (-u) + 1 ∈ Icc (τ (-u)) (τ u) from ⟨by linarith, by linarith⟩)
    have h1 : α w = α (-u) := by
      rw [← hγα w hw, hwτ, hγper (τ (-u)), hγα (-u) hnegI]
    have hwneg : w = -u := hαinj hw hnegI h1
    rw [hwneg] at hwτ
    linarith
  · by_contra hcon
    push_neg at hcon
    obtain ⟨w, hw, hwτ⟩ := intermediate_value_Icc' hul hτc
      (show τ u + 1 ∈ Set.Icc (τ u) (τ (-u)) from ⟨by linarith, by linarith⟩)
    have h1 : α w = α u := by
      rw [← hγα w hw, hwτ, hγper (τ u), hγα u hposI]
    have hwpos : w = u := hαinj hw hposI h1
    rw [hwpos] at hwτ
    linarith

end Topology

/-! ## 2. The arc algebra -/

section Arcs

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {S : SaddleChart D}

/-- The lower and left arcs are injective in the parameter, like the upper ones. -/
lemma injOn_arcD (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    Set.InjOn (fun w : ℝ => S.arcD ηs w) (Set.Icc (-2) 2) := by
  intro w hw w' hw' h
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  have hw2' : |w'| ≤ 2 := by rw [abs_le]; exact ⟨hw'.1, hw'.2⟩
  have h3 : S.Zc (S.arcU ηs w) = S.Zc (S.arcU ηs w') := by
    have h4 : S.Zc (S.arcD ηs w) = S.Zc (S.arcD ηs w') := congrArg S.Zc h
    rw [S.arcD_Zc_neg hηs.le hηs1 hw2, S.arcD_Zc_neg hηs.le hηs1 hw2'] at h4
    exact neg_inj.mp h4
  exact S.injOn_arcU hηs hηs1 hw hw'
    (S.injOn_Zc (S.arcU_source hηs.le hηs1 hw2) (S.arcU_source hηs.le hηs1 hw2') h3)

lemma injOn_arcL (S : SaddleChart D) {ηs : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) :
    Set.InjOn (fun w : ℝ => S.arcL ηs w) (Set.Icc (-2) 2) := by
  intro w hw w' hw' h
  have hw2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨hw.1, hw.2⟩
  have hw2' : |w'| ≤ 2 := by rw [abs_le]; exact ⟨hw'.1, hw'.2⟩
  have h3 : S.Zc (S.arcR ηs w) = S.Zc (S.arcR ηs w') := by
    have h4 : S.Zc (S.arcL ηs w) = S.Zc (S.arcL ηs w') := congrArg S.Zc h
    rw [S.arcL_Zc_neg hηs.le hηs1 hw2, S.arcL_Zc_neg hηs.le hηs1 hw2'] at h4
    exact neg_inj.mp h4
  exact S.injOn_arcR hηs hηs1 hw hw'
    (S.injOn_Zc (S.arcR_source hηs.le hηs1 hw2) (S.arcR_source hηs.le hηs1 hw2') h3)

end Arcs

/-! ## 3. The strip of the pin and its classification -/

section Strip

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {S : SaddleChart D}

/-- **The strip of the anchor pin at the cut scale `c`**: the marked model ball of radius `ρ j` cut
by the invariant `|Im (Zc ·)²| < cλ²`, `λ = ρ j / 8`. -/
def pinStrip (D : Work.Drive.N2.WindowDatum f p) (S : SaddleChart D) (c : ℝ) : Set M :=
  {x : M | x ∈ Work.Drive.N2.modelBall S.φ' (D.ρ D.j) ∧
    |((S.Zc x) ^ 2).im| < c * (D.ρ D.j / 8) ^ 2}

/-- **Classification of a point of the strip**: a point of the strip at the anchor level is one of
the two anchor arcs, with `|w| < c`. -/
lemma strip_mem_arc {ηs c : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hcm : c ≤ 99 / 50)
    {x : M} (hxT : x ∈ pinStrip D S c)
    (hxlev : f x = f p - (D.ρ D.j / 8) ^ 2 * ηs) :
    ∃ w : ℝ, |w| < c ∧ (x = S.arcU ηs w ∨ x = S.arcD ηs w) := by
  rw [pinStrip, Set.mem_setOf_eq] at hxT
  obtain ⟨hxball, him⟩ := hxT
  obtain ⟨hxsrc, hxnorm⟩ := hxball
  have hlam2 : 0 < (D.ρ D.j / 8 : ℝ) ^ 2 :=
    pow_pos (div_pos (D.hρ D.j) (by norm_num)) 2
  have hxpin : x ∈ saddlePin D (f p - (D.ρ D.j / 8) ^ 2 * ηs) (99 / 50) := by
    refine ⟨?_, ?_, hxlev, ?_⟩
    · rw [← S.source_eq]; exact hxsrc
    · rw [← S.norm_eq hxsrc]; exact hxnorm
    · rw [← S.Zc_sq_im_abs hxsrc]
      exact le_of_lt (lt_of_lt_of_le him (by nlinarith [hcm, hlam2]))
  obtain ⟨w, hw, hcase⟩ := S.pin_eq_arcs hηs hηs1 (by norm_num) (by norm_num) hxpin
  have hw2 : |w| ≤ 2 := by linarith
  have himw : ((S.Zc x) ^ 2).im = (D.ρ D.j / 8 : ℝ) ^ 2 * w := by
    rcases hcase with h | h
    · rw [h]; exact S.arcU_imSq hηs.le hηs1 hw2
    · rw [h]; exact S.arcD_imSq hηs.le hηs1 hw2
  rw [himw, abs_mul, abs_of_nonneg (le_of_lt hlam2)] at him
  exact ⟨w, by nlinarith [him, hlam2], hcase⟩

end Strip

/-! ## 4. Preconnected arc images and their components -/

section Images

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {S : SaddleChart D}

lemma isPreconnected_arcU_image {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) : IsPreconnected (S.arcU ηs '' Set.Icc (-m) m) :=
  (isPreconnected_Icc (a := -m) (b := m)).image _ ((S.continuousOn_arcU hηs hηs1).mono (fun w hw =>
    ⟨by linarith [hw.1, hm0], by linarith [hw.2, hm2]⟩))

lemma isPreconnected_arcD_image {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) : IsPreconnected (S.arcD ηs '' Set.Icc (-m) m) :=
  (isPreconnected_Icc (a := -m) (b := m)).image _ ((S.continuousOn_arcD hηs hηs1).mono (fun w hw =>
    ⟨by linarith [hw.1, hm0], by linarith [hw.2, hm2]⟩))

lemma isPreconnected_arcR_image {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) : IsPreconnected (S.arcR ηs '' Set.Icc (-m) m) :=
  (isPreconnected_Icc (a := -m) (b := m)).image _ ((S.continuousOn_arcR hηs hηs1).mono (fun w hw =>
    ⟨by linarith [hw.1, hm0], by linarith [hw.2, hm2]⟩))

lemma isPreconnected_arcL_image {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) : IsPreconnected (S.arcL ηs '' Set.Icc (-m) m) :=
  (isPreconnected_Icc (a := -m) (b := m)).image _ ((S.continuousOn_arcL hηs hηs1).mono (fun w hw =>
    ⟨by linarith [hw.1, hm0], by linarith [hw.2, hm2]⟩))

/-- An anchor arc spans a single component of the anchor level. -/
lemma arcU_image_subset_component {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) :
    S.arcU ηs '' Set.Icc (-m) m ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0) := by
  refine (isPreconnected_arcU_image (S := S) hηs hηs1 hm0 hm2).subset_connectedComponentIn
    ⟨0, ⟨by linarith, by linarith⟩, rfl⟩ ?_
  rintro y ⟨w, hw, rfl⟩
  exact S.arcU_level hηs.le hηs1 (by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)

lemma arcD_image_subset_component {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) :
    S.arcD ηs '' Set.Icc (-m) m ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0) := by
  refine (isPreconnected_arcD_image (S := S) hηs hηs1 hm0 hm2).subset_connectedComponentIn
    ⟨0, ⟨by linarith, by linarith⟩, rfl⟩ ?_
  rintro y ⟨w, hw, rfl⟩
  exact S.arcD_level hηs.le hηs1 (by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)

/-- An upper arc spans a single component of the upper level. -/
lemma arcR_image_subset_component {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) :
    S.arcR ηs '' Set.Icc (-m) m ⊆
      connectedComponentIn {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} (S.arcR ηs 0) := by
  refine (isPreconnected_arcR_image (S := S) hηs hηs1 hm0 hm2).subset_connectedComponentIn
    ⟨0, ⟨by linarith, by linarith⟩, rfl⟩ ?_
  rintro y ⟨w, hw, rfl⟩
  exact S.arcR_level hηs.le hηs1 (by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)

lemma arcL_image_subset_component {ηs m : ℝ} (hηs : 0 < ηs) (hηs1 : ηs ≤ 1) (hm0 : 0 ≤ m)
    (hm2 : m ≤ 2) :
    S.arcL ηs '' Set.Icc (-m) m ⊆
      connectedComponentIn {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} (S.arcL ηs 0) := by
  refine (isPreconnected_arcL_image (S := S) hηs hηs1 hm0 hm2).subset_connectedComponentIn
    ⟨0, ⟨by linarith, by linarith⟩, rfl⟩ ?_
  rintro y ⟨w, hw, rfl⟩
  exact S.arcL_level hηs.le hηs1 (by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩)

end Images


open scoped Manifold ContDiff Topology in
/-- **The dichotomy, merge case.**  If the anchor pin (`f p - 3η/2`) is not contained in one
connected component of its level, then the upper pin (`f p + 3η/2`) is.

Route (all ingredients on disk; `S : SaddleChart D` is the canonical chart package of
`Work.Drive.N2Lead.SaddleChart`, and `lam = ρ j / 8`, `ηs = (3η/2)/lam²`):

* the anchor pin is exactly the union of the two arcs `arcU`, `arcD`
  (`Work.Drive.N2Lead.SaddleChart.pin_eq_arcs`), and the upper pin is covered by `arcR`, `arcL`
  (`arcR_mem_pin`, `arcL_mem_pin`); the upper-pin *classification* is the same algebra as
  `pin_eq_arcs`;
* let `K`, `K'` be the components of the anchor level through `arcU 0`, `arcD 0`; the hypothesis
  gives `K ≠ K'`;
* cut the strip by `S.φ'.source`: `K ∩ {x ∈ φ'.source : |Im (Zc x)²| < c₀ λ²} = arcU ((-c₀,c₀))`
  (classification + `K ≠ K'`), hence `K ∖ strip = K ∖ arcU ((-c₀,c₀))`; with the continuous lift `τ`
  of `arcU` along the level curves of the anchor level
  (`Work.Drive.N2Lead.exists_continuous_arcLift`, applied to `arcU` restricted to the range of one
  component curve, using `SaddleChart.continuousOn_arcU`), this set is the image of the interval
  `Icc (τ c₀) (τ (-c₀) + 1)` under the component curve, hence preconnected;
* every point of `K ∖ strip` is a box point (off the model ball of radius `ρ j` or `|Im| ≥ c₀ λ²`),
  so `Work.Drive.N2Lead.landingWide_band` puts its flow image on the upper level (take the band
  parameter `η'` with `ηs < η'` and `λ²η' < 2 ηd`, possible from `hsep` and `hηs'`); the image of
  `K ∖ strip` is therefore a connected subset of the upper level containing
  `Φ (3η, arcU (c₀)) = arcR c₀` and `Φ (3η, arcU (-c₀)) = arcL (-c₀)`
  (`Work.Drive.N2Lead.flow_arcIds`) — so those two points lie in one component of the upper level;
* the same argument with `K'` gives that `Φ (3η, arcD (c₀)) = arcL c₀` and
  `Φ (3η, arcD (-c₀)) = arcR (-c₀)` lie in one component;
* the arcs `arcR ((-2,2))` and `arcL ((-2,2))` are connected in the upper level and carry these four
  points, so the two components coincide, and the whole upper pin is on one component.

## Implementation notes

The bricks below carry the proof:

* `isPreconnected_sdiff_arc_of_strictMonoOn` / `isPreconnected_sdiff_arc_of_lift`: the complement of a
  liftable open arc in a periodic curve is preconnected (the topological core, with the lift
  hypothesis only on the closed interval, which is what `exists_continuous_arcLift` provides);
* `span_lt_one_of_lift`: the lift of an injective arc spans less than one period;
* `pinStrip` and `strip_mem_arc`: the cut of the pin by `|Im (Zc ·)²| < cλ²`;
* `injOn_arcD`, `injOn_arcL`: the missing injectivity rows of the lower/left arcs;
* `*_image_subset_component`, `isPreconnected_*_image`: the arcs lie in single components.

The entity proved in `saddlePin_oneComp_or` uses the cut parameter
`c = (c₀ + (2 - 2δ))/2`, which satisfies `2 - 2δ ≤ c ≤ c₀ ≤ 99/50` and `c < 2`: the lower bound is
what the collar row `flow_arcIds` needs, the upper bounds are what the pin classification
(`|w| < c ≤ 99/50`) and the lift (`Icc (-c) c ⊆ Ioo (-2) 2`) need. -/
theorem saddlePin_split_imp_upper {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j) (S : Work.Drive.N2Lead.SaddleChart D)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {η ηs c₀ δ : ℝ} (hη : 0 < η)
    (hηs : ηs = 3 * η / 2 / (D.ρ D.j / 8) ^ 2)
    (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hηs' : ηs < 1 / 10)
    (hηb' : 2 * η / (D.ρ D.j / 8) ^ 2 < 1 / 10)
    (hc₀lo : 2 - 2 * δ ≤ c₀) (hc₀hi : c₀ ≤ 2) (hc₀m : c₀ ≤ 99 / 50)
    (hsep : (D.ρ D.j / 8) ^ 2 * ηs < 2 * D.ηd)
    (hreg : ∀ x : M, f x = f p - 3 * η / 2 → ¬ Work.Drive.Morse.IsCritical f x)
    (hne : ∃ x : M, f x = f p - 3 * η / 2) :
    ¬ Work.Drive.N2Lead.OnOneComponent (f := f) (f p - 3 * η / 2)
        (Work.Drive.N2Lead.saddlePin D (f p - 3 * η / 2) (99 / 50)) →
    Work.Drive.N2Lead.OnOneComponent (f := f) (f p + 3 * η / 2)
        (Work.Drive.N2Lead.saddlePin D (f p + 3 * η / 2) (99 / 50)) := by
  intro hsplit
  -- ### 0. numerical preliminaries
  have hρ : 0 < D.ρ D.j := D.hρ D.j
  have hlam : (0 : ℝ) < D.ρ D.j / 8 := div_pos hρ (by norm_num)
  have hlam2 : (0 : ℝ) < (D.ρ D.j / 8) ^ 2 := pow_pos hlam 2
  have hηs_pos : 0 < ηs := by
    rw [hηs]; exact div_pos (by linarith) hlam2
  have hηs1 : ηs ≤ 1 := by linarith [hηs']
  have hηsnn : 0 ≤ ηs := le_of_lt hηs_pos
  have hkey : (D.ρ D.j / 8) ^ 2 * ηs = 3 * η / 2 := by
    rw [hηs]; exact mul_div_cancel₀ _ (ne_of_gt hlam2)
  have hdn : f p - 3 * η / 2 = f p - (D.ρ D.j / 8) ^ 2 * ηs := by rw [hkey]
  have hup : f p + 3 * η / 2 = f p + (D.ρ D.j / 8) ^ 2 * ηs := by rw [hkey]
  rw [hdn] at hsplit
  rw [hup]
  -- the cut parameter
  set c : ℝ := (c₀ + (2 - 2 * δ)) / 2 with hcdef
  have hc_ge : 2 - 2 * δ ≤ c := by rw [hcdef]; linarith
  have hc_le : c ≤ c₀ := by rw [hcdef]; linarith
  have hc_lt2 : c < 2 := by rw [hcdef]; linarith
  have hc_gt1 : 1 < c := by rw [hcdef]; linarith
  have hc0 : 0 < c := by linarith
  have hc_m : c ≤ 99 / 50 := le_trans hc_le hc₀m
  -- ### 1. the level curves of the anchor level
  have hreg' : ∀ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * ηs →
      ¬ Work.Drive.Morse.IsCritical f x :=
    fun x hx => hreg x (by rw [hdn]; exact hx)
  have hne' : ∃ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by rw [← hdn]; exact hx⟩
  obtain ⟨n, γ, hsm, hper, hinj, hval, _hze0, hker, hcoverU, hdisj, _hclos, hmod⟩ :=
    Work.Drive.N2.exists_levelComponentCurves f hf (f p - (D.ρ D.j / 8) ^ 2 * ηs) hreg' hne'
  have hcover : ∀ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * ηs →
      ∃ (i : Fin n) (t : ℝ), x = γ i t := by
    intro x hx
    have h1 : x ∈ ⋃ i, Set.range (γ i) := by rw [hcoverU]; exact hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    obtain ⟨t, ht⟩ := hi
    exact ⟨i, t, ht.symm⟩
  obtain ⟨L⟩ := Work.Drive.N2C.levelCurves_ofComponentCurves hsm hper hinj hval hker hcover hdisj
  -- ### 2. the two components of the anchor pin
  have hUlev : f (S.arcU ηs 0) = f p - (D.ρ D.j / 8) ^ 2 * ηs :=
    S.arcU_level hηsnn hηs1 (by norm_num)
  have hDlev : f (S.arcD ηs 0) = f p - (D.ρ D.j / 8) ^ 2 * ηs :=
    S.arcD_level hηsnn hηs1 (by norm_num)
  obtain ⟨iU, tU, htU⟩ := L.cover (S.arcU ηs 0) hUlev
  obtain ⟨iD, tD, htD⟩ := L.cover (S.arcD ηs 0) hDlev
  have hKrange : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
      = Set.range (L.γ iU) := by
    rw [htU]; exact (range_eq_connectedComponentIn L iU tU).symm
  have hK'range : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
      = Set.range (L.γ iD) := by
    rw [htD]; exact (range_eq_connectedComponentIn L iD tD).symm
  -- the arcs inside `K`
  have harcU_sub2 : S.arcU ηs '' Set.Icc (-2) 2 ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0) :=
    arcU_image_subset_component (S := S) hηs_pos hηs1 (by norm_num) (by norm_num)
  have harcD_sub2 : S.arcD ηs '' Set.Icc (-2) 2 ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0) :=
    arcD_image_subset_component (S := S) hηs_pos hηs1 (by norm_num) (by norm_num)
  have hm99 : (99 : ℝ) / 50 ≤ 2 := by norm_num
  have harcU_sub99 : S.arcU ηs '' Set.Icc (-(99 / 50)) (99 / 50) ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0) :=
    arcU_image_subset_component (S := S) hηs_pos hηs1 (by norm_num) hm99
  have harcD_sub99 : S.arcD ηs '' Set.Icc (-(99 / 50)) (99 / 50) ⊆
      connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0) :=
    arcD_image_subset_component (S := S) hηs_pos hηs1 (by norm_num) hm99
  -- the two components are different
  have hne_comp : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
      ≠ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0) := by
    intro heq
    refine hsplit ?_
    intro x hx y hy
    have hmem : ∀ z : M, z ∈ saddlePin D (f p - (D.ρ D.j / 8) ^ 2 * ηs) (99 / 50) →
        z ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0) := by
      intro z hz
      obtain ⟨w, hw, hcase⟩ := S.pin_eq_arcs hηs_pos hηs1 (by norm_num) hm99 hz
      have hw2 : -(99 / 50 : ℝ) ≤ w ∧ w ≤ 99 / 50 := abs_le.mp hw
      rcases hcase with h | h
      · exact harcU_sub99 ⟨w, hw2, h.symm⟩
      · rw [heq]
        exact harcD_sub99 ⟨w, hw2, h.symm⟩
    rw [← connectedComponentIn_eq (hmem x hx)]
    exact hmem y hy
  -- ### 3. the strip meets `K` exactly in the open arc
  have hstrip_arc : ∀ {x : M} (hxK : x ∈ connectedComponentIn
        {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)) (hxT : x ∈ pinStrip D S c),
      ∃ w : ℝ, |w| < c ∧ x = S.arcU ηs w := by
    intro x hxK hxT
    have hxlev : f x = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
      simpa using connectedComponentIn_subset {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcU ηs 0) hxK
    obtain ⟨w, hw, hcase⟩ := strip_mem_arc (S := S) hηs_pos hηs1 hc_m hxT hxlev
    have hw2 : -(99 / 50 : ℝ) ≤ w ∧ w ≤ 99 / 50 := abs_le.mp (le_of_lt (lt_of_lt_of_le hw hc_m))
    rcases hcase with h | h
    · exact ⟨w, hw, h⟩
    · exfalso
      have hxK' : x ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
          (S.arcD ηs 0) :=
        harcD_sub99 ⟨w, hw2, h.symm⟩
      exact hne_comp ((connectedComponentIn_eq hxK).trans (connectedComponentIn_eq hxK').symm)
  have hinterU : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
      ∩ pinStrip D S c = S.arcU ηs '' Set.Ioo (-c) c := by
    ext x
    constructor
    · rintro ⟨hxK, hxT⟩
      obtain ⟨w, hw, hwU⟩ := hstrip_arc hxK hxT
      exact ⟨w, abs_lt.mp hw, hwU.symm⟩
    · rintro ⟨w, hw, rfl⟩
      have h2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2, hc_lt2]⟩
      obtain ⟨hsrcJ, hnormJ, -, -⟩ := S.arcU_mem_pin hηsnn hηs1 (by norm_num) hm99 (w := w)
        (by rw [abs_le]; exact ⟨by linarith [hw.1, hc_m], by linarith [hw.2, hc_m]⟩)
      have hsrc : S.arcU ηs w ∈ S.φ'.source := by rw [S.source_eq]; exact hsrcJ
      have hnorm : ‖S.φ' (S.arcU ηs w)‖ < D.ρ D.j := by rw [S.norm_eq hsrc]; exact hnormJ
      refine ⟨harcU_sub2 ⟨w, ⟨by linarith [hw.1], by linarith [hw.2, hc_lt2]⟩, rfl⟩, ?_, ?_⟩
      · exact ⟨hsrc, hnorm⟩
      · rw [S.arcU_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2)]
        have hwabs : |w| < c := abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
        nlinarith [hwabs, hlam2]
  have hstrip_arcD : ∀ {x : M} (hxK : x ∈ connectedComponentIn
        {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)) (hxT : x ∈ pinStrip D S c),
      ∃ w : ℝ, |w| < c ∧ x = S.arcD ηs w := by
    intro x hxK hxT
    have hxlev : f x = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
      simpa using connectedComponentIn_subset {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcD ηs 0) hxK
    obtain ⟨w, hw, hcase⟩ := strip_mem_arc (S := S) hηs_pos hηs1 hc_m hxT hxlev
    have hw2 : -(99 / 50 : ℝ) ≤ w ∧ w ≤ 99 / 50 := abs_le.mp (le_of_lt (lt_of_lt_of_le hw hc_m))
    rcases hcase with h | h
    · exfalso
      have hxK' : x ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
          (S.arcU ηs 0) :=
        harcU_sub99 ⟨w, hw2, h.symm⟩
      exact hne_comp ((connectedComponentIn_eq hxK').trans (connectedComponentIn_eq hxK).symm)
    · exact ⟨w, hw, h⟩
  have hinterD : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
      ∩ pinStrip D S c = S.arcD ηs '' Set.Ioo (-c) c := by
    ext x
    constructor
    · rintro ⟨hxK, hxT⟩
      obtain ⟨w, hw, hwU⟩ := hstrip_arcD hxK hxT
      exact ⟨w, abs_lt.mp hw, hwU.symm⟩
    · rintro ⟨w, hw, rfl⟩
      have h2 : |w| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hw.1], by linarith [hw.2, hc_lt2]⟩
      obtain ⟨hsrcJ, hnormJ, -, -⟩ := S.arcD_mem_pin hηsnn hηs1 (by norm_num) hm99 (w := w)
        (by rw [abs_le]; exact ⟨by linarith [hw.1, hc_m], by linarith [hw.2, hc_m]⟩)
      have hsrc : S.arcD ηs w ∈ S.φ'.source := by rw [S.source_eq]; exact hsrcJ
      have hnorm : ‖S.φ' (S.arcD ηs w)‖ < D.ρ D.j := by rw [S.norm_eq hsrc]; exact hnormJ
      refine ⟨harcD_sub2 ⟨w, ⟨by linarith [hw.1], by linarith [hw.2, hc_lt2]⟩, rfl⟩, ?_, ?_⟩
      · exact ⟨hsrc, hnorm⟩
      · rw [S.arcD_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2)]
        have hwabs : |w| < c := abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
        nlinarith [hwabs, hlam2]
  -- ### 4. the complement of the strip in a component is preconnected
  have hpreU : IsPreconnected (Set.range (L.γ iU) \ S.arcU ηs '' Set.Ioo (-c) c) := by
    have hJα : ∀ w ∈ Set.Ioo (-2) 2, S.arcU ηs w ∈ Set.range (L.γ iU) := by
      intro w hw
      rw [← hKrange]
      exact harcU_sub2 ⟨w, ⟨le_of_lt hw.1, le_of_lt hw.2⟩, rfl⟩
    obtain ⟨τ, hτcont, hτlift⟩ := exists_continuous_arcLift L iU isOpen_Ioo
      (isPreconnected_Ioo (a := (-2 : ℝ)) (b := 2))
      ((S.continuousOn_arcU hηs_pos hηs1).mono Ioo_subset_Icc_self) hJα
    have hsubIc : Set.Icc (-c) c ⊆ Set.Ioo (-2) 2 := fun w hw =>
      ⟨by linarith [hw.1, hc_lt2], by linarith [hw.2, hc_lt2]⟩
    have hτc : ContinuousOn τ (Set.Icc (-c) c) := hτcont.mono hsubIc
    have hγα : ∀ w ∈ Set.Icc (-c) c, L.γ iU (τ w) = S.arcU ηs w := fun w hw => hτlift w (hsubIc hw)
    have hsubI2 : Set.Icc (-c) c ⊆ Set.Icc (-2) 2 := fun w hw =>
      ⟨by linarith [hw.1, hc_lt2], by linarith [hw.2, hc_lt2]⟩
    have hαinj : Set.InjOn (fun w : ℝ => S.arcU ηs w) (Set.Icc (-c) c) :=
      (S.injOn_arcU hηs_pos hηs1).mono hsubI2
    have hτinj : Set.InjOn τ (Set.Icc (-c) c) := by
      intro w hw w' hw' h
      exact hαinj hw hw' (by
        show S.arcU ηs w = S.arcU ηs w'
        rw [← hγα w hw, ← hγα w' hw', h])
    have hτm := hτc.strictMonoOn_of_injOn_Icc' (a := -c) (b := c) (by linarith) hτinj
    have hpair := span_lt_one_of_lift (L.per iU) hγα hτc hαinj hc0
    have hspan : |τ c - τ (-c)| < 1 := by
      rw [abs_lt]
      exact ⟨by linarith [hpair.2], hpair.1⟩
    exact isPreconnected_sdiff_arc_of_lift (L.sm iU).continuous (L.per iU) (L.modOne iU)
      hγα hτc hτm hc0 hspan
  have hpreD : IsPreconnected (Set.range (L.γ iD) \ S.arcD ηs '' Set.Ioo (-c) c) := by
    have hJα : ∀ w ∈ Set.Ioo (-2) 2, S.arcD ηs w ∈ Set.range (L.γ iD) := by
      intro w hw
      rw [← hK'range]
      exact harcD_sub2 ⟨w, ⟨le_of_lt hw.1, le_of_lt hw.2⟩, rfl⟩
    obtain ⟨τ, hτcont, hτlift⟩ := exists_continuous_arcLift L iD isOpen_Ioo
      (isPreconnected_Ioo (a := (-2 : ℝ)) (b := 2))
      ((S.continuousOn_arcD hηs_pos hηs1).mono Ioo_subset_Icc_self) hJα
    have hsubIc : Set.Icc (-c) c ⊆ Set.Ioo (-2) 2 := fun w hw =>
      ⟨by linarith [hw.1, hc_lt2], by linarith [hw.2, hc_lt2]⟩
    have hτc : ContinuousOn τ (Set.Icc (-c) c) := hτcont.mono hsubIc
    have hγα : ∀ w ∈ Set.Icc (-c) c, L.γ iD (τ w) = S.arcD ηs w := fun w hw => hτlift w (hsubIc hw)
    have hsubI2 : Set.Icc (-c) c ⊆ Set.Icc (-2) 2 := fun w hw =>
      ⟨by linarith [hw.1, hc_lt2], by linarith [hw.2, hc_lt2]⟩
    have hαinj : Set.InjOn (fun w : ℝ => S.arcD ηs w) (Set.Icc (-c) c) :=
      (injOn_arcD S hηs_pos hηs1).mono hsubI2
    have hτinj : Set.InjOn τ (Set.Icc (-c) c) := by
      intro w hw w' hw' h
      exact hαinj hw hw' (by
        show S.arcD ηs w = S.arcD ηs w'
        rw [← hγα w hw, ← hγα w' hw', h])
    have hτm := hτc.strictMonoOn_of_injOn_Icc' (a := -c) (b := c) (by linarith) hτinj
    have hpair := span_lt_one_of_lift (L.per iD) hγα hτc hαinj hc0
    have hspan : |τ c - τ (-c)| < 1 := by
      rw [abs_lt]
      exact ⟨by linarith [hpair.2], hpair.1⟩
    exact isPreconnected_sdiff_arc_of_lift (L.sm iD).continuous (L.per iD) (L.modOne iD)
      hγα hτc hτm hc0 hspan
  -- ### 5. the flow sends `K ∖ strip` and `K' ∖ strip` to the upper level
  set ηb : ℝ := (ηs + min (1 / 10) (2 * D.ηd / (D.ρ D.j / 8) ^ 2)) / 2 with hηbdef
  have hηb_gt : ηs < ηb := by
    have h1 : ηs < 2 * D.ηd / (D.ρ D.j / 8) ^ 2 := by
      rw [lt_div_iff₀ hlam2]; linarith [hsep]
    rw [hηbdef]; linarith [lt_min hηs' h1]
  have hηb_pos : 0 < ηb := lt_trans hηs_pos hηb_gt
  have hηb_lt : ηb < 1 / 10 := by
    rw [hηbdef]; linarith [hηs', min_le_left (1 / 10) (2 * D.ηd / (D.ρ D.j / 8) ^ 2)]
  have hηb_sep : (D.ρ D.j / 8) ^ 2 * ηb < 2 * D.ηd := by
    have h1 : ηb < 2 * D.ηd / (D.ρ D.j / 8) ^ 2 := by
      rw [hηbdef]
      linarith [hηs', hηb_gt, min_le_right (1 / 10) (2 * D.ηd / (D.ρ D.j / 8) ^ 2),
        min_le_left (1 / 10) (2 * D.ηd / (D.ρ D.j / 8) ^ 2)]
    calc (D.ρ D.j / 8) ^ 2 * ηb < (D.ρ D.j / 8) ^ 2 * (2 * D.ηd / (D.ρ D.j / 8) ^ 2) :=
          mul_lt_mul_of_pos_left h1 hlam2
      _ = 2 * D.ηd := by field_simp
  have hland : ∀ x : M, x ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcU ηs 0) → x ∉ pinStrip D S c →
      f (D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) = f p + (D.ρ D.j / 8) ^ 2 * ηs := by
    intro x hxK hxT
    have hxlev : f x = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
      simpa using connectedComponentIn_subset {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcU ηs 0) hxK
    have hbox : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
        c * (D.ρ D.j / 8) ^ 2 ≤ |((S.Zc x) ^ 2).im| := by
      by_contra hcon
      rw [not_or] at hcon
      push_neg at hcon
      exact hxT ⟨by rw [S.ball_eq]; exact hcon.1, hcon.2⟩
    exact landingWide_band D hsgn S.φ' S.Zc (D.ρ D.j / 8) rfl S.source_eq S.ball_eq S.Zc_eq
      (fun y hy => S.level_eq y (by rw [S.source_eq]; exact hy)) S.im_inv hηb_pos hηb_lt hc_gt1
      hηb_sep hbox
      (by rw [hxlev]; exact ⟨by nlinarith [hlam2, hηs_pos, hηb_gt], by nlinarith [hlam2, hηb_pos]⟩)
      (by exact ⟨by nlinarith [hlam2, hηs_pos, hηb_gt], by nlinarith [hlam2, hηb_pos]⟩)
  have hlandD : ∀ x : M, x ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcD ηs 0) → x ∉ pinStrip D S c →
      f (D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) = f p + (D.ρ D.j / 8) ^ 2 * ηs := by
    intro x hxK hxT
    have hxlev : f x = f p - (D.ρ D.j / 8) ^ 2 * ηs := by
      simpa using connectedComponentIn_subset {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
        (S.arcD ηs 0) hxK
    have hbox : x ∉ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∨
        c * (D.ρ D.j / 8) ^ 2 ≤ |((S.Zc x) ^ 2).im| := by
      by_contra hcon
      rw [not_or] at hcon
      push_neg at hcon
      exact hxT ⟨by rw [S.ball_eq]; exact hcon.1, hcon.2⟩
    exact landingWide_band D hsgn S.φ' S.Zc (D.ρ D.j / 8) rfl S.source_eq S.ball_eq S.Zc_eq
      (fun y hy => S.level_eq y (by rw [S.source_eq]; exact hy)) S.im_inv hηb_pos hηb_lt hc_gt1
      hηb_sep hbox
      (by rw [hxlev]; exact ⟨by nlinarith [hlam2, hηs_pos, hηb_gt], by nlinarith [hlam2, hηb_pos]⟩)
      (by exact ⟨by nlinarith [hlam2, hηs_pos, hηb_gt], by nlinarith [hlam2, hηb_pos]⟩)
  -- ### 6. the images of `K ∖ strip` and `K' ∖ strip` lie on the upper level
  have hcontΦ : Continuous (fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) :=
    D.hΦsm.continuous.comp ((continuous_const.sub hf.continuous).prodMk continuous_id)
  have hKdiff : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
      \ pinStrip D S c = Set.range (L.γ iU) \ S.arcU ηs '' Set.Ioo (-c) c := by
    have h1 : Set.range (L.γ iU) ∩ pinStrip D S c = S.arcU ηs '' Set.Ioo (-c) c := by
      rw [← hKrange]; exact hinterU
    rw [hKrange, ← h1]
    ext x
    constructor
    · rintro ⟨hxK, hxT⟩
      exact ⟨hxK, fun hxint => hxT hxint.2⟩
    · rintro ⟨hxK, hxT⟩
      exact ⟨hxK, fun hxint => hxT ⟨hxK, hxint⟩⟩
  have hK'diff : connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
      \ pinStrip D S c = Set.range (L.γ iD) \ S.arcD ηs '' Set.Ioo (-c) c := by
    have h1 : Set.range (L.γ iD) ∩ pinStrip D S c = S.arcD ηs '' Set.Ioo (-c) c := by
      rw [← hK'range]; exact hinterD
    rw [hK'range, ← h1]
    ext x
    constructor
    · rintro ⟨hxK, hxT⟩
      exact ⟨hxK, fun hxint => hxT hxint.2⟩
    · rintro ⟨hxK, hxT⟩
      exact ⟨hxK, fun hxint => hxT ⟨hxK, hxint⟩⟩
  have hWu_pre : IsPreconnected ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
        \ pinStrip D S c)) := by
    rw [hKdiff]
    exact hpreU.image _ hcontΦ.continuousOn
  have hWu_lev : ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
        \ pinStrip D S c)) ⊆ {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
    rintro z ⟨x, hx, rfl⟩
    exact hland x hx.1 hx.2
  have hWv_pre : IsPreconnected ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
        \ pinStrip D S c)) := by
    rw [hK'diff]
    exact hpreD.image _ hcontΦ.continuousOn
  have hWv_lev : ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
        \ pinStrip D S c)) ⊆ {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
    rintro z ⟨x, hx, rfl⟩
    exact hlandD x hx.1 hx.2
  -- ### 7. the four flow identifications of the arc endpoints
  have hflow := flow_arcIds D hsgn S hη hηs hδ hδ' hηs' hηb' (c₀ := c) hc_ge (le_of_lt hc_lt2)
  obtain ⟨hflowR, hflowL, hflowL', hflowR'⟩ := hflow
  -- the four endpoints are box points of their components
  have hmemU : S.arcU ηs c ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
      (S.arcU ηs 0) \ pinStrip D S c := by
    refine ⟨harcU_sub2 ⟨c, ⟨by linarith, le_of_lt hc_lt2⟩, rfl⟩, fun hT => ?_⟩
    have h2 : |c| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, le_of_lt hc_lt2⟩
    have him := hT.2
    rw [S.arcU_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2), abs_of_pos hc0] at him
    nlinarith [him, hlam2]
  have hmemU' : S.arcU ηs (-c) ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
      (S.arcU ηs 0) \ pinStrip D S c := by
    refine ⟨harcU_sub2 ⟨-c, ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩, rfl⟩, fun hT => ?_⟩
    have h2 : |-c| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩
    have him := hT.2
    rw [S.arcU_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2), abs_neg,
      abs_of_pos hc0] at him
    nlinarith [him, hlam2]
  have hmemD : S.arcD ηs c ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
      (S.arcD ηs 0) \ pinStrip D S c := by
    refine ⟨harcD_sub2 ⟨c, ⟨by linarith, le_of_lt hc_lt2⟩, rfl⟩, fun hT => ?_⟩
    have h2 : |c| ≤ 2 := by rw [abs_le]; exact ⟨by linarith, le_of_lt hc_lt2⟩
    have him := hT.2
    rw [S.arcD_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2), abs_of_pos hc0] at him
    nlinarith [him, hlam2]
  have hmemD' : S.arcD ηs (-c) ∈ connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs}
      (S.arcD ηs 0) \ pinStrip D S c := by
    refine ⟨harcD_sub2 ⟨-c, ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩, rfl⟩, fun hT => ?_⟩
    have h2 : |-c| ≤ 2 := by rw [abs_le]; exact ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩
    have him := hT.2
    rw [S.arcD_imSq hηsnn hηs1 h2, abs_mul, abs_of_nonneg (le_of_lt hlam2), abs_neg,
      abs_of_pos hc0] at him
    nlinarith [him, hlam2]
  -- ### 8. the flow images meet at the four upper arc points
  have harcRc_mem : S.arcR ηs c ∈ (fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
        \ pinStrip D S c) := by
    refine ⟨S.arcU ηs c, hmemU, ?_⟩
    show D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcU ηs c), S.arcU ηs c) = S.arcR ηs c
    have ht : f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcU ηs c) = 3 * η := by
      rw [S.arcU_level hηsnn hηs1 (by rw [abs_le]; exact ⟨by linarith, le_of_lt hc_lt2⟩), hkey]
      ring
    rw [ht, hflowR]
  have harcL_negc_mem : S.arcL ηs (-c) ∈ (fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
        \ pinStrip D S c) := by
    refine ⟨S.arcU ηs (-c), hmemU', ?_⟩
    show D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcU ηs (-c)), S.arcU ηs (-c)) = S.arcL ηs (-c)
    have ht : f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcU ηs (-c)) = 3 * η := by
      rw [S.arcU_level hηsnn hηs1
        (by rw [abs_le]; exact ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩), hkey]
      ring
    rw [ht, hflowL]
  have harcLc_mem : S.arcL ηs c ∈ (fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
        \ pinStrip D S c) := by
    refine ⟨S.arcD ηs c, hmemD, ?_⟩
    show D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcD ηs c), S.arcD ηs c) = S.arcL ηs c
    have ht : f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcD ηs c) = 3 * η := by
      rw [S.arcD_level hηsnn hηs1 (by rw [abs_le]; exact ⟨by linarith, le_of_lt hc_lt2⟩), hkey]
      ring
    rw [ht, hflowL']
  have harcR_negc_mem : S.arcR ηs (-c) ∈ (fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
        \ pinStrip D S c) := by
    refine ⟨S.arcD ηs (-c), hmemD', ?_⟩
    show D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcD ηs (-c)), S.arcD ηs (-c)) = S.arcR ηs (-c)
    have ht : f p + (D.ρ D.j / 8) ^ 2 * ηs - f (S.arcD ηs (-c)) = 3 * η := by
      rw [S.arcD_level hηsnn hηs1
        (by rw [abs_le]; exact ⟨by linarith [hc_lt2], by linarith [hc_gt1]⟩), hkey]
      ring
    rw [ht, hflowR']
  -- ### 9. the components
  set Z := connectedComponentIn {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} (S.arcR ηs c) with hZdef
  have hWu_sub : ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcU ηs 0)
        \ pinStrip D S c)) ⊆ Z := hWu_pre.subset_connectedComponentIn harcRc_mem hWu_lev
  have harcL_negc_mem_Z : S.arcL ηs (-c) ∈ Z := hWu_sub harcL_negc_mem
  set Z' := connectedComponentIn {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} (S.arcR ηs (-c))
    with hZ'def
  have hWv_sub : ((fun x : M => D.Φ (f p + (D.ρ D.j / 8) ^ 2 * ηs - f x, x)) ''
      (connectedComponentIn {z : M | f z = f p - (D.ρ D.j / 8) ^ 2 * ηs} (S.arcD ηs 0)
        \ pinStrip D S c)) ⊆ Z' := hWv_pre.subset_connectedComponentIn harcR_negc_mem hWv_lev
  have harcLc_mem_Z' : S.arcL ηs c ∈ Z' := hWv_sub harcLc_mem
  -- the upper arcs are connected inside the level
  have harcR_negc_mem_Z : S.arcR ηs (-c) ∈ Z := by
    have hbase : S.arcR ηs c ∈ S.arcR ηs '' Set.Icc (-c) c :=
      ⟨c, ⟨by linarith, le_rfl⟩, rfl⟩
    have hlevel : S.arcR ηs '' Set.Icc (-c) c ⊆
        {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
      rintro y ⟨u, hu, rfl⟩
      exact S.arcR_level hηsnn hηs1
        (by rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2, hc_lt2]⟩)
    have hsub := (isPreconnected_arcR_image (S := S) hηs_pos hηs1 (le_of_lt hc0) (le_of_lt hc_lt2)).subset_connectedComponentIn
      hbase hlevel
    rw [hZdef]
    exact hsub ⟨-c, ⟨by linarith, by linarith [hc_gt1]⟩, rfl⟩
  have hZ'eq : Z' = Z := by
    rw [hZdef, hZ'def]
    exact (connectedComponentIn_eq harcR_negc_mem_Z).symm
  have harcLc_mem_Z : S.arcL ηs c ∈ Z := by
    rw [← hZ'eq]
    exact harcLc_mem_Z'
  -- ### 10. the whole upper pin lies in `Z`
  refine fun x hx y hy => ?_
  have hmemZ : ∀ z ∈ saddlePin D (f p + (D.ρ D.j / 8) ^ 2 * ηs) (99 / 50), z ∈ Z := by
    intro z hz
    obtain ⟨w, hw, hcase⟩ := pinUpEqArcs D S hηs_pos hηs1 (by norm_num) hm99 hz
    rcases hcase with h | h
    · have hbase : S.arcR ηs c ∈ S.arcR ηs '' Set.Icc (-(99 / 50)) (99 / 50) :=
        ⟨c, ⟨by linarith, hc_m⟩, rfl⟩
      have hlevel : S.arcR ηs '' Set.Icc (-(99 / 50)) (99 / 50) ⊆
          {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
        rintro y ⟨u, hu, rfl⟩
        exact S.arcR_level hηsnn hηs1 (by rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      have hsub := (isPreconnected_arcR_image (S := S) hηs_pos hηs1 (by norm_num) hm99).subset_connectedComponentIn
        hbase hlevel
      rw [h, hZdef]
      exact hsub ⟨w, abs_le.mp hw, rfl⟩
    · have hbase : S.arcL ηs c ∈ S.arcL ηs '' Set.Icc (-(99 / 50)) (99 / 50) :=
        ⟨c, ⟨by linarith, hc_m⟩, rfl⟩
      have hlevel : S.arcL ηs '' Set.Icc (-(99 / 50)) (99 / 50) ⊆
          {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
        rintro y ⟨u, hu, rfl⟩
        exact S.arcL_level hηsnn hηs1 (by rw [abs_le]; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      have hsub := (isPreconnected_arcL_image (S := S) hηs_pos hηs1 (by norm_num) hm99).subset_connectedComponentIn
        hbase hlevel
      have h2 : connectedComponentIn {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} (S.arcL ηs c) = Z := by
        rw [hZdef]
        exact (connectedComponentIn_eq harcLc_mem_Z).symm
      rw [h2] at hsub
      rw [h]
      exact hsub ⟨w, abs_le.mp hw, rfl⟩
  have hZsub : Z ⊆ {z : M | f z = f p + (D.ρ D.j / 8) ^ 2 * ηs} := by
    rw [hZdef]
    exact connectedComponentIn_subset _ _
  have hZpre : IsPreconnected Z := by
    rw [hZdef]
    exact isPreconnected_connectedComponentIn
  exact (hZpre.subset_connectedComponentIn (hmemZ x hx) hZsub) (hmemZ y hy)

end Work.Drive.N2Lead
