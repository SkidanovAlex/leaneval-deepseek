/-
  Own copy of `Work.WilG1.OneDim.oneDim_thin` (which is proved in the workspace but
  rests on the two `sorry`s `Work.WilG1.Thin.osc_mem` and `Work.WilG1.Thin.disc_mem`).
  Here the oscillation sets' `Ω`-membership is the one proved in this directory
  (`Work.WilG4bF.oscRL_mem`), and the finiteness of the discontinuity set is taken from
  `Work.WilG4b.nd_cont_off_finite` (also proved, by sharp cell decomposition).
-/
/-
  WilG1 / OneDim / oneDim_thin

  `interior {x | ¬ DifferentiableAt ℝ g x} = ∅` for a function whose graph is `Ω`-definable.

  The proof proceeds in four steps.

  * The set of discontinuities is countable (its points lie in the boundaries of the level
    sets of `g`, and those boundaries are finite because the level sets are `Ω`-definable,
    hence finite unions of intervals).
  * It is also `Ω`-definable, hence (being countable) finite.
  * Hence any interval of non-differentiability carries a non-degenerate interval of
    continuity.
  * On an interval of continuity, the non-differentiability set is covered by the
    oscillation sets, the corner sets and the two infinite-derivative sets: the oscillation
    and infinite-derivative sets are `Ω`-definable and contain no subinterval, so they meet
    the interval in a finite set; the corner sets are countable.  A countable union of finite
    (resp. countable) sets cannot cover an interval.
-/
import Submission.Work.WilG1.OneDim.thin_assemble
import Submission.Work.WilG4b.oscRL_memAux
import Submission.Work.WilG4b.nd_cont_off_finite
import Submission.Work.WilG1.OneDim.thin_cover
import Submission.Work.WilG1.OneDim.thin_corner
import Submission.Work.WilG1.Analysis.no_deriv_atTop_interval
import Submission.Work.WilG1.OneDim.infDeriv_mem
import Submission.Work.WilG1.Thin.level_mem
import Submission.Work.WilG1.Thin.boundary_finite

set_option autoImplicit false
noncomputable section
open Classical Filter

namespace Work.WilG4bF

open Work.WilG1 Work.WilG1.OneDim

open WilkiesDesign

theorem oneDim_thin {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    interior {x : ℝ | ¬ DifferentiableAt ℝ g x} = ∅ := by
  classical
  obtain ⟨Kosc, posc, hosc⟩ := oscRL_mem (S := S) (F := F) (D := D) g hg
  -- (0) the discontinuity set is finite
  have hfinDsc : ({x : ℝ | ¬ ContinuousAt g x} : Set ℝ).Finite :=
    Work.WilG4b.nd_cont_off_finite S hcd g hg
  -- (3) suppose the non-differentiability set has non-empty interior
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  set c : ℝ := x₀ - ε with hc
  set d : ℝ := x₀ + ε with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hsubB : Set.Ioo c d ⊆ {x : ℝ | ¬ DifferentiableAt ℝ g x} := by
    intro x hx
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have h1 := hx.1
    have h2 := hx.2
    rw [hc] at h1
    rw [hd] at h2
    exact ⟨by linarith, by linarith⟩
  -- (4) an interval of continuity inside `(c,d)`
  have hex : ∃ t : ℝ, t ∈ Set.Ioo c d ∧ t ∉ {x : ℝ | ¬ ContinuousAt g x} := by
    by_contra hcon
    push_neg at hcon
    have : (Set.Ioo c d).Countable := hfinDsc.countable.mono hcon
    exact not_countable_Ioo hcd this
  obtain ⟨t, ht, htD⟩ := hex
  have hclosed : IsClosed ({x : ℝ | ¬ ContinuousAt g x} : Set ℝ) := hfinDsc.isClosed
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl t htD
  have hminpos : 0 < min r₁ (min (t - c) (d - t)) :=
    lt_min hr₁ (lt_min (by linarith [ht.1]) (by linarith [ht.2]))
  set r : ℝ := min r₁ (min (t - c) (d - t)) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrle : r ≤ r₁ := by
    rw [hr]
    have h1 : min r₁ (min (t - c) (d - t)) ≤ r₁ := min_le_left _ _
    linarith
  have hrlt₁ : r < t - c := by
    rw [hr]
    have h1 : min r₁ (min (t - c) (d - t)) ≤ min (t - c) (d - t) := min_le_right _ _
    have h2 : min (t - c) (d - t) ≤ t - c := min_le_left _ _
    linarith
  have hrlt₂ : r < d - t := by
    rw [hr]
    have h1 : min r₁ (min (t - c) (d - t)) ≤ min (t - c) (d - t) := min_le_right _ _
    have h2 : min (t - c) (d - t) ≤ d - t := min_le_right _ _
    linarith
  set c' : ℝ := t - r with hc'
  set d' : ℝ := t + r with hd'
  have hc'd' : c' < d' := by rw [hc', hd']; linarith
  have hcont' : ∀ x ∈ Set.Ioo c' d', ContinuousAt g x := by
    intro x hx
    have hxball : x ∈ Metric.ball t r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      rw [hc'] at hx
      rw [hd'] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact not_not.mp (hr₁sub (Metric.ball_subset_ball hrle hxball))
  have hsubB' : Set.Ioo c' d' ⊆ {x : ℝ | ¬ DifferentiableAt ℝ g x} := by
    intro x hx
    apply hsubB
    rw [hc'] at hx
    rw [hd'] at hx
    exact ⟨by linarith [hx.1, hrlt₁], by linarith [hx.2, hrlt₂]⟩
  -- (5) no subinterval of `(c',d')` is a piece with infinite derivative
  have hnoInf1 : ∀ u v : ℝ, c' ≤ u → u < v → v ≤ d' → Set.Ioo u v ⊆ infDeriv g 1 → False := by
    intro u v hcu huv hvd hsub
    have hcont_uv : ∀ x ∈ Set.Ioo u v, ContinuousAt g x := fun x hx =>
      hcont' x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩
    have hlim : ∀ x ∈ Set.Ioo u v,
        Tendsto (fun y : ℝ => (g y - g x) / (y - x)) (nhdsWithin x {x}ᶜ) atTop := by
      intro x hx
      have hxinf : x ∈ infDeriv g 1 := hsub hx
      rw [Filter.tendsto_atTop]
      intro A
      obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ, 1 < M ∧ A ≤ M :=
        ⟨max A 2, by linarith [le_max_right A 2], le_max_left A 2⟩
      obtain ⟨δ, hδ, hδ'⟩ := hxinf M hM1
      filter_upwards [self_mem_nhdsWithin (s := {x}ᶜ), nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
        with y hyne hyball
      have hyx : |y - x| < δ := by rw [← Real.dist_eq]; exact hyball
      have hMlt : M < dq g x y := by simpa using hδ' y hyne hyx
      exact le_trans hM2 (le_of_lt hMlt)
    have hsingle := Work.WilG1.Analysis.no_deriv_atTop_interval
      (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) hcont_uv hlim
    have h1 : u + (v - u)/3 ∈ Set.Ioo u v := ⟨by linarith, by linarith⟩
    have h2 : u + 2*(v - u)/3 ∈ Set.Ioo u v := ⟨by linarith, by linarith⟩
    have hsub' : u + (v - u)/3 = u + 2*(v - u)/3 := hsingle h1 h2
    linarith
  have hnoInf2 : ∀ u v : ℝ, c' ≤ u → u < v → v ≤ d' → Set.Ioo u v ⊆ infDeriv g (-1) → False := by
    intro u v hcu huv hvd hsub
    have hcont_uv : ∀ x ∈ Set.Ioo u v, ContinuousAt (fun y : ℝ => -g y) x := fun x hx =>
      (hcont' x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩).neg
    have hlim : ∀ x ∈ Set.Ioo u v,
        Tendsto (fun y : ℝ => ((-g y) - (-g x)) / (y - x)) (nhdsWithin x {x}ᶜ) atTop := by
      intro x hx
      have hxinf : x ∈ infDeriv g (-1) := hsub hx
      rw [Filter.tendsto_atTop]
      intro A
      obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ, 1 < M ∧ A ≤ M :=
        ⟨max A 2, by linarith [le_max_right A 2], le_max_left A 2⟩
      obtain ⟨δ, hδ, hδ'⟩ := hxinf M hM1
      filter_upwards [self_mem_nhdsWithin (s := {x}ᶜ), nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
        with y hyne hyball
      have hyx : |y - x| < δ := by rw [← Real.dist_eq]; exact hyball
      have hMlt : M < (-1 : ℝ) * dq g x y := hδ' y hyne hyx
      have hle : M ≤ ((-g y) - (-g x)) / (y - x) := by
        have h2 : M ≤ - dq g x y := by linarith
        rw [dq] at h2
        have h3 : -((g y - g x) / (y - x)) = ((-g y) - (-g x)) / (y - x) := by ring
        linarith [h3]
      exact le_trans hM2 hle
    have hsingle := Work.WilG1.Analysis.no_deriv_atTop_interval
      (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) hcont_uv hlim
    have h1 : u + (v - u)/3 ∈ Set.Ioo u v := ⟨by linarith, by linarith⟩
    have h2 : u + 2*(v - u)/3 ∈ Set.Ioo u v := ⟨by linarith, by linarith⟩
    have hsub' : u + (v - u)/3 = u + 2*(v - u)/3 := hsingle h1 h2
    linarith
  -- (6) the cover of `(c',d')`
  have hcover : Set.Ioo c' d' ⊆
      (⋃ q : ℚ, (oscR g (q:ℝ) ∪ oscL g (q:ℝ) ∪ cornerMax g (q:ℝ) ∪ cornerMin g (q:ℝ))) ∪
        infDeriv g 1 ∪ infDeriv g (-1) := by
    intro x hx
    have hbad : ¬ DifferentiableAt ℝ g x := hsubB' hx
    rcases bad_covered_cont hbad with ⟨q, hq⟩ | ⟨q, hq⟩ | h1 | h2
    · rcases hq with hq | hq
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inl hq))⟩))
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inr hq))⟩))
    · rcases hq with hq | hq
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inr hq)⟩))
      · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inr hq⟩))
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h2
  -- (7) each piece meets `(c',d')` in a countable set
  have hpiece : ∀ q : ℚ, (Set.Ioo c' d' ∩ (oscR g (q:ℝ) ∪ oscL g (q:ℝ) ∪
      cornerMax g (q:ℝ) ∪ cornerMin g (q:ℝ))).Countable := by
    intro q
    have h1 : (Set.Ioo c' d' ∩ oscR g (q:ℝ)).Countable :=
      (finite_of_omega_noInterval (g := g) (P := oscR g (q:ℝ)) (c := c') (d := d')
          (hA := (hosc (q:ℝ)).1)
          (hno := fun u v hcu huv hvd hsub =>
            no_interval_oscR huv
              (fun x hx => hcont' x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩)
              hsub)).countable
    have h2 : (Set.Ioo c' d' ∩ oscL g (q:ℝ)).Countable :=
      (finite_of_omega_noInterval (g := g) (P := oscL g (q:ℝ)) (c := c') (d := d')
          (hA := (hosc (q:ℝ)).2)
          (hno := fun u v hcu huv hvd hsub =>
            no_interval_oscL huv
              (fun x hx => hcont' x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩)
              hsub)).countable
    have h3 : (Set.Ioo c' d' ∩ cornerMax g (q:ℝ)).Countable :=
      (cornerMax_countable g (q:ℝ)).mono Set.inter_subset_right
    have h4 : (Set.Ioo c' d' ∩ cornerMin g (q:ℝ)).Countable :=
      (cornerMin_countable g (q:ℝ)).mono Set.inter_subset_right
    exact Set.Countable.mono
      (s₂ := ((Set.Ioo c' d' ∩ oscR g (q:ℝ)) ∪ (Set.Ioo c' d' ∩ oscL g (q:ℝ)) ∪
        (Set.Ioo c' d' ∩ cornerMax g (q:ℝ)) ∪ (Set.Ioo c' d' ∩ cornerMin g (q:ℝ))))
      (fun x hx => by
        obtain ⟨hxI, hxA⟩ := hx
        rcases hxA with ((hxA | hxA) | hxA) | hxA
        · exact Or.inl (Or.inl (Or.inl ⟨hxI, hxA⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hxI, hxA⟩))
        · exact Or.inl (Or.inr ⟨hxI, hxA⟩)
        · exact Or.inr ⟨hxI, hxA⟩)
      (Set.Countable.union (Set.Countable.union (Set.Countable.union h1 h2) h3) h4)
  have hcountI1 : (Set.Ioo c' d' ∩ infDeriv g 1).Countable :=
    (finite_of_omega_noInterval (g := g) (P := infDeriv g 1) (c := c') (d := d')
      (hA := Work.WilG1.OneDim.infDeriv_mem g hg 1) (hno := hnoInf1)).countable
  have hcountI2 : (Set.Ioo c' d' ∩ infDeriv g (-1)).Countable :=
    (finite_of_omega_noInterval (g := g) (P := infDeriv g (-1)) (c := c') (d := d')
      (hA := Work.WilG1.OneDim.infDeriv_mem g hg (-1)) (hno := hnoInf2)).countable
  have hcountUnion : (((⋃ q : ℚ, (Set.Ioo c' d' ∩ (oscR g (q:ℝ) ∪ oscL g (q:ℝ) ∪
        cornerMax g (q:ℝ) ∪ cornerMin g (q:ℝ)))) ∪
        (Set.Ioo c' d' ∩ infDeriv g 1)) ∪ (Set.Ioo c' d' ∩ infDeriv g (-1))).Countable :=
    Set.Countable.union (Set.Countable.union (Set.countable_iUnion hpiece) hcountI1) hcountI2
  have hcoverI : Set.Ioo c' d' ⊆
      (((⋃ q : ℚ, (Set.Ioo c' d' ∩ (oscR g (q:ℝ) ∪ oscL g (q:ℝ) ∪
        cornerMax g (q:ℝ) ∪ cornerMin g (q:ℝ)))) ∪
        (Set.Ioo c' d' ∩ infDeriv g 1)) ∪ (Set.Ioo c' d' ∩ infDeriv g (-1))) := by
    intro x hx
    have h := hcover hx
    rcases h with (hq | h1) | h2
    · obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hq
      refine Or.inl (Or.inl ?_)
      exact Set.mem_iUnion.mpr ⟨q, ⟨hx, hq⟩⟩
    · exact Or.inl (Or.inr ⟨hx, h1⟩)
    · exact Or.inr ⟨hx, h2⟩
  exact not_countable_Ioo hc'd' (hcountUnion.mono hcoverI)

end Work.WilG4bF
