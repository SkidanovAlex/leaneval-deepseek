/-
  WilG4a — `nondiff_interval_free`.

  A continuous function `g : ℝ → ℝ` whose graph is an `Ω F D 2`-set of an abstract
  sharply o-minimal structure cannot be nowhere differentiable on a non-degenerate
  interval.

  This is the `SharpCD`-free form of the one-dimensional argument.  It uses only already
  established facts about the `Ω`-calculus for abstract `SOMin`s:

  * `Work.WilG1.OneDim.bad_covered`: at a point where `g` is not differentiable, `g` is
    an oscillation point (`oscR`/`oscL`, at some rational slope `q`), a corner
    (`cornerMax`/`cornerMin`, at some rational slope `q`), or a point where the two-sided
    difference quotient tends to `+∞`/`-∞` (`infDeriv g 1`/`infDeriv g (-1)`);
  * the `Ω`-membership of the oscillation sets (`Work.WilG4a.osc_mem_local`) and of the
    infinite-derivative sets (`Work.WilG1.OneDim.infDeriv_mem`);
  * `Work.WilG1.OneDim.finite_of_omega_noInterval`: an `Ω`-subset of `ℝ¹` containing no
    non-degenerate interval meets `(c,d)` in a finite set, combined with the
    interval-emptiness lemmas `no_interval_oscR`, `no_interval_oscL` and
    `no_deriv_atTop_interval`;
  * `Work.WilG1.OneDim.cornerMax_countable`, `cornerMin_countable`: the corner sets are
    countable outright (no `Ω`-membership needed).

  Consequently `(c,d)` is contained in the countable union of the traces of the
  oscillation, corner and infinite-derivative sets, hence is countable, contradicting
  `c < d`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.OneDim.bad_covered
import Submission.Work.WilG1.OneDim.infDeriv_mem
import Submission.Work.WilG1.OneDim.thin_nointerval
import Submission.Work.WilG1.OneDim.thin_finite
import Submission.Work.WilG1.OneDim.thin_corner
import Submission.Work.WilG1.Analysis.no_deriv_atTop_interval
import Submission.Work.WilG4a.osc_membership

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilG4a

open WilkiesDesign

/-! ## 1. Auxiliary facts about open intervals -/

/-- Ord-connectedness of an open interval, proved directly. -/
lemma ordConnected_Ioo' {u v : ℝ} : (Set.Ioo u v).OrdConnected :=
  ⟨fun x hx y hy z hz => ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩⟩

/-- Two distinct points of a non-degenerate interval. -/
lemma two_points_Ioo {u v : ℝ} (huv : u < v) :
    (2 * u + v) / 3 ∈ Set.Ioo u v ∧ (u + 2 * v) / 3 ∈ Set.Ioo u v ∧
      (2 * u + v) / 3 ≠ (u + 2 * v) / 3 :=
  ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-! ## 2. Traces of the elementary thin sets in an interval -/

/-- **Right oscillation sets meet an interval of continuity in a finite set.** -/
theorem oscR_trace_finite {S : WilkiesDesign.SOMin} {a b : ℕ} {g : ℝ → ℝ} {q c d : ℝ}
    (hA : Work.WilG1.liftR (Work.WilG1.oscR g q) ∈ S.Ω a b 1)
    (hcont : ∀ t ∈ Set.Ioo c d, ContinuousAt g t) :
    ({x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ Work.WilG1.oscR g q} : Set ℝ).Finite := by
  refine Work.WilG1.OneDim.finite_of_omega_noInterval (g := g) (a := a) (b := b) (c := c)
    (d := d) hA ?_
  intro u v hcu huv hvd hsub
  exact Work.WilG1.OneDim.no_interval_oscR (g := g) (q := q) huv
    (fun x hx => hcont x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩) hsub

/-- **Left oscillation sets meet an interval of continuity in a finite set.** -/
theorem oscL_trace_finite {S : WilkiesDesign.SOMin} {a b : ℕ} {g : ℝ → ℝ} {q c d : ℝ}
    (hA : Work.WilG1.liftR (Work.WilG1.oscL g q) ∈ S.Ω a b 1)
    (hcont : ∀ t ∈ Set.Ioo c d, ContinuousAt g t) :
    ({x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ Work.WilG1.oscL g q} : Set ℝ).Finite := by
  refine Work.WilG1.OneDim.finite_of_omega_noInterval (g := g) (a := a) (b := b) (c := c)
    (d := d) hA ?_
  intro u v hcu huv hvd hsub
  exact Work.WilG1.OneDim.no_interval_oscL (g := g) (q := q) huv
    (fun x hx => hcont x ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩) hsub

/-- **The set `infDeriv g 1` meets an interval of continuity in a finite set.** -/
theorem infDeriv_one_trace_finite {S : WilkiesDesign.SOMin} {a b : ℕ} {g : ℝ → ℝ} {c d : ℝ}
    (hA : Work.WilG1.liftR (Work.WilG1.infDeriv g 1) ∈ S.Ω a b 1)
    (hcont : ∀ t ∈ Set.Ioo c d, ContinuousAt g t) :
    ({x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ Work.WilG1.infDeriv g 1} : Set ℝ).Finite := by
  refine Work.WilG1.OneDim.finite_of_omega_noInterval (g := g) (a := a) (b := b) (c := c)
    (d := d) hA ?_
  intro u v hcu huv hvd hsub
  have hsubI : Set.Ioo u v ⊆ Set.Ioo c d :=
    fun x hx => ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩
  have hcont' : ∀ x ∈ Set.Ioo u v, ContinuousAt g x := fun x hx => hcont x (hsubI hx)
  have hlim : ∀ x ∈ Set.Ioo u v,
      Filter.Tendsto (fun y : ℝ => (g y - g x) / (y - x)) (𝓝[≠] x) atTop := by
    intro x hx
    have hxinf : ∀ M : ℝ, 1 < M → ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ, y ≠ x → |y - x| < δ → M < 1 * Work.WilG1.dq g x y := hsub hx
    rw [Filter.tendsto_atTop]
    intro A
    obtain ⟨δ, hδ, hδ'⟩ := hxinf (max A 1 + 1) (by have := le_max_right A 1; linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun y hy hyne => ?_⟩
    have hy' : |y - x| < δ := by rwa [Real.dist_eq] at hy
    have hA2 : A ≤ max A 1 + 1 := by have := le_max_left A 1; linarith
    have hkey : max A 1 + 1 < Work.WilG1.dq g x y := by
      have h1 := hδ' y hyne hy'
      simpa using h1
    rw [Work.WilG1.dq] at hkey
    linarith
  have hss : (Set.Ioo u v).Subsingleton :=
    Work.WilG1.Analysis.no_deriv_atTop_interval (f := g) (I := Set.Ioo u v)
      ordConnected_Ioo' hcont' hlim
  obtain ⟨h1, h2, hne⟩ := two_points_Ioo huv
  exact hne (hss h1 h2)

/-- **The set `infDeriv g (-1)` meets an interval of continuity in a finite set.** -/
theorem infDeriv_neg_one_trace_finite {S : WilkiesDesign.SOMin} {a b : ℕ} {g : ℝ → ℝ}
    {c d : ℝ}
    (hA : Work.WilG1.liftR (Work.WilG1.infDeriv g (-1)) ∈ S.Ω a b 1)
    (hcont : ∀ t ∈ Set.Ioo c d, ContinuousAt g t) :
    ({x : ℝ | x ∈ Set.Ioo c d ∧ x ∈ Work.WilG1.infDeriv g (-1)} : Set ℝ).Finite := by
  refine Work.WilG1.OneDim.finite_of_omega_noInterval (g := g) (a := a) (b := b) (c := c)
    (d := d) hA ?_
  intro u v hcu huv hvd hsub
  have hsubI : Set.Ioo u v ⊆ Set.Ioo c d :=
    fun x hx => ⟨lt_of_le_of_lt hcu hx.1, lt_of_lt_of_le hx.2 hvd⟩
  have hcont' : ∀ x ∈ Set.Ioo u v, ContinuousAt (fun y : ℝ => -g y) x :=
    fun x hx => (hcont x (hsubI hx)).neg
  have hlim : ∀ x ∈ Set.Ioo u v,
      Filter.Tendsto (fun y : ℝ => ((-g y) - (-g x)) / (y - x)) (𝓝[≠] x) atTop := by
    intro x hx
    have hxinf : ∀ M : ℝ, 1 < M → ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ, y ≠ x → |y - x| < δ → M < (-1) * Work.WilG1.dq g x y := hsub hx
    rw [Filter.tendsto_atTop]
    intro A
    obtain ⟨δ, hδ, hδ'⟩ := hxinf (max A 1 + 1) (by have := le_max_right A 1; linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun y hy hyne => ?_⟩
    have hy' : |y - x| < δ := by rwa [Real.dist_eq] at hy
    have hA2 : A ≤ max A 1 + 1 := by have := le_max_left A 1; linarith
    have hkey := hδ' y hyne hy'
    have hrel : ((-g y) - (-g x)) / (y - x) = -Work.WilG1.dq g x y := by
      rw [Work.WilG1.dq]
      ring
    linarith [hkey, hrel, hA2]
  have hss : (Set.Ioo u v).Subsingleton :=
    Work.WilG1.Analysis.no_deriv_atTop_interval (f := fun y : ℝ => -g y) (I := Set.Ioo u v)
      ordConnected_Ioo' hcont' hlim
  obtain ⟨h1, h2, hne⟩ := two_points_Ioo huv
  exact hne (hss h1 h2)

/-! ## 3. The main theorem -/

theorem nondiff_interval_free (S : WilkiesDesign.SOMin) {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2)
    {c d : ℝ} (hcd : c < d) (hcont : ∀ t ∈ Set.Ioo c d, ContinuousAt g t)
    (hbad : ∀ t ∈ Set.Ioo c d, ¬ DifferentiableAt ℝ g t) : False := by
  -- For each rational slope, the corner/oscillation trace is countable.
  have hqFin : ∀ q : ℚ,
      ((Set.Ioo c d ∩ Work.WilG1.oscR g (q : ℝ)) ∪ (Set.Ioo c d ∩ Work.WilG1.oscL g (q : ℝ))
        ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMax g (q : ℝ))
        ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMin g (q : ℝ))).Countable := by
    intro q
    obtain ⟨aR, bR, hR⟩ := (Work.WilG4a.osc_mem_local (S := S) (F := F) (D := D) g hg (q : ℝ)).1
    obtain ⟨aL, bL, hL⟩ := (Work.WilG4a.osc_mem_local (S := S) (F := F) (D := D) g hg (q : ℝ)).2
    refine Set.Countable.union (Set.Countable.union (Set.Countable.union ?_ ?_) ?_) ?_
    · exact (oscR_trace_finite (S := S) (a := aR) (b := bR.eval D) (hA := hR) hcont).countable
    · exact (oscL_trace_finite (S := S) (a := aL) (b := bL.eval D) (hA := hL) hcont).countable
    · exact (Work.WilG1.OneDim.cornerMax_countable g (q : ℝ)).mono Set.inter_subset_right
    · exact (Work.WilG1.OneDim.cornerMin_countable g (q : ℝ)).mono Set.inter_subset_right
  -- The two infinite-derivative traces are countable (indeed finite).
  have hinf1Fin : (Set.Ioo c d ∩ Work.WilG1.infDeriv g 1).Countable :=
    (infDeriv_one_trace_finite (S := S) (a := F + 1000)
      (b := (Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1) : Polynomial ℕ).eval D)
      (hA := Work.WilG1.OneDim.infDeriv_mem (S := S) (F := F) (D := D) g hg 1) hcont).countable
  have hinfmFin : (Set.Ioo c d ∩ Work.WilG1.infDeriv g (-1)).Countable :=
    (infDeriv_neg_one_trace_finite (S := S) (a := F + 1000)
      (b := (Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1) : Polynomial ℕ).eval D)
      (hA := Work.WilG1.OneDim.infDeriv_mem (S := S) (F := F) (D := D) g hg (-1)) hcont).countable
  -- `(c,d)` is covered by the countable union of the traces.
  have hsub : Set.Ioo c d ⊆
      (⋃ q : ℚ, ((Set.Ioo c d ∩ Work.WilG1.oscR g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.oscL g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMax g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMin g (q : ℝ))))
        ∪ (Set.Ioo c d ∩ Work.WilG1.infDeriv g 1)
        ∪ (Set.Ioo c d ∩ Work.WilG1.infDeriv g (-1)) := by
    intro x hx
    have hxbad : x ∈ Work.WilG1.badSet g := hbad x hx
    rcases Work.WilG1.OneDim.bad_covered hxbad with ⟨q, hq | hq⟩ | h1 | h2 | ⟨q, hq | hq⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inl ⟨hx, hq⟩))⟩))
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inl (Or.inr ⟨hx, hq⟩))⟩))
    · exact Or.inl (Or.inr ⟨hx, h1⟩)
    · exact Or.inr ⟨hx, h2⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inl (Or.inr ⟨hx, hq⟩)⟩))
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨q, Or.inr ⟨hx, hq⟩⟩))
  have hcount : ((⋃ q : ℚ, ((Set.Ioo c d ∩ Work.WilG1.oscR g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.oscL g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMax g (q : ℝ))
          ∪ (Set.Ioo c d ∩ Work.WilG1.cornerMin g (q : ℝ))))
        ∪ (Set.Ioo c d ∩ Work.WilG1.infDeriv g 1)
        ∪ (Set.Ioo c d ∩ Work.WilG1.infDeriv g (-1))).Countable :=
    (Set.Countable.union (Set.Countable.union
      (Set.countable_iUnion (fun q : ℚ => hqFin q)) hinf1Fin) hinfmFin)
  have hcIoo : (Set.Ioo c d).Countable := hcount.mono hsub
  exact absurd (Cardinal.Real.Ioo_countable_iff.mp hcIoo) (not_le.mpr hcd)

end Work.WilG4a
