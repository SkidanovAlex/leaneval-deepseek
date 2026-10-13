/-
  WilE7 / dimension chapter: the fibre of a `Good` stratum of *full* fibre codimension is closed.

  For a `Good` stratum `S : Stratum p q` with `S.j = q`, every point `z` of `S.X.set` has an
  invertible fibrewise Jacobian `∂S.h/∂y` (a `q × q` matrix of rank `q`), so the fibre map
  `y ↦ (eaEval S.X.c (S.h a) (x, y))_a` is a local diffeomorphism at `y`; `eaEval_eventually_eq`
  (the uniqueness half of the implicit function theorem) therefore isolates each point of the
  fibre `fiber S.X.set x` in the fibre.

  The fibre is the set of the *specialisation* `speSemiPfAt x S.X` (`speAt_set`), i.e. a finite
  union of basic semianalytic pieces intersected with the cube `cubeC q`.  A point of the closure
  which is not in the fibre would, by semianalytic curve selection (`curve_sel_in_cube`, which
  handles the closed cube constraint), produce an analytic arc inside the fibre; but a subset of a
  set in which every point is isolated which is preconnected is a single point, so the arc has to
  be constant and its value is both in and not in the fibre.

  The set `B.holds c` of a `Basic` set is rewritten as the basic set `BasicSA F g` of a single
  equation `F = ∑ (eqs)²` and the `pos` atoms (`basic_holds_basicSA`), so that curve selection
  applies. -/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilE7.eaEval_eventually_eq
import Submission.Work.WilE7.speAt_set
import Submission.Work.WilE7.fiber_finite_of_good_full_rank
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE7.Dim.curve_sel_in_cube
import Submission.Work.WilE7.Dim.basic_holds_basicSA

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.Dim

open WilkiesConjecture WilkiesDesign WilkiesDesign.E WilkiesDesign.CG

/-- Finitely many closed sets: a point of the closure of a finite union lies in the closure of one
member. -/
theorem mem_closure_iUnion_fin {α : Type*} [TopologicalSpace α] {n : ℕ} {A : Fin n → Set α}
    {y : α} (h : y ∈ closure (⋃ i, A i)) : ∃ i, y ∈ closure (A i) := by
  rw [closure_iUnion_of_finite] at h
  exact Set.mem_iUnion.mp h

/-- **Local isolation of the fibre points of a `Good` stratum of full fibre codimension.**
With `S.j = q` the fibrewise Jacobian of `S.h` is a square matrix of full rank `q` at every point
of `S.X.set`, hence invertible; `eaEval_eventually_eq` (the uniqueness half of the implicit
function theorem for the fibre map) then isolates each fibre point among the solutions of
`h = 0`, and `Good` says every fibre point is such a solution. -/
theorem fiber_isolated {p q : ℕ} (S : Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (x : Fin p → ℝ) :
    ∀ y ∈ WilkiesDesign.E.fiber S.X.set x,
      ∀ᶠ y' in 𝓝 y, y' ∈ WilkiesDesign.E.fiber S.X.set x → y' = y := by
  intro y hy
  obtain ⟨hh0, hrank, -⟩ := hGood (Fin.append x y) hy
  let e : Fin q ≃ Fin S.j := finCongr hj.symm
  let h' : Fin q → EAPoly (p + q) S.X.r := fun a => S.h (e a)
  have hMrank : (Matrix.of fun (a : Fin q) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y)).rank = q := by
    have hsub : (Matrix.of fun (a : Fin q) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y))
        = (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
            eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) (Fin.append x y)).submatrix
          (⇑e) (⇑(Equiv.refl (Fin q))) := rfl
    rw [hsub, Matrix.rank_submatrix, hrank, hj]
  have hdet : (Matrix.of fun (a : Fin q) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (h' a)) (Fin.append x y)).det ≠ 0 :=
    Work.WilE7.det_ne_zero_of_rank_eq hMrank
  have hev := Work.WilE7.eaEval_eventually_eq S.X.c h' x y (fun a => hh0 (e a)) hdet
  filter_upwards [hev] with y' hy' hy'fib
  exact hy' (fun a => (hGood (Fin.append x y') hy'fib).1 (e a))

/-- The assembly of `fibre_closed_of_fullRank`, with the two auxiliary facts taken as hypotheses:
`hL1` is `Work.WilE7.Dim.curve_sel_in_cube` and `hL2` is `Work.WilE7.Dim.basic_holds_basicSA`. -/
theorem fibre_closed_of_fullRank_aux {p q : ℕ} (S : Stratum p q) (hGood : S.Good)
    (x : Fin p → ℝ) (hj : S.j = q)
    (hL1 : ∀ {q l : ℕ} (F : (Fin q → ℝ) → ℝ) (g : Fin l → (Fin q → ℝ) → ℝ) (y : Fin q → ℝ),
      AnalyticAt ℝ F y → (∀ j, AnalyticAt ℝ (g j) y) →
      y ∈ closure (WilkiesDesign.E.cubeC q ∩ C4a.BasicSA F g) →
      ∃ γ : ℝ → (Fin q → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧ ∃ ε > (0 : ℝ),
        ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ WilkiesDesign.E.cubeC q ∩ C4a.BasicSA F g)
    (hL2 : ∀ {q r : ℕ} (c : EAChain q r) (B : Basic q r),
      {y : Fin q → ℝ | B.holds c y} = C4a.BasicSA
        (fun y : Fin q → ℝ => ∑ i : Fin B.eqs.length, (eaEval c (B.eqs.get i) y) ^ 2)
        (fun (j : Fin B.pos.length) (y : Fin q → ℝ) => eaEval c (B.pos.get j) y)) :
    IsClosed (WilkiesDesign.E.fiber S.X.set x) := by
  by_cases hx : x ∈ WilkiesDesign.E.cubeC p
  · set X' : SemiPf q := Work.WilE7.speSemiPfAt x S.X with hX'
    have hset : X'.set = WilkiesDesign.E.fiber S.X.set x := Work.WilE7.speAt_set x S.X hx
    have hiso : ∀ y ∈ X'.set, ∀ᶠ y' in 𝓝 y, y' ∈ X'.set → y' = y := by
      intro y hy
      rw [hset] at hy ⊢
      exact fiber_isolated S hGood hj x y hy
    rw [← hset, ← closure_subset_iff_isClosed]
    intro y₀ hy₀cl
    by_contra hy₀
    -- the fibre is a finite union of pieces, one over each basic set
    have hUnion : X'.set = ⋃ i : Fin X'.basics.length,
        (WilkiesDesign.E.cubeC q ∩ {y : Fin q → ℝ | (X'.basics.get i).holds X'.c y}) := by
      ext y
      simp only [SemiPf.set, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨hyc, B, hB, hBh⟩
        rw [List.mem_iff_get] at hB
        obtain ⟨i, rfl⟩ := hB
        exact ⟨i, hyc, hBh⟩
      · rintro ⟨i, hyc, hBh⟩
        exact ⟨hyc, X'.basics.get i, X'.basics.get_mem i, hBh⟩
    rw [hUnion] at hy₀cl
    obtain ⟨i, hi⟩ := mem_closure_iUnion_fin hy₀cl
    set B : Basic q X'.r := X'.basics.get i with hB
    have hcl : y₀ ∈ closure (WilkiesDesign.E.cubeC q ∩ C4a.BasicSA
        (fun y : Fin q → ℝ => ∑ i : Fin B.eqs.length, (eaEval X'.c (B.eqs.get i) y) ^ 2)
        (fun (j : Fin B.pos.length) (y : Fin q → ℝ) => eaEval X'.c (B.pos.get j) y)) := by
      rwa [hL2 X'.c B] at hi
    have hF : AnalyticAt ℝ
        (fun y : Fin q → ℝ => ∑ i : Fin B.eqs.length, (eaEval X'.c (B.eqs.get i) y) ^ 2) y₀ := by
      have h := Finset.analyticAt_sum (Finset.univ : Finset (Fin B.eqs.length))
        (fun i _ => (Work.WilE5.Strat.analyticAt_eaEval X'.c (B.eqs.get i) y₀).pow 2)
      have hfeq : (∑ i : Fin B.eqs.length,
            ((fun y : Fin q → ℝ => eaEval X'.c (B.eqs.get i) y) ^ 2))
          = fun y : Fin q → ℝ => ∑ i : Fin B.eqs.length, (eaEval X'.c (B.eqs.get i) y) ^ 2 := by
        funext y
        simp [Finset.sum_apply]
      rw [hfeq] at h
      exact h
    have hg : ∀ j : Fin B.pos.length,
        AnalyticAt ℝ (fun y : Fin q → ℝ => eaEval X'.c (B.pos.get j) y) y₀ :=
      fun j => Work.WilE5.Strat.analyticAt_eaEval X'.c (B.pos.get j) y₀
    obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ := hL1 _ _ y₀ hF hg hcl
    have hγK : ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ X'.set := by
      intro s hs
      have h1 := hγε s hs
      rw [hUnion]
      refine Set.mem_iUnion.mpr ⟨i, ⟨h1.1, ?_⟩⟩
      rw [hL2 X'.c B]
      exact h1.2
    -- discreteness of the fibre turns the arc into a single point
    obtain ⟨R, hRpos, hRan⟩ := hγan.exists_ball_analyticOnNhd
    set ε' : ℝ := min ε (R / 2) with hε'
    have hε'pos : 0 < ε' := lt_min hεpos (by linarith)
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'R : ε' ≤ R / 2 := min_le_right _ _
    have hcont : ContinuousOn γ (Set.Ioo (0 : ℝ) ε') := by
      refine (hRan.mono ?_).continuousOn
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1]
      linarith [hs.2, hε'R]
    have hTpre : IsPreconnected (γ '' Set.Ioo (0 : ℝ) ε') :=
      isPreconnected_Ioo.image γ hcont
    have hTK : γ '' Set.Ioo (0 : ℝ) ε' ⊆ X'.set := by
      rintro y ⟨s, hs, rfl⟩
      exact hγK s ⟨hs.1, lt_of_lt_of_le hs.2 hε'le⟩
    have hTne : (γ '' Set.Ioo (0 : ℝ) ε').Nonempty :=
      ⟨γ (ε' / 2), ⟨ε' / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩
    have hsub : (γ '' Set.Ioo (0 : ℝ) ε').Subsingleton := by
      intro a ha b hb
      by_contra hab
      have hmem_a : a ∈ X'.set := hTK ha
      have hne_a : {y' : Fin q → ℝ | y' ∈ X'.set → y' = a} ∈ 𝓝 a :=
        Filter.eventually_iff.mp (hiso a hmem_a)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hne_a
      have haU : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
      have hcov : γ '' Set.Ioo (0 : ℝ) ε' ⊆ Metric.ball a δ ∪ {a}ᶜ := fun z _ =>
        if hza : z = a then Or.inl (by rw [hza]; exact haU) else Or.inr hza
      obtain ⟨x, hxT, hxU, hxne⟩ :=
        hTpre (Metric.ball a δ) {a}ᶜ Metric.isOpen_ball isOpen_compl_singleton hcov
          ⟨a, ha, haU⟩ ⟨b, hb, by simpa using (Ne.symm hab : b ≠ a)⟩
      exact hxne (hδsub hxU (hTK hxT))
    obtain ⟨v, hv⟩ := hTne
    have hTsingle : γ '' Set.Ioo (0 : ℝ) ε' = {v} := hsub.eq_singleton_of_mem hv
    have hconst : ∀ s ∈ Set.Ioo (0 : ℝ) ε', γ s = v := by
      intro s hs
      have : γ s ∈ ({v} : Set (Fin q → ℝ)) := by rw [← hTsingle]; exact ⟨s, hs, rfl⟩
      simpa using this
    have hvK : v ∈ X'.set := hTK hv
    have htend1 : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 v) := by
      have hev : (fun _ : ℝ => v) =ᶠ[𝓝[>] (0 : ℝ)] γ := by
        show ∀ᶠ s in 𝓝[>] (0 : ℝ), v = γ s
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Iio_mem_nhds hε'pos] with s hs hs0
        exact (hconst s ⟨hs0, hs⟩).symm
      exact (tendsto_const_nhds (x := v)).congr' hev
    have htend2 : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) :=
      hγan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hy₀v : y₀ = v := by
      have h := tendsto_nhds_unique htend1 htend2
      rw [hγ0] at h
      exact h.symm
    exact hy₀ (by rw [hy₀v]; exact hvK)
  · have hempty : WilkiesDesign.E.fiber S.X.set x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact hx fun i => by
        have h1 : |Fin.append x y (Fin.castAdd q i)| ≤ 1 := hy.1 (Fin.castAdd q i)
        rwa [Fin.append_left] at h1
    rw [hempty]
    exact isClosed_empty

theorem fibre_closed_of_fullRank {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (hGood : WilkiesDesign.E.Stratum.Good S) (x : Fin p → ℝ) (hj : S.j = q) :
    IsClosed (WilkiesDesign.E.fiber S.X.set x) :=
  fibre_closed_of_fullRank_aux S hGood x hj curve_sel_in_cube basic_holds_basicSA

end Work.WilE7.Dim
