/-
  Area E7 / `CoreLT_succ`: the **strengthened BV fibre cut**.

  BV's fibre-cutting Lemma 8 (`Work.WilE7.cover_cut_deg`, `Work.WilE7.E7_fiber_cut_proved`)
  produces, for a semi-Pfaffian set `X ⊆ ℝ^{n+m}` of format `≤ F`, a list of semi-Pfaffian
  pieces with *finite* `π_n`-fibres whose `π_n`-images cover `π_n(X.set)`, with format `≤ a` and
  degree `≤ b X.deg`.  Its conclusion, however, records nothing about *where* the pieces live.

  The statement proved here adds the one extra clause that the `CoreLT_succ` assembly needs:
  every piece is contained in the ordinary topological closure `closure X.set`.  This is exactly
  the invariant that the recursion of `Submission/Work/WilE7/Deg/Recursion.lean` maintains: its
  base case returns the `X`-sets of the current worklist of `Good` strata, and its inductive step
  replaces a stratum by children drawn from its `E6`-frontier and its fibre-critical sets, both of
  which are contained in the fibre-wise closure, hence in the closure, of the parent.

  Because `cover_cut_aux`'s *statement* does not carry that information, the recursion is forked
  here with a parameter `U : Set (Fin (n+m) → ℝ)` and the extra hypothesis
  `∀ S ∈ Ys, closure S.X.set ⊆ U`, so that the induction can carry it to the output.  Everything
  else (the format sequence `Fb`, the degree polynomial `Pb`, the child bound `brB`, the count
  bound `Kb`, and the two per-stratum steps `Deg.step_frontier_deg` / `Deg.step_crit_deg`) is the
  bookkeeping already proved in the workspace and is used verbatim.
-/
import Mathlib
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.E7_fiber_cut_proved
import Submission.Work.WilE7.frontierDrop_proved
import Submission.Work.WilE7.cover_cut_deg

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology

namespace Work.WilE7.coreLT_succ
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The fibrewise closure is contained in the closure -/

/-- `fiberClosure X ⊆ closure X`: a point whose fibre coordinate is a limit of fibre points is a
limit of points of the set itself (the slice `y ↦ Fin.append x y` is continuous). -/
theorem fiberClosure_subset_closure {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) :
    fiberClosure X ⊆ closure X := by
  intro z hz
  have hz' : projSnd p q z ∈ closure (fiber X (projFirst p q z)) := hz
  have hcont : Continuous fun y : Fin q → ℝ => Fin.append (projFirst p q z) y :=
    (Fin.continuous_append p q).comp (continuous_const.prodMk continuous_id)
  have himg : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) ''
      (fiber X (projFirst p q z)) ⊆ X := by
    rintro w ⟨y, hy, rfl⟩
    exact hy
  have h1 : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) ''
      closure (fiber X (projFirst p q z)) ⊆ closure X :=
    (image_closure_subset_closure_image hcont).trans (closure_mono himg)
  exact h1 ⟨projSnd p q z, hz', Work.WilE7.append_projFirst_projSnd z⟩

/-! ## The forked recursion, tracking containment in `U` -/

/-- **The degree/count-tracking fibre-cutting recursion, with a containment invariant.**

`cover_cut_aux` with the extra parameter `U` and the extra hypothesis that the closure of every
stratum of the worklist lies in `U`.  The output pieces then satisfy `Xh.set ⊆ U` in addition to
all the format/degree/finiteness/coverage properties of `cover_cut_aux`. -/
theorem cover_cut_aux_clos (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ)
    (hE2 : E2Interface) (hFD : FrontierDrop) (hCD : CritDrop)
    (hCW : CritWitness) (D : ℕ) :
    ∀ k, k ≤ k₀ → ∀ (n m : ℕ), m ≤ A₀ → ∀ (U : Set (Fin (n + m) → ℝ))
      (Ys : List (Stratum n m)),
      (∀ S ∈ Ys, S.Good) → (∀ S ∈ Ys, S.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k) →
      (∀ S ∈ Ys, S.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D) →
      (∀ S ∈ Ys, S.j < m → m - S.j ≤ k) →
      (∀ S ∈ Ys, closure S.X.set ⊆ U) →
      ∃ L : List (SemiPf (n + m)),
        L.length ≤ Ys.length * (Kb hE5 hE6 A₀ k₀ k).eval D ∧
        (∀ Xh ∈ L, Xh.set ⊆ U ∧ Xh.fmt ≤ Fb hE5 hE6 A₀ k₀ 0 ∧
          Xh.deg ≤ (Pb hE5 hE6 A₀ k₀ 0).eval D ∧ ∀ x, (fiber Xh.set x).Finite) ∧
        (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆ (⋃ Xh ∈ L, projFirst n m '' Xh.set) ∧
        (⋃ Xh ∈ L, projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
  intro k
  induction k with
  | zero =>
      intro hk n m hm U Ys hgood hfmt hdeg hbud hU
      have hLenL : (Ys.map (fun S => S.X)).length ≤
          Ys.length * (Kb hE5 hE6 A₀ k₀ 0).eval D := by
        rw [show (Kb hE5 hE6 A₀ k₀ 0).eval D = 1 by
              rw [show Kb hE5 hE6 A₀ k₀ 0 = 1 from rfl]; simp]
        simp
      have hPiecesL : ∀ Xh ∈ Ys.map (fun S => S.X), Xh.set ⊆ U ∧
          Xh.fmt ≤ Fb hE5 hE6 A₀ k₀ 0 ∧
          Xh.deg ≤ (Pb hE5 hE6 A₀ k₀ 0).eval D ∧ ∀ x, (fiber Xh.set x).Finite := by
        intro Xh hXh
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hXh
        have hdegX : S.X.deg ≤ S.deg := by
          simp only [Stratum.deg]
          exact Nat.le_add_right _ _
        refine ⟨subset_closure.trans (hU S hS), hfmt S hS, le_trans hdegX (hdeg S hS), ?_⟩
        by_cases hne : S.X.set.Nonempty
        · have hjm : S.j = m := by
            have hle : S.j ≤ m := good_j_le S (hgood S hS) hne
            by_contra h
            have := hbud S hS (by omega)
            omega
          exact fiber_finite_of_good_full_rank hE2 S (hgood S hS) hjm
        · intro x
          have hempty : fiber S.X.set x = ∅ := by
            ext y
            simp only [Set.mem_empty_iff_false, iff_false]
            intro hy
            exact hne ⟨Fin.append x y, hy⟩
          rw [hempty]
          exact Set.finite_empty
      have hCovL : (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆
          (⋃ Xh ∈ Ys.map (fun S => S.X), projFirst n m '' Xh.set) := by
        intro x hx
        obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨S.X, List.mem_map.mpr ⟨S, hS, rfl⟩, hxS⟩
      have hSubL : (⋃ Xh ∈ Ys.map (fun S => S.X), projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
        intro x hx
        obtain ⟨Xh, hXh, hxXh⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hXh
        exact Set.mem_iUnion₂.mpr ⟨S, hS,
          Deg.projFirst_subset_projFirst_fiberClosure S.X.set hxXh⟩
      exact ⟨Ys.map (fun S => S.X), hLenL, hPiecesL, hCovL, hSubL⟩
  | succ k ih =>
      intro hk n m hm U Ys hgood hfmt hdeg hbud hU
      have hklt : k < k₀ := by omega
      -- the per-stratum child step
      have hstep : ∀ S ∈ Ys, ∃ Cs : List (Stratum n m),
          (∀ S' ∈ Cs, S'.Good) ∧ (∀ S' ∈ Cs, S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k) ∧
          (∀ S' ∈ Cs, S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D) ∧
          (∀ S' ∈ Cs, S'.X.set.Nonempty) ∧ (∀ S' ∈ Cs, m - S'.j ≤ k) ∧
          Cs.length ≤ (brB hE5 hE6 A₀ k₀ (k + 1)).eval D ∧
          (projFirst n m '' S.X.set ⊆ ⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ∧
          ((⋃ S' ∈ Cs, projFirst n m '' (fiberClosure S'.X.set)) ⊆
            projFirst n m '' (fiberClosure S.X.set)) ∧
          (∀ S' ∈ Cs, closure S'.X.set ⊆ U) := by
        intro S hS
        have hSgood : S.Good := hgood S hS
        have hSf : S.X.fmt ≤ Fb hE5 hE6 A₀ k₀ (k + 1) := hfmt S hS
        have hSd : S.deg ≤ (Pb hE5 hE6 A₀ k₀ (k + 1)).eval D := hdeg S hS
        by_cases hne : S.X.set.Nonempty
        · by_cases hlt : S.j < m
          · -- the main case: frontier children and critical children
            have hE6A : ∀ (X : SemiPf (n + m)), X.fmt ≤ Fb hE5 hE6 A₀ k₀ (k + 1) →
                ∃ Y Y' : SemiPf (n + m), Y'.fmt ≤ e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)) ∧
                  Y'.deg ≤ (e6deg hE6 (Fb hE5 hE6 A₀ k₀ (k + 1))).eval X.deg ∧
                  Y.set = fiberClosure X.set ∧ Y'.set = fiberClosure X.set \ X.set := by
              intro X hX
              obtain ⟨Y, Y', _, _, h3, h4, h5, h6⟩ :=
                e6spec hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)) n m X hX
              exact ⟨Y, Y', h3, h4, h5, h6⟩
            have hE5B : ∀ (X : SemiPf (n + m)), X.fmt ≤ e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)) →
                ∃ L : List (Stratum n m),
                  L.length ≤ (e5deg hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)))).eval X.deg ∧
                  (∀ S' ∈ L,
                    S'.X.fmt ≤ e5fmt hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1))) ∧ S'.Good ∧
                    S'.deg ≤ (e5deg hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)))).eval X.deg) ∧
                  X.set = (⋃ S' ∈ L, S'.X.set) := by
              intro X hX
              obtain ⟨L, hlen, hspec, hset, _⟩ :=
                e5spec hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1))) n m X hX
              exact ⟨L, hlen,
                fun S' hS' => ⟨(hspec S' hS').1, (hspec S' hS').2.2, (hspec S' hS').2.1⟩, hset⟩
            obtain ⟨Fs, hFsGood, hFsFmt, hFsDeg, hFsLen, hFsNe, hFsSub, hFsJ, hFsCov, hFsNo⟩ :=
              Deg.step_frontier_deg (hFD := hFD) (D := D) hE6A hE5B S hSgood hSf hSd
            have hE5A : ∀ (X : SemiPf (n + m)), X.fmt ≤ Fb hE5 hE6 A₀ k₀ (k + 1) →
                ∃ L : List (Stratum n m),
                  L.length ≤ (e5deg hE5 (Fb hE5 hE6 A₀ k₀ (k + 1))).eval X.deg ∧
                  (∀ S' ∈ L,
                    S'.X.fmt ≤ e5fmt hE5 (Fb hE5 hE6 A₀ k₀ (k + 1)) ∧ S'.Good ∧
                    S'.deg ≤ (e5deg hE5 (Fb hE5 hE6 A₀ k₀ (k + 1))).eval X.deg) ∧
                  X.set = (⋃ S' ∈ L, S'.X.set) := by
              intro X hX
              obtain ⟨L, hlen, hspec, hset, _⟩ :=
                e5spec hE5 (Fb hE5 hE6 A₀ k₀ (k + 1)) n m X hX
              exact ⟨L, hlen,
                fun S' hS' => ⟨(hspec S' hS').1, (hspec S' hS').2.2, (hspec S' hS').2.1⟩, hset⟩
            have hCDeg : ∀ (S' : Stratum n m), S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ (k + 1) → S'.j ≤ m →
                S'.X.basics.length ≤ S'.X.deg + 1 → ∀ l : Fin m,
                (critSet S' l).deg ≤ (cdpoly (Fb hE5 hE6 A₀ k₀ (k + 1))).eval S'.deg :=
              fun S' h1 h2 h3 l => cdspec (Fb hE5 hE6 A₀ k₀ (k + 1)) n m S' h1 h2 h3 l
            obtain ⟨Cs', hCsGood, hCsFmt, hCsDeg, hCsLen, hCsNe, hCsSub, hCsJ, hCsCov, hCsNo⟩ :=
              Deg.step_crit_deg (hCD := hCD) (hCW := hCW) (Ab := A₀) hE5A hCDeg hm S hSgood hSf hSd
                hne hlt
            have hbrB : brB hE5 hE6 A₀ k₀ (k + 1)
                = chpoly hE5 hE6 A₀ (Fb hE5 hE6 A₀ k₀ (k + 1)) (Pb hE5 hE6 A₀ k₀ (k + 1)) := rfl
            have hGoods : ∀ S' ∈ Fs ++ Cs', S'.Good := by
              intro S' hS'
              rcases List.mem_append.mp hS' with h | h
              · exact hFsGood S' h
              · exact hCsGood S' h
            have hFmts : ∀ S' ∈ Fs ++ Cs', S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
              intro S' hS'
              rcases List.mem_append.mp hS' with h | h
              · exact le_trans (hFsFmt S' h) (e5fmt_e6fmt_Fb_le hE5 hE6 A₀ k₀ k hklt)
              · exact le_trans (hCsFmt S' h) (e5fmt_Fb_le hE5 hE6 A₀ k₀ k hklt)
            have hDegs : ∀ S' ∈ Fs ++ Cs', S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
              intro S' hS'
              rcases List.mem_append.mp hS' with h | h
              · refine le_trans (hFsDeg S' h)
                  (le_trans ?_ (brB_eval_le_Pb hE5 hE6 A₀ k₀ k hklt D))
                rw [hbrB]
                exact chpoly_frontier_le hE5 hE6 A₀ _ _ D
              · refine le_trans (hCsDeg S' h)
                  (le_trans ?_ (brB_eval_le_Pb hE5 hE6 A₀ k₀ k hklt D))
                rw [hbrB]
                exact chpoly_crit_le hE5 hE6 A₀ _ _ D
            have hNes : ∀ S' ∈ Fs ++ Cs', S'.X.set.Nonempty := by
              intro S' hS'
              rcases List.mem_append.mp hS' with h | h
              · exact hFsNe S' h
              · exact hCsNe S' h
            have hBuds : ∀ S' ∈ Fs ++ Cs', m - S'.j ≤ k := by
              intro S' hS'
              rcases List.mem_append.mp hS' with h | h
              · have hJ := hFsJ S' h
                have hle : S'.j ≤ m := good_j_le S' (hFsGood S' h) (hFsNe S' h)
                have h2 : m - S.j ≤ k + 1 := hbud S hS hlt
                omega
              · have hJ := hCsJ S' h
                have hle : S'.j ≤ m := good_j_le S' (hCsGood S' h) (hCsNe S' h)
                have h2 : m - S.j ≤ k + 1 := hbud S hS hlt
                omega
            have hLens : (Fs ++ Cs').length ≤ (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by
              rw [List.length_append, hbrB]
              have h3 : ((e5deg hE5 (e6fmt hE6 (Fb hE5 hE6 A₀ k₀ (k + 1)))).comp
                    ((e6deg hE6 (Fb hE5 hE6 A₀ k₀ (k + 1))).comp
                      (Pb hE5 hE6 A₀ k₀ (k + 1)))).eval D
                  + A₀ * ((e5deg hE5 (Fb hE5 hE6 A₀ k₀ (k + 1))).comp
                      ((cdpoly (Fb hE5 hE6 A₀ k₀ (k + 1))).comp
                        (Pb hE5 hE6 A₀ k₀ (k + 1)))).eval D
                  ≤ (chpoly hE5 hE6 A₀ (Fb hE5 hE6 A₀ k₀ (k + 1))
                      (Pb hE5 hE6 A₀ k₀ (k + 1))).eval D :=
                chpoly_count_le hE5 hE6 A₀ _ _ D
              omega
            have hCovs : projFirst n m '' S.X.set ⊆
                ⋃ S' ∈ Fs ++ Cs', projFirst n m '' S'.X.set := by
              intro x hx
              by_cases hfr : x ∈ projFirst n m '' (fiberClosure S.X.set \ S.X.set)
              · have h1 : x ∈ ⋃ S' ∈ Fs, projFirst n m '' S'.X.set := hFsCov ⟨hx, hfr⟩
                obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp h1
                exact Set.mem_iUnion₂.mpr ⟨S', List.mem_append.mpr (Or.inl hS'), hxS'⟩
              · have h1 : x ∈ ⋃ S' ∈ Cs', projFirst n m '' S'.X.set := hCsCov ⟨hx, hfr⟩
                obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp h1
                exact Set.mem_iUnion₂.mpr ⟨S', List.mem_append.mpr (Or.inr hS'), hxS'⟩
            have hNoGrows : (⋃ S' ∈ Fs ++ Cs', projFirst n m '' (fiberClosure S'.X.set)) ⊆
                projFirst n m '' (fiberClosure S.X.set) := by
              intro x hx
              obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp hx
              rcases List.mem_append.mp hS' with h | h
              · exact image_fiberClosure_le_of_subset_frontier (hFsSub S' h) hxS'
              · exact image_fiberClosure_le_of_subset (hCsSub S' h) hxS'
            -- the new conjunct: the children stay in `U`
            have hClosContain : ∀ S' ∈ Fs ++ Cs', closure S'.X.set ⊆ U := by
              intro S' hS'
              have h1 : S'.X.set ⊆ closure S.X.set := by
                rcases List.mem_append.mp hS' with h | h
                · exact ((hFsSub S' h).trans Set.diff_subset).trans
                    (fiberClosure_subset_closure S.X.set)
                · exact (hCsSub S' h).trans subset_closure
              exact (closure_minimal h1 isClosed_closure).trans (hU S hS)
            exact ⟨Fs ++ Cs', hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows,
              hClosContain⟩
          · -- the pass-through case: `m ≤ S.j`, the stratum is its own child
            have hGoods : ∀ S' ∈ [S], S'.Good := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              exact hS' ▸ hSgood
            have hFmts : ∀ S' ∈ [S], S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              exact hS' ▸ le_trans hSf (Fb_self_le hE5 hE6 A₀ k₀ k hklt)
            have hDegs : ∀ S' ∈ [S], S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              exact hS' ▸ le_trans hSd (Pb_eval_le hE5 hE6 A₀ k₀ k hklt D)
            have hNes : ∀ S' ∈ [S], S'.X.set.Nonempty := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              exact hS' ▸ hne
            have hBuds : ∀ S' ∈ [S], m - S'.j ≤ k := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              subst hS'
              omega
            have hLens : ([S] : List (Stratum n m)).length ≤
                (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by
              simpa using brB_eval_ge_one hE5 hE6 A₀ k₀ (k + 1) D
            have hCovs : projFirst n m '' S.X.set ⊆ ⋃ S' ∈ [S], projFirst n m '' S'.X.set := by
              intro x hx
              exact Set.mem_iUnion₂.mpr ⟨S, List.mem_singleton.mpr rfl, hx⟩
            have hNoGrows : (⋃ S' ∈ [S], projFirst n m '' (fiberClosure S'.X.set)) ⊆
                projFirst n m '' (fiberClosure S.X.set) := by
              intro x hx
              obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp hx
              rw [List.mem_singleton] at hS'
              subst hS'
              exact hxS'
            have hClosContain : ∀ S' ∈ [S], closure S'.X.set ⊆ U := by
              intro S' hS'
              rw [List.mem_singleton] at hS'
              rw [hS']
              exact hU S hS
            exact ⟨[S], hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows,
              hClosContain⟩
        · -- the empty stratum: no children
          have hGoods : ∀ S' ∈ ([] : List (Stratum n m)), S'.Good := by simp
          have hFmts : ∀ S' ∈ ([] : List (Stratum n m)),
              S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by simp
          have hDegs : ∀ S' ∈ ([] : List (Stratum n m)),
              S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by simp
          have hNes : ∀ S' ∈ ([] : List (Stratum n m)), S'.X.set.Nonempty := by simp
          have hBuds : ∀ S' ∈ ([] : List (Stratum n m)), m - S'.j ≤ k := by simp
          have hLens : ([] : List (Stratum n m)).length ≤
              (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by simp
          have hCovs : projFirst n m '' S.X.set ⊆
              ⋃ S' ∈ ([] : List (Stratum n m)), projFirst n m '' S'.X.set := by
            intro x hx
            obtain ⟨z, hz, -⟩ := hx
            exact absurd ⟨z, hz⟩ hne
          have hNoGrows : (⋃ S' ∈ ([] : List (Stratum n m)),
              projFirst n m '' (fiberClosure S'.X.set)) ⊆
              projFirst n m '' (fiberClosure S.X.set) := by simp
          exact ⟨[], hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows, by simp⟩
      -- the children of every stratum
      let ch : Stratum n m → List (Stratum n m) :=
        fun S => if h : S ∈ Ys then (hstep S h).choose else []
      have chspec : ∀ (S : Stratum n m) (hS : S ∈ Ys), ch S = (hstep S hS).choose := by
        intro S hS
        simp only [ch, dite_eq_left hS]
      have chGood : ∀ S ∈ Ys, ∀ S' ∈ ch S, S'.Good := by
        intro S hS S' hS'
        rw [chspec S hS] at hS'
        exact ((hstep S hS).choose_spec).1 S' hS'
      have chFmt : ∀ S ∈ Ys, ∀ S' ∈ ch S, S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
        intro S hS S' hS'
        rw [chspec S hS] at hS'
        exact ((hstep S hS).choose_spec).2.1 S' hS'
      have chDeg : ∀ S ∈ Ys, ∀ S' ∈ ch S, S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
        intro S hS S' hS'
        rw [chspec S hS] at hS'
        exact ((hstep S hS).choose_spec).2.2.1 S' hS'
      have chLen : ∀ S ∈ Ys, (ch S).length ≤ (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by
        intro S hS
        rw [chspec S hS]
        exact ((hstep S hS).choose_spec).2.2.2.2.2.1
      have chCov : ∀ S ∈ Ys, projFirst n m '' S.X.set ⊆ ⋃ S' ∈ ch S, projFirst n m '' S'.X.set := by
        intro S hS
        rw [chspec S hS]
        exact ((hstep S hS).choose_spec).2.2.2.2.2.2.1
      have chNoGrow : ∀ S ∈ Ys,
          ((⋃ S' ∈ ch S, projFirst n m '' (fiberClosure S'.X.set)) ⊆
            projFirst n m '' (fiberClosure S.X.set)) := by
        intro S hS
        rw [chspec S hS]
        exact ((hstep S hS).choose_spec).2.2.2.2.2.2.2.1
      have chClos : ∀ S ∈ Ys, ∀ S' ∈ ch S, closure S'.X.set ⊆ U := by
        intro S hS S' hS'
        rw [chspec S hS] at hS'
        exact ((hstep S hS).choose_spec).2.2.2.2.2.2.2.2 S' hS'
      have mem_ch : ∀ S' ∈ Ys.flatMap ch, ∃ S ∈ Ys, S' ∈ ch S := by
        intro S' hS'
        exact List.mem_flatMap.mp hS'
      have hgood' : ∀ S' ∈ Ys.flatMap ch, S'.Good := by
        intro S' hS'
        obtain ⟨S, hS, hSc⟩ := mem_ch S' hS'
        exact chGood S hS S' hSc
      have hfmt' : ∀ S' ∈ Ys.flatMap ch, S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
        intro S' hS'
        obtain ⟨S, hS, hSc⟩ := mem_ch S' hS'
        exact chFmt S hS S' hSc
      have hdeg' : ∀ S' ∈ Ys.flatMap ch, S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
        intro S' hS'
        obtain ⟨S, hS, hSc⟩ := mem_ch S' hS'
        exact chDeg S hS S' hSc
      have hbud' : ∀ S' ∈ Ys.flatMap ch, S'.j < m → m - S'.j ≤ k := by
        intro S' hS' _
        obtain ⟨S, hS, hSc⟩ := mem_ch S' hS'
        rw [chspec S hS] at hSc
        exact ((hstep S hS).choose_spec).2.2.2.2.1 S' hSc
      have hU' : ∀ S' ∈ Ys.flatMap ch, closure S'.X.set ⊆ U := by
        intro S' hS'
        obtain ⟨S, hS, hSc⟩ := mem_ch S' hS'
        exact chClos S hS S' hSc
      obtain ⟨L, hLen, hPieces, hCov, hSub⟩ :=
        ih (by omega) n m hm U (Ys.flatMap ch) hgood' hfmt' hdeg' hbud' hU'
      have hLenL : L.length ≤ Ys.length * (Kb hE5 hE6 A₀ k₀ (k + 1)).eval D := by
        have hYs' : (Ys.flatMap ch).length ≤
            Ys.length * (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by
          rw [List.length_flatMap]
          calc (Ys.map (fun S => (ch S).length)).sum
              ≤ (Ys.map (fun _ => (brB hE5 hE6 A₀ k₀ (k + 1)).eval D)).sum :=
                List.sum_le_sum (fun S hS => chLen S hS)
            _ = Ys.length * (brB hE5 hE6 A₀ k₀ (k + 1)).eval D := by simp
        calc L.length ≤ (Ys.flatMap ch).length * (Kb hE5 hE6 A₀ k₀ k).eval D := hLen
          _ ≤ (Ys.length * (brB hE5 hE6 A₀ k₀ (k + 1)).eval D) *
                (Kb hE5 hE6 A₀ k₀ k).eval D := Nat.mul_le_mul_right _ hYs'
          _ = Ys.length * (Kb hE5 hE6 A₀ k₀ (k + 1)).eval D := by
                rw [show Kb hE5 hE6 A₀ k₀ (k + 1) = brB hE5 hE6 A₀ k₀ (k + 1) *
                  Kb hE5 hE6 A₀ k₀ k from rfl, Polynomial.eval_mul, Nat.mul_assoc]
      have hCovL : (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆
          (⋃ Xh ∈ L, projFirst n m '' Xh.set) := by
        intro x hx
        obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.mp hx
        have h1 := chCov S hS hxS
        obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp h1
        exact hCov (Set.mem_iUnion₂.mpr ⟨S', List.mem_flatMap.mpr ⟨S, hS, hS'⟩, hxS'⟩)
      have hSubL : (⋃ Xh ∈ L, projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
        intro x hx
        have h1 := hSub hx
        obtain ⟨S', hS', hxS'⟩ := Set.mem_iUnion₂.mp h1
        obtain ⟨S, hS, hSc⟩ := List.mem_flatMap.mp hS'
        exact Set.mem_iUnion₂.mpr ⟨S, hS,
          chNoGrow S hS (Set.mem_iUnion₂.mpr ⟨S', hSc, hxS'⟩)⟩
      exact ⟨L, hLenL, hPieces, hCovL, hSubL⟩

/-! ## The instantiation, with containment -/

/-- `Work.WilE7.cover_cut_deg` with the containment clause. -/
theorem cover_cut_deg_clos
    (hE2 : E2Interface) (hE5 : E5Interface) (hE6 : E6Interface)
    (hFD : FrontierDrop) (hCD : CritDrop) (hCW : CritWitness) (A₀ k₀ : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (k A : ℕ) (n m : ℕ) (U : Set (Fin (n + m) → ℝ))
      (Ys : List (Stratum n m)) (D : ℕ),
      A ≤ A₀ → k ≤ k₀ → (∀ S ∈ Ys, S.Good) → (∀ S ∈ Ys, S.X.fmt ≤ A) →
      (∀ S ∈ Ys, S.deg ≤ D) → (∀ S ∈ Ys, S.j < m → m - S.j ≤ k) →
      (∀ S ∈ Ys, closure S.X.set ⊆ U) →
      ∃ L : List (SemiPf (n + m)), L.length ≤ Ys.length * b.eval D ∧
        (∀ Xh ∈ L, Xh.set ⊆ U ∧ Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval D ∧
          ∀ x, (fiber Xh.set x).Finite) ∧
        (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆
          (⋃ Xh ∈ L, projFirst n m '' Xh.set) ∧
        (⋃ Xh ∈ L, projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
  refine ⟨Fb hE5 hE6 A₀ k₀ 0, Kb hE5 hE6 A₀ k₀ k₀ + Pb hE5 hE6 A₀ k₀ 0, ?_⟩
  intro k A n m U Ys D hA hk hgood hfmt hdeg hbud hU
  by_cases hYs : Ys = []
  · subst hYs
    exact ⟨[], by simp, by simp, by simp, by simp⟩
  · obtain ⟨S₀, hS₀⟩ := List.exists_mem_of_ne_nil Ys hYs
    have hm : m ≤ A₀ := by
      have h1 : n + m ≤ S₀.X.fmt := by simp [SemiPf.fmt]
      have h2 : S₀.X.fmt ≤ A := hfmt S₀ hS₀
      omega
    have hfmt' : ∀ S ∈ Ys, S.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k := by
      intro S hS
      exact le_trans (hfmt S hS) (le_trans hA (Fb_ge_A₀ hE5 hE6 A₀ k₀ k))
    have hdeg' : ∀ S ∈ Ys, S.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D := by
      intro S hS
      exact le_trans (hdeg S hS) (degSeq_eval_ge hE5 hE6 A₀ D (k₀ - k))
    obtain ⟨L, hLen, hPieces, hCov, hSub⟩ :=
      cover_cut_aux_clos hE5 hE6 A₀ k₀ hE2 hFD hCD hCW D k hk n m hm U Ys
        hgood hfmt' hdeg' hbud hU
    refine ⟨L, ?_, ?_, hCov, hSub⟩
    · refine le_trans hLen (Nat.mul_le_mul_left _ ?_)
      rw [Polynomial.eval_add]
      exact le_trans (Kb_eval_mono hE5 hE6 A₀ k₀ D hk) (Nat.le_add_right _ _)
    · intro Xh hXh
      obtain ⟨h1, h2, h3, h4⟩ := hPieces Xh hXh
      refine ⟨h1, h2, ?_, h4⟩
      rw [Polynomial.eval_add]
      exact le_trans h3 (Nat.le_add_left _ _)

/-! ## The strengthened fibre cut -/

theorem fiberCut_subset_closure
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧
        L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.SemiPf (n + m)),
        (∀ Xh ∈ L, Xh.set ⊆ closure X.set ∧ Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
          ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
        WilkiesDesign.E.projFirst n m '' X.set =
          ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set := by
  obtain ⟨a5, b5, h5⟩ := hE5 F
  obtain ⟨a, b, hb⟩ :=
    cover_cut_deg_clos hE2 hE5 hE6 frontierDrop_proved critDrop_proved'
      critWitness_proved' (max a5 F) F
  refine ⟨a, b.comp b5, ?_⟩
  intro n m X hX
  obtain ⟨Ys, -, hgood, hset, -⟩ := h5 n m X hX
  have hfmt : ∀ S ∈ Ys, S.X.fmt ≤ max a5 F := fun S hS =>
    le_trans (hgood S hS).1 (le_max_left _ _)
  have hdeg : ∀ S ∈ Ys, S.deg ≤ b5.eval X.deg := fun S hS => (hgood S hS).2.1
  have hbud : ∀ S ∈ Ys, S.j < m → m - S.j ≤ F := by
    intro S hS _
    have h1 : m ≤ X.fmt := by rw [SemiPf.fmt]; omega
    exact le_trans (Nat.sub_le m S.j) (le_trans h1 hX)
  have hU : ∀ S ∈ Ys, closure S.X.set ⊆ closure X.set := by
    intro S hS
    apply closure_mono
    intro z hz
    rw [hset]
    exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hz⟩⟩
  obtain ⟨L, -, hpieces, hcov, hsub⟩ :=
    hb F (max a5 F) n m (closure X.set) Ys (b5.eval X.deg) le_rfl le_rfl
      (fun S hS => (hgood S hS).2.2) hfmt hdeg hbud hU
  refine ⟨L, ?_, ?_⟩
  · intro Xh hXh
    obtain ⟨hsubU, hf, hd, hfin⟩ := hpieces Xh hXh
    refine ⟨hsubU, hf, ?_, hfin⟩
    rw [Deg.eval_comp_eval]
    exact hd
  · have hunion : projFirst n m '' X.set = ⋃ S ∈ Ys, projFirst n m '' S.X.set := by
      rw [hset]
      ext x
      simp only [Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨z, ⟨S, hS, hzS⟩, rfl⟩
        exact ⟨S, hS, z, hzS, rfl⟩
      · rintro ⟨S, hS, z, hzS, rfl⟩
        exact ⟨z, ⟨S, hS, hzS⟩, rfl⟩
    refine Set.Subset.antisymm ?_ ?_
    · rw [hunion]; exact hcov
    · intro x hx
      have h1 : x ∈ ⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set) := hsub hx
      simp only [Set.mem_iUnion] at h1
      obtain ⟨S, hS, hxS⟩ := h1
      rw [closureProj_proved' n m S.X.set] at hxS
      rw [hunion]
      exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hS, hxS⟩⟩

end Work.WilE7.coreLT_succ
