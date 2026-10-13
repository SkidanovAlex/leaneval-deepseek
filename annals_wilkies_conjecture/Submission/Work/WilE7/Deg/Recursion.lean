/-
  Area E7, module `Submission.Work.WilE7.Deg.Recursion`: the worklist recursion of BV's fibre-cutting
  Lemma 8 with the degree and count bookkeeping (`Work.WilE7.cover_cut_aux`), which the target
  `Work.WilE7.cover_cut_deg` instantiates.

  Each round of the recursion replaces every stratum of the worklist by the children produced by
  `Work.WilE7.Deg.step_frontier_deg` (the strata of the `E5`-stratification of the `E6`-frontier)
  and `Work.WilE7.Deg.step_crit_deg` (the strata of the `E5`-stratification of the fibre-critical
  sets carrying a witness); the strata with `S.j ≥ m` (which are empty, or have fibre dimension
  zero) are their own children, and the strata with empty set are dropped.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.FiberCutCover
import Submission.Work.WilE7.semiPf_normalize_exists
import Submission.Work.WilE7.fiber_finite_of_good_full_rank
import Submission.Work.WilE7.Deg.SeqLemmas
import Submission.Work.WilE7.Deg.step_frontier_deg
import Submission.Work.WilE7.Deg.step_crit_deg

set_option autoImplicit false
noncomputable section
open Classical Topology
open scoped Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

section Recursion

variable (hE5 : E5Interface) (hE6 : E6Interface) (A₀ k₀ : ℕ)

/-- **The worklist recursion with degree and count bookkeeping.**  A worklist `Ys` of `Good` strata
of format `≤ Fb k`, degree `≤ (Pb k).eval D` and fibre dimension `≤ k` produces a list `L` of
semi-Pfaffian sets with finite fibres, of format `≤ Fb 0`, degree `≤ (Pb 0).eval D` and length
`≤ Ys.length * (Kb k).eval D`, covering `⋃ π(S.X.set)` and contained in
`⋃ π(fiberClosure S.X.set)`. -/
theorem cover_cut_aux (hE2 : E2Interface) (hFD : FrontierDrop) (hCD : CritDrop)
    (hCW : CritWitness) (D : ℕ) :
    ∀ k, k ≤ k₀ → ∀ (n m : ℕ), m ≤ A₀ → ∀ Ys : List (Stratum n m),
      (∀ S ∈ Ys, S.Good) → (∀ S ∈ Ys, S.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k) →
      (∀ S ∈ Ys, S.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D) →
      (∀ S ∈ Ys, S.j < m → m - S.j ≤ k) →
      ∃ L : List (SemiPf (n + m)),
        L.length ≤ Ys.length * (Kb hE5 hE6 A₀ k₀ k).eval D ∧
        (∀ Xh ∈ L, Xh.fmt ≤ Fb hE5 hE6 A₀ k₀ 0 ∧
          Xh.deg ≤ (Pb hE5 hE6 A₀ k₀ 0).eval D ∧ ∀ x, (fiber Xh.set x).Finite) ∧
        (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆ (⋃ Xh ∈ L, projFirst n m '' Xh.set) ∧
        (⋃ Xh ∈ L, projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
  intro k
  induction k with
  | zero =>
      intro hk n m hm Ys hgood hfmt hdeg hbud
      have hLenL : (Ys.map (fun S => S.X)).length ≤
          Ys.length * (Kb hE5 hE6 A₀ k₀ 0).eval D := by
        rw [show (Kb hE5 hE6 A₀ k₀ 0).eval D = 1 by
              rw [show Kb hE5 hE6 A₀ k₀ 0 = 1 from rfl]; simp]
        simp
      have hPiecesL : ∀ Xh ∈ Ys.map (fun S => S.X), Xh.fmt ≤ Fb hE5 hE6 A₀ k₀ 0 ∧
          Xh.deg ≤ (Pb hE5 hE6 A₀ k₀ 0).eval D ∧ ∀ x, (fiber Xh.set x).Finite := by
        intro Xh hXh
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hXh
        have hdegX : S.X.deg ≤ S.deg := by
          simp only [Stratum.deg]
          exact Nat.le_add_right _ _
        refine ⟨hfmt S hS, le_trans hdegX (hdeg S hS), ?_⟩
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
      intro hk n m hm Ys hgood hfmt hdeg hbud
      have hklt : k < k₀ := by omega
      -- the per-stratum child step
      have hstep : ∀ S ∈ Ys, ∃ Cs : List (Stratum n m),
          (∀ S' ∈ Cs, S'.Good) ∧ (∀ S' ∈ Cs, S'.X.fmt ≤ Fb hE5 hE6 A₀ k₀ k) ∧
          (∀ S' ∈ Cs, S'.deg ≤ (Pb hE5 hE6 A₀ k₀ k).eval D) ∧
          (∀ S' ∈ Cs, S'.X.set.Nonempty) ∧ (∀ S' ∈ Cs, m - S'.j ≤ k) ∧
          Cs.length ≤ (brB hE5 hE6 A₀ k₀ (k + 1)).eval D ∧
          (projFirst n m '' S.X.set ⊆ ⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ∧
          ((⋃ S' ∈ Cs, projFirst n m '' (fiberClosure S'.X.set)) ⊆
            projFirst n m '' (fiberClosure S.X.set)) := by
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
            exact ⟨Fs ++ Cs', hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows⟩
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
            exact ⟨[S], hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows⟩
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
          exact ⟨[], hGoods, hFmts, hDegs, hNes, hBuds, hLens, hCovs, hNoGrows⟩
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
        exact ((hstep S hS).choose_spec).2.2.2.2.2.2.2
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
      obtain ⟨L, hLen, hPieces, hCov, hSub⟩ :=
        ih (by omega) n m hm (Ys.flatMap ch) hgood' hfmt' hdeg' hbud'
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

end Recursion

end Work.WilE7
