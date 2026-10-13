/-
  Area E7: the **assembly** of BV's Lemma 8 (`lem:fiber-cut`) from the frozen holes
  `E2_components`, `E5_strat`, `E6_fiber_closure` plus the four geometric inputs.

  This file contains the recursion over worklists of `Good` strata (BV's induction on the fibre
  dimension `m - S.j`), with the geometric inputs isolated as hypotheses in `FiberCutInputs.lean`:

  * `Work.WilE7.FrontierDrop`     — the frontier dimension drop (the open one);
  * `Work.WilE7.CritDrop`         — the critical-side dimension drop (`stratum_j_lt_of_subset_crit`);
  * `Work.WilE7.CritWitness`      — the critical point with a witness over closed fibres;
  * `Work.WilE7.ClosureProj`      — the closure trick `π(fiberClosure Y) = π(Y)`
                                    (`Work.WilE7.projFirst_fiberClosure`).

  The format bound is tracked by the sequence `fmtBound`; the degree and count bounds are dealt
  with in `E7_fiber_cut_proved.lean`.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.FiberCutDefs
import Submission.Work.WilE7.FiberCutInputs
import Submission.Work.WilE7.fiber_finite_of_good_full_rank
import Submission.Work.WilE7.projFirst_fiberClosure

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## The format bound sequence -/

/-- The format bound after `t` rounds, given the bound `F` at round `0` and the two format
functions `e ↦ a5 e` (`E5`) and `e ↦ a6 e` (`E6`).  Each entry dominates the previous one, so the
sequence is monotone. -/
noncomputable def fmtBound (F : ℕ) (a5 a6 : ℕ → ℕ) : ℕ → ℕ
  | 0 => F
  | (t + 1) =>
      max (fmtBound F a5 a6 t)
        (max (a5 (fmtBound F a5 a6 t)) (a5 (a6 (fmtBound F a5 a6 t))))

theorem fmtBound_le_succ (F : ℕ) (a5 a6 : ℕ → ℕ) (t : ℕ) :
    fmtBound F a5 a6 t ≤ fmtBound F a5 a6 (t + 1) :=
  le_max_left _ _

theorem fmtBound_mono (F : ℕ) (a5 a6 : ℕ → ℕ) : Monotone (fmtBound F a5 a6) :=
  monotone_nat_of_le_succ (fmtBound_le_succ F a5 a6)

/-! ## An elementary fact about `Good` strata -/

/-- A `Good` stratum with non-empty set has `S.j ≤ q` (its fibrewise Jacobian has `q` columns). -/
theorem good_j_le {p q : ℕ} (S : Stratum p q) (hG : S.Good) (hne : S.X.set.Nonempty) :
    S.j ≤ q := by
  obtain ⟨z, hz⟩ := hne
  have hrank := (hG z hz).2.1
  have := Matrix.rank_le_width
    (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z)
  rw [hrank] at this
  simpa using this

/-! ## The one-stratum step -/

/-- The witness condition of `CritDrop`, as a predicate. -/
def CritWitnessAt {p q : ℕ} (S : Stratum p q) (l : Fin q) (S' : Stratum p q) : Prop :=
  ∃ z ∈ S'.X.set, ∃ w ∈ fiber S.X.set (projFirst p q z),
    w ∈ connectedComponentIn (fiber S.X.set (projFirst p q z)) (projSnd p q z) ∧
      w l ≠ z (fibDir p q l)

/-- **The one-stratum step.**  For a single `Good` stratum `S` of fibre dimension `≥ 1` (so
`S.j < m`), the *children* are

* the non-empty strata of the `E5`-stratification of the fibrewise frontier
  `fiberClosure S.X.set \ S.X.set` (`E6`), which by `FrontierDrop` all have `S.j < S'.j`;
* for each fibre coordinate `l`, the strata of the `E5`-stratification of `critSet S l` that are
  non-empty and carry the `CritWitnessAt` condition, which by `CritDrop` have `S.j < S'.j`.

They cover `π(S.X.set)` and their projections stay inside `π(fiberClosure S.X.set)`; each child has
fibre dimension `≤ k` as soon as `m - S.j ≤ k + 1`. -/
theorem stratum_step
    {n m k : ℕ} (hPC : ClosureProj) (hFD : FrontierDrop) (hCD : CritDrop) (hCW : CritWitness)
    {A A5 A6 : ℕ}
    (hE5A : ∀ (X : SemiPf (n + m)), X.fmt ≤ A → ∃ L : List (Stratum n m),
      (∀ S ∈ L, S.X.fmt ≤ A5 ∧ S.Good) ∧ X.set = (⋃ S ∈ L, S.X.set))
    (hE5B : ∀ (X : SemiPf (n + m)), X.fmt ≤ A6 → ∃ L : List (Stratum n m),
      (∀ S ∈ L, S.X.fmt ≤ A5 ∧ S.Good) ∧ X.set = (⋃ S ∈ L, S.X.set))
    (hE6A : ∀ (X : SemiPf (n + m)), X.fmt ≤ A → ∃ Y Y' : SemiPf (n + m),
      Y'.fmt ≤ A6 ∧ Y.set = fiberClosure X.set ∧ Y'.set = fiberClosure X.set \ X.set)
    (S : Stratum n m) (hSG : S.Good) (hSf : S.X.fmt ≤ A) (hSne : S.X.set.Nonempty)
    (hSlt : S.j < m) (hfib : m - S.j ≤ k + 1) :
    ∃ Cs : List (Stratum n m),
      (∀ S' ∈ Cs, S'.Good) ∧ (∀ S' ∈ Cs, S'.X.fmt ≤ max A A5) ∧
      (∀ S' ∈ Cs, m - S'.j ≤ k) ∧
      (projFirst n m '' S.X.set ⊆ ⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ∧
      ((⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ⊆ projFirst n m '' fiberClosure S.X.set) := by
  classical
  -- the frontier and its stratification
  obtain ⟨Y, Y', hY'fmt, hYset, hY'set⟩ := hE6A S.X hSf
  obtain ⟨Lf, hLf, hLfset⟩ := hE5B Y' hY'fmt
  -- the critical stratifications
  have hcf : ∀ l : Fin m, (critSet S l).fmt ≤ A := fun l => by
    rw [critSet_fmt]; exact hSf
  let critL : Fin m → List (Stratum n m) := fun l => (hE5A (critSet S l) (hcf l)).choose
  have hcritL : ∀ l : Fin m,
      (∀ T ∈ critL l, T.X.fmt ≤ A5 ∧ T.Good) ∧
        (critSet S l).set = (⋃ T ∈ critL l, T.X.set) :=
    fun l => (hE5A (critSet S l) (hcf l)).choose_spec
  -- the children
  let Fs : List (Stratum n m) := Lf.filter (fun T => T.X.set.Nonempty)
  let Cs : List (Stratum n m) := Fs ++ (List.finRange m).flatMap
      (fun l => (critL l).filter (fun T => T.X.set.Nonempty ∧ CritWitnessAt S l T))
  refine ⟨Cs, ?_, ?_, ?_, ?_, ?_⟩
  · -- every child is `Good`
    intro S' hS'
    rcases List.mem_append.mp hS' with h | h
    · exact (hLf S' (List.mem_of_mem_filter h)).2
    · obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
      exact ((hcritL l).1 S' (List.mem_of_mem_filter hl)).2
  · -- formats
    intro S' hS'
    rcases List.mem_append.mp hS' with h | h
    · exact le_trans ((hLf S' (List.mem_of_mem_filter h)).1) (le_max_right _ _)
    · obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
      exact le_trans ((hcritL l).1 S' (List.mem_of_mem_filter hl)).1 (le_max_right _ _)
  · -- fibre dimensions
    intro S' hS'
    rcases List.mem_append.mp hS' with h | h
    · have hmem : S' ∈ Lf := (List.mem_filter.mp h).1
      have hne : S'.X.set.Nonempty := of_decide_eq_true (List.mem_filter.mp h).2
      have hsub : S'.X.set ⊆ fiberClosure S.X.set \ S.X.set := by
        intro z hz
        have h1 : z ∈ Y'.set := by
          rw [hLfset]
          simp only [Set.mem_iUnion]
          exact ⟨S', hmem, hz⟩
        rwa [hY'set] at h1
      have hlt : S.j < S'.j := hFD n m S S' hSG ((hLf S' hmem).2) hsub hne
      have hle : S'.j ≤ m := good_j_le S' ((hLf S' hmem).2) hne
      omega
    · obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
      have hmem : S' ∈ critL l := (List.mem_filter.mp hl).1
      have hboth := of_decide_eq_true (List.mem_filter.mp hl).2
      have hne : S'.X.set.Nonempty := hboth.1
      have hwit : CritWitnessAt S l S' := hboth.2
      have hsub : S'.X.set ⊆ (critSet S l).set := by
        intro z hz
        rw [(hcritL l).2]
        simp only [Set.mem_iUnion]
        exact ⟨S', hmem, hz⟩
      have hlt : S.j < S'.j :=
        hCD n m S S' hSG ((hcritL l).1 S' hmem).2 l hSlt hsub hwit
      have hle : S'.j ≤ m := good_j_le S' ((hcritL l).1 S' hmem).2 hne
      omega
  · -- coverage of `π(S.X.set)`
    intro x hx
    by_cases hcase : x ∈ projFirst n m '' (fiberClosure S.X.set \ S.X.set)
    · -- the fibre is not closed: the frontier children cover `x`
      have hxY : x ∈ projFirst n m '' Y'.set := by rw [hY'set]; exact hcase
      rw [hLfset] at hxY
      simp only [Set.mem_image, Set.mem_iUnion] at hxY
      obtain ⟨z, ⟨T, hT, hzT⟩, hxeq⟩ := hxY
      refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hT, decide_eq_true ⟨z, hzT⟩⟩))
      · exact ⟨z, hzT, hxeq⟩
    · -- the fibre is compact: the critical children cover `x`
      obtain ⟨z0, hz0, hxeq⟩ := hx
      have hcase' : projFirst n m z0 ∉ projFirst n m '' (fiberClosure S.X.set \ S.X.set) := by
        intro h
        exact hcase (hxeq ▸ h)
      have hne : (fiber S.X.set (projFirst n m z0)).Nonempty :=
        ⟨projSnd n m z0, by
          show Fin.append (projFirst n m z0) (projSnd n m z0) ∈ S.X.set
          rw [append_projFirst_projSnd z0]
          exact hz0⟩
      obtain ⟨l, z, hzcrit, hzbase, w, hw, hwcomp, hwne⟩ :=
        hCW n m S hSG hSlt (projFirst n m z0) hcase' hne
      have hzmem : z ∈ (critSet S l).set := hzcrit
      rw [(hcritL l).2] at hzmem
      simp only [Set.mem_iUnion] at hzmem
      obtain ⟨T, hT, hzT⟩ := hzmem
      refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · refine List.mem_append.mpr (Or.inr ?_)
        refine List.mem_flatMap.mpr ⟨l, List.mem_finRange l, ?_⟩
        refine List.mem_filter.mpr ⟨hT,
          decide_eq_true ⟨⟨z, hzT⟩, z, hzT, w, ?_, ?_, ?_⟩⟩
        · have hzx : projFirst n m z = projFirst n m z0 := by rw [hzbase, hxeq]
          rwa [hzx]
        · have hzx : projFirst n m z = projFirst n m z0 := by rw [hzbase, hxeq]
          rwa [hzx]
        · exact hwne
      · exact ⟨z, hzT, by rw [hzbase, hxeq]⟩
  · -- no growth
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨S', hS', hxS'⟩ := hx
    rcases List.mem_append.mp hS' with h | h
    · obtain ⟨z, hz, hxeq⟩ := hxS'
      have hmem : S' ∈ Lf := (List.mem_filter.mp h).1
      have hzfr : z ∈ fiberClosure S.X.set \ S.X.set := by
        have h1 : z ∈ Y'.set := by
          rw [hLfset]
          simp only [Set.mem_iUnion]
          exact ⟨S', hmem, hz⟩
        rwa [hY'set] at h1
      exact ⟨z, hzfr.1, hxeq⟩
    · obtain ⟨l, _, hl⟩ := List.mem_flatMap.mp h
      have hmem : S' ∈ critL l := (List.mem_filter.mp hl).1
      obtain ⟨z, hz, hxeq⟩ := hxS'
      have hzS : z ∈ S.X.set := by
        refine critSet_subset S l ?_
        rw [(hcritL l).2]
        simp only [Set.mem_iUnion]
        exact ⟨S', hmem, hz⟩
      have hx' : projFirst n m z ∈ projFirst n m '' S.X.set := ⟨z, hzS, rfl⟩
      rw [← hPC n m S.X.set, hxeq] at hx'
      exact hx'

/-! ## Coverage of a worklist of `Good` strata -/

/-- **The worklist recursion.**  Given a list `Ys` of `Good` strata of `ℝ^{n+m}`, all of format
`≤ A` and with fibre dimension `m - S.j ≤ k`, produce a list of semi-Pfaffian sets with *finite
fibres* whose projections cover the union of the projections of the `S.X.set`, and all of whose
projections lie in the projections of the fibrewise closures `fiberClosure S.X.set`. -/
theorem cover_cut
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧
        Y'.set = fiberClosure X.set \ X.set)
    (hPC : ClosureProj) (hFD : FrontierDrop) (hCD : CritDrop) (hCW : CritWitness) :
    ∀ (k A : ℕ) (n m : ℕ) (Ys : List (Stratum n m)),
      (∀ S ∈ Ys, S.Good) →
      (∀ S ∈ Ys, S.X.fmt ≤ A) →
      (∀ S ∈ Ys, S.j < m → m - S.j ≤ k) →
      ∃ L : List (SemiPf (n + m)),
        (∀ Xh ∈ L, ∀ x, (fiber Xh.set x).Finite) ∧
        (⋃ S ∈ Ys, projFirst n m '' S.X.set) ⊆
          (⋃ Xh ∈ L, projFirst n m '' Xh.set) ∧
        (⋃ Xh ∈ L, projFirst n m '' Xh.set) ⊆
          (⋃ S ∈ Ys, projFirst n m '' (fiberClosure S.X.set)) := by
  intro k
  induction k with
  | zero =>
    intro A n m Ys hgood hfmt hjle
    refine ⟨Ys.map (fun S => S.X), ?_, ?_, ?_⟩
    · intro Xh hXh x
      obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hXh
      by_cases hne : S.X.set.Nonempty
      · have hj : S.j = m := by
          have hle : S.j ≤ m := good_j_le S (hgood S hS) hne
          by_contra h
          have := hjle S hS (by omega)
          omega
        exact fiber_finite_of_good_full_rank hE2 S (hgood S hS) hj x
      · have hempty : WilkiesDesign.E.fiber S.X.set x = ∅ := by
          ext y
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hy
          exact hne ⟨Fin.append x y, hy⟩
        rw [hempty]
        exact Set.finite_empty
    · intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨S, hS, hxS⟩ := hx
      exact ⟨S.X, List.mem_map.mpr ⟨S, hS, rfl⟩, hxS⟩
    · intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨Xh, hXh, hxXh⟩ := hx
      obtain ⟨S, hS, hXS⟩ := List.mem_map.mp hXh
      rw [← hXS] at hxXh
      refine ⟨S, hS, ?_⟩
      obtain ⟨z, hz, rfl⟩ := hxXh
      exact ⟨z, by
        show projSnd n m z ∈ closure (WilkiesDesign.E.fiber S.X.set (projFirst n m z))
        apply subset_closure
        show Fin.append (projFirst n m z) (projSnd n m z) ∈ S.X.set
        rw [append_projFirst_projSnd z]
        exact hz, rfl⟩
  | succ k ih =>
    intro A n m Ys hgood hfmt hjle
    obtain ⟨a5, b5, h5⟩ := hE5 A
    obtain ⟨a6, b6, h6⟩ := hE6 A
    obtain ⟨a5B, b5B, h5B⟩ := hE5 (max a6 A)
    -- the interfaces used by `stratum_step`
    have hE5A : ∀ (X : SemiPf (n + m)), X.fmt ≤ A → ∃ L : List (Stratum n m),
        (∀ S ∈ L, S.X.fmt ≤ max a5 a5B ∧ S.Good) ∧ X.set = (⋃ S ∈ L, S.X.set) := by
      intro X hX
      obtain ⟨L, -, hLgood, hLset, -⟩ := h5 n m X hX
      exact ⟨L, fun S hS => ⟨le_trans (hLgood S hS).1 (le_max_left _ _), (hLgood S hS).2.2⟩, hLset⟩
    have hE5B' : ∀ (X : SemiPf (n + m)), X.fmt ≤ max a6 A → ∃ L : List (Stratum n m),
        (∀ S ∈ L, S.X.fmt ≤ max a5 a5B ∧ S.Good) ∧ X.set = (⋃ S ∈ L, S.X.set) := by
      intro X hX
      obtain ⟨L, -, hLgood, hLset, -⟩ := h5B n m X hX
      exact ⟨L, fun S hS => ⟨le_trans (hLgood S hS).1 (le_max_right _ _), (hLgood S hS).2.2⟩, hLset⟩
    have hE6A : ∀ (X : SemiPf (n + m)), X.fmt ≤ A → ∃ Y Y' : SemiPf (n + m),
        Y'.fmt ≤ max a6 A ∧ Y.set = fiberClosure X.set ∧
          Y'.set = fiberClosure X.set \ X.set := by
      intro X hX
      obtain ⟨Y, Y', hYf, -, hY'f, -, hYset, hY'set⟩ := h6 n m X hX
      exact ⟨Y, Y', le_trans hY'f (le_max_left _ _), hYset, hY'set⟩
    -- the per-stratum step
    have hstep : ∀ S ∈ Ys, ∃ Cs : List (Stratum n m),
        (∀ S' ∈ Cs, S'.Good) ∧ (∀ S' ∈ Cs, S'.X.fmt ≤ max A (max a5 a5B)) ∧
        (∀ S' ∈ Cs, m - S'.j ≤ k) ∧
        (projFirst n m '' S.X.set ⊆ ⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ∧
        ((⋃ S' ∈ Cs, projFirst n m '' S'.X.set) ⊆ projFirst n m '' fiberClosure S.X.set) := by
      intro S hSmem
      by_cases hne : S.X.set.Nonempty
      · by_cases hlt : S.j < m
        · exact stratum_step hPC hFD hCD hCW hE5A hE5B' hE6A S (hgood S hSmem) (hfmt S hSmem)
            hne hlt (hjle S hSmem hlt)
        · -- the fibre dimension is zero: the stratum itself is the child
          have hle : S.j ≤ m := good_j_le S (hgood S hSmem) hne
          have hjm : S.j = m := by omega
          refine ⟨[S], ?_, ?_, ?_, ?_, ?_⟩
          · intro S' hS'
            rw [List.mem_singleton] at hS'
            rw [hS']
            exact hgood S hSmem
          · intro S' hS'
            rw [List.mem_singleton] at hS'
            rw [hS']
            exact le_trans (hfmt S hSmem) (le_max_left _ _)
          · intro S' hS'
            rw [List.mem_singleton] at hS'
            rw [hS']
            simp [hjm]
          · intro x hx
            simp only [Set.mem_iUnion]
            exact ⟨S, List.mem_singleton.mpr rfl, hx⟩
          · intro x hx
            simp only [Set.mem_iUnion] at hx
            obtain ⟨S', hS', hxS'⟩ := hx
            rw [List.mem_singleton] at hS'
            rw [hS'] at hxS'
            exact (hPC n m S.X.set).symm ▸ hxS'
      · -- the set is empty: there is nothing to cover
        refine ⟨[], by simp, by simp, by simp, ?_, by simp⟩
        intro x hx
        obtain ⟨z, hz, -⟩ := hx
        exact absurd ⟨z, hz⟩ hne
    -- the children of each stratum
    let ch : Stratum n m → List (Stratum n m) := fun S => if h : S ∈ Ys then (hstep S h).choose else []
    have chspec : ∀ (S : Stratum n m) (hS : S ∈ Ys), ch S = (hstep S hS).choose := by
      intro S hS
      simp only [ch, dite_eq_left hS]
    have chgood : ∀ S ∈ Ys, ∀ S' ∈ ch S, S'.Good := by
      intro S hS S' hS'
      rw [chspec S hS] at hS'
      exact ((hstep S hS).choose_spec).1 S' hS'
    have chfmt : ∀ S ∈ Ys, ∀ S' ∈ ch S, S'.X.fmt ≤ max A (max a5 a5B) := by
      intro S hS S' hS'
      rw [chspec S hS] at hS'
      exact ((hstep S hS).choose_spec).2.1 S' hS'
    have chfib : ∀ S ∈ Ys, ∀ S' ∈ ch S, m - S'.j ≤ k := by
      intro S hS S' hS'
      rw [chspec S hS] at hS'
      exact ((hstep S hS).choose_spec).2.2.1 S' hS'
    have chcov : ∀ S ∈ Ys, projFirst n m '' S.X.set ⊆ ⋃ S' ∈ ch S, projFirst n m '' S'.X.set := by
      intro S hS
      rw [chspec S hS]
      exact ((hstep S hS).choose_spec).2.2.2.1
    have chsub : ∀ S ∈ Ys,
        (⋃ S' ∈ ch S, projFirst n m '' S'.X.set) ⊆ projFirst n m '' fiberClosure S.X.set := by
      intro S hS
      rw [chspec S hS]
      exact ((hstep S hS).choose_spec).2.2.2.2
    -- the new worklist
    let Ys' : List (Stratum n m) := Ys.flatMap ch
    have mem_Ys' : ∀ S' ∈ Ys', ∃ S ∈ Ys, S' ∈ ch S := by
      intro S' hS'
      obtain ⟨S, hS, hSc⟩ := List.mem_flatMap.mp (by simpa only [Ys'] using hS')
      exact ⟨S, hS, hSc⟩
    have hgood' : ∀ S' ∈ Ys', S'.Good := by
      intro S' hS'
      obtain ⟨S, hS, hSc⟩ := mem_Ys' S' hS'
      exact chgood S hS S' hSc
    have hfmt' : ∀ S' ∈ Ys', S'.X.fmt ≤ max A (max a5 a5B) := by
      intro S' hS'
      obtain ⟨S, hS, hSc⟩ := mem_Ys' S' hS'
      exact chfmt S hS S' hSc
    have hfib' : ∀ S' ∈ Ys', S'.j < m → m - S'.j ≤ k := by
      intro S' hS' _
      obtain ⟨S, hS, hSc⟩ := mem_Ys' S' hS'
      exact chfib S hS S' hSc
    obtain ⟨L, hLfin, hLcov, hLsub⟩ :=
      ih (max A (max a5 a5B)) n m Ys' hgood' hfmt' hfib'
    refine ⟨L, hLfin, ?_, ?_⟩
    · -- coverage
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨S, hS, hxS⟩ := hx
      have h1 : x ∈ ⋃ S' ∈ ch S, projFirst n m '' S'.X.set := chcov S hS hxS
      simp only [Set.mem_iUnion] at h1
      obtain ⟨S', hS', hxS'⟩ := h1
      have h2 : x ∈ ⋃ S' ∈ Ys', projFirst n m '' S'.X.set := by
        simp only [Set.mem_iUnion]
        exact ⟨S', by simpa only [Ys'] using List.mem_flatMap.mpr ⟨S, hS, hS'⟩, hxS'⟩
      simpa only [Set.mem_iUnion] using hLcov h2
    · -- no growth
      intro x hx
      have h1 := hLsub hx
      simp only [Set.mem_iUnion] at h1 ⊢
      obtain ⟨S', hS', hxS'⟩ := h1
      obtain ⟨S, hS, hSc⟩ := mem_Ys' S' hS'
      have hxS'' : x ∈ projFirst n m '' S'.X.set := by
        rwa [hPC n m S'.X.set] at hxS'
      have h2 : x ∈ projFirst n m '' fiberClosure S.X.set :=
        chsub S hS (by
          simp only [Set.mem_iUnion]
          exact ⟨S', hSc, hxS''⟩)
      exact ⟨S, hS, h2⟩

end Work.WilE7
