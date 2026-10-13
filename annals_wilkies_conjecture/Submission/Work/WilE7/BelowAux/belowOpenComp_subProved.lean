/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowOpenComp_subProved`): the *forward* inclusion for
  the connected component of the **open** below presentation `belowSopen Z S`.

  The closed analogue is `belowComp_sub` (component of `belowS` through the `-1`-point of sheet
  `0`).  Here the presentation carries the extra strict atom `t > -1`, and the base point of the
  component is the *interior* point `belowPt u₀ (s 0 (π u₀)) (belowT0 s 0 u₀)`, whose vertical
  coordinate is the midpoint of `-1` and the level of sheet `0`.

  The argument is the same as for the closed cell: the component satisfies the semialgebraic
  constraints `belowS`, the second block is over the base component `C`, the sheets cover `S.X`
  over `C` (`hcov`) with pointwise distinct graphs (`hinj`), so `connSub_graph` forces the
  component to stay on the graph of sheet `0`.  The only new inputs are that the base point lies
  in `belowSopen` (`belowPt_mem_open`, which needs the level of sheet `0` to be `≤ 1`, coming
  from the cube constraint on `S.X.set`), and that the first block of a point of the component
  lies in the component of `u₀` in `Z.set` (`belowOpenComp_sub_belowZ1_image`).
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.BelowAux.belowComp_sub
import Submission.Work.WilE7.BelowAux.belowOpenAux
import Submission.Work.WilE7.BelowAux.connSub_graph

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The first block lands in the base component -/

/-- `belowZ1` carries the connected component of `belowPt u₀ v t` inside `belowSopen` into the
connected component of `u₀` inside `Z.set`. -/
theorem belowOpenComp_sub_belowZ1_image
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (v : Fin (m + 1) → ℝ) (t : ℝ)
    (hP : belowPt u₀ v t ∈ (belowSopen Z S).set) :
    belowZ1 '' connectedComponentIn (belowSopen Z S).set (belowPt u₀ v t)
      ⊆ connectedComponentIn Z.set u₀ := by
  have h := ContinuousOn.image_connectedComponentIn_subset (f := belowZ1 (p := p) (m := m))
    (s := (belowSopen Z S).set) (a := belowPt u₀ v t) continuous_belowZ1.continuousOn hP
  rw [belowZ1_belowPt] at h
  refine h.trans (connectedComponentIn_mono u₀ ?_)
  rintro z ⟨u, hu, rfl⟩
  exact ((belowS_mem_iff Z S u).mp ((belowSopen_mem_iff Z S u).mp hu).1).1

/-! ## §2. The component stays on the lowest sheet -/

/-- Every point of the connected component of `belowSopen` through the interior point of the
`0`-th sheet lies on that same sheet: its second block is `(base, s 0 base)`.  This is where the
covering hypothesis `hcov` (the sheets cover `S.X` over `C`) and the injectivity `hinj` (their
graphs are pointwise distinct) are used: the graphs are relatively closed in the union, so a
preconnected set meeting one of them stays inside it. -/
theorem belowOpenComp_sub_sheet_eq
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    ∀ w ∈ connectedComponentIn (belowSopen Z S).set
        (belowPt u₀ (s ⟨0, hk⟩ (projFirst p (m + 1) u₀)) (belowT0 s ⟨0, hk⟩ u₀)),
      projSnd p (m + 1) (belowZ2 w) = s ⟨0, hk⟩ (projFirst p (m + 1) (belowZ2 w)) := by
  intro w hwK
  let v₀ : Fin (m + 1) → ℝ := s ⟨0, hk⟩ (projFirst p (m + 1) u₀)
  let t₀ : ℝ := belowT0 s ⟨0, hk⟩ u₀
  have hu0C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hlt0 : -1 < v₀ (Fin.last m) := hlt _ hu0C
  -- the level of the lowest sheet is `≤ 1`: it lies in the cube
  have hlev : v₀ (Fin.last m) ≤ 1 := by
    have h := (hsub ⟨0, hk⟩ _ hu0C).1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact (abs_le.mp h).2
  have hP : belowPt u₀ v₀ t₀ ∈ (belowSopen Z S).set :=
    belowPt_mem_open Z S u₀ hu₀ v₀ t₀ (hsub ⟨0, hk⟩ _ hu0C)
      (belowT0_abs hlt0 hlev) (belowT0_gt hlt0) (belowT0_lt hlt0)
  have hZ1c := belowOpenComp_sub_belowZ1_image S Z u₀ v₀ t₀ hP
  -- the "graph" map of the second block
  let Φ : (Fin (belowDim p m) → ℝ) → (Fin p → ℝ) × (Fin (m + 1) → ℝ) :=
    fun x => (projFirst p (m + 1) (belowZ2 x), projSnd p (m + 1) (belowZ2 x))
  have hΦ : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i =>
        (continuous_apply (Fin.castAdd (m + 1) i)).comp continuous_belowZ2
    · exact continuous_pi fun i =>
        (continuous_apply (Fin.natAdd p i)).comp continuous_belowZ2
  have hTconn : IsPreconnected
      (Φ '' (connectedComponentIn (belowSopen Z S).set (belowPt u₀ v₀ t₀))) :=
    (isPreconnected_connectedComponentIn (F := (belowSopen Z S).set)
      (x := belowPt u₀ v₀ t₀)).image Φ hΦ.continuousOn
  have hTU : Φ '' (connectedComponentIn (belowSopen Z S).set (belowPt u₀ v₀ t₀))
      ⊆ {q : (Fin p → ℝ) × (Fin (m + 1) → ℝ) | q.1 ∈ C ∧ ∃ i, q.2 = s i q.1} := by
    rintro q ⟨u, hu, rfl⟩
    have hu' := (belowS_mem_iff Z S u).mp
      ((belowSopen_mem_iff Z S u).mp (connectedComponentIn_subset _ _ hu)).1
    have hz1u : belowZ1 u ∈ connectedComponentIn Z.set u₀ := hZ1c ⟨u, hu, rfl⟩
    have hb1 : projFirst p (m + 1) (belowZ1 u) ∈ C := by
      rw [hC]; exact ⟨belowZ1 u, hz1u, rfl⟩
    have hb2 : projFirst p (m + 1) (belowZ2 u) ∈ C := by
      rw [← hu'.2.2.1]; exact hb1
    refine ⟨hb2, ?_⟩
    obtain ⟨i, hi⟩ := hcov (belowZ2 u) hu'.2.1 hb2
    exact ⟨i, hi.symm⟩
  have hTj : ∃ q ∈ Φ '' (connectedComponentIn (belowSopen Z S).set (belowPt u₀ v₀ t₀)),
      q.2 = s ⟨0, hk⟩ q.1 := by
    refine ⟨Φ (belowPt u₀ v₀ t₀),
      ⟨belowPt u₀ v₀ t₀, mem_connectedComponentIn hP, rfl⟩, ?_⟩
    show projSnd p (m + 1) (belowZ2 (belowPt u₀ v₀ t₀)) =
      s ⟨0, hk⟩ (projFirst p (m + 1) (belowZ2 (belowPt u₀ v₀ t₀)))
    rw [belowZ2_belowPt, projSnd_append, projFirst_append]
  have hfin := (connSub_graph (C := C) (s := s) (j := ⟨0, hk⟩) hcont hinj hTconn hTU hTj)
    ⟨w, hwK, rfl⟩
  exact hfin.2

/-! ## §3. The main statement -/

theorem belowOpenComp_subProved
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.BelowAux.belowSopen Z S).set
          (Work.WilE7.BelowAux.belowPt u₀
            (s ⟨0, hk⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀))
            (Work.WilE7.BelowAux.belowT0 s ⟨0, hk⟩ u₀)))
      ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  let v₀ : Fin (m + 1) → ℝ := s ⟨0, hk⟩ (projFirst p (m + 1) u₀)
  let t₀ : ℝ := belowT0 s ⟨0, hk⟩ u₀
  have hu0C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hlt0 : -1 < v₀ (Fin.last m) := hlt _ hu0C
  have hlev : v₀ (Fin.last m) ≤ 1 := by
    have h := (hsub ⟨0, hk⟩ _ hu0C).1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    exact (abs_le.mp h).2
  have hP : belowPt u₀ v₀ t₀ ∈ (belowSopen Z S).set :=
    belowPt_mem_open Z S u₀ hu₀ v₀ t₀ (hsub ⟨0, hk⟩ _ hu0C)
      (belowT0_abs hlt0 hlev) (belowT0_gt hlt0) (belowT0_lt hlt0)
  have hZ1c := belowOpenComp_sub_belowZ1_image S Z u₀ v₀ t₀ hP
  intro y hy
  obtain ⟨w, hwK, rfl⟩ := hy
  have hsheet :=
    belowOpenComp_sub_sheet_eq S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt w hwK
  have hwopen := (belowSopen_mem_iff Z S w).mp (connectedComponentIn_subset _ _ hwK)
  have hw := (belowS_mem_iff Z S w).mp hwopen.1
  refine ⟨?_, ?_, ?_⟩
  · rw [belowComp_sub_Fin_init, hC]
    exact ⟨belowZ1 w, hZ1c ⟨w, hwK, rfl⟩, rfl⟩
  · rw [belowExtract_apply_last]
    exact hwopen.2
  · rw [belowExtract_apply_last, belowComp_sub_Fin_init]
    rw [hw.2.2.1, ← hsheet]
    exact hw.2.2.2.2

end Work.WilE7.BelowAux
