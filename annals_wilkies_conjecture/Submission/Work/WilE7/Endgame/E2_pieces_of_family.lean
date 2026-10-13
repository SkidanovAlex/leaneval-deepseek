import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.coreLT_succ.Pieces
import Submission.Work.WilE7.CoreStep.piFamily
import Submission.Work.WilE7.coreLT_succ.reindex_family_base
import Submission.Work.WilE7.coreLT_succ.SwapEquiv0
import Submission.Work.WilE7.coreLT_succ.finrank_map_reindex
import Submission.Work.WilE7.Endgame.nullDimLE_finInit

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## Frame-change helpers for `E2.swapStratum` -/

/-- `basePr n m` is `Fin.init ∘ π_{n+1}`, as a function. -/
private lemma basePr_eq_init_comp {n m : ℕ} :
    (Work.WilE7.MainDesign.basePr n m)
      = fun x : Fin ((n + 1) + m) → ℝ => Fin.init (WilkiesDesign.E.projFirst (n + 1) m x) := by
  funext z
  exact (E2.init_projFirst z).symm

private lemma swapStratum_fmt_local {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    (E2.swapStratum T).X.fmt = T.X.fmt := by
  have hr := E2.swapStratum_r T
  simp only [WilkiesDesign.E.SemiPf.fmt]
  rw [hr]
  omega

private lemma swapStratum_projFirst_local {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    WilkiesDesign.E.projFirst n (m + 1) '' absSet (E2.swapStratum T)
      = basePr n m '' absSet T := by
  have hcomp : (WilkiesDesign.E.projFirst n (m + 1))
      = fun x : Fin (n + (m + 1)) → ℝ => Fin.init (Work.WilE7.CoreStep.projTop n m x) := by
    funext z
    exact (Work.WilE7.CoreStep.projTop_init n m z).symm
  calc WilkiesDesign.E.projFirst n (m + 1) '' absSet (E2.swapStratum T)
      = (fun x : Fin (n + (m + 1)) → ℝ =>
            Fin.init (Work.WilE7.CoreStep.projTop n m x)) '' absSet (E2.swapStratum T) := by
          rw [hcomp]
    _ = Fin.init '' (Work.WilE7.CoreStep.projTop n m '' absSet (E2.swapStratum T)) :=
          (Set.image_image Fin.init (Work.WilE7.CoreStep.projTop n m) _).symm
    _ = Fin.init '' (WilkiesDesign.E.projFirst (n + 1) m '' absSet T) := by
          rw [E2.swapStratum_projTop T]
    _ = (fun x : Fin ((n + 1) + m) → ℝ =>
            Fin.init (WilkiesDesign.E.projFirst (n + 1) m x)) '' absSet T :=
          Set.image_image Fin.init (WilkiesDesign.E.projFirst (n + 1) m) _
    _ = basePr n m '' absSet T := by rw [basePr_eq_init_comp]

/-- Monotonicity of the `basePr`-image, derived from the `π_{n+1}`-image inclusion. -/
private lemma basePr_image_mono {n m : ℕ} {S T : Set (Fin ((n + 1) + m) → ℝ)}
    (h : WilkiesDesign.E.projFirst (n + 1) m '' S
      ⊆ WilkiesDesign.E.projFirst (n + 1) m '' T) :
    basePr n m '' S ⊆ basePr n m '' T := by
  calc basePr n m '' S
      = (fun x : Fin ((n + 1) + m) → ℝ =>
            Fin.init (WilkiesDesign.E.projFirst (n + 1) m x)) '' S := by rw [basePr_eq_init_comp]
    _ = Fin.init '' (WilkiesDesign.E.projFirst (n + 1) m '' S) :=
          (Set.image_image Fin.init (WilkiesDesign.E.projFirst (n + 1) m) _).symm
    _ ⊆ Fin.init '' (WilkiesDesign.E.projFirst (n + 1) m '' T) := Set.image_mono h
    _ = (fun x : Fin ((n + 1) + m) → ℝ =>
            Fin.init (WilkiesDesign.E.projFirst (n + 1) m x)) '' T :=
          Set.image_image Fin.init (WilkiesDesign.E.projFirst (n + 1) m) _
    _ = basePr n m '' T := by rw [basePr_eq_init_comp]

/-- The immersed-rank condition of a `π_{n+1}`-rank-full stratum, transported across the frame
change `E2.swapStratum`. -/
private lemma swapStratum_finrank_local {n m : ℕ} (T : Stratum 0 ((n + 1) + m))
    (hrank : ∀ z ∈ T.X.set, projRank T z = (n + 1) + m - T.j) :
    ∀ z ∈ (E2.swapStratum T).X.set, Module.finrank ℝ
      ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1))))
        (jac (E2.swapStratum T) z).ker) = n + (m + 1) - (E2.swapStratum T).j := by
  intro z hz
  have hz' : (fun i : Fin (0 + ((n + 1) + m)) =>
      z ((Work.WilE7.coreLT_succ.swapEquiv0 n m) i)) ∈ T.X.set :=
    (Work.CoreStep.Stratum.reindex_mem (Work.WilE7.coreLT_succ.swapEquiv0 n m) T z).mp hz
  change Module.finrank ℝ
      ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1))))
        (jac (Work.CoreStep.Stratum.reindex (Work.WilE7.coreLT_succ.swapEquiv0 n m) T) z).ker)
      = n + (m + 1)
        - (Work.CoreStep.Stratum.reindex (Work.WilE7.coreLT_succ.swapEquiv0 n m) T).j
  have h1 := Work.WilE7.coreLT_succ.finrank_map_reindex
    (Work.WilE7.coreLT_succ.swapEquiv0 n m) T z
    ((projTopLin n m).comp (absPtLin (n + (m + 1))))
    (basePrLin (n + 1) m)
    (fun v => Work.WilE7.coreLT_succ.projTopLin_absPtLin_swapEquiv0 n m v)
  rw [h1]
  have h2 : Module.finrank ℝ ↥(Submodule.map (basePrLin (n + 1) m)
      (jac T (fun i : Fin (0 + ((n + 1) + m)) =>
        z ((Work.WilE7.coreLT_succ.swapEquiv0 n m) i))).ker) = (n + 1) + m - T.j :=
    hrank _ hz'
  rw [h2]
  rw [show (Work.CoreStep.Stratum.reindex (Work.WilE7.coreLT_succ.swapEquiv0 n m) T).j = T.j
      from rfl]
  omega

/-- The lift of a `NullDimLE` bound through one free coordinate, in the form used below. -/
private lemma lift_nullDimLE {n m K : ℕ} {S : Set (Fin ((n + 1) + m) → ℝ)}
    (h : Work.WilE7.MainDesign.NullDimLE (basePr n m '' S) K) :
    Work.WilE7.MainDesign.NullDimLE (WilkiesDesign.E.projFirst (n + 1) m '' S) (K + 1) := by
  have hinit : Fin.init '' (WilkiesDesign.E.projFirst (n + 1) m '' S) = basePr n m '' S := by
    rw [Set.image_image, basePr_eq_init_comp]
  have h1 := Work.WilE7.Endgame.nullDimLE_finInit
    (X := Fin.init '' (WilkiesDesign.E.projFirst (n + 1) m '' S)) (by rw [hinit]; exact h)
  exact Work.WilE7.MainDesign.NullDimLE.mono h1 (fun z hz => ⟨z, hz, rfl⟩)

/-! ## The two elementary filtering identities for unions over lists -/

private lemma biUnion_filter_eq {α β : Type*} (L : List α) (f : α → Bool) (A : α → Set β)
    (h : ∀ a ∈ L, f a = false → A a = ∅) :
    (⋃ a ∈ L.filter f, A a) = ⋃ a ∈ L, A a := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, (List.mem_filter.mp ha).1, hxa⟩
  · intro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    by_cases hf : f a = true
    · exact ⟨a, List.mem_filter.mpr ⟨ha, hf⟩, hxa⟩
    · have hf' : f a = false := by simpa using hf
      rw [h a ha hf'] at hxa
      exact absurd hxa (Set.notMem_empty x)

private lemma biUnion_filter_filter {α β : Type*} (L : List α) (f g : α → Bool) (A : α → Set β)
    (h : ∀ a ∈ L, f a = false → A a = ∅) :
    (⋃ a ∈ (L.filter f).filter g, A a) = ⋃ a ∈ L.filter g, A a := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨ha', hga⟩ := List.mem_filter.mp ha
    obtain ⟨haL, _⟩ := List.mem_filter.mp ha'
    exact ⟨a, List.mem_filter.mpr ⟨haL, hga⟩, hxa⟩
  · intro x hx
    rw [Set.mem_iUnion₂] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨haL, hga⟩ := List.mem_filter.mp ha
    by_cases hf : f a = true
    · exact ⟨a, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨haL, hf⟩, hga⟩, hxa⟩
    · have hf' : f a = false := by simpa using hf
      rw [h a haL hf'] at hxa
      exact absurd hxa (Set.notMem_empty x)

theorem E2_pieces_of_family (hFC : HypFC) (hE5 : HypE5) (F : ℕ) :
    ∃ (A : ℕ) (P : Polynomial ℕ) (N : MvPolynomial (Fin 2) ℕ),
      ∀ (D k n m K : ℕ) (X : Fin k → SemiPf ((n + 1) + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        (∀ i, NullDimLT (basePr n m '' (X i).set) (K + 1)) →
        ∃ (Pie : List (Fin k × Stratum 0 ((n + 1) + m)))
          (Pie' : List (Fin k × Stratum 0 (n + (m + 1))))
          (Cut : List (Stratum 0 (n + (m + 1)))),
          Pie.length ≤ MvPolynomial.eval ![D, k] N ∧
          Pie'.length ≤ MvPolynomial.eval ![D, k] N ∧
          Cut.length ≤ MvPolynomial.eval ![D, k] N ∧
          (∀ p ∈ Pie, (p.2).Good ∧ (p.2).X.fmt ≤ A ∧ (p.2).deg ≤ P.eval D ∧
            (∀ x : Fin (n + 1) → ℝ, (WilkiesDesign.E.fiber (absSet (p.2)) x).Finite) ∧
            (∀ z ∈ (p.2).X.set, projRank (p.2) z = (n + 1) + m - (p.2).j) ∧
            projFirst (n + 1) m '' absSet (p.2) ⊆ projFirst (n + 1) m '' (X p.1).set) ∧
          (∀ i : Fin k, projFirst (n + 1) m '' (X i).set =
            ⋃ p ∈ Pie.filter (fun p => p.1 = i), projFirst (n + 1) m '' absSet (p.2)) ∧
          Pie' = Pie.map (fun p => (p.1, E2.swapStratum p.2)) ∧
          (∀ p ∈ Pie, (E2.swapStratum (p.2)).Good ∧ (E2.swapStratum (p.2)).X.fmt ≤ A ∧
            (E2.swapStratum (p.2)).deg ≤ P.eval D ∧
            n + (m + 1) - (E2.swapStratum (p.2)).j ≤ K + 1 ∧
            (∀ z ∈ (E2.swapStratum (p.2)).X.set, projRank (E2.swapStratum (p.2)) z ≤ K) ∧
            (∀ z ∈ (E2.swapStratum (p.2)).X.set, Module.finrank ℝ
              ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1))))
                (jac (E2.swapStratum (p.2)) z).ker) = n + (m + 1) - (E2.swapStratum (p.2)).j) ∧
            projTop n m '' absSet (E2.swapStratum (p.2)) ⊆ projFirst (n + 1) m '' (X p.1).set) ∧
          (∀ R ∈ Cut, R.Good ∧ R.X.fmt ≤ A ∧ R.deg ≤ P.eval D ∧
            (∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j) ∧
            n + (m + 1) - R.j ≤ K ∧
            (∃ i : Fin k, projFirst n (m + 1) '' absSet R ⊆ basePr n m '' (X i).set)) ∧
          ((⋃ i : Fin k, basePr n m '' (X i).set) =
            ⋃ R ∈ Cut, projFirst n (m + 1) '' absSet R) := by
  classical
  obtain ⟨A₁, B₁, N₁, hmain⟩ := Work.CoreStep.piPiecesIdx hFC hE5 F
  obtain ⟨A₂, B₂, N₂, hcut⟩ := Work.WilE7.CoreStep.piFamily hFC hE5 F
  refine ⟨max A₁ A₂, B₁ + B₂, N₁ + N₂, ?_⟩
  intro D k n m K X hfmt hnull
  -- the pieces of the `((n+1), m)` cut
  obtain ⟨Pi, hPilen, hPimem, hPicov⟩ := hmain D k n m X hfmt
  -- the reindexed family and its `π_n`-cut
  obtain ⟨X', hX'r, hX'deg, -, hX'proj⟩ :=
    Work.WilE7.coreLT_succ.reindex_family_base (n := n) (m := m) (k := k) X
  have hX' : ∀ i, (X' i).fmt ≤ F ∧ (X' i).deg ≤ D := by
    intro i
    refine ⟨?_, ?_⟩
    · have h : (X' i).fmt = (X i).fmt := by
        simp only [WilkiesDesign.E.SemiPf.fmt]
        rw [hX'r i]
        omega
      rw [h]; exact (hfmt i).1
    · rw [hX'deg i]; exact (hfmt i).2
  obtain ⟨Cut₀, hCut₀len, hCut₀mem, hCut₀cov⟩ := hcut D k n m X' hX'
  -- the dimension input from the hypothesis
  have hNullLE : ∀ i : Fin k, Work.WilE7.MainDesign.NullDimLE (basePr n m '' (X i).set) K :=
    fun i => hnull i
  have hDimLE : ∀ i : Fin k, WilkiesDesign.DimLE (basePr n m '' (X i).set) K :=
    fun i => (hNullLE i).dimLE
  have hLift : ∀ i : Fin k, Work.WilE7.MainDesign.NullDimLE
      (WilkiesDesign.E.projFirst (n + 1) m '' (X i).set) (K + 1) :=
    fun i => lift_nullDimLE (hNullLE i)
  -- the filtering predicates and the assembled lists
  let keepP : Fin k × Stratum 0 ((n + 1) + m) → Bool :=
    fun p => decide (p.2.X.set.Nonempty)
  let Pie : List (Fin k × Stratum 0 ((n + 1) + m)) := Pi.filter keepP
  let keepC : Stratum 0 (n + (m + 1)) → Bool := fun R => decide (R.X.set.Nonempty)
  let Cut : List (Stratum 0 (n + (m + 1))) := Cut₀.filter keepC
  have hPmem : ∀ p ∈ Pie, p ∈ Pi := fun p hp => (List.mem_filter.mp hp).1
  have hPne : ∀ p ∈ Pie, (p.2).X.set.Nonempty :=
    fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2
  have hCne : ∀ R ∈ Cut, R.X.set.Nonempty :=
    fun R hR => of_decide_eq_true (List.mem_filter.mp hR).2
  have hCmem : ∀ R ∈ Cut, R ∈ Cut₀ := fun R hR => (List.mem_filter.mp hR).1
  have hkeepP : ∀ a ∈ Pi, keepP a = false →
      WilkiesDesign.E.projFirst (n + 1) m '' absSet (a.2) = ∅ := by
    intro a _ ha
    have hne : (a.2).X.set = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false ha)
    simp [Work.WilE7.MainDesign.absSet, hne]
  have hkeepC : ∀ a ∈ Cut₀, keepC a = false →
      WilkiesDesign.E.projFirst n (m + 1) '' absSet a = ∅ := by
    intro a _ ha
    have hne : a.X.set = ∅ := Set.not_nonempty_iff_eq_empty.mp (of_decide_eq_false ha)
    simp [Work.WilE7.MainDesign.absSet, hne]
  -- bound helpers
  have hBN₁ : B₁.eval D ≤ (B₁ + B₂).eval D := by
    rw [Polynomial.eval_add]
    exact Nat.le_add_right _ _
  have hBN₂ : B₂.eval D ≤ (B₁ + B₂).eval D := by
    rw [Polynomial.eval_add]
    exact Nat.le_add_left _ _
  have hNN₁ : MvPolynomial.eval ![D, k] N₁ ≤ MvPolynomial.eval ![D, k] (N₁ + N₂) := by
    rw [MvPolynomial.eval_add]
    exact Nat.le_add_right _ _
  have hNN₂ : MvPolynomial.eval ![D, k] N₂ ≤ MvPolynomial.eval ![D, k] (N₁ + N₂) := by
    rw [MvPolynomial.eval_add]
    exact Nat.le_add_left _ _
  refine ⟨Pie, Pie.map (fun p => (p.1, E2.swapStratum p.2)), Cut, ?_, ?_, ?_, ?_, ?_, rfl,
    ?_, ?_, ?_⟩
  · -- `Pie.length`
    exact le_trans (le_trans (List.length_filter_le keepP Pi) hPilen) hNN₁
  · -- `Pie'.length`
    rw [List.length_map]
    exact le_trans (le_trans (List.length_filter_le keepP Pi) hPilen) hNN₁
  · -- `Cut.length`
    exact le_trans (le_trans (List.length_filter_le keepC Cut₀) hCut₀len) hNN₂
  · -- the pieces
    intro p hp
    obtain ⟨hgood, hfmtp, hdegp, hfinp, hrankp, hsubp⟩ := hPimem p (hPmem p hp)
    exact ⟨hgood, le_trans hfmtp (le_max_left _ _), le_trans hdegp hBN₁, hfinp, hrankp,
      hsubp⟩
  · -- the per-index coverage
    intro i
    rw [hPicov i]
    exact (biUnion_filter_filter Pi keepP (fun p => decide (p.1 = i))
      (fun p => WilkiesDesign.E.projFirst (n + 1) m '' absSet (p.2)) hkeepP).symm
  · -- the transported pieces
    intro p hp
    obtain ⟨hgood, hfmtp, hdegp, hfinp, hrankp, hsubp⟩ := hPimem p (hPmem p hp)
    have hne : (p.2).X.set.Nonempty := hPne p hp
    have hbase : basePr n m '' absSet (p.2) ⊆ basePr n m '' (X p.1).set := basePr_image_mono hsubp
    refine ⟨(E2.swapStratum_good (p.2)).mpr hgood, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- format
      rw [swapStratum_fmt_local (p.2)]
      exact le_trans hfmtp (le_max_left _ _)
    · -- degree
      rw [E2.swapStratum_deg (p.2)]
      exact le_trans hdegp hBN₁
    · -- the dimension bound `dim ≤ K+1`
      rw [E2.swapStratum_j (p.2)]
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨z, hz⟩ := hne
      have hrank := hrankp z hz
      have hK : K + 1 < Work.WilE7.MainDesign.projRank (p.2) z := by rw [hrank]; omega
      have hnot := Work.WilE7.DimAPI.not_dimLE_of_projRank (p.2) hgood hz hK
      have hle : Work.WilE7.MainDesign.NullDimLE
          (WilkiesDesign.E.projFirst (n + 1) m '' absSet (p.2)) (K + 1) :=
        Work.WilE7.MainDesign.NullDimLE.mono (hLift (p.1)) hsubp
      exact hnot hle.dimLE
    · -- the `π_n`-rank bound
      have hsub : WilkiesDesign.E.projFirst n (m + 1) '' absSet (E2.swapStratum (p.2))
          ⊆ basePr n m '' (X p.1).set := by
        rw [swapStratum_projFirst_local (p.2)]
        exact hbase
      exact projRank_le_of_dimLE ((E2.swapStratum_good (p.2)).mpr hgood) (hDimLE (p.1)) hsub
    · -- the immersed-rank condition
      exact swapStratum_finrank_local (p.2) hrankp
    · -- the projection inclusion
      rw [E2.swapStratum_projTop (p.2)]
      exact hsubp
  · -- the cut pieces
    intro R hR
    obtain ⟨hgood, hfmt, hdeg, hfin, hrank, hprov⟩ := hCut₀mem R (hCmem R hR)
    obtain ⟨i, hi⟩ := hprov
    have hiproj : WilkiesDesign.E.projFirst n (m + 1) '' absSet R
        ⊆ basePr n m '' (X i).set := by
      rw [← hX'proj i]
      exact hi
    obtain ⟨z, hz⟩ := hCne R hR
    have hleK : n + (m + 1) - R.j ≤ K := by
      have h := projRank_le_of_dimLE hgood (hDimLE i) hiproj z hz
      rwa [hrank z hz] at h
    exact ⟨hgood, le_trans hfmt (le_max_right _ _), le_trans hdeg hBN₂, hrank, hleK,
      ⟨i, hiproj⟩⟩
  · -- the `π_n`-coverage
    rw [show (⋃ i : Fin k, basePr n m '' (X i).set)
        = ⋃ i : Fin k, WilkiesDesign.E.projFirst n (m + 1) '' (X' i).set from
      Set.iUnion_congr (fun i => (hX'proj i).symm)]
    rw [hCut₀cov]
    exact (biUnion_filter_eq Cut₀ keepC (fun R => WilkiesDesign.E.projFirst n (m + 1) '' absSet R)
      hkeepC).symm

end Work.WilE7.Endgame
