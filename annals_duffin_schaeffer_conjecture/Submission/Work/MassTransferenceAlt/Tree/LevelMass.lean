/-
# The mass of the levels of the Cantor tree, and the level measures

This file collects the material needed for the lower bound on the Hausdorff measure of the
Cantor set of the Beresnevich–Velani construction (`cantorHausdorff`, proved in
`Submission.Work.MassTransferenceAlt.Tree.cantorHausdorff`).

* `meetMass d c ρ η T N x r` is the total mass of the balls of level `N` meeting the interval
  `Iv x r`;
* `rmin0 d c ρ η T` is the smallest radius of a ball of level `0`; an interval of radius
  `≤ rmin0` meets at most one ball of level `0` (`hits_unique_level0`);
* `meetMass_le_of_small` is the key estimate: for such an interval the meeting mass of a
  sufficiently deep level is at most `400 (2 r)^d / η` up to an arbitrarily small `δ`;
* `levelMeasure d c ρ η T N` is the probability measure on `ℝ` which distributes the mass of
  level `N` uniformly on each of the balls of that level.  It is the building block of the
  mass distribution on the Cantor set.
-/
import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data
import Submission.Work.MassTransferenceAlt.Tree.MassLe
import Submission.Work.MassTransferenceAlt.Tree.MassSum
import Submission.Work.MassTransferenceAlt.Tree.massAncestor
import Submission.Work.MassTransferenceAlt.Tree.levelBoundReal
import Submission.Work.MassTransferenceAlt.Tree.radiusLe
import Submission.Work.MassTransferenceAlt.Tree.childrenMem
import Submission.Work.MassTransferenceAlt.Tree.ballSubsetAnc
import Submission.Work.MassTransferenceAlt.Tree.ancMem
import Submission.Work.MassTransferenceAlt.Tree.massMono

namespace Work.MassTransferenceAlt.Tree.Hausdorff

open Work.MassTransferenceAlt MeasureTheory Set Metric
open scoped ENNReal NNReal


/-- The total mass of the balls of level `N` meeting `Iv x r`. -/
noncomputable def meetMass (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    (N : ℕ) (x r : ℝ) : ℝ :=
  ∑ i ∈ (T.lev N).filter (fun i => hits c ρ x r i), Mass d c ρ η T N (some i)

lemma meetMass_eq (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ) (x r : ℝ) :
    meetMass d c ρ η T N x r
      = ∑ i ∈ (T.lev N).filter (fun i => hits c ρ x r i), Mass d c ρ η T N (some i) := rfl

/-- **Nonnegativity of the mass.** -/
lemma mass_nonneg (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ∀ (n i : ℕ), i ∈ T.lev n → 0 ≤ Mass d c ρ η T n (some i) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      rw [show Mass d c ρ η T 0 (some i) =
          vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) from by rw [Mass]; simp [hi]]
      refine div_nonneg ?_ (Finset.sum_nonneg fun j hj => ?_)
      · exact Real.rpow_nonneg (by linarith [(T.good 0 i hi).1]) _
      · exact Real.rpow_nonneg (by linarith [(T.good 0 j hj).1]) _
  | succ n ih =>
      intro i hi
      obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
      rw [show Mass d c ρ η T (n+1) (some i) =
          (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter
            (fun j => T.par (n+1) j = some B), vf d ρ j))
            * Mass d c ρ η T n (some B) from by rw [Mass]; simp [hi, hpar]]
      refine mul_nonneg (div_nonneg ?_ (Finset.sum_nonneg fun j hj => ?_)) (ih B hB)
      · exact Real.rpow_nonneg (by linarith [(T.good (n+1) i hi).1]) _
      · exact Real.rpow_nonneg (by linarith [(T.good (n+1) j (Finset.mem_filter.mp hj).1).1]) _

/-- The mass at `none` is non-negative. -/
lemma mass_none_nonneg (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    0 ≤ Mass d c ρ η T n none := by
  cases n with
  | zero => rw [show Mass d c ρ η T 0 none = 1 from rfl]; norm_num
  | succ n => rw [show Mass d c ρ η T (n+1) none = 0 from rfl]

/-- A positive `ρ ≤ 1` is at most its `d`-th power, for `d ≤ 1`. -/
lemma le_rpow_self {d ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hd1 : d ≤ 1) : ρ ≤ ρ ^ d := by
  have h := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show d ≤ 1 from hd1) (y := (1:ℝ))
  rwa [Real.rpow_one] at h

/-- A level is non-empty. -/
lemma rootLev_nonempty (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    (T.lev 0).Nonempty := by
  obtain ⟨i, hi, _⟩ :=
    T.root_loc.2.2.2.2.2.2.1 0 (lt_of_lt_of_le Nat.zero_lt_one (nsubRoot_pos η))
  exact ⟨i, hi⟩

lemma lev_nonempty (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    (T.lev n).Nonempty := by
  induction n with
  | zero => exact rootLev_nonempty d c ρ η T
  | succ n ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj, _⟩ := childrenMem d c ρ η T hi
      exact ⟨j, hj⟩

/-- The interval of a child lies in the interval of its parent. -/
lemma iv_subset_of_par (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {n i B : ℕ} (hi : i ∈ T.lev (n+1)) (hpar : T.par (n+1) i = some B) :
    Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B) := by
  obtain ⟨B', hB', hpar'⟩ := T.par_mem n i hi
  rw [hpar] at hpar'
  simp only [Option.some.injEq] at hpar'
  subst hpar'
  have hmem : i ∈ (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B) :=
    Finset.mem_filter.mpr ⟨hi, hpar⟩
  have hIv : Fenl d c ρ i ⊆ Iv (c B) (ρ B) := (T.loc n B hB').2.2.1 i hmem
  have hgood := T.good (n+1) i hi
  have hle : ρ i ≤ (ρ i) ^ d :=
    le_rpow_self hgood.1 (le_trans hgood.2.1 (Rabs_le_one hd1)) (le_of_lt hd1)
  calc Iv (c i) (ρ i) ⊆ Iv (c i) ((ρ i) ^ d) := Iv_mono hle
    _ = Fenl d c ρ i := rfl
    _ ⊆ Iv (c B) (ρ B) := hIv

/-- The level sets are nested. -/
lemma levSet_succ_subset (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    levSet T (n+1) ⊆ levSet T n := by
  rintro z hz
  rw [levSet] at hz ⊢
  rw [Set.mem_iUnion₂] at hz ⊢
  obtain ⟨i, hi, hzi⟩ := hz
  obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
  exact ⟨B, hB, iv_subset_of_par d hd1 c ρ η T hi hpar hzi⟩

lemma levSet_anti (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {m n : ℕ} (h : n ≤ m) : levSet T m ⊆ levSet T n := by
  induction m with
  | zero => simp only [Nat.le_zero] at h; subst h; exact subset_rfl
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact subset_rfl
      · exact (levSet_succ_subset d hd1 c ρ η T m).trans (ih (Nat.lt_succ_iff.mp hlt))

/-- All balls of all levels lie in `[0,1]`. -/
lemma levSet_subset_Icc (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    levSet T n ⊆ Set.Icc 0 1 := by
  rintro z hz
  rw [levSet, Set.mem_iUnion₂] at hz
  obtain ⟨i, hi, hzi⟩ := hz
  have hgood := T.good n i hi
  rw [Iv, Set.mem_Icc] at hzi
  exact ⟨le_trans hgood.2.2.1 hzi.1, le_trans hzi.2 hgood.2.2.2⟩

lemma levSet_nonempty (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    (levSet T n).Nonempty := by
  obtain ⟨i, hi⟩ := lev_nonempty d c ρ η T n
  obtain ⟨z, hz⟩ := Iv_nonempty (le_of_lt (T.good n i hi).1)
  exact ⟨z, Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩⟩

lemma isClosed_levSet (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    IsClosed (levSet T n) := by
  have h : levSet T n = ⋃ i : {i // i ∈ T.lev n}, Iv (c i) (ρ i) := by
    rw [levSet]
    ext z
    simp only [Set.mem_iUnion, Set.mem_iUnion₂, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, hz⟩; exact ⟨⟨i, hi⟩, hz⟩
    · rintro ⟨⟨i, hi⟩, hz⟩; exact ⟨i, hi, hz⟩
  rw [h]
  exact isClosed_iUnion_of_finite fun i => isClosed_Iv _ _

/-- The Cantor set is closed. -/
lemma isClosed_cantor (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    IsClosed (cantor T) := isClosed_iInter fun n => isClosed_levSet d c ρ η T n

lemma cantor_subset_Icc (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    cantor T ⊆ Set.Icc 0 1 :=
  (Set.iInter_subset _ 0).trans (levSet_subset_Icc d c ρ η T 0)

lemma isCompact_cantor (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    IsCompact (cantor T) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_cantor d c ρ η T, (isBounded_Icc 0 1).subset (cantor_subset_Icc d c ρ η T)⟩

/-! ### Every node meets the Cantor set -/

/-- Every node of the tree meets the Cantor set: the deeper levels of the tree form a
decreasing sequence of non-empty compact sets inside the node. -/
lemma cantor_inter_iv_nonempty (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {N i : ℕ} (hi : i ∈ T.lev N) : (cantor T ∩ Iv (c i) (ρ i)).Nonempty := by
  classical
  have key : ∀ m, ∃ j, j ∈ T.lev (N + m) ∧ Iv (c j) (ρ j) ⊆ Iv (c i) (ρ i) := by
    intro m
    induction m with
    | zero => exact ⟨i, by simpa using hi, subset_rfl⟩
    | succ m ih =>
        obtain ⟨j, hj, hsub⟩ := ih
        obtain ⟨j', hj', hpar⟩ := childrenMem d c ρ η T hj
        refine ⟨j', ?_, ?_⟩
        · rw [Nat.add_succ]; exact hj'
        · exact (iv_subset_of_par d hd1 c ρ η T hj' hpar).trans hsub
  set t : ℕ → Set ℝ := fun m => Iv (c i) (ρ i) ∩ levSet T (N + m) with ht
  have hne : ∀ m, (t m).Nonempty := by
    intro m
    obtain ⟨j, hj, hsub⟩ := key m
    obtain ⟨z, hz⟩ := Iv_nonempty (le_of_lt (T.good (N + m) j hj).1)
    exact ⟨z, hsub hz, Set.mem_iUnion₂.mpr ⟨j, hj, hz⟩⟩
  have hdir : Directed (· ⊇ ·) t := by
    intro m m'
    refine ⟨max m m', ?_, ?_⟩
    · intro z hz
      exact ⟨hz.1, levSet_anti d hd1 c ρ η T (by omega) hz.2⟩
    · intro z hz
      exact ⟨hz.1, levSet_anti d hd1 c ρ η T (by omega) hz.2⟩
  have hcl : ∀ m, IsClosed (t m) := fun m =>
    (isClosed_Iv _ _).inter (isClosed_levSet d c ρ η T (N + m))
  have hcomp : ∀ m, IsCompact (t m) := fun m =>
    (isCompact_Iv (c i) (ρ i)).of_isClosed_subset (hcl m) Set.inter_subset_left
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcomp hcl
  have hzm : ∀ m, z ∈ t m := fun m => Set.mem_iInter.mp hz m
  refine ⟨z, ?_, (hzm 0).1⟩
  rw [cantor]
  refine Set.mem_iInter.mpr fun n => ?_
  rcases le_or_gt n N with hn | hn
  · exact levSet_anti d hd1 c ρ η T hn (hzm 0).2
  · have hthis : n = N + (n - N) := (Nat.add_sub_of_le (le_of_lt hn)).symm
    rw [hthis]
    exact (hzm (n - N)).2

/-! ### The smallest radius at level `0` -/

/-- The smallest radius of a ball of level `0`. -/
noncomputable def rmin0 (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) : ℝ :=
  (T.lev 0).inf' (rootLev_nonempty d c ρ η T) ρ

lemma rmin0_pos (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) : 0 < rmin0 d c ρ η T := by
  rw [rmin0]
  refine Finset.inf'_mem {y : ℝ | 0 < y} ?_ (T.lev 0) (rootLev_nonempty d c ρ η T) ρ ?_
  · intro x hx y hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    exact lt_min hx hy
  · intro i hi
    exact (T.good 0 i hi).1

lemma rmin0_le (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) {j : ℕ}
    (hj : j ∈ T.lev 0) : rmin0 d c ρ η T ≤ ρ j := by
  rw [rmin0]
  exact Finset.inf'_le ρ hj

/-- Two distinct balls of level `0` cannot both meet an interval of radius `≤ rmin0`. -/
lemma hits_unique_level0 (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {x r : ℝ} (hr : r ≤ rmin0 d c ρ η T) {j j' : ℕ} (hj : j ∈ T.lev 0) (hj' : j' ∈ T.lev 0)
    (hne : j ≠ j') : ¬ (hits c ρ x r j ∧ hits c ρ x r j') := by
  rintro ⟨h1, h2⟩
  have hdisj : Disjoint (Iv (c j) (3 * ρ j)) (Iv (c j') (3 * ρ j')) :=
    T.root_loc.2.2.2.2.1 j hj j' hj' hne
  have h3j : 0 ≤ 3 * ρ j := by linarith [(T.good 0 j hj).1]
  have h3j' : 0 ≤ 3 * ρ j' := by linarith [(T.good 0 j' hj').1]
  have hlt : 3 * ρ j + 3 * ρ j' < |c j - c j'| := (disjoint_Iv_iff h3j h3j').mp hdisj
  rw [hits] at h1 h2
  have hle : |c j - c j'| ≤ 2 * r + ρ j + ρ j' := by
    have hA : |c j - c j'| ≤ |x - c j| + |x - c j'| := by
      calc |c j - c j'| = |(c j - x) + (x - c j')| := by ring_nf
        _ ≤ |c j - x| + |x - c j'| := abs_add_le _ _
        _ = |x - c j| + |x - c j'| := by rw [abs_sub_comm (c j) x]
    linarith
  have hsum : ρ j + ρ j' < r := by linarith
  have h2r : 2 * rmin0 d c ρ η T ≤ ρ j + ρ j' := by
    have h1' := rmin0_le d c ρ η T hj
    have h2' := rmin0_le d c ρ η T hj'
    linarith
  have hρj : 0 < ρ j := (T.good 0 j hj).1
  have hρj' : 0 < ρ j' := (T.good 0 j' hj').1
  linarith

/-- If `Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B)` then `hits` propagates from `i` to `B`. -/
lemma hits_of_iv_subset {c ρ : ℕ → ℝ} {x r : ℝ} (hr : 0 ≤ r) {i B : ℕ} (hρi : 0 ≤ ρ i)
    (hρB : 0 ≤ ρ B) (hsub : Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B)) (h : hits c ρ x r i) :
    hits c ρ x r B := by
  have hne : (Iv x r ∩ Iv (c i) (ρ i)).Nonempty := (hits_iff hr hρi).mpr h
  obtain ⟨z, hz1, hz2⟩ := hne
  exact (hits_iff hr hρB).mp ⟨z, hz1, hsub hz2⟩

/-! ### The key estimate on the meeting mass of a level -/

/-- **The key estimate.**  For an interval `Iv x r` of radius `r ≤ 1/2` meeting at most one
ball of level `0`, the mass of the balls of a sufficiently deep level meeting `Iv x r` is at
most `400 * (2 * r) ^ d / η` (up to an arbitrarily small `δ`). -/
lemma meetMass_le_of_small (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (T : TreeData d c ρ η) {x r : ℝ} (hr : 0 ≤ r) (hr1 : 2 * r ≤ 1)
    (huniq0 : ∀ j ∈ T.lev 0, ∀ j' ∈ T.lev 0, j ≠ j' → ¬ (hits c ρ x r j ∧ hits c ρ x r j'))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N, 1 ≤ N ∧ meetMass d c ρ η T N x r ≤ 400 * (2 * r) ^ d / η + δ := by
  classical
  by_cases hex : ∃ m, 2 ≤ ((T.lev m).filter (fun i => hits c ρ x r i)).card
  · -- the first level meeting the interval in at least two balls
    have hn2 : 2 ≤ ((T.lev (Nat.find hex)).filter (fun i => hits c ρ x r i)).card :=
      Nat.find_spec hex
    have hprev : ∀ k < Nat.find hex,
        ¬ 2 ≤ ((T.lev k).filter (fun i => hits c ρ x r i)).card :=
      fun k hk => Nat.find_min hex hk
    have hn1 : 1 ≤ Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · exfalso
        have hn2' : 2 ≤ ((T.lev 0).filter (fun i => hits c ρ x r i)).card := by
          have h := hn2
          rw [h0] at h
          exact h
        have hc : 1 < ((T.lev 0).filter (fun i => hits c ρ x r i)).card := by omega
        obtain ⟨j, hj, j', hj', hne⟩ := Finset.one_lt_card.mp hc
        exact huniq0 j (Finset.mem_filter.mp hj).1 j' (Finset.mem_filter.mp hj').1 hne
          ⟨(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hj').2⟩
      · exact hpos
    set n := Nat.find hex with hn
    have hn1' : 1 ≤ n := hn1
    have hn2' : 2 ≤ ((T.lev n).filter (fun i => hits c ρ x r i)).card := hn2
    have hprev' : ∀ k < n, ¬ 2 ≤ ((T.lev k).filter (fun i => hits c ρ x r i)).card := hprev
    -- the level `n-1` meets the interval in exactly one ball `B`
    have hcard1 : ((T.lev (n - 1)).filter (fun i => hits c ρ x r i)).card = 1 := by
      have hle : ((T.lev (n - 1)).filter (fun i => hits c ρ x r i)).card ≤ 1 := by
        have := hprev' (n - 1) (by omega)
        omega
      have hge : 1 ≤ ((T.lev (n - 1)).filter (fun i => hits c ρ x r i)).card := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < ((T.lev n).filter
          (fun i => hits c ρ x r i)).card by omega)
        have hhit : hits c ρ x r i := (Finset.mem_filter.mp hi).2
        have hilev : i ∈ T.lev n := (Finset.mem_filter.mp hi).1
        have hm : n - 1 + 1 = n := Nat.sub_add_cancel hn1'
        have hi' : i ∈ T.lev (n - 1 + 1) := by rw [hm]; exact hilev
        obtain ⟨B, hB, hpar⟩ := T.par_mem (n - 1) i hi'
        refine Finset.card_pos.mpr ⟨B, Finset.mem_filter.mpr ⟨hB, ?_⟩⟩
        exact hits_of_iv_subset hr (le_of_lt (T.good n i hilev).1) (le_of_lt (T.good (n-1) B hB).1)
          (iv_subset_of_par d hd1 c ρ η T hi' hpar) hhit
      omega
    obtain ⟨B, hBs⟩ := Finset.card_eq_one.mp hcard1
    have hBmem : B ∈ T.lev (n - 1) :=
      (Finset.mem_filter.mp (hBs ▸ Finset.mem_singleton_self B)).1
    have huniqB : ∀ B' ∈ T.lev (n - 1), (Iv x r ∩ Iv (c B') (ρ B')).Nonempty → B' = B := by
      intro B' hB' hmeet
      have hhit' : hits c ρ x r B' := (hits_iff hr (le_of_lt (T.good (n-1) B' hB').1)).mp hmeet
      have hmem : B' ∈ (T.lev (n - 1)).filter (fun i => hits c ρ x r i) :=
        Finset.mem_filter.mpr ⟨hB', hhit'⟩
      rw [hBs] at hmem
      simpa using hmem
    have hmeet2 : 2 ≤ ((T.lev n).filter
        (fun i => T.par n i = some B ∧ hits c ρ x r i)).card := by
      have hsub : (T.lev n).filter (fun i => hits c ρ x r i)
          ⊆ (T.lev n).filter (fun i => T.par n i = some B ∧ hits c ρ x r i) := by
        intro i hi
        obtain ⟨hilev, hihit⟩ := Finset.mem_filter.mp hi
        have hm : n - 1 + 1 = n := Nat.sub_add_cancel hn1'
        have hi' : i ∈ T.lev (n - 1 + 1) := by rw [hm]; exact hilev
        obtain ⟨B'', hB'', hpar''⟩ := T.par_mem (n - 1) i hi'
        have hB''hit : hits c ρ x r B'' :=
          hits_of_iv_subset hr (le_of_lt (T.good n i hilev).1)
            (le_of_lt (T.good (n-1) B'' hB'').1) (iv_subset_of_par d hd1 c ρ η T hi' hpar'') hihit
        have heq : B'' = B :=
          huniqB B'' hB'' ((hits_iff hr (le_of_lt (T.good (n-1) B'' hB'').1)).mpr hB''hit)
        rw [heq] at hpar''
        refine Finset.mem_filter.mpr ⟨hilev, ?_, hihit⟩
        rw [← hm]
        exact hpar''
      exact le_trans hn2' (Finset.card_le_card hsub)
    have hbound : meetMass d c ρ η T n x r ≤ 400 * (2 * r) ^ d / η :=
      levelBoundReal d hd0 hd1 c ρ η hη T n hn1' B hBmem hr hr1 hmeet2 huniqB
    have hmono : meetMass d c ρ η T (max 1 n) x r ≤ meetMass d c ρ η T n x r :=
      massMono d hd0 hd1 c ρ η T (x := x) (r := r) (n := n) (N := max 1 n) hn1'
        (le_max_right _ _)
    exact ⟨max 1 n, le_max_left _ _, le_trans hmono (le_trans hbound (le_add_of_nonneg_right hδ.le))⟩
  · -- every level meets the interval in at most one ball
    push_neg at hex
    have hRpos : 0 < Rabs d := Rabs_pos d
    have hηδ : 0 < δ * η := mul_pos hδ hη
    have hroot : 0 < (δ * η) ^ (1 / d) := Real.rpow_pos_of_pos hηδ _
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * Rabs d / (δ * η) ^ (1 / d))
    refine ⟨max 1 N, le_max_left _ _, ?_⟩
    set M := max 1 N with hM
    have hMN : N ≤ M := le_max_right _ _
    have hpow : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ M :=
      pow_le_pow_right₀ (by norm_num) hMN
    have hbd : 2 * Rabs d / 2 ^ M ≤ (δ * η) ^ (1 / d) := by
      have h2M : 0 < (2 : ℝ) ^ M := by positivity
      have hc : 0 < (δ * η) ^ (1 / d) := hroot
      rw [div_le_iff₀ h2M]
      have key : 2 * Rabs d / (δ * η) ^ (1 / d) ≤ (2 : ℝ) ^ M := by
        have h3 : (2 * Rabs d) / (δ * η) ^ (1 / d) < (N : ℝ) := hN
        have h4 : (N : ℝ) ≤ (2 : ℝ) ^ N := by
          exact_mod_cast le_of_lt (Nat.lt_two_pow_self (n := N))
        have h5 : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ M := hpow
        linarith
      calc 2 * Rabs d = (2 * Rabs d / (δ * η) ^ (1 / d)) * (δ * η) ^ (1 / d) :=
            (div_mul_cancel₀ _ (ne_of_gt hc)).symm
        _ ≤ (2 : ℝ) ^ M * (δ * η) ^ (1 / d) := mul_le_mul_of_nonneg_right key hc.le
        _ = (δ * η) ^ (1 / d) * 2 ^ M := by ring
    have hterm : ∀ i ∈ (T.lev M).filter (fun i => hits c ρ x r i),
        Mass d c ρ η T M (some i) ≤ δ := by
      intro i hi
      have hilev : i ∈ T.lev M := (Finset.mem_filter.mp hi).1
      have hρi : 0 < ρ i := (T.good M i hilev).1
      have hle1 : Mass d c ρ η T M (some i) ≤ vf d ρ i / η :=
        MassLe d hd0 hd1 c ρ η hη T M i hilev
      have hle2 : ρ i ≤ Rabs d / 2 ^ M := radiusLe d hd0 hd1 c ρ η T M hilev
      have hle3 : (2 * ρ i) ^ d ≤ (2 * Rabs d / 2 ^ M) ^ d := by
        have h2 : 2 * ρ i ≤ 2 * (Rabs d / 2 ^ M) := by linarith
        have h3 : 2 * (Rabs d / 2 ^ M) = 2 * Rabs d / 2 ^ M := by ring
        rw [← h3]
        exact Real.rpow_le_rpow (by linarith) h2 hd0.le
      have hle4 : (2 * Rabs d / 2 ^ M) ^ d ≤ ((δ * η) ^ (1 / d)) ^ d :=
        Real.rpow_le_rpow (by positivity) hbd hd0.le
      have h5 : ((δ * η) ^ (1 / d)) ^ d = δ * η := by
        rw [← Real.rpow_mul hηδ.le]
        have : 1 / d * d = 1 := by field_simp
        rw [this, Real.rpow_one]
      calc Mass d c ρ η T M (some i) ≤ vf d ρ i / η := hle1
        _ = (2 * ρ i) ^ d / η := rfl
        _ ≤ (2 * Rabs d / 2 ^ M) ^ d / η := by gcongr
        _ ≤ ((δ * η) ^ (1 / d)) ^ d / η := by gcongr
        _ = δ := by rw [h5]; field_simp
    have hcard : ((T.lev M).filter (fun i => hits c ρ x r i)).card ≤ 1 := by
      have := hex M; omega
    have hfinal : meetMass d c ρ η T M x r ≤ δ := by
      rw [meetMass]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
      · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; exact hδ.le
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
        rw [hi, Finset.sum_singleton]
        exact hterm i (by rw [hi]; exact Finset.mem_singleton_self i)
    have hnn : 0 ≤ 400 * (2 * r) ^ d / η := by
      apply div_nonneg _ hη.le
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
    linarith



/-- `rmin0` is at most `Rabs d`. -/
lemma rmin0_le_Rabs (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    rmin0 d c ρ η T ≤ Rabs d := by
  obtain ⟨j, hj⟩ := rootLev_nonempty d c ρ η T
  exact (rmin0_le d c ρ η T hj).trans (T.good 0 j hj).2.1

/-- **The meeting mass is non-increasing in the level.** -/
lemma meetMass_mono (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) {x r : ℝ} {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    meetMass d c ρ η T N x r ≤ meetMass d c ρ η T n x r :=
  massMono d hd0 hd1 c ρ η T hn hnN

/-! ### The level measures -/

/-- **The measure of a level.**  The mass of each ball of level `N` is spread uniformly on it. -/
noncomputable def levelMeasure (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ) :
    Measure ℝ :=
  ∑ i ∈ T.lev N, ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) •
    volume.restrict (Iv (c i) (ρ i))

lemma levelMeasure_apply (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ)
    (A : Set ℝ) :
    levelMeasure d c ρ η T N A
      = ∑ i ∈ T.lev N, ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) *
          ((volume.restrict (Iv (c i) (ρ i))) A) := by
  classical
  rw [levelMeasure]
  induction T.lev N using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.add_apply, Measure.smul_apply, ih]
      rfl

/-- The `f`-volume part of the weights of the level measure collapses. -/
lemma levelMeasure_weight_cancel (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {N i : ℕ} (hi : i ∈ T.lev N) :
    ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) * (ENNReal.ofReal (2 * ρ i))
      = ENNReal.ofReal (Mass d c ρ η T N (some i)) := by
  have hρ : 0 < ρ i := (T.good N i hi).1
  have h2ρ : (0:ℝ) < 2 * ρ i := by linarith
  rw [← ENNReal.ofReal_mul (div_nonneg (mass_nonneg d c ρ η T N i hi) (le_of_lt h2ρ))]
  congr 1
  field_simp

/-- The level measure is a probability measure. -/
lemma levelMeasure_univ (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ) :
    levelMeasure d c ρ η T N Set.univ = 1 := by
  classical
  rw [levelMeasure_apply]
  have hterm : ∀ i ∈ T.lev N,
      ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) *
        ((volume.restrict (Iv (c i) (ρ i))) Set.univ)
      = ENNReal.ofReal (Mass d c ρ η T N (some i)) := by
    intro i hi
    have hρ : 0 < ρ i := (T.good N i hi).1
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, volume_Iv _ _ hρ.le]
    exact levelMeasure_weight_cancel d c ρ η T hi
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun i hi => mass_nonneg d c ρ η T N i hi),
    MassSum d c ρ η T N]
  norm_num

/-- The level measure gives full measure to the union of the balls of its level, hence to every
coarser level. -/
lemma levelMeasure_levSet (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {m N : ℕ} (hm : m ≤ N) : levelMeasure d c ρ η T N (levSet T m) = 1 := by
  classical
  have hsub : ∀ i ∈ T.lev N, Iv (c i) (ρ i) ⊆ levSet T m := by
    intro i hi
    have h1 : Iv (c i) (ρ i) ⊆ levSet T N := by
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hz⟩
    exact h1.trans (levSet_anti d hd1 c ρ η T hm)
  rw [levelMeasure_apply]
  have hterm : ∀ i ∈ T.lev N,
      ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) *
        ((volume.restrict (Iv (c i) (ρ i))) (levSet T m))
      = ENNReal.ofReal (Mass d c ρ η T N (some i)) := by
    intro i hi
    have hρ : 0 < ρ i := (T.good N i hi).1
    have hmeas : MeasurableSet (levSet T m) := (isClosed_levSet d c ρ η T m).measurableSet
    have hI : levSet T m ∩ Iv (c i) (ρ i) = Iv (c i) (ρ i) :=
      Set.inter_eq_right.mpr (hsub i hi)
    rw [Measure.restrict_apply hmeas, hI, volume_Iv _ _ hρ.le]
    exact levelMeasure_weight_cancel d c ρ η T hi
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun i hi => mass_nonneg d c ρ η T N i hi),
    MassSum d c ρ η T N]
  norm_num

/-- **The level measure of an interval is at most the mass of the balls of the level meeting
it.** -/
lemma levelMeasure_le_meetMass (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N : ℕ)
    {x r : ℝ} (hr : 0 ≤ r) :
    levelMeasure d c ρ η T N (Iv x r) ≤ ENNReal.ofReal (meetMass d c ρ η T N x r) := by
  classical
  rw [levelMeasure_apply]
  have hterm : ∀ i ∈ T.lev N,
      ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) *
        ((volume.restrict (Iv (c i) (ρ i))) (Iv x r))
      ≤ (if hits c ρ x r i then ENNReal.ofReal (Mass d c ρ η T N (some i)) else 0) := by
    intro i hi
    have hρ : 0 < ρ i := (T.good N i hi).1
    by_cases hhit : hits c ρ x r i
    · rw [if_pos hhit]
      have hle : (volume.restrict (Iv (c i) (ρ i))) (Iv x r) ≤ ENNReal.ofReal (2 * ρ i) := by
        rw [Measure.restrict_apply (isClosed_Iv x r).measurableSet]
        calc volume (Iv x r ∩ Iv (c i) (ρ i)) ≤ volume (Iv (c i) (ρ i)) :=
              measure_mono Set.inter_subset_right
          _ = ENNReal.ofReal (2 * ρ i) := volume_Iv _ _ hρ.le
      calc ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) *
            ((volume.restrict (Iv (c i) (ρ i))) (Iv x r))
          ≤ ENNReal.ofReal (Mass d c ρ η T N (some i) / (2 * ρ i)) * ENNReal.ofReal (2 * ρ i) :=
            mul_le_mul_of_nonneg_left hle bot_le
        _ = ENNReal.ofReal (Mass d c ρ η T N (some i)) := levelMeasure_weight_cancel d c ρ η T hi
    · rw [if_neg hhit]
      have hempty : Iv x r ∩ Iv (c i) (ρ i) = ∅ := by
        by_contra hne
        exact hhit ((hits_iff hr hρ.le).mp (Set.nonempty_iff_ne_empty.mpr hne))
      rw [Measure.restrict_apply (isClosed_Iv x r).measurableSet, hempty, measure_empty]
      simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, meetMass,
    ← ENNReal.ofReal_sum_of_nonneg
      (fun i hi => mass_nonneg d c ρ η T N i (Finset.mem_filter.mp hi).1)]



end Work.MassTransferenceAlt.Tree.Hausdorff
