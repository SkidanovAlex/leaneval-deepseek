import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data
import Submission.Work.MassTransferenceAlt.Tree.MassLe
import Submission.Work.MassTransferenceAlt.Tree.MassSum
import Submission.Work.MassTransferenceAlt.Tree.vfChildrenGe
import Submission.Work.MassTransferenceAlt.Tree.childrenMem
import Submission.Work.MassTransferenceAlt.Tree.radiusLe
import Submission.Work.MassTransferenceAlt.Tree.ballSubsetAnc
import Submission.Work.MassTransferenceAlt.Tree.ancMem
import Submission.Work.MassTransferenceAlt.Tree.massAncestor

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt
open MeasureTheory Set Metric

/-!
# The level bound for an arbitrary interval

This file proves `levelBoundReal`: the total mass of the balls of level `n` meeting a
given interval `Iv x rA` is at most `400 * (2 rA)^d / η`, provided the interval meets at
least two children of the unique ball of level `n - 1` it meets.

The argument is the "measure of an arbitrary ball" section of Beresnevich–Velani,
*A mass transference principle and the Duffin–Schaeffer conjecture for Hausdorff
measures*, Ann. of Math. 164 (2006):

* if the parent ball `B` is not larger than `Iv x rA`, the trivial bound through the mass
  of `B` suffices;
* otherwise, every hitting child `i` has `ρ i < rA` (because a second hitting child is
  disjoint from it at distance `3 ρ i`), which already gives
  `(2 ρ i)^d ≤ (2 rA)^d` for single children, and lets (P4) sum the single-child
  sub-levels geometrically; sub-levels containing at least two hits have their enlarged
  intervals disjoint inside `Iv x (5 rA)`, so each of them carries at most `10 rA` of
  `(ρ)^d`-mass, and there are at most `nsub d (ρ B) ≤ 32 (ρ B)^(d-1)` of them.
-/

/-- The children of the ball `B` of level `n - 1` whose interval meets `Iv x rA`. -/
noncomputable def childrenHits (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    (n B : ℕ) (x rA : ℝ) : Finset ℕ :=
  (T.lev n).filter (fun i => T.par n i = some B ∧ hits c ρ x rA i)

/-! ### Elementary facts -/

/-- The ordinary interval is contained in the enlarged one, for radii at most `1`. -/
private lemma iv_subset_fenl_of_le_one {d : ℝ} (hd1 : d < 1) {c ρ : ℕ → ℝ} {i : ℕ}
    (hρ : 0 < ρ i) (hρ1 : ρ i ≤ 1) : Iv (c i) (ρ i) ⊆ Fenl d c ρ i := by
  have hle : ρ i ≤ (ρ i) ^ d := by
    have h := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (le_of_lt hd1)
    rwa [Real.rpow_one] at h
  exact Iv_mono hle

/-- The interval of a child is contained in the interval of its parent. -/
private lemma child_subset_par (d : ℝ) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {i B : ℕ} (hi : i ∈ T.lev n)
    (hpar : T.par n i = some B) : Iv (c i) (ρ i) ⊆ Iv (c B) (ρ B) := by
  have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hi' : i ∈ T.lev ((n - 1) + 1) := by rw [hn']; exact hi
  obtain ⟨B', hB', hpar'⟩ := T.par_mem (n - 1) i hi'
  rw [hn'] at hpar'
  have hB'' : B' = B := by rw [hpar] at hpar'; exact (Option.some.inj hpar').symm
  have hmem : i ∈ (T.lev ((n-1)+1)).filter (fun j => T.par ((n-1)+1) j = some B') :=
    Finset.mem_filter.mpr ⟨hi', by rw [hn']; exact hpar'⟩
  have hIv : Fenl d c ρ i ⊆ Iv (c B') (ρ B') := (T.loc (n-1) B' hB').2.2.1 i hmem
  rw [hB''] at hIv
  have hgood := T.good n i hi
  have hρ1 : ρ i ≤ 1 := le_trans hgood.2.1 (Rabs_le_one hd1)
  exact (iv_subset_fenl_of_le_one hd1 hgood.1 hρ1).trans hIv

/-- The mass of every node is nonnegative. -/
private lemma Mass_nonneg (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ∀ n (x : Option ℕ), 0 ≤ Mass d c ρ η T n x := by
  intro n
  induction n with
  | zero =>
      intro x
      cases x with
      | none => simp [Mass]
      | some i =>
        by_cases hi : i ∈ T.lev 0
        · rw [show Mass d c ρ η T 0 (some i) =
              vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) from by simp [Mass, hi]]
          exact div_nonneg (vf_pos (T.good 0 i hi).1).le
            (Finset.sum_nonneg (fun j hj => (vf_pos (T.good 0 j hj).1).le))
        · rw [show Mass d c ρ η T 0 (some i) = 0 from by simp [Mass, hi]]
  | succ n ih =>
      intro x
      cases x with
      | none => simp [Mass]
      | some i =>
        by_cases hi : i ∈ T.lev (n+1)
        · rw [show Mass d c ρ η T (n+1) (some i) =
              (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter
                (fun j => T.par (n+1) j = T.par (n+1) i), vf d ρ j))
                * Mass d c ρ η T n (T.par (n+1) i) from by simp [Mass, hi]]
          refine mul_nonneg (div_nonneg (vf_pos (T.good (n+1) i hi).1).le ?_) (ih _)
          exact Finset.sum_nonneg (fun j hj => (vf_pos (T.good (n+1) j (Finset.mem_filter.mp hj).1).1).le)
        · rw [show Mass d c ρ η T (n+1) (some i) = 0 from by simp [Mass, hi]]

/-- The geometric series `∑_{t < m} 2^{-t}` is at most `2`. -/
private lemma geom_half_sum_le (m : ℕ) : ∑ t ∈ Finset.range m, ((1:ℝ)/2)^t ≤ 2 := by
  have key : ∀ m : ℕ, ∑ t ∈ Finset.range m, ((1:ℝ)/2)^t ≤ 2 - 2 * ((1:ℝ)/2)^m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have h : 2 * ((1:ℝ)/2)^(m+1) = ((1:ℝ)/2)^m := by rw [pow_succ]; ring
        linarith
  have h2 : (0:ℝ) ≤ 2 * ((1:ℝ)/2)^m := by positivity
  linarith [key m]

/-! ### The two geometric facts about hitting children -/

/-- **Fact A.**  If two distinct children of `B` meet `Iv x rA`, then each of them has
radius strictly less than `rA`: a point of `Iv x rA` in the second child lies outside the
threefold dilation of the first, while it is at distance at most `2 rA + ρ i` from its
centre. -/
private lemma hit_radius_lt (d : ℝ) (_hd0 : 0 < d) (_hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ)
    (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {B : ℕ} (hB : B ∈ T.lev (n-1))
    {x rA : ℝ} (hrA : 0 ≤ rA) {i j : ℕ}
    (hi : i ∈ childrenHits d c ρ η T n B x rA) (hj : j ∈ childrenHits d c ρ η T n B x rA)
    (hij : i ≠ j) : ρ i < rA := by
  obtain ⟨hilev, hipar, hihit⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjlev, hjpar, hjhit⟩ := Finset.mem_filter.mp hj
  have hρi : 0 < ρ i := (T.good n i hilev).1
  have hρj : 0 < ρ j := (T.good n j hjlev).1
  -- a point of `Iv x rA` inside the `j`-th child
  obtain ⟨z, hzx, hzj⟩ := (Work.MassTransferenceAlt.hits_iff hrA hρj.le).mpr hjhit
  have hzx' : |z - x| ≤ rA := by rw [mem_Iv] at hzx; exact hzx
  -- it lies outside the threefold dilation of the `i`-th child
  have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hiF : i ∈ (T.lev n).filter (fun i => T.par n i = some B) :=
    Finset.mem_filter.mpr ⟨hilev, hipar⟩
  have hjF : j ∈ (T.lev n).filter (fun j => T.par n j = some B) :=
    Finset.mem_filter.mpr ⟨hjlev, hjpar⟩
  have hloc := T.loc (n - 1) B hB
  rw [hn'] at hloc
  have hdisj3 : Disjoint (Iv (c i) (3 * ρ i)) (Iv (c j) (3 * ρ j)) :=
    hloc.2.2.2.2.1 i hiF j hjF hij
  have hzj3 : z ∈ Iv (c j) (3 * ρ j) := by
    rw [mem_Iv] at hzj ⊢
    linarith
  have hzi3 : z ∉ Iv (c i) (3 * ρ i) := fun h => (Set.disjoint_left.mp hdisj3 h) hzj3
  rw [mem_Iv] at hzi3
  have hgt : 3 * ρ i < |z - c i| := not_le.mp hzi3
  have hxc : |x - c i| ≤ rA + ρ i := by
    have h := hihit; rw [hits] at h; exact h
  have hle : |z - c i| ≤ 2 * rA + ρ i := by
    calc |z - c i| = |(z - x) + (x - c i)| := by ring_nf
      _ ≤ |z - x| + |x - c i| := abs_add_le _ _
      _ ≤ rA + (rA + ρ i) := by linarith
      _ = 2 * rA + ρ i := by ring
  linarith

/-- **Fact B.**  If two distinct children of `B` lie in the same sub-level and both meet
`Iv x rA`, then the enlarged interval of each of them is contained in `Iv x (5 rA)`. -/
private lemma fenl_subset_five_of_same_sub (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1)
    (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {B : ℕ}
    (hB : B ∈ T.lev (n-1)) {x rA : ℝ} (hrA : 0 ≤ rA) {i j : ℕ}
    (hi : i ∈ childrenHits d c ρ η T n B x rA) (hj : j ∈ childrenHits d c ρ η T n B x rA)
    (hij : i ≠ j) (hsub : T.sub n i = T.sub n j) : Fenl d c ρ i ⊆ Iv x (5 * rA) := by
  obtain ⟨hilev, hipar, hihit⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjlev, hjpar, hjhit⟩ := Finset.mem_filter.mp hj
  have hρi : 0 < ρ i := (T.good n i hilev).1
  have hρj : 0 < ρ j := (T.good n j hjlev).1
  have hρj1 : ρ j ≤ 1 := le_trans (T.good n j hjlev).2.1 (Rabs_le_one hd1)
  obtain ⟨z, hzx, hzj⟩ := (Work.MassTransferenceAlt.hits_iff hrA hρj.le).mpr hjhit
  have hzx' : |z - x| ≤ rA := by rw [mem_Iv] at hzx; exact hzx
  have hzjFenl : z ∈ Fenl d c ρ j := (iv_subset_fenl_of_le_one hd1 hρj hρj1) hzj
  -- enlarged intervals of children in the same sub-level are disjoint
  have hn' : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hiF : i ∈ (T.lev n).filter (fun i => T.par n i = some B) :=
    Finset.mem_filter.mpr ⟨hilev, hipar⟩
  have hjF : j ∈ (T.lev n).filter (fun j => T.par n j = some B) :=
    Finset.mem_filter.mpr ⟨hjlev, hjpar⟩
  have hloc := T.loc (n - 1) B hB
  rw [hn'] at hloc
  have hdisjF : Disjoint (Fenl d c ρ i) (Fenl d c ρ j) :=
    hloc.2.2.2.1 i hiF j hjF hij hsub
  have hzFenl : z ∉ Fenl d c ρ i := fun h => (Set.disjoint_left.mp hdisjF h) hzjFenl
  rw [Fenl, mem_Iv] at hzFenl
  have hpid : (ρ i) ^ d < |z - c i| := not_le.mp hzFenl
  have hρi_lt : ρ i < rA := hit_radius_lt d hd0 hd1 c ρ η T hn hB hrA hi hj hij
  have hxc : |x - c i| ≤ rA + ρ i := by
    have h := hihit; rw [hits] at h; exact h
  have hle : |z - c i| ≤ 2 * rA + ρ i := by
    calc |z - c i| = |(z - x) + (x - c i)| := by ring_nf
      _ ≤ |z - x| + |x - c i| := abs_add_le _ _
      _ ≤ rA + (rA + ρ i) := by linarith
      _ = 2 * rA + ρ i := by ring
  have hpid3 : (ρ i) ^ d < 3 * rA := by linarith
  intro w hw
  rw [Fenl, mem_Iv] at hw
  rw [mem_Iv]
  calc |w - x| = |(w - c i) + (c i - x)| := by ring_nf
    _ ≤ |w - c i| + |c i - x| := abs_add_le _ _
    _ ≤ (ρ i) ^ d + (rA + ρ i) := by
        have hxci : |c i - x| ≤ rA + ρ i := by rw [abs_sub_comm]; exact hxc
        linarith
    _ ≤ 5 * rA := by linarith

/-- The total `d`-mass of a family of disjoint enlarged intervals inside `Iv x (5 rA)` is
at most the length `10 rA` of that interval. -/
private lemma sum_two_rpow_le_of_disjoint {d : ℝ} {c ρ : ℕ → ℝ} {H : Finset ℕ} {x rA : ℝ}
    (hrA : 0 ≤ rA) (hpos : ∀ i ∈ H, 0 ≤ ρ i)
    (hdisj : ∀ i ∈ H, ∀ j ∈ H, i ≠ j → Disjoint (Fenl d c ρ i) (Fenl d c ρ j))
    (hface : ∀ i ∈ H, Fenl d c ρ i ⊆ Iv x (5 * rA)) :
    ∑ i ∈ H, 2 * (ρ i) ^ d ≤ 10 * rA := by
  have hmeas : ∀ i ∈ H, MeasurableSet (Fenl d c ρ i) := fun i _ => measurableSet_Icc
  have h1 : ∑ i ∈ H, ENNReal.ofReal (2 * (ρ i) ^ d) ≤ ENNReal.ofReal (10 * rA) := by
    calc ∑ i ∈ H, ENNReal.ofReal (2 * (ρ i) ^ d)
        = ∑ i ∈ H, volume (Fenl d c ρ i) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Fenl, volume_Iv _ _ (Real.rpow_nonneg (hpos i hi) d)]
      _ = volume (⋃ i ∈ (H : Set ℕ), Fenl d c ρ i) :=
          (MeasureTheory.measure_biUnion_finset (fun i hi j hj hij => hdisj i hi j hj hij)
            hmeas).symm
      _ ≤ volume (Iv x (5 * rA)) := measure_mono (Set.iUnion₂_subset (fun i hi => hface i hi))
      _ = ENNReal.ofReal (10 * rA) := by
          rw [volume_Iv _ _ (by linarith)]
          congr 1
          ring
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => by
    have := Real.rpow_nonneg (hpos i hi) d; linarith)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h1


/-- `(2 x)^d ≤ 2 x^d` for `x ≥ 0` and `d ≤ 1`. -/
private lemma two_mul_rpow_le {x d : ℝ} (hx : 0 ≤ x) (hd : d ≤ 1) :
    (2 * x) ^ d ≤ 2 * x ^ d := by
  rw [Real.mul_rpow (by norm_num) hx]
  have h2 : (2:ℝ)^d ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hd
    simpa using h
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx d)

/-- The sub-level index of an element of `F` is one of the sub-levels of the local level
of `B`. -/
private lemma sub_lt_of_mem (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    {n : ℕ} (hn : 1 ≤ n) {B : ℕ} (hB : B ∈ T.lev (n-1)) {x rA : ℝ} {F : Finset ℕ}
    (hF : ∀ i, i ∈ F ↔ i ∈ T.lev n ∧ T.par n i = some B ∧ hits c ρ x rA i) {i : ℕ}
    (hi : i ∈ F) : T.sub n i < nsub d (ρ B) := by
  obtain ⟨h1, h2, _⟩ := (hF i).mp hi
  have hn' : (n-1)+1 = n := Nat.sub_add_cancel hn
  have hloc := T.loc (n-1) B hB
  rw [hn'] at hloc
  exact hloc.2.2.2.2.2.1 i (Finset.mem_filter.mpr ⟨h1, h2⟩)

/-- **A sub-level with at least two hits carries at most `10 rA` of mass.**  Its enlarged
intervals are disjoint (property (P2)) and all contained in `Iv x (5 rA)` (Fact B). -/
private lemma sub_level_le_of_two (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (η : ℝ) (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {B : ℕ} (hB : B ∈ T.lev (n-1))
    {x rA : ℝ} (hrA : 0 ≤ rA) {k : ℕ}
    (hcard : 2 ≤ ((childrenHits d c ρ η T n B x rA).filter (fun i => T.sub n i = k)).card) :
    ∑ i ∈ (childrenHits d c ρ η T n B x rA).filter (fun i => T.sub n i = k),
        2 * (ρ i) ^ d ≤ 10 * rA := by
  set H : Finset ℕ := (childrenHits d c ρ η T n B x rA).filter (fun i => T.sub n i = k)
    with hHdef
  have hmem : ∀ i, i ∈ H ↔ i ∈ childrenHits d c ρ η T n B x rA ∧ T.sub n i = k := by
    intro i; rw [hHdef, Finset.mem_filter]
  have hcardH : 2 ≤ H.card := hcard
  refine sum_two_rpow_le_of_disjoint (c := c) (x := x) hrA ?_ ?_ ?_
  · intro i hi
    have hlev : i ∈ T.lev n := (Finset.mem_filter.mp ((hmem i).mp hi).1).1
    exact le_of_lt (T.good n i hlev).1
  · intro i hi j hj hij
    obtain ⟨hic, hik⟩ := (hmem i).mp hi
    obtain ⟨hjc, hjk⟩ := (hmem j).mp hj
    obtain ⟨hilev, hipar, _⟩ := Finset.mem_filter.mp hic
    obtain ⟨hjlev, hjpar, _⟩ := Finset.mem_filter.mp hjc
    have hsub : T.sub n i = T.sub n j := by rw [hik, hjk]
    have hn' : (n-1)+1 = n := Nat.sub_add_cancel hn
    have hiF : i ∈ (T.lev n).filter (fun i => T.par n i = some B) :=
      Finset.mem_filter.mpr ⟨hilev, hipar⟩
    have hjF : j ∈ (T.lev n).filter (fun j => T.par n j = some B) :=
      Finset.mem_filter.mpr ⟨hjlev, hjpar⟩
    have hloc := T.loc (n-1) B hB
    rw [hn'] at hloc
    exact hloc.2.2.2.1 i hiF j hjF hij hsub
  · intro i hi
    obtain ⟨hic, hik⟩ := (hmem i).mp hi
    have h1 : 1 < H.card := by omega
    obtain ⟨j, hjH, hji⟩ := Finset.exists_mem_ne h1 i
    obtain ⟨hjc, hjk⟩ := (hmem j).mp hjH
    exact fenl_subset_five_of_same_sub d hd0 hd1 c ρ η T hn hB hrA hic hjc hji.symm
      (by rw [hik, hjk])

/-- **The single-child sub-levels contribute at most `2 (2 rA)^d`.**  All their radii are
below `rA`, so the first of them contributes at most `(2 rA)^d`, and (P4) makes the rest a
geometric series. -/
private lemma sum_single_le_two (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (η : ℝ) (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {B : ℕ} (hB : B ∈ T.lev (n-1))
    {x rA : ℝ} (hrA : 0 ≤ rA) {F G : Finset ℕ}
    (hF : ∀ i, i ∈ F ↔ i ∈ T.lev n ∧ T.par n i = some B ∧ hits c ρ x rA i)
    (hcard : 2 ≤ F.card) (hGF : G ⊆ F)
    (hG : ∀ i ∈ G, (F.filter (fun j => T.sub n j = T.sub n i)).card = 1) :
    ∑ i ∈ G, (2 * ρ i) ^ d ≤ 2 * (2 * rA) ^ d := by
  classical
  rcases Finset.eq_empty_or_nonempty G with hGe | hGne
  · rw [hGe, Finset.sum_empty]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) d)
  · obtain ⟨i₁, hi₁G, hmin⟩ := Finset.exists_min_image G (fun i => T.sub n i) hGne
    have hi₁F : i₁ ∈ F := hGF hi₁G
    have hρi₁ : 0 < ρ i₁ := by
      obtain ⟨h1, _, _⟩ := (hF i₁).mp hi₁F
      exact (T.good n i₁ h1).1
    -- every element of `G` has radius below `rA`
    have hρlt : ∀ i ∈ G, ρ i < rA := by
      intro i hi
      have hiF : i ∈ F := hGF hi
      obtain ⟨j, hjF, hji⟩ := Finset.exists_mem_ne (by omega : 1 < F.card) i
      have hi_ch : i ∈ childrenHits d c ρ η T n B x rA := by
        obtain ⟨h1, h2, h3⟩ := (hF i).mp hiF
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
      have hj_ch : j ∈ childrenHits d c ρ η T n B x rA := by
        obtain ⟨h1, h2, h3⟩ := (hF j).mp hjF
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
      exact hit_radius_lt d hd0 hd1 c ρ η T hn hB hrA hi_ch hj_ch hji.symm
    -- the sub-level index is injective on `G`
    have hinj : ∀ i ∈ G, ∀ j ∈ G, T.sub n i = T.sub n j → i = j := by
      intro i hi j hj heq
      have hiF : i ∈ F := hGF hi
      have hjF : j ∈ F := hGF hj
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hG i hi)
      have hja : j ∈ ({a} : Finset ℕ) := by
        rw [← ha]; exact Finset.mem_filter.mpr ⟨hjF, heq.symm⟩
      have hia : i ∈ ({a} : Finset ℕ) := by
        rw [← ha]; exact Finset.mem_filter.mpr ⟨hiF, rfl⟩
      simp only [Finset.mem_singleton] at hja hia
      rw [hja, hia]
    -- the pointwise bound
    have hstep : ∀ j ∈ G,
        (2 * ρ j) ^ d ≤ ((1:ℝ)/2) ^ (T.sub n j - T.sub n i₁) * (2 * ρ i₁) ^ d := by
      intro j hj
      by_cases hji : j = i₁
      · subst hji
        rw [Nat.sub_self, pow_zero, one_mul]
      · obtain ⟨h1, h2, _⟩ := (hF i₁).mp hi₁F
        obtain ⟨k1, k2, _⟩ := (hF j).mp (hGF hj)
        have hiFc : i₁ ∈ (T.lev n).filter (fun i => T.par n i = some B) :=
          Finset.mem_filter.mpr ⟨h1, h2⟩
        have hjFc : j ∈ (T.lev n).filter (fun j => T.par n j = some B) :=
          Finset.mem_filter.mpr ⟨k1, k2⟩
        have hsublt : T.sub n i₁ < T.sub n j := by
          exact lt_of_le_of_ne (hmin j hj) (fun h => hji (hinj i₁ hi₁G j hj h).symm)
        have hn' : (n-1)+1 = n := Nat.sub_add_cancel hn
        have hloc := T.loc (n-1) B hB
        rw [hn'] at hloc
        have hdecay := hloc.2.2.2.2.2.2.2.2 i₁ hiFc j hjFc hsublt
        have hρj0 : (0:ℝ) < ρ j := (T.good n j k1).1
        have hA : (2 * ρ j) ^ d = (2:ℝ)^d * (ρ j)^d := Real.mul_rpow (by norm_num) hρj0.le
        have hB : (2 * ρ i₁) ^ d = (2:ℝ)^d * (ρ i₁)^d := Real.mul_rpow (by norm_num) hρi₁.le
        rw [hA, hB]
        calc (2:ℝ)^d * (ρ j)^d
            ≤ (2:ℝ)^d * (((1:ℝ)/2) ^ (T.sub n j - T.sub n i₁) * (ρ i₁)^d) :=
              mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg (by norm_num) d)
          _ = ((1:ℝ)/2) ^ (T.sub n j - T.sub n i₁) * ((2:ℝ)^d * (ρ i₁)^d) := by ring
    -- the geometric bound for the sub-level differences
    have hgeom : ∑ i ∈ G, ((1:ℝ)/2) ^ (T.sub n i - T.sub n i₁) ≤ 2 := by
      have hinj2 : Set.InjOn (fun i => T.sub n i - T.sub n i₁) (↑G : Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        beta_reduce at hab
        have : T.sub n a = T.sub n b := by
          have ha' : T.sub n i₁ ≤ T.sub n a := hmin a ha
          have hb' : T.sub n i₁ ≤ T.sub n b := hmin b hb
          rw [show T.sub n a = (T.sub n a - T.sub n i₁) + T.sub n i₁ from
              (Nat.sub_add_cancel ha').symm,
            show T.sub n b = (T.sub n b - T.sub n i₁) + T.sub n i₁ from
              (Nat.sub_add_cancel hb').symm, hab]
        exact hinj a ha b hb this
      rw [← Finset.sum_image (f := fun t : ℕ => ((1:ℝ)/2)^t)
        (g := fun i => T.sub n i - T.sub n i₁) hinj2]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (geom_half_sum_le (nsub d (ρ B)))
      · intro t ht
        obtain ⟨i, hiG, rfl⟩ := Finset.mem_image.mp ht
        have hlt : T.sub n i < nsub d (ρ B) := sub_lt_of_mem d c ρ η T hn hB hF (hGF hiG)
        exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) hlt)
      · intro t ht _
        positivity
    calc ∑ i ∈ G, (2 * ρ i) ^ d
        ≤ ∑ i ∈ G, ((1:ℝ)/2) ^ (T.sub n i - T.sub n i₁) * (2 * ρ i₁) ^ d :=
          Finset.sum_le_sum hstep
      _ = (∑ i ∈ G, ((1:ℝ)/2) ^ (T.sub n i - T.sub n i₁)) * (2 * ρ i₁) ^ d := by
          rw [Finset.sum_mul]
      _ ≤ 2 * (2 * ρ i₁) ^ d :=
          mul_le_mul_of_nonneg_right hgeom (Real.rpow_nonneg (by linarith) d)
      _ ≤ 2 * (2 * rA) ^ d := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Real.rpow_le_rpow (by linarith) (by linarith [hρlt i₁ hi₁G]) hd0.le

/-- **The sub-levels with at least two hits contribute at most `nsub d (ρ B) * 10 rA`.**
There are at most `nsub d (ρ B)` sub-levels, and each of them carries at most `10 rA`. -/
private lemma sum_multi_le (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (η : ℝ) (T : TreeData d c ρ η) {n : ℕ} (hn : 1 ≤ n) {B : ℕ} (hB : B ∈ T.lev (n-1))
    {x rA : ℝ} (hrA : 0 ≤ rA) {F G : Finset ℕ}
    (hF : ∀ i, i ∈ F ↔ i ∈ T.lev n ∧ T.par n i = some B ∧ hits c ρ x rA i)
    (hGF : G ⊆ F) (hG : ∀ i ∈ G, 2 ≤ (F.filter (fun j => T.sub n j = T.sub n i)).card) :
    ∑ i ∈ G, 2 * (ρ i) ^ d ≤ (nsub d (ρ B) : ℝ) * (10 * rA) := by
  classical
  have hdecomp : ∑ i ∈ G, 2 * (ρ i) ^ d
      = ∑ k ∈ Finset.range (nsub d (ρ B)),
          ∑ i ∈ G.filter (fun i => T.sub n i = k), 2 * (ρ i) ^ d :=
    (Finset.sum_fiberwise_of_maps_to (s := G) (t := Finset.range (nsub d (ρ B)))
      (g := fun i => T.sub n i)
      (fun i hi => Finset.mem_range.mpr (sub_lt_of_mem d c ρ η T hn hB hF (hGF hi)))
      (fun i => 2 * (ρ i) ^ d)).symm
  rw [hdecomp]
  calc ∑ k ∈ Finset.range (nsub d (ρ B)),
        ∑ i ∈ G.filter (fun i => T.sub n i = k), 2 * (ρ i) ^ d
      ≤ ∑ k ∈ Finset.range (nsub d (ρ B)), 10 * rA := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        by_cases hemp : (G.filter (fun i => T.sub n i = k)).Nonempty
        · obtain ⟨i, hiGk⟩ := hemp
          have hiG : i ∈ G := (Finset.mem_filter.mp hiGk).1
          have hik : T.sub n i = k := (Finset.mem_filter.mp hiGk).2
          have hFk : F.filter (fun j => T.sub n j = k)
              = (childrenHits d c ρ η T n B x rA).filter (fun j => T.sub n j = k) := by
            ext a
            rw [Finset.mem_filter, Finset.mem_filter]
            constructor
            · rintro ⟨ha, hk⟩
              obtain ⟨h1, h2, h3⟩ := (hF a).mp ha
              exact ⟨Finset.mem_filter.mpr ⟨h1, h2, h3⟩, hk⟩
            · rintro ⟨ha, hk⟩
              exact ⟨(hF a).mpr ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2.1,
                (Finset.mem_filter.mp ha).2.2⟩, hk⟩
          have hcard : 2 ≤ ((childrenHits d c ρ η T n B x rA).filter
              (fun i => T.sub n i = k)).card := by
            have h2 := hG i hiG
            rw [hik] at h2
            rwa [← hFk]
          have hsub : (G.filter (fun i => T.sub n i = k)) ⊆
              (childrenHits d c ρ η T n B x rA).filter (fun i => T.sub n i = k) := by
            intro a ha
            obtain ⟨haG, hak⟩ := Finset.mem_filter.mp ha
            obtain ⟨h1, h2, h3⟩ := (hF a).mp (hGF haG)
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h1, h2, h3⟩, hak⟩
          calc ∑ i ∈ G.filter (fun i => T.sub n i = k), 2 * (ρ i) ^ d
              ≤ ∑ i ∈ (childrenHits d c ρ η T n B x rA).filter (fun i => T.sub n i = k),
                  2 * (ρ i) ^ d := by
                refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a ha _ => ?_)
                have hlev : a ∈ T.lev n := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
                have hpos : 0 < ρ a := (T.good n a hlev).1
                positivity
            _ ≤ 10 * rA := sub_level_le_of_two d hd0 hd1 c ρ η T hn hB hrA hcard
        · rw [Finset.not_nonempty_iff_eq_empty] at hemp
          rw [hemp, Finset.sum_empty]
          linarith
    _ = (nsub d (ρ B) : ℝ) * (10 * rA) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma levelBoundReal (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (hη : 0 < η) (T : Work.MassTransferenceAlt.TreeData d c ρ η) (n : ℕ) (hn : 1 ≤ n) (B : ℕ) (hB : B ∈ T.lev (n-1)) {x rA : ℝ} (hrA : 0 ≤ rA) (hrA1 : 2 * rA ≤ 1) (hmeet : 2 ≤ ((T.lev n).filter (fun i => T.par n i = some B ∧ Work.MassTransferenceAlt.hits c ρ x rA i)).card) (huniq : ∀ B' ∈ T.lev (n-1), (Work.MassTransferenceAlt.Iv x rA ∩ Work.MassTransferenceAlt.Iv (c B') (ρ B')).Nonempty → B' = B) : ∑ i ∈ (T.lev n).filter (fun i => Work.MassTransferenceAlt.hits c ρ x rA i), Work.MassTransferenceAlt.Mass d c ρ η T n (some i) ≤ 400 * (2 * rA) ^ d / η := by
  classical
  set F : Finset ℕ := (T.lev n).filter (fun i => T.par n i = some B ∧ hits c ρ x rA i) with hFdef
  have hFmem : ∀ i, i ∈ F ↔ i ∈ T.lev n ∧ T.par n i = some B ∧ hits c ρ x rA i := by
    intro i; rw [hFdef, Finset.mem_filter]
  have hmeetF : 2 ≤ F.card := hmeet
  -- the balls of level `n` meeting `Iv x rA` are exactly the children of `B` meeting it
  have hHF : (T.lev n).filter (fun i => hits c ρ x rA i) = F := by
    rw [hFdef]
    ext i
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hilev, hhit⟩
      refine ⟨hilev, ?_, hhit⟩
      obtain ⟨B', hB', hpar⟩ := T.par_mem (n-1) i (by rw [Nat.sub_add_cancel hn]; exact hilev)
      have hpar' : T.par n i = some B' := by rw [← Nat.sub_add_cancel hn]; exact hpar
      have hsub := child_subset_par d hd1 c ρ η T hn hilev hpar'
      have hρi : 0 < ρ i := (T.good n i hilev).1
      have hA := (Work.MassTransferenceAlt.hits_iff hrA hρi.le).mpr hhit
      have hA' : (Iv x rA ∩ Iv (c B') (ρ B')).Nonempty :=
        hA.mono (Set.inter_subset_inter_right _ hsub)
      have hBeq := huniq B' hB' hA'
      rw [hBeq] at hpar'
      exact hpar'
    · rintro ⟨hilev, _, hhit⟩
      exact ⟨hilev, hhit⟩
  rw [hHF]
  have hposF : ∀ i ∈ F, 0 ≤ ρ i := fun i hi => le_of_lt ((T.good n i ((hFmem i).mp hi).1).1)
  -- the mass of a hitting child is at most its `f`-volume divided by `η`
  have hmass : ∑ i ∈ F, Mass d c ρ η T n (some i) ≤ (∑ i ∈ F, (2 * ρ i) ^ d) / η := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have h := MassLe d hd0 hd1 c ρ η hη T n i ((hFmem i).mp hi).1
    simpa only [vf] using h
  by_cases hcase : ρ B ≤ rA
  · -- case 1: the parent ball is no larger than `Iv x rA`
    have hchildren := childrenMass d c ρ η T (n-1) B hB
    rw [Nat.sub_add_cancel hn] at hchildren
    have hsub : F ⊆ (T.lev n).filter (fun i => T.par n i = some B) := by
      intro i hi
      obtain ⟨h1, h2, _⟩ := (hFmem i).mp hi
      exact Finset.mem_filter.mpr ⟨h1, h2⟩
    calc ∑ i ∈ F, Mass d c ρ η T n (some i)
        ≤ ∑ i ∈ (T.lev n).filter (fun i => T.par n i = some B), Mass d c ρ η T n (some i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i hi _ => Mass_nonneg d c ρ η T n (some i))
      _ = Mass d c ρ η T (n-1) (some B) := hchildren
      _ ≤ vf d ρ B / η := MassLe d hd0 hd1 c ρ η hη T (n-1) B hB
      _ ≤ (2 * rA) ^ d / η := by
          rw [div_le_div_iff_of_pos_right hη, vf]
          have hρB0 : 0 < ρ B := (T.good (n-1) B hB).1
          exact Real.rpow_le_rpow (by linarith) (by linarith) hd0.le
      _ ≤ 400 * (2 * rA) ^ d / η := by
          rw [div_le_div_iff_of_pos_right hη]
          nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * rA) d]
  · -- case 2: the parent ball is larger than `Iv x rA`
    have hcase' : rA < ρ B := not_le.mp hcase
    have hρB0 : 0 < ρ B := (T.good (n-1) B hB).1
    -- two distinct children of `B` hit `Iv x rA`, so `rA > 0`
    obtain ⟨i₀, hi₀F, i₁, hi₁F, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    have hrApos : 0 < rA := by
      have hi₀ : i₀ ∈ childrenHits d c ρ η T n B x rA := by
        obtain ⟨h1, h2, h3⟩ := (hFmem i₀).mp hi₀F
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
      have hi₁ : i₁ ∈ childrenHits d c ρ η T n B x rA := by
        obtain ⟨h1, h2, h3⟩ := (hFmem i₁).mp hi₁F
        exact Finset.mem_filter.mpr ⟨h1, h2, h3⟩
      have hlt := hit_radius_lt d hd0 hd1 c ρ η T hn hB hrA hi₀ hi₁ hne
      have hpos : 0 < ρ i₀ := (T.good n i₀ ((hFmem i₀).mp hi₀F).1).1
      linarith
    -- the `f`-volume bound
    have hvfsum : ∑ i ∈ F, (2 * ρ i) ^ d ≤ 322 * (2 * rA) ^ d := by
      have h1 : ∑ i ∈ F.filter (fun i => (F.filter (fun j => T.sub n j = T.sub n i)).card = 1),
            (2 * ρ i) ^ d ≤ 2 * (2 * rA) ^ d :=
        sum_single_le_two d hd0 hd1 c ρ η T hn hB hrA hFmem hmeetF
          (fun i hi => (Finset.mem_filter.mp hi).1) (fun i hi => (Finset.mem_filter.mp hi).2)
      have h2 : ∑ i ∈ F.filter
            (fun i => ¬ (F.filter (fun j => T.sub n j = T.sub n i)).card = 1),
            (2 * ρ i) ^ d ≤ (nsub d (ρ B) : ℝ) * (10 * rA) := by
        set G : Finset ℕ := F.filter
          (fun i => ¬ (F.filter (fun j => T.sub n j = T.sub n i)).card = 1) with hGdef
        have hGsub : G ⊆ F := fun i hi => (Finset.mem_filter.mp hi).1
        have hGcard : ∀ i ∈ G, 2 ≤ (F.filter (fun j => T.sub n j = T.sub n i)).card := by
          intro i hi
          have hne := (Finset.mem_filter.mp hi).2
          have hiF : i ∈ F := (Finset.mem_filter.mp hi).1
          have hcard1 : 1 ≤ (F.filter (fun j => T.sub n j = T.sub n i)).card := by
            have hpos : 0 < (F.filter (fun j => T.sub n j = T.sub n i)).card :=
              Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiF, rfl⟩⟩
            omega
          omega
        refine le_trans (Finset.sum_le_sum (s := G) (fun i hi => ?_))
          (sum_multi_le d hd0 hd1 c ρ η T hn hB hrA hFmem hGsub hGcard)
        exact two_mul_rpow_le (hposF i (hGsub hi)) (le_of_lt hd1)
      have h3 : (nsub d (ρ B) : ℝ) * (10 * rA) ≤ 320 * (2 * rA) ^ d := by
        have hLle : (nsub d (ρ B) : ℝ) ≤ 32 * (ρ B) ^ (d-1) :=
          nsub_le hρB0 hd1 (T.good (n-1) B hB).2.1
        have hpow : (ρ B) ^ (d-1) ≤ rA ^ (d-1) :=
          Real.rpow_le_rpow_of_nonpos hrApos hcase'.le (by linarith)
        have hpow2 : rA ^ (d-1) * rA = rA ^ d := by
          calc rA ^ (d-1) * rA = rA ^ (d-1) * rA ^ (1:ℝ) := by rw [Real.rpow_one]
            _ = rA ^ ((d-1) + 1) := (Real.rpow_add hrApos (d-1) 1).symm
            _ = rA ^ d := by rw [show (d-1) + 1 = d by ring]
        calc (nsub d (ρ B) : ℝ) * (10 * rA)
            ≤ (32 * (ρ B) ^ (d-1)) * (10 * rA) :=
              mul_le_mul_of_nonneg_right hLle (by linarith)
          _ = 32 * (10 * rA) * (ρ B) ^ (d-1) := by ring
          _ ≤ 32 * (10 * rA) * rA ^ (d-1) :=
              mul_le_mul_of_nonneg_left hpow (by linarith)
          _ = 320 * rA ^ d := by rw [← hpow2]; ring
          _ ≤ 320 * (2 * rA) ^ d := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact Real.rpow_le_rpow hrA (by linarith) hd0.le
      have hsplit := Finset.sum_filter_add_sum_filter_not F
        (fun i => (F.filter (fun j => T.sub n j = T.sub n i)).card = 1) (fun i => (2 * ρ i) ^ d)
      calc ∑ i ∈ F, (2 * ρ i) ^ d
          = (∑ i ∈ F.filter (fun i => (F.filter (fun j => T.sub n j = T.sub n i)).card = 1),
                (2 * ρ i) ^ d)
            + (∑ i ∈ F.filter
                (fun i => ¬ (F.filter (fun j => T.sub n j = T.sub n i)).card = 1),
                (2 * ρ i) ^ d) := hsplit.symm
        _ ≤ 2 * (2 * rA) ^ d + 320 * (2 * rA) ^ d := add_le_add h1 (le_trans h2 h3)
        _ = 322 * (2 * rA) ^ d := by ring
    calc ∑ i ∈ F, Mass d c ρ η T n (some i)
        ≤ (∑ i ∈ F, (2 * ρ i) ^ d) / η := hmass
      _ ≤ (322 * (2 * rA) ^ d) / η := by
          rw [div_le_div_iff_of_pos_right hη]
          exact hvfsum
      _ ≤ 400 * (2 * rA) ^ d / η := by
          rw [div_le_div_iff_of_pos_right hη]
          nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * rA) d]

end Work.MassTransferenceAlt.Tree
