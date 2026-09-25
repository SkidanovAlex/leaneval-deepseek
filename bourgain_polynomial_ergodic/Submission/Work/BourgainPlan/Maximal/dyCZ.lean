import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The dyadic Calderón--Zygmund decomposition of a nonnegative function

For `ψ : ℝ → ℝ≥0∞` and a level `c`, `czCells ψ c` is the set of dyadic cells (encoded as
`(level, index)`) whose `ψ`-average exceeds `c`, and `czMax ψ c` is the set of *maximal* such
cells. These are the cells of the dyadic Calderón--Zygmund decomposition of `ψ` at height `c`.

The main content is that every cell of `czCells` is contained in a maximal one, that the maximal
cells are pairwise disjoint, and that their averages are at most `2c`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The average of `ψ` over the dyadic cell of level `n` containing `x`. -/
noncomputable def dyAvg (ψ : ℝ → ℝ≥0∞) (n : ℤ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ * ∫⁻ y in dyCell n (dyIdx n x), ψ y

lemma dyAvg_le_dyMax (ψ : ℝ → ℝ≥0∞) (n : ℤ) (x : ℝ) : dyAvg ψ n x ≤ dyMax ψ x := by
  unfold dyAvg dyMax
  exact le_iSup_of_le n (le_iSup_of_le (dyIdx n x) (le_iSup_of_le (dyIdx_mem n x) le_rfl))

/-- The dyadic cells whose `ψ`-average exceeds the level `c`. -/
def czCells (ψ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Set (ℤ × ℤ) :=
  {p | c < ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y}

/-- The maximal cells of `czCells ψ c` (maximal with respect to inclusion). -/
def czMax (ψ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Set (ℤ × ℤ) :=
  {p | p ∈ czCells ψ c ∧ ∀ q ∈ czCells ψ c, dyCell p.1 p.2 ⊆ dyCell q.1 q.2 → q.1 ≤ p.1}

@[simp] lemma czCells_level_iff (ψ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (n : ℤ) (x : ℝ) :
    (n, dyIdx n x) ∈ czCells ψ c ↔ c < dyAvg ψ n x := by
  simp [czCells, dyAvg]

lemma czMax_mem_czCells {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ} (hp : p ∈ czMax ψ c) :
    p ∈ czCells ψ c := hp.1

/-- Two cells of the same level that meet are equal (as indices). -/
lemma dyCell_index_eq {n k k' : ℤ} (h : (dyCell n k ∩ dyCell n k').Nonempty) : k = k' := by
  obtain ⟨x, hx1, hx2⟩ := h
  simp only [dyCell, Set.mem_Ico] at hx1 hx2
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exfalso
    have hstep : ((k : ℝ) + 1) ≤ (k' : ℝ) := by
      have : k + 1 ≤ k' := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := zpow_two_pos n
    nlinarith [hx1.2, hx2.1]
  · exact heq
  · exfalso
    have hstep : ((k' : ℝ) + 1) ≤ (k : ℝ) := by
      have : k' + 1 ≤ k := by omega
      exact_mod_cast this
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := zpow_two_pos n
    nlinarith [hx2.2, hx1.1]

/-- Membership in a cell determines the index. -/
lemma dyIdx_eq_of_mem_cell {n k : ℤ} {y : ℝ} (h : y ∈ dyCell n k) : dyIdx n y = k :=
  dyCell_index_eq ⟨y, dyIdx_mem n y, h⟩

/-- Two cells of the same level that meet are equal. -/
lemma dyCell_eq_of_meet {n k k' : ℤ} {x : ℝ} (h : x ∈ dyCell n k) (h' : x ∈ dyCell n k') :
    dyCell n k = dyCell n k' := by
  have h1 := dyIdx_eq_of_mem_cell h
  have h2 := dyIdx_eq_of_mem_cell h'
  rw [← h1, ← h2]

/-- `2^(n+1) = 2^n · 2`. -/
lemma zpow_succ_two (n : ℤ) : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring

/-- `ofReal (2^n)⁻¹` is the inverse of `ofReal (2^n)`. -/
lemma ofReal_zpow_inv (n : ℤ) :
    ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ = (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ :=
  ENNReal.ofReal_inv_of_pos (zpow_two_pos n)

/-- The level-`n+1` index of `x` is the level-`n` index divided by `2`. -/
lemma dyIdx_succ (n : ℤ) (x : ℝ) : dyIdx (n + 1) x = dyIdx n x / 2 := by
  unfold dyIdx
  have h : x / (2 : ℝ) ^ (n + 1) = (x / (2 : ℝ) ^ n) / ((2 : ℕ) : ℝ) := by
    rw [zpow_succ_two, div_div, Nat.cast_ofNat]
  rw [h]
  simpa only [Nat.cast_ofNat] using Int.floor_div_natCast (x / (2 : ℝ) ^ n) (2 : ℕ)

/-- The dyadic cell of level `n` is contained in the dyadic cell of level `n+1` (its parent). -/
lemma dyCell_subset_succ (n : ℤ) (k : ℤ) : dyCell n k ⊆ dyCell (n + 1) (k / 2) := by
  intro x hx
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := zpow_two_pos n
  have hn1 : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := zpow_succ_two n
  have h2i : (2 : ℤ) * (k / 2) ≤ k := by
    have h1 := Int.mul_ediv_add_emod k 2
    have h2 := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
    omega
  have h3i : k ≤ 2 * (k / 2) + 1 := by
    have h1 := Int.mul_ediv_add_emod k 2
    have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
    omega
  have h2r : (2 : ℝ) * ((k / 2 : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2i
  have h3r : (k : ℝ) ≤ 2 * ((k / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast h3i
  simp only [dyCell, Set.mem_Ico] at hx ⊢
  constructor
  · rw [hn1]; nlinarith
  · rw [hn1]; nlinarith

lemma dyCell_subset_parent (n : ℤ) (x : ℝ) :
    dyCell n (dyIdx n x) ⊆ dyCell (n + 1) (dyIdx (n + 1) x) := by
  rw [dyIdx_succ]
  exact dyCell_subset_succ n (dyIdx n x)

/-- Nesting of the dyadic cells: for `n ≤ m` the level-`n` cell containing `x` is contained in the
level-`m` cell containing `x`. -/
lemma dyCell_subset_of_le {n m : ℤ} (h : n ≤ m) (x : ℝ) :
    dyCell n (dyIdx n x) ⊆ dyCell m (dyIdx m x) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = n + j := ⟨(m - n).toNat, by omega⟩
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : dyCell n (dyIdx n x) ⊆ dyCell (n + (j : ℤ)) (dyIdx (n + (j : ℤ)) x) :=
        ih (by omega)
      have h2 : dyCell (n + (j : ℤ)) (dyIdx (n + (j : ℤ)) x)
          ⊆ dyCell (n + (j : ℤ) + 1) (dyIdx (n + (j : ℤ) + 1) x) := dyCell_subset_parent _ x
      have h3 : n + (j : ℤ) + 1 = n + ((j : ℤ) + 1) := by ring
      calc dyCell n (dyIdx n x)
          ⊆ dyCell (n + (j : ℤ)) (dyIdx (n + (j : ℤ)) x) := h1
        _ ⊆ dyCell (n + (j : ℤ) + 1) (dyIdx (n + (j : ℤ) + 1) x) := h2
        _ = dyCell (n + ((j : ℤ) + 1)) (dyIdx (n + ((j : ℤ) + 1)) x) := by rw [h3]

/-- A cell of a smaller level that contains a point of a cell of a bigger level contains it. -/
lemma dyCell_subset_of_meet {n m : ℤ} (h : n ≤ m) {k j : ℤ} {x : ℝ}
    (hx : x ∈ dyCell n j) (hx' : x ∈ dyCell m k) : dyCell n j ⊆ dyCell m k := by
  have h1 : dyCell n j = dyCell n (dyIdx n x) := dyCell_eq_of_meet hx (dyIdx_mem n x)
  have h2 : dyCell m k = dyCell m (dyIdx m x) := dyCell_eq_of_meet hx' (dyIdx_mem m x)
  rw [h1, h2]
  exact dyCell_subset_of_le h x

/-- The cells of `czMax` are pairwise disjoint. -/
lemma czMax_disjoint {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p q : ℤ × ℤ}
    (hp : p ∈ czMax ψ c) (hq : q ∈ czMax ψ c) (hne : p ≠ q) :
    Disjoint (dyCell p.1 p.2) (dyCell q.1 q.2) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · have hsub : dyCell p.1 p.2 ⊆ dyCell q.1 q.2 := dyCell_subset_of_meet hlt.le hxp hxq
    have := hp.2 q hq.1 hsub
    omega
  · have hsame : dyCell p.1 p.2 = dyCell q.1 q.2 := by
      have h1 : dyCell p.1 p.2 = dyCell p.1 (dyIdx p.1 x) :=
        dyCell_eq_of_meet hxp (dyIdx_mem p.1 x)
      have h2 : dyCell q.1 q.2 = dyCell q.1 (dyIdx q.1 x) :=
        dyCell_eq_of_meet hxq (dyIdx_mem q.1 x)
      rw [h1, h2, heq]
    have hp2 : p.2 = q.2 := by
      rw [heq] at hsame
      exact dyCell_index_eq ⟨x, by rwa [← heq], hxq⟩
    exact hne (by ext <;> simp [heq, hp2])
  · have hsub : dyCell q.1 q.2 ⊆ dyCell p.1 p.2 := dyCell_subset_of_meet hgt.le hxq hxp
    have := hq.2 p hp.1 hsub
    omega

/-- A dyadic cell contained in another dyadic cell has the smaller level. -/
lemma dyCell_level_le_of_subset {m j n k : ℤ} (h : dyCell n k ⊆ dyCell m j) : n ≤ m := by
  have hvol : volume (dyCell n k) ≤ volume (dyCell m j) := MeasureTheory.measure_mono h
  rw [dyCell, dyCell, Real.volume_Ico, Real.volume_Ico, dyCell_len, dyCell_len] at hvol
  have h2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ m :=
    (ENNReal.ofReal_le_ofReal_iff (zpow_two_pos m).le).mp hvol
  exact (zpow_le_zpow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mp h2

/-- In `czCells`, the level is bounded above (when `∫ψ < ∞`). -/
lemma czCells_level_le {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hint : ∫⁻ y, ψ y < ∞) :
    ∃ B : ℤ, ∀ (m : ℤ) (k : ℤ), (m, k) ∈ czCells ψ c → m ≤ B := by
  by_cases hctop : c = ⊤
  · refine ⟨0, fun m k hm => ?_⟩
    exfalso
    have h1 : c < ENNReal.ofReal ((2 : ℝ) ^ m)⁻¹ * ∫⁻ y in dyCell m k, ψ y := hm
    rw [hctop] at h1
    exact absurd h1 (not_lt.mpr le_top)
  · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hint.ne hc.ne').ne
    refine ⟨N, fun m k hm => ?_⟩
    have h1 : c < ENNReal.ofReal ((2 : ℝ) ^ m)⁻¹ * ∫⁻ y in dyCell m k, ψ y := hm
    have hpos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_two_pos m
    have h2 : c * ENNReal.ofReal ((2 : ℝ) ^ m) < ∫⁻ y in dyCell m k, ψ y := by
      have h3 := ENNReal.mul_lt_mul_left (a := ENNReal.ofReal ((2 : ℝ) ^ m))
        (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top (b := c)
        (c := ENNReal.ofReal ((2 : ℝ) ^ m)⁻¹ * ∫⁻ y in dyCell m k, ψ y) h1
      have h4 : ENNReal.ofReal ((2 : ℝ) ^ m)⁻¹ * (∫⁻ y in dyCell m k, ψ y)
            * ENNReal.ofReal ((2 : ℝ) ^ m) = ∫⁻ y in dyCell m k, ψ y := by
        rw [ofReal_zpow_inv, mul_assoc,
          mul_comm (∫⁻ y in dyCell m k, ψ y) (ENNReal.ofReal ((2 : ℝ) ^ m)), ← mul_assoc,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top, one_mul]
      rw [h4] at h3
      exact h3
    have h6 : ENNReal.ofReal ((2 : ℝ) ^ m) < (∫⁻ y, ψ y) / c := by
      rw [ENNReal.lt_div_iff_mul_lt (a := ∫⁻ y, ψ y) (b := c)
        (c := ENNReal.ofReal ((2 : ℝ) ^ m)) (Or.inl hc.ne') (Or.inl hctop), mul_comm]
      exact lt_of_lt_of_le h2 (MeasureTheory.setLIntegral_le_lintegral _ _)
    have h7 : ENNReal.ofReal ((2 : ℝ) ^ m) < (N : ℝ≥0∞) := lt_trans h6 hN
    have hNpos : (0 : ℝ) < N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos'
      · rw [h0] at h7; simp at h7
      · exact_mod_cast hpos'
    have h7' : ENNReal.ofReal ((2 : ℝ) ^ m) < ENNReal.ofReal (N : ℝ) := by
      rw [← ENNReal.ofReal_natCast N] at h7
      exact h7
    have h8 : (2 : ℝ) ^ m < (N : ℝ) := (ENNReal.ofReal_lt_ofReal_iff hNpos).mp h7' 
    by_contra hcon
    push_neg at hcon
    have hm0 : 0 ≤ m := by omega
    have hmN : (N : ℝ) < (m : ℝ) := by exact_mod_cast hcon
    have hNpow : (N : ℝ) < (2 : ℝ) ^ (N : ℤ) := by
      have h := Nat.lt_two_pow_self (n := N)
      exact_mod_cast h
    have hm1 : (N : ℤ) + 1 ≤ m := by omega
    have hmono : (2 : ℝ) ^ ((N : ℤ) + 1) ≤ (2 : ℝ) ^ m :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm1
    have hsucc : (2 : ℝ) ^ ((N : ℤ) + 1) = (2 : ℝ) ^ (N : ℤ) * 2 := zpow_succ_two (N : ℤ)
    have hbig : (N : ℝ) < (2 : ℝ) ^ m := by
      have h2N : (N : ℝ) < (2 : ℝ) ^ (N : ℤ) * 2 := by
        nlinarith [hNpow, zpow_pos (by norm_num : (0 : ℝ) < 2) (N : ℤ)]
      calc (N : ℝ) < (2 : ℝ) ^ (N : ℤ) * 2 := h2N
        _ = (2 : ℝ) ^ ((N : ℤ) + 1) := hsucc.symm
        _ ≤ (2 : ℝ) ^ m := hmono
    linarith

set_option maxHeartbeats 1000000 in
/-- Every cell of `czCells` is contained in a cell of `czMax`. -/
lemma exists_czMax_subset {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c)
    (hint : ∫⁻ y, ψ y < ∞) {n : ℤ} {x : ℝ} (hn : (n, dyIdx n x) ∈ czCells ψ c) :
    ∃ p ∈ czMax ψ c, dyCell n (dyIdx n x) ⊆ dyCell p.1 p.2 := by
  obtain ⟨B, hB⟩ := czCells_level_le (ψ := ψ) hc hint
  set S : Set ℤ := {m : ℤ | n ≤ m ∧ (m, dyIdx m x) ∈ czCells ψ c} with hS
  have hne : S.Nonempty := ⟨n, le_rfl, hn⟩
  have hfin : S.Finite :=
    Set.Finite.subset (Set.finite_Icc n B)
      (fun m hm => ⟨hm.1, hB m (dyIdx m x) hm.2⟩)
  obtain ⟨M, hM⟩ := hfin.exists_maximal hne
  have hMmem : M ∈ S := hM.1
  have hMcells : (M, dyIdx M x) ∈ czCells ψ c := hMmem.2
  have hMge : n ≤ M := hMmem.1
  refine ⟨(M, dyIdx M x), ⟨hMcells, fun q hq hsub => ?_⟩, dyCell_subset_of_le hMge x⟩
  have hxq : x ∈ dyCell q.1 q.2 := hsub (dyIdx_mem M x)
  have hqidx : q.2 = dyIdx q.1 x := (dyIdx_eq_of_mem_cell hxq).symm
  have hlev : M ≤ q.1 := dyCell_level_le_of_subset hsub
  have hqmem : q.1 ∈ S := by
    refine ⟨le_trans hMge hlev, ?_⟩
    rw [← hqidx]
    exact hq
  have := hM.2 hqmem hlev
  omega

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- Any cell of `czCells` is contained in a maximal one (arbitrary index form). -/
lemma exists_czMax_subset' {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hint : ∫⁻ y, ψ y < ∞)
    {p : ℤ × ℤ} (hp : p ∈ czCells ψ c) :
    ∃ q ∈ czMax ψ c, dyCell p.1 p.2 ⊆ dyCell q.1 q.2 := by
  obtain ⟨x, hx⟩ := dyCell_nonempty p.1 p.2
  have hxidx : dyIdx p.1 x = p.2 := dyIdx_eq_of_mem_cell hx
  have hp' : (p.1, dyIdx p.1 x) ∈ czCells ψ c := by rwa [hxidx]
  obtain ⟨q, hq, hsub⟩ := exists_czMax_subset hc hint hp'
  refine ⟨q, hq, ?_⟩
  have hcell : dyCell p.1 (dyIdx p.1 x) = dyCell p.1 p.2 := by rw [hxidx]
  rwa [← hcell]

set_option maxHeartbeats 1000000 in
/-- The level set of `dyMax` is the union of the cells of `czCells`. -/
lemma levelSet_eq_iUnion_czCells {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) :
    {x : ℝ | c < dyMax ψ x} = ⋃ p ∈ czCells ψ c, dyCell p.1 p.2 := by
  ext x
  constructor
  · intro hx
    have hx' : c < dyMax ψ x := hx
    unfold dyMax at hx'
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hx'
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp hn
    obtain ⟨hxk, hlt⟩ := lt_iSup_iff.mp hk
    exact mem_iUnion.mpr ⟨(n, k), mem_iUnion.mpr ⟨hlt, hxk⟩⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hp, hxp⟩
    have hp' : c < ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y := hp
    have hle : ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y ≤ dyMax ψ x := by
      unfold dyMax
      exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hxp le_rfl))
    exact lt_of_lt_of_le hp' hle

set_option maxHeartbeats 1000000 in
/-- The level set of `dyMax` is the union of the maximal cells. -/
lemma levelSet_eq_iUnion_czMax {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c)
    (hint : ∫⁻ y, ψ y < ∞) :
    {x : ℝ | c < dyMax ψ x} = ⋃ p ∈ czMax ψ c, dyCell p.1 p.2 := by
  apply le_antisymm
  · rw [levelSet_eq_iUnion_czCells hc]
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hp, hxp⟩
    obtain ⟨q, hq, hsub⟩ := exists_czMax_subset' hc hint hp
    exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hq, hsub hxp⟩⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hp, hxp⟩
    have hp' : c < ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y :=
      czMax_mem_czCells hp
    have hle : ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y
        ≤ dyMax ψ x := by
      unfold dyMax
      exact le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hxp le_rfl))
    exact lt_of_lt_of_le hp' hle

set_option maxHeartbeats 1000000 in
/-- For a maximal cell, the average is at most twice the level. -/
lemma czMax_avg_le {ψ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hint : ∫⁻ y, ψ y < ∞)
    {p : ℤ × ℤ} (hp : p ∈ czMax ψ c) :
    ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y ≤ 2 * c := by
  have hpar : (p.1 + 1, p.2 / 2) ∉ czCells ψ c := by
    intro hmem
    have := hp.2 (p.1 + 1, p.2 / 2) hmem (dyCell_subset_succ p.1 p.2)
    omega
  have hle : ENNReal.ofReal ((2 : ℝ) ^ (p.1 + 1))⁻¹
      * ∫⁻ y in dyCell (p.1 + 1) (p.2 / 2), ψ y ≤ c := by
    by_contra hcon
    exact hpar (not_le.mp hcon)
  have hmono : ∫⁻ y in dyCell p.1 p.2, ψ y
      ≤ ∫⁻ y in dyCell (p.1 + 1) (p.2 / 2), ψ y :=
    MeasureTheory.lintegral_mono_set (dyCell_subset_succ p.1 p.2)
  have hpow : ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹
      = 2 * ENNReal.ofReal ((2 : ℝ) ^ (p.1 + 1))⁻¹ := by
    have key : ((2 : ℝ) ^ p.1)⁻¹ = 2 * (((2 : ℝ) ^ (p.1 + 1))⁻¹) := by
      rw [zpow_succ_two (p.1)]; field_simp
    calc ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹
        = ENNReal.ofReal (2 * (((2 : ℝ) ^ (p.1 + 1))⁻¹)) := by rw [key]
      _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (((2 : ℝ) ^ (p.1 + 1))⁻¹) :=
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)
      _ = 2 * ENNReal.ofReal ((2 : ℝ) ^ (p.1 + 1))⁻¹ := by norm_num
  calc ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹ * ∫⁻ y in dyCell p.1 p.2, ψ y
      ≤ ENNReal.ofReal ((2 : ℝ) ^ p.1)⁻¹
        * ∫⁻ y in dyCell (p.1 + 1) (p.2 / 2), ψ y := mul_le_mul_right hmono _
    _ = 2 * (ENNReal.ofReal ((2 : ℝ) ^ (p.1 + 1))⁻¹
          * ∫⁻ y in dyCell (p.1 + 1) (p.2 / 2), ψ y) := by
        rw [hpow, mul_assoc]
    _ ≤ 2 * c := mul_le_mul_right hle 2

end Work.BourgainPlan.Maximal
