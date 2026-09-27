import Mathlib
import Submission.Commons.Measure.AddCircle.cell_add_cell
import Submission.Commons.Algebra.Group.card_union_image_add_one

open MeasureTheory Set
open scoped ENNReal Pointwise

set_option autoImplicit false
noncomputable section

namespace Commons.Measure.AddCircle

/-- The `k`-th elementary half-open cell of the `n`-fold grid on the additive circle `ℝ/ℤ`:
the image of the half-open interval `[k/n, (k+1)/n)` under the quotient map `ℝ → ℝ/ℤ`. -/
private def cell (n : ℕ) [NeZero n] (k : ZMod n) : Set UnitAddCircle :=
  (fun x : ℝ => (x : UnitAddCircle)) '' Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)

variable {n : ℕ} [NeZero n]

private lemma cell_def (k : ZMod n) : cell n k = (fun x : ℝ => (x : UnitAddCircle)) ''
    Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) := rfl

private lemma cell_interval_subset (k : ZMod n) :
    Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) ⊆ Set.Ico (0 : ℝ) (0 + 1) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  intro x hx
  rw [Set.mem_Ico] at hx ⊢
  refine ⟨le_trans (by positivity) hx.1, ?_⟩
  have hlt : (k.val : ℝ) + 1 ≤ n := by
    have : k.val + 1 ≤ n := Nat.succ_le_of_lt k.val_lt
    exact_mod_cast this
  have hle : ((k.val : ℝ) + 1) / n ≤ 1 := by
    rw [div_le_one hn]; exact hlt
  linarith [hx.2]

private lemma cell_interval_disjoint {k l : ZMod n} (hkl : k ≠ l) :
    Disjoint (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n))
      (Set.Ico ((l.val : ℝ) / n) (((l.val : ℝ) + 1) / n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hne : k.val ≠ l.val := fun h => hkl (ZMod.val_injective n h)
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_Ico] at hx hy
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : (k.val : ℝ) + 1 ≤ l.val := by
      have : k.val + 1 ≤ l.val := h
      exact_mod_cast this
    have h1 : ((k.val : ℝ) + 1) / n ≤ (l.val : ℝ) / n := by gcongr
    linarith [hx.2, hy.1]
  · have hle : (l.val : ℝ) + 1 ≤ k.val := by
      have : l.val + 1 ≤ k.val := h
      exact_mod_cast this
    have h1 : ((l.val : ℝ) + 1) / n ≤ (k.val : ℝ) / n := by gcongr
    linarith [hy.2, hx.1]

private lemma cell_disjoint {k l : ZMod n} (hkl : k ≠ l) : Disjoint (cell n k) (cell n l) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy : x = y := (AddCircle.coe_eq_coe_iff_of_mem_Ico (cell_interval_subset k hx)
    (cell_interval_subset l hy)).mp hyx.symm
  subst hxy
  exact Set.disjoint_left.mp (cell_interval_disjoint hkl) hx hy

private lemma cell_eq_preimage (k : ZMod n) :
    cell n k = (AddCircle.measurableEquivIco (T := (1:ℝ)) (0:ℝ)) ⁻¹'
      ((fun x : Set.Ico (0 : ℝ) (0 + 1) => (x : ℝ)) ⁻¹'
        Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)) := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [Set.mem_preimage, Set.mem_preimage]
    have hmem : t ∈ Set.Ico (0:ℝ) (0 + (1:ℝ)) := by simpa using cell_interval_subset k ht
    change ((AddCircle.equivIco (1:ℝ) 0 ((t : UnitAddCircle))) : ℝ) ∈
      Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)
    rw [AddCircle.equivIco_coe_eq hmem]
    exact ht
  · intro hp
    rw [Set.mem_preimage, Set.mem_preimage] at hp
    exact ⟨(AddCircle.equivIco (1:ℝ) 0 p : ℝ), hp, by simp⟩

private lemma measurableSet_cell (k : ZMod n) : MeasurableSet (cell n k) := by
  rw [cell_eq_preimage (n := n) k]
  exact (measurableSet_Ico.preimage measurable_subtype_coe).preimage
    (AddCircle.measurableEquivIco (T := (1:ℝ)) (0:ℝ)).measurable

private lemma cell_subset_univ (k : ZMod n) : cell n k ⊆ (Set.univ : Set UnitAddCircle) := fun _ _ => trivial

private lemma volume_cell (k : ZMod n) : volume (cell n k) = ENNReal.ofReal (1 / n) := by
  have hmeas := measurableSet_cell (n := n) k
  rw [AddCircle.add_projection_respects_measure (1:ℝ) (0:ℝ) hmeas]
  have hle1 : QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1) ⊆
      Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) ∪ {1} := by
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_Ioc] at hx2
    rcases hx1 with ⟨t, ht, htx⟩
    rw [Set.mem_union]
    by_cases hx : x = 1
    · exact Or.inr hx
    · left
      have hxI : x ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨le_of_lt hx2.1, lt_of_le_of_ne hx2.2 (by simpa using hx)⟩
      have htx' : t = x := (AddCircle.coe_eq_coe_iff_of_mem_Ico (cell_interval_subset k ht) hxI).mp htx
      rwa [htx'] at ht
  have hle2 : Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) ⊆
      QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1) ∪ {0} := by
    intro x hx
    rw [Set.mem_union]
    by_cases hx0 : x = 0
    · exact Or.inr hx0
    · left
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rw [Set.mem_Ioc]
      exact ⟨lt_of_le_of_ne (cell_interval_subset k hx).1 (Ne.symm hx0),
        le_of_lt (cell_interval_subset k hx).2⟩
  have hnull1 : volume ({1} : Set ℝ) = 0 := by simp
  have hnull0 : volume ({0} : Set ℝ) = 0 := by simp
  have h1 : volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1)) ≤
      volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)) := by
    calc volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1))
        ≤ volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n) ∪ {1}) :=
          measure_mono hle1
      _ ≤ volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)) + volume ({1} : Set ℝ) :=
          measure_union_le _ _
      _ = volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)) := by rw [hnull1, add_zero]
  have h2 : volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n)) ≤
      volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1)) := by
    calc volume (Set.Ico ((k.val : ℝ) / n) (((k.val : ℝ) + 1) / n))
        ≤ volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1) ∪ {0}) :=
          measure_mono hle2
      _ ≤ volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1)) + volume ({0} : Set ℝ) :=
          measure_union_le _ _
      _ = volume (QuotientAddGroup.mk ⁻¹' cell n k ∩ Set.Ioc (0:ℝ) (0 + 1)) := by rw [hnull0, add_zero]
  rw [le_antisymm h1 h2, Real.volume_Ico]
  congr 1
  ring

private lemma exists_cell_mem (p : UnitAddCircle) : ∃ k : ZMod n, p ∈ cell n k := by
  obtain ⟨t, ht, htp⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) p
  rw [Set.mem_Ico] at ht
  set m : ℤ := ⌊(n : ℝ) * t⌋ with hm
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have h1 : (m : ℝ) ≤ (n : ℝ) * t := by rw [hm]; exact Int.floor_le _
  have h2 : (n : ℝ) * t < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one _
  have hnt : (0 : ℝ) ≤ (n : ℝ) * t := mul_nonneg (le_of_lt hn) ht.1
  have hm0 : 0 ≤ m := by
    have : (-1 : ℤ) < m := by
      have : (-1 : ℝ) < (m : ℝ) := by linarith
      exact_mod_cast this
    omega
  have hmn : m < (n : ℤ) := by
    have hlt : (n : ℝ) * t < (n : ℝ) := by nlinarith [ht.2]
    have : (m : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(m.toNat : ZMod n), t, ?_, htp⟩
  have hval : ((m.toNat : ZMod n)).val = m.toNat := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    omega
  rw [hval, Set.mem_Ico]
  have hcast : ((m.toNat : ℝ)) = (m : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  constructor
  · rw [div_le_iff₀ hn, hcast]; linarith
  · rw [lt_div_iff₀ hn, hcast]; linarith

private lemma volume_biUnion_cell (J : Finset (ZMod n)) :
    volume (⋃ j ∈ J, cell n j) = ENNReal.ofReal ((J.card : ℝ) / n) := by
  rw [measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun j _ => volume_cell j), Finset.sum_const, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg J.card), mul_one_div]
  · intro j _ l _ hjl
    exact cell_disjoint hjl
  · intro j _
    exact measurableSet_cell j

private lemma measurableSet_biUnion_cell (J : Finset (ZMod n)) :
    MeasurableSet (⋃ j ∈ J, cell n j) :=
  Finset.measurableSet_biUnion J (fun j _ => measurableSet_cell j)

/-- The grid cells of the `n`-fold grid that are entirely contained in `A`. -/
private def gridSet (n : ℕ) [NeZero n] (A : Set UnitAddCircle) : Finset (ZMod n) := by
  classical exact Finset.univ.filter (fun k => cell n k ⊆ A)

/-- The inner grid approximation of `A`: the union of all grid cells contained in `A`. -/
private def gridApprox (n : ℕ) [NeZero n] (A : Set UnitAddCircle) : Set UnitAddCircle :=
  ⋃ k ∈ gridSet n A, cell n k

variable (A B : Set UnitAddCircle)

private lemma gridApprox_subset : gridApprox n A ⊆ A := by
  classical
  intro p hp
  rw [gridApprox] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨k, hkS, hkp⟩ := hp
  exact (Finset.mem_filter.mp hkS).2 hkp

private lemma gridSet_mono (h : A ⊆ B) : gridSet n A ⊆ gridSet n B := by
  classical
  intro k hk
  rw [gridSet] at hk ⊢
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subset.trans (Finset.mem_filter.mp hk).2 h⟩

private lemma volume_gridApprox :
    volume (gridApprox n A) = ENNReal.ofReal (((gridSet n A).card : ℝ) / n) :=
  volume_biUnion_cell (gridSet n A)

private lemma measurableSet_gridApprox : MeasurableSet (gridApprox n A) :=
  measurableSet_biUnion_cell (gridSet n A)

/-- The child commons version of the cell addition, phrased with `cell`. -/
private lemma cell_add_cell' (k l : ZMod n) :
    cell n k + cell n l = cell n (k + l) ∪ cell n (k + l + 1) := by
  simpa only [cell_def] using Commons.Measure.AddCircle.cell_add_cell n k l

private lemma iUnion_cell_add_iUnion_cell (S T : Finset (ZMod n)) :
    (⋃ k ∈ S, cell n k) + (⋃ l ∈ T, cell n l)
      = ⋃ j ∈ (S + T) ∪ (S + T).image (fun x => x + 1), cell n j := by
  classical
  apply Set.Subset.antisymm
  · rintro p ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_iUnion] at ha hb
    obtain ⟨k, hkS, hak⟩ := ha
    obtain ⟨l, hkT, hbl⟩ := hb
    have hmem : a + b ∈ cell n (k + l) ∪ cell n (k + l + 1) := by
      rw [← cell_add_cell']
      exact ⟨a, hak, b, hbl, rfl⟩
    rcases hmem with h | h
    · refine Set.mem_iUnion.mpr ⟨k + l, Set.mem_iUnion.mpr ⟨?_, h⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_add.mpr ⟨k, hkS, l, hkT, rfl⟩)
    · refine Set.mem_iUnion.mpr ⟨k + l + 1, Set.mem_iUnion.mpr ⟨?_, h⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k + l, Finset.mem_add.mpr ⟨k, hkS, l, hkT, rfl⟩, rfl⟩)
  · rintro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨j, hj, hp⟩ := hp
    rw [Finset.mem_union] at hj
    rcases hj with hj | hj
    · obtain ⟨k, hkS, l, hkT, hkl⟩ := Finset.mem_add.mp hj
      rw [← hkl] at hp
      have hmem : p ∈ cell n k + cell n l := by rw [cell_add_cell']; exact Or.inl hp
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      exact ⟨a, Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkS, ha⟩⟩,
             b, Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hkT, hb⟩⟩, hab⟩
    · obtain ⟨m, hm, hjm⟩ := Finset.mem_image.mp hj
      obtain ⟨k, hkS, l, hkT, hkl⟩ := Finset.mem_add.mp hm
      rw [← hjm, ← hkl] at hp
      have hmem : p ∈ cell n k + cell n l := by rw [cell_add_cell']; exact Or.inr hp
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      exact ⟨a, Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkS, ha⟩⟩,
             b, Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hkT, hb⟩⟩, hab⟩

private lemma gridApprox_add :
    gridApprox n A + gridApprox n B
      = ⋃ j ∈ (gridSet n A + gridSet n B)
          ∪ (gridSet n A + gridSet n B).image (fun x => x + 1), cell n j := by
  rw [gridApprox, gridApprox]
  exact iUnion_cell_add_iUnion_cell _ _

private lemma volumeReal_gridApprox :
    volume.real (gridApprox n A) = ((gridSet n A).card : ℝ) / n := by
  rw [measureReal_def, volume_gridApprox, ENNReal.toReal_ofReal]
  positivity

private lemma volumeReal_gridApprox_add :
    volume.real (gridApprox n A + gridApprox n B) =
      ((((gridSet n A + gridSet n B) ∪ (gridSet n A + gridSet n B).image
        (fun x => x + 1))).card : ℝ) / n := by
  rw [measureReal_def, gridApprox_add, volume_biUnion_cell, ENNReal.toReal_ofReal]
  positivity

/-- The key finite combinatorial estimate: for `n` prime and nonempty index sets `S`, `T` of cells,
the number of cells meeting the union of the cells of `S + T` and its shift by one is at least
`min n (|S| + |T|)`. -/
private lemma card_le_card_union_shift_of_prime (hp : n.Prime) {S T : Finset (ZMod n)}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    min n (S.card + T.card) ≤ ((S + T) ∪ (S + T).image (fun x => x + 1)).card := by
  classical
  have hU : (S + T).Nonempty := by
    obtain ⟨k, hk⟩ := hS
    obtain ⟨l, hl⟩ := hT
    exact ⟨k + l, Finset.mem_add.mpr ⟨k, hk, l, hl, rfl⟩⟩
  have hCD : min n (S.card + T.card - 1) ≤ (S + T).card := ZMod.cauchy_davenport hp hS hT
  by_cases hcase : (S + T).card = n
  · have htop : S + T = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcase, ZMod.card]
    have hW : ((Finset.univ : Finset (ZMod n)) ∪ Finset.univ.image (fun x => x + 1))
        = Finset.univ := by simp
    rw [htop, hW, Finset.card_univ, ZMod.card]
    exact min_le_left _ _
  · have hle : (S + T).card ≤ n := by
      simpa [ZMod.card] using Finset.card_le_univ (S + T)
    have hlt : (S + T).card < n := lt_of_le_of_ne hle hcase
    have hne : S + T ≠ Finset.univ := by
      intro h; rw [h, Finset.card_univ, ZMod.card] at hcase; exact hcase rfl
    have h1 := Commons.Algebra.Group.card_union_image_add_one n (S + T) hU hne
    have hx : S.card + T.card - 1 ≤ (S + T).card := by
      by_cases h : S.card + T.card - 1 ≤ n
      · rw [min_eq_right h] at hCD; exact hCD
      · exfalso
        have hlt : n < S.card + T.card - 1 := not_le.mp h
        have : min n (S.card + T.card - 1) = n := min_eq_left (le_of_lt hlt)
        rw [this] at hCD
        omega
    calc min n (S.card + T.card) ≤ S.card + T.card := min_le_right _ _
      _ = (S.card + T.card - 1) + 1 := by
          have h1' : 1 ≤ S.card + T.card := by
            have := hS.card_pos; have := hT.card_pos; omega
          omega
      _ ≤ (S + T).card + 1 := by omega
      _ ≤ ((S + T) ∪ (S + T).image (fun x => x + 1)).card := h1

private lemma min_le_volumeReal_gridApprox_add (hp : n.Prime)
    (hS : (gridSet n A).Nonempty) (hT : (gridSet n B).Nonempty) :
    min 1 (volume.real (gridApprox n A) + volume.real (gridApprox n B))
      ≤ volume.real (gridApprox n A + gridApprox n B) := by
  rw [volumeReal_gridApprox, volumeReal_gridApprox, volumeReal_gridApprox_add]
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hsuff := card_le_card_union_shift_of_prime (n := n) hp hS hT
  have hcast : min (n : ℝ) (((gridSet n A).card : ℝ) + ((gridSet n B).card : ℝ))
      ≤ (((gridSet n A + gridSet n B) ∪ (gridSet n A + gridSet n B).image
          (fun x => x + 1))).card := by
    have heq : min (n : ℝ) (((gridSet n A).card : ℝ) + ((gridSet n B).card : ℝ))
        = (((min n ((gridSet n A).card + (gridSet n B).card)) : ℕ) : ℝ) := by
      rw [Nat.cast_min, Nat.cast_add]
    rw [heq]
    exact_mod_cast hsuff
  have hdiv : min (n : ℝ) (((gridSet n A).card : ℝ) + ((gridSet n B).card : ℝ)) / (n : ℝ)
      ≤ ((((gridSet n A + gridSet n B) ∪ (gridSet n A + gridSet n B).image
          (fun x => x + 1))).card : ℝ) / n :=
    div_le_div_of_nonneg_right hcast (le_of_lt hn)
  rw [← min_div_div_right (le_of_lt hn)] at hdiv
  rw [div_self (ne_of_gt hn)] at hdiv
  rw [add_div] at hdiv
  exact hdiv

private lemma dist_le_of_mem_cell {k : ZMod n} {x y : UnitAddCircle} (hx : x ∈ cell n k)
    (hy : y ∈ cell n k) : dist x y ≤ 1 / n := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  have h1 : ‖(((s - t : ℝ)) : UnitAddCircle)‖ ≤ ‖(s - t : ℝ)‖ :=
    QuotientAddGroup.norm_mk_le_norm
  rw [Real.norm_eq_abs] at h1
  rw [Set.mem_Ico] at hs ht
  rw [add_div] at hs ht
  refine le_trans h1 ?_
  rw [abs_sub_le_iff]
  exact ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩

private lemma exists_forall_gridApprox {A : Set UnitAddCircle} (hA : IsOpen A) (hAne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n →
      (gridSet n A).Nonempty ∧ volume.real A - ε ≤ volume.real (gridApprox n A) := by
  obtain ⟨x₀, hx₀⟩ := hAne
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.mp hA x₀ hx₀
  obtain ⟨K, hKA, hKc, hKvol⟩ := hA.measurableSet.exists_isCompact_lt_add
    (measure_ne_top (volume : Measure UnitAddCircle) A)
    (ε := ENNReal.ofReal (ε / 2)) (by rw [ENNReal.ofReal_ne_zero_iff]; linarith)
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := hKc.exists_cthickening_subset_open hA hKA
  have hKvol' : volume.real A - ε / 2 < volume.real K := by
    have h' : (volume A).toReal < (volume K + ENNReal.ofReal (ε / 2)).toReal :=
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by finiteness)).mpr hKvol
    rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),
      ENNReal.toReal_ofReal (by linarith)] at h'
    rw [measureReal_def, measureReal_def]
    linarith
  have hmin : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min δ₀ δ₁)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (one_div_pos.mpr hmin) hN.le
  have hNle : (1 : ℝ) / (N : ℝ) < min δ₀ δ₁ := by
    have h1 : (1 : ℝ) < (N : ℝ) * min δ₀ δ₁ := (div_lt_iff₀ hmin).mp hN
    rw [div_lt_iff₀ hNpos]
    linarith
  refine ⟨max N 1, ?_⟩
  intro n hninst hn
  have := hninst
  classical
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle : 1 / (n : ℝ) < min δ₀ δ₁ := by
    have h2 : (1 : ℝ) / (n : ℝ) ≤ 1 / (N : ℝ) :=
      one_div_le_one_div_of_le hNpos (by exact_mod_cast hnN)
    exact lt_of_le_of_lt h2 hNle
  have hδle : 1 / (n : ℝ) < δ₀ := lt_of_lt_of_le hle (min_le_left _ _)
  have hδle₁ : 1 / (n : ℝ) < δ₁ := lt_of_lt_of_le hle (min_le_right _ _)
  constructor
  · obtain ⟨k, hk⟩ := exists_cell_mem (n := n) x₀
    refine ⟨k, ?_⟩
    rw [gridSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
    refine hδ₀sub ?_
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_le_of_lt (dist_le_of_mem_cell hk hy) hδle
  · have hKsub : K ⊆ gridApprox n A := by
      intro x hxK
      obtain ⟨k, hk⟩ := exists_cell_mem (n := n) x
      refine Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨?_, hk⟩⟩
      rw [gridSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun y hy => ?_⟩
      refine hδ₁sub ?_
      refine Metric.mem_cthickening_of_dist_le y x δ₁ K hxK ?_
      rw [dist_comm]
      exact le_trans (dist_le_of_mem_cell hk hy) hδle₁.le
    have := measureReal_mono hKsub (by finiteness : volume (gridApprox n A) ≠ ∞)
    linarith

private lemma min_one_add_eps (x ε : ℝ) (hε : 0 ≤ ε) : min 1 (x + ε) ≤ min 1 x + ε := by
  rcases le_total x 1 with hx | hx
  · rw [min_eq_right hx]
    rcases le_total (x + ε) 1 with h | h
    · rw [min_eq_right h]
    · rw [min_eq_left h]; exact h
  · rw [min_eq_left hx]
    have : min 1 (x + ε) ≤ 1 := min_le_left _ _
    linarith

/-- **Kemperman's inequality for the circle**, real-valued form, for nonempty open sets. -/
private lemma kemperman_open_real {A B : Set UnitAddCircle} (hA : IsOpen A) (hB : IsOpen B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    min 1 (volume.real A + volume.real B) ≤ volume.real (A + B) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N₁, hN₁⟩ := exists_forall_gridApprox (A := A) hA hAne (ε := ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := exists_forall_gridApprox (A := B) hB hBne (ε := ε / 2) (by linarith)
  obtain ⟨p, hpN, hpprime⟩ := Nat.exists_infinite_primes (max (max N₁ N₂) 2)
  have : NeZero p := ⟨hpprime.ne_zero⟩
  have hp₁ : N₁ ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hpN
  have hp₂ : N₂ ≤ p := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hpN
  have h₁ := hN₁ p hp₁
  have h₂ := hN₂ p hp₂
  have hper := min_le_volumeReal_gridApprox_add (A := A) (B := B) hpprime h₁.1 h₂.1
  have hmono : volume.real (gridApprox p A + gridApprox p B) ≤ volume.real (A + B) :=
    measureReal_mono (add_subset_add (gridApprox_subset A) (gridApprox_subset B))
      (measure_ne_top _ _)
  have hstep : volume.real A + volume.real B ≤
      volume.real (gridApprox p A) + volume.real (gridApprox p B) + ε := by linarith [h₁.2, h₂.2]
  calc min 1 (volume.real A + volume.real B)
      ≤ min 1 (volume.real (gridApprox p A) + volume.real (gridApprox p B) + ε) :=
        min_le_min_left 1 hstep
    _ ≤ min 1 (volume.real (gridApprox p A) + volume.real (gridApprox p B)) + ε :=
        min_one_add_eps _ ε hε.le
    _ ≤ volume.real (A + B) + ε := by linarith [hper, hmono]

/-- **Kemperman's inequality for the circle**: for nonempty open `A`, `B` in `ℝ/ℤ` the
normalised Haar measure of the sumset is at least `min 1 (μ A + μ B)`. -/
theorem kemperman_open {A B : Set UnitAddCircle} (hA : IsOpen A) (hB : IsOpen B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    min 1 (volume A + volume B) ≤ volume (A + B) := by
  have hreal := kemperman_open_real hA hB hAne hBne
  have hAfin : volume A ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _
  have hBfin : volume B ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _
  have hABfin : volume (A + B) ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _
  have hsum : volume A + volume B = ENNReal.ofReal (volume.real A + volume.real B) := by
    rw [show volume A = ENNReal.ofReal (volume.real A) from
      (ENNReal.ofReal_toReal hAfin).symm,
      show volume B = ENNReal.ofReal (volume.real B) from
      (ENNReal.ofReal_toReal hBfin).symm,
      ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  have hmin : min 1 (ENNReal.ofReal (volume.real A + volume.real B))
      = ENNReal.ofReal (min 1 (volume.real A + volume.real B)) := by
    rcases le_total (volume.real A + volume.real B) 1 with h | h
    · have h' : ENNReal.ofReal (volume.real A + volume.real B) ≤ 1 := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h
      rw [min_eq_right h', min_eq_right h]
    · have h' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (volume.real A + volume.real B) := by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h
      rw [min_eq_left h', min_eq_left h, ENNReal.ofReal_one]
  rw [hsum, hmin, show volume (A + B) = ENNReal.ofReal (volume.real (A + B)) from
    (ENNReal.ofReal_toReal hABfin).symm]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Kemperman/Raikov for the circle, `1/3` form**: a nonempty open subset `U` of the circle of
measure `> 1/3` contains `a, b, c` with `a + b + c = 0`. -/
private theorem exists_add_add_eq_zero_of_third_lt {U : Set UnitAddCircle} (hU : IsOpen U)
    (hUne : U.Nonempty) (h : (1 / 3 : ℝ) < volume.real U) :
    ∃ a ∈ U, ∃ b ∈ U, ∃ c ∈ U, a + b + c = 0 := by
  by_contra hcon
  have hdisj : Disjoint (U + U) (-U) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, b, hb, rfl⟩ hx
    rw [Set.mem_neg] at hx
    exact hcon ⟨a, ha, b, hb, -(a + b), hx, by abel⟩
  have hmeas_neg : MeasurableSet (-U) := hU.measurableSet.neg
  have h1 : volume.real (U + U) + volume.real (-U) ≤ 1 := by
    have hsub : (U + U) ∪ (-U) ⊆ (Set.univ : Set UnitAddCircle) := fun _ _ => trivial
    have h2 : volume.real ((U + U) ∪ (-U)) ≤ volume.real (Set.univ : Set UnitAddCircle) :=
      measureReal_mono hsub (by finiteness)
    rw [measureReal_union hdisj hmeas_neg (by finiteness) (by finiteness)] at h2
    have h3 : volume.real (Set.univ : Set UnitAddCircle) = 1 := by
      rw [measureReal_def, AddCircle.measure_univ]
      simp
    rw [h3] at h2
    exact h2
  have hneg : volume.real (-U) = volume.real U := by
    rw [measureReal_def, measureReal_def, Measure.measure_neg]
  rw [hneg] at h1
  have hkem := kemperman_open_real hU hU hUne hUne
  have h2 : (2 / 3 : ℝ) < volume.real (U + U) := by
    have h3 : volume.real U + volume.real U = 2 * volume.real U := by ring
    rw [h3] at hkem
    rcases le_total (2 * volume.real U) 1 with hlt | hlt
    · rw [min_eq_right hlt] at hkem; linarith
    · rw [min_eq_left hlt] at hkem; linarith
  linarith


end Commons.Measure.AddCircle
