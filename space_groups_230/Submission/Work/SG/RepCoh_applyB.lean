import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.ApplyBDefs
import Submission.Work.SG.applyB_range
import Submission.Work.SG.ad_bmats_getD_succ

/-!
# `RepCoh_applyB`: the `applyB` recursion for the cocycle coordinates

Let `z : ℕ → Fin 3 → ℤ` be the integer numerator of a `1`-cocycle on the point group `arithRep j`
(`z i` is `n · τ(elems i)`).  The cocycle identity reads

`z(g·i) ≡ z(g) + g · z(i)   (mod n)`  (`g` a generator, `i` an element index),

which is the hypothesis `hrec` below.  Then

* `z i ≡ applyB (bmats[i]) y  (mod n)` for every element index `i`, where `y = yvec j z` collects
  the generator values `z(geni g)`;
* every relation row of `Data.relRows` annihilates `y` modulo `n`.

The first statement is a strong induction along the BFS indexing of `ArithData.elems`
(`elems[i+1] = gens[par[i].1] · elems[par[i].2]`), the second is the linearity of `applyB`.
-/

namespace Work.SG

open Work.SG.RC

/-! ## 0. A length computation for `yvec` -/

theorem length_flatMap_toList : ∀ l : List Data.V3,
    (l.flatMap Data.V3.toList).length = 3 * l.length
  | [] => rfl
  | v :: t => by
      cases v with
      | mk x y z =>
        simp only [List.flatMap_cons, Data.V3.toList, Data.V3.toList, List.length_append,
          List.length_cons, List.length_nil]
        rw [length_flatMap_toList t]
        omega

theorem yvec_len' (j : Fin 73) (z : ℕ → Fin 3 → ℤ) : (RC.yvec j z).length = 3 * RC.KK j := by
  show (Data.unblocks ((List.range (RC.KK j)).map (fun g => CZ.ofFun (z (RC.geni j g))))).length
    = 3 * RC.KK j
  simp only [Data.unblocks]
  rw [length_flatMap_toList, List.length_map, List.length_range]

/-! ## 1. The block list and rows of `Data.relRows` -/

/-- The generator matrix used by the `(g', i)`-th relation family. -/
abbrev blkG (j : Fin 73) (g' : ℕ) : Data.M3 := (RC.Ad j).gens.getD g' Data.M3.one

/-- The "left" block list `bmats[mulg j g' i]`. -/
abbrev blkLhs (j : Fin 73) (g' i : ℕ) : List Data.M3 :=
  (Data.bmats (RC.Ad j)).getD (RC.mulg j g' i) []

/-- The "right" block list `bmats[i]`. -/
abbrev blkRhs (j : Fin 73) (g' i : ℕ) : List Data.M3 := (Data.bmats (RC.Ad j)).getD i []

/-- The block list of the `(g', i)`-th relation family:
`bmats[mulg g' i] - (E_{g'} + g' · bmats[i])` blockwise. -/
def relBlk (j : Fin 73) (g' i : ℕ) : List Data.M3 :=
  let gM := (RC.Ad j).gens.getD g' Data.M3.one
  let lhs := (Data.bmats (RC.Ad j)).getD ((RC.Ad j).mulGen.getD g' [] |>.getD i 0) []
  let rhs := (Data.bmats (RC.Ad j)).getD i [] |>.map (Data.M3.mul gM)
  (List.range (RC.Ad j).gens.length).map fun g =>
    Data.M3.sub (lhs.getD g Data.M3.zero)
      (Data.M3.add (if g = g' then Data.M3.one else Data.M3.zero) (rhs.getD g Data.M3.zero))

/-- The `r`-th relation row of the `(g', i)`-th family. -/
def relRow (j : Fin 73) (g' i r : ℕ) : List ℤ :=
  (relBlk j g' i).flatMap fun A => ((Data.M3.rows A).getD r Data.V3.zero).toList

theorem relBlk_eq (j : Fin 73) (g' i : ℕ) :
    relBlk j g' i = (List.range (RC.Ad j).gens.length).map (fun g =>
      Data.M3.sub ((blkLhs j g' i).getD g Data.M3.zero)
        (Data.M3.add (if g = g' then Data.M3.one else Data.M3.zero)
          (((blkRhs j g' i).map (Data.M3.mul (blkG j g'))).getD g Data.M3.zero))) := rfl

theorem relBlk_length (j : Fin 73) (g' i : ℕ) : (relBlk j g' i).length = RC.KK j := by
  rw [relBlk_eq]
  simp [RC.KK]

theorem relRows_eq (j : Fin 73) :
    Data.relRows (RC.Ad j) = (List.range (RC.KK j)).flatMap (fun g' =>
      (List.range (RC.Ad j).n).flatMap (fun i => [0, 1, 2].map (fun r => relRow j g' i r))) :=
  rfl

theorem relRow_eq_unblocks (j : Fin 73) (g' i r : ℕ) :
    relRow j g' i r = Data.unblocks ((relBlk j g' i).map
      (fun A => (Data.M3.rows A).getD r Data.V3.zero)) := by
  simp only [relRow, Data.unblocks, List.flatMap_map]

/-- `relBlk`'s `g`-th block, in the `sub … (add … (mul …))` form. -/
theorem relBlk_getD (j : Fin 73) (g' i g : ℕ) (hi : i < (RC.Ad j).n) (hg : g < RC.KK j) :
    (relBlk j g' i).getD g Data.M3.zero =
      Data.M3.sub ((blkLhs j g' i).getD g Data.M3.zero)
        (Data.M3.add (if g = g' then Data.M3.one else Data.M3.zero)
          (Data.M3.mul (blkG j g') ((blkRhs j g' i).getD g Data.M3.zero))) := by
  rw [relBlk_eq]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hg),
      List.getElem_map, List.getElem_range]
  rw [getD_map_lt _ _ _ _ (by rw [ad_bmats_rowlen j i hi]; exact hg)]

/-! ## 2. `applyB` of a `bmats` block list -/

theorem applyB_getD (k : ℕ) (L : List Data.M3) (y : List ℤ) (hL : L.length = k)
    (hk : k ≤ (Data.blocks y).length) :
    (Data.applyB L y).toFun = appV k (fun g => L.getD g Data.M3.zero) y := by
  conv_lhs => rw [← eq_range_map_getD L Data.M3.zero]
  rw [hL]
  exact applyB_range k (fun g => L.getD g Data.M3.zero) y hk

theorem blocks_yvec' (j : Fin 73) (z : ℕ → Fin 3 → ℤ) (g : ℕ) (hg : g < RC.KK j) :
    (Data.blocks (RC.yvec j z)).getD g Data.V3.zero = CZ.ofFun (z (RC.geni j g)) :=
  RC.blocks_yvec j z g hg

theorem yvec_hk (j : Fin 73) (z : ℕ → Fin 3 → ℤ) :
    RC.KK j ≤ (Data.blocks (RC.yvec j z)).length := by
  rw [blocks_length, yvec_len']
  omega

/-- The tree step of the `bmats` recursion, at the level of `applyB`. -/
theorem applyB_step (j : Fin 73) (z : ℕ → Fin 3 → ℤ) (i : ℕ)
    (hi : i < (RC.Ad j).par.length) :
    Data.applyB ((Data.bmats (RC.Ad j)).getD (i + 1) []) (RC.yvec j z) =
      Data.V3.add (CZ.ofFun (z (RC.geni j (RC.par1 j i))))
        (Data.M3.mulV (RC.gMt j (RC.par1 j i))
          (Data.applyB ((Data.bmats (RC.Ad j)).getD (RC.par2 j i) []) (RC.yvec j z))) := by
  apply CZ.toFun_inj
  have hg : RC.par1 j i < RC.KK j := RC.par1_lt j i hi
  have hp2n : RC.par2 j i < (RC.Ad j).n := by
    have h2 := RC.par2_le j i hi
    have h1 : i < (RC.Ad j).n := by have := RC.par_len_eq j; omega
    omega
  have hk := yvec_hk j z
  rw [toFun_add, ← mvf_eq_mulV]
  rw [applyB_getD (RC.KK j) (blkRhs j (RC.par1 j i) (RC.par2 j i)) (RC.yvec j z)
    (ad_bmats_rowlen j (RC.par2 j i) hp2n) hk]
  rw [ad_bmats_getD_succ j i hi]
  rw [applyB_range (RC.KK j) _ (RC.yvec j z) hk, appV_add,
    appV_single (RC.KK j) (RC.par1 j i) hg Data.M3.one (RC.yvec j z), mvf_one_mat,
    blocks_yvec' j z (RC.par1 j i) hg, appV_mul]

/-- `mulg j g' i` is the BFS index of `gens g' · elems i` on the tree edge. -/
theorem ad_mulg_par (j : Fin 73) (i : ℕ) (hi : i < (RC.Ad j).par.length) :
    RC.mulg j (RC.par1 j i) (RC.par2 j i) = i + 1 := by
  have hg := RC.par1_lt j i hi
  have hsub : i < (RC.Ad j).n - 1 := by rw [← RC.par_len_eq j]; exact hi
  have hp2n : RC.par2 j i < (RC.Ad j).n := by
    have h2 := RC.par2_le j i hi
    have h1 : i < (RC.Ad j).n := by have := RC.par_len_eq j; omega
    omega
  have hm : RC.mulg j (RC.par1 j i) (RC.par2 j i) < (RC.Ad j).n :=
    RC.mulg_lt j _ hg _ hp2n
  have h3 := RC.Ad_par_rel3 j i hsub
  have h4 := RC.Ad_mulGen_rel j (RC.par1 j i) hg (RC.par2 j i) hp2n
  have h5 : (RC.Ad j).elems.getD (RC.mulg j (RC.par1 j i) (RC.par2 j i)) Data.M3.one
      = (RC.Ad j).elems.getD (i + 1) Data.M3.one := by
    simp only [RC.mulg, RC.par1, RC.par2, RC.par] at h3 h4 ⊢
    rw [h4, h3]
  refine RC.e_inj j hm (by omega) ?_
  simp only [RC.e, RC.eM]
  rw [h5]

/-- The relation block list is `bmats[mulg g' i]` minus the `(geni, i)`-contribution. -/
theorem applyB_relBlk (j : Fin 73) (z : ℕ → Fin 3 → ℤ) (g' : ℕ) (hg' : g' < RC.KK j)
    (i : ℕ) (hi : i < (RC.Ad j).n) :
    Data.applyB (relBlk j g' i) (RC.yvec j z) =
      Data.V3.sub (Data.applyB (blkLhs j g' i) (RC.yvec j z))
        (Data.V3.add (CZ.ofFun (z (RC.geni j g')))
          (Data.M3.mulV (RC.gMt j g') (Data.applyB (blkRhs j g' i) (RC.yvec j z)))) := by
  apply CZ.toFun_inj
  have hmlt := RC.mulg_lt j g' hg' i hi
  have hk := yvec_hk j z
  rw [toFun_sub, toFun_add, ← mvf_eq_mulV]
  rw [applyB_getD (RC.KK j) (blkRhs j g' i) (RC.yvec j z) (ad_bmats_rowlen j i hi) hk]
  rw [applyB_getD (RC.KK j) (blkLhs j g' i) (RC.yvec j z) (ad_bmats_rowlen j (RC.mulg j g' i) hmlt) hk]
  rw [applyB_getD (RC.KK j) (relBlk j g' i) (RC.yvec j z) (relBlk_length j g' i) hk]
  rw [appV_congr (RC.KK j) _ _ (RC.yvec j z) (fun g hg => relBlk_getD j g' i g hi hg),
    appV_sub, appV_add,
    appV_single (RC.KK j) g' hg' Data.M3.one (RC.yvec j z), mvf_one_mat,
    blocks_yvec' j z g' hg', appV_mul]
  simp only [RC.gMt, blkG]

/-! ## 3. The relation rows annihilate `yvec` -/

theorem ldot_relRow (j : Fin 73) {z : ℕ → Fin 3 → ℤ} (g' i r : ℕ) (hr : r < 3) :
    Data.ldot (relRow j g' i r) (RC.yvec j z)
      = (Data.applyB (relBlk j g' i) (RC.yvec j z)).toFun ⟨r, hr⟩ := by
  rw [relRow_eq_unblocks]
  rw [show RC.yvec j z
      = Data.unblocks ((List.range (RC.KK j)).map (fun g => CZ.ofFun (z (RC.geni j g))))
      from rfl]
  exact ldot_applyB _ _ ⟨r, hr⟩

theorem relRow_ann (j : Fin 73) {z : ℕ → Fin 3 → ℤ}
    (hrec : ∀ g, g < RC.KK j → ∀ i, i < RC.N j →
      Data.V3.dvd ((RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z (RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (z (RC.geni j g)))
          (Data.M3.mulV (RC.gMt j g) (CZ.ofFun (z i))))) = true)
    (hhz : ∀ i, i < (RC.Ad j).n → congV ((RC.Ad j).n) (CZ.ofFun (z i))
      (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)))
    (g' : ℕ) (hg' : g' < RC.KK j) (i : ℕ) (hi : i < (RC.Ad j).n) (r : ℕ) (hr : r < 3) :
    Data.ldot (relRow j g' i r) (RC.yvec j z) % ((RC.Ad j).n : ℤ) = 0 := by
  have hmlt := RC.mulg_lt j g' hg' i hi
  rw [ldot_relRow j g' i r hr]
  rw [applyB_relBlk j z g' hg' i hi]
  rw [← Int.dvd_iff_emod_eq_zero]
  have hA : congV ((RC.Ad j).n)
      (Data.V3.add (CZ.ofFun (z (RC.geni j g')))
        (Data.M3.mulV (RC.gMt j g') (CZ.ofFun (z i))))
      (Data.V3.add (CZ.ofFun (z (RC.geni j g')))
        (Data.M3.mulV (RC.gMt j g') (Data.applyB (blkRhs j g' i) (RC.yvec j z)))) :=
    congV_add (congV_refl _ _) (congV_mulV _ (hhz i hi))
  have hB : congV ((RC.Ad j).n) (CZ.ofFun (z (RC.mulg j g' i)))
      (Data.V3.add (CZ.ofFun (z (RC.geni j g')))
        (Data.M3.mulV (RC.gMt j g') (CZ.ofFun (z i)))) := hrec g' hg' i hi
  have hY : congV ((RC.Ad j).n) (Data.applyB (blkLhs j g' i) (RC.yvec j z))
      (Data.V3.add (CZ.ofFun (z (RC.geni j g')))
        (Data.M3.mulV (RC.gMt j g') (Data.applyB (blkRhs j g' i) (RC.yvec j z)))) :=
    congV_trans (congV_symm (hhz (RC.mulg j g' i) hmlt)) (congV_trans hB hA)
  exact (RC.dvd_iff_toFun _ _).mp hY ⟨r, hr⟩

theorem relRows_ann (j : Fin 73) {z : ℕ → Fin 3 → ℤ}
    (hrec : ∀ g, g < RC.KK j → ∀ i, i < RC.N j →
      Data.V3.dvd ((RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z (RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (z (RC.geni j g)))
          (Data.M3.mulV (RC.gMt j g) (CZ.ofFun (z i))))) = true)
    (hhz : ∀ i, i < (RC.Ad j).n → congV ((RC.Ad j).n) (CZ.ofFun (z i))
      (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z))) :
    ∀ row ∈ Data.relRows (RC.Ad j), Data.ldot row (RC.yvec j z) % ((RC.Ad j).n : ℤ) = 0 := by
  rw [relRows_eq]
  intro row hrow
  rw [List.mem_flatMap] at hrow
  rcases hrow with ⟨g', hg'mem, hrow⟩
  rw [List.mem_range] at hg'mem
  rw [List.mem_flatMap] at hrow
  rcases hrow with ⟨i, himem, hrow⟩
  rw [List.mem_range] at himem
  rw [List.mem_map] at hrow
  rcases hrow with ⟨r, hr, hrrow⟩
  rw [← hrrow]
  rw [List.mem_cons, List.mem_cons, List.mem_singleton] at hr
  rcases hr with h0 | h1 | h2
  · rw [h0]; exact relRow_ann j hrec hhz g' hg'mem i himem 0 (by norm_num)
  · rw [h1]; exact relRow_ann j hrec hhz g' hg'mem i himem 1 (by norm_num)
  · rw [h2]; exact relRow_ann j hrec hhz g' hg'mem i himem 2 (by norm_num)

/-! ## 4. The strong induction along the BFS order -/

theorem ad_applyB_cong (j : Fin 73) {z : ℕ → Fin 3 → ℤ}
    (hz0 : Data.V3.dvd ((RC.Ad j).n) (CZ.ofFun (z 0)) = true)
    (hrec : ∀ g, g < RC.KK j → ∀ i, i < RC.N j →
      Data.V3.dvd ((RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z (RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (z (RC.geni j g)))
          (Data.M3.mulV (RC.gMt j g) (CZ.ofFun (z i))))) = true) :
    ∀ i, i < (RC.Ad j).n → congV ((RC.Ad j).n) (CZ.ofFun (z i))
      (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z)) := by
  intro i
  refine Nat.strong_induction_on (p := fun i => i < (RC.Ad j).n → congV ((RC.Ad j).n)
    (CZ.ofFun (z i)) (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) (RC.yvec j z))) i ?_
  intro i ih hi
  rcases i with _ | i'
  · rw [ad_bmats_getD_zero j]
    rw [show RC.yvec j z
        = Data.unblocks ((List.range (RC.KK j)).map (fun g => CZ.ofFun (z (RC.geni j g))))
        from rfl]
    rw [applyB_replicate_zero]
    exact congV_zero hz0
  · have hi' : i' < (RC.Ad j).par.length := by
      have h1 : i' + 1 < (RC.Ad j).n := hi
      have h2 := RC.par_len_eq j
      omega
    have hp2le := RC.par2_le j i' hi'
    have hp2n : RC.par2 j i' < (RC.Ad j).n := by omega
    have hg : RC.par1 j i' < RC.KK j := RC.par1_lt j i' hi'
    have hsub : RC.mulg j (RC.par1 j i') (RC.par2 j i') = i' + 1 := ad_mulg_par j i' hi'
    have hhrec := hrec (RC.par1 j i') hg (RC.par2 j i') hp2n
    rw [hsub] at hhrec
    have hih := ih (RC.par2 j i') (by omega) hp2n
    rw [applyB_step j z i' hi']
    exact congV_trans hhrec (congV_add (congV_refl _ _) (congV_mulV _ hih))

/-! ## 5. The target statement -/

theorem RepCoh_applyB (j : Fin 73) {z : ℕ → Fin 3 → ℤ}
    (hz0 : Data.V3.dvd ((Work.SG.RC.Ad j).n) (CZ.ofFun (z 0)) = true)
    (hrec : ∀ g, g < Work.SG.RC.KK j → ∀ i, i < Work.SG.RC.N j →
      Data.V3.dvd ((Work.SG.RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z (Work.SG.RC.mulg j g i)))
        (Data.V3.add (CZ.ofFun (z (Work.SG.RC.geni j g))) (Data.M3.mulV (Work.SG.RC.gMt j g) (CZ.ofFun (z i)))))
        = true) :
    (∀ i, i < Work.SG.RC.N j → Data.V3.dvd ((Work.SG.RC.Ad j).n) (Data.V3.sub (CZ.ofFun (z i))
        (Data.applyB ((Data.bmats (Work.SG.RC.Ad j)).getD i []) (Work.SG.RC.yvec j z))) = true) ∧
    (∀ row ∈ Data.relRows (Work.SG.RC.Ad j), Data.ldot row (Work.SG.RC.yvec j z) % ((Work.SG.RC.Ad j).n : ℤ) = 0) :=
  ⟨ad_applyB_cong j hz0 hrec, relRows_ann j hrec (ad_applyB_cong j hz0 hrec)⟩

end Work.SG
