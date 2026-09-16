import Submission.CertJAccum
import Submission.Commons.Algebra.Sum.sum_fiber_range_list
import Submission.Commons.Data.List.map_range_getD
import Submission.CertJBridge1
import Submission.CertJPsiTspec
import Submission.CertJEval
import Submission.CertSsum49All
import Submission.CertRowL
import Submission.CertJTabsSpecP0
import Submission.CertJTabsSpecP1
import Submission.CertJTabsSpecP2
import Submission.CertJTabsSpecP3
import Submission.CertJTabsSpecP4
import Submission.CertJTabsSpecP5
import Submission.CertJTabsSpecP6
import Submission.CertJTabsSpecP7

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `J`-form: the signature grouping and the table identification

`Submission/CertJBridge1.certJSum_flat` writes the cleared `J`-form as a double sum over the
flat list `cJTrips` of `(β, ã, W)` entries.  Here we

* partition that double sum by the position `sigPosOf β` of the signature in
  `certGroupSigs`,
* identify, for a pair of positions `(i,j)`, the sum over the two fibers with the
  four-block sign expansion of the *accumulated* group weights `gPosL`/`gNegL`,
* and replace the two remaining factors `Ssum β β' 49` and `certJPsiND N L` by the verified
  table lookups `ssumTable49L` and `psiTabTN`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## `getD` on a zip -/

theorem getD_zip_fst {α β : Type*} (l : List α) (m : List β) (d : α × β) (i : ℕ)
    (hi : i < l.length) (hi' : i < m.length) : ((l.zip m).getD i d).1 = l.getD i d.1 := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zip]; omega)]
  rw [List.getElem_zip, List.getD_eq_getElem l d.1 hi]

theorem getD_zip_snd {α β : Type*} (l : List α) (m : List β) (d : α × β) (i : ℕ)
    (hi : i < l.length) (hi' : i < m.length) : ((l.zip m).getD i d).2 = m.getD i d.2 := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zip]; omega)]
  rw [List.getElem_zip, List.getD_eq_getElem m d.2 hi']

theorem getD_zip_eq {α β : Type*} (l : List α) (m : List β) (d : α × β) (i : ℕ)
    (h1 : i < l.length) (h2 : i < m.length) :
    (l.zip m).getD i d = (l.getD i d.1, m.getD i d.2) :=
  Prod.ext (getD_zip_fst l m d i h1 h2) (getD_zip_snd l m d i h1 h2)

/-! ## The signature fibers of the flat `J`-data -/

/-- The fiber of `cJTrips` over a signature position, with the `(ã, W)` data. -/
theorem wTab_fiber (i : ℕ) :
    (wTab.filter (fun t => decide (t.1 = i))).map (fun t => (t.2.1, t.2.2))
      = (cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => (w.2.1, w.2.2)) := by
  rw [wTab, List.filter_map, List.map_map]
  rfl

/-- The accumulated group tables are the accumulated fibers. -/
theorem accPos_fiber (i : ℕ) :
    accPosOf ((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map
        (fun w => (w.2.1, w.2.2))) = accPos wTab i := by
  rw [← wTab_fiber, accPos_eq_accPosOf]

theorem accNeg_fiber (i : ℕ) :
    accNegOf ((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map
        (fun w => (w.2.1, w.2.2))) = accNeg wTab i := by
  rw [← wTab_fiber, accNeg_eq_accNegOf]

/-! ## The table identifications -/

theorem cJTrips_exp_le : cJTrips.all (fun w => decide (w.2.1 ≤ 26)) = true := by decide

theorem cJTrips_sum_le : cJTrips.all (fun w => decide (w.1.sum ≤ 24)) = true := by decide

theorem cJTrips_exp_le' {w : List ℕ × ℕ × ℤ} (hw : w ∈ cJTrips) : w.2.1 ≤ 26 :=
  of_decide_eq_true (List.all_eq_true.mp cJTrips_exp_le w hw)

theorem cJTrips_sum_le' {w : List ℕ × ℕ × ℤ} (hw : w ∈ cJTrips) : w.1.sum ≤ 24 :=
  of_decide_eq_true (List.all_eq_true.mp cJTrips_sum_le w hw)

theorem cSigs_getD_fst (i : ℕ) (hi : i < 272) : (cSigs.getD i cNil).1 = certGroupSigs.getD i [] := by
  rw [cSigs]
  exact getD_zip_fst certGroupSigs certGroupCoefs cNil i (by rw [certGroupSigs_length]; exact hi)
    (by rw [certGroupCoefs_length]; exact hi)

/-- The `mc 49 (mult β)` factor is the `mcL` table entry. -/
theorem mcL_getD (j : ℕ) (hj : j < 272) :
    mcL.getD j 0 = mc 49 (mult (certGroupSigs.getD j [])) := by
  rw [mcL_spec]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, certGroupSigs_length]; exact hj)]
  rw [List.getElem_map]
  rw [← List.getD_eq_getElem certGroupSigs [] (by rw [certGroupSigs_length]; exact hj)]

/-- The `(i,j)` entry of the `k = 49` table is the unpacked packed row. -/
theorem ssumRowOfAt_getD (p' : List ℕ × List ℤ) (i : ℕ) (hi : i < 272) :
    (ssumRowOfAt 49 p').getD i 0
      = unpack (packedRowAt 49 (mult p'.1)) (mult (cSigs.getD i cNil).1) := by
  unfold ssumRowOfAt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, cSigs_length49]; exact hi)]
  rw [List.getElem_map]
  rw [← List.getD_eq_getElem cSigs cNil (by rw [cSigs_length49]; exact hi)]

theorem ssumTable49L_getD_getD (i j : ℕ) (hi : i < 272) (hj : j < 272) :
    (ssumTable49L.getD j []).getD i 0
      = unpack (packedRowAt 49 (mult (cSigs.getD j cNil).1)) (mult (cSigs.getD i cNil).1) := by
  rw [ssumTable49L_row j hj, ssumRowOfAt_getD _ i hi]

/-- **`Ssum β β' 49` as the `(i,j)` table entry times `mcL`.** -/
theorem Ssum_eq_table (i j : ℕ) (hi : i < 272) (hj : j < 272)
    (w w' : List ℕ × ℕ × ℤ) (hw : w ∈ cJTrips) (hw' : w' ∈ cJTrips)
    (hwi : sigPosOf w.1 = i) (hwj : sigPosOf w'.1 = j) :
    Ssum w.1 w'.1 49 = mcL.getD j 0 * (ssumTable49L.getD j []).getD i 0 := by
  have hmem := cJTrips_sig_mem' hw
  have hmem' := cJTrips_sig_mem' hw'
  have h1 := Ssum_eq_packedRowAt w.1 w'.1 49 (by norm_num) (certGroupSigs_support hmem)
    (certGroupSigs_support hmem') (certGroupSigs_sum_le hmem) (certGroupSigs_sum_le hmem')
  rw [h1]
  have hmc : mc 49 (mult w'.1) = mcL.getD j 0 := by
    rw [mcL_getD j hj, ← hwj, sigPosOf_getD hw']
  have hrow : unpack (packedRowAt 49 (mult w'.1)) (mult w.1) = (ssumTable49L.getD j []).getD i 0 := by
    rw [ssumTable49L_getD_getD i j hi hj, cSigs_getD_fst j hj, cSigs_getD_fst i hi,
      ← hwj, ← hwi, sigPosOf_getD hw', sigPosOf_getD hw]
  rw [hmc, hrow]

/-- **The `Ψ`-kernel as a `psiTabTN` lookup.** -/
theorem certJPsiND_eq_table (w w' : List ℕ × ℕ × ℤ) (hw : w ∈ cJTrips) (hw' : w' ∈ cJTrips) :
    certJPsiND (w.2.1 + w'.2.1) (w.1.sum + w'.1.sum)
      = nthD (nthDl psiTabTN (w'.1.sum + w.1.sum) []) (w.2.1 + w'.2.1) 0 := by
  rw [certJPsiND_eq_nthDl _ _ (by have := cJTrips_exp_le' hw; have := cJTrips_exp_le' hw'; omega)
    (by have := cJTrips_sum_le' hw; have := cJTrips_sum_le' hw'; omega)]
  rw [Nat.add_comm]

/-! ## The group tables are the accumulated fibers -/

/-- **The `gPosL`/`gNegL` tables are the accumulated `ã`-weights of the fibers.** -/
theorem gTab_spec (i : ℕ) (hi : i < 272) :
    gPosL.getD i [] = accPos wTab i ∧ gNegL.getD i [] = accNeg wTab i := by
  obtain ⟨c, m, hc, hm, hikm⟩ : ∃ c m, c < 8 ∧ m < 34 ∧ i = 34 * c + m :=
    ⟨i / 34, i % 34, by omega, by omega, by omega⟩
  subst hikm
  interval_cases c
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_0 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_1 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_2 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_3 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_4 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_5 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_6 m (List.mem_range.mpr hm))
  · exact of_decide_eq_true (List.all_eq_true.mp gTab_spec_7 m (List.mem_range.mpr hm))

theorem gPosL_getD (i : ℕ) (hi : i < 272) : gPosL.getD i [] = accPos wTab i := (gTab_spec i hi).1

theorem gNegL_getD (i : ℕ) (hi : i < 272) : gNegL.getD i [] = accNeg wTab i := (gTab_spec i hi).2

/-! ## The `ℕ`/`ℤ` bridge for the block contractions -/

/-- Casting a `List ℕ` sum. -/
theorem cast_listSum (l : List ℕ) : ((l.sum : ℕ) : ℤ) = (l.map (fun n => (n : ℤ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.sum_cons, ih]

/-- Casting the sum of a mapped list. -/
theorem cast_listSum_map {α : Type*} (l : List α) (f : α → ℕ) :
    (((l.map f).sum : ℕ) : ℤ) = (l.map (fun a => (f a : ℤ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- **The `ℕ`-valued block sum `jb` is the `ℤ`-valued four-block contraction `BLK`.** -/
theorem cast_jb (row : List ℕ) (g h : List (ℕ × ℕ)) :
    ((jb row g h : ℕ) : ℤ) = BLK g h (fun m n => (nthD row (m + n) 0 : ℤ)) := by
  unfold jb BLK jt
  rw [cast_listSum_map g (fun a => (List.map (fun b => a.2 * b.2 * nthD row (a.1 + b.1) 0) h).sum)]
  refine congrArg List.sum (List.map_congr_left (fun a _ => ?_))
  rw [cast_listSum_map h (fun b => a.2 * b.2 * nthD row (a.1 + b.1) 0)]
  refine congrArg List.sum (List.map_congr_left (fun b _ => ?_))
  push_cast
  ring

/-! ## The pointwise summand of a pair of signature fibers -/

/-- **One `J`-summand of a signature-pair fiber, in table form.** -/
theorem Gt_eq_K_p (i j : ℕ) (hi : i < 272) (hj : j < 272)
    (w w' : List ℕ × ℕ × ℤ) (hw : w ∈ cJTrips) (hw' : w' ∈ cJTrips)
    (hwi : sigPosOf w.1 = i) (hwj : sigPosOf w'.1 = j) :
    Gt w w' = w.2.2 * w'.2.2
      * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ))
      * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) [])
          (w.2.1 + w'.2.1) 0 : ℤ) := by
  rw [Gt, Ssum_eq_table i j hi hj w w' hw hw' hwi hwj, certJPsiND_eq_table w w' hw hw']
  have hsum : w'.1.sum + w.1.sum = (certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum := by
    rw [← hwj, ← hwi, sigPosOf_getD hw', sigPosOf_getD hw]
  rw [hsum]
  push_cast
  ring

/-- The double fiber sum with the constant factor `mcL·row` removed. -/
theorem fiber_sum_BLKZ (i j : ℕ) (K : ℕ → ℕ → ℤ) :
    (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w =>
        ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map
          (fun w' => w.2.2 * w'.2.2 * K w.2.1 w'.2.1)).sum)).sum)
      = BLKZ ((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map
            (fun w => (w.2.1, w.2.2)))
          ((cJTrips.filter (fun w => decide (sigPosOf w.1 = j))).map
            (fun w => (w.2.1, w.2.2))) K := by
  unfold BLKZ
  simp only [List.map_map]
  rfl





/-- **The double fiber sum of a signature pair, as the four-block table contraction.** -/
theorem pair_fiber_eq_jp (i j : ℕ) (hi : i < 272) (hj : j < 272) :
    (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => Gt w w')).sum)).sum)
      = jp (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) ((ssumTable49L.getD j []).getD i 0) (mcL.getD j 0)
          (gPosL.getD i []) (gNegL.getD i []) (gPosL.getD j []) (gNegL.getD j []) := by
  have h1 : (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => Gt w w')).sum)).sum)
      = (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => w.2.2 * w'.2.2 * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)) * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ))).sum)).sum) := by
    refine congrArg List.sum (List.map_congr_left (fun w hw =>
      congrArg List.sum (List.map_congr_left (fun w' hw' => ?_))))
    rw [Gt_eq_K_p i j hi hj w w' (List.mem_filter.mp hw).1 (List.mem_filter.mp hw').1
      (of_decide_eq_true (List.mem_filter.mp hw).2) (of_decide_eq_true (List.mem_filter.mp hw').2)]
  have h2 : (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => w.2.2 * w'.2.2 * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)) * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ))).sum)).sum)
      = ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)) * (((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => w.2.2 * w'.2.2 * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ))).sum)).sum) := by
    have hinner : ∀ w : List ℕ × ℕ × ℤ, ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => w.2.2 * w'.2.2 * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)) * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ))).sum = ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => w.2.2 * w'.2.2 * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ))).sum * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)) := by
      intro w
      trans ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => (w.2.2 * w'.2.2 * (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (w.2.1 + w'.2.1) 0 : ℤ)) * ((mcL.getD j 0 : ℤ) * ((ssumTable49L.getD j []).getD i 0 : ℤ)))).sum
      · exact congrArg List.sum (List.map_congr_left (fun w' _ => by ring))
      · rw [List.sum_map_mul_right]
    rw [List.map_congr_left (fun w _ => hinner w), List.sum_map_mul_right, mul_comm]
  rw [h1, h2, fiber_sum_BLKZ i j (fun m n => (nthD (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) (m + n) 0 : ℤ)), sum_pair_blocks,
    accPos_fiber i, accNeg_fiber i, accPos_fiber j, accNeg_fiber j,
    ← gPosL_getD i hi, ← gNegL_getD i hi, ← gPosL_getD j hj, ← gNegL_getD j hj,
    ← cast_jb (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []), ← cast_jb (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []), ← cast_jb (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []), ← cast_jb (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) [])]
  rw [jp]
  push_cast
  ring

/-! ## The nested four-fold zip as a range -/

theorem zip4_eq_range {α β γ δ : Type*} (n : ℕ) (l1 : List α) (l2 : List β) (l3 : List γ)
    (l4 : List δ) (d1 : α) (d2 : β) (d3 : γ) (d4 : δ)
    (h1 : l1.length = n) (h2 : l2.length = n) (h3 : l3.length = n) (h4 : l4.length = n) :
    l1.zip (l2.zip (l3.zip l4))
      = (List.range n).map (fun i => (l1.getD i d1, l2.getD i d2, l3.getD i d3, l4.getD i d4)) := by
  apply List.ext_getElem
  · rw [List.length_zip, List.length_zip, List.length_zip, List.length_map,
      List.length_range, h1, h2, h3, h4]
    omega
  · intro i hL hR
    have hi : i < n := by simpa [List.length_range] using hR
    rw [List.getElem_zip, List.getElem_zip, List.getElem_zip]
    rw [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem sum_zip4 {α β γ δ M : Type*} [AddCommMonoid M] (n : ℕ) (l1 : List α) (l2 : List β)
    (l3 : List γ) (l4 : List δ) (d1 : α) (d2 : β) (d3 : γ) (d4 : δ)
    (h1 : l1.length = n) (h2 : l2.length = n) (h3 : l3.length = n) (h4 : l4.length = n)
    (F : α → β → γ → δ → M) :
    ((l1.zip (l2.zip (l3.zip l4))).map (fun q => F q.1 q.2.1 q.2.2.1 q.2.2.2)).sum
      = ((List.range n).map (fun i =>
          F (l1.getD i d1) (l2.getD i d2) (l3.getD i d3) (l4.getD i d4))).sum := by
  rw [zip4_eq_range n l1 l2 l3 l4 d1 d2 d3 d4 h1 h2 h3 h4, List.map_map]
  rfl

/-! ## The flat `J`-sum partitioned by signature positions -/

/-- **The double fiber partition.** -/
theorem sum_fiber_range_list2 {α β M : Type*} [AddCommMonoid M] (l : List α) (m : List β)
    (g : α → ℕ) (g' : β → ℕ) (n : ℕ) (F : α → β → M)
    (h : ∀ x ∈ l, g x < n) (h' : ∀ y ∈ m, g' y < n) :
    ((l.map (fun x => (m.map (fun y => F x y)).sum)).sum)
      = ((List.range n).map (fun i => ((List.range n).map (fun j =>
          ((l.filter (fun x => decide (g x = i))).map (fun x =>
            ((m.filter (fun y => decide (g' y = j))).map (fun y => F x y)).sum)).sum)).sum)).sum := by
  rw [Commons.Algebra.Sum.sum_fiber_range_list l g n (fun x => (m.map (fun y => F x y)).sum) h]
  refine congrArg List.sum (List.map_congr_left (fun i _ => ?_))
  rw [show ((l.filter (fun x => decide (g x = i))).map (fun x => (m.map (fun y => F x y)).sum))
      = ((l.filter (fun x => decide (g x = i))).map (fun x => ((List.range n).map (fun j =>
          ((m.filter (fun y => decide (g' y = j))).map (fun y => F x y)).sum)).sum)) from
    List.map_congr_left (fun x _ =>
      Commons.Algebra.Sum.sum_fiber_range_list m g' n (fun y => F x y) h')]
  rw [list_sum_comm (l.filter (fun x => decide (g x = i))) (List.range n)
    (fun x j => ((m.filter (fun y => decide (g' y = j))).map (fun y => F x y)).sum)]

/-- **The `J`-form as a double sum over signature positions.** -/
theorem certJSum_range :
    certJSum = ((List.range 272).map (fun j => ((List.range 272).map (fun i =>
        jp (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) ((ssumTable49L.getD j []).getD i 0) (mcL.getD j 0) (gPosL.getD i []) (gNegL.getD i []) (gPosL.getD j []) (gNegL.getD j []))).sum)).sum := by
  rw [certJSum_flat,
    sum_fiber_range_list2 cJTrips cJTrips (fun w => sigPosOf w.1) (fun w' => sigPosOf w'.1) 272
      (fun w w' => Gt w w') (fun w hw => cJTrips_pos_lt' hw) (fun w' hw' => cJTrips_pos_lt' hw')]
  rw [list_sum_comm (List.range 272) (List.range 272) (fun i j => ((cJTrips.filter (fun w => decide (sigPosOf w.1 = i))).map (fun w => ((cJTrips.filter (fun w' => decide (sigPosOf w'.1 = j))).map (fun w' => Gt w w')).sum)).sum)]
  refine congrArg List.sum (List.map_congr_left (fun j hj => ?_))
  refine congrArg List.sum (List.map_congr_left (fun i hi => ?_))
  exact pair_fiber_eq_jp i j (List.mem_range.mp hi) (List.mem_range.mp hj)

/-! ## The table evaluation as a range sum -/

theorem mcL_length : mcL.length = 272 := by decide

theorem ssumTable49L_rowlen : ssumTable49L.all (fun r => decide (r.length = 272)) = true := by decide

theorem ssumTable49L_getD_length (j : ℕ) (hj : j < 272) :
    (ssumTable49L.getD j []).length = 272 := by
  rw [List.getD_eq_getElem _ _ (by rw [ssumTable49L_length]; exact hj)]
  exact of_decide_eq_true (List.all_eq_true.mp ssumTable49L_rowlen _
    (List.get_mem _ _))

theorem gPosL_length' : gPosL.length = 272 := by decide

theorem gNegL_length' : gNegL.length = 272 := by decide

/-- The default outer entry of the `J`-evaluation. -/
def outerJDef : List ℕ × (List ℕ × (List (ℕ × ℕ) × (List (ℕ × ℕ) × ℕ))) :=
  ([], ([], ([], ([], 0))))

theorem outerJ_length : outerJ.length = 272 := by
  rw [outerJ, List.length_zip, List.length_zip, List.length_zip, List.length_zip,
    certGroupSigs_length, ssumTable49L_length, gPosL_length', gNegL_length', mcL_length]
  omega

/-- **One outer entry of the table evaluation, as a range sum.** -/
theorem innerJ_eq_range (β : List ℕ) (row : List ℕ) (P N : List (ℕ × ℕ)) (mc : ℕ)
    (hrow : row.length = 272) :
    innerJ (β, (row, (P, (N, mc))))
      = ((List.range 272).map (fun i =>
          jp (nthDl psiTabTN (β.sum + (certGroupSigs.getD i []).sum) [])
            (row.getD i 0) mc (gPosL.getD i []) (gNegL.getD i []) P N)).sum := by
  unfold innerJ
  simp only [List.map_cons, List.sum_cons, List.sum_nil, List.map_nil, add_zero]
  rw [sum_zip4 272 certGroupSigs row gPosL gNegL [] 0 [] []
    certGroupSigs_length hrow gPosL_length' gNegL_length'
    (fun β' row' P' N' => jp (nthDl psiTabTN (β.sum + β'.sum) []) row' mc P' N' P N)]

/-- The outer entry of `outerJ` at a position, componentwise. -/
theorem outerJ_getD (j : ℕ) (hj : j < 272) :
    outerJ.getD j outerJDef
      = (certGroupSigs.getD j [], (ssumTable49L.getD j [], (gPosL.getD j [],
          (gNegL.getD j [], mcL.getD j 0)))) := by
  have hz1 : (ssumTable49L.zip (gPosL.zip (gNegL.zip mcL))).length = 272 := by
    rw [List.length_zip, List.length_zip, List.length_zip, ssumTable49L_length,
      gPosL_length', gNegL_length', mcL_length]
    omega
  have hz2 : (gPosL.zip (gNegL.zip mcL)).length = 272 := by
    rw [List.length_zip, List.length_zip, gPosL_length', gNegL_length', mcL_length]
    omega
  have hz3 : (gNegL.zip mcL).length = 272 := by
    rw [List.length_zip, gNegL_length', mcL_length]; omega
  rw [outerJ,
    getD_zip_eq certGroupSigs (ssumTable49L.zip (gPosL.zip (gNegL.zip mcL))) outerJDef j
      (by rw [certGroupSigs_length]; exact hj) (by rw [hz1]; exact hj),
    getD_zip_eq ssumTable49L (gPosL.zip (gNegL.zip mcL)) outerJDef.2 j
      (by rw [ssumTable49L_length]; exact hj) (by rw [hz2]; exact hj),
    getD_zip_eq gPosL (gNegL.zip mcL) outerJDef.2.2 j
      (by rw [gPosL_length']; exact hj) (by rw [hz3]; exact hj),
    getD_zip_eq gNegL mcL outerJDef.2.2.2 j
      (by rw [gNegL_length']; exact hj) (by rw [mcL_length]; exact hj)]
  rfl

/-- **One outer entry of `certJval`, as a range sum.** -/
theorem innerJ_getD (j : ℕ) (hj : j < 272) :
    innerJ (outerJ.getD j outerJDef) = ((List.range 272).map (fun i =>
      jp (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) ((ssumTable49L.getD j []).getD i 0) (mcL.getD j 0) (gPosL.getD i []) (gNegL.getD i []) (gPosL.getD j []) (gNegL.getD j []))).sum := by
  rw [outerJ_getD j hj,
    innerJ_eq_range (certGroupSigs.getD j []) (ssumTable49L.getD j []) (gPosL.getD j [])
      (gNegL.getD j []) (mcL.getD j 0) (ssumTable49L_getD_length j hj)]

/-- **The table evaluation `certJval` as a range sum.** -/
theorem certJval_range :
    certJval = ((List.range 272).map (fun j => ((List.range 272).map (fun i =>
      jp (nthDl psiTabTN ((certGroupSigs.getD j []).sum + (certGroupSigs.getD i []).sum) []) ((ssumTable49L.getD j []).getD i 0) (mcL.getD j 0) (gPosL.getD i []) (gNegL.getD i []) (gPosL.getD j []) (gNegL.getD j []))).sum)).sum := by
  rw [certJval, ← Commons.Data.List.map_range_getD outerJ outerJDef innerJ, outerJ_length]
  refine congrArg List.sum (List.map_congr_left (fun j hj => ?_))
  exact innerJ_getD j (List.mem_range.mp hj)

/-- **The `J`-form of the certificate is its table evaluation.** -/
theorem certJSum_eq_certJval : certJSum = certJval := by
  rw [certJSum_range, certJval_range]

/-! ## Splitting the `J`-evaluation into chunks -/

theorem sum_map_take_drop' {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → β) (n : ℕ) :
    (l.map g).sum = ((l.take n).map g).sum + ((l.drop n).map g).sum := by
  conv_lhs => rw [← List.take_append_drop (i := n) (l := l)]
  rw [List.map_append, List.sum_append]

theorem sum_map_singletons {α β : Type*} [AddCommMonoid β] (g : α → β) :
    ∀ (l : List α) (N : ℕ), l.length ≤ N →
      (l.map g).sum = ∑ c ∈ Finset.range N, (((l.drop c).take 1).map g).sum := by
  intro l N
  induction N generalizing l with
  | zero =>
      intro h
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hl]
  | succ N ih =>
      intro h
      rw [Finset.sum_range_succ', sum_map_take_drop' l g 1]
      have hlen : (l.drop 1).length ≤ N := by rw [List.length_drop]; omega
      rw [ih (l.drop 1) hlen]
      have hA : ((l.take 1).map g).sum = (((l.drop 0).take 1).map g).sum := by simp
      have hS : (∑ c ∈ Finset.range N, ((((l.drop 1).drop c).take 1).map g).sum)
          = (∑ c ∈ Finset.range N, (((l.drop (c + 1)).take 1).map g).sum) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [List.drop_drop, show 1 + c = c + 1 from by omega]
      rw [hA, hS, add_comm]

/-- **`certJval` as the sum of its `272` one-group chunks.** -/
theorem certJval_chunk :
    certJval = ∑ c ∈ Finset.range 272,
      List.sum (List.map innerJ (List.take 1 (List.drop c outerJ))) := by
  rw [certJval]
  exact sum_map_singletons innerJ outerJ 272 (by rw [outerJ_length])

end Commons.NumberTheory.MaynardSieve
