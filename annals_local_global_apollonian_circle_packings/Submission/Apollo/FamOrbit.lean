/-
Interface facts for the orbit of the family quadruple famQuad t = (−(24t+19),
24t+21, 8(6t+5)², 8(6t+5)²+4) under the Apollonian group: every orbit member
is Descartes with positive sum, primitive, has the (6,5) residue structure
(indices 0,1 odd ≡ 5 mod 8; 2,3 even ≡ 0 mod 4), and has no zero coordinate.

These are the exact facts that the χ₂ constancy machinery (WD, Sarnak, copath,
crack) needs; the family orbit satisfies them exactly as the orbit of
(−3,5,8,8) does.
-/
import Submission.Apollo.PackDistinct
import Submission.Apollo.PackFamily
import Submission.Apollo.Parity
import Submission.Apollo.Structure
import Submission.Apollo.Descartes
import Submission.Apollo.OrbitFacts
import Submission.Apollo.SarnakParam
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-! ## parity of the base quadruple -/

/-- indices 0,1 of the family base are odd; 2,3 even. -/
lemma famQuad_parity (t : ℕ) :
    ¬ 2 ∣ famQuad t 0 ∧ ¬ 2 ∣ famQuad t 1 ∧ 2 ∣ famQuad t 2 ∧ 2 ∣ famQuad t 3 := by
  constructor
  · change ¬ 2 ∣ famA t
    unfold famA
    intro h
    rcases h with ⟨k, hk⟩
    omega
  · constructor
    · change ¬ 2 ∣ famB t
      unfold famB
      intro h
      rcases h with ⟨k, hk⟩
      omega
    · constructor
      · change 2 ∣ famC t
        refine ⟨4 * (6 * (t : ℤ) + 5) ^ 2, ?_⟩
        unfold famC
        ring
      · change 2 ∣ famD t
        refine ⟨4 * (6 * (t : ℤ) + 5) ^ 2 + 2, ?_⟩
        unfold famD famC
        ring

/-- indices 0,1 stay odd and 2,3 stay even through the whole orbit. -/
theorem famOrbit_parity (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) :
    ¬ 2 ∣ v 0 ∧ ¬ 2 ∣ v 1 ∧ 2 ∣ v 2 ∧ 2 ∣ v 3 := by
  refine of_orbitOf_apply (w0 := famQuad t)
    (P := fun w => ¬ 2 ∣ w 0 ∧ ¬ 2 ∣ w 1 ∧ 2 ∣ w 2 ∧ 2 ∣ w 3) ?hP ?hS v hv
  · exact famQuad_parity t
  · intro i w hw
    exact ⟨odd_preserved w i 0 hw.1, odd_preserved w i 1 hw.2.1,
      even_preserved w i 2 hw.2.2.1, even_preserved w i 3 hw.2.2.2⟩

/-- every member of the family orbit is Descartes. -/
theorem famOrbit_desc (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) :
    (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2 := by
  refine of_orbitOf_apply (w0 := famQuad t)
    (P := fun w => (∑ j : Fin 4, w j) ^ 2 = 2 * ∑ j : Fin 4, (w j) ^ 2) ?hP ?hS v hv
  · exact fam_descartes t
  · intro i w hw
    exact gen_smul_descarates i w hw

/-- every member of the family orbit has positive sum (and is Descartes). -/
theorem famOrbit_desc_posSum (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) :
    (∑ i : Fin 4, v i) ^ 2 = 2 * ∑ i : Fin 4, (v i) ^ 2 ∧ 0 < ∑ i : Fin 4, v i := by
  refine of_orbitOf_apply
    (w0 := famQuad t)
    (P := fun w => (∑ j : Fin 4, w j) ^ 2 = 2 * ∑ j : Fin 4, (w j) ^ 2 ∧ 0 < ∑ j : Fin 4, w j)
    ?hP ?hS v hv
  · constructor
    · exact fam_descartes t
    · exact fam_sum_pos t
  · intro i w hw
    constructor
    · exact gen_smul_descarates i w hw.1
    · exact pos_sum_of_pos_sum_move w i hw.1 hw.2

/-- the orbit is closed under every S-move. -/
lemma famOrbit_gen (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) (i : Fin 4) :
    gen i • v ∈ orbitOf (famQuad t) := by
  rcases hv with ⟨g, hg, rfl⟩
  change ∃ g' : GL (Fin 4) ℤ, g' ∈ ApollonianGroup ∧ gen i • (g • famQuad t) = g' • famQuad t
  refine ⟨gen i * g, ?_⟩
  constructor
  · rw [apollonianGroup_eq_closure]
    have hgi : gen i ∈ Subgroup.closure gens :=
      Subgroup.subset_closure (k := gens) ⟨i, rfl⟩
    exact Subgroup.mul_mem (Subgroup.closure gens) hgi (by simpa [apollonianGroup_eq_closure] using hg)
  · rw [mul_smul]

/-- every member of the family orbit is primitive. -/
theorem famOrbit_gcd_one (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) :
    Finset.univ.gcd v = 1 := by
  rcases hv with ⟨g, hg, rfl⟩
  exact gl_smul_gcd_one g (famQuad t) (fam_univ_gcd_one t)

/-- an odd-looking linear form is not divisible by 2. -/
lemma not_two_dvd_of_eq_five_add {x k : ℤ} (h : x = 5 + 24 * k) : ¬ 2 ∣ x := by
  intro h2
  rcases h2 with ⟨w, hw⟩
  rw [h] at hw
  omega

/-- an odd-looking linear form is not divisible by 2. -/
lemma not_two_dvd_of_eq_twentyone_add {x k : ℤ} (h : x = 21 + 24 * k) : ¬ 2 ∣ x := by
  intro h2
  rcases h2 with ⟨w, hw⟩
  rw [h] at hw
  omega

/-- generic: an odd coordinate of a Qpred residue vector is ≡ 5 mod 8. -/
lemma qpred_odd_mod8 (v : Fin 4 → ℤ) (hq : Qpred (toZ24 v)) (i : Fin 4)
    (hodd : ¬ 2 ∣ v i) : v i % 8 = 5 := by
  have hr : A24 ((v i : ZMod 24)) := hq.1 i
  rcases hr with h | h | h | h | h | h
  · exfalso
    have hz : (v i : ZMod 24) = (0 : ZMod 24) := h
    have hm : v i ≡ (0 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 0).1 hz
    rcases modEq24_eq hm with ⟨k, hk⟩
    have h2 : v i = 2 * (12 * k) := by rw [hk]; ring
    exact hodd ⟨12 * k, h2⟩
  · have hm : v i ≡ (5 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 5).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk8 : v i = 5 + 8 * (3 * k) := by rw [hk]; ring
    omega
  · exfalso
    have hm : v i ≡ (8 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 8).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have h2 : v i = 2 * (4 + 12 * k) := by rw [hk]; ring
    exact hodd ⟨4 + 12 * k, h2⟩
  · exfalso
    have hm : v i ≡ (12 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 12).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have h2 : v i = 2 * (6 + 12 * k) := by rw [hk]; ring
    exact hodd ⟨6 + 12 * k, h2⟩
  · exfalso
    have hm : v i ≡ (20 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 20).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have h2 : v i = 2 * (10 + 12 * k) := by rw [hk]; ring
    exact hodd ⟨10 + 12 * k, h2⟩
  · have hm : v i ≡ (21 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 21).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk8 : v i = 5 + 8 * (3 * k + 2) := by rw [hk]; ring
    omega

/-- generic: an even coordinate of a Qpred residue vector is ≡ 0 mod 4. -/
lemma qpred_even_mod4 (v : Fin 4 → ℤ) (hq : Qpred (toZ24 v)) (i : Fin 4)
    (heven : 2 ∣ v i) : v i % 4 = 0 := by
  have hr : A24 ((v i : ZMod 24)) := hq.1 i
  rcases hr with h | h | h | h | h | h
  · have hm : v i ≡ (0 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 0).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk4 : v i = 4 * (6 * k) := by rw [hk]; ring
    omega
  · exfalso
    have hm : v i ≡ (5 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 5).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    exact not_two_dvd_of_eq_five_add hk heven
  · have hm : v i ≡ (8 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 8).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk4 : v i = 4 * (6 * k + 2) := by rw [hk]; ring
    omega
  · have hm : v i ≡ (12 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 12).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk4 : v i = 4 * (6 * k + 3) := by rw [hk]; ring
    omega
  · have hm : v i ≡ (20 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 20).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    have hk4 : v i = 4 * (6 * k + 5) := by rw [hk]; ring
    omega
  · exfalso
    have hm : v i ≡ (21 : ℤ) [ZMOD (24 : ℤ)] := (zmod24_eq_iff_modEq (v i) 21).1 h
    rcases modEq24_eq hm with ⟨k, hk⟩
    exact not_two_dvd_of_eq_twentyone_add hk heven

/-- coordinates at indices 0,1 of a family-orbit quadruple are ≡ 5 mod 8. -/
theorem famOrbit_odd_coord_eq_five_mod8 (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t))
    (i : Fin 4) (hi : i = 0 ∨ i = 1) : v i % 8 = 5 := by
  rcases hi with rfl | rfl
  · have ho : ¬ 2 ∣ v 0 := (famOrbit_parity t v hv).1
    exact qpred_odd_mod8 v (fam_orbit_Qpred t v hv) 0 ho
  · have ho : ¬ 2 ∣ v 1 := (famOrbit_parity t v hv).2.1
    exact qpred_odd_mod8 v (fam_orbit_Qpred t v hv) 1 ho

/-- coordinates at indices 2,3 of a family-orbit quadruple are ≡ 0 mod 4. -/
theorem famOrbit_even_coord_eq_zero_mod4 (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t))
    (i : Fin 4) (hi : i = 2 ∨ i = 3) : v i % 4 = 0 := by
  rcases hi with rfl | rfl
  · have he : 2 ∣ v 2 := (famOrbit_parity t v hv).2.2.1
    exact qpred_even_mod4 v (fam_orbit_Qpred t v hv) 2 he
  · have he : 2 ∣ v 3 := (famOrbit_parity t v hv).2.2.2
    exact qpred_even_mod4 v (fam_orbit_Qpred t v hv) 3 he

/-- a coordinate of a family-orbit quadruple is odd iff its index is 0 or 1. -/
theorem famOrbit_coord_odd_iff (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (m : Fin 4) : (¬ 2 ∣ w m) ↔ m = 0 ∨ m = 1 := by
  fin_cases m <;> simp [famOrbit_parity t w hw]

/-- an odd-index coordinate of a family-orbit quadruple is nonzero (≡ 5 mod 8). -/
theorem famOrbit_odd_coord_ne_zero (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t))
    (i : Fin 4) (hi : i = 0 ∨ i = 1) : w i ≠ 0 := by
  intro hz
  have h8 : w i % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw i hi
  rw [hz] at h8
  norm_num at h8

/-- gcd-instance for a zero at index 2 (family). -/
lemma fam_gcd_one_of_divides2 (t : ℕ) {w : Fin 4 → ℤ} (hw : w ∈ orbitOf (famQuad t))
    (hzero : w 2 = 0) {r : ℕ} (hr0 : r ∣ (w 0).natAbs) (hr1 : r ∣ (w 1).natAbs)
    (hr3 : r ∣ (w 3).natAbs) : r = 1 := by
  have hg : (r : ℤ) ∣ Finset.univ.gcd w := by
    rw [Finset.dvd_gcd_iff]
    intro k hk
    fin_cases k
    · exact Int.natCast_dvd.mpr hr0
    · exact Int.natCast_dvd.mpr hr1
    · simpa [hzero]
    · exact Int.natCast_dvd.mpr hr3
  have hg1 : (r : ℤ) ∣ (1 : ℤ) := by rwa [famOrbit_gcd_one t w hw] at hg
  exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)

/-- gcd-instance for a zero at index 3 (family). -/
lemma fam_gcd_one_of_divides3 (t : ℕ) {w : Fin 4 → ℤ} (hw : w ∈ orbitOf (famQuad t))
    (hzero : w 3 = 0) {r : ℕ} (hr0 : r ∣ (w 0).natAbs) (hr1 : r ∣ (w 1).natAbs)
    (hr2 : r ∣ (w 2).natAbs) : r = 1 := by
  have hg : (r : ℤ) ∣ Finset.univ.gcd w := by
    rw [Finset.dvd_gcd_iff]
    intro k hk
    fin_cases k
    · exact Int.natCast_dvd.mpr hr0
    · exact Int.natCast_dvd.mpr hr1
    · exact Int.natCast_dvd.mpr hr2
    · simpa [hzero]
  have hg1 : (r : ℤ) ∣ (1 : ℤ) := by rwa [famOrbit_gcd_one t w hw] at hg
  exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)

/-- coordinate 2 of a family-orbit quadruple is never 0. -/
theorem famOrbit_two_ne_zero (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) : w 2 ≠ 0 := by
  intro hzero
  have ha : (w 0) % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw 0 (Or.inl rfl)
  have hb : (w 1) % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw 1 (Or.inr rfl)
  have hce : (2 : ℤ) ∣ w 3 := (famOrbit_parity t w hw).2.2.2
  have hD3 : (w 0 + w 1 + w 3) ^ 2 = 2 * ((w 0) ^ 2 + (w 1) ^ 2 + (w 3) ^ 2) := by
    have hD' := famOrbit_desc t w hw
    have hs1 : (∑ j : Fin 4, w j) = w 0 + w 1 + w 3 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    have hs2 : (∑ j : Fin 4, (w j) ^ 2) = (w 0) ^ 2 + (w 1) ^ 2 + (w 3) ^ 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    rw [hs1, hs2] at hD'
    exact hD'
  exact descartes_zero_contra ha hb hce hD3 (fun r hr0 hr1 hr3 => fam_gcd_one_of_divides2 t hw hzero hr0 hr1 hr3)

/-- coordinate 3 of a family-orbit quadruple is never 0. -/
theorem famOrbit_three_ne_zero (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) : w 3 ≠ 0 := by
  intro hzero
  have ha : (w 0) % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw 0 (Or.inl rfl)
  have hb : (w 1) % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw 1 (Or.inr rfl)
  have hce : (2 : ℤ) ∣ w 2 := (famOrbit_parity t w hw).2.2.1
  have hD3 : (w 0 + w 1 + w 2) ^ 2 = 2 * ((w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2) := by
    have hD' := famOrbit_desc t w hw
    have hs1 : (∑ j : Fin 4, w j) = w 0 + w 1 + w 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    have hs2 : (∑ j : Fin 4, (w j) ^ 2) = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by
      rw [Fin.sum_univ_four]
      simp [hzero]
    rw [hs1, hs2] at hD'
    exact hD'
  exact descartes_zero_contra ha hb hce hD3 (fun r hr0 hr1 hr2 => fam_gcd_one_of_divides3 t hw hzero hr0 hr1 hr2)

/-- no coordinate of any family-orbit quadruple is 0. -/
theorem famOrbit_ne_zero (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4) :
    w i ≠ 0 := by
  fin_cases i
  · exact famOrbit_odd_coord_ne_zero t w hw 0 (Or.inl rfl)
  · exact famOrbit_odd_coord_ne_zero t w hw 1 (Or.inr rfl)
  · exact famOrbit_two_ne_zero t w hw
  · exact famOrbit_three_ne_zero t w hw

/-- at most one negative coordinate in every family-orbit quadruple. -/
theorem famOrbit_at_most_one_neg (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t)) :
    ¬ ∃ i j : Fin 4, i ≠ j ∧ v i < 0 ∧ v j < 0 := by
  have hD := famOrbit_desc t v hv
  have hS := (famOrbit_desc_posSum t v hv).2
  exact at_most_one_neg_coord v hD hS

/-- two (distinct) coordinates of a family-orbit quadruple: at least one positive. -/
lemma famOrbit_pos_of_two_coords (t : ℕ) (v : Fin 4 → ℤ) (hv : v ∈ orbitOf (famQuad t))
    (i j : Fin 4) (hij : i ≠ j) : 0 < v i ∨ 0 < v j := by
  by_cases hi : 0 < v i
  · exact Or.inl hi
  · right
    have hine : v i ≠ 0 := famOrbit_ne_zero t v hv i
    have hilt : v i < 0 := lt_of_le_of_ne (le_of_not_gt hi) hine
    by_contra hnot
    have hjle : v j ≤ 0 := le_of_not_gt hnot
    have hjne : v j ≠ 0 := famOrbit_ne_zero t v hv j
    have hjlt : v j < 0 := lt_of_le_of_ne hjle hjne
    exact famOrbit_at_most_one_neg t v hv ⟨i, j, hij, hilt, hjlt⟩

/-- ring moves preserve membership in the family orbit. -/
theorem famOrbit_ringReach (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4) :
    ∀ u : Fin 4 → ℤ, ringReach i w u → u ∈ orbitOf (famQuad t) := by
  intro u h
  induction h with
  | refl => exact hw
  | tail hprev hstep ih =>
      rcases hstep with ⟨j, hji, rfl⟩
      exact famOrbit_gen t _ ih j

/-- the base of the family orbit is in its own orbit. -/
lemma famQuad_mem_own_orbit (t : ℕ) : famQuad t ∈ orbitOf (famQuad t) :=
  orbitOf_self (famQuad t)

/-- an odd value of a family-orbit quadruple is ≡ 1 mod 4 (indeed ≡ 5 mod 8). -/
lemma famOrbit_odd_val_four_one (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4)
    (hodd : ¬ 2 ∣ w i) : (w i) % 4 = 1 := by
  have hin : i = 0 ∨ i = 1 := (famOrbit_coord_odd_iff t w hw i).1 hodd
  have h5 : w i % 8 = 5 := famOrbit_odd_coord_eq_five_mod8 t w hw i hin
  omega

/-- an odd value of a family-orbit quadruple is ≡ 5 mod 8. -/
lemma famOrbit_odd_val_eight_five (t : ℕ) (w : Fin 4 → ℤ) (hw : w ∈ orbitOf (famQuad t)) (i : Fin 4)
    (hodd : ¬ 2 ∣ w i) : (w i) % 8 = 5 := by
  have hin : i = 0 ∨ i = 1 := (famOrbit_coord_odd_iff t w hw i).1 hodd
  exact famOrbit_odd_coord_eq_five_mod8 t w hw i hin

end Apollo
