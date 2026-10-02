import Mathlib
import Submission.Work.ELTop.PolyCurve.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.PolyCurve.intLift_core
import Submission.Work.ELTop.PolyCurve.cyclicStrict_angle_data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop.PolyCurve

/-! ## The `ℤ`-indexed angle data of an admissible list of co-landing pairs -/

/-- The pair occupying the position `i` of the list, for `i` in the range `[0, ps.length)`. -/
def angIdx {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (ps : List (Work.EL.CoPair hN))
    (i : ℤ) (h : 0 ≤ i ∧ i < (ps.length : ℤ)) : Fin ps.length :=
  ⟨i.toNat, by rw [Int.toNat_lt h.1]; exact h.2⟩

/-- The first angle of the pair at position `i`, extended by `0` outside the range
`[0, ps.length)`. -/
def angA {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (ps : List (Work.EL.CoPair hN))
    (i : ℤ) : ℝ :=
  if h : 0 ≤ i ∧ i < (ps.length : ℤ) then (ps.get (angIdx ps i h)).a else 0

/-- The second angle of the pair at position `i`, extended by `0` outside the range. -/
def angB {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (ps : List (Work.EL.CoPair hN))
    (i : ℤ) : ℝ :=
  if h : 0 ≤ i ∧ i < (ps.length : ℤ) then (ps.get (angIdx ps i h)).b else 0

/-- The landing point of the pair at position `i`, extended by `0` outside the range. -/
def angY {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (ps : List (Work.EL.CoPair hN))
    (i : ℤ) : ℂ :=
  if h : 0 ≤ i ∧ i < (ps.length : ℤ) then (ps.get (angIdx ps i h)).y else 0

theorem angA_of_mem {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : ℤ) (h : 0 ≤ i ∧ i < (ps.length : ℤ)) :
    angA ps i = (ps.get (angIdx ps i h)).a := by
  unfold angA
  rw [dite_eq_left h]

theorem angB_of_mem {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : ℤ) (h : 0 ≤ i ∧ i < (ps.length : ℤ)) :
    angB ps i = (ps.get (angIdx ps i h)).b := by
  unfold angB
  rw [dite_eq_left h]

theorem angY_of_mem {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : ℤ) (h : 0 ≤ i ∧ i < (ps.length : ℤ)) :
    angY ps i = (ps.get (angIdx ps i h)).y := by
  unfold angY
  rw [dite_eq_left h]

theorem angIdx_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length)
    (h : 0 ≤ (i : ℤ) ∧ (i : ℤ) < (ps.length : ℤ)) :
    angIdx ps (i : ℤ) h = i := by
  apply Fin.ext
  simp only [angIdx, Fin.val_mk]
  exact Int.toNat_natCast i.val

theorem angIdx_succ_val {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : ℤ)
    (h : 0 ≤ i ∧ i < (ps.length : ℤ)) (h' : 0 ≤ i + 1 ∧ i + 1 < (ps.length : ℤ)) :
    (angIdx ps (i + 1) h').val = (angIdx ps i h).val + 1 := by
  simp only [angIdx, Fin.val_mk]
  rw [Int.toNat_add h.1 (by norm_num)]
  norm_num

theorem angIdx_succ {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : ℤ)
    (h : 0 ≤ i ∧ i < (ps.length : ℤ)) (h' : 0 ≤ i + 1 ∧ i + 1 < (ps.length : ℤ)) :
    angIdx ps (i + 1) h' =
      ⟨(angIdx ps i h).val + 1, by
        have h1 := (angIdx ps (i + 1) h').isLt
        have h2 := angIdx_succ_val ps i h h'
        omega⟩ :=
  Fin.ext (angIdx_succ_val ps i h h')

theorem angA_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) :
    angA ps (i : ℤ) = (ps.get i).a := by
  have h : 0 ≤ (i : ℤ) ∧ (i : ℤ) < (ps.length : ℤ) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast i.isLt⟩
  rw [angA_of_mem ps (i : ℤ) h, angIdx_natCast ps i h]

theorem angB_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) :
    angB ps (i : ℤ) = (ps.get i).b := by
  have h : 0 ≤ (i : ℤ) ∧ (i : ℤ) < (ps.length : ℤ) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast i.isLt⟩
  rw [angB_of_mem ps (i : ℤ) h, angIdx_natCast ps i h]

theorem angY_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) :
    angY ps (i : ℤ) = (ps.get i).y := by
  have h : 0 ≤ (i : ℤ) ∧ (i : ℤ) < (ps.length : ℤ) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast i.isLt⟩
  rw [angY_of_mem ps (i : ℤ) h, angIdx_natCast ps i h]

theorem angA_lt_angB {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN))
    (h1 : ∀ i : Fin ps.length, (ps.get i).a < (ps.get i).b)
    (i : ℤ) (h0 : 0 ≤ i) (h1' : i < (ps.length : ℤ)) : angA ps i < angB ps i := by
  have h : 0 ≤ i ∧ i < (ps.length : ℤ) := ⟨h0, h1'⟩
  rw [angA_of_mem ps i h, angB_of_mem ps i h]
  exact h1 (angIdx ps i h)

theorem angB_lt_angA_succ {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN))
    (h2 : ∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      (ps.get i).b < (ps.get ⟨i.val + 1, hi⟩).a)
    (i : ℤ) (h0 : 0 ≤ i) (h1 : i + 1 < (ps.length : ℤ)) :
    angB ps i < angA ps (i + 1) := by
  have h : 0 ≤ i ∧ i < (ps.length : ℤ) := ⟨h0, by linarith⟩
  have h' : 0 ≤ i + 1 ∧ i + 1 < (ps.length : ℤ) := ⟨by linarith, h1⟩
  rw [angB_of_mem ps i h, angA_of_mem ps (i + 1) h', angIdx_succ ps i h h']
  exact h2 (angIdx ps i h) _

theorem angIdx_zero {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (h : 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < (ps.length : ℤ)) :
    angIdx ps 0 h = ⟨0, by omega⟩ := by
  apply Fin.ext
  simp only [angIdx, Fin.val_mk]
  norm_num

theorem angIdx_last {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hpos : 0 < ps.length)
    (h : 0 ≤ ((ps.length : ℤ) - 1) ∧ ((ps.length : ℤ) - 1) < (ps.length : ℤ)) :
    angIdx ps ((ps.length : ℤ) - 1) h = ⟨ps.length - 1, by omega⟩ := by
  apply Fin.ext
  simp only [angIdx, Fin.val_mk]
  have hcast : ((ps.length : ℤ) - 1 : ℤ) = ((ps.length - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ ps.length)]
    norm_num
  rw [hcast, Int.toNat_natCast]

theorem angB_last_lt_angA_zero {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hpos : 0 < ps.length)
    (h3 : (ps.get ⟨ps.length - 1, by omega⟩).b < (ps.get ⟨0, by omega⟩).a + 1) :
    angB ps ((ps.length : ℤ) - 1) < angA ps 0 + 1 := by
  have h : 0 ≤ ((ps.length : ℤ) - 1) ∧ ((ps.length : ℤ) - 1) < (ps.length : ℤ) :=
    ⟨by omega, by omega⟩
  have h0 : 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < (ps.length : ℤ) := ⟨le_refl _, by omega⟩
  rw [angB_of_mem ps ((ps.length : ℤ) - 1) h, angA_of_mem ps 0 h0,
    angIdx_last ps hpos h, angIdx_zero ps h0]
  exact h3

theorem angY_mem_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (i : ℤ) (h : 0 ≤ i ∧ i < (ps.length : ℤ)) :
    angY ps i ∈ Work.EL.K c := by
  rw [angY_of_mem ps i h]
  exact Work.ELTop.landsN_mem_K hN (ps.get (angIdx ps i h)).lands_a

theorem angY_inj {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hinj : ps.Pairwise fun P Q => P.y ≠ Q.y)
    (i j : ℤ) (hi0 : 0 ≤ i) (hi : i < (ps.length : ℤ))
    (hj0 : 0 ≤ j) (hj : j < (ps.length : ℤ))
    (h : angY ps i = angY ps j) : i = j := by
  have hi' : 0 ≤ i ∧ i < (ps.length : ℤ) := ⟨hi0, hi⟩
  have hj' : 0 ≤ j ∧ j < (ps.length : ℤ) := ⟨hj0, hj⟩
  rw [angY_of_mem ps i hi', angY_of_mem ps j hj'] at h
  have key : angIdx ps i hi' = angIdx ps j hj' := by
    by_contra hneIJ
    have hlt : (angIdx ps i hi').val < (angIdx ps j hj').val ∨
        (angIdx ps j hj').val < (angIdx ps i hi').val :=
      lt_or_gt_of_ne fun hh => hneIJ (Fin.ext hh)
    rcases hlt with hlt | hlt
    · exact absurd (by simpa only [List.get_eq_getElem] using h)
        ((List.pairwise_iff_getElem.mp hinj) (angIdx ps i hi').val (angIdx ps j hj').val
          (angIdx ps i hi').isLt (angIdx ps j hj').isLt hlt)
    · exact absurd (by simpa only [List.get_eq_getElem] using h.symm)
        ((List.pairwise_iff_getElem.mp hinj) (angIdx ps j hj').val (angIdx ps i hi').val
          (angIdx ps j hj').isLt (angIdx ps i hi').isLt hlt)
  have hval : i.toNat = j.toNat := by
    have := congrArg Fin.val key
    simpa only [angIdx, Fin.val_mk] using this
  rw [← Int.toNat_of_nonneg hi0, ← Int.toNat_of_nonneg hj0, hval]

/-! ## `A i = angA ps i` at natural-number indices -/

theorem A_at_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) (A : ℤ → ℝ)
    (hA : ∀ k : ℤ, A k = angA ps (k % (ps.length : ℤ)) +
      ((k / (ps.length : ℤ) : ℤ) : ℝ)) :
    A (i : ℤ) = (ps.get i).a := by
  rw [hA]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg i.val) (by exact_mod_cast i.isLt),
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg i.val) (by exact_mod_cast i.isLt)]
  rw [angA_natCast]
  norm_num

theorem B_at_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) (B : ℤ → ℝ)
    (hB : ∀ k : ℤ, B k = angB ps (k % (ps.length : ℤ)) +
      ((k / (ps.length : ℤ) : ℤ) : ℝ)) :
    B (i : ℤ) = (ps.get i).b := by
  rw [hB]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg i.val) (by exact_mod_cast i.isLt),
    Int.ediv_eq_zero_of_lt (Int.natCast_nonneg i.val) (by exact_mod_cast i.isLt)]
  rw [angB_natCast]
  norm_num

theorem Y_at_natCast {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (i : Fin ps.length) (Y : ℤ → ℂ)
    (hY : ∀ k : ℤ, Y k = angY ps (k % (ps.length : ℤ))) :
    Y (i : ℤ) = (ps.get i).y := by
  rw [hY]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg i.val) (by exact_mod_cast i.isLt)]
  rw [angY_natCast]

/-! ## Main theorem -/

theorem exists_cycLift {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∃ D : Work.ELTop.CycLift hN, D.Matches ps := by
  classical
  have hm : 0 < ps.length := List.length_pos_iff.mpr hA.ne
  obtain ⟨hstep₁, hstep₂, hstep₃⟩ := cyclicStrict_angle_data ps hm hA.cyc
  obtain ⟨A, B, Y, hAdef, hBdef, hYdef, hAadd, hBadd, hYadd, hAB, hBA, hYinj⟩ :=
    intLift_core hm (angA ps) (angB ps) (angY ps)
      (angA_lt_angB ps hstep₁) (angB_lt_angA_succ ps hstep₂)
      (angB_last_lt_angA_zero ps hm hstep₃) (angY_inj ps hA.inj)
  refine ⟨⟨ps.length, hm, A, B, Y, hAadd, hBadd, hYadd, hAB, hBA, hYinj, ?_⟩, ?_⟩
  · intro k
    rw [hYdef k]
    exact angY_mem_K hN ps (k % (ps.length : ℤ))
      ⟨Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hm),
        Int.emod_lt_of_pos _ (by exact_mod_cast hm)⟩
  · refine ⟨rfl, ?_⟩
    intro i
    refine ⟨(i : ℤ), 0, by ring, ?_, ?_, ?_⟩
    · simpa using A_at_natCast ps i A hAdef
    · simpa using B_at_natCast ps i B hBdef
    · simpa using Y_at_natCast ps i Y hYdef

end Work.ELTop.PolyCurve
