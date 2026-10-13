import Mathlib
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- The open unit interval band `{z : Fin 2 → ℝ | z 0 ∈ (0,1)}` is `Ω`-definable
(both half-spaces are already available from `WilG5`). -/
theorem intervalBand_mem (S : WilkiesDesign.SOMin) :
    {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∈ S.Ω 29 16 2 := by
  have hlt : {z : Fin 2 → ℝ | (0 : ℝ) < z 0} ∈ S.Ω (4 * 2 + 20) 8 2 :=
    Work.WilG5.ltSet_mem (S := S) (0 : Fin 2) 0
  have hgt : {z : Fin 2 → ℝ | z 0 < 1} ∈ S.Ω (4 * 2 + 20) 8 2 :=
    Work.WilG5.gtSet_mem (S := S) (0 : Fin 2) 1
  have h := S.inter (fun _ : Fin 2 => 8)
    (fun j : Fin 2 => if j = 0 then {z : Fin 2 → ℝ | (0 : ℝ) < z 0}
      else {z : Fin 2 → ℝ | z 0 < 1})
    (by intro j; fin_cases j
        · simpa using hlt
        · simpa using hgt)
  rw [show (∑ _ : Fin 2, 8) = 16 from by simp] at h
  have he : (⋂ j : Fin 2, if j = 0 then {z : Fin 2 → ℝ | (0 : ℝ) < z 0}
      else {z : Fin 2 → ℝ | z 0 < 1}) = {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} := by
    ext x; simp [Fin.forall_fin_two, Set.mem_Ioo]
  rw [he] at h
  simpa using h

/-- The coordinate-equality band `{z : Fin 2 → ℝ | z 1 = z 0}` is `Ω`-definable. -/
theorem coordEqBand_mem (S : WilkiesDesign.SOMin) :
    {z : Fin 2 → ℝ | z 1 = z 0} ∈ S.Ω 2 1 2 := by
  have h := S.hyp 2
    (MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ)
  have he : {x : Fin 2 → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (1 : Fin 2) - MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0}
      = {z : Fin 2 → ℝ | z 1 = z 0} := by
    ext z
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_eq_zero]
  rw [he] at h
  refine Work.WilG5.mem_mono h 2 1 le_rfl ?_
  exact le_trans (Work.WilG5.td_sub_le _ _)
    (max_le (Work.WilG5.td_X_le (1 : Fin 2)) (Work.WilG5.td_X_le (0 : Fin 2)))

/-- The value band `{z : Fin 2 → ℝ | z 1 = 1/2}` is `Ω`-definable. -/
theorem halfBand_mem (S : WilkiesDesign.SOMin) :
    {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)} ∈ S.Ω 2 1 2 := by
  have h := S.hyp 2
    (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ)
  have he : {x : Fin 2 → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) = 0}
      = {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)} := by
    ext z
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]
  rw [he] at h
  refine Work.WilG5.mem_mono h 2 1 le_rfl ?_
  refine le_trans (Work.WilG5.td_sub_le _ _)
    (max_le (Work.WilG5.td_X_le (1 : Fin 2)) ?_)
  exact le_trans (Work.WilG5.td_C_le (1 / 2 : ℝ)) (Nat.zero_le 1)

/-- The graph of `clamp01 ∘ (· 0)` on `Fin 1 → ℝ`, in `ℝ²`. -/
theorem clampGraphMem_fin2 (S : WilkiesDesign.SOMin) : ∃ (a c : ℕ),
    WilkiesDesign.graphOf (fun v : Fin 1 → ℝ =>
        if v 0 ∈ Set.Ioo (0 : ℝ) 1 then v 0 else (1 / 2 : ℝ)) ∈ S.Ω a c 2 := by
  -- the four pieces
  have hI0 := intervalBand_mem S
  have hB0 := coordEqBand_mem S
  have hEv0 := halfBand_mem S
  have hI : {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∈ S.Ω 70 70 2 :=
    Work.WilG5.mem_mono hI0 70 70 (by omega) (by omega)
  have hIc : ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∈ S.Ω 70 70 2 :=
    Work.WilG5.mem_mono (S.compl hI0) 70 70 (by omega) (by omega)
  have hB : {z : Fin 2 → ℝ | z 1 = z 0} ∈ S.Ω 70 70 2 :=
    Work.WilG5.mem_mono hB0 70 70 (by omega) (by omega)
  have hEv : {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)} ∈ S.Ω 70 70 2 :=
    Work.WilG5.mem_mono hEv0 70 70 (by omega) (by omega)
  -- intersections and union
  have hAB : ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
      ∈ S.Ω 71 140 2 := by
    have h := S.inter (fun _ : Fin 2 => 70)
      (fun j : Fin 2 => if j = 0 then {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1}
        else {z : Fin 2 → ℝ | z 1 = z 0})
      (by intro j; fin_cases j
          · simpa using hI
          · simpa using hB)
    rw [show (∑ _ : Fin 2, 70) = 140 from by simp] at h
    have he : (⋂ j : Fin 2, if j = 0 then {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1}
        else {z : Fin 2 → ℝ | z 1 = z 0})
        = {z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0} := by
      ext x; simp [Fin.forall_fin_two]
    rw [he] at h
    simpa using h
  have hCE : (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)})
      ∈ S.Ω 71 140 2 := by
    have h := S.inter (fun _ : Fin 2 => 70)
      (fun j : Fin 2 => if j = 0 then ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ
        else {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)})
      (by intro j; fin_cases j
          · simpa using hIc
          · simpa using hEv)
    rw [show (∑ _ : Fin 2, 70) = 140 from by simp] at h
    have he : (⋂ j : Fin 2, if j = 0 then ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ
        else {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)})
        = ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)} := by
      ext x; simp [Fin.forall_fin_two]
    rw [he] at h
    simpa using h
  have hU : ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
      ∪ (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)})
      ∈ S.Ω 71 280 2 := by
    have h := S.union (fun _ : Fin 2 => 140)
      (fun j : Fin 2 => if j = 0
        then ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
        else (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)}))
      (by intro j; fin_cases j
          · simpa using hAB
          · simpa using hCE)
    rw [show (∑ _ : Fin 2, 140) = 280 from by simp] at h
    have he : (⋃ j : Fin 2, if j = 0
        then ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
        else (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)}))
        = ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
          ∪ (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)}) := by
      ext x; simp [Fin.exists_fin_two]
    rw [he] at h
    simpa using h
  refine ⟨71, 280, ?_⟩
  have hset : WilkiesDesign.graphOf (fun v : Fin 1 → ℝ =>
        if v 0 ∈ Set.Ioo (0 : ℝ) 1 then v 0 else (1 / 2 : ℝ))
      = ({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1} ∩ {z : Fin 2 → ℝ | z 1 = z 0})
        ∪ (({z : Fin 2 → ℝ | z 0 ∈ Set.Ioo (0 : ℝ) 1})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = (1 / 2 : ℝ)}) := by
    ext z
    simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff]
    rw [show z (Fin.last 1) = z 1 from rfl, show (Fin.init z) 0 = z 0 from rfl]
    by_cases h : z 0 ∈ Set.Ioo (0 : ℝ) 1 <;> simp [h]
  rw [hset]
  exact hU

theorem clampGraphMem (S : WilkiesDesign.SOMin) : ∃ (a c : ℕ),
    WilkiesDesign.graphOf (fun v : Fin 1 → ℝ =>
        if v 0 ∈ Set.Ioo (0 : ℝ) 1 then v 0 else (1 / 2 : ℝ)) ∈ S.Ω a c (1 + 1) := by
  obtain ⟨a, c, h⟩ := clampGraphMem_fin2 S
  exact ⟨a, c, h⟩

end Work.WilG4c
