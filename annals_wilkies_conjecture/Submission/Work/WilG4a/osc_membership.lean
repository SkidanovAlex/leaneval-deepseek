/-
  WilG4a — `osc_membership`.

  `oscR g q` and `oscL g q` are the one-sided oscillation sets of `g : ℝ → ℝ` at slope `q`
  (`Work.WilG1.oscR`, `Work.WilG1.oscL`).  This file proves, from the generic formula
  machinery of `Work.WilG1.Thin.osc_mem` (`oscGeneric_mem`), that whenever the graph of `g`
  lies in `S.Ω F D 2` both lifts are `Ω`-sets.

  Writing `X = oscGraph g` and reading the five coordinates as `(x, v, δ, y, u)`:

  * `oscGeneric X winR1 winR2 (valUp q) = liftR (RHi g q)`,
  * `oscGeneric X winR1 winR2 (valDn q) = liftR (RLo g q)`,
  * `oscGeneric X winL1 winL2 (valDn q) = liftR (LHi g q)`,
  * `oscGeneric X winL1 winL2 (valUp q) = liftR (LLo g q)`,

  and `oscR g q = RHi g q ∩ RLo g q`, `oscL g q = LHi g q ∩ LLo g q`; the result follows
  from `oscGeneric_mem` and closure of `S.Ω` under binary intersection.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.OneDim.thin_ev
import Submission.Work.WilG1.Thin.osc_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign

/-! ## 1. The four scalar conditions -/

/-- Right quotients above `q` accumulate at `x`. -/
def RHi (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ q < Work.WilG1.dq g x y}

/-- Right quotients below `q` accumulate at `x`. -/
def RLo (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x < y ∧ y < x + δ ∧ Work.WilG1.dq g x y < q}

/-- Left quotients above `q` accumulate at `x`. -/
def LHi (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ q < Work.WilG1.dq g x y}

/-- Left quotients below `q` accumulate at `x`. -/
def LLo (g : ℝ → ℝ) (q : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ y : ℝ, x - δ < y ∧ y < x ∧ Work.WilG1.dq g x y < q}

lemma oscR_eq (g : ℝ → ℝ) (q : ℝ) : Work.WilG1.oscR g q = RHi g q ∩ RLo g q := by
  ext x
  simp only [Work.WilG1.oscR, RHi, RLo, Set.mem_ofPred_eq, Set.mem_inter_iff]

lemma oscL_eq (g : ℝ → ℝ) (q : ℝ) : Work.WilG1.oscL g q = LHi g q ∩ LLo g q := by
  ext x
  simp only [Work.WilG1.oscL, LHi, LLo, Set.mem_ofPred_eq, Set.mem_inter_iff]

lemma liftR_inter (A B : Set ℝ) :
    Work.WilG1.liftR (A ∩ B) = Work.WilG1.liftR A ∩ Work.WilG1.liftR B := by
  ext w
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, Set.mem_inter_iff]

/-! ## 2. Reading graph membership at a two-vector -/

@[simp] lemma graph_mem_pt2 {g : ℝ → ℝ} {y u : ℝ} :
    (![y, u] : Fin 2 → ℝ) ∈ Work.WilG1.Thin.oscGraph g ↔ u = g y := by
  rw [Work.WilG1.Thin.mem_oscGraph]
  simp

/-! ## 3. The four realisations -/

lemma oscGeneric_RHi (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.Thin.oscGeneric (Work.WilG1.Thin.oscGraph g) Work.WilG1.Thin.winR1
        Work.WilG1.Thin.winR2 (Work.WilG1.Thin.valUp q) = Work.WilG1.liftR (RHi g q) := by
  ext w
  rw [Work.WilG1.Thin.mem_oscGeneric]
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, RHi]
  constructor
  · rintro ⟨v, hv, hbody⟩ δ hδ
    rw [graph_mem_pt2] at hv
    obtain ⟨y, u, hyu⟩ := hbody δ hδ
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2] at hyu
    obtain ⟨hP, hQ, hR, hX⟩ := hyu
    subst hv
    subst hX
    rw [Work.WilG1.Thin.eval_winR1] at hP
    rw [Work.WilG1.Thin.eval_winR2] at hQ
    rw [Work.WilG1.Thin.eval_valUp] at hR
    refine ⟨y, sub_pos.mp hP, by linarith, ?_⟩
    rw [Work.WilG1.Thin.dq_lt_iff (sub_pos.mp hP)]
    linarith
  · intro h
    refine ⟨g (w 0), graph_mem_pt2.mpr rfl, ?_⟩
    intro δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    refine ⟨y, g y, ?_⟩
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2]
    rw [Work.WilG1.Thin.eval_winR1, Work.WilG1.Thin.eval_winR2, Work.WilG1.Thin.eval_valUp]
    refine ⟨by linarith, by linarith, ?_, rfl⟩
    have := (Work.WilG1.Thin.dq_lt_iff hy1).mp hy3
    linarith

lemma oscGeneric_RLo (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.Thin.oscGeneric (Work.WilG1.Thin.oscGraph g) Work.WilG1.Thin.winR1
        Work.WilG1.Thin.winR2 (Work.WilG1.Thin.valDn q) = Work.WilG1.liftR (RLo g q) := by
  ext w
  rw [Work.WilG1.Thin.mem_oscGeneric]
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, RLo]
  constructor
  · rintro ⟨v, hv, hbody⟩ δ hδ
    rw [graph_mem_pt2] at hv
    obtain ⟨y, u, hyu⟩ := hbody δ hδ
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2] at hyu
    obtain ⟨hP, hQ, hR, hX⟩ := hyu
    subst hv
    subst hX
    rw [Work.WilG1.Thin.eval_winR1] at hP
    rw [Work.WilG1.Thin.eval_winR2] at hQ
    rw [Work.WilG1.Thin.eval_valDn] at hR
    refine ⟨y, sub_pos.mp hP, by linarith, ?_⟩
    rw [Work.WilG1.Thin.lt_dq_iff (sub_pos.mp hP)]
    linarith
  · intro h
    refine ⟨g (w 0), graph_mem_pt2.mpr rfl, ?_⟩
    intro δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    refine ⟨y, g y, ?_⟩
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2]
    rw [Work.WilG1.Thin.eval_winR1, Work.WilG1.Thin.eval_winR2, Work.WilG1.Thin.eval_valDn]
    refine ⟨by linarith, by linarith, ?_, rfl⟩
    have := (Work.WilG1.Thin.lt_dq_iff hy1).mp hy3
    linarith

lemma oscGeneric_LHi (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.Thin.oscGeneric (Work.WilG1.Thin.oscGraph g) Work.WilG1.Thin.winL1
        Work.WilG1.Thin.winL2 (Work.WilG1.Thin.valDn q) = Work.WilG1.liftR (LHi g q) := by
  ext w
  rw [Work.WilG1.Thin.mem_oscGeneric]
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, LHi]
  constructor
  · rintro ⟨v, hv, hbody⟩ δ hδ
    rw [graph_mem_pt2] at hv
    obtain ⟨y, u, hyu⟩ := hbody δ hδ
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2] at hyu
    obtain ⟨hP, hQ, hR, hX⟩ := hyu
    subst hv
    subst hX
    rw [Work.WilG1.Thin.eval_winL1] at hP
    rw [Work.WilG1.Thin.eval_winL2] at hQ
    rw [Work.WilG1.Thin.eval_valDn] at hR
    refine ⟨y, by linarith, sub_pos.mp hQ, ?_⟩
    rw [Work.WilG1.OneDim.lt_dq_iff_of_lt (sub_pos.mp hQ)]
    linarith
  · intro h
    refine ⟨g (w 0), graph_mem_pt2.mpr rfl, ?_⟩
    intro δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    refine ⟨y, g y, ?_⟩
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2]
    rw [Work.WilG1.Thin.eval_winL1, Work.WilG1.Thin.eval_winL2, Work.WilG1.Thin.eval_valDn]
    refine ⟨by linarith, by linarith, ?_, rfl⟩
    have := (Work.WilG1.OneDim.lt_dq_iff_of_lt hy2).mp hy3
    linarith

lemma oscGeneric_LLo (g : ℝ → ℝ) (q : ℝ) :
    Work.WilG1.Thin.oscGeneric (Work.WilG1.Thin.oscGraph g) Work.WilG1.Thin.winL1
        Work.WilG1.Thin.winL2 (Work.WilG1.Thin.valUp q) = Work.WilG1.liftR (LLo g q) := by
  ext w
  rw [Work.WilG1.Thin.mem_oscGeneric]
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, LLo]
  constructor
  · rintro ⟨v, hv, hbody⟩ δ hδ
    rw [graph_mem_pt2] at hv
    obtain ⟨y, u, hyu⟩ := hbody δ hδ
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2] at hyu
    obtain ⟨hP, hQ, hR, hX⟩ := hyu
    subst hv
    subst hX
    rw [Work.WilG1.Thin.eval_winL1] at hP
    rw [Work.WilG1.Thin.eval_winL2] at hQ
    rw [Work.WilG1.Thin.eval_valUp] at hR
    refine ⟨y, by linarith, sub_pos.mp hQ, ?_⟩
    rw [Work.WilG1.OneDim.dq_lt_iff_of_lt (sub_pos.mp hQ)]
    linarith
  · intro h
    refine ⟨g (w 0), graph_mem_pt2.mpr rfl, ?_⟩
    intro δ hδ
    obtain ⟨y, hy1, hy2, hy3⟩ := h δ hδ
    refine ⟨y, g y, ?_⟩
    rw [Work.WilG1.Thin.mem_oscBody, graph_mem_pt2]
    rw [Work.WilG1.Thin.eval_winL1, Work.WilG1.Thin.eval_winL2, Work.WilG1.Thin.eval_valUp]
    refine ⟨by linarith, by linarith, ?_, rfl⟩
    have := (Work.WilG1.OneDim.dq_lt_iff_of_lt hy2).mp hy3
    linarith

/-! ## 4. The `Ω`-membership -/

theorem osc_mem_local {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    (∃ a : ℕ, ∃ b : Polynomial ℕ,
        Work.WilG1.liftR (Work.WilG1.oscR g q) ∈ S.Ω a (b.eval D) 1) ∧
    (∃ a : ℕ, ∃ b : Polynomial ℕ,
        Work.WilG1.liftR (Work.WilG1.oscL g q) ∈ S.Ω a (b.eval D) 1) := by
  have hX : Work.WilG1.Thin.oscGraph g ∈ S.Ω F D 2 := hg
  have hRhi := Work.WilG1.Thin.oscGeneric_mem (S := S) (F := F) (D := D)
    (X := Work.WilG1.Thin.oscGraph g) hX Work.WilG1.Thin.winR1 Work.WilG1.Thin.winR2
    (Work.WilG1.Thin.valUp q) Work.WilG1.Thin.td_winR1 Work.WilG1.Thin.td_winR2
    (Work.WilG1.Thin.td_valUp q)
  have hRlo := Work.WilG1.Thin.oscGeneric_mem (S := S) (F := F) (D := D)
    (X := Work.WilG1.Thin.oscGraph g) hX Work.WilG1.Thin.winR1 Work.WilG1.Thin.winR2
    (Work.WilG1.Thin.valDn q) Work.WilG1.Thin.td_winR1 Work.WilG1.Thin.td_winR2
    (Work.WilG1.Thin.td_valDn q)
  have hLhi := Work.WilG1.Thin.oscGeneric_mem (S := S) (F := F) (D := D)
    (X := Work.WilG1.Thin.oscGraph g) hX Work.WilG1.Thin.winL1 Work.WilG1.Thin.winL2
    (Work.WilG1.Thin.valDn q) Work.WilG1.Thin.td_winL1 Work.WilG1.Thin.td_winL2
    (Work.WilG1.Thin.td_valDn q)
  have hLlo := Work.WilG1.Thin.oscGeneric_mem (S := S) (F := F) (D := D)
    (X := Work.WilG1.Thin.oscGraph g) hX Work.WilG1.Thin.winL1 Work.WilG1.Thin.winL2
    (Work.WilG1.Thin.valUp q) Work.WilG1.Thin.td_winL1 Work.WilG1.Thin.td_winL2
    (Work.WilG1.Thin.td_valUp q)
  constructor
  · refine ⟨max (F + 100) (F + 100) + 1, Work.WilG1.Thin.deg2 + Work.WilG1.Thin.deg2, ?_⟩
    rw [oscR_eq, liftR_inter, ← oscGeneric_RHi, ← oscGeneric_RLo]
    exact Work.WilG1.Omega.inter₂ hRhi hRlo
  · refine ⟨max (F + 100) (F + 100) + 1, Work.WilG1.Thin.deg2 + Work.WilG1.Thin.deg2, ?_⟩
    rw [oscL_eq, liftR_inter, ← oscGeneric_LHi, ← oscGeneric_LLo]
    exact Work.WilG1.Omega.inter₂ hLhi hLlo

end Work.WilG4a
