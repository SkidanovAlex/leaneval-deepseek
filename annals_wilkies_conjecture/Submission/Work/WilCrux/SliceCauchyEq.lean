/-
  WilCrux — the set equality `bigSet = sliceCauchySet` (and its ingredient lemmas).

  `bigSet` is the `projN`-presentation of the construction described in
  `Submission/Work/WilCrux/sliceCauchy_mem.lean`; here we show it really is
  `Work.WilCrux.sliceCauchySet`.
-/
import Mathlib
import Submission.Work.WilCrux.SliceCauchyBig
import Submission.Work.WilCrux.SliceCauchyDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

variable {a b : ℕ}

/-- The constant function `Fin 1 → ℝ`. -/
def etaOf (r : ℝ) : Fin 1 → ℝ := fun _ => r

@[simp] theorem etaOf_zero (r : ℝ) : etaOf r 0 = r := rfl

/-- Splitting a function on `Fin (b + b)` into its `z` and `z'` halves. -/
theorem forall_append_iff (b : ℕ) (P : (Fin (b + b) → ℝ) → Prop) :
    (∀ q, P q) ↔ (∀ z z' : Fin b → ℝ, P (Fin.append z z')) := by
  constructor
  · intro h z z'; exact h _
  · intro h q
    have hq : Fin.append (fun j : Fin b => q (Fin.castAdd b j))
        (fun j : Fin b => q (Fin.natAdd b j)) = q :=
      Fin.append_castAdd_natAdd (m := b) (n := b)
    rw [← hq]; exact h _ _

/-- `hypSet` at the point with blocks `(w, η, z, z')`. -/
theorem hyp_append_iff (w : Fin a → ℝ) (η : Fin 1 → ℝ) (z z' : Fin b → ℝ) :
    Fin.append (Fin.append w η) (Fin.append z z') ∈ hypSet (a := a) (b := b) ↔
      (fun j : Fin b => z j) ≠ 0 ∧ (∀ j : Fin b, |z j| < η 0) ∧
      (fun j : Fin b => z' j) ≠ 0 ∧ (∀ j : Fin b, |z' j| < η 0) := by
  simp only [hypSet, Set.mem_setOf_eq, mid_eta, mid_z, mid_z', Fin.append_left, Fin.append_right]

/-- `coreSet` at the canonical point, expanded. -/
theorem core_append_iff (f : (Fin (a + b) → ℝ) → ℝ) (i : Fin (a + b))
    (w : Fin a → ℝ) (η : Fin 1 → ℝ) (z z' : Fin b → ℝ) (yy : Fin 2 → ℝ) (ε : ℝ) :
    pt w η (Fin.append z z') yy ∈ coreSet (a := a) (b := b)
        (Work.WilG4b.derivGraph f i) ε ↔
      Fin.append w z ∈ Work.WilG4b.c1Loc f ∧ yy 0 = Work.WilG4b.dDir f i (Fin.append w z) ∧
      Fin.append w z' ∈ Work.WilG4b.c1Loc f ∧ yy 1 = Work.WilG4b.dDir f i (Fin.append w z') ∧
      |yy 0 - yy 1| < ε := by
  simp only [coreSet, Set.mem_setOf_eq, pt_derivGraph_e1, pt_derivGraph_e2, pt_yIx, pt_yIx']
  tauto

/-- The existential over the value pair `yy`, eliminated. -/
theorem exists_yy_core_iff (f : (Fin (a + b) → ℝ) → ℝ) (i : Fin (a + b))
    (w : Fin a → ℝ) (η : Fin 1 → ℝ) (z z' : Fin b → ℝ) (ε : ℝ) :
    (∃ yy : Fin 2 → ℝ, pt w η (Fin.append z z') yy ∈ coreSet (a := a) (b := b)
        (Work.WilG4b.derivGraph f i) ε) ↔
      Fin.append w z ∈ Work.WilG4b.c1Loc f ∧ Fin.append w z' ∈ Work.WilG4b.c1Loc f ∧
      |Work.WilG4b.dDir f i (Fin.append w z) - Work.WilG4b.dDir f i (Fin.append w z')| < ε := by
  constructor
  · rintro ⟨yy, hyy⟩
    rw [core_append_iff] at hyy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hyy
    exact ⟨h1, h3, by rw [← h2, ← h4]; exact h5⟩
  · rintro ⟨h1, h3, h5⟩
    refine ⟨![Work.WilG4b.dDir f i (Fin.append w z),
      Work.WilG4b.dDir f i (Fin.append w z')], ?_⟩
    rw [core_append_iff]
    exact ⟨h1, rfl, h3, rfl, by simpa using h5⟩

/-- `0 < 1/((k:ℝ)+1)`. -/
theorem one_div_succ_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1) := by
  apply one_div_pos.mpr
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- **The big set really is `sliceCauchySet`.** -/
theorem bigSet_eq (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (k : ℕ) (ε : ℝ) :
    bigSet G j k ε = sliceCauchySet G j k ε := by
  ext w
  rw [bigSet]
  simp only [Work.WilG5.projN, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
    threshSet, small_eta, pt]
  rw [sliceCauchySet]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨η, ⟨hc, h1⟩, hbody⟩
    have hpos : 0 < η 0 := lt_trans (one_div_succ_pos k) hc
    refine ⟨η 0, hc, h1, ?_⟩
    have hbody' : ∀ q : Fin (b + b) → ℝ,
        Fin.append (Fin.append w η) q ∈ hypSet (a := a) (b := b) →
        ∃ yy : Fin 2 → ℝ, pt w η q yy ∈ coreSet (a := a) (b := b)
          (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε := by
      intro q hq
      by_contra hcon
      exact hbody ⟨q, hq, hcon⟩
    intro z z' hz0 hzn hz'0 hz'n
    have hq : Fin.append (Fin.append w η) (Fin.append z z') ∈ hypSet (a := a) (b := b) := by
      rw [hyp_append_iff]
      refine ⟨by simpa using hz0, ?_, by simpa using hz'0, ?_⟩
      · intro j
        have hj := (pi_norm_lt_iff hpos).mp hzn j
        simpa [Real.norm_eq_abs] using hj
      · intro j
        have hj := (pi_norm_lt_iff hpos).mp hz'n j
        simpa [Real.norm_eq_abs] using hj
    exact (exists_yy_core_iff (Work.WilG4c.famFun G) (Fin.natAdd a j) w η z z' ε).mp
      (hbody' (Fin.append z z') hq)
  · rintro ⟨ηr, hc, h1, hbody⟩
    have hpos : 0 < ηr := lt_trans (one_div_succ_pos k) hc
    refine ⟨etaOf ηr, ⟨by simpa [etaOf] using hc, by simpa [etaOf] using h1⟩, ?_⟩
    rintro ⟨q, hq, hno⟩
    let z : Fin b → ℝ := fun j => q (Fin.castAdd b j)
    let z' : Fin b → ℝ := fun j => q (Fin.natAdd b j)
    have hq' : Fin.append z z' = q := Fin.append_castAdd_natAdd (m := b) (n := b)
    rw [← hq'] at hq
    rw [hyp_append_iff] at hq
    simp only [etaOf] at hq
    obtain ⟨hz0, hzn, hz'0, hz'n⟩ := hq
    have hzn' : ‖z‖ < ηr := (pi_norm_lt_iff hpos).mpr
      (fun j => by simpa [Real.norm_eq_abs] using hzn j)
    have hz'n' : ‖z'‖ < ηr := (pi_norm_lt_iff hpos).mpr
      (fun j => by simpa [Real.norm_eq_abs] using hz'n j)
    have hres := hbody z z' (by simpa using hz0) hzn' (by simpa using hz'0) hz'n'
    have hcore := (exists_yy_core_iff (Work.WilG4c.famFun G) (Fin.natAdd a j) w (etaOf ηr)
      z z' ε).mpr hres
    rw [hq'] at hcore
    exact hno hcore

end Work.WilCrux
