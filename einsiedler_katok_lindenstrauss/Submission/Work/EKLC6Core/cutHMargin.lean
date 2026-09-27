import Mathlib
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.mem_VThick_frontier_of_mem_of_not_mem

namespace Work.EKLC6Core

open Work.EKLContract

/-- The thin shell `shellThin S η` of the cut is monotone in the scale `η`. -/
theorem shellThin_mono {μ : MeasureTheory.Measure X3} {U : Subgroup SL3} {ε : ℝ}
    (S : CutData μ U ε) {η η' : ℝ} (h : η ≤ η') :
    shellThin S η ⊆ shellThin S η' := by
  intro z hz
  simp only [shellThin, Set.mem_union, Set.mem_iUnion] at hz ⊢
  exact hz.imp (fun ⟨i, hi⟩ => ⟨i, VThick_mono_left h _ hi⟩)
    (fun hb => VThick_mono_left h _ hb)

theorem cutHMargin {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) (O : ℕ → Set Work.EKLContract.SL3)
    (hOopen : ∀ m, IsOpen (O m))
    (hvis : ∀ z : Work.EKLContract.SL3, ∃ m, z ∈ Work.EKLC6Core.sat U (O m))
    (hsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.sat U (O m) ↔ w ∈ Work.EKLC6Core.sat U (O m))) →
      w ∈ Work.EKLC6Core.sat U ({z} : Set Work.EKLContract.SL3))
    (huni : ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0)
    {t : Fin 3 → ℝ} {C μ0 : ℝ} (hC : 0 < C) (hμ0 : 0 < μ0) {N n : ℕ}
    (hμ0n : C * μ0 ^ n ≤ 1)
    {y : Work.EKLContract.X3} (hy : y ∈ Work.EKLC6Core.CutGood S t C μ0 N)
    (hn : N ≤ n) {c : ℝ} (hc : 0 < c) (hcm : 20 * c ≤ C) (hρn : c * μ0 ^ n ≤ 10 * S.ρ)
    {u : Work.EKLContract.SL3} (huU : u ∈ U)
    (huV : u ∈ Work.EKLContract.V (c * μ0 ^ n)) :
    u • (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) y) ∈
      Work.EKLContract.atom (Work.EKLC6Core.MCut S O)
        (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) y) := by
  classical
  -- shorthand for the orbit point at time `n`
  set z : X3 := ((fun x : X3 => aDiag t • x)^[n]) y with hz
  -- the point is deep inside the partition at time `n`
  have hdeep : z ∉ shellThin S (C * μ0 ^ n) := by rw [hz]; exact CutGood_deep hy hn
  -- the orbit point is free
  have hfree : z ∈ cutFree U := by rw [hz]; exact CutGood_free hy n
  -- the scale `τ = c μ0ⁿ` is positive, `≤ 1`, and `20 τ ≤ C μ0ⁿ`
  have hμ0nn : (0 : ℝ) ≤ μ0 ^ n := pow_nonneg hμ0.le n
  have hτpos : 0 < c * μ0 ^ n := mul_pos hc (pow_pos hμ0 n)
  have hτle : 20 * (c * μ0 ^ n) ≤ C * μ0 ^ n := by
    calc 20 * (c * μ0 ^ n) = (20 * c) * μ0 ^ n := by ring
      _ ≤ C * μ0 ^ n := mul_le_mul_of_nonneg_right hcm hμ0nn
  have hτle1 : c * μ0 ^ n ≤ 1 := by
    have h1 : 20 * (c * μ0 ^ n) ≤ 1 := le_trans hτle hμ0n
    nlinarith [h1, hτpos]
  -- hence `z` is outside the shell at the (smaller) scale `20 τ`
  have hshell : z ∉ shellThin S (20 * (c * μ0 ^ n)) :=
    fun h => hdeep (shellThin_mono S hτle h)
  -- `u ∈ V (10 ρ)`
  have huV10 : u ∈ V (10 * S.ρ) := fun i j => lt_of_lt_of_le (huV i j) hρn
  -- **crossing lemma**: small `u`-translations do not cross the frontier of a cell
  have hcell : ∀ i : Fin S.N, z ∈ S.cell i → u • z ∈ S.cell i := by
    intro i hzi
    by_contra hnot
    have hfr := mem_VThick_frontier_of_mem_of_not_mem huni (S.hopen i) hτpos hτle1 u huU huV
      (Or.inl ⟨hzi, hnot⟩)
    exact hshell (Or.inl (Set.mem_iUnion.mpr ⟨i, hfr⟩))
  -- **crossing lemma** for the open exceptional piece
  have hbad : z ∈ S.bad → u • z ∈ S.bad := by
    intro hzbad
    by_contra hnot
    have hfr := mem_VThick_frontier_of_mem_of_not_mem huni S.hbad_open hτpos hτle1 u huU huV
      (Or.inl ⟨hzbad, hnot⟩)
    exact hshell (Or.inr hfr)
  -- **the atoms are `u`-invariant on the generating family**
  have hbad_iff : (u • z ∈ S.bad ↔ z ∈ S.bad) := by
    refine ⟨?_, fun h => hbad h⟩
    intro hub
    by_contra hznb
    have hfr := mem_VThick_frontier_of_mem_of_not_mem huni S.hbad_open hτpos hτle1 u huU huV
      (Or.inr ⟨hznb, hub⟩)
    exact hshell (Or.inr hfr)
  have hcell_iff : ∀ (i : Fin S.N) (m : ℕ),
      (u • z ∈ genCell S O i m ↔ z ∈ genCell S O i m) := by
    intro i m
    by_cases hzi : z ∈ S.cell i
    · -- the same cell: the lift transports the pattern
      have h1 : u • z ∈ genCell S O i m ↔ S.lift i (u • z) ∈ sat U (O m) :=
        genCell_mem_iff S O i m (hcell i hzi)
      have h2 : S.lift i (u • z) = u * S.lift i z :=
        S.lift_eq i z hzi hfree (u • z) (hcell i hzi) u huV10 huU rfl
      have h3 : u * S.lift i z ∈ sat U (O m) ↔ S.lift i z ∈ sat U (O m) :=
        mem_sat_mul_iff huU (O m) (S.lift i z)
      have h4 : z ∈ genCell S O i m ↔ S.lift i z ∈ sat U (O m) :=
        genCell_mem_iff S O i m hzi
      simp only [h1, h2, h3, h4]
    · -- a different cell: `u • z` cannot enter (or leave) `cell i`
      have hzng : z ∉ genCell S O i m := fun h => hzi h.2
      have huzng : u • z ∉ genCell S O i m := by
        intro h
        have hfr := mem_VThick_frontier_of_mem_of_not_mem huni (S.hopen i) hτpos hτle1 u huU huV
          (Or.inr ⟨hzi, h.2⟩)
        exact hshell (Or.inl (Set.mem_iUnion.mpr ⟨i, hfr⟩))
      exact ⟨fun h => absurd h huzng, fun h => absurd h hzng⟩
  -- finally, `atom (MCut S O) z` is cut out by the patterns against the generators
  change u • z ∈ atom (MeasurableSpace.generateFrom (famAtom S O)) z
  rw [mem_atom_generateFrom_iff]
  intro A hA
  simp only [famAtom, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hA
  rcases hA with ⟨p, hp⟩ | hb
  · rw [← hp]
    exact hcell_iff p.1 p.2
  · rw [hb]
    exact hbad_iff

end Work.EKLC6Core
