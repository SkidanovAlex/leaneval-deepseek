/-
  WilG1 / Plumb / SsetCore.

  The `ε`-`δ` bridge and the unfolding of the construction `Sset` (see `DerivDefs`).

  * `hasDerivAt_iff_epsDeriv` : `HasDerivAt g c a` is the `ε`-`δ` condition `epsDeriv g a c`;
  * `mem_projYSet`, `mem_projDSet` : the two quantified middle stages of `Sset`, in terms of the
    `Fin.append`/`Fin 1` skeleton;
  * `Sset_unfold_aux` : `Sset` is the set of `(x,c)` satisfying the `ε`-`δ` formula with the
    point `y` agreeing with `x` off the coordinate `i`.
-/
import Mathlib
import Submission.Work.WilG1.Plumb.DerivDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical

namespace Work.WilG1.Plumb

open WilkiesDesign WilkiesConjecture

variable {S : WilkiesDesign.SOMin}

/-! ## 1. The `ε`-`δ` characterisation of `HasDerivAt` -/

theorem hasDerivAt_iff_epsDeriv {g : ℝ → ℝ} {a c : ℝ} :
    HasDerivAt g c a ↔ epsDeriv g a c := by
  rw [epsDeriv]
  constructor
  · intro hD ε hε
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at hD
    have hf := Asymptotics.isLittleO_iff.mp hD (c := ε) hε
    rw [Metric.eventually_nhds_iff] at hf
    obtain ⟨δ, hδ, hδ'⟩ := hf
    refine ⟨δ, hδ, fun t ht => ?_⟩
    have h1 := hδ' (by simpa [Real.dist_eq] using ht)
    simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using h1
  · intro H
    rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro e he
    obtain ⟨δ, hδ, hδ'⟩ := H e he
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro t ht
    have h1 := hδ' t (by simpa [Real.dist_eq] using ht)
    simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using h1

/-! ## 2. Reading the `Fin 1`-blocks of an appended point -/

@[simp] theorem eIdxB_append (N : ℕ) (v : Fin (N+1) → ℝ) (e : Fin 1 → ℝ) :
    (Fin.append v e) (eIdxB N) = e 0 := by
  rw [eIdxB, Fin.append_right]

@[simp] theorem dIdxA_append (N : ℕ) (u : Fin (bDim N) → ℝ) (d : Fin 1 → ℝ) :
    (Fin.append u d) (dIdxA N) = d 0 := by
  rw [dIdxA, Fin.append_right]

theorem mem_posESet (N : ℕ) (w : Fin (bDim N) → ℝ) :
    w ∈ posESet N ↔ 0 < w (eIdxB N) := Iff.rfl

theorem mem_posDSet (N : ℕ) (w : Fin (aDim N) → ℝ) :
    w ∈ posDSet N ↔ 0 < w (dIdxA N) := Iff.rfl

theorem mem_projYSet {N : ℕ} (i : Fin N) (f : (Fin N → ℝ) → ℝ) (z : Fin (aDim N) → ℝ) :
    z ∈ projYSet N i f ↔ ∀ r : Fin (N+2) → ℝ, Fin.append z r ∈ innerSet N i f := by
  rw [projYSet, Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists]
  exact forall_congr' fun r => by rw [Set.mem_compl_iff, not_not]

theorem mem_projDSet {N : ℕ} (i : Fin N) (f : (Fin N → ℝ) → ℝ) (u : Fin (bDim N) → ℝ) :
    u ∈ projDSet N i f ↔ ∃ δ : ℝ, 0 < δ ∧
      ∀ r : Fin (N+2) → ℝ,
        Fin.append (Fin.append u (fun _ : Fin 1 => δ)) r ∈ innerSet N i f := by
  rw [projDSet, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, hd1, hd2⟩
    rw [mem_posDSet, dIdxA_append] at hd1
    rw [mem_projYSet] at hd2
    refine ⟨d 0, hd1, fun r => ?_⟩
    have h := hd2 r
    rwa [fin1_ext d] at h
  · rintro ⟨δ, hδ0, hδ⟩
    refine ⟨fun _ : Fin 1 => δ, ?_, ?_⟩
    · rw [mem_posDSet, dIdxA_append]
      exact hδ0
    · rw [mem_projYSet]
      exact hδ

/-! ## 3. Unfolding `Sset` -/

theorem Sset_unfold_aux {N : ℕ} (i : Fin N) (f : (Fin N → ℝ) → ℝ) (v : Fin (N+1) → ℝ) :
    v ∈ Sset N i f ↔ ∀ ε > 0, ∃ δ > 0, ∀ y : Fin N → ℝ, ∀ u w : ℝ,
      asm N (Fin.init v) (v (Fin.last N)) ε δ y u w ∈ innerSet N i f := by
  rw [Sset, Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists]
  constructor
  · intro H ε hε
    have hpos : (Fin.append v (fun _ : Fin 1 => ε)) ∈ posESet N := by
      rw [mem_posESet, eIdxB_append]
      simpa using hε
    have hpd : (Fin.append v (fun _ : Fin 1 => ε)) ∈ projDSet N i f := by
      by_contra hc
      exact H (fun _ : Fin 1 => ε) ⟨hpos, by rwa [Set.mem_compl_iff]⟩
    rw [mem_projDSet] at hpd
    obtain ⟨δ, hδ0, hδ⟩ := hpd
    refine ⟨δ, hδ0, fun y u w => ?_⟩
    have h := hδ (Fin.append y ![u, w])
    simpa [append_asm] using h
  · intro H e hcon
    rw [Set.mem_inter_iff] at hcon
    obtain ⟨hpos, hnot⟩ := hcon
    rw [Set.mem_compl_iff] at hnot
    rw [mem_posESet, eIdxB_append] at hpos
    obtain ⟨δ, hδ0, hδ⟩ := H (e 0) hpos
    rw [mem_projDSet] at hnot
    refine hnot ⟨δ, hδ0, fun r => ?_⟩
    have h := hδ (fun j : Fin N => r (Fin.castAdd 2 j)) (r (Fin.natAdd N (0 : Fin 2)))
      (r (Fin.natAdd N (1 : Fin 2)))
    rw [← append_last_eq r]
    simpa [append_asm] using h

end Work.WilG1.Plumb
