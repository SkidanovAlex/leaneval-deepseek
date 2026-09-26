import Submission.Work.Item3.EnergyStep
import Submission.Work.Item3.OtherRCOverlap

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# EnergyStepGeneral: the cut-slide energy step for *arbitrary* half-length `k`

`Item3/EnergyStep.lean` proves the balanced-side energy step for a
*half-length-1* factor (`w_p = [a] ++ [b]`).  This module removes the `k = 1`
restriction: the same two classical cut-slide transvections work for **every**
half-length `k ≥ 1`, with the *energy comparison* replacing the
letter-rank comparison:

* left neighbour `w_v = X ++ invRev A`, move `w_v ↦ w_v · w_p^δ`
  (`rho`/`rhoNeg`): word `X ++ B`, energy change
  `wordEnergy B − wordEnergy (invRev A)`;
* right neighbour `w_u = invRev B ++ Z`, move `w_u ↦ w_p^δ · w_u`
  (`lam`/`lamNeg`): word `A ++ Z`, energy change
  `wordEnergy A − wordEnergy (invRev B)` (times the positive factor
  `ebase^{|Z|}`).

Both moves preserve `N` in a residual state (needed: `|A| = |B|`, the
balanced-halves hypothesis), exactly as in the `k = 1` case, and each strictly
decreases `eEnergy` under its comparison.  Writing `r`, `s` for the rank
sequences of `A`, `B`, the comparisons read

    `Δ_L < 0  ⟺  s <_lex reverse r`,   `Δ_R < 0  ⟺  r <_lex reverse s`

(*not* one another's negation: for `k ≥ 2` both can fail, e.g. the rank
sequences `r = (2,1)`, `s = (3,1)`).  For `k = 1` the two comparisons are
exactly `lweight b < lweight a` and `lweight a < lweight b`, so exactly one
holds unless the two letters coincide (which is impossible for a basis image,
`PowNoGenerator.sq_ne_of`); this is why `energy_step_k1_cover` needs no
disjunction hypothesis while the general statement below carries it.  In the
machine record the *fallback* moves for the "both fail" cases are the other
transvection orientations and single inversions (`FallTwoRunNotes.md`).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## General word identities (all `k`) -/

/-- `(X ++ invRev A) · (A ++ B) = X ++ B` at the element level — the
general-half-length `rho` atom. -/
lemma mk_invRev_append_mul {n : ℕ} (X A B : List (Fin n × Bool)) :
    FreeGroup.mk (X ++ FreeGroup.invRev A) * FreeGroup.mk (A ++ B) =
      FreeGroup.mk (X ++ B) := by
  have h1 : FreeGroup.mk (X ++ FreeGroup.invRev A) * FreeGroup.mk A = FreeGroup.mk X :=
    mul_mk_app_invRev X A
  have h2 : FreeGroup.mk (A ++ B) = FreeGroup.mk A * FreeGroup.mk B :=
    (FreeGroup.mul_mk (L₁ := A) (L₂ := B)).symm
  rw [h2, ← mul_assoc, h1, FreeGroup.mul_mk]

/-- `(A ++ B) · (invRev B ++ Z) = A ++ Z` at the element level — the
general-half-length `lam` atom. -/
lemma mk_app_invRev_mul {n : ℕ} (A B Z : List (Fin n × Bool)) :
    FreeGroup.mk (A ++ B) * FreeGroup.mk (FreeGroup.invRev B ++ Z) =
      FreeGroup.mk (A ++ Z) := by
  have h1 : FreeGroup.mk B * FreeGroup.mk (FreeGroup.invRev B ++ Z) = FreeGroup.mk Z :=
    mul_mk_append_invRev Z B
  have h2 : FreeGroup.mk (A ++ B) = FreeGroup.mk A * FreeGroup.mk B :=
    (FreeGroup.mul_mk (L₁ := A) (L₂ := B)).symm
  rw [h2, mul_assoc, h1, FreeGroup.mul_mk]

/-- Length bookkeeping: `|X ++ invRev A| = |X| + |A|`. -/
lemma length_append_invRev {α : Type*} [DecidableEq α] (X A : List (α × Bool)) :
    (X ++ FreeGroup.invRev A).length = X.length + A.length := by
  rw [List.length_append, FreeGroup.invRev_length]

/-! ## The two general cut-slide moves -/

/-- **General left cut-slide (`rho` orientation).**  In a residual state, a row
`v` whose word is `X ++ invRev A` and a row `p` whose word is `A ++ B` with
`|A| = |B|`: if the energy of `B` is smaller than the energy of `invRev A`,
then right-composing by `rho v p` preserves `N` and strictly decreases the
state energy.  (`k = 1`: `energy_step_rho`.) -/
theorem energy_step_general_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) B <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (hp : coordWord α p = A ++ B)
    (hv : coordWord α v = X ++ FreeGroup.invRev A) :
    eEnergy (α * rho v p hvp) < eEnergy α ∧ N (α * rho v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev A := hv
  -- the new word of the moved row
  have hel : (α * rho v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ B) := by
    rw [mul_rho_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hv', hp']
    exact mk_invRev_append_mul X A B
  have hW : coordWord (α * rho v p hvp) v = FreeGroup.reduce (X ++ B) := by
    show ((α * rho v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * rho v p hvp) v).length ≤ X.length + B.length := by
    rw [hW]
    calc (FreeGroup.reduce (X ++ B)).length ≤ (X ++ B).length := reduce_length_le _
      _ = X.length + B.length := List.length_append (as := X) (bs := B)
  have hlen0 : (coordWord α v).length = X.length + A.length := by
    rw [hv, length_append_invRev]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rho v p hvp) := hmin.1 v p hvp
  have hNform := N_mul_rho α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) :=
    (N_le_N_mul_rho_iff α v p hvp).mp hNle
  have hge : X.length + A.length ≤ (coordWord (α * rho v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
        (coordWord (α * rho v p hvp) v).length := by
      rw [← mul_rho_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * rho v p hvp) v).length = X.length + A.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rho v p hvp) v = X ++ B := by
    rw [hW]
    refine reduce_eq_of_length_eq (X ++ B) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * rho v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
        X.length + A.length := by
      have hh : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
          (coordWord (α * rho v p hvp) v).length := by
        rw [← mul_rho_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rho α v p hvp (coordWord (α * rho v p hvp) v) rfl
  rw [hWeq, hv] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (X ++ B) <
      wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev A) := by
    rw [wordEnergy_append, wordEnergy_append, FreeGroup.invRev_length, ← hAB]
    exact Nat.add_lt_add_left hE _
  omega

/-- **General right cut-slide (`lam` orientation).**  In a residual state, a row
`u` whose word is `invRev B ++ Z` and a row `p` whose word is `A ++ B` with
`|A| = |B|`: if the energy of `A` is smaller than the energy of `invRev B`,
then right-composing by `lam u p` preserves `N` and strictly decreases the
state energy.  (`k = 1`: `energy_step_lam`.) -/
theorem energy_step_general_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) A <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    (hp : coordWord α p = A ++ B)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z) :
    eEnergy (α * lam u p hup) < eEnergy α ∧ N (α * lam u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Z := hu
  have hel : (α * lam u p hup) (FreeGroup.of u) = FreeGroup.mk (A ++ Z) := by
    rw [mul_lam_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hp', hu']
    exact mk_app_invRev_mul A B Z
  have hW : coordWord (α * lam u p hup) u = FreeGroup.reduce (A ++ Z) := by
    show ((α * lam u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * lam u p hup) u).length ≤ A.length + Z.length := by
    rw [hW]
    calc (FreeGroup.reduce (A ++ Z)).length ≤ (A ++ Z).length := reduce_length_le _
      _ = A.length + Z.length := List.length_append (as := A) (bs := Z)
  have hlen0 : (coordWord α u).length = B.length + Z.length := by
    rw [hu, List.length_append, FreeGroup.invRev_length]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lam u p hup) := hmin.2.2.1 u p hup
  have hNform := N_mul_lam α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) :=
    (N_le_N_mul_lam_iff α u p hup).mp hNle
  have hge : B.length + Z.length ≤ (coordWord (α * lam u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
        (coordWord (α * lam u p hup) u).length := by
      rw [← mul_lam_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * lam u p hup) u).length = B.length + Z.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lam u p hup) u = A ++ Z := by
    rw [hW]
    refine reduce_eq_of_length_eq (A ++ Z) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * lam u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
        B.length + Z.length := by
      have hh : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
          (coordWord (α * lam u p hup) u).length := by
        rw [← mul_lam_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lam α u p hup (coordWord (α * lam u p hup) u) rfl
  rw [hWeq, hu] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (A ++ Z) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ Z) := by
    rw [wordEnergy_append, wordEnergy_append]
    have hpos := pow_ebase_pos (n := n) Z.length
    have hmul : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A <
        (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) :=
      Nat.mul_lt_mul_of_pos_left hE hpos
    omega
  omega

/-! ## The general covering step -/

/-- **General energy step (covering form, all half-lengths).**  In a residual
state, suppose a row `p` has word `A ++ B` with `|A| = |B|`, the row `v` covers
`invRev A` from the right (`coordWord α v = X ++ invRev A`) and the row `u`
covers `invRev B` from the left (`coordWord α u = invRev B ++ Z`).  If one of
the two energy comparisons holds (`wordEnergy B < wordEnergy (invRev A)` or
`wordEnergy A < wordEnergy (invRev B)`), then some elementary transvection in
`AutClosure n` preserves `N` and strictly decreases `eEnergy`.

This is the general-`k` replacement of `energy_step_k1_cover`; the residual
states carrying a balanced configuration with half-length `k ≥ 2` (e.g. the
machine counterexample to `ConjectureKResidual`, see
`Submission/Status.lean`) are handled by this lemma whenever one of the two
comparisons holds (`≍ 91 %` of the machine witnesses); the remaining "both
fail" cases need the fallback moves (inversions / other orientations). -/
theorem energy_step_general_cover {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p)
    (A B X Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (hv : coordWord α v = X ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z)
    (hE : wordEnergy (ebase n) (lweight) B <
        wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ∨
      wordEnergy (ebase n) (lweight) A <
        wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases hE with hE | hE
  · rcases energy_step_general_rho α hres hvp A B X hAB hE hp hv with ⟨hEn, hN⟩
    exact ⟨rho v p hvp, Subgroup.subset_closure (rho_mem_AutGen n hvp), le_of_eq hN, hEn⟩
  · rcases energy_step_general_lam α hres hup A B Z hAB hE hp hu with ⟨hEn, hN⟩
    exact ⟨lam u p hup, Subgroup.subset_closure (lam_mem_AutGen n hup), le_of_eq hN, hEn⟩

end Submission.Nielsen
