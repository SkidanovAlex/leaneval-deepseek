import Submission.Work.Item3.EnergyStepGeneral

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# EnergyStepGeneralMinus: the cut-slide energy step in the *negative*
orientation, for arbitrary half-length `k`

`Item3/EnergyStepGeneral.lean` proves the general-`k` cut-slide step for a
neighbour whose *coordinate* word carries the covered half verbatim
(`coordWord α v = X ++ invRev A`, `coordWord α u = invRev B ++ Z`).
When a neighbour's coordinate word is instead the *inverse* of the
aggregate factor word (`coordWord α v = A ++ invRev X` for a factor word
`X ++ invRev A`, resp. `coordWord α u = invRev Z ++ B` for a factor word
`invRev B ++ Z`) the classical cut-slide is realised by a *left* transvection
(`lam`/`lamNeg`) resp. a `rho`/`rhoNeg` with the inverted multiplier — exactly
as in the half-length-1 lemmas `energy_Lminus`/`energy_Rminus` of
`Item3/EnergyBridge.lean`.  This module removes the `k = 1` restriction there.

The four word atoms (`mk_lamNeg_general`, `mk_lam_general`,
`mk_rho_general`, `mk_rhoNeg_general`) say that the neighbour's new coordinate
word is `invRev B ++ invRev X` (left) resp. `invRev Z ++ invRev A` (right),
i.e. `invRev` of the *new factor word* `X ++ B` resp. `A ++ Z`.

The energy comparisons become

* left neighbour:  `wordEnergy (invRev B) < wordEnergy A`;
* right neighbour: `wordEnergy (invRev A) < wordEnergy B`

(both times the common prefix `invRev Z`/`invRev X` contributes the same
positive multiple and cancels).  These are the *complementary* comparisons to
those of `EnergyStepGeneral` (`Δ_R > 0` resp. `Δ_L > 0`), which together with
the `+`-orientation moves give the full four-way classical cut-slide.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## The four word atoms -/

/-- `(mk (A ++ B))⁻¹ · mk (A ++ invRev X) = mk (invRev B ++ invRev X)`: the
general-half-length `lamNeg` atom (left neighbour, balanced row `+`). -/
lemma mk_lamNeg_general {n : ℕ} (A B X : List (Fin n × Bool)) :
    (FreeGroup.mk (A ++ B))⁻¹ * FreeGroup.mk (A ++ FreeGroup.invRev X) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
  have h1 : (FreeGroup.mk (A ++ B))⁻¹ = FreeGroup.mk (FreeGroup.invRev (A ++ B)) :=
    FreeGroup.inv_mk
  rw [h1, FreeGroup.invRev_append, mk_mul_eq (FreeGroup.invRev B) (FreeGroup.invRev A),
    mul_assoc, mul_mk_invRev_prefix (P := FreeGroup.invRev X) (L := A)]
  exact (mk_mul_eq (FreeGroup.invRev B) (FreeGroup.invRev X)).symm

/-- `mk (invRev B ++ invRev A) · mk (A ++ invRev X) = mk (invRev B ++ invRev X)`:
the general-half-length `lam` atom (left neighbour, balanced row `-`). -/
lemma mk_lam_general {n : ℕ} (A B X : List (Fin n × Bool)) :
    FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev A) *
        FreeGroup.mk (A ++ FreeGroup.invRev X) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
  rw [mk_mul_eq (FreeGroup.invRev B) (FreeGroup.invRev A), mul_assoc,
    mul_mk_invRev_prefix (P := FreeGroup.invRev X) (L := A)]
  exact (mk_mul_eq (FreeGroup.invRev B) (FreeGroup.invRev X)).symm

/-- `mk B · mk (invRev B) = 1`. -/
lemma mk_invRev_mul_self' {n : ℕ} (B : List (Fin n × Bool)) :
    FreeGroup.mk B * FreeGroup.mk (FreeGroup.invRev B) = 1 := by
  have h := mul_mk_append_invRev (P := ([] : List (Fin n × Bool))) (L := B)
  rw [List.append_nil] at h
  exact h

/-- `mk (invRev Z ++ B) · mk (invRev B ++ invRev A) = mk (invRev Z ++ invRev A)`:
the general-half-length `rho` atom (right neighbour, balanced row `-`). -/
lemma mk_rho_general {n : ℕ} (A B Z : List (Fin n × Bool)) :
    FreeGroup.mk (FreeGroup.invRev Z ++ B) *
        FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev A) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
  rw [mk_mul_eq (FreeGroup.invRev Z) B, mk_mul_eq (FreeGroup.invRev B) (FreeGroup.invRev A)]
  rw [show FreeGroup.mk (FreeGroup.invRev Z) * FreeGroup.mk B *
          (FreeGroup.mk (FreeGroup.invRev B) * FreeGroup.mk (FreeGroup.invRev A))
      = FreeGroup.mk (FreeGroup.invRev Z) *
          (FreeGroup.mk B * FreeGroup.mk (FreeGroup.invRev B)) *
          FreeGroup.mk (FreeGroup.invRev A) from by
        rw [mul_assoc, mul_assoc, mul_assoc]]
  rw [mk_invRev_mul_self' B, mul_one]
  exact (mk_mul_eq (FreeGroup.invRev Z) (FreeGroup.invRev A)).symm

/-- `mk (invRev Z ++ B) · (mk (A ++ B))⁻¹ = mk (invRev Z ++ invRev A)`: the
general-half-length `rhoNeg` atom (right neighbour, balanced row `+`). -/
lemma mk_rhoNeg_general {n : ℕ} (A B Z : List (Fin n × Bool)) :
    FreeGroup.mk (FreeGroup.invRev Z ++ B) * (FreeGroup.mk (A ++ B))⁻¹ =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
  have h1 : (FreeGroup.mk (A ++ B))⁻¹ = FreeGroup.mk (FreeGroup.invRev (A ++ B)) :=
    FreeGroup.inv_mk
  rw [h1, FreeGroup.invRev_append]
  exact mk_rho_general A B Z

/-- Length bookkeeping: `|invRev A ++ invRev B| = |A| + |B|`. -/
lemma length_invRev_invRev {α : Type*} [DecidableEq α] (A B : List (α × Bool)) :
    (FreeGroup.invRev A ++ FreeGroup.invRev B).length = A.length + B.length := by
  simp [List.length_append, FreeGroup.invRev_length]

/-- Length bookkeeping: `|invRev A ++ B| = |A| + |B|`. -/
lemma length_invRev_append {α : Type*} [DecidableEq α] (A B : List (α × Bool)) :
    (FreeGroup.invRev A ++ B).length = A.length + B.length := by
  simp [List.length_append, FreeGroup.invRev_length]

/-- Length bookkeeping: `|A ++ invRev B| = |A| + |B|`. -/
lemma length_append_invRev' {α : Type*} [DecidableEq α] (A B : List (α × Bool)) :
    (A ++ FreeGroup.invRev B).length = A.length + B.length := by
  simp [List.length_append, FreeGroup.invRev_length]

/-! ## The two left-neighbour moves -/

/-- **General left cut-slide, `lamNeg` orientation.**  In a residual state, a
row `v` whose word is `A ++ invRev X` (the inverse of the aggregate factor word
`X ++ invRev A`) and a row `p` whose word is `A ++ B` with `|A| = |B|`: if
`wordEnergy (invRev B) < wordEnergy A` then right-composing by `lamNeg v p`
preserves `N` and strictly decreases the state energy. -/
theorem energy_step_general_lamNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
      wordEnergy (ebase n) (lweight) A)
    (hp : coordWord α p = A ++ B)
    (hv : coordWord α v = A ++ FreeGroup.invRev X) :
    eEnergy (α * lamNeg v p hvp) < eEnergy α ∧ N (α * lamNeg v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hv' : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := hv
  have hel : (α * lamNeg v p hvp) (FreeGroup.of v) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    rw [mul_lamNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv']
    exact mk_lamNeg_general A B X
  have hW : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    show ((α * lamNeg v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * lamNeg v p hvp) v).length ≤ B.length + X.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev B ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = B.length + X.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α v).length = A.length + X.length := by
    rw [hv, length_append_invRev']
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lamNeg v p hvp) := hmin.2.2.2 v p hvp
  have hNform := N_mul_lamNeg α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) :=
    (N_le_N_mul_lamNeg_iff α v p hvp).mp hNle
  have hge : A.length + X.length ≤ (coordWord (α * lamNeg v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        (coordWord (α * lamNeg v p hvp) v).length := by
      rw [← mul_lamNeg_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * lamNeg v p hvp) v).length = A.length + X.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.invRev B ++ FreeGroup.invRev X := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, hAB]
    exact (length_invRev_invRev B X).symm
  have hNeq : N (α * lamNeg v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        A.length + X.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
          (coordWord (α * lamNeg v p hvp) v).length := by
        rw [← mul_lamNeg_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lamNeg α v p hvp (coordWord (α * lamNeg v p hvp) v) rfl
  rw [hWeq, hv] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev X) <
      wordEnergy (ebase n) (lweight) (A ++ FreeGroup.invRev X) := by
    have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev X)
        = (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
      rw [wordEnergy_append, FreeGroup.invRev_length]
    have e2 : wordEnergy (ebase n) (lweight) (A ++ FreeGroup.invRev X)
        = (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
          + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
      rw [wordEnergy_append, FreeGroup.invRev_length]
    rw [e1, e2]
    have hpos := pow_ebase_pos (n := n) X.length
    have hmul : (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
        (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A :=
      Nat.mul_lt_mul_of_pos_left hE hpos
    omega
  omega

/-- **General left cut-slide, `lam` orientation.**  Same as
`energy_step_general_lamNeg` but with the balanced row in the negative
orientation (`coordWord α p = invRev B ++ invRev A`), where the appropriate
left transvection is `lam v p`. -/
theorem energy_step_general_lam_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
      wordEnergy (ebase n) (lweight) A)
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = A ++ FreeGroup.invRev X) :
    eEnergy (α * lam v p hvp) < eEnergy α ∧ N (α * lam v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hv' : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := hv
  have hel : (α * lam v p hvp) (FreeGroup.of v) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    rw [mul_lam_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv']
    exact mk_lam_general A B X
  have hW : coordWord (α * lam v p hvp) v =
      FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    show ((α * lam v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * lam v p hvp) v).length ≤ B.length + X.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev B ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = B.length + X.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α v).length = A.length + X.length := by
    rw [hv, length_append_invRev']
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lam v p hvp) := hmin.2.2.1 v p hvp
  have hNform := N_mul_lam α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of p)) * α (FreeGroup.of v)) :=
    (N_le_N_mul_lam_iff α v p hvp).mp hNle
  have hge : A.length + X.length ≤ (coordWord (α * lam v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        (coordWord (α * lam v p hvp) v).length := by
      rw [← mul_lam_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * lam v p hvp) v).length = A.length + X.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lam v p hvp) v =
      FreeGroup.invRev B ++ FreeGroup.invRev X := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, hAB]
    exact (length_invRev_invRev B X).symm
  have hNeq : N (α * lam v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        A.length + X.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
          (coordWord (α * lam v p hvp) v).length := by
        rw [← mul_lam_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lam α v p hvp (coordWord (α * lam v p hvp) v) rfl
  rw [hWeq, hv] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev X) <
      wordEnergy (ebase n) (lweight) (A ++ FreeGroup.invRev X) := by
    have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev X)
        = (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
      rw [wordEnergy_append, FreeGroup.invRev_length]
    have e2 : wordEnergy (ebase n) (lweight) (A ++ FreeGroup.invRev X)
        = (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
          + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
      rw [wordEnergy_append, FreeGroup.invRev_length]
    rw [e1, e2]
    have hpos := pow_ebase_pos (n := n) X.length
    have hmul : (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
        (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A :=
      Nat.mul_lt_mul_of_pos_left hE hpos
    omega
  omega

/-! ## The two right-neighbour moves -/

/-- **General right cut-slide, `rhoNeg` orientation.**  In a residual state, a
row `u` whose word is `invRev Z ++ B` (the inverse of the aggregate factor word
`invRev B ++ Z`) and a row `p` whose word is `A ++ B` with `|A| = |B|`: if
`wordEnergy (invRev A) < wordEnergy B` then right-composing by `rhoNeg u p`
preserves `N` and strictly decreases the state energy. -/
theorem energy_step_general_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
      wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = A ++ B)
    (hu : coordWord α u = FreeGroup.invRev Z ++ B) :
    eEnergy (α * rhoNeg u p hup) < eEnergy α ∧ N (α * rhoNeg u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := hu
  have hel : (α * rhoNeg u p hup) (FreeGroup.of u) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    rw [mul_rhoNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    exact mk_rhoNeg_general A B Z
  have hW : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    show ((α * rhoNeg u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * rhoNeg u p hup) u).length ≤ Z.length + A.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A)).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev A).length := reduce_length_le _
      _ = Z.length + A.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α u).length = Z.length + B.length := by
    rw [hu, length_invRev_append]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rhoNeg u p hup) := hmin.2.1 u p hup
  have hNform := N_mul_rhoNeg α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) :=
    (N_le_N_mul_rhoNeg_iff α u p hup).mp hNle
  have hge : Z.length + B.length ≤ (coordWord (α * rhoNeg u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg u p hup) u).length := by
      rw [← mul_rhoNeg_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * rhoNeg u p hup) u).length = Z.length + B.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.invRev Z ++ FreeGroup.invRev A := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, length_invRev_invRev, hAB]
  have hNeq : N (α * rhoNeg u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        Z.length + B.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
          (coordWord (α * rhoNeg u p hup) u).length := by
        rw [← mul_rhoNeg_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rhoNeg α u p hup (coordWord (α * rhoNeg u p hup) u) rfl
  rw [hWeq, hu] at hEu
  have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev A)
      = (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) := by
    rw [wordEnergy_append, FreeGroup.invRev_length]
  have e2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ B)
      = (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) B := by
    rw [wordEnergy_append]
  have hcmp : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev A) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ B) := by
    rw [e1, e2, hAB]
    have hpos := pow_ebase_pos (n := n) B.length
    have hmul : (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
        (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) B :=
      Nat.mul_lt_mul_of_pos_left hE hpos
    omega
  omega

/-- **General right cut-slide, `rho` orientation.**  Same as
`energy_step_general_rhoNeg` but with the balanced row in the negative
orientation (`coordWord α p = invRev B ++ invRev A`), where the appropriate
transvection is `rho u p`. -/
theorem energy_step_general_rho_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
      wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev Z ++ B) :
    eEnergy (α * rho u p hup) < eEnergy α ∧ N (α * rho u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := hu
  have hel : (α * rho u p hup) (FreeGroup.of u) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    rw [mul_rho_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    exact mk_rho_general A B Z
  have hW : coordWord (α * rho u p hup) u =
      FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    show ((α * rho u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * rho u p hup) u).length ≤ Z.length + A.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A)).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev A).length := reduce_length_le _
      _ = Z.length + A.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α u).length = Z.length + B.length := by
    rw [hu, length_invRev_append]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rho u p hup) := hmin.1 u p hup
  have hNform := N_mul_rho α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of u) * α (FreeGroup.of p)) :=
    (N_le_N_mul_rho_iff α u p hup).mp hNle
  have hge : Z.length + B.length ≤ (coordWord (α * rho u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        (coordWord (α * rho u p hup) u).length := by
      rw [← mul_rho_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * rho u p hup) u).length = Z.length + B.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rho u p hup) u =
      FreeGroup.invRev Z ++ FreeGroup.invRev A := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, length_invRev_invRev, hAB]
  have hNeq : N (α * rho u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        Z.length + B.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
          (coordWord (α * rho u p hup) u).length := by
        rw [← mul_rho_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rho α u p hup (coordWord (α * rho u p hup) u) rfl
  rw [hWeq, hu] at hEu
  have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev A)
      = (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) := by
    rw [wordEnergy_append, FreeGroup.invRev_length]
  have e2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ B)
      = (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) B := by
    rw [wordEnergy_append]
  have hcmp : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev A) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ B) := by
    rw [e1, e2, hAB]
    have hpos := pow_ebase_pos (n := n) B.length
    have hmul : (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
        (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) B :=
      Nat.mul_lt_mul_of_pos_left hE hpos
    omega
  omega

/-! ## The two sign-parametrized covering forms -/

/-- **General left-neighbour energy move (negative orientation).**  The
balanced row's word is `A ++ B` (sign `true`) or `invRev B ++ invRev A`
(sign `false`); the left neighbour's coordinate word is `A ++ invRev X`.  If
`wordEnergy (invRev B) < wordEnergy A` then a single left transvection in
`AutClosure n` keeps `N` and strictly decreases the energy. -/
theorem energy_general_Lminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length) (s : Bool)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
      wordEnergy (ebase n) (lweight) A)
    (hp : coordWord α p = if s then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = A ++ FreeGroup.invRev X) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  cases s
  · simp only [Bool.false_eq_true, if_false] at hp
    rcases energy_step_general_lam_minus α hres hvp A B X hAB hE hp hv with ⟨hE', hN⟩
    exact ⟨lam v p hvp, Subgroup.subset_closure (lam_mem_AutGen n hvp), le_of_eq hN, hE'⟩
  · simp only [if_true] at hp
    rcases energy_step_general_lamNeg α hres hvp A B X hAB hE hp hv with ⟨hE', hN⟩
    exact ⟨lamNeg v p hvp,
      Subgroup.subset_closure (lamNeg_mem_AutGen n (i := p) (j := v) (fun h => hvp h.symm)),
      le_of_eq hN, hE'⟩

/-- **General right-neighbour energy move (negative orientation).**  The
balanced row's word is `A ++ B` (sign `true`) or `invRev B ++ invRev A`
(sign `false`); the right neighbour's coordinate word is `invRev Z ++ B`.  If
`wordEnergy (invRev A) < wordEnergy B` then a single transvection in
`AutClosure n` keeps `N` and strictly decreases the energy. -/
theorem energy_general_Rminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length) (s : Bool)
    (hE : wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
      wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = if s then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev Z ++ B) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  cases s
  · simp only [Bool.false_eq_true, if_false] at hp
    rcases energy_step_general_rho_minus α hres hup A B Z hAB hE hp hu with ⟨hE', hN⟩
    exact ⟨rho u p hup, Subgroup.subset_closure (rho_mem_AutGen n hup), le_of_eq hN, hE'⟩
  · simp only [if_true] at hp
    rcases energy_step_general_rhoNeg α hres hup A B Z hAB hE hp hu with ⟨hE', hN⟩
    exact ⟨rhoNeg u p hup, Subgroup.subset_closure (rhoNeg_mem_AutGen n hup), le_of_eq hN, hE'⟩


/-! ## The two "balanced-row-inverted" plus-orientation cut-slides -/

/-- `mk (invRev B ++ invRev A) = (mk (A ++ B))⁻¹`: the general-half-length
inverse-pair atom. -/
lemma mk_invRev_pair_general {n : ℕ} (A B : List (Fin n × Bool)) :
    FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev A) =
      (FreeGroup.mk (A ++ B))⁻¹ := by
  rw [← FreeGroup.invRev_append]
  exact FreeGroup.inv_mk.symm

theorem energy_step_general_rhoNeg_bal {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) B <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = X ++ FreeGroup.invRev A) :
    eEnergy (α * rhoNeg v p hvp) < eEnergy α ∧ N (α * rhoNeg v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk (A ++ B) := by
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    rw [mk_invRev_pair_general, inv_inv]
  have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev A := hv
  -- the new word of the moved row
  have hel : (α * rhoNeg v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ B) := by
    rw [mul_rhoNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv', hwp]
    exact mk_invRev_append_mul X A B
  have hW : coordWord (α * rhoNeg v p hvp) v = FreeGroup.reduce (X ++ B) := by
    show ((α * rhoNeg v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * rhoNeg v p hvp) v).length ≤ X.length + B.length := by
    rw [hW]
    calc (FreeGroup.reduce (X ++ B)).length ≤ (X ++ B).length := reduce_length_le _
      _ = X.length + B.length := List.length_append (as := X) (bs := B)
  have hlen0 : (coordWord α v).length = X.length + A.length := by
    rw [hv, length_append_invRev]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rhoNeg v p hvp) := hmin.2.1 v p hvp
  have hNform := N_mul_rhoNeg α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) :=
    (N_le_N_mul_rhoNeg_iff α v p hvp).mp hNle
  have hge : X.length + A.length ≤ (coordWord (α * rhoNeg v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg v p hvp) v).length := by
      rw [← mul_rhoNeg_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * rhoNeg v p hvp) v).length = X.length + A.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rhoNeg v p hvp) v = X ++ B := by
    rw [hW]
    refine reduce_eq_of_length_eq (X ++ B) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * rhoNeg v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        X.length + A.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
          (coordWord (α * rhoNeg v p hvp) v).length := by
        rw [← mul_rhoNeg_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rhoNeg α v p hvp (coordWord (α * rhoNeg v p hvp) v) rfl
  rw [hWeq, hv] at hEu
  have hcmp : wordEnergy (ebase n) (lweight) (X ++ B) <
      wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev A) := by
    rw [wordEnergy_append, wordEnergy_append, FreeGroup.invRev_length, ← hAB]
    exact Nat.add_lt_add_left hE _
  omega


theorem energy_step_general_lamNeg_bal {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) A <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z) :
    eEnergy (α * lamNeg u p hup) < eEnergy α ∧ N (α * lamNeg u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk (A ++ B) := by
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    rw [mk_invRev_pair_general, inv_inv]
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Z := hu
  have hel : (α * lamNeg u p hup) (FreeGroup.of u) = FreeGroup.mk (A ++ Z) := by
    rw [mul_lamNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu', hwp]
    exact mk_app_invRev_mul A B Z
  have hW : coordWord (α * lamNeg u p hup) u = FreeGroup.reduce (A ++ Z) := by
    show ((α * lamNeg u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * lamNeg u p hup) u).length ≤ A.length + Z.length := by
    rw [hW]
    calc (FreeGroup.reduce (A ++ Z)).length ≤ (A ++ Z).length := reduce_length_le _
      _ = A.length + Z.length := List.length_append (as := A) (bs := Z)
  have hlen0 : (coordWord α u).length = B.length + Z.length := by
    rw [hu, List.length_append, FreeGroup.invRev_length]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lamNeg u p hup) := hmin.2.2.2 u p hup
  have hNform := N_mul_lamNeg α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) :=
    (N_le_N_mul_lamNeg_iff α u p hup).mp hNle
  have hge : B.length + Z.length ≤ (coordWord (α * lamNeg u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        (coordWord (α * lamNeg u p hup) u).length := by
      rw [← mul_lamNeg_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * lamNeg u p hup) u).length = B.length + Z.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lamNeg u p hup) u = A ++ Z := by
    rw [hW]
    refine reduce_eq_of_length_eq (A ++ Z) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * lamNeg u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        B.length + Z.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
          (coordWord (α * lamNeg u p hup) u).length := by
        rw [← mul_lamNeg_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lamNeg α u p hup (coordWord (α * lamNeg u p hup) u) rfl
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


end Submission.Nielsen
