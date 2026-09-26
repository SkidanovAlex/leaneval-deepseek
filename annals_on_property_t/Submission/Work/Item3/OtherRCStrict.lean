import Submission.Work.Item3.OtherRCOverlap
import Submission.Work.NielsenEndCancel

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# OtherRCStrict: state-level strict closure drops for the OTHER-rc shapes

Each `OtherRCShape` constructor (`Item3/OtherRCOverlap.lean`) is a word
identity between the rc-coverer `u` and its strict-move partner `v`; this
module wraps those identities in the state-level `N` bookkeeping
(`end_cancel_shortens` + the `N_mul_*` formulas), producing the
`∃ γ ∈ AutClosure n, N (α * γ) < N α` shape of `otherRC_forces_strict`
(U1b, `UnchangedLow.lean`).

Formalised constructors (each a template of the others):

* `begTelescopeRight_strict`    — `W_u = [z] ++ invRev W_v`: `rho u v`
  telescopes `w_u·w_v` to the single letter `z`;
* `begTelescopeInvRight_strict` — `W_u = [z] ++ W_v`: `rhoNeg u v`
  telescopes `w_u·w_v⁻¹` to the single letter `z`;
* `prefixOverlap_strict`        — `W_v = invRev W_u ++ S`: `rho u v`
  shortens `w_u` to at most `|S|`;
* `covererExtendsPartner_strict`— `W_u = W_v ++ S`: `lamNeg u v`
  shortens `w_u` to at most `|S|`;
* `partnerExtendsCoverer_strict`— `W_v = W_u ++ S`: `lamNeg u v`
  shortens `w_u` to at most `|S|`;
* `covererPairOverlap_strict`   — `W_u = P ++ [y]`, `W_v = P ++ S ++ [y]`
  (two rc-coverers sharing a prefix): `lamNeg u v` shortens `w_u` to at
  most `|S| + 2` (`mul_mk_invRev_shared_prefix`);
* `boundaryZipper_strict`       — `W_u = X_a ++ Z`, `W_v = invRev Z ++ X_b`
  (the suffix of one row inverse-reverses into the prefix of the other):
  `rho u v` shortens `w_u` by the matched boundary block
  (`mul_mk_zipper`), whenever `|W_v| < 2|Z|`.

Each requires only the word identity, the coordinate distinctness `u ≠ v`,
and the length bound `|S| < |w_u|` (resp. `2 ≤ |w_u|` for the single-letter
shapes).  All kernel-checked; axioms `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **`begTelescopeRight` forces a strict closure drop.**  If the image of
coordinate `u` has word `[z] ++ invRev W_v` (the coverer begins with the
letter `z` and continues with the inverse-reversal of coordinate `v`'s
word) and `|w_u| ≥ 2`, then right composition by the elementary transvection
`rho u v` strictly lowers `N`: the product `w_u · w_v` telescopes to the
single letter `z` (`mul_mk_app_invRev`).  This is the state-level content of
the `begTelescopeRight` constructor of the OTHER-rc taxonomy. -/
theorem begTelescopeRight_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (z : Fin n × Bool)
    (hu : (α (FreeGroup.of u)).toWord =
      [z] ++ FreeGroup.invRev ((α (FreeGroup.of v)).toWord))
    (hlen2 : 2 ≤ FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  left
  have htw : ((α (FreeGroup.of u)) * (α (FreeGroup.of v))).toWord = [z] := by
    rw [FreeGroup.toWord_mul]
    rw [hu]
    rw [List.append_assoc]
    rw [← FreeGroup.reduce_append_reduce_reduce (L₁ := [z])
      (L₂ := FreeGroup.invRev ((α (FreeGroup.of v)).toWord) ++ (α (FreeGroup.of v)).toWord)]
    rw [FreeGroup.reduce_invRev_left_cancel]
    simp
  have hprod : FreeGroup.norm (α (FreeGroup.of u) * α (FreeGroup.of v)) = 1 := by
    unfold FreeGroup.norm
    rw [htw]
    simp
  rw [hprod]
  omega

/-- **`begTelescopeInvRight` forces a strict closure drop.**  If
`W_u = [z] ++ W_v` (coverer begins with `z` and continues with the partner's
own word), the product `w_u · w_v⁻¹` telescopes to `z`, so `rhoNeg u v`
strictly lowers `N`. -/
theorem begTelescopeInvRight_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (z : Fin n × Bool)
    (hu : (α (FreeGroup.of u)).toWord =
      [z] ++ (α (FreeGroup.of v)).toWord)
    (hlen2 : 2 ≤ FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  left
  have htw : ((α (FreeGroup.of u)) * (α (FreeGroup.of v))⁻¹).toWord = [z] := by
    rw [FreeGroup.toWord_mul]
    rw [FreeGroup.toWord_inv]
    rw [hu]
    rw [List.append_assoc]
    rw [← FreeGroup.reduce_append_reduce_reduce (L₁ := [z])
      (L₂ := (α (FreeGroup.of v)).toWord ++ FreeGroup.invRev ((α (FreeGroup.of v)).toWord))]
    rw [reduce_append_invRev_right ((α (FreeGroup.of v)).toWord)]
    simp
  have hprod : FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of v))⁻¹) = 1 := by
    unfold FreeGroup.norm
    rw [htw]
    simp
  rw [hprod]
  omega

/-- **`prefixOverlap` forces a strict closure drop.**  If
`W_v = invRev W_u ++ S` (the partner begins with the inverse-reversal of the
coverer's word), the product `w_u · w_v` reduces to `reduce S`, so `rho u v`
strictly lowers `N` whenever `|S| < |w_u|`. -/
theorem prefixOverlap_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (S : List (Fin n × Bool))
    (hv : (α (FreeGroup.of v)).toWord =
      FreeGroup.invRev ((α (FreeGroup.of u)).toWord) ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  left
  have hle : FreeGroup.norm (α (FreeGroup.of u) * α (FreeGroup.of v)) ≤ S.length := by
    have htw : ((α (FreeGroup.of u)) * (α (FreeGroup.of v))).toWord = FreeGroup.reduce S := by
      rw [FreeGroup.toWord_mul]
      rw [hv]
      rw [← List.append_assoc]
      rw [← FreeGroup.reduce_append_reduce_reduce
        (L₁ := (α (FreeGroup.of u)).toWord ++ FreeGroup.invRev ((α (FreeGroup.of u)).toWord)) (L₂ := S)]
      rw [reduce_append_invRev_right ((α (FreeGroup.of u)).toWord)]
      simp
    unfold FreeGroup.norm
    rw [htw]
    exact reduce_length_le S
  exact lt_of_le_of_lt hle hshort

/-- **`covererExtendsPartner` forces a strict closure drop.**  If
`W_u = W_v ++ S` (the coverer is the partner's word followed by `S`), the
product `w_v⁻¹ · w_u` reduces to `reduce S`, so `lamNeg u v` strictly lowers
`N` whenever `|S| < |w_u|`. -/
theorem covererExtendsPartner_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (S : List (Fin n × Bool))
    (hu : (α (FreeGroup.of u)).toWord =
      (α (FreeGroup.of v)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  right
  left
  have hle : FreeGroup.norm ((α (FreeGroup.of v))⁻¹ * α (FreeGroup.of u)) ≤ S.length := by
    have htw : ((α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of u))).toWord = FreeGroup.reduce S := by
      rw [FreeGroup.toWord_mul]
      rw [FreeGroup.toWord_inv]
      rw [hu]
      rw [← List.append_assoc]
      rw [← FreeGroup.reduce_append_reduce_reduce
        (L₁ := FreeGroup.invRev ((α (FreeGroup.of v)).toWord) ++ (α (FreeGroup.of v)).toWord) (L₂ := S)]
      rw [FreeGroup.reduce_invRev_left_cancel]
      simp
    unfold FreeGroup.norm
    rw [htw]
    exact reduce_length_le S
  exact lt_of_le_of_lt hle hshort

/-- **`partnerExtendsCoverer` forces a strict closure drop.**  If
`W_v = W_u ++ S` (the partner is the coverer's word followed by `S`), the
product `w_v⁻¹ · w_u` reduces to `reduce (invRev S)`, so `lamNeg u v`
strictly lowers `N` whenever `|S| < |w_u|`. -/
theorem partnerExtendsCoverer_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (S : List (Fin n × Bool))
    (hv : (α (FreeGroup.of v)).toWord =
      (α (FreeGroup.of u)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  right
  left
  have hle : FreeGroup.norm ((α (FreeGroup.of v))⁻¹ * α (FreeGroup.of u)) ≤ S.length := by
    have htw : ((α (FreeGroup.of v))⁻¹ * (α (FreeGroup.of u))).toWord =
        FreeGroup.reduce (FreeGroup.invRev S) := by
      rw [FreeGroup.toWord_mul]
      rw [FreeGroup.toWord_inv]
      rw [hv]
      rw [FreeGroup.invRev_append]
      rw [List.append_assoc]
      rw [← FreeGroup.reduce_append_reduce_reduce
        (L₁ := FreeGroup.invRev S)
        (L₂ := FreeGroup.invRev ((α (FreeGroup.of u)).toWord) ++ (α (FreeGroup.of u)).toWord)]
      rw [FreeGroup.reduce_invRev_left_cancel]
      simp
    unfold FreeGroup.norm
    rw [htw]
    calc
      (FreeGroup.reduce (FreeGroup.invRev S)).length ≤ (FreeGroup.invRev S).length :=
        reduce_length_le (FreeGroup.invRev S)
      _ = S.length := FreeGroup.invRev_length
  exact lt_of_le_of_lt hle hshort


/-- **`covererPairOverlap` forces a strict closure drop.**  If two rows
share a prefix `P` and end with the same letter `y`, the second carrying an
extra block `S` (`W_u = P ++ [y]`, `W_v = P ++ S ++ [y]`), the product
`w_v⁻¹ · w_u` reduces to `invRev [y] ++ invRev S ++ [y]` of length at most
`|S| + 2` (`mul_mk_invRev_shared_prefix`), so `lamNeg u v` strictly lowers
`N` whenever `3 < |w_u|`.  This is the sixth constructor of the OTHER-rc
taxonomy (n = 4 volume: 3 of 49 OTHER-rc posts; e.g. post
`[dBab, dBaab, Ab, dc]` with rows `dBab`, `dBaab` both ending in `y = b`). -/
theorem covererPairOverlap_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v) (P S : List (Fin n × Bool)) (y : Fin n × Bool)
    (hu : (α (FreeGroup.of u)).toWord = P ++ [y])
    (hv : (α (FreeGroup.of v)).toWord = P ++ S ++ [y])
    (hshort : S.length + 2 < FreeGroup.norm (α (FreeGroup.of u))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  right
  left
  have htw : (((α (FreeGroup.of v))⁻¹) * (α (FreeGroup.of u))).toWord =
      FreeGroup.reduce (FreeGroup.invRev [y] ++ FreeGroup.invRev S ++ [y]) := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv, hv, hu]
    exact FreeGroup.reduce.sound (mul_mk_invRev_shared_prefix P S y)
  have hle : FreeGroup.norm (((α (FreeGroup.of v))⁻¹) * (α (FreeGroup.of u))) ≤
      S.length + 2 := by
    unfold FreeGroup.norm
    rw [htw]
    calc
      (FreeGroup.reduce (FreeGroup.invRev [y] ++ FreeGroup.invRev S ++ [y])).length
          ≤ (FreeGroup.invRev [y] ++ FreeGroup.invRev S ++ [y]).length :=
            reduce_length_le (FreeGroup.invRev [y] ++ FreeGroup.invRev S ++ [y])
      _ = S.length + 2 := by
            simp only [List.length_append, FreeGroup.invRev_length, List.length_singleton]
            omega
  exact lt_of_le_of_lt hle hshort


/-- **`boundaryZipper` forces a strict closure drop.**  If the suffix `Z` of
`u`'s word is the inverse-reversal of the prefix of `v`'s word
(`W_u = X_a ++ Z`, `W_v = invRev Z ++ X_b`), the product `w_u · w_v` reduces
to `reduce (X_a ++ X_b)` (`mul_mk_zipper`), of length at most
`|X_a| + |X_b| = |W_u| + |W_v| - 2|Z|`, so `rho u v` strictly lowers `N`
whenever `|W_v| < 2|Z|`.  This is the seventh constructor of the OTHER-rc
taxonomy (the third n=4 uncovered trace `['Ca','dB','ACaD','dAcca']`: the
suffix `D a C` of `ACaD` zippers into the prefix `d A c` of `dAcca`, with
`ACaD · dAcca = Aca`). -/
theorem boundaryZipper_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (u v : Fin n) (huv : u ≠ v)
    (Xa Xb Z : List (Fin n × Bool))
    (hu : (α (FreeGroup.of u)).toWord = Xa ++ Z)
    (hv : (α (FreeGroup.of v)).toWord = FreeGroup.invRev Z ++ Xb)
    (hshort : (α (FreeGroup.of v)).toWord.length < 2 * Z.length) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  apply end_cancel_shortens n α (i := u) (j := v) huv
  right
  left
  have htw : (α (FreeGroup.of u) * α (FreeGroup.of v)).toWord =
      FreeGroup.reduce (Xa ++ Xb) := by
    rw [FreeGroup.toWord_mul, hu, hv]
    exact FreeGroup.reduce.sound (mul_mk_zipper Xa Xb Z)
  have hXa : Xa.length + Z.length = (α (FreeGroup.of u)).toWord.length := by
    rw [hu, List.length_append]
  have hXb : Xb.length + Z.length = (α (FreeGroup.of v)).toWord.length := by
    rw [hv, List.length_append, FreeGroup.invRev_length]
    omega
  have hXb_lt : Xb.length < Z.length := by omega
  have hlt : (FreeGroup.reduce (Xa ++ Xb)).length < FreeGroup.norm (α (FreeGroup.of u)) := by
    calc
      (FreeGroup.reduce (Xa ++ Xb)).length ≤ Xa.length + Xb.length := by
            rw [← List.length_append]
            exact reduce_length_le (Xa ++ Xb)
      _ < Xa.length + Z.length := by omega
      _ = (α (FreeGroup.of u)).toWord.length := hXa
      _ = FreeGroup.norm (α (FreeGroup.of u)) := rfl
  unfold FreeGroup.norm
  rw [htw]
  exact hlt

end Submission.Nielsen
