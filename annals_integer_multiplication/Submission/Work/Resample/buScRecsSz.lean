import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Resample.buScKeysFacts

namespace Work.Resample

open HvdH

/-! ## Size of the record list `buScRecs` of the scaling stage

`buScRecs s t d = zipWith cons (buScKeys s t) (d.map cfxVal)` is the list of records
`cons (int ((t·i) mod s)) (cfxVal dᵢ)` (truncated at `min s d.length`).  Every record — and every
record with its key stripped off (`buScStrip`) — fits in the uniform budget `buScB p = 3p+12`:

* the key `(t·i) mod s` is `< s < t < 2^p`, so `isz ≤ p+2`;
* an entry `z ∈ d` of the vector lies in the disc of radius `2^p`, so `|z_j| ≤ 2^p < 2^{p+1}` and
  `isz z_j ≤ p+3`, hence `vsz (cfxVal z) = isz z₁ + isz z₂ + 1 ≤ 2p+7`;
* a record adds `1 + isz (key) ≤ p+3`, so `vsz ≤ 3p+10`.

This is the list-level size input of the scaling stage; it needs no coprimality of `s` and `t`. -/

/-- Every entry of `buScKeys s t` is `Val.int` of the key `egKeyS s t i` at a source index
`i < s`.  (Unlike `buScKeys_mem`, the index is kept.) -/
theorem buScKeys_mem_getElem {s t : ℕ} {a : Val} (ha : a ∈ buScKeys s t) :
    ∃ (i : ℕ) (_ : i < s), a = Val.int (((egKeyS s t i : ℕ) : ℤ)) := by
  rw [buScKeys, List.mem_map] at ha
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
  exact ⟨i, i.isLt, congrArg Val.int hi.symm⟩

/-- The integer key of a record is small: `(t·i) mod s < s < t < 2^p`. -/
theorem buScRecs_key_isz_le {s t p i : ℕ} (hs : 0 < s) (hst : s < t) (htp : t < 2 ^ p) :
    HvdH.isz (((egKeyS s t i : ℕ) : ℤ)) ≤ p + 2 := by
  refine Work.Fx.isz_le_of_natAbs_lt ?_
  rw [Int.natAbs_natCast]
  calc egKeyS s t i = (t * i) % s := rfl
    _ < s := Nat.mod_lt _ hs
    _ < 2 ^ p := by omega

/-- The two coordinates of a point of the disc of radius `2^p` have `isz ≤ p+3`
(indeed `|z_j| ≤ 2^p < 2^{p+1}`). -/
theorem buScRecs_inDisc_isz_le {p : ℕ} {z : ℤ × ℤ} (hz : buIn (2 ^ p) z) :
    HvdH.isz z.1 ≤ p + 3 ∧ HvdH.isz z.2 ≤ p + 3 := by
  obtain ⟨h1, h2⟩ := buIn_coord hz
  exact ⟨Work.Fx.isz_le_of_natAbs_lt (lt_of_le_of_lt h1 (Nat.pow_lt_pow_succ (by norm_num))),
    Work.Fx.isz_le_of_natAbs_lt (lt_of_le_of_lt h2 (Nat.pow_lt_pow_succ (by norm_num)))⟩

/-- Shape of an element of the record list: `x = cons (int ((t·i) mod s)) (cfxVal z)` with `z` an
entry of the vector (at the source index `i < s`). -/
theorem buScRecs_mem_shape {s t : ℕ} {d : List (ℤ × ℤ)} {x : Val} (hx : x ∈ buScRecs s t d) :
    ∃ (i : ℕ) (_ : i < s) (z : ℤ × ℤ),
      x = Val.cons (Val.int (((egKeyS s t i : ℕ) : ℤ))) (cfxVal z) ∧ z ∈ d := by
  rw [buScRecs] at hx
  obtain ⟨a, ha, b, hb, he⟩ := mem_zipWith_exists hx
  obtain ⟨i, hi, rfl⟩ := buScKeys_mem_getElem ha
  rw [List.mem_map] at hb
  obtain ⟨z, hz, rfl⟩ := hb
  exact ⟨i, hi, z, he.symm, hz⟩

/-- The record list has as many entries as the vector has points (truncated at `s`). -/
theorem buScRecs_len {s t : ℕ} {d : List (ℤ × ℤ)} (hd : d.length = s) :
    (buScRecs s t d).length = s := by
  rw [buScRecs, List.length_zipWith, buScKeys_length, List.length_map, hd, Nat.min_self]

theorem buScRecsSz (p s t : ℕ) (hs : 0 < s) (hst : s < t) (htp : t < 2 ^ p)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (hVd : Work.Resample.buInV (2 ^ p) d) :
    (Work.Resample.buScRecs s t d).length = s ∧
    (∀ x ∈ Work.Resample.buScRecs s t d, HvdH.vsz x ≤ Work.Resample.buScB p) ∧
    (∀ x ∈ Work.Resample.buScRecs s t d,
      HvdH.vsz (Work.Resample.buScStrip x) ≤ Work.Resample.buScB p) := by
  refine ⟨buScRecs_len hd, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, his, z, rfl, hz⟩ := buScRecs_mem_shape hx
    obtain ⟨hz1, hz2⟩ := buScRecs_inDisc_isz_le (hVd z hz)
    have hkey : HvdH.isz (((egKeyS s t i : ℕ) : ℤ)) ≤ p + 2 := buScRecs_key_isz_le hs hst htp
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_cfxVal]
    simp only [buScB]
    omega
  · intro x hx
    obtain ⟨i, his, z, rfl, hz⟩ := buScRecs_mem_shape hx
    obtain ⟨hz1, hz2⟩ := buScRecs_inDisc_isz_le (hVd z hz)
    rw [buScStrip_apply, Work.Fx.vsz_cfxVal]
    simp only [buScB]
    omega

end Work.Resample
