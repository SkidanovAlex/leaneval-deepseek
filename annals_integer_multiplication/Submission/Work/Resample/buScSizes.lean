import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Resample.buScProdSz
import Submission.Work.Resample.buScRecsSz

namespace Work.Resample

namespace Work.Resample
open HvdH

/-! ## size bookkeeping for the scaling stage -/

/-- `vsz (ofList xs) ≤ (|xs|+1)·(B+1)` when every entry of `xs` has `vsz ≤ B`.  (Local copy of
`Work.Resample.vsz_ofList_le`; the module `auPreKit` is not in the import closure here.) -/
theorem buSc_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, Work.Fx.vsz_cons, List.length_cons]
    nlinarith [ih']

/-- `|z| ≤ 2^N` gives `isz z ≤ N+3` (`N+2` would require the strict bound). -/
lemma buSc_isz_le_of_natAbs_le {z : ℤ} {N : ℕ} (h : z.natAbs ≤ 2 ^ N) : isz z ≤ N + 3 := by
  have h2 : z.natAbs.size ≤ N + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt h (Nat.pow_lt_pow_succ (by norm_num)))
  simp only [isz]; omega

/-- `|z| < 2^N` gives `isz z ≤ N+2`. -/
lemma buSc_isz_le_of_natAbs_lt {z : ℤ} {N : ℕ} (h : z.natAbs < 2 ^ N) : isz z ≤ N + 2 := by
  have h2 : z.natAbs.size ≤ N := Nat.size_le.mpr h
  simp only [isz]; omega

/-- `8·|W| ≤ 3·2^p` forces the *strict* bound `|W| < 2^p`. -/
lemma buSc_natAbs_lt_two_pow {W : ℤ} {p : ℕ} (h : 8 * W.natAbs ≤ 3 * 2 ^ p) :
    W.natAbs < 2 ^ p := by
  have h2 : 3 * 2 ^ p < 8 * 2 ^ p :=
    Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p)
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h h2)

/-- A fixed-point pair in the disc of radius `2^N` has `vsz (cfxVal z) ≤ 2N + 7`. -/
lemma buSc_vsz_cfxVal_le {N : ℕ} {z : ℤ × ℤ} (h : buIn (2 ^ N) z) :
    vsz (cfxVal z) ≤ 2 * N + 7 := by
  rw [Work.Fx.vsz_cfxVal]
  have h1 := buSc_isz_le_of_natAbs_le (N := N) (buIn_coord h).1
  have h2 := buSc_isz_le_of_natAbs_le (N := N) (buIn_coord h).2
  omega

/-- Uniform size bounds for the windows of the scaling stage: every single value has `vsz ≤ buScB p`
and every list window at most `(s+1)·(buScB p + 1)`.  `buScB p = 3p+12`.  Useful fact:
`vsz (ofList l) ≤ (l.length + 1) * (B + 1)` when all entries have `vsz ≤ B`
(`Work.Resample.vsz_ofList_le`). -/
theorem buScSizes (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
    (hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
    (u : List (ℤ × ℤ)) (hu : u.length = s) (hV : buInV (2 ^ (p + 1)) u)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (hVd : buInV (2 ^ p) d)
    (ys : List Val) (hperm : ys.Perm (buScRecs s t d)) :
    vsz (cvecVal u) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (buWdL p α s t) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (buKeysS s t) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (cvecVal d) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (ofList (buScRecs s t d)) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (ofList ys) ≤ (s + 1) * (buScB p + 1) ∧
    isz ((2 : ℤ) ^ p) ≤ buScB p ∧
    isz ((s : ℤ)) ≤ buScB p ∧
    isz ((p : ℤ)) ≤ buScB p ∧
    (∀ x ∈ buScRecs s t d, vsz x ≤ buScB p) ∧
    (∀ x ∈ ys.take s, vsz (buScStrip x) ≤ buScB p) ∧
    (∀ x ∈ List.zipWith (buScProd ((2 : ℤ) ^ p))
        ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int) (u.map cfxVal),
      vsz x ≤ buScB p) := by
  have hs0 : 0 < s := by omega
  obtain ⟨hreclen, hrecmem, hrecstrip⟩ := buScRecsSz p s t hs0 hst htp d hd hVd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrecmem, ?_, buScProdSz p α s t u hwd hV⟩
  · -- `cvecVal u`, entries in the disc of radius `2^(p+1)`
    have h := buSc_ofList_le (l := u.map cfxVal) (B := buScB p) (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have hz' := buSc_vsz_cfxVal_le (N := p + 1) (hV z hz)
      simp only [buScB] at *
      omega)
    simpa [cvecVal, List.length_map, hu] using h
  · -- the diagonal weight list `buWdL`
    show vsz (ofList ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int)) ≤ _
    have h := buSc_ofList_le
        (l := (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int) (B := buScB p)
        (fun x hx => by
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
      rw [Work.Fx.vsz_int]
      have hz' := buSc_isz_le_of_natAbs_lt (N := p) (buSc_natAbs_lt_two_pow (hwd (i : ℤ)))
      simp only [buScB] at *
      omega)
    simpa [List.length_map, List.length_ofFn] using h
  · -- the key list `buKeysS`
    rw [buKeysS_eq]
    have h := buSc_ofList_le (l := buScKeys s t) (B := buScB p) (fun x hx => by
      rw [buScKeys] at hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      rw [Work.Fx.vsz_int]
      have hk : (((egKeyS s t (i : ℕ) : ℕ) : ℤ)).natAbs < 2 ^ p := by
        rw [Int.natAbs_natCast]
        exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.mod_lt _ hs0) (le_of_lt hst)) (le_of_lt htp)
      have hz' := buSc_isz_le_of_natAbs_lt hk
      simp only [buScB] at *
      omega)
    rw [buScKeys_length s t] at h
    exact h
  · -- `cvecVal d`, entries in the disc of radius `2^p`
    have h := buSc_ofList_le (l := d.map cfxVal) (B := buScB p) (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have hz' := buSc_vsz_cfxVal_le (N := p) (hVd z hz)
      simp only [buScB] at *
      omega)
    simpa [cvecVal, List.length_map, hd] using h
  · -- the record list
    have h := buSc_ofList_le (l := buScRecs s t d) (B := buScB p) hrecmem
    rwa [hreclen] at h
  · -- the permuted record list
    have hlen : ys.length = s := by rw [List.Perm.length_eq hperm, hreclen]
    have h := buSc_ofList_le (l := ys) (B := buScB p)
      (fun x hx => hrecmem x ((hperm.mem_iff).mp hx))
    rwa [hlen] at h
  · -- `isz (2^p)`
    rw [isz, Int.natAbs_pow]
    have h2 : (2 : ℤ).natAbs = 2 := rfl
    rw [h2, Nat.size_pow]
    simp only [buScB]; omega
  · -- `isz s`
    rw [isz, Int.natAbs_natCast]
    have hsz : s.size ≤ p := Nat.size_le.mpr (lt_trans hst htp)
    simp only [buScB] at *
    omega
  · -- `isz p`
    rw [isz, Int.natAbs_natCast]
    have hsz : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [buScB] at *
    omega
  · -- the images under `buScStrip` of the taken record list
    intro x hx
    exact hrecstrip x ((hperm.mem_iff).mp (List.mem_of_mem_take hx))

end Work.Resample

open HvdH

/-- The same statement under the name requested by the caller, `Work.Resample.buScSizes`: the body
above lives in the (duplicated) namespace block of the stub, so this alias exposes it one level up.
`Work.Resample.buScSorted` uses the identical device. -/
theorem buScSizes (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p)
    (hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p)
    (u : List (ℤ × ℤ)) (hu : u.length = s) (hV : buInV (2 ^ (p + 1)) u)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (hVd : buInV (2 ^ p) d)
    (ys : List Val) (hperm : ys.Perm (buScRecs s t d)) :
    vsz (cvecVal u) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (buWdL p α s t) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (buKeysS s t) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (cvecVal d) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (ofList (buScRecs s t d)) ≤ (s + 1) * (buScB p + 1) ∧
    vsz (ofList ys) ≤ (s + 1) * (buScB p + 1) ∧
    isz ((2 : ℤ) ^ p) ≤ buScB p ∧
    isz ((s : ℤ)) ≤ buScB p ∧
    isz ((p : ℤ)) ≤ buScB p ∧
    (∀ x ∈ buScRecs s t d, vsz x ≤ buScB p) ∧
    (∀ x ∈ ys.take s, vsz (buScStrip x) ≤ buScB p) ∧
    (∀ x ∈ List.zipWith (buScProd ((2 : ℤ) ^ p))
        ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int) (u.map cfxVal),
      vsz x ≤ buScB p) :=
  _root_.Work.Resample.Work.Resample.buScSizes p α s t hs hst hcop htp hwd u hu hV d hd hVd ys hperm

end Work.Resample
