import Mathlib
import Submission.Work.Resample.buQWscalDefs
import Submission.Work.Resample.buScKeysFacts

/-!
# `Work.Resample.buScSizeKit`: the size toolkit of the scaling stage

Elementary size lemmas about `vsz`/`isz` used to bound the windows of the scaling stage
(`buScB p = 3p+12`): a uniform bound for `ofList`-windows, the `isz` bounds for integers bounded by
`2^N`, the coordinate bound of the input vectors (`buInV`) and the list-level bounds for
`cvecVal`, `buWdL`, `buKeysS` and the three scalar bounds `isz (2^p)`, `isz s`, `isz p`.

The remaining element bounds (the records `buScRecs` and the products `buScProd`) are separate.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## elementary size bounds -/

/-- A `cons`-list of values of size `≤ B` has size `≤ (length + 1) * (B + 1)`. -/
theorem buScOfList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, Work.Fx.vsz_cons, List.length_cons]
    nlinarith [ih']

/-- `isz z ≤ N + 3` when `|z| ≤ 2^N`. -/
lemma buScIsz_le_of_natAbs_le {z : ℤ} {N : ℕ} (h : z.natAbs ≤ 2 ^ N) : isz z ≤ N + 3 := by
  have h2 : z.natAbs.size ≤ N + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt h (Nat.pow_lt_pow_succ (by norm_num)))
  simp only [isz]; omega

/-- `isz z ≤ N + 2` when `|z| < 2^N`. -/
lemma buScIsz_le_of_natAbs_lt {z : ℤ} {N : ℕ} (h : z.natAbs < 2 ^ N) : isz z ≤ N + 2 := by
  have h2 : z.natAbs.size ≤ N := Nat.size_le.mpr h
  simp only [isz]; omega

/-- `8|W| ≤ 3·2^p` forces `|W| < 2^p`. -/
lemma buScNatAbs_lt_two_pow {W : ℤ} {p : ℕ} (h : 8 * W.natAbs ≤ 3 * 2 ^ p) :
    W.natAbs < 2 ^ p := by
  have h2 : 3 * 2 ^ p < 8 * 2 ^ p :=
    Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p)
  exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h h2)

/-- The `cfxVal` of a point of the disc of radius `2^N`. -/
lemma buScVsz_cfxVal_le {N : ℕ} {z : ℤ × ℤ} (h : buIn (2 ^ N) z) :
    vsz (cfxVal z) ≤ 2 * N + 7 := by
  rw [Work.Fx.vsz_cfxVal]
  have h1 := buScIsz_le_of_natAbs_le (N := N) (buIn_coord h).1
  have h2 := buScIsz_le_of_natAbs_le (N := N) (buIn_coord h).2
  omega

/-- Every entry of the key list `buScKeys s t` is `Val.int` of a natural number `< s`. -/
lemma buScKeys_mem_lt {s t : ℕ} {a : Val} (ha : a ∈ buScKeys s t) :
    ∃ k : ℕ, k < s ∧ a = Val.int (k : ℤ) := by
  rw [buScKeys, List.mem_map] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  rw [List.mem_ofFn] at hk
  obtain ⟨i, rfl⟩ := hk
  exact ⟨egKeyS s t (i : ℕ), Nat.mod_lt _ (Nat.lt_of_lt_of_le (Fin.pos i) (le_refl s)), rfl⟩

/-! ## list-level bounds -/

/-- The vector `cvecVal v` as an `ofList`-window. -/
theorem buScVsz_cvecVal_le (v : List (ℤ × ℤ)) (B : ℕ) (h : ∀ z ∈ v, vsz (cfxVal z) ≤ B) :
    vsz (cvecVal v) ≤ (v.length + 1) * (B + 1) := by
  have h' : ∀ x ∈ v.map cfxVal, vsz x ≤ B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact h z hz
  have := buScOfList_le h'
  simpa [cvecVal, List.length_map] using this

/-- The window `cvecVal u` of the input vector (disc of radius `2^(p+1)`). -/
theorem buScVsz_cvecVal_u (p s : ℕ) (u : List (ℤ × ℤ)) (hu : u.length = s)
    (hV : buInV (2 ^ (p + 1)) u) : vsz (cvecVal u) ≤ (s + 1) * (buScB p + 1) := by
  have h := buScVsz_cvecVal_le u (buScB p) (fun z hz => by
    refine le_trans (buScVsz_cfxVal_le (N := p + 1) (hV z hz)) ?_
    simp only [buScB]; omega)
  rwa [hu] at h

/-- The window `cvecVal d` (disc of radius `2^p`). -/
theorem buScVsz_cvecVal_d (p s : ℕ) (d : List (ℤ × ℤ)) (hd : d.length = s)
    (hVd : buInV (2 ^ p) d) : vsz (cvecVal d) ≤ (s + 1) * (buScB p + 1) := by
  have h := buScVsz_cvecVal_le d (buScB p) (fun z hz => by
    refine le_trans (buScVsz_cfxVal_le (N := p) (hVd z hz)) ?_
    simp only [buScB]; omega)
  rwa [hd] at h

/-- The window `buWdL p α s t` of the diagonal weights. -/
theorem buScVsz_buWdL (p α s t : ℕ)
    (hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    vsz (buWdL p α s t) ≤ (s + 1) * (buScB p + 1) := by
  show vsz (ofList ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int)) ≤
    (s + 1) * (buScB p + 1)
  have h : ∀ x ∈ (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map Val.int,
      vsz x ≤ buScB p := by
    intro x hx
    obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
    rw [Work.Fx.vsz_int]
    have h2 := buScIsz_le_of_natAbs_lt (buScNatAbs_lt_two_pow (hwd (i : ℤ)))
    simp only [buScB] at *
    omega
  have := buScOfList_le h
  simpa [List.length_map, List.length_ofFn] using this

/-- The window `buKeysS s t` of the key list `i ↦ (t·i) mod s`. -/
theorem buScVsz_buKeysS (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    vsz (buKeysS s t) ≤ (s + 1) * (buScB p + 1) := by
  rw [buKeysS_eq]
  have h : ∀ x ∈ buScKeys s t, vsz x ≤ buScB p := by
    intro x hx
    obtain ⟨k, hks, rfl⟩ := buScKeys_mem_lt hx
    rw [Work.Fx.vsz_int]
    have hlt : ((k : ℤ)).natAbs < 2 ^ p := by
      rw [Int.natAbs_natCast]
      exact lt_of_lt_of_le hks (le_of_lt (lt_trans hst htp))
    have h2 := buScIsz_le_of_natAbs_lt hlt
    simp only [buScB] at *
    omega
  have h2 := buScOfList_le h
  rwa [buScKeys_length] at h2

/-! ## the scalar bounds -/

theorem buScIsz_two_pow (p : ℕ) : isz ((2 : ℤ) ^ p) ≤ buScB p := by
  rw [isz, Int.natAbs_pow]
  have h2 : (2 : ℤ).natAbs = 2 := rfl
  rw [h2, Nat.size_pow]
  simp only [buScB]; omega

theorem buScIsz_s (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) : isz ((s : ℤ)) ≤ buScB p := by
  rw [isz, Int.natAbs_natCast]
  have hsz : s.size ≤ p := Nat.size_le.mpr (lt_trans hst htp)
  simp only [buScB] at *
  omega

theorem buScIsz_p (p : ℕ) : isz ((p : ℤ)) ≤ buScB p := by
  rw [isz, Int.natAbs_natCast]
  have hsz : p.size ≤ 3 * p + 10 := by
    rw [Nat.size_le]
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [buScB] at *
  omega

end Work.Resample
