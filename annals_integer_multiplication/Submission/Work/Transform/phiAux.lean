import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.Kernel.encodeNatBits

/-!
# Toolkit for `phiWord` (paper Prop 3.5)

Small reusable lemmas for the word lemmas `Work.Transform.phiChunkWord`,
`Work.Transform.phiZipWord` and `Work.Transform.phiWordNE`:

* list indexing: `getD_drop`, `getD_take`, `getD_drop_take`, `eq_of_getD_eq`, `sum_map_le`;
* sizes in `C̃◦`: `isz_le_of_inDisc` (`isz z ≤ p + 3` for `z ∈ C̃◦`), `inDisc_natAbs_le`;
* sizes of encodings: `vsz_int`, `vsz_cfxVal`, `vsz_ofList`, `vsz_cvecVal_le`, `vsz_rarrVal_le`;
* `InDiscVec`/`InDiscArr` bridges: `inDiscVec_getD`, `inDiscArr_iff`, `inDiscArr_of_chunks`;
* `cfxVal_injective` and the one-element product word `cfxMulWord`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-! ## List indexing -/

theorem getD_drop {α : Type} [Inhabited α] (l : List α) (k c : ℕ) (d : α) :
    (l.drop k).getD c d = l.getD (k + c) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take {α : Type} [Inhabited α] (l : List α) (m c : ℕ) (d : α) (h : c < m) :
    (l.take m).getD c d = l.getD c d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem getD_drop_take {α : Type} [Inhabited α] (l : List α) (k m c : ℕ) (d : α) (h : c < m) :
    ((l.drop k).take m).getD c d = l.getD (k + c) d := by
  rw [getD_take _ _ _ _ h, getD_drop]

/-- Two lists of the same length whose `getD`s agree below the length are equal. -/
theorem eq_of_getD_eq {α : Type} [Inhabited α] {l l' : List α} (hlen : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i (default : α) = l'.getD i (default : α)) : l = l' := by
  refine List.ext_getElem hlen ?_
  intro n h1 h2
  rw [← List.getD_eq_getElem (l := l) (d := (default : α)) h1,
    ← List.getD_eq_getElem (l := l') (d := (default : α)) h2]
  exact h n h1

theorem sum_map_le {α : Type} (l : List α) (f : α → ℕ) (C : ℕ) (h : ∀ a ∈ l, f a ≤ C) :
    (l.map f).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h' : ∀ a ∈ t, f a ≤ C := fun a ha => h a (by simp [ha])
    have hle := ih h'
    have ha := h a (by simp)
    rw [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-! ## Sizes of integers of `C̃◦` -/

theorem nat_size_le_self (n : ℕ) : n.size ≤ n := by
  rw [Nat.size_le]
  exact Nat.lt_two_pow_self

theorem isz_le (z : ℤ) : isz z ≤ z.natAbs + 2 := by
  have := nat_size_le_self z.natAbs
  simp only [isz]
  omega

theorem two_pow_sq (p : ℕ) : ((2 : ℤ) ^ p) ^ 2 = 4 ^ p := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ (2 : ℤ) k, mul_pow, ih, show ((2 : ℤ)) ^ 2 = 4 from by norm_num,
      pow_succ (4 : ℤ) k]

/-- In `C̃◦` both coordinates have absolute value at most `2^p`. -/
theorem inDisc_natAbs_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    z.1.natAbs ≤ 2 ^ p ∧ z.2.natAbs ≤ 2 ^ p := by
  have hx : z.1 ^ 2 ≤ 4 ^ p := by
    have h2 : (0 : ℤ) ≤ z.2 ^ 2 := sq_nonneg _
    have h' := h
    simp only [inDisc] at h'
    linarith
  have hy : z.2 ^ 2 ≤ 4 ^ p := by
    have h2 : (0 : ℤ) ≤ z.1 ^ 2 := sq_nonneg _
    have h' := h
    simp only [inDisc] at h'
    linarith
  have key : ∀ (w : ℤ), w ^ 2 ≤ 4 ^ p → w.natAbs ≤ 2 ^ p := by
    intro w hw
    have h5 : ((w.natAbs : ℤ)) ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
      rw [Int.natCast_natAbs, sq_abs, two_pow_sq]
      exact hw
    have h6 := sq_le_sq.mp h5
    rw [abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (by positivity)] at h6
    exact_mod_cast h6
  exact ⟨key _ hx, key _ hy⟩

/-- A value of `C̃◦` has coordinates of bit-size `≤ p + 1`, hence `isz ≤ p + 3`. -/
theorem isz_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    isz z.1 ≤ p + 3 ∧ isz z.2 ≤ p + 3 := by
  have h1 := inDisc_natAbs_le h
  have key : ∀ w : ℤ, w.natAbs ≤ 2 ^ p → isz w ≤ p + 3 := by
    intro w hw
    have h2 : w.natAbs < 2 ^ (p + 1) := by
      have h3 : (2 : ℕ) ^ p < 2 ^ (p + 1) := by
        rw [pow_succ]
        have : 0 < 2 ^ p := by positivity
        omega
      omega
    have h4 : w.natAbs.size ≤ p + 1 := (Nat.size_le).2 h2
    simp only [isz]
    omega
  exact ⟨key _ h1.1, key _ h1.2⟩

/-! ## Sizes of encodings -/

@[simp] theorem vsz_nil : vsz Val.nil = 1 := rfl

theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc]

theorem vsz_int_aux (z : ℤ) : vsz (Val.int z) = (Computability.encodeNat z.natAbs).length + 2 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_map,
    List.length_nil]

theorem vsz_int (z : ℤ) : vsz (Val.int z) = isz z := by
  rw [vsz_int_aux, isz, Work.Kernel.encodeNatBits, Nat.size_eq_bits_len]

theorem vsz_ofList (l : List Val) : vsz (ofList l) = l.length + (l.map vsz).sum + 1 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h : ofList (a :: t) = Val.cons a (ofList t) := rfl
    rw [h, vsz_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem vsz_cfxVal (z : ℤ × ℤ) : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
  rw [cfxVal, vsz_cons, vsz_int, vsz_int]

theorem vsz_cvecVal (zs : List (ℤ × ℤ)) :
    vsz (cvecVal zs) = zs.length + (zs.map fun z => isz z.1 + isz z.2 + 1).sum + 1 := by
  have h1 : cvecVal zs = ofList (zs.map cfxVal) := rfl
  rw [h1, vsz_ofList, List.length_map]
  have h2 : (zs.map cfxVal).map vsz = zs.map (fun z => isz z.1 + isz z.2 + 1) := by
    rw [List.map_map]
    exact List.map_congr_left fun z _ => vsz_cfxVal z
  rw [h2]

theorem vsz_cfxVal_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : vsz (cfxVal z) ≤ 2 * p + 8 := by
  have h1 := isz_le_of_inDisc h
  rw [vsz_cfxVal]
  omega

/-- Size of a `C̃◦` vector of length `n`. -/
theorem vsz_cvecVal_le {p n : ℕ} {zs : List (ℤ × ℤ)} (h : InDiscVec p n zs) (hp : 100 ≤ p) :
    vsz (cvecVal zs) ≤ 200 * (n * p ^ 2 + 1) := by
  have hlen : zs.length = n := h.1
  have hsum : (zs.map fun z => isz z.1 + isz z.2 + 1).sum ≤ zs.length * (2 * p + 8) :=
    sum_map_le zs _ _ fun z hz => by
      rw [← vsz_cfxVal]
      exact vsz_cfxVal_le (h.2 z hz)
  have h2p : 2 * p + 8 ≤ p ^ 2 := by nlinarith [hp]
  have hle : zs.length * (2 * p + 8) ≤ n * p ^ 2 := by
    rw [hlen]
    exact Nat.mul_le_mul_left n h2p
  rw [vsz_cvecVal, hlen]
  nlinarith [hsum, hle, Nat.zero_le n]

theorem inDiscVec_getD {p n : ℕ} {zs : List (ℤ × ℤ)} (h : InDiscVec p n zs) (i : ℕ) (hi : i < n) :
    inDisc p (zs.getD i (0, 0)) := by
  have hi' : i < zs.length := by rw [h.1]; exact hi
  rw [List.getD_eq_getElem (l := zs) (d := ((0, 0) : ℤ × ℤ)) hi']
  exact h.2 _ (List.mem_iff_getElem.mpr ⟨i, hi', rfl⟩)

theorem vsz_cfxVal_getD_le {p n : ℕ} {zs : List (ℤ × ℤ)} (h : InDiscVec p n zs) (i : ℕ)
    (hi : i < n) : vsz (cfxVal (zs.getD i (0, 0))) ≤ 2 * p + 8 :=
  vsz_cfxVal_le (inDiscVec_getD h i hi)

/-! ## `InDiscArr` bridges -/

theorem inDiscArr_iff {p M r : ℕ} {a : List (List (ℤ × ℤ))} (hlen : a.length = M) :
    InDiscArr p M r a ↔ ∀ i < M, InDiscVec p r (a.getD i []) := by
  constructor
  · intro h i hi
    have hi' : i < a.length := by rw [hlen]; exact hi
    rw [List.getD_eq_getElem (l := a) (d := ([] : List (ℤ × ℤ))) hi']
    exact h.2 _ (List.mem_iff_getElem.mpr ⟨i, hi', rfl⟩)
  · intro h
    refine ⟨hlen, ?_⟩
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    rw [← List.getD_eq_getElem (l := a) (d := ([] : List (ℤ × ℤ))) hi]
    exact h i (by rw [← hlen]; exact hi)

theorem vsz_cvecVal_getD_le {p M r : ℕ} {a : List (List (ℤ × ℤ))} (h : InDiscArr p M r a)
    (hp : 100 ≤ p) (i : ℕ) (hi : i < M) : vsz (cvecVal (a.getD i [])) ≤ 200 * (r * p ^ 2 + 1) :=
  vsz_cvecVal_le ((inDiscArr_iff h.1).mp h i hi) hp

theorem vsz_rarrVal_le {p M r : ℕ} {a : List (List (ℤ × ℤ))} (h : InDiscArr p M r a)
    (hp : 100 ≤ p) (hr : 2 ≤ r) : vsz (rarrVal a) ≤ 400 * (M * r * p ^ 2 + 1) := by
  have hlen : a.length = M := h.1
  have hsum : (a.map fun w => vsz (cvecVal w)).sum ≤ a.length * (200 * (r * p ^ 2 + 1)) :=
    sum_map_le a _ _ fun w hw => vsz_cvecVal_le (h.2 w hw) hp
  have hle : a.length * (200 * (r * p ^ 2 + 1)) ≤ M * (200 * (r * p ^ 2 + 1)) := by rw [hlen]
  have hS : (a.map fun w => vsz (cvecVal w)).sum ≤ 200 * M * r * p ^ 2 + 200 * M := by
    have h1 : M * (200 * (r * p ^ 2 + 1)) = 200 * M * r * p ^ 2 + 200 * M := by ring
    rw [h1] at hle
    exact le_trans hsum hle
  have h200 : 201 ≤ 200 * (r * p ^ 2) := by nlinarith [hr, hp]
  have hB : 201 * M ≤ 200 * M * r * p ^ 2 := by
    have h2 : 201 * M ≤ (200 * (r * p ^ 2)) * M := Nat.mul_le_mul_right M h200
    nlinarith [h2]
  have hS' : (List.map (vsz ∘ cvecVal) a).sum ≤ 200 * M * r * p ^ 2 + 200 * M := hS
  have h1 : rarrVal a = ofList (a.map cvecVal) := rfl
  rw [h1, vsz_ofList, List.length_map, List.map_map, hlen]
  nlinarith [hS', hB]

/-- Chunks of a `C̃◦` vector are again in `C̃◦` (feeds `PhiZipWord` from `PhiChunkWord`). -/
theorem inDiscArr_of_chunks {p M r : ℕ} {x : List (ℤ × ℤ)} {a : List (List (ℤ × ℤ))}
    (hx : InDiscVec p (M * r) x) (hlen : a.length = M)
    (hlen2 : ∀ i < M, (a.getD i []).length = r)
    (hval : ∀ i < M, ∀ c < r, (a.getD i []).getD c (0, 0) = x.getD (i * r + c) (0, 0)) :
    InDiscArr p M r a := by
  refine ⟨hlen, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
  have hiM : i < M := by rw [← hlen]; exact hi
  have hwi : a[i] = a.getD i [] := (List.getD_eq_getElem (l := a) (d := ([] : List (ℤ × ℤ))) hi).symm
  rw [hwi]
  refine ⟨hlen2 i hiM, ?_⟩
  intro z hz
  obtain ⟨c, hc, rfl⟩ := List.mem_iff_getElem.mp hz
  have hcr : c < r := by rw [← hlen2 i hiM]; exact hc
  have hzc : (a.getD i [])[c] = (a.getD i []).getD c (0, 0) :=
    (List.getD_eq_getElem (l := a.getD i []) (d := ((0, 0) : ℤ × ℤ)) hc).symm
  rw [hzc, hval i hiM c hcr]
  have hidx : i * r + c < x.length := by
    rw [hx.1]
    have h1 : (i + 1) * r ≤ M * r := Nat.mul_le_mul_right r (by omega)
    have h2 : i * r + c < (i + 1) * r := by
      have h3 := Nat.add_lt_add_left hcr (i * r)
      simpa [Nat.succ_mul] using h3
    omega
  exact hx.2 _ (List.mem_iff_getElem.mpr
    ⟨i * r + c, hidx, (List.getD_eq_getElem (l := x) (d := ((0, 0) : ℤ × ℤ)) hidx).symm⟩)

/-! ## The one-element product word -/

theorem cfxVal_injective : Function.Injective cfxVal := by
  intro u v h
  have h' : Val.cons (Val.int u.1) (Val.int u.2) = Val.cons (Val.int v.1) (Val.int v.2) := h
  injection h' with h1 h2
  injection h1 with h3
  injection h2 with h4
  exact Prod.ext h3 h4

/-- `int p :: cfxVal u :: cfxVal v :: R ↦ cfxVal w :: int p :: R` with `w ≈ u * v`:
copy `p` to the top (`KernelLib.pick 2`) and run `FxLib.mulS`. -/
theorem cfxMulWord : HvdH.KernelLib → HvdH.FxLib → ∃ (prog : Cmd) (K : ℕ),
    ∀ (main : Cmd) (p : ℕ) (u v : ℤ × ℤ) (R : List Val),
      inDisc p u → inDisc p v → 100 ≤ p →
      WordR main prog
        (fun vs => vs = cfxVal u :: cfxVal v :: Val.int p :: R)
        (fun vs out => ∃ w : ℤ × ℤ, out = cfxVal w :: Val.int p :: R ∧ inDisc p w ∧
          (2 : ℝ) ^ p * ‖fxC p w - fxC p v * fxC p u‖ < 2)
        (fun _ => K * (p + 1) ^ 2) := by
  intro Kl Fl
  obtain ⟨pick, K₁, hpick⟩ := Kl.pick
  obtain ⟨mulS, K₂, hmulS⟩ := Fl.mulS
  refine ⟨Cmd.seq (pick 2) mulS, 9 * K₁ + K₂, ?_⟩
  intro main p u v R hu hv hp
  have hcu : vsz (cfxVal u) ≤ 2 * p + 8 := vsz_cfxVal_le hu
  have hcv : vsz (cfxVal v) ≤ 2 * p + 8 := vsz_cfxVal_le hv
  have hcp : isz ((p : ℤ)) ≤ p + 2 := isz_le _
  have hkey : 3 * (5 * p + 18 + 1) ≤ 9 * ((p + 1) ^ 2) := by nlinarith [hp]
  have hpick' : WordR main (pick 2)
      (fun vs => vs = cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R)
      (fun _ out => out = Val.int (p : ℤ) :: cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R)
      (fun _ => 9 * K₁ * ((p + 1) ^ 2)) := by
    refine Work.Kernel.WordR_conseq (hpick main 2) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      have hlen2 : 2 < (cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R).length := by
        simp only [List.length_cons]
        omega
      have hget : (cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R).getD 2 Val.nil
          = Val.int (p : ℤ) := by
        rw [List.getD_eq_getElem (l := cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R)
          (d := Val.nil) hlen2]
        rfl
      rw [hget] at hout
      rw [hout]
    · intro vs hvs
      rw [hvs]
      have hsum : (((cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R).take (2 + 1)).map vsz).sum
          ≤ 5 * p + 18 := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, vsz_int]
        omega
      calc K₁ * (2 + 1) * ((((cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R).take
              (2 + 1)).map vsz).sum + 1)
          = K₁ * 3 * ((((cfxVal u :: cfxVal v :: Val.int (p : ℤ) :: R).take
              (2 + 1)).map vsz).sum + 1) := by norm_num
        _ ≤ K₁ * 3 * (5 * p + 18 + 1) := by
              apply Nat.mul_le_mul_left
              omega
        _ ≤ 9 * K₁ * ((p + 1) ^ 2) := by nlinarith [hkey]
  refine Work.Kernel.WordR_conseq (p := Cmd.seq (pick 2) mulS)
    (Work.Kernel.WordR_seq (B := fun _ => K₂ * ((p + 1) ^ 2)) hpick' (hmulS main p) ?_) ?_ ?_ ?_
  · intro vs mid hvs hmid
    subst mid
    refine ⟨⟨u, v, Val.int (p : ℤ) :: R, rfl, hu, hv⟩, ?_⟩
    show K₂ * ((p + 1) ^ 2) ≤ K₂ * ((p + 1) ^ 2)
    exact le_refl _
  · intro vs hvs
    exact hvs
  · intro vs out hvs hout
    obtain ⟨mid, hmid, u', v', rest, w, hmid', hout', hdisc, herr⟩ := hout
    subst mid
    have hB := (List.cons.inj hmid').2
    have hu' : u = u' := cfxVal_injective (List.cons.inj hB).1
    have hC := (List.cons.inj hB).2
    have hv' : v = v' := cfxVal_injective (List.cons.inj hC).1
    have hrest : rest = Val.int (p : ℤ) :: R := ((List.cons.inj hC).2).symm
    refine ⟨w, ?_, hdisc, ?_⟩
    · rw [hout', hrest]
    · have hc : fxC p v' * fxC p u' = fxC p u' * fxC p v' := mul_comm _ _
      rw [hu', hv', hc]
      exact herr
  · intro vs hvs
    rw [add_mul]

end Work.Transform
