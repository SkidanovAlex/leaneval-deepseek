import Mathlib
import Submission.Work.Resample.buKit

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## Auxiliary lemmas -/

/-- `(List.range n).map g = List.ofFn g`. -/
theorem buKeys_range_map_ofFn (n : ℕ) (g : ℕ → Val) :
    (List.range n).map g = List.ofFn (fun i : Fin n => g i) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- `ofList` of a list of values of size `≤ B` has size `≤ (length+1)(B+1)`. -/
theorem buKeys_vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hcons : vsz (ofList (x :: t)) = vsz x + vsz (ofList t) + 1 := by
      show vsz (Val.cons x (ofList t)) = vsz x + vsz (ofList t) + 1
      simp [vsz, Val.enc]
    rw [hcons, List.length_cons]
    nlinarith [ih']

/-- `Kc * C ≤ (p+1)^e` when `C ≤ (p+1)^d` and `Kc + d ≤ e`, for `p ≥ 100`. -/
theorem buKeys_mul_pow_le {p Kc C d e : ℕ} (hp : 100 ≤ p) (hC : C ≤ (p + 1) ^ d)
    (h : Kc + d ≤ e) : Kc * C ≤ (p + 1) ^ e := by
  have hb : 2 ≤ p + 1 := by omega
  have hK : Kc ≤ (p + 1) ^ Kc :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := Kc))) (Nat.pow_le_pow_left hb Kc)
  calc Kc * C ≤ (p + 1) ^ Kc * (p + 1) ^ d := Nat.mul_le_mul hK hC
    _ = (p + 1) ^ (Kc + d) := by rw [← pow_add]
    _ ≤ (p + 1) ^ e := Nat.pow_le_pow_right (by omega) h

/-- `M * (p+1)^d ≤ 8(s+1)(p+1)^Λ` when `M * (p+1)^d ≤ (s+1)(p+1)^50`. -/
theorem buKeys_step_le {p s Kc D Λ : ℕ} (hp : 100 ≤ p)
    (hD : D ≤ (s + 1) * (p + 1) ^ 50) (hK : Kc + 51 ≤ Λ) :
    Kc * D ≤ 8 * (s + 1) * (p + 1) ^ Λ := by
  have hb : 2 ≤ p + 1 := by omega
  have hKc : Kc ≤ (p + 1) ^ Kc :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := Kc))) (Nat.pow_le_pow_left hb Kc)
  have h1 : (s + 1) * (p + 1) ^ (Kc + 50) ≤ (s + 1) * (p + 1) ^ (Λ - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (s + 1) * (p + 1) ^ (Λ - 1) ≤ (s + 1) * (p + 1) ^ Λ :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  calc Kc * D ≤ (p + 1) ^ Kc * D := Nat.mul_le_mul_right _ hKc
    _ ≤ (p + 1) ^ Kc * ((s + 1) * (p + 1) ^ 50) := Nat.mul_le_mul_left _ hD
    _ = (s + 1) * (p + 1) ^ (Kc + 50) := by rw [pow_add]; ring
    _ ≤ (s + 1) * (p + 1) ^ (Λ - 1) := h1
    _ ≤ (s + 1) * (p + 1) ^ Λ := h2
    _ ≤ 8 * (s + 1) * (p + 1) ^ Λ := by
        calc (s + 1) * (p + 1) ^ Λ = 1 * ((s + 1) * (p + 1) ^ Λ) := (Nat.one_mul _).symm
          _ ≤ 8 * ((s + 1) * (p + 1) ^ Λ) := Nat.mul_le_mul_right _ (by norm_num)
          _ = 8 * (s + 1) * (p + 1) ^ Λ := by ring

/-- A numeral bound: `C ≤ (p+1)^d` for `p ≥ 100` whenever `C ≤ 101^d`. -/
theorem buKeys_num_le {p C d : ℕ} (hp : 100 ≤ p) (h : C ≤ 101 ^ d) : C ≤ (p + 1) ^ d :=
  le_trans h (Nat.pow_le_pow_left (by omega : 101 ≤ p + 1) d)

/-- A polynomial-in-`p` bound: `P ≤ M(p+1) ≤ (p+1)^50`. -/
theorem buKeys_poly_le {p P M : ℕ} (hp : 100 ≤ p) (h : P ≤ M * (p + 1))
    (hM : M ≤ 101 ^ 49) : P ≤ (p + 1) ^ 50 := by
  calc P ≤ M * (p + 1) := h
    _ ≤ (p + 1) ^ 49 * (p + 1) := Nat.mul_le_mul_right _ (buKeys_num_le hp hM)
    _ = (p + 1) ^ 50 := by ring

/-- `p + k ≤ (p+1)^2` for `k ≤ 200`, `p ≥ 100`. -/
theorem buKeys_add_le_sq {p k : ℕ} (hp : 100 ≤ p) (hk : k ≤ 200) : p + k ≤ (p + 1) ^ 2 := by
  have h3 : 200 ≤ p * p := le_trans (by norm_num : (200 : ℕ) ≤ 100 * 100) (Nat.mul_le_mul hp hp)
  have h2 : k ≤ p * p + p + 1 := by omega
  calc p + k ≤ p + (p * p + p + 1) := Nat.add_le_add_left h2 _
    _ = (p + 1) ^ 2 := by ring

/-- `2p + 8 ≤ (p+1)^2` for `p ≥ 100`. -/
theorem buKeys_twop_le_sq {p : ℕ} (hp : 100 ≤ p) : 2 * p + 8 ≤ (p + 1) ^ 2 := by
  have h4 : 7 ≤ p * p := le_trans (by norm_num : (7 : ℕ) ≤ 100 * 100) (Nat.mul_le_mul hp hp)
  have h3 : 8 ≤ p * p + 1 := by omega
  calc 2 * p + 8 ≤ 2 * p + (p * p + 1) := Nat.add_le_add_left h3 _
    _ = (p + 1) ^ 2 := by ring

/-- `9 ≤ (p+1)^2` for `p ≥ 100`. -/
theorem buKeys_nine_le_sq {p : ℕ} (hp : 100 ≤ p) : 9 ≤ (p + 1) ^ 2 := by
  have h : (101 : ℕ) * 101 ≤ (p + 1) * (p + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h9 : (9 : ℕ) ≤ 101 * 101 := by norm_num
  simpa [pow_two] using le_trans h9 h

/-! ## The label list and the per-element function -/

/-- The function implemented by the per-element word: `cons (int i) _ ↦ int ((t·i) % s)`. -/
def buKeyF (s t : ℕ) : Val → Val
  | .cons (.int i) _ => .int (((t * i.toNat) % s : ℕ) : ℤ)
  | _ => .nil

theorem buKeyF_cons (s t i : ℕ) :
    buKeyF s t (.cons (.int (i : ℤ)) .nil) = .int (((t * i) % s : ℕ) : ℤ) := by
  show Val.int (((t * ((i : ℤ)).toNat) % s : ℕ) : ℤ) = Val.int (((t * i) % s : ℕ) : ℤ)
  rw [Int.toNat_natCast]

/-- The list of labels `[cons (int 0) nil, …, cons (int (s-1)) nil]`. -/
def buKeysList (s : ℕ) : List Val :=
  (List.range s).map (fun i : ℕ => Val.cons (.int (i : ℤ)) .nil)

theorem buKeysList_length (s : ℕ) : (buKeysList s).length = s := by
  simp [buKeysList]

theorem buKeysList_map (s t : ℕ) :
    (buKeysList s).map (buKeyF s t)
      = (List.range s).map (fun i : ℕ => Val.int (((t * i) % s : ℕ) : ℤ)) := by
  simp only [buKeysList, List.map_map]
  apply List.map_congr_left
  intro i _
  exact buKeyF_cons s t i

theorem buKeys_ofList_range (p α s t : ℕ) :
    ofList ((List.range s).map (fun i : ℕ => Val.int (((t * i) % s : ℕ) : ℤ)))
      = buL8 p α s t := by
  have h1 : buL8 p α s t
      = zl (List.ofFn (fun i : Fin s => (((t * (i : ℕ)) % s : ℕ) : ℤ))) := by
    simp only [buL8, egKeyS]
  rw [h1, zl, List.map_ofFn, buKeys_range_map_ofFn]
  rfl

theorem buKeys_ofList_map (p α s t : ℕ) :
    ofList ((buKeysList s).map (buKeyF s t)) = buL8 p α s t := by
  rw [buKeysList_map, buKeys_ofList_range]

/-- Size of a `cons`. -/
theorem buKeys_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (Val.cons a b).enc.length = a.enc.length + b.enc.length + 1
  simp [Val.enc, List.length_append]

/-- `vsz (cons (int z) nil) = isz z + 2`. -/
theorem buKeys_vsz_cons_nil (z : ℤ) : vsz (Val.cons (.int z) .nil) = isz z + 2 := by
  rw [buKeys_vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_nil]

/-- `mapList` with an element word that depends on the (fixed) tail `rest`. -/
theorem buKeysMapListRest {comb : Cmd → Cmd} {Kml : ℕ} (hML : MapListField comb Kml)
    {main q : Cmd} {rest : List Val} {xs : List Val} {F : Val → Val} {c L : ℕ}
    (h : ∀ x ∈ xs, WordR main q (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ y = F x ∧ vsz y ≤ L) (fun _ => c))
    (hx : ∀ x ∈ xs, vsz x ≤ L) :
    WordR main (comb q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => out = ofList (xs.map F) :: rest)
      (fun _ => xs.length * (c + Kml * (L + 1)) + Kml) := by
  have h1 : WordR main (comb q) (fun vs => vs = ofList xs :: rest)
      (fun _ out => ∃ ys, out = ofList ys :: rest ∧ List.Forall₂ (fun x y => y = F x) xs ys)
      (fun _ => xs.length * (c + Kml * (L + 1)) + Kml) :=
    hML main q rest (fun x => x ∈ xs) (fun x y => y = F x) c L h xs
      (fun x hxm => ⟨hxm, hx x hxm⟩)
  refine Work.Kernel.WordR_conseq h1 ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out _ hout
    obtain ⟨ys, hout', hf⟩ := hout
    rw [hout', forall₂_map_right hf]
  · intro vs _; exact le_rfl

/-- Composition of two `WordR`s with a fixed value list. -/
theorem buKeys_comp {main p q : Cmd} {A B D : List Val} {c1 c2 : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c1))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = D) (fun _ => c2)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = D) (fun _ => c1 + c2) := by
  intro vs hvs s R hR
  obtain ⟨mid, s', n1, hmid, hev1, hn1, hstk1, hoth1⟩ := h1 vs hvs s R hR
  obtain ⟨out, s'', n2, hout, hev2, hn2, hstk2, hoth2⟩ := h2 mid hmid s' R hstk1
  exact ⟨out, s'', n1 + n2, hout, Eval.seq hev1 hev2, Nat.add_le_add hn1 hn2, hstk2,
    fun k hk => by rw [hoth2 k hk, hoth1 k hk]⟩

/-- Rewrite the *pre*-window of a `Pipe`. -/
theorem buKeys_rwPre {main prog : Cmd} {A B A' : List Val} {c : ℕ}
    (h : Pipe main prog A B c) (hA : A = A') : Pipe main prog A' B c := by
  rw [hA] at h
  exact h

/-- `isz` of `egN p α s t`. -/
theorem buKeys_isz_egN_le (p α s t : ℕ) (hs : 0 < s) (hsp : s < 2 ^ p) (hp : 1 ≤ p) :
    isz ((egN p α s t : ℕ) : ℤ) ≤ auSZ p := by
  have h1 : egN p α s t ≤ p * s := by
    have h := Nat.div_le_self (p * s - 1) (α ^ 2 * (t - s))
    have h3 : 1 ≤ p * s := Nat.mul_pos hp hs
    show (p * s - 1) / (α ^ 2 * (t - s)) + 1 ≤ p * s
    omega
  have h2 : p * s ≤ 2 ^ (2 * p) := by
    have hp2 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
    calc p * s ≤ p * 2 ^ p := Nat.mul_le_mul_left _ (le_of_lt hsp)
      _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ hp2
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  have hle : egN p α s t ≤ 2 ^ (2 * p) := le_trans h1 h2
  have hsz : (egN p α s t).size ≤ 2 * p + 1 :=
    Nat.size_le.mpr (lt_of_le_of_lt hle (Nat.pow_lt_pow_right one_lt_two (by omega)))
  simp only [isz, Int.natAbs_natCast, auSZ]
  omega


/-- `2p + k ≤ (p+1)^2` for `k ≤ 200`, `p ≥ 100`. -/
theorem buKeys_twop_le_sq' {p k : ℕ} (hp : 100 ≤ p) (hk : k ≤ 200) : 2 * p + k ≤ (p + 1) ^ 2 := by
  have h4 : 199 ≤ p * p := le_trans (by norm_num : (199 : ℕ) ≤ 100 * 100) (Nat.mul_le_mul hp hp)
  have h3 : 200 ≤ p * p + 1 := by omega
  calc 2 * p + k ≤ 2 * p + (p * p + 1) := Nat.add_le_add_left (le_trans hk h3) _
    _ = (p + 1) ^ 2 := by ring

/-- Sum of seven terms bounded by `A`. -/
theorem buKeys_sum7_le {A x1 x2 x3 x4 x5 x6 x7 : ℕ} (h1 : x1 ≤ A) (h2 : x2 ≤ A) (h3 : x3 ≤ A)
    (h4 : x4 ≤ A) (h5 : x5 ≤ A) (h6 : x6 ≤ A) (h7 : x7 ≤ A) :
    x1 + (x2 + (x3 + (x4 + (x5 + (x6 + x7))))) ≤ 7 * A := by omega

/-- Sum of six terms bounded by `A`. -/
theorem buKeys_sum6_le {A x1 x2 x3 x4 x5 x6 : ℕ} (h1 : x1 ≤ A) (h2 : x2 ≤ A) (h3 : x3 ≤ A)
    (h4 : x4 ≤ A) (h5 : x5 ≤ A) (h6 : x6 ≤ A) :
    x1 + (x2 + (x3 + (x4 + (x5 + x6)))) ≤ 6 * A := by omega

end Work.Resample
