import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBitsAPI

/-!
# Arithmetic layer for the schoolbook multiplication word (`Work.IntLib.mulSWord`)

All the `ℕ`/`List Bool` reasoning needed to justify the bit-level algorithms, independent of
`Cmd`/`Eval`.  Bit lists are least significant bit first (like `Nat.bits`).

* `mbits m v` : the `m` low-order bits of `v`, LSB first.
* `addBits α ρ c` : ripple-carry addition of the two equal-length bit lists `α`, `ρ` with
  carry-in `c`; returns `(sum bits, carry out)`.
* `stepR α ρ b` / `run α bs acc ρ` : one / many steps of the serial multiplier's inner state
  (the "right-shift" schoolbook loop).
* `stripHigh l` : `l` with its high-order (trailing) zeros removed.
-/

set_option autoImplicit false

namespace Work.IntLib
namespace MulS

/-! ## Bit lists -/

/-- The `m` low-order bits of `v`, least significant bit first. -/
def mbits (m v : ℕ) : List Bool := (List.range m).map (fun j => decide (v / 2 ^ j % 2 = 1))

theorem mbits_length (m v : ℕ) : (mbits m v).length = m := by simp [mbits]

theorem mbits_succ (m v : ℕ) :
    mbits (m + 1) v = decide (v % 2 = 1) :: mbits m (v / 2) := by
  unfold mbits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    rw [pow_succ', Nat.div_div_eq_div_mul]

theorem mbits_zero (m : ℕ) : mbits m 0 = List.replicate m false := by
  unfold mbits
  have h : (fun j => decide (0 / 2 ^ j % 2 = 1)) = (fun _ => false) := by
    funext j; simp
  rw [h, List.map_const']
  simp

theorem mod_two_pow_succ (v m : ℕ) : v % 2 ^ (m + 1) = v % 2 + 2 * (v / 2 % 2 ^ m) := by
  rw [pow_succ']
  have hv : v = 2 * (v / 2) + v % 2 := by have h := Nat.div_add_mod v 2; omega
  have hA : v / 2 = v / 2 % 2 ^ m + 2 ^ m * (v / 2 / 2 ^ m) := by
    have h := Nat.div_add_mod (v / 2) (2 ^ m); omega
  conv_lhs => rw [hv, hA]
  rw [show 2 * (v / 2 % 2 ^ m + 2 ^ m * (v / 2 / 2 ^ m)) + v % 2
        = 2 * (v / 2 % 2 ^ m) + v % 2 + (2 * 2 ^ m) * (v / 2 / 2 ^ m) by ring]
  rw [Nat.add_mul_mod_self_left]
  have h1 : v / 2 % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
  have h2 : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem ofBits_mbits (m v : ℕ) : ofBits (mbits m v) = v % 2 ^ m := by
  induction m generalizing v with
  | zero => simp [mbits, ofBits, Nat.mod_one]
  | succ m ih =>
    rw [mbits_succ, ofBits_cons, ih, mod_two_pow_succ]
    congr 1
    obtain h | h := Nat.mod_two_eq_zero_or_one v <;> simp [h]

/-- `l` with its high-order (trailing) zeros removed. -/
def stripHigh (l : List Bool) : List Bool := (l.reverse.dropWhile (fun b => !b)).reverse

theorem or_head?_dropWhile : ∀ (l : List Bool),
    (l.dropWhile (fun b => !b)).head? = none ∨ (l.dropWhile (fun b => !b)).head? = some true
  | [] => Or.inl rfl
  | x :: xs => by
      rw [List.dropWhile_cons]
      by_cases hx : (!x) = true
      · simp only [hx, ite_true]; exact or_head?_dropWhile xs
      · simp only [hx]; cases x <;> simp_all

theorem isBits_stripHigh (l : List Bool) : IsBits (stripHigh l) := by
  rw [stripHigh]
  rcases or_head?_dropWhile l.reverse with h | h
  · left; rw [List.head?_eq_none_iff.mp h]; rfl
  · right; rw [List.getLast?_reverse]; exact h

theorem ofBits_singleton (b : Bool) : ofBits [b] = b.toNat := by simp [ofBits]

theorem ofBits_stripHigh (l : List Bool) : ofBits (stripHigh l) = ofBits l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
    rw [stripHigh, List.reverse_append, List.reverse_singleton]
    cases b with
    | true => simp [List.dropWhile_cons, ofBits_append, ofBits_singleton]
    | false =>
      simp only [List.singleton_append]
      rw [List.dropWhile_cons]
      simp only [Bool.not_false, ite_true]
      rw [show (List.dropWhile (fun b => !b) xs.reverse).reverse = stripHigh xs from rfl, ih]
      simp [ofBits_append, ofBits_singleton]

theorem stripHigh_eq_bits (l : List Bool) : stripHigh l = (ofBits l).bits :=
  (bits_ofBits_of_isBits _ (isBits_stripHigh l)).symm.trans (by rw [ofBits_stripHigh])

/-! ## Ripple-carry addition of two equal-length bit lists -/

/-- Sum bit of the full adder. -/
def faSum : Bool → Bool → Bool → Bool
  | true, true, true => true
  | true, true, false => false
  | true, false, true => false
  | true, false, false => true
  | false, true, true => false
  | false, true, false => true
  | false, false, true => true
  | false, false, false => false

/-- Carry bit of the full adder. -/
def faCarry : Bool → Bool → Bool → Bool
  | true, true, _ => true
  | true, false, true => true
  | false, true, true => true
  | _, _, _ => false

theorem fa_val (a b c : Bool) :
    (faSum a b c).toNat + 2 * (faCarry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Ripple-carry addition of two equal-length bit lists, with carry-in `c`. -/
def addBits : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | a :: as, r :: rs, c => let t := addBits as rs (faCarry a r c); (faSum a r c :: t.1, t.2)
  | [], _ :: _, c => ([], c)
  | _ :: _, [], c => ([], c)

theorem addBits_len : ∀ (α ρ : List Bool), α.length = ρ.length → ∀ c : Bool,
    (addBits α ρ c).1.length = α.length
  | [], [], _, c => by simp [addBits]
  | [], _ :: _, h, c => by simp at h
  | _ :: _, [], h, c => by simp at h
  | a :: as, r :: rs, h, c => by
      have h' : as.length = rs.length := by simpa using h
      simp only [addBits, List.length_cons]
      rw [addBits_len as rs h' (faCarry a r c)]

theorem addBits_val : ∀ (α ρ : List Bool), α.length = ρ.length → ∀ c : Bool,
    ofBits (addBits α ρ c).1 + 2 ^ α.length * (addBits α ρ c).2.toNat
      = ofBits α + ofBits ρ + c.toNat
  | [], [], _, c => by simp [addBits, ofBits]
  | [], _ :: _, h, c => by simp at h
  | _ :: _, [], h, c => by simp at h
  | a :: as, r :: rs, h, c => by
      have h' : as.length = rs.length := by simpa using h
      have ih := addBits_val as rs h' (faCarry a r c)
      have hb := fa_val a r c
      simp only [addBits, ofBits_cons, List.length_cons, pow_succ']
      generalize ht : addBits as rs (faCarry a r c) = t
      rw [ht] at ih
      rw [show (faSum a r c).toNat + 2 * ofBits t.1 + 2 * 2 ^ as.length * t.2.toNat
            = (faSum a r c).toNat
              + (2 * ofBits t.1 + 2 * 2 ^ as.length * t.2.toNat) by ring]
      rw [show 2 * ofBits t.1 + 2 * 2 ^ as.length * t.2.toNat
            = 2 * (ofBits t.1 + 2 ^ as.length * t.2.toNat) by ring, ih]
      omega

/-! ## One step of the serial multiplier -/

theorem ofBits_headD (l : List Bool) : ofBits l = (l.headD false).toNat + 2 * ofBits l.tail := by
  cases l with
  | nil => simp [ofBits]
  | cons b t => simp [ofBits_cons]

theorem headD_toNat_mod (l : List Bool) : (l.headD false).toNat = ofBits l % 2 := by
  cases l with
  | nil => simp [ofBits]
  | cons b t => rw [ofBits_cons]; cases b <;> simp [Nat.add_mul_mod_self_left]

theorem bool_eq_of_toNat_eq {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

theorem bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> simp

def padFalse (α : List Bool) (b : Bool) : List Bool := if b then α else α.map (fun _ => false)

theorem padFalse_length (α : List Bool) (b : Bool) : (padFalse α b).length = α.length := by
  cases b <;> simp [padFalse]

theorem ofBits_replicate_false (n : ℕ) : ofBits (List.replicate n false) = 0 := by
  induction n with
  | zero => simp [ofBits]
  | succ n ih => rw [List.replicate_succ, ofBits_cons, ih]; simp

theorem ofBits_padFalse (α : List Bool) (b : Bool) :
    ofBits (padFalse α b) = b.toNat * ofBits α := by
  cases b with
  | true => simp [padFalse]
  | false => simp [padFalse, List.map_const', ofBits_replicate_false]

@[simp] theorem padFalse_nil (β : Bool) : padFalse [] β = [] := by cases β <;> rfl

@[simp] theorem addBits_nil_nil (c : Bool) : addBits [] [] c = ([], c) := rfl

theorem padFalse_cons (a : Bool) (α : List Bool) (β : Bool) :
    padFalse (a :: α) β = (if β then a else false) :: padFalse α β := by
  cases β <;> rfl

theorem addBits_cons (x y : Bool) (xs ys : List Bool) (c : Bool) :
    addBits (x :: xs) (y :: ys) c
      = (faSum x y c :: (addBits xs ys (faCarry x y c)).1,
         (addBits xs ys (faCarry x y c)).2) := rfl

/-- One step: `S = ρ + (b ? α : 0)`, output bit `S % 2`, new `ρ = S / 2` (as bit lists). -/
def stepR (α ρ : List Bool) (b : Bool) : Bool × List Bool :=
  let sc := addBits (padFalse α b) ρ false
  let R := sc.1 ++ [sc.2]
  (R.headD false, R.tail)

theorem stepR_val (α ρ : List Bool) (h : ρ.length = α.length) (b : Bool) :
    (stepR α ρ b).1 = decide ((ofBits ρ + b.toNat * ofBits α) % 2 = 1)
    ∧ ofBits ρ + b.toNat * ofBits α = (stepR α ρ b).1.toNat + 2 * ofBits (stepR α ρ b).2
    ∧ (stepR α ρ b).2.length = α.length := by
  have hlen : (padFalse α b).length = ρ.length := by rw [padFalse_length, h]
  have hval := addBits_val (padFalse α b) ρ hlen false
  have hlen2 := addBits_len (padFalse α b) ρ hlen false
  rw [padFalse_length] at hval hlen2
  have hkey : ofBits (addBits (padFalse α b) ρ false).1
      + 2 ^ α.length * (addBits (padFalse α b) ρ false).2.toNat
      = ofBits ρ + b.toNat * ofBits α := by
    rw [hval, ofBits_padFalse]
    simp only [Bool.toNat_false, Nat.add_zero]
    omega
  dsimp only [stepR]
  set R := addBits (padFalse α b) ρ false with hR
  have hdec : ofBits (R.1 ++ [R.2]) = ofBits ρ + b.toNat * ofBits α := by
    rw [ofBits_append, ofBits_singleton, hlen2, hkey]
  refine ⟨?_, ?_, ?_⟩
  · apply bool_eq_of_toNat_eq
    rw [headD_toNat_mod, hdec]
    obtain hh | hh := Nat.mod_two_eq_zero_or_one (ofBits ρ + b.toNat * ofBits α) <;> simp [hh]
  · rw [← hdec, ofBits_headD]
  · rw [List.length_tail, List.length_append, hlen2]; simp

/-- Process the bits `bs` (least significant first) of the multiplier. -/
def run (α : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [], acc, ρ => (acc, ρ)
  | b :: bs, acc, ρ => let s := stepR α ρ b; run α bs (s.1 :: acc) s.2

theorem run_spec (α : List Bool) :
    ∀ (bs acc ρ : List Bool), ρ.length = α.length →
      (run α bs acc ρ).1 = (mbits bs.length (ofBits ρ + ofBits α * ofBits bs)).reverse ++ acc
      ∧ ofBits (run α bs acc ρ).2 = (ofBits ρ + ofBits α * ofBits bs) / 2 ^ bs.length
      ∧ (run α bs acc ρ).2.length = α.length := by
  intro bs
  induction bs with
  | nil =>
      intro acc ρ h
      refine ⟨?_, ?_, ?_⟩
      · simp only [run, List.length_nil, mbits, List.range_zero, List.map_nil,
          List.reverse_nil, List.nil_append]
      · simp only [run, ofBits, List.foldr_nil, List.length_nil, Nat.mul_zero, Nat.add_zero,
          pow_zero, Nat.div_one]
      · simpa only [run] using h
  | cons b bs ih =>
      intro acc ρ h
      obtain ⟨hv1, hv2, hv3⟩ := stepR_val α ρ h b
      obtain ⟨h1, h2, h3⟩ := ih ((stepR α ρ b).1 :: acc) (stepR α ρ b).2 hv3
      set out := (stepR α ρ b).1 with hout'
      set ρ' := (stepR α ρ b).2 with hρ'
      have hv1' : out = decide ((ofBits ρ + b.toNat * ofBits α) % 2 = 1) := hv1
      have hv2' : ofBits ρ + b.toNat * ofBits α = out.toNat + 2 * ofBits ρ' := hv2
      have h1' : (run α bs (out :: acc) ρ').1
          = (mbits bs.length (ofBits ρ' + ofBits α * ofBits bs)).reverse ++ (out :: acc) := h1
      have h2' : ofBits (run α bs (out :: acc) ρ').2
          = (ofBits ρ' + ofBits α * ofBits bs) / 2 ^ bs.length := h2
      have h3' : (run α bs (out :: acc) ρ').2.length = α.length := h3
      have hX : ofBits ρ + ofBits α * ofBits (b :: bs)
          = out.toNat + 2 * (ofBits ρ' + ofBits α * ofBits bs) := by
        rw [ofBits_cons]
        have e1 : ofBits ρ + ofBits α * (b.toNat + 2 * ofBits bs)
            = (ofBits ρ + b.toNat * ofBits α) + 2 * (ofBits α * ofBits bs) := by ring
        rw [e1, hv2']
        ring
      have houtl : out.toNat ≤ 1 := bool_toNat_le_one out
      have hYmod : (ofBits ρ + b.toNat * ofBits α) % 2
          = (ofBits ρ + ofBits α * ofBits (b :: bs)) % 2 := by rw [hX]; omega
      have hout : out = decide ((ofBits ρ + ofBits α * ofBits (b :: bs)) % 2 = 1) := by
        rw [hv1', hYmod]
      have hdiv : (ofBits ρ + ofBits α * ofBits (b :: bs)) / 2
          = ofBits ρ' + ofBits α * ofBits bs := by
        rw [hX]; omega
      dsimp only [run]
      rw [← hout', ← hρ']
      refine ⟨?_, ?_, ?_⟩
      · rw [h1', List.length_cons, mbits_succ, hout, hdiv, List.reverse_cons]
        rw [List.append_assoc, List.singleton_append]
      · rw [h2', List.length_cons, pow_succ, Nat.mul_comm (2 ^ bs.length) 2,
            ← Nat.div_div_eq_div_mul, hdiv]
      · exact h3'

theorem stripHigh_eq_nil_iff (l : List Bool) : stripHigh l = [] ↔ ofBits l = 0 := by
  rw [stripHigh_eq_bits]
  constructor
  · intro h
    by_contra h0
    exact (bits_ne_nil_iff (n := ofBits l)).mpr h0 h
  · intro h0
    rw [h0]; rfl

/-- The value of `mbits n X ++ ρ` when `ρ` is the `m`-bit representation of `X / 2 ^ n`. -/
theorem finalize_val (n X : ℕ) (ρ : List Bool) (h : ofBits ρ = X / 2 ^ n) :
    ofBits (mbits n X ++ ρ) = X := by
  rw [ofBits_append, ofBits_mbits, mbits_length, h]
  exact Nat.mod_add_div X (2 ^ n)

/-- The bit list produced by the multiplier loop is (a padded version of) the binary expansion of
`ofBits α * Bv`. -/
theorem run_final_val (α : List Bool) (Bv : ℕ) :
    ofBits ((run α Bv.bits [] (List.replicate α.length false)).1.reverse
      ++ (run α Bv.bits [] (List.replicate α.length false)).2) = ofBits α * Bv := by
  obtain ⟨h1, h2, -⟩ := run_spec α Bv.bits [] (List.replicate α.length false)
    (by simp [List.length_replicate])
  rw [ofBits_bits, ofBits_replicate_false, Nat.zero_add] at h1 h2
  have h1' : (run α Bv.bits [] (List.replicate α.length false)).1.reverse
      = mbits Bv.bits.length (ofBits α * Bv) := by
    rw [h1, List.append_nil, List.reverse_reverse]
  rw [h1', finalize_val _ _ _ h2]

end MulS
end Work.IntLib
