import Mathlib
import Submission.Work.Transform.chirpAux
import Submission.Work.Transform.Defs
import Submission.Work.Transform.chirpTabKit

/-!
# The chirp table word `Work.Transform.chirpTabWordBnd`

`int p :: int t :: R ↦ cvecVal c :: int p :: R`, where `c` has length `t`, lies in `C̃◦ᵗ` and
satisfies `2^p ‖c_m - ζ_t^{m²}‖ < 2` for every `m < t` (`ζ_t = e^{πi/t}`): the one-dimensional
Bluestein chirp table of a single dimension, the input of `Work.Transform.chirpWord`.

Construction, from the library `Prop`s only:

* the list of records `idxRecs t = (List.range t).map (fun i => cons (int i) (int t))` of length `t`
  (`KernelLib.roll`, `KernelLib.dup`, `LayoutLib.replicate` with payload `int t`,
  `LayoutLib.enumerate`);
* `KernelLib.mapList` over it with the per-element word
  `unconsV; roll 1; dup; IntLib.add; roll 1; dup; IntLib.mulS; pick 2; FxLib.cis`, which turns
  `cons (int m) (int t) :: int p :: R` into `cfxVal w :: int p :: R` with `w ∈ C̃◦` and
  `2^p ‖w - ζ_t^{m²}‖ < 2` (the identity `e^{2πi m²/(2t)} = ζ_t^{m²}` of `chirpTabKit`); the
  `pick 2` is needed because `cis` consumes the `int p` below its two arguments;
* extracting the coefficient list from the list of values (`chirpTabExtract`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.Transform

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

/-! ## `WordR` plumbing -/

/-- Sequential composition of two exact-state steps. -/
theorem seqStep {main p q : Cmd} {A B : List Val} {P : List Val → Prop} {c₁ c₂ : ℕ}
    (h₁ : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁))
    (h₂ : WordR main q (fun vs => vs = B) (fun _ out => P out) (fun _ => c₂)) :
    WordR main (p ;;; q) (fun vs => vs = A) (fun _ out => P out) (fun _ => c₁ + c₂) := by
  refine Work.Kernel.WordR_conseq (Work.Kernel.WordR_seq (B := fun _ => c₂) h₁ h₂ ?_)
    ?_ ?_ ?_
  · intro vs mid hvs hmid
    exact ⟨hmid, le_refl _⟩
  · intro vs hvs; exact hvs
  · intro vs out hvs hq
    obtain ⟨mid, hmid, hq'⟩ := hq
    exact hq'
  · intro vs hvs; exact le_rfl

/-- Turn a `WordR` with a structural pre/post into an exact-state one. -/
theorem liftStep {main p : Cmd} {P : List Val → Prop} {Q : List Val → List Val → Prop}
    {C : List Val → ℕ} (h : WordR main p P Q C) {L M : List Val} {c : ℕ}
    (hP : P L) (hQ : ∀ out, Q L out → out = M) (hC : C L ≤ c) :
    WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => c) := by
  refine Work.Kernel.WordR_conseq h ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; exact hP
  · intro vs out hvs hq; rw [hvs] at hq; exact hQ out hq
  · intro vs hvs; rw [hvs]; exact hC

/-- The list of index records of the chirp table: entry `i` is `cons (int i) (int t)`. -/
def idxRecs (t : ℕ) : List Val :=
  (List.range t).map (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int (t : ℤ)))

/-- The per-element relation of the chirp table: the record `cons (int m) (int t)` is paired
with a fixed-point number `w ∈ C̃◦` approximating `ζ_t^{m²}` with scaled error `< 2`. -/
def TabRel (p t : ℕ) : Val → (ℤ × ℤ) → Prop := fun x w =>
  ∃ (m : ℕ), x = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ)) ∧ m < t ∧
    inDisc p w ∧ (2 : ℝ) ^ p * ‖fxC p w - zeta t (m * m)‖ < 2

/-- The same relation on `Val`s: the second value is `cfxVal` of a coefficient of the table. -/
def TabRelV (p t : ℕ) : Val → Val → Prop := fun x y =>
  ∃ w : ℤ × ℤ, y = cfxVal w ∧ TabRel p t x w

/-- `(List.replicate n a).sum = n * a` for naturals (avoids `nsmul` bookkeeping). -/
theorem sum_replicate_nat (n a : ℕ) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.sum_cons, ih]; ring

/-! ## Piece 1: the list of index records -/

/-- The index-list phase of the chirp table word. -/
theorem chirpTabIdxWord (hK : KernelLib) (hL : LayoutLib) :
    ∃ (prog : Cmd) (C : ℕ), ∀ (main : Cmd) (p t : ℕ) (R : List Val),
      100 ≤ p → 2 ≤ t → t < 2 ^ p →
      WordR main prog (fun vs => vs = Val.int p :: Val.int t :: R)
        (fun _ out => out = ofList (idxRecs t) :: Val.int p :: R)
        (fun _ => C * (t * (p + 1) ^ C) + C) := by
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  obtain ⟨dupP, Kd, hdup⟩ := hK.dup
  obtain ⟨repP, Kre, hrep⟩ := hL.replicate
  obtain ⟨enumP, Ken, henum⟩ := hL.enumerate
  refine ⟨rollP 1 ;;; dupP ;;; repP ;;; enumP, 100 * (Kr + Kd + Kre + Ken) + 100, ?_⟩
  intro main p t R hp ht htp
  set C : ℕ := 100 * (Kr + Kd + Kre + Ken) + 100 with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; omega
  have hCbig : 8 * Kr + 2 * Kd + 4 * Kre + 6 * Ken ≤ C := by rw [hCdef]; omega
  have hp2 : isz (p : ℤ) ≤ p + 2 := isz_natCast_le (Nat.lt_two_pow_self)
  have ht2 : isz (t : ℤ) ≤ p + 2 := isz_natCast_le htp
  have hts : t.size ≤ p := Nat.size_le.mpr htp
  have ht1 : 1 ≤ t := by omega
  let X : ℕ := (p + 1) ^ C
  have hX1 : p + 1 ≤ X := by
    show p + 1 ≤ (p + 1) ^ C
    calc p + 1 = (p + 1) ^ 1 := (pow_one _).symm
      _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) hC1
  have hX0 : 1 ≤ X := le_trans (by omega : 1 ≤ p + 1) hX1
  have hXt : X ≤ t * X + 1 := by
    have h : X ≤ t * X := Nat.le_mul_of_pos_left X (by omega : 0 < t)
    omega
  have hvsz : vsz (ofList (List.replicate t (Val.int (t : ℤ)))) = t + t * isz (t : ℤ) + 1 := by
    rw [vsz_ofList, List.length_replicate, List.map_replicate, vsz_int, sum_replicate_nat]
  let L0 : List Val := Val.int (p : ℤ) :: Val.int (t : ℤ) :: R
  let L1 : List Val := Val.int (t : ℤ) :: Val.int (p : ℤ) :: R
  let L2 : List Val := Val.int (t : ℤ) :: Val.int (t : ℤ) :: Val.int (p : ℤ) :: R
  let L3 : List Val := ofList (List.replicate t (Val.int (t : ℤ))) :: Val.int (p : ℤ) :: R
  let L4 : List Val := ofList (idxRecs t) :: Val.int (p : ℤ) :: R
  have h1 : WordR main (rollP 1) (fun vs => vs = L0) (fun _ out => out = L1)
      (fun _ => Kr * (1 + 1) * (isz (p : ℤ) + isz (t : ℤ) + 1)) := by
    refine liftStep (hroll main 1) ?_ ?_ ?_
    · show 1 < L0.length
      simp only [L0, List.length_cons]
      omega
    · intro out hq
      rw [hq]
      rfl
    · show Kr * (1 + 1) * (((L0.take (1 + 1)).map vsz).sum + 1) ≤
        Kr * (1 + 1) * (isz (p : ℤ) + isz (t : ℤ) + 1)
      simp only [L0, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
      exact le_rfl
  have h2 : WordR main dupP (fun vs => vs = L1) (fun _ out => out = L2)
      (fun _ => Kd * (isz (t : ℤ) + 1)) := by
    refine liftStep (hdup main) ?_ ?_ ?_
    · show L1 ≠ []
      simp [L1]
    · intro out hq
      obtain ⟨v, rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      rw [hout, ← h1.1, ← h1.2]
    · show Kd * (vsz (L1.headD Val.nil) + 1) ≤ Kd * (isz (t : ℤ) + 1)
      rw [show L1.headD Val.nil = Val.int (t : ℤ) from rfl, vsz_int]
  have h3 : WordR main repP (fun vs => vs = L2) (fun _ out => out = L3)
      (fun _ => Kre * ((t + 1) * (isz (t : ℤ) + 1) + isz (t : ℤ) + 1)) := by
    refine liftStep (hrep main t (Val.int (t : ℤ))) ?_ ?_ ?_
    · show ∃ rest, L2 = Val.int (t : ℤ) :: Val.int (t : ℤ) :: rest
      exact ⟨Val.int (p : ℤ) :: R, rfl⟩
    · intro out hq
      obtain ⟨rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      have h2 := List.cons.inj h1.2
      rw [hout, ← h2.2]
    · show Kre * ((t + 1) * (vsz (Val.int (t : ℤ)) + 1) + isz (t : ℤ) + 1) ≤
        Kre * ((t + 1) * (isz (t : ℤ) + 1) + isz (t : ℤ) + 1)
      rw [vsz_int]
  have h4 : WordR main enumP (fun vs => vs = L3) (fun _ out => out = L4)
      (fun _ => Ken * (t + t * isz (t : ℤ) + 1 + t * (t.size + 1) + 1)) := by
    refine liftStep (henum main (List.replicate t (Val.int (t : ℤ)))) ?_ ?_ ?_
    · show ∃ rest, L3 = ofList (List.replicate t (Val.int (t : ℤ))) :: rest
      exact ⟨Val.int (p : ℤ) :: R, rfl⟩
    · intro out hq
      obtain ⟨rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      rw [hout, ← h1.2]
      have hmap : (List.range (List.replicate t (Val.int (t : ℤ))).length).map
            (fun i : ℕ => Val.cons (Val.int (i : ℤ))
              ((List.replicate t (Val.int (t : ℤ))).getD i Val.nil)) = idxRecs t := by
        rw [idxRecs, List.length_replicate]
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        exact congrArg (Val.cons (Val.int (i : ℤ)))
          (List.getD_replicate (Val.int (t : ℤ)) hi)
      rw [hmap]
    · show Ken * (vsz (ofList (List.replicate t (Val.int (t : ℤ)))) +
          (List.replicate t (Val.int (t : ℤ))).length *
            ((List.replicate t (Val.int (t : ℤ))).length.size + 1) + 1) ≤
        Ken * (t + t * isz (t : ℤ) + 1 + t * (t.size + 1) + 1)
      rw [hvsz, List.length_replicate]
  have hchain := seqStep h1 (seqStep h2 (seqStep h3 h4))
  refine Work.Kernel.WordR_conseq hchain ?_ ?_ ?_
  · intro vs hvs
    simpa [L0] using hvs
  · intro vs out hvs hq
    simpa [L4] using hq
  · intro vs hvs
    have hb1 : Kr * (1 + 1) * (isz (p : ℤ) + isz (t : ℤ) + 1) ≤ Kr * 8 * (t * X + 1) := by
      have hA : isz (p : ℤ) + isz (t : ℤ) + 1 ≤ 4 * (p + 1) := by omega
      have hB : 2 * (isz (p : ℤ) + isz (t : ℤ) + 1) ≤ 8 * X := by
        calc 2 * (isz (p : ℤ) + isz (t : ℤ) + 1) ≤ 2 * (4 * (p + 1)) :=
              Nat.mul_le_mul_left 2 hA
          _ = 8 * (p + 1) := by ring
          _ ≤ 8 * X := Nat.mul_le_mul_left 8 hX1
      have hD : 8 * X ≤ 8 * (t * X + 1) := Nat.mul_le_mul_left 8 hXt
      calc Kr * (1 + 1) * (isz (p : ℤ) + isz (t : ℤ) + 1)
          = Kr * (2 * (isz (p : ℤ) + isz (t : ℤ) + 1)) := by ring
        _ ≤ Kr * (8 * X) := Nat.mul_le_mul_left Kr hB
        _ ≤ Kr * (8 * (t * X + 1)) := Nat.mul_le_mul_left Kr hD
        _ = Kr * 8 * (t * X + 1) := by ring
    have hb2 : Kd * (isz (t : ℤ) + 1) ≤ 2 * Kd * (t * X + 1) := by
      have hA : isz (t : ℤ) + 1 ≤ 2 * (t * X + 1) := by
        have h1 : isz (t : ℤ) + 1 ≤ 2 * (p + 1) := by omega
        have h2 : 2 * (p + 1) ≤ 2 * X := Nat.mul_le_mul_left 2 hX1
        have h3 : 2 * X ≤ 2 * (t * X + 1) := by
          have : X ≤ t * X + 1 := hXt
          nlinarith [Nat.zero_le X]
        linarith
      calc Kd * (isz (t : ℤ) + 1) ≤ Kd * (2 * (t * X + 1)) := Nat.mul_le_mul_left Kd hA
        _ = 2 * Kd * (t * X + 1) := by ring
    have hb3 : Kre * ((t + 1) * (isz (t : ℤ) + 1) + isz (t : ℤ) + 1) ≤
        4 * Kre * (t * X + 1) := by
      have hA : (t + 1) * (isz (t : ℤ) + 1) + isz (t : ℤ) + 1 ≤ 4 * (t * X + 1) := by
        have e1 : (t + 1) * (isz (t : ℤ) + 1) ≤ (t + 1) * (p + 3) :=
          Nat.mul_le_mul_left (t + 1) (by omega)
        have e2 : isz (t : ℤ) + 1 ≤ p + 3 := by omega
        have e3 : (t + 1) * (p + 3) + (p + 3) ≤ 4 * (t * X + 1) := by
          have f1 : t + 2 ≤ 2 * t := by omega
          have f2 : p + 3 ≤ 2 * X := by
            have h40 : p + 3 ≤ 2 * (p + 1) := by omega
            have h41 : 2 * (p + 1) ≤ 2 * X := Nat.mul_le_mul_left 2 hX1
            linarith
          calc (t + 1) * (p + 3) + (p + 3) = (t + 2) * (p + 3) := by ring
            _ ≤ (t + 2) * (2 * X) := Nat.mul_le_mul_left (t + 2) f2
            _ ≤ (2 * t) * (2 * X) := Nat.mul_le_mul_right (2 * X) f1
            _ = 4 * (t * X) := by ring
            _ ≤ 4 * (t * X + 1) := by omega
        linarith
      calc Kre * ((t + 1) * (isz (t : ℤ) + 1) + isz (t : ℤ) + 1)
          ≤ Kre * (4 * (t * X + 1)) := Nat.mul_le_mul_left Kre hA
        _ = 4 * Kre * (t * X + 1) := by ring
    have hb4 : Ken * (t + t * isz (t : ℤ) + 1 + t * (t.size + 1) + 1) ≤
        6 * Ken * (t * X + 1) := by
      have hA : t + t * isz (t : ℤ) + 1 + t * (t.size + 1) + 1 ≤ 6 * (t * X + 1) := by
        have h1 : t * isz (t : ℤ) ≤ t * (2 * X) := by
          have : isz (t : ℤ) ≤ 2 * X := by
            have h40 : isz (t : ℤ) ≤ 2 * (p + 1) := by omega
            have h41 : 2 * (p + 1) ≤ 2 * X := Nat.mul_le_mul_left 2 hX1
            linarith
          exact Nat.mul_le_mul_left t this
        have h2 : t * (t.size + 1) ≤ t * X := by
          have : t.size + 1 ≤ X := by omega
          exact Nat.mul_le_mul_left t this
        have h3 : t + 2 ≤ 2 * t * X := by
          have e1 : t + 2 ≤ 2 * t := by omega
          have e3 : 2 * t * 1 ≤ 2 * t * X := Nat.mul_le_mul_left (2 * t) hX0
          omega
        nlinarith [h1, h2, h3, Nat.zero_le t, Nat.zero_le X]
      calc Ken * (t + t * isz (t : ℤ) + 1 + t * (t.size + 1) + 1)
          ≤ Ken * (6 * (t * X + 1)) := Nat.mul_le_mul_left Ken hA
        _ = 6 * Ken * (t * X + 1) := by ring
    have hXeq : C * (t * (p + 1) ^ C) + C = C * (t * X) + C := rfl
    rw [hXeq]
    nlinarith [hb1, hb2, hb3, hb4, hCbig, Nat.zero_le t, Nat.zero_le X]

/-! ## Piece 2: the per-element phase word -/

/-- The per-element phase word: `cons (int m) (int t) :: int p :: R` becomes
`cfxVal w :: int p :: R` with `w ∈ C̃◦` and `2^p ‖w - ζ_t^{m²}‖ < 2`. -/
theorem chirpTabElemWord (hK : KernelLib) (hI : IntLib) (hF : FxLib) :
    ∃ (prog : Cmd) (C : ℕ), ∀ (main : Cmd) (p t m : ℕ) (R : List Val),
      100 ≤ p → 2 ≤ t → t < 2 ^ p → m < t →
      WordR main prog
        (fun vs => vs = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ)) :: Val.int (p : ℤ) :: R)
        (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: Val.int (p : ℤ) :: R ∧ inDisc p w ∧
          (2 : ℝ) ^ p * ‖fxC p w - zeta t (m * m)‖ < 2)
        (fun _ => C * (p + 1) ^ C) := by
  obtain ⟨rollP, Kr, hroll⟩ := hK.roll
  obtain ⟨dupP, Kd, hdup⟩ := hK.dup
  obtain ⟨pickP, Kp, hpick⟩ := hK.pick
  obtain ⟨unconsP, Ku, huncons⟩ := hK.unconsV
  obtain ⟨addP, Ka, hadd⟩ := hI.add
  obtain ⟨mulSP, Kms, hmulS⟩ := hI.mulS
  obtain ⟨cisP, Kcs, hcis⟩ := hF.cis
  refine ⟨unconsP ;;; rollP 1 ;;; dupP ;;; addP ;;; rollP 1 ;;; dupP ;;; mulSP ;;; pickP 2 ;;; cisP,
    100 * (Kr + Kd + Kp + Ku + Ka + Kms + Kcs) + 100, ?_⟩
  intro main p t m R hp ht htp hm
  set C : ℕ := 100 * (Kr + Kd + Kp + Ku + Ka + Kms + Kcs) + 100 with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; omega
  have hCbig : Ku + 16 * Kr + 4 * Kd + 4 * Ka + 4 * Kms + 24 * Kp + Kcs ≤ C := by
    rw [hCdef]; omega
  have hC2 : 2 ≤ C := by omega
  have hC2k : 2 * Kcs ≤ C := by rw [hCdef]; omega
  have hp2 : isz (p : ℤ) ≤ p + 2 := isz_natCast_le (Nat.lt_two_pow_self)
  have ht2 : isz (t : ℤ) ≤ p + 2 := isz_natCast_le htp
  have hm2 : isz (m : ℤ) ≤ p + 2 := isz_natCast_le (lt_trans hm htp)
  have htt : isz ((t + t : ℕ) : ℤ) ≤ p + 3 := isz_two_mul_le htp
  have hmm : isz (((m * m : ℕ)) : ℤ) ≤ 2 * p + 2 := isz_mul_self_le (lt_trans hm htp)
  let X : ℕ := (p + 1) ^ C
  have hX1 : p + 1 ≤ X := by
    show p + 1 ≤ (p + 1) ^ C
    calc p + 1 = (p + 1) ^ 1 := (pow_one _).symm
      _ ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) hC1
  have hX0 : 1 ≤ X := le_trans (by omega : 1 ≤ p + 1) hX1
  have hXs : (p + 1) ^ 2 ≤ X := by
    show (p + 1) ^ 2 ≤ (p + 1) ^ C
    exact Nat.pow_le_pow_right (by omega) hC2
  have hto : t ≠ 0 := by omega
  let B0 : List Val :=
    Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ)) :: Val.int (p : ℤ) :: R
  let B1 : List Val := Val.int (m : ℤ) :: Val.int (t : ℤ) :: Val.int (p : ℤ) :: R
  let B2 : List Val := Val.int (t : ℤ) :: Val.int (m : ℤ) :: Val.int (p : ℤ) :: R
  let B3 : List Val :=
    Val.int (t : ℤ) :: Val.int (t : ℤ) :: Val.int (m : ℤ) :: Val.int (p : ℤ) :: R
  let B4 : List Val :=
    Val.int ((t + t : ℕ) : ℤ) :: Val.int (m : ℤ) :: Val.int (p : ℤ) :: R
  let B5 : List Val :=
    Val.int (m : ℤ) :: Val.int ((t + t : ℕ) : ℤ) :: Val.int (p : ℤ) :: R
  let B6 : List Val := Val.int (m : ℤ) :: Val.int (m : ℤ) ::
    Val.int ((t + t : ℕ) : ℤ) :: Val.int (p : ℤ) :: R
  let B7 : List Val := Val.int ((m * m : ℕ) : ℤ) ::
    Val.int ((t + t : ℕ) : ℤ) :: Val.int (p : ℤ) :: R
  let B8 : List Val := Val.int (p : ℤ) :: Val.int ((m * m : ℕ) : ℤ) ::
    Val.int ((t + t : ℕ) : ℤ) :: Val.int (p : ℤ) :: R
  have h1 : WordR main unconsP (fun vs => vs = B0) (fun _ out => out = B1) (fun _ => Ku) := by
    refine liftStep (huncons main) ?_ ?_ ?_
    · show ∃ a b rest, B0 = Val.cons a b :: rest
      exact ⟨Val.int (m : ℤ), Val.int (t : ℤ), Val.int (p : ℤ) :: R, rfl⟩
    · intro out hq
      obtain ⟨a, b, rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      have h2 := Val.cons.inj h1.1
      rw [hout, ← h2.1, ← h2.2, ← h1.2]
    · exact le_rfl
  have h2 : WordR main (rollP 1) (fun vs => vs = B1) (fun _ out => out = B2)
      (fun _ => Kr * (1 + 1) * (isz (m : ℤ) + isz (t : ℤ) + 1)) := by
    refine liftStep (hroll main 1) ?_ ?_ ?_
    · show 1 < B1.length
      simp only [B1, List.length_cons]
      omega
    · intro out hq
      rw [hq]
      rfl
    · show Kr * (1 + 1) * (((B1.take (1 + 1)).map vsz).sum + 1) ≤
        Kr * (1 + 1) * (isz (m : ℤ) + isz (t : ℤ) + 1)
      simp only [B1, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
      exact le_rfl
  have h3 : WordR main dupP (fun vs => vs = B2) (fun _ out => out = B3)
      (fun _ => Kd * (isz (t : ℤ) + 1)) := by
    refine liftStep (hdup main) ?_ ?_ ?_
    · show B2 ≠ []
      simp [B2]
    · intro out hq
      obtain ⟨v, rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      rw [hout, ← h1.1, ← h1.2]
    · show Kd * (vsz (B2.headD Val.nil) + 1) ≤ Kd * (isz (t : ℤ) + 1)
      rw [show B2.headD Val.nil = Val.int (t : ℤ) from rfl, vsz_int]
  have h4 : WordR main addP (fun vs => vs = B3) (fun _ out => out = B4)
      (fun _ => Ka * (isz (t : ℤ) + isz (t : ℤ))) := by
    refine Work.Kernel.WordR_conseq (hadd main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨(t : ℤ), (t : ℤ), Val.int (m : ℤ) :: Val.int (p : ℤ) :: R, rfl, trivial⟩
    · intro vs out hvs hq
      obtain ⟨a, b, rest, hv, hout⟩ := hq
      rw [hvs] at hv
      have h1 := List.cons.inj hv
      have h2 := List.cons.inj h1.2
      have ha : (t : ℤ) = a := Val.int.inj h1.1
      have hb : (t : ℤ) = b := Val.int.inj h2.1
      rw [hout, ← ha, ← hb, ← h2.2]
      simp only [B4]
      push_cast
      rfl
    · intro vs hvs
      rw [hvs]
      exact le_of_eq rfl
  have h5 : WordR main (rollP 1) (fun vs => vs = B4) (fun _ out => out = B5)
      (fun _ => Kr * (1 + 1) * (isz ((t + t : ℕ) : ℤ) + isz (m : ℤ) + 1)) := by
    refine liftStep (hroll main 1) ?_ ?_ ?_
    · show 1 < B4.length
      simp only [B4, List.length_cons]
      omega
    · intro out hq
      rw [hq]
      rfl
    · show Kr * (1 + 1) * (((B4.take (1 + 1)).map vsz).sum + 1) ≤
        Kr * (1 + 1) * (isz ((t + t : ℕ) : ℤ) + isz (m : ℤ) + 1)
      simp only [B4, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
      exact le_rfl
  have h6 : WordR main dupP (fun vs => vs = B5) (fun _ out => out = B6)
      (fun _ => Kd * (isz (m : ℤ) + 1)) := by
    refine liftStep (hdup main) ?_ ?_ ?_
    · show B5 ≠ []
      simp [B5]
    · intro out hq
      obtain ⟨v, rest, hv, hout⟩ := hq
      have h1 := List.cons.inj hv
      rw [hout, ← h1.1, ← h1.2]
    · show Kd * (vsz (B5.headD Val.nil) + 1) ≤ Kd * (isz (m : ℤ) + 1)
      rw [show B5.headD Val.nil = Val.int (m : ℤ) from rfl, vsz_int]
  have h7 : WordR main mulSP (fun vs => vs = B6) (fun _ out => out = B7)
      (fun _ => Kms * isz (m : ℤ) * isz (m : ℤ)) := by
    refine Work.Kernel.WordR_conseq (hmulS main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨(m : ℤ), (m : ℤ), Val.int ((t + t : ℕ) : ℤ) :: Val.int (p : ℤ) :: R, rfl, trivial⟩
    · intro vs out hvs hq
      obtain ⟨a, b, rest, hv, hout⟩ := hq
      rw [hvs] at hv
      have h1 := List.cons.inj hv
      have h2 := List.cons.inj h1.2
      have ha : (m : ℤ) = a := Val.int.inj h1.1
      have hb : (m : ℤ) = b := Val.int.inj h2.1
      rw [hout, ← ha, ← hb, ← h2.2]
      simp only [B7]
      push_cast
      rfl
    · intro vs hvs
      rw [hvs]
      exact le_of_eq rfl
  have h8 : WordR main (pickP 2) (fun vs => vs = B7) (fun _ out => out = B8)
      (fun _ => Kp * (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) +
        isz (p : ℤ)) + 1)) := by
    refine liftStep (hpick main 2) ?_ ?_ ?_
    · show 2 < B7.length
      simp only [B7, List.length_cons]
      omega
    · intro out hq
      rw [hq]
      rfl
    · show Kp * (2 + 1) * (((B7.take (2 + 1)).map vsz).sum + 1) ≤
        Kp * (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) + isz (p : ℤ)) + 1)
      simp only [B7, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, vsz_int, Nat.add_zero]
      exact le_rfl
  have h9 : WordR main cisP (fun vs => vs = B8)
      (fun _ out => ∃ (w : ℤ × ℤ), out = cfxVal w :: Val.int (p : ℤ) :: R ∧ inDisc p w ∧
        (2 : ℝ) ^ p * ‖fxC p w - zeta t (m * m)‖ < 2)
      (fun _ => Kcs * (p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ)) ^ Kcs) := by
    refine Work.Kernel.WordR_conseq
      (hcis main p (((m * m : ℕ)) : ℤ) (t + t) hp (by omega)) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨Val.int (p : ℤ) :: R, rfl⟩
    · intro vs out hvs hq
      obtain ⟨rest, w, hv, hout, hdisc, hbnd⟩ := hq
      rw [hvs] at hv
      have h1 := List.cons.inj hv
      have h2 := List.cons.inj h1.2
      have h3 := List.cons.inj h2.2
      refine ⟨w, ?_, hdisc, ?_⟩
      · rw [hout, h3.2]
      · rw [← exp_cis_eq_zeta t (m * m) hto]
        exact hbnd
    · intro vs hvs
      exact le_rfl
  have hchain := seqStep h1 (seqStep h2 (seqStep h3 (seqStep h4 (seqStep h5
    (seqStep h6 (seqStep h7 (seqStep h8 h9)))))))
  refine Work.Kernel.WordR_conseq hchain ?_ ?_ ?_
  · intro vs hvs
    simpa [B0] using hvs
  · intro vs out hvs hq
    exact hq
  · intro vs hvs
    have b1 : Ku ≤ Ku * X := by
      calc Ku = Ku * 1 := (mul_one Ku).symm
        _ ≤ Ku * X := Nat.mul_le_mul_left Ku hX0
    have b2 : Kr * (1 + 1) * (isz (m : ℤ) + isz (t : ℤ) + 1) ≤ Kr * 8 * X := by
      have hA : 2 * (isz (m : ℤ) + isz (t : ℤ) + 1) ≤ 8 * X := by
        have e1 : isz (m : ℤ) + isz (t : ℤ) + 1 ≤ 4 * (p + 1) := by omega
        calc 2 * (isz (m : ℤ) + isz (t : ℤ) + 1) ≤ 2 * (4 * (p + 1)) :=
              Nat.mul_le_mul_left 2 e1
          _ = 8 * (p + 1) := by ring
          _ ≤ 8 * X := Nat.mul_le_mul_left 8 hX1
      calc Kr * (1 + 1) * (isz (m : ℤ) + isz (t : ℤ) + 1)
          = Kr * (2 * (isz (m : ℤ) + isz (t : ℤ) + 1)) := by ring
        _ ≤ Kr * (8 * X) := Nat.mul_le_mul_left Kr hA
        _ = Kr * 8 * X := by ring
    have b3 : Kd * (isz (t : ℤ) + 1) ≤ 2 * Kd * X := by
      have hA : isz (t : ℤ) + 1 ≤ 2 * X := by
        have e1 : isz (t : ℤ) + 1 ≤ 2 * (p + 1) := by omega
        have e2 : 2 * (p + 1) ≤ 2 * X := Nat.mul_le_mul_left 2 hX1
        linarith
      calc Kd * (isz (t : ℤ) + 1) ≤ Kd * (2 * X) := Nat.mul_le_mul_left Kd hA
        _ = 2 * Kd * X := by ring
    have b4 : Ka * (isz (t : ℤ) + isz (t : ℤ)) ≤ 4 * Ka * X := by
      have e1 : isz (t : ℤ) + isz (t : ℤ) ≤ 4 * X := by
        have e0 : isz (t : ℤ) + isz (t : ℤ) ≤ 4 * (p + 1) := by omega
        have e4 : 4 * (p + 1) ≤ 4 * X := Nat.mul_le_mul_left 4 hX1
        linarith
      calc Ka * (isz (t : ℤ) + isz (t : ℤ)) ≤ Ka * (4 * X) := Nat.mul_le_mul_left Ka e1
        _ = 4 * Ka * X := by ring
    have b5 : Kr * (1 + 1) * (isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1) ≤ Kr * 8 * X := by
      have hA : 2 * (isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1) ≤ 8 * X := by
        have e1 : isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1 ≤ 4 * (p + 1) := by omega
        calc 2 * (isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1) ≤ 2 * (4 * (p + 1)) :=
              Nat.mul_le_mul_left 2 e1
          _ = 8 * (p + 1) := by ring
          _ ≤ 8 * X := Nat.mul_le_mul_left 8 hX1
      calc Kr * (1 + 1) * (isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1)
          = Kr * (2 * (isz (m : ℤ) + isz ((t + t : ℕ) : ℤ) + 1)) := by ring
        _ ≤ Kr * (8 * X) := Nat.mul_le_mul_left Kr hA
        _ = Kr * 8 * X := by ring
    have b6 : Kd * (isz (m : ℤ) + 1) ≤ 2 * Kd * X := by
      have hA : isz (m : ℤ) + 1 ≤ 2 * X := by
        have e1 : isz (m : ℤ) + 1 ≤ 2 * (p + 1) := by omega
        have e2 : 2 * (p + 1) ≤ 2 * X := Nat.mul_le_mul_left 2 hX1
        linarith
      calc Kd * (isz (m : ℤ) + 1) ≤ Kd * (2 * X) := Nat.mul_le_mul_left Kd hA
        _ = 2 * Kd * X := by ring
    have b7 : Kms * isz (m : ℤ) * isz (m : ℤ) ≤ 4 * Kms * X := by
      have e1 : isz (m : ℤ) ≤ 2 * (p + 1) := by omega
      have e2 : isz (m : ℤ) * isz (m : ℤ) ≤ (2 * (p + 1)) * (2 * (p + 1)) :=
        Nat.mul_le_mul e1 e1
      have e3 : (2 * (p + 1)) * (2 * (p + 1)) = 4 * (p + 1) ^ 2 := by ring
      rw [e3] at e2
      have e4 : 4 * (p + 1) ^ 2 ≤ 4 * X := Nat.mul_le_mul_left 4 hXs
      calc Kms * isz (m : ℤ) * isz (m : ℤ) = Kms * (isz (m : ℤ) * isz (m : ℤ)) := by ring
        _ ≤ Kms * (4 * X) := Nat.mul_le_mul_left Kms (by linarith)
        _ = 4 * Kms * X := by ring
    have b8 : Kp * (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) +
        isz (p : ℤ)) + 1) ≤ 24 * Kp * X := by
      have hA : (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) +
          isz (p : ℤ)) + 1) ≤ 24 * X := by
        have e1 : isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) + isz (p : ℤ)) + 1 ≤
            4 * (p + 2) := by omega
        calc (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) + isz (p : ℤ)) + 1)
            = 3 * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) + isz (p : ℤ)) + 1) := by
              norm_num
          _ ≤ 3 * (4 * (p + 2)) := Nat.mul_le_mul_left 3 e1
          _ = 12 * (p + 2) := by ring
          _ ≤ 24 * X := by
              have h1 : 12 * (p + 2) ≤ 24 * (p + 1) := by omega
              have h2 : 24 * (p + 1) ≤ 24 * X := Nat.mul_le_mul_left 24 hX1
              linarith
      calc Kp * (2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) + isz (p : ℤ)) + 1)
          = Kp * ((2 + 1) * (isz (((m * m : ℕ)) : ℤ) + (isz ((t + t : ℕ) : ℤ) +
              isz (p : ℤ)) + 1)) := by ring
        _ ≤ Kp * (24 * X) := Nat.mul_le_mul_left Kp hA
        _ = 24 * Kp * X := by ring
    have b9 : Kcs * (p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ)) ^ Kcs ≤ Kcs * X := by
      have hA : p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ) ≤ (p + 1) ^ 2 := by
        have e1 : p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ) ≤
            p + (2 * p + 2) + (p + 3) := by omega
        have e2 : p + (2 * p + 2) + (p + 3) ≤ (p + 1) ^ 2 := by nlinarith
        linarith
      have hB : (p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ)) ^ Kcs ≤
          ((p + 1) ^ 2) ^ Kcs := Nat.pow_le_pow_left hA Kcs
      have hC : ((p + 1) ^ 2) ^ Kcs = (p + 1) ^ (2 * Kcs) := by rw [← pow_mul]
      have hD : (p + 1) ^ (2 * Kcs) ≤ (p + 1) ^ C := Nat.pow_le_pow_right (by omega) hC2k
      calc Kcs * (p + isz (((m * m : ℕ)) : ℤ) + isz ((t + t : ℕ) : ℤ)) ^ Kcs
          ≤ Kcs * ((p + 1) ^ 2) ^ Kcs := Nat.mul_le_mul_left Kcs hB
        _ = Kcs * (p + 1) ^ (2 * Kcs) := by rw [hC]
        _ ≤ Kcs * (p + 1) ^ C := Nat.mul_le_mul_left Kcs hD
        _ = Kcs * X := rfl
    have hXeq : C * (p + 1) ^ C = C * X := rfl
    rw [hXeq]
    nlinarith [b1, b2, b3, b4, b5, b6, b7, b8, b9, hCbig, Nat.zero_le X]

/-! ## Piece 3: extracting the coefficient vector -/

/-- Extraction of a list of coefficients from a list of values pointwise related to `xs`. -/
theorem extractAux (R : Val → (ℤ × ℤ) → Prop) :
    ∀ (xs : List Val) (ys : List Val),
      List.Forall₂ (fun x y => ∃ z : ℤ × ℤ, y = cfxVal z ∧ R x z) xs ys →
      ∃ vs : List (ℤ × ℤ), ys = vs.map cfxVal ∧ vs.length = xs.length ∧
        ∀ i, i < xs.length → R (xs.getD i Val.nil) (vs.getD i (0, 0)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases h with
      | nil => exact ⟨[], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons a as ih =>
      intro ys h
      cases h with
      | cons hhead htail =>
          obtain ⟨z, hy, hR⟩ := hhead
          obtain ⟨vs, hys, hlen, hP⟩ := ih _ htail
          refine ⟨z :: vs, ?_, ?_, ?_⟩
          · rw [hy, hys]; rfl
          · simp [hlen]
          · intro i hi
            cases i with
            | zero => simpa using hR
            | succ j => simpa using hP j (by simpa using hi)

/-- Combinatorial extraction step of the chirp table word. -/
theorem chirpTabExtract (p t : ℕ) (ys : List Val)
    (h : List.Forall₂ (TabRelV p t) (idxRecs t) ys) :
    ∃ c : List (ℤ × ℤ), ys = c.map cfxVal ∧ c.length = t ∧ InDiscVec p t c ∧
      ∀ m < t, (2 : ℝ) ^ p * ‖fxC p (c.getD m (0, 0)) - zeta t (m * m)‖ < 2 := by
  have hxslen : (idxRecs t).length = t := by simp [idxRecs]
  obtain ⟨c, hys, hlen, hP⟩ := extractAux (TabRel p t) (idxRecs t) ys h
  refine ⟨c, hys, ?_, ?_, ?_⟩
  · rw [hlen, hxslen]
  · refine ⟨?_, ?_⟩
    · rw [hlen, hxslen]
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
      obtain ⟨m, -, -, hdisc, -⟩ := hP i (by rw [← hlen]; exact hi)
      rwa [List.getD_eq_getElem _ _ hi] at hdisc
  · intro m hm
    have hm' : m < (idxRecs t).length := by rw [hxslen]; exact hm
    obtain ⟨m', heq, hm'lt, hdisc, hbnd⟩ := hP m hm'
    have h2 : (idxRecs t).getD m Val.nil = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ)) := by
      rw [idxRecs]
      exact getD_map_range (fun i : ℕ => Val.cons (Val.int (i : ℤ)) (Val.int (t : ℤ)))
        Val.nil (by simpa only [idxRecs, List.length_map, List.length_range] using hm')
    have h3 : (m' : ℤ) = (m : ℤ) := Val.int.inj (Val.cons.inj (by rw [← heq, h2])).1
    have h5 : m' = m := by exact_mod_cast h3
    rw [h5] at hbnd
    exact hbnd

/-! ## Piece 4: the cost contraction -/

/-- Cost contraction for the chirp table word, in the form with an abstract budget `K`. -/
theorem chirpTabCostGen (Ci Ce Km K p t : ℕ) (hp : 100 ≤ p)
    (hsum : Ci + Ce + Km ≤ K) (hCK : Ci + Km ≤ K) (hCi : Ci ≤ K) (hCe : Ce ≤ K)
    (hKm : Km ≤ K) (hK2 : 2 ≤ K) :
    Ci * (t * (p + 1) ^ Ci) + Ci + (t * (Ce * (p + 1) ^ Ce + Km * (2 * p + 9)) + Km) ≤
      K * (t * (p + 1) ^ K) + K := by
  have hbase : 1 ≤ p + 1 := by omega
  have hXCi : (p + 1) ^ Ci ≤ (p + 1) ^ K := Nat.pow_le_pow_right hbase hCi
  have hXCe : (p + 1) ^ Ce ≤ (p + 1) ^ K := Nat.pow_le_pow_right hbase hCe
  have h29 : 2 * p + 9 ≤ (p + 1) ^ K := by
    have h1 : 2 * p + 9 ≤ (p + 1) ^ 2 := by nlinarith
    have h2 : (p + 1) ^ 2 ≤ (p + 1) ^ K := Nat.pow_le_pow_right hbase hK2
    linarith
  have step1 : Ci * (t * (p + 1) ^ Ci) ≤ Ci * (t * (p + 1) ^ K) :=
    Nat.mul_le_mul_left Ci (Nat.mul_le_mul_left t hXCi)
  have step2 : Ce * (p + 1) ^ Ce ≤ Ce * (p + 1) ^ K := Nat.mul_le_mul_left Ce hXCe
  have step3 : Km * (2 * p + 9) ≤ Km * (p + 1) ^ K := Nat.mul_le_mul_left Km h29
  have step23 : Ce * (p + 1) ^ Ce + Km * (2 * p + 9) ≤
      Ce * (p + 1) ^ K + Km * (p + 1) ^ K := Nat.add_le_add step2 step3
  have step4 : t * (Ce * (p + 1) ^ Ce + Km * (2 * p + 9)) ≤
      t * (Ce * (p + 1) ^ K + Km * (p + 1) ^ K) := Nat.mul_le_mul_left t step23
  have e3 : Ci * (t * (p + 1) ^ K) + Ci + (t * (Ce * (p + 1) ^ K + Km * (p + 1) ^ K) + Km) =
      (Ci + Ce + Km) * (t * (p + 1) ^ K) + (Ci + Km) := by ring
  have e4 : (Ci + Ce + Km) * (t * (p + 1) ^ K) + (Ci + Km) ≤ K * (t * (p + 1) ^ K) + K := by
    have f1 : (Ci + Ce + Km) * (t * (p + 1) ^ K) ≤ K * (t * (p + 1) ^ K) :=
      Nat.mul_le_mul_right _ hsum
    linarith
  linarith [step1, step4, e3, e4]

/-- Cost contraction for the chirp table word. -/
theorem chirpTabCost (Ci Ce Km p t : ℕ) (hp : 100 ≤ p) :
    Ci * (t * (p + 1) ^ Ci) + Ci + (t * (Ce * (p + 1) ^ Ce + Km * (2 * p + 9)) + Km) ≤
      (2 * (Ci + Ce + Km) + 100) * (t * (p + 1) ^ (2 * (Ci + Ce + Km) + 100)) +
        (2 * (Ci + Ce + Km) + 100) :=
  chirpTabCostGen Ci Ce Km (2 * (Ci + Ce + Km) + 100) p t hp
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## The chirp table word -/

theorem chirpTabWordBnd : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p t : ℕ) (R : List HvdH.Val),
      100 ≤ p → 2 ≤ t → t < 2 ^ p →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int p :: HvdH.Val.int t :: R)
        (fun vs out => vs = HvdH.Val.int p :: HvdH.Val.int t :: R ∧
          ∃ (c : List (ℤ × ℤ)),
            out = HvdH.cvecVal c :: HvdH.Val.int p :: R ∧
            c.length = t ∧ HvdH.InDiscVec p t c ∧
            ∀ m < t, (2 : ℝ) ^ p * ‖HvdH.fxC p (c.getD m (0, 0)) -
              Work.Transform.zeta t (m * m)‖ < 2)
        (fun _ => K * (t * (p + 1) ^ K) + K) := by
  intro hK hI hL hF
  obtain ⟨idxP, Ci, hidx⟩ := chirpTabIdxWord hK hL
  obtain ⟨elemP, Ce, helem⟩ := chirpTabElemWord hK hI hF
  obtain ⟨mapP, Km, hmap⟩ := hK.mapList
  refine ⟨idxP ;;; mapP elemP, 2 * (Ci + Ce + Km) + 100, ?_⟩
  intro main p t R hp ht htp
  have hxsk : ∀ x ∈ idxRecs t,
      (∃ m : ℕ, m < t ∧ x = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ))) ∧
        vsz x ≤ 2 * p + 8 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hit : i < t := List.mem_range.mp hi
    refine ⟨⟨i, hit, rfl⟩, ?_⟩
    rw [vsz_cons, vsz_int, vsz_int]
    have h1 : isz (i : ℤ) ≤ p + 2 := isz_natCast_le (lt_trans hit htp)
    have h2 : isz (t : ℤ) ≤ p + 2 := isz_natCast_le htp
    omega
  have helemSpec : ∀ x, (∃ m : ℕ, m < t ∧ x = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ))) →
      WordR main elemP (fun vs => vs = x :: Val.int (p : ℤ) :: R)
        (fun _ out => ∃ y, out = y :: Val.int (p : ℤ) :: R ∧ TabRelV p t x y ∧
          vsz y ≤ 2 * p + 8)
        (fun _ => Ce * (p + 1) ^ Ce) := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine Work.Kernel.WordR_conseq (helem main p t m R hp ht htp hm) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hvs hq
      obtain ⟨w, hout, hdisc, hbnd⟩ := hq
      exact ⟨cfxVal w, hout, ⟨w, rfl, m, rfl, hm, hdisc, hbnd⟩, vsz_cfxVal_le hdisc⟩
    · intro vs hvs; exact le_rfl
  have hmapR := hmap main elemP (Val.int (p : ℤ) :: R)
      (fun x => ∃ m : ℕ, m < t ∧ x = Val.cons (Val.int (m : ℤ)) (Val.int (t : ℤ)))
      (TabRelV p t) (Ce * (p + 1) ^ Ce) (2 * p + 8) helemSpec (idxRecs t) hxsk
  have hidxR := hidx main p t R hp ht htp
  have hxslen : (idxRecs t).length = t := by simp [idxRecs]
  have hcomp := seqStep hidxR hmapR
  refine Work.Kernel.WordR_conseq hcomp ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hq
    obtain ⟨ys, hout, hF2⟩ := hq
    obtain ⟨c, hys, hclen, hdisc, hbnd⟩ := chirpTabExtract p t ys hF2
    refine ⟨hvs, c, ?_, hclen, hdisc, hbnd⟩
    rw [hout, hys]
    rfl
  · intro vs hvs
    have h2p : 2 * p + 8 + 1 = 2 * p + 9 := by omega
    rw [hxslen, h2p]
    exact chirpTabCost Ci Ce Km p t hp
