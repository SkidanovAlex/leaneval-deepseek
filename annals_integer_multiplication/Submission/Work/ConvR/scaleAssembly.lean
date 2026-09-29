import Mathlib
import Submission.Work.Kernel.Raw
import Submission.Work.ConvR.scaleFacts
import Submission.Work.ConvR.scaleInject

/-!
# ConvR/`scaleArr`: assembly of the pointwise-scaling program

The *assembly* step of `Work.ConvR.scaleArr`: given

* a *flag word* `flagProg` (specification `hflag`: on `int p :: int c :: rarrVal As :: rest` it
  pushes `int 0` if every row of the array is empty and `int 1` if some row is not, restoring
  everything else), and
* a *map* `mapProg` (specification `hmap`: it applies the per-row scaling word to every row),

this file builds the program of `scaleArr` and proves its `WordR` specification, including the cost
bound `K * (M * r + 1) * (p + 1) ^ 2 + K`.

The dispatch on the flag uses `KernelLib.ifZero`, whose cost `K + max c₁ c₂` is instantiated with
the *vacuous* branch at cost `0`: the branch that would traverse the (huge) array is not the one
taken in the degenerate case, so its cost is never charged.  This is what makes the case "every row
is empty" (`M * r = 0`) cost `O(p)` rather than `Ω(M)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ConvR

open HvdH
open Work.Kernel

/-! ## The predicates and the program of the assembly -/

/-- The postcondition of `Work.ConvR.scaleArr` (as a predicate on the output value list). -/
def PostArr (p c M r : ℕ) (As : List (List (ℤ × ℤ))) (a : Fin M → Fin r → ℂ) (rest : List Val)
    (out : List Val) : Prop :=
  ∃ Bs : List (List (ℤ × ℤ)), out = rarrVal Bs :: rest ∧ InDiscArr p M r Bs ∧
    ∀ (i : Fin M) (j : Fin r), (2 : ℝ) ^ p *
        ‖fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * a i j‖ <
      2 * c * ((2 : ℝ) ^ p * ‖fxC p ((As.getD i []).getD j (0, 0)) - a i j‖) + 3

/-- The postcondition of the array map (`Work.ConvR.scaleArrMap`), before the deletion of the
parameters. -/
def PostGen (p c M r : ℕ) (As : List (List (ℤ × ℤ))) (rest : List Val) (out : List Val) : Prop :=
  ∃ Bs : List (List (ℤ × ℤ)), out = rarrVal Bs :: rest ∧ Bs.length = M ∧
    (∀ i : ℕ, i < M → InDiscVec p r (Bs.getD i []) ∧
      ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
        (2 : ℝ) ^ p * ‖fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * x‖ <
          2 * c * ((2 : ℝ) ^ p * ‖fxC p ((As.getD i []).getD j (0, 0)) - x‖) + 3)

/-- The postcondition of the map itself (parameters still on top of the value list). -/
def PostMap (p c M r : ℕ) (As : List (List (ℤ × ℤ))) (rest : List Val) (out : List Val) : Prop :=
  ∃ Bs : List (List (ℤ × ℤ)),
    out = rarrVal Bs :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest ∧ Bs.length = M ∧
    (∀ i : ℕ, i < M → InDiscVec p r (Bs.getD i []) ∧
      ∀ (j : Fin r) (x : ℂ), (c : ℝ) * ‖x‖ ≤ 1 →
        (2 : ℝ) ^ p * ‖fxC p ((Bs.getD i []).getD j (0, 0)) - (c : ℂ) * x‖ <
          2 * c * ((2 : ℝ) ^ p * ‖fxC p ((As.getD i []).getD j (0, 0)) - x‖) + 3)

/-- The multiplication program of the assembly. -/
noncomputable def sProg (hK : HvdH.KernelLib) (flagProg mapProg : Cmd) : Cmd :=
  flagProg ;; (hK.ifZero.choose (hK.drop.choose ;; hK.drop.choose)
    (hK.roll.choose 2 ;; (mapProg ;; (hK.roll.choose 2 ;; (hK.drop.choose ;;
      (hK.roll.choose 1 ;; hK.drop.choose))))))


/-! ## Basic constant-cost `WordR` consequences of `KernelLib.drop` and `KernelLib.roll` -/

/-- A value-dependent `WordR` bound whose precondition fixes the value can be made constant. -/
theorem wordR_const {main p : Cmd} {P₀ P : List Val → Prop} {Q₀ Q : List Val → List Val → Prop}
    {C : List Val → ℕ} {C' : ℕ} (h : WordR main p P₀ Q₀ C)
    (hP : ∀ vs, P vs → P₀ vs) (hQ : ∀ vs out, P vs → Q₀ vs out → Q vs out)
    (hC : ∀ vs, P vs → C vs ≤ C') : WordR main p P Q (fun _ => C') :=
  WordR_conseq (C := C) (C' := fun _ => C') h (fun vs hh => hP vs hh)
    (fun vs out hp hq => hQ vs out hp hq) hC

/-- `drop` on a value stack of known head, at constant cost. -/
theorem dropWordC (hK : HvdH.KernelLib) (main : Cmd) (v : Val) (rest : List Val) :
    WordC main hK.drop.choose (fun vs => vs = v :: rest) (fun _ out => out = rest)
      (hK.drop.choose_spec.choose * (vsz v + 1)) := by
  refine WordC.ofWordR (wordR_const (P := fun vs => vs = v :: rest)
    (Q := fun _ out => out = rest)
    (C := fun vs => hK.drop.choose_spec.choose * (vsz (vs.headD .nil) + 1))
    (hK.drop.choose_spec.choose_spec main) (fun vs hv => ?_) (fun vs out hv hq => ?_)
    (fun vs hv => ?_))
  · rw [hv]; simp
  · obtain ⟨v', rest', hvv, hout⟩ := hq
    rw [hv] at hvv
    simp only [List.cons.injEq] at hvv
    rw [← hvv.2] at hout
    exact hout
  · rw [hv]; simp

/-- `drop` twice: delete the two parameters, at constant cost. -/
theorem cheapWord (hK : HvdH.KernelLib) (main : Cmd) (p c : ℕ) (A : Val) (rest : List Val) :
    WordC main (hK.drop.choose ;; hK.drop.choose)
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: A :: rest)
      (fun _ out => out = A :: rest)
      (hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
        hK.drop.choose_spec.choose * (isz (c : ℤ) + 1)) := by
  have h1 := dropWordC hK main (Val.int (p : ℤ)) (Val.int (c : ℤ) :: A :: rest)
  have h2 := dropWordC hK main (Val.int (c : ℤ)) (A :: rest)
  refine WordC.conseq hK (WordC.seq hK h1 h2 (fun vs mid hv hq => hq))
    (fun vs hv => hv) (fun vs out hv hq => ?_) ?_
  · obtain ⟨mid, hm, hout⟩ := hq
    exact hout
  · rw [vsz_int (p : ℤ), vsz_int (c : ℤ)]

/-- The 2-element `roll`: bring the value at depth 2 to the top, at constant cost. -/
theorem rollTwice (hK : HvdH.KernelLib) (main : Cmd) (a b d : Val) (rest : List Val)
    (A B D : ℕ) (ha : vsz a ≤ A) (hb : vsz b ≤ B) (hd : vsz d ≤ D) :
    WordC main (hK.roll.choose 2)
      (fun vs => vs = a :: b :: d :: rest)
      (fun _ out => out = d :: a :: b :: rest)
      (hK.roll.choose_spec.choose * 3 * (A + B + D + 1)) := by
  refine WordC.ofWordR (wordR_const (P := fun vs => vs = a :: b :: d :: rest)
    (Q := fun _ out => out = d :: a :: b :: rest)
    (C := fun vs => hK.roll.choose_spec.choose * (2 + 1) *
      (((List.take (2 + 1) vs).map vsz).sum + 1))
    (hK.roll.choose_spec.choose_spec main 2) (fun vs hv => ?_) (fun vs out hv hq => ?_)
    (fun vs hv => ?_))
  · rw [hv]; simp
  · rw [hv] at hq
    simpa using hq
  · rw [hv, show (2 : ℕ) + 1 = 3 from rfl,
      show List.take 3 (a :: b :: d :: rest) = [a, b, d] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h : vsz a + (vsz b + (vsz d + 0)) + 1 ≤ A + B + D + 1 := by omega
    exact Nat.mul_le_mul_left _ h

/-- The 1-element `roll`: swap the top two values, at constant cost. -/
theorem rollOnce (hK : HvdH.KernelLib) (main : Cmd) (a b : Val) (rest : List Val)
    (A B : ℕ) (ha : vsz a ≤ A) (hb : vsz b ≤ B) :
    WordC main (hK.roll.choose 1)
      (fun vs => vs = a :: b :: rest)
      (fun _ out => out = b :: a :: rest)
      (hK.roll.choose_spec.choose * 2 * (A + B + 1)) := by
  refine WordC.ofWordR (wordR_const (P := fun vs => vs = a :: b :: rest)
    (Q := fun _ out => out = b :: a :: rest)
    (C := fun vs => hK.roll.choose_spec.choose * (1 + 1) *
      (((List.take (1 + 1) vs).map vsz).sum + 1))
    (hK.roll.choose_spec.choose_spec main 1) (fun vs hv => ?_) (fun vs out hv hq => ?_)
    (fun vs hv => ?_))
  · rw [hv]; simp
  · rw [hv] at hq
    simpa using hq
  · rw [hv, show (1 : ℕ) + 1 = 2 from rfl,
      show List.take 2 (a :: b :: rest) = [a, b] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h : vsz a + (vsz b + 0) + 1 ≤ A + B + 1 := by omega
    exact Nat.mul_le_mul_left _ h

/-- Delete the two parameters sitting *below* the top value `X`, at constant cost. -/
theorem delPcSpec (hK : HvdH.KernelLib) (main : Cmd) (p c : ℕ) (X : Val) (rest : List Val)
    (A : ℕ) (hX : vsz X ≤ A) :
    WordC main
      (hK.roll.choose 2 ;; (hK.drop.choose ;; (hK.roll.choose 1 ;; hK.drop.choose)))
      (fun vs => vs = X :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
      (fun _ out => out = X :: rest)
      (hK.roll.choose_spec.choose * 3 * (A + isz (p : ℤ) + isz (c : ℤ) + 1) +
        (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
          (hK.roll.choose_spec.choose * 2 * (A + isz (p : ℤ) + 1) +
            hK.drop.choose_spec.choose * (isz (p : ℤ) + 1)))) := by
  have h1 := rollTwice hK main X (Val.int (p : ℤ)) (Val.int (c : ℤ)) rest A (isz (p : ℤ))
    (isz (c : ℤ)) hX (le_of_eq (vsz_int (p : ℤ))) (le_of_eq (vsz_int (c : ℤ)))
  have h2 := dropWordC hK main (Val.int (c : ℤ)) (X :: Val.int (p : ℤ) :: rest)
  have h3 := rollOnce hK main X (Val.int (p : ℤ)) rest A (isz (p : ℤ)) hX
    (le_of_eq (vsz_int (p : ℤ)))
  have h4 := dropWordC hK main (Val.int (p : ℤ)) (X :: rest)
  have h34 : WordC main (hK.roll.choose 1 ;; hK.drop.choose)
      (fun vs => vs = X :: Val.int (p : ℤ) :: rest)
      (fun _ out => out = X :: rest)
      (hK.roll.choose_spec.choose * 2 * (A + isz (p : ℤ) + 1) +
        hK.drop.choose_spec.choose * (isz (p : ℤ) + 1)) := by
    refine WordC.conseq hK (WordC.seq hK h3 h4 (fun vs mid hv hq => hq))
      (fun vs hv => hv) (fun vs out hv hq => ?_) ?_
    · obtain ⟨mid, hm, hout⟩ := hq
      exact hout
    · rw [vsz_int (p : ℤ)]
  have h234 : WordC main (hK.drop.choose ;; (hK.roll.choose 1 ;; hK.drop.choose))
      (fun vs => vs = Val.int (c : ℤ) :: X :: Val.int (p : ℤ) :: rest)
      (fun _ out => out = X :: rest)
      (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
        (hK.roll.choose_spec.choose * 2 * (A + isz (p : ℤ) + 1) +
          hK.drop.choose_spec.choose * (isz (p : ℤ) + 1))) := by
    refine WordC.conseq hK (WordC.seq hK h2 h34 (fun vs mid hv hq => hq))
      (fun vs hv => hv) (fun vs out hv hq => ?_) ?_
    · obtain ⟨mid, hm, hout⟩ := hq
      exact hout
    · rw [vsz_int (c : ℤ)]
  refine WordC.conseq hK (WordC.seq hK h1 h234 (fun vs mid hv hq => hq))
    (fun vs hv => hv) (fun vs out hv hq => ?_) ?_
  · obtain ⟨mid, hm, hout⟩ := hq
    exact hout
  · omega



/-! ## The dispatch and the assembly -/


/-- Delete the two parameters below the top value, the latter bounded by `A` (`∃`-form). -/
theorem delPcB (hK : HvdH.KernelLib) (main : Cmd) (p c : ℕ) (rest : List Val) (A : ℕ) :
    WordC main
      (hK.roll.choose 2 ;; (hK.drop.choose ;; (hK.roll.choose 1 ;; hK.drop.choose)))
      (fun vs => ∃ X : Val, vs = X :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest ∧ vsz X ≤ A)
      (fun vs out => ∃ X : Val, vs = X :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest ∧
        vsz X ≤ A ∧ out = X :: rest)
      (hK.roll.choose_spec.choose * 3 * (A + isz (p : ℤ) + isz (c : ℤ) + 1) +
        (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
          (hK.roll.choose_spec.choose * 2 * (A + isz (p : ℤ) + 1) +
            hK.drop.choose_spec.choose * (isz (p : ℤ) + 1)))) := by
  intro vs hpre s R hR
  obtain ⟨X, hXeq, hXsz⟩ := hpre
  subst hXeq
  obtain ⟨out, s', n, hpost, hev, hn, hstk, hoth⟩ :=
    delPcSpec hK main p c X rest A hXsz (X :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
      rfl s R hR
  exact ⟨out, s', n, ⟨X, rfl, hXsz, hpost⟩, hev, hn, hstk, hoth⟩

/-- The `ifZero` dispatch, at constant cost, with the branch costs kept as parameters. -/
theorem dispatchWordC (hK : HvdH.KernelLib) {main : Cmd} {q₁ q₂ : Cmd} {Q₁ Q₂ : List Val → Prop}
    {z : ℤ} {rest' : List Val} {c₁ c₂ : ℕ}
    (h1 : z = 0 → WordC main q₁ (fun vs => vs = rest') (fun _ out => Q₁ out) c₁)
    (h2 : z ≠ 0 → WordC main q₂ (fun vs => vs = rest') (fun _ out => Q₂ out) c₂) :
    WordC main (hK.ifZero.choose q₁ q₂) (fun vs => vs = Val.int z :: rest')
      (fun _ out => (z = 0 → Q₁ out) ∧ (z ≠ 0 → Q₂ out))
      (hK.ifZero.choose_spec.choose * (isz z + 1) + max c₁ c₂) :=
  WordC.ofWordR (hK.ifZero.choose_spec.choose_spec main q₁ q₂ z rest' Q₁ Q₂ c₁ c₂
    (fun h => (h1 h)) (fun h => (h2 h)))

/-- If every row of a disc array is empty then `M = 0` or `r = 0`. -/
theorem eq_zero_or_eq_zero_of_all_rows_nil {p M r : ℕ} {As : List (List (ℤ × ℤ))}
    (h : ∀ u ∈ As, u = []) (hdisc : InDiscArr p M r As) : M = 0 ∨ r = 0 := by
  rcases As with _ | ⟨u, us⟩
  · left; simpa using hdisc.1.symm
  · right
    have hu : u ∈ u :: us := List.mem_cons_self ..
    exact eq_nil_of_inDiscArr_row_nil hdisc hu (h u hu)

/-- `arrSz p M r ≤ 12 (M+1) (r+1) (p+1)`. -/
theorem arrSz_le' (p M r : ℕ) : arrSz p M r ≤ 12 * (M + 1) * (r + 1) * (p + 1) := by
  have h1 : cfxSz p ≤ 10 * (p + 1) := cfxSz_le p
  have h2 : cvecSz p r ≤ (r + 1) * (10 * (p + 1) + 1) := by
    rw [cvecSz]; nlinarith [Nat.zero_le r, h1]
  have h3 : 1 ≤ (r + 1) * (p + 1) := by nlinarith [Nat.zero_le r, Nat.zero_le p]
  have h4 : M ≤ M * ((r + 1) * (p + 1)) := Nat.le_mul_of_pos_right M (by omega)
  have h5 : 1 ≤ 12 * (r + 1) * (p + 1) := by nlinarith [h3]
  have h6 : M * cvecSz p r ≤ M * ((r + 1) * (10 * (p + 1) + 1)) := Nat.mul_le_mul_left M h2
  simp only [arrSz]
  nlinarith [h3, h4, h5, h6, Nat.zero_le M, Nat.zero_le p, Nat.zero_le r]


/-- **Assembly of `Work.ConvR.scaleArr`.**  Given the flag word (`hflag`) and the array map
(`hmap`), the program `flagProg ;; ifZero (drop;drop) (roll2; map; delete)` computes the pointwise
scaling of a disc array, at cost `K * (M * r + 1) * (p + 1) ^ 2 + K`. -/
theorem scaleArrAssembly (hK : HvdH.KernelLib)
    (flagProg mapProg : Cmd) (KF Kmap Krow : ℕ)
    (hflag : ∀ (main : Cmd) (p c M r : ℕ) (As : List (List (ℤ × ℤ))) (rest : List Val),
      InDiscArr p M r As →
      WordR main flagProg
        (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (fun _ out => ∃ fg : Val,
          out = fg :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest ∧
          ((∀ u ∈ As, u = []) → fg = Val.int 0) ∧
          ((∃ u ∈ As, u ≠ []) → fg = Val.int 1))
        (fun vs => KF * (vsz (vs.getD 0 Val.nil) + vsz (vs.getD 1 Val.nil) + 1)))
    (hmap : ∀ (main : Cmd) (p c M r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (As : List (List (ℤ × ℤ))) (rest : List Val), InDiscArr p M r As →
      WordR main mapProg
        (fun vs => vs = rarrVal As :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
        (fun _ out => PostMap p c M r As rest out)
        (fun _ => Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap)) :
    ∃ (K : ℕ), ∀ (main : Cmd) (p c M r : ℕ), 1 ≤ c → c ≤ 2 ^ p →
      ∀ (As : List (List (ℤ × ℤ))) (a : Fin M → Fin r → ℂ) (rest : List Val),
        InDiscArr p M r As → (∀ (i : Fin M) (j : Fin r), (c : ℝ) * ‖a i j‖ ≤ 1) →
        WordR main (sProg hK flagProg mapProg)
          (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
          (fun _ out => PostArr p c M r As a rest out)
          (fun _ => K * (M * r + 1) * (p + 1) ^ 2 + K) := by
  refine ⟨1000000 * (KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
    hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1) ^ 2, ?_⟩
  intro main p c M r hc1 hc2 As a rest hdisc ha
  have hF : WordC main flagProg
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
      (fun _ out => ∃ fg : Val,
        out = fg :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest ∧
        ((∀ u ∈ As, u = []) → fg = Val.int 0) ∧ ((∃ u ∈ As, u ≠ []) → fg = Val.int 1))
      (KF * (isz (p : ℤ) + isz (c : ℤ) + 1)) :=
    WordC.ofWordR (wordR_const (hflag main p c M r As rest hdisc)
      (fun vs hv => hv) (fun vs out hv hq => hq)
      (fun vs hv => by rw [hv]; simp only [List.getD_cons_zero, List.getD_cons_succ, vsz_int]; exact le_rfl))
  -- the general path (used in the generic case; stated for all instances)
  have hGEN : WordC main
      (hK.roll.choose 2 ;; (mapProg ;; (hK.roll.choose 2 ;; (hK.drop.choose ;;
        (hK.roll.choose 1 ;; hK.drop.choose)))))
      (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
      (fun _ out => PostArr p c M r As a rest out)
      (hK.roll.choose_spec.choose * 3 * (isz (p : ℤ) + isz (c : ℤ) + arrSz p M r + 1) +
        ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
          (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
            (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
              (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                hK.drop.choose_spec.choose * (isz (p : ℤ) + 1)))))) := by
    have hROLL := rollTwice hK main (Val.int (p : ℤ)) (Val.int (c : ℤ)) (rarrVal As) rest
      (isz (p : ℤ)) (isz (c : ℤ)) (arrSz p M r) (le_of_eq (vsz_int (p : ℤ)))
      (le_of_eq (vsz_int (c : ℤ))) (vsz_rarrVal_le hdisc)
    have hMAPC : WordC main mapProg
        (fun vs => vs = rarrVal As :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
        (fun _ out => PostMap p c M r As rest out)
        (Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) :=
      WordC.ofWordR (hmap main p c M r hc1 hc2 As rest hdisc)
    have hDEL := delPcB hK main p c rest (arrSz p M r)
    have hMID : WordC main
        (mapProg ;; (hK.roll.choose 2 ;; (hK.drop.choose ;; (hK.roll.choose 1 ;; hK.drop.choose))))
        (fun vs => vs = rarrVal As :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rest)
        (fun _ out => PostGen p c M r As rest out)
        ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
          (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
            (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
              (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                hK.drop.choose_spec.choose * (isz (p : ℤ) + 1))))) := by
      refine WordC.conseq hK (WordC.seq hK hMAPC hDEL (fun vs mid hv hq => ?_))
        (fun vs hv => hv) (fun vs out hv hq => ?_) le_rfl
      · obtain ⟨Bs, hmid, hlen, hrow⟩ := hq
        have hID : InDiscArr p M r Bs := by
          refine ⟨hlen, fun w hw => ?_⟩
          obtain ⟨i, hi, hw⟩ := List.mem_iff_getElem.mp hw
          rw [← hw]
          have hh := (hrow i (by rw [← hlen]; exact hi)).1
          rwa [List.getD_eq_getElem _ _ hi] at hh
        exact ⟨rarrVal Bs, hmid, vsz_rarrVal_le hID⟩
      · obtain ⟨mid, hm, hX⟩ := hq
        obtain ⟨Bs, hmid, hlen, hrow⟩ := hm
        obtain ⟨X, hmidX, hsz, hout⟩ := hX
        have hXeq : X = rarrVal Bs := by rw [hmid] at hmidX; simpa using hmidX.symm
        exact ⟨Bs, by rw [hout, hXeq], hlen, hrow⟩
    refine WordC.conseq hK (WordC.seq hK hROLL hMID (fun vs mid hv hq => hq))
      (fun vs hv => hv) (fun vs out hv hq => ?_) (le_refl _)
    obtain ⟨mid, hm, hg⟩ := hq
    obtain ⟨Bs, hout, hlen, hrow⟩ := hg
    refine ⟨Bs, hout, ?_, ?_⟩
    · refine ⟨hlen, fun w hw => ?_⟩
      obtain ⟨i, hi, hw⟩ := List.mem_iff_getElem.mp hw
      rw [← hw]
      have hh := (hrow i (by rw [← hlen]; exact hi)).1
      rwa [List.getD_eq_getElem _ _ hi] at hh
    · intro i j
      exact (hrow (i : ℕ) i.isLt).2 j (a i j) (ha i j)
  by_cases hA : ∀ u ∈ As, u = []
  · -- the degenerate case: every row is empty, the cheap branch is taken
    have hF0 : WordC main flagProg
        (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (fun _ out => out = Val.int 0 :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (KF * (isz (p : ℤ) + isz (c : ℤ) + 1)) := by
      refine WordC.conseq hK hF (fun vs hv => hv) (fun vs out hv hq => ?_) le_rfl
      obtain ⟨fg, hfg, h0, -⟩ := hq
      rw [h0 hA] at hfg
      exact hfg
    have hCH : WordC main (hK.drop.choose ;; hK.drop.choose)
        (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (fun _ out => PostArr p c M r As a rest out)
        (hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
          hK.drop.choose_spec.choose * (isz (c : ℤ) + 1)) := by
      refine WordC.conseq hK (cheapWord hK main p c (rarrVal As) rest)
        (fun vs hv => hv) (fun vs out hv hq => ?_) le_rfl
      refine ⟨As, hq, hdisc, fun i j => ?_⟩
      rcases eq_zero_or_eq_zero_of_all_rows_nil hA hdisc with hM0 | hr0
      · exact absurd i.isLt (by omega)
      · exact absurd j.isLt (by omega)
    have hDISP := dispatchWordC hK (q₁ := hK.drop.choose ;; hK.drop.choose)
      (q₂ := hK.roll.choose 2 ;; (mapProg ;; (hK.roll.choose 2 ;; (hK.drop.choose ;;
        (hK.roll.choose 1 ;; hK.drop.choose)))))
      (Q₁ := PostArr p c M r As a rest)
      (Q₂ := fun _ => False) (z := 0)
      (rest' := Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
      (c₁ := hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
        hK.drop.choose_spec.choose * (isz (c : ℤ) + 1))
      (c₂ := 0)
      (fun _ => WordC.toWordR hCH) (fun h => absurd rfl h)
    have hMR : M * r = 0 := by
      rcases eq_zero_or_eq_zero_of_all_rows_nil hA hdisc with hM0 | hr0
      · rw [hM0]; ring
      · rw [hr0]; ring
    have hcost : KF * (isz (p : ℤ) + isz (c : ℤ) + 1) +
        (hK.ifZero.choose_spec.choose * (isz ((0 : ℤ)) + 1) + max
          (hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
            hK.drop.choose_spec.choose * (isz (c : ℤ) + 1)) 0) ≤
        1000000 * (KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
          hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1) ^ 2 *
            (M * r + 1) * (p + 1) ^ 2 +
          1000000 * (KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
            hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1) ^ 2 := by
      have h1 : isz (p : ℤ) ≤ p + 2 := isz_int_le p
      have h2 : isz (c : ℤ) ≤ p + 3 := isz_pow_le hc2
      have h3 : isz ((0 : ℤ)) = 2 := by simp [isz]
      have h4 : max (hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
          hK.drop.choose_spec.choose * (isz (c : ℤ) + 1)) 0 =
          hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
            hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) :=
        Nat.max_eq_left (Nat.zero_le _)
      set Sf : ℕ := KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
        hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1 with hSf
      have hS1 : 1 ≤ Sf := by omega
      have hsq : Sf ≤ Sf ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ hS1
      rw [hMR, h3, h4, show (0 : ℕ) + 1 = 1 from rfl, Nat.mul_one]
      have hA0 : KF * (isz (p : ℤ) + isz (c : ℤ) + 1) +
          (hK.ifZero.choose_spec.choose * (2 + 1) +
            (hK.drop.choose_spec.choose * (isz (p : ℤ) + 1) +
              hK.drop.choose_spec.choose * (isz (c : ℤ) + 1)))
          ≤ (6 * KF + 3 * hK.ifZero.choose_spec.choose +
              9 * hK.drop.choose_spec.choose) * (p + 1) := by
        nlinarith [h1, h2]
      have hstep1 : (6 * KF + 3 * hK.ifZero.choose_spec.choose +
            9 * hK.drop.choose_spec.choose) * (p + 1) ≤ 60 * Sf ^ 2 * (p + 1) ^ 2 := by
        have hc : 6 * KF + 3 * hK.ifZero.choose_spec.choose +
            9 * hK.drop.choose_spec.choose ≤ 60 * Sf ^ 2 := by
          have e1 : 6 * KF + 3 * hK.ifZero.choose_spec.choose +
              9 * hK.drop.choose_spec.choose ≤ 18 * Sf := by omega
          have e2 : 18 * Sf ≤ 18 * Sf ^ 2 := Nat.mul_le_mul_left 18 hsq
          have e3 : (18 : ℕ) * Sf ^ 2 ≤ 60 * Sf ^ 2 :=
            Nat.mul_le_mul_right (Sf ^ 2) (by norm_num : 18 ≤ 60)
          exact le_trans e1 (le_trans e2 e3)
        have hPT : p + 1 ≤ (p + 1) ^ 2 := by
          rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
        calc (6 * KF + 3 * hK.ifZero.choose_spec.choose +
              9 * hK.drop.choose_spec.choose) * (p + 1)
            ≤ (60 * Sf ^ 2) * (p + 1) := Nat.mul_le_mul_right _ hc
          _ ≤ (60 * Sf ^ 2) * ((p + 1) ^ 2) := Nat.mul_le_mul_left _ hPT
      nlinarith [hA0, hstep1]
    exact WordC.toWordR (WordC.conseq hK
      (WordC.seq hK hF0 hDISP (fun vs mid hv hq => hq))
      (fun vs hv => hv) (fun vs out hv hq => by obtain ⟨mid, hm, hq⟩ := hq; exact hq.1 rfl) hcost)
  · -- the generic case: the array is traversed
    have hne : ∃ u ∈ As, u ≠ [] := by
      by_contra h
      apply hA
      intro u hu
      by_contra huu
      exact h ⟨u, hu, huu⟩
    have hF1 : WordC main flagProg
        (fun vs => vs = Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (fun _ out => out = Val.int 1 :: Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
        (KF * (isz (p : ℤ) + isz (c : ℤ) + 1)) := by
      refine WordC.conseq hK hF (fun vs hv => hv) (fun vs out hv hq => ?_) le_rfl
      obtain ⟨fg, hfg, -, h1⟩ := hq
      rw [h1 hne] at hfg
      exact hfg
    have hMpos : 0 < M := by
      obtain ⟨u, hu, -⟩ := hne
      by_contra h
      rw [Nat.not_lt] at h
      rw [Nat.le_zero] at h
      have hnil : As = [] := List.eq_nil_of_length_eq_zero (by rw [hdisc.1, h])
      rw [hnil] at hu
      exact absurd hu (by simp)
    have hDISP := dispatchWordC hK
      (q₁ := hK.drop.choose ;; hK.drop.choose)
      (q₂ := hK.roll.choose 2 ;; (mapProg ;; (hK.roll.choose 2 ;; (hK.drop.choose ;;
        (hK.roll.choose 1 ;; hK.drop.choose)))))
      (Q₁ := fun _ => False)
      (Q₂ := PostArr p c M r As a rest)
      (z := 1)
      (rest' := Val.int (p : ℤ) :: Val.int (c : ℤ) :: rarrVal As :: rest)
      (c₁ := 0)
      (c₂ := hK.roll.choose_spec.choose * 3 * (isz (p : ℤ) + isz (c : ℤ) + arrSz p M r + 1) +
        ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
          (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
            (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
              (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                hK.drop.choose_spec.choose * (isz (p : ℤ) + 1))))))
      (fun h => absurd h (by norm_num))
      (fun _ => WordC.toWordR hGEN)
    have hrpos : 0 < r := by
      obtain ⟨u, hu, hune⟩ := hne
      have h1 : u.length = r := (hdisc.2 u hu).1
      have h2 : 0 < u.length := List.length_pos_iff.mpr hune
      omega
    have hMr : 1 ≤ M * r := by nlinarith [hMpos, hrpos]
    have hcost : KF * (isz (p : ℤ) + isz (c : ℤ) + 1) +
        (hK.ifZero.choose_spec.choose * (isz ((1 : ℤ)) + 1) + max 0
          (hK.roll.choose_spec.choose * 3 * (isz (p : ℤ) + isz (c : ℤ) + arrSz p M r + 1) +
            ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
              (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
                (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
                  (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                    hK.drop.choose_spec.choose * (isz (p : ℤ) + 1))))))) ≤
        1000000 * (KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
          hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1) ^ 2 *
            (M * r + 1) * (p + 1) ^ 2 +
          1000000 * (KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
            hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1) ^ 2 := by
      have h1 : isz (p : ℤ) ≤ p + 2 := isz_int_le p
      have h2 : isz (c : ℤ) ≤ p + 3 := isz_pow_le hc2
      have h3 : isz ((1 : ℤ)) = 3 := by simp [isz]
      have h4 : max 0
          (hK.roll.choose_spec.choose * 3 * (isz (p : ℤ) + isz (c : ℤ) + arrSz p M r + 1) +
            ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
              (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
                (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
                  (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                    hK.drop.choose_spec.choose * (isz (p : ℤ) + 1)))))) = _ :=
        Nat.max_eq_right (Nat.zero_le _)
      have hA1 : arrSz p M r ≤ 12 * (M + 1) * (r + 1) * (p + 1) := arrSz_le' p M r
      set Sf : ℕ := KF + Kmap + Krow + hK.ifZero.choose_spec.choose +
        hK.roll.choose_spec.choose + hK.drop.choose_spec.choose + 1 with hSf
      have hS1 : 1 ≤ Sf := by omega
      have hsq : Sf ≤ Sf ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ hS1
      have hKmapS : Kmap ≤ Sf := by omega
      have hKrowS : Krow + 1 ≤ Sf := by omega
      have hM1 : 1 ≤ M := by omega
      have hr1 : 1 ≤ r := by omega
      rw [h3, h4]
      have hL1 : KF * (isz (p : ℤ) + isz (c : ℤ) + 1) +
          (hK.ifZero.choose_spec.choose * (3 + 1) +
            (hK.roll.choose_spec.choose * 3 * (isz (p : ℤ) + isz (c : ℤ) + arrSz p M r + 1) +
              ((Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) +
                (hK.roll.choose_spec.choose * 3 * (arrSz p M r + isz (p : ℤ) + isz (c : ℤ) + 1) +
                  (hK.drop.choose_spec.choose * (isz (c : ℤ) + 1) +
                    (hK.roll.choose_spec.choose * 2 * (arrSz p M r + isz (p : ℤ) + 1) +
                      hK.drop.choose_spec.choose * (isz (p : ℤ) + 1))))))) ≤
          (6 * KF + 4 * hK.ifZero.choose_spec.choose + 42 * hK.roll.choose_spec.choose +
              7 * hK.drop.choose_spec.choose) * (p + 1) + 8 * hK.roll.choose_spec.choose * arrSz p M r +
            (Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap) := by
        nlinarith [h1, h2]
      have hPT : p + 1 ≤ (M * r + 1) * (p + 1) ^ 2 := by
        have hpp : p + 1 ≤ (p + 1) ^ 2 := by
          rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
        exact le_trans hpp (Nat.le_mul_of_pos_left _ (by omega : 0 < M * r + 1))
      have hX1 : 1 ≤ (M * r + 1) * (p + 1) ^ 2 := by
        have h : 0 < (M * r + 1) * (p + 1) ^ 2 := by positivity
        omega
      have hstep1 : (6 * KF + 4 * hK.ifZero.choose_spec.choose +
            42 * hK.roll.choose_spec.choose + 7 * hK.drop.choose_spec.choose) * (p + 1) ≤
          60 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by
        have hc : 6 * KF + 4 * hK.ifZero.choose_spec.choose +
            42 * hK.roll.choose_spec.choose + 7 * hK.drop.choose_spec.choose ≤ 60 * Sf ^ 2 := by
          have e1 : 6 * KF + 4 * hK.ifZero.choose_spec.choose +
              42 * hK.roll.choose_spec.choose + 7 * hK.drop.choose_spec.choose ≤ 59 * Sf := by
            omega
          have e2 : 59 * Sf ≤ 59 * Sf ^ 2 := Nat.mul_le_mul_left 59 hsq
          have e3 : (59 : ℕ) * Sf ^ 2 ≤ 60 * Sf ^ 2 :=
            Nat.mul_le_mul_right (Sf ^ 2) (by norm_num : 59 ≤ 60)
          exact le_trans e1 (le_trans e2 e3)
        calc (6 * KF + 4 * hK.ifZero.choose_spec.choose +
              42 * hK.roll.choose_spec.choose + 7 * hK.drop.choose_spec.choose) * (p + 1)
            ≤ (60 * Sf ^ 2) * (p + 1) := Nat.mul_le_mul_right _ hc
          _ ≤ (60 * Sf ^ 2) * ((M * r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_left _ hPT
      have hsum_mul : (M + 1) * (r + 1) ≤ 3 * (M * r + 1) := by
        have hA' : M ≤ M * r := Nat.le_mul_of_pos_right M (by omega)
        have hB' : r ≤ M * r := Nat.le_mul_of_pos_left r (by omega)
        nlinarith
      have harr : arrSz p M r ≤ 36 * ((M * r + 1) * (p + 1) ^ 2) := by
        have harr3 : 12 * (M + 1) * (r + 1) * (p + 1) ≤ 36 * ((M * r + 1) * (p + 1) ^ 2) := by
          have h4' : 12 * ((M + 1) * (r + 1)) * (p + 1) ≤ 12 * (3 * (M * r + 1)) * (p + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hsum_mul)
          have h5' : (12 : ℕ) * (3 * (M * r + 1)) * (p + 1) ≤
              36 * ((M * r + 1) * (p + 1) ^ 2) := by
            have hpp : p + 1 ≤ (p + 1) ^ 2 := by
              rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
            have h6' : (M * r + 1) * (p + 1) ≤ (M * r + 1) * (p + 1) ^ 2 :=
              Nat.mul_le_mul_left _ hpp
            nlinarith
          calc 12 * (M + 1) * (r + 1) * (p + 1) = 12 * ((M + 1) * (r + 1)) * (p + 1) := by ring
            _ ≤ 12 * (3 * (M * r + 1)) * (p + 1) := h4'
            _ ≤ 36 * ((M * r + 1) * (p + 1) ^ 2) := h5'
        exact le_trans hA1 harr3
      have hstep2 : 8 * hK.roll.choose_spec.choose * arrSz p M r ≤
          30000 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by
        have h8 : 8 * hK.roll.choose_spec.choose ≤ 600 * Sf ^ 2 := by
          have e1 : 8 * hK.roll.choose_spec.choose ≤ 8 * Sf := by omega
          have e2 : 8 * Sf ≤ 8 * Sf ^ 2 := Nat.mul_le_mul_left 8 hsq
          have e3 : (8 : ℕ) * Sf ^ 2 ≤ 600 * Sf ^ 2 :=
            Nat.mul_le_mul_right (Sf ^ 2) (by norm_num : 8 ≤ 600)
          exact le_trans e1 (le_trans e2 e3)
        calc 8 * hK.roll.choose_spec.choose * arrSz p M r
            ≤ (600 * Sf ^ 2) * (36 * ((M * r + 1) * (p + 1) ^ 2)) := Nat.mul_le_mul h8 harr
          _ ≤ 30000 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by nlinarith
      have hin : M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1 ≤
          5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2) := by
        have hr2 : r + 1 ≤ 2 * r := by omega
        have hzp : 1 ≤ r * (p + 1) ^ 2 := by
          have h : 0 < r * (p + 1) ^ 2 := by positivity
          omega
        have e1a : Krow * (r + 1) * (p + 1) ^ 2 ≤ Krow * (2 * r) * (p + 1) ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left Krow hr2)
        have e1 : Krow * (r + 1) * (p + 1) ^ 2 ≤ 2 * (Krow * r * (p + 1) ^ 2) := by
          rw [show Krow * (2 * r) * (p + 1) ^ 2 = 2 * (Krow * r * (p + 1) ^ 2) by ring] at e1a
          exact e1a
        have e2 : Krow ≤ Krow * r * (p + 1) ^ 2 := by
          have h := Nat.mul_le_mul_left Krow hzp
          simpa [Nat.mul_assoc, Nat.mul_one] using h
        have hs' : Krow * (r + 1) * (p + 1) ^ 2 + Krow ≤ 3 * (Krow * r * (p + 1) ^ 2) := by
          omega
        have hmul : M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) ≤
            M * (3 * (Krow * r * (p + 1) ^ 2)) := Nat.mul_le_mul_left M hs'
        have hmain : M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) ≤
            3 * Krow * ((M * r + 1) * (p + 1) ^ 2) := by
          have h2' : M * (3 * (Krow * r * (p + 1) ^ 2)) = 3 * Krow * (M * r) * (p + 1) ^ 2 := by
            ring
          have h3'' : 3 * Krow * (M * r) * (p + 1) ^ 2 ≤
              3 * Krow * ((M * r + 1) * (p + 1) ^ 2) := by
            simpa [Nat.mul_assoc] using
              Nat.mul_le_mul_right ((p + 1) ^ 2)
                (Nat.mul_le_mul_left (3 * Krow) (Nat.le_succ (M * r)))
          exact le_trans hmul (by rw [h2']; exact h3'')
        have hfin : 3 * Krow * ((M * r + 1) * (p + 1) ^ 2) + 1 ≤
            5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2) := by nlinarith [hX1]
        calc M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1
            ≤ 3 * Krow * ((M * r + 1) * (p + 1) ^ 2) + 1 := by have := hmain; omega
          _ ≤ 5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2) := hfin
      have hstep3 : Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap ≤
          200 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by
        have h2' : Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) ≤
            Kmap * (5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2)) :=
          Nat.mul_le_mul_left Kmap hin
        have hk : Kmap * (Krow + 1) ≤ Sf ^ 2 := by
          have := Nat.mul_le_mul hKmapS hKrowS
          simpa [pow_two] using this
        have h3'' : Kmap * (5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2)) ≤
            100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by
          rw [show Kmap * (5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2)) =
              5 * (Kmap * (Krow + 1)) * ((M * r + 1) * (p + 1) ^ 2) by ring]
          calc 5 * (Kmap * (Krow + 1)) * ((M * r + 1) * (p + 1) ^ 2) ≤
                5 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 hk)
            _ ≤ 100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right (Sf ^ 2) (by norm_num : 5 ≤ 100))
        have h4'' : Kmap ≤ 100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by
          have h2'' : Sf ≤ 100 * Sf ^ 2 := by
            calc (Sf : ℕ) ≤ Sf ^ 2 := hsq
              _ ≤ 100 * Sf ^ 2 := by
                  have h := Nat.mul_le_mul_right (Sf ^ 2) (by norm_num : 1 ≤ 100)
                  simpa using h
          calc Kmap ≤ Sf := hKmapS
            _ ≤ Sf * ((M * r + 1) * (p + 1) ^ 2) :=
                  Nat.le_mul_of_pos_right Sf (show 0 < (M * r + 1) * (p + 1) ^ 2 by omega)
            _ ≤ 100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := Nat.mul_le_mul_right _ h2''
        calc Kmap * (M * (Krow * (r + 1) * (p + 1) ^ 2 + Krow) + 1) + Kmap
            ≤ Kmap * (5 * (Krow + 1) * ((M * r + 1) * (p + 1) ^ 2)) + Kmap := by
                have := h2'; omega
          _ ≤ 100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) +
                100 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := add_le_add h3'' h4''
          _ = 200 * Sf ^ 2 * ((M * r + 1) * (p + 1) ^ 2) := by ring
      nlinarith [hL1, hstep1, hstep2, hstep3]
    exact WordC.toWordR (WordC.conseq hK
      (WordC.seq hK hF1 hDISP (fun vs mid hv hq => hq))
      (fun vs hv => hv) (fun vs out hv hq => by obtain ⟨mid, hm, hq⟩ := hq; exact hq.2 (by norm_num)) hcost)

end Work.ConvR
