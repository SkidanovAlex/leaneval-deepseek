import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWsort
import Submission.Work.Fx.FxCommon
import Submission.Work.Kernel.Raw
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auMapListTail

/-!
# `Work.Resample.buQWscalDefs`: the list-level objects of the scaling stage of the `B̃` word

The stage `buQWscal` of `Work.Resample.buQW` reads the vector `u` (length `s`, in the disc of
radius `2^{p+1}`) together with the diagonal weights `buWdL p α s t` (entry 9 of the table), the key
list `buKeysS s t` (entry 8) and the parameters `s`, `p`, and produces

`buPermL s t _ hcop.symm (buDscL (buWd p α s t) p s u)`

i.e. the pointwise product with the diagonal weights `D̃'`, the division by `2^p`, and the final
permutation `P̃_sᵀ` (the key list `i ↦ (t·i) mod s` inverted by sorting).

The word is: `zipWith` of `buWdL` with the vector (element word: multiply and divide by `2^p`), then
the label/sort/take/strip sequence already used by `buQWsel`, this time with the keys `egKeyS s t`.

This module fixes the list-level objects those stages mention (records, key list, element maps) and
the size/cost normal form, so that the stage lemmas can state their results without repeating the
unwieldy `zip`/`ofFn` expressions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## the list-level objects -/

/-- The key list of the final `P̃_sᵀ` step as a list of `Val`s: entry `i` is `(t·i) mod s`. -/
def buScKeys (s t : ℕ) : List Val :=
  (List.ofFn (fun i : Fin s => ((egKeyS s t (i : ℕ) : ℕ) : ℤ))).map Val.int

/-- `buKeysS s t` (entry 8 of the static table) is `ofList (buScKeys s t)`. -/
theorem buKeysS_eq (s t : ℕ) : buKeysS s t = ofList (buScKeys s t) := rfl

theorem buScKeys_length (s t : ℕ) : (buScKeys s t).length = s := by
  simp [buScKeys]

/-- The records `cons (int (egKeyS s t i)) (cfxVal dᵢ)` produced by the labelling `zipWith`. -/
def buScRecs (s t : ℕ) (d : List (ℤ × ℤ)) : List Val :=
  List.zipWith Val.cons (buScKeys s t) (d.map cfxVal)

/-- The same records in `ofFn` form. -/
def buScRecs' (s t : ℕ) (d : List (ℤ × ℤ)) : List Val :=
  List.ofFn (fun i : Fin s =>
    Val.cons (Val.int (((egKeyS s t (i : ℕ) : ℕ) : ℤ))) (cfxVal (d.getD (i : ℕ) (0, 0))))

/-- The element map of the final step: drop the key. -/
def buScStrip : Val → Val
  | Val.cons (Val.int _) (Val.cons (Val.int x) (Val.int y)) => Val.cons (Val.int x) (Val.int y)
  | _ => Val.nil

theorem buScStrip_apply (k : ℤ) (z : ℤ × ℤ) :
    buScStrip (Val.cons (Val.int k) (cfxVal z)) = cfxVal z := rfl

/-- The element map of the scaling `zipWith`: multiply by the weight and divide by `D`. -/
def buScProd (D : ℤ) : Val → Val → Val
  | Val.int W, Val.cons (Val.int a) (Val.int b) =>
      Val.cons (Val.int (Int.tdiv (W * a) D)) (Val.int (Int.tdiv (W * b) D))
  | _, _ => Val.nil

theorem buScProd_apply (D W a b : ℤ) :
    buScProd D (Val.int W) (Val.cons (Val.int a) (Val.int b))
      = Val.cons (Val.int (Int.tdiv (W * a) D)) (Val.int (Int.tdiv (W * b) D)) := rfl

/-! ## the uniform size bound of the stage -/

/-- A uniform bound on `isz` for every single value occurring in the scaling stage: an integer value
of the stage has at most `p+4` bits (`isz ≤ p+4` for the input entries, `≤ 2p+2` for the products,
`≤ p+2` after the division), so `isz ≤ buScB p = 3p+12` always. -/
def buScB (p : ℕ) : ℕ := 3 * p + 12

theorem buScB_succ_le (p : ℕ) : buScB p + 1 ≤ 13 * (p + 1) := by
  simp only [buScB]; omega

theorem one_le_buScB (p : ℕ) : 1 ≤ buScB p + 1 := by simp only [buScB]; omega

theorem le_buScB (p : ℕ) : p + 2 ≤ buScB p := by simp only [buScB]; omega

/-- The normalised cost budget of one stage: `400·S·(s+1)·(buScB p + 1)·(p+1)`. -/
def buScQ (S s p : ℕ) : ℕ := 400 * S * ((s + 1) * (buScB p + 1) * (p + 1))

/-! ## a window specification with an existential output -/

/-- `WSw main prog A B c`: for every list `rest`, the word `prog` maps the window `A ++ rest` to some
window `Bv ++ rest` satisfying `B`, at cost `≤ c`. -/
def WSw (main prog : Cmd) (A : List Val) (B : List Val → Prop) (c : ℕ) : Prop :=
  ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest)
    (fun _ out => ∃ Bv : List Val, B Bv ∧ out = Bv ++ rest) (fun _ => c)

theorem WSw.ofPipe (KL : KernelLib) {main p : Cmd} {A B : List Val} {c : ℕ}
    (h : Pipe main p A B c) : WSw main p A (fun Bv => Bv = B) c := by
  intro rest
  refine KL.conseq main p
    (fun vs : List Val => vs = A ++ rest) (fun vs : List Val => vs = A ++ rest)
    (fun _ out => out = B ++ rest) (fun _ out => ∃ Bv : List Val, Bv = B ∧ out = Bv ++ rest)
    (fun _ => c) (fun _ => c) (h rest) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs hout
  exact ⟨B, rfl, hout⟩

theorem WSw.mono (KL : KernelLib) {main p : Cmd} {A : List Val}
    {B C : List Val → Prop} {c : ℕ} (h : WSw main p A B c) (hBC : ∀ Bv, B Bv → C Bv) :
    WSw main p A C c := by
  intro rest
  refine KL.conseq main p
    (fun vs : List Val => vs = A ++ rest) (fun vs : List Val => vs = A ++ rest)
    (fun _ out => ∃ Bv : List Val, B Bv ∧ out = Bv ++ rest)
    (fun _ out => ∃ Bv : List Val, C Bv ∧ out = Bv ++ rest)
    (fun _ => c) (fun _ => c) (h rest) (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs hout
  obtain ⟨Bv, hB, hout⟩ := hout
  exact ⟨Bv, hBC Bv hB, hout⟩

theorem WSw.cost (KL : KernelLib) {main p : Cmd} {A : List Val}
    {B : List Val → Prop} {c c' : ℕ} (h : WSw main p A B c) (hcc : c ≤ c') : WSw main p A B c' := by
  intro rest
  refine KL.conseq main p
    (fun vs : List Val => vs = A ++ rest) (fun vs : List Val => vs = A ++ rest)
    (fun _ out => ∃ Bv : List Val, B Bv ∧ out = Bv ++ rest)
    (fun _ out => ∃ Bv : List Val, B Bv ∧ out = Bv ++ rest)
    (fun _ => c) (fun _ => c') (h rest) (fun vs hvs => hvs)
    (fun vs out hvs hout => hout) (fun vs hvs => hcc)

theorem WSw.comp (KL : KernelLib) {main p q : Cmd} {A : List Val}
    {B C : List Val → Prop} {c d : ℕ} (h1 : WSw main p A B c)
    (h2 : ∀ Bv, B Bv → WSw main q Bv C d) : WSw main (.seq p q) A C (c + d) := by
  intro rest
  have h2' : WordR main q (fun vs => ∃ Bv : List Val, B Bv ∧ vs = Bv ++ rest)
      (fun _ out => ∃ Cv : List Val, C Cv ∧ out = Cv ++ rest) (fun _ => d) := by
    intro mid hmid st Rh hRh
    obtain ⟨Bv, hB, hmid'⟩ := hmid
    subst hmid'
    exact h2 Bv hB rest (Bv ++ rest) rfl st Rh hRh
  have hcost : ∀ vs mid, vs = A ++ rest →
      (∃ Bv : List Val, B Bv ∧ mid = Bv ++ rest) →
      (∃ Bv : List Val, B Bv ∧ mid = Bv ++ rest) ∧ d ≤ d :=
    fun vs mid _ hmid => ⟨hmid, le_rfl⟩
  have hseq := KL.seq main p q
    (fun vs : List Val => vs = A ++ rest)
    (fun _ out => ∃ Bv : List Val, B Bv ∧ out = Bv ++ rest)
    (fun _ => c)
    (fun mid => ∃ Bv : List Val, B Bv ∧ mid = Bv ++ rest)
    (fun _ out => ∃ Cv : List Val, C Cv ∧ out = Cv ++ rest)
    (fun _ => d) (fun _ => d) (h1 rest) h2' hcost
  refine KL.conseq main (.seq p q)
    (fun vs : List Val => vs = A ++ rest) (fun vs : List Val => vs = A ++ rest)
    (fun _ out => ∃ mid, (∃ Bv : List Val, B Bv ∧ mid = Bv ++ rest) ∧
      ∃ Cv : List Val, C Cv ∧ out = Cv ++ rest)
    (fun _ out => ∃ Cv : List Val, C Cv ∧ out = Cv ++ rest)
    (fun _ => c + d) (fun _ => c + d) hseq (fun vs hvs => hvs) ?_ (fun vs hvs => le_rfl)
  intro vs out hvs h
  obtain ⟨mid, ⟨Bv, hB, hm⟩, Cv, hC, ho⟩ := h
  exact ⟨Cv, hC, ho⟩

end Work.Resample
