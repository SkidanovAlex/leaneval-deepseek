import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.chunks.hcoeff_lt
import Submission.Work.Main.glue
import Submission.Work.Main.final.evalChunks_range_hcoeff
import Submission.Work.Main.final.stripP_exists
import Submission.Work.Main.final.stripN_exists

/-!
# `Work.Main.final.finalWord`: the closing word of the main step

Given the `S` chunk-product coefficients of `x * y` on top of the parameter environment `env sp R`,
the word `roll 3 ; roll 1 ; (strip)⁸ ; evalPoly` keeps the coefficient list and the chunk size `b`
on top, deletes the eight remaining parameter values, and evaluates the coefficient list at `2 ^ b`,
which is exactly `x * y`.

The proof assembles `KernelLib.roll` (twice), a generic "strip the value at depth two" phase
iterated eight times, and `IntLib.evalPoly`, with the algebraic input that the extra coefficients
(indices `≥ 2 * N' - 1`) vanish.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Main.final

open HvdH

/-! ## Auxiliary data and cost constants -/

/-- The eight parameter values that lie below the chunk size `b` after the two rolls. -/
def fwJunk (sp : SP) : List Val :=
  [Val.int sp.S, Val.int sp.N', Val.int sp.p, Val.int sp.α,
   intList sp.ts, intList sp.ss, Val.int sp.x, Val.int sp.y]

theorem fwJunk_length (sp : SP) : (fwJunk sp).length = 8 := by simp [fwJunk]

/-- Cost budget of the two `roll` steps: `vsz L + envsz sp + 1`. -/
def fwB (sp : SP) (ys : List ℤ) : ℕ := vsz (ofList (ys.map Val.int)) + envsz sp + 1

/-- Cost budget of the strip phase (spelled exactly as in the strip lemma). -/
def fwM (sp : SP) (ys : List ℤ) : ℕ :=
  vsz (ofList (ys.map Val.int)) + vsz (Val.int sp.b) + ((fwJunk sp).map vsz).sum + 1

/-- Cost budget of the `evalPoly` phase (spelled exactly as `KernelLib.evalPoly` elaborates it). -/
def fwQ (sp : SP) : ℕ :=
  (List.map (fun h : ℤ => isz h)
      (List.flatMap (fun a : ℕ => pure ((a : ℤ)))
        (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S)))).sum
    + (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S)).length * (sp.b + 1)
    + isz sp.b + 1

/-- The two factors of the target cost bound. -/
def fwX (sp : SP) : ℕ := (sp.S + 1) * (sp.b + 1)
def fwY (sp : SP) : ℕ := envsz sp + 1

/-! ## Elementary list and size lemmas -/

/-- Sum of a list of naturals bounded elementwise. -/
theorem list_sum_le_length_mul {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a ≤ B := h a (by simp)
      have ht : t.sum ≤ t.length * B := ih fun x hx => h x (by simp [hx])
      rw [List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      omega

/-- `vsz (ofList xs) = Σ_{x ∈ xs} vsz x + xs.length + 1`. -/
theorem vsz_ofList_eq : ∀ xs : List Val, vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1
  | [] => by simp [ofList, vsz, Val.enc]
  | a :: t => by
      have ih := vsz_ofList_eq t
      rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, vsz_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- The sizes of the elements of `ofList (ys.map Val.int)` are the `isz` of the entries. -/
theorem map_vsz_map_int (ys : List ℤ) : (ys.map Val.int).map vsz = ys.map (fun z => isz z) := by
  induction ys with
  | nil => rfl
  | cons z t ih => simp only [List.map_cons, ih, vsz_int]

/-- `isz` of a natural cast is the bit-size plus two. -/
theorem isz_natCast (n : ℕ) : isz ((n : ℕ) : ℤ) = n.size + 2 := by
  simp [HvdH.isz, Int.natAbs_natCast]

/-- `List.flatMap` by singletons is `List.map`; this is the form the elaborator produces for the
inserted coercion `List ℕ → List ℤ`. -/
theorem flatMap_singleton_map {α β : Type*} (f : α → β) (l : List α) :
    List.flatMap (fun a => [f a]) l = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- The same with `pure` (the form the coercion is actually displayed in). -/
theorem flatMap_pure_map {α β : Type*} (f : α → β) (l : List α) :
    List.flatMap (fun a => pure (f a)) l = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, ih]; rfl

/-! ## Chaining -/

/-- Chain two constant-cost words with exact state equalities. -/
theorem seqState (hKer : KernelLib) {main p q : Cmd} {A B C : List Val} {c₁ c₂ : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => out = C) (fun _ => c₂)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => out = C) (fun _ => c₁ + c₂) := by
  refine hKer.conseq main (.seq p q) (fun vs => vs = A) (fun vs => vs = A)
    (fun vs out => ∃ mid, mid = B ∧ out = C) (fun _ out => out = C) (fun _ => c₁ + c₂)
    (fun _ => c₁ + c₂)
    (hKer.seq main p q (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁)
      (fun vs => vs = B) (fun _ out => out = C) (fun _ => c₂) (fun _ => c₂) h1 h2
      ?_)
    (fun _ h => h) ?_ (fun vs _ => le_rfl)
  · intro vs mid hp hq
    exact ⟨hq, le_rfl⟩
  · intro vs out _ hq
    obtain ⟨mid, -, hout⟩ := hq
    exact hout

/-- `conseq` for words whose precondition fixes the state. -/
theorem conseqState (hKer : KernelLib) {main p : Cmd} {A : List Val}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (h : WordR main p (fun vs => vs = A) Q C) (hQ : ∀ vs out, vs = A → Q vs out → Q' vs out)
    (hC : ∀ vs, vs = A → C vs ≤ C' vs) :
    WordR main p (fun vs => vs = A) Q' C' :=
  hKer.conseq main p (fun vs => vs = A) (fun vs => vs = A) Q Q' C C' h (fun _ h => h) hQ hC

/-- The `List ℕ → List ℤ` coercion inserted by the elaborator (e.g. inside `HvdH.intList`) is
`List.map Nat.cast`. -/
theorem coe_list_int (T : List ℕ) : (↑T : List ℤ) = T.map (fun n : ℕ => (n : ℤ)) := by
  show T >>= (fun a : ℕ => (pure ((a : ℕ) : ℤ) : List ℤ)) = T.map (fun n : ℕ => (n : ℤ))
  rw [bind_pure_comp]
  rfl

/-- The `int`-values of `ys` form the `intList` of the coefficient list. -/
theorem ofList_map_int_eq {sp : SP} {ys : List ℤ} (hlen : ys.length = sp.S)
    (hc : ∀ m < sp.S, ys.getD m 0 = ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ)) :
    HvdH.ofList (ys.map HvdH.Val.int) =
      HvdH.intList ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m)) := by
  have hys : ys = (List.range sp.S).map
      (fun m => ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ)) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      have h2' : i < sp.S := by simpa using h2
      have h := hc i h2'
      rw [List.getD_eq_getElem _ _ h1] at h
      rw [h, List.getElem_map, List.getElem_range]
  have hL : ys.map HvdH.Val.int
      = (List.range sp.S).map
          (fun m => HvdH.Val.int ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ)) := by
    rw [hys, List.map_map]
    rfl
  have hI : HvdH.intList ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m))
      = HvdH.ofList
          ((((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) : List ℕ) : List ℤ).map
            (fun n : ℤ => HvdH.Val.int n)) := rfl
  have hM : HvdH.ofList
          ((((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) : List ℕ) : List ℤ).map
            (fun n : ℤ => HvdH.Val.int n))
      = HvdH.ofList
          ((List.range sp.S).map
            (fun m => HvdH.Val.int ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ))) := by
    rw [coe_list_int, List.map_map, List.map_map]
    rfl
  rw [hL, hI, hM]

/-! ## The word -/

theorem finalWord (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (R : List HvdH.Val) (sp : SP) (ys : List ℤ),
      ys.length = sp.S →
      (∀ m < sp.S, ys.getD m 0 = ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ)) →
      1 ≤ sp.b → sp.N' ≤ 2 ^ sp.b → 2 * sp.N' - 1 ≤ sp.S → sp.x.size ≤ sp.b * sp.N' →
      sp.y.size ≤ sp.b * sp.N' →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList (ys.map HvdH.Val.int) :: env sp R)
        (fun vs out => vs = HvdH.ofList (ys.map HvdH.Val.int) :: env sp R ∧
          out = HvdH.Val.int (sp.x * sp.y) :: R)
        (fun _ => K * (sp.S + 1) * (sp.b + 1) + K * (envsz sp + 1)) := by
  obtain ⟨rollP, Kr, hroll⟩ := hKer.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hKer.drop
  obtain ⟨evalP, Ke, heval⟩ := hInt.evalPoly
  obtain ⟨stripProg, C0, hstripProg⟩ := stripP_exists hKer
  obtain ⟨stripIter, hstripIter⟩ := stripN_exists hKer stripProg C0 hstripProg
  refine ⟨Cmd.seq (Cmd.seq (Cmd.seq (rollP 3) (rollP 1)) (stripIter 8)) evalP,
    1000 * (Kr + Kd + Ke + C0 + 1), ?_⟩
  intro main R sp ys hlen hc hb1 hN' hS hxs hys
  -- ### (a) the coefficient list and the two semantic facts
  have hxlt : sp.x < 2 ^ (sp.b * sp.N') := Nat.size_le.mp hxs
  have hylt : sp.y < 2 ^ (sp.b * sp.N') := Nat.size_le.mp hys
  have hEval : HvdH.evalChunks ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m)) sp.b
      = sp.x * sp.y := evalChunks_range_hcoeff hb1 hxlt hylt hS
  have hList : HvdH.intList ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m))
      = HvdH.ofList (ys.map HvdH.Val.int) :=
    (ofList_map_int_eq (sp := sp) (ys := ys) hlen hc).symm
  -- ### (c) the size arithmetic
  have hV : HvdH.vsz (HvdH.ofList (ys.map HvdH.Val.int)) ≤ 10 * ((sp.S + 1) * (sp.b + 1)) := by
    have h1 : ∀ x ∈ ys.map (fun z => HvdH.isz z), x ≤ 3 * sp.b + 2 := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      obtain ⟨m, hm, hme⟩ := List.mem_iff_getElem.mp hz
      have hmS : m < sp.S := by rw [← hlen]; exact hm
      have hzs : z = ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ) := by
        rw [← hme, ← List.getD_eq_getElem ys 0 hm, hc m hmS]
      rw [hzs]
      have h2 : (hcoeff sp.x sp.y sp.b sp.N' m).size ≤ 3 * sp.b :=
        Nat.size_le.mpr (Work.Main.chunks.hcoeff_lt (x := sp.x) (y := sp.y) (N := sp.N') hN')
      simp only [HvdH.isz, Int.natAbs_natCast]
      omega
    have hsum := list_sum_le_length_mul h1
    simp only [List.length_map, hlen] at hsum
    simp only [vsz_ofList_eq, map_vsz_map_int, List.length_map, hlen]
    have hX : sp.S * (3 * sp.b + 2) ≤ 3 * ((sp.S + 1) * (sp.b + 1)) := by
      calc sp.S * (3 * sp.b + 2) ≤ (sp.S + 1) * (3 * (sp.b + 1)) :=
            Nat.mul_le_mul (Nat.le_succ sp.S) (by omega)
        _ = 3 * ((sp.S + 1) * (sp.b + 1)) := by ring
    have hY : sp.S + 1 ≤ (sp.S + 1) * (sp.b + 1) := by
      calc sp.S + 1 = (sp.S + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (sp.S + 1) * (sp.b + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hA : (List.map (fun h : ℤ => HvdH.isz h)
      (List.flatMap (fun a : ℕ => pure ((a : ℤ)))
        (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S)))).sum
      ≤ 5 * ((sp.S + 1) * (sp.b + 1)) := by
    have hEq : List.flatMap (fun a : ℕ => pure ((a : ℤ)))
          (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S))
        = List.map (fun a : ℕ => ((a : ℤ)))
          (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S)) :=
      flatMap_pure_map _ _
    rw [hEq]
    have h1 : ∀ x ∈ List.map (fun h : ℤ => HvdH.isz h)
        (List.map (fun a : ℕ => (a : ℤ))
          (List.map (fun m => hcoeff sp.x sp.y sp.b sp.N' m) (List.range sp.S))),
        x ≤ 3 * sp.b + 2 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      rw [List.mem_map] at hh
      obtain ⟨a, ha, hha⟩ := hh
      rw [← hha]
      rw [List.mem_map] at ha
      obtain ⟨m, hm, rfl⟩ := ha
      rw [List.mem_range] at hm
      have h2 : (hcoeff sp.x sp.y sp.b sp.N' m).size ≤ 3 * sp.b :=
        Nat.size_le.mpr (Work.Main.chunks.hcoeff_lt (x := sp.x) (y := sp.y) (N := sp.N') hN')
      simp only [HvdH.isz, Int.natAbs_natCast]
      omega
    have h := list_sum_le_length_mul h1
    simp only [List.length_map, List.length_range] at h
    have h5 : sp.S * (3 * sp.b + 2) ≤ 5 * ((sp.S + 1) * (sp.b + 1)) := by
      calc sp.S * (3 * sp.b + 2) ≤ (sp.S + 1) * (5 * (sp.b + 1)) :=
            Nat.mul_le_mul (Nat.le_succ sp.S) (by omega)
        _ = 5 * ((sp.S + 1) * (sp.b + 1)) := by ring
    omega
  have hJ : ((fwJunk sp).map HvdH.vsz).sum ≤ envsz sp := by
    simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
    omega
  have hBi : HvdH.vsz (Val.int sp.b) ≤ envsz sp := by
    simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
    omega
  have hBi' : HvdH.isz sp.b ≤ envsz sp := by
    simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
    omega
  have hSB : sp.S * (sp.b + 1) ≤ (sp.S + 1) * (sp.b + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_succ sp.S)
  -- ### (d) the four phases
  have hr3 : HvdH.WordR main (rollP 3)
      (fun vs => vs = HvdH.ofList (ys.map HvdH.Val.int) :: env sp R)
      (fun _ out => out = Val.int sp.b :: HvdH.ofList (ys.map HvdH.Val.int) :: fwJunk sp ++ R)
      (fun _ => 4 * Kr * fwB sp ys) := by
    refine Work.Main.conseq' hKer (hroll main 3) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp [env]
    · intro vs out hv hq
      rw [hv] at hq
      rw [hq]
      simp [env, fwJunk]
    · intro vs hv
      rw [hv]
      have htake : (((HvdH.ofList (ys.map HvdH.Val.int) :: env sp R).take 4).map HvdH.vsz).sum + 1
          ≤ fwB sp ys := by
        simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
        omega
      calc Kr * (3 + 1) *
            ((((HvdH.ofList (ys.map HvdH.Val.int) :: env sp R).take 4).map HvdH.vsz).sum + 1)
          ≤ Kr * (3 + 1) * fwB sp ys := Nat.mul_le_mul_left _ htake
        _ = 4 * Kr * fwB sp ys := by ring
  have hr1 : HvdH.WordR main (rollP 1)
      (fun vs => vs = Val.int sp.b :: HvdH.ofList (ys.map HvdH.Val.int) :: fwJunk sp ++ R)
      (fun _ out => out = HvdH.ofList (ys.map HvdH.Val.int) :: Val.int sp.b :: fwJunk sp ++ R)
      (fun _ => 2 * Kr * fwB sp ys) := by
    refine Work.Main.conseq' hKer (hroll main 1) ?_ ?_ ?_
    · intro vs hv
      rw [hv]
      simp [fwJunk]
    · intro vs out hv hq
      rw [hv] at hq
      rw [hq]
      simp [fwJunk]
    · intro vs hv
      rw [hv]
      have htake : (((Val.int sp.b :: HvdH.ofList (ys.map HvdH.Val.int) :: fwJunk sp ++ R).take 2).map
            HvdH.vsz).sum + 1 ≤ fwB sp ys := by
        simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
        omega
      calc Kr * (1 + 1) *
            ((((Val.int sp.b :: HvdH.ofList (ys.map HvdH.Val.int) :: fwJunk sp ++ R).take 2).map
              HvdH.vsz).sum + 1)
          ≤ Kr * (1 + 1) * fwB sp ys := Nat.mul_le_mul_left _ htake
        _ = 2 * Kr * fwB sp ys := by ring
  have hstrip : HvdH.WordR main (stripIter 8)
      (fun vs => vs = HvdH.ofList (ys.map HvdH.Val.int) :: Val.int sp.b :: fwJunk sp ++ R)
      (fun _ out => out = HvdH.ofList (ys.map HvdH.Val.int) :: Val.int sp.b :: R)
      (fun _ => 9 * C0 * fwM sp ys) :=
    hstripIter 8 main (HvdH.ofList (ys.map HvdH.Val.int)) (Val.int sp.b) (fwJunk sp) R
      (fwJunk_length sp)
  have hev : HvdH.WordR main evalP
      (fun vs => vs = HvdH.ofList (ys.map HvdH.Val.int) :: Val.int sp.b :: R)
      (fun _ out => out = Val.int (HvdH.evalChunks
        ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m)) sp.b) :: R)
      (fun _ => Ke * fwQ sp) := by
    refine Work.Main.conseq' hKer
      (heval main ((List.range sp.S).map (fun m => hcoeff sp.x sp.y sp.b sp.N' m)) sp.b hb1 ?_)
      ?_ ?_ ?_
    · intro h hh
      simp only [List.mem_map, List.mem_range] at hh
      obtain ⟨m, hm, rfl⟩ := hh
      exact Work.Main.chunks.hcoeff_lt hN'
    · intro vs hv
      refine ⟨R, ?_⟩
      rw [hv, hList]
    · intro vs out hv hq
      obtain ⟨rest', hvs', hout⟩ := hq
      rw [hv, hList] at hvs'
      injection hvs' with _ h2b
      injection h2b with _ h2d
      rw [hout, h2d]
    · intro vs hv
      simp only [fwQ]
      try rfl
  -- ### (e) the composite
  have h12 := seqState hKer hr3 hr1
  have h123 := seqState hKer h12 hstrip
  have h1234 := seqState hKer h123 hev
  refine conseqState hKer h1234 ?_ ?_
  · rintro vs out hv hq
    refine ⟨hv, ?_⟩
    rw [hq, hEval]
    congr 1
  · intro vs hv
    have h1 : fwB sp ys ≤ 10 * (fwX sp + fwY sp) := by
      simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
      omega
    have h3 : fwM sp ys ≤ 10 * (fwX sp + fwY sp) := by
      simp only [env, envsz, fwJunk, fwB, fwM, fwQ, fwX, fwY, List.cons_append, List.nil_append, List.append_nil, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_append, List.length_nil, vsz_int]
      omega
    have h4 : fwQ sp ≤ 6 * (fwX sp + fwY sp) := by
      simp only [fwQ, fwX, fwY, List.length_map, List.length_range]
      omega
    have hp1 : 4 * Kr * fwB sp ys ≤ 40 * Kr * (fwX sp + fwY sp) := by
      calc 4 * Kr * fwB sp ys ≤ 4 * Kr * (10 * (fwX sp + fwY sp)) := Nat.mul_le_mul_left _ h1
        _ = 40 * Kr * (fwX sp + fwY sp) := by ring
    have hp2 : 2 * Kr * fwB sp ys ≤ 20 * Kr * (fwX sp + fwY sp) := by
      calc 2 * Kr * fwB sp ys ≤ 2 * Kr * (10 * (fwX sp + fwY sp)) := Nat.mul_le_mul_left _ h1
        _ = 20 * Kr * (fwX sp + fwY sp) := by ring
    have hp3 : 9 * C0 * fwM sp ys ≤ 90 * C0 * (fwX sp + fwY sp) := by
      calc 9 * C0 * fwM sp ys ≤ 9 * C0 * (10 * (fwX sp + fwY sp)) := Nat.mul_le_mul_left _ h3
        _ = 90 * C0 * (fwX sp + fwY sp) := by ring
    have hp4 : Ke * fwQ sp ≤ 6 * Ke * (fwX sp + fwY sp) := by
      calc Ke * fwQ sp ≤ Ke * (6 * (fwX sp + fwY sp)) := Nat.mul_le_mul_left _ h4
        _ = 6 * Ke * (fwX sp + fwY sp) := by ring
    have hK : 60 * Kr + 90 * C0 + 6 * Ke ≤ 1000 * (Kr + Kd + Ke + C0 + 1) := by omega
    calc ((4 * Kr * fwB sp ys + 2 * Kr * fwB sp ys) + 9 * C0 * fwM sp ys) + Ke * fwQ sp
        ≤ ((40 * Kr * (fwX sp + fwY sp) + 20 * Kr * (fwX sp + fwY sp))
            + 90 * C0 * (fwX sp + fwY sp)) + 6 * Ke * (fwX sp + fwY sp) :=
          add_le_add (add_le_add (add_le_add hp1 hp2) hp3) hp4
      _ = (60 * Kr + 90 * C0 + 6 * Ke) * (fwX sp + fwY sp) := by ring
      _ ≤ 1000 * (Kr + Kd + Ke + C0 + 1) * (fwX sp + fwY sp) := Nat.mul_le_mul_right _ hK
      _ ≤ 1000 * (Kr + Kd + Ke + C0 + 1) * (sp.S + 1) * (sp.b + 1)
            + 1000 * (Kr + Kd + Ke + C0 + 1) * (envsz sp + 1) := by
          rw [Nat.mul_add (1000 * (Kr + Kd + Ke + C0 + 1)) (fwX sp) (fwY sp)]
          refine Nat.add_le_add ?_ ?_
          · rw [fwX]
            exact Nat.le_of_eq
              (Nat.mul_assoc (1000 * (Kr + Kd + Ke + C0 + 1)) (sp.S + 1) (sp.b + 1)).symm
          · rw [fwY]

end Work.Main.final
