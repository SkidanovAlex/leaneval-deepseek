import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.word.recoverVec2
import Submission.Work.Main.word.toCfx

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Main.fstep

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## Generic `WordR` plumbing -/

theorem wrMono {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hp s R hs
  obtain ⟨o, s', n, hQ', he, hn, hl, hk⟩ := h vs (hP vs hp) s R hs
  exact ⟨o, s', n, hQ vs o hp hQ', he, le_trans hn (hC vs hp), hl, hk⟩

theorem wrSeq1 {main q₁ q₂ : Cmd} {A B : List Val} {Q : List Val → Prop} {a b : ℕ}
    (h₁ : WordR main q₁ (fun vs => vs = A) (fun _ out => out = B) (fun _ => a))
    (h₂ : WordR main q₂ (fun vs => vs = B) (fun _ out => Q out) (fun _ => b)) :
    WordR main (q₁ ;;; q₂) (fun vs => vs = A) (fun _ out => Q out) (fun _ => a + b) := by
  intro vs hvs s R hs
  rw [hvs] at hs
  obtain ⟨o₁, s₁, n₁, ho₁, he₁, hn₁, hl₁, hk₁⟩ := h₁ A rfl s R hs
  rw [ho₁] at hl₁
  obtain ⟨o₂, s₂, n₂, ho₂, he₂, hn₂, hl₂, hk₂⟩ := h₂ B rfl s₁ R hl₁
  exact ⟨o₂, s₂, n₁ + n₂, ho₂, Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hl₂,
    fun k hk => by rw [hk₂ k hk, hk₁ k hk]⟩

theorem wrSeqX {main q₁ q₂ : Cmd} {A : List Val} {X : Type} {Body : X → List Val}
    {Facts : X → Prop} {Q : X → List Val → Prop} {a b : ℕ}
    (h₁ : WordR main q₁ (fun vs => vs = A) (fun _ out => ∃ x, out = Body x ∧ Facts x) (fun _ => a))
    (h₂ : ∀ x, Facts x → WordR main q₂ (fun vs => vs = Body x) (fun _ out => Q x out) (fun _ => b)) :
    WordR main (q₁ ;;; q₂) (fun vs => vs = A) (fun _ out => ∃ x, Facts x ∧ Q x out) (fun _ => a + b) := by
  intro vs hvs s R hs
  rw [hvs] at hs
  obtain ⟨o₁, s₁, n₁, ⟨x, ho₁, hfx⟩, he₁, hn₁, hl₁, hk₁⟩ := h₁ A rfl s R hs
  rw [ho₁] at hl₁
  obtain ⟨o₂, s₂, n₂, ho₂, he₂, hn₂, hl₂, hk₂⟩ := h₂ x hfx (Body x) rfl s₁ R hl₁
  exact ⟨o₂, s₂, n₁ + n₂, ⟨x, hfx, ho₂⟩, Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hl₂,
    fun k hk => by rw [hk₂ k hk, hk₁ k hk]⟩

/-! ## `take`-sum bounds and cost helpers -/

theorem take_map_sum_le (l : List Val) (n : ℕ) : ((l.take n).map vsz).sum ≤ (l.map vsz).sum := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [List.take_succ_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih n) _

theorem take_sum_le_prefix {A P R : List Val} (hA : A = P ++ R) {n B : ℕ} (hn : n ≤ P.length)
    (hP : (P.map vsz).sum ≤ B) : ((A.take n).map vsz).sum ≤ B := by
  rw [hA, List.take_append_of_le_length hn]
  exact le_trans (take_map_sum_le _ _) hP

theorem pickCost_le {K k B Phi : ℕ} (hk : k + 1 ≤ 10) (hB : B ≤ Phi) (hPhi : 1 ≤ Phi) :
    K * (k + 1) * (B + 1) ≤ 20 * K * Phi := by
  have h2 : B + 1 ≤ 2 * Phi := by omega
  calc K * (k + 1) * (B + 1) = (K * (k + 1)) * (B + 1) := rfl
    _ ≤ (K * 10) * (2 * Phi) := Nat.mul_le_mul (Nat.mul_le_mul_left K hk) h2
    _ = 20 * K * Phi := by ring

theorem dropCost_le {K Phi : ℕ} {v : Val} (h : vsz v ≤ Phi) (hPhi : 1 ≤ Phi) :
    K * (vsz v + 1) ≤ 2 * K * Phi := by
  have h2 : vsz v + 1 ≤ 2 * Phi := by omega
  calc K * (vsz v + 1) ≤ K * (2 * Phi) := Nat.mul_le_mul_left K h2
    _ = 2 * K * Phi := by ring

theorem pushCost_le {K Phi : ℕ} (hPhi : 1 ≤ Phi) :
    K * (vsz (Val.int (1 : ℤ)) + 1) ≤ 4 * K * Phi := by
  have h1 : vsz (Val.int (1 : ℤ)) ≤ 3 := by
    rw [Work.Main.vsz_int]
    exact Work.Main.word.isz_le_of_le_two_pow (p := 0) (by norm_num)
  have h2 : vsz (Val.int (1 : ℤ)) + 1 ≤ 4 * Phi := by omega
  calc K * (vsz (Val.int (1 : ℤ)) + 1) ≤ K * (4 * Phi) := Nat.mul_le_mul_left K h2
    _ = 4 * K * Phi := by ring

theorem one_le_mul' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have hm := Nat.mul_le_mul ha hb
  simpa using hm

/-! ## Injectivity of the value encoder -/

theorem ofList_cons_eq (a : Val) (t : List Val) : ofList (a :: t) = Val.cons a (ofList t) := by
  simp only [ofList, List.foldr_cons]

theorem ofList_inj {a b : List Val} (h : ofList a = ofList b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd h (by simp [ofList])
  | cons x xs ih =>
    cases b with
    | nil => exact absurd h.symm (by simp [ofList])
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := Val.cons.inj h
      rw [h'.1, ih h'.2]

theorem map_inj_of_inj {α β : Type*} {f : α → β} (hf : ∀ x y, f x = f y → x = y) :
    ∀ {a b : List α}, a.map f = b.map f → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf x y h.1, ih h.2]

theorem cvecVal_inj {a b : List (ℤ × ℤ)} (h : cvecVal a = cvecVal b) : a = b :=
  map_inj_of_inj (fun x y hxy => Work.Main.word.cfxVal_inj' hxy) (ofList_inj h)

/-! ## Sizes of the value lists appearing in the main step -/

theorem vsz_ofList_le {xs : List Val} {B : ℕ} (h : ∀ x ∈ xs, vsz x ≤ B) :
    vsz (ofList xs) ≤ (xs.length + 1) * (B + 1) := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons a t ih =>
      have ha : vsz a ≤ B := h a List.mem_cons_self
      have ht : ∀ x ∈ t, vsz x ≤ B := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hih := ih ht
      rw [ofList_cons_eq, Work.Main.vsz_cons, List.length_cons]
      have h2 : (t.length + 1 + 1) * (B + 1) = (t.length + 1) * (B + 1) + (B + 1) := by ring
      omega

theorem vsz_cvecVal_le {p n : ℕ} {zs : List (ℤ × ℤ)} (hlen : zs.length = n)
    (h : ∀ z ∈ zs, inDisc p z) : vsz (cvecVal zs) ≤ (n + 1) * (2 * p + 8) := by
  have h1 : vsz (ofList (zs.map cfxVal)) ≤ ((zs.map cfxVal).length + 1) * ((2 * p + 7) + 1) := by
    refine vsz_ofList_le (xs := zs.map cfxVal) (B := 2 * p + 7) ?_
    rw [List.forall_mem_map]
    intro z hz
    rw [Work.Main.vsz_cfxVal]
    have h2 := Work.Main.word.isz_fst_le (h z hz)
    have h3 := Work.Main.word.isz_snd_le (h z hz)
    omega
  rw [List.length_map, hlen] at h1
  exact h1

theorem vsz_intList_aux {p : ℕ} {xs : List ℕ} (h : ∀ x ∈ xs, x < 2 ^ p) :
    vsz (intList xs) ≤ (xs.length + 1) * (p + 3) := by
  induction xs with
  | nil =>
      have h1 : vsz (intList ([] : List ℕ)) = 1 := by
        simp [intList, ofList, vsz, Val.enc]
      have h2 : (([] : List ℕ).length + 1) * (p + 3) = p + 3 := by
        simp only [List.length_nil]
        ring
      rw [h1, h2]
      omega
  | cons a t ih =>
      have ha : a.size + 2 ≤ p + 2 := by
        have h3 : a.size ≤ p := Nat.size_le.mpr (h a (by simp))
        omega
      have ht0 : ∀ x ∈ t, x < 2 ^ p := fun x hx => h x (by simp [hx])
      have hih := ih ht0
      have hcons : vsz (intList (a :: t)) = (a.size + 2) + vsz (intList t) + 1 := by
        have e1 : intList (a :: t) = Val.cons (Val.int (a : ℤ)) (intList t) := rfl
        rw [e1, Work.Main.vsz_cons, Work.Main.vsz_int, isz, Int.natAbs_natCast]
      rw [hcons, List.length_cons]
      have h2 : (t.length + 1 + 1) * (p + 3) = (t.length + 1) * (p + 3) + (p + 3) := by ring
      omega

theorem vsz_intList_le {p D : ℕ} {xs : List ℕ} (hlen : xs.length = D) (h : ∀ x ∈ xs, x < 2 ^ p) :
    vsz (intList xs) ≤ (D + 1) * (p + 3) := by
  have h1 := vsz_intList_aux (p := p) h
  rw [hlen] at h1
  exact h1

theorem vsz_ofList_map_int_le {S p : ℕ} {hs : List ℤ} (hlen : hs.length = S)
    (h : ∀ i < S, isz (hs.getD i 0) ≤ 2 * p + 5) :
    vsz (ofList (hs.map Val.int)) ≤ (S + 1) * (2 * p + 8) := by
  have h1 : vsz (ofList (hs.map Val.int)) ≤ ((hs.map Val.int).length + 1) * ((2 * p + 5) + 1) := by
    refine vsz_ofList_le (xs := hs.map Val.int) (B := 2 * p + 5) ?_
    rw [List.forall_mem_map]
    intro z hz
    rw [Work.Main.vsz_int]
    obtain ⟨i, hi, hni⟩ := List.mem_iff_getElem.mp hz
    have hi' : i < S := by rwa [hlen] at hi
    have h2 := h i hi'
    rw [List.getD_eq_getElem _ (0 : ℤ) hi, hni] at h2
    exact h2
  rw [List.length_map, hlen] at h1
  calc vsz (ofList (hs.map Val.int)) ≤ (S + 1) * (2 * p + 6) := h1
    _ ≤ (S + 1) * (2 * p + 8) := Nat.mul_le_mul_left _ (by omega)

/-! ## The CRT index and the final reindexing identification -/

theorem crtIdx_cons (t : ℕ) (ts : List ℕ) (m : ℕ) :
    HvdH.crtIdx (t :: ts) m = (m % t) * ts.prod + HvdH.crtIdx ts m := rfl

theorem crtIdx_lt {ss : List ℕ} (h : ∀ s ∈ ss, 1 ≤ s) (m : ℕ) : HvdH.crtIdx ss m < ss.prod := by
  induction ss generalizing m with
  | nil => simp [HvdH.crtIdx]
  | cons t ts ih =>
      rw [crtIdx_cons, List.prod_cons]
      have ht : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (h t List.mem_cons_self)
      have hts : ∀ s ∈ ts, 1 ≤ s := fun s hs => h s (List.mem_cons_of_mem _ hs)
      have ih' := ih hts m
      have hmod : m % t < t := Nat.mod_lt _ ht
      have h1 : m % t * ts.prod + HvdH.crtIdx ts m < m % t * ts.prod + ts.prod :=
        Nat.add_lt_add_left ih' _
      have h2 : m % t * ts.prod + ts.prod = (m % t + 1) * ts.prod := by ring
      have h3 : (m % t + 1) * ts.prod ≤ t * ts.prod :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hmod)
      omega

theorem getD_map_int {hs : List ℤ} {j : ℕ} (hj : j < hs.length) :
    (hs.map Val.int).getD j Val.nil = Val.int (hs.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    ← List.getD_eq_getElem (l := hs) (d := (0 : ℤ)) hj]

theorem crtIdent {ss : List ℕ} {ys : List Val} {hs : List ℤ} {zs : List (ℤ × ℤ)} {S p b : ℕ}
    (hhsl : hs.length = zs.length)
    (hidx : ∀ m < ss.prod, HvdH.crtIdx ss m < hs.length)
    (hlen : ys.length = ss.prod)
    (hcrt : ∀ m < ss.prod,
      ys.getD m Val.nil = (hs.map Val.int).getD (HvdH.crtIdx ss m) Val.nil)
    (hrec : ∀ i < zs.length, hs.getD i 0 = Work.Main.recov S p b (zs.getD i (0, 0))) :
    ∃ ys' : List ℤ, ys = ys'.map Val.int ∧ ys'.length = ss.prod ∧
      ∀ m < ss.prod, ys'.getD m 0 = Work.Main.recov S p b (zs.getD (HvdH.crtIdx ss m) (0, 0)) := by
  refine ⟨(List.range ss.prod).map (fun m => hs.getD (HvdH.crtIdx ss m) 0), ?_, ?_, ?_⟩
  · apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      have hi : i < ss.prod := by rwa [hlen] at h1
      have hci := hcrt i hi
      have hyi : ys[i] = Val.int (hs.getD (HvdH.crtIdx ss i) 0) := by
        rw [← List.getD_eq_getElem _ Val.nil h1]
        rw [hci, getD_map_int (hidx i hi)]
      rw [hyi]
      rw [List.getElem_map]
      congr 1
      rw [List.getElem_map, List.getElem_range]
  · simp
  · intro m hm
    rw [List.getD_eq_getElem _ 0 (by simpa using hm), List.getElem_map, List.getElem_range]
    exact hrec (HvdH.crtIdx ss m) (by rw [← hhsl]; exact hidx m hm)

/-! ## The cost arithmetic -/

def phiOf (S p D : ℕ) : ℕ :=
  3 * ((S + 1) * (2 * p + 8)) + 6 * ((D + 1) * (p + 3)) + 5 * (p + 3) + 1

theorem costArith {S D p Kp Kr Kd Kv Kcrt Krev F K53 : ℕ}
    (hS : 1 ≤ S) (hD : 1 ≤ D) (hp : 2 ≤ p) (hSZ : S ≤ 2 ^ p) :
    ((20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D
          + 20 * Kp * phiOf S p D) + (F + K53))
      + (20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D
          + 20 * Kr * phiOf S p D
          + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
          + (20 * Kr * phiOf S p D + 2 * Kd * phiOf S p D + 20 * Kr * phiOf S p D
              + 2 * Kd * phiOf S p D + 20 * Kr * phiOf S p D + 2 * Kd * phiOf S p D
              + 20 * Kp * phiOf S p D + 4 * Kv * phiOf S p D
              + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)))
    ≤ (F + K53) + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (p + 1) * (p + 1)
      + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (D + 1) * (p + 1) * (p + 1) := by
  set B : ℕ := (S + 1) * (D + 1) * (p + 1) * (p + 1) with hB
  have hsz : S.size + 1 ≤ p + 2 := by
    have h1 : S.size ≤ p + 1 :=
      Nat.size_le.mpr (lt_of_le_of_lt hSZ (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p)))
    omega
  have hS1 : 1 ≤ S + 1 := by omega
  have hD1 : 1 ≤ D + 1 := by omega
  have hp1 : 1 ≤ p + 1 := by omega
  have hB1 : 1 ≤ B := by
    rw [hB]
    exact one_le_mul' (one_le_mul' (one_le_mul' hS1 hD1) hp1) hp1
  have hA : (S + 1) * (2 * p + 8) ≤ 4 * B := by
    rw [hB]
    have h2p : 2 * p + 8 ≤ 4 * (p + 1) := by omega
    have hQ : 1 ≤ (D + 1) * (p + 1) := one_le_mul' hD1 hp1
    calc (S + 1) * (2 * p + 8) ≤ (S + 1) * (4 * (p + 1)) := Nat.mul_le_mul_left _ h2p
      _ = 4 * ((S + 1) * (p + 1)) := by ring
      _ ≤ 4 * ((S + 1) * (p + 1) * ((D + 1) * (p + 1))) := by
          apply Nat.mul_le_mul_left
          calc (S + 1) * (p + 1) = (S + 1) * (p + 1) * 1 := by ring
            _ ≤ (S + 1) * (p + 1) * ((D + 1) * (p + 1)) := Nat.mul_le_mul_left _ hQ
      _ = 4 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) := by ring
  have hA4 : (D + 1) * (p + 3) ≤ 4 * B := by
    rw [hB]
    have hp3 : p + 3 ≤ 4 * (p + 1) := by omega
    have hQ : 1 ≤ (S + 1) * (p + 1) := one_le_mul' hS1 hp1
    calc (D + 1) * (p + 3) ≤ (D + 1) * (4 * (p + 1)) := Nat.mul_le_mul_left _ hp3
      _ = 4 * ((D + 1) * (p + 1)) := by ring
      _ ≤ 4 * ((S + 1) * (p + 1) * ((D + 1) * (p + 1))) := by
          apply Nat.mul_le_mul_left
          calc (D + 1) * (p + 1) = 1 * ((D + 1) * (p + 1)) := by ring
            _ ≤ ((S + 1) * (p + 1)) * ((D + 1) * (p + 1)) := Nat.mul_le_mul_right _ hQ
      _ = 4 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) := by ring
  have hC5 : 5 * (p + 3) + 1 ≤ 6 * B := by
    rw [hB]
    have h1 : 5 * (p + 3) + 1 ≤ 6 * ((p + 1) * (p + 1)) := by nlinarith
    have hQ : 1 ≤ (S + 1) * (D + 1) := one_le_mul' hS1 hD1
    calc 5 * (p + 3) + 1 ≤ 6 * ((p + 1) * (p + 1)) := h1
      _ ≤ 6 * ((S + 1) * (D + 1) * ((p + 1) * (p + 1))) := by
          apply Nat.mul_le_mul_left
          calc (p + 1) * (p + 1) = 1 * ((p + 1) * (p + 1)) := by ring
            _ ≤ ((S + 1) * (D + 1)) * ((p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hQ
      _ = 6 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) := by ring
  have hPhi : phiOf S p D ≤ 42 * B := by
    have h3 : 3 * ((S + 1) * (2 * p + 8)) ≤ 12 * B := by
      calc 3 * ((S + 1) * (2 * p + 8)) ≤ 3 * (4 * B) := Nat.mul_le_mul_left 3 hA
        _ = 12 * B := by ring
    have h6 : 6 * ((D + 1) * (p + 3)) ≤ 24 * B := by
      calc 6 * ((D + 1) * (p + 3)) ≤ 6 * (4 * B) := Nat.mul_le_mul_left 6 hA4
        _ = 24 * B := by ring
    have h5 : 5 * (p + 3) + 1 ≤ 6 * B := hC5
    simp only [phiOf]
    omega
  have hX1 : (S + 1) * (2 * p + 8) * (S.size + 1) ≤ 8 * B := by
    have h2 : (S + 1) * (2 * p + 8) ≤ 4 * ((S + 1) * (p + 1)) := by
      calc (S + 1) * (2 * p + 8) ≤ (S + 1) * (4 * (p + 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = 4 * ((S + 1) * (p + 1)) := by ring
    have hs2 : S.size + 1 ≤ 2 * (p + 1) := by omega
    calc (S + 1) * (2 * p + 8) * (S.size + 1)
        ≤ (4 * ((S + 1) * (p + 1))) * (2 * (p + 1)) := Nat.mul_le_mul h2 hs2
      _ = 8 * ((S + 1) * (p + 1) * (p + 1)) := by ring
      _ ≤ 8 * B := by
          apply Nat.mul_le_mul_left
          rw [hB]
          calc (S + 1) * (p + 1) * (p + 1) = 1 * ((S + 1) * (p + 1) * (p + 1)) := by ring
            _ ≤ (D + 1) * ((S + 1) * (p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hD1
            _ = (S + 1) * (D + 1) * (p + 1) * (p + 1) := by ring
  have hX2 : S * ((D + 1) * (p + 3) + 1) * (S.size + 1) ≤ 12 * B := by
    have h2 : (D + 1) * (p + 3) + 1 ≤ 5 * ((D + 1) * (p + 1)) := by
      calc (D + 1) * (p + 3) + 1 ≤ (D + 1) * (4 * (p + 1)) + (D + 1) * (p + 1) := by
            apply Nat.add_le_add
            · exact Nat.mul_le_mul_left _ (by omega)
            · exact one_le_mul' hD1 hp1
        _ = 5 * ((D + 1) * (p + 1)) := by ring
    have hs2 : S * (S.size + 1) ≤ (S + 1) * (2 * (p + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc S * ((D + 1) * (p + 3) + 1) * (S.size + 1)
        = (S * (S.size + 1)) * ((D + 1) * (p + 3) + 1) := by ring
      _ ≤ ((S + 1) * (2 * (p + 1))) * (5 * ((D + 1) * (p + 1))) := Nat.mul_le_mul hs2 h2
      _ = 10 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) := by ring
      _ ≤ 12 * B := by
          rw [hB]
          have hlt : 10 * ((S + 1) * (D + 1) * (p + 1) * (p + 1))
              ≤ 12 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) :=
            Nat.mul_le_mul_right _ (by norm_num)
          exact hlt
  have hX3 : 1 * (S.size + 1) ≤ 2 * B := by
    have hQ : 1 ≤ (S + 1) * (D + 1) * (p + 1) := one_le_mul' (one_le_mul' hS1 hD1) hp1
    rw [hB]
    calc 1 * (S.size + 1) ≤ 2 * (p + 1) := by omega
      _ ≤ 2 * ((S + 1) * (D + 1) * (p + 1) * (p + 1)) := by
          apply Nat.mul_le_mul_left
          calc (p + 1) = 1 * (p + 1) := by ring
            _ ≤ ((S + 1) * (D + 1) * (p + 1)) * (p + 1) := Nat.mul_le_mul_right _ hQ
            _ = (S + 1) * (D + 1) * (p + 1) * (p + 1) := by ring
  have hCrt : Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
      ≤ 100 * (Kcrt * B) := by
    have he : ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
        = (S + 1) * (2 * p + 8) * (S.size + 1)
          + S * ((D + 1) * (p + 3) + 1) * (S.size + 1) + 1 * (S.size + 1) := by ring
    have h2 : ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
        ≤ 22 * B := by
      rw [he]
      omega
    calc Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
        = Kcrt * (((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1)
            * (S.size + 1)) := by ring
      _ ≤ Kcrt * (22 * B) := Nat.mul_le_mul_left Kcrt h2
      _ = 22 * (Kcrt * B) := by ring
      _ ≤ 100 * (Kcrt * B) := Nat.mul_le_mul_right _ (by norm_num)
  have hRev : Krev * (S + 1) * (p + 1) * (p + 1) + Krev ≤ 2 * (Krev * B) := by
    have h1 : (S + 1) * (p + 1) * (p + 1) ≤ B := by
      rw [hB]
      calc (S + 1) * (p + 1) * (p + 1) = 1 * ((S + 1) * (p + 1) * (p + 1)) := by ring
        _ ≤ (D + 1) * ((S + 1) * (p + 1) * (p + 1)) := Nat.mul_le_mul_right _ hD1
        _ = (S + 1) * (D + 1) * (p + 1) * (p + 1) := by ring
    have h2 : Krev * (S + 1) * (p + 1) * (p + 1) ≤ Krev * B := by
      calc Krev * (S + 1) * (p + 1) * (p + 1)
          = Krev * ((S + 1) * (p + 1) * (p + 1)) := by ring
        _ ≤ Krev * B := Nat.mul_le_mul_left Krev h1
    have h3 : Krev ≤ Krev * B := by
      calc Krev = Krev * 1 := by ring
        _ ≤ Krev * B := Nat.mul_le_mul_left Krev hB1
    calc Krev * (S + 1) * (p + 1) * (p + 1) + Krev ≤ Krev * B + Krev * B := add_le_add h2 h3
      _ = 2 * (Krev * B) := by ring
  have ht1 : 8 * (20 * Kp * phiOf S p D) ≤ 6720 * (Kp * B) := by
    have h1 : 20 * Kp * phiOf S p D ≤ 20 * Kp * (42 * B) := Nat.mul_le_mul_left _ hPhi
    calc 8 * (20 * Kp * phiOf S p D) ≤ 8 * (20 * Kp * (42 * B)) := Nat.mul_le_mul_left 8 h1
      _ = 6720 * (Kp * B) := by ring
  have ht2 : 4 * (20 * Kr * phiOf S p D) ≤ 3360 * (Kr * B) := by
    have h1 : 20 * Kr * phiOf S p D ≤ 20 * Kr * (42 * B) := Nat.mul_le_mul_left _ hPhi
    calc 4 * (20 * Kr * phiOf S p D) ≤ 4 * (20 * Kr * (42 * B)) := Nat.mul_le_mul_left 4 h1
      _ = 3360 * (Kr * B) := by ring
  have ht3 : 3 * (2 * Kd * phiOf S p D) ≤ 252 * (Kd * B) := by
    have h1 : 2 * Kd * phiOf S p D ≤ 2 * Kd * (42 * B) := Nat.mul_le_mul_left _ hPhi
    calc 3 * (2 * Kd * phiOf S p D) ≤ 3 * (2 * Kd * (42 * B)) := Nat.mul_le_mul_left 3 h1
      _ = 252 * (Kd * B) := by ring
  have ht4 : 4 * Kv * phiOf S p D ≤ 168 * (Kv * B) := by
    have h1 : 4 * Kv * phiOf S p D ≤ 4 * Kv * (42 * B) := Nat.mul_le_mul_left _ hPhi
    calc 4 * Kv * phiOf S p D ≤ 4 * Kv * (42 * B) := h1
      _ = 168 * (Kv * B) := by ring
  have hothers : 8 * (20 * Kp * phiOf S p D) + 4 * (20 * Kr * phiOf S p D)
      + 3 * (2 * Kd * phiOf S p D) + 4 * Kv * phiOf S p D
      + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
      + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
      ≤ 1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1) * B := by
    have h1 : 6720 * (Kp * B) ≤ 1000000 * (Kp * B) := Nat.mul_le_mul_right _ (by norm_num)
    have h2 : 3360 * (Kr * B) ≤ 1000000 * (Kr * B) := Nat.mul_le_mul_right _ (by norm_num)
    have h3 : 252 * (Kd * B) ≤ 1000000 * (Kd * B) := Nat.mul_le_mul_right _ (by norm_num)
    have h4 : 168 * (Kv * B) ≤ 1000000 * (Kv * B) := Nat.mul_le_mul_right _ (by norm_num)
    have h5 : 2 * (Krev * B) ≤ 1000000 * (Krev * B) := Nat.mul_le_mul_right _ (by norm_num)
    have h6 : 100 * (Kcrt * B) ≤ 1000000 * (Kcrt * B) := Nat.mul_le_mul_right _ (by norm_num)
    have hsum := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4) hRev) hCrt
    have hsum2 := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5) h6
    have hmid : 6720 * (Kp * B) + 3360 * (Kr * B) + 252 * (Kd * B) + 168 * (Kv * B)
        + 2 * (Krev * B) + 100 * (Kcrt * B)
        ≤ 1000000 * (Kp * B) + 1000000 * (Kr * B) + 1000000 * (Kd * B)
          + 1000000 * (Kv * B) + 1000000 * (Krev * B) + 1000000 * (Kcrt * B) + 1000000 * B := by
      refine le_trans hsum2 ?_
      exact le_add_of_nonneg_right (Nat.zero_le _)
    have hfin : 1000000 * (Kp * B) + 1000000 * (Kr * B) + 1000000 * (Kd * B)
        + 1000000 * (Kv * B) + 1000000 * (Krev * B) + 1000000 * (Kcrt * B) + 1000000 * B
        = 1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1) * B := by ring
    calc 8 * (20 * Kp * phiOf S p D) + 4 * (20 * Kr * phiOf S p D)
          + 3 * (2 * Kd * phiOf S p D) + 4 * Kv * phiOf S p D
          + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
          + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)
        ≤ 6720 * (Kp * B) + 3360 * (Kr * B) + 252 * (Kd * B) + 168 * (Kv * B)
          + 2 * (Krev * B) + 100 * (Kcrt * B) := hsum
      _ ≤ 1000000 * (Kp * B) + 1000000 * (Kr * B) + 1000000 * (Kd * B)
          + 1000000 * (Kv * B) + 1000000 * (Krev * B) + 1000000 * (Kcrt * B) + 1000000 * B := hmid
      _ = 1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1) * B := hfin
  have hreorder : ((20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D
          + 20 * Kp * phiOf S p D) + (F + K53))
      + (20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D + 20 * Kp * phiOf S p D
          + 20 * Kr * phiOf S p D
          + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
          + (20 * Kr * phiOf S p D + 2 * Kd * phiOf S p D + 20 * Kr * phiOf S p D
              + 2 * Kd * phiOf S p D + 20 * Kr * phiOf S p D + 2 * Kd * phiOf S p D
              + 20 * Kp * phiOf S p D + 4 * Kv * phiOf S p D
              + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1)))
      = (8 * (20 * Kp * phiOf S p D) + 4 * (20 * Kr * phiOf S p D)
          + 3 * (2 * Kd * phiOf S p D) + 4 * Kv * phiOf S p D
          + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
          + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1))
        + (F + K53) := by ring
  rw [hreorder]
  have hR : (F + K53) + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (p + 1)
        * (p + 1)
      + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (D + 1) * (p + 1)
        * (p + 1)
      = (F + K53) + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (p + 1)
        * (p + 1)
      + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (D + 1) * (p + 1)
        * (p + 1) := rfl
  have hfin2 : 1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1) * B
      = (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (D + 1) * (p + 1)
        * (p + 1) := by
    rw [hB]
    ring
  calc (8 * (20 * Kp * phiOf S p D) + 4 * (20 * Kr * phiOf S p D)
          + 3 * (2 * Kd * phiOf S p D) + 4 * Kv * phiOf S p D
          + (Krev * (S + 1) * (p + 1) * (p + 1) + Krev)
          + Kcrt * ((S + 1) * (2 * p + 8) + S * ((D + 1) * (p + 3) + 1) + 1) * (S.size + 1))
        + (F + K53)
      ≤ 1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1) * B + (F + K53) :=
        add_le_add hothers (le_refl _)
    _ ≤ (F + K53) + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (p + 1)
          * (p + 1)
        + (1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1)) * (S + 1) * (D + 1) * (p + 1)
          * (p + 1) := by
        rw [hfin2]
        omega

/-! ## Stage helpers for the concrete library words -/

theorem pickStage {main : Cmd} {pickP : ℕ → Cmd} {Kp : ℕ}
    (hpick : ∀ k : ℕ, WordR main (pickP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k Val.nil :: vs)
      (fun vs => Kp * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A B : List Val} {k : ℕ} {C : ℕ} (hB : B = A.getD k Val.nil :: A) (hlen : k < A.length)
    (hC : Kp * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordR main (pickP k) (fun vs => vs = A) (fun _ out => out = B) (fun _ => C) := by
  refine wrMono (hpick k) (fun vs h => by rw [h]; exact hlen) ?_ (fun vs h => by rw [h]; exact hC)
  intro vs out h hout
  rw [h] at hout
  rw [hout]
  exact hB.symm

theorem rollStage {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (hroll : ∀ k : ℕ, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k Val.nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    {A B : List Val} {k : ℕ} {C : ℕ} (hB : B = A.getD k Val.nil :: A.eraseIdx k)
    (hlen : k < A.length)
    (hC : Kr * (k + 1) * (((A.take (k + 1)).map vsz).sum + 1) ≤ C) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = B) (fun _ => C) := by
  refine wrMono (hroll k) (fun vs h => by rw [h]; exact hlen) ?_ (fun vs h => by rw [h]; exact hC)
  intro vs out h hout
  rw [h] at hout
  rw [hout]
  exact hB.symm

theorem dropStage {main : Cmd} {dropP : Cmd} {Kd : ℕ}
    (hdrop : WordR main dropP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kd * (vsz (vs.headD Val.nil) + 1)))
    {A B : List Val} {v : Val} {C : ℕ} (hA : A = v :: B) (hC : Kd * (vsz v + 1) ≤ C) :
    WordR main dropP (fun vs => vs = A) (fun _ out => out = B) (fun _ => C) := by
  refine wrMono hdrop ?_ ?_ ?_
  · intro vs h
    rw [h, hA]
    exact List.cons_ne_nil _ _
  · intro vs out h hq
    rw [h, hA] at hq
    obtain ⟨w, rest, hv, hr⟩ := hq
    simp only [List.cons.injEq] at hv
    rw [← hv.2] at hr
    exact hr
  · intro vs h
    rw [h, hA, List.headD_cons]
    exact hC

theorem pushStage {main : Cmd} {pushP : Val → Cmd} {Kv : ℕ}
    (hpush : ∀ v : Val, WordR main (pushP v) (fun _ => True) (fun vs out => out = v :: vs)
      (fun _ => Kv * (vsz v + 1)))
    {A B : List Val} {w : Val} {C : ℕ} (hB : B = w :: A) (hC : Kv * (vsz w + 1) ≤ C) :
    WordR main (pushP w) (fun vs => vs = A) (fun _ out => out = B) (fun _ => C) := by
  refine wrMono (hpush w) (fun vs _ => trivial) ?_ (fun vs h => hC)
  intro vs out h hout
  rw [h] at hout
  rw [hout]
  exact hB.symm

theorem one_le_prod_list : ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s) → 1 ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha : 1 ≤ a := h a List.mem_cons_self
      have ht : 1 ≤ t.prod := ih (fun s hs => h s (List.mem_cons_of_mem _ hs))
      have hm := Nat.mul_le_mul ha ht
      simpa using hm



theorem finalize (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib) (hFx : HvdH.FxLib)
    (hC : HvdH.CrtWordProp) (prog53 : HvdH.Cmd) (K53 : ℕ)
    (h53 : ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm →
      ∀ (p α : ℕ) (ss ts : List ℕ), HvdH.FsParams p α ss ts → 3 * HvdH.lmax ts * p < N → K53 * p < N →
      HvdH.WordR main prog53 (P53 p α ss ts) (Q53 p α ss ts) (fun _ => 3 * HvdH.fsCost K53 Cm p α ts + K53)) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm →
      ∀ (R : List HvdH.Val) (sp : SP) (u v : List (ℤ × ℤ)),
      HvdH.FsParams sp.p sp.α sp.ss sp.ts → 3 * HvdH.lmax sp.ts * sp.p < N → K53 * sp.p < N →
      sp.S = sp.ss.prod → (∀ s ∈ sp.ss, 1 ≤ s) → sp.ss.Pairwise Nat.Coprime →
      sp.b ≤ sp.p → 2 * sp.b < sp.p → sp.S ≤ 2 ^ sp.p → 2 * sp.N' ≤ sp.S + 1 →
      u.length = sp.ss.prod → v.length = sp.ss.prod →
      (∀ z ∈ u, HvdH.inDisc sp.p z) → (∀ z ∈ v, HvdH.inDisc sp.p z) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal u :: HvdH.cvecVal v :: env sp R)
        (fun vs out => (∃ (zs : List (ℤ × ℤ)) (ys : List ℤ), vs = HvdH.cvecVal u :: HvdH.cvecVal v :: env sp R ∧
            out = HvdH.ofList (ys.map HvdH.Val.int) :: env sp R ∧
            zs.length = sp.ss.prod ∧ ys.length = sp.ss.prod ∧
            HvdH.Approx sp.p zs (HvdH.convC sp.ss (HvdH.fxVec sp.p sp.ss.prod u) (HvdH.fxVec sp.p sp.ss.prod v))
              ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ) ∧
            (∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)))))
        (fun _ => 3 * HvdH.fsCost K53 Cm sp.p sp.α sp.ts + K53 + K * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) +
          K * (sp.S + 1) * (HvdH.D + 1) * (sp.p + 1) * (sp.p + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := hKer.pick
  obtain ⟨rollP, Kr, hroll⟩ := hKer.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hKer.drop
  obtain ⟨pushP, Kv, hpush⟩ := hKer.pushVal
  obtain ⟨crtP, Kcrt, hcrtAll⟩ := hC
  obtain ⟨recP, Krev, hrecAll⟩ := Work.Main.word.recoverVec2 hKer hInt hLay
  refine ⟨((pickP 7) ;;; (pickP 9) ;;; (pickP 8) ;;; (pickP 8) ;;; prog53) ;;;
    (((pickP 3) ;;; (pickP 5) ;;; (pickP 3) ;;; (rollP 3) ;;; recP) ;;;
      ((rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;; (pickP 7) ;;;
        (pushP (Val.int (1 : ℤ))) ;;; crtP)),
    1000000 * (Kp + Kr + Kd + Kv + Kcrt + Krev + 1), ?_⟩
  intro main N Cm hmono hmul R sp u v hFs hlt1 hltK hS hss1 hsscop hb h2b hSp hNp hu hvv huD hvD
  have hFs' : HvdH.FsParams sp.p sp.α sp.ss sp.ts := hFs
  obtain ⟨hP2, hRes, h2Da, h3Dp, hssle⟩ := hFs
  obtain ⟨hPtsLen, hP2pow, hPtsPair, hPtsProd, hP100⟩ := hP2
  obtain ⟨hssLen, htsLen, hR100, h2a, halp, hRow⟩ := hRes
  have hp2 : 2 ≤ sp.p := by omega
  have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
  have hts_lt : ∀ t ∈ sp.ts, t < 2 ^ sp.p := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp ht
    have hiD : i < HvdH.D := by rwa [hPtsLen] at hi
    have hlt := (hRow i hiD).2.2.1
    rw [List.getD_eq_getElem _ 0 hi, hti] at hlt
    exact hlt
  have hss_lt : ∀ s ∈ sp.ss, s < 2 ^ sp.p := by
    intro s hs
    obtain ⟨i, hi, hsi⟩ := List.mem_iff_getElem.mp hs
    have hiD : i < HvdH.D := by rwa [hssLen] at hi
    have hlt := (hRow i hiD).2.1
    have hlt2 := (hRow i hiD).2.2.1
    rw [List.getD_eq_getElem _ 0 hi, hsi] at hlt
    exact lt_trans hlt hlt2
  have hS1 : 1 ≤ sp.S := by
    rw [hS]
    exact one_le_prod_list sp.ss hss1
  have hNle : sp.N' ≤ 2 ^ sp.p := by
    have h1 : 2 ^ sp.p + 1 ≤ 2 * 2 ^ sp.p := by
      have h2 : 2 ≤ 2 ^ sp.p := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ sp.p := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hble : sp.b ≤ 2 ^ sp.p :=
    le_trans hb (le_of_lt (show sp.p < 2 ^ sp.p from Nat.lt_two_pow_self))
  have hαle : sp.α ≤ 2 ^ sp.p := by
    have h1 : sp.α ≤ sp.p := by
      by_contra hc
      push_neg at hc
      have h4 : (sp.p + 1) ^ 2 ≤ sp.α ^ 2 := by
        calc (sp.p + 1) ^ 2 = (sp.p + 1) * (sp.p + 1) := by ring
          _ ≤ sp.α * sp.α := Nat.mul_le_mul hc hc
          _ = sp.α ^ 2 := by ring
      have h5 : sp.p < (sp.p + 1) ^ 2 := by nlinarith
      omega
    exact le_trans h1 (le_of_lt (show sp.p < 2 ^ sp.p from Nat.lt_two_pow_self))
  have hCUu : vsz (cvecVal u) ≤ (sp.S + 1) * (2 * sp.p + 8) :=
    vsz_cvecVal_le (by rw [hS]; exact hu) huD
  have hCUv : vsz (cvecVal v) ≤ (sp.S + 1) * (2 * sp.p + 8) :=
    vsz_cvecVal_le (by rw [hS]; exact hvv) hvD
  have hCTs : vsz (intList sp.ts) ≤ (HvdH.D + 1) * (sp.p + 3) := vsz_intList_le htsLen hts_lt
  have hCSs : vsz (intList sp.ss) ≤ (HvdH.D + 1) * (sp.p + 3) := vsz_intList_le hssLen hss_lt
  have hscS : isz (sp.S : ℤ) ≤ sp.p + 3 := Work.Main.word.isz_le_of_le_two_pow hSp
  have hscN : isz (sp.N' : ℤ) ≤ sp.p + 3 := Work.Main.word.isz_le_of_le_two_pow hNle
  have hscb : isz (sp.b : ℤ) ≤ sp.p + 3 := Work.Main.word.isz_le_of_le_two_pow hble
  have hscp : isz (sp.p : ℤ) ≤ sp.p + 3 :=
    le_trans (Work.Main.word.isz_int_le sp.p) (by omega)
  have hsca : isz (sp.α : ℤ) ≤ sp.p + 3 := Work.Main.word.isz_le_of_le_two_pow hαle
  set PHI : ℕ := 3 * ((sp.S + 1) * (2 * sp.p + 8)) + 6 * ((HvdH.D + 1) * (sp.p + 3))
    + 5 * (sp.p + 3) + 1 with hPHI
  have hPHI1 : 1 ≤ PHI := by rw [hPHI]; omega
  let E : List Val := env sp R
  let cu : Val := cvecVal u
  let cv : Val := cvecVal v
  let TSv : Val := intList sp.ts
  let SSv : Val := intList sp.ss
  let Sv : Val := Val.int (sp.S : ℤ)
  let Nv : Val := Val.int (sp.N' : ℤ)
  let bv : Val := Val.int (sp.b : ℤ)
  let pv : Val := Val.int (sp.p : ℤ)
  let av : Val := Val.int (sp.α : ℤ)
  let xv : Val := Val.int (sp.x : ℤ)
  let yv : Val := Val.int (sp.y : ℤ)
  let A0 : List Val := cu :: cv :: E
  let A1 : List Val := TSv :: A0
  let A2 : List Val := SSv :: A1
  let A3 : List Val := av :: A2
  let A4 : List Val := pv :: A3
  have hsumA0 : ((A0.take 8).map vsz).sum ≤ PHI := by
    refine take_sum_le_prefix (P := [cvecVal u, cvecVal v, Val.int (sp.S : ℤ), Val.int (sp.N' : ℤ),
      Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), Val.int (sp.α : ℤ), intList sp.ts])
      (R := intList sp.ss :: Val.int (sp.x : ℤ) :: Val.int (sp.y : ℤ) :: R) (n := 8) (B := PHI)
      ?_ (by simp) ?_
    · simp only [A0, E, cu, cv, env, List.cons_append, List.nil_append]
    · rw [hPHI]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int]
      omega
  have hsumA1 : ((A1.take 10).map vsz).sum ≤ PHI := by
    refine take_sum_le_prefix (P := [intList sp.ts, cvecVal u, cvecVal v, Val.int (sp.S : ℤ),
      Val.int (sp.N' : ℤ), Val.int (sp.b : ℤ), Val.int (sp.p : ℤ), Val.int (sp.α : ℤ),
      intList sp.ts, intList sp.ss])
      (R := Val.int (sp.x : ℤ) :: Val.int (sp.y : ℤ) :: R) (n := 10) (B := PHI)
      ?_ (by simp) ?_
    · simp only [A1, A0, E, TSv, cu, cv, env, List.cons_append, List.nil_append]
    · rw [hPHI]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int]
      omega
  have hsumA2 : ((A2.take 9).map vsz).sum ≤ PHI := by
    refine take_sum_le_prefix (P := [intList sp.ss, intList sp.ts, cvecVal u, cvecVal v,
      Val.int (sp.S : ℤ), Val.int (sp.N' : ℤ), Val.int (sp.b : ℤ), Val.int (sp.p : ℤ),
      Val.int (sp.α : ℤ)])
      (R := intList sp.ts :: intList sp.ss :: Val.int (sp.x : ℤ) :: Val.int (sp.y : ℤ) :: R)
      (n := 9) (B := PHI) ?_ (by simp) ?_
    · simp only [A2, A1, A0, E, SSv, TSv, cu, cv, env, List.cons_append, List.nil_append]
    · rw [hPHI]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int]
      omega
  have hsumA3 : ((A3.take 9).map vsz).sum ≤ PHI := by
    refine take_sum_le_prefix (P := [Val.int (sp.α : ℤ), intList sp.ss, intList sp.ts, cvecVal u,
      cvecVal v, Val.int (sp.S : ℤ), Val.int (sp.N' : ℤ), Val.int (sp.b : ℤ), Val.int (sp.p : ℤ)])
      (R := Val.int (sp.α : ℤ) :: intList sp.ts :: intList sp.ss :: Val.int (sp.x : ℤ) ::
        Val.int (sp.y : ℤ) :: R) (n := 9) (B := PHI) ?_ (by simp) ?_
    · simp only [A3, A2, A1, A0, E, av, SSv, TSv, cu, cv, env, List.cons_append, List.nil_append]
    · rw [hPHI]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int]
      omega
  have hget1 : A0.getD 7 Val.nil = TSv := by
    simp only [A0, cu, cv, E, env, TSv, List.getD_cons_zero, List.getD_cons_succ,
      List.cons_append, List.nil_append]
  have hlen1 : 7 < A0.length := by
    simp only [A0, cu, cv, E, env, List.length_cons, List.length_append, List.length_nil,
      List.cons_append, List.nil_append]
    omega
  have hget2 : A1.getD 9 Val.nil = SSv := by
    simp only [A1, A0, cu, cv, E, env, TSv, SSv, List.getD_cons_zero, List.getD_cons_succ,
      List.cons_append, List.nil_append]
  have hlen2 : 9 < A1.length := by
    simp only [A1, A0, cu, cv, E, env, List.length_cons, List.length_append, List.length_nil,
      List.cons_append, List.nil_append]
    omega
  have hget3 : A2.getD 8 Val.nil = av := by
    simp only [A2, A1, A0, cu, cv, E, env, TSv, SSv, av, List.getD_cons_zero, List.getD_cons_succ,
      List.cons_append, List.nil_append]
  have hlen3 : 8 < A2.length := by
    simp only [A2, A1, A0, cu, cv, E, env, List.length_cons, List.length_append, List.length_nil,
      List.cons_append, List.nil_append]
    omega
  have hget4 : A3.getD 8 Val.nil = pv := by
    simp only [A3, A2, A1, A0, cu, cv, E, env, TSv, SSv, av, pv, List.getD_cons_zero,
      List.getD_cons_succ, List.cons_append, List.nil_append]
  have hlen4 : 8 < A3.length := by
    simp only [A3, A2, A1, A0, cu, cv, E, env, List.length_cons, List.length_append, List.length_nil,
      List.cons_append, List.nil_append]
    omega
  have s1 : WordR main (pickP 7) (fun vs => vs = A0) (fun _ out => out = A1) (fun _ => 20 * Kp * PHI) :=
    pickStage (hpick main) (A := A0) (B := A1) (k := 7) (C := 20 * Kp * PHI) (by rw [hget1])
      hlen1 (pickCost_le (k := 7) (by norm_num) hsumA0 hPHI1)
  have s2 : WordR main (pickP 9) (fun vs => vs = A1) (fun _ out => out = A2) (fun _ => 20 * Kp * PHI) :=
    pickStage (hpick main) (A := A1) (B := A2) (k := 9) (C := 20 * Kp * PHI) (by rw [hget2])
      hlen2 (pickCost_le (k := 9) (by norm_num) hsumA1 hPHI1)
  have s3 : WordR main (pickP 8) (fun vs => vs = A2) (fun _ out => out = A3) (fun _ => 20 * Kp * PHI) :=
    pickStage (hpick main) (A := A2) (B := A3) (k := 8) (C := 20 * Kp * PHI) (by rw [hget3])
      hlen3 (pickCost_le (k := 8) (by norm_num) hsumA2 hPHI1)
  have s4 : WordR main (pickP 8) (fun vs => vs = A3) (fun _ out => out = A4) (fun _ => 20 * Kp * PHI) :=
    pickStage (hpick main) (A := A3) (B := A4) (k := 8) (C := 20 * Kp * PHI) (by rw [hget4])
      hlen4 (pickCost_le (k := 8) (by norm_num) hsumA3 hPHI1)
  have p12 := wrSeq1 s1 s2
  have p123 := wrSeq1 p12 s3
  have p1234 := wrSeq1 p123 s4
  have s5 : WordR main prog53 (fun vs => vs = A4) (fun _ out => ∃ zs : List (ℤ × ℤ),
      out = cvecVal zs :: env sp R ∧
      HvdH.Approx sp.p zs (HvdH.convC sp.ss (HvdH.fxVec sp.p sp.ss.prod u) (HvdH.fxVec sp.p sp.ss.prod v))
        ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ))
      (fun _ => 3 * HvdH.fsCost K53 Cm sp.p sp.α sp.ts + K53) := by
    refine wrMono (h53 main N Cm hmono hmul sp.p sp.α sp.ss sp.ts hFs' hlt1 hltK) ?_ ?_ ?_
    · intro vs h
      rw [h]
      refine ⟨u, v, env sp R, ?_, ⟨hu, huD⟩, ⟨hvv, hvD⟩⟩
      simp only [A4, A3, A2, A1, A0, E, pv, av, SSv, TSv, cu, cv, env, List.cons_append,
        List.nil_append]
    · intro vs out h hq
      rw [h] at hq
      obtain ⟨us, ws, rest, zs, hvs, hout, happ⟩ := hq
      have hrest : rest = env sp R := by
        have hd := congrArg (fun l => l.drop 6) hvs
        simp only [A4, A3, A2, A1, A0, E, pv, av, SSv, TSv, cu, cv, env, List.cons_append,
          List.nil_append, List.drop_succ_cons, List.drop_zero] at hd
        exact hd.symm
      have h5 : u = us := by
        have hd := congrArg (fun l => l.getD 4 Val.nil) hvs
        simp only [A4, A3, A2, A1, A0, E, pv, av, SSv, TSv, cu, cv, env, List.cons_append,
          List.nil_append, List.getD_cons_zero, List.getD_cons_succ] at hd
        exact cvecVal_inj hd
      have h6 : v = ws := by
        have hd := congrArg (fun l => l.getD 5 Val.nil) hvs
        simp only [A4, A3, A2, A1, A0, E, pv, av, SSv, TSv, cu, cv, env, List.cons_append,
          List.nil_append, List.getD_cons_zero, List.getD_cons_succ] at hd
        exact cvecVal_inj hd
      refine ⟨zs, ?_, ?_⟩
      · rw [hout, hrest]
      · rw [← h5, ← h6] at happ
        exact happ
    · intro vs h
      exact le_rfl
  have p12345 := wrSeq1 p1234 s5
  let X1 : Cmd := (pickP 3) ;;; (pickP 5) ;;; (pickP 3) ;;; (rollP 3) ;;; recP
  let X2 : Cmd := (rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;;
    (pickP 7) ;;; (pushP (Val.int (1 : ℤ))) ;;; crtP
  let REST : Cmd := X1 ;;; X2
  let CREST : ℕ := 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kr * PHI
    + (Krev * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) + Krev)
    + (20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI
      + 2 * Kd * PHI + 20 * Kp * PHI + 4 * Kv * PHI
      + Kcrt * ((sp.S + 1) * (2 * sp.p + 8) + sp.S * ((HvdH.D + 1) * (sp.p + 3) + 1) + 1)
          * (sp.S.size + 1))
  have hCREST : CREST = 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kr * PHI
    + (Krev * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) + Krev)
    + (20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI
      + 2 * Kd * PHI + 20 * Kp * PHI + 4 * Kv * PHI
      + Kcrt * ((sp.S + 1) * (2 * sp.p + 8) + sp.S * ((HvdH.D + 1) * (sp.p + 3) + 1) + 1)
          * (sp.S.size + 1)) := rfl
  have hrest : ∀ (zs : List (ℤ × ℤ)),
      HvdH.Approx sp.p zs (HvdH.convC sp.ss (HvdH.fxVec sp.p sp.ss.prod u) (HvdH.fxVec sp.p sp.ss.prod v))
        ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ) →
      WordR main REST (fun vs => vs = cvecVal zs :: env sp R)
        (fun _ out => ∃ ys : List ℤ, out = ofList (ys.map Val.int) :: env sp R ∧ ys.length = sp.ss.prod ∧
          ∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)))
        (fun _ => CREST) := by
    intro zs happ
    have hdisc : InDiscVec sp.p sp.ss.prod zs := happ.1
    have hzl : zs.length = sp.S := by rw [hS]; exact hdisc.1
    have hvz : vsz (cvecVal zs) ≤ (sp.S + 1) * (2 * sp.p + 8) := vsz_cvecVal_le hzl hdisc.2
    let B0 : List Val := cvecVal zs :: E
    let B1 : List Val := bv :: B0
    let B2 : List Val := pv :: B1
    let B3 : List Val := Sv :: B2
    let B4 : List Val := cvecVal zs :: Sv :: pv :: bv :: E
    have hs_B0 : ((B0.take 4).map vsz).sum ≤ PHI := by
      refine take_sum_le_prefix (P := [cvecVal zs, Sv, Nv, bv])
        (R := pv :: av :: TSv :: SSv :: xv :: yv :: R) (n := 4) (B := PHI) ?_ (by simp) ?_
      · simp only [B0, E, env, Sv, Nv, bv, pv, av, TSv, SSv, xv, yv, List.cons_append,
          List.nil_append]
      · rw [hPHI]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
          Sv, Nv, bv]
        omega
    have hs_B1 : ((B1.take 6).map vsz).sum ≤ PHI := by
      refine take_sum_le_prefix (P := [bv, cvecVal zs, Sv, Nv, bv, pv])
        (R := av :: TSv :: SSv :: xv :: yv :: R) (n := 6) (B := PHI) ?_ (by simp) ?_
      · simp only [B1, B0, E, env, bv, Sv, Nv, pv, av, TSv, SSv, xv, yv, List.cons_append,
          List.nil_append]
      · rw [hPHI]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
          bv, Sv, Nv, pv]
        omega
    have hs_B2 : ((B2.take 4).map vsz).sum ≤ PHI := by
      refine take_sum_le_prefix (P := [pv, bv, cvecVal zs, Sv])
        (R := Nv :: bv :: pv :: av :: TSv :: SSv :: xv :: yv :: R) (n := 4) (B := PHI)
        ?_ (by simp) ?_
      · simp only [B2, B1, B0, E, env, pv, bv, Sv, Nv, av, TSv, SSv, xv, yv, List.cons_append,
          List.nil_append]
      · rw [hPHI]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
          pv, bv, Sv]
        omega
    have hs_B3 : ((B3.take 4).map vsz).sum ≤ PHI := by
      refine take_sum_le_prefix (P := [Sv, pv, bv, cvecVal zs])
        (R := Sv :: Nv :: bv :: pv :: av :: TSv :: SSv :: xv :: yv :: R) (n := 4) (B := PHI)
        ?_ (by simp) ?_
      · simp only [B3, B2, B1, B0, E, env, Sv, pv, bv, Nv, av, TSv, SSv, xv, yv,
          List.cons_append, List.nil_append]
      · rw [hPHI]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
          Sv, pv, bv]
        omega
    have hget_b0 : B0.getD 3 Val.nil = bv := by
      simp only [B0, E, env, bv, Sv, Nv, pv, List.getD_cons_zero, List.getD_cons_succ,
        List.cons_append, List.nil_append]
    have hlen_b0 : 3 < B0.length := by
      simp only [B0, E, env, List.length_cons, List.length_append, List.length_nil,
        List.cons_append, List.nil_append]
      omega
    have hget_b1 : B1.getD 5 Val.nil = pv := by
      simp only [B1, B0, E, env, bv, pv, Sv, Nv, List.getD_cons_zero, List.getD_cons_succ,
        List.cons_append, List.nil_append]
    have hlen_b1 : 5 < B1.length := by
      simp only [B1, B0, E, env, List.length_cons, List.length_append, List.length_nil,
        List.cons_append, List.nil_append]
      omega
    have hget_b2 : B2.getD 3 Val.nil = Sv := by
      simp only [B2, B1, B0, E, env, bv, pv, Sv, Nv, List.getD_cons_zero, List.getD_cons_succ,
        List.cons_append, List.nil_append]
    have hlen_b2 : 3 < B2.length := by
      simp only [B2, B1, B0, E, env, List.length_cons, List.length_append, List.length_nil,
        List.cons_append, List.nil_append]
      omega
    have hget_b3 : B3.getD 3 Val.nil = cvecVal zs := by
      simp only [B3, B2, B1, B0, E, env, bv, pv, Sv, Nv, List.getD_cons_zero,
        List.getD_cons_succ, List.cons_append, List.nil_append]
    have hlen_b3 : 3 < B3.length := by
      simp only [B3, B2, B1, B0, E, env, List.length_cons, List.length_append, List.length_nil,
        List.cons_append, List.nil_append]
      omega
    have d1 : WordR main (pickP 3) (fun vs => vs = B0) (fun _ out => out = B1)
        (fun _ => 20 * Kp * PHI) :=
      pickStage (hpick main) (A := B0) (B := B1) (k := 3) (C := 20 * Kp * PHI) (by rw [hget_b0])
        hlen_b0 (pickCost_le (k := 3) (by norm_num) hs_B0 hPHI1)
    have d2 : WordR main (pickP 5) (fun vs => vs = B1) (fun _ out => out = B2)
        (fun _ => 20 * Kp * PHI) :=
      pickStage (hpick main) (A := B1) (B := B2) (k := 5) (C := 20 * Kp * PHI) (by rw [hget_b1])
        hlen_b1 (pickCost_le (k := 5) (by norm_num) hs_B1 hPHI1)
    have d3 : WordR main (pickP 3) (fun vs => vs = B2) (fun _ out => out = B3)
        (fun _ => 20 * Kp * PHI) :=
      pickStage (hpick main) (A := B2) (B := B3) (k := 3) (C := 20 * Kp * PHI) (by rw [hget_b2])
        hlen_b2 (pickCost_le (k := 3) (by norm_num) hs_B2 hPHI1)
    have d4 : WordR main (rollP 3) (fun vs => vs = B3) (fun _ out => out = B4)
        (fun _ => 20 * Kr * PHI) :=
      rollStage (hroll main) (A := B3) (B := B4) (k := 3) (C := 20 * Kr * PHI)
        (by simp only [B4, B3, B2, B1, B0, E, env, Sv, pv, bv, Nv, List.getD_cons_zero,
          List.getD_cons_succ, List.eraseIdx_cons_zero, List.eraseIdx_cons_succ,
          List.cons_append, List.nil_append])
        hlen_b3 (pickCost_le (k := 3) (by norm_num) hs_B3 hPHI1)
    have dB : WordR main ((pickP 3) ;;; (pickP 5) ;;; (pickP 3) ;;; (rollP 3))
        (fun vs => vs = B0) (fun _ out => out = B4)
        (fun _ => (20 * Kp * PHI + 20 * Kp * PHI + 20 * Kp * PHI) + 20 * Kr * PHI) :=
      wrSeq1 (wrSeq1 (wrSeq1 d1 d2) d3) d4
    have d5 : WordR main recP (fun vs => vs = B4)
        (fun _ out => ∃ hs : List ℤ, out = ofList (hs.map Val.int) :: Sv :: pv :: bv :: E ∧
          hs.length = zs.length ∧
          ∀ i < zs.length, hs.getD i 0 = recov sp.S sp.p sp.b (zs.getD i (0,0)))
        (fun _ => Krev * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) + Krev) := by
      refine wrMono (hrecAll main sp.S sp.p sp.b zs E h2b hSp ⟨rfl, hdisc.2⟩) ?_ ?_ ?_
      · intro vs h
        rw [h]
      · intro vs out h hq
        obtain ⟨hs, hvs, hout, hlen, hget⟩ := hq
        exact ⟨hs, hout, hlen, hget⟩
      · intro vs h
        rw [hzl]
    have dB5 : WordR main X1 (fun vs => vs = B0)
        (fun _ out => ∃ hs : List ℤ, out = ofList (hs.map Val.int) :: Sv :: pv :: bv :: E ∧
          hs.length = zs.length ∧
          ∀ i < zs.length, hs.getD i 0 = recov sp.S sp.p sp.b (zs.getD i (0,0)))
        (fun _ => 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kp * PHI + 20 * Kr * PHI
          + (Krev * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) + Krev)) := by
      have h := wrSeq1 dB d5
      exact h
    have htail : ∀ (hs : List ℤ), hs.length = zs.length →
        (∀ i < zs.length, hs.getD i 0 = recov sp.S sp.p sp.b (zs.getD i (0,0))) →
        WordR main X2
          (fun vs => vs = ofList (hs.map Val.int) :: Sv :: pv :: bv :: E)
          (fun _ out => ∃ ys : List ℤ, out = ofList (ys.map Val.int) :: env sp R ∧
            ys.length = sp.ss.prod ∧
            ∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)))
          (fun _ => 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI
            + 2 * Kd * PHI + 20 * Kp * PHI + 4 * Kv * PHI
            + Kcrt * ((sp.S + 1) * (2 * sp.p + 8) + sp.S * ((HvdH.D + 1) * (sp.p + 3) + 1) + 1)
                * (sp.S.size + 1)) := by
      intro hs hlen hget
      have hX : vsz (ofList (hs.map Val.int)) ≤ (sp.S + 1) * (2 * sp.p + 8) := by
        apply vsz_ofList_map_int_le (S := sp.S)
        · rw [hlen, hzl]
        · intro i hi
          have hi' : i < zs.length := by rwa [← hzl] at hi
          rw [hget i hi']
          refine Work.Main.word.isz_recov_le h2b hSp (hdisc.2 _ ?_)
          exact List.mem_iff_getElem.mpr ⟨i, hi', (List.getD_eq_getElem zs (0,0) hi').symm⟩
      let X : Val := ofList (hs.map Val.int)
      let C0 : List Val := X :: Sv :: pv :: bv :: E
      let C1 : List Val := Sv :: X :: pv :: bv :: E
      let C2 : List Val := X :: pv :: bv :: E
      let C3 : List Val := pv :: X :: bv :: E
      let C4 : List Val := X :: bv :: E
      let C5 : List Val := bv :: X :: E
      let C6 : List Val := X :: E
      let D0 : List Val := SSv :: X :: E
      let D1 : List Val := Val.int (1 : ℤ) :: SSv :: X :: E
      have hdropS : vsz Sv ≤ PHI := by rw [hPHI]; simp only [Sv, Work.Main.vsz_int]; omega
      have hdropp : vsz pv ≤ PHI := by rw [hPHI]; simp only [pv, Work.Main.vsz_int]; omega
      have hdropb : vsz bv ≤ PHI := by rw [hPHI]; simp only [bv, Work.Main.vsz_int]; omega
      have hs_C0 : ((C0.take 2).map vsz).sum ≤ PHI := by
        refine take_sum_le_prefix (P := [X, Sv]) (R := pv :: bv :: E) (n := 2) (B := PHI)
          ?_ (by simp) ?_
        · simp only [C0, E, List.cons_append, List.nil_append]
        · rw [hPHI]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
            X, Sv]
          omega
      have hs_C2 : ((C2.take 2).map vsz).sum ≤ PHI := by
        refine take_sum_le_prefix (P := [X, pv]) (R := bv :: E) (n := 2) (B := PHI)
          ?_ (by simp) ?_
        · simp only [C2, E, List.cons_append, List.nil_append]
        · rw [hPHI]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
            X, pv]
          omega
      have hs_C4 : ((C4.take 2).map vsz).sum ≤ PHI := by
        refine take_sum_le_prefix (P := [X, bv]) (R := E) (n := 2) (B := PHI) ?_ (by simp) ?_
        · simp only [C4, E, List.cons_append, List.nil_append]
        · rw [hPHI]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
            X, bv]
          omega
      have hs_C6 : ((C6.take 8).map vsz).sum ≤ PHI := by
        refine take_sum_le_prefix (P := [X, Sv, Nv, bv, pv, av, TSv, SSv])
          (R := xv :: yv :: R) (n := 8) (B := PHI) ?_ (by simp) ?_
        · simp only [C6, E, env, Sv, Nv, bv, pv, av, TSv, SSv, xv, yv, List.cons_append,
            List.nil_append]
        · rw [hPHI]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Work.Main.vsz_int,
            X, Sv, Nv, bv, pv, av, TSv, SSv]
          omega
      have hget_c0 : C0.getD 1 Val.nil = Sv := by
        simp only [C0, E, Sv, List.getD_cons_zero, List.getD_cons_succ]
      have hlen_c0 : 1 < C0.length := by
        simp only [C0, E, List.length_cons, List.length_append]
        omega
      have hget_c2 : C2.getD 1 Val.nil = pv := by
        simp only [C2, E, pv, List.getD_cons_zero, List.getD_cons_succ]
      have hlen_c2 : 1 < C2.length := by
        simp only [C2, E, List.length_cons, List.length_append]
        omega
      have hget_c4 : C4.getD 1 Val.nil = bv := by
        simp only [C4, E, bv, List.getD_cons_zero, List.getD_cons_succ]
      have hlen_c4 : 1 < C4.length := by
        simp only [C4, E, List.length_cons, List.length_append]
        omega
      have hget_c6 : C6.getD 7 Val.nil = SSv := by
        simp only [C6, E, env, SSv, List.getD_cons_zero, List.getD_cons_succ,
          List.cons_append, List.nil_append]
      have hlen_c6 : 7 < C6.length := by
        simp only [C6, E, env, List.length_cons, List.length_append, List.length_nil,
          List.cons_append, List.nil_append]
        omega
      have e1 : WordR main (rollP 1) (fun vs => vs = C0) (fun _ out => out = C1)
          (fun _ => 20 * Kr * PHI) :=
        rollStage (hroll main) (A := C0) (B := C1) (k := 1) (C := 20 * Kr * PHI)
          (by simp only [C1, C0, E, Sv, List.getD_cons_zero, List.getD_cons_succ,
            List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.cons_append, List.nil_append])
          hlen_c0 (pickCost_le (k := 1) (by norm_num) hs_C0 hPHI1)
      have e2 : WordR main dropP (fun vs => vs = C1) (fun _ out => out = C2)
          (fun _ => 2 * Kd * PHI) :=
        dropStage (hdrop main) (A := C1) (B := C2) (v := Sv) (C := 2 * Kd * PHI)
          (by simp only [C1, C2, E]) (dropCost_le hdropS hPHI1)
      have e3 : WordR main (rollP 1) (fun vs => vs = C2) (fun _ out => out = C3)
          (fun _ => 20 * Kr * PHI) :=
        rollStage (hroll main) (A := C2) (B := C3) (k := 1) (C := 20 * Kr * PHI)
          (by simp only [C3, C2, E, pv, List.getD_cons_zero, List.getD_cons_succ,
            List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.cons_append, List.nil_append])
          hlen_c2 (pickCost_le (k := 1) (by norm_num) hs_C2 hPHI1)
      have e4 : WordR main dropP (fun vs => vs = C3) (fun _ out => out = C4)
          (fun _ => 2 * Kd * PHI) :=
        dropStage (hdrop main) (A := C3) (B := C4) (v := pv) (C := 2 * Kd * PHI)
          (by simp only [C3, C4, E]) (dropCost_le hdropp hPHI1)
      have e5 : WordR main (rollP 1) (fun vs => vs = C4) (fun _ out => out = C5)
          (fun _ => 20 * Kr * PHI) :=
        rollStage (hroll main) (A := C4) (B := C5) (k := 1) (C := 20 * Kr * PHI)
          (by simp only [C5, C4, E, bv, List.getD_cons_zero, List.getD_cons_succ,
            List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, List.cons_append, List.nil_append])
          hlen_c4 (pickCost_le (k := 1) (by norm_num) hs_C4 hPHI1)
      have e6 : WordR main dropP (fun vs => vs = C5) (fun _ out => out = C6)
          (fun _ => 2 * Kd * PHI) :=
        dropStage (hdrop main) (A := C5) (B := C6) (v := bv) (C := 2 * Kd * PHI)
          (by simp only [C5, C6, E]) (dropCost_le hdropb hPHI1)
      have e7 : WordR main (pickP 7) (fun vs => vs = C6) (fun _ out => out = D0)
          (fun _ => 20 * Kp * PHI) :=
        pickStage (hpick main) (A := C6) (B := D0) (k := 7) (C := 20 * Kp * PHI)
          (by rw [hget_c6]) hlen_c6 (pickCost_le (k := 7) (by norm_num) hs_C6 hPHI1)
      have e8 : WordR main (pushP (Val.int (1 : ℤ))) (fun vs => vs = D0) (fun _ out => out = D1)
          (fun _ => 4 * Kv * PHI) :=
        pushStage (hpush main) (A := D0) (B := D1) (w := Val.int (1 : ℤ)) (C := 4 * Kv * PHI)
          (by simp only [D1, D0]) (pushCost_le hPHI1)
      have hxslen : (hs.map Val.int).length = sp.ss.prod := by
        rw [List.length_map, hlen, hzl, hS]
      have e9 : WordR main crtP (fun vs => vs = D1)
          (fun _ out => ∃ ys : List Val, out = ofList ys :: E ∧ ys.length = sp.ss.prod ∧
            ∀ m < sp.ss.prod,
              ys.getD m Val.nil = (hs.map Val.int).getD (HvdH.crtIdx sp.ss m) Val.nil)
          (fun _ => Kcrt * ((sp.S + 1) * (2 * sp.p + 8) + sp.S * ((HvdH.D + 1) * (sp.p + 3) + 1) + 1)
            * (sp.S.size + 1)) := by
        refine wrMono (hcrtAll main sp.ss 1 (hs.map Val.int) hss1 hsscop hxslen (by norm_num)) ?_ ?_ ?_
        · intro vs h
          rw [h]
          refine ⟨E, ?_⟩
          simp only [D1, D0, E, X, SSv, Nat.cast_one]
        · intro vs out h hq
          rw [h] at hq
          obtain ⟨rest, ys, hvs, hout, hleny, hcrt⟩ := hq
          have hrest : rest = E := by
            have hd := congrArg (fun l => l.drop 3) hvs
            simp only [D1, D0, E, X, SSv, List.drop_succ_cons, List.drop_zero] at hd
            exact hd.symm
          refine ⟨ys, ?_, hleny, ?_⟩
          · rw [hout, hrest]
          · intro m hm
            exact (hcrt m hm).2 rfl
        · intro vs h
          rw [← hS]
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          apply add_le_add
          · apply add_le_add
            · exact hX
            · exact Nat.mul_le_mul_left sp.S (Nat.add_le_add_right hCSs 1)
          · rfl
      have h9 : WordR main X2 (fun vs => vs = C0)
          (fun _ out => ∃ ys : List Int, out = ofList (ys.map Val.int) :: env sp R ∧
            ys.length = sp.ss.prod ∧
            ∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)))
          (fun _ => 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI + 2 * Kd * PHI + 20 * Kr * PHI
            + 2 * Kd * PHI + 20 * Kp * PHI + 4 * Kv * PHI
            + Kcrt * ((sp.S + 1) * (2 * sp.p + 8) + sp.S * ((HvdH.D + 1) * (sp.p + 3) + 1) + 1)
                * (sp.S.size + 1)) := by
        have hh := wrSeq1 (wrSeq1 (wrSeq1 (wrSeq1 (wrSeq1 (wrSeq1 (wrSeq1 e1 e2) e3) e4) e5) e6) e7) e8
        have hh2 := wrSeq1 hh e9
        have heq : X2 = (rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;; (rollP 1) ;;; dropP ;;;
            (pickP 7) ;;; (pushP (Val.int (1 : ℤ))) ;;; crtP := rfl
        rw [heq]
        exact wrMono hh2 (fun vs h => h) (fun vs out h hq => by
          obtain ⟨ys, hout, hylen, hcrt⟩ := hq
          have hidx : ∀ m < sp.ss.prod, HvdH.crtIdx sp.ss m < hs.length := by
            intro m hm
            rw [hlen, hzl, hS]
            exact crtIdx_lt hss1 m
          obtain ⟨ys', hys, hylen', hrec'⟩ := crtIdent (hhsl := hlen) (hidx := hidx) hylen hcrt hget
          exact ⟨ys', by rw [hout, hys], hylen', hrec'⟩) (fun vs h => le_rfl)
      exact h9
    have dAll : WordR main REST (fun vs => vs = cvecVal zs :: env sp R)
        (fun _ out => ∃ ys : List ℤ, out = ofList (ys.map Val.int) :: env sp R ∧
          ys.length = sp.ss.prod ∧
          ∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)))
        (fun _ => CREST) := by
      have heq : REST = X1 ;;; X2 := rfl
      rw [heq]
      refine wrMono (wrSeqX (X := List ℤ)
        (Body := fun hs => ofList (hs.map Val.int) :: Sv :: pv :: bv :: E)
        dB5 (fun hs hf => htail hs hf.1 hf.2)) (fun vs h => h) ?_ ?_
      · intro vs out h hq
        obtain ⟨hs1, hf, ys, hout, hylen, hrec⟩ := hq
        exact ⟨ys, hout, hylen, hrec⟩
      · intro vs h
        rw [hCREST, hPHI]
        try omega
    exact dAll
  have hfull := wrSeqX
    (q₁ := (pickP 7) ;;; (pickP 9) ;;; (pickP 8) ;;; (pickP 8) ;;; prog53)
    (q₂ := REST)
    (X := List (ℤ × ℤ)) (Body := fun zs => cvecVal zs :: env sp R)
    p12345 (fun zs happ => hrest zs happ)
  refine wrMono hfull (fun vs h => h) ?_ ?_
  · intro vs out h hq
    obtain ⟨zs, happ, ys, hout, hylen, hrec⟩ := hq
    exact ⟨zs, ys, h, hout, happ.1.1, hylen, happ, hrec⟩
  · intro vs _
    have hPHI' : PHI = phiOf sp.S sp.p HvdH.D := rfl
    rw [hPHI', hCREST]
    have hca := costArith (S := sp.S) (D := HvdH.D) (p := sp.p) (Kp := Kp) (Kr := Kr) (Kd := Kd)
      (Kv := Kv) (Kcrt := Kcrt) (Krev := Krev)
      (F := 3 * HvdH.fsCost K53 Cm sp.p sp.α sp.ts) (K53 := K53) hS1 hD1 hp2 hSp
    exact hca

end Work.Main.fstep
