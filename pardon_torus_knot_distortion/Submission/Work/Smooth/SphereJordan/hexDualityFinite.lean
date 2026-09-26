import Mathlib

namespace Work.Smooth.SphereJordan

open Classical

set_option maxHeartbeats 1000000

/-! ## Generic combinatorial tools -/

/-- A `Relation.ReflTransGen` chain is a `Fin`-indexed path. -/
lemma reflTransGen_to_path {X : Type*} (r : X → X → Prop) {a b : X}
    (h : Relation.ReflTransGen r a b) :
    ∃ m : ℕ, ∃ f : Fin (m + 1) → X,
      f 0 = a ∧ f (Fin.last m) = b ∧ ∀ i : Fin m, r (f i.castSucc) (f i.succ) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i => i.elim0⟩
  | tail hab hbc ih =>
      rename_i c
      obtain ⟨m, f, hf0, hflast, hfstep⟩ := ih
      refine ⟨m + 1, @Fin.snoc (m+1) (fun _ => X) f c, ?_, ?_, ?_⟩
      · show @Fin.snoc (m+1) (fun _ => X) f c (0 : Fin (m + 2)) = a
        rw [show (0 : Fin (m+2)) = Fin.castSucc (0 : Fin (m+1)) from rfl,
            @Fin.snoc_castSucc (m+1) (fun _ => X) c f, hf0]
      · exact @Fin.snoc_last (m+1) (fun _ => X) c f
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.succ_castSucc, @Fin.snoc_castSucc (m+1) (fun _ => X) c f,
              @Fin.snoc_castSucc (m+1) (fun _ => X) c f]
          exact hfstep j
        · rw [Fin.succ_last, @Fin.snoc_castSucc (m+1) (fun _ => X) c f,
              @Fin.snoc_last (m+1) (fun _ => X) c f, hflast]
          exact hbc

/-- Parity fact: if all vertices outside `T ∪ B` have even degree and the number of
odd-degree vertices in `T` is odd, then some component meets both `T` and `B`. -/
lemma reachableOfOddDeg {C : Type*} [Fintype C] [DecidableEq C]
    (G : SimpleGraph C) [DecidableRel G.Adj]
    (T B : C → Prop) [DecidablePred T] [DecidablePred B]
    (heven : ∀ c, ¬ T c → ¬ B c → Even (G.degree c))
    (hodd : Odd (Finset.univ.filter (fun c => T c ∧ Odd (G.degree c))).card) :
    ∃ t b, T t ∧ B b ∧ G.Reachable t b := by
  classical
  by_contra hcon
  push_neg at hcon
  let U : C → Prop := fun c => ∃ t, T t ∧ G.Reachable t c
  have hUclosed : ∀ a b, G.Adj a b → U a → U b := by
    rintro a b hab ⟨t, ht, hr⟩
    exact ⟨t, ht, hr.trans (hab.reachable)⟩
  have hTU : ∀ c, T c → U c := fun c hc => ⟨c, hc, SimpleGraph.Reachable.refl c⟩
  have hUB : ∀ c, U c → ¬ B c := by
    rintro c ⟨t, ht, hr⟩ hb
    exact hcon t c ht hb hr
  let G2 : SimpleGraph C :=
    { Adj := fun a b => G.Adj a b ∧ U a
      symm := ⟨fun a b h => ⟨G.symm.symm a b h.1, hUclosed a b h.1 h.2⟩⟩
      loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩ }
  have hdeg2 : ∀ c, Odd (G2.degree c) ↔ (U c ∧ Odd (G.degree c)) := by
    intro c
    by_cases hc : U c
    · have hthis : G2.degree c = G.degree c := by
        simp only [SimpleGraph.degree]
        congr 1
        ext d
        simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hthis]; exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
    · have hthis : G2.degree c = 0 := by
        rw [SimpleGraph.degree, Finset.card_eq_zero]
        ext d
        simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
        rintro ⟨-, hU⟩
        exact hc hU
      rw [hthis]
      constructor
      · intro h; exact absurd h Nat.not_odd_zero
      · rintro ⟨hU, -⟩; exact absurd hU hc
  have hEven2 : Even (Finset.univ.filter (fun c => Odd (G2.degree c))).card := by
    simpa only [Set.toFinset_ofPred] using SimpleGraph.even_card_odd_degree_vertices G2
  have hEq1 : (Finset.univ.filter (fun c => Odd (G2.degree c)))
      = (Finset.univ.filter (fun c => U c ∧ Odd (G.degree c))) := by
    apply Finset.filter_congr
    intro c _
    exact hdeg2 c
  rw [hEq1] at hEven2
  have hEq2 : (Finset.univ.filter (fun c => U c ∧ Odd (G.degree c)))
      = (Finset.univ.filter (fun c => T c ∧ Odd (G.degree c))) := by
    apply Finset.filter_congr
    intro c _
    constructor
    · rintro ⟨hU, hodd'⟩
      refine ⟨?_, hodd'⟩
      by_contra hTc
      exact (Nat.not_even_iff_odd.mpr hodd') (heven c hTc (hUB c hU))
    · rintro ⟨hT, hodd'⟩
      exact ⟨hTU c hT, hodd'⟩
  rw [hEq2] at hEven2
  have hodd' : Odd (Finset.univ.filter (fun c => T c ∧ Odd (G.degree c))).card := by
    simpa only [Set.toFinset_ofPred] using hodd
  exact (Nat.not_even_iff_odd.mpr hodd') hEven2

/-! ## The grid -/

/-- Cells of the real board (integral coordinates). -/
def isO (N : ℕ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 < (N:ℤ) ∧ 0 ≤ p.2 ∧ p.2 < (N:ℤ)

/-- Cells of the board extended by one virtual column on the left. -/
def isE (N : ℕ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 < (N:ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (N:ℤ)

/-- Reinterpret an in-board integral cell as a `Fin`-indexed cell. -/
def toFin {N : ℕ} (p : ℤ × ℤ) (h : isO N p) : Fin N × Fin N :=
  (⟨p.1.toNat, (Int.toNat_lt h.1).mpr h.2.1⟩, ⟨p.2.toNat, (Int.toNat_lt h.2.2.1).mpr h.2.2.2⟩)

/-- `p` is a blocked cell of the real board. -/
def bk {N : ℕ} (blocked : Fin N × Fin N → Prop) (p : ℤ × ℤ) : Prop :=
  ∃ h : isO N p, blocked (toFin p h)

/-- `p` is an unblocked cell of the real board. -/
def Unb {N : ℕ} (blocked : Fin N × Fin N → Prop) (p : ℤ × ℤ) : Prop := isO N p ∧ ¬ bk blocked p

/-- 4-adjacency of cells (same row, adjacent columns; or same column, adjacent rows). -/
def adj4 (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

/-- 8-adjacency of cells (as in the second disjunct of the target). -/
def adj8 (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∨ p.1 + 1 = q.1 ∨ q.1 + 1 = p.1) ∧
  (p.2 = q.2 ∨ p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)

/-- Adjacency relation on unblocked cells. -/
def RelU {N : ℕ} (blocked : Fin N × Fin N → Prop) (p q : ℤ × ℤ) : Prop :=
  Unb blocked p ∧ Unb blocked q ∧ adj4 p q

/-- Cells of the real board reachable from the left edge through unblocked cells. -/
def InR {N : ℕ} (blocked : Fin N × Fin N → Prop) (x : ℤ × ℤ) : Prop :=
  Unb blocked x ∧ ∃ y : ℤ × ℤ, y.2 = 0 ∧ Unb blocked y ∧ Relation.ReflTransGen (RelU blocked) y x

/-- Membership in the extended reachable region `R⁺` (board plus virtual column). -/
def Rp {N : ℕ} (blocked : Fin N × Fin N → Prop) (p : ℤ × ℤ) : Prop :=
  isE N p ∧ (p.2 = 0 ∨ InR blocked (p.1, p.2 - 1))

/-! ## Basic facts -/

lemma adj4_symm {p q : ℤ × ℤ} (h : adj4 p q) : adj4 q p := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a.symm, b.symm⟩
  · exact Or.inr ⟨a.symm, b.symm⟩

lemma InR_unb {N : ℕ} {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ} (h : InR blocked x) :
    Unb blocked x := h.1

lemma InR_extension {N : ℕ} {blocked : Fin N × Fin N → Prop} {x y : ℤ × ℤ}
    (hx : InR blocked x) (hxy : adj4 x y) (hy : Unb blocked y) : InR blocked y := by
  obtain ⟨hxu, z, hz0, hzu, hchain⟩ := hx
  refine ⟨hy, z, hz0, hzu, ?_⟩
  exact hchain.tail (⟨hxu, hy, hxy⟩ : RelU blocked x y)

/-! ## The two disjuncts -/

/-- The first disjunct: an unblocked left-to-right 4-crossing. -/
def LRopen {N : ℕ} (blocked : Fin N × Fin N → Prop) : Prop :=
  ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, ¬ blocked (f i)) ∧
      (∀ i : Fin m,
        ((f i.castSucc).1 = (f i.succ).1 ∧
          ((f i.castSucc).2.1 + 1 = (f i.succ).2.1 ∨ (f i.succ).2.1 + 1 = (f i.castSucc).2.1)) ∨
        ((f i.castSucc).2 = (f i.succ).2 ∧
          ((f i.castSucc).1.1 + 1 = (f i.succ).1.1 ∨ (f i.succ).1.1 + 1 = (f i.castSucc).1.1))) ∧
      (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = N

/-- The second disjunct: a blocked top-to-bottom 8-crossing. -/
def TBblocked {N : ℕ} (blocked : Fin N × Fin N → Prop) : Prop :=
  ∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, blocked (f i)) ∧
      (∀ i : Fin m,
        ((f i.castSucc).1 = (f i.succ).1 ∨ (f i.castSucc).1.1 + 1 = (f i.succ).1.1 ∨ (f i.succ).1.1 + 1 = (f i.castSucc).1.1) ∧
        ((f i.castSucc).2 = (f i.succ).2 ∨ (f i.castSucc).2.1 + 1 = (f i.succ).2.1 ∨ (f i.succ).2.1 + 1 = (f i.castSucc).2.1)) ∧
      (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N

/-! ## Converting integral cells to `Fin` cells -/

lemma toNat_eq_iff {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a.toNat = b.toNat ↔ a = b := by
  constructor
  · intro h
    have h2 : (a.toNat : ℤ) = (b.toNat : ℤ) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] at h2
  · intro h; rw [h]

lemma toNat_add_one_iff {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.toNat + 1 = b.toNat ↔ a + 1 = b := by
  constructor
  · intro h
    have h2 : (a.toNat : ℤ) + 1 = (b.toNat : ℤ) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb] at h2
  · intro h
    have h2 : (a.toNat : ℤ) + 1 = (b.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]; exact h
    have h3 : ((a.toNat + 1 : ℕ) : ℤ) = (b.toNat : ℤ) := by push_cast; exact h2
    exact_mod_cast h3

lemma toFin_fst_val {N : ℕ} (p : ℤ × ℤ) (h : isO N p) : (toFin p h).1.1 = p.1.toNat := rfl
lemma toFin_snd_val {N : ℕ} (p : ℤ × ℤ) (h : isO N p) : (toFin p h).2.1 = p.2.toNat := rfl

lemma toFin_fst_eq {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin p hp).1 = (toFin q hq).1 ↔ p.1 = q.1 := by
  rw [Fin.ext_iff, toFin_fst_val, toFin_fst_val, toNat_eq_iff hp.1 hq.1]

lemma toFin_snd_eq {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin p hp).2 = (toFin q hq).2 ↔ p.2 = q.2 := by
  rw [Fin.ext_iff, toFin_snd_val, toFin_snd_val, toNat_eq_iff hp.2.2.1 hq.2.2.1]

lemma toFin_fst_add {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin p hp).1.1 + 1 = (toFin q hq).1.1 ↔ p.1 + 1 = q.1 := by
  rw [toFin_fst_val, toFin_fst_val, toNat_add_one_iff hp.1 hq.1]

lemma toFin_fst_add' {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin q hq).1.1 + 1 = (toFin p hp).1.1 ↔ q.1 + 1 = p.1 := by
  rw [toFin_fst_val, toFin_fst_val, toNat_add_one_iff hq.1 hp.1]

lemma toFin_snd_add {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin p hp).2.1 + 1 = (toFin q hq).2.1 ↔ p.2 + 1 = q.2 := by
  rw [toFin_snd_val, toFin_snd_val, toNat_add_one_iff hp.2.2.1 hq.2.2.1]

lemma toFin_snd_add' {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) :
    (toFin q hq).2.1 + 1 = (toFin p hp).2.1 ↔ q.2 + 1 = p.2 := by
  rw [toFin_snd_val, toFin_snd_val, toNat_add_one_iff hq.2.2.1 hp.2.2.1]

lemma toFin_adj4 {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) (h : adj4 p q) :
    ((toFin p hp).1 = (toFin q hq).1 ∧
      ((toFin p hp).2.1 + 1 = (toFin q hq).2.1 ∨ (toFin q hq).2.1 + 1 = (toFin p hp).2.1)) ∨
    ((toFin p hp).2 = (toFin q hq).2 ∧
      ((toFin p hp).1.1 + 1 = (toFin q hq).1.1 ∨ (toFin q hq).1.1 + 1 = (toFin p hp).1.1)) := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨(toFin_fst_eq hp hq).mpr h1, Or.inl ((toFin_snd_add hp hq).mpr h2)⟩
  · exact Or.inl ⟨(toFin_fst_eq hp hq).mpr h1, Or.inr ((toFin_snd_add' hp hq).mpr h2)⟩
  · exact Or.inr ⟨(toFin_snd_eq hp hq).mpr h1, Or.inl ((toFin_fst_add hp hq).mpr h2)⟩
  · exact Or.inr ⟨(toFin_snd_eq hp hq).mpr h1, Or.inr ((toFin_fst_add' hp hq).mpr h2)⟩

lemma toFin_adj8 {N : ℕ} {p q : ℤ × ℤ} (hp : isO N p) (hq : isO N q) (h : adj8 p q) :
    ((toFin p hp).1 = (toFin q hq).1 ∨ (toFin p hp).1.1 + 1 = (toFin q hq).1.1 ∨
      (toFin q hq).1.1 + 1 = (toFin p hp).1.1) ∧
    ((toFin p hp).2 = (toFin q hq).2 ∨ (toFin p hp).2.1 + 1 = (toFin q hq).2.1 ∨
      (toFin q hq).2.1 + 1 = (toFin p hp).2.1) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1 | h1
    · exact Or.inl ((toFin_fst_eq hp hq).mpr h1)
    · exact Or.inr (Or.inl ((toFin_fst_add hp hq).mpr h1))
    · exact Or.inr (Or.inr ((toFin_fst_add' hp hq).mpr h1))
  · rcases h2 with h2 | h2 | h2
    · exact Or.inl ((toFin_snd_eq hp hq).mpr h2)
    · exact Or.inr (Or.inl ((toFin_snd_add hp hq).mpr h2))
    · exact Or.inr (Or.inr ((toFin_snd_add' hp hq).mpr h2))

lemma toNat_sub_one_add_one (N : ℕ) (hN : 0 < N) : ((N:ℤ) - 1).toNat + 1 = N := by
  have h : 0 ≤ (N:ℤ) - 1 := by omega
  have h3 : ((((N:ℤ) - 1).toNat + 1 : ℕ) : ℤ) = (N:ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg h]
    ring
  exact_mod_cast h3

/-! ## From reachability to the first disjunct -/

lemma LRopen_of_InR {N : ℕ} (hN : 0 < N) {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ}
    (hx : InR blocked x) (hxN : x.2 = (N:ℤ) - 1) : LRopen blocked := by
  obtain ⟨hxu, y, hy0, hyu, hchain⟩ := hx
  obtain ⟨m, g, hg0, hgl, hgs⟩ := reflTransGen_to_path (RelU blocked) hchain
  have hUnb : ∀ i : Fin (m + 1), Unb blocked (g i) := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · rw [h0, hg0]; exact hyu
    · exact (hgs j).2.1
  refine ⟨m, fun i => toFin (g i) (hUnb i).1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact fun hb => (hUnb i).2 ⟨(hUnb i).1, hb⟩
  · intro i
    exact toFin_adj4 (hUnb i.castSucc).1 (hUnb i.succ).1 (hgs i).2.2
  · change (g 0).2.toNat = 0
    rw [hg0, hy0]
    rfl
  · change (g (Fin.last m)).2.toNat + 1 = N
    rw [hgl, hxN]
    exact toNat_sub_one_add_one N hN


/-! ## The interface graph on corners -/

/-- The corners of the extended board. -/
noncomputable def cornerFinset (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (0:ℤ) (N:ℤ)) ×ˢ (Finset.Icc (0:ℤ) ((N:ℤ) + 1))

/-- The finite type of corners. -/
abbrev CC (N : ℕ) : Type := {x : ℤ × ℤ // x ∈ cornerFinset N}

noncomputable instance (N : ℕ) : Fintype (CC N) := (cornerFinset N).finite_toSet.fintype

lemma mem_cornerFinset {N : ℕ} {x : ℤ × ℤ} :
    x ∈ cornerFinset N ↔ 0 ≤ x.1 ∧ x.1 ≤ (N:ℤ) ∧ 0 ≤ x.2 ∧ x.2 ≤ (N:ℤ) + 1 := by
  simp only [cornerFinset, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- interface edge direction predicates -/
def upI {N : ℕ} (blocked : Fin N × Fin N → Prop) (x : ℤ × ℤ) : Prop :=
  isE N (x.1 - 1, x.2 - 1) ∧ isE N (x.1 - 1, x.2) ∧
    Xor (Rp blocked (x.1 - 1, x.2 - 1)) (Rp blocked (x.1 - 1, x.2))

def dnI {N : ℕ} (blocked : Fin N × Fin N → Prop) (x : ℤ × ℤ) : Prop :=
  isE N (x.1, x.2 - 1) ∧ isE N (x.1, x.2) ∧
    Xor (Rp blocked (x.1, x.2 - 1)) (Rp blocked (x.1, x.2))

def ltI {N : ℕ} (blocked : Fin N × Fin N → Prop) (x : ℤ × ℤ) : Prop :=
  isE N (x.1 - 1, x.2 - 1) ∧ isE N (x.1, x.2 - 1) ∧
    Xor (Rp blocked (x.1 - 1, x.2 - 1)) (Rp blocked (x.1, x.2 - 1))

def rtI {N : ℕ} (blocked : Fin N × Fin N → Prop) (x : ℤ × ℤ) : Prop :=
  isE N (x.1 - 1, x.2) ∧ isE N (x.1, x.2) ∧
    Xor (Rp blocked (x.1 - 1, x.2)) (Rp blocked (x.1, x.2))

lemma upI_mem {N : ℕ} {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ} (h : upI blocked x) :
    (x.1 - 1, x.2) ∈ cornerFinset N := by
  have hE : isE N (x.1 - 1, x.2) := h.2.1
  rw [mem_cornerFinset]
  simp only [isE] at hE
  exact ⟨hE.1, by omega, hE.2.2.1, by omega⟩

lemma dnI_mem {N : ℕ} {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ} (h : dnI blocked x) :
    (x.1 + 1, x.2) ∈ cornerFinset N := by
  have hE : isE N (x.1, x.2) := h.2.1
  rw [mem_cornerFinset]
  simp only [isE] at hE
  exact ⟨by omega, by omega, hE.2.2.1, by omega⟩

lemma ltI_mem {N : ℕ} {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ} (h : ltI blocked x) :
    (x.1, x.2 - 1) ∈ cornerFinset N := by
  have hE : isE N (x.1, x.2 - 1) := h.2.1
  rw [mem_cornerFinset]
  simp only [isE] at hE
  exact ⟨hE.1, by omega, hE.2.2.1, by omega⟩

lemma rtI_mem {N : ℕ} {blocked : Fin N × Fin N → Prop} {x : ℤ × ℤ} (h : rtI blocked x) :
    (x.1, x.2 + 1) ∈ cornerFinset N := by
  have hE : isE N (x.1, x.2) := h.2.1
  rw [mem_cornerFinset]
  simp only [isE] at hE
  exact ⟨hE.1, by omega, by omega, by omega⟩

lemma upI_dnI {N : ℕ} {blocked : Fin N × Fin N → Prop} (x : ℤ × ℤ) :
    upI blocked (x.1 + 1, x.2) ↔ dnI blocked x := by
  simp only [upI, dnI, add_sub_cancel_right]

lemma dnI_upI {N : ℕ} {blocked : Fin N × Fin N → Prop} (x : ℤ × ℤ) :
    dnI blocked (x.1 - 1, x.2) ↔ upI blocked x := by
  simp only [upI, dnI]

lemma ltI_rtI {N : ℕ} {blocked : Fin N × Fin N → Prop} (x : ℤ × ℤ) :
    ltI blocked (x.1, x.2 + 1) ↔ rtI blocked x := by
  simp only [ltI, rtI, add_sub_cancel_right]

lemma rtI_ltI {N : ℕ} {blocked : Fin N × Fin N → Prop} (x : ℤ × ℤ) :
    rtI blocked (x.1, x.2 - 1) ↔ ltI blocked x := by
  simp only [rtI, ltI]

/-- Adjacency in the interface graph, in coordinate form. -/
def IAdjZ {N : ℕ} (blocked : Fin N × Fin N → Prop) (x y : ℤ × ℤ) : Prop :=
  (y = (x.1 + 1, x.2) ∧ dnI blocked x) ∨ (y = (x.1 - 1, x.2) ∧ upI blocked x) ∨
  (y = (x.1, x.2 + 1) ∧ rtI blocked x) ∨ (y = (x.1, x.2 - 1) ∧ ltI blocked x)

lemma IAdjZ_irrefl {N : ℕ} {blocked : Fin N × Fin N → Prop} (x : ℤ × ℤ) :
    ¬ IAdjZ blocked x x := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
  · have hh : x.1 = x.1 + 1 := congrArg Prod.fst h; omega
  · have hh : x.1 = x.1 - 1 := congrArg Prod.fst h; omega
  · have hh : x.2 = x.2 + 1 := congrArg Prod.snd h; omega
  · have hh : x.2 = x.2 - 1 := congrArg Prod.snd h; omega

lemma IAdjZ_symm {N : ℕ} {blocked : Fin N × Fin N → Prop} {x y : ℤ × ℤ}
    (h : IAdjZ blocked x y) : IAdjZ blocked y x := by
  rcases h with ⟨hy, hd⟩ | ⟨hy, hu⟩ | ⟨hy, hr⟩ | ⟨hy, hl⟩
  · subst hy
    exact Or.inr (Or.inl ⟨by refine Prod.ext ?_ ?_ <;> omega, (upI_dnI x).mpr hd⟩)
  · subst hy
    exact Or.inl ⟨by refine Prod.ext ?_ ?_ <;> omega, (dnI_upI x).mpr hu⟩
  · subst hy
    exact Or.inr (Or.inr (Or.inr ⟨by refine Prod.ext ?_ ?_ <;> omega, (ltI_rtI x).mpr hr⟩))
  · subst hy
    exact Or.inr (Or.inr (Or.inl ⟨by refine Prod.ext ?_ ?_ <;> omega, (rtI_ltI x).mpr hl⟩))

/-- The interface graph. -/
def GG {N : ℕ} (blocked : Fin N × Fin N → Prop) : SimpleGraph (CC N) :=
  { Adj := fun c d => IAdjZ blocked c.1 d.1
    symm := ⟨fun c d h => IAdjZ_symm h⟩
    loopless := ⟨fun c h => IAdjZ_irrefl c.1 h⟩ }

/-! ## Computing the degree of a corner in the interface graph -/

lemma card_filter_coord {N : ℕ} (P : ℤ × ℤ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun d : CC N => P d.1)).card = ((cornerFinset N).filter P).card := by
  refine Finset.card_bij (fun d _ => d.1) ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_filter.mpr ⟨d.2, hd.2⟩
  · intro d1 h1 d2 h2 h
    exact Subtype.ext h
  · intro e he
    rw [Finset.mem_filter] at he
    exact ⟨⟨e, he.1⟩,
      by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, he.2⟩, rfl⟩

lemma card_filter_val (s : Finset (ℤ × ℤ)) (e0 : ℤ × ℤ) (P : Prop) [Decidable P] :
    (s.filter (fun e => e = e0 ∧ P)).card = if P then (if e0 ∈ s then 1 else 0) else 0 := by
  by_cases hP : P
  · rw [if_pos hP]
    have hcongr : (s.filter (fun e => e = e0 ∧ P)) = s.filter (fun e => e = e0) := by
      apply Finset.filter_congr
      intro e _
      simp [hP]
    rw [hcongr, Finset.filter_eq']
    by_cases hmem : e0 ∈ s
    · rw [if_pos hmem, if_pos hmem]; exact Finset.card_singleton e0
    · rw [if_neg hmem, if_neg hmem]; exact Finset.card_empty
  · rw [if_neg hP]
    have hcongr : (s.filter (fun e => e = e0 ∧ P)) = (s.filter (fun _ => False)) := by
      apply Finset.filter_congr
      intro e _
      exact ⟨fun h => hP h.2, fun h => h.elim⟩
    rw [hcongr]
    simp

lemma card_filter_val' (s : Finset (ℤ × ℤ)) (e0 : ℤ × ℤ) (P : Prop) [Decidable P]
    (hP : P → e0 ∈ s) :
    (s.filter (fun e => e = e0 ∧ P)).card = if P then 1 else 0 := by
  rw [card_filter_val]
  by_cases h : P
  · rw [if_pos h, if_pos h, if_pos (hP h)]
  · rw [if_neg h, if_neg h]

lemma cand_ne12 (x : ℤ × ℤ) : (x.1 + 1, x.2) ≠ (x.1 - 1, x.2) := by
  intro h; have := congrArg Prod.fst h; omega
lemma cand_ne13 (x : ℤ × ℤ) : (x.1 + 1, x.2) ≠ (x.1, x.2 + 1) := by
  intro h; have := congrArg Prod.fst h; omega
lemma cand_ne14 (x : ℤ × ℤ) : (x.1 + 1, x.2) ≠ (x.1, x.2 - 1) := by
  intro h; have := congrArg Prod.fst h; omega
lemma cand_ne23 (x : ℤ × ℤ) : (x.1 - 1, x.2) ≠ (x.1, x.2 + 1) := by
  intro h; have := congrArg Prod.fst h; omega
lemma cand_ne24 (x : ℤ × ℤ) : (x.1 - 1, x.2) ≠ (x.1, x.2 - 1) := by
  intro h; have := congrArg Prod.fst h; omega
lemma cand_ne34 (x : ℤ × ℤ) : (x.1, x.2 + 1) ≠ (x.1, x.2 - 1) := by
  intro h; have := congrArg Prod.snd h; omega

lemma disj_pair (s : Finset (ℤ × ℤ)) {e1 e2 : ℤ × ℤ} (h : e1 ≠ e2) (P Q : Prop) :
    Disjoint (s.filter (fun e => e = e1 ∧ P)) (s.filter (fun e => e = e2 ∧ Q)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  rw [Finset.mem_filter] at he1 he2
  exact h (he1.2.1.symm.trans he2.2.1)

/-- The degree of a corner equals the number of incident interface edges. -/
lemma degree_eq {N : ℕ} (blocked : Fin N × Fin N → Prop) (c : CC N) :
    (GG blocked).degree c =
      (if dnI blocked c.1 then 1 else 0) + (if upI blocked c.1 then 1 else 0) +
      (if rtI blocked c.1 then 1 else 0) + (if ltI blocked c.1 then 1 else 0) := by
  classical
  set x := c.1 with hx
  set s := cornerFinset N with hs
  have hnf : (GG blocked).neighborFinset c
      = Finset.univ.filter (fun d : CC N => IAdjZ blocked x d.1) := by
    ext d
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [SimpleGraph.degree, hnf]
  rw [card_filter_coord (fun e => IAdjZ blocked x e), ← hs]
  have hsplit : s.filter (fun e => IAdjZ blocked x e)
      = (s.filter (fun e => e = (x.1 + 1, x.2) ∧ dnI blocked x))
        ∪ ((s.filter (fun e => e = (x.1 - 1, x.2) ∧ upI blocked x))
          ∪ ((s.filter (fun e => e = (x.1, x.2 + 1) ∧ rtI blocked x))
            ∪ (s.filter (fun e => e = (x.1, x.2 - 1) ∧ ltI blocked x)))) := by
    rw [show IAdjZ blocked x = (fun e => (e = (x.1 + 1, x.2) ∧ dnI blocked x) ∨
        ((e = (x.1 - 1, x.2) ∧ upI blocked x) ∨
         ((e = (x.1, x.2 + 1) ∧ rtI blocked x) ∨ (e = (x.1, x.2 - 1) ∧ ltI blocked x)))) from rfl]
    simp only [Finset.filter_or]
  have hAB := disj_pair s (cand_ne12 x) (dnI blocked x) (upI blocked x)
  have hAC := disj_pair s (cand_ne13 x) (dnI blocked x) (rtI blocked x)
  have hAD := disj_pair s (cand_ne14 x) (dnI blocked x) (ltI blocked x)
  have hBC := disj_pair s (cand_ne23 x) (upI blocked x) (rtI blocked x)
  have hBD := disj_pair s (cand_ne24 x) (upI blocked x) (ltI blocked x)
  have hCD := disj_pair s (cand_ne34 x) (rtI blocked x) (ltI blocked x)
  have hU2 : Disjoint (s.filter (fun e => e = (x.1 - 1, x.2) ∧ upI blocked x))
      ((s.filter (fun e => e = (x.1, x.2 + 1) ∧ rtI blocked x))
        ∪ (s.filter (fun e => e = (x.1, x.2 - 1) ∧ ltI blocked x))) :=
    Finset.disjoint_union_right.mpr ⟨hBC, hBD⟩
  have hU1 : Disjoint (s.filter (fun e => e = (x.1 + 1, x.2) ∧ dnI blocked x))
      ((s.filter (fun e => e = (x.1 - 1, x.2) ∧ upI blocked x))
        ∪ ((s.filter (fun e => e = (x.1, x.2 + 1) ∧ rtI blocked x))
          ∪ (s.filter (fun e => e = (x.1, x.2 - 1) ∧ ltI blocked x)))) :=
    Finset.disjoint_union_right.mpr ⟨hAB, Finset.disjoint_union_right.mpr ⟨hAC, hAD⟩⟩
  rw [hsplit, Finset.card_union_of_disjoint hU1, Finset.card_union_of_disjoint hU2,
    Finset.card_union_of_disjoint hCD]
  rw [card_filter_val' s (x.1 + 1, x.2) (dnI blocked x) (dnI_mem (blocked := blocked)),
      card_filter_val' s (x.1 - 1, x.2) (upI blocked x) (upI_mem (blocked := blocked)),
      card_filter_val' s (x.1, x.2 + 1) (rtI blocked x) (rtI_mem (blocked := blocked)),
      card_filter_val' s (x.1, x.2 - 1) (ltI blocked x) (ltI_mem (blocked := blocked))]
  ac_rfl

/-! ## Parities of degrees -/

lemma even_xor_cycle (A B C D : Prop) [Decidable A] [Decidable B] [Decidable C] [Decidable D] :
    Even ((if Xor A B then 1 else 0) + (if Xor B C then 1 else 0) +
          (if Xor C D then 1 else 0) + (if Xor D A then 1 else 0)) := by
  by_cases ha : A <;> by_cases hb : B <;> by_cases hc : C <;> by_cases hd : D <;>
    simp only [Xor, ha, hb, hc, hd, and_false, not_true, not_false_eq_true,
      true_and, false_and, if_true, if_false, true_or, false_or] <;> decide

lemma Rp_col0_iff {N : ℕ} (blocked : Fin N × Fin N → Prop) (a : ℤ) :
    Rp blocked (a, 0) ↔ isE N (a, 0) := by
  rw [Rp]; constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, Or.inl rfl⟩

lemma Rp_eq_of_snd_zero {N : ℕ} (blocked : Fin N × Fin N → Prop) {a b : ℤ} (h : b = 0) :
    Rp blocked (a, b) ↔ isE N (a, b) := by
  subst h; exact Rp_col0_iff blocked a

lemma Rp_colN_false {N : ℕ} (hN : 0 < N) {blocked : Fin N × Fin N → Prop}
    (hnoLR : ¬ LRopen blocked) (a : ℤ) : ¬ Rp blocked (a, (N:ℤ)) := by
  rintro ⟨-, h | h⟩
  · omega
  · exact hnoLR (LRopen_of_InR hN h rfl)

lemma Rp_false_of_snd_N {N : ℕ} (hN : 0 < N) {blocked : Fin N × Fin N → Prop}
    (hnoLR : ¬ LRopen blocked) {a b : ℤ} (h : b = (N:ℤ)) : ¬ Rp blocked (a, b) := by
  subst h; exact Rp_colN_false hN hnoLR a

lemma degree_left {N : ℕ} (blocked : Fin N × Fin N → Prop) {c : CC N} (h : c.1.2 = 0) :
    (GG blocked).degree c = 0 := by
  rw [degree_eq]
  have hup : ¬ upI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2 - 1) := hh.1
    simp only [isE] at hE; omega
  have hdn : ¬ dnI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1, c.1.2 - 1) := hh.1
    simp only [isE] at hE; omega
  have hlt : ¬ ltI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2 - 1) := hh.1
    simp only [isE] at hE; omega
  have hrt : ¬ rtI blocked c.1 := by
    intro hh
    have hq : Rp blocked (c.1.1 - 1, c.1.2) := (Rp_eq_of_snd_zero blocked h).mpr hh.1
    have hq2 : Rp blocked (c.1.1, c.1.2) := (Rp_eq_of_snd_zero blocked h).mpr hh.2.1
    rcases hh.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 hq2
    · exact h2 hq
  simp [hup, hdn, hlt, hrt]

lemma degree_right {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hnoLR : ¬ LRopen blocked) {c : CC N} (h : c.1.2 = (N:ℤ) + 1) :
    (GG blocked).degree c = 0 := by
  rw [degree_eq]
  have hup : ¬ upI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2) := hh.2.1
    simp only [isE] at hE; omega
  have hdn : ¬ dnI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1, c.1.2) := hh.2.1
    simp only [isE] at hE; omega
  have hrt : ¬ rtI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2) := hh.1
    simp only [isE] at hE; omega
  have hlt : ¬ ltI blocked c.1 := by
    intro hh
    have hq : ¬ Rp blocked (c.1.1 - 1, c.1.2 - 1) :=
      Rp_false_of_snd_N hN hnoLR (by omega)
    have hq2 : ¬ Rp blocked (c.1.1, c.1.2 - 1) :=
      Rp_false_of_snd_N hN hnoLR (by omega)
    rcases hh.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hq h1
    · exact hq2 h1
  simp [hup, hdn, hrt, hlt]

lemma degree_top {N : ℕ} (blocked : Fin N × Fin N → Prop) {c : CC N} (h : c.1.1 = 0) :
    (GG blocked).degree c = (if dnI blocked c.1 then 1 else 0) := by
  rw [degree_eq]
  have h1 : ¬ upI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2) := hh.2.1
    simp only [isE] at hE; omega
  have h2 : ¬ rtI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2) := hh.1
    simp only [isE] at hE; omega
  have h3 : ¬ ltI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1 - 1, c.1.2 - 1) := hh.1
    simp only [isE] at hE; omega
  simp [h1, h2, h3]

lemma degree_bottom {N : ℕ} (blocked : Fin N × Fin N → Prop) {c : CC N}
    (h : c.1.1 = (N:ℤ)) :
    (GG blocked).degree c = (if upI blocked c.1 then 1 else 0) := by
  rw [degree_eq]
  have h1 : ¬ dnI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1, c.1.2) := hh.2.1
    simp only [isE] at hE; omega
  have h2 : ¬ rtI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1, c.1.2) := hh.2.1
    simp only [isE] at hE; omega
  have h3 : ¬ ltI blocked c.1 := by
    intro hh; have hE : isE N (c.1.1, c.1.2 - 1) := hh.2.1
    simp only [isE] at hE; omega
  simp [h1, h2, h3]

/-- Every corner that is neither on the top row nor on the bottom row has even degree. -/
lemma degree_even_of_notTopBot {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hnoLR : ¬ LRopen blocked) {c : CC N}
    (h0 : c.1.1 ≠ 0) (hNn : c.1.1 ≠ (N:ℤ)) : Even ((GG blocked).degree c) := by
  have hmem : 0 ≤ c.1.1 ∧ c.1.1 ≤ (N:ℤ) ∧ 0 ≤ c.1.2 ∧ c.1.2 ≤ (N:ℤ) + 1 := by
    have := c.2; rwa [mem_cornerFinset] at this
  by_cases hj0 : c.1.2 = 0
  · rw [degree_left blocked hj0]; decide
  · by_cases hjN : c.1.2 = (N:ℤ) + 1
    · rw [degree_right hN blocked hnoLR hjN]; decide
    · have hJ : 1 ≤ c.1.2 ∧ c.1.2 ≤ (N:ℤ) := by omega
      have hI : 1 ≤ c.1.1 ∧ c.1.1 ≤ (N:ℤ) - 1 := by omega
      have eA : isE N (c.1.1 - 1, c.1.2 - 1) := by
        simp only [isE]; exact ⟨by omega, by omega, by omega, by omega⟩
      have eB : isE N (c.1.1 - 1, c.1.2) := by
        simp only [isE]; exact ⟨by omega, by omega, by omega, by omega⟩
      have eC : isE N (c.1.1, c.1.2) := by
        simp only [isE]; exact ⟨by omega, by omega, by omega, by omega⟩
      have eD : isE N (c.1.1, c.1.2 - 1) := by
        simp only [isE]; exact ⟨by omega, by omega, by omega, by omega⟩
      rw [degree_eq]
      have hup : upI blocked c.1 ↔
          Xor (Rp blocked (c.1.1 - 1, c.1.2 - 1)) (Rp blocked (c.1.1 - 1, c.1.2)) := by
        simp [upI, eA, eB]
      have hdn : dnI blocked c.1 ↔
          Xor (Rp blocked (c.1.1, c.1.2 - 1)) (Rp blocked (c.1.1, c.1.2)) := by
        simp [dnI, eD, eC]
      have hrt : rtI blocked c.1 ↔
          Xor (Rp blocked (c.1.1 - 1, c.1.2)) (Rp blocked (c.1.1, c.1.2)) := by
        simp [rtI, eB, eC]
      have hlt : ltI blocked c.1 ↔
          Xor (Rp blocked (c.1.1 - 1, c.1.2 - 1)) (Rp blocked (c.1.1, c.1.2 - 1)) := by
        simp [ltI, eA, eD]
      rw [hup, hdn, hrt, hlt]
      by_cases hA : Rp blocked (c.1.1 - 1, c.1.2 - 1)
        <;> by_cases hB : Rp blocked (c.1.1 - 1, c.1.2)
        <;> by_cases hC : Rp blocked (c.1.1, c.1.2)
        <;> by_cases hD : Rp blocked (c.1.1, c.1.2 - 1)
        <;> simp only [Xor, hA, hB, hC, hD, and_false, not_true, not_false_eq_true,
              true_and, false_and, if_true, if_false, true_or, false_or] <;> decide

/-! ## Parity of the number of transitions along a `Bool`-like sequence -/

lemma not_xor_iff (p q : Prop) : ¬ Xor p q ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [Xor, hp, hq]

lemma even_if_xor (p q : Prop) [Decidable p] [Decidable q] :
    Even (if Xor p q then 1 else 0) ↔ (p ↔ q) := by
  by_cases h : Xor p q
  · rw [if_pos h]
    have hne : ¬(p ↔ q) := fun hiff => ((not_xor_iff p q).mpr hiff) h
    exact ⟨fun he => absurd he (by decide), fun hiff => (hne hiff).elim⟩
  · rw [if_neg h]
    have heq : (p ↔ q) := (not_xor_iff p q).mp h
    exact ⟨fun _ => heq, fun _ => by decide⟩

lemma even_transitions_sum (b : ℕ → Prop) [DecidablePred b] (n : ℕ) :
    Even (∑ j ∈ Finset.Icc 1 n, (if Xor (b (j-1)) (b j) then 1 else 0)) ↔ (b 0 ↔ b n) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega)]
      rw [Nat.even_add, ih, even_if_xor]
      by_cases h0 : b 0 <;> by_cases hk : b k <;> by_cases h1 : b (k+1) <;> simp_all

lemma even_transitions (b : ℕ → Prop) [DecidablePred b] (n : ℕ) :
    Even ((Finset.Icc 1 n).filter (fun j => Xor (b (j-1)) (b j))).card ↔ (b 0 ↔ b n) := by
  rw [Finset.card_filter]
  exact even_transitions_sum b n

lemma odd_transitions (b : ℕ → Prop) [DecidablePred b] (n : ℕ) (h0 : b 0) (hn : ¬ b n) :
    Odd ((Finset.Icc 1 n).filter (fun j => Xor (b (j-1)) (b j))).card := by
  rw [← Nat.not_even_iff_odd]
  intro hev
  exact hn (((even_transitions b n).mp hev).mp h0)

lemma toNat_sub_one (j : ℕ) (hj : 1 ≤ j) : ((j - 1 : ℕ) : ℤ) = (j:ℤ) - 1 := by omega

/-- The number of top corners of odd degree is odd. -/
lemma odd_topCount {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hnoLR : ¬ LRopen blocked) :
    Odd ((Finset.univ.filter (fun c : CC N => c.1.1 = 0 ∧ Odd ((GG blocked).degree c))).card) := by
  have hfilter : (Finset.univ.filter (fun c : CC N => c.1.1 = 0 ∧ Odd ((GG blocked).degree c)))
      = (Finset.univ.filter (fun c : CC N => c.1.1 = 0 ∧ dnI blocked c.1)) := by
    apply Finset.filter_congr
    intro c _
    by_cases h : c.1.1 = 0
    · rw [degree_top blocked h]
      constructor
      · rintro ⟨-, ho⟩
        refine ⟨h, ?_⟩
        by_contra hd
        rw [if_neg hd] at ho; exact absurd ho (by decide)
      · rintro ⟨-, hd⟩
        exact ⟨h, by rw [if_pos hd]; decide⟩
    · constructor <;> rintro ⟨hc, -⟩ <;> exact absurd hc h
  rw [hfilter]
  have hbij : ((Finset.univ.filter (fun c : CC N => c.1.1 = 0 ∧ dnI blocked c.1)).card)
      = ((Finset.Icc 1 N).filter (fun j : ℕ =>
          Xor (Rp blocked (0, (j:ℤ) - 1)) (Rp blocked (0, (j:ℤ))))).card := by
    apply Finset.card_bij (fun c _ => (c.1.2).toNat)
    · intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hc1, hc2⟩ := hc
      rw [Finset.mem_filter]
      simp only [dnI, isE] at hc2
      obtain ⟨hA, hB, hxo⟩ := hc2
      rw [hc1] at hxo
      refine ⟨by rw [Finset.mem_Icc]; omega, ?_⟩
      have eb : 0 ≤ c.1.2 := by omega
      have e1 : ((c.1.2).toNat : ℤ) = c.1.2 := Int.toNat_of_nonneg eb
      rw [e1]
      exact hxo
    · intro c1 h1 c2 h2 h
      refine Subtype.ext (Prod.ext ?_ ?_)
      · rw [(Finset.mem_filter.mp h1).2.1, (Finset.mem_filter.mp h2).2.1]
      · have hb1 : 0 ≤ c1.1.2 := by
          have := c1.2; rw [mem_cornerFinset] at this; exact this.2.2.1
        have hb2 : 0 ≤ c2.1.2 := by
          have := c2.2; rw [mem_cornerFinset] at this; exact this.2.2.1
        have hh : ((c1.1.2).toNat : ℤ) = ((c2.1.2).toNat : ℤ) := by rw [h]
        rwa [Int.toNat_of_nonneg hb1, Int.toNat_of_nonneg hb2] at hh
    · intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hj1, hj2⟩ := hj
      rw [Finset.mem_Icc] at hj1
      refine ⟨⟨(0, (j:ℤ)), by rw [mem_cornerFinset]; omega⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩
        simp only [dnI, isE]
        exact ⟨⟨le_refl 0, by exact_mod_cast hN, by omega, by omega⟩,
               ⟨le_refl 0, by exact_mod_cast hN, by omega, by omega⟩, hj2⟩
      · show ((j:ℤ)).toNat = j
        exact Int.toNat_natCast j
  rw [hbij]
  have hp0 : (fun j : ℕ => Rp blocked (0, (j:ℤ))) 0 := by
    change Rp blocked (0, (0:ℤ))
    rw [Rp_col0_iff]; simp only [isE]
    exact ⟨le_refl 0, by exact_mod_cast hN, le_refl 0, by omega⟩
  have hpN : ¬ (fun j : ℕ => Rp blocked (0, (j:ℤ))) N := Rp_colN_false hN hnoLR 0
  have hcnt := odd_transitions (fun j : ℕ => Rp blocked (0, (j:ℤ))) N hp0 hpN
  have heq : (Finset.Icc 1 N).filter (fun j : ℕ =>
        Xor (Rp blocked (0, (j:ℤ) - 1)) (Rp blocked (0, (j:ℤ))))
      = (Finset.Icc 1 N).filter (fun j : ℕ =>
        Xor (Rp blocked (0, ((j-1:ℕ):ℤ))) (Rp blocked (0, (j:ℤ)))) := by
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [toNat_sub_one j hj.1]
  rw [heq]
  exact hcnt


/-! ## Existence of a top-to-bottom path in the interface graph -/

lemma exists_topbot {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hnoLR : ¬ LRopen blocked) :
    ∃ t b : CC N, t.1.1 = 0 ∧ b.1.1 = (N:ℤ) ∧ (GG blocked).Reachable t b := by
  classical
  exact reachableOfOddDeg (GG blocked) (fun c => c.1.1 = 0) (fun c => c.1.1 = (N:ℤ))
    (fun c h0 hNn => degree_even_of_notTopBot hN blocked hnoLR h0 hNn)
    (odd_topCount hN blocked hnoLR)


/-! ## Turning a path in the interface graph into a blocked crossing -/

def IsCornerOf (c p : ℤ × ℤ) : Prop :=
  (p.1 = c.1 - 1 ∨ p.1 = c.1) ∧ (p.2 = c.2 - 1 ∨ p.2 = c.2)

lemma adj8_of_common_corner {c a b : ℤ × ℤ} (ha : IsCornerOf c a) (hb : IsCornerOf c b) :
    adj8 a b := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  simp only [adj8]
  refine ⟨?_, ?_⟩ <;> omega

/-- The blocked (non-`Rp`) cell of an interface edge. -/
noncomputable def ycellZ {N : ℕ} (blocked : Fin N × Fin N → Prop) (x y : ℤ × ℤ) : ℤ × ℤ :=
  if y = (x.1 + 1, x.2) then (if Rp blocked (x.1, x.2 - 1) then (x.1, x.2) else (x.1, x.2 - 1))
  else if y = (x.1 - 1, x.2) then
    (if Rp blocked (x.1 - 1, x.2 - 1) then (x.1 - 1, x.2) else (x.1 - 1, x.2 - 1))
  else if y = (x.1, x.2 + 1) then (if Rp blocked (x.1 - 1, x.2) then (x.1, x.2) else (x.1 - 1, x.2))
  else (if Rp blocked (x.1 - 1, x.2 - 1) then (x.1, x.2 - 1) else (x.1 - 1, x.2 - 1))

lemma adj4_orig {A B : ℤ × ℤ} (h : adj4 A B) : adj4 (A.1, A.2 - 1) (B.1, B.2 - 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by rcases h2 with h2 | h2 <;> [left; right] <;> omega⟩
  · right; exact ⟨by omega, by rcases h2 with h2 | h2 <;> [left; right] <;> omega⟩

lemma one_le_snd_of_notRp {N : ℕ} {blocked : Fin N × Fin N → Prop} {p : ℤ × ℤ}
    (hp : isE N p) (h : ¬ Rp blocked p) : 1 ≤ p.2 := by
  by_contra hc
  have h0 : p.2 = 0 := by
    simp only [isE] at hp; omega
  exact h ⟨hp, Or.inl h0⟩

lemma isO_orig {N : ℕ} {p : ℤ × ℤ} (hp : isE N p) (h : 1 ≤ p.2) : isO N (p.1, p.2 - 1) := by
  simp only [isE] at hp
  simp only [isO]
  exact ⟨hp.1, hp.2.1, by omega, by omega⟩

lemma pair_ne' {a b c d : ℤ} (h : a ≠ b ∨ c ≠ d) : (a, c) ≠ (b, d) := by
  intro hh
  rcases h with h | h
  · exact h (congrArg Prod.fst hh)
  · exact h (congrArg Prod.snd hh)

lemma blocked_of_Rp_adj {N : ℕ} {blocked : Fin N × Fin N → Prop} {A B : ℤ × ℤ}
    (hB : isE N B) (hARp : Rp blocked A) (hBRp : ¬ Rp blocked B)
    (hB1 : 1 ≤ B.2) (hadj : adj4 A B) : bk blocked (B.1, B.2 - 1) := by
  have hbO : isO N (B.1, B.2 - 1) := by
    simp only [isE] at hB
    simp only [isO]
    exact ⟨hB.1, hB.2.1, by omega, by omega⟩
  by_contra hbk
  have hbUnb : Unb blocked (B.1, B.2 - 1) := ⟨hbO, hbk⟩
  have hbnotR : ¬ InR blocked (B.1, B.2 - 1) := fun hh => hBRp ⟨hB, Or.inr hh⟩
  rcases hARp with ⟨hAe, hA0 | hAI⟩
  · rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
    · have hb0 : B.2 - 1 = 0 := by omega
      exact hbnotR ⟨hbUnb, (B.1, B.2 - 1), hb0, hbUnb, Relation.ReflTransGen.refl⟩
    · omega
    · omega
  · exact hbnotR (InR_extension hAI (adj4_orig hadj) hbUnb)

lemma ycellZ_spec {N : ℕ} {blocked : Fin N × Fin N → Prop} {x y : ℤ × ℤ}
    (h : IAdjZ blocked x y) :
    IsCornerOf x (ycellZ blocked x y) ∧ IsCornerOf y (ycellZ blocked x y) ∧
    isO N ((ycellZ blocked x y).1, (ycellZ blocked x y).2 - 1) ∧
    bk blocked ((ycellZ blocked x y).1, (ycellZ blocked x y).2 - 1) := by
  rcases h with ⟨hy, hd⟩ | ⟨hy, hu⟩ | ⟨hy, hr⟩ | ⟨hy, hl⟩
  · subst hy
    simp only [dnI, isE] at hd
    obtain ⟨⟨h1a,h1b,h1c,h1d⟩, ⟨h2a,h2b,h2c,h2d⟩, hdX⟩ := hd
    unfold ycellZ
    rw [if_pos rfl]
    by_cases hR : Rp blocked (x.1, x.2 - 1)
    · rw [if_pos hR]
      have hq : ¬ Rp blocked (x.1, x.2) := hdX.elim (fun hh => hh.2) (fun hh => (hh.2 hR).elim)
      refine ⟨⟨Or.inr rfl, Or.inr rfl⟩, ⟨Or.inl (by omega), Or.inr rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h2a,h2b,h2c,h2d⟩ (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
      · exact blocked_of_Rp_adj ⟨h2a,h2b,h2c,h2d⟩ hR hq
          (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
          (Or.inl ⟨rfl, Or.inl (by omega)⟩)
    · rw [if_neg hR]
      have hq : Rp blocked (x.1, x.2) := hdX.elim (fun hh => (hR hh.1).elim) (fun hh => hh.1)
      refine ⟨⟨Or.inr rfl, Or.inl rfl⟩, ⟨Or.inl (by omega), Or.inl rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h1a,h1b,h1c,h1d⟩ (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
      · exact blocked_of_Rp_adj ⟨h1a,h1b,h1c,h1d⟩ hq hR
          (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
          (Or.inl ⟨rfl, Or.inr (by omega)⟩)
  · subst hy
    simp only [upI, isE] at hu
    obtain ⟨⟨h1a,h1b,h1c,h1d⟩, ⟨h2a,h2b,h2c,h2d⟩, huX⟩ := hu
    unfold ycellZ
    rw [if_neg (pair_ne' (Or.inl (by omega : x.1 - 1 ≠ x.1 + 1))), if_pos rfl]
    by_cases hR : Rp blocked (x.1 - 1, x.2 - 1)
    · rw [if_pos hR]
      have hq : ¬ Rp blocked (x.1 - 1, x.2) := huX.elim (fun hh => hh.2) (fun hh => (hh.2 hR).elim)
      refine ⟨⟨Or.inl rfl, Or.inr rfl⟩, ⟨Or.inr rfl, Or.inr rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h2a,h2b,h2c,h2d⟩ (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
      · exact blocked_of_Rp_adj ⟨h2a,h2b,h2c,h2d⟩ hR hq
          (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
          (Or.inl ⟨rfl, Or.inl (by omega)⟩)
    · rw [if_neg hR]
      have hq : Rp blocked (x.1 - 1, x.2) := huX.elim (fun hh => (hR hh.1).elim) (fun hh => hh.1)
      refine ⟨⟨Or.inl rfl, Or.inl rfl⟩, ⟨Or.inr rfl, Or.inl rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h1a,h1b,h1c,h1d⟩ (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
      · exact blocked_of_Rp_adj ⟨h1a,h1b,h1c,h1d⟩ hq hR
          (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
          (Or.inl ⟨rfl, Or.inr (by omega)⟩)
  · subst hy
    simp only [rtI, isE] at hr
    obtain ⟨⟨h1a,h1b,h1c,h1d⟩, ⟨h2a,h2b,h2c,h2d⟩, hrX⟩ := hr
    unfold ycellZ
    rw [if_neg (pair_ne' (Or.inl (by omega : x.1 ≠ x.1 + 1))),
        if_neg (pair_ne' (Or.inl (by omega : x.1 ≠ x.1 - 1))), if_pos rfl]
    by_cases hR : Rp blocked (x.1 - 1, x.2)
    · rw [if_pos hR]
      have hq : ¬ Rp blocked (x.1, x.2) := hrX.elim (fun hh => hh.2) (fun hh => (hh.2 hR).elim)
      refine ⟨⟨Or.inr rfl, Or.inr rfl⟩, ⟨Or.inr rfl, Or.inl (by omega)⟩, ?_, ?_⟩
      · exact isO_orig ⟨h2a,h2b,h2c,h2d⟩ (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
      · exact blocked_of_Rp_adj ⟨h2a,h2b,h2c,h2d⟩ hR hq
          (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
          (Or.inr ⟨rfl, Or.inl (by omega)⟩)
    · rw [if_neg hR]
      have hq : Rp blocked (x.1, x.2) := hrX.elim (fun hh => (hR hh.1).elim) (fun hh => hh.1)
      refine ⟨⟨Or.inl rfl, Or.inr rfl⟩, ⟨Or.inl rfl, Or.inl (by omega)⟩, ?_, ?_⟩
      · exact isO_orig ⟨h1a,h1b,h1c,h1d⟩ (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
      · exact blocked_of_Rp_adj ⟨h1a,h1b,h1c,h1d⟩ hq hR
          (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
          (Or.inr ⟨rfl, Or.inr (by omega)⟩)
  · subst hy
    simp only [ltI, isE] at hl
    obtain ⟨⟨h1a,h1b,h1c,h1d⟩, ⟨h2a,h2b,h2c,h2d⟩, hlX⟩ := hl
    unfold ycellZ
    rw [if_neg (pair_ne' (Or.inl (by omega : x.1 ≠ x.1 + 1))),
        if_neg (pair_ne' (Or.inl (by omega : x.1 ≠ x.1 - 1))),
        if_neg (pair_ne' (Or.inr (by omega : x.2 - 1 ≠ x.2 + 1)))]
    by_cases hR : Rp blocked (x.1 - 1, x.2 - 1)
    · rw [if_pos hR]
      have hq : ¬ Rp blocked (x.1, x.2 - 1) := hlX.elim (fun hh => hh.2) (fun hh => (hh.2 hR).elim)
      refine ⟨⟨Or.inr rfl, Or.inl rfl⟩, ⟨Or.inr rfl, Or.inr rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h2a,h2b,h2c,h2d⟩ (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
      · exact blocked_of_Rp_adj ⟨h2a,h2b,h2c,h2d⟩ hR hq
          (one_le_snd_of_notRp ⟨h2a,h2b,h2c,h2d⟩ hq)
          (Or.inr ⟨rfl, Or.inl (by omega)⟩)
    · rw [if_neg hR]
      have hq : Rp blocked (x.1, x.2 - 1) := hlX.elim (fun hh => (hR hh.1).elim) (fun hh => hh.1)
      refine ⟨⟨Or.inl rfl, Or.inl rfl⟩, ⟨Or.inl rfl, Or.inr rfl⟩, ?_, ?_⟩
      · exact isO_orig ⟨h1a,h1b,h1c,h1d⟩ (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
      · exact blocked_of_Rp_adj ⟨h1a,h1b,h1c,h1d⟩ hq hR
          (one_le_snd_of_notRp ⟨h1a,h1b,h1c,h1d⟩ hR)
          (Or.inr ⟨rfl, Or.inr (by omega)⟩)

lemma adj8_orig {a b : ℤ × ℤ} (h : adj8 a b) : adj8 (a.1, a.2 - 1) (b.1, b.2 - 1) := by
  obtain ⟨h1, h2⟩ := h
  simp only [adj8]
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rcases h2 with h2 | h2 | h2
    · left; omega
    · right; left; omega
    · right; right; omega

lemma Int_toNat_sub_one (N : ℕ) (hN : 0 < N) : (((N:ℤ) - 1).toNat : ℤ) = (N:ℤ) - 1 :=
  Int.toNat_of_nonneg (by omega)

lemma TBblocked_of_noLR {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop)
    (hnoLR : ¬ LRopen blocked) : TBblocked blocked := by
  classical
  obtain ⟨t, b, ht, hb, hreach⟩ := exists_topbot hN blocked hnoLR
  have hw : Relation.ReflTransGen (GG blocked).Adj t b :=
    (SimpleGraph.reachable_iff_reflTransGen t b).mp hreach
  obtain ⟨L, v, hv0, hvL, hvstep⟩ := reflTransGen_to_path (GG blocked).Adj hw
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · exfalso
      have hlast : Fin.last L = 0 := by rw [h]; rfl
      rw [hlast] at hvL
      have htb : t = b := hv0.symm.trans hvL
      have h0N : (0:ℤ) = (N:ℤ) := by rw [← ht, htb, hb]
      omega
    · exact h
  have hspec : ∀ i : Fin L, IsCornerOf (v i.castSucc).1 (ycellZ blocked (v i.castSucc).1 (v i.succ).1) ∧
      IsCornerOf (v i.succ).1 (ycellZ blocked (v i.castSucc).1 (v i.succ).1) ∧
      isO N ((ycellZ blocked (v i.castSucc).1 (v i.succ).1).1,
        (ycellZ blocked (v i.castSucc).1 (v i.succ).1).2 - 1) ∧
      bk blocked ((ycellZ blocked (v i.castSucc).1 (v i.succ).1).1,
        (ycellZ blocked (v i.castSucc).1 (v i.succ).1).2 - 1) :=
    fun i => ycellZ_spec (hvstep i)
  let Yz : Fin L → ℤ × ℤ := fun i => ycellZ blocked (v i.castSucc).1 (v i.succ).1
  have hYc : ∀ i, IsCornerOf (v i.castSucc).1 (Yz i) ∧ IsCornerOf (v i.succ).1 (Yz i) :=
    fun i => ⟨(hspec i).1, (hspec i).2.1⟩
  have hYo : ∀ i, isO N ((Yz i).1, (Yz i).2 - 1) := fun i => (hspec i).2.2.1
  have hYb : ∀ i, bk blocked ((Yz i).1, (Yz i).2 - 1) := fun i => (hspec i).2.2.2
  let Yf : Fin L → Fin N × Fin N := fun i => toFin ((Yz i).1, (Yz i).2 - 1) (hYo i)
  have hYbl : ∀ i, blocked (Yf i) := by
    intro i
    obtain ⟨h, hh⟩ := hYb i
    rw [Subsingleton.elim h (hYo i)] at hh
    exact hh
  have hrow : ∀ i : Fin L, (Yz i).1 = 0 → (Yf i).1.1 = 0 := by
    intro i hi
    have : (Yf i).1.1 = ((Yz i).1).toNat := rfl
    rw [this, hi]; rfl
  have hrowN : ∀ i : Fin L, (Yz i).1 = (N:ℤ) - 1 → (Yf i).1.1 + 1 = N := by
    intro i hi
    have h1 : (Yf i).1.1 = ((Yz i).1).toNat := rfl
    have h2 : ((Yz i).1).toNat + 1 = N := by
      rw [hi]
      have h3 : (((N:ℤ) - 1).toNat : ℤ) = (N:ℤ) - 1 := Int_toNat_sub_one N hN
      omega
    rw [h1]; exact h2
  let g : Fin (L+1) → Fin N × Fin N :=
    fun i => if h : i.val < L then Yf ⟨i.val, h⟩ else Yf ⟨L-1, by omega⟩
  refine ⟨L, g, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [g]
    split
    · exact hYbl _
    · exact hYbl _
  · intro i
    rcases Nat.lt_or_ge i.val (L-1) with hi | hi
    · have hia : (i.succ).val < L := by
        have h : (i.succ).val = i.val + 1 := rfl
        omega
      have hga : g i.castSucc = Yf ⟨i.val, i.isLt⟩ := by
        simp only [g]
        rw [dif_pos (show (i.castSucc).val < L from i.isLt)]
        exact congrArg Yf (Fin.ext rfl)
      have hgb : g i.succ = Yf ⟨i.val + 1, hia⟩ := by
        simp only [g]
        rw [dif_pos hia]
        exact congrArg Yf (Fin.ext rfl)
      have hA : IsCornerOf (v (⟨i.val + 1, hia⟩ : Fin L).castSucc).1 (Yz ⟨i.val, i.isLt⟩) := by
        have h := (hYc ⟨i.val, i.isLt⟩).2
        have he : (⟨i.val, i.isLt⟩ : Fin L).succ = (⟨i.val + 1, hia⟩ : Fin L).castSucc :=
          Fin.ext rfl
        rw [he] at h
        exact h
      have hB : IsCornerOf (v (⟨i.val + 1, hia⟩ : Fin L).castSucc).1 (Yz ⟨i.val + 1, hia⟩) :=
        (hYc ⟨i.val + 1, hia⟩).1
      rw [hga, hgb]
      exact toFin_adj8 (hYo _) (hYo _) (adj8_orig (adj8_of_common_corner hA hB))
    · have hiv : i.val = L - 1 := by omega
      have hca : (i.castSucc).val < L := by
        have h : (i.castSucc).val = i.val := rfl
        omega
      have hsa : ¬ ((i.succ).val < L) := by
        have h : (i.succ).val = i.val + 1 := rfl
        omega
      have hga : g i.castSucc = Yf ⟨L-1, by omega⟩ := by
        simp only [g]
        rw [dif_pos hca]
        exact congrArg Yf (Fin.ext (by rw [show (i.castSucc).val = i.val from rfl]; exact hiv))
      have hgb : g i.succ = Yf ⟨L-1, by omega⟩ := by
        simp only [g]
        rw [dif_neg hsa]
        try exact congrArg Yf (Fin.ext rfl)
      rw [hga, hgb]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  · show (g 0).1.1 = 0
    have h0a : (0 : Fin (L+1)).val < L := by
      have h : (0 : Fin (L+1)).val = 0 := rfl
      omega
    have hg0 : g 0 = Yf ⟨0, hL⟩ := by
      simp only [g]
      rw [dif_pos h0a]
      exact congrArg Yf (Fin.ext rfl)
    rw [hg0]
    have hz : (Yz ⟨0, hL⟩).1 = 0 := by
      have hc := (hYc ⟨0, hL⟩).1
      have hv : (v (⟨0, hL⟩ : Fin L).castSucc).1 = t.1 := by
        rw [show (⟨0, hL⟩ : Fin L).castSucc = 0 from Fin.ext rfl, hv0]
      rw [hv] at hc
      obtain ⟨hc1, -⟩ := hc
      rw [ht] at hc1
      have ho1 := (hYo ⟨0, hL⟩).1
      omega
    exact hrow ⟨0, hL⟩ hz
  · show (g (Fin.last L)).1.1 + 1 = N
    have hLa : ¬ ((Fin.last L).val < L) := by
      have h : (Fin.last L).val = L := rfl
      omega
    have hgL : g (Fin.last L) = Yf ⟨L-1, by omega⟩ := by
      simp only [g]
      rw [dif_neg hLa]
      try exact congrArg Yf (Fin.ext rfl)
    rw [hgL]
    have hz : (Yz ⟨L-1, by omega⟩).1 = (N:ℤ) - 1 := by
      have hc := (hYc ⟨L-1, by omega⟩).2
      have hv : (v (⟨L-1, by omega⟩ : Fin L).succ).1 = b.1 := by
        rw [show (⟨L-1, by omega⟩ : Fin L).succ = Fin.last L from Fin.ext (by simp; omega), hvL]
      rw [hv] at hc
      obtain ⟨hc1, -⟩ := hc
      rw [hb] at hc1
      have ho1 := (hYo ⟨L-1, by omega⟩).1
      have ho2 := (hYo ⟨L-1, by omega⟩).2.1
      omega
    exact hrowN ⟨L-1, by omega⟩ hz

/-- **Hex duality (finite form).**  For every colouring of the `N × N` grid by "blocked"
cells, either there is an unblocked left-to-right 4-crossing, or a blocked
top-to-bottom 8-crossing. -/
theorem hexDualityFinite {N : ℕ} (hN : 0 < N) (blocked : Fin N × Fin N → Prop) :
    (∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, ¬ blocked (f i)) ∧
        (∀ i : Fin m,
          ((f i.castSucc).1 = (f i.succ).1 ∧
            ((f i.castSucc).2.1 + 1 = (f i.succ).2.1 ∨ (f i.succ).2.1 + 1 = (f i.castSucc).2.1)) ∨
          ((f i.castSucc).2 = (f i.succ).2 ∧
            ((f i.castSucc).1.1 + 1 = (f i.succ).1.1 ∨ (f i.succ).1.1 + 1 = (f i.castSucc).1.1))) ∧
        (f 0).2.1 = 0 ∧ (f (Fin.last m)).2.1 + 1 = N) ∨
      (∃ m : ℕ, ∃ f : Fin (m + 1) → Fin N × Fin N, (∀ i, blocked (f i)) ∧
        (∀ i : Fin m,
          ((f i.castSucc).1 = (f i.succ).1 ∨ (f i.castSucc).1.1 + 1 = (f i.succ).1.1 ∨ (f i.succ).1.1 + 1 = (f i.castSucc).1.1) ∧
          ((f i.castSucc).2 = (f i.succ).2 ∨ (f i.castSucc).2.1 + 1 = (f i.succ).2.1 ∨ (f i.succ).2.1 + 1 = (f i.castSucc).2.1)) ∧
        (f 0).1.1 = 0 ∧ (f (Fin.last m)).1.1 + 1 = N) := by
  show LRopen blocked ∨ TBblocked blocked
  by_cases h : LRopen blocked
  · exact Or.inl h
  · exact Or.inr (TBblocked_of_noLR hN blocked h)

end Work.Smooth.SphereJordan
