import Mathlib
import Submission.Work.PTCert.Checks.SharedAll
import Submission.Work.PTCert.modelSound
import Submission.Work.PTCert.permCheckKSound
import Submission.Work.PTCert.letterAction

/-!
# Auxiliary lemmas for the `E`-structure glue (`eSem`)

Small reusable facts turning the kernel `Bool` checks (`KernelShared.lean`) into `Prop`s:
soundness of `allL`/`allR`/`eqL`, `strictInc` implies `Nodup`, the elementary bound on `normC`,
the identity `eAll = eC0 ++ … ++ eC7`, and the extraction lemma for `eChunkOK`.
-/

set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## `Bool` check soundness -/

/-- `allL l p = true` means `p` holds on every element of `l`. -/
theorem allL_iff_eAux (l : List ℕ) (p : ℕ → Bool) : allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
    have h : allL (a :: t) p = (p a && allL t p) := rfl
    rw [h, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hp, hall⟩ b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hp
      · exact hall b hb
    · intro h
      exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

/-- `allR n p = true` means `p k` holds for every `k < n`. -/
theorem allR_iff_eAux (n : ℕ) (p : ℕ → Bool) : allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
    have h : allR (n + 1) p = (p n && allR n p) := rfl
    rw [h, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hp, hall⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact hall k hk
      · exact hp
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- `allL` is multiplicative with respect to concatenation. -/
theorem allL_append_eAux (l m : List ℕ) (p : ℕ → Bool) :
    allL (l ++ m) p = (allL l p && allL m p) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change allL (a :: (t ++ m)) p = (allL (a :: t) p && allL m p)
    have h1 : allL (a :: (t ++ m)) p = (p a && allL (t ++ m) p) := rfl
    have h2 : allL (a :: t) p = (p a && allL t p) := rfl
    rw [h1, h2, ih, Bool.and_assoc]

/-- `eqL` is list equality. -/
theorem eqL_iff_eAux : ∀ (l m : List ℕ), eqL l m = true ↔ l = m
  | [], [] => by simp [eqL]
  | [], b :: t => by simp [eqL]
  | a :: s, [] => by simp [eqL]
  | a :: s, b :: t => by
      have h : eqL (a :: s) (b :: t) = (Nat.beq a b && eqL s t) := rfl
      rw [h, Bool.and_eq_true, Nat.beq_eq, eqL_iff_eAux s t]
      constructor
      · rintro ⟨h1, h2⟩; rw [h1, h2]
      · intro h; injection h with h1 h2; exact ⟨h1, h2⟩

/-! ## `strictInc` -/

/-- The recursion body of `strictInc`, with the previous element as an argument. -/
def strictIncA (l : List ℕ) (prev : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih prev => Nat.ble prev a && ih (a + 1)) l prev

theorem strictInc_eq (l : List ℕ) : strictInc l = strictIncA l 0 := rfl

/-- `strictIncA l prev` says that `l` is strictly increasing with all elements `≥ prev`. -/
theorem strictIncA_spec : ∀ (l : List ℕ) (prev : ℕ), strictIncA l prev = true →
    (∀ x ∈ l, prev ≤ x) ∧ List.Pairwise (· < ·) l
  | [], prev, _ => ⟨by simp, by simp⟩
  | a :: t, prev, h => by
      have hh : strictIncA (a :: t) prev = (Nat.ble prev a && strictIncA t (a + 1)) := rfl
      rw [hh, Bool.and_eq_true, Nat.ble_eq] at h
      obtain ⟨hp, ht⟩ := h
      obtain ⟨hle, hpw⟩ := strictIncA_spec t (a + 1) ht
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hp
        · exact le_trans hp (le_trans (Nat.le_succ a) (hle x hx))
      · rw [List.pairwise_cons]
        exact ⟨fun x hx => lt_of_lt_of_le (Nat.lt_succ_self a) (hle x hx), hpw⟩

/-- A strictly increasing list has no repetitions. -/
theorem strictInc_nodup (l : List ℕ) (h : strictInc l = true) : l.Nodup := by
  rw [strictInc_eq] at h
  exact (strictIncA_spec l 0 h).2.nodup

/-- Strictly increasing lists have no repetitions (`Perm` form). -/
theorem nodup_of_strictInc_perm (l : List ℕ) (h : strictInc l = true) {m : List ℕ}
    (hpm : l.Perm m) : m.Nodup :=
  (List.Perm.nodup_iff hpm).mp (strictInc_nodup l h)

/-! ## The bound on `normC` -/

/-- On letters `< 81` the normal code is `< 10368 = 128 · 81`. -/
theorem normC_lt (cm : NT) (a b : ℕ) (ha : a < 81) (hb : b < 81) : normC cm a b < 10368 := by
  rw [normC]
  simp only [cond_eq_ite]
  split_ifs <;> omega

/-! ## The chunk decomposition of `eAll` -/

/-- `eAll` is the concatenation of the eight emitted chunks. -/
theorem eAll_chunks_eAux :
    eAll = eC0 ++ eC1 ++ eC2 ++ eC3 ++ eC4 ++ eC5 ++ eC6 ++ eC7 := rfl

/-- Membership in `eAll` is membership in one of the chunks. -/
theorem mem_eAll_iff (z : ℕ) :
    z ∈ eAll ↔ z ∈ eC0 ∨ z ∈ eC1 ∨ z ∈ eC2 ∨ z ∈ eC3 ∨ z ∈ eC4 ∨ z ∈ eC5 ∨ z ∈ eC6 ∨ z ∈ eC7 := by
  rw [eAll_chunks_eAux, List.mem_append, List.mem_append, List.mem_append, List.mem_append,
    List.mem_append, List.mem_append, List.mem_append]
  tauto

/-- The spec of `eChunkOK`: on every element of the chunk the code is normal and bounded. -/
theorem eChunkOK_spec (cm eM nT repT : NT) (l : List ℕ)
    (h : eChunkOK cm eM nT repT l = true) :
    ∀ z ∈ l, z < 10368 ∧ z % 128 < 81 ∧ z / 128 < 81 ∧ normC cm (z / 128) (z % 128) = z := by
  have h2 : allL l (fun z =>
      let v := eG eM z - 1
      Nat.blt z 10368 && Nat.blt (z % 128) 81 && Nat.blt (z / 128) 81 &&
        Nat.beq (normC cm (z / 128) (z % 128)) z && !(Nat.beq (eG eM z) 0) &&
        Nat.beq (actC cm (nT.get (v % 32)) (cG repT (v / 32))) z) = true := h
  intro z hz
  have h3 := (allL_iff_eAux l _).mp h2 z hz
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h3
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, _⟩, _⟩ := h3
  exact ⟨ha, hb, hc, hd⟩

end Work.PTCert
