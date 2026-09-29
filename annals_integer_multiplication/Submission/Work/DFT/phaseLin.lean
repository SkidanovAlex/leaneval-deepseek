import Mathlib
import Submission.Work.DFT.dftDefs

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-! Linearity of `myPhase`/`phase` under componentwise subtraction of digit lists,
and index bounds for `undigits`/`subDigits`/`subIdx`. -/

theorem undigits_lt : ∀ {ts xs : List ℕ}, List.Forall₂ (· < ·) xs ts → HvdH.undigits ts xs < ts.prod
  | [], [], _ => by simp [HvdH.undigits]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | t :: ts, x :: xs, h => by
      rw [List.forall₂_cons] at h
      obtain ⟨hx, htail⟩ := h
      have ih := undigits_lt htail
      have key : x * ts.prod + HvdH.undigits ts xs < t * ts.prod := by
        calc x * ts.prod + HvdH.undigits ts xs < x * ts.prod + ts.prod :=
              Nat.add_lt_add_left ih _
          _ = (x + 1) * ts.prod := (Nat.succ_mul x ts.prod).symm
          _ ≤ t * ts.prod := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hx)
      simpa [HvdH.undigits, List.prod_cons] using key

theorem subDigits_forall₂_lt : ∀ (ts js ks : List ℕ), (∀ t ∈ ts, 0 < t) →
    js.length = ts.length → ks.length = ts.length →
    List.Forall₂ (· < ·) (HvdH.subDigits ts js ks) ts := by
  intro ts
  induction ts with
  | nil =>
      intro js ks hpos h1 h2
      have hj : js = [] := List.eq_nil_of_length_eq_zero h1
      have hk : ks = [] := List.eq_nil_of_length_eq_zero h2
      subst hj; subst hk
      simp [HvdH.subDigits]
  | cons t ts ih =>
      intro js ks hpos h1 h2
      have ht : 0 < t := hpos t (by simp)
      have hpos' : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
      obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
        cases js with
        | nil => simp at h1
        | cons j js' => exact ⟨j, js', rfl⟩
      obtain ⟨k', ks', rfl⟩ : ∃ k' ks', ks = k' :: ks' := by
        cases ks with
        | nil => simp at h2
        | cons k' ks' => exact ⟨k', ks', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2
      show List.Forall₂ (· < ·) ((j + t - k') % t :: HvdH.subDigits ts js' ks') (t :: ts)
      rw [List.forall₂_cons]
      exact ⟨Nat.mod_lt _ ht, ih js' ks' hpos' h1 h2⟩

theorem subIdx_lt (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (j k : ℕ) :
    HvdH.subIdx ts j k < ts.prod := by
  unfold HvdH.subIdx
  refine undigits_lt ?_
  exact subDigits_forall₂_lt ts _ _ hpos (digits_length ts j) (digits_length ts k)

/-- `phase` is additive-linear: the difference of two phases is a `myPhase` with
componentwise-difference coefficients. -/
theorem phase_sub : ∀ (ts js ks as : List ℕ), js.length = ts.length → as.length = ts.length →
    ks.length = ts.length →
    HvdH.phase ts js ks - HvdH.phase ts ks as = myPhase ts (subN js as) ks := by
  intro ts
  induction ts with
  | nil =>
      intro js ks as h1 h2 h3
      have hj : js = [] := List.eq_nil_of_length_eq_zero h1
      have hk : ks = [] := List.eq_nil_of_length_eq_zero h3
      have ha : as = [] := List.eq_nil_of_length_eq_zero h2
      subst hj; subst hk; subst ha
      simp [HvdH.phase, myPhase]
  | cons t ts ih =>
      intro js ks as h1 h2 h3
      obtain ⟨j, js', rfl⟩ : ∃ j js', js = j :: js' := by
        cases js with
        | nil => simp at h1
        | cons j js' => exact ⟨j, js', rfl⟩
      obtain ⟨k, ks', rfl⟩ : ∃ k ks', ks = k :: ks' := by
        cases ks with
        | nil => simp at h3
        | cons k ks' => exact ⟨k, ks', rfl⟩
      obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
        cases as with
        | nil => simp at h2
        | cons a as' => exact ⟨a, as', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2 h3
      have hsub := ih js' ks' as' h1 h2 h3
      simp only [subN_cons, HvdH.phase, myPhase]
      rw [← hsub]
      push_cast
      ring

/-- Subtracting a phase from a `myPhase` subtracts componentwise. -/
theorem myPhase_sub_phase : ∀ (ts : List ℕ) (c : List ℤ) (ks bs : List ℕ),
    c.length = ts.length → ks.length = ts.length → bs.length = ts.length →
    myPhase ts c ks - HvdH.phase ts ks bs = myPhase ts (subNZ c bs) ks := by
  intro ts
  induction ts with
  | nil =>
      intro c ks bs h1 h2 h3
      have hc : c = [] := List.eq_nil_of_length_eq_zero h1
      have hk : ks = [] := List.eq_nil_of_length_eq_zero h2
      have hb : bs = [] := List.eq_nil_of_length_eq_zero h3
      subst hc; subst hk; subst hb
      simp [HvdH.phase, myPhase]
  | cons t ts ih =>
      intro c ks bs h1 h2 h3
      obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, c = c0 :: cs := by
        cases c with
        | nil => simp at h1
        | cons c0 cs => exact ⟨c0, cs, rfl⟩
      obtain ⟨k, ks', rfl⟩ : ∃ k ks', ks = k :: ks' := by
        cases ks with
        | nil => simp at h2
        | cons k ks' => exact ⟨k, ks', rfl⟩
      obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => simp at h3
        | cons b bs' => exact ⟨b, bs', rfl⟩
      simp only [List.length_cons, Nat.succ.injEq] at h1 h2 h3
      have hsub := ih cs ks' bs' h1 h2 h3
      simp only [subNZ_cons, HvdH.phase, myPhase]
      rw [← hsub]
      push_cast
      ring

/-- Triple difference of phases. -/
theorem phase_sub3 (ts js ks as bs : List ℕ) (hjs : js.length = ts.length)
    (has : as.length = ts.length) (hks : ks.length = ts.length) (hbs : bs.length = ts.length) :
    HvdH.phase ts js ks - HvdH.phase ts ks as - HvdH.phase ts ks bs
      = myPhase ts (subNZ (subN js as) bs) ks := by
  have h1 := phase_sub ts js ks as hjs has hks
  have h2 := myPhase_sub_phase ts (subN js as) ks bs ?_ hks hbs
  · rw [h1, h2]
  · simp [subN, hjs, has]

end Work.DFT
