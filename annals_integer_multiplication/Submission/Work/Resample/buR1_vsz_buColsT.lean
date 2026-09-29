import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs
import Submission.Work.Fx.FxCommon

set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Small list-size lemmas

These are the list-size estimates of `Work.Resample.buQWrounds`, re-proved here to keep this
module's import cone small. -/

/-- total size of a list of values -/
theorem buR1_vsz_ofList (l : List Val) : vsz (ofList l) = l.length + 1 + (l.map vsz).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have h : ofList (a :: t) = Val.cons a (ofList t) := rfl
    rw [h, Work.Fx.vsz_cons, ih, List.length_cons, List.map_cons, List.sum_cons]
    ring

/-- size of a list of integers, as a value -/
theorem buR1_vsz_zl (l : List ℤ) : vsz (zl l) = l.length + 1 + (l.map isz).sum := by
  unfold zl
  rw [buR1_vsz_ofList, List.length_map]
  have h1 : ((l.map Val.int).map vsz) = l.map isz := by
    rw [List.map_map]
    exact List.map_congr_left (fun z _ => Work.Fx.vsz_int z)
  rw [h1]

/-- a sum of naturals bounded termwise -/
theorem buR1_sum_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≤ M := h a (by simp)
    have ht : ∀ x ∈ t, x ≤ M := fun x hx => h x (by simp [hx])
    have := ih ht
    rw [List.sum_cons, List.length_cons]
    nlinarith

/-- `egM p α ≤ p + 1` -/
theorem buR1_egM_le (p α : ℕ) : egM p α ≤ p + 1 := by
  have h1 : Nat.sqrt p / (2 * α) ≤ Nat.sqrt p := Nat.div_le_self _ _
  have h2 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
  simp only [egM]
  omega

theorem buR1_vsz_buColsT (p α s t : ℕ) (hs : 2 ≤ s) (hp : 100 ≤ p)
    (hwt : ∀ (ℓ h : ℤ), h ∈ Work.Resample.egHset (Work.Resample.egM p α) →
      HvdH.isz (Work.Resample.buWt p α s t ℓ h) ≤ p + 3) :
    (∀ h ∈ Work.Resample.egHs (Work.Resample.egM p α),
        HvdH.vsz (Work.Resample.buCol p α s t h) ≤ (s + 1) * (p + 4)) ∧
    HvdH.vsz (Work.Resample.buColsT p α s t) ≤
      20 * (Work.Resample.egM p α + 1) * (s + 1) * (p + 1) := by
  have hm : egM p α ≤ p + 1 := buR1_egM_le p α
  obtain ⟨hfins, _, hlen, _, hle, _⟩ := buQWhs (egM p α)
  have hmem : ∀ h ∈ egHs (egM p α), h ∈ egHset (egM p α) := by
    intro h hh
    rw [← hfins, List.mem_toFinset]
    exact hh
  have hisz : ∀ h ∈ egHs (egM p α), isz h ≤ p + 3 := by
    intro h hh
    have h2 : h.natAbs ≤ p + 1 := le_trans (hle h hh) hm
    have h3 : h.natAbs < 2 ^ (p + 1) :=
      lt_of_le_of_lt h2 (Nat.lt_two_pow_self (n := p + 1))
    exact Work.Fx.isz_le_of_natAbs_lt h3
  have hcol : ∀ h ∈ egHs (egM p α), vsz (buCol p α s t h) ≤ (s + 1) * (p + 4) := by
    intro h hh
    have h1 : vsz (buCol p α s t h) =
        s + 1 + ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum := by
      unfold buCol
      rw [buR1_vsz_zl]
      simp
    rw [h1]
    have h2 : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤
        s * (p + 3) := by
      have hb : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤
          ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).length * (p + 3) :=
        buR1_sum_le_length_mul (by
          intro x hx
          rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hz
          rw [← hi]
          exact hwt _ h (hmem h hh))
      simpa using hb
    nlinarith [Nat.zero_le s, Nat.zero_le p]
  refine ⟨hcol, ?_⟩
  unfold buColsT
  rw [buR1_vsz_ofList, List.length_map, hlen]
  have hsum : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ 2 * egM p α * (2 * (p + 4) * (s + 1)) := by
    have hb : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).sum ≤
        ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).length * (2 * (p + 4) * (s + 1)) :=
      buR1_sum_le_length_mul (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
        rcases List.mem_map.mp ha with ⟨h, hh, rfl⟩
        rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
        have h1 := hcol h hh
        have h2 := hisz h hh
        nlinarith [Nat.zero_le s, Nat.zero_le p])
    simp only [List.length_map] at hb
    rw [hlen] at hb
    exact hb
  have hs1 : 1 ≤ s + 1 := by omega
  have hp1 : 1 ≤ p + 1 := by omega
  have hAB : 1 ≤ (s + 1) * (p + 1) := by nlinarith [hs1, hp1]
  have hsum2 : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ 8 * egM p α * ((s + 1) * (p + 1)) := by
    have hmul : 2 * (p + 4) * (s + 1) ≤ 4 * ((s + 1) * (p + 1)) := by
      nlinarith [Nat.zero_le s]
    calc ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
        (egHs (egM p α))).map vsz).sum
        ≤ 2 * egM p α * (2 * (p + 4) * (s + 1)) := hsum
      _ ≤ 2 * egM p α * (4 * ((s + 1) * (p + 1))) := Nat.mul_le_mul_left _ hmul
      _ = 8 * egM p α * ((s + 1) * (p + 1)) := by ring
  have hE : 1 ≤ egM p α := by
    unfold egM
    exact Nat.succ_le_succ (Nat.zero_le _)
  have h1 : 2 * egM p α + 1 ≤ 3 * egM p α * ((s + 1) * (p + 1)) := by
    have ha : 2 * egM p α + 1 ≤ 3 * egM p α := by omega
    calc 2 * egM p α + 1 ≤ 3 * egM p α := ha
      _ = 3 * egM p α * 1 := by ring
      _ ≤ 3 * egM p α * ((s + 1) * (p + 1)) := Nat.mul_le_mul_left _ hAB
  have h2 : 11 * egM p α * ((s + 1) * (p + 1)) ≤
      20 * (egM p α + 1) * (s + 1) * (p + 1) := by
    have hb : 11 * egM p α ≤ 20 * (egM p α + 1) := by omega
    calc 11 * egM p α * ((s + 1) * (p + 1)) ≤ (20 * (egM p α + 1)) * ((s + 1) * (p + 1)) :=
          Nat.mul_le_mul_right _ hb
      _ = 20 * (egM p α + 1) * (s + 1) * (p + 1) := by ring
  have h3 : 3 * egM p α * ((s + 1) * (p + 1)) + 8 * egM p α * ((s + 1) * (p + 1)) =
      11 * egM p α * ((s + 1) * (p + 1)) := by ring
  linarith

end Work.Resample
