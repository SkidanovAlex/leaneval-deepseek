import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.auCWDefs
import Submission.Work.Resample.pbDefs
import Submission.Work.Layout.mvVal_ev_full

set_option autoImplicit false

namespace Work.Resample

open HvdH

theorem encs_cons' (v : Val) (vs : List Val) : HvdH.encs (v :: vs) = v.enc ++ HvdH.encs vs := by
  show (List.map Val.enc (v :: vs)).flatten = _
  rw [List.map_cons, List.flatten_cons]
  rfl

theorem encs_nil' : HvdH.encs ([] : List Val) = [] := rfl

/-- A `WordM` that starts and ends with no values on the non-zero stacks is a `WordR`. -/
theorem WordM.toWordR {main p : Cmd} {Pre : List Val → Prop}
    {Post : List Val → List Val → Prop} {C : List Val → ℕ}
    (h : WordM main p (fun vs a => Pre vs ∧ a = fun _ : Stk => ([] : List Val))
        (fun vs a out b => Post vs out ∧ b = fun _ : Stk => ([] : List Val)) (fun vs a => C vs)) :
    WordR main p Pre Post C := by
  intro vs hvs s R hR
  obtain ⟨out, b, s', n, ⟨hpost, hb⟩, hev, hc, h0, hk⟩ :=
    h vs (fun _ => ([] : List Val)) ⟨hvs, rfl⟩ s R (fun k => s.stk k) hR
      (fun k _ => by rw [encs_nil']; rfl)
  refine ⟨out, s', n, hpost, hev, hc, h0, fun k hk0 => ?_⟩
  have hb' : b k = ([] : List Val) := by rw [hb]
  rw [hk k hk0, hb', encs_nil']
  rfl

/-- Move the top value of stack `0` onto stack `tgt`, in front of the values already there.
`c`, `d` are the scratch stacks of `Work.Layout.mvVal` (restored by it). -/
theorem mvOut (tgt c d : Stk) (h1 : tgt ≠ 0) (h2 : c ≠ 0) (h3 : c ≠ tgt) (h4 : d ≠ 0)
    (h5 : d ≠ tgt) (h6 : c ≠ d) :
    ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (rest L0 : List Val),
      WordM main prog (fun vs a => vs = v :: rest ∧ a tgt = L0)
        (fun vs a out b => out = rest ∧ b tgt = v :: L0) (fun _ _ => Kc * (vsz v + 1)) := by
  refine ⟨Work.Layout.mvVal 0 tgt c d, 16, ?_⟩
  intro main v rest L0 vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = HvdH.encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = HvdH.encs (a k) ++ Bg k := hk
  have h00 : X 0 = v.enc ++ (HvdH.encs rest ++ R) := by
    rw [h0X, hvs, encs_cons', List.append_assoc]
  have htX : X tgt = HvdH.encs L0 ++ Bg tgt := by
    rw [hkX tgt h1, ha]
  obtain ⟨s', N, hev, hN, h0', ht', hc', hd', hf⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := 0) (b := tgt) (c := c) (d := d)
      (Ne.symm h1) (Ne.symm h2) (Ne.symm h4) (Ne.symm h3) (Ne.symm h5) h6
      (g := g) (X := X) (v := v) (A := HvdH.encs rest ++ R) (B := HvdH.encs L0 ++ Bg tgt) h00 htX
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨rest, Function.update a tgt (v :: L0), s', n, ⟨rfl, by simp⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · exact h0'
  · intro k hk0
    by_cases hkt : k = tgt
    · rw [hkt]
      rw [Function.update_self]
      rw [ht', encs_cons', List.append_assoc]
    · rw [Function.update_of_ne hkt]
      by_cases hkc : k = c
      · rw [hkc, hc']
        exact hkX c h2
      · by_cases hkd : k = d
        · rw [hkd, hd']
          exact hkX d h4
        · rw [hf k hk0 hkt hkc hkd]
          exact hkX k hk0

/-- Move the top value of stack `src` onto stack `0`. -/
theorem mvIn (src c d : Stk) (h1 : src ≠ 0) (h2 : c ≠ 0) (h3 : c ≠ src) (h4 : d ≠ 0)
    (h5 : d ≠ src) (h6 : c ≠ d) :
    ∃ (prog : Cmd) (Kc : ℕ), ∀ (main : Cmd) (v : Val) (L0 rest : List Val),
      WordM main prog (fun vs a => vs = rest ∧ a src = v :: L0)
        (fun vs a out b => out = v :: vs ∧ b src = L0) (fun _ _ => Kc * (vsz v + 1)) := by
  refine ⟨Work.Layout.mvVal src 0 c d, 16, ?_⟩
  intro main v L0 rest vs a hpre s R Bg h0 hk
  obtain ⟨hvs, ha⟩ := hpre
  obtain ⟨g, X⟩ := s
  have h0X : X 0 = HvdH.encs vs ++ R := h0
  have hkX : ∀ k : Stk, k ≠ 0 → X k = HvdH.encs (a k) ++ Bg k := hk
  have h00 : X 0 = HvdH.encs rest ++ R := by rw [h0X, hvs]
  have hsX : X src = v.enc ++ (HvdH.encs L0 ++ Bg src) := by
    rw [hkX src h1, ha, encs_cons', List.append_assoc]
  obtain ⟨s', N, hev, hN, hs', h0', hc', hd', hf⟩ :=
    Work.Layout.mvVal_ev_full (main := main) (a := src) (b := 0) (c := c) (d := d)
      h1 (Ne.symm h3) (Ne.symm h5) (Ne.symm h2) (Ne.symm h4) h6
      (g := g) (X := X) (v := v) (A := HvdH.encs L0 ++ Bg src) (B := HvdH.encs rest ++ R) hsX h00
  obtain ⟨n, heval, hnN⟩ := hev
  refine ⟨v :: vs, Function.update a src L0, s', n, ⟨rfl, by simp⟩, heval, ?_, ?_, ?_⟩
  · exact le_trans hnN hN
  · rw [hvs, encs_cons', List.append_assoc]
    exact h0'
  · intro k hk0
    by_cases hks : k = src
    · rw [hks]
      rw [Function.update_self]
      exact hs'
    · rw [Function.update_of_ne hks]
      by_cases hkc : k = c
      · rw [hkc, hc']
        exact hkX c h2
      · by_cases hkd : k = d
        · rw [hkd, hd']
          exact hkX d h4
        · rw [hf k hks hk0 hkc hkd]
          exact hkX k hk0

/-- The cost arithmetic of the assembly: the four phases fit the advertised bound. -/
theorem auCWCostBound (K1 K2 K3 K4 Kf L p : ℕ) (Cm : ℕ → ℕ) (KK : ℕ)
    (hS : 20 * (K1 + K2 + K3 + K4 + Kf + 1) ≤ KK)
    (hmono : Cm (K2 * p) ≤ Cm (KK * p)) :
    K1 * (L + 1) * (p + 1)
      + (L * (K2 * (Cm (K2 * p) + p + 1) + Kf * (3 * p + 12 + 1)) + Kf)
      + (K3 * (L + 1) * (p + 1) + K4 * (p + 1) * (L + 1))
      ≤ KK * (L + 1) * (Cm (KK * p) + p + 1) := by
  set S : ℕ := K1 + K2 + K3 + K4 + Kf + 1 with hSdef
  have hK1 : K1 ≤ S := by omega
  have hK2 : K2 ≤ S := by omega
  have hK3 : K3 ≤ S := by omega
  have hK4 : K4 ≤ S := by omega
  have hKf : Kf ≤ S := by omega
  have hSKK : 20 * S ≤ KK := by omega
  set Y : ℕ := Cm (KK * p) + p + 1 with hY
  have hpY : p + 1 ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hL1 : 1 ≤ L + 1 := by omega
  have hCm : Cm (K2 * p) + p + 1 ≤ Y := by omega
  have hb1 : K1 * (L + 1) * (p + 1) ≤ S * ((L + 1) * Y) := by
    calc K1 * (L + 1) * (p + 1) = (K1 * (p + 1)) * (L + 1) := by ring
      _ ≤ (S * (p + 1)) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK1)
      _ ≤ (S * Y) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpY)
      _ = S * ((L + 1) * Y) := by ring
  have hb2 : L * (K2 * (Cm (K2 * p) + p + 1) + Kf * (3 * p + 12 + 1)) + Kf
      ≤ 15 * (S * ((L + 1) * Y)) := by
    have hE : K2 * (Cm (K2 * p) + p + 1) + Kf * (3 * p + 12 + 1) ≤ 14 * S * Y := by
      have ha : K2 * (Cm (K2 * p) + p + 1) ≤ S * Y := by
        calc K2 * (Cm (K2 * p) + p + 1) ≤ S * (Cm (K2 * p) + p + 1) :=
              Nat.mul_le_mul_right _ hK2
          _ ≤ S * Y := Nat.mul_le_mul_left _ hCm
      have hb : Kf * (3 * p + 12 + 1) ≤ 13 * S * Y := by
        have h6 : 3 * p + 12 + 1 ≤ 13 * (p + 1) := by omega
        calc Kf * (3 * p + 12 + 1) ≤ Kf * (13 * (p + 1)) := Nat.mul_le_mul_left _ h6
          _ = 13 * Kf * (p + 1) := by ring
          _ ≤ 13 * S * (p + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKf)
          _ ≤ 13 * S * Y := Nat.mul_le_mul_left _ hpY
      linarith [ha, hb]
    have hLm : L * (14 * S * Y) ≤ 14 * S * ((L + 1) * Y) := by
      calc L * (14 * S * Y) = (14 * S) * (L * Y) := by ring
        _ ≤ (14 * S) * ((L + 1) * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right Y (by omega))
        _ = 14 * S * ((L + 1) * Y) := by ring
    have hkf : Kf ≤ S * ((L + 1) * Y) := by
      calc Kf ≤ S := hKf
        _ = S * 1 := by ring
        _ ≤ S * ((L + 1) * Y) := by
          have h1 : 1 ≤ (L + 1) * Y := by
            have := Nat.mul_le_mul hL1 hY1
            simpa using this
          have h2 := Nat.mul_le_mul_left S h1
          simpa using h2
    calc L * (K2 * (Cm (K2 * p) + p + 1) + Kf * (3 * p + 12 + 1)) + Kf
        ≤ L * (14 * S * Y) + Kf := Nat.add_le_add_right (Nat.mul_le_mul_left _ hE) _
      _ ≤ 14 * S * ((L + 1) * Y) + S * ((L + 1) * Y) := Nat.add_le_add hLm hkf
      _ = 15 * (S * ((L + 1) * Y)) := by ring
  have hb3 : K3 * (L + 1) * (p + 1) ≤ S * ((L + 1) * Y) := by
    calc K3 * (L + 1) * (p + 1) = (K3 * (p + 1)) * (L + 1) := by ring
      _ ≤ (S * (p + 1)) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK3)
      _ ≤ (S * Y) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpY)
      _ = S * ((L + 1) * Y) := by ring
  have hb4 : K4 * (p + 1) * (L + 1) ≤ S * ((L + 1) * Y) := by
    calc K4 * (p + 1) * (L + 1) = (K4 * (p + 1)) * (L + 1) := by ring
      _ ≤ (S * (p + 1)) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK4)
      _ ≤ (S * Y) * (L + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpY)
      _ = S * ((L + 1) * Y) := by ring
  calc K1 * (L + 1) * (p + 1)
      + (L * (K2 * (Cm (K2 * p) + p + 1) + Kf * (3 * p + 12 + 1)) + Kf)
      + (K3 * (L + 1) * (p + 1) + K4 * (p + 1) * (L + 1))
      ≤ S * ((L + 1) * Y) + 15 * (S * ((L + 1) * Y))
        + (S * ((L + 1) * Y) + S * ((L + 1) * Y)) := by
        have := hb1; have := hb2; have := hb3; have := hb4; omega
    _ = 18 * (S * ((L + 1) * Y)) := by ring
    _ ≤ 20 * (S * ((L + 1) * Y)) := by omega
    _ = 20 * S * ((L + 1) * Y) := by ring
    _ ≤ KK * ((L + 1) * Y) := Nat.mul_le_mul_right _ hSKK
    _ = KK * (L + 1) * (Cm (KK * p) + p + 1) := by rw [hY]; ring

end Work.Resample
