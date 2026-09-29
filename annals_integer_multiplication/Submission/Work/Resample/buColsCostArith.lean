import Mathlib
import Submission.Work.Resample.buColsDefs

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The cost bookkeeping of `Work.Resample.buColsWord`: the four step costs `C1 … C4` (the shift
list, the `mapList` of the columns, the `enumerate`, the `mapList` of the labels) fit into
`buColsK · (egM p α + 1) · (s+1) · (p+1)^{buColsK}`. -/
theorem buColsCostArith (p α s Kl Kc Kml Ke KAR Kuc Kcs C1 C2 C3 C4 : ℕ)
    (hs : 2 ≤ s) (hp : 100 ≤ p) (hα : 2 ≤ α)
    (h1 : C1 ≤ Kl * (egM p α + 1) * (p + 1) ^ Kl)
    (h2 : C2 ≤ (2 * egM p α) * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (buLout p s + 1)) + Kml)
    (h3 : C3 ≤ Ke * ((2 * egM p α + 1) * (buLout p s + 1) + (2 * egM p α) * (2 * (p + 1)) + 1))
    (h4 : C4 ≤ (2 * egM p α) * (Kuc + (KAR * (buLout p s + 1) + Kcs)
      + Kml * (buLout p s + 1)) + Kml) :
    C1 + (C2 + (C3 + C4))
      ≤ buColsK Kl Kc Kml Ke KAR Kuc Kcs * (egM p α + 1) * (s + 1)
          * (p + 1) ^ buColsK Kl Kc Kml Ke KAR Kuc Kcs := by
  set KK := buColsK Kl Kc Kml Ke KAR Kuc Kcs with hKKdef
  set m := egM p α with hmdef
  let X : ℕ := (m + 1) * (s + 1) * (p + 1) ^ KK
  have hKK : KK = 1000 * (Kl + Kc + Kml + Ke + KAR + Kuc + Kcs + 2) := by rw [hKKdef]; rfl
  have hb2 : 2 ≤ p + 1 := by omega
  have hs1 : 1 ≤ s + 1 := by omega
  have hm1 : 1 ≤ m + 1 := by omega
  have hB4 : buSZ p + 1 ≤ (p + 1) ^ 4 := buSZ_add_one_le_four p hp
  have hKK20 : 20 ≤ KK := by rw [hKK]; omega
  -- power facts
  have hpowKl : Kl * (p + 1) ^ Kl ≤ (p + 1) ^ KK := by
    calc Kl * (p + 1) ^ Kl ≤ (p + 1) ^ Kl * (p + 1) ^ Kl :=
          Nat.mul_le_mul_right _ (le_pow_self (p + 1) Kl hb2)
      _ = (p + 1) ^ (Kl + Kl) := by rw [← pow_add]
      _ ≤ (p + 1) ^ KK := Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega)
  have hpowKc : Kc * (p + 1) ^ Kc ≤ (p + 1) ^ KK := by
    calc Kc * (p + 1) ^ Kc ≤ (p + 1) ^ Kc * (p + 1) ^ Kc :=
          Nat.mul_le_mul_right _ (le_pow_self (p + 1) Kc hb2)
      _ = (p + 1) ^ (Kc + Kc) := by rw [← pow_add]
      _ ≤ (p + 1) ^ KK := Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega)
  have hL5 : buLout p s + 1 ≤ (s + 1) * (p + 1) ^ 5 := by
    have h2 : 2 ≤ (p + 1) ^ 1 := by simpa using hb2
    have hB2 : 2 * (buSZ p + 1) ≤ (p + 1) ^ 5 := by
      calc 2 * (buSZ p + 1) ≤ (p + 1) ^ 1 * (p + 1) ^ 4 :=
            Nat.mul_le_mul (by simpa using h2) hB4
        _ = (p + 1) ^ (1 + 4) := by rw [← pow_add]
        _ = (p + 1) ^ 5 := by norm_num
    calc buLout p s + 1 ≤ 2 * ((s + 1) * (buSZ p + 1)) := by
          have h3 : buSZ p + 2 ≤ 3 * (buSZ p + 1) := by omega
          have h3' : 3 * (buSZ p + 1) ≤ (s + 1) * (buSZ p + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          simp only [buLout]
          omega
      _ = (s + 1) * (2 * (buSZ p + 1)) := by ring
      _ ≤ (s + 1) * (p + 1) ^ 5 := Nat.mul_le_mul_left _ hB2
  have hpowKml : Kml * (buLout p s + 1) ≤ (s + 1) * (p + 1) ^ KK := by
    calc Kml * (buLout p s + 1) ≤ Kml * ((s + 1) * (p + 1) ^ 5) :=
          Nat.mul_le_mul_left _ hL5
      _ = (s + 1) * (Kml * (p + 1) ^ 5) := by ring
      _ ≤ (s + 1) * (p + 1) ^ (Kml + 5) :=
          Nat.mul_le_mul_left _ (const_mul_pow_le_pow (C := Kml) (b := p + 1) (n := 5) hb2)
      _ ≤ (s + 1) * (p + 1) ^ KK :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega))
  have hKml : Kml ≤ (p + 1) ^ KK :=
    le_trans (le_pow_self (p + 1) Kml hb2) (Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega))
  -- the four term bounds
  have t1 : Kl * (m + 1) * (p + 1) ^ Kl ≤ 1 * X := by
    have h := mul_le_mul3 (le_refl (m + 1)) hs1 hpowKl
    calc Kl * (m + 1) * (p + 1) ^ Kl ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := by
          calc Kl * (m + 1) * (p + 1) ^ Kl = (m + 1) * (Kl * (p + 1) ^ Kl) := by ring
            _ ≤ (m + 1) * (p + 1) ^ KK := Nat.mul_le_mul_left _ hpowKl
            _ ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := prod_le_prod m s p KK
      _ = 1 * X := by rw [one_mul]
  have t2 : (2 * m) * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (buLout p s + 1)) + Kml ≤ 5 * X := by
    have hA : (2 * m) * (Kc * (s + 1) * (p + 1) ^ Kc) ≤ 2 * X := by
      calc (2 * m) * (Kc * (s + 1) * (p + 1) ^ Kc)
          = (2 * m) * (Kc * (p + 1) ^ Kc) * (s + 1) := by ring
        _ ≤ (2 * (m + 1)) * ((p + 1) ^ KK) * (s + 1) :=
            mul_le_mul3 (Nat.mul_le_mul_left 2 (by omega)) hpowKc (le_refl (s + 1))
        _ = 2 * ((m + 1) * (s + 1) * (p + 1) ^ KK) := by ring
        _ = 2 * X := rfl
    have hB : (2 * m) * (Kml * (buLout p s + 1)) ≤ 2 * X := by
      calc (2 * m) * (Kml * (buLout p s + 1))
          ≤ (2 * (m + 1)) * ((s + 1) * (p + 1) ^ KK) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hpowKml
        _ = 2 * ((m + 1) * (s + 1) * (p + 1) ^ KK) := by ring
        _ = 2 * X := rfl
    have hC : Kml ≤ 1 * X := by
      calc Kml ≤ (p + 1) ^ KK := hKml
        _ ≤ X := by
            calc (p + 1) ^ KK ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := pow_le_prod m s p KK
              _ = X := rfl
        _ = 1 * X := (one_mul X).symm
    calc (2 * m) * (Kc * (s + 1) * (p + 1) ^ Kc + Kml * (buLout p s + 1)) + Kml
        = (2 * m) * (Kc * (s + 1) * (p + 1) ^ Kc) + (2 * m) * (Kml * (buLout p s + 1)) + Kml := by
          ring
      _ ≤ 2 * X + 2 * X + 1 * X := Nat.add_le_add (Nat.add_le_add hA hB) hC
      _ = 5 * X := by ring
  have t3 : Ke * ((2 * m + 1) * (buLout p s + 1) + (2 * m) * (2 * (p + 1)) + 1) ≤ 8 * X := by
    have hu1 : (2 * m + 1) * (buLout p s + 1) ≤ 3 * ((m + 1) * (s + 1) * (p + 1) ^ 5) := by
      have h2 : 2 * m + 1 ≤ 3 * (m + 1) := by omega
      calc (2 * m + 1) * (buLout p s + 1) ≤ (3 * (m + 1)) * ((s + 1) * (p + 1) ^ 5) :=
            Nat.mul_le_mul h2 hL5
        _ = 3 * ((m + 1) * (s + 1) * (p + 1) ^ 5) := by ring
    have hu2 : (2 * m) * (2 * (p + 1)) ≤ 4 * ((m + 1) * (s + 1) * (p + 1) ^ 5) := by
      have h3 : (p + 1) ≤ (s + 1) * (p + 1) ^ 5 := by
        calc (p + 1) = 1 * ((p + 1) ^ 1) := by simp
          _ ≤ (s + 1) * (p + 1) ^ 5 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      calc (2 * m) * (2 * (p + 1)) ≤ (2 * (m + 1)) * (2 * ((s + 1) * (p + 1) ^ 5)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (Nat.mul_le_mul_left 2 h3)
        _ = 4 * ((m + 1) * (s + 1) * (p + 1) ^ 5) := by ring
    have hp15 : (1 : ℕ) ≤ (p + 1) ^ 5 := by
      simpa using Nat.pow_le_pow_left (by omega : (1 : ℕ) ≤ p + 1) 5
    have hu3 : (1 : ℕ) ≤ (m + 1) * (s + 1) * (p + 1) ^ 5 := by
      calc (1 : ℕ) = 1 * 1 * 1 := by ring
        _ ≤ (m + 1) * (s + 1) * (p + 1) ^ 5 :=
            Nat.mul_le_mul (Nat.mul_le_mul hm1 hs1) hp15
    have hins : (2 * m + 1) * (buLout p s + 1) + (2 * m) * (2 * (p + 1)) + 1
        ≤ 8 * ((m + 1) * (s + 1) * (p + 1) ^ 5) := by
      linarith [hu1, hu2, hu3]
    calc Ke * ((2 * m + 1) * (buLout p s + 1) + (2 * m) * (2 * (p + 1)) + 1)
        ≤ Ke * (8 * ((m + 1) * (s + 1) * (p + 1) ^ 5)) := Nat.mul_le_mul_left _ hins
      _ ≤ (p + 1) ^ Ke * (8 * ((m + 1) * (s + 1) * (p + 1) ^ 5)) :=
          Nat.mul_le_mul_right _ (le_pow_self (p + 1) Ke hb2)
      _ = 8 * ((m + 1) * (s + 1) * ((p + 1) ^ Ke * (p + 1) ^ 5)) := by ring
      _ = 8 * ((m + 1) * (s + 1) * (p + 1) ^ (Ke + 5)) := by rw [← pow_add]
      _ ≤ 8 * ((m + 1) * (s + 1) * (p + 1) ^ KK) := by
          have h1 : (p + 1) ^ (Ke + 5) ≤ (p + 1) ^ KK :=
            Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega)
          exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left ((m + 1) * (s + 1)) h1)
      _ = 8 * X := rfl
  have t4 : (2 * m) * (Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1)) + Kml
      ≤ 3 * X := by
    have hE1 : Kuc ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) := by
      calc Kuc ≤ (p + 1) ^ Kuc := le_pow_self (p + 1) Kuc hb2
        _ ≤ (s + 1) * (p + 1) ^ Kuc := le_mul_succ s _
        _ ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hE2 : KAR * (buLout p s + 1) ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) := by
      calc KAR * (buLout p s + 1) ≤ KAR * ((s + 1) * (p + 1) ^ 5) := Nat.mul_le_mul_left _ hL5
        _ = (s + 1) * (KAR * (p + 1) ^ 5) := by ring
        _ ≤ (s + 1) * (p + 1) ^ (KAR + 5) :=
            Nat.mul_le_mul_left _ (const_mul_pow_le_pow (C := KAR) (b := p + 1) (n := 5) hb2)
        _ ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hE3 : Kcs ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) := by
      calc Kcs ≤ (p + 1) ^ Kcs := le_pow_self (p + 1) Kcs hb2
        _ ≤ (s + 1) * (p + 1) ^ Kcs := le_mul_succ s _
        _ ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hE4 : Kml * (buLout p s + 1) ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) := by
      calc Kml * (buLout p s + 1) ≤ Kml * ((s + 1) * (p + 1) ^ 5) := Nat.mul_le_mul_left _ hL5
        _ = (s + 1) * (Kml * (p + 1) ^ 5) := by ring
        _ ≤ (s + 1) * (p + 1) ^ (Kml + 5) :=
            Nat.mul_le_mul_left _ (const_mul_pow_le_pow (C := Kml) (b := p + 1) (n := 5) hb2)
        _ ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 5) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hE2' : KAR * (buLout p s + 1) ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 7) :=
      le_trans hE2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
    have hE3' : Kcs ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 7) :=
      le_trans hE3 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
    have h23 : KAR * (buLout p s + 1) + Kcs
        ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 9) :=
      add_le_mul_pow hb2 hE2' hE3'
    have hE1' : Kuc ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 9) :=
      le_trans hE1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
    have h123 : Kuc + (KAR * (buLout p s + 1) + Kcs)
        ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 11) :=
      add_le_mul_pow hb2 hE1' h23
    have hE4' : Kml * (buLout p s + 1) ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 11) :=
      le_trans hE4 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
    have hins : Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1)
        ≤ (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 13) :=
      add_le_mul_pow hb2 h123 hE4'
    have hmul : (2 * m) * (Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1))
        ≤ 2 * X := by
      have h2 : (2 * m) ≤ 2 * (m + 1) := Nat.mul_le_mul_left 2 (by omega)
      calc (2 * m) * (Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1))
          ≤ (2 * (m + 1)) * ((s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 13)) :=
            Nat.mul_le_mul h2 hins
        _ = 2 * ((m + 1) * (s + 1) * (p + 1) ^ (KAR + Kuc + Kcs + Kml + 13)) := by ring
        _ ≤ 2 * X := by
            have h1 : (p + 1) ^ (KAR + Kuc + Kcs + Kml + 13) ≤ (p + 1) ^ KK :=
              Nat.pow_le_pow_right (by omega) (by rw [hKK]; omega)
            exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left ((m + 1) * (s + 1)) h1)
    have hKml2 : Kml ≤ 1 * X := by
      calc Kml ≤ (p + 1) ^ KK := hKml
        _ ≤ X := by
            calc (p + 1) ^ KK ≤ (m + 1) * (s + 1) * (p + 1) ^ KK := pow_le_prod m s p KK
              _ = X := rfl
        _ = 1 * X := (one_mul X).symm
    calc (2 * m) * (Kuc + (KAR * (buLout p s + 1) + Kcs) + Kml * (buLout p s + 1)) + Kml
        ≤ 2 * X + 1 * X := Nat.add_le_add hmul hKml2
      _ = 3 * X := by ring
  -- the total
  have e1 : C1 ≤ 1 * X := le_trans h1 t1
  have e2 : C2 ≤ 5 * X := le_trans h2 t2
  have e3 : C3 ≤ 8 * X := le_trans h3 t3
  have e4 : C4 ≤ 3 * X := le_trans h4 t4
  have hsum : C1 + (C2 + (C3 + C4)) ≤ 17 * X := by linarith [e1, e2, e3, e4]
  have hfin : 17 * X ≤ KK * X := Nat.mul_le_mul_right X (by omega)
  have hXeq : KK * X = KK * (m + 1) * (s + 1) * (p + 1) ^ KK := by
    dsimp only [X]
    ring
  calc C1 + (C2 + (C3 + C4)) ≤ 17 * X := hsum
    _ ≤ KK * X := hfin
    _ = KK * (m + 1) * (s + 1) * (p + 1) ^ KK := hXeq

end Work.Resample
