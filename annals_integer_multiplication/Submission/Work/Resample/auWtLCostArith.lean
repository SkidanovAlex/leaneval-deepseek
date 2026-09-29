import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auWtLCostPoly
import Submission.Work.Resample.auWtLCostPow

/-!
# The arithmetic core of the weight-word cost bound (`Work.Resample.auWtLWord`)

`auWtLCostArith` bounds the (abstract) cost expression of the weight word by the single power
`2^N * (p+1)^(2^N)`, `N = Krep + Kenum + Kml + KE + 40`, using only the hypotheses that the loop
counters `L, V1, V2, V3, W` never exceed the uniform bound `auSZ p = 10p + 400` (`V3` and `W` being
one multiplication away from it).

The proof reduces every summand to the polynomial bound `(p+1)^8` (`Work.Resample.auWtLCostPoly`)
and then to the exponent domination `N·(p+1)^8 ≤ (p+1)^(2^N)`, `KE·(p+1)^(KE+2) ≤ (p+1)^(2^N)`
(`Work.Resample.auWtLCostPow`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

theorem auWtLCostArith {Krep Kenum Kml KE p L V1 V2 V3 W : ℕ}
    (hp : 100 ≤ p) (hL : L ≤ 4 * p + 1)
    (hV1 : V1 ≤ Work.Resample.auSZ p) (hV2 : V2 ≤ Work.Resample.auSZ p)
    (hV3 : V3 ≤ L * (Work.Resample.auSZ p + 1) + 1) (hW : W ≤ 2 * Work.Resample.auSZ p + 1) :
    Krep * ((L + 1) * (V1 + 1) + V2 + 1)
      + Kenum * (V3 + L * (L.size + 1) + 1)
      + (L * (KE * (p + 1) ^ KE + Kml * (W + 1)) + Kml)
    ≤ (2 ^ (Krep + Kenum + Kml + KE + 40)) *
        (p + 1) ^ (2 ^ (Krep + Kenum + Kml + KE + 40)) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := auWtLCostPoly p hp
  obtain ⟨hpow1, hpow2⟩ :=
    auWtLCostPow (Krep := Krep) (Kenum := Kenum) (Kml := Kml) (KE := KE) (p := p) (by omega)
  simp only [auSZ] at hV1 hV2 hV3 hW
  set B := (p+1)^8 with hBdef
  -- (1) the first summand
  have hT1 : (L + 1) * (V1 + 1) + V2 + 1 ≤ B := by
    rw [hBdef]
    have h1 : (L+1)*(V1+1) ≤ (4*p+2)*(10*p+401) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : V2 + 1 ≤ 10*p+401 := by omega
    have h3 : (4*p+2)*(10*p+401) + (10*p+401) ≤ (p+1)^8 := by
      have he : (4*p+2)*(10*p+401) + (10*p+401) = (4*p+3)*(10*p+401) := by ring
      rw [he]; exact hp1
    linarith
  -- (2) the second summand
  have hT2 : V3 + L * (L.size + 1) + 1 ≤ B := by
    rw [hBdef]
    have hV3' : V3 ≤ L * (10*p+401) + 1 := hV3
    have hsz : L.size + 1 ≤ L + 1 := by
      have h : L.size ≤ L := Nat.size_le.mpr Nat.lt_two_pow_self
      omega
    have hLsz : L*(L.size+1) ≤ (4*p+1)*(4*p+2) := by
      calc L*(L.size+1) ≤ (4*p+1)*(L+1) := Nat.mul_le_mul hL hsz
        _ ≤ (4*p+1)*(4*p+2) := Nat.mul_le_mul_left _ (by omega)
    have hV3'' : V3 ≤ (4*p+1)*(10*p+401) + 1 := by
      have hm : L * (10*p+401) ≤ (4*p+1)*(10*p+401) := Nat.mul_le_mul hL le_rfl
      linarith
    linarith
  -- (3) the `Kml` part of the third summand
  have hT3 : L * (W + 1) + 1 ≤ B := by
    rw [hBdef]
    have hW' : W + 1 ≤ 20*p + 802 := by
      have h := hW
      omega
    have hm : L*(W+1) ≤ (4*p+1)*(20*p+802) := Nat.mul_le_mul hL hW'
    linarith [hp3]
  -- (4) the `KE` part of the third summand
  have hL2 : L ≤ (p+1)^2 := le_trans hL hp4
  have hT4 : L * (KE * (p+1)^KE) ≤ KE * (p+1)^(KE+2) := by
    have hm : L*(KE*(p+1)^KE) ≤ (p+1)^2 * (KE*(p+1)^KE) := Nat.mul_le_mul_right _ hL2
    have he : (p+1)^2 * (KE*(p+1)^KE) = KE*(p+1)^(KE+2) := by
      rw [mul_comm ((p+1)^2) (KE*(p+1)^KE), mul_assoc, ← pow_add]
    exact le_trans hm (le_of_eq he)
  have hsmall : (Krep + Kenum + Kml) * B ≤ (p+1)^(2^(Krep+Kenum+Kml+KE+40)) := by
    rw [hBdef]
    exact le_trans (Nat.mul_le_mul_right ((p+1)^8) (by omega)) hpow1
  have hT3' : L*(Kml*(W+1)) + Kml ≤ Kml*B := by
    calc L*(Kml*(W+1)) + Kml = Kml*(L*(W+1)) + Kml := by ring
      _ = Kml*(L*(W+1)+1) := by ring
      _ ≤ Kml*B := Nat.mul_le_mul_left Kml hT3
  have hA : Krep * ((L + 1) * (V1 + 1) + V2 + 1) + Kenum * (V3 + L * (L.size + 1) + 1)
      ≤ Krep*B + Kenum*B :=
    add_le_add (Nat.mul_le_mul_left Krep hT1) (Nat.mul_le_mul_left Kenum hT2)
  have hBig : L*(KE*(p+1)^KE) + (L*(Kml*(W+1)) + Kml) ≤ KE*(p+1)^(KE+2) + Kml*B :=
    add_le_add hT4 hT3'
  calc Krep * ((L + 1) * (V1 + 1) + V2 + 1)
        + Kenum * (V3 + L * (L.size + 1) + 1)
        + (L * (KE * (p + 1) ^ KE + Kml * (W + 1)) + Kml)
      = Krep * ((L + 1) * (V1 + 1) + V2 + 1) + Kenum * (V3 + L * (L.size + 1) + 1)
        + (L*(KE*(p+1)^KE) + (L*(Kml*(W+1)) + Kml)) := by ring
    _ ≤ (Krep*B + Kenum*B) + (KE*(p+1)^(KE+2) + Kml*B) := add_le_add hA hBig
    _ = (Krep + Kenum + Kml) * B + KE * (p+1)^(KE+2) := by ring
    _ ≤ (p+1)^(2^(Krep+Kenum+Kml+KE+40)) + (p+1)^(2^(Krep+Kenum+Kml+KE+40)) :=
        add_le_add hsmall hpow2
    _ = 2 * (p+1)^(2^(Krep+Kenum+Kml+KE+40)) := by ring
    _ ≤ 2^(Krep+Kenum+Kml+KE+40) * (p + 1)^(2^(Krep+Kenum+Kml+KE+40)) := by
        have h2 : (2:ℕ) ≤ 2^(Krep+Kenum+Kml+KE+40) := by
          calc (2:ℕ) = 2^1 := by norm_num
            _ ≤ 2^(Krep+Kenum+Kml+KE+40) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact Nat.mul_le_mul_right _ h2

end Work.Resample
