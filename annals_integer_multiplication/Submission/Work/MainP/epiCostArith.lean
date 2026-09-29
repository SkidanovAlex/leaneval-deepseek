import Mathlib

/-!
# Arithmetic for the epilogue cost budget (`Work.MainP.epiCostArith`)

The epilogue of the main program (§5.4 of the paper) has a cost of the shape

`(S+1) * (Ku + Ks*A + (Kd+Km)*B) + Km + Kr*Q₁ + 4*Kp + Kdl*Q₄`

where `A = (3d+4)(sz+2) + 4d + 6`, `B = A + 1`, `Q₁ = (S+1)(sz+2) + (S+1) + 2` and
`Q₄ = (S+1)(sz+2) + (S+1) + 5` (here `S ≥ 1`, `d`, `sz` are the recursion parameters and
the `K•` are the (nonnegative) per-symbol constants of the various libraries).

We prove the crude domination

`LHS ≤ 1000 * (∑K + 1) * (S*(d+1)*(sz+2) + 1)`,

which only needs `S ≥ 1`.  Writing `Y = (d+1)(sz+2)`, `X = S*Y` and `T = ∑K + 1`:

* `A ≤ 11*Y`, `B ≤ 12*Y` (both because `Y ≥ 2`), and `S+1 ≤ 2S` gives
  `(S+1)*A ≤ 22*X` and `(S+1)*B ≤ 24*X`;
* `Q₁ ≤ 4*X` and `Q₄ ≤ 6*X`;
* `S+1 ≤ X` (as `Y ≥ 2`), so `(S+1)*Ku ≤ X*T`;
* finally `86*X*T ≤ 1000*T*(X+1)`.

Summing the eight individual bounds gives `LHS ≤ 86*X*T ≤ 1000*T*(X+1) = RHS`.
-/

set_option maxHeartbeats 2000000

namespace Work.MainP

theorem epiCostArith (Ku Ks Kd Km Kr Kp Kdl S d sz : ℕ) (hS : 1 ≤ S) :
    (S + 1) * ((Ku + Ks * ((3*d+4)*(sz+2) + 4*d + 6) + Kd * (((3*d+4)*(sz+2) + 4*d + 6) + 1))
        + Km * (((3*d+4)*(sz+2) + 4*d + 6) + 1)) + Km
      + Kr * (((S+1)*(sz+2) + (S+1) + 1) + 1)
      + Kp * 4 + Kdl * (((S+1)*(sz+2) + (S+1) + 1) + 4)
      ≤ 1000 * (Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1) * (S * (d + 1) * (sz + 2) + 1) := by
  -- abbreviations: `S0 = ∑K + 1`, `X = S*(d+1)*(sz+2)`, `A`, `B`, `Q`
  set S0 := Ku + Ks + Kd + Km + Kr + Kp + Kdl + 1 with hS0
  set X := S * (d + 1) * (sz + 2) with hX
  set A := (3*d+4)*(sz+2) + 4*d + 6 with hA
  set B := A + 1 with hB
  set Q := ((S+1)*(sz+2) + (S+1) + 1) with hQ
  -- numeric side conditions
  have hS1 : S + 1 ≤ 2 * S := by omega
  have hA' : A ≤ 11*((d+1)*(sz+2)) := by rw [hA]; nlinarith
  have hB' : B ≤ 12*((d+1)*(sz+2)) := by rw [hB]; rw [hA]; nlinarith
  have h2a : (S+1)*A ≤ 22*X := by rw [hA, hX]; nlinarith [hS1]
  have h3a : (S+1)*B ≤ 24*X := by rw [hB, hA, hX]; nlinarith [hS1]
  have hXS : S + 1 ≤ X := by rw [hX]; nlinarith [hS1]
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith [hS]
  have hQ1 : Q + 1 ≤ 4*X := by rw [hQ, hX]; nlinarith [hS1]
  have hQ4 : Q + 4 ≤ 6*X := by rw [hQ, hX]; nlinarith [hS1]
  have hKu : Ku ≤ S0 := by omega
  have hKs : Ks ≤ S0 := by omega
  have hKd : Kd ≤ S0 := by omega
  have hKm : Km ≤ S0 := by omega
  have hKr : Kr ≤ S0 := by omega
  have hKp : Kp ≤ S0 := by omega
  have hKdl : Kdl ≤ S0 := by omega
  -- the eight summand bounds, each `≤ c * X * S0`
  have h1 : (S+1)*Ku ≤ X*S0 := by nlinarith [hXS, hKu]
  have h2 : (S+1)*Ks*A ≤ 22*X*S0 := by nlinarith [h2a, hKs]
  have h3 : (S+1)*Kd*B ≤ 24*X*S0 := by nlinarith [h3a, hKd]
  have h4 : (S+1)*Km*B ≤ 24*X*S0 := by nlinarith [h3a, hKm]
  have h5 : Km ≤ X*S0 := by nlinarith [hKm, hX1]
  have h6 : Kr*(Q+1) ≤ 4*X*S0 := by nlinarith [hQ1, hKr]
  have h7 : Kp*4 ≤ 4*X*S0 := by nlinarith [hKp, hX1]
  have h8 : Kdl*(Q+4) ≤ 6*X*S0 := by nlinarith [hQ4, hKdl]
  -- the constants fit: `1+22+24+24+1+4+4+6 = 86 ≤ 1000`
  have h9 : 86*X*S0 ≤ 1000*S0*(X+1) := by nlinarith
  nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9]

end Work.MainP
