import Mathlib

namespace Work.SynFFT

/-- Geometric / arithmetic domination lemma used by the `SynFFT` fold driver: the
capacity `V = 1000 * (Km + Kt + Ka + 1) * (M * (r + 1) * (p + 1) * (M.size + 2))`
dominates every quantity that occurs as a bound in the fold loop, given
`1 ≤ M`, `2 ≤ r`, `1 ≤ p` and `r < 2 ^ p`. -/
theorem axFoldVBounds (p r Km Kt Ka M V : ℕ)
    (hM : 1 ≤ M) (hr2 : 2 ≤ r) (hp1 : 1 ≤ p) (hrp : r < 2 ^ p)
    (hV : V = 1000 * (Km + Kt + Ka + 1) * (M * (r + 1) * (p + 1) * (M.size + 2))) :
    14 * (M * (r + 1) * (p + 1)) ≤ V ∧
    M.size + 2 ≤ V ∧
    p + 2 ≤ V ∧
    r.size + 2 ≤ V ∧
    3 ≤ V ∧
    Km * ((M.size + 2) * (M.size + 2)) ≤ V ∧
    Kt * ((M.size + 2) * (M.size + 2)) ≤ V ∧
    Ka * (M * (r + 1) * (p + 1) * (M.size + 2)) * 2 + Ka ≤ V ∧
    18 * (M + 1) ≤ V := by
  -- `Nat.size` is the binary length, so `M.size ≤ M` and `r.size ≤ p`.
  have hMs : M.size ≤ M := Nat.size_le.mpr (Nat.lt_two_pow_self (n := M))
  have hMs1 : 1 ≤ M.size := Nat.size_pos.mpr (by omega)
  have hrs : r.size ≤ p := Nat.size_le.mpr hrp
  have hr3 : 3 ≤ r + 1 := by omega
  have hp2 : 2 ≤ p + 1 := by omega
  -- abbreviations
  set S := M.size + 2 with hSdef
  set A := M * (r + 1) * (p + 1) with hAdef
  set K := Km + Kt + Ka + 1 with hKdef
  set X := A * S with hXdef
  -- now `hV : V = 1000 * K * X`
  have hS3 : 3 ≤ S := by omega
  have hS1000M : S ≤ 1000 * M := by omega
  have hK1 : 1 ≤ K := by omega
  have hKkm : Km ≤ K := by omega
  have hKkt : Kt ≤ K := by omega
  have hKka : Ka ≤ K := by omega
  have hA0 : 0 < A := by
    rw [hAdef]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hSX : S ≤ X := by
    rw [hXdef]
    exact Nat.le_mul_of_pos_left S hA0
  have hAX : A ≤ X := by
    rw [hXdef]
    exact Nat.le_mul_of_pos_right A (by omega : 0 < S)
  have hMA : M ≤ A := by
    rw [hAdef]
    have h1 : 1 ≤ (r + 1) * (p + 1) := by
      have := Nat.mul_le_mul (show 1 ≤ r + 1 by omega) (show 1 ≤ p + 1 by omega)
      simpa using this
    calc M = M * 1 := by ring
      _ ≤ M * ((r + 1) * (p + 1)) := Nat.mul_le_mul_left M h1
      _ = M * (r + 1) * (p + 1) := by ring
  have hMX : M * S ≤ X := by
    rw [hXdef]
    exact Nat.mul_le_mul_right S hMA
  have hX1 : 1 ≤ X := le_trans (by norm_num : 1 ≤ 3) (le_trans hS3 hSX)
  have hVlow : 1000 * X ≤ V := by
    rw [hV]
    calc 1000 * X ≤ 1000 * (K * X) :=
          Nat.mul_le_mul_left 1000 (Nat.le_mul_of_pos_left X (by omega : 0 < K))
      _ = 1000 * K * X := by ring
  have g1 : 14 * A ≤ V := by
    calc 14 * A ≤ 14 * X := Nat.mul_le_mul_left 14 hAX
      _ ≤ 1000 * X := Nat.mul_le_mul_right X (by norm_num)
      _ ≤ V := hVlow
  have g2 : S ≤ V :=
    le_trans hSX (le_trans (Nat.le_mul_of_pos_left X (by norm_num : 0 < 1000)) hVlow)
  have hA3p : 3 * (p + 1) ≤ A := by
    rw [hAdef]
    have h13 : 3 ≤ M * (r + 1) := by
      have := Nat.mul_le_mul hM hr3
      simpa using this
    exact Nat.mul_le_mul_right (p + 1) h13
  have hpX : p + 2 ≤ X := by
    calc p + 2 ≤ 9 * (p + 1) := by omega
      _ = (3 * (p + 1)) * 3 := by ring
      _ ≤ A * S := Nat.mul_le_mul hA3p hS3
      _ = X := hXdef.symm
  have g3 : p + 2 ≤ V :=
    le_trans hpX (le_trans (Nat.le_mul_of_pos_left X (by norm_num : 0 < 1000)) hVlow)
  have g4 : r.size + 2 ≤ V := le_trans (by omega : r.size + 2 ≤ p + 2) g3
  have g5 : 3 ≤ V :=
    le_trans (le_trans hS3 hSX)
      (le_trans (Nat.le_mul_of_pos_left X (by norm_num : 0 < 1000)) hVlow)
  have hSS : S * S ≤ 1000 * (M * S) := by
    calc S * S ≤ (1000 * M) * S := Nat.mul_le_mul hS1000M le_rfl
      _ = 1000 * (M * S) := by ring
  have g6 : Km * (S * S) ≤ V := by
    calc Km * (S * S) ≤ K * (S * S) := Nat.mul_le_mul_right (S * S) hKkm
      _ ≤ K * (1000 * (M * S)) := Nat.mul_le_mul_left K hSS
      _ ≤ K * (1000 * X) := Nat.mul_le_mul_left K (Nat.mul_le_mul_left 1000 hMX)
      _ = 1000 * K * X := by ring
      _ = V := hV.symm
  have g7 : Kt * (S * S) ≤ V := by
    calc Kt * (S * S) ≤ K * (S * S) := Nat.mul_le_mul_right (S * S) hKkt
      _ ≤ K * (1000 * (M * S)) := Nat.mul_le_mul_left K hSS
      _ ≤ K * (1000 * X) := Nat.mul_le_mul_left K (Nat.mul_le_mul_left 1000 hMX)
      _ = 1000 * K * X := by ring
      _ = V := hV.symm
  have h2X : 2 * X + 1 ≤ 1000 * X := by omega
  have g8 : Ka * X * 2 + Ka ≤ V := by
    calc Ka * X * 2 + Ka = Ka * (2 * X + 1) := by ring
      _ ≤ K * (2 * X + 1) := Nat.mul_le_mul_right (2 * X + 1) hKka
      _ ≤ K * (1000 * X) := Nat.mul_le_mul_left K h2X
      _ = 1000 * K * X := by ring
      _ = V := hV.symm
  have h18M : 18 * M ≤ X := by
    rw [hXdef]
    have hMr : 3 * M ≤ M * (r + 1) := by
      calc 3 * M = M * 3 := by ring
        _ ≤ M * (r + 1) := Nat.mul_le_mul_left M hr3
    have h6pS : 6 ≤ (p + 1) * S := Nat.mul_le_mul hp2 hS3
    calc 18 * M = (3 * M) * 6 := by ring
      _ ≤ (M * (r + 1)) * ((p + 1) * S) := Nat.mul_le_mul hMr h6pS
      _ = A * S := by rw [hAdef]; ring
  have g9 : 18 * (M + 1) ≤ V := by
    have h18 : 18 * (M + 1) ≤ 1000 * X := by
      calc 18 * (M + 1) ≤ 1000 * (18 * M) := by omega
        _ ≤ 1000 * X := Nat.mul_le_mul_left 1000 h18M
    exact le_trans h18 hVlow
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩

end Work.SynFFT
