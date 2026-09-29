import Mathlib
import Submission.Work.Layout.Shared
import Submission.Work.Params.steps
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.SB.kw1Sizes
import Submission.Work.SB.kw1Vsh

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 10000

namespace Work.SB

open HvdH
open Work.Layout
open Work.Params

theorem vsz_int' (z : ℤ) : vsz (.int z) = isz z := Work.IntLib.vsz_int z

theorem vsz_cons' (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

/-! ## Budget lemmas -/

theorem bd_mul {T W : ℕ} {K0 X Y : ℕ} (hK0 : K0 ≤ W) (hXY : X * Y ≤ 2 * T) :
    K0 * X * Y ≤ 1000 * W * T := by
  calc K0 * X * Y = (X * Y) * K0 := by ring
    _ ≤ (2 * T) * W := Nat.mul_le_mul hXY hK0
    _ = 2 * (W * T) := by ring
    _ ≤ 1000 * (W * T) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 1000 * W * T := by ring

theorem bd_sum {U T W : ℕ} (hUT : U ≤ T) {K0 X Y : ℕ} (hK0 : K0 ≤ W)
    (hXY : X + Y ≤ 2 * U) : K0 * (X + Y) ≤ 1000 * W * T := by
  calc K0 * (X + Y) ≤ K0 * (2 * U) := Nat.mul_le_mul_left K0 hXY
    _ = 2 * (K0 * U) := by ring
    _ ≤ 2 * (W * T) := by
        apply Nat.mul_le_mul_left
        calc K0 * U ≤ W * U := Nat.mul_le_mul_right U hK0
          _ ≤ W * T := Nat.mul_le_mul_left W hUT
    _ ≤ 1000 * (W * T) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 1000 * W * T := by ring

theorem bd_lin {U T W : ℕ} (hUT : U ≤ T) {K0 X : ℕ} (hK0 : K0 ≤ W) (hX : X ≤ 4 * U) :
    K0 * X ≤ 1000 * W * T := by
  calc K0 * X ≤ K0 * (4 * U) := Nat.mul_le_mul_left K0 hX
    _ = 4 * (K0 * U) := by ring
    _ ≤ 4 * (W * T) := by
        apply Nat.mul_le_mul_left
        calc K0 * U ≤ W * U := Nat.mul_le_mul_right U hK0
          _ ≤ W * T := Nat.mul_le_mul_left W hUT
    _ ≤ 1000 * (W * T) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 1000 * W * T := by ring

theorem bd_pick {U T W : ℕ} (hU1 : 1 ≤ U) (h189 : 189 * U ≤ 1000 * T) {K0 k s : ℕ}
    (hK0 : K0 ≤ W) (hk : k + 1 ≤ 9) (hs : s ≤ 20 * U) :
    K0 * (k + 1) * (s + 1) ≤ 1000 * W * T := by
  have h1 : s + 1 ≤ 21 * U := by omega
  have h2 : (k + 1) * (s + 1) ≤ 189 * U := by
    calc (k + 1) * (s + 1) ≤ 9 * (21 * U) := Nat.mul_le_mul hk h1
      _ = 189 * U := by ring
  calc K0 * (k + 1) * (s + 1) = K0 * ((k + 1) * (s + 1)) := by ring
    _ ≤ K0 * (189 * U) := Nat.mul_le_mul_left K0 h2
    _ ≤ W * (1000 * T) := Nat.mul_le_mul hK0 h189
    _ = 1000 * W * T := by ring

theorem bd_const {T W : ℕ} (hT1 : 1 ≤ T) {K0 : ℕ} (hK0 : K0 ≤ W) : K0 ≤ 1000 * W * T := by
  calc K0 ≤ W := hK0
    _ ≤ W * T := by
        calc W = W * 1 := by ring
          _ ≤ W * T := Nat.mul_le_mul_left W hT1
    _ ≤ 1000 * (W * T) := by
        calc W * T = 1 * (W * T) := by ring
          _ ≤ 1000 * (W * T) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 1000 * W * T := by ring

/-- Chain two `WordR` steps keeping the cost in the normal form `E * n`. -/
theorem seqU (hK : KernelLib) {main : Cmd} {p q : Cmd} {L M N : List Val} {E n : ℕ}
    (hp : WordR main p (fun vs => vs = L) (fun _ out => out = M) (fun _ => E * n))
    (hq : WordR main q (fun vs => vs = M) (fun _ out => out = N) (fun _ => E)) :
    WordR main (.seq p q) (fun vs => vs = L) (fun _ out => out = N) (fun _ => E * (n + 1)) := by
  have h := hK.seq main p q (fun vs => vs = L) (fun _ out => out = M) (fun _ => E * n)
      (fun vs => vs = M) (fun _ out => out = N) (fun _ => E) (fun _ => E) hp hq
      (fun vs mid _ h2 => ⟨h2, le_rfl⟩)
  refine hK.conseq main (.seq p q) (fun vs => vs = L) (fun vs => vs = L)
      (fun vs out => ∃ mid, mid = M ∧ out = N) (fun _ out => out = N)
      (fun _ => E * n + E) (fun _ => E * (n + 1)) h ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out _ hpost; obtain ⟨mid, _, h3⟩ := hpost; exact h3
  · intro vs _; rw [Nat.mul_succ]

theorem kw1Word (hK : HvdH.KernelLib) (hI : HvdH.IntLib) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (m B N Lin : ℕ) (i : ℤ) (v : Val) (tail : List Val),
      0 < m → 0 < B → 0 ≤ i → i.toNat < N → keyIdx1 m B i.toNat < N →
      isz (m : ℤ) ≤ Lin → isz (B : ℤ) ≤ Lin →
      vsz (.cons (.int i) v) ≤ Lin →
      vsz (Val.cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v) ≤ Lin + N.size + 2 ∧
      WordR main p
        (fun vs => vs = .cons (.int i) v :: .int (m : ℤ) :: .int (B : ℤ) :: tail)
        (fun _ out => out = .cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v ::
          .int (m : ℤ) :: .int (B : ℤ) :: tail)
        (fun _ => K * (Lin + N.size + 2) * (N.size + 2)) := by
  obtain ⟨dupP, Kdup, hdup⟩ := hK.dup
  obtain ⟨dropP, Kdr, hdrop⟩ := hK.drop
  obtain ⟨swapP, Ksw, hswap⟩ := hK.swap
  obtain ⟨pickP, Kpk, hpick⟩ := hK.pick
  obtain ⟨rollP, Krl, hroll⟩ := hK.roll
  obtain ⟨consP, Kcs, hcons⟩ := hK.consV
  obtain ⟨uncP, Kuc, hunc⟩ := hK.unconsV
  obtain ⟨addP, Kad, hadd⟩ := hI.add
  obtain ⟨mulP, Kml, hml⟩ := hI.mulS
  obtain ⟨fdivP, Kfd, hfd⟩ := hI.fdiv
  obtain ⟨fmodP, Kfm, hfm⟩ := hI.fmod
  set W : ℕ := 1000 * (Kdup + Kdr + Ksw + Kpk + Krl + Kcs + Kuc + Kad + Kml + Kfd + Kfm + 1)
    with hWdef
  refine ⟨(Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq (Cmd.seq uncP (pickP 3)) (pickP 1)) (fdivP)) (dupP)) (pickP 4)) (swapP)) (fdivP)) (pickP 4)) (rollP 2)) (fmodP)) (pickP 5)) (pickP 3)) (fmodP)) (pickP 2)) (pickP 7)) (mulP)) (rollP 1)) (addP)) (pickP 5)) (mulP)) (rollP 1)) (addP)) (rollP 1)) (dropP)) (rollP 1)) (dropP)) (consP)), 28 * 1000 * W + 1, ?_⟩
  intro main m B N Lin i v tail hm hB hi hiN hkN hLm hLB hLv
  obtain ⟨hV1, hIi, hQv, hBbv, hAv, hRv, hABv, hSsv, hSMv, hKv, hKeyEq, hFinalv⟩ :=
    kw1Sizes m B N Lin i v hm hB hi hiN hkN hLm hLB hLv
  set U : ℕ := Lin + N.size + 2 with hUdef
  set T : ℕ := U * (N.size + 2) with hTdef
  set E : ℕ := 1000 * W * T with hEdef
  have hU1 : 1 ≤ U := by rw [hUdef]; omega
  have hSU : N.size + 2 ≤ U := by rw [hUdef]; omega
  have hUT : U ≤ T := by
    rw [hTdef]
    calc U = U * 1 := by ring
      _ ≤ U * (N.size + 2) := Nat.mul_le_mul_left U (by omega)
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    calc (1:ℕ) = 1 * 1 := by ring
      _ ≤ U * (N.size + 2) := Nat.mul_le_mul hU1 (by omega)
  have hS3 : 3 ≤ N.size + 2 := by
    have hN : 0 < N := by omega
    have hNs : 0 < N.size := Nat.size_pos.mpr hN
    omega
  have h189 : 189 * U ≤ 1000 * T := by
    rw [hTdef]
    have h2 : 3 * U ≤ U * (N.size + 2) := by
      calc 3 * U = U * 3 := by ring
        _ ≤ U * (N.size + 2) := Nat.mul_le_mul_left U hS3
    calc 189 * U ≤ 3000 * U := Nat.mul_le_mul_right U (by norm_num)
      _ = 1000 * (3 * U) := by ring
      _ ≤ 1000 * (U * (N.size + 2)) := Nat.mul_le_mul_left 1000 h2
  have hBU : isz (B:ℤ) ≤ U := by omega
  have hmU : isz (m:ℤ) ≤ U := by omega
  have hVU : vsz v ≤ U := by omega
  have hprodT : ∀ {X Y : ℕ}, X ≤ N.size + 2 → Y ≤ U → X * Y ≤ 2 * T := by
    intro X Y hX hY
    have h1 : X * Y ≤ (N.size + 2) * U := Nat.mul_le_mul hX hY
    have h2 : (N.size + 2) * U ≤ 2 * T := by
      have h3 : (N.size + 2) * U = U * (N.size + 2) := by ring
      rw [h3, hTdef]
      calc U * (N.size + 2) = 1 * (U * (N.size + 2)) := by ring
        _ ≤ 2 * (U * (N.size + 2)) := Nat.mul_le_mul_right _ (by norm_num)
    omega
  have hprodT' : ∀ {X Y : ℕ}, X ≤ U → Y ≤ N.size + 2 → X * Y ≤ 2 * T := by
    intro X Y hX hY
    rw [mul_comm]
    exact hprodT hY hX
  have hsum2U : ∀ {X Y : ℕ}, X ≤ N.size + 2 → Y ≤ N.size + 2 → X + Y ≤ 2 * U := by
    intro X Y hX hY
    have h1 : X + Y ≤ (N.size + 2) + (N.size + 2) := add_le_add hX hY
    have h2 : (N.size + 2) + (N.size + 2) ≤ 2 * U := by omega
    omega
  have hWdup : Kdup ≤ W := by rw [hWdef]; omega
  have hWdr : Kdr ≤ W := by rw [hWdef]; omega
  have hWsw : Ksw ≤ W := by rw [hWdef]; omega
  have hWpk : Kpk ≤ W := by rw [hWdef]; omega
  have hWrl : Krl ≤ W := by rw [hWdef]; omega
  have hWcs : Kcs ≤ W := by rw [hWdef]; omega
  have hWuc : Kuc ≤ W := by rw [hWdef]; omega
  have hWad : Kad ≤ W := by rw [hWdef]; omega
  have hWml : Kml ≤ W := by rw [hWdef]; omega
  have hWfd : Kfd ≤ W := by rw [hWdef]; omega
  have hWfm : Kfm ≤ W := by rw [hWdef]; omega
  -- values
  set I0 : Val := .int i with hI0
  set V0 : Val := v with hV0
  set M0 : Val := .int (m : ℤ) with hM0
  set B0 : Val := .int (B : ℤ) with hB0
  set T0 : Val := .cons (.int i) v with hT0
  set Q : Val := .int (Int.fdiv i (B:ℤ)) with hQ
  set Bb : Val := .int (Int.fmod i (B:ℤ)) with hBb
  set A : Val := .int (Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) with hA
  set R : Val := .int (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ)) with hR
  set AB : Val := .int ((B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) with hAB
  set Ss : Val := .int (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)) with hSs
  set SM : Val :=
    .int ((m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))) with hSM
  set Key : Val :=
    .int (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ) +
      (m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))) with hKey
  set Finl : Val := .cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v with hFinl
  -- Z: all values occurring in the states
  set Z : List Val := [I0, V0, M0, B0, Q, Bb, A, R, AB, Ss, SM, Key] with hZdef
  have hpb : (0:ℤ) < (B:ℤ) := by exact_mod_cast hB
  have hpm : (0:ℤ) < (m:ℤ) := by exact_mod_cast hm
  have hZ : ∀ x ∈ Z, vsz x ≤ U := by
    intro x hx
    simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h, hI0, vsz_int']; omega
    · rw [h, hV0]; exact hVU
    · rw [h, hM0, vsz_int']; omega
    · rw [h, hB0, vsz_int']; omega
    · rw [h, hQ, vsz_int']; omega
    · rw [h, hBb, vsz_int']; omega
    · rw [h, hA, vsz_int']; omega
    · rw [h, hR, vsz_int']; omega
    · rw [h, hAB, vsz_int']; omega
    · rw [h, hSs, vsz_int']; omega
    · rw [h, hSM, vsz_int']; omega
    · rw [h, hKey, vsz_int']; omega
  have hvshP : ∀ (P : List Val) (n : ℕ), (∀ x ∈ P, x ∈ Z) → n ≤ P.length → n ≤ 20 →
      Work.Params.vsh n (P ++ tail) ≤ 20 * U := by
    intro P n hP hn hn20
    have hsub : ∀ x ∈ P, vsz x ≤ U := fun x hx => hZ x (hP x hx)
    have h := kw1Vsh (n := n) (Bv := U) (P := P) (Tr := tail) hn hsub
    have h2 : n * U ≤ 20 * U := Nat.mul_le_mul_right U hn20
    omega
  -- states
  set S0 : List Val := [T0, M0, B0] ++ tail with hS0
  set S1 : List Val := [I0, V0, M0, B0] ++ tail with hS1
  set S2 : List Val := [B0, I0, V0, M0, B0] ++ tail with hS2
  set S3 : List Val := [I0, B0, I0, V0, M0, B0] ++ tail with hS3
  set S4 : List Val := [Q, I0, V0, M0, B0] ++ tail with hS4
  set S5 : List Val := [Q, Q, I0, V0, M0, B0] ++ tail with hS5
  set S6 : List Val := [M0, Q, Q, I0, V0, M0, B0] ++ tail with hS6
  set S7 : List Val := [Q, M0, Q, I0, V0, M0, B0] ++ tail with hS7
  set S8 : List Val := [A, Q, I0, V0, M0, B0] ++ tail with hS8
  set S9 : List Val := [M0, A, Q, I0, V0, M0, B0] ++ tail with hS9
  set S10 : List Val := [Q, M0, A, I0, V0, M0, B0] ++ tail with hS10
  set S11 : List Val := [R, A, I0, V0, M0, B0] ++ tail with hS11
  set S12 : List Val := [B0, R, A, I0, V0, M0, B0] ++ tail with hS12
  set S13 : List Val := [I0, B0, R, A, I0, V0, M0, B0] ++ tail with hS13
  set S14 : List Val := [Bb, R, A, I0, V0, M0, B0] ++ tail with hS14
  set S15 : List Val := [A, Bb, R, A, I0, V0, M0, B0] ++ tail with hS15
  set S16 : List Val := [B0, A, Bb, R, A, I0, V0, M0, B0] ++ tail with hS16
  set S17 : List Val := [AB, Bb, R, A, I0, V0, M0, B0] ++ tail with hS17
  set S18 : List Val := [Bb, AB, R, A, I0, V0, M0, B0] ++ tail with hS18
  set S19 : List Val := [Ss, R, A, I0, V0, M0, B0] ++ tail with hS19
  set S20 : List Val := [M0, Ss, R, A, I0, V0, M0, B0] ++ tail with hS20
  set S21 : List Val := [SM, R, A, I0, V0, M0, B0] ++ tail with hS21
  set S22 : List Val := [R, SM, A, I0, V0, M0, B0] ++ tail with hS22
  set S23 : List Val := [Key, A, I0, V0, M0, B0] ++ tail with hS23
  set S24 : List Val := [A, Key, I0, V0, M0, B0] ++ tail with hS24
  set S25 : List Val := [Key, I0, V0, M0, B0] ++ tail with hS25
  set S26 : List Val := [I0, Key, V0, M0, B0] ++ tail with hS26
  set S27 : List Val := [Key, V0, M0, B0] ++ tail with hS27
  set S28 : List Val := [Finl, M0, B0] ++ tail with hS28
  -- the individual steps
  have hs1 : WordR main uncP (fun vs => vs = S0) (fun _ out => out = S1) (fun _ => 1000 * W * T) :=
    unconsVStep hK (hunc main) (.int i) v (M0 :: B0 :: tail) (1000 * W * T) (bd_const hT1 hWuc)
  have hs2 : WordR main (pickP 3) (fun vs => vs = S1) (fun _ out => out = S2)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 3 S1 (by rw [hS1]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [I0, V0, M0, B0] 4
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS1] using h))
  have hs3 : WordR main (pickP 1) (fun vs => vs = S2) (fun _ out => out = S3)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 1 S2 (by rw [hS2]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [B0, I0, V0, M0, B0] 2
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS2] using h))
  have hs4 : WordR main fdivP (fun vs => vs = S3) (fun _ out => out = S4)
      (fun _ => 1000 * W * T) :=
    binStep hK (hfd main) i (B:ℤ) (I0 :: V0 :: M0 :: B0 :: tail) hpb (1000 * W * T)
      (bd_mul hWfd (hprodT hIi hBU))
  have hs5 : WordR main dupP (fun vs => vs = S4) (fun _ out => out = S5)
      (fun _ => 1000 * W * T) :=
    dupStep hK (hdup main) Q (I0 :: V0 :: M0 :: B0 :: tail) (1000 * W * T)
      (bd_lin hUT hWdup (by rw [hQ, vsz_int']; omega))
  have hs6 : WordR main (pickP 4) (fun vs => vs = S5) (fun _ out => out = S6)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 4 S5 (by rw [hS5]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [Q, Q, I0, V0, M0, B0] 5
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS5] using h))
  have hs7 : WordR main swapP (fun vs => vs = S6) (fun _ out => out = S7)
      (fun _ => 1000 * W * T) :=
    swapStep hK (hswap main) M0 Q (Q :: I0 :: V0 :: M0 :: B0 :: tail) (1000 * W * T)
      (bd_lin hUT hWsw (by rw [hM0, hQ, vsz_int', vsz_int']; omega))
  have hs8 : WordR main fdivP (fun vs => vs = S7) (fun _ out => out = S8)
      (fun _ => 1000 * W * T) :=
    binStep hK (hfd main) (Int.fdiv i (B:ℤ)) (m:ℤ) (Q :: I0 :: V0 :: M0 :: B0 :: tail) hpm
      (1000 * W * T) (bd_mul hWfd (hprodT hQv hmU))
  have hs9 : WordR main (pickP 4) (fun vs => vs = S8) (fun _ out => out = S9)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 4 S8 (by rw [hS8]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [A, Q, I0, V0, M0, B0] 5
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS8] using h))
  have hs10 : WordR main (rollP 2) (fun vs => vs = S9) (fun _ out => out = S10)
      (fun _ => 1000 * W * T) :=
    rollStep hK (hroll main) 2 S9 (by rw [hS9]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWrl (by norm_num)
        (by have h := hvshP [M0, A, Q, I0, V0, M0, B0] 3
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS9] using h))
  have hs11 : WordR main fmodP (fun vs => vs = S10) (fun _ out => out = S11)
      (fun _ => 1000 * W * T) :=
    binStep hK (hfm main) (Int.fdiv i (B:ℤ)) (m:ℤ) (A :: I0 :: V0 :: M0 :: B0 :: tail) hpm
      (1000 * W * T) (bd_mul hWfm (hprodT hQv hmU))
  have hs12 : WordR main (pickP 5) (fun vs => vs = S11) (fun _ out => out = S12)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 5 S11 (by rw [hS11]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [R, A, I0, V0, M0, B0] 6
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS11] using h))
  have hs13 : WordR main (pickP 3) (fun vs => vs = S12) (fun _ out => out = S13)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 3 S12 (by rw [hS12]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [B0, R, A, I0, V0, M0, B0] 4
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS12] using h))
  have hs14 : WordR main fmodP (fun vs => vs = S13) (fun _ out => out = S14)
      (fun _ => 1000 * W * T) :=
    binStep hK (hfm main) i (B:ℤ) (R :: A :: I0 :: V0 :: M0 :: B0 :: tail) hpb (1000 * W * T)
      (bd_mul hWfm (hprodT hIi hBU))
  have hs15 : WordR main (pickP 2) (fun vs => vs = S14) (fun _ out => out = S15)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 2 S14 (by rw [hS14]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [Bb, R, A, I0, V0, M0, B0] 3
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS14] using h))
  have hs16 : WordR main (pickP 7) (fun vs => vs = S15) (fun _ out => out = S16)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 7 S15 (by rw [hS15]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [A, Bb, R, A, I0, V0, M0, B0] 8
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS15] using h))
  have hs17 : WordR main mulP (fun vs => vs = S16) (fun _ out => out = S17)
      (fun _ => 1000 * W * T) :=
    binStep hK (hml main) (B:ℤ) (Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))
      (Bb :: R :: A :: I0 :: V0 :: M0 :: B0 :: tail) trivial (1000 * W * T)
      (bd_mul hWml (hprodT' hBU hAv))
  have hs18 : WordR main (rollP 1) (fun vs => vs = S17) (fun _ out => out = S18)
      (fun _ => 1000 * W * T) :=
    rollStep hK (hroll main) 1 S17 (by rw [hS17]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWrl (by norm_num)
        (by have h := hvshP [AB, Bb, R, A, I0, V0, M0, B0] 2
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS17] using h))
  have hs19 : WordR main addP (fun vs => vs = S18) (fun _ out => out = S19)
      (fun _ => 1000 * W * T) :=
    binStep hK (hadd main) (Int.fmod i (B:ℤ)) ((B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))
      (R :: A :: I0 :: V0 :: M0 :: B0 :: tail) trivial (1000 * W * T)
      (bd_sum hUT hWad (hsum2U hBbv hABv))
  have hs20 : WordR main (pickP 5) (fun vs => vs = S19) (fun _ out => out = S20)
      (fun _ => 1000 * W * T) :=
    pickStep hK (hpick main) 5 S19 (by rw [hS19]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWpk (by norm_num)
        (by have h := hvshP [Ss, R, A, I0, V0, M0, B0] 6
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS19] using h))
  have hs21 : WordR main mulP (fun vs => vs = S20) (fun _ out => out = S21)
      (fun _ => 1000 * W * T) :=
    binStep hK (hml main) (m:ℤ)
      (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ))
      (R :: A :: I0 :: V0 :: M0 :: B0 :: tail) trivial (1000 * W * T)
      (bd_mul hWml (hprodT' hmU hSsv))
  have hs22 : WordR main (rollP 1) (fun vs => vs = S21) (fun _ out => out = S22)
      (fun _ => 1000 * W * T) :=
    rollStep hK (hroll main) 1 S21 (by rw [hS21]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWrl (by norm_num)
        (by have h := hvshP [SM, R, A, I0, V0, M0, B0] 2
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS21] using h))
  have hs23 : WordR main addP (fun vs => vs = S22) (fun _ out => out = S23)
      (fun _ => 1000 * W * T) :=
    binStep hK (hadd main) (Int.fmod (Int.fdiv i (B:ℤ)) (m:ℤ))
      ((m:ℤ) * (Int.fmod i (B:ℤ) + (B:ℤ) * Int.fdiv (Int.fdiv i (B:ℤ)) (m:ℤ)))
      (A :: I0 :: V0 :: M0 :: B0 :: tail) trivial (1000 * W * T)
      (bd_sum hUT hWad (hsum2U hRv hSMv))
  have hs24 : WordR main (rollP 1) (fun vs => vs = S23) (fun _ out => out = S24)
      (fun _ => 1000 * W * T) :=
    rollStep hK (hroll main) 1 S23 (by rw [hS23]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWrl (by norm_num)
        (by have h := hvshP [Key, A, I0, V0, M0, B0] 2
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS23] using h))
  have hs25 : WordR main dropP (fun vs => vs = S24) (fun _ out => out = S25)
      (fun _ => 1000 * W * T) :=
    dropStep hK (hdrop main) A (Key :: I0 :: V0 :: M0 :: B0 :: tail) (1000 * W * T)
      (bd_lin hUT hWdr (by rw [hA, vsz_int']; omega))
  have hs26 : WordR main (rollP 1) (fun vs => vs = S25) (fun _ out => out = S26)
      (fun _ => 1000 * W * T) :=
    rollStep hK (hroll main) 1 S25 (by rw [hS25]; simp) (1000 * W * T)
      (bd_pick hU1 h189 hWrl (by norm_num)
        (by have h := hvshP [Key, I0, V0, M0, B0] 2
              (by
      intro x hx
      simp only [hZdef, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h)))))))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      )
              (by simp) (by norm_num)
            simpa only [hS25] using h))
  have hs27 : WordR main dropP (fun vs => vs = S26) (fun _ out => out = S27)
      (fun _ => 1000 * W * T) :=
    dropStep hK (hdrop main) I0 (Key :: V0 :: M0 :: B0 :: tail) (1000 * W * T)
      (bd_lin hUT hWdr (by rw [hI0, vsz_int']; omega))
  have hs28 : WordR main consP (fun vs => vs = S27) (fun _ out => out = S28)
      (fun _ => 1000 * W * T) := by
    have hKk : Key = .int ((keyIdx1 m B i.toNat : ℕ) : ℤ) := by rw [hKey, hKeyEq]
    refine hK.conseq main consP (fun vs => vs = S27) (fun vs => vs = S27)
      (fun _ out => out = .cons Key V0 :: M0 :: B0 :: tail) (fun _ out => out = S28)
      (fun _ => 1000 * W * T) (fun _ => 1000 * W * T)
      (consVStep hK (hcons main) Key V0 (M0 :: B0 :: tail) (1000 * W * T) (bd_const hT1 hWcs))
      ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out hpre hpost
      rw [hpost, hS28]
      simp only [hFinl, hKk, hV0, List.cons_append, List.nil_append]
    · intro vs _; exact le_rfl
  have w1 : WordR main uncP (fun vs => vs = S0) (fun _ out => out = S1) (fun _ => E * 1) :=
    hK.conseq main uncP (fun vs => vs = S0) (fun vs => vs = S0) (fun _ out => out = S1)
      (fun _ out => out = S1) (fun _ => 1000 * W * T) (fun _ => E * 1) hs1
      (fun vs h => h) (fun vs out _ h => h) (fun vs _ => by rw [hEdef, Nat.mul_one])
  have w2 := seqU (n := 1) hK w1 hs2
  have w3 := seqU (n := 2) hK w2 hs3
  have w4 := seqU (n := 3) hK w3 hs4
  have w5 := seqU (n := 4) hK w4 hs5
  have w6 := seqU (n := 5) hK w5 hs6
  have w7 := seqU (n := 6) hK w6 hs7
  have w8 := seqU (n := 7) hK w7 hs8
  have w9 := seqU (n := 8) hK w8 hs9
  have w10 := seqU (n := 9) hK w9 hs10
  have w11 := seqU (n := 10) hK w10 hs11
  have w12 := seqU (n := 11) hK w11 hs12
  have w13 := seqU (n := 12) hK w12 hs13
  have w14 := seqU (n := 13) hK w13 hs14
  have w15 := seqU (n := 14) hK w14 hs15
  have w16 := seqU (n := 15) hK w15 hs16
  have w17 := seqU (n := 16) hK w16 hs17
  have w18 := seqU (n := 17) hK w17 hs18
  have w19 := seqU (n := 18) hK w18 hs19
  have w20 := seqU (n := 19) hK w19 hs20
  have w21 := seqU (n := 20) hK w20 hs21
  have w22 := seqU (n := 21) hK w21 hs22
  have w23 := seqU (n := 22) hK w22 hs23
  have w24 := seqU (n := 23) hK w23 hs24
  have w25 := seqU (n := 24) hK w24 hs25
  have w26 := seqU (n := 25) hK w25 hs26
  have w27 := seqU (n := 26) hK w26 hs27
  have w28 := seqU (n := 27) hK w27 hs28

  constructor
  · exact hFinalv
  · refine hK.conseq main _ (fun vs => vs = S0)
      (fun vs => vs = .cons (.int i) v :: .int (m : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ out => out = S28)
      (fun _ out => out = .cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v ::
        .int (m : ℤ) :: .int (B : ℤ) :: tail)
      _ (fun _ => (28 * 1000 * W + 1) * (Lin + N.size + 2) * (N.size + 2)) w28 ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [hS0, hT0, hM0, hB0, List.cons_append, List.nil_append]
    · intro vs out _ hpost
      rw [hpost]
      simp only [hS28, hFinl, hM0, hB0, List.cons_append, List.nil_append]
    · intro vs _
      have h28 : E * 28 ≤ (28 * 1000 * W + 1) * (Lin + N.size + 2) * (N.size + 2) := by
        rw [hEdef]
        have hT2 : T = (Lin + N.size + 2) * (N.size + 2) := by rw [hTdef]
        rw [hT2]
        rw [show (1000 * W * ((Lin + N.size + 2) * (N.size + 2))) * 28
            = (28 * 1000 * W) * ((Lin + N.size + 2) * (N.size + 2)) by ring]
        rw [show (28 * 1000 * W + 1) * (Lin + N.size + 2) * (N.size + 2)
            = (28 * 1000 * W + 1) * ((Lin + N.size + 2) * (N.size + 2)) by ring]
        exact Nat.mul_le_mul_right _ (Nat.le_succ _)
      exact h28

end Work.SB
