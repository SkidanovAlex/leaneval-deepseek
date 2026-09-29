import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.SB.Core.sortedLabelledEq
import Submission.Work.SB.Core.slicesFlattenEq
import Submission.Work.SB.Core.kw1MapStage
import Submission.Work.SB.Core.sortStripStage

set_option autoImplicit false

namespace Work.SB

open HvdH
open Work.Layout

/-! ## Elementary size facts -/

theorem vsz_cons_eq (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, List.length_append]

theorem vsz_int_eq (z : ℤ) : vsz (.int z) = isz z := Work.IntLib.vsz_int z

theorem vsz_ofList_eq (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      show vsz (Val.cons x (ofList xs)) = (List.map vsz (x :: xs)).sum + (x :: xs).length + 1
      rw [vsz_cons_eq, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

theorem isz_nat_le (k N : ℕ) (h : k ≤ N) : isz ((k : ℕ) : ℤ) ≤ N.size + 2 := by
  have h1 : k.size ≤ N.size := Nat.size_le_size h
  simp only [isz, Int.natAbs_natCast]
  omega

theorem getD_mem_le (es : List Val) (L : ℕ) (hv : ∀ x ∈ es, vsz x ≤ L) (i : ℕ)
    (hi : i < es.length) : vsz (es.getD i .nil) ≤ L := by
  rw [List.getD_eq_getElem es .nil hi]
  exact hv _ (List.getElem_mem hi)

/-! ## The key index map -/

theorem keyIdx1_lt (A m B i : ℕ) (hm : 0 < m) (hB : 0 < B) (hi : i < A * m * B) :
    keyIdx1 m B i < A * m * B := by
  have hmB : 0 < m * B := Nat.mul_pos hm hB
  have h1 : i / (m * B) < A := by
    rw [Nat.div_lt_iff_lt_mul hmB]
    calc i < A * m * B := hi
      _ = A * (m * B) := by ring
  have h2 : i % B < B := Nat.mod_lt _ hB
  have h3 : i / B % m < m := Nat.mod_lt _ hm
  have ha : i / (m * B) * B + i % B + 1 ≤ A * B := by
    have h4 : (i / (m * B) + 1) * B ≤ A * B :=
      Nat.mul_le_mul_right B (Nat.succ_le_of_lt h1)
    have h5 : (i / (m * B) + 1) * B = i / (m * B) * B + B := by ring
    rw [h5] at h4
    have h6 : i % B + 1 ≤ B := Nat.succ_le_of_lt h2
    omega
  refine Nat.lt_of_succ_le ?_
  calc keyIdx1 m B i + 1
      = (i / (m * B) * B + i % B) * m + i / B % m + 1 := rfl
    _ ≤ (i / (m * B) * B + i % B) * m + m := by omega
    _ = (i / (m * B) * B + i % B + 1) * m := by ring
    _ ≤ (A * B) * m := Nat.mul_le_mul_right m ha
    _ = A * m * B := by ring

theorem keyIdx1_inj (m B : ℕ) (hm : 0 < m) (hB : 0 < B) : Function.Injective (keyIdx1 m B) := by
  intro i j hij
  have h1 := invIdx1_keyIdx1 m B i hm hB
  have h2 := invIdx1_keyIdx1 m B j hm hB
  rw [hij, h2] at h1
  exact h1.symm

/-! ## Cost parameters -/

def phaseL (N L : ℕ) : ℕ := L + 2 * N.size + 5

theorem phaseL_ge (N L : ℕ) : L ≤ phaseL N L := by
  simp only [phaseL]; omega

theorem phaseL_add_bound (N L : ℕ) : phaseL N L + N.size + 1 ≤ 8 * (L + N.size + 1) := by
  simp only [phaseL]; omega

theorem cost_phaseL (K N L : ℕ) :
    K * (N + 1) * (phaseL N L + N.size + 1) * (N.size + 1)
      ≤ 8 * (K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  have h := phaseL_add_bound N L
  calc K * (N + 1) * (phaseL N L + N.size + 1) * (N.size + 1)
      ≤ K * (N + 1) * (8 * (L + N.size + 1)) * (N.size + 1) :=
        Nat.mul_le_mul_right (N.size + 1) (Nat.mul_le_mul_left (K * (N + 1)) h)
    _ = 8 * (K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by ring

theorem enumSizeBound (N L : ℕ) (es : List Val) (hN : es.length ≤ N) (hv : ∀ x ∈ es, vsz x ≤ L) :
    vsz (ofList es) + es.length * (es.length.size + 1) + 1 ≤
      2 * ((N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  have hsum : (es.map vsz).sum ≤ es.length * L := by
    calc (es.map vsz).sum ≤ (es.map (fun _ => L)).sum := List.sum_le_sum (fun x hx => hv x hx)
      _ = es.length * L := by simp [List.sum_replicate, Nat.mul_comm]
  have hsz : vsz (ofList es) ≤ (N + 1) * (L + 1) := by
    rw [vsz_ofList_eq]
    have h4 : es.length * L + es.length ≤ N * L + N := by
      calc es.length * L + es.length = es.length * (L + 1) := by ring
        _ ≤ N * (L + 1) := Nat.mul_le_mul hN (le_refl _)
        _ = N * L + N := by ring
    have h5 : es.length * L + es.length + 1 ≤ (N + 1) * (L + 1) := by
      calc es.length * L + es.length + 1 ≤ N * L + N + 1 := by omega
        _ ≤ N * L + N + L + 1 := by omega
        _ = (N + 1) * (L + 1) := by ring
    omega
  have hlen' : es.length * (es.length.size + 1) + 1 ≤ (N + 1) * (N.size + 1) := by
    have h2 : es.length.size + 1 ≤ N.size + 1 := by
      have := Nat.size_le_size hN
      omega
    have h3 : es.length * (es.length.size + 1) ≤ N * (N.size + 1) := Nat.mul_le_mul hN h2
    calc es.length * (es.length.size + 1) + 1 ≤ N * (N.size + 1) + (N.size + 1) := by omega
      _ = (N + 1) * (N.size + 1) := by ring
  have he1 : (N + 1) * (L + 1) ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := by
    have h2 : L + 1 ≤ L + N.size + 1 := by omega
    have h3 : (N + 1) * (L + 1) ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul_left _ h2
    have h4 : (N + 1) * (L + N.size + 1) ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := by
      calc (N + 1) * (L + N.size + 1) = (N + 1) * (L + N.size + 1) * 1 := by ring
        _ ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := Nat.mul_le_mul_left _ (by omega)
    exact le_trans h3 h4
  have he2 : (N + 1) * (N.size + 1) ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := by
    have h3 : N + 1 ≤ (N + 1) * (L + N.size + 1) := by
      calc N + 1 = (N + 1) * 1 := by ring
        _ ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul_left _ (by omega)
    exact Nat.mul_le_mul_right _ h3
  have h1 : vsz (ofList es) ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := le_trans hsz he1
  have h2 : es.length * (es.length.size + 1) + 1
      ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) := le_trans hlen' he2
  have h3 : vsz (ofList es) + (es.length * (es.length.size + 1) + 1)
      ≤ ((N + 1) * (L + N.size + 1) * (N.size + 1))
        + ((N + 1) * (L + N.size + 1) * (N.size + 1)) := Nat.add_le_add h1 h2
  calc vsz (ofList es) + es.length * (es.length.size + 1) + 1
      = vsz (ofList es) + (es.length * (es.length.size + 1) + 1) := by ring
    _ ≤ ((N + 1) * (L + N.size + 1) * (N.size + 1))
        + ((N + 1) * (L + N.size + 1) * (N.size + 1)) := h3
    _ = 2 * ((N + 1) * (L + N.size + 1) * (N.size + 1)) := by ring

/-! ## The enumerate stage -/

theorem enumStage (hEn : EnumerateSpec) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es rest : List Val),
      0 < m → 0 < B → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => out = ofList ((List.range (A * m * B)).map
            (fun i => Val.cons (.int ((i : ℕ) : ℤ)) (es.getD i .nil))) ::
          .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  obtain ⟨p, K0, hspec⟩ := hEn
  refine ⟨p, 2 * K0 + 1, ?_⟩
  intro main A m B N L es rest hm hB hN hlen hv
  have hb := enumSizeBound N L es (by omega) hv
  intro vs hvs s R hs
  subst hvs
  obtain ⟨out, s', n, hpost, hev, hle, hstk, hfr⟩ :=
    hspec main es (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
      ⟨.int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest, rfl⟩ s R hs
  obtain ⟨r, hr, hout⟩ := hpost
  have hr' : r = .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest := by
    injection hr with _ h
    exact h.symm
  refine ⟨out, s', n, ?_, hev, ?_, ?_, hfr⟩
  · rw [hout, hlen, hr']
  · show n ≤ (2 * K0 + 1) * (N + 1) * (L + N.size + 1) * (N.size + 1)
    calc n ≤ K0 * (vsz (ofList es) + es.length * (es.length.size + 1) + 1) := hle
      _ ≤ K0 * (2 * ((N + 1) * (L + N.size + 1) * (N.size + 1))) := Nat.mul_le_mul_left K0 hb
      _ = 2 * K0 * ((N + 1) * (L + N.size + 1) * (N.size + 1)) := by ring
      _ ≤ (2 * K0 + 1) * ((N + 1) * (L + N.size + 1) * (N.size + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (2 * K0 + 1) * (N + 1) * (L + N.size + 1) * (N.size + 1) := by ring
  · rw [hstk, hout, hlen, hr']

/-! ## Facts about the two labelled lists -/

theorem enumList_length (A m B : ℕ) (es : List Val) :
    ((List.range (A * m * B)).map (fun i => Val.cons (.int ((i : ℕ) : ℤ)) (es.getD i .nil))).length
      = A * m * B := by
  simp

theorem enumList_vsz_le (A m B N L : ℕ) (es : List Val) (hN : A * m * B ≤ N)
    (hlen : es.length = A * m * B) (hv : ∀ x ∈ es, vsz x ≤ L) (x : Val)
    (hx : x ∈ (List.range (A * m * B)).map (fun i => Val.cons (.int ((i : ℕ) : ℤ)) (es.getD i .nil))) :
    vsz x ≤ phaseL N L := by
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have h1 : isz ((i : ℕ) : ℤ) ≤ N.size + 2 := isz_nat_le i N (le_trans (Nat.le_of_lt hi) hN)
  have h2 : vsz (es.getD i .nil) ≤ L := getD_mem_le es L hv i (by omega)
  rw [vsz_cons_eq, vsz_int_eq]
  simp only [phaseL]
  omega

theorem kwList_length (A m B : ℕ) (es : List Val) :
    ((List.range (A * m * B)).map
      (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))).length = A * m * B := by
  simp

theorem kwList_vsz_le (A m B N L : ℕ) (es : List Val) (hm : 0 < m) (hB : 0 < B)
    (hN : A * m * B ≤ N) (hlen : es.length = A * m * B) (hv : ∀ x ∈ es, vsz x ≤ L) (x : Val)
    (hx : x ∈ (List.range (A * m * B)).map
      (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) :
    vsz x ≤ phaseL N L := by
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hlt := keyIdx1_lt A m B i hm hB hi
  have h1 : isz ((keyIdx1 m B i : ℕ) : ℤ) ≤ N.size + 2 :=
    isz_nat_le _ N (le_trans (Nat.le_of_lt hlt) hN)
  have h2 : vsz (es.getD i .nil) ≤ L := getD_mem_le es L hv i (by omega)
  rw [vsz_cons_eq, vsz_int_eq]
  simp only [phaseL]
  omega

theorem kwList_shape (A m B : ℕ) (es : List Val) (x : Val)
    (hx : x ∈ (List.range (A * m * B)).map
      (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) :
    ∃ (k : ℕ) (v : Val), x = Val.cons (.int (k : ℤ)) v := by
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨keyIdx1 m B i, es.getD i .nil, rfl⟩

theorem kwList_nodup (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) (es : List Val) :
    (((List.range (A * m * B)).map
      (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))).map pairKey).Nodup := by
  have h2 : ((List.range (A * m * B)).map
        (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))).map pairKey
      = (List.range (A * m * B)).map (fun i : ℕ => ((keyIdx1 m B i : ℕ) : ℤ)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    rfl
  rw [h2]
  exact List.Nodup.map_on
    (fun a _ b _ hab => keyIdx1_inj m B hm hB (by exact_mod_cast hab)) List.nodup_range

/-! ## Assembly -/

theorem phase1 (hK : HvdH.KernelLib) (hEn : EnumerateSpec) (hSo : SortSpec) (hKw : Kw1Spec) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val) (rest : List Val),
      0 < m → 0 < B → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => out = ofList ((slices A m B es).flatten) ::
          .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  obtain ⟨p1, K1, h1⟩ := enumStage hEn
  obtain ⟨p2, K2, h2⟩ := Core.kw1MapStage hK hKw
  obtain ⟨p3, K3, h3⟩ := Core.sortStripStage hK hSo
  refine ⟨.seq (.seq p1 p2) p3, 8 * (K1 + K2 + K3) + 8, ?_⟩
  intro main A m B N L es rest hm hB hN hlen hv
  have hv' : ∀ x ∈ es, vsz x ≤ phaseL N L := fun x hx => le_trans (hv x hx) (phaseL_ge N L)
  intro vs hvs s R hs
  subst hvs
  -- stage 1: enumerate
  obtain ⟨o1, s1, n1, hP1, hev1, hle1, hstk1, hfr1⟩ :=
    h1 main A m B N (phaseL N L) es rest hm hB hN hlen hv'
      (ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) rfl s R hs
  have hs1 : s1.stk 0 = encs (ofList ((List.range (A * m * B)).map
      (fun i => Val.cons (.int ((i : ℕ) : ℤ)) (es.getD i .nil))) ::
      .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) ++ R := by
    rw [hstk1, hP1]
  -- stage 2: mapList with the kw1 element word
  obtain ⟨o2, s2, n2, hP2, hev2, hle2, hstk2, hfr2⟩ :=
    h2 main A m B N (phaseL N L) es rest hm hB hN hlen hv'
      (ofList ((List.range (A * m * B)).map
        (fun i => Val.cons (.int ((i : ℕ) : ℤ)) (es.getD i .nil))) ::
        .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) rfl s1 R hs1
  have hs2 : s2.stk 0 = encs (ofList ((List.range (A * m * B)).map
      (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) ::
      .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) ++ R := by
    rw [hstk2, hP2]
  -- stage 3: sort by key and strip the keys
  obtain ⟨o3, s3, n3, hP3, hev3, hle3, hstk3, hfr3⟩ :=
    h3 main A m B N (phaseL N L)
      ((List.range (A * m * B)).map
        (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) rest
      hN (kwList_length A m B es)
      (fun x hx => kwList_vsz_le A m B N L es hm hB hN hlen hv x hx)
      (fun x hx => kwList_shape A m B es x hx)
      (kwList_nodup A m B hm hB es)
      (ofList ((List.range (A * m * B)).map
        (fun i => Val.cons (.int ((keyIdx1 m B i : ℕ) : ℤ)) (es.getD i .nil))) ::
        .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest) rfl s2 R hs2
  obtain ⟨ys, hpermy, hsorty, hout3⟩ := hP3
  -- identify the sorted list with the flattened slices
  have hA := Core.sortedLabelledEq A m B hm hB es ys hlen hpermy hsorty
  have hB2 := Core.slicesFlattenEq A m B hm hB es hlen
  have hunlab : ys.map unlab = (slices A m B es).flatten := by
    rw [hA, hB2]
    simp only [List.map_map]
    apply List.map_congr_left
    intro t _
    rfl
  refine ⟨o3, s3, (n1 + n2) + n3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout3, hunlab]
  · exact Eval.seq (Eval.seq hev1 hev2) hev3
  · show n1 + n2 + n3 ≤ (8 * (K1 + K2 + K3) + 8) * (N + 1) * (L + N.size + 1) * (N.size + 1)
    have hc1 : n1 ≤ K1 * (N + 1) * (phaseL N L + N.size + 1) * (N.size + 1) := hle1
    have hc2 : n2 ≤ K2 * (N + 1) * (phaseL N L + N.size + 1) * (N.size + 1) := hle2
    have hc3 : n3 ≤ K3 * (N + 1) * (phaseL N L + N.size + 1) * (N.size + 1) := hle3
    have b1 := le_trans hc1 (cost_phaseL K1 N L)
    have b2 := le_trans hc2 (cost_phaseL K2 N L)
    have b3 := le_trans hc3 (cost_phaseL K3 N L)
    have hmid : n1 + n2 + n3
        ≤ 8 * (K1 * (N + 1) * (L + N.size + 1) * (N.size + 1))
          + (8 * (K2 * (N + 1) * (L + N.size + 1) * (N.size + 1))
            + 8 * (K3 * (N + 1) * (L + N.size + 1) * (N.size + 1))) := by omega
    have heq : 8 * (K1 * (N + 1) * (L + N.size + 1) * (N.size + 1))
          + (8 * (K2 * (N + 1) * (L + N.size + 1) * (N.size + 1))
            + 8 * (K3 * (N + 1) * (L + N.size + 1) * (N.size + 1)))
        = 8 * (K1 + K2 + K3) * (N + 1) * (L + N.size + 1) * (N.size + 1) := by ring
    have hle : 8 * (K1 + K2 + K3) * (N + 1) * (L + N.size + 1) * (N.size + 1)
        ≤ (8 * (K1 + K2 + K3) + 8) * (N + 1) * (L + N.size + 1) * (N.size + 1) :=
      Nat.mul_le_mul_right (N.size + 1)
        (Nat.mul_le_mul_right (L + N.size + 1)
          (Nat.mul_le_mul_right (N + 1) (by omega)))
    calc n1 + n2 + n3
        ≤ 8 * (K1 * (N + 1) * (L + N.size + 1) * (N.size + 1))
          + (8 * (K2 * (N + 1) * (L + N.size + 1) * (N.size + 1))
            + 8 * (K3 * (N + 1) * (L + N.size + 1) * (N.size + 1))) := hmid
      _ = 8 * (K1 + K2 + K3) * (N + 1) * (L + N.size + 1) * (N.size + 1) := heq
      _ ≤ (8 * (K1 + K2 + K3) + 8) * (N + 1) * (L + N.size + 1) * (N.size + 1) := hle
  · rw [hstk3, hout3, hunlab]
  · intro k hk
    rw [hfr3 k hk, hfr2 k hk, hfr1 k hk]

end Work.SB
