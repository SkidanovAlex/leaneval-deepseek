import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.phase1
import Submission.Work.SB.BW2.vszFlatChunks
import Submission.Work.SB.BW2.swapChunksWord
import Submission.Work.SB.BW2.dropTwoBelowWord

set_option autoImplicit false

/-!
# `bgenWord`: the generic branch of `branchWord2`

`Work.SB.BW2.bgenWord` is the `0 < m`, `B ≠ 0` branch of the `slices` word.  Starting from
`ofList es :: int m :: int B :: int A :: rest` (with `es.length = A*m*B ≤ N` and all entries of
size `≤ L`) it must produce `ofList ((slices A m B es).map ofList) :: rest` at cost
`K * BIG N L + K * S A m B`.

The word is the three-stage pipeline

* `phase1` (`Phase1Spec`): sort the `A*m*B` entries by their slice-major label and strip the
  labels, leaving the flattened slices `ofList flat :: int m :: int B :: int A :: rest`;
* `swap ; chunksOf m`: bring `int m` on top and split `flat` into its `A*B` blocks of length `m`,
  which are exactly the slices (one needs `chunksFlatten`: all slices have length `m`);
* `roll 2 ; drop ; roll 1 ; drop`: delete the two remaining integers `int B`, `int A` below the
  result.

`BIG` is the per-stage budget `(N+1)*(L+N.size+1)*(N.size+1)`, `S` the parameter-size budget
`isz A + isz m + isz B`; the finitely many "+1"s are absorbed by a single large `K`, so every
stage cost is dominated by `(Bg + Ss)` with `Bg := BIG N L`, `Ss := S A m B`.
-/

namespace Work.SB.BW2

open HvdH

/-! ## Arithmetic and size facts used by the cost analysis -/

theorem one_le_BIG (N L : ℕ) : 1 ≤ BIG N L := by
  simp only [BIG]
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

theorem iszA_le_S (A m B : ℕ) : isz (A : ℤ) ≤ S A m B := by
  simp only [S]; omega

theorem iszm_le_S (A m B : ℕ) : isz (m : ℤ) ≤ S A m B := by
  simp only [S]; omega

theorem iszB_le_S (A m B : ℕ) : isz (B : ℤ) ≤ S A m B := by
  simp only [S]; omega

theorem isz_nat_le_N (k N : ℕ) (h : k ≤ N) : isz (k : ℤ) ≤ N.size + 2 := by
  have h1 : k.size ≤ N.size := Nat.size_le_size h
  simp only [isz, Int.natAbs_natCast]
  omega

/-- `(A*B+1) * isz m` is dominated by `BIG N L + S A m B` as soon as `A*m*B ≤ N` and `m ≠ 0`:
either `A*B = 0`, in which case `isz m ≤ S A m B`, or `A*B ≥ 1` and then `m ≤ N`, so that
`A*B+1 ≤ N+1` and `isz m ≤ N.size + 2`. -/
theorem abMul_le (A m B N L : ℕ) (hm : 0 < m) (hAmB : A * m * B ≤ N) :
    (A * B + 1) * isz (m : ℤ) ≤ BIG N L + S A m B := by
  rcases Nat.eq_zero_or_pos (A * B) with h0 | hpos
  · have h1 : isz (m : ℤ) ≤ S A m B := iszm_le_S A m B
    rw [h0]
    simp only [Nat.zero_add, Nat.one_mul]
    omega
  · have hmN : m ≤ N := by
      calc m = 1 * m := (Nat.one_mul m).symm
        _ ≤ (A * B) * m := Nat.mul_le_mul_right m hpos
        _ = A * m * B := by ring
        _ ≤ N := hAmB
    have hNpos : 1 ≤ N := le_trans hm hmN
    have hNs : 1 ≤ N.size := by
      have h := Nat.size_le_size hNpos
      have h1 : Nat.size 1 = 1 := by decide
      omega
    have hABle : A * B ≤ N := by
      calc A * B = A * B * 1 := (Nat.mul_one _).symm
        _ ≤ A * B * m := Nat.mul_le_mul_left _ hm
        _ = A * m * B := by ring
        _ ≤ N := hAmB
    have hAB1 : A * B + 1 ≤ N + 1 := by omega
    have h2 : isz (m : ℤ) ≤ N.size + 2 := isz_nat_le_N m N hmN
    have h3 : (A * B + 1) * isz (m : ℤ) ≤ (N + 1) * (N.size + 2) := Nat.mul_le_mul hAB1 h2
    have h4 : (N + 1) * (N.size + 2) ≤ BIG N L := by
      have h5 : N.size + 2 ≤ (N.size + 1) * (N.size + 1) := by nlinarith
      have h6 : (N.size + 1) * (N.size + 1) ≤ (L + N.size + 1) * (N.size + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      calc (N + 1) * (N.size + 2) ≤ (N + 1) * ((L + N.size + 1) * (N.size + 1)) :=
            Nat.mul_le_mul_left _ (le_trans h5 h6)
        _ = BIG N L := by rw [BIG]; ring
    omega

/-! ## The assembled word -/

private theorem bgenWordAux (hK : HvdH.KernelLib)
    (hP1 : Work.Layout.Phase1Spec)
    (hSCW : ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (m A B Bg Ss : ℕ)
        (flat : List HvdH.Val) (rest : List HvdH.Val),
      1 ≤ m → m ∣ flat.length → 1 ≤ Bg → HvdH.vsz (HvdH.ofList flat) ≤ Bg →
      HvdH.isz (m : ℤ) ≤ Ss → (flat.length / m + 1) * HvdH.isz (m : ℤ) ≤ Bg + Ss →
      HvdH.WordR main p
        (fun vs => vs = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
          HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => out = HvdH.ofList ((List.range (flat.length / m)).map
            (fun i => HvdH.ofList ((flat.drop (i * m)).take m))) ::
          HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ => K * (Bg + Ss)))
    (hDTB : ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (a : HvdH.Val)
        (A B Bg Ss : ℕ) (rest : List HvdH.Val),
      1 ≤ Bg → HvdH.vsz a ≤ 4 * Bg → HvdH.isz (A : ℤ) ≤ Ss → HvdH.isz (B : ℤ) ≤ Ss →
      HvdH.WordR main p
        (fun vs => vs = a :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => out = a :: rest)
        (fun _ => K * (Bg + Ss)))
    (hVFC : ∀ (A m B N L : ℕ) (es : List HvdH.Val), 0 < m → A * m * B ≤ N →
      es.length = A * m * B → (∀ x ∈ es, HvdH.vsz x ≤ L) →
      (∀ x ∈ (HvdH.slices A m B es).flatten, HvdH.vsz x ≤ L) ∧
      HvdH.vsz (HvdH.ofList ((HvdH.slices A m B es).flatten)) ≤ Work.SB.BW2.BIG N L ∧
      HvdH.vsz (HvdH.ofList ((List.range ((HvdH.slices A m B es).flatten.length / m)).map
          (fun i => HvdH.ofList (((HvdH.slices A m B es).flatten.drop (i * m)).take m)))) ≤
        4 * Work.SB.BW2.BIG N L) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A m B N L : ℕ) (es rest : List HvdH.Val),
      0 < m → B ≠ 0 → A * m * B ≤ N → es.length = A * m * B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.WordR main p (Work.SB.BW2.Pre A m B es rest) (Work.SB.BW2.Post A m B es rest)
        (fun _ => K * Work.SB.BW2.BIG N L + K * Work.SB.BW2.S A m B) := by
  obtain ⟨pSw, KSw, hSw⟩ := hSCW
  obtain ⟨pDr, KDr, hDr⟩ := hDTB
  obtain ⟨p1, K1, h1⟩ := hP1
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq p1 pSw) pDr, K1 + KSw + 6 * KDr + 1, ?_⟩
  intro main A m B N L es rest hm hBne hAmB hlen hv
  have hB : 0 < B := Nat.pos_of_ne_zero hBne
  have hm1 : 1 ≤ m := hm
  set Bg : ℕ := BIG N L with hBg
  set Ss : ℕ := S A m B with hSs
  set flat : List HvdH.Val := (HvdH.slices A m B es).flatten with hflat
  set ch : List HvdH.Val := (List.range (flat.length / m)).map
      (fun i => HvdH.ofList ((flat.drop (i * m)).take m)) with hch
  set sls : List (List HvdH.Val) := (List.range (flat.length / m)).map
      (fun i => (flat.drop (i * m)).take m) with hsls
  -- ## the size facts
  have hBg1 : 1 ≤ Bg := by rw [hBg]; exact one_le_BIG N L
  have hV := hVFC A m B N L es hm hAmB hlen hv
  have hvf : HvdH.vsz (HvdH.ofList flat) ≤ Bg := by rw [hBg, hflat]; exact hV.2.1
  have hvc : HvdH.vsz (HvdH.ofList ch) ≤ 4 * Bg := by rw [hBg, hch, hflat]; exact hV.2.2
  have hiszm : HvdH.isz (m : ℤ) ≤ Ss := by rw [hSs]; exact iszm_le_S A m B
  have hiszA : HvdH.isz (A : ℤ) ≤ Ss := by rw [hSs]; exact iszA_le_S A m B
  have hiszB : HvdH.isz (B : ℤ) ≤ Ss := by rw [hSs]; exact iszB_le_S A m B
  have hflen : flat.length = A * m * B := by
    rw [hflat]; exact (Work.SB.slicesFacts A m B es).2.2.1
  have hdiv : m ∣ flat.length := ⟨A * B, by rw [hflen]; ring⟩
  have hquot : flat.length / m = A * B := by
    rw [hflen, show A * m * B = m * (A * B) from by ring, Nat.mul_div_cancel_left _ hm]
  have hab : (flat.length / m + 1) * HvdH.isz (m : ℤ) ≤ Bg + Ss := by
    rw [hquot, hBg, hSs]
    exact abMul_le A m B N L hm hAmB
  -- ## the list identifications
  have hmem : ∀ l ∈ HvdH.slices A m B es, l.length = m := by
    intro l hl
    rw [HvdH.slices] at hl
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hl
    simp
  have hslseq : sls = HvdH.slices A m B es := by
    rw [hsls, hflat]
    exact Work.SB.chunksFlatten (HvdH.slices A m B es) m hm hmem
  have hcheq : HvdH.ofList ch = HvdH.ofList (sls.map HvdH.ofList) := by
    rw [hch, hsls, List.map_map]
    rfl
  -- ## stage 1: the sort-based phase 1
  have hS1 : HvdH.WordR main p1 (Work.SB.BW2.Pre A m B es rest)
      (fun _ out => out = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
        HvdH.Val.int (A : ℤ) :: rest)
      (fun _ => K1 * Bg) := by
    refine hK.conseq main p1 _ _ _ _ _ _ (h1 main A m B N L es rest hm hB hAmB hlen hv) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hout; rw [hout, hflat]
    · intro vs _
      rw [hBg]
      exact le_of_eq (by rw [BIG]; ring)
  -- ## stage 2: swap and split into blocks of `m`
  have hS2 : HvdH.WordR main pSw
      (fun vs => vs = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
        HvdH.Val.int (A : ℤ) :: rest)
      (fun _ out => out = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (fun _ => KSw * (Bg + Ss)) := by
    refine hK.conseq main pSw _ _ _ _ _ _
      (hSw main m A B Bg Ss flat rest hm1 hdiv hBg1 hvf hiszm hab) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hout; rw [hout, hch]
    · intro vs _; exact le_rfl
  -- ## stage 3: drop the two remaining integers
  have hS3 : HvdH.WordR main pDr
      (fun vs => vs = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (fun _ out => out = HvdH.ofList ch :: rest)
      (fun _ => 6 * KDr * (Bg + Ss)) := by
    refine hK.conseq main pDr _ _ _ _ _ _
      (hDr main (HvdH.ofList ch) A B Bg Ss rest hBg1 hvc hiszA hiszB) ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hout; exact hout
    · intro vs _
      rw [show 6 * KDr * (Bg + Ss) = KDr * (6 * (Bg + Ss)) from by ring]
      exact Nat.mul_le_mul_left _ (by omega)
  -- ## chaining
  have hC1 : HvdH.WordR main (HvdH.Cmd.seq p1 pSw) (Work.SB.BW2.Pre A m B es rest)
      (fun _ out => ∃ mid : List HvdH.Val,
        mid = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
          HvdH.Val.int (A : ℤ) :: rest ∧
        out = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (fun _ => K1 * Bg + KSw * (Bg + Ss)) :=
    hK.seq (main := main) (p := p1) (q := pSw) (P := Work.SB.BW2.Pre A m B es rest)
      (Q := fun _ out => out = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
        HvdH.Val.int (A : ℤ) :: rest)
      (C := fun _ => K1 * Bg)
      (P' := fun vs => vs = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
        HvdH.Val.int (A : ℤ) :: rest)
      (Q' := fun _ out => out = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) ::
        HvdH.Val.int (A : ℤ) :: rest)
      (C' := fun _ => KSw * (Bg + Ss)) (B := fun _ => KSw * (Bg + Ss))
      hS1 hS2 (fun vs mid _ hQ => ⟨hQ, le_rfl⟩)
  have hC2 : HvdH.WordR main (HvdH.Cmd.seq p1 pSw) (Work.SB.BW2.Pre A m B es rest)
      (fun _ out => out = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (fun _ => K1 * Bg + KSw * (Bg + Ss)) := by
    refine hK.conseq main (HvdH.Cmd.seq p1 pSw) _ _ _ _ _ _ hC1 ?_ ?_ ?_
    · intro vs hvs; exact hvs
    · intro vs out _ hout
      obtain ⟨_, _, hout2⟩ := hout
      exact hout2
    · intro vs _; exact le_rfl
  have hC3 : HvdH.WordR main (HvdH.Cmd.seq (HvdH.Cmd.seq p1 pSw) pDr)
      (Work.SB.BW2.Pre A m B es rest)
      (fun _ out => ∃ mid : List HvdH.Val,
        mid = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest ∧
        out = HvdH.ofList ch :: rest)
      (fun _ => K1 * Bg + KSw * (Bg + Ss) + 6 * KDr * (Bg + Ss)) :=
    hK.seq (main := main) (p := HvdH.Cmd.seq p1 pSw) (q := pDr) (P := Work.SB.BW2.Pre A m B es rest)
      (Q := fun _ out => out = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (C := fun _ => K1 * Bg + KSw * (Bg + Ss))
      (P' := fun vs => vs = HvdH.ofList ch :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
      (Q' := fun _ out => out = HvdH.ofList ch :: rest)
      (C' := fun _ => 6 * KDr * (Bg + Ss)) (B := fun _ => 6 * KDr * (Bg + Ss))
      hC2 hS3 (fun vs mid _ hQ => ⟨hQ, le_rfl⟩)
  refine hK.conseq main (HvdH.Cmd.seq (HvdH.Cmd.seq p1 pSw) pDr) _ _ _ _ _ _ hC3
    (fun vs hvs => hvs) ?_ ?_
  · intro vs out _ hout
    obtain ⟨_, _, hout2⟩ := hout
    refine ⟨sls, ?_, hslseq⟩
    rw [hout2, hcheq]
  · intro vs _
    rw [hBg, hSs]
    calc K1 * BIG N L + KSw * (BIG N L + S A m B) + 6 * KDr * (BIG N L + S A m B)
        ≤ K1 * (BIG N L + S A m B) + KSw * (BIG N L + S A m B)
          + 6 * KDr * (BIG N L + S A m B) :=
          Nat.add_le_add (Nat.add_le_add_right
            (Nat.mul_le_mul_left K1 (Nat.le_add_right (BIG N L) (S A m B))) _) le_rfl
      _ = (K1 + KSw + 6 * KDr) * (BIG N L + S A m B) := by ring
      _ ≤ (K1 + KSw + 6 * KDr + 1) * (BIG N L + S A m B) := Nat.mul_le_mul_right _ (by omega)
      _ = (K1 + KSw + 6 * KDr + 1) * BIG N L + (K1 + KSw + 6 * KDr + 1) * S A m B :=
          Nat.mul_add ..

theorem bgenWord (hK : HvdH.KernelLib) (hCh : Work.Layout.ChunksSpec)
    (hP1 : Work.Layout.Phase1Spec) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A m B N L : ℕ) (es rest : List HvdH.Val),
      0 < m → B ≠ 0 → A * m * B ≤ N → es.length = A * m * B →
      (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.WordR main p (Work.SB.BW2.Pre A m B es rest) (Work.SB.BW2.Post A m B es rest)
        (fun _ => K * Work.SB.BW2.BIG N L + K * Work.SB.BW2.S A m B) :=
  bgenWordAux hK hP1 (swapChunksWord hK hCh) (dropTwoBelowWord hK) vszFlatChunks

end Work.SB.BW2
