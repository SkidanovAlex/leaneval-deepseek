import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.SB.BW2.Defs
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.encodeNatBridge

/-!
# `Work.SB.BW2.swapChunksWord`

`KernelLib.swap` followed by a `ChunksSpec` word, on the value list

`ofList flat :: int m :: int B :: int A :: rest`.

The swap moves `int m` to the top, so the list becomes exactly the input shape
`int m :: ofList flat :: rest'` of the `ChunksSpec` word (with `rest' = int B :: int A :: rest`);
the two integers ride along in that `rest'` and reappear below the list of chunks.

Cost.  `swap` costs `Ks * (vsz (ofList flat) + isz m + 1) ≤ Ks * (2 * (Bg + Ss))` and
`chunksOf m` costs `Kc * (vsz (ofList flat) + (flat.length / m + 1) * isz m + 1) ≤ Kc * (3 * (Bg + Ss))`
by the size hypotheses (`1 ≤ Bg` makes `1 ≤ Bg + Ss`, so both sums fit), hence
`K = 2 * Ks + 3 * Kc` works.
-/

set_option autoImplicit false

namespace Work.SB.BW2

open HvdH

/-- Size of an integer value: `vsz (.int z) = isz z`. -/
theorem vsz_int_swapChunks (z : ℤ) : vsz (.int z) = isz z := by
  simpa [vsz] using Work.IntLib.vsz_int z

theorem swapChunksWord (hK : HvdH.KernelLib) (hCh : Work.Layout.ChunksSpec) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (m A B Bg Ss : ℕ) (flat : List HvdH.Val)
        (rest : List HvdH.Val),
      1 ≤ m → m ∣ flat.length → 1 ≤ Bg → HvdH.vsz (HvdH.ofList flat) ≤ Bg →
      HvdH.isz (m : ℤ) ≤ Ss → (flat.length / m + 1) * HvdH.isz (m : ℤ) ≤ Bg + Ss →
      HvdH.WordR main p
        (fun vs => vs = HvdH.ofList flat :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
          HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => out = HvdH.ofList ((List.range (flat.length / m)).map
            (fun i => HvdH.ofList ((flat.drop (i * m)).take m))) ::
          HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ => K * (Bg + Ss)) := by
  obtain ⟨chP, chK, hChSpec⟩ := hCh
  obtain ⟨swP, swK, hSw⟩ := hK.swap
  refine ⟨Cmd.seq swP chP, 2 * swK + 3 * chK, ?_⟩
  intro main m A B Bg Ss flat rest hm hdvd hBg hvsz hSz hprod
  -- the three value lists involved
  let VS : List Val := ofList flat :: Val.int (m : ℤ) :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest
  let MID : List Val := Val.int (m : ℤ) :: ofList flat :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest
  let CH : List Val :=
    (List.range (flat.length / m)).map (fun i => ofList ((flat.drop (i * m)).take m))
  let OUT : List Val := ofList CH :: Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest
  -- 1. the swap step, in the shape `VS ↦ MID`
  have hsw : WordR main swP (fun vs => vs = VS) (fun _ out => out = MID)
      (fun vs => swK * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)) := by
    refine Work.Kernel.WordR_conseq (hSw main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      show 2 ≤ (ofList flat :: Val.int (m : ℤ) :: Val.int (B : ℤ) :: Val.int (A : ℤ)
        :: rest).length
      simp only [List.length_cons]
      omega
    · intro vs out hvs hq
      obtain ⟨a, b, r, h1, h2⟩ := hq
      rw [hvs] at h1
      dsimp only [VS] at h1
      obtain ⟨h1a, h1b, h1r⟩ : ofList flat = a ∧ Val.int (m : ℤ) = b ∧
          Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest = r := by
        simpa [List.cons.injEq] using h1
      rw [← h1a, ← h1b, ← h1r] at h2
      exact h2
    · intro vs _
      exact le_rfl
  -- 2. the `ChunksSpec` word, in the shape `MID ↦ OUT`
  have hch : WordR main chP (fun vs => vs = MID) (fun _ out => out = OUT)
      (fun _ => chK * (vsz (ofList flat) + (flat.length / m + 1) * isz (m : ℤ) + 1)) := by
    refine Work.Kernel.WordR_conseq (hChSpec main m flat hm hdvd) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest, rfl⟩
    · intro vs out hvs hq
      obtain ⟨r, h1, h2⟩ := hq
      rw [hvs] at h1
      dsimp only [MID] at h1
      have h1r : Val.int (B : ℤ) :: Val.int (A : ℤ) :: rest = r := by
        simpa [List.cons.injEq] using h1
      rw [← h1r] at h2
      exact h2
    · intro vs _
      exact le_rfl
  -- 3. compose
  have hseq : WordR main (.seq swP chP) (fun vs => vs = VS) (fun _ out => out = OUT)
      (fun vs => swK * (vsz (vs.getD 0 .nil) + vsz (vs.getD 1 .nil) + 1)
        + chK * (3 * (Bg + Ss))) := by
    refine Work.Kernel.WordR_conseq
      (Work.Kernel.WordR_seq hsw hch (B := fun _ => chK * (3 * (Bg + Ss))) ?_) ?_ ?_ ?_
    · intro vs mid _ hmid
      refine ⟨hmid, ?_⟩
      apply Nat.mul_le_mul_left
      omega
    · intro vs hvs
      exact hvs
    · intro vs out _ hq
      obtain ⟨mid, -, hout⟩ := hq
      exact hout
    · intro vs _
      exact le_rfl
  -- 4. final cost bound
  refine Work.Kernel.WordR_conseq hseq ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out _ hout
    exact hout
  · intro vs hvs
    rw [hvs]
    have h1 : swK * (vsz (ofList flat) + isz (m : ℤ) + 1) ≤ swK * (2 * (Bg + Ss)) := by
      apply Nat.mul_le_mul_left
      omega
    simp only [List.getD_cons_zero, List.getD_cons_succ, vsz_int_swapChunks]
    calc swK * (vsz (ofList flat) + isz (m : ℤ) + 1) + chK * (3 * (Bg + Ss))
        ≤ swK * (2 * (Bg + Ss)) + chK * (3 * (Bg + Ss)) := Nat.add_le_add_right h1 _
      _ = (2 * swK + 3 * chK) * (Bg + Ss) := by ring

end Work.SB.BW2
