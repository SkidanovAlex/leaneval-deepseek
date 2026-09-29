import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.unslicesIdx
import Submission.Work.SB.P3.stripFromKernel
import Submission.Work.SB.P3.keyNodup
import Submission.Work.SB.unslicesFacts
import Submission.Work.IntLib.encodeNatBridge
import Submission.Work.SB.P3b.flatLen
import Submission.Work.SB.P3b.flatGetD
import Submission.Work.SB.P3b.tgtIdxKeyLt
import Submission.Work.SB.P3b.forall2Map

namespace Work.SB

open HvdH
open Work.Layout

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Supporting facts

`vsz` of an `ofList` and a general sum bound; both are used by the cost estimate below.
-/

private theorem p3b_vsz_ofList (l : List Val) : vsz (ofList l) = (l.map vsz).sum + l.length + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
      have h : ofList (x :: xs) = Val.cons x (ofList xs) := rfl
      rw [h, Work.SB.P3.vsz_cons, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

private theorem p3b_sum_le_card_mul (l : List Val) (f : Val → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) : (l.map f).sum ≤ l.length * c := by
  have h1 : (l.map f).sum ≤ (l.map (fun _ => c)).sum := List.sum_le_sum (fun x hx => h x hx)
  have h2 : (l.map (fun _ : Val => c)).sum = l.length * c := by
    rw [show (fun _ : Val => c) = Function.const Val c from rfl, List.map_const,
      List.sum_replicate]
    simp
  omega

/-- The cost bookkeeping of the second phase of the sort-based `applyAlong`: the sum of the five
stage costs implied by the `K`s of the individual words is bounded by `K * (N+1) * (L+N.size+1)
* (N.size+1)` for a constant `K` depending only on those.  The hypotheses are the *size* facts
about the input/output slices; no positivity of `n`/`B` is needed (the degenerate case
`A*B*n = 0` is covered, where all lists are empty). -/
theorem p3b_costBound_local (Kfl Ken Kso Kml Kkw Kst : ℕ) :
    ∃ K : ℕ, ∀ (A n B N L : ℕ) (outs : List (List Val)) (ys0 : List Val),
      A * B ≤ N → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      ys0.length = A * B * n →
      (∀ y ∈ ys0, vsz y ≤ L + N.size + 4 + N.size + 2) →
      Kfl * (vsz (ofList (outs.map ofList)) + 1)
      + (Ken * (vsz (ofList outs.flatten) + outs.flatten.length * (outs.flatten.length.size + 1) + 1)
      + ((A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml
      + (Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
      + ((A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml))))
      ≤ K * (N + 1) * (L + N.size + 1) * (N.size + 1) := by
  set C : ℕ := Kfl + Ken + Kso + Kml + Kkw + Kst + 1 with hCdef
  refine ⟨128 * C, ?_⟩
  intro A n B N L outs ys0 hAB hN hlen hsl hsz hys0len hys0sz
  set M : ℕ := (N + 1) * ((L + N.size + 1) * (N.size + 1)) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    have h2 : 1 ≤ (L + N.size + 1) * (N.size + 1) := Nat.mul_pos (by omega) (by omega)
    exact Nat.mul_pos (by omega) h2
  -- the entries of `outs` have length `n` and entries of size `≤ L`
  have hmem : ∀ x ∈ outs, x.length = n ∧ ∀ y ∈ x, vsz y ≤ L := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hx
    have hsAB : s < A * B := by rw [← hlen]; exact hs
    have h1 : outs.getD s [] = outs[s] := List.getD_eq_getElem outs [] hs
    exact ⟨by rw [← h1]; exact hsl s hsAB,
      fun y hy => hsz s hsAB y (by rw [h1]; exact hy)⟩
  have hflatmem : ∀ y ∈ outs.flatten, vsz y ≤ L := by
    intro y hy
    rw [List.mem_flatten] at hy
    obtain ⟨sl, hslmem, hy⟩ := hy
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hslmem
    have hsAB : s < A * B := by rw [← hlen]; exact hs
    have h1 : outs.getD s [] = outs[s] := List.getD_eq_getElem outs [] hs
    exact hsz s hsAB y (by rw [h1]; exact hy)
  have hlenflat : outs.flatten.length = A * B * n := P3b.flatLen A n B outs hlen hsl
  have hlf : outs.flatten.length ≤ N := by rw [hlenflat]; exact hN
  have hlfns : outs.flatten.length.size + 1 ≤ N.size + 1 := by
    have := Nat.size_le_size hlf
    omega
  have hY3 : ys0.length.size + 1 ≤ N.size + 1 := by
    have h : ys0.length ≤ N := by rw [hys0len]; exact hN
    have := Nat.size_le_size h
    omega
  -- size of the value `ofList (outs.map ofList)`
  have hS1 : vsz (ofList (outs.map ofList)) ≤ N * L + 3 * N + 1 := by
    rw [p3b_vsz_ofList, List.length_map, hlen]
    have hper : ∀ x ∈ outs.map ofList, vsz x ≤ n * L + n + 1 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨xl, hxl, rfl⟩ := hx
      obtain ⟨hlenx, hszx⟩ := hmem xl hxl
      have h2 : (xl.map vsz).sum ≤ xl.length * L := p3b_sum_le_card_mul xl vsz L hszx
      rw [hlenx] at h2
      rw [p3b_vsz_ofList, hlenx]
      omega
    have hsum := p3b_sum_le_card_mul (outs.map ofList) vsz (n * L + n + 1) hper
    rw [List.length_map, hlen] at hsum
    have h1 : A * B * (n * L + n + 1) = A * B * n * L + A * B * n + A * B := by ring
    rw [h1] at hsum
    have h2 : A * B * n * L ≤ N * L := Nat.mul_le_mul_right L hN
    omega
  -- size of the flattened output slices
  have hS2 : vsz (ofList outs.flatten) ≤ N * L + N + 1 := by
    rw [p3b_vsz_ofList]
    have hsum := p3b_sum_le_card_mul outs.flatten vsz L hflatmem
    rw [hlenflat] at hsum
    have h2 : A * B * n * L ≤ N * L := Nat.mul_le_mul_right L hN
    omega
  -- size of the labelled list
  have hS3 : vsz (ofList ys0) ≤ N * (L + 2 * N.size + 7) + N + 1 := by
    rw [p3b_vsz_ofList]
    have hper : ∀ y ∈ ys0, vsz y ≤ L + 2 * N.size + 6 := by
      intro y hy
      have := hys0sz y hy
      omega
    have hsum := p3b_sum_le_card_mul ys0 vsz (L + 2 * N.size + 6) hper
    rw [hys0len] at hsum
    have h2 : A * B * n * (L + 2 * N.size + 6) ≤ N * (L + 2 * N.size + 6) :=
      Nat.mul_le_mul_right _ hN
    have h3 : N * (L + 2 * N.size + 6) ≤ N * (L + 2 * N.size + 7) :=
      Nat.mul_le_mul_left N (by omega)
    omega
  -- product bounds against `M`
  have hNL_M : N * L ≤ M := by
    rw [hMdef]
    calc N * L ≤ N * (L + N.size + 1) := Nat.mul_le_mul_left N (by omega)
      _ ≤ (N + 1) * (L + N.size + 1) := Nat.mul_le_mul (by omega) (le_refl _)
      _ ≤ (N + 1) * ((L + N.size + 1) * (N.size + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
  have hN1_M : N + 1 ≤ M := by
    rw [hMdef]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hNNs_M : N * (N.size + 1) ≤ M := by
    rw [hMdef]
    calc N * (N.size + 1) ≤ (N + 1) * (N.size + 1) := Nat.mul_le_mul (by omega) (le_refl _)
      _ ≤ (N + 1) * ((L + N.size + 1) * (N.size + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hNL2_M : N * (L + 2 * N.size + 7) * (N.size + 1) ≤ 8 * M := by
    rw [hMdef]
    calc N * (L + 2 * N.size + 7) * (N.size + 1)
        ≤ ((N + 1) * (8 * (L + N.size + 1))) * (N.size + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 8 * ((N + 1) * ((L + N.size + 1) * (N.size + 1))) := by ring
  have hNsN2 : (N + 2) * (N.size + 1) ≤ 3 * M := by
    rw [hMdef]
    calc (N + 2) * (N.size + 1) ≤ (3 * (N + 1)) * (N.size + 1) :=
          Nat.mul_le_mul (by omega) (le_refl _)
      _ ≤ (3 * (N + 1)) * ((L + N.size + 1) * (N.size + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      _ = 3 * ((N + 1) * ((L + N.size + 1) * (N.size + 1))) := by ring
  -- the five per-stage bounds
  have hS1' : vsz (ofList (outs.map ofList)) + 1 ≤ 6 * M := by
    have h2 : N ≤ M := by omega
    omega
  have hX : vsz (ofList outs.flatten) + outs.flatten.length * (outs.flatten.length.size + 1) + 1
      ≤ 6 * M := by
    have h1 : outs.flatten.length * (outs.flatten.length.size + 1) ≤ N * (N.size + 1) :=
      Nat.mul_le_mul hlf hlfns
    omega
  have hZ : (vsz (ofList ys0) + 1) * (ys0.length.size + 1) ≤ 11 * M := by
    have hS3g : vsz (ofList ys0) + 1 ≤ N * (L + 2 * N.size + 7) + (N + 2) := by omega
    have h1 : (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
        ≤ (N * (L + 2 * N.size + 7) + (N + 2)) * (N.size + 1) :=
      Nat.mul_le_mul hS3g hY3
    have h2 : (N * (L + 2 * N.size + 7) + (N + 2)) * (N.size + 1)
        = N * (L + 2 * N.size + 7) * (N.size + 1) + (N + 2) * (N.size + 1) := by ring
    rw [h2] at h1
    exact le_trans h1 (le_trans (add_le_add hNL2_M hNsN2) (le_of_eq (by ring)))
  have hckw : (A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2))
      ≤ 24 * Kkw * M := by
    have hle : Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
        ≤ 24 * Kkw * ((L + N.size + 1) * (N.size + 1)) := by
      have h1 : L + N.size + 4 + N.size + 2 ≤ 8 * (L + N.size + 1) := by omega
      have h2 : N.size + 2 ≤ 3 * (N.size + 1) := by omega
      calc Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
          ≤ Kkw * (8 * (L + N.size + 1)) * (3 * (N.size + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left Kkw h1) h2
        _ = 24 * Kkw * ((L + N.size + 1) * (N.size + 1)) := by ring
    have h1 : (A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2))
        ≤ (A * B * n) * (24 * Kkw * ((L + N.size + 1) * (N.size + 1))) :=
      Nat.mul_le_mul_left _ hle
    have h2 : (A * B * n) * (24 * Kkw * ((L + N.size + 1) * (N.size + 1)))
        ≤ (N + 1) * (24 * Kkw * ((L + N.size + 1) * (N.size + 1))) := by
      refine Nat.mul_le_mul_right _ ?_
      omega
    refine le_trans (le_trans h1 h2) ?_
    rw [hMdef]
    exact le_of_eq (by ring)
  have hcm : (A * B * n) * (Kml * (L + N.size + 4 + N.size + 2 + 1))
      ≤ 8 * Kml * M := by
    have hle : Kml * (L + N.size + 4 + N.size + 2 + 1)
        ≤ 8 * Kml * (L + N.size + 1) := by
      have h1 : L + N.size + 4 + N.size + 2 + 1 ≤ 8 * (L + N.size + 1) := by omega
      calc Kml * (L + N.size + 4 + N.size + 2 + 1) ≤ Kml * (8 * (L + N.size + 1)) :=
            Nat.mul_le_mul_left Kml h1
        _ = 8 * Kml * (L + N.size + 1) := by ring
    have hle2 : 8 * Kml * (L + N.size + 1) ≤ 8 * Kml * ((L + N.size + 1) * (N.size + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have h1 : (A * B * n) * (Kml * (L + N.size + 4 + N.size + 2 + 1))
        ≤ (A * B * n) * (8 * Kml * ((L + N.size + 1) * (N.size + 1))) :=
      Nat.mul_le_mul_left _ (le_trans hle hle2)
    have h2 : (A * B * n) * (8 * Kml * ((L + N.size + 1) * (N.size + 1)))
        ≤ (N + 1) * (8 * Kml * ((L + N.size + 1) * (N.size + 1))) := by
      refine Nat.mul_le_mul_right _ ?_
      omega
    refine le_trans (le_trans h1 h2) ?_
    rw [hMdef]
    exact le_of_eq (by ring)
  have hcst : (A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1))
      ≤ 8 * Kst * M := by
    have hle : Kst * (L + N.size + 4 + N.size + 2 + 1)
        ≤ 8 * Kst * (L + N.size + 1) := by
      have h1 : L + N.size + 4 + N.size + 2 + 1 ≤ 8 * (L + N.size + 1) := by omega
      calc Kst * (L + N.size + 4 + N.size + 2 + 1) ≤ Kst * (8 * (L + N.size + 1)) :=
            Nat.mul_le_mul_left Kst h1
        _ = 8 * Kst * (L + N.size + 1) := by ring
    have hle2 : 8 * Kst * (L + N.size + 1) ≤ 8 * Kst * ((L + N.size + 1) * (N.size + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    have h1 : (A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1))
        ≤ (A * B * n) * (8 * Kst * ((L + N.size + 1) * (N.size + 1))) :=
      Nat.mul_le_mul_left _ (le_trans hle hle2)
    have h2 : (A * B * n) * (8 * Kst * ((L + N.size + 1) * (N.size + 1)))
        ≤ (N + 1) * (8 * Kst * ((L + N.size + 1) * (N.size + 1))) := by
      refine Nat.mul_le_mul_right _ ?_
      omega
    refine le_trans (le_trans h1 h2) ?_
    rw [hMdef]
    exact le_of_eq (by ring)
  -- combine
  have hKfl : Kfl * (vsz (ofList (outs.map ofList)) + 1) ≤ 6 * Kfl * M := by
    calc Kfl * (vsz (ofList (outs.map ofList)) + 1) ≤ Kfl * (6 * M) :=
          Nat.mul_le_mul_left Kfl hS1'
      _ = 6 * Kfl * M := by ring
  have hKen : Ken * (vsz (ofList outs.flatten)
        + outs.flatten.length * (outs.flatten.length.size + 1) + 1) ≤ 6 * Ken * M := by
    calc Ken * (vsz (ofList outs.flatten)
          + outs.flatten.length * (outs.flatten.length.size + 1) + 1) ≤ Ken * (6 * M) :=
          Nat.mul_le_mul_left Ken hX
      _ = 6 * Ken * M := by ring
  have hKso : Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1) ≤ 11 * Kso * M := by
    calc Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
        = Kso * ((vsz (ofList ys0) + 1) * (ys0.length.size + 1)) := by ring
      _ ≤ Kso * (11 * M) := Nat.mul_le_mul_left Kso hZ
      _ = 11 * Kso * M := by ring
  have hKml : Kml ≤ Kml * M := by
    calc Kml = Kml * 1 := (Nat.mul_one Kml).symm
      _ ≤ Kml * M := Nat.mul_le_mul_left Kml hM1
  have hfinal : Kfl * (vsz (ofList (outs.map ofList)) + 1)
      + (Ken * (vsz (ofList outs.flatten) + outs.flatten.length * (outs.flatten.length.size + 1) + 1)
      + ((A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml
      + (Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
      + ((A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml))))
      ≤ 128 * C * M := by
    have hbig : Kfl * (vsz (ofList (outs.map ofList)) + 1)
      + (Ken * (vsz (ofList outs.flatten) + outs.flatten.length * (outs.flatten.length.size + 1) + 1)
      + ((A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml
      + (Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
      + ((A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1)
            + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml))))
        = Kfl * (vsz (ofList (outs.map ofList)) + 1)
      + (Ken * (vsz (ofList outs.flatten) + outs.flatten.length * (outs.flatten.length.size + 1) + 1)
      + ((A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2))
      + ((A * B * n) * (Kml * (L + N.size + 4 + N.size + 2 + 1))
      + (Kml
      + (Kso * (vsz (ofList ys0) + 1) * (ys0.length.size + 1)
      + ((A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1))
      + ((A * B * n) * (Kml * (L + N.size + 4 + N.size + 2 + 1))
      + Kml))))))) := by ring
    rw [hbig]
    have hsum := add_le_add hKfl (add_le_add hKen
      (add_le_add hckw (add_le_add hcm (add_le_add hKml
        (add_le_add hKso (add_le_add hcst (add_le_add hcm hKml)))))))
    refine le_trans hsum ?_
    have hc1 : 6 * Kfl * M ≤ 6 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 6 (by omega))
    have hc2 : 6 * Ken * M ≤ 6 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 6 (by omega))
    have hc3 : 24 * Kkw * M ≤ 24 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 24 (by omega))
    have hc4 : 8 * Kml * M ≤ 8 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 8 (by omega))
    have hc5 : Kml * M ≤ C * M := Nat.mul_le_mul_right M (by omega)
    have hc6 : 11 * Kso * M ≤ 11 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 11 (by omega))
    have hc7 : 8 * Kst * M ≤ 8 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 8 (by omega))
    have hc8 : 8 * Kml * M ≤ 8 * C * M :=
      Nat.mul_le_mul_right M (Nat.mul_le_mul_left 8 (by omega))
    have hc9 : Kml * M ≤ C * M := Nat.mul_le_mul_right M (by omega)
    refine le_trans (add_le_add hc1 (add_le_add hc2 (add_le_add hc3 (add_le_add hc4
      (add_le_add hc5 (add_le_add hc6 (add_le_add hc7 (add_le_add hc8 hc9)))))))) ?_
    rw [show 6 * C * M + (6 * C * M + (24 * C * M + (8 * C * M + (C * M + (11 * C * M
          + (8 * C * M + (8 * C * M + C * M))))))) = 73 * C * M by ring]
    exact Nat.mul_le_mul_right M (by omega)
  have hMfin : 128 * C * (N + 1) * (L + N.size + 1) * (N.size + 1) = 128 * C * M := by
    rw [hMdef]
    ring
  rw [hMfin]
  exact hfinal

/-! ## `phase3b` -/

theorem phase3b (hK : HvdH.KernelLib) (hFl : FlattenSpec) (hEn : EnumerateSpec) (hSo : SortSpec)
    (hKw : Kw2Spec) :
    ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A n B N L : ℕ) (outs : List (List Val)) (rest : List Val),
      A * B ≤ N → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      WordR main p
        (fun vs => vs = ofList (outs.map ofList) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = ofList (unslices A n B outs) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  obtain ⟨pFl, Kfl, hFl⟩ := hFl
  obtain ⟨pEn, Ken, hEn⟩ := hEn
  obtain ⟨pSo, Kso, hSo⟩ := hSo
  obtain ⟨pKw, Kkw, hKw⟩ := hKw
  obtain ⟨combM, Kml, hMl⟩ := hK.mapList
  obtain ⟨pStrip, Kst, hStrip⟩ := Work.SB.P3.stripFromKernel hK
  obtain ⟨Kb, hKb⟩ := p3b_costBound_local Kfl Ken Kso Kml Kkw Kst
  refine ⟨Cmd.seq pFl (Cmd.seq pEn (Cmd.seq (combM pKw) (Cmd.seq pSo (combM pStrip)))), Kb, ?_⟩
  intro main A n B N L outs rest hAB hN hlen hsl hsz
  intro vs hvs s R h0
  subst hvs
  set enumL : List Val :=
    (List.range (A * B * n)).map (fun i : ℕ => Val.cons (.int (i : ℤ)) ((outs.flatten).getD i .nil)) with henumL
  set ys0 : List Val := enumL.map (lab2 n B) with hys0
  -- basic length facts
  have hFlatLen : (outs.flatten).length = A * B * n := P3b.flatLen A n B outs hlen hsl
  have hEnumLen : enumL.length = A * B * n := by
    rw [henumL, List.length_map, List.length_range]
  have hYs0Len : ys0.length = A * B * n := by
    rw [hys0, List.length_map, hEnumLen]
  -- the per-element predicate of the second labelling: a `Pkw`-witness records its own position,
  -- so the predicate is *empty* whenever `A * B * n = 0`
  let Pkw : Val → Prop := fun x => ∃ (i : ℕ), i < A * B * n ∧
    x = Val.cons (.int (i : ℤ)) ((outs.flatten).getD i .nil)
  let Qkw : Val → Val → Prop := fun x y => y = lab2 n B x
  let Pst : Val → Prop := fun x => ∃ (k : ℤ) (w : Val), x = Val.cons (.int k) w ∧
    vsz x ≤ L + N.size + 4 + N.size + 2
  let Qst : Val → Val → Prop := fun x y => y = unlab x
  -- the enumeration list consists of well-formed labelled records with the needed size bounds
  have hxs : ∀ x ∈ enumL, Pkw x ∧ vsz x ≤ L + N.size + 4 + N.size + 2 := by
    intro x hx
    rw [henumL, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hiM : i < A * B * n := List.mem_range.mp hi
    have hiN : i < N := lt_of_lt_of_le hiM hN
    have h3 : i.size ≤ N.size := Nat.size_le_size (le_of_lt hiN)
    have h2 : vsz ((outs.flatten).getD i .nil) ≤ L :=
      P3b.flatGetD A n B L outs hlen hsl hsz i hiM
    have hP : Pkw (Val.cons (.int (i : ℤ)) ((outs.flatten).getD i .nil)) := ⟨i, hiM, rfl⟩
    refine ⟨hP, ?_⟩
    rw [Work.SB.P3.vsz_cons]
    have hint : vsz (Val.int (i : ℤ)) = isz (i : ℤ) := Work.IntLib.vsz_int (i : ℤ)
    rw [hint]
    have h4 : isz ((i : ℤ)) = i.size + 2 := by simp [isz, Int.natAbs_natCast]
    omega
  -- the enumerated list is indexed by `f ↦ tgtIdx`
  have hys0eq : ys0 = (List.range (A * B * n)).map (fun f : ℕ =>
      Val.cons (.int ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) ((outs.flatten).getD f .nil)) := by
    rw [hys0]
    rw [henumL]
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    have hlab : lab2 n B (Val.cons (.int (i : ℤ)) ((outs.flatten).getD i .nil)) =
        Val.cons (.int ((tgtIdx n B ((i : ℤ).toNat / n) ((i : ℤ).toNat % n) : ℕ) : ℤ))
          ((outs.flatten).getD i .nil) := rfl
    rw [hlab, Int.toNat_natCast]
  have hys0sz : ∀ y ∈ ys0, vsz y ≤ L + N.size + 4 + N.size + 2 := by
    intro y hy
    rw [hys0eq, List.mem_map] at hy
    obtain ⟨f, hf, rfl⟩ := hy
    have hfN : f < A * B * n := List.mem_range.mp hf
    have htf : tgtIdx n B (f / n) (f % n) < N :=
      lt_of_lt_of_le (P3b.tgtIdxKeyLt A n B f hfN) hN
    have h2 : vsz ((outs.flatten).getD f .nil) ≤ L :=
      P3b.flatGetD A n B L outs hlen hsl hsz f hfN
    rw [Work.SB.P3.vsz_cons]
    have hint : vsz (Val.int ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) =
        isz ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ) := Work.IntLib.vsz_int _
    rw [hint]
    have h3 : isz (((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) ≤ N.size + 2 := by
      have hs := Nat.size_le_size (le_of_lt htf)
      simp only [isz, Int.natAbs_natCast]
      omega
    omega
  have hys0form : ∀ x ∈ ys0, ∃ (k : ℕ) (v : Val), x = Val.cons (.int (k : ℤ)) v := by
    intro x hx
    rw [hys0eq, List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨_, _, rfl⟩
  have hys0Pst : ∀ x ∈ ys0, Pst x ∧ vsz x ≤ L + N.size + 4 + N.size + 2 := by
    intro x hx
    have hszx := hys0sz x hx
    have hP : Pst x := by
      rw [hys0eq, List.mem_map] at hx
      obtain ⟨f, hf, rfl⟩ := hx
      exact ⟨_, _, rfl, hszx⟩
    exact ⟨hP, hszx⟩
  have hys0nodup : (ys0.map pairKey).Nodup := by
    have heq : ys0.map pairKey =
        (List.range (A * B * n)).map (fun f : ℕ => ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) := by
      rw [hys0eq, List.map_map]
      apply List.map_congr_left
      intro f hf
      rfl
    rw [heq]
    by_cases hz : A * B * n = 0
    · rw [hz, List.range_zero, List.map_nil]
      exact List.nodup_nil
    · have hABn : A * B ≠ 0 := fun h => hz (by rw [h, Nat.zero_mul])
      have hn1 : 0 < n := Nat.pos_of_ne_zero (fun h => hz (by rw [h, Nat.mul_zero]))
      have hB1 : 0 < B := Nat.pos_of_ne_zero (fun h => hABn (by rw [h, Nat.mul_zero]))
      exact Work.SB.P3.keyNodup n B (A * B * n) hn1 hB1
  -- the second labelling word
  have hElkw : ∀ x, Pkw x → WordR main pKw
      (fun vs => vs = x :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      (fun _ out => ∃ y, out = y :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest ∧ Qkw x y ∧
        vsz y ≤ L + N.size + 4 + N.size + 2)
      (fun _ => Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)) := by
    intro x hx
    obtain ⟨i, hiM, rfl⟩ := hx
    have hz : A * B * n ≠ 0 := by omega
    have hABn : A * B ≠ 0 := fun h => hz (by rw [h, Nat.zero_mul])
    have hA1 : 1 ≤ A := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (fun h => hABn (by rw [h, Nat.zero_mul])))
    have hB1 : 1 ≤ B := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (fun h => hABn (by rw [h, Nat.mul_zero])))
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (fun h => hz (by rw [h, Nat.mul_zero])))
    have hAB1 : 1 ≤ A * B := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hA1)
      (lt_of_lt_of_le Nat.zero_lt_one hB1)
    have hnN : n ≤ N := le_trans (by simpa [Nat.one_mul] using Nat.mul_le_mul_right n hAB1) hN
    have hBle : B ≤ N := by
      have h1 : B ≤ A * B := by
        calc B = 1 * B := (Nat.one_mul B).symm
          _ ≤ A * B := Nat.mul_le_mul_right B hA1
      have h2 : A * B ≤ A * B * n := by
        simpa using Nat.mul_le_mul_left (A * B) hn1
      exact le_trans (le_trans h1 h2) hN
    have hiN : i < N := lt_of_lt_of_le hiM hN
    have htf : tgtIdx n B (i / n) (i % n) < N :=
      lt_of_lt_of_le (P3b.tgtIdxKeyLt A n B i hiM) hN
    have hiszn : isz (n : ℤ) ≤ L + N.size + 4 := by
      have h2 : isz (n : ℤ) = n.size + 2 := by simp [isz, Int.natAbs_natCast]
      have h3 : n.size ≤ N.size := Nat.size_le_size hnN
      omega
    have hiszB : isz (B : ℤ) ≤ L + N.size + 4 := by
      have h2 : isz (B : ℤ) = B.size + 2 := by simp [isz, Int.natAbs_natCast]
      have h3 : B.size ≤ N.size := Nat.size_le_size hBle
      omega
    have hvszx : vsz (Val.cons (.int (i : ℤ)) ((outs.flatten).getD i .nil)) ≤ L + N.size + 4 := by
      rw [Work.SB.P3.vsz_cons]
      have hint : vsz (Val.int (i : ℤ)) = isz (i : ℤ) := Work.IntLib.vsz_int (i : ℤ)
      rw [hint]
      have h4 : isz (i : ℤ) = i.size + 2 := by simp [isz, Int.natAbs_natCast]
      have h3 : i.size ≤ N.size := Nat.size_le_size (le_of_lt hiN)
      have h2 : vsz ((outs.flatten).getD i .nil) ≤ L :=
        P3b.flatGetD A n B L outs hlen hsl hsz i hiM
      omega
    obtain ⟨hszout, hw⟩ := hKw main n B N (L + N.size + 4) (i : ℤ) ((outs.flatten).getD i .nil)
      rest hn1 hB1 (by simp) (by simpa using hiN)
      (by simpa using htf) hiszn hiszB hvszx
    refine hK.conseq main pKw _ _ _ _ _ _ hw ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out hpre hpost
      exact ⟨_, hpost, rfl, hszout⟩
    · intro vs h; exact le_rfl
  -- ============ stage 1: flatten ============
  obtain ⟨v1, s1, k1, ⟨r1, hv1, ho1⟩, hev1, hk1, hs1, hf1⟩ :=
    hFl main outs (ofList (outs.map ofList) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      ⟨Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest, rfl⟩ s R h0
  have hr1 : r1 = Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := ((List.cons.inj hv1).2).symm
  have hv1' : v1 = ofList (outs.flatten) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := by
    rw [ho1, hr1]
  have hs1' : s1.stk 0 =
      encs (ofList (outs.flatten) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) ++ R := by
    rw [hs1, hv1']
  -- ============ stage 2: enumerate ============
  obtain ⟨v2, s2, k2, ⟨r2, hv2, ho2⟩, hev2, hk2, hs2, hf2⟩ :=
    hEn main (outs.flatten) (ofList (outs.flatten) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      ⟨Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest, rfl⟩ s1 R hs1'
  have hr2 : r2 = Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := ((List.cons.inj hv2).2).symm
  have ho2' : v2 = ofList enumL :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := by
    rw [ho2, hFlatLen, ← henumL]
    rw [hr2]
  have hs2' : s2.stk 0 = encs (ofList enumL :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) ++ R := by
    rw [hs2, ho2']
  -- ============ stage 3: label (mapList kw2) ============
  obtain ⟨v3, s3, k3, ⟨ys, ho3, hyF⟩, hev3, hk3, hs3, hf3⟩ :=
    hMl main pKw (Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) Pkw Qkw
      (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)) (L + N.size + 4 + N.size + 2)
      hElkw enumL hxs (ofList enumL :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) rfl s2 R hs2'
  have hys_eq : ys = ys0 := by
    rw [hys0]
    simpa using P3b.forall2Map (lab2 n B) id enumL ys hyF
  have ho3' : v3 = ofList ys0 :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := by
    rw [ho3, hys_eq]
  have hs3' : s3.stk 0 = encs (ofList ys0 :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) ++ R := by
    rw [hs3, ho3']
  -- ============ stage 4: sort by key ============
  obtain ⟨v4, s4, k4, ⟨r4, ys', hv4, ho4, hperm4, hsort4⟩, hev4, hk4, hs4, hf4⟩ :=
    hSo main ys0 hys0form hys0nodup
      (ofList ys0 :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      ⟨Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest, rfl⟩ s3 R hs3'
  have hr4 : r4 = Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := ((List.cons.inj hv4).2).symm
  have ho4' : v4 = ofList ys' :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := by
    rw [ho4, hr4]
  have hs4' : s4.stk 0 = encs (ofList ys' :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) ++ R := by
    rw [hs4, ho4']
  -- ============ stage 5: strip keys (mapList strip) ============
  have hElst : ∀ x, Pst x → WordR main pStrip
      (fun vs => vs = x :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest)
      (fun _ out => ∃ y, out = y :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest ∧ Qst x y ∧
        vsz y ≤ L + N.size + 4 + N.size + 2)
      (fun _ => Kst * (L + N.size + 4 + N.size + 2 + 1)) := by
    intro x hx
    obtain ⟨k', w, rfl, hszx⟩ := hx
    obtain ⟨hw, hwv⟩ := hStrip main (L + N.size + 4 + N.size + 2) k' w
      (Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) hszx
    refine hK.conseq main pStrip _ _ _ _ _ _ hwv ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out hpre hpost
      exact ⟨_, hpost, rfl, hw⟩
    · intro vs h; exact le_rfl
  have hxsst : ∀ x ∈ ys', Pst x ∧ vsz x ≤ L + N.size + 4 + N.size + 2 := by
    intro x hx
    exact hys0Pst x ((hperm4.mem_iff).mp hx)
  obtain ⟨v5, s5, k5, ⟨ys'', ho5, hyF5⟩, hev5, hk5, hs5, hf5⟩ :=
    hMl main pStrip (Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) Pst Qst
      (Kst * (L + N.size + 4 + N.size + 2 + 1)) (L + N.size + 4 + N.size + 2)
      hElst ys' hxsst (ofList ys' :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) rfl s4 R hs4'
  have hys'' : ys'' = ys'.map unlab := by
    simpa using P3b.forall2Map unlab id ys' ys'' hyF5
  -- ============ the final value ============
  have hyslen : ys'.length = A * B * n := by
    rw [hperm4.length_eq, hYs0Len]
  have hperm5 : ys'.Perm ((List.range (A * B * n)).map (fun f : ℕ =>
      Val.cons (.int ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) ((outs.flatten).getD f .nil))) := by
    rw [← hys0eq]
    exact hperm4
  have huns : ys'.map unlab = unslices A n B outs := by
    by_cases hz : A * B * n = 0
    · have hys0nil : ys0 = [] := by rw [hys0, henumL, hz]; simp
      have hys'nil : ys' = [] := List.Perm.eq_nil (hperm4.trans (by rw [hys0nil]))
      rw [hys'nil]
      have hz' : A * n * B = 0 := by rw [show A * n * B = A * B * n by ring, hz]
      rw [HvdH.unslices, hz']
      simp
    · have hABn : A * B ≠ 0 := fun h => hz (by rw [h, Nat.zero_mul])
      have hn1 : 0 < n := Nat.pos_of_ne_zero (fun h => hz (by rw [h, Nat.mul_zero]))
      have hB1 : 0 < B := Nat.pos_of_ne_zero (fun h => hABn (by rw [h, Nat.mul_zero]))
      exact (Work.SB.unslicesFacts A n B outs).2 hn1 hB1 hlen hsl ys' hperm5 hsort4
  have hv5' : v5 = ofList (unslices A n B outs) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest := by
    rw [ho5, hys'', huns]
  have hs5' : s5.stk 0 =
      encs (ofList (unslices A n B outs) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest) ++ R := by
    rw [hs5, hv5']
  -- ============ the evaluation and the cost ============
  have heval : Eval main (Cmd.seq pFl (Cmd.seq pEn (Cmd.seq (combM pKw) (Cmd.seq pSo (combM pStrip)))))
      s s5 (k1 + (k2 + (k3 + (k4 + k5)))) :=
    Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 (Eval.seq hev4 hev5)))
  have hk3' : k3 ≤ (A * B * n) * (Kkw * (L + N.size + 4 + N.size + 2) * (N.size + 2)
      + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml := by
    rw [hEnumLen] at hk3; exact hk3
  have hk5' : k5 ≤ (A * B * n) * (Kst * (L + N.size + 4 + N.size + 2 + 1)
      + Kml * (L + N.size + 4 + N.size + 2 + 1)) + Kml := by
    rw [hyslen] at hk5; exact hk5
  have hcost : k1 + (k2 + (k3 + (k4 + k5))) ≤ Kb * (N + 1) * (L + N.size + 1) * (N.size + 1) := by
    refine le_trans (add_le_add hk1 (add_le_add hk2 (add_le_add hk3' (add_le_add hk4 hk5'))))
      (hKb A n B N L outs ys0 hAB hN hlen hsl hsz hYs0Len hys0sz)
  have hframe : ∀ k : Stk, k ≠ 0 → s5.stk k = s.stk k := by
    intro k hk
    rw [hf5 k hk, hf4 k hk, hf3 k hk, hf2 k hk, hf1 k hk]
  exact ⟨ofList (unslices A n B outs) :: Val.int (n : ℤ) :: Val.int (B : ℤ) :: rest, s5,
    k1 + (k2 + (k3 + (k4 + k5))), rfl, heval, hcost, hs5', hframe⟩

end Work.SB
