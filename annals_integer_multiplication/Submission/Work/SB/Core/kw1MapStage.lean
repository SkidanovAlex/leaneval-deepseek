import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx
import Submission.Work.SB.Core.Kw1StageDefs
import Submission.Work.SB.Core.kw1Forall2
import Submission.Work.SB.Core.kw1CostBound
import Submission.Work.SB.keyFacts
import Submission.Work.IntLib.encodeNatBridge

set_option autoImplicit false

namespace Work.SB.Core

open HvdH

/-- `WordR` with the four `KernelLib.conseq` obligations, in a usable argument order. -/
private theorem conseqR {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (hK : HvdH.KernelLib) (h : WordR main p P Q C)
    (h1 : ∀ vs, P' vs → P vs) (h2 : ∀ vs out, P' vs → Q vs out → Q' vs out)
    (h3 : ∀ vs, P' vs → C vs ≤ C' vs) : WordR main p P' Q' C' :=
  hK.conseq main p P P' Q Q' C C' h h1 h2 h3

/-- Size of `int (n : ℤ)`. -/
theorem vsz_intNat (n : ℕ) : vsz (Val.int ((n : ℕ) : ℤ)) = n.size + 2 := by
  show (Val.int ((n : ℕ) : ℤ)).enc.length = n.size + 2
  rw [Work.IntLib.vsz_int, Work.IntLib.isz_eq, Int.natAbs_natCast]

theorem kw1MapStage (hK : HvdH.KernelLib) (hKw : Work.Layout.Kw1Spec) :
    ∃ (p : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (A m B N L : ℕ) (es rest : List HvdH.Val),
      0 < m → 0 < B → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, HvdH.vsz x ≤ L) →
      HvdH.WordR main p
        (fun vs => vs = HvdH.ofList ((List.range (A * m * B)).map (fun i =>
            HvdH.Val.cons (HvdH.Val.int ((i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil))) ::
          HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => out = HvdH.ofList ((List.range (A * m * B)).map (fun i =>
            HvdH.Val.cons (HvdH.Val.int ((Work.Layout.keyIdx1 m B i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil))) ::
          HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1)) := by
  obtain ⟨qw, K0, hkw⟩ := hKw
  obtain ⟨comb, K1, hML⟩ := hK.mapList
  refine ⟨comb qw, 10 * K0 + 6 * K1 + 1, ?_⟩
  intro main A m B N L es rest hm hB hle hlen hvsz
  have helem : ∀ x : HvdH.Val, kw1P A m B N L x →
      HvdH.WordR main qw
        (fun vs => vs = x :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
          HvdH.Val.int (A : ℤ) :: rest)
        (fun _ out => ∃ y, out = y :: HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) ::
          HvdH.Val.int (A : ℤ) :: rest ∧ kw1Q A m B x y ∧ HvdH.vsz y ≤ kw1SizeOut N L)
        (fun _ => kw1ElemCost K0 N L) := by
    intro x hx
    obtain ⟨i, v, hi, hxv, hvszx⟩ := hx
    have hitoNat : (((i : ℕ) : ℤ)).toNat = i := Int.toNat_natCast i
    have hvszx' : HvdH.vsz (HvdH.Val.cons (HvdH.Val.int ((i : ℕ) : ℤ)) v) ≤ L + N.size + 3 := by
      rw [← hxv]; exact hvszx
    have hiN : i < N := lt_of_lt_of_le hi hle
    have hprod : 0 < A * m * B := lt_of_le_of_lt (Nat.zero_le i) hi
    have hApos : 0 < A := by
      have h : 0 < A * (m * B) := by rw [← Nat.mul_assoc]; exact hprod
      exact Nat.pos_of_mul_pos_right h
    have hmN : m ≤ N := by
      have h1 : m ≤ m * B := Nat.le_mul_of_pos_right m hB
      have h2 : m * B ≤ A * (m * B) := Nat.le_mul_of_pos_left (m * B) hApos
      have h3 : A * (m * B) ≤ N := by rw [← Nat.mul_assoc]; exact hle
      exact le_trans h1 (le_trans h2 h3)
    have hBN : B ≤ N := by
      have h1 : B ≤ m * B := Nat.le_mul_of_pos_left B hm
      have h2 : m * B ≤ A * (m * B) := Nat.le_mul_of_pos_left (m * B) hApos
      have h3 : A * (m * B) ≤ N := by rw [← Nat.mul_assoc]; exact hle
      exact le_trans h1 (le_trans h2 h3)
    have hiszm : HvdH.isz (m : ℤ) ≤ L + N.size + 3 := by
      rw [Work.IntLib.isz_eq, Int.natAbs_natCast]
      have h := Nat.size_le_size hmN
      omega
    have hiszB : HvdH.isz (B : ℤ) ≤ L + N.size + 3 := by
      rw [Work.IntLib.isz_eq, Int.natAbs_natCast]
      have h := Nat.size_le_size hBN
      omega
    have hkeyN : Work.Layout.keyIdx1 m B (((i : ℕ) : ℤ)).toNat < N := by
      rw [hitoNat]
      exact lt_of_lt_of_le ((Work.SB.keyFacts A m B hm hB).1 i hi) hle
    obtain ⟨hvszout, hWR⟩ :=
      hkw main m B N (L + N.size + 3) (((i : ℕ) : ℤ)) v (HvdH.Val.int (A : ℤ) :: rest)
        hm hB (Int.natCast_nonneg i) (by rw [hitoNat]; exact hiN) hkeyN hiszm hiszB hvszx'
    refine conseqR hK hWR ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hxv]
    · intro vs out hvs hpost
      refine ⟨HvdH.Val.cons (HvdH.Val.int ((Work.Layout.keyIdx1 m B i : ℕ) : ℤ)) v, ?_, ?_, ?_⟩
      · rw [hpost, hitoNat]
      · exact ⟨i, v, hi, hxv, rfl⟩
      · rw [hitoNat] at hvszout
        rw [kw1SizeOut]
        exact hvszout
    · intro vs _
      rw [kw1ElemCost]
  have hmem : ∀ x ∈ kw1In A m B es, kw1P A m B N L x ∧ HvdH.vsz x ≤ kw1SizeOut N L := by
    intro x hx
    simp only [kw1In, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, hix⟩ := hx
    rw [← hix]
    have hilt : i < es.length := by rw [hlen]; exact hi
    have hvszi : HvdH.vsz (es.getD i HvdH.Val.nil) ≤ L := by
      rw [List.getD_eq_getElem es HvdH.Val.nil hilt]
      exact hvsz _ (List.getElem_mem hilt)
    have hsizei : i.size ≤ N.size := Nat.size_le_size (le_trans (le_of_lt hi) hle)
    have hvx : HvdH.vsz (HvdH.Val.cons (HvdH.Val.int ((i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil))
        ≤ L + N.size + 3 := by
      rw [vsz_cons, vsz_intNat]
      omega
    constructor
    · exact ⟨i, es.getD i HvdH.Val.nil, hi, rfl, hvx⟩
    · rw [kw1SizeOut]
      omega
  have hml := hML main qw
    (HvdH.Val.int (m : ℤ) :: HvdH.Val.int (B : ℤ) :: HvdH.Val.int (A : ℤ) :: rest)
    (kw1P A m B N L) (kw1Q A m B) (kw1ElemCost K0 N L) (kw1SizeOut N L) helem
    (kw1In A m B es) hmem
  refine conseqR hK hml ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs hpost
    obtain ⟨ys, hout, hfor⟩ := hpost
    rw [hout, kw1Forall2 A m B es ys hfor]
    rfl
  · intro vs _
    rw [kw1In_length]
    exact kw1CostBound hle

end Work.SB.Core
