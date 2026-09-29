import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlDefs
import Submission.Work.SynFFT.blkLvlSuffixKit

/-!
# `Work.SynFFT.fstCompPass`: mapping `vfst` over a list of `cons` values

The suffix pass of the block level FFT has to extract the first component of every bunched
butterfly output (`Work.SynFFT.vfst`).  This file proves that the corresponding list map is
realised by a StackLang word with a *constant* per-element cost, given a uniform size bound `Lb`
on the elements.

The per-element word is `unconsV ;;; roll 1 ;;; drop`: it turns `cons a b :: t` into `a :: t`.
Its cost is `Kuc + (2·Kr + Kdr)·(Lb + 1)` whenever `vsz (cons a b) ≤ Lb`, because
`vsz a + vsz b + 1 = vsz (cons a b) ≤ Lb` bounds both the `roll` and the `drop` step.

Composing with `KLib.mapList` (lemma `MrgKit.mapStep`) gives the map `xs ↦ xs.map vfst` at cost
`K·(xs.length·(Lb+1)+1) + K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-- The per-element word `cons a b :: t ↦ a :: t`, at a cost depending only on a bound `Lb` for
`vsz (cons a b)`. -/
theorem fstElemStep {main : Cmd} {uncP : Cmd} {rollP : ℕ → Cmd} {kdrP : Cmd}
    {Kuc Kr Kdr : ℕ}
    (hunc : WordR main uncP (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => Kuc))
    (hroll : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k + 1) * (((vs.take (k + 1)).map vsz).sum + 1)))
    (hkdr : WordR main kdrP (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => Kdr * (vsz (vs.headD .nil) + 1)))
    (Lb : ℕ) (a b : Val) (t : List Val) (hx : vsz a + vsz b + 1 ≤ Lb) :
    WordR main ((uncP ;;; rollP 1) ;;; kdrP) (fun vs => vs = .cons a b :: t)
      (fun _ out => out = a :: t) (fun _ => Kuc + (2 * Kr + Kdr) * (Lb + 1)) := by
  have h1 : WordR main uncP (fun vs => vs = .cons a b :: t) (fun _ out => out = a :: b :: t)
      (fun _ => Kuc) := MrgKit.uncStep hunc a b t Kuc le_rfl
  have h2 : WordR main (rollP 1) (fun vs => vs = a :: b :: t) (fun _ out => out = b :: a :: t)
      (fun _ => Kr * 2 * (vsz a + vsz b + 1)) := by
    refine MrgKit.WordR_conseqC
      (MrgKit.rollStep hroll 1 (a :: b :: t) (by simp) (Kr * 2 * (vsz a + vsz b + 1)) ?_)
      rfl ?_ le_rfl
    · simp
    · intro out hout
      rw [hout]
      simp
  have h3 : WordR main kdrP (fun vs => vs = b :: a :: t) (fun _ out => out = a :: t)
      (fun _ => Kdr * (vsz b + 1)) := by
    refine MrgKit.WordR_conseqC
      (MrgKit.kdropStep hkdr (b :: a :: t) (by simp) (Kdr * (vsz b + 1)) ?_) rfl ?_ le_rfl
    · simp
    · intro out hout
      rw [hout]
      simp
  have hs : WordR main ((uncP ;;; rollP 1) ;;; kdrP) (fun vs => vs = .cons a b :: t)
      (fun _ out => out = a :: t)
      (fun _ => Kuc + Kr * 2 * (vsz a + vsz b + 1) + Kdr * (vsz b + 1)) :=
    MrgKit.WordR_seqC (MrgKit.WordR_seqC h1 h2) h3
  refine MrgKit.WordR_weaken hs (fun vs hvs => hvs) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  nlinarith [Nat.zero_le Kr, Nat.zero_le Kdr]

theorem fstCompPass (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Lb : ℕ) (xs : List HvdH.Val)
      (rest : List HvdH.Val),
      (∀ x ∈ xs, ∃ a b : HvdH.Val, x = HvdH.Val.cons a b) → (∀ x ∈ xs, HvdH.vsz x ≤ Lb) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList xs :: rest)
        (fun _ out => out = HvdH.ofList (xs.map Work.SynFFT.vfst) :: rest)
        (fun _ => K * (xs.length * (Lb + 1) + 1) + K) := by
  obtain ⟨uncP, Kuc, hunc⟩ := hk.unconsV
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  obtain ⟨mapP, Kml, hmap⟩ := hk.mapList
  set K : ℕ := Kuc + 2 * Kr + Kdr + Kml + Kml with hKdef
  refine ⟨mapP ((uncP ;;; rollP 1) ;;; kdrP), K, ?_⟩
  intro main Lb xs rest hcons hsz
  set c : ℕ := Kuc + (2 * Kr + Kdr) * (Lb + 1) with hcdef
  set P : Val → Prop := fun x => (∃ a b : Val, x = .cons a b) ∧ vsz x ≤ Lb with hPdef
  have hstep : ∀ x, P x → WordR main ((uncP ;;; rollP 1) ;;; kdrP) (fun vs => vs = x :: rest)
      (fun _ out => ∃ y, out = y :: rest ∧ y = vfst x ∧ vsz y ≤ Lb) (fun _ => c) := by
    rintro x ⟨⟨a, b, rfl⟩, hxsz⟩
    have hx' : vsz a + vsz b + 1 ≤ Lb := by simpa [MrgKit.vsz_cons'] using hxsz
    have hle : vsz a ≤ Lb := by omega
    refine MrgKit.WordR_weaken (fstElemStep (hunc main) (hroll main) (hkdr main) Lb a b rest hx')
      (fun vs hvs => hvs) ?_ ?_
    · rintro vs out hvs hout
      exact ⟨a, hout, rfl, hle⟩
    · intro vs hvs
      exact le_of_eq hcdef.symm
  have hxs : ∀ x ∈ xs, P x ∧ vsz x ≤ Lb := by
    intro x hx
    exact ⟨⟨hcons x hx, hsz x hx⟩, hsz x hx⟩
  have hB : ∀ ys : List Val, List.Forall₂ (fun x y => y = vfst x) xs ys →
      ofList (xs.map vfst) = ofList ys := by
    intro ys hy
    rw [forall₂_vfst hy]
  have hcK : c + Kml * (Lb + 1) ≤ K * (Lb + 1) := by
    rw [hKdef, hcdef]
    nlinarith [Nat.zero_le Kr, Nat.zero_le Kdr, Nat.zero_le Kml, Nat.zero_le Kuc, Nat.zero_le Lb]
  have hD : xs.length * (c + Kml * (Lb + 1)) + Kml ≤ K * (xs.length * (Lb + 1) + 1) + K := by
    have h1 : xs.length * (c + Kml * (Lb + 1)) ≤ K * (xs.length * (Lb + 1)) :=
      calc xs.length * (c + Kml * (Lb + 1)) ≤ xs.length * (K * (Lb + 1)) :=
            Nat.mul_le_mul_left _ hcK
        _ = K * (xs.length * (Lb + 1)) := by ring
    have h2 : Kml ≤ 2 * K := by rw [hKdef]; omega
    calc xs.length * (c + Kml * (Lb + 1)) + Kml
        ≤ K * (xs.length * (Lb + 1)) + Kml := Nat.add_le_add_right h1 Kml
      _ ≤ K * (xs.length * (Lb + 1)) + 2 * K := Nat.add_le_add_left h2 _
      _ = K * (xs.length * (Lb + 1) + 1) + K := by ring
  exact MrgKit.mapStep (main := main) (hmap main) ((uncP ;;; rollP 1) ;;; kdrP) rest P
    (fun x y => y = vfst x) c Lb hstep xs hxs (ofList (xs.map vfst)) hB
    (K * (xs.length * (Lb + 1) + 1) + K) hD

end Work.SynFFT
