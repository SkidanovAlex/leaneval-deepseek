import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs
import Submission.Work.SynFFT.blkLvlDefs
import Submission.Work.SynFFT.blkLvlSuffixKit

/-!
# `Work.SynFFT.sndCompPass`: map `vsnd` over a list of `cons` values

A `KLib` word which turns `ofList xs :: rest` into `ofList (xs.map vsnd) :: rest` for every list
`xs` of `cons`-values of size `≤ Lb`, at cost `K * (xs.length * (Lb + 1) + 1) + K` — i.e. one
`KLib.mapList` pass whose per-element word is `unconsV ; drop` (read the `cons`, drop its first
component).  The per-element word's cost is the constant `Ku + Kdr * (Lb + 1)`, which is why the
`mapList` contract (a cost independent of the element) is met.

The two ingredients are isolated below: `sndElem` (the single-element word) and `sndCompCost`
(the arithmetic of the accumulated cost).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-! ## Arithmetic of the cost bound -/

/-- With `c = Ke * (Lb + 1)` the `mapList` bound `n * (c + Kml * (Lb + 1)) + Kml` is dominated by
`K * (n * (Lb + 1) + 1) + K` for `K = Ke + Kml + 1`. -/
lemma sndCompCost (Ke Kml Lb n : ℕ) :
    n * (Ke * (Lb + 1) + Kml * (Lb + 1)) + Kml
      ≤ (Ke + Kml + 1) * (n * (Lb + 1) + 1) + (Ke + Kml + 1) := by
  have hB : 1 ≤ Lb + 1 := by omega
  have h1 : Ke * 1 ≤ Ke * (Lb + 1) := Nat.mul_le_mul_left _ hB
  nlinarith [h1, Nat.zero_le n, Nat.zero_le Ke, Nat.zero_le Kml, Nat.zero_le Lb]

/-! ## The single-element word: `cons a b :: rest ↦ b :: rest` -/

/-- The per-element word of `sndCompPass`: `unconsV` followed by `drop`.  Its cost is constant in
the element (`K * (Lb + 1)` once the size bound `vsz (.cons a b) ≤ Lb` is known), which is what
`KLib.mapList` needs. -/
lemma sndElem (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (Lb : ℕ) (a b : HvdH.Val) (rest : List HvdH.Val),
        HvdH.vsz (HvdH.Val.cons a b) ≤ Lb →
        HvdH.WordR main prog (fun vs => vs = HvdH.Val.cons a b :: rest)
          (fun _ out => out = b :: rest) (fun _ => K * (Lb + 1)) := by
  obtain ⟨uncP, Ku, hunc⟩ := hk.unconsV
  obtain ⟨kdrP, Kdr, hkdr⟩ := hk.drop
  refine ⟨Cmd.seq uncP kdrP, Ku + Kdr, ?_⟩
  intro main Lb a b rest hle
  have hva : vsz a ≤ Lb := le_trans (vfst_cons_le a b) hle
  have h1 : WordR main uncP (fun vs => vs = Val.cons a b :: rest)
      (fun _ out => out = a :: b :: rest) (fun _ => Ku) := by
    refine MrgKit.WordR_weaken (hunc main) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨a, b, rest, rfl⟩
    · intro vs out hvs hpost
      rw [hvs] at hpost
      obtain ⟨a', b', r', heq, hout⟩ := hpost
      obtain ⟨hA, hR⟩ := List.cons.inj heq
      obtain ⟨ha, hb⟩ := Val.cons.inj hA
      rw [hout, ← ha, ← hb, ← hR]
    · intro vs hvs
      exact le_rfl
  have h2 : WordR main kdrP (fun vs => vs = a :: b :: rest) (fun _ out => out = b :: rest)
      (fun _ => Kdr * (Lb + 1)) := by
    refine MrgKit.kdropStep (hkdr main) (a :: b :: rest) (by simp) (Kdr * (Lb + 1)) ?_
    have : Kdr * (vsz a + 1) ≤ Kdr * (Lb + 1) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right hva 1)
    simpa using this
  refine MrgKit.WordR_weaken (MrgKit.WordR_seqC h1 h2)
    (P' := fun vs => vs = Val.cons a b :: rest) (Q' := fun _ out => out = b :: rest)
    (C' := fun _ => (Ku + Kdr) * (Lb + 1)) ?_ ?_ ?_
  · intro vs hvs
    exact hvs
  · intro vs out hvs hpost
    exact hpost
  · intro vs hvs
    show Ku + Kdr * (Lb + 1) ≤ (Ku + Kdr) * (Lb + 1)
    have hB : 1 ≤ Lb + 1 := by omega
    have hKu : Ku * 1 ≤ Ku * (Lb + 1) := Nat.mul_le_mul_left _ hB
    nlinarith [hKu, Nat.zero_le Lb, Nat.zero_le Ku, Nat.zero_le Kdr]

/-! ## The pass -/

theorem sndCompPass (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (Lb : ℕ) (xs : List HvdH.Val)
      (rest : List HvdH.Val),
      (∀ x ∈ xs, ∃ a b : HvdH.Val, x = HvdH.Val.cons a b) → (∀ x ∈ xs, HvdH.vsz x ≤ Lb) →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.ofList xs :: rest)
        (fun _ out => out = HvdH.ofList (xs.map Work.SynFFT.vsnd) :: rest)
        (fun _ => K * (xs.length * (Lb + 1) + 1) + K) := by
  obtain ⟨mapP, Kml, hmap⟩ := hk.mapList
  obtain ⟨elemP, Ke, helem⟩ := sndElem hk
  refine ⟨mapP elemP, Ke + Kml + 1, ?_⟩
  intro main Lb xs rest hcons hsize
  refine MrgKit.mapStep (hmap main) elemP rest (cnsP Lb) (fun x y => y = vsnd x)
    (Ke * (Lb + 1)) Lb ?_ xs ?_ (ofList (xs.map vsnd)) ?_
    ((Ke + Kml + 1) * (xs.length * (Lb + 1) + 1) + (Ke + Kml + 1)) ?_
  · -- the per-element word, with the `mapList` contract (cost independent of `x`)
    intro x hP
    obtain ⟨a, b, hx⟩ := hP.1
    have hle : vsz (Val.cons a b) ≤ Lb := by rw [← hx]; exact hP.2
    have hb : vsz b ≤ Lb := le_trans (vsnd_cons_le a b) hle
    refine MrgKit.WordR_weaken (helem main Lb a b rest hle) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs, hx]
    · intro vs out hvs hpost
      exact ⟨b, hpost, by rw [hx, vsnd_cons], hb⟩
    · intro vs hvs
      exact le_rfl
  · -- every element is a `cons` of size `≤ Lb`
    intro x hx
    exact ⟨⟨hcons x hx, hsize x hx⟩, hsize x hx⟩
  · -- the output list is pinned by the `Forall₂`
    intro ys hF
    rw [forall₂_vsnd hF]
  · -- the accumulated cost
    exact sndCompCost Ke Kml Lb xs.length

end Work.SynFFT
