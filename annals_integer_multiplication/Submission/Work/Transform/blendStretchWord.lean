import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.Kernel.Raw
import Submission.Work.Transform.chirpAux
import Submission.Work.Transform.blendStretchCost

namespace Work.Transform

open HvdH

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# `Work.Transform.blendStretchWord`: stretching a disc vector

Given a disc vector `c ∈ C̃◦ᵗ` (encoded as `cvecVal c`) and the parameters `int P, int p, int t`
sitting below it, produce the vector `X` of length `t * P` whose `(a * P + b)`-th entry is
`cfxVal (c a)` for `a < t`, `b < P` — i.e. the vector obtained by repeating every coefficient of
`c` exactly `P` times.

Implementation: `KernelLib.mapList` runs the per-element word (`KernelLib.pick 1` to copy the
parameter `int P` from below the list to the top, then `LayoutLib.replicate` to replicate the
element `P` times) over the list `c.map cfxVal`, and `LayoutLib.flatten` concatenates the pieces.

Cost: `O((t+1) ((P+1)(p+1)² + 1))` (the `mapList` loop pays `O(t · (P+1)(p+1))`, the flatten pays
`O(t (P+1) (p+1))`).
-/

/-! ## Auxiliary lemmas -/

/-- The `a`-th value of the list of `cfxVal`s encoded by `cvecVal c` (with `(0,0)` defaults). -/
theorem bswGetDMap (c : List (ℤ × ℤ)) (a : ℕ) (ha : a < c.length) :
    (c.map cfxVal).getD a Val.nil = cfxVal (c.getD a (0, 0)) := by
  induction c generalizing a with
  | nil => exact absurd ha (by simp)
  | cons z c ih =>
    cases a with
    | zero => simp
    | succ a =>
      have ha' : a < c.length := by simpa using ha
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih a ha'

/-- Extraction of the image list (and of membership in it) from a `List.Forall₂` relation whose
first component is functional. -/
theorem bswForall₂ {α : Type*} {f : α → Val} {R : Val → Prop} :
    ∀ {xs : List α} {ys : List Val},
      List.Forall₂ (fun x y => y = f x ∧ R y) xs ys → ys = xs.map f ∧ ∀ y ∈ ys, R y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases h with
    | nil => exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    intro ys h
    cases h with
    | cons hxy htail =>
      obtain ⟨hb, hR⟩ := hxy
      obtain ⟨hys, hall⟩ := ih htail
      rw [hb] at hR
      refine ⟨by simp [hys, hb], ?_⟩
      intro y hy
      rw [hys, hb] at hy
      rw [hys] at hall
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hR
      · exact hall y hy

/-- Sum of the encoding sizes over a `replicate`d list. -/
theorem bswVszReplicate (k : ℕ) (v : Val) : ((List.replicate k v).map vsz).sum = k * vsz v := by
  induction k with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]; ring

/-- Sum bound for a list all of whose members have encoding size `≤ B`. -/
theorem bswVszSumLe {ys : List Val} {B : ℕ} (h : ∀ y ∈ ys, vsz y ≤ B) :
    (ys.map vsz).sum ≤ ys.length * B := by
  calc (ys.map vsz).sum ≤ (ys.map (fun _ => B)).sum := List.sum_le_sum h
    _ = ys.length * B := Work.ConvR.sum_map_const ys B

/-! ## The per-element word -/

/-- One step of the stretching: copy the parameter `int P` from below the element list to the top
and replicate the disc value `x` exactly `P` times. -/
theorem bswElem (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p P : ℕ) (x : HvdH.Val) (rest : List HvdH.Val),
      (∃ z : ℤ × ℤ, x = HvdH.cfxVal z ∧ HvdH.inDisc p z) →
      HvdH.WordR main prog
        (fun vs => vs = x :: HvdH.Val.int P :: rest)
        (fun _ out => ∃ y : HvdH.Val,
          out = y :: HvdH.Val.int P :: rest ∧
          y = HvdH.ofList (List.replicate P x) ∧
          HvdH.vsz y ≤ (P + 1) * (2 * p + 9))
        (fun _ => K * ((P + 1) * (2 * p + 9) + HvdH.isz (P : ℤ) + 1)) := by
  obtain ⟨pickP, Kp, hpick⟩ := hK.pick
  obtain ⟨repP, Kr, hrep⟩ := hL.replicate
  refine ⟨HvdH.Cmd.seq (pickP 1) repP, 2 * Kp + Kr, ?_⟩
  intro main p P x rest hx
  obtain ⟨z, rfl, hz⟩ := hx
  have hszx : vsz (cfxVal z) ≤ 2 * p + 8 := chirpAux_vsz_cfxVal_le hz
  have hstep1 : WordR main (pickP 1)
      (fun vs => vs = cfxVal z :: Val.int P :: rest)
      (fun _ out => out = Val.int P :: cfxVal z :: Val.int P :: rest)
      (fun _ => 2 * Kp * ((2 * p + 9) + isz (P : ℤ))) := by
    refine Work.Kernel.WordR_conseq (hpick main 1) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      simp only [List.length_cons]
      omega
    · intro vs out hvs hout
      rw [hvs] at hout
      rw [hout]
      simp
    · intro vs hvs
      rw [hvs]
      have hsum : (((cfxVal z :: Val.int P :: rest).take 2).map vsz).sum
          ≤ (2 * p + 8) + isz (P : ℤ) := by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Work.ConvR.vsz_int]
        omega
      have h1 : (((cfxVal z :: Val.int P :: rest).take 2).map vsz).sum + 1
          ≤ (2 * p + 9) + isz (P : ℤ) := by omega
      calc Kp * (1 + 1) * ((((cfxVal z :: Val.int P :: rest).take 2).map vsz).sum + 1)
          ≤ Kp * 2 * ((2 * p + 9) + isz (P : ℤ)) := Nat.mul_le_mul_left (Kp * 2) h1
        _ = 2 * Kp * ((2 * p + 9) + isz (P : ℤ)) := by ring
  have hstep2 : WordR main repP
      (fun vs => vs = Val.int P :: cfxVal z :: Val.int P :: rest)
      (fun _ out => ∃ y : Val, out = y :: Val.int P :: rest ∧
        y = ofList (List.replicate P (cfxVal z)) ∧ vsz y ≤ (P + 1) * (2 * p + 9))
      (fun _ => Kr * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1)) := by
    refine Work.Kernel.WordR_conseq (hrep main P (cfxVal z)) ?_ ?_ ?_
    · intro vs hvs
      rw [hvs]
      exact ⟨Val.int P :: rest, rfl⟩
    · intro vs out hvs hout
      rw [hvs] at hout
      obtain ⟨r, hvr, houtr⟩ := hout
      have h2 : Val.int P :: rest = r := (List.cons.inj (List.cons.inj hvr).2).2
      refine ⟨ofList (List.replicate P (cfxVal z)), ?_, rfl, ?_⟩
      · rw [houtr, h2]
      · rw [Work.ConvR.vsz_ofList, bswVszReplicate, List.length_replicate]
        have h1 : P * vsz (cfxVal z) + P + 1 ≤ (P + 1) * (2 * p + 9) := by
          have h2 : P * vsz (cfxVal z) ≤ P * (2 * p + 8) := Nat.mul_le_mul_left P hszx
          have h3 : P * (2 * p + 8) + P + 1 ≤ (P + 1) * (2 * p + 9) := by
            have e : (P + 1) * (2 * p + 9) = P * (2 * p + 8) + P + (2 * p + 9) := by ring
            rw [e]; omega
          omega
        exact h1
    · intro vs hvs
      have h1 : (P + 1) * (vsz (cfxVal z) + 1) ≤ (P + 1) * (2 * p + 9) :=
        Nat.mul_le_mul_left (P + 1) (by omega)
      exact Nat.mul_le_mul_left Kr (by omega)
  have hmid : ∀ vs mid, (vs = cfxVal z :: Val.int P :: rest) →
      (mid = Val.int P :: cfxVal z :: Val.int P :: rest) →
      (mid = Val.int ↑P :: cfxVal z :: Val.int P :: rest) ∧
      Kr * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1)
        ≤ Kr * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1) := by
    rintro vs mid _ hmid
    exact ⟨hmid, le_rfl⟩
  have hcomp := Work.Kernel.WordR_seq (p := pickP 1) (q := repP) hstep1 hstep2 hmid
  refine Work.Kernel.WordR_conseq (p := HvdH.Cmd.seq (pickP 1) repP) hcomp (fun _ h => h) ?_ ?_
  · rintro vs out _ ⟨mid, hmid1, y, hout1, hy, hbnd⟩
    exact ⟨y, hout1, hy, hbnd⟩
  · intro _ _
    have ha : (2 * p + 9) + isz (P : ℤ) ≤ (P + 1) * (2 * p + 9) + isz (P : ℤ) + 1 := by
      have h : 2 * p + 9 ≤ (P + 1) * (2 * p + 9) := by
        have e : (P + 1) * (2 * p + 9) = (2 * p + 9) + P * (2 * p + 9) := by ring
        rw [e]; omega
      omega
    calc 2 * Kp * ((2 * p + 9) + isz (P : ℤ))
          + Kr * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1)
        ≤ 2 * Kp * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1)
          + Kr * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left (2 * Kp) ha) _
      _ = (2 * Kp + Kr) * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1) := by ring

/-- **`Work.Transform.blendStretchWord`** (paper §3, the "stretch" step): repeat every entry of a
disc vector `P` times. -/
theorem blendStretchWord (hK : HvdH.KernelLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p t P : ℕ) (c : List (ℤ × ℤ)) (rest : List HvdH.Val),
      c.length = t → HvdH.InDiscVec p t c →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal c :: HvdH.Val.int P :: HvdH.Val.int p :: HvdH.Val.int t :: rest)
        (fun vs out => ∃ X : List HvdH.Val,
          out = HvdH.ofList X :: HvdH.Val.int P :: HvdH.Val.int p :: HvdH.Val.int t :: rest ∧
          X.length = t * P ∧
          ∀ a < t, ∀ b < P, X.getD (a * P + b) HvdH.Val.nil = HvdH.cfxVal (c.getD a (0, 0)))
        (fun _ => K * ((t + 1) * ((P + 1) * (p + 1) ^ 2 + 1) + 1)) := by
  obtain ⟨mapP, Km, hmap⟩ := hK.mapList
  obtain ⟨flaP, Kf, hfla⟩ := hL.flatten
  obtain ⟨elemP, Ke, helem⟩ := bswElem hK hL
  refine ⟨HvdH.Cmd.seq (mapP elemP) flaP, 12 * (Ke + Km + Kf) + 1, ?_⟩
  intro main p t P c rest hlen hdisc
  set xs : List Val := c.map cfxVal with hxs
  set xss : List (List Val) := xs.map (fun x => List.replicate P x) with hxss
  have hper : ∀ x : Val, (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) →
      WordR main elemP (fun vs => vs = x :: Val.int P :: Val.int p :: Val.int t :: rest)
        (fun _ out => ∃ y : Val, out = y :: Val.int P :: Val.int p :: Val.int t :: rest ∧
          (y = ofList (List.replicate P x) ∧ vsz y ≤ (P + 1) * (2 * p + 9)) ∧
          vsz y ≤ (P + 1) * (2 * p + 9))
        (fun _ => Ke * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1)) := by
    intro x hx
    refine Work.Kernel.WordR_conseq (helem main p P x (Val.int p :: Val.int t :: rest) hx)
      (fun _ h => h) ?_ (fun _ _ => le_rfl)
    rintro vs out _ ⟨y, hout, hy, hbnd⟩
    exact ⟨y, hout, ⟨hy, hbnd⟩, hbnd⟩
  have hxsP : ∀ x ∈ xs, (∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z) ∧
      vsz x ≤ (P + 1) * (2 * p + 9) := by
    intro x hx
    rw [hxs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    refine ⟨⟨z, rfl, hdisc.2 z hz⟩, ?_⟩
    have h1 : vsz (cfxVal z) ≤ 2 * p + 8 := chirpAux_vsz_cfxVal_le (hdisc.2 z hz)
    have h2 : 2 * p + 8 ≤ (P + 1) * (2 * p + 9) := by
      have e : (P + 1) * (2 * p + 9) = P * (2 * p + 9) + (2 * p + 9) := by ring
      rw [e]; omega
    omega
  have hmapW := hmap main elemP (Val.int P :: Val.int p :: Val.int t :: rest)
      (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ inDisc p z)
      (fun x y => y = ofList (List.replicate P x) ∧ vsz y ≤ (P + 1) * (2 * p + 9))
      (Ke * ((P + 1) * (2 * p + 9) + isz (P : ℤ) + 1))
      ((P + 1) * (2 * p + 9)) hper xs hxsP
  have hflaW := hfla main xss
  have hxss_ofList : xss.map ofList = xs.map (fun x => ofList (List.replicate P x)) := by
    rw [hxss, List.map_map]; rfl
  have hxs_len : xs.length = t := by rw [hxs, List.length_map, hlen]
  have hmid : ∀ vs mid, (vs = ofList xs :: Val.int P :: Val.int p :: Val.int t :: rest) →
      (∃ ys, mid = ofList ys :: Val.int P :: Val.int p :: Val.int t :: rest ∧
        List.Forall₂ (fun x y => y = ofList (List.replicate P x) ∧
          vsz y ≤ (P + 1) * (2 * p + 9)) xs ys) →
      (∃ r, mid = ofList (xss.map ofList) :: r) ∧
      Kf * (vsz (ofList (xss.map ofList)) + 1) ≤
        Kf * ((t + 1) * ((P + 1) * (2 * p + 9) + 1)) := by
    rintro vs mid _ ⟨ys, hmid_eq, hF2⟩
    obtain ⟨hys, hbound⟩ := bswForall₂ hF2
    have hlen_ys : ys.length = t := by rw [hys, List.length_map, hxs_len]
    have hsum_ys : (ys.map vsz).sum ≤ t * ((P + 1) * (2 * p + 9)) := by
      have h := bswVszSumLe hbound
      rwa [hlen_ys] at h
    constructor
    · exact ⟨Val.int P :: Val.int p :: Val.int t :: rest, by rw [hmid_eq, hys, hxss_ofList]⟩
    · rw [hxss_ofList, ← hys, Work.ConvR.vsz_ofList, hlen_ys]
      refine Nat.mul_le_mul_left Kf ?_
      have hL1 : 1 ≤ (P + 1) * (2 * p + 9) := by
        have e : (P + 1) * (2 * p + 9) = P * (2 * p + 9) + (2 * p + 9) := by ring
        rw [e]; omega
      have hexp : (t + 1) * ((P + 1) * (2 * p + 9) + 1)
          = t * ((P + 1) * (2 * p + 9)) + t + ((P + 1) * (2 * p + 9)) + 1 := by ring
      rw [hexp]
      omega
  have hcomp := Work.Kernel.WordR_seq (p := mapP elemP) (q := flaP) hmapW hflaW hmid
  refine Work.Kernel.WordR_conseq (p := HvdH.Cmd.seq (mapP elemP) flaP) hcomp ?_ ?_ ?_
  · intro vs hvs
    rw [hvs, hxs]
    rfl
  · rintro vs out _ ⟨mid, ⟨ys, hmid_eq, hF2⟩, r, hmid2, hout⟩
    obtain ⟨-, hbound⟩ := bswForall₂ hF2
    have hr : r = Val.int P :: Val.int p :: Val.int t :: rest := by
      rw [hmid_eq] at hmid2
      exact ((List.cons.inj hmid2).2).symm
    refine ⟨xss.flatten, ?_, ?_, ?_⟩
    · rw [hout, hr]
    · have h1 : (xss.flatten).length = xs.length * P := by
        rw [hxss, length_map_replicate_flatten]
      rw [h1, hxs_len]
    · intro a ha b hb
      have hxa : a < xs.length := by rw [hxs_len]; exact ha
      have h1 : (xss.flatten).getD (a * P + b) Val.nil = xs.getD a Val.nil := by
        rw [hxss]
        exact getD_map_replicate_flatten xs Val.nil P a b hb hxa
      rw [h1, hxs]
      exact bswGetDMap c a (by rw [hlen]; exact ha)
  · intro _ _
    have hxt : xs.length = t := hxs_len
    rw [hxt]
    exact blendStretchCost Ke Km Kf p P t

end Work.Transform
