import Mathlib
import Submission.Work.KronP.defs

namespace Work.KronP

open HvdH

/-!
# `Work.KronP.mapSndWord`: reading off the second coordinate of a coefficient vector

The word maps a coefficient vector `cvecVal xs = ofList (xs.map cfxVal)` (each entry is the pair
value `cons (int a) (int b)`) to the integer list `zsVal (xs.map Prod.snd)` (each entry `int b`).

The implementation is `KernelLib.mapList` applied to the per-element word
"`KernelLib.unconsV` then `KernelLib.drop`", which turns `cons (int a) (int b) :: rest` into
`int b :: rest` at cost proportional to the encoding size of the input value.  The only thing
beyond the generic `mapList` law is the extraction of the result list from the `∃ ys` produced by
`mapList` (same shape as `Work.Main.word.conjExtract`).
-/

/-- Read off the second coordinate of a pair value.  The second case is never reached on the
values that occur in a `cvecVal`. -/
def sndVal : Val → Val
  | .cons (.int _) (.int b) => .int b
  | _ => .int 0

@[simp] theorem sndVal_cons_int (a b : ℤ) :
    sndVal (.cons (.int a) (.int b)) = .int b := rfl

@[simp] theorem sndVal_cfxVal (z : ℤ × ℤ) : sndVal (cfxVal z) = .int z.2 := rfl

/-- The second coordinate of a fixed-point number has encoding size at most that of the number. -/
theorem isz_snd_le_vsz_cfxVal (z : ℤ × ℤ) : isz z.2 ≤ vsz (cfxVal z) := by
  rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, Work.ConvR.vsz_cons,
    Work.ConvR.vsz_int, Work.ConvR.vsz_int]
  omega

theorem vsz_sndVal_cfxVal (z : ℤ × ℤ) : vsz (sndVal (cfxVal z)) ≤ vsz (cfxVal z) := by
  rw [sndVal_cfxVal, Work.ConvR.vsz_int]
  exact isz_snd_le_vsz_cfxVal z

/-! ## Generic `WordR` plumbing -/

/-- The consequence (monotonicity) rule for `WordR`. -/
theorem wrdConseq {main p : Cmd} {P P' : List Val → Prop} {Q Q' : List Val → List Val → Prop}
    {C C' : List Val → ℕ} (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' := by
  intro vs hP' s R hR
  obtain ⟨out, s', n, hQh, he, hn, hstk, hoth⟩ := h vs (hP vs hP') s R hR
  exact ⟨out, s', n, hQ vs out hP' hQh, he, le_trans hn (hC vs hP'), hstk, hoth⟩

/-- Sequential composition of two constant-cost words with a fixed intermediate value stack. -/
theorem wrdSeq {main p q : Cmd} {A B : List Val} {R : List Val → Prop} {c₁ c₂ : ℕ}
    (h1 : WordR main p (fun vs => vs = A) (fun _ out => out = B) (fun _ => c₁))
    (h2 : WordR main q (fun vs => vs = B) (fun _ out => R out) (fun _ => c₂)) :
    WordR main (.seq p q) (fun vs => vs = A) (fun _ out => R out) (fun _ => c₁ + c₂) := by
  intro vs hvs s T hT
  rw [hvs] at hT
  obtain ⟨mid, s₂, n₁, hQ, he₁, hn₁, hstk₁, hoth₁⟩ := h1 A rfl s T hT
  rw [hQ] at hstk₁
  obtain ⟨out, s₃, n₂, hQ', he₂, hn₂, hstk₂, hoth₂⟩ := h2 B rfl s₂ T hstk₁
  exact ⟨out, s₃, n₁ + n₂, hQ', Eval.seq he₁ he₂, Nat.add_le_add hn₁ hn₂, hstk₂,
    fun k hk => by rw [hoth₂ k hk, hoth₁ k hk]⟩

/-! ## Cost arithmetic -/

/-- Cost of the per-element word `unconsV ; drop` on `cons (int a) (int b)`, absorbed into a
multiple of the encoding size of that value (`s = isz a`, `t = isz b`). -/
theorem peCost (Ku Kd s t : ℕ) : Ku + Kd * (s + 1) ≤ (Ku + Kd) * (s + t + 2) := by
  have h1 : Ku ≤ Ku * (s + t + 2) := by
    conv_lhs => rw [← Nat.mul_one Ku]
    exact Nat.mul_le_mul_left Ku (by omega : 1 ≤ s + t + 2)
  have h2 : Kd * (s + 1) ≤ Kd * (s + t + 2) := Nat.mul_le_mul_left _ (by omega)
  have h3 : (Ku + Kd) * (s + t + 2) = Ku * (s + t + 2) + Kd * (s + t + 2) := Nat.add_mul _ _ _
  omega

/-- The `mapList` cost `n * (c + Km * (L+1)) + Km` with `c = Cu * (L+1)` is bounded by
`(Cu+Km+1) * (n * (L+1) + L + 1)`. -/
theorem mapSndCost (Cu Km n L : ℕ) :
    n * (Cu * (L + 1) + Km * (L + 1)) + Km ≤
      (Cu + Km + 1) * (n * (L + 1) + L + 1) := by
  have hM : 1 ≤ L + 1 := by omega
  have h1 : Cu * (L + 1) + Km * (L + 1) = (Cu + Km) * (L + 1) := by ring
  rw [h1]
  have h2 : (Cu + Km) * (L + 1) ≤ (Cu + Km + 1) * (L + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : Km ≤ (Cu + Km + 1) * (L + 1) := by
    have h3a : Km ≤ Km * (L + 1) := by
      conv_lhs => rw [← Nat.mul_one Km]
      exact Nat.mul_le_mul_left Km hM
    exact le_trans h3a (Nat.mul_le_mul_right _ (by omega))
  calc n * ((Cu + Km) * (L + 1)) + Km
      ≤ n * ((Cu + Km + 1) * (L + 1)) + (Cu + Km + 1) * (L + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left n h2) h3
    _ = (Cu + Km + 1) * (n * (L + 1) + L + 1) := by ring

/-! ## The per-element word -/

/-- **Element word.**  `unconsV ; drop` turns `cons (int a) (int b) :: tl` into `int b :: tl` in
cost proportional to the encoding size of the input value. -/
theorem sndElem (hK : HvdH.KernelLib) :
    ∃ (q : HvdH.Cmd) (C : ℕ), ∀ (main : HvdH.Cmd) (a b : ℤ) (tl : List HvdH.Val),
      HvdH.WordR main q
        (fun vs => vs = .cons (.int a) (.int b) :: tl)
        (fun _ out => out = .int b :: tl)
        (fun _ => C * (vsz (.cons (.int a) (.int b)) + 1)) := by
  obtain ⟨uncP, Ku, hunc⟩ := hK.unconsV
  obtain ⟨dropP, Kd, hdrop⟩ := hK.drop
  refine ⟨.seq uncP dropP, Ku + Kd, ?_⟩
  intro main a b tl
  -- `cons (int a) (int b) :: tl ↦ int a :: int b :: tl`
  have h1 : WordR main uncP (fun vs => vs = .cons (.int a) (.int b) :: tl)
      (fun _ out => out = .int a :: .int b :: tl) (fun _ => Ku) := by
    refine wrdConseq (hunc main) ?_ ?_ ?_
    · intro vs hvs; exact ⟨.int a, .int b, tl, hvs⟩
    · intro vs out hvs hq
      obtain ⟨a', b', tl', hvs', hout⟩ := hq
      rw [hvs] at hvs'
      injection hvs' with h1' h2'
      injection h1' with ha hb
      rw [hout, ← ha, ← hb, ← h2']
    · intro vs hvs; exact le_rfl
  -- `int a :: int b :: tl ↦ int b :: tl`
  have h2 : WordR main dropP (fun vs => vs = .int a :: .int b :: tl)
      (fun _ out => out = .int b :: tl) (fun _ => Kd * (isz a + 1)) := by
    refine wrdConseq (hdrop main) ?_ ?_ ?_
    · intro vs hvs; rw [hvs]; exact List.cons_ne_nil _ _
    · intro vs out hvs hq
      obtain ⟨v, tl', hvs', hout⟩ := hq
      rw [hvs] at hvs'
      injection hvs' with hv ht
      rw [hout, ← ht]
    · intro vs hvs
      rw [hvs]
      show Kd * (vsz (Val.int a) + 1) ≤ Kd * (isz a + 1)
      rw [Work.ConvR.vsz_int]
  have h12 := wrdSeq h1 h2
  refine wrdConseq h12 ?_ ?_ ?_
  · intro vs hvs; exact hvs
  · intro vs out hvs hout; exact hout
  · intro vs hvs
    show Ku + Kd * (isz a + 1) ≤ (Ku + Kd) * (vsz (.cons (.int a) (.int b)) + 1)
    rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_int, Work.ConvR.vsz_int]
    have h : isz a + isz b + 1 + 1 = isz a + isz b + 2 := by omega
    rw [h]
    exact peCost Ku Kd (isz a) (isz b)

/-! ## Extraction of the result from `mapList` -/

/-- `List.Forall₂` of the pointwise relation `y = sndVal x` over `zs.map cfxVal` determines the
whole list `ys`. -/
theorem forall₂_snd_eq_map : ∀ (zs : List (ℤ × ℤ)) {ys : List Val},
    List.Forall₂ (fun x y => y = sndVal x) (zs.map cfxVal) ys → ys = (zs.map cfxVal).map sndVal
  | [], ys, h => by cases h with | nil => rfl
  | z :: zs, ys, h => by
      cases h with
      | cons hx htl =>
        rw [forall₂_snd_eq_map zs htl]
        simp only [List.map_cons]
        rw [hx]

/-- A list of values pointwise `sndVal` of `zs.map cfxVal` encodes the second coordinates. -/
theorem sndExtract {zs : List (ℤ × ℤ)} {ys : List Val}
    (h : List.Forall₂ (fun x y => y = sndVal x) (zs.map cfxVal) ys) :
    ofList ys = zsVal (zs.map Prod.snd) := by
  rw [forall₂_snd_eq_map zs h]
  simp only [zsVal, List.map_map, Function.comp_def, sndVal_cfxVal]

/-! ## The main word -/

theorem mapSndWord (hK : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (xs : List (ℤ × ℤ)) (L : ℕ) (tl : List HvdH.Val),
        (∀ z ∈ xs, HvdH.vsz (HvdH.cfxVal z) ≤ L) →
        HvdH.WordR main prog
          (fun vs => vs = HvdH.cvecVal xs :: tl)
          (fun _ out => out = Work.KronP.zsVal (xs.map Prod.snd) :: tl)
          (fun _ => K * (xs.length * (L + 1) + L + 1)) := by
  obtain ⟨elemP, Ce, helem⟩ := sndElem hK
  obtain ⟨mapP, Km, hmap⟩ := hK.mapList
  refine ⟨mapP elemP, Ce + Km + 1, ?_⟩
  intro main xs L tl hL
  -- the per-element word, with the disc-size hypothesis absorbed
  have hbody : ∀ x, (∃ z : ℤ × ℤ, x = cfxVal z ∧ vsz x ≤ L) →
      WordR main elemP (fun vs => vs = x :: tl)
        (fun _ out => ∃ y : Val, out = y :: tl ∧ y = sndVal x ∧ vsz y ≤ L)
        (fun _ => Ce * (L + 1)) := by
    intro x hx
    obtain ⟨z, rfl, hsz⟩ := hx
    have hsz' : vsz (Val.cons (.int z.1) (.int z.2)) ≤ L := hsz
    refine wrdConseq (helem main z.1 z.2 tl) ?_ ?_ ?_
    · intro vs hvs; simpa only [cfxVal] using hvs
    · intro vs out hvs hout
      refine ⟨sndVal (cfxVal z), ?_, rfl, ?_⟩
      · rw [hout, sndVal_cfxVal]
      · rw [sndVal_cfxVal, Work.ConvR.vsz_int]
        exact le_trans (isz_snd_le_vsz_cfxVal z) hsz
    · intro vs hvs
      exact Nat.mul_le_mul_left _ (by omega)
  -- every element of the vector satisfies the precondition
  have hxs : ∀ x ∈ xs.map cfxVal,
      (∃ z : ℤ × ℤ, x = cfxVal z ∧ vsz x ≤ L) ∧ vsz x ≤ L := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hx
    subst hzx
    exact ⟨⟨z, rfl, hL z hz⟩, hL z hz⟩
  have hmain := hmap main elemP tl (fun x => ∃ z : ℤ × ℤ, x = cfxVal z ∧ vsz x ≤ L)
    (fun x y => y = sndVal x) (Ce * (L + 1)) L hbody (xs.map cfxVal) hxs
  refine wrdConseq hmain ?_ ?_ ?_
  · intro vs hvs
    simpa only [cvecVal] using hvs
  · intro vs out hvs hpost
    obtain ⟨ys, hout, hF2⟩ := hpost
    rw [hout, sndExtract hF2]
  · intro vs hvs
    rw [List.length_map]
    exact mapSndCost Ce Km xs.length L

end Work.KronP
