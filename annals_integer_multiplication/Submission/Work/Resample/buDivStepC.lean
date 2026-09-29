import Mathlib
import Submission.Work.Resample.buDivDefs
import Submission.Work.Resample.buWtKit

/-!
# `Work.Resample.buDivStepC`: the middle step of the shift word of `Work.Resample.buWdDiv`

`Work.Resample.buWdDiv` forms the shift exponent
`k = auPrec p - p + (2α² - 2) = (2p + 98) + buDivZ3 α` from the entries `p` and `α` of the
canonical block.  This module proves the middle step of the chain: from the window

`[buDivZ3 α, Ad, p, α]`

it computes simultaneously `buDivZ5 p = 2·(p+50)` and adds it to the top entry, leaving

`[buDivK p α, Ad, p, α] = [buDivZ5 p + buDivZ3 α, Ad, p, α]`.

The word is `pick 2`, `push 50`, `add` (`50 + p`), `dup`, `add` (`2(p+50)` = `buDivZ5 p`),
`roll 1` (bringing `buDivZ3 α` back on top), `add`.  Every intermediate value has
`isz ≤ buSZ p` (`isz_buDivZ3_le`, `isz_buDivZ4_le`, `isz_buDivZ5_le`, `isz_alpha_le_DSC`), so every
step costs at most the uniform one-step budget `buSBW p Λ` of `Work.Resample.buWtKit` and the
seven steps are absorbed into a single `K (buSZ p + 8)^2` with `K = 7Λ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Size bounds for the intermediate values -/

/-- `buDivZ3 α = 2α² - 2` has at most `2p+2` bits when `α² < p`. -/
theorem isz_buDivZ3_le (p α : ℕ) (_hα : 2 ≤ α) (hαp : α ^ 2 < p) : isz (buDivZ3 α) ≤ buSZ p := by
  have hval : buDivZ2 α = 2 * (α : ℤ) ^ 2 := by unfold buDivZ2 buDivZ1; ring
  have h2 : (buDivZ2 α).natAbs = 2 * α ^ 2 := by
    rw [hval, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    norm_num
  have h3 : ((2 : ℤ)).natAbs = 2 := by norm_num
  have hnat : (buDivZ3 α).natAbs ≤ 2 * p + 2 := by
    have hsub := Int.natAbs_sub_le (buDivZ2 α) (2 : ℤ)
    rw [h2, h3] at hsub
    show (buDivZ2 α - 2).natAbs ≤ 2 * p + 2
    omega
  refine isz_le_buSZ_of_lin (A := 2 * p + 2) (by omega) ?_
  exact le_trans hnat (le_of_lt (Nat.lt_two_pow_self (n := 2 * p + 2)))

/-- `buDivZ4 p = p + 50` fits the uniform size bound. -/
theorem isz_buDivZ4_le (p : ℕ) : isz (buDivZ4 p) ≤ buSZ p := by
  have hval : buDivZ4 p = ((p + 50 : ℕ) : ℤ) := by unfold buDivZ4; push_cast; ring
  refine isz_le_buSZ_of_lin (A := p + 50) (by omega) ?_
  rw [hval, Int.natAbs_natCast]
  exact le_of_lt (Nat.lt_two_pow_self (n := p + 50))

/-- `buDivZ5 p = 2(p+50)` fits the uniform size bound. -/
theorem isz_buDivZ5_le (p : ℕ) : isz (buDivZ5 p) ≤ buSZ p := by
  have hval : buDivZ5 p = ((2 * p + 100 : ℕ) : ℤ) := by unfold buDivZ5 buDivZ4; push_cast; ring
  refine isz_le_buSZ_of_lin (A := 2 * p + 100) (by omega) ?_
  rw [hval, Int.natAbs_natCast]
  exact le_of_lt (Nat.lt_two_pow_self (n := 2 * p + 100))

/-- Under `2 ≤ α` and `α² < p` the entry `α` of the canonical block fits the uniform size bound. -/
theorem isz_alpha_le_DSC (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) : isz ((α : ℤ)) ≤ buSZ p := by
  have hαle : α ≤ α ^ 2 := by
    calc α = α * 1 := by ring
      _ ≤ α * α := Nat.mul_le_mul_left α (by omega)
      _ = α ^ 2 := by ring
  have hαp' : α < p := lt_of_le_of_lt hαle hαp
  refine isz_natCast_le_buSZ_lt (p := p) ?_
  have := Nat.lt_two_pow_self (n := p)
  omega

/-- The middle step of the shift word: form `buDivZ5 p` and add it to `buDivZ3 α`. -/
theorem buDivStepC (KL : HvdH.KernelLib) (IL : HvdH.IntLib) : ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (Ad : ℤ) (hAd : HvdH.isz Ad ≤ Work.Resample.buSZ p) (V : List HvdH.Val), Work.Resample.Pipe main prog ([HvdH.Val.int (Work.Resample.buDivZ3 α), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) ([HvdH.Val.int (Work.Resample.buDivK p α), HvdH.Val.int Ad, HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ)] ++ V) (K * (Work.Resample.buSZ p + 8) ^ 2) := by
  obtain ⟨pickProg, KP, hpick⟩ := KL.pick
  obtain ⟨dupProg, Kdup, hdup⟩ := KL.dup
  obtain ⟨rollProg, Kr, hroll⟩ := KL.roll
  obtain ⟨pushProg, Kpv, hpv⟩ := KL.pushVal
  obtain ⟨addProg, Kad, hadd⟩ := IL.add
  set Λ : ℕ := KP + Kdup + Kr + Kpv + Kad + 1 with hΛ
  have hKP : KP ≤ Λ := by rw [hΛ]; omega
  have hKdup : Kdup ≤ Λ := by rw [hΛ]; omega
  have hKr : Kr ≤ Λ := by rw [hΛ]; omega
  have hKpv : Kpv ≤ Λ := by rw [hΛ]; omega
  have hKad : Kad ≤ Λ := by rw [hΛ]; omega
  refine ⟨Cmd.seq (pickProg 2) (Cmd.seq (pushProg (.int 50))
    (Cmd.seq addProg (Cmd.seq dupProg (Cmd.seq addProg (Cmd.seq (rollProg 1) addProg))))),
    7 * Λ, ?_⟩
  intro main p α hα hαp Ad hAd V
  have hz3 : isz (buDivZ3 α) ≤ buSZ p := isz_buDivZ3_le p α hα hαp
  have hz4 : isz (buDivZ4 p) ≤ buSZ p := isz_buDivZ4_le p
  have hz5 : isz (buDivZ5 p) ≤ buSZ p := isz_buDivZ5_le p
  have hpp : isz ((p : ℤ)) ≤ buSZ p := isz_p_le_buSZ p
  have haa : isz ((α : ℤ)) ≤ buSZ p := isz_alpha_le_DSC p α hα hαp
  have hz50 : isz ((50 : ℤ)) ≤ buSZ p := isz_const_le_buSZ p 50 (by omega)
  -- uniform membership of the windows in the size bound
  have mem4 : ∀ v ∈ ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val),
      vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simpa only [vsz_int] using hz3
    · simpa only [vsz_int] using hAd
    · simpa only [vsz_int] using hpp
    · simpa only [vsz_int] using haa
  have mem5 : ∀ v ∈ ([Val.int (buDivZ5 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ),
      Val.int (α : ℤ)] : List Val), vsz v ≤ buSZ p := by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · simpa only [vsz_int] using hz5
    · simpa only [vsz_int] using hz3
    · simpa only [vsz_int] using hAd
    · simpa only [vsz_int] using hpp
    · simpa only [vsz_int] using haa
  -- ## the seven steps, each of cost `≤ buSBW p Λ`
  -- step 1: `pick 2` copies `p` to the top
  have s1 : Pipe main (pickProg 2)
      ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      ([Val.int (p : ℤ), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      (buSBW p Λ) := by
    have h := Pipe.pick main hpick
      (A := ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
      (k := 2) (by simp)
    refine Pipe.le (Pipe.rw h (by rfl)) ?_
    exact le_buSBW_roll (K := KP) (KS := Λ) hKP (k := 2) (by omega) (by simp) mem4
  -- step 2: push `50`
  have s2 : Pipe main (pushProg (.int 50))
      ([Val.int (p : ℤ), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      ([Val.int (50 : ℤ), Val.int (p : ℤ), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ),
        Val.int (α : ℤ)] : List Val)
      (buSBW p Λ) := by
    have h := Pipe.pushOnAny (main := main)
      (T := ([Val.int (p : ℤ), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)) (hpv main (.int 50))
    refine Pipe.le h ?_
    rw [vsz_int]
    exact le_buSBW_one (K := Kpv) (KS := Λ) hKpv hz50
  -- step 3: `50 + p = buDivZ4 p`
  have s3 : Pipe main addProg
      ([Val.int (50 : ℤ), Val.int (p : ℤ), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ),
        Val.int (α : ℤ)] : List Val)
      ([Val.int (buDivZ4 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := (50 : ℤ)) (b := (p : ℤ)) trivial
    have h1 : Pipe main addProg
        (([Val.int (50 : ℤ), Val.int (p : ℤ)] : List Val) ++
          ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (([Val.int ((50 : ℤ) + (p : ℤ))] : List Val) ++
          ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (Kad * (isz (50 : ℤ) + isz (p : ℤ))) :=
      Pipe.appendTail _ h0
    refine Pipe.le (Pipe.rw h1 (by rfl)) ?_
    exact le_buSBW_two (K := Kad) (KS := Λ) hKad hz50 hpp
  -- step 4: `dup`
  have s4 : Pipe main dupProg
      ([Val.int (buDivZ4 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      ([Val.int (buDivZ4 p), Val.int (buDivZ4 p), Val.int (buDivZ3 α), Val.int Ad,
        Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      (buSBW p Λ) := by
    have h := Pipe.appendTail ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
      List Val) (Pipe.dup main hdup (.int (buDivZ4 p)))
    refine Pipe.le h ?_
    rw [vsz_int]
    exact le_buSBW_one (K := Kdup) (KS := Λ) hKdup hz4
  -- step 5: `buDivZ4 p + buDivZ4 p = buDivZ5 p`
  have s5 : Pipe main addProg
      ([Val.int (buDivZ4 p), Val.int (buDivZ4 p), Val.int (buDivZ3 α), Val.int Ad,
        Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      ([Val.int (buDivZ5 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := buDivZ4 p) (b := buDivZ4 p) trivial
    have h1 : Pipe main addProg
        (([Val.int (buDivZ4 p), Val.int (buDivZ4 p)] : List Val) ++
          ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (([Val.int (buDivZ4 p + buDivZ4 p)] : List Val) ++
          ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (Kad * (isz (buDivZ4 p) + isz (buDivZ4 p))) :=
      Pipe.appendTail _ h0
    refine Pipe.le (Pipe.rw h1 (by rfl)) ?_
    exact le_buSBW_two (K := Kad) (KS := Λ) hKad hz4 hz4
  -- step 6: `roll 1` brings `buDivZ3 α` back to the top
  have s6 : Pipe main (rollProg 1)
      ([Val.int (buDivZ5 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      ([Val.int (buDivZ3 α), Val.int (buDivZ5 p), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      (buSBW p Λ) := by
    have h := Pipe.roll main hroll
      (A := ([Val.int (buDivZ5 p), Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ),
        Val.int (α : ℤ)] : List Val)) (k := 1) (by simp)
    refine Pipe.le (Pipe.rw h (by rfl)) ?_
    exact le_buSBW_roll (K := Kr) (KS := Λ) hKr (k := 1) (by omega) (by simp) mem5
  -- step 7: `buDivZ3 α + buDivZ5 p = buDivK p α`
  have s7 : Pipe main addProg
      ([Val.int (buDivZ3 α), Val.int (buDivZ5 p), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] :
        List Val)
      ([Val.int (buDivK p α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      (buSBW p Λ) := by
    have h0 := Pipe.binOp (hadd main) (a := buDivZ3 α) (b := buDivZ5 p) trivial
    have h1 : Pipe main addProg
        (([Val.int (buDivZ3 α), Val.int (buDivZ5 p)] : List Val) ++
          ([Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (([Val.int (buDivZ3 α + buDivZ5 p)] : List Val) ++
          ([Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val))
        (Kad * (isz (buDivZ3 α) + isz (buDivZ5 p))) :=
      Pipe.appendTail _ h0
    have hsum : buDivZ3 α + buDivZ5 p = buDivK p α := by unfold buDivK; ring
    refine Pipe.le (Pipe.rw h1 (by rw [hsum]; rfl)) ?_
    exact le_buSBW_two (K := Kad) (KS := Λ) hKad hz3 hz5
  -- ## assembly
  have hall : Pipe main
      (Cmd.seq (pickProg 2) (Cmd.seq (pushProg (.int 50))
        (Cmd.seq addProg (Cmd.seq dupProg (Cmd.seq addProg (Cmd.seq (rollProg 1) addProg))))))
      ([Val.int (buDivZ3 α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      ([Val.int (buDivK p α), Val.int Ad, Val.int (p : ℤ), Val.int (α : ℤ)] : List Val)
      (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ +
        buSBW p Λ)))))) :=
    Pipe.comp s1 (Pipe.comp s2 (Pipe.comp s3 (Pipe.comp s4 (Pipe.comp s5 (Pipe.comp s6 s7)))))
  refine Pipe.le (Pipe.appendTail V hall) ?_
  have hsum7 : buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ + (buSBW p Λ +
      buSBW p Λ))))) ≤ 7 * buSBW p Λ := by
    simp only [buSBW]; ring_nf; omega
  refine le_trans hsum7 ?_
  rw [show 7 * buSBW p Λ = 7 * Λ * (buSZ p + 8) ^ 2 from by simp only [buSBW]; ring]

end Work.Resample
