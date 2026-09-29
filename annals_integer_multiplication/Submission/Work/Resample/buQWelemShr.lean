import Mathlib
import Submission.Work.Resample.buQWelemKit

/-!
# `Work.Resample.buQWelemShr`: the per-element halving word

The word sends the fixed window `[cfxVal a, int pp]` to `[cfxVal (tdiv a.1 2^pp, tdiv a.2 2^pp)]`,
i.e. it halves (with truncation) the fixed-point complex number `a` shifted by `pp` bits:

```
[A, pp] →ᵘⁿᶜ [a₁,a₂,pp] →ᵖⁱᶜᵏ² [pp,a₁,a₂,pp] →ʳᵒˡˡ² [a₂,pp,a₁,pp] →ˢʰʳᵀ [t₂,a₁,pp]
        →ʳᵒˡˡ² [pp,t₂,a₁] →ʳᵒˡˡ² [a₁,pp,t₂] →ˢʰʳᵀ [t₁,t₂] →ᶜᵒⁿˢ [cfxVal (t₁,t₂)]
```

with `tᵢ = Int.tdiv aᵢ 2^pp`; total cost `≤ (Ku + 120·KP + 360·KR + 4·Ksh + Kcs)·(P+1)` where
`Ku, KP, KR, Ksh, Kcs` are the uniform constants of `unconsV`, `pick`, `roll`, `shrT`, `consV`.
The toolkit `Submission/Work/Resample/buQWelemKit.lean` provides every intermediate `Pipe` step
(`bu_unconsTail`, `bu_pickK`, `bu_rollK`, `bu_binOpTail`, `bu_consTail`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Main.word

local infixl:68 " ;;; " => HvdH.Cmd.seq

/-! ## membership helpers for the window-size obligations -/

theorem buQWelemShr_mem3 {v1 v2 v3 : Val} {M : ℕ} (h1 : vsz v1 ≤ M) (h2 : vsz v2 ≤ M)
    (h3 : vsz v3 ≤ M) : ∀ v ∈ ([v1, v2, v3] : List Val), vsz v ≤ M := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> assumption

theorem buQWelemShr_mem4 {v1 v2 v3 v4 : Val} {M : ℕ} (h1 : vsz v1 ≤ M) (h2 : vsz v2 ≤ M)
    (h3 : vsz v3 ≤ M) (h4 : vsz v4 ≤ M) :
    ∀ v ∈ ([v1, v2, v3, v4] : List Val), vsz v ≤ M := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> assumption

/-- **The halving word**: `cfxVal a :: int pp :: rest ↦ cfxVal (a.1 /ᵗ 2^pp, a.2 /ᵗ 2^pp) :: rest`,
cost `≤ Kc·(P+1)` when `isz a.1, isz a.2, isz (pp:ℤ) ≤ P`. -/
theorem buQWelemShr (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (P : ℕ) (pp : ℕ) (a : ℤ × ℤ),
        HvdH.isz a.1 ≤ P → HvdH.isz a.2 ≤ P → HvdH.isz (pp : ℤ) ≤ P →
        HvdH.WordR main q
          (fun vs => ∃ rest, vs = HvdH.cfxVal a :: HvdH.Val.int (pp : ℤ) :: rest)
          (fun vs out => ∃ rest, vs = HvdH.cfxVal a :: HvdH.Val.int (pp : ℤ) :: rest ∧
            out = HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ pp), Int.tdiv a.2 ((2 : ℤ) ^ pp)) :: rest)
          (fun _ => Kc * (P + 1)) := by
  obtain ⟨uncP, Ku, hunc⟩ := KL.unconsV
  obtain ⟨pickP, KP, hpick⟩ := KL.pick
  obtain ⟨rollP, KR, hroll⟩ := KL.roll
  obtain ⟨consP, Kcs, hcons⟩ := KL.consV
  obtain ⟨shrP, Ksh, hshr⟩ := IL.shrT
  refine ⟨uncP ;;; pickP 2 ;;; rollP 2 ;;; shrP ;;; rollP 2 ;;; rollP 2 ;;; shrP ;;; consP,
    Ku + 120 * KP + 360 * KR + 4 * Ksh + Kcs, ?_⟩
  intro main P pp a ha1 ha2 hpp
  -- size facts
  have e_a1 : vsz (Val.int a.1) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_a2 : vsz (Val.int a.2) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_pp : vsz (Val.int (pp : ℤ)) ≤ 3 * P + 4 := by rw [vsz_int]; omega
  have e_t1 : vsz (Val.int (Int.tdiv a.1 ((2 : ℤ) ^ pp))) ≤ 3 * P + 4 :=
    vsz_int_le (isz_tdiv_le ha1 pp)
  have e_t2 : vsz (Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))) ≤ 3 * P + 4 :=
    vsz_int_le (isz_tdiv_le ha2 pp)
  -- step 1: split the complex value `cfxVal a` into its two coordinates
  have H1 : Pipe main uncP
      [Val.cons (Val.int a.1) (Val.int a.2), Val.int (pp : ℤ)]
      [Val.int a.1, Val.int a.2, Val.int (pp : ℤ)] (Ku * (P + 1)) :=
    Pipe.le (bu_unconsTail main hunc (Val.int a.1) (Val.int a.2) [Val.int (pp : ℤ)])
      (bu_const_bound Ku P)
  -- step 2: copy the shift `pp` to the front
  have H2 : Pipe main (pickP 2) [Val.int a.1, Val.int a.2, Val.int (pp : ℤ)]
      [Val.int (pp : ℤ), Val.int a.1, Val.int a.2, Val.int (pp : ℤ)] (120 * KP * (P + 1)) :=
    bu_pickK main hpick (A := [Val.int a.1, Val.int a.2, Val.int (pp : ℤ)]) (k := 2) (P := P)
      (by simp) (by omega) (buQWelemShr_mem3 e_a1 e_a2 e_pp)
  -- step 3: bring `a₂` to the top
  have H3 : Pipe main (rollP 2)
      [Val.int (pp : ℤ), Val.int a.1, Val.int a.2, Val.int (pp : ℤ)]
      [Val.int a.2, Val.int (pp : ℤ), Val.int a.1, Val.int (pp : ℤ)] (120 * KR * (P + 1)) :=
    bu_rollK main hroll
      (A := [Val.int (pp : ℤ), Val.int a.1, Val.int a.2, Val.int (pp : ℤ)]) (k := 2) (P := P)
      (by simp) (by omega) (buQWelemShr_mem4 e_pp e_a1 e_a2 e_pp)
  -- step 4: `t₂ = tdiv a₂ 2^pp`
  have H4o : Pipe main shrP
      [Val.int a.2, Val.int (pp : ℤ), Val.int a.1, Val.int (pp : ℤ)]
      [Val.int (Int.tdiv a.2 (2 ^ ((pp : ℤ)).toNat)), Val.int a.1, Val.int (pp : ℤ)]
      (2 * Ksh * (P + 1)) :=
    bu_binOpTail main (hshr main) (a := a.2) (b := (pp : ℤ)) (Int.natCast_nonneg pp)
      (bu_add_bound ha2 hpp) [Val.int a.1, Val.int (pp : ℤ)]
  have H4 : Pipe main shrP
      [Val.int a.2, Val.int (pp : ℤ), Val.int a.1, Val.int (pp : ℤ)]
      [Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1, Val.int (pp : ℤ)]
      (2 * Ksh * (P + 1)) :=
    Pipe.rw H4o (by rw [Int.toNat_natCast])
  -- step 5
  have H5 : Pipe main (rollP 2)
      [Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1, Val.int (pp : ℤ)]
      [Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1]
      (120 * KR * (P + 1)) :=
    bu_rollK main hroll
      (A := [Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1, Val.int (pp : ℤ)])
      (k := 2) (P := P) (by simp) (by omega) (buQWelemShr_mem3 e_t2 e_a1 e_pp)
  -- step 6
  have H6 : Pipe main (rollP 2)
      [Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1]
      [Val.int a.1, Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      (120 * KR * (P + 1)) :=
    bu_rollK main hroll
      (A := [Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp)), Val.int a.1])
      (k := 2) (P := P) (by simp) (by omega) (buQWelemShr_mem3 e_pp e_t2 e_a1)
  -- step 7: `t₁ = tdiv a₁ 2^pp`
  have H7o : Pipe main shrP
      [Val.int a.1, Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      [Val.int (Int.tdiv a.1 (2 ^ ((pp : ℤ)).toNat)),
        Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))] (2 * Ksh * (P + 1)) :=
    bu_binOpTail main (hshr main) (a := a.1) (b := (pp : ℤ)) (Int.natCast_nonneg pp)
      (bu_add_bound ha1 hpp) [Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
  have H7 : Pipe main shrP
      [Val.int a.1, Val.int (pp : ℤ), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      [Val.int (Int.tdiv a.1 ((2 : ℤ) ^ pp)), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      (2 * Ksh * (P + 1)) :=
    Pipe.rw H7o (by rw [Int.toNat_natCast])
  -- step 8: repack
  have H8 : Pipe main consP
      [Val.int (Int.tdiv a.1 ((2 : ℤ) ^ pp)), Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ pp), Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      (Kcs * (P + 1)) :=
    Pipe.le (bu_consTail main hcons (Val.int (Int.tdiv a.1 ((2 : ℤ) ^ pp)))
      (Val.int (Int.tdiv a.2 ((2 : ℤ) ^ pp))) []) (bu_const_bound Kcs P)
  -- the chain
  have hchain : Pipe main
      (uncP ;;; pickP 2 ;;; rollP 2 ;;; shrP ;;; rollP 2 ;;; rollP 2 ;;; shrP ;;; consP)
      [Val.cons (Val.int a.1) (Val.int a.2), Val.int (pp : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ pp), Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      (Ku * (P + 1) + 120 * KP * (P + 1) + 120 * KR * (P + 1) + 2 * Ksh * (P + 1)
        + 120 * KR * (P + 1) + 120 * KR * (P + 1) + 2 * Ksh * (P + 1) + Kcs * (P + 1)) :=
    Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp (Pipe.comp H1 H2) H3) H4)
      H5) H6) H7) H8
  have hsum : Ku * (P + 1) + 120 * KP * (P + 1) + 120 * KR * (P + 1) + 2 * Ksh * (P + 1)
      + 120 * KR * (P + 1) + 120 * KR * (P + 1) + 2 * Ksh * (P + 1) + Kcs * (P + 1)
      = (Ku + 120 * KP + 360 * KR + 4 * Ksh + Kcs) * (P + 1) := by ring
  have hfin : Pipe main
      (uncP ;;; pickP 2 ;;; rollP 2 ;;; shrP ;;; rollP 2 ;;; rollP 2 ;;; shrP ;;; consP)
      [Val.cons (Val.int a.1) (Val.int a.2), Val.int (pp : ℤ)]
      [HvdH.cfxVal (Int.tdiv a.1 ((2 : ℤ) ^ pp), Int.tdiv a.2 ((2 : ℤ) ^ pp))]
      ((Ku + 120 * KP + 360 * KR + 4 * Ksh + Kcs) * (P + 1)) :=
    Pipe.le hchain (le_of_eq hsum)
  intro vs hpre s R hR
  obtain ⟨rest, hvs⟩ := hpre
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := hfin rest vs hvs s R hR
  exact ⟨out, s', n, ⟨rest, hvs, hout⟩, hev, hn, hstk, hoth⟩

end Work.Resample
