import Mathlib
import Submission.Work.Resample.auSetupDefs
import Submission.Work.Resample.auSplit
import Submission.Work.Resample.auPeel
import Submission.Work.Resample.auWinSlice
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auWtSize
import Submission.Work.Resample.auStreamSz
import Submission.Work.Resample.auOffCop
import Submission.Work.Resample.auMLe
import Submission.Work.Resample.auSetupRecWord
import Submission.Work.ConvR.basic

/-!
# Auxiliary lemmas for the setup word of the resampling (`Work.Resample.auSetupRun`)
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.Resample

open HvdH

/-! ## List and flag helpers -/

/-- Flattening commutes with the pointwise image of a replicated list. -/
theorem auSetup_flatten_replicate_map {α β : Type*} (n : ℕ) (l : List α) (f : α → β) :
    (List.replicate n (l.map f)).flatten = ((List.replicate n l).flatten).map f := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons, ih,
      List.map_append]

/-- The flag of a slide: `auSetupFlag` is `auSeqFlg` on the cast slide. -/
theorem auSetupFlag_eq (s t k : ℕ) :
    auSetupFlag ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))
      = auSeqFlg (auK s t (k + 1) - auK s t k) := by
  have hmono : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
  have hcast : ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))
      = (((auK s t (k + 1) - auK s t k : ℕ)) : ℤ) := (Nat.cast_sub hmono).symm
  rw [hcast, auSetupFlag, auSeqFlg]
  by_cases hz : auK s t (k + 1) - auK s t k = 0
  · simp [hz]
  · have hz' : (((auK s t (k + 1) - auK s t k : ℕ)) : ℤ) ≠ 0 := by omega
    simp only [hz, hz', if_false]

/-- Size of a flag value. -/
theorem auSetupFlag_vsz (g : ℤ) : vsz (auSetupFlag g) ≤ 3 := by
  rw [auSetupFlag]
  split <;> simp [vsz, Val.enc]

/-- `vsz` of a list value under a pointwise bound. -/
theorem auSetup_vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ l.length * B + l.length + 1 := by
  rw [Work.ConvR.vsz_ofList]
  have h1 : (l.map vsz).sum ≤ (l.map (fun _ => B)).sum := List.sum_le_sum (fun x hx => h x hx)
  rw [Work.ConvR.sum_map_const] at h1
  omega

/-- Length of a flatten of a replicated list. -/
theorem auSetup_length_flatten_replicate (n : ℕ) (u : List (ℤ × ℤ)) :
    ((List.replicate n u).flatten).length = n * u.length := by
  rw [List.length_flatten, List.map_replicate, List.sum_replicate]
  exact nsmul_eq_mul n u.length

/-- `auCop` is at least one. -/
theorem auSetup_auCop_one_le (p α s : ℕ) (hs : 1 ≤ s) : 1 ≤ auCop p α s := by
  have h : s ≤ auOff p α s + 2 * s + 2 * auM p α := by omega
  calc 1 = s / s := (Nat.div_self (by omega : 0 < s)).symm
    _ ≤ (auOff p α s + 2 * s + 2 * auM p α) / s := Nat.div_le_div_right h
    _ = auCop p α s := rfl

/-- `4p+3 < 2^(p+3)`. -/
theorem auSetup_four_mul_add_three_lt (p : ℕ) (hp : 6 ≤ p) : 4 * p + 3 < 2 ^ (p + 3) := by
  have h := four_p_add_five_le_two_pow p hp
  calc 4 * p + 3 < 4 * p + 5 := by omega
    _ ≤ 2 ^ p := h
    _ ≤ 2 ^ (p + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## The list identities of the setup word -/

/-- The extended array of the setup word is the `cfxVal`-image of `auExt`. -/
theorem auSetupE_eq_ext (p α s : ℕ) (u : List (ℤ × ℤ)) :
    auSetupE p α s u = (auExt p α s u).map cfxVal := by
  simp only [auSetupE, auSetupFlat, auExt]
  rw [auSetup_flatten_replicate_map, ← List.map_drop]

/-- The element run is the tail of the extended array. -/
theorem auSetupE_drop (p α s : ℕ) (u : List (ℤ × ℤ)) :
    (auSetupE p α s u).drop (auL p α) = auElems p α s u := by
  rw [auSetupE_eq_ext, ← List.map_drop]
  rfl

/-- The window of round `0` is the head of the extended array. -/
theorem auWinV_zero (p α s t : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hu : u.length = s)
    (ht : 0 < t) : auWinV p α s t u 0 = (auSetupE p α s u).take (auL p α) := by
  have hslice := auWin_slice p α s t hs u hu 0 ht
  rw [auWinV, hslice, auK_zero ht, List.drop_zero, List.map_take, auSetupE_eq_ext]

/-- The table starts with its first record. -/
theorem auRecs_cons (p α s t : ℕ) (ht : 1 ≤ t) :
    auRecs p α s t = auRec p α s t 0 :: (auRecs p α s t).drop 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  simp only [auRecs, List.range_succ_eq_map, List.map_cons, List.drop_one, List.tail_cons,
    List.map_map, Function.comp_apply]

/-- The table is its first record consed onto the rest. -/
theorem auTable_cons (p α s t : ℕ) (ht : 1 ≤ t) :
    auTable p α s t = Val.cons (auRec p α s t 0) (ofList ((auRecs p α s t).drop 1)) := by
  rw [auTable_eq, auRecs_cons p α s t ht]
  rfl

/-- The extended record is the flag consed onto the record. -/
theorem auRecF_eq (p α s t k : ℕ) :
    auRecF p α s t k = Val.cons
      (auSetupFlag ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))) (auRec p α s t k) := by
  simp only [auRecF, auRec, auWts, auSetupFlag_eq]

/-- The record word maps `auRec k` to `auRecF k`. -/
theorem auSetupRecFun_auRec (p α s t k : ℕ) :
    auSetupRecFun (auRec p α s t k) = auRecF p α s t k := by
  rw [auRecF_eq, auRec]
  rfl

/-- The record map sends the table to the extended table. -/
theorem auRecs_map_auSetupRecFun (p α s t : ℕ) :
    (auRecs p α s t).map auSetupRecFun = auRecsF p α s t := by
  rw [auRecsF, auRecs, List.map_map]
  apply List.map_congr_left
  intro k _
  exact auSetupRecFun_auRec p α s t k


/-! ## `Pipe` adapters for the library words -/

/-- A `WordR` in the `∃ rest` fixed-window form is a `Pipe`. -/
theorem Pipe.ofWordR_auSetupRunAux {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨mid, hmid, hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hrest : mid = rest := List.append_cancel_left (by rw [← hmid, hvs])
  exact ⟨out, s', n, by rw [hout, hrest], hev, hn, hstk, hoth⟩

/-- `WordR` with the pre/post fixed at `A`/`B` for every `rest`. -/
theorem Pipe.ofWordRAll {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest)
      (fun _ out => out = B ++ rest) (fun _ => c)) : Pipe main prog A B c := h

/-- `KernelLib.unconsV` as a `Pipe` on a one-value window. -/
private theorem Pipe.unconsV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => ∃ a b rest, vs = .cons a b :: rest)
      (fun vs out => ∃ a b rest, vs = .cons a b :: rest ∧ out = a :: b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [.cons a b] [a, b] K := by
  intro rest vs hvs s R hR
  have hv : vs = .cons a b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs ⟨a, b, rest, hv⟩ s R hR
  have hh : (Val.cons a' b') :: r' = (Val.cons a b) :: rest := hvs'.symm.trans hv
  obtain ⟨h1, h2⟩ := List.cons.inj hh
  obtain ⟨h1a, h1b⟩ := Val.cons.inj h1
  exact ⟨out, s', n, by rw [hout, h1a, h1b, h2]; rfl, hev, hn, hstk, hoth⟩

/-- `KernelLib.consV` as a `Pipe` on a two-value window. -/
theorem Pipe.consV {main prog : Cmd} {K : ℕ}
    (h : ∀ m : Cmd, WordR m prog (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b rest, vs = a :: b :: rest ∧ out = .cons a b :: rest) (fun _ => K))
    (a b : Val) : Pipe main prog [a, b] [.cons a b] K := by
  intro rest vs hvs s R hR
  have hv : vs = a :: b :: rest := by rw [hvs]; rfl
  obtain ⟨out, s', n, ⟨a', b', r', hvs', hout⟩, hev, hn, hstk, hoth⟩ :=
    h main vs (by rw [hv]; simp) s R hR
  obtain ⟨h1, h2, h3⟩ := Work.Fx.cons_inj3 (hvs'.symm.trans hv)
  exact ⟨out, s', n, by rw [hout, h1, h2, h3]; rfl, hev, hn, hstk, hoth⟩

/-! ## Cost helpers for the budget -/

theorem auSetupBd_def (p α s t : ℕ) :
    auSetupBd p α s t = (s + t * auL p α + auCop p α s * s + 1) * (p + 1) := rfl

/-- The elementary components of the budget. -/
theorem auSetupBd_ge (p α s t : ℕ) (hs : 1 ≤ s) :
    s * (p + 1) ≤ auSetupBd p α s t ∧ auCop p α s * s * (p + 1) ≤ auSetupBd p α s t ∧
      t * auL p α * (p + 1) ≤ auSetupBd p α s t ∧ (p + 1) ≤ auSetupBd p α s t ∧
      1 ≤ auSetupBd p α s t := by
  have h2 : s ≤ s + (t * auL p α + auCop p α s * s) + 1 := by omega
  have h3 : auCop p α s * s ≤ s + (t * auL p α + auCop p α s * s) + 1 := by omega
  have h4 : t * auL p α ≤ s + (t * auL p α + auCop p α s * s) + 1 := by omega
  have h5 : 1 ≤ s + (t * auL p α + auCop p α s * s) + 1 := by omega
  have hB : auSetupBd p α s t = (s + (t * auL p α + auCop p α s * s) + 1) * (p + 1) := by
    rw [auSetupBd]; ring
  rw [hB]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul_right _ h2
  · exact Nat.mul_le_mul_right _ h3
  · exact Nat.mul_le_mul_right _ h4
  · simpa using Nat.mul_le_mul_right (p + 1) h5
  · exact le_trans (by omega : 1 ≤ 1 * (p + 1)) (Nat.mul_le_mul_right (p + 1) h5)

/-! ## Size bounds -/

theorem auSetupInp_vsz (p α s : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hp : 100 ≤ p)
    (hu : u.length = s) (hdisc : ∀ z ∈ u, inDisc p z) :
    vsz (ofList (auSetupInp u)) ≤ 4 * s * (p + 1) := by
  have h1 : ∀ z ∈ u, vsz (cfxVal z) ≤ Work.ConvR.cfxSz p :=
    fun z hz => Work.ConvR.vsz_cfxVal_le (hdisc z hz)
  have h2 := vsz_ofList_map_le u cfxVal (Work.ConvR.cfxSz p) h1
  simp only [auSetupInp] at *
  rw [hu, Work.ConvR.cfxSz] at h2
  nlinarith

theorem auSetupFlat_vsz (p α s : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hp : 100 ≤ p)
    (hu : u.length = s) (hdisc : ∀ z ∈ u, inDisc p z) :
    vsz (ofList (auSetupFlat p α s u)) ≤ 4 * (auCop p α s * s) * (p + 1) := by
  have h1 : ∀ z ∈ (List.replicate (auCop p α s) u).flatten, vsz (cfxVal z) ≤ Work.ConvR.cfxSz p := by
    intro z hz
    rw [List.mem_flatten] at hz
    obtain ⟨l, hl, hzl⟩ := hz
    rw [List.mem_replicate] at hl
    exact Work.ConvR.vsz_cfxVal_le (hdisc z (hl.2 ▸ hzl))
  have hlen : ((List.replicate (auCop p α s) u).flatten).length = auCop p α s * s := by
    rw [auSetup_length_flatten_replicate, hu]
  have h2 := vsz_ofList_map_le ((List.replicate (auCop p α s) u).flatten) cfxVal
    (Work.ConvR.cfxSz p) h1
  rw [hlen, Work.ConvR.cfxSz] at h2
  have hc1 := auSetup_auCop_one_le p α s (by omega)
  rw [auSetupFlat, auSetup_flatten_replicate_map]
  nlinarith

theorem auSetupE_vsz (p α s : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hp : 100 ≤ p)
    (hu : u.length = s) (hdisc : ∀ z ∈ u, inDisc p z) :
    vsz (ofList (auSetupE p α s u)) ≤ 4 * (auCop p α s * s) * (p + 1) :=
  le_trans (vsz_drop_le (auSetupFlat p α s u) (auOff p α s))
    (auSetupFlat_vsz p α s u hs hp hu hdisc)

theorem auSetupW_vsz (p α s : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hp : 100 ≤ p)
    (hu : u.length = s) (hdisc : ∀ z ∈ u, inDisc p z) :
    vsz (ofList ((auSetupE p α s u).take (auL p α))) ≤ 4 * (auCop p α s * s) * (p + 1) :=
  le_trans (vsz_take_le (auSetupE p α s u) (auL p α)) (auSetupE_vsz p α s u hs hp hu hdisc)

theorem auOff_isz_le (p α s : ℕ) : HvdH.isz ((auOff p α s : ℕ) : ℤ) ≤ s + 2 := by
  have h1 : auOff p α s ≤ s - 1 := auOffCop_aux_off_le p α s
  have h2 : (auOff p α s).size ≤ s := by
    calc (auOff p α s).size ≤ auOff p α s := Nat.size_le.mpr Nat.lt_two_pow_self
      _ ≤ s := by omega
  rw [isz_natCast]
  omega

theorem auCop_le_lin (p α s : ℕ) (hs : 1 ≤ s) (hαp : α ^ 2 < p) :
    auCop p α s ≤ 4 * p + 3 := by
  have hM : auM p α ≤ 2 * p := auOffCop_aux_auM_le p α hαp
  have hoff : auOff p α s ≤ s - 1 := auOffCop_aux_off_le p α s
  rw [auCop]
  apply Nat.div_le_of_le_mul
  have h1 : auOff p α s + 2 * s + 2 * auM p α ≤ 3 * s + 4 * p := by omega
  have h2 : 3 * s + 4 * p ≤ s * (4 * p + 3) := by nlinarith
  omega

theorem auCop_isz_le (p α s : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) :
    HvdH.isz ((auCop p α s : ℕ) : ℤ) ≤ 2 * (p + 1) := by
  have hcop : auCop p α s ≤ 4 * p + 3 := auCop_le_lin p α s (by omega) hαp
  have hlt : auCop p α s < 2 ^ (p + 3) :=
    lt_of_le_of_lt hcop (auSetup_four_mul_add_three_lt p (by omega))
  have hsize : (auCop p α s).size ≤ p + 3 := Nat.size_le.mpr hlt
  rw [isz_natCast]
  omega

theorem auL_isz_le (p α : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) :
    HvdH.isz ((auL p α : ℕ) : ℤ) ≤ 2 * (p + 1) := by
  have hL : auL p α ≤ 4 * p + 1 := (auMLe p α hα hαp).2
  have hlt : auL p α < 2 ^ (p + 3) :=
    lt_of_le_of_lt hL (lt_of_lt_of_le (by omega : 4 * p + 1 < 4 * p + 3)
      (le_of_lt (auSetup_four_mul_add_three_lt p (by omega))))
  have hsize : (auL p α).size ≤ p + 3 := Nat.size_le.mpr hlt
  rw [isz_natCast]
  omega

theorem aup_isz_le (p : ℕ) : HvdH.isz ((p : ℕ) : ℤ) ≤ 2 * (p + 1) := by
  have hsize : p.size ≤ p := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [isz_natCast]
  omega

theorem auSetup_auWts_vsz_le (p α s t k : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (ht : 1 ≤ t) (hk : k < t) :
    vsz (ofList (auWts p α s t k)) ≤ 16 * auL p α * (p + 1) := by
  have h1 : ∀ i ∈ List.range (auL p α), vsz (Val.int (auWt p α t (auNsq p α s t k i))) ≤ auSZ p := by
    intro i _
    rw [Work.ConvR.vsz_int]
    exact auWtSize p α t (auNsq p α s t k i) (auNsq_nonneg p α s t k i) hα ht hp
  have h2 := vsz_ofList_map_le (List.range (auL p α))
    (fun i => Val.int (auWt p α t (auNsq p α s t k i))) (auSZ p) h1
  simp only [auWts, List.length_range, auSZ] at h2 ⊢
  have hL := auL_pos p α
  nlinarith

theorem auRec_vsz_le (p α s t k : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hst : s < t) (hk : k < t)
    (hW : vsz (ofList (auWts p α s t k)) ≤ 16 * auL p α * (p + 1)) :
    vsz (auRec p α s t k) ≤ auSetupLrec p α := by
  have ht : 0 < t := by omega
  have hg : HvdH.isz ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ)) ≤ 3 := isz_auK_diff hst ht
  simp only [auRec, auWts, auSetupLrec] at hW ⊢
  rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
  nlinarith [auL_pos p α]

theorem auRecF_vsz_le (p α s t k : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hst : s < t) (hk : k < t)
    (hW : vsz (ofList (auWts p α s t k)) ≤ 16 * auL p α * (p + 1)) :
    vsz (auRecF p α s t k) ≤ auSetupLrec p α := by
  have ht : 0 < t := by omega
  have hg : HvdH.isz ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ)) ≤ 3 := isz_auK_diff hst ht
  have hR : vsz (auRec p α s t k)
      = HvdH.isz ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))
        + vsz (ofList (auWts p α s t k)) + 1 := by
    simp only [auRec, auWts, Work.ConvR.vsz_cons, Work.ConvR.vsz_int]
  rw [auRecF_eq, Work.ConvR.vsz_cons, hR]
  have h2 := auSetupFlag_vsz ((auK s t (k + 1) : ℤ) - (auK s t k : ℤ))
  have hL := auL_pos p α
  simp only [auSetupLrec]
  nlinarith

theorem auRecs_vsz_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hst : s < t)
    (hrec : ∀ k < t, vsz (auRec p α s t k) ≤ auSetupLrec p α) :
    vsz (ofList (auRecs p α s t)) ≤ 30 * t * auL p α * (p + 1) := by
  have h1 : ∀ x ∈ auRecs p α s t, vsz x ≤ auSetupLrec p α := by
    intro x hx
    simp only [auRecs, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hrec k hk
  have h2 := auSetup_vsz_ofList_le h1
  simp only [auRecs, List.length_map, List.length_range, auSetupLrec] at h2 ⊢
  have hL := auL_pos p α
  have ht : 1 ≤ t := by omega
  have h3 : t + 1 ≤ 2 * (t * (auL p α * (p + 1))) := by
    have hp1 : 1 ≤ auL p α * (p + 1) := by nlinarith
    nlinarith
  nlinarith

theorem auRecsF_vsz_le (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hst : s < t)
    (hrecF : ∀ k < t, vsz (auRecF p α s t k) ≤ auSetupLrec p α) :
    vsz (ofList (auRecsF p α s t)) ≤ 30 * t * auL p α * (p + 1) := by
  have h1 : ∀ x ∈ auRecsF p α s t, vsz x ≤ auSetupLrec p α := by
    intro x hx
    simp only [auRecsF, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hrecF k hk
  have h2 := auSetup_vsz_ofList_le h1
  simp only [auRecsF, List.length_map, List.length_range, auSetupLrec] at h2 ⊢
  have hL := auL_pos p α
  have ht : 1 ≤ t := by omega
  have h3 : t + 1 ≤ 2 * (t * (auL p α * (p + 1))) := by
    have hp1 : 1 ≤ auL p α * (p + 1) := by nlinarith
    nlinarith
  nlinarith

theorem auRecs_drop_vsz_le (p α s t : ℕ)
    (h : vsz (ofList (auRecs p α s t)) ≤ 30 * t * auL p α * (p + 1)) :
    vsz (ofList ((auRecs p α s t).drop 1)) ≤ 30 * t * auL p α * (p + 1) :=
  le_trans (vsz_drop_le (auRecs p α s t) 1) h


/-! ## More helpers -/

/-- Size of a replicated list value. -/
theorem vsz_ofList_replicate (n : ℕ) (v : Val) :
    vsz (ofList (List.replicate n v)) = n * (vsz v + 1) + 1 := by
  induction n with
  | zero => simp [ofList, vsz, Val.enc]
  | succ k ih =>
    have h : ofList (List.replicate (k + 1) v) = Val.cons v (ofList (List.replicate k v)) := by
      rw [List.replicate_succ]; rfl
    rw [h, Work.ConvR.vsz_cons, ih]; ring

/-- `szl` of a list under a pointwise bound. -/
theorem auSetup_szl_le {A : List Val} {M : ℕ} (h : ∀ v ∈ A, vsz v ≤ M) :
    Work.Fx.szl A ≤ A.length * M := by
  simp only [Work.Fx.szl]
  have h1 : (A.map vsz).sum ≤ (A.map (fun _ => M)).sum := List.sum_le_sum h
  rw [Work.ConvR.sum_map_const] at h1
  exact h1

/-- `Pipe` with the pre window rewritten. -/
theorem Pipe.rwA {main prog : Cmd} {A A' B : List Val} {c : ℕ} (h : Pipe main prog A B c)
    (hA : A = A') : Pipe main prog A' B c := hA ▸ h

/-! ## The size bundle for the setup word -/

theorem auSetup_szBd (p α s t : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hαp : α ^ 2 < p) (hst : s < t) (hu : u.length = s) (hdisc : ∀ z ∈ u, inDisc p z) :
    vsz (ofList (auSetupInp u)) ≤ 30 * auSetupBd p α s t ∧
    HvdH.isz ((auOff p α s : ℕ) : ℤ) ≤ 30 * auSetupBd p α s t ∧
    HvdH.isz ((auCop p α s : ℕ) : ℤ) ≤ 30 * auSetupBd p α s t ∧
    HvdH.isz ((p : ℕ) : ℤ) ≤ 30 * auSetupBd p α s t ∧
    HvdH.isz ((auL p α : ℕ) : ℤ) ≤ 30 * auSetupBd p α s t ∧
    vsz (auTable p α s t) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList (auSetupE p α s u)) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList ((auSetupE p α s u).take (auL p α))) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList (List.replicate (auCop p α s) (ofList (auSetupInp u)))) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList (auSetupFlat p α s u)) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList (auWts p α s t 0)) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList ((auRecs p α s t).drop 1)) ≤ 30 * auSetupBd p α s t ∧
    vsz (ofList (auRecsF p α s t)) ≤ 30 * auSetupBd p α s t := by
  have ht : 1 ≤ t := by omega
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  have hI : vsz (ofList (auSetupInp u)) ≤ 4 * s * (p + 1) := auSetupInp_vsz p α s u hs hp hu hdisc
  have hO : HvdH.isz ((auOff p α s : ℕ) : ℤ) ≤ s + 2 := auOff_isz_le p α s
  have hC : HvdH.isz ((auCop p α s : ℕ) : ℤ) ≤ 2 * (p + 1) := auCop_isz_le p α s hs hα hp hαp
  have hP : HvdH.isz ((p : ℕ) : ℤ) ≤ 2 * (p + 1) := aup_isz_le p
  have hL : HvdH.isz ((auL p α : ℕ) : ℤ) ≤ 2 * (p + 1) := auL_isz_le p α hα hp hαp
  have hE : vsz (ofList (auSetupE p α s u)) ≤ 4 * (auCop p α s * s) * (p + 1) :=
    auSetupE_vsz p α s u hs hp hu hdisc
  have hWv : vsz (ofList ((auSetupE p α s u).take (auL p α))) ≤ 4 * (auCop p α s * s) * (p + 1) :=
    auSetupW_vsz p α s u hs hp hu hdisc
  have hFx : vsz (ofList (auSetupFlat p α s u)) ≤ 4 * (auCop p α s * s) * (p + 1) :=
    auSetupFlat_vsz p α s u hs hp hu hdisc
  have hWts : vsz (ofList (auWts p α s t 0)) ≤ 16 * auL p α * (p + 1) :=
    auSetup_auWts_vsz_le p α s t 0 hα hp ht (by omega)
  have hRec : ∀ k, k < t → vsz (auRec p α s t k) ≤ auSetupLrec p α := fun k hk =>
    auRec_vsz_le p α s t k hα hp hst hk (auSetup_auWts_vsz_le p α s t k hα hp ht hk)
  have hRecF : ∀ k, k < t → vsz (auRecF p α s t k) ≤ auSetupLrec p α := fun k hk =>
    auRecF_vsz_le p α s t k hα hp hst hk (auSetup_auWts_vsz_le p α s t k hα hp ht hk)
  have hRecs : vsz (ofList (auRecs p α s t)) ≤ 30 * t * auL p α * (p + 1) :=
    auRecs_vsz_le p α s t hα hp hst hRec
  have hRecsF : vsz (ofList (auRecsF p α s t)) ≤ 30 * t * auL p α * (p + 1) :=
    auRecsF_vsz_le p α s t hα hp hst hRecF
  have hRecsD : vsz (ofList ((auRecs p α s t).drop 1)) ≤ 30 * t * auL p α * (p + 1) :=
    auRecs_drop_vsz_le p α s t hRecs
  have hcs : 1 ≤ auCop p α s := auSetup_auCop_one_le p α s (by omega)
  have hRep : vsz (ofList (List.replicate (auCop p α s) (ofList (auSetupInp u))))
      ≤ 30 * auSetupBd p α s t := by
    rw [vsz_ofList_replicate]
    have h1 : vsz (ofList (auSetupInp u)) + 1 ≤ 5 * (s * (p + 1)) := by nlinarith
    have h2 : auCop p α s * (vsz (ofList (auSetupInp u)) + 1)
        ≤ 5 * (auCop p α s * s * (p + 1)) :=
      calc auCop p α s * (vsz (ofList (auSetupInp u)) + 1)
          ≤ auCop p α s * (5 * (s * (p + 1))) := Nat.mul_le_mul_left _ h1
        _ = 5 * (auCop p α s * s * (p + 1)) := by ring
    nlinarith
  have hTab : vsz (auTable p α s t) ≤ 30 * auSetupBd p α s t := by
    rw [auTable_eq]; nlinarith
  have hLp1 : 1 ≤ auL p α * (p + 1) := by nlinarith [auL_pos p α]
  have hLb : auL p α * (p + 1) ≤ auSetupBd p α s t := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, hTab, ?_, ?_, hRep, ?_, ?_, ?_, ?_⟩
  · have h1 : 4 * s * (p + 1) ≤ 30 * auSetupBd p α s t := by nlinarith
    nlinarith
  · have h1 : s + 2 ≤ 30 * (s * (p + 1)) := by nlinarith
    nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have h1 : 16 * (auL p α * (p + 1)) ≤ 30 * auSetupBd p α s t := by nlinarith
    nlinarith
  · nlinarith
  · nlinarith

/-! ## Cost helpers for the setup word -/

/-- A step of the form `K * (c + 1)` with `c` linear in the budget. -/
theorem auSetup_step_le {K Ksum c Bd : ℕ} (hK : K ≤ Ksum) (hKsum : 1 ≤ Ksum)
    (hc : c ≤ 3000 * Bd) (hB1 : 1 ≤ Bd) : K * (c + 1) ≤ 200000 * Ksum * Bd := by
  have h1 : c + 1 ≤ 3001 * Bd := by nlinarith
  calc K * (c + 1) ≤ Ksum * (3001 * Bd) := Nat.mul_le_mul hK h1
    _ = (3001 * Ksum) * Bd := by ring
    _ ≤ (200000 * Ksum) * Bd := Nat.mul_le_mul_right Bd (Nat.mul_le_mul_right Ksum (by omega))
    _ = 200000 * Ksum * Bd := by ring

/-- A constant step. -/
theorem auSetup_step_const {K Ksum Bd : ℕ} (hK : K ≤ Ksum) (hKs : 1 ≤ Ksum) (hB1 : 1 ≤ Bd) :
    K ≤ 200000 * Ksum * Bd := by nlinarith

/-- A step of the form `K * k * (c + 1)`. -/
theorem auSetup_mulk_le {K Ksum c Bd k : ℕ} (hK : K ≤ Ksum) (hk : k ≤ 8) (hc : c ≤ 1000 * Bd)
    (hB1 : 1 ≤ Bd) : K * k * (c + 1) ≤ 200000 * Ksum * Bd := by
  have h1 : c + 1 ≤ 1001 * Bd := by nlinarith
  have h2 : K * k ≤ Ksum * 8 := Nat.mul_le_mul hK hk
  calc K * k * (c + 1) ≤ (Ksum * 8) * (1001 * Bd) := Nat.mul_le_mul h2 h1
    _ = 8008 * (Ksum * Bd) := by ring
    _ ≤ 200000 * (Ksum * Bd) := Nat.mul_le_mul_right _ (by omega)
    _ = 200000 * Ksum * Bd := by ring

/-- Five budget units. -/
theorem auSetup_five (B : ℕ) : B + (B + (B + (B + B))) = 5 * B := by ring

/-- Four budget units. -/
theorem auSetup_four (B : ℕ) : B + (B + (B + B)) = 4 * B := by ring

/-- Three budget units. -/
theorem auSetup_three (B : ℕ) : B + (B + B) = 3 * B := by ring

/-- Two budget units. -/
theorem auSetup_two (B : ℕ) : B + B = 2 * B := by ring

/-- `vsz`-bound of an integer value from an `isz`-bound. -/
theorem auSetup_vsz_int_le {z : ℤ} {B : ℕ} (h : HvdH.isz z ≤ B) : vsz (Val.int z) ≤ B := by
  rw [Work.ConvR.vsz_int]; exact h

/-! ## Chain 1: the extended array -/

theorem auSetupArrPipe (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ)),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      Pipe main prog (ofList (auSetupInp u) :: auPvals p α s t)
        (ofList (auSetupE p α s u) :: auPvals p α s t) (K * auSetupBd p α s t) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨replP, Krl, hrepl⟩ := hl.replicate
  obtain ⟨flatP, Kf, hflat⟩ := hl.flatten
  obtain ⟨dropLP, Kdl, hdropL⟩ := hl.drop
  refine ⟨Cmd.seq (pickP 2) (Cmd.seq replP (Cmd.seq flatP (Cmd.seq (pickP 1) dropLP))),
    2000000 * (Kp + Krl + Kf + Kdl + 1), ?_⟩
  intro main p α s t u hu hdisc hs hα hp hαp hst
  set Bd := auSetupBd p α s t with hBd
  obtain ⟨hI, hO, hC, hPv, hLz, hT, hE, hWv, hRep, hFx, hWts, hRecsD, hRecsF⟩ :=
    auSetup_szBd p α s t u hs hα hp hαp hst hu hdisc
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  have hKs : 1 ≤ Kp + Krl + Kf + Kdl + 1 := by omega
  have hKp : Kp ≤ Kp + Krl + Kf + Kdl + 1 := by omega
  have hKrl : Krl ≤ Kp + Krl + Kf + Kdl + 1 := by omega
  have hKf : Kf ≤ Kp + Krl + Kf + Kdl + 1 := by omega
  have hKdl : Kdl ≤ Kp + Krl + Kf + Kdl + 1 := by omega
  have hcs : 1 ≤ auCop p α s := auSetup_auCop_one_le p α s (by omega)
  have hIsh : vsz (ofList (auSetupInp u)) ≤ 4 * s * (p + 1) :=
    auSetupInp_vsz p α s u hs hp hu hdisc
  have hCsh : auCop p α s ≤ 6 * (p + 1) := by
    have h := auCop_le_lin p α s (by omega) hαp
    nlinarith
  have hCisz : HvdH.isz ((auCop p α s : ℕ) : ℤ) ≤ 2 * (p + 1) :=
    auCop_isz_le p α s hs hα hp hαp
  have hOsh : HvdH.isz ((auOff p α s : ℕ) : ℤ) ≤ s + 2 := auOff_isz_le p α s
  set T : List Val := [Val.int (auOff p α s : ℤ), Val.int (auCop p α s : ℤ),
    Val.int (p : ℤ), auTable p α s t] with hTdef
  have hTsz : ∀ v ∈ T, vsz v ≤ 30 * Bd := by
    intro v hv
    simp only [hTdef, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    exacts [auSetup_vsz_int_le hO, auSetup_vsz_int_le hC, auSetup_vsz_int_le hPv, hT]
  have hW0sz : ∀ v ∈ ofList (auSetupInp u) :: T, vsz v ≤ 30 * Bd := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hI
    · exact hTsz v hv
  -- step 1: pick the copy count
  have hstep1 : Pipe main (pickP 2) (ofList (auSetupInp u) :: T)
      (Val.int (auCop p α s : ℤ) :: ofList (auSetupInp u) :: T) (200000 * (Kp + Krl + Kf + Kdl + 1) * Bd) := by
    have h0 := Pipe.pick main hpick (A := ofList (auSetupInp u) :: T) (k := 2) (by simp [hTdef])
    rw [show (ofList (auSetupInp u) :: T).getD 2 Val.nil = Val.int (auCop p α s : ℤ) from by
      simp [hTdef]] at h0
    refine Pipe.le h0 (auSetup_mulk_le hKp (by omega) ?_ hB1)
    have hszl := auSetup_szl_le hW0sz
    have hlen : (ofList (auSetupInp u) :: T).length = 5 := by simp [hTdef]
    rw [hlen] at hszl
    refine le_trans (szl_take_le _ 3) ?_
    nlinarith
  -- step 2: replicate
  have hstep2 : Pipe main replP (Val.int (auCop p α s : ℤ) :: ofList (auSetupInp u) :: T)
      (ofList (List.replicate (auCop p α s) (ofList (auSetupInp u))) :: T)
      (200000 * (Kp + Krl + Kf + Kdl + 1) * Bd) := by
    have h0 : Pipe main replP [Val.int (auCop p α s : ℤ), ofList (auSetupInp u)]
        [ofList (List.replicate (auCop p α s) (ofList (auSetupInp u)))]
        (Krl * ((auCop p α s + 1) * (vsz (ofList (auSetupInp u)) + 1)
          + HvdH.isz (auCop p α s : ℤ) + 1)) :=
      Pipe.ofWordR_auSetupRunAux (hrepl main (auCop p α s) (ofList (auSetupInp u)))
    have h1 := Pipe.appendTail T h0
    refine Pipe.le h1 (auSetup_step_le hKrl hKs ?_ hB1)
    have ha : (auCop p α s + 1) * (vsz (ofList (auSetupInp u)) + 1) ≤ 10 * Bd := by
      have hx : vsz (ofList (auSetupInp u)) + 1 ≤ 5 * (s * (p + 1)) := by nlinarith
      have hy : (auCop p α s + 1) * (5 * (s * (p + 1)))
          ≤ 10 * (auCop p α s * s * (p + 1)) := by
        rw [add_mul, one_mul]
        have hz : 5 * (s * (p + 1)) ≤ 5 * (auCop p α s * s * (p + 1)) :=
          Nat.mul_le_mul_left _ (by nlinarith)
        nlinarith
      have hw : (auCop p α s + 1) * (vsz (ofList (auSetupInp u)) + 1)
          ≤ (auCop p α s + 1) * (5 * (s * (p + 1))) := Nat.mul_le_mul_left _ hx
      nlinarith
    have hb : HvdH.isz (auCop p α s : ℤ) ≤ 2 * Bd := by nlinarith
    nlinarith
  -- step 3: flatten
  have hstep3 : Pipe main flatP (ofList (List.replicate (auCop p α s) (ofList (auSetupInp u))) :: T)
      (ofList (auSetupFlat p α s u) :: T)
      (200000 * (Kp + Krl + Kf + Kdl + 1) * Bd) := by
    have h0 : Pipe main flatP
        [ofList ((List.replicate (auCop p α s) (u.map cfxVal)).map ofList)]
        [ofList ((List.replicate (auCop p α s) (u.map cfxVal)).flatten)]
        (Kf * (vsz (ofList ((List.replicate (auCop p α s) (u.map cfxVal)).map ofList)) + 1)) :=
      Pipe.ofWordR_auSetupRunAux (hflat main (List.replicate (auCop p α s) (u.map cfxVal)))
    have hA : [ofList ((List.replicate (auCop p α s) (u.map cfxVal)).map ofList)]
        = [ofList (List.replicate (auCop p α s) (ofList (auSetupInp u)))] := by
      simp only [List.map_replicate, auSetupInp]
    have h1 := Pipe.appendTail T (Pipe.rwA h0 hA)
    refine Pipe.le h1 (auSetup_step_le hKf hKs ?_ hB1)
    have hsz : vsz (ofList ((List.replicate (auCop p α s) (u.map cfxVal)).map ofList)) ≤ 30 * Bd := by
      rw [List.map_replicate]
      simpa only [auSetupInp] using hRep
    nlinarith
  -- step 4: pick the offset
  have hstep4 : Pipe main (pickP 1) (ofList (auSetupFlat p α s u) :: T)
      (Val.int (auOff p α s : ℤ) :: ofList (auSetupFlat p α s u) :: T)
      (200000 * (Kp + Krl + Kf + Kdl + 1) * Bd) := by
    have h0 := Pipe.pick main hpick (A := ofList (auSetupFlat p α s u) :: T) (k := 1) (by simp [hTdef])
    rw [show (ofList (auSetupFlat p α s u) :: T).getD 1 Val.nil = Val.int (auOff p α s : ℤ) from by
      simp [hTdef]] at h0
    refine Pipe.le h0 (auSetup_mulk_le hKp (by omega) ?_ hB1)
    have hW : ∀ v ∈ ofList (auSetupFlat p α s u) :: T, vsz v ≤ 30 * Bd := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hFx
      · exact hTsz v hv
    have hszl := auSetup_szl_le hW
    have hlen : (ofList (auSetupFlat p α s u) :: T).length = 5 := by simp [hTdef]
    rw [hlen] at hszl
    refine le_trans (szl_take_le _ 2) ?_
    nlinarith
  -- step 5: drop the offset
  have hstep5 : Pipe main dropLP (Val.int (auOff p α s : ℤ) :: ofList (auSetupFlat p α s u) :: T)
      (ofList (auSetupE p α s u) :: T) (200000 * (Kp + Krl + Kf + Kdl + 1) * Bd) := by
    have h0 : Pipe main dropLP [Val.int (auOff p α s : ℤ), ofList (auSetupFlat p α s u)]
        [ofList ((auSetupFlat p α s u).drop (auOff p α s))]
        (Kdl * (vsz (ofList (auSetupFlat p α s u)) + HvdH.isz (auOff p α s : ℤ) + 1)) :=
      Pipe.ofWordR_auSetupRunAux (hdropL main (auOff p α s) (auSetupFlat p α s u))
    have h1 := Pipe.appendTail T h0
    refine Pipe.le h1 (auSetup_step_le hKdl hKs ?_ hB1)
    have hx : vsz (ofList (auSetupFlat p α s u)) ≤ 30 * Bd := hFx
    have hy : HvdH.isz (auOff p α s : ℤ) ≤ 30 * Bd := hO
    nlinarith
  have hchain := Pipe.comp hstep1 (Pipe.comp hstep2 (Pipe.comp hstep3 (Pipe.comp hstep4 hstep5)))
  have hEq : (ofList (auSetupInp u) :: T) = (ofList (auSetupInp u) :: auPvals p α s t) := by
    simp [hTdef, auPvals]
  have hEq2 : (ofList (auSetupE p α s u) :: T) = (ofList (auSetupE p α s u) :: auPvals p α s t) := by
    simp [hTdef, auPvals]
  rw [hEq, hEq2] at hchain
  refine Pipe.le hchain ?_
  rw [auSetup_five]
  nlinarith

/-! ## Chain 2: reading the window length off the table -/

theorem auSetupLPipe (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ)),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      Pipe main prog (ofList (auSetupE p α s u) :: auPvals p α s t)
        (Val.int (auL p α : ℤ) :: ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
          :: ofList (auSetupE p α s u) :: auPvals p α s t) (K * auSetupBd p α s t) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨ucP, Ku, huc⟩ := hk.unconsV
  obtain ⟨drP, Kdr, hdr⟩ := hk.drop
  obtain ⟨lenP, Kln, hlen⟩ := hl.length
  refine ⟨Cmd.seq (pickP 4) (Cmd.seq ucP (Cmd.seq ucP (Cmd.seq drP lenP))),
    2000000 * (Kp + Ku + Kdr + Kln + 1), ?_⟩
  intro main p α s t u hu hdisc hs hα hp hαp hst
  set Bd := auSetupBd p α s t with hBd
  obtain ⟨hI, hO, hC, hPv, hLz, hT, hE, hWv, hRep, hFx, hWts, hRecsD, hRecsF⟩ :=
    auSetup_szBd p α s t u hs hα hp hαp hst hu hdisc
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  have htw : 1 ≤ t := by omega
  have hKs : 1 ≤ Kp + Ku + Kdr + Kln + 1 := by omega
  have hKp : Kp ≤ Kp + Ku + Kdr + Kln + 1 := by omega
  have hKu : Ku ≤ Kp + Ku + Kdr + Kln + 1 := by omega
  have hKdr : Kdr ≤ Kp + Ku + Kdr + Kln + 1 := by omega
  have hKln : Kln ≤ Kp + Ku + Kdr + Kln + 1 := by omega
  set TL : List Val := [Val.int (auOff p α s : ℤ), Val.int (auCop p α s : ℤ), Val.int (p : ℤ),
    auTable p α s t] with hTL
  have hTsz : ∀ v ∈ TL, vsz v ≤ 30 * Bd := by
    intro v hv
    simp only [hTL, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    exacts [auSetup_vsz_int_le hO, auSetup_vsz_int_le hC, auSetup_vsz_int_le hPv, hT]
  -- step 1: pick the table
  have hstep1 : Pipe main (pickP 4) (ofList (auSetupE p α s u) :: TL)
      (auTable p α s t :: ofList (auSetupE p α s u) :: TL) (200000 * (Kp + Ku + Kdr + Kln + 1) * Bd) := by
    have h0 := Pipe.pick main hpick (A := ofList (auSetupE p α s u) :: TL) (k := 4) (by simp [hTL])
    rw [show (ofList (auSetupE p α s u) :: TL).getD 4 Val.nil = auTable p α s t from by
      simp [hTL]] at h0
    refine Pipe.le h0 (auSetup_mulk_le hKp (by omega) ?_ hB1)
    have hW : ∀ v ∈ ofList (auSetupE p α s u) :: TL, vsz v ≤ 30 * Bd := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hE
      · exact hTsz v hv
    have hszl := auSetup_szl_le hW
    have hlen : (ofList (auSetupE p α s u) :: TL).length = 5 := by simp [hTL]
    rw [hlen] at hszl
    refine le_trans (szl_take_le _ 5) ?_
    nlinarith
  -- step 2: split the table into its first record
  have hstep2 : Pipe main ucP (auTable p α s t :: ofList (auSetupE p α s u) :: TL)
      (auRec p α s t 0 :: ofList ((auRecs p α s t).drop 1) :: ofList (auSetupE p α s u) :: TL)
      (200000 * (Kp + Ku + Kdr + Kln + 1) * Bd) := by
    have h0 := Pipe.unconsV (main := main) huc (auRec p α s t 0) (ofList ((auRecs p α s t).drop 1))
    have hA : ([(Val.cons (auRec p α s t 0) (ofList ((auRecs p α s t).drop 1)))] : List Val)
        = [auTable p α s t] := by
      rw [auTable_cons p α s t htw]
    have h1 := Pipe.appendTail (ofList (auSetupE p α s u) :: TL) (Pipe.rwA h0 hA)
    exact Pipe.le h1 (auSetup_step_const hKu hKs hB1)
  -- step 3: split the record into slide and weights
  have hstep3 : Pipe main ucP (auRec p α s t 0 :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: TL)
      (Val.int ((auK s t (0 + 1) : ℤ) - (auK s t 0 : ℤ)) :: ofList (auWts p α s t 0)
        :: ofList ((auRecs p α s t).drop 1) :: ofList (auSetupE p α s u) :: TL)
      (200000 * (Kp + Ku + Kdr + Kln + 1) * Bd) := by
    have h0 := Pipe.unconsV (main := main) huc (Val.int ((auK s t (0 + 1) : ℤ) - (auK s t 0 : ℤ)))
      (ofList (auWts p α s t 0))
    have h1 := Pipe.appendTail (ofList ((auRecs p α s t).drop 1) :: ofList (auSetupE p α s u) :: TL) h0
    exact Pipe.le h1 (auSetup_step_const hKu hKs hB1)
  -- step 4: drop the slide
  have hstep4 : Pipe main drP (Val.int ((auK s t (0 + 1) : ℤ) - (auK s t 0 : ℤ))
        :: ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: TL)
      (ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: TL) (200000 * (Kp + Ku + Kdr + Kln + 1) * Bd) := by
    have h0 := Pipe.drop main hdr (Val.int ((auK s t (0 + 1) : ℤ) - (auK s t 0 : ℤ)))
    have h1 := Pipe.appendTail (ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
      :: ofList (auSetupE p α s u) :: TL) h0
    refine Pipe.le h1 (auSetup_step_le hKdr hKs ?_ hB1)
    have hg : vsz (Val.int ((auK s t (0 + 1) : ℤ) - (auK s t 0 : ℤ))) ≤ 3 :=
      auSetup_vsz_int_le (isz_auK_diff hst (by omega))
    nlinarith
  -- step 5: read the length
  have hstep5 : Pipe main lenP (ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
        :: ofList (auSetupE p α s u) :: TL)
      (Val.int (auL p α : ℤ) :: ofList (auWts p α s t 0)
        :: ofList ((auRecs p α s t).drop 1) :: ofList (auSetupE p α s u) :: TL)
      (200000 * (Kp + Ku + Kdr + Kln + 1) * Bd) := by
    have h0 : Pipe main lenP [ofList (auWts p α s t 0)]
        [Val.int ((auWts p α s t 0).length : ℤ), ofList (auWts p α s t 0)]
        (Kln * (vsz (ofList (auWts p α s t 0)) + 1)) :=
      Pipe.ofWordR_auSetupRunAux (hlen main (auWts p α s t 0))
    rw [auWts_length p α s t 0] at h0
    have h1 := Pipe.appendTail (ofList ((auRecs p α s t).drop 1)
      :: ofList (auSetupE p α s u) :: TL) h0
    refine Pipe.le h1 (auSetup_step_le hKln hKs ?_ hB1)
    nlinarith
  have hchain := Pipe.comp hstep1 (Pipe.comp hstep2 (Pipe.comp hstep3 (Pipe.comp hstep4 hstep5)))
  have hEq : (ofList (auSetupE p α s u) :: TL) = (ofList (auSetupE p α s u) :: auPvals p α s t) := by
    simp [hTL, auPvals]
  rw [hEq] at hchain
  refine Pipe.le hchain ?_
  rw [auSetup_five]
  nlinarith

/-! ## Chain 3: dropping the two auxiliary lists -/

theorem auSetupDropPipe (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ)),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      Pipe main prog (ofList (auWts p α s t 0) :: ofList ((auRecs p α s t).drop 1)
          :: ofList (auSetupE p α s u) :: auPvals p α s t)
        (ofList (auSetupE p α s u) :: auPvals p α s t) (K * auSetupBd p α s t) := by
  obtain ⟨dropP, Kdr, hdrop⟩ := hk.drop
  refine ⟨Cmd.seq dropP dropP, 2000000 * (Kdr + 1), ?_⟩
  intro main p α s t u hu hdisc hs hα hp hαp hst
  set Bd := auSetupBd p α s t with hBd
  obtain ⟨hI, hO, hC, hPv, hLz, hT, hE, hWv, hRep, hFx, hWts, hRecsD, hRecsF⟩ :=
    auSetup_szBd p α s t u hs hα hp hαp hst hu hdisc
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  have hKs : 1 ≤ Kdr + 1 := by omega
  have hKdr : Kdr ≤ Kdr + 1 := by omega
  set TL : List Val := ofList (auSetupE p α s u) :: auPvals p α s t with hTL
  have hstep1 : Pipe main dropP (ofList (auWts p α s t 0) :: (ofList ((auRecs p α s t).drop 1) :: TL))
      (ofList ((auRecs p α s t).drop 1) :: TL) (200000 * (Kdr + 1) * Bd) := by
    have h0 := Pipe.drop main hdrop (ofList (auWts p α s t 0))
    have h1 := Pipe.appendTail (ofList ((auRecs p α s t).drop 1) :: TL) h0
    refine Pipe.le h1 (auSetup_step_le hKdr hKs ?_ hB1)
    nlinarith
  have hstep2 : Pipe main dropP (ofList ((auRecs p α s t).drop 1) :: TL) TL
      (200000 * (Kdr + 1) * Bd) := by
    have h0 := Pipe.drop main hdrop (ofList ((auRecs p α s t).drop 1))
    have h1 := Pipe.appendTail TL h0
    refine Pipe.le h1 (auSetup_step_le hKdr hKs ?_ hB1)
    nlinarith
  have hchain := Pipe.comp hstep1 hstep2
  refine Pipe.le hchain ?_
  rw [auSetup_two]
  nlinarith

/-! ## Chain 4: the record run -/

theorem auSetupRecsPipe (hk : HvdH.KernelLib) (hl : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (p α s t : ℕ) (u : List (ℤ × ℤ)) (W : HvdH.Val),
      u.length = s → (∀ z ∈ u, HvdH.inDisc p z) → 2 ≤ s → 2 ≤ α → 100 ≤ p → α ^ 2 < p → s < t →
      vsz W ≤ 30 * auSetupBd p α s t →
      Pipe main prog (W :: auPvals p α s t) (ofList ((auRecsF p α s t).reverse) :: W :: auPvals p α s t)
        (K * auSetupBd p α s t) := by
  obtain ⟨pickP, Kp, hpick⟩ := hk.pick
  obtain ⟨comb, Kml, hML⟩ := hk.mapList
  obtain ⟨recP, Kre, hrec⟩ := auSetupRecWord hk
  obtain ⟨revP, Kr, hrev⟩ := hl.reverse
  refine ⟨Cmd.seq (pickP 4) (Cmd.seq (comb recP) revP), 2000000 * (Kp + Kml + Kre + Kr + 1), ?_⟩
  intro main p α s t u W hu hdisc hs hα hp hαp hst hW
  set Bd := auSetupBd p α s t with hBd
  obtain ⟨hI, hO, hC, hPv, hLz, hT, hE, hWv, hRep, hFx, hWts, hRecsD, hRecsF⟩ :=
    auSetup_szBd p α s t u hs hα hp hαp hst hu hdisc
  obtain ⟨hBs, hBcs, hBt, hBp, hB1⟩ := auSetupBd_ge p α s t (by omega)
  have htw : 1 ≤ t := by omega
  have hKs : 1 ≤ Kp + Kml + Kre + Kr + 1 := by omega
  have hKp : Kp ≤ Kp + Kml + Kre + Kr + 1 := by omega
  have hKr : Kr ≤ Kp + Kml + Kre + Kr + 1 := by omega
  have hKml : Kml ≤ Kp + Kml + Kre + Kr + 1 := by omega
  have hKre : Kre ≤ Kp + Kml + Kre + Kr + 1 := by omega
  -- the element word
  have helem : ∀ x ∈ auRecs p α s t,
      Pipe main recP [x] [auSetupRecFun x] (Kre * (auSetupLrec p α + 1)) := by
    intro x hx
    simp only [auRecs, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hpre : ∃ (g : ℤ) (w : Val), auRec p α s t k = Val.cons (.int g) w := ⟨_, _, rfl⟩
    have hWtsk : vsz (ofList (auWts p α s t k)) ≤ 16 * auL p α * (p + 1) :=
      auSetup_auWts_vsz_le p α s t k hα hp htw hk
    have hszk : vsz (auRec p α s t k) ≤ auSetupLrec p α :=
      auRec_vsz_le p α s t k hα hp hst hk hWtsk
    have h' : ∀ rest : List Val, WordR main recP (fun vs => vs = [auRec p α s t k] ++ rest)
        (fun _ out => out = [auSetupRecFun (auRec p α s t k)] ++ rest)
        (fun _ => Kre * (auSetupLrec p α + 1)) := by
      intro rest
      have h1 := hrec main (auRec p α s t k) rest hpre
      refine Work.Kernel.WordR_conseq h1 (fun vs hv => hv) ?_ ?_
      · intro vs out _ ho
        rw [ho, auSetupRecFun_auRec p α s t k]
        rfl
      · intro vs _
        nlinarith
    exact Pipe.ofWordRAll h'
  have hxL : ∀ x ∈ auRecs p α s t, vsz x ≤ auSetupLrec p α := by
    intro x hx
    simp only [auRecs, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact auRec_vsz_le p α s t k hα hp hst hk (auSetup_auWts_vsz_le p α s t k hα hp htw hk)
  have hyL : ∀ x ∈ auRecs p α s t, vsz (auSetupRecFun x) ≤ auSetupLrec p α := by
    intro x hx
    simp only [auRecs, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [auSetupRecFun_auRec p α s t k]
    exact auRecF_vsz_le p α s t k hα hp hst hk (auSetup_auWts_vsz_le p α s t k hα hp htw hk)
  have hmlGen : ∀ R : List Val, WordR main (comb recP) (fun vs => vs = ofList (auRecs p α s t) :: R)
      (fun _ out => out = ofList (auRecsF p α s t) :: R)
      (fun _ => t * (Kre * (auSetupLrec p α + 1) + Kml * (auSetupLrec p α + 1)) + Kml) := by
    intro R
    have hml := mapListFun (comb := comb) (Kml := Kml) hML (rest := R)
      (xs := auRecs p α s t) (F := auSetupRecFun) (c := Kre * (auSetupLrec p α + 1))
      (L := auSetupLrec p α) helem hxL hyL
    refine Work.Kernel.WordR_conseq hml (fun vs hv => hv) ?_ ?_
    · intro vs out _ ho
      rw [ho, auRecs_map_auSetupRecFun]
    · intro vs _
      simp only [auRecs, List.length_map, List.length_range]
      exact le_rfl
  -- step 1: pick the table
  have hstep1 : Pipe main (pickP 4) (W :: auPvals p α s t)
      (auTable p α s t :: W :: auPvals p α s t) (200000 * (Kp + Kml + Kre + Kr + 1) * Bd) := by
    have h0 := Pipe.pick main hpick (A := W :: auPvals p α s t) (k := 4) (by simp [auPvals])
    rw [show (W :: auPvals p α s t).getD 4 Val.nil = auTable p α s t from by simp [auPvals]] at h0
    refine Pipe.le h0 (auSetup_mulk_le hKp (by omega) ?_ hB1)
    have hW' : ∀ v ∈ W :: auPvals p α s t, vsz v ≤ 30 * Bd := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hW
      · simp only [auPvals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        exacts [auSetup_vsz_int_le hO, auSetup_vsz_int_le hC, auSetup_vsz_int_le hPv, hT]
    have hszl := auSetup_szl_le hW'
    have hlen : (W :: auPvals p α s t).length = 5 := by simp [auPvals]
    rw [hlen] at hszl
    refine le_trans (szl_take_le _ 5) ?_
    nlinarith
  -- step 2: the mapList
  have hstep2 : Pipe main (comb recP) (auTable p α s t :: W :: auPvals p α s t)
      (ofList (auRecsF p α s t) :: W :: auPvals p α s t)
      (200000 * (Kp + Kml + Kre + Kr + 1) * Bd) := by
    have h1 : Pipe main (comb recP) [ofList (auRecs p α s t)] [ofList (auRecsF p α s t)]
        (200000 * (Kp + Kml + Kre + Kr + 1) * Bd) := by
      refine Pipe.le (Pipe.ofWordRAll hmlGen) ?_
      have hLp : 1 ≤ auL p α * (p + 1) := by nlinarith [auL_pos p α]
      have hLrec : auSetupLrec p α + 1 ≤ 29 * (auL p α * (p + 1)) := by
        simp only [auSetupLrec]
        have hX : 28 * (auL p α * (p + 1)) = 28 * auL p α * (p + 1) := by ring
        rw [← hX]
        nlinarith
      have htL : t * (auL p α * (p + 1)) ≤ Bd := by
        simpa only [mul_assoc] using hBt
      have hb : t * (Kre * (auSetupLrec p α + 1) + Kml * (auSetupLrec p α + 1)) + Kml
          ≤ 29 * (Kre + Kml) * (t * (auL p α * (p + 1))) + Kml := by
        refine Nat.add_le_add_right ?_ Kml
        have h1 : Kre * (auSetupLrec p α + 1) + Kml * (auSetupLrec p α + 1)
            = (Kre + Kml) * (auSetupLrec p α + 1) := by ring
        rw [h1]
        have h2 : (Kre + Kml) * (auSetupLrec p α + 1)
            ≤ (Kre + Kml) * (29 * (auL p α * (p + 1))) := Nat.mul_le_mul_left _ hLrec
        have h3 : t * ((Kre + Kml) * (29 * (auL p α * (p + 1))))
            = 29 * (Kre + Kml) * (t * (auL p α * (p + 1))) := by ring
        calc t * ((Kre + Kml) * (auSetupLrec p α + 1))
            ≤ t * ((Kre + Kml) * (29 * (auL p α * (p + 1)))) := Nat.mul_le_mul_left _ h2
          _ = 29 * (Kre + Kml) * (t * (auL p α * (p + 1))) := h3
      have hb2 : 29 * (Kre + Kml) * (t * (auL p α * (p + 1))) + Kml
          ≤ 200000 * (Kp + Kml + Kre + Kr + 1) * Bd := by
        have hKmls : Kml ≤ (Kp + Kml + Kre + Kr + 1) * Bd := by
          calc Kml ≤ (Kp + Kml + Kre + Kr + 1) * 1 := by omega
            _ ≤ (Kp + Kml + Kre + Kr + 1) * Bd := Nat.mul_le_mul_left _ hB1
        have h1 : Kre + Kml ≤ Kp + Kml + Kre + Kr + 1 := by omega
        have h2 : 29 * (Kre + Kml) * (t * (auL p α * (p + 1)))
            ≤ 29 * (Kp + Kml + Kre + Kr + 1) * Bd :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 29 h1) htL
        have h3 : 29 * (Kp + Kml + Kre + Kr + 1) * Bd
            ≤ 200000 * (Kp + Kml + Kre + Kr + 1) * Bd :=
          Nat.mul_le_mul_right Bd (Nat.mul_le_mul_right _ (by omega))
        linarith
      exact le_trans hb hb2
    exact Pipe.appendTail (W :: auPvals p α s t) h1
  -- step 3: reverse
  have hstep3 : Pipe main revP (ofList (auRecsF p α s t) :: W :: auPvals p α s t)
      (ofList ((auRecsF p α s t).reverse) :: W :: auPvals p α s t)
      (200000 * (Kp + Kml + Kre + Kr + 1) * Bd) := by
    have h0 : Pipe main revP [ofList (auRecsF p α s t)]
        [ofList ((auRecsF p α s t).reverse)] (Kr * (vsz (ofList (auRecsF p α s t)) + 1)) :=
      Pipe.ofWordR_auSetupRunAux (hrev main (auRecsF p α s t))
    have h1 := Pipe.appendTail (W :: auPvals p α s t) h0
    refine Pipe.le h1 (auSetup_step_le hKr hKs ?_ hB1)
    nlinarith
  have hchain := Pipe.comp hstep1 (Pipe.comp hstep2 hstep3)
  refine Pipe.le hchain ?_
  rw [auSetup_three]
  nlinarith

end Work.Resample
