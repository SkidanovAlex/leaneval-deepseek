import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWstepKit
import Submission.Work.Resample.buJsumL_ofFn
import Submission.Work.Resample.buQWhs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## The entry formula of the partial fold

The pointwise description of the partial fold `buPFold` in terms of the shifts and the input
vector: this is the `b1rPS1`/`b1rPS2`/`b1rPFold_getD1`/`b1rPFold_getD2` block of
`Submission/Work/Resample/sliceB1RDefs.lean`, transcribed into the `buPFold`/`buKk` vocabulary of
`buQWstepKit` (which does not contain it, and cannot be combined with `sliceB1RDefs` because of the
duplicate `buPFold_*` declarations). -/

/-- The `ℓ`-th coordinate sum of the first `i` columns (first coordinate). -/
noncomputable def buQW3_PS1 (s : ℕ) (Wt : ℤ → ℤ → ℤ) (m : ℕ) (v : List (ℤ × ℤ))
    (ℓ i : ℕ) : ℤ :=
  List.sum (List.map (fun h => Wt (ℓ : ℤ) h *
    (v.getD ((ℓ + (h % (s : ℤ)).toNat) % v.length) (0, 0)).1) ((egHs m).take i))

/-- The `ℓ`-th coordinate sum of the first `i` columns (second coordinate). -/
noncomputable def buQW3_PS2 (s : ℕ) (Wt : ℤ → ℤ → ℤ) (m : ℕ) (v : List (ℤ × ℤ))
    (ℓ i : ℕ) : ℤ :=
  List.sum (List.map (fun h => Wt (ℓ : ℤ) h *
    (v.getD ((ℓ + (h % (s : ℤ)).toNat) % v.length) (0, 0)).2) ((egHs m).take i))

/-- The rotation amount `buKk` is at most `s`, so that `buRot_getD` applies. -/
theorem buQW3_Kk_le (s m i : ℕ) (hs : 0 < s) : buKk s m i ≤ s := by
  have hsZ : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs
  have h1 : (egHs m).getD i 0 % (s : ℤ) < (s : ℤ) := Int.emod_lt_of_pos _ hsZ
  have h0 : 0 ≤ (egHs m).getD i 0 % (s : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : ((egHs m).getD i 0 % (s : ℤ)).toNat < s := by omega
  simpa only [buKk] using le_of_lt h2

/-- **The entry formula of the partial fold, first coordinate.** -/
theorem buQW3_PFold_getD1 (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (hs : 0 < s) (v : List (ℤ × ℤ))
    (hv : v.length = s) (ℓ : ℕ) (hℓ : ℓ < s) :
    ∀ i, i ≤ (buColsN Wt s m).length →
      ((buPFold Wt s m v i).getD ℓ (0, 0)).1 = buQW3_PS1 s Wt m v ℓ i := by
  intro i
  induction i with
  | zero => intro _; simp [buPFold, buQW3_PS1]
  | succ i ih =>
    intro hi
    have hi' : i < (buColsN Wt s m).length := by omega
    have hm2 : i < (egHs m).length := by rw [buColsN_length] at hi'; rw [buQWhs_length]; omega
    have hleni : (buPFold Wt s m v i).length = s := buPFold_length Wt s m v hv i (le_of_lt hi')
    have hlenm : (buMulCol (buColL Wt s ((egHs m).getD i 0)) (buRot (buKk s m i) v)).length = s := by
      rw [buMulCol_length, buColL_length, buRot_length, hv]; omega
    rw [buPFold_succ Wt s m v i hi',
      buAddV_getD _ _ ℓ (by rw [hleni]; exact hℓ) (by rw [hlenm]; exact hℓ),
      buMulCol_getD _ _ ℓ (by rw [buColL_length]; exact hℓ)
        (by rw [buRot_length, hv]; exact hℓ),
      ih (le_of_lt hi'), buRot_getD (buKk s m i) v ℓ (by rw [hv]; exact hℓ)
        (by rw [hv]; exact buQW3_Kk_le s m i hs),
      buColL_getD Wt s _ ℓ hℓ]
    have htake : (egHs m).take (i + 1) = (egHs m).take i ++ [(egHs m).getD i 0] := by
      rw [List.getD_eq_getElem _ _ hm2]
      exact (List.take_concat_get' (egHs m) i hm2).symm
    simp only [buQW3_PS1, htake, buKk, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_singleton, Prod.fst_add]

/-- **The entry formula of the partial fold, second coordinate.** -/
theorem buQW3_PFold_getD2 (Wt : ℤ → ℤ → ℤ) (s m : ℕ) (hs : 0 < s) (v : List (ℤ × ℤ))
    (hv : v.length = s) (ℓ : ℕ) (hℓ : ℓ < s) :
    ∀ i, i ≤ (buColsN Wt s m).length →
      ((buPFold Wt s m v i).getD ℓ (0, 0)).2 = buQW3_PS2 s Wt m v ℓ i := by
  intro i
  induction i with
  | zero => intro _; simp [buPFold, buQW3_PS2]
  | succ i ih =>
    intro hi
    have hi' : i < (buColsN Wt s m).length := by omega
    have hm2 : i < (egHs m).length := by rw [buColsN_length] at hi'; rw [buQWhs_length]; omega
    have hleni : (buPFold Wt s m v i).length = s := buPFold_length Wt s m v hv i (le_of_lt hi')
    have hlenm : (buMulCol (buColL Wt s ((egHs m).getD i 0)) (buRot (buKk s m i) v)).length = s := by
      rw [buMulCol_length, buColL_length, buRot_length, hv]; omega
    rw [buPFold_succ Wt s m v i hi',
      buAddV_getD _ _ ℓ (by rw [hleni]; exact hℓ) (by rw [hlenm]; exact hℓ),
      buMulCol_getD _ _ ℓ (by rw [buColL_length]; exact hℓ)
        (by rw [buRot_length, hv]; exact hℓ),
      ih (le_of_lt hi'), buRot_getD (buKk s m i) v ℓ (by rw [hv]; exact hℓ)
        (by rw [hv]; exact buQW3_Kk_le s m i hs),
      buColL_getD Wt s _ ℓ hℓ]
    have htake : (egHs m).take (i + 1) = (egHs m).take i ++ [(egHs m).getD i 0] := by
      rw [List.getD_eq_getElem _ _ hm2]
      exact (List.take_concat_get' (egHs m) i hm2).symm
    simp only [buQW3_PS2, htake, buKk, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_singleton, Prod.snd_add]

/-! ## The round bridge -/

/-- Reading `List.ofFn` outside its range. -/
theorem buQW3_getD_ofFn {β : Type} {n : ℕ} (f : Fin n → β) (i : ℕ) (d : β) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

/-- `List.ofFn`-reading at a `Fin` index. -/
theorem buQW3_getD_ofFn_fin {β : Type} {n : ℕ} (f : Fin n → β) (j : Fin n) :
    (List.ofFn f).getD (j : ℕ) (f j) = f j := by
  rw [buQW3_getD_ofFn, dif_pos j.isLt]

/-- **One round, list level** (paper Lemma 4.11): folding the columns `buColsN Wt s (egM p α)` onto
`0` and dividing by `2^p` computes the convolution `buRound Wt p α s t hs` of the vector
`j ↦ u.getD j (0,0)`, provided `u` has length `s`.

This is `Work.Resample.buRoundL_eq_ofFn_gen` of `Submission/Work/Resample/buRoundL_ofFn.lean`,
transcribed into the vocabulary of `buQWstepKit`. -/
theorem buQW3_RoundL_eq_ofFn_gen (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s)
    (u : List (ℤ × ℤ)) (hu : u.length = s) :
    buRoundL Wt p s (egM p α) u =
      List.ofFn (fun ℓ : Fin s =>
        buRound Wt p α s t hs (fun j : Fin s => u.getD (j : ℕ) (0, 0)) ℓ) := by
  have hm : 2 * egM p α ≤ (buColsN Wt s (egM p α)).length :=
    le_of_eq (buColsN_length Wt s (egM p α)).symm
  have hlenp : (buPFold Wt s (egM p α) u (2 * egM p α)).length = s :=
    buPFold_length Wt s (egM p α) u hu (2 * egM p α) hm
  have hlen1 : (buRoundL Wt p s (egM p α) u).length = s := by
    rw [buRoundL_eq_pfold, buTdivV_length, hlenp]
  apply List.ext_getElem
  · rw [hlen1, List.length_ofFn]
  · intro k h1 h2
    have hks : k < s := by simpa using h2
    rw [List.getElem_ofFn, ← List.getD_eq_getElem _ _ h1]
    rw [buRoundL_eq_pfold, buTdivV_getD _ _ k (by rw [hlenp]; exact hks),
      buQW3_PFold_getD1 _ _ _ hs u hu k hks _ hm, buQW3_PFold_getD2 _ _ _ hs u hu k hks _ hm]
    have htk : (egHs (egM p α)).take (2 * egM p α) = egHs (egM p α) :=
      List.take_of_length_le (le_of_eq (buQWhs_length _))
    simp only [buQW3_PS1, buQW3_PS2, htk]
    rw [sum_toFinset (buQWhs_nodup (egM p α)), sum_toFinset (buQWhs_nodup (egM p α)),
      (buQWhs (egM p α)).1]
    have hkey : ∀ h : ℤ, ((fun j : Fin s => u.getD (j : ℕ) (0, 0))
          (egIdx s hs (((⟨k, hks⟩ : Fin s) : ℤ) + h)))
        = (u.getD ((k + (h % (s : ℤ)).toNat) % u.length) (0, 0)) := by
      intro h
      have h1 : ((egIdx s hs (((⟨k, hks⟩ : Fin s) : ℤ) + h) : Fin s) : ℕ)
          = (k + (h % (s : ℤ)).toNat) % s := by
        have hcast : ((⟨k, hks⟩ : Fin s) : ℤ) = (k : ℤ) := by simp
        rw [hcast, egIdx]
        show (((k : ℤ) + h) % (s : ℤ)).toNat = (k + (h % (s : ℤ)).toNat) % s
        exact (buIdx_eq s hs k h).symm
      show u.getD ((egIdx s hs (((⟨k, hks⟩ : Fin s) : ℤ) + h) : Fin s) : ℕ) (0, 0)
        = u.getD ((k + (h % (s : ℤ)).toNat) % u.length) (0, 0)
      rw [h1, hu]
    simp only [buRound, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · refine congrArg (fun z : ℤ => Int.tdiv z ((2 : ℤ) ^ p)) ?_
      exact Finset.sum_congr rfl (fun x _ => by rw [congrArg Prod.fst (hkey x)])
    · refine congrArg (fun z : ℤ => Int.tdiv z ((2 : ℤ) ^ p)) ?_
      exact Finset.sum_congr rfl (fun x _ => by rw [congrArg Prod.snd (hkey x)])

/-- **One round, vector level**: `buRoundL` on the `List.ofFn` of a vector is the `List.ofFn` of
`buRound`. -/
theorem buQW3_RoundL_ofFn (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) :
    buRoundL Wt p s (egM p α) (List.ofFn v) = List.ofFn (buRound Wt p α s t hs v) := by
  have hfun : (fun j : Fin s => (List.ofFn v).getD (j : ℕ) (0, 0)) = v := by
    funext j
    rw [buQW3_getD_ofFn, dif_pos j.isLt]
  rw [buQW3_RoundL_eq_ofFn_gen Wt p α s t hs (List.ofFn v) (List.length_ofFn), hfun]

/-! ## The bridge -/

/-- `egGet` on the `Fin`-vector arising from a list. -/
theorem buQW3_egGet_ofFn_getD {n : ℕ} (u : List (ℤ × ℤ)) (hu : u.length = n) (i : ℕ) :
    egGet (fun j : Fin n => u.getD (j : ℕ) (0, 0)) i = u.getD i (0, 0) := by
  unfold egGet
  split
  · rfl
  · exact (List.getD_eq_default u (0, 0) (by omega)).symm

/-- `egGet` at an index which is a `Fin`. -/
theorem buQW3_egGet_fin {n : ℕ} (v : Fin n → ℤ × ℤ) (j : Fin n) : egGet v (j : ℕ) = v j := by
  unfold egGet
  rw [dif_pos j.isLt]

/-- The vector fed into the Neumann series by `buPhi`: the fused `C̃ ∘ P̃_t` step followed by the
halving, written in the exact form of the body of `buPhi`. -/
noncomputable def buQW3_V0 (s t : ℕ) (u : List (ℤ × ℤ)) : Fin s → ℤ × ℤ :=
  fun ℓ =>
    (Int.tdiv ((egGet (fun j : Fin t => u.getD (j : ℕ) (0, 0)) (egNu s t (ℓ : ℕ))).1) 2,
     Int.tdiv ((egGet (fun j : Fin t => u.getD (j : ℕ) (0, 0)) (egNu s t (ℓ : ℕ))).2) 2)

/-- The diagonal scaling of a vector written with `List.ofFn`. -/
theorem buQW3_DscL_ofFn (Wd : ℤ → ℤ) (p s : ℕ) (f : Fin s → ℤ × ℤ) :
    buDscL Wd p s (List.ofFn f) = List.ofFn (buDsc Wd p s f) := by
  rw [buDscL]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < s := by simpa using h2
    rw [List.getElem_map, List.getElem_zip]
    simp only [List.getElem_ofFn, buDsc]

/-- The final permutation, read at a `Fin` index. -/
theorem buQW3_PermL_getD (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (d : List (ℤ × ℤ))
    (k : Fin s) :
    (buPermL s t hs hcop d).getD (k : ℕ) (0, 0) =
      d.getD (((egGam s t hs hcop k : Fin s) : ℕ)) (0, 0) := by
  rw [buPermL, buQW3_getD_ofFn, dif_pos k.isLt]

/-- `buQW3_V0`, unfolded (the equation is only available in the applied form, so we state it as an
equality of functions). -/
theorem buQW3_V0_eq (s t : ℕ) (u : List (ℤ × ℤ)) :
    buQW3_V0 s t u = fun ℓ : Fin s =>
      (Int.tdiv ((egGet (fun j : Fin t => u.getD (j : ℕ) (0, 0)) (egNu s t (ℓ : ℕ))).1) 2,
       Int.tdiv ((egGet (fun j : Fin t => u.getD (j : ℕ) (0, 0)) (egNu s t (ℓ : ℕ))).2) 2) := by
  funext ℓ
  rfl

/-- Unfolding `buPhi` at one coordinate. -/
theorem buQW3_Phi_apply (Wt : ℤ → ℤ → ℤ) (Wd : ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s)
    (hcop : Nat.Coprime t s) (u : List (ℤ × ℤ)) (k : Fin s) :
    buPhi Wt Wd p α s t hs hcop (fun j : Fin t => u.getD (j : ℕ) (0, 0)) k =
      (buDsc Wd p s (buJsum Wt p α s t hs (buQW3_V0 s t u))) (egGam s t hs hcop k) := by
  simp only [buPhi]
  rw [buQW3_V0_eq]
  rw [buQW3_egGet_fin]

/-- The list-level map `buPhiL` is the entrywise `List.ofFn` of the `Fin`-level map `buPhi`. -/
theorem buQW3_PhiL_eq_ofFn (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s)
    (u : List (ℤ × ℤ)) (hu : u.length = t) :
    buPhiL p α s t hs hcop u =
      List.ofFn (buPhi (buWt p α s t) (buWd p α s t) p α s t hs hcop
        (fun j : Fin t => u.getD (j : ℕ) (0, 0))) := by
  have hsel : buSelL s t u = List.ofFn (buQW3_V0 s t u) := by
    rw [buSelL, List.ofFn_inj]
    funext ℓ
    simp only [buQW3_V0, buHalve]
    rw [buQW3_egGet_ofFn_getD u hu]
  have hJ : buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) (buSelL s t u) =
      List.ofFn (buJsum (buWt p α s t) p α s t hs (buQW3_V0 s t u)) := by
    rw [hsel]
    exact buJsumL_ofFn (buWt p α s t) p α s t hs
      (fun v => buQW3_RoundL_ofFn (buWt p α s t) p α s t hs v) (buQW3_V0 s t u)
  have hD : buDscL (buWd p α s t) p s
        (buJsumL (buWt p α s t) p s (egM p α) (egN p α s t) (buSelL s t u)) =
      List.ofFn (buDsc (buWd p α s t) p s
        (buJsum (buWt p α s t) p α s t hs (buQW3_V0 s t u))) := by
    rw [hJ, buQW3_DscL_ofFn]
  rw [buPhiL, hD, buPermL, List.ofFn_inj]
  funext k
  simp only [buQW3_getD_ofFn, dif_pos (egGam s t hs hcop k).isLt]
  rw [buQW3_Phi_apply]

/-- **The list-level / `Fin`-level bridge of the `B̃` word**: the `List.ofFn`-built `buPhiL` is the
pointwise image of the `Fin`-level `buPhi` of the same weight tables.

This is a PORT of `Work.Resample.buQWbridge` (`Submission/Work/Resample/buQWbridge.lean`, already
proved) into the `buQWstepKit` vocabulary.  WHY A PORT AND NOT AN IMPORT: `Work.Resample.buQWbridge`
gets its input `buRoundL Wt p s m (List.ofFn v) = List.ofFn (buRound …)` from
`Work.Resample.buRoundL_ofFn`, which imports `Submission.Work.Resample.sliceB1RDefs`; and
`sliceB1RDefs` re-declares `Work.Resample.buPFold`, `buPFold_zero`, `buPFold_succ`, … which are ALSO
declared in `Submission/Work/Resample/buQWstepKit.lean`.  Any environment containing both modules
fails with `environment already contains 'Work.Resample.buPFold_zero'`.  THIS file must therefore
import `buQWstepKit` (it is needed by the rounds stage of the caller) and must NOT import
`sliceB1RDefs`, `buRoundL_ofFn` or `buQWbridge` -- importing any of them makes the file unbuildable.

READ (do not import!) `Submission/Work/Resample/buQWbridge.lean` and
`Submission/Work/Resample/sliceB1RDefs.lean`; the proof below is a transcription of theirs with the
`b1r*`-vocabulary replaced by the `buQWstepKit` one (`b1rPFold → buPFold`, `b1rKk → buKk`,
`b1rColsN_length → buColsN_length`, `b1rColsN_getD → buColsN_getD`, `b1rAddV_getD → buAddV_getD`,
`b1rMulCol_getD → buMulCol_getD`, `b1rRot_getD' → buRot_getD`, `b1rIdx_eq → buIdx_eq`,
`b1r_sum_toFinset → sum_toFinset`, `b1rRoundL_eq_pfold → buRoundL_eq_pfold`,
`b1rPFold_getD1/2` and `b1rPS1/b1rPS2`, which have no counterpart in `buQWstepKit`: define
`buPS1`/`buPS2` yourself (copy the definitions from `sliceB1RDefs.lean`, renaming them, e.g.
`buQ3PS1`) and reprove the two pointwise lemmas `∀ i ≤ (buColsN Wt s m).length, ((buPFold Wt s m v i).getD ℓ (0,0)).1 = buQ3PS1 s Wt m v ℓ i` and the `.2`/`buQ3PS2` analogue (copy the
inductions from `sliceB1RDefs.lean` lines ~282-336); note `buPFold_succ`, `buPFold_length`,
`buPFold_zero`, `buRowS_zero`, `buRowS_succ`, `buRowS_full`, `buRowS_mono`, `buRowS_le_row`,
`sum_toFinset`, `buIdx_eq`, `buRot_getD`, `buAddV_getD`, `buMulCol_getD`, `buTdivV_getD`,
`buColL_getD`, `buColL_length`, `buColsN_length`, `buColsN_getD`, `getD_drop_eq`, `getD_take_eq`,
`buColsN_length`, `buRoundL_eq_pfold` are all already PROVED in `buQWstepKit`.  Then
`buRoundL_eq_ofFn_gen`/`buRoundL_ofFn` follow as in `buRoundL_ofFn.lean` (which ports
`b1rRoundL_eq_ofFn_gen`; `buQWhs_length`, `buQWhs_nodup`, `buQWhs`, `List.take_of_length_le`,
`buRound` are available), and finally the bridge follows the proof of `buQWbridge.lean`, where the
`buJsumL_ofFn` step must also be replaced by a local copy (`buQWbridge`'s proof has it inline as
`buQWb_JsumL_eq_ofFn`; `buJsumL_ofFn.lean` is a valid import -- it imports only `buQWdefs` and
`buQWstepKit` -- but if you import it, beware that its helper `buAddV_ofFn`/`buSMulV_ofFn`/
`buJacc`/`buJfold_range`/etc. are fine, no clash).
Keep every helper you add in a namespace that does not collide with existing declarations. -/
theorem buQWbr3 (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (u : List (ℤ × ℤ))
    (hu : u.length = t) :
    (Work.Resample.buPhiL p α s t hs hcop u).length = s ∧
    ∀ k : Fin s, (Work.Resample.buPhiL p α s t hs hcop u).getD (k : ℕ) (0, 0) =
      Work.Resample.buPhi (Work.Resample.buWt p α s t) (Work.Resample.buWd p α s t) p α s t hs hcop
        (fun j : Fin t => u.getD (j : ℕ) (0, 0)) k := by
  constructor
  · rw [buQW3_PhiL_eq_ofFn p α s t hs hcop u hu, List.length_ofFn]
  · intro k
    rw [buQW3_PhiL_eq_ofFn p α s t hs hcop u hu, buQW3_getD_ofFn, dif_pos k.isLt]

end Work.Resample
