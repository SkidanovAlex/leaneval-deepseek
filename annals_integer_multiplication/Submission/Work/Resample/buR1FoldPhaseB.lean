import Mathlib
import Submission.Work.Resample.buQWcolWord

namespace Work.Resample
open HvdH

-- NOTE for the prover: instantiate `(KL.foldList)` (`WordR main (comb q) ...`, `I : ℕ → List Val → Prop`)
-- with `q := (buQWcolWord KL IL LL).choose`, `xs := (egHs (egM p α)).map
-- (fun h => Val.cons (.int h) (buCol p α s t h))` (so `ofList xs = buColsT p α s t`),
-- `I i st := ∃ z : List (ℤ × ℤ), st = cvecVal z :: Val.int σ :: cvecVal v :: cvecVal acc ::
--   Val.int (s : ℤ) :: Val.int (p : ℤ) :: buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest ∧
--   z = buPFold (buWt p α s t) s (egM p α) v i ∧ z.length = s ∧
--   (∀ y ∈ z, isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8)`,
-- `c := Kcol * (s + 1) * (Cm (Kcol * p) + p + 1)` and `L := 100 * (s + 1) * (p + 1)`.
-- The invariant is preserved by `buQW_fold_isz` (row-sum bound `hrow` plus `buInV B v`); each step is
-- the `Pipe` of `buQWcolWord` applied at the tail `buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest`;
-- use `buColsN_length`/`buQWhs_length` for the column index bound, `buPFold_succ`/`buPFold_zero` for the
-- accumulator, `buQW_col_vsz_le` for `L`.  Do NOT import `buQWr1Kit`/`buR1Snap` (they clash with
-- `buQWstepKit`).  The same fold is carried out inside `Submission/Work/Resample/buQWstep.lean`.

theorem buR1FoldPhaseB (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (p α s t : ℕ)
    (hmono : Monotone Cm) (hmb : HvdH.MulBelow main N Cm)
    (hKN : (buQWcolWord KL IL LL).choose_spec.choose * p < N)
    (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
    (hrow : ∀ ℓ : ℤ, ∑ h ∈ egHset (egM p α),
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ))
    (v acc : List (ℤ × ℤ)) (hv : v.length = s) (ha : acc.length = s)
    (hbv : buInV B v) (hbacc : buInV B2 acc) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (rest : List Val) :
    WordR main ((KL.foldList).choose ((buQWcolWord KL IL LL).choose))
      (fun vs => vs = buColsT p α s t :: ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) ::
        Val.int σ :: cvecVal v :: cvecVal acc :: Val.int (s : ℤ) :: Val.int (p : ℤ) ::
        buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest)
      (fun _ out => out = cvecVal (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)) ::
        Val.int σ :: cvecVal v :: cvecVal acc :: Val.int (s : ℤ) :: Val.int (p : ℤ) ::
        buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest)
      (fun _ => 2 * egM p α *
        ((buQWcolWord KL IL LL).choose_spec.choose * (s + 1) *
            (Cm ((buQWcolWord KL IL LL).choose_spec.choose * p) + p + 1) +
          (KL.foldList).choose_spec.choose * (100 * (s + 1) * (p + 1) + 1)) +
        (KL.foldList).choose_spec.choose) := by
  set foldP : HvdH.Cmd → HvdH.Cmd := (KL.foldList).choose with hfoldP
  set kfold : ℕ := (KL.foldList).choose_spec.choose with hkfold
  have hfold := (KL.foldList).choose_spec.choose_spec
  set colP : HvdH.Cmd := (buQWcolWord KL IL LL).choose with hcolP
  set kcol : ℕ := (buQWcolWord KL IL LL).choose_spec.choose with hkcol
  have hcol := (buQWcolWord KL IL LL).choose_spec.choose_spec
  set XS : List Val := (egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)) with hXS
  set FT : List Val := buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest with hFT
  set F : List Val := Val.int σ :: cvecVal v :: cvecVal acc :: Val.int (s : ℤ) :: Val.int (p : ℤ) ::
      FT with hF
  have hofXS : ofList XS = buColsT p α s t := by rw [hXS]; rfl
  have hXSlen : XS.length = 2 * egM p α := by
    simp only [hXS, List.length_map, buQWhs_length]
  have hvsz : ∀ z ∈ v, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 :=
    fun z hz => buQW_isz_of_buInV hB hbv z hz
  have haccsz : ∀ z ∈ acc, isz z.1 ≤ p + 5 ∧ isz z.2 ≤ p + 5 :=
    fun z hz => buQW_isz_of_buInV hB2 hbacc z hz
  let LEL : ℕ := 100 * (s + 1) * (p + 1)
  let cCol : ℕ := kcol * (s + 1) * (Cm (kcol * p) + p + 1)
  set I : ℕ → List Val → Prop := fun i st =>
    ∃ z : List (ℤ × ℤ), st = cvecVal z :: F ∧
      z = buPFold (buWt p α s t) s (egM p α) v i ∧ z.length = s ∧
      (∀ y ∈ z, isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8) with hI
  have hLbnd : ∀ x ∈ XS, vsz x ≤ LEL := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨h, hh, rfl⟩
    exact buQW_col_vsz_le p α s t hα hp hrow hh
  have hElem : ∀ i st, i < XS.length → I i st → WordR main colP
      (fun vs => vs = XS.getD i .nil :: st) (fun _ out => I (i + 1) out) (fun _ => cCol) := by
    intro i st hi hIst
    obtain ⟨z, hst, hz, hzlen, hzsz⟩ := hIst
    have him : i < (egHs (egM p α)).length := by
      rw [hXSlen] at hi; rw [buQWhs_length]; exact hi
    have hidx : i < (buColsN (buWt p α s t) s (egM p α)).length := by
      rw [buColsN_length]; rw [buQWhs_length] at him; exact him
    have hh : (egHs (egM p α)).getD i 0 ∈ egHs (egM p α) := by
      rw [List.getD_eq_getElem _ _ him]; exact List.getElem_mem him
    have hhmem : (egHs (egM p α)).getD i 0 ∈ egHset (egM p α) := by
      rw [← (buQWhs (egM p α)).1, List.mem_toFinset]; exact hh
    have hwisz : ∀ y ∈ buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0), isz y ≤ p + 3 := by
      intro y hy
      obtain ⟨ℓ, rfl⟩ := List.mem_ofFn.mp hy
      exact buQT_buWt_isz_le p α s t hα hp hrow _ _ hhmem
    have hcolPipe : Pipe main colP
        [.cons (.int ((egHs (egM p α)).getD i 0))
            (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)),
          cvecVal z, .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)]
        [cvecVal (buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
            (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))),
          .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] cCol :=
      hcol p α s t hs hp main N Cm hmono hmb hKN ((egHs (egM p α)).getD i 0)
        (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)) hh rfl hwisz
        (buColL_length _ _ _) σ hσ v z acc hv hzlen ha hvsz hzsz haccsz
    have hXSget : XS.getD i .nil = Val.cons (.int ((egHs (egM p α)).getD i 0))
        (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)) := by
      rw [List.getD_eq_getElem _ _ hi]
      simp only [hXS, List.getElem_map]
      rw [List.getD_eq_getElem _ _ him]
      rfl
    have hz' : buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
        (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))
        = buPFold (buWt p α s t) s (egM p α) v (i + 1) := by
      rw [hz]
      exact (buPFold_succ (buWt p α s t) s (egM p α) v i hidx).symm
    have hz'len : (buPFold (buWt p α s t) s (egM p α) v (i + 1)).length = s :=
      buPFold_length (buWt p α s t) s (egM p α) v hv (i + 1) (by rw [buColsN_length]; omega)
    have hz'sz : ∀ y ∈ buPFold (buWt p α s t) s (egM p α) v (i + 1),
        isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8 := by
      intro y hy
      obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_iff_getElem.mp hy
      have h := buQW_fold_isz p α s t hp hrow B hB v hv hbv (i + 1) (by omega) ℓ
        (by rw [← hz'len]; exact hℓ)
      rwa [List.getD_eq_getElem _ _ hℓ] at h
    intro vs hvs
    have hvseq : vs = [Val.cons (.int ((egHs (egM p α)).getD i 0))
        (ofList ((buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0)).map Val.int)),
        cvecVal z, .int σ, cvecVal v, cvecVal acc, .int (s : ℤ), .int (p : ℤ)] ++ FT := by
      rw [hvs, hst, hXSget]
      rfl
    intro s0 R hR
    obtain ⟨out, s1, n1, hout1, hev, hn, hstk, hoth⟩ := hcolPipe FT vs hvseq s0 R hR
    have hout2 : out = cvecVal (buAddV z (buMulCol (buColL (buWt p α s t) s
        ((egHs (egM p α)).getD i 0))
        (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v))) :: F := by
      rw [hout1]
      rfl
    refine ⟨out, s1, n1, ?_, hev, hn, hstk, hoth⟩
    refine ⟨buAddV z (buMulCol (buColL (buWt p α s t) s ((egHs (egM p α)).getD i 0))
      (buRot (((egHs (egM p α)).getD i 0 % (s : ℤ)).toNat) v)), hout2, ?_, ?_, ?_⟩
    · exact hz'
    · rw [hz']; exact hz'len
    · intro y hy
      rw [hz'] at hy
      exact hz'sz y hy
  have hFoldApp : WordR main (foldP colP)
      (fun vs => ∃ acc0, vs = ofList XS :: acc0 ∧ I 0 acc0)
      (fun _ out => I XS.length out)
      (fun _ => XS.length * (cCol + kfold * (LEL + 1)) + kfold) :=
    hfold main colP XS I cCol LEL hLbnd hElem
  refine KL.conseq main (foldP colP)
    (fun vs => ∃ acc0, vs = ofList XS :: acc0 ∧ I 0 acc0)
    (fun vs => vs = buColsT p α s t :: ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: F)
    (fun _ out => I XS.length out)
    (fun _ out => out = cvecVal (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)) :: F)
    (fun _ => XS.length * (cCol + kfold * (LEL + 1)) + kfold)
    (fun _ => 2 * egM p α * (kcol * (s + 1) * (Cm (kcol * p) + p + 1)
        + kfold * (100 * (s + 1) * (p + 1) + 1)) + kfold)
    hFoldApp ?_ ?_ ?_
  · intro vs hvs
    refine ⟨ofList (List.replicate s (cfxVal ((0 : ℤ), (0 : ℤ)))) :: F, ?_, ?_⟩
    · rw [hvs, hofXS]
    · refine ⟨List.replicate s ((0 : ℤ), (0 : ℤ)), ?_, ?_, ?_, ?_⟩
      · rw [cvecVal, List.map_replicate]
      · rw [buPFold_zero]
      · rw [List.length_replicate]
      · intro y hy
        have hy' : y = ((0 : ℤ), (0 : ℤ)) := List.eq_of_mem_replicate hy
        rw [hy']
        have h0 : isz ((0 : ℤ)) ≤ 2 * p + 8 := by
          simp only [isz, Int.natAbs_zero, Nat.size_zero]; omega
        exact ⟨h0, h0⟩
  · intro vs out _ hout
    obtain ⟨z, hz, hzf, _, _⟩ := hout
    rw [hz, hzf, hXSlen]
  · intro vs _
    exact le_of_eq (by rw [hXSlen])

end Work.Resample
