import Mathlib
import Submission.Work.Resample.buQWcolWord
import Submission.Work.Resample.buQWpostWord
import Submission.Work.Resample.buR1FoldPhaseB
import Submission.Work.Resample.buR1RoundDisc
import Submission.Work.Resample.buR1SetupW

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.Resample

open HvdH

theorem buQWround1 (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib) (FL : HvdH.FxLib) :
    ∃ (q : HvdH.Cmd) (Kc : ℕ),
    ∀ (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
      (B B2 : ℕ) (hB : B ≤ 2 ^ (p + 2)) (hB2 : B2 ≤ 2 ^ (p + 2))
      (hrow : ∀ ℓ : ℤ, ∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α),
        |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p / 2
          + 8 * (Work.Resample.egM p α : ℝ))
      (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kc * p < N →
    HvdH.WordR main q
      (fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val),
        (σ = 1 ∨ σ = -1) ∧
        vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v.length = s ∧ acc.length = s ∧ Work.Resample.buInV B v ∧ Work.Resample.buInV B2 acc)
      (fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val) (v' acc' : List (ℤ × ℤ)),
        (σ = 1 ∨ σ = -1) ∧
        vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        out = HvdH.cvecVal v' :: HvdH.cvecVal acc' ::
          Work.Resample.buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
        v' = Work.Resample.buRoundL (Work.Resample.buWt p α s t) p s (Work.Resample.egM p α) v ∧
        acc' = Work.Resample.buAddV acc (Work.Resample.buSMulV σ v') ∧
        v'.length = s ∧ acc'.length = s ∧
        Work.Resample.buInV (B / 2 + 34 * Work.Resample.egM p α + 4) v' ∧
        Work.Resample.buInV (B2 + B / 2 + 34 * Work.Resample.egM p α + 5) acc')
      (fun _ => Kc * (Work.Resample.egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1)) := by
  obtain ⟨pickP, Kpick, hpick⟩ := KL.pick
  obtain ⟨rollP, Kroll, hroll⟩ := KL.roll
  obtain ⟨pushP, Kpush, hpush⟩ := KL.pushVal
  obtain ⟨repP, Krep, hrep⟩ := LL.replicate
  obtain ⟨postP, Kpost, hpost⟩ := buQWpostWord KL IL
  let colP : Cmd := (buQWcolWord KL IL LL).choose
  let Kcol : ℕ := (buQWcolWord KL IL LL).choose_spec.choose
  let foldComb : Cmd → Cmd := (KL.foldList).choose
  let Kfold : ℕ := (KL.foldList).choose_spec.choose
  let KS : ℕ := Kpick + Kroll + Kpush + Krep + Kcol + Kfold + Kpost + 100
  have hKpick : Kpick ≤ KS := by simp only [KS]; omega
  have hKroll : Kroll ≤ KS := by simp only [KS]; omega
  have hKpush : Kpush ≤ KS := by simp only [KS]; omega
  have hKrep : Krep ≤ KS := by simp only [KS]; omega
  have hKcol : Kcol ≤ KS := by simp only [KS]; omega
  have hKfold : Kfold ≤ KS := by simp only [KS]; omega
  have hKpost : Kpost ≤ KS := by simp only [KS]; omega
  have hKS1 : 1 ≤ KS := by simp only [KS]; omega
  let Kc : ℕ := 100000000 * KS
  refine ⟨.seq (buR1SetupProg pickP rollP pushP repP)
      (.seq (foldComb colP) postP), Kc, ?_⟩
  intro p α s t hs hst hα hp B B2 hB hB2 hrow main N Cm hmono hmb hKN
  have hKcolKc : Kcol ≤ Kc := by simp only [Kc]; omega
  have hKN' : Kcol * p < N := by
    have h : Kcol * p ≤ Kc * p := Nat.mul_le_mul_right p hKcolKc
    omega
  -- ===== the cost bound =====
  have hpp : (s + 1) * (p + 1) ≤ (s + 1) * (Cm (Kc * p) + p + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hCmmono : Cm (Kcol * p) ≤ Cm (Kc * p) := hmono (Nat.mul_le_mul_right p hKcolKc)
  have hS1CC1 : 1 ≤ (s + 1) * (Cm (Kc * p) + p + 1) := by
    have h1 : 1 ≤ s + 1 := by omega
    have h2 : 1 ≤ Cm (Kc * p) + p + 1 := by omega
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ (s + 1) * (Cm (Kc * p) + p + 1) := Nat.mul_le_mul h1 h2
  have hM11 : 1 ≤ egM p α + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hcost : 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) +
      2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
        Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold +
      Kpost * (s + 1) * (p + 1)
      ≤ Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1) := by
    have hW : Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1) =
        100000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by
      simp only [Kc]; ring
    rw [hW]
    have h1 : 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) ≤
        2000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by
      calc 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1))
          = 2000000 * ((egM p α + 1) * (KS * ((s + 1) * (p + 1)))) := by ring
        _ ≤ 2000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpp))
    have hA : Kcol * (s + 1) * (Cm (Kcol * p) + p + 1)
        ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) := by
      calc Kcol * (s + 1) * (Cm (Kcol * p) + p + 1)
          = Kcol * ((s + 1) * (Cm (Kcol * p) + p + 1)) := by ring
        _ ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) :=
            Nat.mul_le_mul hKcol (Nat.mul_le_mul_left _ (by omega))
    have hB' : Kfold * (100 * (s + 1) * (p + 1) + 1)
        ≤ 101 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
      have h1 : 100 * (s + 1) * (p + 1) + 1 ≤ 101 * ((s + 1) * (Cm (Kc * p) + p + 1)) := by
        have h2 : (s + 1) * (p + 1) ≤ (s + 1) * (Cm (Kc * p) + p + 1) := hpp
        have h3 : 1 ≤ (s + 1) * (Cm (Kc * p) + p + 1) := hS1CC1
        have h4 : 100 * (s + 1) * (p + 1) ≤ 100 * ((s + 1) * (Cm (Kc * p) + p + 1)) := by
          calc 100 * (s + 1) * (p + 1) = 100 * ((s + 1) * (p + 1)) := by ring
            _ ≤ 100 * ((s + 1) * (Cm (Kc * p) + p + 1)) := Nat.mul_le_mul_left _ h2
        calc 100 * (s + 1) * (p + 1) + 1
            ≤ 100 * ((s + 1) * (Cm (Kc * p) + p + 1)) + ((s + 1) * (Cm (Kc * p) + p + 1)) := by
              omega
          _ = 101 * ((s + 1) * (Cm (Kc * p) + p + 1)) := by ring
      calc Kfold * (100 * (s + 1) * (p + 1) + 1)
          ≤ KS * (101 * ((s + 1) * (Cm (Kc * p) + p + 1))) := Nat.mul_le_mul hKfold h1
        _ = 101 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by ring
    have h2 : 2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
        Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold
        ≤ 205 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by
      have hbr : Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
          Kfold * (100 * (s + 1) * (p + 1) + 1)
          ≤ 102 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
        have := hA
        have := hB'
        calc Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
              Kfold * (100 * (s + 1) * (p + 1) + 1)
            ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) +
              101 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
              exact add_le_add hA hB'
          _ = 102 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by ring
      have hmul : 2 * egM p α *
          (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
            Kfold * (100 * (s + 1) * (p + 1) + 1))
          ≤ 204 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by
        have h2e : 2 * egM p α ≤ 2 * (egM p α + 1) := by omega
        calc 2 * egM p α *
              (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
                Kfold * (100 * (s + 1) * (p + 1) + 1))
            ≤ 2 * (egM p α + 1) * (102 * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) :=
              Nat.mul_le_mul h2e hbr
          _ = 204 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by ring
      have hkf : Kfold ≤ (egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
        have h1 : KS ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) := by
          have := Nat.mul_le_mul_left KS hS1CC1
          rwa [Nat.mul_one] at this
        have h2 : KS * ((s + 1) * (Cm (Kc * p) + p + 1))
            ≤ (egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) :=
          (by simpa using Nat.mul_le_mul_right (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) hM11)
        exact le_trans hKfold (le_trans h1 h2)
      calc 2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
            Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold
          ≤ 204 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) +
            (egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) :=
            add_le_add hmul hkf
        _ = 205 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by ring
    have h3 : Kpost * (s + 1) * (p + 1)
        ≤ (egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
      have h4 : Kpost * (s + 1) * (p + 1) ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) := by
        calc Kpost * (s + 1) * (p + 1) = Kpost * ((s + 1) * (p + 1)) := by ring
          _ ≤ KS * ((s + 1) * (p + 1)) := Nat.mul_le_mul hKpost le_rfl
          _ ≤ KS * ((s + 1) * (Cm (Kc * p) + p + 1)) := Nat.mul_le_mul_left _ hpp
      have h5 : KS * ((s + 1) * (Cm (Kc * p) + p + 1))
          ≤ (egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) := by
        simpa using Nat.mul_le_mul_right (KS * ((s + 1) * (Cm (Kc * p) + p + 1))) hM11
      exact le_trans h4 h5
    have hstep : 2000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) +
        205 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) +
        1 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))))
        ≤ 100000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by
      have h7 : 2000000 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) +
          205 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) +
          1 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1))))
          = 2000206 * ((egM p α + 1) * (KS * ((s + 1) * (Cm (Kc * p) + p + 1)))) := by ring
      rw [h7]
      exact Nat.mul_le_mul_right _ (by norm_num)
    linarith [h1, h2, h3, hstep]
  -- ===== the main assembly =====
  refine KL.conseq (main := main) (p := .seq (buR1SetupProg pickP rollP pushP repP)
      (.seq (foldComb colP) postP))
    (P := fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val),
      (σ = 1 ∨ σ = -1) ∧
      vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
      v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
    (P' := fun vs => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val),
      (σ = 1 ∨ σ = -1) ∧
      vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
      v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc)
    (Q := fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val),
      (σ = 1 ∨ σ = -1) ∧
      vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
      v.length = s ∧ acc.length = s ∧ buInV B v ∧ buInV B2 acc ∧
      out = HvdH.cvecVal (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))) ::
        HvdH.cvecVal (buAddV acc (buSMulV σ
          (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))))) ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest)
    (Q' := fun vs out => ∃ (σ : ℤ) (v acc : List (ℤ × ℤ)) (rest : List HvdH.Val)
      (v' acc' : List (ℤ × ℤ)), (σ = 1 ∨ σ = -1) ∧
      vs = HvdH.Val.int σ :: HvdH.cvecVal v :: HvdH.cvecVal acc ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
      out = HvdH.cvecVal v' :: HvdH.cvecVal acc' ::
        buColsT p α s t :: HvdH.Val.int (s : ℤ) :: HvdH.Val.int (p : ℤ) :: rest ∧
      v' = buRoundL (buWt p α s t) p s (egM p α) v ∧
      acc' = buAddV acc (buSMulV σ v') ∧
      v'.length = s ∧ acc'.length = s ∧
      buInV (B / 2 + 34 * egM p α + 4) v' ∧
      buInV (B2 + B / 2 + 34 * egM p α + 5) acc')
    (C := fun _ => 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) +
      2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
        Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold +
      Kpost * (s + 1) * (p + 1))
    (C' := fun _ => Kc * (egM p α + 1) * (s + 1) * (Cm (Kc * p) + p + 1))
    ?_ (fun vs hvs => hvs) ?_ (fun vs hvs => hcost)
  -- the word: setup, fold, post
  · intro vs hP st0 R hR
    obtain ⟨σ, v, acc, rest, hσ, hvs, hvlen, hacclen, hbv, hbacc⟩ := hP
    have hvsz : ∀ y ∈ v, isz y.1 ≤ p + 5 ∧ isz y.2 ≤ p + 5 := buQW_isz_of_buInV hB hbv
    have haccsz : ∀ y ∈ acc, isz y.1 ≤ p + 5 ∧ isz y.2 ≤ p + 5 := buQW_isz_of_buInV hB2 hbacc
    have hzlen : (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)).length = s :=
      buPFold_length (buWt p α s t) s (egM p α) v hvlen (2 * egM p α)
        (by rw [buColsN_length])
    have hzsz : ∀ y ∈ buPFold (buWt p α s t) s (egM p α) v (2 * egM p α),
        isz y.1 ≤ 2 * p + 8 ∧ isz y.2 ≤ 2 * p + 8 := by
      intro y hy
      obtain ⟨ll, hll, rfl⟩ := List.mem_iff_getElem.mp hy
      have hlls : ll < s := by
        have h := hzlen
        rw [h] at hll
        exact hll
      rw [List.getElem_eq_getD (0, 0)]
      exact buQW_fold_isz p α s t hp hrow B hB v hvlen hbv (2 * egM p α) le_rfl ll hlls
    have hSetupW := buR1SetupW pickP rollP pushP repP Kpick Kroll Kpush Krep KS
      hKpick hKroll hKpush hKrep hKS1 hpick hroll hpush hrep main p α s t hs hα hp σ v acc
      B B2 hB hB2 hvlen hacclen hbv hbacc hσ hrow
    have hFoldW := buR1FoldPhaseB KL IL LL main N Cm p α s t hmono hmb hKN' hs hα hp
      B B2 hB hB2 hrow v acc hvlen hacclen hbv hbacc σ hσ rest
    -- the post phase
    have hPostW : Pipe main postP
        [cvecVal (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)), Val.int σ, cvecVal v,
          cvecVal acc, Val.int (s : ℤ), Val.int (p : ℤ)]
        [cvecVal (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α))),
          cvecVal (buAddV acc (buSMulV σ
            (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)))))]
        (Kpost * (s + 1) * (p + 1)) :=
      hpost p s main hp σ hσ _ v acc hzlen hzsz hvlen hvsz haccsz hacclen
    obtain ⟨w1, st1, n1, hw1, hev1, hn1, hstk1, hoth1⟩ :=
      hSetupW rest vs (by simpa only [List.cons_append, List.nil_append] using hvs) st0 R hR
    obtain ⟨w2, st2, n2, hw2, hev2, hn2, hstk2, hoth2⟩ :=
      hFoldW w1 (by simpa only [List.cons_append, List.nil_append] using hw1) st1 R hstk1
    obtain ⟨w3, st3, n3, hw3, hev3, hn3, hstk3, hoth3⟩ :=
      (hPostW (buColsT p α s t :: Val.int (s : ℤ) :: Val.int (p : ℤ) :: rest)) w2
        (by simpa only [List.cons_append, List.nil_append] using hw2) st2 R hstk2
    refine ⟨w3, st3, n1 + (n2 + n3), ?_, ?_, ?_, hstk3, ?_⟩
    · exact ⟨σ, v, acc, rest, hσ, hvs, hvlen, hacclen, hbv, hbacc,
        by simpa only [List.cons_append, List.nil_append] using hw3⟩
    · exact Eval.seq hev1 (Eval.seq hev2 hev3)
    · show n1 + (n2 + n3) ≤
          2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) +
          2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
            Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold +
          Kpost * (s + 1) * (p + 1)
      have h1 : n1 ≤ 2000000 * KS * ((egM p α + 1) * (s + 1) * (p + 1)) := hn1
      have h2 : n2 ≤ 2 * egM p α * (Kcol * (s + 1) * (Cm (Kcol * p) + p + 1) +
          Kfold * (100 * (s + 1) * (p + 1) + 1)) + Kfold := hn2
      have h3 : n3 ≤ Kpost * (s + 1) * (p + 1) := hn3
      omega
    · intro k hk
      rw [hoth3 k hk, hoth2 k hk, hoth1 k hk]
  -- the output conversion
  · intro vs out hvs hpost
    obtain ⟨σ, v, acc, rest, hσ, hvs', hvlen, hacclen, hbv, hbacc, hout⟩ := hpost
    refine ⟨σ, v, acc, rest,
      buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)),
      buAddV acc (buSMulV σ (buTdivV p (buPFold (buWt p α s t) s (egM p α) v (2 * egM p α)))),
      hσ, hvs', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hout
    · exact (buRoundL_eq_pfold (buWt p α s t) p s (egM p α) v).symm
    · rfl
    · exact (buR1RoundDisc p α s t hs hp B B2 hB hB2 hrow v acc hvlen hacclen hbv hbacc σ hσ).1
    · exact (buR1RoundDisc p α s t hs hp B B2 hB hB2 hrow v acc hvlen hacclen hbv hbacc σ hσ).2.2.1
    · exact (buR1RoundDisc p α s t hs hp B B2 hB hB2 hrow v acc hvlen hacclen hbv hbacc σ hσ).2.1
    · exact (buR1RoundDisc p α s t hs hp B B2 hB hB2 hrow v acc hvlen hacclen hbv hbacc σ hσ).2.2.2

end Work.Resample
