import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.KronP.defs
import Submission.Work.KronP.splitAux
import Submission.Work.KronP.packListWord
import Submission.Work.KronP.mapFstWord
import Submission.Work.KronP.mapSndWord
import Submission.Work.KronP.kronSizes
import Submission.Work.KronP.twoListWord
import Submission.Work.KronP.quadWord
import Submission.Work.KronP.quadRevWord

/-!
# KronP: assembly of `splitPack` (paper Lemma 2.5, `SplitPackSpec`)

`splitPack_of_children` builds the Kronecker split-and-pack word out of the delegated pieces
(`packListWord`, `mapFstWord`, `mapSndWord`, `twoListWord`, `quadWord`, `quadRevWord`, `kronSizes`)
and the words of `KernelLib`/`LayoutLib`, by composing 29 `WordR` steps of cost `CMU * B`
(`B` the cost currency of the caller).  It yields `splitPack` once the pieces are available.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KronP

open HvdH

theorem splitPack_of_children (hK : KernelLib) (hI : IntLib) (hL : LayoutLib)
    (hPack : KernelLib → IntLib → PackSpec) (hFst : KernelLib → MapFstSpec)
    (hSnd : KernelLib → MapSndSpec) (hSizes : SizesSpec) (hTwo : KernelLib → TwoListSpec)
    (hQuad : KernelLib → LayoutLib → QuadSpec)
    (hQuadRev : KernelLib → LayoutLib → QuadRevSpec) :
    ∃ (prog : Cmd) (K : ℕ),
      ∀ (main : Cmd) (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List Val),
      1 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) → InDiscVec p r u → InDiscVec p r v →
      WordR main prog
        (fun vs => vs = Val.int (3 * p : ℤ) :: Val.int (2 * r : ℤ) ::
            Val.int (digitOffset p (2 * r)) ::
            Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            Val.int (p : ℤ) :: Val.int (r : ℤ) ::
            cvecVal u :: cvecVal v :: rest)
        (fun _ out => out = zsVal [kronX0 u p, kronX1 u p, kronX0 u p, kronX1 u p] ::
            zsVal [kronY0 v p, kronY1 v p, kronY1 v p, kronY0 v p] ::
            Val.int (3 * p : ℤ) :: Val.int (2 * r : ℤ) ::
            Val.int (digitOffset p (2 * r)) ::
            Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            Val.int (p : ℤ) :: Val.int (r : ℤ) :: rest)
        (fun _ => K * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
  obtain ⟨dupProg, Kdup, hdup⟩ := hK.dup
  obtain ⟨swapProg, Kswap, hswap⟩ := hK.swap
  obtain ⟨pickProg, Kpick, hpick⟩ := hK.pick
  obtain ⟨rollProg, Kroll, hroll⟩ := hK.roll
  obtain ⟨packProg, Kpack, hpack⟩ := hPack hK hI
  obtain ⟨fstProg, Kfst, hfst⟩ := hFst hK
  obtain ⟨sndProg, Ksnd, hsnd⟩ := hSnd hK
  obtain ⟨twoProg, Ktwo, htwo⟩ := hTwo hK
  obtain ⟨quadProg, Kquad, hquad⟩ := hQuad hK hL
  obtain ⟨quadRevProg, KquadRev, hquadRev⟩ := hQuadRev hK hL
  let CMU : ℕ := (Kdup + Kswap + Kpick + Kroll + Kpack + Kfst + Ksnd + Ktwo + Kquad + KquadRev + 1) * 100000000
  have hCMU : CMU = (Kdup + Kswap + Kpick + Kroll + Kpack + Kfst + Ksnd + Ktwo + Kquad + KquadRev + 1) * 100000000 := rfl
  have hKdup : 100000000 * Kdup ≤ CMU := by rw [hCMU]; omega
  have hKswap : 100000000 * Kswap ≤ CMU := by rw [hCMU]; omega
  have hKpick : 100000000 * Kpick ≤ CMU := by rw [hCMU]; omega
  have hKroll : 100000000 * Kroll ≤ CMU := by rw [hCMU]; omega
  have hKpack : 100000000 * Kpack ≤ CMU := by rw [hCMU]; omega
  have hKfst : 100000000 * Kfst ≤ CMU := by rw [hCMU]; omega
  have hKsnd : 100000000 * Ksnd ≤ CMU := by rw [hCMU]; omega
  have hKtwo : 100000000 * Ktwo ≤ CMU := by rw [hCMU]; omega
  have hKquad : 100000000 * Kquad ≤ CMU := by rw [hCMU]; omega
  have hKquadRev : 100000000 * KquadRev ≤ CMU := by rw [hCMU]; omega
  let P1 : Cmd := rollProg 6
  let P2 : Cmd := Cmd.seq P1 (dupProg)
  let P3 : Cmd := Cmd.seq P2 (fstProg)
  let P4 : Cmd := Cmd.seq P3 (rollProg 1)
  let P5 : Cmd := Cmd.seq P4 (sndProg)
  let P6 : Cmd := Cmd.seq P5 (pickProg 2)
  let P7 : Cmd := Cmd.seq P6 (swapProg)
  let P8 : Cmd := Cmd.seq P7 (packProg)
  let P9 : Cmd := Cmd.seq P8 (rollProg 1)
  let P10 : Cmd := Cmd.seq P9 (pickProg 2)
  let P11 : Cmd := Cmd.seq P10 (swapProg)
  let P12 : Cmd := Cmd.seq P11 (packProg)
  let P13 : Cmd := Cmd.seq P12 (twoProg)
  let P14 : Cmd := Cmd.seq P13 (rollProg 7)
  let P15 : Cmd := Cmd.seq P14 (dupProg)
  let P16 : Cmd := Cmd.seq P15 (fstProg)
  let P17 : Cmd := Cmd.seq P16 (rollProg 1)
  let P18 : Cmd := Cmd.seq P17 (sndProg)
  let P19 : Cmd := Cmd.seq P18 (pickProg 3)
  let P20 : Cmd := Cmd.seq P19 (swapProg)
  let P21 : Cmd := Cmd.seq P20 (packProg)
  let P22 : Cmd := Cmd.seq P21 (rollProg 1)
  let P23 : Cmd := Cmd.seq P22 (pickProg 3)
  let P24 : Cmd := Cmd.seq P23 (swapProg)
  let P25 : Cmd := Cmd.seq P24 (packProg)
  let P26 : Cmd := Cmd.seq P25 (twoProg)
  let P27 : Cmd := Cmd.seq P26 (quadRevProg)
  let P28 : Cmd := Cmd.seq P27 (rollProg 1)
  let P29 : Cmd := Cmd.seq P28 (quadProg)
  refine ⟨P29, 29 * CMU, ?_⟩
  intro main p r u v rest hp hr hrlt hu hv
  have hsizes := hSizes p r u v ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) rfl hp hr hu hv
  obtain ⟨hB1, hszA0, hszB0, hszC0, hszD0, hszP0, hszR0, hszU0m, hszU1m, hszV0m, hszV1m,
    hszX0m, hszX1m, hszY0m, hszY1m, hszL2Um, hszL2Vm, hszL4Um, hszL4Vm⟩ := hsizes
  have hszA : vsz (cA p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cA, Work.ConvR.vsz_int]; exact hszA0
  have hszB : vsz (cB r) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cB, Work.ConvR.vsz_int]; exact hszB0
  have hszC : vsz (cC p r) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cC, Work.ConvR.vsz_int]; exact hszC0
  have hszD : vsz (cD p r) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cD, Work.ConvR.vsz_int]; exact hszD0
  have hszP : vsz (cP p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cP, Work.ConvR.vsz_int]; exact hszP0
  have hszR : vsz (cR r) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    rw [cR, Work.ConvR.vsz_int]; exact hszR0
  have hszU0 : vsz (cU0 u) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cU0]; exact hszU0m
  have hszU1 : vsz (cU1 u) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cU1]; exact hszU1m
  have hszV0 : vsz (cV0 v) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cV0]; exact hszV0m
  have hszV1 : vsz (cV1 v) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cV1]; exact hszV1m
  have hszX0 : vsz (cX0 u p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cX0, Work.ConvR.vsz_int]; exact hszX0m
  have hszX1 : vsz (cX1 u p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cX1, Work.ConvR.vsz_int]; exact hszX1m
  have hszY0 : vsz (cY0 v p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cY0, Work.ConvR.vsz_int]; exact hszY0m
  have hszY1 : vsz (cY1 v p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cY1, Work.ConvR.vsz_int]; exact hszY1m
  have hszL2U : vsz (cL2U u p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cL2U]; exact hszL2Um
  have hszL2V : vsz (cL2V v p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cL2V]; exact hszL2Vm
  have hszL4U : vsz (cL4U u p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cL4U]; exact hszL4Um
  have hszL4V : vsz (cL4V v p) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [cL4V]; exact hszL4Vm
  have hszCU : vsz (cU u) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    have h : vsz (cU u) ≤ ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
      show vsz (cvecVal u) ≤ (r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)
      omega
    calc vsz (cU u) ≤ 1 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [Nat.one_mul]; exact h
      _ ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := Nat.mul_le_mul_right _ (by norm_num)
  have hszCV : vsz (cV v) ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    have h : vsz (cV v) ≤ ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
      show vsz (cvecVal v) ≤ (r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)
      omega
    calc vsz (cV v) ≤ 1 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by rw [Nat.one_mul]; exact h
      _ ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := Nat.mul_le_mul_right _ (by norm_num)
  have hBp2 : (r + 1) * (p + 1) ^ 2 ≤ ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by omega
  have hBp : (r + 1) * (p + 1) ≤ ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
    have h1 : (p + 1) ≤ (p + 1) ^ 2 := by
      have h2 : (p + 1) ^ 2 = (p + 1) * (p + 1) := by ring
      rw [h2]; exact Nat.le_mul_of_pos_right (p + 1) (by omega)
    calc (r + 1) * (p + 1) ≤ (r + 1) * (p + 1) ^ 2 := Nat.mul_le_mul_left _ h1
      _ ≤ ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := hBp2
  have hcfxU : ∀ z ∈ u, vsz (cfxVal z) ≤ Work.ConvR.cfxSz p := fun z hz => Work.ConvR.vsz_cfxVal_le (hu.2 z hz)
  have hcfxV : ∀ z ∈ v, vsz (cfxVal z) ≤ Work.ConvR.cfxSz p := fun z hz => Work.ConvR.vsz_cfxVal_le (hv.2 z hz)
  have h3p : 1 ≤ 3 * p := by omega
  have hbdU0 : ∀ x ∈ u.map Prod.fst, x.natAbs < 2 ^ (3 * (3 * p)) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact pow_lt_9p (Work.ConvR.natAbs_fst_le_of_inDisc (hu.2 z hz)) hp
  have hbdU1 : ∀ x ∈ u.map Prod.snd, x.natAbs < 2 ^ (3 * (3 * p)) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact pow_lt_9p (Work.ConvR.natAbs_snd_le_of_inDisc (hu.2 z hz)) hp
  have hbdV0 : ∀ x ∈ v.map Prod.fst, x.natAbs < 2 ^ (3 * (3 * p)) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact pow_lt_9p (Work.ConvR.natAbs_fst_le_of_inDisc (hv.2 z hz)) hp
  have hbdV1 : ∀ x ∈ v.map Prod.snd, x.natAbs < 2 ^ (3 * (3 * p)) := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact pow_lt_9p (Work.ConvR.natAbs_snd_le_of_inDisc (hv.2 z hz)) hp

  -- step 1 (roll)
  have hstep1 : WC main (rollProg 6) (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest)
      (fun _ out => out = cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 6 (cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest).take (6 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hszA
        · exact hszB
        · exact hszC
        · exact hszD
        · exact hszP
        · exact hszR
        · exact hszCU
      exact take_cost_le (by norm_num : 6 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h1 : WC main P1 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (1 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.monoCost hK hstep1 (by simp)

  -- step 2 (dup)
  have hstep2 : WC main (dupProg) (fun vs => vs = cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepDup hdup hK (cU u) (cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) hKdup hszCU hB1
  have h2 : WC main P2 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (2 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h1 hstep2

  -- step 3 (map)
  have hstep3 : WC main (fstProg) (fun vs => vs = cU u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU0 u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hfst main u (Work.ConvR.cfxSz p) (cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) hcfxU) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKfst hB1 (coordCost_le hu.1 hBp)
  have h3 : WC main P3 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU0 u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (3 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h2 hstep3

  -- step 4 (roll)
  have hstep4 : WC main (rollProg 1) (fun vs => vs = cU0 u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 1 (cU0 u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (cU u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cU0 u :: cU u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest).take (1 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hszU0
        · exact hszCU
      exact take_cost_le (by norm_num : 1 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h4 : WC main P4 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (4 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h3 hstep4

  -- step 5 (map)
  have hstep5 : WC main (sndProg) (fun vs => vs = cU u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hsnd main u (Work.ConvR.cfxSz p) (cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) hcfxU) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKsnd hB1 (coordCost_le hu.1 hBp)
  have h5 : WC main P5 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (5 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h4 hstep5

  -- step 6 (pick)
  have hstep6 : WC main (pickProg 2) (fun vs => vs = cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cA p :: cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepPick hpick hK 2 (cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (cA p :: cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) ?_ ?_ hKpick ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest).take (2 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hszU1
        · exact hszU0
        · exact hszA
      exact take_cost_le (by norm_num : 2 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h6 : WC main P6 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cA p :: cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (6 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h5 hstep6

  -- step 7 (swap)
  have hstep7 : WC main (swapProg) (fun vs => vs = cA p :: cU1 u :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU1 u :: cA p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepSwap hswap hK (cA p) (cU1 u) (cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) hKswap hszA hszU1 hB1
  have h7 : WC main P7 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU1 u :: cA p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (7 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h6 hstep7

  -- step 8 (pack)
  have hstep8 : WC main (packProg) (fun vs => vs = cU1 u :: cA p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cX1 u p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hpack main (u.map Prod.snd) (3 * p) (cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) h3p hbdU1) ?_ ?_ ?_
    · rw [int_cast_A p]; rfl
    · intro out hout; rw [hout]; rfl
    · rw [List.length_map, hu.1]
      exact cost_le hKpack hB1 (packCost_le hszU1 hszA0 hB1 hBp)
  have h8 : WC main P8 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cX1 u p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (8 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h7 hstep8

  -- step 9 (roll)
  have hstep9 : WC main (rollProg 1) (fun vs => vs = cX1 u p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 1 (cX1 u p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cX1 u p :: cU0 u :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest).take (1 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hszX1
        · exact hszU0
      exact take_cost_le (by norm_num : 1 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h9 : WC main P9 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (9 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h8 hstep9

  -- step 10 (pick)
  have hstep10 : WC main (pickProg 2) (fun vs => vs = cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cA p :: cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepPick hpick hK 2 (cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (cA p :: cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) ?_ ?_ hKpick ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest).take (2 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact hszU0
        · exact hszX1
        · exact hszA
      exact take_cost_le (by norm_num : 2 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h10 : WC main P10 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cA p :: cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (10 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h9 hstep10

  -- step 11 (swap)
  have hstep11 : WC main (swapProg) (fun vs => vs = cA p :: cU0 u :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cU0 u :: cA p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepSwap hswap hK (cA p) (cU0 u) (cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) hKswap hszA hszU0 hB1
  have h11 : WC main P11 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cU0 u :: cA p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (11 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h10 hstep11

  -- step 12 (pack)
  have hstep12 : WC main (packProg) (fun vs => vs = cU0 u :: cA p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cX0 u p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hpack main (u.map Prod.fst) (3 * p) (cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) h3p hbdU0) ?_ ?_ ?_
    · rw [int_cast_A p]; rfl
    · intro out hout; rw [hout]; rfl
    · rw [List.length_map, hu.1]
      exact cost_le hKpack hB1 (packCost_le hszU0 hszA0 hB1 hBp)
  have h12 : WC main P12 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cX0 u p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (12 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h11 hstep12

  -- step 13 (two)
  have hstep13 : WC main (twoProg) (fun vs => vs = cX0 u p :: cX1 u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (htwo main (cX0 u p) (cX1 u p) (cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKtwo hB1 (twoCost_le hB1 hszX0 hszX1)
  have h13 : WC main P13 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (13 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h12 hstep13

  -- step 14 (roll)
  have hstep14 : WC main (rollProg 7) (fun vs => vs = cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest)
      (fun _ out => out = cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 7 (cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest) (cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cV v :: rest).take (7 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hszL2U
        · exact hszA
        · exact hszB
        · exact hszC
        · exact hszD
        · exact hszP
        · exact hszR
        · exact hszCV
      exact take_cost_le (by norm_num : 7 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h14 : WC main P14 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (14 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h13 hstep14

  -- step 15 (dup)
  have hstep15 : WC main (dupProg) (fun vs => vs = cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepDup hdup hK (cV v) (cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) hKdup hszCV hB1
  have h15 : WC main P15 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (15 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h14 hstep15

  -- step 16 (map)
  have hstep16 : WC main (fstProg) (fun vs => vs = cV v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV0 v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hfst main v (Work.ConvR.cfxSz p) (cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) hcfxV) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKfst hB1 (coordCost_le hv.1 hBp)
  have h16 : WC main P16 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV0 v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (16 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h15 hstep16

  -- step 17 (roll)
  have hstep17 : WC main (rollProg 1) (fun vs => vs = cV0 v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 1 (cV0 v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (cV v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cV0 v :: cV v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest).take (1 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hszV0
        · exact hszCV
      exact take_cost_le (by norm_num : 1 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h17 : WC main P17 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (17 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h16 hstep17

  -- step 18 (map)
  have hstep18 : WC main (sndProg) (fun vs => vs = cV v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hsnd main v (Work.ConvR.cfxSz p) (cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) hcfxV) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKsnd hB1 (coordCost_le hv.1 hBp)
  have h18 : WC main P18 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (18 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h17 hstep18

  -- step 19 (pick)
  have hstep19 : WC main (pickProg 3) (fun vs => vs = cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cA p :: cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepPick hpick hK 3 (cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (cA p :: cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKpick ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest).take (3 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact hszV1
        · exact hszV0
        · exact hszL2U
        · exact hszA
      exact take_cost_le (by norm_num : 3 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h19 : WC main P19 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cA p :: cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (19 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h18 hstep19

  -- step 20 (swap)
  have hstep20 : WC main (swapProg) (fun vs => vs = cA p :: cV1 v :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV1 v :: cA p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepSwap hswap hK (cA p) (cV1 v) (cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) hKswap hszA hszV1 hB1
  have h20 : WC main P20 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV1 v :: cA p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (20 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h19 hstep20

  -- step 21 (pack)
  have hstep21 : WC main (packProg) (fun vs => vs = cV1 v :: cA p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cY1 v p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hpack main (v.map Prod.snd) (3 * p) (cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) h3p hbdV1) ?_ ?_ ?_
    · rw [int_cast_A p]; rfl
    · intro out hout; rw [hout]; rfl
    · rw [List.length_map, hv.1]
      exact cost_le hKpack hB1 (packCost_le hszV1 hszA0 hB1 hBp)
  have h21 : WC main P21 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cY1 v p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (21 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h20 hstep21

  -- step 22 (roll)
  have hstep22 : WC main (rollProg 1) (fun vs => vs = cY1 v p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 1 (cY1 v p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cY1 v p :: cV0 v :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest).take (1 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hszY1
        · exact hszV0
      exact take_cost_le (by norm_num : 1 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h22 : WC main P22 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (22 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h21 hstep22

  -- step 23 (pick)
  have hstep23 : WC main (pickProg 3) (fun vs => vs = cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cA p :: cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepPick hpick hK 3 (cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (cA p :: cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKpick ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest).take (3 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact hszV0
        · exact hszY1
        · exact hszL2U
        · exact hszA
      exact take_cost_le (by norm_num : 3 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h23 : WC main P23 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cA p :: cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (23 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h22 hstep23

  -- step 24 (swap)
  have hstep24 : WC main (swapProg) (fun vs => vs = cA p :: cV0 v :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cV0 v :: cA p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    exact stepSwap hswap hK (cA p) (cV0 v) (cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) hKswap hszA hszV0 hB1
  have h24 : WC main P24 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cV0 v :: cA p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (24 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h23 hstep24

  -- step 25 (pack)
  have hstep25 : WC main (packProg) (fun vs => vs = cV0 v :: cA p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cY0 v p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hpack main (v.map Prod.fst) (3 * p) (cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) h3p hbdV0) ?_ ?_ ?_
    · rw [int_cast_A p]; rfl
    · intro out hout; rw [hout]; rfl
    · rw [List.length_map, hv.1]
      exact cost_le hKpack hB1 (packCost_le hszV0 hszA0 hB1 hBp)
  have h25 : WC main P25 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cY0 v p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (25 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h24 hstep25

  -- step 26 (two)
  have hstep26 : WC main (twoProg) (fun vs => vs = cY0 v p :: cY1 v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cL2V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (htwo main (cY0 v p) (cY1 v p) (cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKtwo hB1 (twoCost_le hB1 hszY0 hszY1)
  have h26 : WC main P26 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cL2V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (26 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h25 hstep26

  -- step 27 (quadrev)
  have hstep27 : WC main (quadRevProg) (fun vs => vs = cL2V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cL4V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hquadRev main ([cY0 v p, cY1 v p]) (cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil]
      rfl
    · exact cost_le hKquadRev hB1 (quadCost_le hB1 hszL2V)
  have h27 : WC main P27 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cL4V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (27 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h26 hstep27

  -- step 28 (roll)
  have hstep28 : WC main (rollProg 1) (fun vs => vs = cL4V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cL2U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine stepRoll hroll hK 1 (cL4V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (cL2U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) ?_ ?_ hKroll ?_ hB1
    · simp only [List.length_cons]; omega
    · rfl
    · have hmem : ∀ w ∈ (cL4V v p :: cL2U u p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest).take (1 + 1), vsz w ≤ 1000 * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)) := by
        intro w hw
        simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hszL4V
        · exact hszL2U
      exact take_cost_le (by norm_num : 1 ≤ 8) (by simp only [List.length_cons]; omega) hB1 hmem
  have h28 : WC main P28 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cL2U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (28 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h27 hstep28

  -- step 29 (quad)
  have hstep29 : WC main (quadProg) (fun vs => vs = cL2U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)
      (fun _ out => out = cL4U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v))) := by
    refine WC.ofState hK (hquad main ([cX0 u p, cX1 u p]) (cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest)) ?_ ?_ ?_
    · rfl
    · intro out hout; rw [hout]; rfl
    · exact cost_le hKquad hB1 (quadCost_le hB1 hszL2U)
  have h29 : WC main P29 (fun vs => vs = cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: cU u :: cV v :: rest) (fun _ out => out = cL4U u p :: cL4V v p :: cA p :: cB r :: cC p r :: cD p r :: cP p :: cR r :: rest) (29 * (CMU * ((r + 1) * (p + 1) ^ 2 + vsz (cvecVal u) + vsz (cvecVal v)))) :=
    WC.add hK h28 hstep29

  refine WC.monoCost hK h29 (le_of_eq ?_)
  ring


/-- **The requested lemma**: the Kronecker split-and-pack word (paper Lemma 2.5). -/
theorem splitPack (hK : HvdH.KernelLib) (hI : HvdH.IntLib) (hL : HvdH.LayoutLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ),
      ∀ (main : HvdH.Cmd) (p r : ℕ) (u v : List (ℤ × ℤ)) (rest : List HvdH.Val),
      1 ≤ p → 2 ≤ r → r < 2 ^ (p - 1) → HvdH.InDiscVec p r u → HvdH.InDiscVec p r v →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.Val.int (3 * p : ℤ) :: HvdH.Val.int (2 * r : ℤ) ::
            HvdH.Val.int (Work.KronP.digitOffset p (2 * r)) ::
            HvdH.Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) ::
            HvdH.cvecVal u :: HvdH.cvecVal v :: rest)
        (fun _ out => out = Work.KronP.zsVal [Work.KronP.kronX0 u p, Work.KronP.kronX1 u p,
              Work.KronP.kronX0 u p, Work.KronP.kronX1 u p] ::
            Work.KronP.zsVal [Work.KronP.kronY0 v p, Work.KronP.kronY1 v p,
              Work.KronP.kronY1 v p, Work.KronP.kronY0 v p] ::
            HvdH.Val.int (3 * p : ℤ) :: HvdH.Val.int (2 * r : ℤ) ::
            HvdH.Val.int (Work.KronP.digitOffset p (2 * r)) ::
            HvdH.Val.int ((2 : ℤ) ^ (p + Nat.clog 2 r)) ::
            HvdH.Val.int (p : ℤ) :: HvdH.Val.int (r : ℤ) :: rest)
        (fun _ => K * ((r + 1) * (p + 1) ^ 2 + HvdH.vsz (HvdH.cvecVal u) +
          HvdH.vsz (HvdH.cvecVal v))) :=
  splitPack_of_children hK hI hL packListWord mapFstWord mapSndWord
    kronSizes twoListWord quadWord quadRevWord

end Work.KronP
