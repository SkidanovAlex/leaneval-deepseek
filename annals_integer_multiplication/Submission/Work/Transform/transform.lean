import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic
import Submission.Work.Transform.paramFacts
import Submission.Work.Transform.bluestein
import Submission.Work.Transform.eps_mul
import Submission.Work.Transform.arrangeWord
import Submission.Work.Transform.mulWord
import Submission.Work.Transform.ztabWord
import Submission.Work.Transform.rarrInj
import Submission.Work.Transform.chirpWordB2
import Submission.Work.Transform.paramWord
import Submission.Work.Transform.chirp_norm
import Submission.Work.Transform.phiArrL_norm
import Submission.Work.Transform.convR_norm
import Submission.Work.Transform.convR_sub
import Submission.Work.Transform.convC_norm
import Submission.Work.Transform.psiFlatL_norm
import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic
import Submission.Work.Transform.paramFacts
import Submission.Work.Transform.bluestein
import Submission.Work.Transform.eps_mul
import Submission.Work.Transform.arrangeWord
import Submission.Work.Transform.chirp_norm
import Submission.Work.Transform.phiArrL_norm
import Submission.Work.Transform.convR_norm
import Submission.Work.Transform.convR_sub
import Submission.Work.Transform.convC_norm
import Submission.Work.Transform.psiFlatL_norm
import Submission.Work.Transform.psiFlatL_phiArrL
import Submission.Work.Transform.SeqUtil
import Submission.Work.Transform.costKit
import Submission.Work.Transform.costAbsorb
import Submission.Work.Transform.costShapes
import Submission.Work.Transform.transformCost
import Submission.Work.Transform.convC_bridge
import Submission.Work.Transform.finalApprox
import Submission.Work.Transform.phiWordV2
import Submission.Work.Transform.psiWordV2
import Submission.Work.Transform.shift3Word
import Submission.Work.Transform.arrangeWord
import Submission.Work.Transform.inDiscVecSizes
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace Work.Transform
open HvdH

/-- Paper Thm 3.1 (with Proposition 3.5 and Bluestein): power-of-two complex transforms. -/
theorem transform : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.ConvRProp →
    HvdH.TransformProp := by
  intro hKL hIL hLL hFx hCR
  obtain ⟨paramP, Kp, hParam⟩ := paramWord hKL hIL
  obtain ⟨ztabP, Kz, hZtab⟩ := ztabWord hKL hIL hLL hFx
  obtain ⟨chirpP, Kc, hChirp⟩ := chirpWordB2 hKL hIL hLL hFx
  obtain ⟨arrP, Ka, hArr⟩ := arrangeWord hKL
  obtain ⟨mulP, Km, hMul⟩ := mulWord hKL hIL hFx
  obtain ⟨phiP, Kph, hPhi⟩ := phiWordV2 hKL hIL hLL hFx
  obtain ⟨psiP, Kps, hPsi⟩ := psiWordV2 hKL hIL hLL hFx
  obtain ⟨rollP, Kr, hRoll⟩ := hKL.roll
  obtain ⟨shiftP, Ks, hShift⟩ := shift3Word hKL
  obtain ⟨convP, KR, hConv⟩ := hCR
  refine ⟨seqAll [paramP, ztabP, (rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP],
    2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100), ?_⟩
  intro main N Cm hmon hMB p ts hpar hN
  obtain ⟨hlenD, hpow2, hpair, hTlt, hp100⟩ := hpar
  let r : ℕ := HvdH.lmax ts
  let ts' : List ℕ := ts.dropLast
  let T : ℕ := ts.prod
  let M : ℕ := ts'.prod
  obtain ⟨hsplit, hTMr, hM2, hrpos, hr2, hr_lt, hsyn⟩ := paramFacts p ts hlenD hpow2 hpair hTlt hp100
  have hsplit' : ts = ts' ++ [r] := hsplit
  have hTMr' : T = M * r := hTMr
  have hsyn' : HvdH.SynParams p r ts' := hsyn
  have hts_ne : ts ≠ [] := by intro hh; rw [hh] at hlenD; simp [HvdH.D] at hlenD
  have hts_pos : ∀ t ∈ ts, 0 < t := by
    intro t ht; obtain ⟨k, hk, rfl⟩ := hpow2 t ht; exact pow_pos (by norm_num) k
  have hMpos : 0 < M := by
    have h2 : 2 ≤ M := hM2
    omega
  have hdiv : T / r = M := by
    rw [hTMr', Nat.mul_comm M r]
    exact Nat.mul_div_cancel_left M hrpos
  intro vs hPre s Rg hstk
  obtain ⟨zs, R, hvs, hdisc⟩ := hPre
  subst hvs
  have hzlen : zs.length = T := hdisc.1
  -- ---- 1. parameters
  obtain ⟨vs1, s1, n1, hpost1, hev1, hcost1, hstk1, hfr1⟩ :=
    (hParam main p ts zs R hts_ne hts_pos) (HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zs :: R) rfl s Rg hstk
  -- ---- 2. zeta tables
  obtain ⟨vs2, s2, n2, hpost2, hev2, hcost2, hstk2, hfr2⟩ :=
    (hZtab main p r ts' ts zs R hp100 hr2 hr_lt hzlen hts_pos rfl) vs1 hpost1 s1 Rg hstk1
  obtain ⟨zst, zstie, hzout, hzlen1, hzlen2, hzD1, hzD2, hzE1, hzE2⟩ := hpost2
  -- ---- 3. roll 5
  obtain ⟨vs3, s3, n3, hpost3, hev3, hcost3, hstk3, hfr3⟩ :=
    (hRoll main 5) vs2 (by rw [hzout]; simp) s2 Rg hstk2
  have hs3 : vs3 = HvdH.intList ts :: HvdH.cvecVal zst :: HvdH.cvecVal zstie :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R := by rw [hpost3, hzout]; simp
  -- ---- 4. roll 3
  obtain ⟨vs4, s4, n4, hpost4, hev4, hcost4, hstk4, hfr4⟩ :=
    (hRoll main 3) vs3 (by rw [hs3]; simp) s3 Rg hstk3
  have hs4 : vs4 = HvdH.Val.int p :: HvdH.intList ts :: HvdH.cvecVal zst :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R := by rw [hpost4, hs3]; simp
  -- ---- 5. chirp
  obtain ⟨vs5, s5, n5, hpost5, hev5, hcost5, hstk5, hfr5⟩ :=
    (hChirp main p ts (HvdH.cvecVal zst :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R) hp100 hpow2 hlenD hTlt)
      vs4 hs4 s4 Rg hstk4
  obtain ⟨a, ab, hcaout, hcalen, hcablen, hcaD, habD, hcaE, habE⟩ := hpost5
  -- ---- 6. shift the parameter p past the zeta tables
  obtain ⟨vs6, s6, n6, hpost6, hev6, hcost6, hstk6, hfr6⟩ :=
    (hShift main (HvdH.cvecVal a) (HvdH.cvecVal ab) (HvdH.Val.int p) (HvdH.cvecVal zst)
      (HvdH.cvecVal zstie) (HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R))
      vs5 hcaout s5 Rg hstk5
  have hs6 : vs6 = HvdH.cvecVal a :: HvdH.cvecVal ab :: HvdH.cvecVal zst :: HvdH.cvecVal zstie :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R := hpost6
  -- ---- 7. arrange
  obtain ⟨vs7, s7, n7, hpost7, hev7, hcost7, hstk7, hfr7⟩ :=
    (hArr main p r ts' zs zst zstie a ab R) vs6 hs6 s6 Rg hstk6
  have hs7 : vs7 = HvdH.Val.int p :: HvdH.cvecVal ab :: HvdH.cvecVal zs :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R := hpost7
  -- ---- 8. b = ab * zs
  obtain ⟨vs8, s8, n8, hpost8, hev8, hcost8, hstk8, hfr8⟩ :=
    (hMul main p T ab zs (HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.Val.int p ::
      HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R)
      hcablen hzlen habD hdisc hp100) vs7 hs7 s7 Rg hstk7
  obtain ⟨b, hbout, hblen, hbD, hbE⟩ := hpost8
  have hbMr : b.length = M * r := hblen.trans hTMr
  have hzstMr : zst.length = M * r := hzlen1.trans (hzlen.trans hTMr)
  have hzsMr : zs.length = M * r := hzlen.trans hTMr
  have hbD2 : HvdH.InDiscVec p (M * r) b := by
    have h : HvdH.InDiscVec p T b := hbD
    convert h using 1
    exact hTMr'.symm
  have hzstD2 : HvdH.InDiscVec p (M * r) zst := hzsMr ▸ hzD1
  have hzstieD2 : HvdH.InDiscVec p (M * r) zstie := hzsMr ▸ hzD2
  -- ---- 9. Phi(b)
  obtain ⟨vs9, s9, n9, hpost9, hev9, hcost9, hstk9, hfr9⟩ :=
    (hPhi main p r M b zst (HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab ::
      HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R) hbMr hzstMr hbD2 hzstD2 hp100 hr2) vs8 hbout s8 Rg hstk8
  obtain ⟨ub, hubout, hublen, hubD, hubrow, hubE⟩ := hpost9
  -- ---- 10. roll 4
  obtain ⟨vs10, s10, n10, hpost10, hev10, hcost10, hstk10, hfr10⟩ :=
    (hRoll main 4) vs9 (by rw [hubout]; simp) s9 Rg hstk9
  have hs10 : vs10 = HvdH.Val.int p :: HvdH.rarrVal ub :: HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R := by rw [hpost10, hubout]; simp
  -- ---- 11. roll 4
  obtain ⟨vs11, s11, n11, hpost11, hev11, hcost11, hstk11, hfr11⟩ :=
    (hRoll main 4) vs10 (by rw [hs10]; simp) s10 Rg hstk10
  have hs11 : vs11 = HvdH.Val.int r :: HvdH.Val.int p :: HvdH.rarrVal ub :: HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R := by rw [hpost11, hs10]; simp
  -- ---- 12. roll 4
  obtain ⟨vs12, s12, n12, hpost12, hev12, hcost12, hstk12, hfr12⟩ :=
    (hRoll main 4) vs11 (by rw [hs11]; simp) s11 Rg hstk11
  have hs12 : vs12 = HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.rarrVal ub :: HvdH.cvecVal a :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R := by rw [hpost12, hs11]; simp
  -- ---- 13. roll 4
  obtain ⟨vs13, s13, n13, hpost13, hev13, hcost13, hstk13, hfr13⟩ :=
    (hRoll main 4) vs12 (by rw [hs12]; simp) s12 Rg hstk12
  have hs13 : vs13 = HvdH.cvecVal a :: HvdH.cvecVal zst :: HvdH.Val.int r :: HvdH.Val.int p :: HvdH.rarrVal ub :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R := by rw [hpost13, hs12]; simp
  have haMr : a.length = M * r := hcalen.trans hTMr
  have haD2 : HvdH.InDiscVec p (M * r) a := by
    have h : HvdH.InDiscVec p T a := hcaD
    convert h using 1
    exact hTMr'.symm
  -- ---- 14. Phi(a)
  obtain ⟨vs14, s14, n14, hpost14, hev14, hcost14, hstk14, hfr14⟩ :=
    (hPhi main p r M a zst (HvdH.rarrVal ub :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R)
      haMr hzstMr haD2 hzstD2 hp100 hr2) vs13 hs13 s13 Rg hstk13
  obtain ⟨ua, huaout, hualen, huaD, huarow, huaE⟩ := hpost14
  -- ---- 15. roll 8
  obtain ⟨vs15, s15, n15, hpost15, hev15, hcost15, hstk15, hfr15⟩ :=
    (hRoll main 8) vs14 (by rw [huaout]; simp) s14 Rg hstk14
  have hs15 : vs15 = HvdH.intList ts' :: HvdH.rarrVal ua :: HvdH.rarrVal ub :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: R := by rw [hpost15, huaout]; simp
  -- ---- 16. roll 8
  obtain ⟨vs16, s16, n16, hpost16, hev16, hcost16, hstk16, hfr16⟩ :=
    (hRoll main 8) vs15 (by rw [hs15]; simp) s15 Rg hstk15
  have hs16 : vs16 = HvdH.Val.int r :: HvdH.intList ts' :: HvdH.rarrVal ua :: HvdH.rarrVal ub :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: R := by rw [hpost16, hs15]; simp
  -- ---- 17. roll 8
  obtain ⟨vs17, s17, n17, hpost17, hev17, hcost17, hstk17, hfr17⟩ :=
    (hRoll main 8) vs16 (by rw [hs16]; simp) s16 Rg hstk16
  have hs17 : vs17 = HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: HvdH.rarrVal ua :: HvdH.rarrVal ub :: HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: R := by rw [hpost17, hs16]; simp
  -- ---- 18. ConvR
  obtain ⟨vs18, s18, n18, hpost18, hev18, hcost18, hstk18, hfr18⟩ :=
    (hConv main N Cm hmon hMB p r ts' hsyn' (by simpa only [r] using hN)) vs17
      ⟨ua, ub, HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: R,
        hs17, huaD, hubD⟩ s17 Rg hstk17
  obtain ⟨us0, ws0, rest0, w, hvs18, hpost18a, hpost18b⟩ := hpost18
  have hrest0 : rest0 = HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: R := by
    have h2 := congrArg (List.drop 5) hvs18
    simpa [hs17] using h2.symm
  obtain ⟨hwInDisc, hwApprox⟩ := hpost18b
  have hwlen : w.length = M := hwInDisc.1
  have hwrow : ∀ a < M, (w.getD a []).length = r := by
    intro a ha
    have ha' : a < w.length := by rw [hwlen]; exact ha
    have hmem : w.getD a [] ∈ w := by
      rw [List.getD_eq_getElem _ _ ha']; exact List.getElem_mem ha'
    exact (hwInDisc.2 _ hmem).1
  have hvs18' : (HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' ::
        HvdH.rarrVal us0 :: HvdH.rarrVal ws0 :: rest0) =
      HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' ::
        HvdH.rarrVal ua :: HvdH.rarrVal ub ::
        (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: R) := by
    rw [← hvs18, hs17]
  have hs18c : (HvdH.rarrVal us0 :: HvdH.rarrVal ws0 :: rest0) =
      HvdH.rarrVal ua :: HvdH.rarrVal ub ::
        (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: R) :=
    (List.cons.inj (List.cons.inj (List.cons.inj hvs18').2).2).2
  have hus0 : us0 = ua := rarrVal_inj_aux (List.cons.inj hs18c).1
  have hws0 : ws0 = ub := rarrVal_inj_aux (List.cons.inj (List.cons.inj hs18c).2).1
  have hwApprox' : HvdH.ApproxR p w (HvdH.convR r ts' (HvdH.fxArr p ts'.prod r ua)
      (HvdH.fxArr p ts'.prod r ub))
      ((3 * (M * r) * Nat.log 2 (M * r) + 2 * (M * r) + 3 : ℕ) : ℝ) := by
    rw [hus0, hws0] at hwApprox
    exact ⟨hwInDisc, hwApprox⟩
  -- ---- 19. psi
  obtain ⟨vs19, s19, n19, hpost19, hev19, hcost19, hstk19, hfr19⟩ :=
    (hPsi main p r M w zstie (HvdH.cvecVal ab :: R)
      hwlen hwrow (hzlen2.trans (hzlen.trans hTMr)) hwInDisc
      hzstieD2 hp100 hr2) vs18
      (by rw [hpost18a, hrest0]) s18 Rg hstk18
  obtain ⟨c, hcout, hclen, hcD, hcE⟩ := hpost19
  -- ---- 20. z = c * ab
  obtain ⟨vs20, s20, n20, hpost20, hev20, hcost20, hstk20, hfr20⟩ :=
    (hMul main p T c ab R (by rw [hclen]; exact hTMr'.symm) (by rw [hcablen])
      (by rw [hTMr']; exact hcD) habD hp100)
      vs19 hcout s19 Rg hstk19
  obtain ⟨z, hzout20, hzlen', hzD, hzE⟩ := hpost20
  have e20 : Eval main (seqAll [mulP]) s19 s20 (csum [n20]) :=
    seqAll_cons main mulP [] s19 s20 s20 n20 [] hev20 (seqAll_nil main s20)
  have e19 : Eval main (seqAll [psiP, mulP]) s18 s20 (csum [n19, n20]) :=
    seqAll_cons main psiP [mulP] s18 s19 s20 n19 [n20] hev19 e20
  have e18 : Eval main (seqAll [convP, psiP, mulP]) s17 s20 (csum [n18, n19, n20]) :=
    seqAll_cons main convP [psiP, mulP] s17 s18 s20 n18 [n19, n20] hev18 e19
  have e17 : Eval main (seqAll [(rollP 8), convP, psiP, mulP]) s16 s20 (csum [n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 8) [convP, psiP, mulP] s16 s17 s20 n17 [n18, n19, n20] hev17 e18
  have e16 : Eval main (seqAll [(rollP 8), (rollP 8), convP, psiP, mulP]) s15 s20 (csum [n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 8) [(rollP 8), convP, psiP, mulP] s15 s16 s20 n16 [n17, n18, n19, n20] hev16 e17
  have e15 : Eval main (seqAll [(rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s14 s20 (csum [n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 8) [(rollP 8), (rollP 8), convP, psiP, mulP] s14 s15 s20 n15 [n16, n17, n18, n19, n20] hev15 e16
  have e14 : Eval main (seqAll [phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s13 s20 (csum [n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main phiP [(rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s13 s14 s20 n14 [n15, n16, n17, n18, n19, n20] hev14 e15
  have e13 : Eval main (seqAll [(rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s12 s20 (csum [n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 4) [phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s12 s13 s20 n13 [n14, n15, n16, n17, n18, n19, n20] hev13 e14
  have e12 : Eval main (seqAll [(rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s11 s20 (csum [n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 4) [(rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s11 s12 s20 n12 [n13, n14, n15, n16, n17, n18, n19, n20] hev12 e13
  have e11 : Eval main (seqAll [(rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s10 s20 (csum [n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 4) [(rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s10 s11 s20 n11 [n12, n13, n14, n15, n16, n17, n18, n19, n20] hev11 e12
  have e10 : Eval main (seqAll [(rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s9 s20 (csum [n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 4) [(rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s9 s10 s20 n10 [n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev10 e11
  have e9 : Eval main (seqAll [phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s8 s20 (csum [n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main phiP [(rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s8 s9 s20 n9 [n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev9 e10
  have e8 : Eval main (seqAll [mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s7 s20 (csum [n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main mulP [phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s7 s8 s20 n8 [n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev8 e9
  have e7 : Eval main (seqAll [arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s6 s20 (csum [n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main arrP [mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s6 s7 s20 n7 [n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev7 e8
  have e6 : Eval main (seqAll [shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s5 s20 (csum [n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main shiftP [arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s5 s6 s20 n6 [n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev6 e7
  have e5 : Eval main (seqAll [chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s4 s20 (csum [n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main chirpP [shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s4 s5 s20 n5 [n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev5 e6
  have e4 : Eval main (seqAll [(rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s3 s20 (csum [n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 3) [chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s3 s4 s20 n4 [n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev4 e5
  have e3 : Eval main (seqAll [(rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s2 s20 (csum [n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main (rollP 5) [(rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s2 s3 s20 n3 [n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev3 e4
  have e2 : Eval main (seqAll [ztabP, (rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s1 s20 (csum [n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main ztabP [(rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s1 s2 s20 n2 [n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev2 e3
  have e1 : Eval main (seqAll [paramP, ztabP, (rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP]) s s20 (csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]) :=
    seqAll_cons main paramP [ztabP, (rollP 5), (rollP 3), chirpP, shiftP, arrP, mulP, phiP, (rollP 4), (rollP 4), (rollP 4), (rollP 4), phiP, (rollP 8), (rollP 8), (rollP 8), convP, psiP, mulP] s s1 s20 n1 [n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] hev1 e2
  have hfrall : ∀ k : Stk, k ≠ 0 → s20.stk k = s.stk k := by
    intro k hk
    rw [hfr20 k hk, hfr19 k hk, hfr18 k hk, hfr17 k hk, hfr16 k hk, hfr15 k hk, hfr14 k hk,
      hfr13 k hk, hfr12 k hk, hfr11 k hk, hfr10 k hk, hfr9 k hk, hfr8 k hk, hfr7 k hk,
      hfr6 k hk, hfr5 k hk, hfr4 k hk, hfr3 k hk, hfr2 k hk, hfr1 k hk]
  have hT4' : 4 ≤ T := by
    rw [hTMr']
    calc (4 : ℕ) = 2 * 2 := by norm_num
      _ ≤ M * r := Nat.mul_le_mul hM2 hr2
  have heven : ∀ t ∈ ts, Even t := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := hpow2 t ht
    exact even_iff_two_dvd.mpr ⟨2 ^ (k - 1), by rw [← pow_succ']; congr 1; omega⟩
  have happrox : Approx p z (HvdH.dftMulti ts (-1) (HvdH.fxVec p ts.prod zs))
      ((8 * ts.prod * Nat.log 2 ts.prod : ℕ) : ℝ) :=
    finalApprox p r M T ts ts' zs zst zstie a ab b c z w ua ub
      hsplit' hTMr'
      (D_le_log_two_prod ts hlenD (fun t ht => two_le_of_isPow2 (hpow2 t ht)))
      (le_trans (by norm_num : 3 ≤ 4) hT4')
      hts_pos heven hzlen hp100
      (hzlen ▸ hzD1) (hzlen ▸ hzD2) (hzlen ▸ hzE1) (hzlen ▸ hzE2)
      hcaD habD hcaE habE hbD hbE hubD hubrow hubE huaD huarow huaE hwlen hwrow hwInDisc
      (rfl : ts.prod = T) (rfl : ts'.prod = M) hwApprox'
      (by rw [hTMr']; exact hcD) (by rw [hTMr']; exact hcE) hzD hzE
  have hcost : csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20] ≤
      4 * (ts.prod / HvdH.lmax ts) * Cm (3 * HvdH.lmax ts * p) + 2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100) * ts.prod * p ^ 2 +
        2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100) * ts.sum * (p + 1) ^ (2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100)) := by
    clear hKL hIL hLL hFx hParam hZtab hChirp hArr hMul hPhi hPsi hRoll hShift hConv hMB
    let KB : ℕ := 2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100)
    have hKB : KB = 2 ^ (Kp + Kz + Kc + Ks + Ka + Km + Kph + Kps + Kr + KR + 100) := rfl
    let S : ℕ := T * p ^ 2 + ts.sum * (p + 1) ^ KB
    let VB : ℕ := 100 * T * p ^ 2
    have hSdef : S = T * p ^ 2 + ts.sum * (p + 1) ^ KB := rfl
    have hVBdef : VB = 100 * T * p ^ 2 := rfl
    have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (lt_of_lt_of_le (by norm_num) hp100)
    have h2p : 2 ≤ p := le_trans (by norm_num : 2 ≤ 100) hp100
    have hT4 : 4 ≤ T := by
      rw [hTMr']
      calc (4 : ℕ) = 2 * 2 := by norm_num
        _ ≤ M * r := Nat.mul_le_mul hM2 hr2
    have hT1 : 1 ≤ T := le_trans (by norm_num : 1 ≤ 4) hT4
    have h2T : 2 ≤ T := le_trans (by norm_num : 2 ≤ 4) hT4
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : 0 < 1) hT1
    have hTne : T ≠ 0 := ne_of_gt hTpos
    have hrT : r ≤ T := by
      rw [hTMr']
      calc r = 1 * r := (one_mul r).symm
        _ ≤ M * r := Nat.mul_le_mul_right r (le_trans (by norm_num : 1 ≤ 2) hM2)
    have hlog : HvdH.D ≤ Nat.log 2 T :=
      D_le_log_two_prod ts hlenD (fun t ht => two_le_of_isPow2 (hpow2 t ht))
    have hpowDT : 2 ^ HvdH.D ≤ T := (Nat.le_log_iff_pow_le (by norm_num) hTne).mp hlog
    have hDT : HvdH.D ≤ T := le_trans (le_of_lt Nat.lt_two_pow_self) hpowDT
    have hTpS : T * p ^ 2 ≤ S := by rw [hSdef]; exact Nat.le_add_right _ _
    have hsumS : ts.sum * (p + 1) ^ KB ≤ S := by rw [hSdef]; exact Nat.le_add_left _ _
    have hS1 : 1 ≤ S := by
      rw [hSdef]
      refine le_trans ?_ (Nat.le_add_right _ _)
      calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
        _ ≤ T * p ^ 2 := Nat.mul_le_mul hT1 hp2
    have hVBS : VB ≤ 100 * S := by
      rw [hVBdef, hSdef]
      calc 100 * T * p ^ 2 = 100 * (T * p ^ 2) := by ring
        _ ≤ 100 * (T * p ^ 2 + ts.sum * (p + 1) ^ KB) :=
            Nat.mul_le_mul_left 100 (Nat.le_add_right _ _)
    have hSle : S ≤ 3000000 * S := by
      calc S = 1 * S := (one_mul S).symm
        _ ≤ 3000000 * S := Nat.mul_le_mul_right S (by norm_num)
    have hpTp : p ≤ T * p ^ 2 := by
      have h1 : p ≤ p * p := by
        calc p = p * 1 := (mul_one p).symm
          _ ≤ p * p := Nat.mul_le_mul_left p (le_trans (by norm_num : 1 ≤ 100) hp100)
      have h2 : p * p ≤ T * (p * p) := by
        calc p * p = 1 * (p * p) := (one_mul _).symm
          _ ≤ T * (p * p) := Nat.mul_le_mul_right (p * p) hT1
      have h3 : T * (p * p) = T * p ^ 2 := by ring
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    have hrTp : r ≤ T * p ^ 2 :=
      le_trans hrT (by
        calc T = T * 1 := (mul_one T).symm
          _ ≤ T * p ^ 2 := Nat.mul_le_mul_left T hp2)
    have hpS : p ≤ S := le_trans hpTp hTpS
    have hrS : r ≤ S := le_trans hrTp hTpS
    have hMr1 : 1 ≤ M * r := by rw [← hTMr']; exact hT1
    have hzs1 : 1 ≤ zs.length := by rw [hzlen]; exact hT1
    have hMrS : (M * r) * p ^ 2 ≤ S := by rw [← hTMr']; exact hTpS
    have hrsum : r ≤ ts.sum := List.le_sum_of_mem (lmax_mem hts_ne hpair)
    have hpTp' : p + 2 ≤ T * p := by
      calc p + 2 ≤ p + p := Nat.add_le_add_left h2p p
        _ = 2 * p := by ring
        _ ≤ T * p := Nat.mul_le_mul_right p h2T
    have hrTp' : r + 2 ≤ T * p := by
      calc r + 2 ≤ T + T := Nat.add_le_add hrT h2T
        _ = 2 * T := by ring
        _ = T * 2 := by ring
        _ ≤ T * p := Nat.mul_le_mul_left T h2p
    have hszT : ∀ t ∈ ts, t < 2 ^ p :=
      fun t ht => lt_of_le_of_lt (Nat.le_of_dvd hTpos (List.dvd_prod ht)) hTlt
    have hszT' : ∀ t ∈ ts', t < 2 ^ p := fun t ht => hszT t (List.dropLast_subset ts ht)
    -- the constants are bounded by KB
    have hKpKB : Kp ≤ KB := by
      rw [hKB]
      exact le_trans (le_exp_1 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_of_lt Nat.lt_two_pow_self)
    have hKzKB : Kz ≤ KB := by
      rw [hKB]
      exact le_trans (le_exp_2 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_of_lt Nat.lt_two_pow_self)
    have hKcKB : Kc ≤ KB := by
      rw [hKB]
      exact le_trans (le_exp_3 Kp Kz Kc Ks Ka Km Kph Kps Kr KR) (le_of_lt Nat.lt_two_pow_self)
    have hpwP : (p + 1) ^ Kp ≤ (p + 1) ^ KB := pow_succ_base hKpKB
    have hpwZ : (p + 1) ^ Kz ≤ (p + 1) ^ KB := pow_succ_base hKzKB
    have hpwC : (p + 1) ^ Kc ≤ (p + 1) ^ KB := pow_succ_base hKcKB
    -- per-value size bounds
    have hZs : vsz (HvdH.cvecVal zs) ≤ VB := by
      rw [hVBdef]; exact cvecVal_vsz_le_100 hdisc hp100 hT1
    have hZst : vsz (HvdH.cvecVal zst) ≤ VB := by
      have h := cvecVal_vsz_le_100 hzD1 hp100 hzs1
      rw [hzlen] at h
      rwa [hVBdef]
    have hZstie : vsz (HvdH.cvecVal zstie) ≤ VB := by
      have h := cvecVal_vsz_le_100 hzD2 hp100 hzs1
      rw [hzlen] at h
      rwa [hVBdef]
    have hAa : vsz (HvdH.cvecVal a) ≤ VB := by
      rw [hVBdef]; exact cvecVal_vsz_le_100 hcaD hp100 hT1
    have hAbb : vsz (HvdH.cvecVal ab) ≤ VB := by
      rw [hVBdef]; exact cvecVal_vsz_le_100 habD hp100 hT1
    have hBb : vsz (HvdH.cvecVal b) ≤ VB := by
      rw [hVBdef]; exact cvecVal_vsz_le_100 hbD hp100 hT1
    have hCc : vsz (HvdH.cvecVal c) ≤ VB := by
      rw [hVBdef, hTMr']; exact cvecVal_vsz_le_100 hcD hp100 hMr1
    have hZz : vsz (HvdH.cvecVal z) ≤ VB := by
      rw [hVBdef]; exact cvecVal_vsz_le_100 hzD hp100 hT1
    have hUa : vsz (HvdH.rarrVal ua) ≤ VB := by
      rw [hVBdef, hTMr']; exact rarrVal_vsz_le_100 huaD hp100 hMr1
    have hUb : vsz (HvdH.rarrVal ub) ≤ VB := by
      rw [hVBdef, hTMr']; exact rarrVal_vsz_le_100 hubD hp100 hMr1
    have hWw : vsz (HvdH.rarrVal w) ≤ VB := by
      rw [hVBdef, hTMr']; exact rarrVal_vsz_le_100 hwInDisc hp100 hMr1
    have hTS : vsz (HvdH.intList ts) ≤ VB := by
      rw [hVBdef]
      exact intList_vsz_le_100 (le_trans (le_of_eq hlenD) hDT) hszT hp100 hT1
    have hTS' : vsz (HvdH.intList ts') ≤ VB := by
      rw [hVBdef]
      refine intList_vsz_le_100 ?_ hszT' hp100 hT1
      rw [List.length_dropLast, hlenD]
      exact le_trans (Nat.sub_le _ _) hDT
    have hIntP : vsz (HvdH.Val.int p) ≤ VB := by
      rw [Work.ConvR.vsz_int, hVBdef]
      exact isz_le_100 (n := p) (T := T) (p := p) hpTp' hp100
    have hIntR : vsz (HvdH.Val.int r) ≤ VB := by
      rw [Work.ConvR.vsz_int, hVBdef]
      exact isz_le_100 (n := r) (T := T) (p := p) hrTp' hp100
    -- the nine roll bounds
    have hL3 : ∀ v ∈ ([HvdH.cvecVal zst, HvdH.cvecVal zstie, HvdH.Val.int p, HvdH.Val.int r, HvdH.intList ts', HvdH.intList ts] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs3L : vs2 = ([HvdH.cvecVal zst, HvdH.cvecVal zstie, HvdH.Val.int p, HvdH.Val.int r, HvdH.intList ts', HvdH.intList ts] : List HvdH.Val) ++ (HvdH.cvecVal zs :: R) := by rw [hzout]; rfl
    have hroll3 : ((vs2.take (5 + 1)).map vsz).sum ≤ (5 + 1) * VB :=
      sum_take_vsz_le hs3L (by simp only [List.length_cons, List.length_nil]; norm_num) hL3
    have hc3 : n3 ≤ Kr * (5 + 1) * (((vs2.take (5 + 1)).map vsz).sum + 1) := hcost3
    have hL4 : ∀ v ∈ ([HvdH.intList ts, HvdH.cvecVal zst, HvdH.cvecVal zstie, HvdH.Val.int p] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs4L : vs3 = ([HvdH.intList ts, HvdH.cvecVal zst, HvdH.cvecVal zstie, HvdH.Val.int p] : List HvdH.Val) ++ (HvdH.Val.int r :: HvdH.intList ts' :: HvdH.cvecVal zs :: R) := by rw [hs3]; rfl
    have hroll4 : ((vs3.take (3 + 1)).map vsz).sum ≤ (3 + 1) * VB :=
      sum_take_vsz_le hs4L (by simp only [List.length_cons, List.length_nil]; norm_num) hL4
    have hc4 : n4 ≤ Kr * (3 + 1) * (((vs3.take (3 + 1)).map vsz).sum + 1) := hcost4
    have hL10 : ∀ v ∈ ([HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst, HvdH.Val.int r, HvdH.Val.int p] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs10L : vs9 = ([HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst, HvdH.Val.int r, HvdH.Val.int p] : List HvdH.Val) ++ (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R) := by rw [hubout]; rfl
    have hroll10 : ((vs9.take (4 + 1)).map vsz).sum ≤ (4 + 1) * VB :=
      sum_take_vsz_le hs10L (by simp only [List.length_cons, List.length_nil]; norm_num) hL10
    have hc10 : n10 ≤ Kr * (4 + 1) * (((vs9.take (4 + 1)).map vsz).sum + 1) := hcost10
    have hL11 : ∀ v ∈ ([HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst, HvdH.Val.int r] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs11L : vs10 = ([HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst, HvdH.Val.int r] : List HvdH.Val) ++ (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R) := by rw [hs10]; rfl
    have hroll11 : ((vs10.take (4 + 1)).map vsz).sum ≤ (4 + 1) * VB :=
      sum_take_vsz_le hs11L (by simp only [List.length_cons, List.length_nil]; norm_num) hL11
    have hc11 : n11 ≤ Kr * (4 + 1) * (((vs10.take (4 + 1)).map vsz).sum + 1) := hcost11
    have hL12 : ∀ v ∈ ([HvdH.Val.int r, HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs12L : vs11 = ([HvdH.Val.int r, HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a, HvdH.cvecVal zst] : List HvdH.Val) ++ (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R) := by rw [hs11]; rfl
    have hroll12 : ((vs11.take (4 + 1)).map vsz).sum ≤ (4 + 1) * VB :=
      sum_take_vsz_le hs12L (by simp only [List.length_cons, List.length_nil]; norm_num) hL12
    have hc12 : n12 ≤ Kr * (4 + 1) * (((vs11.take (4 + 1)).map vsz).sum + 1) := hcost12
    have hL13 : ∀ v ∈ ([HvdH.cvecVal zst, HvdH.Val.int r, HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs13L : vs12 = ([HvdH.cvecVal zst, HvdH.Val.int r, HvdH.Val.int p, HvdH.rarrVal ub, HvdH.cvecVal a] : List HvdH.Val) ++ (HvdH.Val.int p :: HvdH.cvecVal zstie :: HvdH.Val.int r :: HvdH.cvecVal ab :: HvdH.Val.int p :: HvdH.Val.int r :: HvdH.intList ts' :: R) := by rw [hs12]; rfl
    have hroll13 : ((vs12.take (4 + 1)).map vsz).sum ≤ (4 + 1) * VB :=
      sum_take_vsz_le hs13L (by simp only [List.length_cons, List.length_nil]; norm_num) hL13
    have hc13 : n13 ≤ Kr * (4 + 1) * (((vs12.take (4 + 1)).map vsz).sum + 1) := hcost13
    have hL15 : ∀ v ∈ ([HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p, HvdH.Val.int r, HvdH.intList ts'] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs15L : vs14 = ([HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p, HvdH.Val.int r, HvdH.intList ts'] : List HvdH.Val) ++ (R) := by rw [huaout]; rfl
    have hroll15 : ((vs14.take (8 + 1)).map vsz).sum ≤ (8 + 1) * VB :=
      sum_take_vsz_le hs15L (by simp only [List.length_cons, List.length_nil]; norm_num) hL15
    have hc15 : n15 ≤ Kr * (8 + 1) * (((vs14.take (8 + 1)).map vsz).sum + 1) := hcost15
    have hL16 : ∀ v ∈ ([HvdH.intList ts', HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p, HvdH.Val.int r] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs16L : vs15 = ([HvdH.intList ts', HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p, HvdH.Val.int r] : List HvdH.Val) ++ (R) := by rw [hs15]; rfl
    have hroll16 : ((vs15.take (8 + 1)).map vsz).sum ≤ (8 + 1) * VB :=
      sum_take_vsz_le hs16L (by simp only [List.length_cons, List.length_nil]; norm_num) hL16
    have hc16 : n16 ≤ Kr * (8 + 1) * (((vs15.take (8 + 1)).map vsz).sum + 1) := hcost16
    have hL17 : ∀ v ∈ ([HvdH.Val.int r, HvdH.intList ts', HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p] : List HvdH.Val), vsz v ≤ VB := by
      intro v hv; fin_cases hv <;> assumption
    have hs17L : vs16 = ([HvdH.Val.int r, HvdH.intList ts', HvdH.rarrVal ua, HvdH.rarrVal ub, HvdH.Val.int p, HvdH.cvecVal zstie, HvdH.Val.int r, HvdH.cvecVal ab, HvdH.Val.int p] : List HvdH.Val) ++ (R) := by rw [hs16]; rfl
    have hroll17 : ((vs16.take (8 + 1)).map vsz).sum ≤ (8 + 1) * VB :=
      sum_take_vsz_le hs17L (by simp only [List.length_cons, List.length_nil]; norm_num) hL17
    have hc17 : n17 ≤ Kr * (8 + 1) * (((vs16.take (8 + 1)).map vsz).sum + 1) := hcost17
    -- the cost arithmetic (isolated in `Work.Transform.transformCost`)
    have h2a : zs.length * p ^ 2 ≤ S := by rw [hzlen]; exact hTpS
    have hSA : S = T * p ^ 2 + ts.sum * (p + 1) ^ KB := rfl
    have hmain : csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, n19, n20] ≤
        4 * M * Cm (3 * r * p) + KB * T * p ^ 2 + KB * ts.sum * (p + 1) ^ KB :=
      transformCost (p := p) (T := T) (r := r) (M := M) (KB := KB) (S := S) (VB := VB)
        (ts := ts) (Cm := Cm)
        (Kp := Kp) (Kz := Kz) (Kc := Kc) (Ks := Ks) (Ka := Ka) (Km := Km) (Kph := Kph)
        (Kps := Kps) (Kr := Kr) (KR := KR)
        (ZL := zs.length) (VTS := _) (VTS' := _) (VIP := _) (VIR := _) (VZst := _) (VZstie := _)
        (VZs := _) (VA := _) (VAb := _)
        (R3 := _) (R4 := _) (R10 := _) (R11 := _) (R12 := _) (R13 := _) (R15 := _) (R16 := _)
        (R17 := _)
        (n1 := n1) (n2 := n2) (n3 := n3) (n4 := n4) (n5 := n5) (n6 := n6) (n7 := n7) (n8 := n8)
        (n9 := n9) (n10 := n10) (n11 := n11) (n12 := n12) (n13 := n13) (n14 := n14) (n15 := n15)
        (n16 := n16) (n17 := n17) (n18 := n18) (n19 := n19) (n20 := n20)
        (hKB := hKB) (hSA := hSA) (hS1 := hS1) (hVBS := hVBS) (hSle := hSle) (hTpS := hTpS)
        (hsumS := hsumS) (hpS := hpS) (hrS := hrS) (hMrS := hMrS) (hrsum := hrsum)
        (hpwP := hpwP) (hpwZ := hpwZ) (hpwC := hpwC) (h2a := h2a)
        (hTS := hTS) (hTS' := hTS') (hIP := hIntP) (hIR := hIntR)
        (hZst := hZst) (hZstie := hZstie) (hZs := hZs) (hAa := hAa) (hAbb := hAbb)
        (hroll3 := hroll3) (hroll4 := hroll4) (hroll10 := hroll10) (hroll11 := hroll11)
        (hroll12 := hroll12) (hroll13 := hroll13) (hroll15 := hroll15) (hroll16 := hroll16)
        (hroll17 := hroll17)
        (hc1 := hcost1) (hc2 := hcost2) (hc3 := hcost3) (hc4 := hcost4) (hc5 := hcost5)
        (hc6 := hcost6) (hc7 := hcost7) (hc8 := hcost8) (hc9 := hcost9) (hc10 := hcost10)
        (hc11 := hcost11) (hc12 := hcost12) (hc13 := hcost13) (hc14 := hcost14) (hc15 := hcost15)
        (hc16 := hcost16) (hc17 := hcost17) (hc18 := hcost18) (hc19 := hcost19) (hc20 := hcost20)
    have hgoal : csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, n19, n20] ≤
        4 * (ts.prod / HvdH.lmax ts) * Cm (3 * HvdH.lmax ts * p) + KB * ts.prod * p ^ 2 +
          KB * ts.sum * (p + 1) ^ KB := by
      show csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, n19, n20] ≤
        4 * (T / r) * Cm (3 * r * p) + KB * T * p ^ 2 + KB * ts.sum * (p + 1) ^ KB
      rw [hdiv]
      exact hmain
    exact hgoal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HvdH.cvecVal z :: R
  · exact s20
  · exact csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20]
  · exact ⟨zs, R, z, rfl, rfl, happrox⟩
  · exact e1
  · dsimp only
    exact hcost
  · rw [← hzout20]; exact hstk20
  · exact hfrall
end Work.Transform
