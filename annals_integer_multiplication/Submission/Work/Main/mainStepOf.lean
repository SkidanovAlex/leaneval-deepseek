import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs
import Submission.Work.Main.epilogue
import Submission.Work.Main.step.setup
import Submission.Work.Main.step.prep
import Submission.Work.Main.fstep.finalize
import Submission.Work.Main.final.finalWord
import Submission.Work.Main.stepkit.nchunksBounds
import Submission.Work.Main.stepkit.inDisc_pchunkZ
import Submission.Work.Main.stepkit.inDisc_of_labelled
import Submission.Work.Main.stepkit.envszLe
import Submission.Work.Main.cost.mainCostBound

/-!
# Assembly of the main step (`Work.Main.mainStepOf`)

The four stages of one recursive step of the Harvey–van der Hoorn algorithm, composed:

* `Work.Main.step.setup` : `[int x, int y] ++ R ↦ env sp R` (parameters, chunk count, CRT data);
* `Work.Main.step.prep` : `env sp R ↦ [cvecVal F, cvecVal G] ++ env sp R` (chunks, CRT reindexing, scaling);
* `Work.Main.step.finalize` : Prop 5.3 + recovery + inverse reindexing (`ofList ys`);
* `Work.Main.final.finalWord` : take `2N'-1` coefficients, evaluate at `2^b`, drop the environment.

The cost is bounded by `HvdH.mainCost K Cm n` via `Work.Main.cost.mainCostBound`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Main

open HvdH

theorem mainStep_of (hKer : HvdH.KernelLib) (hInt : HvdH.IntLib) (hLay : HvdH.LayoutLib) (hFx : HvdH.FxLib)
    (hDFT : HvdH.DFTMathProp) (hP : HvdH.ParamsProp) (hMP : HvdH.MainParamsProp)
    (h53p : HvdH.Prop53Prop) (hCp : HvdH.CrtWordProp) : HvdH.MainStepProp := by
  obtain ⟨progPar, KPar, nPar, hPar⟩ := hP
  obtain ⟨prog53, K53, h53⟩ := h53p
  obtain ⟨progSetup, KSetup, hSetup⟩ := Work.Main.step.setup hKer hInt hLay progPar KPar nPar hPar
  obtain ⟨progPrep, KPrep, hPrep⟩ := Work.Main.step.prep hKer hInt hLay hCp
  obtain ⟨progFin, KFin, hFin⟩ := Work.Main.fstep.finalize hKer hInt hLay hFx hCp prog53 K53 h53
  obtain ⟨progEpi, Kepi, hEpi⟩ := Work.Main.final.finalWord hKer hInt hLay
  set KB : ℕ := 10000000 * (KPar + KSetup + KPrep + KFin + Kepi + K53 + 1) with hKB
  obtain ⟨n₂, hn₂⟩ := hMP KB
  refine ⟨Cmd.seq progSetup (Cmd.seq progPrep (Cmd.seq progFin progEpi)), KB,
    max nPar (max n₂ (2 ^ (256 * KB ^ 2 + 2 ^ 61 + 2))), ?_⟩
  intro main N Cm hmono hmul
  intro vs hpre s Rg hs
  obtain ⟨x, y, rest, hvs, hna1, hnN⟩ := hpre
  have hn1a : nPar ≤ (max x.size y.size) := le_trans (le_max_left _ _) hna1
  have hn2a : n₂ ≤ (max x.size y.size) := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hna1)
  have hnbig : 2 ^ (256 * KB ^ 2 + 2 ^ 61 + 2) ≤ (max x.size y.size) :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hna1)
  have hnN' : (max x.size y.size) ≤ N := hnN
  -- ##################### stage 1: setup #####################
  have hvs1 : vs = [Val.int x, Val.int y] ++ rest := by rw [hvs]; rfl
  have hs1 : s.stk 0 = encs ([Val.int x, Val.int y] ++ rest) ++ Rg := by rw [← hvs1]; exact hs
  obtain ⟨o1, s1, m1, hQ1, hev1, hcost1, hstk1, hoth1⟩ :=
    hSetup main rest x y hn1a ([Val.int x, Val.int y] ++ rest) rfl s Rg hs1
  obtain ⟨-, sp, ho1, hspx, hspy, hspb, hspp, hspa, hspS, hspT, hsslen, htslen, hOK, hspN⟩ := hQ1
  -- parameter inequalities of §5.1
  obtain ⟨hPow2, hResPar, hlmax, h3rp, hKp, h3Dp2, hγmp, hTlt, hSleT, hN2mp, hTbmp, hnbmp, hb1mp, hp100⟩ :=
    hn₂ (max x.size y.size) sp.ts sp.ss hn2a hOK
  -- ##################### derived facts #####################
  have hDpos : 1 ≤ HvdH.D := by norm_num [HvdH.D]
  have hppar : HvdH.ppar (max x.size y.size) = 6 * HvdH.bpar (max x.size y.size) := rfl
  have hxnt : x.size ≤ (max x.size y.size) := le_max_left _ _
  have hynt : y.size ≤ (max x.size y.size) := le_max_right _ _
  obtain ⟨hNcle, hNcge⟩ := Work.Main.stepkit.nchunksBounds (max x.size y.size) (HvdH.bpar (max x.size y.size)) hb1mp
  have hspx' : sp.x = x := hspx
  have hspy' : sp.y = y := hspy
  have hxl : sp.x.size ≤ (max x.size y.size) := by rw [hspx]; exact hxnt
  have hyl : sp.y.size ≤ (max x.size y.size) := by rw [hspy]; exact hynt
  have hb1 : 1 ≤ sp.b := by rw [hspb]; exact hb1mp
  have hbp : sp.b ≤ sp.p := by rw [hspb, hspp, hppar]; omega
  have h2bp : 2 * sp.b < sp.p := by rw [hspb, hspp, hppar]; omega
  have h6bp : 6 * sp.b ≤ sp.p := by rw [hspb, hspp, hppar]
  have hb12 : 12 ≤ sp.b := by
    rw [hspb]
    have h0 : 0 ≤ 2 * HvdH.D * HvdH.apar (max x.size y.size) ^ 2 := Nat.zero_le _
    omega
  have hcop : sp.ss.Pairwise Nat.Coprime := hOK.2.2.2.2.2.2.1
  have hodd := hOK.2.2.2.2.2.2.2
  have hpos : ∀ s ∈ sp.ss, 1 ≤ s := fun s hs => by have := (hodd s hs).pos; omega
  have hlogN : sp.N' = nchunks (max x.size y.size) (HvdH.bpar (max x.size y.size)) := hspN
  have hNsl : sp.N' ≤ sp.S := by
    rw [hlogN, hspS]
    have h := hN2mp
    simp only [nchunks] at h ⊢
    omega
  have hFlenS : sp.S = sp.ss.prod := hspS
  have hSpow : sp.S ≤ 2 ^ sp.p := by
    have h1 : sp.S ≤ HvdH.Tpar (max x.size y.size) := by rw [hspS]; exact hSleT
    have h2 : HvdH.Tpar (max x.size y.size) = sp.ts.prod := hspT.symm
    have h3 : (sp.ts.prod : ℕ) < 2 ^ HvdH.ppar (max x.size y.size) := hPow2.2.2.2.1
    rw [hspp]
    calc sp.S ≤ HvdH.Tpar (max x.size y.size) := h1
      _ = sp.ts.prod := h2
      _ ≤ 2 ^ HvdH.ppar (max x.size y.size) := le_of_lt h3
  have hN2 : 2 * sp.N' ≤ sp.S + 1 := by rw [hspS, hlogN]; exact hN2mp
  have hxN : sp.x.size ≤ sp.b * sp.N' := by
    rw [hspx, hspb, hlogN]
    calc x.size ≤ (max x.size y.size) := hxnt
      _ ≤ HvdH.bpar (max x.size y.size) * nchunks (max x.size y.size) (HvdH.bpar (max x.size y.size)) := hNcge
  have hyN : sp.y.size ≤ sp.b * sp.N' := by
    rw [hspy, hspb, hlogN]
    calc y.size ≤ (max x.size y.size) := hynt
      _ ≤ HvdH.bpar (max x.size y.size) * nchunks (max x.size y.size) (HvdH.bpar (max x.size y.size)) := hNcge
  have hSleTsp : sp.S ≤ sp.ts.prod := by
    rw [hspS, hspT]
    exact hSleT
  -- ##################### stage 2: preparation #####################
  obtain ⟨o2, s2, m2, hQ2, hev2, hcost2, hstk2, hoth2⟩ :=
    hPrep main rest sp hxN hyN hb1 hbp hspS hsslen hpos hcop hNsl hSpow
      (env sp rest) rfl s1 Rg (by rw [← ho1]; exact hstk1)
  obtain ⟨F, G, -, ho2, hFlen, hGlen, hFl, hGl⟩ := hQ2
  have hFlen' : F.length = sp.ss.prod := by rw [hFlen, hspS]
  have hGlen' : G.length = sp.ss.prod := by rw [hGlen, hspS]
  -- ##################### stage 3: Prop 5.3 + recovery + CRT inverse #####################
  have hFsPar : HvdH.FsParams sp.p sp.α sp.ss sp.ts := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hspp]; exact hPow2
    · rw [hspp, hspa]; exact hResPar
    · rw [hspp, hspa, hppar]
      have := hγmp
      omega
    · rw [hspp, hspT]; exact h3Dp2
    · rw [← hspS]; exact hSleTsp
  have h3lp : 3 * HvdH.lmax sp.ts * sp.p < N := by
    rw [hlmax, hspp]
    exact lt_of_lt_of_le h3rp hnN'
  have hK53le : K53 ≤ KB := by rw [hKB]; omega
  have hK53p : K53 * sp.p < N := by
    rw [hspp]
    exact lt_of_lt_of_le (lt_of_le_of_lt (Nat.mul_le_mul_right _ hK53le) hKp) hnN'
  have hinF : ∀ z ∈ F, HvdH.inDisc sp.p z :=
    Work.Main.stepkit.inDisc_of_labelled (ss := sp.ss) (F := F) (p := sp.p) (b := sp.b)
      (N' := sp.N') (x := sp.x) hcop hpos hFlen' hbp
      (fun m hm => by
        have hm' : m < sp.S := by rw [hspS]; exact hm
        rw [← hspS]
        exact hFl m hm')
  have hinG : ∀ z ∈ G, HvdH.inDisc sp.p z :=
    Work.Main.stepkit.inDisc_of_labelled (ss := sp.ss) (F := G) (p := sp.p) (b := sp.b)
      (N' := sp.N') (x := sp.y) hcop hpos hGlen' hbp
      (fun m hm => by
        have hm' : m < sp.S := by rw [hspS]; exact hm
        rw [← hspS]
        exact hGl m hm')
  obtain ⟨o3, s3, m3, hQ3, hev3, hcost3, hstk3, hoth3⟩ :=
    hFin main N Cm hmono hmul rest sp F G hFsPar h3lp hK53p hspS hpos hcop hbp h2bp hSpow hN2
      hFlen' hGlen' hinF hinG
      (cvecVal F :: cvecVal G :: env sp rest) rfl s2 Rg (by rw [← ho2]; exact hstk2)
  obtain ⟨zs, ys, -, ho3, hzslen, hyslen, hApprox, hysrec⟩ := hQ3
  have hyslenS : ys.length = sp.S := by rw [hyslen, hspS]
  -- ##################### the mathematical identification of `ys` #####################
  have hTbsp : sp.ts.prod * sp.b ≤ 10 * max sp.x.size sp.y.size := by
    rw [hspT, hspb, hspx, hspy]
    have := hTbmp
    omega
  have hnb' : max sp.x.size sp.y.size ≤ 2 ^ sp.b := by
    rw [hspx, hspy, hspb]
    exact hnbmp
  have hγsp : 2 * HvdH.D * sp.α ^ 2 + 13 < sp.b := by rw [hspa, hspb]; exact hγmp
  have hyscoeff : ∀ m < sp.S, ys.getD m 0 = ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ) :=
    Work.Main.ys_getD_hcoeff (sp := sp) (zs := zs) (F := F) (G := G) (ys := ys) hDFT
      (by rw [hspx, hspy]; exact hOK) hspS
      (fun m hm => hFl m (by rw [hspS]; exact hm))
      (fun m hm => hGl m (by rw [hspS]; exact hm))
      (by rw [hspx, hspy]; exact hspb) hγsp hbp h6bp hb12 hTbsp hnb' hApprox hSleTsp hN2 hysrec
  -- ##################### stage 4: the epilogue #####################
  have hNpow : sp.N' ≤ 2 ^ sp.b := by
    rw [hspb, hlogN]
    exact le_trans hNcle hnbmp
  have h2N1 : 2 * sp.N' - 1 ≤ sp.S := by omega
  obtain ⟨o4, s4, m4, hQ4, hev4, hcost4, hstk4, hoth4⟩ :=
    hEpi main rest sp ys hyslenS hyscoeff hb1 hNpow h2N1 hxN hyN
      (ofList (ys.map Val.int) :: env sp rest) rfl s3 Rg (by rw [← ho3]; exact hstk3)
  -- ##################### conclusion #####################
  have hmul : HvdH.mulSize vs = (max x.size y.size) := by
    rw [hvs]
    simp [HvdH.mulSize, Int.natAbs_natCast]
  refine ⟨o4, s4, m1 + (m2 + (m3 + m4)), ?_, ?_, ?_, hstk4,
    fun k hk => by rw [hoth4 k hk, hoth3 k hk, hoth2 k hk, hoth1 k hk]⟩
  · refine ⟨x, y, rest, hvs, ?_⟩
    rw [hQ4.2, hspx, hspy]
    simp only [Nat.cast_mul]
  · exact Eval.seq hev1 (Eval.seq hev2 (Eval.seq hev3 hev4))
  · show m1 + (m2 + (m3 + m4)) ≤ HvdH.mainCost KB Cm (HvdH.mulSize vs)
    rw [hmul]
    have hc1 : m1 ≤ KPar * ((max sp.x.size sp.y.size).size + 1) ^ KPar * KSetup +
        KSetup * (sp.x.size + sp.y.size + 1) := by
      rw [hspx, hspy]; exact hcost1
    have hc2 : m2 ≤ KPrep * (sp.S + 1) * (HvdH.vsz (HvdH.intList sp.ss) + HvdH.vsz (HvdH.intList sp.ts) + sp.b + sp.p + 1)
          * (sp.S.size + 1)
      + KPrep * (sp.S + 1) * (sp.p + 1) * (sp.b + 1) * (HvdH.D + 1)
      + KPrep * (sp.x.size + sp.y.size + sp.b + sp.N' + sp.S + 1)
      + KPrep * (envsz sp + 1) := hcost2
    have hc3 : m3 ≤ 3 * HvdH.fsCost K53 Cm sp.p sp.α sp.ts + K53 +
      KFin * (sp.S + 1) * (sp.p + 1) * (sp.p + 1) +
      KFin * (sp.S + 1) * (HvdH.D + 1) * (sp.p + 1) * (sp.p + 1) := hcost3
    have hc4 : m4 ≤ Kepi * (sp.S + 1) * (sp.b + 1) + Kepi * (envsz sp + 1) := hcost4
    have hclog : (256 * KB ^ 2 + 2 ^ 61 + 2 : ℕ) ≤ HvdH.bpar (max x.size y.size) := by
      have h2 : (256 * KB ^ 2 + 2 ^ 61 + 2 : ℕ) ≤ Nat.clog 2 (max x.size y.size) := by
        rw [← Nat.clog_pow 2 (256 * KB ^ 2 + 2 ^ 61 + 2) (by norm_num)]
        exact Nat.clog_mono_right 2 hnbig
      simpa only [HvdH.bpar] using h2
    have htot : totalCost KPar KSetup KPrep KFin Kepi K53 Cm sp ≤ HvdH.mainCost KB Cm (max x.size y.size) :=
      Work.Main.cost.mainCostBound (sp := sp) (Cm := Cm) (n := (max x.size y.size)) (KPar := KPar)
        (Ksetup := KSetup) (Kprep := KPrep) (Kfin := KFin) (Kepi := Kepi) (K53 := K53)
        (K0 := KB) hmono (by rw [hKB]) hspb hspp hspa hspN hspS hlmax hspT hxl hyl
        (by have := hclog; omega)
        (by have := hclog; omega)
        hTbmp hnbmp hSleT (by rw [← hspS]; exact hN2)
        (Work.Main.step.vsz_intList_params (max x.size y.size) sp.ts sp.ss hOK).1
        (Work.Main.step.vsz_intList_params (max x.size y.size) sp.ts sp.ss hOK).2
        (Work.Main.stepkit.envszLe hOK hspb hspp hspa hspS hspN hxl hyl
          (Work.Main.step.vsz_intList_params (max x.size y.size) sp.ts sp.ss hOK).1
          (Work.Main.step.vsz_intList_params (max x.size y.size) sp.ts sp.ss hOK).2)
        hOK
    have hsum : m1 + (m2 + (m3 + m4)) ≤ totalCost KPar KSetup KPrep KFin Kepi K53 Cm sp := by
      simp only [totalCost]
      omega
    exact le_trans hsum htot

end Work.Main
