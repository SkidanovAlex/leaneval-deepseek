/-
# `FTS/StrongPersist/StarPkg6Assembly.lean` — the assembly of `StarPkg6` from the pieces

This is the assembly step of `StarPkg6OfCore`: from

* the order-**six** flat bounds of the five star fields (`FlatW 6` of `EH, EVz, EV, EUz, EU`,
  the piece produced by `FTS/StrongPersist/SP6/FlatW6Fields`),
* the transfer `FlatW 6 → WlInf` on the closed quadrant
  (`FTS/StrongPersist/SP6/WlInf6OfFlatW`),
* the order-six flat bound of the radial block `Yblk Y = z∂_z Y`
  (`FTS/StrongPersist/SP6/F0SixYblk`) and of `Fb 6` of `Ŷ` (`CoreAux.Fb_of_FlatW`),

build `StarPkg6 α (C·Cs) Φs` from `StarCore α Cs Φs`.

The three flat pieces enter as *hypotheses* here, so that this file is independent of which
module supplies them; `StarPkg6OfCore` instantiates them.

The route is exactly the order-four one of `FTS/PhiStar/CoreAux/Assembly.lean`:

1. `StarCore` gives `FlatW 7 Ŷ (Cs·α)` and (via `Fb_of_FlatW`) `Fb 6 (CB·Cs·α) Ŷ`;
2. the five fields are the expressions `EH α Ŷ`, `EVz Ŷ`, `EV Ŷ`, `EUz α Ŷ`, `EU Ŷ`
   (`fields_ident`), whose `FlatW 6`-bounds are the hypothesis `hF`;
3. `FlatW 6` transfers to `WlInfMem α 6` and `WlInf α 6 ≤ CW·(…)` (`hWl`), using the
   vanishing off the open quadrant (`fields_vanish`) and the open-quadrant smoothness
   (`fields_smooth`);
4. the order-four package `StarPkgo2` is supplied by `FTS/PhiStar/StarPkgo2OfCore` and its
   constant is enlarged to the final one (`StarPkgo2_raise_Cs`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.PhiStar.StarPkgo2OfCore
import Submission.Work.FTS.PhiStar.CoreAux.fields_ident
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth
import Submission.Work.FTS.PhiStar.CoreAux.fields_vanish
import Submission.Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

theorem StarPkg6OfPieces
    (hWl : ∃ CW : ℝ, 0 < CW ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ CW * K)
    (hDz : ∃ CD : ℝ, 0 < CD ∧ ∀ (K : ℝ) (Y : ℝ → ℝ → ℝ),
      0 ≤ K → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.VocabO2.FlatW 7 Y K →
      Work.FTS.PhiStar.F0 6 (CD * K) (Work.FTS.PhiStar.Yblk Y))
    (hF : ∃ CF : ℝ, 0 < CF ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
      0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
      Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
      Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EUz α Y) (CF * (α + 1) * (K + KY + KD)) ∧
      Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EU α Y) (CF * (α + 1) * (K + KY + KD))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
      0 < α → α ≤ 1 / 4 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs →
      StarPkg6 α (C * Cs) Φs := by
  obtain ⟨CW, hCW, hWl⟩ := hWl
  obtain ⟨CD, hCD, hDz⟩ := hDz
  obtain ⟨CF, hCF, hF⟩ := hF
  obtain ⟨CB, hCB, hFb⟩ := Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
  obtain ⟨C1, hC1, hStar⟩ := Work.FTS.PhiStar.StarPkgo2OfCore
  -- the master constants
  set CBal : ℝ := CW * CF * (5 / 4) * (1 + CB + CD) with hCBal
  have hCBal0 : 0 ≤ CBal := by rw [hCBal]; positivity
  set Cfin : ℝ := max C1 CBal + 1 with hCfin
  have hCfin0 : 0 < Cfin := by
    rw [hCfin]
    linarith [le_max_left C1 CBal, le_max_right C1 CBal]
  have hC1le : C1 ≤ Cfin := by
    rw [hCfin]; linarith [le_max_left C1 CBal]
  have hCBle : CBal ≤ Cfin := by
    rw [hCfin]; linarith [le_max_right C1 CBal]
  refine ⟨Cfin, hCfin0, ?_⟩
  intro α Cs Φs hα hα4 hCs hcore
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hα1 : α ≤ 1 := by linarith
  have hα54 : α + 1 ≤ 5 / 4 := by linarith
  have hK0 : 0 ≤ Cs * α := mul_nonneg (le_of_lt hCs) hα0
  have hCB0 : 0 ≤ CB := le_of_lt hCB
  have hCD0 : 0 ≤ CD := le_of_lt hCD
  -- the star datum
  have hsmY : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.VocabO2.Ycheck α Φs) :=
    (Work.FTS.PhiStar.CoreAux.smoothOpen_PhiTs hα hα1 hcore.smooth).2.2
  have hY7 : Work.FTS.VocabO2.FlatW 7 (Work.FTS.VocabO2.Ycheck α Φs) (Cs * α) := hcore.core
  have hFbY : Work.FTS.PhiStar.Fb 6 (CB * (Cs * α)) (Work.FTS.VocabO2.Ycheck α Φs) :=
    hFb (Cs * α) _ hK0 hsmY hY7
  have hDzY : Work.FTS.PhiStar.F0 6 (CD * (Cs * α)) (Work.FTS.PhiStar.Yblk (Work.FTS.VocabO2.Ycheck α Φs)) :=
    hDz (Cs * α) _ hK0 hsmY hY7
  obtain ⟨hFeh, hFevz, hFev, hFeuz, hFeu⟩ :=
    hF α (Cs * α) (CB * (Cs * α)) (CD * (Cs * α)) (Work.FTS.VocabO2.Ycheck α Φs)
      hα0 hK0 (by positivity) (by positivity) hsmY hY7 hFbY hDzY
  -- the identities, smoothness and vanishing of the five fields
  obtain ⟨hidH, hidV, hidVz, hidU, hidUz, _hidPU⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_ident hα hα1 hcore.smooth
  obtain ⟨hvH, hvV, hvVz, hvU, hvUz, -, -, -, -, -⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_vanish hα hcore
  obtain ⟨-, hsmH, hsmV, hsmVz, hsmU, hsmUz, -⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hcore.smooth
  -- the five order-six `WlInf`-bounds, at the intermediate constant
  set Km : ℝ := CF * (α + 1) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) with hKm
  have hH := hWl α
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvH) hsmH
    (FlatW_congr (fun z θ hz hθ hθ' => hidH z θ hz hθ hθ') hFeh)
  have hV := hWl α (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs))
    Km hα hα1 (zeroOff_of_vanish_Q0 hvV) hsmV
    (FlatW_congr (fun z θ hz hθ hθ' => hidV z θ hz hθ hθ') hFev)
  have hVz := hWl α
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvVz) hsmVz
    (FlatW_congr (fun z θ hz hθ hθ' => hidVz z θ hz hθ hθ') hFevz)
  have hU := hWl α
    (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ)
    Km hα hα1 (zeroOff_of_vanish_Q0 hvU) hsmU
    (FlatW_congr (fun z θ hz hθ hθ' => hidU z θ hz hθ hθ') hFeu)
  have hUz := hWl α
    (fun z θ => (z + 1) / z * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ))
    Km hα hα1 (zeroOff_of_vanish_Q0 hvUz) hsmUz
    (FlatW_congr (fun z θ hz hθ hθ' => hidUz z θ hz hθ hθ') hFeuz)
  -- the constant comparison: `CW * Km ≤ CBal * (Cs * α)`
  have hKm_le : CW * Km ≤ CBal * (Cs * α) := by
    have hx : 0 ≤ Cs * α + CB * (Cs * α) + CD * (Cs * α) :=
      add_nonneg (add_nonneg hK0 (mul_nonneg hCB0 hK0)) (mul_nonneg hCD0 hK0)
    have hcc : 0 ≤ CW * CF := mul_nonneg (le_of_lt hCW) (le_of_lt hCF)
    have h1 : CW * CF * (α + 1) ≤ CW * CF * (5 / 4) :=
      mul_le_mul_of_nonneg_left hα54 hcc
    rw [hKm, hCBal]
    calc CW * (CF * (α + 1) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)))
        = (CW * CF * (α + 1)) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) := by ring
      _ ≤ (CW * CF * (5 / 4)) * (Cs * α + CB * (Cs * α) + CD * (Cs * α)) :=
          mul_le_mul_of_nonneg_right h1 hx
      _ = CW * CF * (5 / 4) * (1 + CB + CD) * (Cs * α) := by ring
  have hbound : ∀ f : ℝ → ℝ → ℝ, Work.Spaces.WlInf α 6 f ≤ CW * Km → Work.Spaces.WlInf α 6 f ≤ Cfin * Cs * α := by
    intro f hf
    have h2 : CBal * (Cs * α) ≤ Cfin * (Cs * α) := mul_le_mul_of_nonneg_right hCBle hK0
    have h3 : Cfin * (Cs * α) = Cfin * Cs * α := by ring
    linarith [hKm_le]
  refine
    { toStarPkgo2 := StarPkgo2_raise_Cs hα0
        (mul_le_mul_of_nonneg_right hC1le (le_of_lt hCs))
        (hStar α Cs Φs hα hα4 hCs hcore)
      RW6 := ⟨hH.1, hbound _ hH.2⟩
      VW6 := ⟨hV.1, hbound _ hV.2⟩
      VzW6 := ⟨hVz.1, hbound _ hVz.2⟩
      UsW6 := ⟨hU.1, hbound _ hU.2⟩
      UszW6 := ⟨hUz.1, hbound _ hUz.2⟩ }

end Work.FTS.StrongPersist
