import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.NB4Aux` — the α-absorption helpers for the level-`4` pricing of `blkN`

This file is the toolbox for the per-piece `ℋ⁴`-pricing of the twenty pieces
`Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k` (the `b4` field of `BData α w K (blkN …)`).

The two product rules of the tree have an explicit `α ^ (-1/2)` in front:

* `Work.FTS.OpenPkg.prod_field`: `Xn α (f·g) ≤ Cp·α^{-1/2}·Xn α f·Xn α g`;
* `Work.FTS.OpenPkg.wprod_field_winf`: `Xn α (f·g) ≤ Cw·α^{-1/2}·WlInf α 4 f·Xn α g`.

In every one of the twenty pieces one of the two factors is *`α`-small* — its price carries a
genuine factor `α` (`α¹` for the `𝒲^{4,∞}` star coefficients `Cs·α` and the `hKer` atom `400α`,
`α²` for the perturbed coefficients `Ce·C₀·α²`, the `φ`-multiplications and `FK w`).  So the
`α^{-1/2}` is absorbed:

  `α^{-1/2} · (b·α^s) ≤ b`  for `α ∈ (0,1]`, `s ≥ 1`.

That is the content of `mulQo_absorb` and `mulW_absorb` below: they take the price of the
coefficient in the *normalized* form `bA · α ^ s` (`s ≥ 1`, `bA` independent of `α`) together with
the price `Q` of the factor, and return a bound with the α-free constant `|c|·Cprod·bA·Q`
respectively `|c|·Cw·bF·Q`.

`Xn_w_slots_le` records the three prices of the `w`-slots met in the pieces that *do* grow with
`HkNorm α 5 w` (the shifted slots `D_θw`, `D_zw`, and `w` itself).

`exists_neg_sinSq_mul` is the `-sin²θ`-multiplication used by the pieces 16–19.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The absorption of the `α^{-1/2}` of the product rule against an `α`-small coefficient:
`α^{-1/2}·α^s ≤ 1` for `α ∈ (0,1]`, `s ≥ 1`. -/
theorem rpow_neg_half_mul_nat_le_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {s : ℕ} (hs : 1 ≤ s) :
    α ^ (-(1 / 2 : ℝ)) * α ^ s ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ s = α ^ (-(1 / 2 : ℝ) + (s : ℝ)) := by
    rw [← Real.rpow_natCast α s, ← Real.rpow_add hα]
  rw [h1]
  refine Real.rpow_le_one hα.le hα1 ?_
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  linarith

/-- **The `ℋ⁴`-product rule with an `α`-small `ℋ⁴`-coefficient.**  If `Xn α A ≤ bA · α^s` with
`s ≥ 1` and `Xn α P ≤ Q`, then `c·(A·P)` is `ℋ⁴`-honest with `Xn α (c·(A·P)) ≤ |c|·Cprod·bA·Q`:
the `α^{-1/2}` of `prod_field` is absorbed by the `α`-smallness of `A`. -/
theorem mulQo_absorb {α Cprod : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {c bA Q : ℝ} {s : ℕ} (hs : 1 ≤ s) (hbA : 0 ≤ bA) (hQ : 0 ≤ Q)
    {A P : Fn} (hA : Work.FTS.VocabO.HQo α 4 A) (hP : Work.FTS.VocabO.HQo α 4 P)
    (hAb : Work.FTS.Nonlin.Xn α A ≤ bA * α ^ s) (hPb : Work.FTS.Nonlin.Xn α P ≤ Q) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (A z θ * P z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (A z θ * P z θ)) ≤ |c| * Cprod * bA * Q := by
  obtain ⟨hm, hb⟩ :=
    Work.FTS.StrongEps.ClassCRHS.mulHQo hα hCprod hfield
      (mul_nonneg hbA (by positivity)) (by positivity) hA hP hAb hPb
  refine ⟨hm, ?_⟩
  refine le_trans hb ?_
  have hkey := rpow_neg_half_mul_nat_le_one hα hα1 hs
  have hstep : |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * (bA * α ^ s) * Q
      = (|c| * Cprod * bA * Q) * (α ^ (-(1 / 2 : ℝ)) * α ^ s) := by ring
  rw [hstep]
  simpa using mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hCprod.le) hbA) hQ) hkey

/-- **The `ℋ⁴`-product rule with an `α`-small `𝒲^{4,∞}`-coefficient.**  The `WlInf`-analogue of
`mulQo_absorb`, through `wprod_field_winf`. -/
theorem mulW_absorb {α Cw : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {c bF Q : ℝ} {s : ℕ} (hs : 1 ≤ s) (hbF : 0 ≤ bF) (hQ : 0 ≤ Q)
    {F G : Fn} (hFs : Work.FTS.EllipticEst.SmoothOpen F) (hFm : Work.Spaces.WlInfMem α 4 F)
    (hG : Work.FTS.VocabO.HQo α 4 G)
    (hFb : Work.Spaces.WlInf α 4 F ≤ bF * α ^ s) (hGb : Work.FTS.Nonlin.Xn α G ≤ Q) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * G z θ)) ≤ |c| * Cw * bF * Q := by
  obtain ⟨hm, hb⟩ :=
    Work.FTS.StrongEps.ClassCRHS.mulW hα hCw hfield
      (mul_nonneg hbF (by positivity)) (by positivity) hFs hFm hFb hG hGb
  refine ⟨hm, ?_⟩
  refine le_trans hb ?_
  have hkey := rpow_neg_half_mul_nat_le_one hα hα1 hs
  have hstep : |c| * Cw * α ^ (-(1 / 2 : ℝ)) * (bF * α ^ s) * Q
      = (|c| * Cw * bF * Q) * (α ^ (-(1 / 2 : ℝ)) * α ^ s) := by ring
  rw [hstep]
  simpa using mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg c) hCw.le) hbF) hQ) hkey

/-- **The three `w`-slot prices**: `w`, `D_θw = sin(2θ)∂_θw` and `D_zw` are all priced by
`1 + HkNorm α 5 w` (`w` by monotonicity of the level, the other two by the level-shift theorems
`Xn_Dth_le_Xn5`/`Xn_Dz_le_Xn5`). -/
theorem Xn_w_slots_le {α : ℝ} {w : Fn} (hα : 0 < α) (hreg : Work.FTS.EllipticEst.SmoothOpen w)
    (hm5 : Work.Spaces.HkMem α 5 w) :
    Work.FTS.Nonlin.Xn α w ≤ 1 + Work.Spaces.HkNorm α 5 w ∧
      Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ 1 + Work.Spaces.HkNorm α 5 w ∧
      Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ 1 + Work.Spaces.HkNorm α 5 w := by
  have hmono : Work.Spaces.HkSq α 4 w ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ 4) hm5
  have h4 : Work.FTS.Nonlin.Xn α w ≤ Work.Spaces.HkNorm α 5 w := by
    show Real.sqrt (Work.Spaces.HkSq α 4 w) ≤ Real.sqrt (Work.Spaces.HkSq α 5 w)
    exact Real.sqrt_le_sqrt hmono
  have h5 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ Work.Spaces.HkNorm α 5 w :=
    Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hm5
  have h6 : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Work.Spaces.HkNorm α 5 w :=
    Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hreg hm5
  have hnn : 0 ≤ Work.Spaces.HkNorm α 5 w := Real.sqrt_nonneg _
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **Angular multiplication by `-sin²θ`** in `ℋ⁴`, with an `α`-free constant, at level `4`
(the profile `θ ↦ -sin²θ` is bounded by `192` on `Iθ` with all `D_θ`-iterates up to order `4`
bounded by `192·sin 2θ`). -/
theorem exists_neg_sinSq_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃α : ℝ⦄, 0 < α → α ≤ 1 → ∀ ⦃f : Fn⦄,
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.HQo α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * f z θ)
        ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨Cang, hCang, hang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Bsin, hBsin, -, hBB, hBit⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  have hCsin_pos : 0 < Real.sqrt (Cang * Bsin ^ 2) := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.sqrt (Cang * Bsin ^ 2), hCsin_pos, ?_⟩
  intro α hα hα1 f hfs hfm
  have hmem := hang α hα hα1 (fun θ => -(Real.sin θ) ^ 2) Bsin hBsin
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq (fun θ hθ => hBB θ hθ)
    (fun i hi hi4 θ hθ => hBit i hi hi4 θ hθ) f hfs hfm.2
  obtain ⟨hm, hsq⟩ := hmem
  refine ⟨hm, ?_⟩
  have hann : 0 ≤ Cang * Bsin ^ 2 := by positivity
  calc Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * f z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => -(Real.sin θ) ^ 2 * f z θ)) := rfl
    _ ≤ Real.sqrt (Cang * Bsin ^ 2 * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Cang * Bsin ^ 2) * Work.Spaces.HkNorm α 4 f := by
        rw [Real.sqrt_mul hann, Work.Spaces.HkNorm]
    _ = Real.sqrt (Cang * Bsin ^ 2) * Work.FTS.Nonlin.Xn α f := rfl

/-! ## Two convenience lemmas for the `K · (1 + HkNorm α 5 w)` pricing -/

/-- `1 ≤ 1 + HkNorm α 5 w`. -/
theorem one_le_one_add_HkNorm5 {α : ℝ} {w : Fn} :
    (1 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := by
  have h : (0 : ℝ) ≤ Work.Spaces.HkNorm α 5 w := by
    rw [Work.Spaces.HkNorm]; exact Real.sqrt_nonneg _
  linarith

/-- `0 ≤ 1 + HkNorm α 5 w`. -/
theorem zero_le_G {α : ℝ} {w : Fn} : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w :=
  le_trans zero_le_one one_le_one_add_HkNorm5

/-- **Weakening a constant bound to `K·(1 + HkNorm α 5 w)`.** -/
theorem le_mul_G {α : ℝ} {w : Fn} {x K : ℝ} (h : x ≤ K) (hK : 0 ≤ K) :
    x ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  calc x ≤ K := h
    _ = K * 1 := (mul_one K).symm
    _ ≤ K * (1 + Work.Spaces.HkNorm α 5 w) :=
        mul_le_mul_of_nonneg_left one_le_one_add_HkNorm5 hK

/-- `C·α^s ≤ C` for `α ∈ (0,1]`, `0 ≤ C`. -/
theorem mul_pow_le_self {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {C : ℝ} (hC : 0 ≤ C) (s : ℕ) :
    C * α ^ s ≤ C := by
  have h1 : α ^ s ≤ (1 : ℝ) ^ s := pow_le_pow_left₀ hα0.le hα1 s
  simp only [one_pow] at h1
  calc C * α ^ s ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC
    _ = C := mul_one C

/-! ## The pricing context of the twenty pieces

`NB4Ctx C C₀ Ce Cs α Φs w Φg` collects, at a single `α`-free constant `C ≥ 1`, all the
factor/coefficient data consumed by the twenty per-piece estimates of `NBlk`:

* the two product rules, normalized (`Cprod`, `Cw ≤ C`);
* the three `w`-slots, priced by `1 + HkNorm α 5 w`, and the three `φ = z/(1+z)`-scaled ones,
  priced by `C·(1 + HkNorm α 5 w)`;
* the perturbed coefficients `Rop Φ̃_g`, `Uop Φ̃_g/sin 2θ`, `Vop Φ̃_g` and `FK w`, each
  `α²`-small (`≤ C·α²`) — this is the smallness that absorbs the `α^{-1/2}` of the product rules;
* `-(2α)·hKer` and the three `(z+1)/z`-weighted star coefficients, each `𝒲^{4,∞}`-small
  (`≤ C·α`);
* the fixed `F_*`-atoms (`F_*`, `D_θF_*`, `D_zF_*` with `𝒲^{4,∞}`-prices `Cα`, `Cα²`, `Cα`), the
  three `φ`-scaled `F_*`-atoms and the two fixed `FK(F_*)`-products (priced by the constant `C`);
* the `-sin²θ`-multiplication.

`NB4Ctx` is designed so that every piece `NBlk k` is priced by a single application of
`mulQo_absorb`/`mulW_absorb` (resp. of `hSinMul`), with the *factor*'s price passed in as the
`Q`-argument. -/
structure NB4Ctx (C : ℝ) (C₀ Ce Cs : ℝ) (α : ℝ) (Φs w Φg : Fn) : Prop where
  hα0 : 0 < α
  hα1 : α ≤ 1
  hCpos : 0 < C
  hCone : 1 ≤ C
  /-- the `ℋ⁴ × ℋ⁴` product rule, with the α-free constant `C` -/
  hPQo : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g
  /-- the `𝒲^{4,∞} × ℋ⁴` product rule, with the α-free constant `C` -/
  hPW : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
  -- the `w`-slots
  wqo : Work.FTS.VocabO.HQo α 4 w
  dthwqo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth w)
  dzwqo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dz w)
  wX : Work.FTS.Nonlin.Xn α w ≤ 1 + Work.Spaces.HkNorm α 5 w
  dthwX : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ 1 + Work.Spaces.HkNorm α 5 w
  dzwX : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ 1 + Work.Spaces.HkNorm α 5 w
  phiwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * w z θ)
  phiDthwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
  phiDzwqo : Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
  phiwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  phiDthwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  phiDzwX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ)
    ≤ C * (1 + Work.Spaces.HkNorm α 5 w)
  -- the perturbed coefficients (`α²`-small)
  Rsm : Work.FTS.EllipticEst.SmoothOpen
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
  Rqo : Work.FTS.VocabO.HQo α 4 (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
  RX : Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2
  Usm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
  Uqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ)
  UX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ C * α ^ 2
  Vsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
  Vqo : Work.FTS.VocabO.HQo α 4 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
  VX : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C * α ^ 2
  FKwsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z)
  FKwqo : Work.FTS.VocabO.HQo α 4 (fun z _ => Work.Construction.FK w z)
  FKwX : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ C * α ^ 2
  -- `-(2α)·hKer` (`α`-small, `𝒲^{4,∞}`)
  FKnegsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
  FKnegWm : Work.Spaces.WlInfMem α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z)
  FKnegW : Work.Spaces.WlInf α 4 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ C * α
  -- the three `(z+1)/z`-weighted star coefficients (`α`-small, `𝒲^{4,∞}`)
  Rssm : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  RsWm : Work.Spaces.WlInfMem α 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  RsW : Work.Spaces.WlInf α 4
    (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α
  Ussm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
  UsWm : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
  UsW : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) ≤ C * α
  Vssm : Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  VsWm : Work.Spaces.WlInfMem α 4
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
  VsW : Work.Spaces.WlInf α 4
    (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α
  -- the fixed `F_*`-atoms
  FWsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α)
  FWWm : Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α)
  FWW : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α
  DthFssm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α))
  DthFsWm : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
  DthFsW : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2
  DzFssm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α))
  DzFsWm : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
  DzFsW : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α
  -- the three `φ`-scaled `F_*`-atoms
  phiFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ)
  phiFsX : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C
  phiDthFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  phiDthFsX : Work.FTS.Nonlin.Xn α
    (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C
  phiDzFsqo : Work.FTS.VocabO.HQo α 4
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
  phiDzFsX : Work.FTS.Nonlin.Xn α
    (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C
  -- the fixed `FK(F_*)`-atom and its two products
  FKFSsm : Work.FTS.EllipticEst.SmoothOpen
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
  FKFSWm : Work.Spaces.WlInfMem α 4
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z)
  FKFSW : Work.Spaces.WlInf α 4
    (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) ≤ C * α
  prodFKDthFSqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
  prodFKDthFSX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C
  prodFKFSqo : Work.FTS.VocabO.HQo α 4 (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ)
  prodFKFSX : Work.FTS.Nonlin.Xn α (fun z θ =>
    Work.Construction.FK (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) ≤ C
  /-- angular multiplication by `-sin²θ` -/
  hSinMul : ∀ g : Fn, Work.FTS.EllipticEst.SmoothOpen g → Work.FTS.VocabO.HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => -(Real.sin θ) ^ 2 * g z θ) ≤ C * Work.FTS.Nonlin.Xn α g

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
