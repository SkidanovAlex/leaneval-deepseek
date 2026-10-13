import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row10aux.Rstar_WlInf
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.NonlinRows.NRow10aux.starProdPt
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-!
# Row 10 of the §8 table, primed vocabulary: why the frozen hypothesis is insufficient

`N1sg α Φs g = 2·ℛ(Φ̃_*)·g = 2·H·((z/(1+z))·g)`,  `H := (z+1)/z · Rop α (PhiTs α Φs)`.

**What the row needs.** `HkMem α 4 (N1sg)` and `Xn α (N1sg) ≤ K·√α·Xn α g`.  Since
`R := Rop α (PhiTs α Φs) = (z/(1+z))·H`, the estimate is the product rule for the product
`H·((z/(1+z))·g)`.  The only clause of the frozen primed interface `N4Norm'` that can price a
coefficient which is *not* itself in `ℋ⁴` (`R` is not: it is `O(z)` near `0`, and a coefficient
bounded below near `z = 0` has `∫ (R·w)² = ∞`) is `wprod`, whose hypothesis is the *weighted*
norm `WlInfMem α 4 f`.  With `f := H` and `g' := (z/(1+z))·g` (which lies in `HQo α 4`
whenever `g` does, see `NRow10aux.mul_phi_Hk`) that clause yields exactly the requested rate,
because the paper's `PhiStarRegularity2` gives `WlInf α 4 H ≤ Cs·α` and `α^{-1/2}·α = √α`.
This is the route of the **proved** un-primed parent row
`Nonlinear/Pieces/RNP/row10.lean`, which consumes
`Work.FTS.Nonlin.StarPkg.R : WlInfMem α 4 H ∧ WlInf α 4 H ≤ Cs·α`.

**What the primed interface provides.** `VocabO.StarPkgo.R` prices the same coefficient only by
`D`-sup norms: `WDMem 4 H ∧ WDp 4 H ≤ Cs·α`, i.e. bounds on `D_z^bD_θ^jH` with **no** endpoint
liveness and **no** `(z+1)^k∂_z^k` control.  The only bridge, `OpenPkg.WDp_le_WlInf`, goes the
wrong way (`WDp ≤ C·WlInf`), and the de-weighting `row10aux.deweight_leibniz_sum_le` needs
precisely the `WlInf`-hypothesis `|(z+1)^{k-c}∂_z^{k-c}H| ≤ W` (`Spaces.WlInf_z_bound`) that
`WDMem` does not give: `|z^m∂_z^mH| ≤ K` only yields `(1+z)^m|∂_z^mH| ≤ K((1+z)/z)^m → ∞`.

**Why this is not merely inconvenient.**  (i) The interface cannot see the difference: for
`H' := H + κ·χ(θ)·cos(log(1/θ))` every `mixed b j`-bound and `WDp 4` change by `O(|κ|)` while
`WlInfMem α 4 H'` fails for every `κ ≠ 0` (the angular slot of `WlInf` has weight
`sin(2θ)^{-α/5}/(α+sin 2θ)`, which needs vanishing at the corners).  (ii) With only the
unweighted bound, the sharp weighted-Hardy constant `4/(γ-1)² = 400/α²` governs the mixed slots
of `HkIntegrand α 4 (R·g)` against those of `g` (`γ = 1+α/10`, and `GalClass` admits corner
profiles `sin(2θ)^{s'}·(log(1/sin 2θ))^{-3/2}` with `s' ↓ (γ-1)/2`, which satisfy `HkMem α 6`
and `BdryTraces`), giving `Xn α (N1sg) ≥ 20·Cs·Xn α g`, incompatible with `K·√α·Xn α g` as
`α → 0⁺`.  (iii) The workspace has *verified* that this pricing cannot support this conclusion
shape: `OpenPkg.wprod_field_honest` (declared false, spike family `f_ε = φ(z)·η_ε(θ)` with
`D`-suprema independent of `ε` but `HkSq α 4 (f_ε·g) ~ ε^{-α/20}`) refutes
`Xn α (f·g) ≤ C α^{-1/2}·WDp 4 f·Xn α g`.  (iv) Both reviewers of the auxiliary rate lemma
`NRow10aux.starRate` independently answered "probably wrong as stated": the `sin 2θ`-rate of
`D_θ^i(Rop α (PhiTs α Φs))`, `i ≥ 1`, is not implied by `WDMem`/`WDp`; it is available only from
`WlInfMem` (`Spaces.pz_Dth_sup_bound`, as used by `row19/helpers/dthIter_four_Rop_le`, whose
hypothesis is `StarPkg`).

**Repair (one field).**  Add to `VocabO.StarPkgo` the field that `Vocab.Nonlin.StarPkg` has,
`WlInfMem α 4 ((z+1)/z·Rop α (PhiTil α (Fstar α) Φs)) ∧ WlInf α 4 (…) ≤ Cs·α` (the paper's
`PhiStarRegularity2`), or state this row against `StarPkg`.  `NRow10_of_WlInfStar` below proves
the row verbatim from that additional hypothesis, using `N4Norm'.wprod` with
`f := StarH α Φs`, `g := (z/(1+z))·g`, together with `NRow10aux.starH_smoothOpen` and
`NRow10aux.mul_phi_Hk`.  Conversely, `NRow10aux.starProdPt` shows that the *frozen* conclusion
would follow from the single rate bound `|mixed b i (Rop α (PhiTs α Φs))| ≤ K·sin(2θ)`
(`i ≥ 1`), which is exactly the information that the `WDp`-pricing discards.
-/

/-- The weighted star coefficient `H = ((z+1)/z)·ℛ(Φ̃_*)` of the `Φ_*` node: the object whose
`𝒲^{4,∞}`-bound is the paper's `PhiStarRegularity2` and the field that the frozen primed
interface `VocabO.StarPkgo` is missing. -/
noncomputable def StarH (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ

/-- **Row 10, proved under the paper's `𝒲^{4,∞}`-pricing of the star coefficient** (the field
that `Vocab.Nonlin.StarPkg` carries and `VocabO.StarPkgo` does not).  This is the requested
statement with one additional hypothesis; it localises the gap in `NRow10` to that single
field. -/
theorem NRow10_of_WlInfStar (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : ∀ {α : ℝ} {Cs' : ℝ} {Φs : Fn}, 0 < α → α ≤ 1 →
      Work.FTS.VocabO.StarPkgo α Cs' Φs → Work.Spaces.WlInfMem α 4 (StarH α Φs) ∧
        Work.Spaces.WlInf α 4 (StarH α Φs) ≤ Cs' * α) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1sg α Φs g) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨Cφ, hCφ, hφb⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  refine ⟨2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1, by positivity, ?_⟩
  intro α g Φs Φg hCtx
  have hα : 0 < α := hCtx.hα
  have hα1 : α ≤ 1 := hCtx.hα1
  have hαα₂ : α ≤ α₂ := hCtx.hαα₂
  have hgal : Work.FTS.Nonlin.GalClass α g := hCtx.hg
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hCtx.hs
  -- the missing field, instantiated
  obtain ⟨hHmem, hHle⟩ := hstar hα hα1 hs
  have hHle' : Work.Spaces.WlInf α 4 (StarH α Φs) ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hHsm : Work.FTS.EllipticEst.SmoothOpen (StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hs
  -- the two factors of the product rule
  have hg4 : Work.FTS.VocabO.HQo α 4 g := Work.FTS.OpenPkg.galClass_HQo4 hgal
  obtain ⟨hφmem, hφbnd⟩ := hφb hα hα1 hg4
  have hφsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div ?_ ?_ ?_
      · exact contDiffOn_fst
      · exact contDiffOn_const.add contDiffOn_fst
      · intro p hp
        have hp1 : (0 : ℝ) < 1 + p.1 := by
          have := Set.mem_Ioi.mp hp.1
          linarith
        positivity
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hg4.1
    exact h1.mul h2
  -- the product rule of the primed interface, priced by the weighted norm
  have hprod := hN.wprod α ⟨hα, hαα₂⟩ (StarH α Φs)
    (fun z θ => z / (1 + z) * g z θ) hHsm hHmem ⟨hφsm, hφmem⟩
  -- the row-10 piece is `2` times that product on the open quadrant
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N1sg α Φs g z θ
        = 2 * (StarH α Φs z θ * (z / (1 + z) * g z θ)) := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Work.FTS.Nonlin.N1sg, StarH]
    field_simp
    ring
  have hSeq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1sg α Φs g)
      = Work.Spaces.HkSq α 4
          (fun z θ => 2 * (StarH α Φs z θ * (z / (1 + z) * g z θ))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hagree
  constructor
  · -- `ℋ⁴`-honesty of the row-10 piece: transfer along the open-quadrant agreement
    have hNsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) := by
      have hc2 : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => fun _ : ℝ => (2 : ℝ)) := by
        show ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (2 : ℝ))
          Work.FTS.EllipticEst.Q0
        exact contDiffOn_const
      have hR := Work.FTS.NonlinRows.NRow10aux.smoothOpen_Rop (α := α)
        (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs (α := α) (Cs := Cs) hα hα1 hs)
      have h2R := Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hc2 hR
      have hfin := Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul h2R hg4.1
      exact hfin
    have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N1sg α Φs g) z θ
          ≤ 1 * Work.Spaces.HkIntegrand α 4
              (fun z θ => 2 * (StarH α Φs z θ * (z / (1 + z) * g z θ))) z θ := by
      intro z hz θ hθ
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
      · rw [← h, one_mul, Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ,
          Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ]
      · rw [one_mul,
          ← Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4) hagree z θ h hθ.1 hθ.2]
    have hmem2 : Work.Spaces.HkMem α 4
        (fun z θ => 2 * (StarH α Φs z θ * (z / (1 + z) * g z θ))) :=
      Work.FTS.LocData.HkMem_const_mul α 4 2 hprod.1
    exact (Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 4
      (show (0 : ℝ) ≤ 1 by norm_num) hNsm hmem2 hmaj).1
  · -- the bound
    have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
        = 2 * Work.FTS.Nonlin.Xn α (fun z θ => StarH α Φs z θ * (z / (1 + z) * g z θ)) := by
      rw [show Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
            = Work.FTS.Nonlin.Xn α
                (fun z θ => 2 * (StarH α Φs z θ * (z / (1 + z) * g z θ))) from by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hSeq],
        Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α 2
          (fun z θ => StarH α Φs z θ * (z / (1 + z) * g z θ)),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [hXn]
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hbnd1 : Work.FTS.Nonlin.Xn α
          (fun z θ => StarH α Φs z θ * (z / (1 + z) * g z θ))
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cφ * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hprod.2 ?_
      have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (StarH α Φs) :=
        Work.Spaces.WlInf_nonneg α 4 _ hHmem
      have hA : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hCi.le (Real.rpow_nonneg hα.le _)
      have hB : 0 ≤ Cφ * Work.FTS.Nonlin.Xn α g := mul_nonneg hCφ.le hXg
      calc Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (StarH α Φs)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (StarH α Φs)
              * (Cφ * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_left hφbnd (mul_nonneg hA hWnn)
        _ = Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
              * Work.Spaces.WlInf α 4 (StarH α Φs) := by ring
        _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
              * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hHle' (mul_nonneg hA hB)
        _ = Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
              * (Cφ * Work.FTS.Nonlin.Xn α g) := by ring
    have hbnd2 : 2 * Work.FTS.Nonlin.Xn α
          (fun z θ => StarH α Φs z θ * (z / (1 + z) * g z θ))
        ≤ (2 * Ci * Cφ * max Cs 0) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans (mul_le_mul_of_nonneg_left hbnd1 (by norm_num)) ?_
      rw [show 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
            * (Cφ * Work.FTS.Nonlin.Xn α g))
          = 2 * Ci * Cφ * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
              * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
      exact le_of_eq (by ring)
    refine le_trans hbnd2 ?_
    have hCs : 0 ≤ max Cs 0 := le_max_right Cs 0
    have hle : 2 * Ci * Cφ * max Cs 0 ≤ 2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1 := by
      have hφ' : Cφ ≤ Cφ * Cφ + 1 := by nlinarith [hCφ.le]
      nlinarith [hCi.le, hCs, hφ', mul_nonneg hCi.le hCs, sq_nonneg Cφ]
    exact mul_le_mul_of_nonneg_right hle hS

/- **RETIRED.**  The row-10 statement under the *frozen* `Work.FTS.NonlinRows.Ctx`
(`VocabO.StarPkgo`, flat `WDMem`/`WDp` pricing of the star coefficient) is not derivable: its
`HkMem α 4 (N1sg α Φs g)` conjunct is a weighted-decay statement about `((z+1)/z)·ℛ(Φ̃_*)` that the
flat sups cannot supply (see the docstring of `NRow10_of_WlInfStar` above and
`NOTES_NRow10.md`).  The **true** form is `Work.FTS.NonlinRows.NRow10T2` in
`Submission/Work/FTS/NonlinRows/NRow10T2.lean`, proved against the upgraded
`Work.FTS.VocabO2.Ctx2` whose `StarPkgo2.RW` is exactly the missing `𝒲^{4,∞}` field. -/

end Work.FTS.NonlinRows
