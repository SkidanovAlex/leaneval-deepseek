import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.NonlinRows.pure_slot_mul_pth_le
import Submission.Work.FTS.Nonlinear.Open.Row18
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10 =====
section

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


/- **RETIRED.**  The row-10 statement under the *frozen* `Work.FTS.NonlinRows.Ctx`
(`VocabO.StarPkgo`, flat `WDMem`/`WDp` pricing of the star coefficient) is not derivable: its
`HkMem α 4 (N1sg α Φs g)` conjunct is a weighted-decay statement about `((z+1)/z)·ℛ(Φ̃_*)` that the
flat sups cannot supply (see the docstring of `NRow10_of_WlInfStar` above and
`NOTES_NRow10.md`).  The **true** form is `Work.FTS.NonlinRows.NRow10T2` in
`Submission/Work/FTS/NonlinRows/NRow10T2.lean`, proved against the upgraded
`Work.FTS.VocabO2.Ctx2` whose `StarPkgo2.RW` is exactly the missing `𝒲^{4,∞}` field. -/

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow14T2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows


end Work.FTS.NonlinRows
end
