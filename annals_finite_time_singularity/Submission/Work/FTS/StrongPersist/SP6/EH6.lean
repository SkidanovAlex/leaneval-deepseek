import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.SP6.FieldHints
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.Fb_EH_bound
import Submission.Work.FTS.StrongPersist.SP6.CoefBundle6
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/StrongPersist/SP6/FieldEH` — the order-six flat bound of the `EH`-field

`Work.FTS.PhiStar.EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + z∂_zY) + sin(2θ)·∂_θY` is the
`((z+1)/z)·ℛ(Φ̃_*)`-field (the `Rop`-row of the star package), expressed in terms of
`Ŷ = Ycheck α Φs`.

The task `FieldEH` asks for

`FlatW 6 (EH α Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`, with a *universal*
constant `C` (it may not depend on `Y`, and it carries the factor `(α+1)`, which is needed:
`EH` grows linearly in `α` when `∂_zY ≠ 0`).

## Route

`FlatW 6 f M` is, by `SP6.flatW6_of_F0`, the pair `F0 6 M f` and `F0 5 M (∂_θ f)`; so it
suffices to bound the flat class of `EH α Y` at order `6` and that of `∂_θ(EH α Y)` at
order `5`.

The two expressions are the *canonical forms* of `FbEHDefs.lean`,

* `EhC α Y = 2Y + ((2α)·(sin²θ · X) + sin 2θ · ∂_θY)`,  `X = Y/(z+1) + z∂_zY`
  (with `eh_EH_eq_EhC : EH α Y = EhC α Y` pointwise, no quadrant hypothesis), and
* `EhD α Y = 2∂_θY + ((2α)·(∂_θ(sin²θ)·X + sin²θ·∂_θX)
    + (∂_θ(sin 2θ)·∂_θY + D_θ(∂_θY)))`
  (with `eh_pth_EhC_eq : ∂_θ(EhC α Y) = EhD α Y` on the open quadrant).

Both are sums of *products of a coefficient function with one block*, so they are bounded by
the bilinear flat calculus `F0_mul`/`F0_add`/`F0_zpz`/`F0_Dth`/`F0_const_mul`, which is
*linear* in the block constants; the coefficient constants come from the single bundle
`CoefBundle6`.

The blocks and their constants are

| block | constant |
|---|---|
| `Y`, `∂_θY`, `z∂_zY`, `D_θ(∂_θY)` | `S = K + KY + KD` (`FlatW 7`, `Fb 6`, `F0 6`) |
| `z∂_z(∂_θY)` | `6S` (`F0_zpz` at level `5` applied to `F0 6 K (∂_θY)`) |

and every coefficient constant is `≤ M := A + 6 ≥ 6` where `A` is the `CoefBundle6`
constant.  Since each product of the calculus multiplies the constant of a *coefficient*
(which carries no `S`) by the constant of a *block* (linear in `S`), the accumulated
constants are linear in `S`, and the final bookkeeping (`ehC_const_le`, `ehD_const_le`)
dominates them by `8 · (2^45·M^40·(α+1)·S) ≤ (2^48·M^40 + 8)·(α+1)·S`, using the absorption
lemmas `mono_le_unit`, `mono_le_unit_alpha`, `eight_unit_le` of `StarPkg6Fields.lean`.

Everything here is `sorry`-free (see `declare_proven` / the axiom record).
-/

namespace Work.FTS.StrongPersist.SP6

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.PhiStar
open Work.FTS.PhiStar.CoreAux

set_option maxHeartbeats 1000000

/-- The smoothness class of the open quadrant, as a local abbreviation. -/
private abbrev Sm (f : ℝ → ℝ → ℝ) : Prop := Work.FTS.EllipticEst.SmoothOpen f

/-! ## The arithmetic of the constant

The accumulated constant of the order-`6` half is an explicit polynomial in `M`, `S`, `α`;
the next two lemmas dominate it by `(2^48·M^40 + 8)·(α+1)·S`, splitting it into at most four
"units" `2^j·u·v·w·M^c·(α or 1)·S` with `u,v,w ≤ M`, each of which is an instance of
`mono_le_unit` / `mono_le_unit_alpha`. -/

private lemma eh_unit_nonneg {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    0 ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have h2 : (0 : ℝ) ≤ 2 ^ 45 := by norm_num
  have hM40 : (0 : ℝ) ≤ M ^ 40 := pow_nonneg hM0 40
  have hα1 : (0 : ℝ) ≤ α + 1 := by linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg h2 hM40) hα1) hS

/-- The accumulated constant of the `EhC`-half is dominated by the final constant. -/
private lemma ehC_const_le {M S α : ℝ} (hM : 1 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
      ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have h1 : (2 : ℝ) ^ 1 * 1 * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 1) (c := 0)
      (u := 1) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) hM (by norm_num) hM (by norm_num) hM
  have h2 : (2 : ℝ) ^ 13 * M * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 13) (c := 0)
      (u := M) (v := M) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl
      (le_trans zero_le_one hM) le_rfl (by norm_num) hM
  have h3 : (2 : ℝ) ^ 7 * M * 1 * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 7) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl (by norm_num) hM
      (by norm_num) hM
  have h4 : (2 : ℝ) ^ 6 * M * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 6) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (le_trans zero_le_one hM) le_rfl (by norm_num) hM
      (by norm_num) hM
  have hexp : 2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
      = (2 : ℝ) ^ 1 * 1 * 1 * 1 * M ^ 0 * S
        + ((2 : ℝ) ^ 13 * M * M * 1 * M ^ 0 * α * S
            + (2 : ℝ) ^ 7 * M * 1 * 1 * M ^ 0 * α * S)
        + (2 : ℝ) ^ 6 * M * 1 * 1 * M ^ 0 * S := by ring
  have hunit := eh_unit_nonneg (M := M) (S := S) (α := α) hM hS hα
  have h8 := eight_unit_le (M := M) (S := S) (α := α) hM hS hα
  rw [hexp]
  linarith

/-- The accumulated constant of the `EhD`-half is dominated by the final constant. -/
private lemma ehD_const_le {M S α : ℝ} (hM : 1 ≤ M) (hM7 : 7 ≤ M) (hS : 0 ≤ S) (hα : 0 ≤ α) :
    2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        + (2 ^ 5 * M * S + S))
      ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S := by
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
  have h1 : (2 : ℝ) ^ 0 * 3 * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 0) (c := 0)
      (u := 3) (v := 1) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num) hM (by norm_num) hM
  have h2 : (2 : ℝ) ^ 12 * M * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 12) (c := 0)
      (u := M) (v := M) (w := 1)
      (by norm_num) (by norm_num) hM0 le_rfl hM0 le_rfl (by norm_num) hM
  have h3 : (2 : ℝ) ^ 6 * 7 * M * 1 * M ^ 0 * α * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit_alpha (M := M) (S := S) (α := α) hM hS hα (j := 6) (c := 0)
      (u := 7) (v := M) (w := 1)
      (by norm_num) (by norm_num) (by norm_num) hM7 hM0 le_rfl (by norm_num) hM
  have h4 : (2 : ℝ) ^ 5 * M * 1 * 1 * M ^ 0 * S ≤ (2 ^ 45 * M ^ 40) * (α + 1) * S :=
    mono_le_unit (M := M) (S := S) (α := α) hM hS hα (j := 5) (c := 0)
      (u := M) (v := 1) (w := 1)
      (by norm_num) (by norm_num) hM0 le_rfl (by norm_num) hM (by norm_num) hM
  have hexp : 2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        + (2 ^ 5 * M * S + S))
      = (2 : ℝ) ^ 0 * 3 * 1 * 1 * M ^ 0 * S + (2 : ℝ) ^ 5 * M * 1 * 1 * M ^ 0 * S
        + ((2 : ℝ) ^ 12 * M * M * 1 * M ^ 0 * α * S
            + (2 : ℝ) ^ 6 * 7 * M * 1 * M ^ 0 * α * S) := by ring
  have hunit := eh_unit_nonneg (M := M) (S := S) (α := α) hM hS hα
  have h8 := eight_unit_le (M := M) (S := S) (α := α) hM hS hα
  rw [hexp]
  linarith

/-! ## The field estimate -/

/-- **The order-six flat bound of the `EH`-star-field.**

Prove `FlatW 6 (EH α Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`,
`FlatW 7 Y K` (which yields `F0 6 K (∂_θY)`), `Fb 6 KY Y` and `F0 6 KD (Yblk Y)`; the
constant must stay **linear** in `K + KY + KD` (do not use `Fb_basic`, which squares).

Ingredients (import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`, module
`Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`): `CoefBundle6s`; `atomData`; the
reassociated field `EHR`/`EHD` with `ehEHR_eq`; `flatW6_of_F0`; `FlatW_mono6`;
`mono_const`. The sibling `Submission/Work/FTS/PhiStar/CoreAux/Fb_EH_bound.lean` is the same
statement at order **four** with the constant `C·A⁴(K+1)(α+1)` from `Fb 6 (A(K+1)) Y` — it
contains the `∂_θ`-identity machinery (`EhC`, `EhD`, `eh_pth_EhC_eq`) and can be adapted. -/
theorem EH6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y → Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EH α Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hsin_sq, _hcos_sq, hsin_two, hcos_two,
    _hdsq1, _hdsq2, hdsq3, _hdsq4, _hrho, hrinv⟩ := CoefBundle6
  set M : ℝ := A + 6 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  have hAM : A ≤ M := by rw [hMdef]; linarith
  have hM7 : 7 ≤ M := by rw [hMdef]; linarith
  refine ⟨2 ^ 48 * M ^ 40 + 8, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ 2 ^ 48 * M ^ 40 := mul_nonneg (by norm_num) (pow_nonneg hM0 40)
    linarith
  · intro α K KY KD Y hα hK hKY hKD hsm hY7 hFb hD
    set S : ℝ := K + KY + KD with hSdef
    have hS0 : 0 ≤ S := by rw [hSdef]; linarith
    have hKS : K ≤ S := by rw [hSdef]; linarith
    have hKYS : KY ≤ S := by rw [hSdef]; linarith
    have hKDS : KD ≤ S := by rw [hSdef]; linarith
    -- ### the coefficient bundle at the master constant `M`
    have hPhi1_6 : F0 6 M EhPhi1 := hsin_sq.mono le_rfl hAM
    have hSin2_6 : F0 6 M EhSin2 := hsin_two.mono le_rfl hAM
    have hCos2_6 : F0 6 M EhCos2 := hcos_two.mono le_rfl hAM
    have hRhoInv6 : F0 6 M EhRhoInv := hrinv.mono le_rfl hAM
    have hPhi1_5 : F0 5 M EhPhi1 := hPhi1_6.mono (by norm_num) le_rfl
    have hSin2_5 : F0 5 M EhSin2 := hSin2_6.mono (by norm_num) le_rfl
    have hRhoInv5 : F0 5 M EhRhoInv := hRhoInv6.mono (by norm_num) le_rfl
    -- ### the blocks
    have hP6 : F0 6 K (Work.Spaces.pth Y) := F0_six_pth_of_FlatW hY7
    have bY6 : F0 6 S Y := hFb.f0.mono le_rfl hKYS
    have bP6 : F0 6 S (Work.Spaces.pth Y) := hP6.mono le_rfl hKS
    have bB6 : F0 6 S (Yblk Y) := hD.mono le_rfl hKDS
    have bY5 : F0 5 S Y := bY6.mono (by norm_num) le_rfl
    have bP5 : F0 5 S (Work.Spaces.pth Y) := bP6.mono (by norm_num) le_rfl
    have bB5 : F0 5 S (Yblk Y) := bB6.mono (by norm_num) le_rfl
    -- ### the smoothness of the pieces
    have smYr : Sm (fun z θ => Y z θ * EhRhoInv z θ) := Fbq_smoothOpen_mul hsm eh_smooth_rhoinv
    have smYblk : Sm (Yblk Y) := eh_smooth_yblk hsm
    have smX : Sm (EhX Y) := eh_smooth_EhX hsm
    have smPthYr : Sm (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
      Fbq_smoothOpen_mul hsm.pth eh_smooth_rhoinv
    have smPthYblk : Sm (Yblk (Work.Spaces.pth Y)) := eh_smooth_yblk hsm.pth
    have smDX : Sm (EhDX Y) := eh_smooth_EhDX hsm
    have smDSinSq : Sm EhDSinSq := eh_smooth_dsinsq
    have smDSin2 : Sm EhDSin2 := eh_smooth_dsin2
    have smPhi1 : Sm EhPhi1 := eh_smooth_ph1
    have smSin2 : Sm EhSin2 := eh_smooth_sin2
    have sm2Y : Sm (fun z θ => 2 * Y z θ) := smoothOpen_const_mul 2 hsm
    have sm2Pth : Sm (fun z θ => 2 * Work.Spaces.pth Y z θ) := smoothOpen_const_mul 2 hsm.pth
    have sm2aPhi1X : Sm (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) :=
      smoothOpen_const_mul (2 * α) (Fbq_smoothOpen_mul smPhi1 smX)
    have smSin2P : Sm (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      Fbq_smoothOpen_mul smSin2 hsm.pth
    have smDSinSqX : Sm (fun z θ => EhDSinSq z θ * EhX Y z θ) := Fbq_smoothOpen_mul smDSinSq smX
    have smPhi1DX : Sm (fun z θ => EhPhi1 z θ * EhDX Y z θ) := Fbq_smoothOpen_mul smPhi1 smDX
    have smDSin2P : Sm (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) :=
      Fbq_smoothOpen_mul smDSin2 hsm.pth
    have smDthP : Sm (Work.Spaces.Dth (Work.Spaces.pth Y)) := hsm.pth.Dth
    -- ### level `6`: the canonical form `EhC` of `EH`
    have hX6nn : (0 : ℝ) ≤ 2 ^ 6 * S * M + S := by nlinarith [hS0, hM0]
    have hYr6 : F0 6 (2 ^ 6 * S * M) (fun z θ => Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm eh_smooth_rhoinv bY6 hRhoInv6
    have hX6 : F0 6 (2 ^ 6 * S * M + S) (EhX Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add smYr smYblk hYr6 bB6)
    have hPhi1X6 : F0 6 (2 ^ 6 * M * (2 ^ 6 * S * M + S))
        (fun z θ => EhPhi1 z θ * EhX Y z θ) :=
      F0_mul hM0 hX6nn smPhi1 smX hPhi1_6 hX6
    have h2aPhi1X6 : F0 6 (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)))
        (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ)) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 * α) hPhi1X6
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hSin2P6 : F0 6 (2 ^ 6 * M * S) (fun z θ => EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_mul hM0 hS0 smSin2 hsm.pth hSin2_6 bP6
    have hInner6 : F0 6 (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
        (fun z θ => (2 * α) * (EhPhi1 z θ * EhX Y z θ) + EhSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_add sm2aPhi1X smSin2P h2aPhi1X6 hSin2P6
    have h2Y6 : F0 6 (2 * S) (fun z θ => 2 * Y z θ) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) bY6
      simpa using h
    have hEhC6 : F0 6 (2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S))
        (EhC α Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add sm2Y (smoothOpen_add sm2aPhi1X smSin2P) h2Y6 hInner6)
    have hEHf0 : F0 6 (2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S))
        (Work.FTS.PhiStar.EH α Y) :=
      F0_congr (fun z θ _ _ _ => eh_EH_eq_EhC z θ) hEhC6
    -- ### level `5`: the canonical form `EhD` of `∂_θ(EH)`
    have hBP5 : F0 5 (6 * S) (Yblk (Work.Spaces.pth Y)) := by
      have h := F0_zpz (n := 5) (K := K) hK hsm.pth hP6
      have h6 : ((↑(5 : ℕ) : ℝ) + 1) * K = 6 * K := by norm_num
      rw [h6] at h
      exact h.mono le_rfl (by linarith)
    have hDthP5 : F0 5 S (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
      (F0_Dth (n := 5) hP6).mono le_rfl hKS
    have hX5nn : (0 : ℝ) ≤ 2 ^ 5 * S * M + S := by nlinarith [hS0, hM0]
    have hDX5nn : (0 : ℝ) ≤ 2 ^ 5 * S * M + 6 * S := by nlinarith [hS0, hM0]
    have hYr5 : F0 5 (2 ^ 5 * S * M) (fun z θ => Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm eh_smooth_rhoinv bY5 hRhoInv5
    have hX5 : F0 5 (2 ^ 5 * S * M + S) (EhX Y) :=
      F0_congr (fun z θ _ _ _ => rfl) (F0_add smYr smYblk hYr5 bB5)
    have hDSinSq5 : F0 5 M EhDSinSq := eh_F0_dsinsq hSin2_5
    have hDSinSqX5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + S))
        (fun z θ => EhDSinSq z θ * EhX Y z θ) :=
      F0_mul hM0 hX5nn smDSinSq smX hDSinSq5 hX5
    have hPthYr5 : F0 5 (2 ^ 5 * S * M) (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
      F0_mul hS0 hM0 hsm.pth eh_smooth_rhoinv bP5 hRhoInv5
    have hDX5 : F0 5 (2 ^ 5 * S * M + 6 * S) (EhDX Y) :=
      F0_congr (fun z θ _ _ _ => rfl) (F0_add smPthYr smPthYblk hPthYr5 hBP5)
    have hPhi1DX5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        (fun z θ => EhPhi1 z θ * EhDX Y z θ) :=
      F0_mul hM0 hDX5nn smPhi1 smDX hPhi1_5 hDX5
    have hSum5 : F0 5 (2 ^ 5 * M * (2 ^ 5 * S * M + S) + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S))
        (fun z θ => EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ) :=
      F0_add smDSinSqX smPhi1DX hDSinSqX5 hPhi1DX5
    have h2aSum5 : F0 5 (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)))
        (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 * α) hSum5
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α)] at h
      exact h
    have hDSin2_5 : F0 5 M EhDSin2 := by
      have hb : F0 5 A (fun _ θ : ℝ => deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) :=
        hdsq3.mono (by norm_num) le_rfl
      refine F0_congr (f := EhDSin2)
        (g := fun _ θ : ℝ => deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ) ?_
        (hb.mono le_rfl hAM)
      intro z θ _ _ _
      show 2 * Real.cos (2 * θ) = deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ
      rw [deriv_sin_two]
    have hDSin2P5 : F0 5 (2 ^ 5 * M * S) (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ) :=
      F0_mul hM0 hS0 smDSin2 hsm.pth hDSin2_5 bP5
    have hTail5 : F0 5 (2 ^ 5 * M * S + S)
        (fun z θ => EhDSin2 z θ * Work.Spaces.pth Y z θ
          + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
      F0_add smDSin2P smDthP hDSin2P5 hDthP5
    have hInner5 : F0 5 (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S))
        (fun z θ => (2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
          + (EhDSin2 z θ * Work.Spaces.pth Y z θ + Work.Spaces.Dth (Work.Spaces.pth Y) z θ)) :=
      F0_add (smoothOpen_const_mul (2 * α) (smoothOpen_add smDSinSqX smPhi1DX))
        (smoothOpen_add smDSin2P smDthP) h2aSum5 hTail5
    have h2P5 : F0 5 (2 * S) (fun z θ => 2 * Work.Spaces.pth Y z θ) := by
      have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) bP5
      simpa using h
    have hEhD5 : F0 5 (2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S)))
        (EhD α Y) :=
      F0_congr (fun z θ _ _ _ => rfl)
        (F0_add sm2Pth
          (smoothOpen_add (smoothOpen_const_mul (2 * α) (smoothOpen_add smDSinSqX smPhi1DX))
            (smoothOpen_add smDSin2P smDthP)) h2P5 hInner5)
    have hEHfd : F0 5 (2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S)))
        (Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) :=
      F0_congr (fun z θ hz hθ hθ' => by
        rw [pth_congr_Q0 (f := Work.FTS.PhiStar.EH α Y) (g := EhC α Y)
          (fun z θ _ _ _ => eh_EH_eq_EhC z θ) z θ hz hθ hθ']
        exact eh_pth_EhC_eq hsm z θ hz hθ hθ') hEhD5
    -- ### conclusion
    have hC1 : 2 * S + (2 * α * (2 ^ 6 * M * (2 ^ 6 * S * M + S)) + 2 ^ 6 * M * S)
        ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S :=
      ehC_const_le (M := M) (S := S) (α := α) hM1 hS0 hα
    have hEHf0' : F0 6 ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S) (Work.FTS.PhiStar.EH α Y) :=
      hEHf0.mono le_rfl hC1
    have hC2 : 2 * S + (2 * α * (2 ^ 5 * M * (2 ^ 5 * S * M + S)
          + 2 ^ 5 * M * (2 ^ 5 * S * M + 6 * S)) + (2 ^ 5 * M * S + S))
        ≤ (2 ^ 48 * M ^ 40 + 8) * (α + 1) * S :=
      ehD_const_le (M := M) (S := S) (α := α) hM1 hM7 hS0 hα
    have hEHfd' : F0 5 ((2 ^ 48 * M ^ 40 + 8) * (α + 1) * S)
        (Work.Spaces.pth (Work.FTS.PhiStar.EH α Y)) :=
      hEHfd.mono le_rfl hC2
    exact flatW6_of_F0 hEHf0' hEHfd'

end Work.FTS.StrongPersist.SP6
