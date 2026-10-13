/-
# `E1Parts/RadA` — the radial majorant of `E1` is integrable

For `f ∈ CoerAdm α` and `j ≤ 3`,

  `∫_0^∞ (D_z^j (radA α f)(z))² w(z)² dz < ∞`,

which is the radial input of the `ℋ^n`-membership of the transfer defect
`E1 α f = (D_θΓ) · radA α f`.  The proof chains

* `RadAId.RadA_Efun_eq` — the integrand equals the explicit expression `Efun` on `(0,∞)`;
* `RadABnd.Efun_le_Maj` — `Efun` is dominated by the majorant `Maj`;
* `RadAPieces` — `Maj` is integrable (`∑_c (D_z^c (L₁₂ f))²w²` for `c ≤ 3` is
  `RadL12.L12f_DzdIter_sq_w_sq_integrable` and `(D_z^j (ampB α))²w²` is
  `E2pkg.dzdIter_coeff_bound`), using `Integrable.mono'` with
  `RadABnd.continuousOn_Efun` for the measurability.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAId
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadABnd
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem RadA (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    ∀ j : ℕ, j ≤ 3 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  obtain ⟨K, hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_dzdIter_bound α hα hα1
  intro j hj
  have hMaj_int : IntegrableOn (Maj α f j K) (Set.Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun z : ℝ => ∑ c ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      integrable_finsetSum _ (fun c hc =>
        L12f_DzdIter_sq_w_sq_integrable_Ioi α hα hα1 hf c
          (by have := Finset.mem_range.mp hc; omega))
    have h2 : IntegrableOn (fun z : ℝ =>
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) :=
      ampB_DzdIter_sq_w_sq_integrable_Ioi α hα hα1 (c := j) (by omega)
    have hfun : Maj α f j K = fun z : ℝ =>
        2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
          * (∑ c ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
          * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
              * (Work.Spaces.w z) ^ 2) := by
      funext z; rw [Maj_eq]
    rw [hfun]
    exact (h1.const_mul _).add (h2.const_mul _)
  have hEfun_int : Integrable (Efun α f j) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Integrable.mono' hMaj_int
      ((continuousOn_Efun α hα hα1 f hf hj).aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Efun_nonneg α f j z)]
        exact Efun_le_Maj α hα hα1 f hf hj hKnn hKbd z hz))
  have hF_int : Integrable
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.IntegrableOn.congr_fun hEfun_int
      (fun z hz => (RadA_Efun_eq α hα hα1 f hf hj z hz).symm) measurableSet_Ioi
  exact MeasureTheory.IntegrableOn.congr_set_ae hF_int
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm

end Work.FTS.CoercivityFix.Transfer.E1Parts
