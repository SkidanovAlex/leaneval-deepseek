import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.box_pair_flat_integral
import Submission.Work.BoseBoxFock.integrableOn_box_pair_mean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.abox_pair_split_integral`

The pair-splitting identity for the centred `n`-particle box `abox n ℓ = (Λ(ℓ))ⁿ`,
`Λ(ℓ) = acube ℓ = [−ℓ/2, ℓ/2]³`: for `i ≠ j`, a measurable `G` bounded on the box and any
measurable kernel `k` bounded by `Ck`,

    ∫_{x ∈ abox} ∫_{y ∈ acube} ∫_{u ∈ acube} G (x[i ↦ y][j ↦ u]) · k y u
      = (ℓ³)² ∫_{x ∈ abox} G x · k (x i) (x j) .

The content is that the two distinguished coordinates are integrated over the *same* side-`ℓ`
cube in which they live, so that `y = x i`, `u = x j` is a measure-preserving substitution and the
two cube integrals contribute exactly the factor `(ℓ³)²`.

## Route

Write `n = p + 2`, `j' : Fin (p+1)` with `i.succAbove j' = j`.  The double peel
`Submission.BoseGases.abox_integral_peel2` (Fubini along the measure-preserving identification of
the box with the product of the two slot cubes and the remaining box) reduces both sides to
iterated integrals over `abox p ℓ × acube ℓ × acube ℓ`:

* LHS: the inner integrand `∫_{y'}∫_u G (x[i↦y'][j↦u]) k y' u` is constant in the two outer cube
  variables, so those integrals contribute `(ℓ³)²` (`integral_const_acube` twice), leaving
  `(ℓ³)² ∫_{r2}∫_{y}∫_{u} w y u r2` with `w y u r2 = G (ins2 i j' y u r2) * k y u`;
* RHS: `(ins2 i j' y z r2) i = y` and `(ins2 i j' y z r2) j = z`, so the peeled integrand is
  exactly `w y z r2`.

Both are `(ℓ³)² ∫ w` over the product measure on `acube ℓ × acube ℓ × abox p ℓ` by the Fubini
identity `box_pair_flat_integral`.  Integrability comes from the boundedness of `G` and `k` on the
(finite-measure) box and the parametric-integrability lemma `integrableOn_box_pair_mean`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The double insertion `ins2` of two cube points into a box configuration stays in the box. -/
lemma ins2_mem_abox {p : ℕ} {ℓ : ℝ} {i : Fin (p + 2)} (j' : Fin (p + 1)) {y z : E3}
    (hy : y ∈ acube ℓ) (hz : z ∈ acube ℓ) {r2 : X p} (hr2 : r2 ∈ abox p ℓ) :
    ins2 i j' y z r2 ∈ abox (p + 2) ℓ := by
  intro k
  dsimp [ins2]
  by_cases hk : k = i
  · subst hk
    rw [kc_insN_apply_same]
    exact hy
  · by_cases hkj : k = i.succAbove j'
    · subst hkj
      rw [kc_insN_apply_succ, kc_insN_apply_same]
      exact hz
    · rcases Fin.exists_succAbove_eq hk with ⟨l, hl⟩
      rw [← hl]
      have hlne : l ≠ j' := by
        intro hlj
        exact hkj (by rw [← hl, hlj])
      rw [kc_insN_apply_succ]
      rcases Fin.exists_succAbove_eq hlne with ⟨m, hm⟩
      rw [← hm]
      rw [kc_insN_apply_succ]
      exact hr2 m

theorem abox_pair_split_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {G : Submission.BoseGases.X n → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |G x| ≤ CG)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : Measurable (Function.uncurry k)) {Ck : ℝ} (hkb : ∀ y u, |k y u| ≤ Ck) :
    (∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
        ∫ u in Submission.BoseGases.acube ℓ,
          G (Function.update (Function.update x i y) j u) * k y u)
      = (ℓ ^ 3) * (ℓ ^ 3)
          * ∫ x in Submission.BoseGases.abox n ℓ, G x * k (x i) (x j) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    cases m with
    | zero =>
      exfalso
      have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
      have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
      exact hij (Fin.ext (hi0.trans hj0.symm))
    | succ p =>
      classical
      rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
      have hCG : 0 ≤ CG := le_trans (abs_nonneg _) (hGb 0 (zero_mem_abox hℓ.le))
      have hCk : 0 ≤ Ck := le_trans (abs_nonneg _) (hkb 0 0)
      let w : E3 → E3 → X p → ℝ := fun y u r2 => G (ins2 i j' y u r2) * k y u
      -- (1) the flat kernel is measurable
      have hw_meas : Measurable (Function.uncurry (Function.uncurry w)) := by
        show Measurable (fun q : (E3 × E3) × X p =>
          G ((kcInsN (p + 1) i) (q.1.1, (kcInsN p j') (q.1.2, q.2))) * k q.1.1 q.1.2)
        have hpair2 : Measurable (fun q : (E3 × E3) × X p => (q.1.2, q.2)) :=
          Measurable.prod (by fun_prop : Measurable fun q : (E3 × E3) × X p => q.1.2)
            (by fun_prop : Measurable fun q : (E3 × E3) × X p => q.2)
        have hpair : Measurable (fun q : (E3 × E3) × X p =>
            (q.1.1, (kcInsN p j') (q.1.2, q.2))) :=
          Measurable.prod (by fun_prop : Measurable fun q : (E3 × E3) × X p => q.1.1)
            ((kcInsN p j').measurable.comp hpair2)
        have hkik : Measurable (fun q : (E3 × E3) × X p => k q.1.1 q.1.2) :=
          hkm.comp measurable_fst
        exact (hGm.comp ((kcInsN (p + 1) i).measurable.comp hpair)).mul hkik
      -- (2) the flat kernel is bounded on the box
      have hw_bd : ∀ a b r, a ∈ acube ℓ → b ∈ acube ℓ → r ∈ abox p ℓ → |w a b r| ≤ CG * Ck := by
        intro a b r ha hb hr
        show |G (ins2 i j' a b r) * k a b| ≤ CG * Ck
        rw [abs_mul]
        exact mul_le_mul (hGb _ (ins2_mem_abox j' ha hb hr)) (hkb a b) (abs_nonneg _) hCG
      have hflat := box_pair_flat_integral (p := p) (ℓ := ℓ) hℓ
        (w := w) hw_meas hw_bd
      -- (3) the partner kernel is integrable on the box
      have htest : Measurable (fun x : X (p + 2) => (x i, x j)) :=
        Measurable.prod (measurable_pi_apply i) (measurable_pi_apply j)
      have hkij : Measurable (fun x : X (p + 2) => k (x i) (x j)) := hkm.comp htest
      have hΦ_int : IntegrableOn (fun x : X (p + 2) => G x * k (x i) (x j))
          (abox (p + 2) ℓ) volume := by
        refine IntegrableOn.of_bound (abox_lt_top (p + 2) ℓ hℓ.le) ?_ (CG * Ck) ?_
        · exact (hGm.mul hkij).aestronglyMeasurable
        · rw [ae_restrict_iff' (abox_measurable (p + 2) ℓ)]
          refine Filter.Eventually.of_forall fun x hx => ?_
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hGb x hx) (hkb (x i) (x j)) (abs_nonneg _) hCG
      -- (4) the LHS
      have hφ_int : IntegrableOn (fun x : X (p + 2) =>
            ∫ y in acube ℓ, ∫ u in acube ℓ,
              G (Function.update (Function.update x i y) j u) * k y u)
          (abox (p + 2) ℓ) volume :=
        integrableOn_box_pair_mean (ℓ := ℓ) (i := i) (j := j) hℓ hij hGm hGb hkm hkb
      have hpeelL := abox_integral_peel2 (p := p) (i := i) (j' := j')
        (F := fun x : X (p + 2) =>
          ∫ y in acube ℓ, ∫ u in acube ℓ,
            G (Function.update (Function.update x i y) j u) * k y u) hφ_int
      have hpeelL' : (∫ x in abox (p + 2) ℓ, ∫ y in acube ℓ, ∫ u in acube ℓ,
            G (Function.update (Function.update x i y) j u) * k y u)
          = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              (∫ y' in acube ℓ, ∫ u in acube ℓ,
                G (Function.update (Function.update (ins2 i j' y z r2) i y') j u) * k y' u) := by
        simpa only [ins2] using hpeelL
      have hupd : ∀ (y z y' u : E3) (r2 : X p),
          Function.update (Function.update (ins2 i j' y z r2) i y') j u
            = ins2 i j' y' u r2 := by
        intro y z y' u r2
        rw [ins2_update_i i j' y y' z r2, ← hj', ins2_update_succ i j' y' z u r2]
      have hpoint : ∀ (y z : E3) (r2 : X p),
          (∫ y' in acube ℓ, ∫ u in acube ℓ,
              G (Function.update (Function.update (ins2 i j' y z r2) i y') j u) * k y' u)
            = ∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2 := by
        intro y z r2
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro y'
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro u
        show G (Function.update (Function.update (ins2 i j' y z r2) i y') j u) * k y' u
          = w y' u r2
        rw [hupd y z y' u r2]
      have hstep2 : (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))
            = (ℓ ^ 3) * (ℓ ^ 3)
              * ∫ r2 in abox p ℓ, (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2) := by
        have h1 : ∀ r2 : X p, (∫ z in acube ℓ, ∫ y in acube ℓ,
              (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))
            = ℓ ^ 3 * (ℓ ^ 3 * (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2)) := by
          intro r2
          have hinner : (∫ y in acube ℓ, (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))
              = ℓ ^ 3 * (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2) :=
            integral_const_acube hℓ
          rw [hinner]
          rw [integral_const_acube hℓ]
        calc (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
                (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))
            = ∫ r2 in abox p ℓ,
                (ℓ ^ 3 * (ℓ ^ 3 * (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))) :=
              integral_congr_ae (Filter.Eventually.of_forall h1)
          _ = ∫ r2 in abox p ℓ,
                (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2) * (ℓ ^ 3 * ℓ ^ 3) :=
              integral_congr_ae (Filter.Eventually.of_forall fun r2 => by ring)
          _ = (∫ r2 in abox p ℓ, (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2))
                * (ℓ ^ 3 * ℓ ^ 3) := by rw [integral_mul_const]
          _ = (ℓ ^ 3) * (ℓ ^ 3)
                * ∫ r2 in abox p ℓ, (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2) := by ring
      have hstep1 : (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
            (∫ y' in acube ℓ, ∫ u in acube ℓ,
              G (Function.update (Function.update (ins2 i j' y z r2) i y') j u) * k y' u))
          = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              (∫ y' in acube ℓ, ∫ u in acube ℓ, w y' u r2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro r2
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro z
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro y
        exact hpoint y z r2
      have hLHS_eq : (∫ x in abox (p + 2) ℓ, ∫ y in acube ℓ, ∫ u in acube ℓ,
            G (Function.update (Function.update x i y) j u) * k y u)
          = (ℓ ^ 3) * (ℓ ^ 3)
            * ∫ q : (E3 × E3) × X p, w q.1.1 q.1.2 q.2
                ∂(((volume : Measure E3).restrict (acube ℓ)).prod
                    ((volume : Measure E3).restrict (acube ℓ))).prod
                  ((volume : Measure (X p)).restrict (abox p ℓ)) := by
        rw [hpeelL', hstep1, hstep2, hflat.1]
      -- (5) the RHS
      have hpeelR := abox_integral_peel2 (p := p) (i := i) (j' := j')
        (F := fun x : X (p + 2) => G x * k (x i) (x j)) hΦ_int
      have hpeelR' : (∫ x in abox (p + 2) ℓ, G x * k (x i) (x j))
          = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              G (ins2 i j' y z r2) * k ((ins2 i j' y z r2) i) ((ins2 i j' y z r2) j) := by
        simpa only [ins2] using hpeelR
      have hins2_j : ∀ (y z : E3) (r2 : X p), (ins2 i j' y z r2) j = z := by
        intro y z r2
        rw [← hj']
        exact ins2_apply_succ i j' y z r2
      have hRHS_eq : (∫ x in abox (p + 2) ℓ, G x * k (x i) (x j))
          = ∫ q : (E3 × E3) × X p, w q.1.1 q.1.2 q.2
              ∂(((volume : Measure E3).restrict (acube ℓ)).prod
                  ((volume : Measure E3).restrict (acube ℓ))).prod
                ((volume : Measure (X p)).restrict (abox p ℓ)) := by
        rw [hpeelR']
        have hstep : (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
              G (ins2 i j' y z r2) * k ((ins2 i j' y z r2) i) ((ins2 i j' y z r2) j))
            = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, w y z r2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro r2
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro z
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro y
          show G (ins2 i j' y z r2) * k ((ins2 i j' y z r2) i) ((ins2 i j' y z r2) j)
            = w y z r2
          rw [ins2_apply_i i j' y z r2, hins2_j y z r2]
        rw [hstep, hflat.2]
      rw [hLHS_eq, hRHS_eq]

end Work.BoseBoxFock
