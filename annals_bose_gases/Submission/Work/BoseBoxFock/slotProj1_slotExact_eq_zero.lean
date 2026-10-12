import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj1_slotExact_eq_zero` — the sectors are orthogonal to the
non-occupied slots

The `S`-sector `slotExact e S Φ` (`FibreProjDefs.lean`) is the inclusion–exclusion form of the part
of `Φ` whose slots in `S` lie in `V = span{e l}` and whose slots *outside* `S` lie in `Vᗮ`.  The
point of the sector decomposition is that the slot projections behave like the projections of the
commuting family `Q_i = P_{{i}}`: for a slot `i ∉ S` the sector is killed by `Q_i`, i.e.

`slotProj1 e i (slotExact e S Φ) = 0`   (`i ∉ S`),

the one-slot-projection form of the vanishing of the mixed sectors (`sx_zero`/`slotExact_comp`).

The proof is the "peel one slot" argument, organised around the paired form of the sector
(`SecAux.slotExact_pair_form`): for `i ∉ S`,

`slotExact e S Φ = ∑_{T ⊇ S, i ∉ T} (-1)^{|T|−|S|} • (P_T Φ − P_{T ∪ {i}} Φ)`,

and each pair vanishes after `Q_i` because

* `Q_i (P_T Φ) = P_{T ∪ {i}} Φ` (the peel lemma `slotInt_peelMB`, `i ∉ T`), and
* `Q_i (P_{T ∪ {i}} Φ) = P_{T ∪ {i}} Φ` (absorption of an already projected slot,
  `slotProj1_slotInt_self`, `i ∈ T ∪ {i}`).

The two elementary auxiliary lemmas below push `slotProj1` through a finite linear combination
(`slotProj1_finset_sum`) and through a pointwise difference (`slotProj1_sub_apply`); both are the
one-slot analogues of `SecAux.slotProj_finset_sum`, the integrability input being
`integrable_mul_of_continuous_hasCompactSupport_of_bounded` (a continuous compactly supported
kernel times a bounded measurable state).
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **Linearity of `slotProj1 e i` over a finite `ℂ`-linear combination of states.**  This is the
one-slot analogue of `SecAux.slotProj_finset_sum`: the kernel `w ↦ PV e (x i) w` is continuous with
compact support, each `Ψ U` is measurable and bounded, so every summand of the integrand is
integrable and the Bochner integral commutes with the finite sum. -/
theorem slotProj1_finset_sum {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l)) (i : Fin n)
    (s : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℂ)
    (Ψ : Finset (Fin n) → (Fin n → Ω) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    slotProj1 e i (fun x => ∑ U ∈ s, c U • Ψ U x)
      = fun x => ∑ U ∈ s, c U • slotProj1 e i (Ψ U) x := by
  funext x
  have hInt : ∀ U ∈ s,
      Integrable (fun w : Ω => c U • (PV e (x i) w * Ψ U (Function.update x i w))) volume := by
    intro U _
    have hb : ∃ C, ∀ w : Ω, ‖Ψ U (Function.update x i w)‖ ≤ C :=
      (hΨb U).imp (fun C hC w => hC _)
    exact (integrable_mul_of_continuous_hasCompactSupport_of_bounded
      (continuous_PV_snd e he (x i)) (hasCompactSupport_PV_snd e hec (x i))
      ((hΨm U).comp (measurable_update (f := x) (a := i))).aestronglyMeasurable hb).const_mul (c U)
  have hpt : ∀ w : Ω, PV e (x i) w * (∑ U ∈ s, c U • Ψ U (Function.update x i w))
      = ∑ U ∈ s, c U • (PV e (x i) w * Ψ U (Function.update x i w)) := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [slotProj1]
  trans ∫ w : Ω, ∑ U ∈ s, c U • (PV e (x i) w * Ψ U (Function.update x i w))
  · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  trans ∑ U ∈ s, ∫ w : Ω, c U • (PV e (x i) w * Ψ U (Function.update x i w))
  · exact integral_finsetSum _ hInt
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [integral_smul, slotProj1]

/-- **Linearity of `slotProj1 e i` over a pointwise difference.**  The integrand splits as
`PV e (x i) w * (F − G)(update x i w) = PV e (x i) w * F (update x i w)
 − PV e (x i) w * G (update x i w)`, and both pieces are integrable (continuous compactly
supported kernel times a bounded measurable state). -/
theorem slotProj1_sub_apply {m n : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l)) (i : Fin n) (F G : (Fin n → Ω) → ℂ)
    (hFm : Measurable F) (hFb : ∃ C, ∀ y, ‖F y‖ ≤ C)
    (hGm : Measurable G) (hGb : ∃ C, ∀ y, ‖G y‖ ≤ C) (x : Fin n → Ω) :
    slotProj1 e i (fun y => F y - G y) x = slotProj1 e i F x - slotProj1 e i G x := by
  have hFb' : ∃ C, ∀ w : Ω, ‖F (Function.update x i w)‖ ≤ C := hFb.imp (fun C hC w => hC _)
  have hGb' : ∃ C, ∀ w : Ω, ‖G (Function.update x i w)‖ ≤ C := hGb.imp (fun C hC w => hC _)
  have hIntF : Integrable (fun w : Ω => PV e (x i) w * F (Function.update x i w)) volume :=
    integrable_mul_of_continuous_hasCompactSupport_of_bounded (continuous_PV_snd e he (x i))
      (hasCompactSupport_PV_snd e hec (x i))
      ((hFm.comp (measurable_update (f := x) (a := i))).aestronglyMeasurable) hFb'
  have hIntG : Integrable (fun w : Ω => PV e (x i) w * G (Function.update x i w)) volume :=
    integrable_mul_of_continuous_hasCompactSupport_of_bounded (continuous_PV_snd e he (x i))
      (hasCompactSupport_PV_snd e hec (x i))
      ((hGm.comp (measurable_update (f := x) (a := i))).aestronglyMeasurable) hGb'
  have hpt : ∀ w : Ω, PV e (x i) w * (F (Function.update x i w) - G (Function.update x i w))
      = PV e (x i) w * F (Function.update x i w)
        - PV e (x i) w * G (Function.update x i w) := fun w => by ring
  rw [slotProj1]
  trans ∫ w : Ω, (PV e (x i) w * F (Function.update x i w)
        - PV e (x i) w * G (Function.update x i w))
  · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  · rw [integral_sub hIntF hIntG]
    rfl

/-- **The slots outside the sector are in `Vᗮ`**: the one-slot projection `Q_i = P_{{i}}` kills the
sector `S` as soon as `i ∉ S`.

`SecAux.slotExact_pair_form` writes `slotExact e S Φ` as the sum over the supersets `T ⊇ S` of `S`
that avoid `i` of the pairs `(-1)^{|T|−|S|} • (P_T Φ − P_{T ∪ {i}} Φ)`; for such a `T` the peel
lemma (`slotInt_peelMB`) gives `Q_i (P_T Φ) = P_{T ∪ {i}} Φ` and the absorption
(`slotProj1_slotInt_self`) gives `Q_i (P_{T ∪ {i}} Φ) = P_{T ∪ {i}} Φ`, so every pair maps to
`P_{T ∪ {i}} Φ − P_{T ∪ {i}} Φ = 0`. -/
theorem slotProj1_slotExact_eq_zero {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e i (Work.BoseBoxFock.slotExact e S Φ) = 0 := by
  classical
  -- the paired (and `i`-avoiding) form of the sector
  rw [SecAux.slotExact_pair_form e S i hi Φ]
  -- expose the summands as functions of the configuration, so that linearity of `slotProj1`
  -- (a finite sum of *functions*) is applicable
  rw [show (∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T),
        (-1 : ℂ) ^ (T.card - S.card) • (slotProj e T Φ - slotProj e (insert i T) Φ))
      = (fun x => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T),
        (-1 : ℂ) ^ (T.card - S.card) •
          (slotProj e T Φ x - slotProj e (insert i T) Φ x)) from by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply]]
  -- linearity of the one-slot projection
  rw [slotProj1_finset_sum e he hec i
      (Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T ∧ i ∉ T))
      (fun T => (-1 : ℂ) ^ (T.card - S.card))
      (fun T x => slotProj e T Φ x - slotProj e (insert i T) Φ x)
      (fun T => (sx_proj_mb e he hec T Φ hΦm hΦb).1.sub
        (sx_proj_mb e he hec (insert i T) Φ hΦm hΦb).1)
      (fun T => by
        obtain ⟨C1, h1⟩ := (sx_proj_mb e he hec T Φ hΦm hΦb).2
        obtain ⟨C2, h2⟩ := (sx_proj_mb e he hec (insert i T) Φ hΦm hΦb).2
        exact ⟨C1 + C2, fun x => (norm_sub_le _ _).trans (add_le_add (h1 x) (h2 x))⟩)]
  -- every pair of the sum is annihilated by the extra slot projection
  funext y
  refine Finset.sum_eq_zero (fun T hT => ?_)
  have hiT : i ∉ T := (Finset.mem_filter.mp hT).2.2
  have h1 : slotProj1 e i (slotProj e T Φ) = slotProj e (insert i T) Φ := by
    have hp := slotInt_peelMB e he hec (S := T) (i := i) hiT Φ hΦm hΦb
    rw [Finset.union_singleton] at hp
    exact hp.symm
  have h2 : slotProj1 e i (slotProj e (insert i T) Φ) = slotProj e (insert i T) Φ :=
    slotProj1_slotInt_self e he hec horth Φ hΦm hΦb (U := insert i T) (u := i)
      (Finset.mem_insert_self i T)
  rw [slotProj1_sub_apply e he hec i (slotProj e T Φ) (slotProj e (insert i T) Φ)
    (sx_proj_mb e he hec T Φ hΦm hΦb).1 (sx_proj_mb e he hec T Φ hΦm hΦb).2
    (sx_proj_mb e he hec (insert i T) Φ hΦm hΦb).1
    (sx_proj_mb e he hec (insert i T) Φ hΦm hΦb).2 y]
  rw [h1, h2, sub_self, smul_zero]

end Work.BoseBoxFock
