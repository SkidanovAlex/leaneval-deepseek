import ChallengeDeps
import Submission.Work.BoseGateFS.chat_W1fun_lipschitz
import Submission.Work.BoseGateFS.radialCut_lip
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseGateFS.honW1_lip` — the Lipschitz row of the UV-cut `ζ_Λ Ŵ₁`

`ζ_Λ(p) = f_u(‖p‖/Λ)` is the `Λ`-cut of FS's low-momentum localisation (`fu.f` is a
`Work.BoseBoxFix.LowCut` profile) and `Ŵ₁ = chat (W1fun v h ℓ)` is the renormalised
scattering kernel in momentum space (`Work.BoseFixR.chat`).  The row proved here is

    |ζ_Λ(p)Ŵ₁(p) − ζ_Λ(q)Ŵ₁(q)| ≤ (16πR + 16πM) · (a v) · ‖p − q‖      for all `p, q`,

with `M` any bound on `|(f_u)'|`: the `hW1grad` row of the honest gate
(`FINDINGS_honestRows.md` §3), absolute in the frequency.

## Route

Insert and subtract the cross term and split:

    |ζ_p c_p − ζ_q c_q| = |ζ_p (c_p − c_q) + (ζ_p − ζ_q) c_q|
                        ≤ |ζ_p||c_p − c_q| + |ζ_p − ζ_q||c_q|,

then use the three rows

* `|ζ_p| ≤ 1` and `|ζ_p − ζ_q| ≤ M‖p − q‖` (`radialCut_lip`),
* `|c_p − c_q| ≤ 16πR(a v)‖p − q‖` (`chat_W1fun_lipschitz`),
* `|c_q| ≤ 16π(a v)` (FS `eq:WSestimate`, `W1hat_abs_le`).

Each product costs one factor of the total dilation `16π(a v)`, and
`(16πR + 16πM)(a v) = 16πR(a v) + 16π(a v)·M` by distributivity, with no sign hypothesis
on `a v` needed beyond what the three rows already provide.
-/

namespace Work.BoseGateFS

theorem honW1_lip {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (fu : Work.BoseBoxFix.LowCut) {R M ℓ Λ : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hζ' : ∀ s : ℝ, |deriv fu.f s| ≤ M) (hℓ : 0 < ℓ) (hΛ : 1 ≤ Λ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∀ p q : EuclideanSpace ℝ (Fin 3),
      |fu.f (‖p‖ / Λ) * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - fu.f (‖q‖ / Λ) * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
      ≤ (16 * Real.pi * R + 16 * Real.pi * M) * _root_.BoseGases.a v * ‖p - q‖ := by
  -- the two rows of the radial cut
  have hcutlip : ∀ p q : EuclideanSpace ℝ (Fin 3),
      |fu.f (‖p‖ / Λ) - fu.f (‖q‖ / Λ)| ≤ M * ‖p - q‖ :=
    (radialCut_lip (fu := fu) hΛ hM hζ').1
  have hcutle : ∀ p : EuclideanSpace ℝ (Fin 3), |fu.f (‖p‖ / Λ)| ≤ 1 :=
    (radialCut_lip (fu := fu) hΛ hM hζ').2
  -- the momentum-space Lipschitz row of `Ŵ₁`
  have hw1lip : ∀ p q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
      ≤ 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ :=
    fun p q => chat_W1fun_lipschitz (h := h) hR hℓ hv_nonneg hvrad hv_supp hRℓ p q
  -- the momentum-space bound `|Ŵ₁| ≤ 16π(a v)`
  have hw1le : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ≤ 16 * Real.pi * _root_.BoseGases.a v :=
    fun p => Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ hv_nonneg hvrad hv_supp h hRℓ p
  intro p q
  -- split the difference
  have hkey : fu.f (‖p‖ / Λ) * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - fu.f (‖q‖ / Λ) * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q
      = fu.f (‖p‖ / Λ)
          * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
              - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
        + (fu.f (‖p‖ / Λ) - fu.f (‖q‖ / Λ))
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q := by ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |fu.f (‖p‖ / Λ)
        * (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
            - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)|
      ≤ 1 * (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖) := by
    rw [abs_mul]
    exact mul_le_mul (hcutle p) (hw1lip p q) (abs_nonneg _) zero_le_one
  have h2 : |(fu.f (‖p‖ / Λ) - fu.f (‖q‖ / Λ))
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
      ≤ (M * ‖p - q‖) * (16 * Real.pi * _root_.BoseGases.a v) := by
    rw [abs_mul]
    exact mul_le_mul (hcutlip p q) (hw1le q) (abs_nonneg _) (mul_nonneg hM (norm_nonneg _))
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  ring

end Work.BoseGateFS
