import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.opMono_basic
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.Frame.straightening
import Submission.Work.WilE3.Frame.frame_derivs_vanish
import Submission.Work.WilE3.Frame.order_le_multiplicity
import Submission.Work.WilE3.Frame.vanish_of_real_points

namespace Work.WilE3.Identity

set_option autoImplicit false
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

/-- Monotonicity of `Polynomial.eval : ℕ → ℕ` (all coefficients are natural numbers). -/
theorem polynomial_eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i hi => ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- `toC` (viewing a real point as a complex one) is continuous. -/
private theorem continuous_toC {k : ℕ} : Continuous (Work.WilE3.Frame.toC (k := k)) := by
  refine continuous_pi fun i => ?_
  exact Complex.continuous_ofReal.comp (continuous_apply i)

/-- **`E3_identity` from the local multiplicity bound** (GV survey Cor. 4.7; the *frame step* of
`NOTES.md` §3, with the conclusion identical to the frozen `WilkiesDesign.E.E3_identity`).

The proof is in three parts, each of which is a separate lemma of `Submission.Work.WilE3.Frame`:

* **straightening** (`Frame.straightening`): the coordinate map
  `Φ z = (z|_ιᶜ, h z)` is a local biholomorphism at `toC x` (`h x = 0` and `Δ ≠ 0` are exactly its
  hypotheses), giving an analytic local inverse `Ψ`; the germ of `{h = 0}` at `x` is
  `u ↦ Ψ (u, 0)`.
* **frame half** (`Frame.frame_derivs_vanish`): the ordered reduced derivatives of `f` at `x`, which
  are `Δ⁻¹ detOp`-words (`Frame.eaEvalC_detOp_eq` = `V_l = Δ⁻¹ detOp_l`), control every derivative
  of the one variable function `t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` along *every* real direction
  `w`, up to order `M.eval (∑ atomDeg (h a) + atomDeg f)`.
* **count half** (`Frame.order_le_multiplicity`): if that one variable function has finite vanishing
  order `N` at `0`, then `N ≤ M.eval (∑ atomDeg (h a) + atomDeg f)`; the `N` simple solutions of
  `f = ε` on the straightened curve give `N` nondegenerate zeros of the cut system
  `(h, cut forms, f - ε)` (`Frame.cutSys`, `Frame.nondeg_of_curve`) inside a ball of radius
  `ρ ε → 0`, to which `MultiplicityBound` applies.  The two inequalities are contradictory, so the
  curve function vanishes identically for every direction, and `Frame.vanish_of_real_points`
  converts that into the vanishing of `eaEval c f` on `{h = 0}` near `x`.
* if `ι` is not injective then two columns of the Jacobian coincide and the hypothesis `det ≠ 0`
  is contradictory (the *vacuous* branch); the boundary cases `k = 0` and `j = k` (where `{h = 0}`
  is a single point) are handled directly. -/
theorem E3_identity_proved_of_multiplicity (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ M : Polynomial ℕ, ∀ (k r j : ℕ) (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ),
    k + r ≤ F → (∀ a, eaEval c (h a) x = 0) →
    (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det ≠ 0 →
    (∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) →
      ∑ l, m l ≤ M.eval (∑ a, atomDeg (h a) + atomDeg f) → eaEval c (opMono c h ι m f) x = 0) →
    ∀ᶠ y in 𝓝 x, (∀ a, eaEval c (h a) y = 0) → eaEval c f y = 0 := by
  intro F
  obtain ⟨M, hcount⟩ := Work.WilE3.Frame.order_le_multiplicity hMB F
  refine ⟨M, ?_⟩
  intro k r j c h ι f x hkr hx hdet hvan
  -- `f x = 0`, from the multi-index `0`.
  have hfx : Work.WilE3.eaEvalC c f (Work.WilE3.Frame.toC x) = 0 := by
    have h0 := hvan 0 (fun a => rfl) (by simp)
    rw [Work.WilE3.API.opMono_basic c h ι (0 : Fin k → ℕ) |>.1 f] at h0
    rw [Work.WilE3.Frame.eaEvalC_toC]
    exact_mod_cast h0
  by_cases hinj : Function.Injective ι
  · -- `ι` injective: `j ≤ k`.
    have hjk_le : j ≤ k := by simpa using Fintype.card_le_of_injective ι hinj
    by_cases hk0 : k = 0
    · -- `Fin 0 → ℝ` is a single point.
      subst hk0
      refine Filter.Eventually.of_forall fun y _ => ?_
      have hyx : y = x := by funext i; exact i.elim0
      rw [hyx]
      have h := hfx
      rw [Work.WilE3.Frame.eaEvalC_toC] at h
      exact_mod_cast h
    · -- (1) the complexified hypotheses of the frame and count halves.
      have hxe : ∀ a, Work.WilE3.eaEvalC c (h a) (Work.WilE3.Frame.toC x) = 0 := fun a => by
        rw [Work.WilE3.Frame.eaEvalC_toC]
        exact_mod_cast hx a
      have hdC : (Matrix.of fun a b =>
          Work.WilE3.eaEvalC c (eaD c (ι b) (h a)) (Work.WilE3.Frame.toC x)).det ≠ 0 := by
        have hdetC : (Matrix.of fun a b =>
              Work.WilE3.eaEvalC c (eaD c (ι b) (h a)) (Work.WilE3.Frame.toC x)).det
            = ((Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det : ℂ) := by
          rw [show (Matrix.of fun a b =>
                Work.WilE3.eaEvalC c (eaD c (ι b) (h a)) (Work.WilE3.Frame.toC x))
              = (algebraMap ℝ ℂ).mapMatrix
                  (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x) from by
            ext a b
            simp [Work.WilE3.Frame.eaEvalC_toC]]
          exact (RingHom.map_det (algebraMap ℝ ℂ) _).symm
        rw [hdetC]
        exact_mod_cast hdet
      have hΔ : Work.WilE3.Frame.jacValC c h ι (Work.WilE3.Frame.toC x) ≠ 0 := by
        rw [Work.WilE3.Frame.jacValC_eq_det]
        exact hdC
      -- (2) the straightening of `{h = 0}` at `x`.
      obtain ⟨Ψ, hΨ0, hΨan, hΨΦ, hΨΨ⟩ :=
        Work.WilE3.Frame.straightening c h ι x hxe hdC
      have hIs : Work.WilE3.Frame.IsStraightening c h ι x Ψ := ⟨hΨ0, hΨan, hΨΦ, hΨΨ⟩
      by_cases hjk : j < k
      · -- **Main case** (`0 < j < k`).
        -- (3) every real direction keeps the curve function vanishing near `0`
        have hlines : ∀ w : Work.WilE3.Frame.U k ι → ℝ, ∀ᶠ t in 𝓝 (0 : ℂ),
            Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.uCoord k ι
              (Work.WilE3.Frame.toC x) + t • (fun i => (w i : ℂ)), 0)) = 0 := by
          intro w
          set Gin : ℂ → ℂ := fun t => Work.WilE3.eaEvalC c f
            (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
              t • (fun i => (w i : ℂ)), 0)) with hGin
          by_cases hw : w = 0
          · -- the degenerate direction: the curve function is constant
            subst hw
            refine Filter.Eventually.of_forall fun t => ?_
            have hz : (fun i : Work.WilE3.Frame.U k ι =>
                ((0 : Work.WilE3.Frame.U k ι → ℝ) i : ℂ)) = 0 := by
              funext i; simp
            rw [hz, smul_zero, add_zero, hΨ0]
            exact hfx
          · -- the interesting case: frame half plus count half force infinite order
            have hGan : AnalyticAt ℂ Gin 0 := by
              have hline : AnalyticAt ℂ (fun t : ℂ =>
                  (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
                    t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ))) 0 := by
                have h1 : AnalyticAt ℂ (fun t : ℂ =>
                    t • ((fun i : Work.WilE3.Frame.U k ι => (w i : ℂ)),
                      (0 : Fin j → ℂ))) 0 :=
                  (ContinuousLinearMap.toSpanSingleton ℂ
                    ((fun i : Work.WilE3.Frame.U k ι => (w i : ℂ)),
                      (0 : Fin j → ℂ))).analyticAt 0
                have h2 : AnalyticAt ℂ (fun _ : ℂ =>
                    (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x),
                      (0 : Fin j → ℂ))) 0 := analyticAt_const
                have h3 := h2.add h1
                refine h3.congr ?_
                filter_upwards with t
                simp only [Pi.add_apply, Prod.mk_add_mk, Prod.smul_mk, smul_zero,
                  zero_add]
              have hΨan' : AnalyticAt ℂ Ψ ((fun t : ℂ =>
                  (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
                    t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ))) 0) := by
                simpa using hΨan
              exact AnalyticAt.comp (f := fun t : ℂ =>
                  Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
                    t • (fun i => (w i : ℂ)), 0)) (x := (0 : ℂ))
                (Work.WilE3.API.eaEvalC_fderiv_analytic c f _).1
                (AnalyticAt.comp (f := fun t : ℂ =>
                    (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
                      t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ))) (x := (0 : ℂ))
                  hΨan' hline)
            have hord : analyticOrderAt Gin 0 = ⊤ := by
              by_contra hne
              obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hne
              -- frame half
              have hle : (M.eval (∑ a, atomDeg (h a) + atomDeg f) + 1 : ℕ∞) ≤ (N : ℕ∞) := by
                rw [hN, ← Nat.cast_add_one,
                  natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hGan]
                intro i hi
                exact Work.WilE3.Frame.frame_derivs_vanish c h ι f x
                  (M.eval (∑ a, atomDeg (h a) + atomDeg f)) hvan hΔ Ψ hIs w i (by omega)
              have hfrN : M.eval (∑ a, atomDeg (h a) + atomDeg f) + 1 ≤ N :=
                ENat.natCast_le_natCast.mp hle
              -- count half
              have hcnt := hcount k r j c h ι f x hkr hjk hinj hxe hfx hdC Ψ hIs w N hw hN.symm
              omega
            rwa [analyticOrderAt_eq_top] at hord
        exact Work.WilE3.Frame.vanish_of_real_points c h ι f x Ψ hIs hfx hlines
      · -- **`j = k`**: `{h = 0}` is a single point near `x`.
        have hjk_eq : j = k := by omega
        have hsurj : ∀ i : Fin k, i ∈ Set.range ι := by
          intro i
          have hcard : (Finset.univ.image ι).card = Fintype.card (Fin k) := by
            rw [Finset.card_image_of_injOn hinj.injOn, Finset.card_univ, Fintype.card_fin,
              Fintype.card_fin, hjk_eq]
          have huniv : Finset.univ.image ι = Finset.univ :=
            Finset.eq_univ_of_card _ hcard
          obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (by rw [huniv]; exact Finset.mem_univ i)
          exact ⟨a, ha⟩
        have hsub : ∀ u v : Work.WilE3.Frame.U k ι → ℂ, u = v := fun u v =>
          funext fun i => absurd (hsurj i.1) i.2
        obtain ⟨U₀, hU₀mem, hU₀eq⟩ := Filter.eventually_iff_exists_mem.mp hΨΨ
        have hmem : {y : Fin k → ℝ | Work.WilE3.Frame.toC y ∈ U₀} ∈ 𝓝 x :=
          continuous_toC.continuousAt.preimage_mem_nhds hU₀mem
        refine Filter.eventually_of_mem hmem fun y hy hyh => ?_
        have hyhe : ∀ a, Work.WilE3.eaEvalC c (h a) (Work.WilE3.Frame.toC y) = 0 := fun a => by
          rw [Work.WilE3.Frame.eaEvalC_toC]
          exact_mod_cast hyh a
        have hΦx : Work.WilE3.Frame.PhiC c h ι (Work.WilE3.Frame.toC x)
            = (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) := by
          refine Prod.ext rfl ?_
          funext a
          exact hxe a
        have hΦy : Work.WilE3.Frame.PhiC c h ι (Work.WilE3.Frame.toC y)
            = (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) := by
          refine Prod.ext (hsub _ _) ?_
          funext a
          exact hyhe a
        have hz : ((eaEval c f y : ℝ) : ℂ) = 0 := by
          calc ((eaEval c f y : ℝ) : ℂ)
              = Work.WilE3.eaEvalC c f (Work.WilE3.Frame.toC y) :=
                (Work.WilE3.Frame.eaEvalC_toC c f y).symm
            _ = Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.PhiC c h ι
                  (Work.WilE3.Frame.toC y))) := by rw [hU₀eq _ hy]
            _ = Work.WilE3.eaEvalC c f (Ψ (Work.WilE3.Frame.PhiC c h ι
                  (Work.WilE3.Frame.toC x))) := by rw [hΦy, hΦx]
            _ = Work.WilE3.eaEvalC c f (Work.WilE3.Frame.toC x) := by
                  rw [hU₀eq _ (mem_of_mem_nhds hU₀mem)]
            _ = 0 := hfx
        exact_mod_cast hz
  · -- Degenerate case: two equal columns of the Jacobian force `det = 0`, contradicting `hdet`.
    exfalso
    obtain ⟨a, b, hab, hιab⟩ : ∃ a b : Fin j, a ≠ b ∧ ι a = ι b := by
      by_contra hcon
      exact hinj fun a b hab => by
        by_contra hne
        exact hcon ⟨a, b, hne, hab⟩
    refine hdet (Matrix.det_zero_of_column_eq hab ?_)
    intro i
    simp only [Matrix.of_apply]
    rw [hιab]

end Work.WilE3.Identity
