import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.CutPolyVal
import Submission.Work.WilE3.Frame.exists_cut_forms
import Submission.Work.WilE3.Frame.nondeg_of_curve
import Submission.Work.WilE3.Frame.exists_card_solutions_simple_tendsto
import Submission.Work.WilE3.Frame.cutSys_atomDeg_sum
import Submission.Work.WilE3.Frame.pertSys_atomDeg_sum
import Submission.Work.WilE3.Frame.atomDeg_cutPoly_le
import Submission.Work.WilE3.Frame.cutSys_curvePoint_zero
import Submission.Work.WilE3.Frame.analyticAt_curveFun
import Submission.Work.WilE3.Frame.exists_shrinking_radius
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Filter Matrix
open scoped Topology
open WilkiesDesign.E

/-- Monotonicity of `Polynomial.eval : ℕ → ℕ` (all coefficients are natural numbers). -/
private theorem polynomial_eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- The constant perturbation `pertSys hjk` has vanishing derivatives. -/
private lemma eaD_pertSys_eq_zero {k r j : ℕ} (c : EAChain k r) (hjk : j < k)
    (i i' : Fin k) : eaD c i' (pertSys (k := k) (r := r) hjk i) = 0 := by
  by_cases hi : i = rowF hjk
  · subst hi
    rw [pertSys_rowF]
    exact Work.WilE3.API.eaD_C c i' (-1)
  · rw [pertSys_of_ne hjk hi]
    simp [eaD]

/-- **Order ≤ multiplicity** (the count half of `E3_identity`).  Assuming
`Work.WilE3.MultiplicityBound` (Gabrielov's local multiplicity bound, a hypothesis of the target
theorem), there is a polynomial `M` such that: for an effectively smooth `{h = 0}` at `x`
(`h x = 0`, invertible `ι`-Jacobian, `ι` injective, `j < k`), a straightening `Ψ` of `{h = 0}` at `x`
(`IsStraightening`) and a *non-zero* real direction `w`, the vanishing order at `0` of the one
variable function `t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` — whenever it is finite, i.e. equal to a
natural number `N` — is at most `M.eval (∑ a, atomDeg (h a) + atomDeg f)`.

Proof route (all ingredients available in this workspace):

1. By `Work.WilE3.Frame.exists_cut_forms` (hypotheses `ι` injective, `w ≠ 0`) choose cut forms
   `μ : Fin (k - j - 1) → (U k ι → ℝ)` with `CutForms ι w μ`.
2. By `Work.WilE3.Frame.exists_card_solutions_simple_tendsto` applied to
   `G t := eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` (analytic at `0`, `G 0 = eaEvalC c f (toC x) = 0`,
   order `N`) there are `r, δ > 0` such that for `0 < ‖ε‖ < δ` the disc of radius `r` around `0`
   carries exactly `N` simple solutions of `G t = ε` and, for every `η > 0`, eventually in
   `ε ∈ 𝓝[≠] 0` every solution of `G t = ε` in the disc satisfies `‖t‖ < η`.
3. Let `Z t := Ψ (u₀ + t • w_ℂ, 0)` and `sys := cutSys h (fun a => cutPoly ι (μ a) x) f`.  For a
   solution `t` of `G t = ε`, the point `Z t` satisfies the equations of `sys + ε • pertSys`:
   the `h`-rows vanish because `Z t = Ψ (v, 0)` with `PhiC (Ψ v) = (v,0)`, the cut rows vanish
   because `eaEvalC c (cutPoly ι (μ a) x) (Z t) = t * Σ_i μ a i * w i = 0`
   (`Work.WilE3.Frame.eaEvalC_cutPoly` and `CutForms`), and the last row is `f = ε`; the constant
   perturbation `pertSys` (`-1` in the `rowF` slot, `0` elsewhere) has vanishing derivatives, so the
   Jacobian of the perturbed system is that of `sys`, which is nondegenerate at `Z t` by
   `Work.WilE3.Frame.nondeg_of_curve`.
4. `Z` is injective on the disc (apply `PhiC ∘ Ψ = id` to `Z t = Z t'` and use `w ≠ 0`), so
   `s.image Z` has `N` elements; these are the `N` nondegenerate zeros of the perturbed system
   inside the ball of radius `ρ ε := (if ε = 0 then 1 else 0) + ‖ε‖ + ∑ z ∈ s, ‖Z z - toC x‖`
   (`s` a chosen solution set; the sum is `0` for `ε = 0`), and `ρ ε → 0` as `ε → 0` (step 2),
   `ρ ε > 0`.
5. Apply `hMB F` to the system `sys`, the perturbation `pertSys` and the radius `ρ`, giving
   eventually in `ε ≠ 0`: `N ≤ M0.eval (∑ i, atomDeg (sys i) + ∑ i, atomDeg (pertSys i))`.
6. Degree bookkeeping: `∑ i, atomDeg (sys i) ≤ ∑ a, atomDeg (h a) + 2 * (k - j - 1) + atomDeg f`
   (`atomDeg (cutPoly ι μ x) ≤ 2`), `∑ i, atomDeg (pertSys i) = k`, hence the total is at most
   `S + 3 * F` with `S = ∑ a, atomDeg (h a) + atomDeg f`, because `2 * (k - j - 1) + k ≤ 3 * F`
   (`k ≤ F` from `k + r ≤ F`).  Take `M := M0.comp (X + C (3 * F))`, so that
   `M.eval S = M0.eval (S + 3 * F)` (`Polynomial.eval_comp`); the final monotonicity step uses
   `polynomial_eval_le_eval`, which may be stated locally in your file as
   `p.eval m ≤ p.eval n` for `m ≤ n` (it is `Work.WilE3.Identity.polynomial_eval_le_eval`, but do
   not import `Identity` from `Frame`). -/
theorem order_le_multiplicity (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ M : Polynomial ℕ, ∀ (k r j : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
      (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ),
      k + r ≤ F → j < k → Function.Injective ι →
      (∀ a, Work.WilE3.eaEvalC c (h a) (Work.WilE3.Frame.toC x) = 0) →
      Work.WilE3.eaEvalC c f (Work.WilE3.Frame.toC x) = 0 →
      (Matrix.of fun a b => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c (ι b) (h a))
        (Work.WilE3.Frame.toC x)).det ≠ 0 →
      ∀ (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ)),
      Work.WilE3.Frame.IsStraightening c h ι x Ψ →
      ∀ (w : Work.WilE3.Frame.U k ι → ℝ) (N : ℕ), w ≠ 0 →
      analyticOrderAt (fun t : ℂ => Work.WilE3.eaEvalC c f
        (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
          t • (fun i => (w i : ℂ)), 0))) 0 = N →
      N ≤ M.eval (∑ a, WilkiesDesign.E.atomDeg (h a) + WilkiesDesign.E.atomDeg f) := by
  obtain ⟨M0, hMB0⟩ := hMB F
  refine ⟨M0.comp (Polynomial.X + Polynomial.C (3 * F)), ?_⟩
  intro k r j c h ι f x hkr hjk hι hxe hfx hd Ψ hΨ w N hw hord
  -- cut forms
  obtain ⟨μ, hμ0, hμ1⟩ := exists_cut_forms ι hι w hw
  have hμ : CutForms ι w μ := ⟨hμ0, hμ1⟩
  set L : Fin (k - j - 1) → EAPoly k r := fun a => cutPoly ι (μ a) x with hL
  set sys : Fin k → EAPoly k r := cutSys h L f with hsys
  set pert : Fin k → EAPoly k r := pertSys (k := k) (r := r) hjk with hpert
  set u0 : U k ι → ℂ := uCoord k ι (toC x) with hu0
  set wC : U k ι → ℂ := fun i => (w i : ℂ) with hwC
  set G : ℂ → ℂ := fun t => eaEvalC c f (Ψ (u0 + t • wC, 0)) with hG
  set Z : ℂ → Fin k → ℂ := fun t => Ψ (u0 + t • wC, 0) with hZ
  -- the one-variable function `G` is analytic at `0` and vanishes there
  have hGan : AnalyticAt ℂ G 0 :=
    analyticAt_curveFun c f ι x Ψ hΨ.2.1 w
  have hG0 : G 0 = 0 := by
    simp only [hG, zero_smul, smul_zero, add_zero]
    rw [show Ψ (u0, (0 : Fin j → ℂ)) = toC x from by rw [hu0]; exact hΨ.1]
    exact hfx
  have hordG : analyticOrderAt G 0 = N := hord
  -- counting of the simple solutions
  obtain ⟨rr, δ, hrr, hδ, hcount, hconv⟩ :=
    exists_card_solutions_simple_tendsto hGan hG0 N hordG
  have hcount' : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → ∃ s : Finset ℂ, s.card = N ∧
      (∀ z ∈ s, G z = ε ∧ ‖z‖ < rr ∧ deriv G z ≠ 0) ∧
      (∀ z : ℂ, G z = ε → ‖z‖ < rr → z ∈ s) := by
    intro ε h1 h2
    obtain ⟨s, hs1, hs2, hs3⟩ := hcount ε h1 h2
    exact ⟨s, hs1, by simpa using hs2, by simpa using hs3⟩
  have hconv' : ∀ η : ℝ, 0 < η → ∀ᶠ ε in 𝓝[≠] (0 : ℂ),
      ∀ z : ℂ, G z = ε → ‖z‖ < rr → ‖z‖ < η := by
    intro η hη
    simpa only [sub_zero] using hconv η hη
  -- continuity of the straightening along the curve
  have hcontPair : ContinuousAt (fun t : ℂ => (u0 + t • wC, (0 : Fin j → ℂ))) 0 := by
    have hc : Continuous (fun _ : ℂ => u0) := continuous_const
    have hs : Continuous (fun t : ℂ => t • wC) := continuous_id.smul continuous_const
    exact ((hc.add hs).prodMk continuous_const).continuousAt
  have hZcont : ContinuousAt Z 0 := by
    have hg : ContinuousAt Ψ ((u0 + (0 : ℂ) • wC, (0 : Fin j → ℂ))) := by
      have heq : (u0 + (0 : ℂ) • wC, (0 : Fin j → ℂ)) = (u0, (0 : Fin j → ℂ)) := by
        rw [zero_smul, add_zero]
      rw [heq]; exact hΨ.2.1.continuousAt
    have hmain : ContinuousAt (fun t : ℂ => Ψ (u0 + t • wC, 0)) 0 :=
      hg.comp_of_eq hcontPair rfl
    simpa only [hZ, Function.comp_def] using hmain
  have hZ0 : Z 0 = toC x := by
    simp only [hZ, zero_smul, smul_zero, add_zero]
    rw [show Ψ (u0, (0 : Fin j → ℂ)) = toC x from by rw [hu0]; exact hΨ.1]
  -- the straightening identity holds on a ball around `0`
  obtain ⟨ρ1, hρ1pos, hρ1⟩ : ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ t : ℂ, ‖t‖ < ρ1 →
      PhiC c h ι (Ψ (u0 + t • wC, 0)) = (u0 + t • wC, 0) := by
    have hbase : ∀ᶠ v in 𝓝 ((u0 + (0 : ℂ) • wC, (0 : Fin j → ℂ))),
        PhiC c h ι (Ψ v) = v := by
      have heq : (u0 + (0 : ℂ) • wC, (0 : Fin j → ℂ)) = (u0, (0 : Fin j → ℂ)) := by
        rw [zero_smul, add_zero]
      rw [heq]; exact hΨ.2.2.1
    have hev := hcontPair.eventually hbase
    obtain ⟨ρ1, hρ1pos, hsub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨ρ1, hρ1pos, fun t ht => hsub ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact ht
  -- nondegeneracy holds on a ball around `0`
  have hndev : ∀ᶠ t in 𝓝 (0 : ℂ), deriv G t ≠ 0 →
      (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)).det ≠ 0 := by
    have h := nondeg_of_curve c h ι f x hjk hι hxe hd Ψ hΨ w hw μ hμ
    simpa only [hG, hZ, hsys, hL, hu0, hwC] using h
  obtain ⟨ρ2, hρ2pos, hρ2⟩ : ∃ ρ2 : ℝ, 0 < ρ2 ∧ ∀ t : ℂ, ‖t‖ < ρ2 →
      deriv G t ≠ 0 →
      (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)).det ≠ 0 := by
    obtain ⟨ρ2, hρ2pos, hsub⟩ := Metric.mem_nhds_iff.mp hndev
    refine ⟨ρ2, hρ2pos, fun t ht => hsub ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact ht
  have hη0pos : 0 < min ρ1 ρ2 := lt_min hρ1pos hρ2pos
  have hPhi : ∀ t : ℂ, ‖t‖ < min ρ1 ρ2 → PhiC c h ι (Z t) = (u0 + t • wC, 0) := by
    intro t ht
    have h := hρ1 t (lt_of_lt_of_le ht (min_le_left _ _))
    simpa only [hZ] using h
  have hnd : ∀ t : ℂ, ‖t‖ < min ρ1 ρ2 → deriv G t ≠ 0 →
      (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)).det ≠ 0 := by
    intro t ht hdG
    exact hρ2 t (lt_of_lt_of_le ht (min_le_right _ _)) hdG
  -- the choice of solution sets and the shrinking radius
  set sel : ℂ → Finset ℂ := fun ε =>
    if h : 0 < ‖ε‖ ∧ ‖ε‖ < δ then Classical.choose (hcount' ε h.1 h.2) else ∅ with hsel
  have hselε : ∀ (ε : ℂ) (h1 : 0 < ‖ε‖) (h2 : ‖ε‖ < δ),
      sel ε = Classical.choose (hcount' ε h1 h2) := by
    intro ε h1 h2
    rw [hsel]
    exact dif_pos ⟨h1, h2⟩
  have hsel_card : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → (sel ε).card = N := fun ε h1 h2 => by
    rw [hselε ε h1 h2]
    exact (Classical.choose_spec (hcount' ε h1 h2)).1
  have hsel_sub : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → ∀ z ∈ sel ε, G z = ε ∧ ‖z‖ < rr :=
    fun ε h1 h2 z hz => by
      rw [hselε ε h1 h2] at hz
      exact ⟨((Classical.choose_spec (hcount' ε h1 h2)).2.1 z hz).1,
             ((Classical.choose_spec (hcount' ε h1 h2)).2.1 z hz).2.1⟩
  have hsel_deriv : ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → ∀ z ∈ sel ε, deriv G z ≠ 0 :=
    fun ε h1 h2 z hz => by
      rw [hselε ε h1 h2] at hz
      exact ((Classical.choose_spec (hcount' ε h1 h2)).2.1 z hz).2.2
  have hsel_empty : ∀ ε : ℂ, ¬ (0 < ‖ε‖ ∧ ‖ε‖ < δ) → sel ε = ∅ := fun ε h => by
    rw [hsel]; exact dif_neg h
  obtain ⟨ρ, hρpos, hρtend, hρball⟩ :=
    exists_shrinking_radius G Z (toC x) sel hsel_card hsel_sub hsel_empty hconv' hZcont hZ0
  -- vanishing of the cut system at the real point
  have hsys0 : ∀ i : Fin k, eaEvalC c (sys i) (toC x) = 0 := by
    intro i
    rcases cutSys_cases hjk i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
    · rw [hsys, cutSys_rowH hjk]; exact hxe a
    · rw [hsys, cutSys_rowL hjk, hL]; exact eaEvalC_cutPoly_toC c ι (μ a) x
    · rw [hsys, cutSys_rowF hjk]; exact hfx
  have hMBe := hMB0 k r c sys pert (toC x) ρ hkr hsys0 hρpos hρtend
  -- combine the two eventual statements and extract a concrete `ε`
  have hgood : ∀ᶠ ε in 𝓝[≠] (0 : ℂ),
      (∀ s : Finset (Fin k → ℂ),
        (∀ z ∈ s, (∀ i, eaEvalC c (sys i) z + ε * eaEvalC c (pert i) z = 0) ∧
          (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) z
            + ε * eaEvalC c (eaD c i' (pert i)) z).det ≠ 0) →
        (∀ z ∈ s, ‖z - toC x‖ < ρ ε) →
        s.card ≤ M0.eval (∑ i, atomDeg (sys i) + ∑ i, atomDeg (pert i))) ∧
      (∀ z : ℂ, G z = ε → ‖z‖ < rr → ‖z‖ < min ρ1 ρ2) :=
    hMBe.and (hconv' (min ρ1 ρ2) hη0pos)
  obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.mem_nhdsWithin_iff.mp hgood
  set ε₀ : ℝ := min (δ' / 2) (δ / 2) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by linarith) (by linarith)
  have hε₀δ' : ε₀ < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε₀δ : ε₀ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set ε : ℂ := (ε₀ : ℂ) with hε
  have hεnorm : ‖ε‖ = ε₀ := by
    rw [hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε₀pos]
  have hεnorm_pos : 0 < ‖ε‖ := by rw [hεnorm]; exact hε₀pos
  have hεnorm_lt : ‖ε‖ < δ := by rw [hεnorm]; exact hε₀δ
  have hεne : ε ≠ 0 := norm_pos_iff.mp hεnorm_pos
  have hεmem : ε ∈ Metric.ball (0 : ℂ) δ' ∩ {x : ℂ | x ≠ 0} := by
    refine ⟨?_, hεne⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hεnorm]; exact hε₀δ'
  obtain ⟨hP, hQ⟩ := hδ'sub hεmem
  -- injectivity of `Z` on the chosen solution set
  have hinj : Set.InjOn Z ↑(sel ε) := by
    intro t ht t' ht' heq
    have hst := hsel_sub ε hεnorm_pos hεnorm_lt t ht
    have hst' := hsel_sub ε hεnorm_pos hεnorm_lt t' ht'
    have htη : ‖t‖ < min ρ1 ρ2 := hQ t hst.1 hst.2
    have ht'η : ‖t'‖ < min ρ1 ρ2 := hQ t' hst'.1 hst'.2
    have h1 := hPhi t htη
    have h2 := hPhi t' ht'η
    have hu : u0 + t • wC = u0 + t' • wC := by
      have e1 : PhiC c h ι (Z t) = PhiC c h ι (Z t') := by rw [heq]
      rw [h1, h2] at e1
      exact congrArg Prod.fst e1
    have hw' : t • wC = t' • wC := by
      have h := congrArg (fun v : U k ι → ℂ => -u0 + v) hu
      simpa using h
    have hzero : (t - t') • wC = 0 := by rw [sub_smul, hw', sub_self]
    obtain ⟨l, hl⟩ : ∃ l : U k ι, w l ≠ 0 := by
      by_contra hcon
      exact hw (funext fun l => by
        by_contra hl
        exact hcon ⟨l, hl⟩)
    have hl2 : (t - t') * (w l : ℂ) = 0 := by
      have h := congrFun hzero l
      simpa [hwC] using h
    rcases mul_eq_zero.mp hl2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (Complex.ofReal_eq_zero.mp h) hl
  -- the nondegenerate zero set of the perturbed system
  have hnd_pert : ∀ t : ℂ, ‖t‖ < min ρ1 ρ2 → deriv G t ≠ 0 →
      (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)
        + ε * eaEvalC c (eaD c i' (pert i)) (Z t)).det ≠ 0 := by
    intro t ht hdG
    have hmat : (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)
        + ε * eaEvalC c (eaD c i' (pert i)) (Z t))
        = (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) (Z t)) := by
      ext i i'
      rw [Matrix.of_apply, Matrix.of_apply]
      rw [show eaD c i' (pert i) = 0 from by
            rw [hpert]; exact eaD_pertSys_eq_zero c hjk i i',
        Work.WilE3.API.eaEvalC_zero, mul_zero, add_zero]
    rw [hmat]
    exact hnd t ht hdG
  set simg : Finset (Fin k → ℂ) := (sel ε).image Z with hsimg
  have hsimgn : simg.card = N := by
    rw [hsimg, Finset.card_image_of_injOn hinj, hsel_card ε hεnorm_pos hεnorm_lt]
  have hzeros : ∀ z ∈ simg, (∀ i, eaEvalC c (sys i) z + ε * eaEvalC c (pert i) z = 0) ∧
      (Matrix.of fun i i' => eaEvalC c (eaD c i' (sys i)) z
        + ε * eaEvalC c (eaD c i' (pert i)) z).det ≠ 0 := by
    intro z hz
    rw [hsimg, Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hst := hsel_sub ε hεnorm_pos hεnorm_lt t ht
    have htη : ‖t‖ < min ρ1 ρ2 := hQ t hst.1 hst.2
    have htd : deriv G t ≠ 0 := hsel_deriv ε hεnorm_pos hεnorm_lt t ht
    have hPhiZ : PhiC c h ι (Z t) = (u0 + t • wC, 0) := hPhi t htη
    refine ⟨?_, hnd_pert t htη htd⟩
    have hcur := cutSys_curvePoint_zero c h ι x hjk w μ hμ f t ε (Z t) hPhiZ
      (by simpa only [hG, hZ] using hst.1)
    intro i
    simpa only [hsys, hL, hpert] using hcur i
  have hball : ∀ z ∈ simg, ‖z - toC x‖ < ρ ε := by
    intro z hz
    rw [hsimg, Finset.mem_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact hρball ε hεnorm_pos hεnorm_lt t ht
  have hcard_le := hP simg hzeros hball
  have hND : N ≤ M0.eval (∑ i, atomDeg (sys i) + ∑ i, atomDeg (pert i)) := by
    rw [← hsimgn]; exact hcard_le
  -- degree bookkeeping
  have hsys_sum : (∑ i : Fin k, atomDeg (sys i))
      = (∑ a : Fin j, atomDeg (h a)) + (∑ b : Fin (k - j - 1), atomDeg (L b)) + atomDeg f := by
    rw [hsys]; exact cutSys_atomDeg_sum hjk h L f
  have hcut_le : (∑ b : Fin (k - j - 1), atomDeg (L b)) ≤ 2 * (k - j - 1) := by
    calc (∑ b : Fin (k - j - 1), atomDeg (L b))
        ≤ ∑ _b : Fin (k - j - 1), 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [hL]; exact atomDeg_cutPoly_le ι (μ b) x
      _ = 2 * (k - j - 1) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  have hpert_sum : (∑ i : Fin k, atomDeg (pert i)) = k := by
    rw [hpert]; exact pertSys_atomDeg_sum hjk
  have hDle : (∑ i : Fin k, atomDeg (sys i)) + (∑ i : Fin k, atomDeg (pert i))
      ≤ (∑ a : Fin j, atomDeg (h a)) + atomDeg f + 3 * F := by
    rw [hsys_sum, hpert_sum]
    have hbound : 2 * (k - j - 1) + k ≤ 3 * F := by omega
    omega
  have hMeval : (M0.comp (Polynomial.X + Polynomial.C (3 * F))).eval
        (∑ a, atomDeg (h a) + atomDeg f)
      = M0.eval ((∑ a, atomDeg (h a) + atomDeg f) + 3 * F) := by
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [hMeval]
  exact le_trans hND (polynomial_eval_le_eval (p := M0) hDle)

end

end Work.WilE3.Frame
