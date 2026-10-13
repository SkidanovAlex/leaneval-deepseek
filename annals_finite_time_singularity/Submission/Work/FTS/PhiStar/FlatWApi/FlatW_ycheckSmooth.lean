/-
# `Work.FTS.PhiStar.FlatWApi.FlatW_ycheckSmooth` — the flat bound for the `Ŷ`-expansion

The lead design decomposes the star witness as

`Φ̃_* = Aprof α(z)·sin 2θ + α·φ(z)·ψ(θ) + R`,   `φ(z) = 2/(1+z)`,

and the flat `𝒲^{7,∞}`-bound on `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ` (`VocabO2.Ycheck`) is obtained by
splitting the three summands.  Dividing by `sin 2θ` and multiplying by the flat weight
`(z+1)/z`, the three pieces are

1. `(z+1)/z · Aprof α z`  — purely radial, `O(α)`;
2. `α · (2/(1+z)) · (ψ θ / sin 2θ)` — a radial factor `α·2/(1+z)` times the *angular* divided
   profile `ψ/sin 2θ`, whose flat bound is uniform in `α`;
3. `(z+1)/z · R/sin 2θ` — the hypothesis.

This file proves that the sum again satisfies a flat bound, with constant `C·(α + K)`:

* **piece 1** is `Work.FTS.PhiStar.FlatW_aprof` (`FlatW 7 … (C₁·α)`);
* **piece 2** is `Work.FTS.PhiStar.FlatW_psiDiv` (`FlatW 7 (ψ/sin 2θ) C₂`) combined with
  `FlatW_theta_radial_mul`, for which one needs the one-variable flat estimate
  `|(z+1)^k ∂_z^k (α·2/(1+z))| ≤ α·10080` for `k ≤ 7`, proved here from the explicit
  iterated derivative `∂_z^k (c/(1+z)) = (-1)^k c k! / (1+z)^{k+1}`
  (`iter_deriv_const_div_one_add`, whose one-step input is `deriv_const_div_pow`);
* **piece 3** is the hypothesis.

The three pieces are added with `FlatW_add` (closure of the flat class under sums, which needs
`SmoothOpen` of the summands — the closure facts `smoothOpen_of_radial`,
`smoothOpen_of_angular`, `smoothOpen_mul`, `smoothOpen_add`, `smoothOpen_congr` are proved
here), the constants of the three (`FlatW_add`, `FlatW_theta_radial_mul`, `FlatW_aprof`,
`FlatW_psiDiv`) are existential, so the final constant is built from the chosen witnesses:
with `Ca`, `Cm`, `C₁`, `C₂` the four constants, the summed bound is
`Ca·(Ca·(C₁α + Cm·(α·10080·C₂)) + K)` and it is dominated by
`max (Ca·(Ca·(C₁ + Cm·10080·C₂) + 1)) 1 · (α + K)` using `α ≥ 0` and `K ≥ 0`.

Everything here is fully proved and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatW_aprof
import Submission.Work.FTS.PhiStar.FlatW_psiDiv
import Submission.Work.FTS.PhiStar.GzProfile_smooth
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_add
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_theta_radial_mul
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWApi

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Monotonicity of the flat class in its constant -/

lemma flatW_mono {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') : Work.FTS.VocabO2.FlatW l f K' := by
  intro z θ hz hθ hπ
  obtain ⟨h1, h2⟩ := h z θ hz hθ hπ
  exact ⟨fun k hk => le_trans (h1 k hk) hle, fun k i hki => le_trans (h2 k i hki) hle⟩

/-! ## Closure of `SmoothOpen` under the operations used below -/

lemma smoothOpen_of_radial {g : ℝ → ℝ} (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => g z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun z _ : ℝ => g z) = fun p : ℝ × ℝ => g p.1 := rfl
  rw [hfun]
  exact (hg n).comp contDiffOn_fst (fun p hp => (Set.mem_prod.mp hp).1)

lemma smoothOpen_of_angular {g : ℝ → ℝ} (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioo 0 (π/2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ => g θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun _ θ : ℝ => g θ) = fun p : ℝ × ℝ => g p.2 := rfl
  rw [hfun]
  exact (hg n).comp contDiffOn_snd (fun p hp => (Set.mem_prod.mp hp).2)

lemma smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  rw [hfun]
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) _
      from hf).mul (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) _ from hg)

lemma smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  rw [hfun]
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) _
      from hf).add (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) _ from hg)

lemma smoothOpen_congr {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π/2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hf' := (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n
  refine hf'.congr (fun p hp => ?_)
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ2).symm

/-! ## The one-variable smoothness facts -/

lemma contDiffOn_zdiv (n : ℕ) : ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) := by
  refine ContDiffOn.div (contDiffOn_id.add contDiffOn_const) contDiffOn_id ?_
  intro z hz; exact ne_of_gt hz

lemma contDiffOn_two_div_one_add (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => α * (2 / (1 + z))) (Set.Ioi 0) := by
  have heq : (fun z : ℝ => α * (2 / (1 + z))) = fun z : ℝ => (2 * α) / (1 + z) := by
    funext z; ring
  rw [heq]
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz' : (0:ℝ) < z := hz
  exact ne_of_gt (by linarith : (0:ℝ) < 1 + z)

lemma contDiffOn_inv_s2 (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => (1:ℝ) / Work.Construction.s2 θ) (Set.Ioo 0 (π/2)) := by
  have h : (fun θ : ℝ => (1:ℝ) / Work.Construction.s2 θ)
      = fun θ : ℝ => (1:ℝ) / Real.sin (2*θ) := by
    funext θ; rw [show Work.Construction.s2 θ = Real.sin (2*θ) from rfl]
  rw [h]
  refine ContDiffOn.div contDiffOn_const ?_ ?_
  · fun_prop
  · intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

lemma contDiffOn_psiDiv (α : ℝ) (ψ : ℝ → ℝ) (hang : Work.FTS.PhiStar.AngModel α ψ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => ψ θ / Work.Construction.s2 θ) (Set.Ioo 0 (π/2)) := by
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hang.smooth.of_le (by
      rw [show Work.Stability.smoothOrder = ((⊤:ℕ∞):WithTop ℕ∞) from rfl]
      exact_mod_cast le_top)
  · rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl]
    fun_prop
  · intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

lemma contDiffOn_aprof (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1/4) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.PhiStar.Aprof α) (Set.Ioi 0) := by
  unfold Work.FTS.PhiStar.Aprof
  refine ContDiffOn.sub (Work.FTS.PhiStar.GzProfile_smooth hα hα4 n) ?_
  unfold Work.FTS.PhiStar.ThetaProfile
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_id)) ?_
  intro z hz
  have hz' : (0:ℝ) < z := hz
  exact ne_of_gt (by linarith : (0:ℝ) < 2 * (1 + z))

/-! ## The flat estimate for the radial factor `α·2/(1+z)` -/

/-- `∂_z (c/(1+z)^n) = -c·n/(1+z)^{n+1}`. -/
lemma deriv_const_div_pow (c : ℝ) (n : ℕ) (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => c / (1 + w) ^ n) z = -c * (n : ℝ) / (1 + z) ^ (n + 1) := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1) * 1) z :=
    h1.pow n
  have h3 : HasDerivAt (fun w : ℝ => c / (1 + w) ^ n)
      ((0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / ((1 + z) ^ n) ^ 2) z :=
    (hasDerivAt_const z c).div h2 (by positivity)
  rw [h3.deriv]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    have hsq : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
      rw [show 2 * n = n + n from by ring, pow_add, pow_two]
    rw [hsq]
    rw [show (0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / (1 + z) ^ (2 * n)
        = -(c * (n : ℝ) * (1 + z) ^ (n - 1)) / (1 + z) ^ (2 * n) from by ring]
    rw [div_eq_iff (by positivity : (1 + z) ^ (2 * n) ≠ 0)]
    rw [show -c * (n : ℝ) / (1 + z) ^ (n + 1) * (1 + z) ^ (2 * n)
        = (-c * (n : ℝ)) * ((1 + z) ^ (2 * n) / (1 + z) ^ (n + 1)) from by ring]
    rw [show (1 + z) ^ (2 * n) / (1 + z) ^ (n + 1) = (1 + z) ^ (n - 1) from by
      rw [div_eq_iff (by positivity : (1 + z) ^ (n + 1) ≠ 0), ← hpow]]
    ring

/-- The iterated derivatives of `w ↦ c/(1+w)`. -/
lemma iter_deriv_const_div_one_add (c : ℝ) :
    ∀ k : ℕ, ∀ z : ℝ, (1 : ℝ) + z ≠ 0 →
      deriv^[k] (fun w : ℝ => c / (1 + w)) z
        = (-1 : ℝ) ^ k * c * ((k.factorial : ℕ) : ℝ) / (1 + z) ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro z hz; norm_num
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
      have hev : deriv^[k] (fun w : ℝ => c / (1 + w))
          =ᶠ[𝓝 z] fun w => (-1 : ℝ) ^ k * c * ((k.factorial : ℕ) : ℝ) / (1 + w) ^ (k + 1) := by
        filter_upwards [hset.mem_nhds (show (1 : ℝ) + z ≠ 0 from hz)] with w hw
        exact ih w hw
      rw [hev.deriv_eq, deriv_const_div_pow _ _ z hz]
      have hsign : (-1:ℝ)^(k+1) = (-1)^k * (-1) := by rw [pow_succ]
      rw [hsign, Nat.factorial_succ]
      push_cast
      ring

/-- **The flat bound for the radial factor `α·2/(1+z)`**: for `k ≤ 7` and `z > 0`,
`|(z+1)^k ∂_z^k (α·2/(1+·))| ≤ α·10080` (`10080 = 2·7!`). -/
lemma radial_alpha_bound (α : ℝ) (hα : 0 < α) :
    ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k (fun w : ℝ => α * (2 / (1 + w))) z| ≤ α * 10080 := by
  intro k hk z hz
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hzne : (1:ℝ) + z ≠ 0 := ne_of_gt hz1
  have h1 : iteratedDeriv k (fun w : ℝ => α * (2 / (1 + w))) z
      = α * deriv^[k] (fun w : ℝ => 2 / (1 + w)) z := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate]
  rw [h1, iter_deriv_const_div_one_add 2 k z hzne]
  have hbase : (z + 1) ^ k = (1 + z) ^ k := by ring
  rw [hbase]
  have hprod : (1 + z) ^ k * (α * ((-1 : ℝ) ^ k * 2 * ↑k.factorial / (1 + z) ^ (k + 1)))
      = α * (2 * ↑k.factorial / (1 + z)) * (-1:ℝ)^k := by
    have hpow : (1 + z) ^ k / (1 + z) ^ (k + 1) = 1 / (1 + z) := by
      have hk0 : (1 + z) ^ k ≠ 0 := pow_ne_zero _ hzne
      field_simp
      ring
    rw [show (1 + z) ^ k * (α * ((-1 : ℝ) ^ k * 2 * ↑k.factorial / (1 + z) ^ (k + 1)))
        = α * ((-1:ℝ)^k * (2 * ↑k.factorial)) * ((1 + z) ^ k / (1 + z) ^ (k + 1)) from by ring]
    rw [hpow]
    ring
  rw [hprod]
  have hA : ((k.factorial : ℕ) : ℝ) ≤ 5040 := by
    have h : k.factorial ≤ 5040 := by interval_cases k <;> norm_num
    exact_mod_cast h
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (le_of_lt hα), abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ↑k.factorial),
    abs_of_pos hz1]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hα)
  rw [div_le_iff₀ hz1]
  nlinarith [hA, hz1]

/-! ## The main theorem -/

theorem FlatW_ycheckSmooth : ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (ψ : ℝ → ℝ) (R : Work.FTS.Galerkin.Fn) (K : ℝ),
    0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ → 0 ≤ K →
    Work.FTS.EllipticEst.SmoothOpen R →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) K →
    Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
        + (z + 1) / z * R z θ / Work.Construction.s2 θ) (C * (α + K)) := by
  obtain ⟨C₁, hC₁, hA⟩ := Work.FTS.PhiStar.FlatW_aprof
  obtain ⟨C₂, hC₂, hP⟩ := Work.FTS.PhiStar.FlatW_psiDiv
  obtain ⟨Cm, hCmpos, hRadMul⟩ := FlatW_theta_radial_mul
  obtain ⟨Ca, hCapos, hAdd⟩ := FlatW_add
  refine ⟨max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro α ψ R K hα hα5 hang hK hR hRflat
  have hα4 : α ≤ 1/4 := by linarith
  have hα1 : α ≤ 1 := by linarith
  have hC₂0 : (0:ℝ) ≤ C₂ := le_of_lt hC₂
  have hA0 : (0:ℝ) ≤ α * 10080 := by positivity
  -- the three summands
  have hf1 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) (C₁ * α) := hA α hα hα1
  have hf2 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (Cm * ((α * 10080) * C₂)) := by
    have h := hRadMul 7 (fun z => α * (2 / (1 + z))) (fun θ => ψ θ / Work.Construction.s2 θ)
      (α * 10080) C₂ hA0 hC₂0 (radial_alpha_bound α hα) (hP α ψ hα hα4 hang)
    simpa using h
  have hf3 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) K := hRflat
  -- smoothness of the summands
  have hs1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) :=
    smoothOpen_of_radial (fun n => ContDiffOn.mul (contDiffOn_zdiv n)
      (contDiffOn_aprof α hα hα4 n))
  have hs2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)) :=
    smoothOpen_mul (smoothOpen_of_radial (fun n => contDiffOn_two_div_one_add α n))
      (smoothOpen_of_angular (fun n => contDiffOn_psiDiv α ψ hang n))
  have hs3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) := by
    have hp : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => ((z + 1) / z * R z θ) * (1 / Work.Construction.s2 θ)) :=
      smoothOpen_mul (smoothOpen_mul (smoothOpen_of_radial contDiffOn_zdiv) hR)
        (smoothOpen_of_angular contDiffOn_inv_s2)
    refine smoothOpen_congr hp (fun z θ hz hθ hπ => ?_)
    ring
  -- add the pieces
  have h12 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) :=
    hAdd 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z)
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (C₁ * α) (Cm * ((α * 10080) * C₂)) (by positivity) (by positivity) hs1 hs2 hf1 hf2
  have hfull : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
        + (z + 1) / z * R z θ / Work.Construction.s2 θ)
      (Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)) :=
    hAdd 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ)
      (Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) K
      (by positivity) hK (smoothOpen_add hs1 hs2) hs3 h12 hf3
  -- the assembled constant is dominated by `max (Ca·(Ca·(C₁ + Cm·10080·C₂) + 1)) 1 · (α + K)`
  have hbound : Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)
      ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * (α + K) := by
    have hexp : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
        = Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂))) + Ca := by ring
    have hXY : Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))
        ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := by
      have h1 : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := le_max_left _ _
      have h2 : Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))
          ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) := by
        rw [hexp]
        exact le_add_of_nonneg_right (le_of_lt hCapos)
      exact le_trans h2 h1
    have hb3 : Ca ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := by
      have h1 : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := le_max_left _ _
      have h2 : Ca ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) := by
        have h3 : (1:ℝ) ≤ Ca * (C₁ + Cm * (10080 * C₂)) + 1 :=
          le_add_of_nonneg_left (by positivity)
        have h4 : Ca * 1 ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hCapos)
        simpa using h4
      exact le_trans h2 h1
    have hLHS : Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)
        = (Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))) * α + Ca * K := by ring
    rw [hLHS]
    calc (Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))) * α + Ca * K
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * α
            + max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * K :=
          add_le_add (mul_le_mul_of_nonneg_right hXY (le_of_lt hα))
            (mul_le_mul_of_nonneg_right hb3 hK)
      _ = max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * (α + K) := by ring
  exact flatW_mono hfull hbound

end Work.FTS.PhiStar.FlatWApi
