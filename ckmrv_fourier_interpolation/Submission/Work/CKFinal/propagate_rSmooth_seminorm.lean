import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.CKFinal.bound_of_propagates_uniform
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.CKFinal.iteratedDeriv_iteratedDeriv
import Submission.Work.CKFinal.norm_div_sub_div_le
import Submission.Work.CKFinal.dq_propagation
import Submission.Work.CKFinal.exists_deriv_of_bound

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

# propagate_rSmooth_seminorm  (namespace Work.CKFinal)  — (f), part 2: from 𝒟 to ℍ

Abstract: Ψ r global holomorphic with T2op (Ψ r) = h r, S2op k (Ψ r) = 0; r-smooth with moderate
seminorms on 𝒟; h explicit. Conclude r-smoothness and moderate seminorms on all of ℍ.
(Applied with k = d/2, Ψ r = extension of F₂ r, h r = −T2op (gaussTerm · r).)

PROVED assets: bound_of_propagates_uniform (new, first in the DAG); `Work.Asymptotics.Propagates`;
Mathlib `TendstoLocallyUniformlyOn.differentiableOn`, `hasDerivAt_iff_tendsto_slope`,
`contDiff_of_differentiable_iteratedDeriv`, `UpperHalfPlane.mdifferentiable_iff`.

Proof sketch (constants of bound_of_propagates_uniform are chosen BEFORE the functions — essential):
1. One step. Fix r. For h' ≠ 0 put Q_{h'} := (Ψ(r+h') − Ψ r)/h' : holomorphic, Propagates k univ with
   defects ((h(r+h')−h r)/h', 0). On 𝒟 (Taylor, using ∂²_r on 𝒟 uniformly for |s−r| ≤ 1):
   |Q_a − Q_b| ≤ (|a|+|b|)·C₂ scale^{N₂}; defects likewise with hh_bd. Uniform bound ⇒
   |Q_a − Q_b|(τ) ≤ C(|a|+|b|)(C₂+C₂') scale(τ)^N on ℍ ⇒ Q_{h'} Cauchy, locally uniformly (scale is
   bounded on compacts) ⇒ limit Ψ' holomorphic on ℍ, HasDerivAt (fun s => Ψ s τ) (Ψ' τ) r for EVERY τ,
   T2op Ψ' = ∂_r h, S2op Ψ' = 0 (limits of finite combinations).
2. Induction on l: iteratedDeriv l (Ψ · τ) r = Ψ^{(l)} r τ with Ψ^{(l)} r holomorphic and solving the
   recurrences with defect ∂^l h (hh_holo). Hence ContDiff ∞ (contDiff_of_differentiable_iteratedDeriv).
3. Bounds: for fixed r apply the uniform lemma to f = r^{k'}Ψ^{(l)} r, h₁ = r^{k'}∂^l h r, h₂ = 0 with
   Cf from hD_bd, C₁ from hh_bd (same Nf := max of the two exponents) ⇒ uniform in r.

--imports: Submission.Work.Asymptotics.PropagateDefs Submission.Work.Asymptotics.DomainD Submission.Work.Kernels.ModerateGrowth (+ the bound_of_propagates_uniform module)
-/

namespace Work.CKFinal

open UpperHalfPlane Filter
open scoped ContDiff Manifold Topology

lemma deriv_deriv_eq_iteratedDeriv_two (f : ℝ → ℂ) :
    deriv (deriv f) = iteratedDeriv 2 f := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

lemma contDiff_iteratedDeriv {f : ℝ → ℂ} (h : ContDiff ℝ ∞ f) (l : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv l f) := by
  rw [contDiff_iff_iteratedDeriv]
  constructor
  · intro m _
    rw [iteratedDeriv_iteratedDeriv]
    exact (contDiff_iff_iteratedDeriv.mp h).1 (l + m) le_top
  · intro m _
    rw [iteratedDeriv_iteratedDeriv]
    exact (contDiff_iff_iteratedDeriv.mp h).2 (l + m) (WithTop.coe_lt_top (l + m))

lemma differentiable_iteratedDeriv_of_contDiff {f : ℝ → ℂ} (h : ContDiff ℝ ∞ f) (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.mp h).2 m (WithTop.coe_lt_top m)

/-! ## Linearity of `T2op` and `S2op` -/

lemma T2op_sub (F G : ℍ → ℂ) :
    Work.Kernels.T2op (F - G) = Work.Kernels.T2op F - Work.Kernels.T2op G := by
  ext τ
  simp only [Work.Kernels.T2op, Pi.sub_apply]
  ring

lemma T2op_const_mul (c : ℂ) (F : ℍ → ℂ) :
    Work.Kernels.T2op (fun τ => c * F τ) = fun τ => c * Work.Kernels.T2op F τ := by
  ext τ
  simp only [Work.Kernels.T2op]
  ring

lemma S2op_sub (k : ℤ) (F G : ℍ → ℂ) :
    Work.Asymptotics.S2op k (F - G) = Work.Asymptotics.S2op k F - Work.Asymptotics.S2op k G := by
  ext τ
  simp only [Pi.sub_apply, Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply]
  ring

lemma S2op_const_mul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) :
    Work.Asymptotics.S2op k (fun τ => c * F τ) = fun τ => c * Work.Asymptotics.S2op k F τ := by
  ext τ
  simp only [Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply]
  ring

lemma S2op_apply_expand (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) :
    Work.Asymptotics.S2op k F τ
      = F (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) * ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)
        - 2 * (F (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
        + F (ModularGroup.S • τ) * ((τ : ℍ) : ℂ) ^ (-k) := by
  rw [Work.Asymptotics.S2op_apply_eq]
  simp only [Work.Kernels.slash_S_apply]

lemma norm_ofReal_mul (c : ℝ) (z : ℂ) (hc : 0 ≤ c) : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
  rw [norm_mul, show ‖(c : ℂ)‖ = c from by simp [abs_of_nonneg hc]]

/-! ## Limits of difference quotients -/

lemma tendsto_nhdsWithin_punctured_add (r : ℝ) :
    Tendsto (fun a : ℝ => r + a) (𝓝[≠] (0 : ℝ)) (𝓝[≠] r) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have heq : (fun a : ℝ => r + a) = (fun _ : ℝ => r) + id := by funext a; simp
    rw [heq]
    simpa using ((continuous_const.add continuous_id).tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha ⊢
    intro h
    exact ha (by linarith)

/-- The difference quotients of a function tend to its derivative. -/
lemma tendsto_div_add_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {r : ℝ} (h : HasDerivAt f f' r) :
    Tendsto (fun a : ℝ => (f (r + a) - f r) / a) (𝓝[≠] (0 : ℝ)) (𝓝 f') := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp h
  have hcomp := hslope.comp (tendsto_nhdsWithin_punctured_add r)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  simp only [Function.comp_apply]
  rw [slope, add_sub_cancel_left, vsub_eq_sub, Complex.real_smul, Complex.ofReal_inv,
    div_eq_inv_mul]

/-- Squeeze: a pointwise Cauchy-type bound gives convergence. -/
lemma tendsto_of_bound {F : ℝ → ℍ → ℂ} {D : ℍ → ℂ} {D0 M : ℝ}
    (hbd : ∀ (a : ℝ), a ≠ 0 → ∀ τ : ℍ, ‖F a τ - D τ‖ ≤ D0 * |a| * (Work.Kernels.scale τ) ^ M)
    (τ : ℍ) : Tendsto (fun a : ℝ => F a τ) (𝓝[≠] (0 : ℝ)) (𝓝 (D τ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun a : ℝ => D0 * |a| * (Work.Kernels.scale τ) ^ M)
    (Eventually.of_forall (fun a => norm_nonneg _)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact hbd a ha τ
  · have h1 : Tendsto (fun a : ℝ => |a|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun a : ℝ => a) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
        (continuous_id : Continuous fun a : ℝ => a).tendsto (0 : ℝ) |>.mono_left
          (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa using h0.abs
    have h2 : Tendsto (fun a : ℝ => D0 * |a| * (Work.Kernels.scale τ) ^ M)
        (𝓝[≠] (0 : ℝ)) (𝓝 (D0 * 0 * (Work.Kernels.scale τ) ^ M)) :=
      (tendsto_const_nhds.mul h1).mul tendsto_const_nhds
    simpa using h2

/-! ## Local copies of the delegated lemmas (to be replaced by imports) -/

/-! ## The level predicate -/

/-- The information we carry about the `l`-th `r`-derivative family. -/
structure Lvl (k : ℤ) (Ψ h : ℝ → ℍ → ℂ) (l : ℕ) (G : ℝ → ℍ → ℂ) : Prop where
  holo : ∀ r : ℝ,
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (G r)
  defT : ∀ (r : ℝ) (τ : ℍ), Work.Kernels.T2op (G r) τ = iteratedDeriv l (fun s : ℝ => h s τ) r
  defS : ∀ (r : ℝ) (τ : ℍ), Work.Asymptotics.S2op k (G r) τ = 0
  ident : ∀ (r : ℝ) (τ : ℍ), G r τ = iteratedDeriv l (fun s : ℝ => Ψ s τ) r

/-! ## The one-step propagation -/

private lemma step (k : ℤ) (Ψ h : ℝ → ℍ → ℂ)
    (hh_smooth : ∀ τ : ℍ, ContDiff ℝ ∞ (fun r : ℝ => h r τ))
    (hh_holo : ∀ (l : ℕ) (r : ℝ),
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => iteratedDeriv l (fun s : ℝ => h s τ) r))
    (hh_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : ℍ) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => h s τ) r‖ ≤ C * (Work.Kernels.scale τ) ^ N)
    (hD_smooth : ∀ τ : ℍ, τ ∈ Work.Asymptotics.DomainD → ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ))
    (hD_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ τ : ℍ, τ ∈ Work.Asymptotics.DomainD →
      ∀ r : ℝ, |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N)
    (l : ℕ) (G : ℝ → ℍ → ℂ) (hG : Lvl k Ψ h l G) :
    ∃ G' : ℝ → ℍ → ℂ, Lvl k Ψ h (l + 1) G' ∧
      (∀ (r : ℝ) (τ : ℍ), HasDerivAt (fun s : ℝ => G s τ) (G' r τ) r) := by
  let H : ℝ → ℍ → ℂ := fun r τ => iteratedDeriv l (fun s : ℝ => h s τ) r
  have hHsmooth : ∀ τ : ℍ, ContDiff ℝ ∞ (fun s : ℝ => H s τ) := by
    intro τ
    have hfun : (fun s : ℝ => H s τ) = iteratedDeriv l (fun s : ℝ => h s τ) := by
      funext s; rfl
    rw [hfun]
    exact contDiff_iteratedDeriv (hh_smooth τ) l
  have hHholo : ∀ (l' : ℕ) (r : ℝ),
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => iteratedDeriv l' (fun s : ℝ => H s τ) r) := by
    intro l' r
    have hfun : (fun τ : ℍ => iteratedDeriv l' (fun s : ℝ => H s τ) r)
        = (fun τ : ℍ => iteratedDeriv (l + l') (fun s : ℝ => h s τ) r) := by
      funext τ
      have h1 : (fun s : ℝ => H s τ) = iteratedDeriv l (fun s : ℝ => h s τ) := by
        funext s; rfl
      rw [h1, iteratedDeriv_iteratedDeriv]
    rw [hfun]
    exact hh_holo (l + l') r
  have hHdiff : ∀ τ : ℍ, (∀ x : ℝ, DifferentiableAt ℝ (fun s : ℝ => H s τ) x) ∧
      (∀ x : ℝ, DifferentiableAt ℝ (deriv (fun s : ℝ => H s τ)) x) := by
    intro τ
    refine ⟨fun x => ((hHsmooth τ).differentiable (by simp)).differentiableAt, fun x => ?_⟩
    have h2 : Differentiable ℝ (iteratedDeriv 1 (fun s : ℝ => H s τ)) :=
      differentiable_iteratedDeriv_of_contDiff (hHsmooth τ) 1
    simpa [iteratedDeriv_one] using h2.differentiableAt
  obtain ⟨CH, NH, hCH, hNH, hbdH⟩ := hh_bd 0 (l + 2)
  have hH2 : ∀ (τ : ℍ) (x : ℝ),
      ‖deriv (deriv (fun s : ℝ => H s τ)) x‖ ≤ CH * (Work.Kernels.scale τ) ^ NH := by
    intro τ x
    have hfun : (fun s : ℝ => H s τ) = iteratedDeriv l (fun s : ℝ => h s τ) := by
      funext s; rfl
    rw [hfun, deriv_deriv_eq_iteratedDeriv_two, iteratedDeriv_iteratedDeriv]
    simpa using hbdH τ x
  obtain ⟨CG, NG, hCG, hNG, hbdG⟩ := hD_bd 0 (l + 2)
  have hG2 : ∀ τ ∈ Work.Asymptotics.DomainD, ∀ x : ℝ,
      ‖deriv (deriv (fun s : ℝ => G s τ)) x‖ ≤ CG * (Work.Kernels.scale τ) ^ NG := by
    intro τ hτ x
    have hfun : (fun s : ℝ => G s τ) = iteratedDeriv l (fun s : ℝ => Ψ s τ) := by
      funext s; exact hG.ident s τ
    rw [hfun, deriv_deriv_eq_iteratedDeriv_two, iteratedDeriv_iteratedDeriv]
    simpa using hbdG τ hτ x
  have hGdiff : ∀ τ ∈ Work.Asymptotics.DomainD,
      (∀ x : ℝ, DifferentiableAt ℝ (fun s : ℝ => G s τ) x) ∧
      (∀ x : ℝ, DifferentiableAt ℝ (deriv (fun s : ℝ => G s τ)) x) := by
    intro τ hτ
    have hcd : ContDiff ℝ ∞ (fun s : ℝ => G s τ) := by
      have hfun : (fun s : ℝ => G s τ) = iteratedDeriv l (fun s : ℝ => Ψ s τ) := by
        funext s; exact hG.ident s τ
      rw [hfun]
      exact contDiff_iteratedDeriv (hD_smooth τ hτ) l
    refine ⟨fun x => (hcd.differentiable (by simp)).differentiableAt, fun x => ?_⟩
    have h2 : Differentiable ℝ (iteratedDeriv 1 (fun s : ℝ => G s τ)) :=
      differentiable_iteratedDeriv_of_contDiff hcd 1
    simpa [iteratedDeriv_one] using h2.differentiableAt
  obtain ⟨C, N, hC, hN, hbound⟩ := dq_propagation k (max NG NH)
  have hbd : ∀ r (a b : ℝ) (τ : ℍ), a ≠ 0 → b ≠ 0 →
      ‖(G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b‖
        ≤ C * (CG + CH) * (|a| + |b|) * (Work.Kernels.scale τ) ^ N :=
    fun r => hbound G H CG CH NG NH hCG hCH (le_max_left _ _) (le_max_right _ _)
      hG.holo hHholo hG.defT hG.defS hGdiff hHdiff hG2 hH2 r
  have hmain : ∀ r : ℝ, ∃ D : ℍ → ℂ,
      (∀ τ : ℍ, HasDerivAt (fun s : ℝ => G s τ) (D τ) r) ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D ∧
      (∀ (a : ℝ) (τ : ℍ), a ≠ 0 →
        ‖(G (r + a) τ - G r τ) / a - D τ‖ ≤ C * (CG + CH) * |a| * (Work.Kernels.scale τ) ^ N) := by
    intro r
    exact exists_deriv_of_bound hG.holo (by positivity) hN (hbd r)
  choose G' hspec using hmain
  refine ⟨G', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r; exact (hspec r).2.1
  · intro r τ
    obtain ⟨hd, hmd, hbnd⟩ := hspec r
    set Q : ℝ → ℍ → ℂ := fun a τ' => (G (r + a) τ' - G r τ') / a with hQdef
    have hQT : ∀ a ≠ 0, Work.Kernels.T2op (Q a) τ = (H (r + a) τ - H r τ) / a := by
      intro a ha
      have h1 : Q a = fun τ' : ℍ => (a : ℂ)⁻¹ * (G (r + a) τ' - G r τ') := by
        funext τ'; simp only [hQdef]; rw [div_eq_inv_mul]
      have h2 : (fun τ' : ℍ => (a : ℂ)⁻¹ * (G (r + a) τ' - G r τ'))
          = fun τ' : ℍ => (a : ℂ)⁻¹ * ((G (r + a) - G r) τ') := rfl
      rw [h1, h2, T2op_const_mul, T2op_sub]
      simp only [Pi.sub_apply, Pi.mul_apply]
      rw [hG.defT, hG.defT, div_eq_inv_mul]
    have hHasDeriv : HasDerivAt (fun s : ℝ => H s τ)
        (iteratedDeriv (l + 1) (fun s : ℝ => h s τ) r) r := by
      have hdH := (((hHsmooth τ).differentiable (by simp)).differentiableAt (x := r)).hasDerivAt
      have hval : deriv (fun s : ℝ => H s τ) r = iteratedDeriv (l + 1) (fun s : ℝ => h s τ) r := by
        have hfun : (fun s : ℝ => H s τ) = iteratedDeriv l (fun s : ℝ => h s τ) := by
          funext s; rfl
        rw [hfun, ← iteratedDeriv_succ]
      rwa [hval] at hdH
    have hlim1 : Tendsto (fun a : ℝ => Work.Kernels.T2op (Q a) τ) (𝓝[≠] (0 : ℝ))
        (𝓝 (iteratedDeriv (l + 1) (fun s : ℝ => h s τ) r)) := by
      have hq := tendsto_div_add_of_hasDerivAt hHasDeriv
      refine hq.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact (hQT a ha).symm
    have hpt : ∀ τ' : ℍ, Tendsto (fun a : ℝ => Q a τ') (𝓝[≠] (0 : ℝ)) (𝓝 ((G' r) τ')) :=
      fun τ' => tendsto_of_bound (F := Q) (D := G' r) (D0 := C * (CG + CH)) (M := N)
        (fun a ha τ'' => hbnd a τ'' ha) τ'
    have hlim2 : Tendsto (fun a : ℝ => Work.Kernels.T2op (Q a) τ) (𝓝[≠] (0 : ℝ))
        (𝓝 (Work.Kernels.T2op (G' r) τ)) := by
      have h1 := hpt ((2 : ℝ) +ᵥ τ)
      have h2 := hpt ((1 : ℝ) +ᵥ τ)
      have h3 := hpt τ
      have hcomb : Tendsto
          (fun a : ℝ => Q a ((2 : ℝ) +ᵥ τ) - 2 * Q a ((1 : ℝ) +ᵥ τ) + Q a τ)
          (𝓝[≠] (0 : ℝ))
          (𝓝 ((G' r) ((2 : ℝ) +ᵥ τ) - 2 * (G' r) ((1 : ℝ) +ᵥ τ) + (G' r) τ)) :=
        (h1.sub (h2.const_mul 2)).add h3
      have hfun : (fun a : ℝ => Work.Kernels.T2op (Q a) τ)
          = fun a : ℝ => Q a ((2 : ℝ) +ᵥ τ) - 2 * Q a ((1 : ℝ) +ᵥ τ) + Q a τ := rfl
      have hval : Work.Kernels.T2op (G' r) τ
          = (G' r) ((2 : ℝ) +ᵥ τ) - 2 * (G' r) ((1 : ℝ) +ᵥ τ) + (G' r) τ := rfl
      rw [hfun, hval]
      exact hcomb
    exact tendsto_nhds_unique hlim2 hlim1
  · intro r τ
    obtain ⟨hd, hmd, hbnd⟩ := hspec r
    set Q : ℝ → ℍ → ℂ := fun a τ' => (G (r + a) τ' - G r τ') / a with hQdef
    have hQS : ∀ a ≠ 0, Work.Asymptotics.S2op k (Q a) τ = 0 := by
      intro a ha
      have h1 : Q a = fun τ' : ℍ => (a : ℂ)⁻¹ * (G (r + a) τ' - G r τ') := by
        funext τ'; simp only [hQdef]; rw [div_eq_inv_mul]
      have h2 : (fun τ' : ℍ => (a : ℂ)⁻¹ * (G (r + a) τ' - G r τ'))
          = fun τ' : ℍ => (a : ℂ)⁻¹ * ((G (r + a) - G r) τ') := rfl
      rw [h1, h2, S2op_const_mul, S2op_sub]
      simp only [Pi.sub_apply, Pi.mul_apply]
      rw [hG.defS, hG.defS, sub_zero, mul_zero]
    have hSlim1 : Tendsto (fun a : ℝ => Work.Asymptotics.S2op k (Q a) τ) (𝓝[≠] (0 : ℝ))
        (𝓝 0) := by
      refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact (hQS a ha).symm
    have hpt : ∀ τ' : ℍ, Tendsto (fun a : ℝ => Q a τ') (𝓝[≠] (0 : ℝ)) (𝓝 ((G' r) τ')) :=
      fun τ' => tendsto_of_bound (F := Q) (D := G' r) (D0 := C * (CG + CH)) (M := N)
        (fun a ha τ'' => hbnd a τ'' ha) τ'
    have hSlim2 : Tendsto (fun a : ℝ => Work.Asymptotics.S2op k (Q a) τ) (𝓝[≠] (0 : ℝ))
        (𝓝 (Work.Asymptotics.S2op k (G' r) τ)) := by
      have h1 := (hpt (ModularGroup.S • ((2 : ℝ) +ᵥ τ))).mul_const (((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
      have h2 := (hpt (ModularGroup.S • ((1 : ℝ) +ᵥ τ))).mul_const (((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
      have h3 := (hpt (ModularGroup.S • τ)).mul_const ((((τ : ℍ)) : ℂ) ^ (-k))
      have hcomb : Tendsto
          (fun a : ℝ => Q a (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) * ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)
            - 2 * (Q a (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
            + Q a (ModularGroup.S • τ) * (((τ : ℍ)) : ℂ) ^ (-k))
          (𝓝[≠] (0 : ℝ))
          (𝓝 ((G' r) (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) * ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)
            - 2 * ((G' r) (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
            + (G' r) (ModularGroup.S • τ) * (((τ : ℍ)) : ℂ) ^ (-k))) :=
        (h1.sub (h2.const_mul 2)).add h3
      have hfun : (fun a : ℝ => Work.Asymptotics.S2op k (Q a) τ)
          = fun a : ℝ => Q a (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) * ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)
            - 2 * (Q a (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
            + Q a (ModularGroup.S • τ) * (((τ : ℍ)) : ℂ) ^ (-k) := by
        funext a; rw [S2op_apply_expand]
      have hval : Work.Asymptotics.S2op k (G' r) τ
          = (G' r) (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) * ((((2 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k)
            - 2 * ((G' r) (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) ^ (-k))
            + (G' r) (ModularGroup.S • τ) * (((τ : ℍ)) : ℂ) ^ (-k) :=
        S2op_apply_expand k (G' r) τ
      rw [hfun, hval]
      exact hcomb
    exact tendsto_nhds_unique hSlim2 hSlim1
  · intro r τ
    obtain ⟨hd, hmd, hbnd⟩ := hspec r
    have hfun : (fun s : ℝ => G s τ) = iteratedDeriv l (fun s : ℝ => Ψ s τ) := by
      funext s; exact hG.ident s τ
    rw [← (hd τ).deriv, hfun, ← iteratedDeriv_succ]
  · intro r τ; exact (hspec r).1 τ


/-! ## The induction and the main theorem -/

private lemma main_aux (k : ℤ) (Ψ h : ℝ → ℍ → ℂ)
    (hΨ : ∀ r : ℝ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (Ψ r))
    (hT : ∀ (r : ℝ) (τ : ℍ), Work.Kernels.T2op (Ψ r) τ = h r τ)
    (hS : ∀ (r : ℝ) (τ : ℍ), Work.Asymptotics.S2op k (Ψ r) τ = 0)
    (hh_smooth : ∀ τ : ℍ, ContDiff ℝ ∞ (fun r : ℝ => h r τ))
    (hh_holo : ∀ (l : ℕ) (r : ℝ),
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => iteratedDeriv l (fun s : ℝ => h s τ) r))
    (hh_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : ℍ) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => h s τ) r‖ ≤ C * (Work.Kernels.scale τ) ^ N)
    (hD_smooth : ∀ τ : ℍ, τ ∈ Work.Asymptotics.DomainD → ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ))
    (hD_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ τ : ℍ, τ ∈ Work.Asymptotics.DomainD →
      ∀ r : ℝ, |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) :
    (∀ τ : ℍ, ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ)) ∧
    (∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : ℍ) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) := by
  have hbase : Lvl k Ψ h 0 Ψ :=
    { holo := hΨ
      defT := by intro r τ; rw [hT r τ, iteratedDeriv_zero]
      defS := hS
      ident := by intro r τ; rw [iteratedDeriv_zero] }
  have hQ : ∀ l : ℕ, ∃ G G' : ℝ → ℍ → ℂ, Lvl k Ψ h l G ∧ Lvl k Ψ h (l + 1) G' ∧
      (∀ (r : ℝ) (τ : ℍ), HasDerivAt (fun s : ℝ => G s τ) (G' r τ) r) := by
    intro l
    induction l with
    | zero =>
      obtain ⟨G', hG', hlink⟩ :=
        step k Ψ h hh_smooth hh_holo hh_bd hD_smooth hD_bd 0 Ψ hbase
      exact ⟨Ψ, G', hbase, hG', hlink⟩
    | succ l ih =>
      obtain ⟨G, G', hG, hG', hlink⟩ := ih
      obtain ⟨G'', hG'', hlink'⟩ :=
        step k Ψ h hh_smooth hh_holo hh_bd hD_smooth hD_bd (l + 1) G' hG'
      exact ⟨G', G'', hG', hG'', hlink'⟩
  have hLvl : ∀ l : ℕ, ∃ G : ℝ → ℍ → ℂ, Lvl k Ψ h l G := by
    intro l
    obtain ⟨G, -, hG, -, -⟩ := hQ l
    exact ⟨G, hG⟩
  have hlinkΨ : ∀ l : ℕ, ∀ (r : ℝ) (τ : ℍ),
      HasDerivAt (fun s : ℝ => iteratedDeriv l (fun u : ℝ => Ψ u τ) s)
        (iteratedDeriv (l + 1) (fun u : ℝ => Ψ u τ) r) r := by
    intro l
    obtain ⟨G, G', hG, hG', hlink⟩ := hQ l
    intro r τ
    have h1 : (fun s : ℝ => G s τ) = iteratedDeriv l (fun u : ℝ => Ψ u τ) := by
      funext s; exact hG.ident s τ
    have h2 : G' r τ = iteratedDeriv (l + 1) (fun u : ℝ => Ψ u τ) r := hG'.ident r τ
    rw [← h1, ← h2]
    exact hlink r τ
  refine ⟨?_, ?_⟩
  · intro τ
    apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
    intro m _
    exact fun r => (hlinkΨ m r τ).differentiableAt
  · intro k' l
    obtain ⟨G, hG⟩ := hLvl l
    obtain ⟨Cf, NfD, hCf, hNfD, hbdD⟩ := hD_bd k' l
    obtain ⟨C₁, NfH, hC₁, hNfH, hbdH⟩ := hh_bd k' l
    obtain ⟨C, N, hC, hN, hbound⟩ := bound_of_propagates_uniform k (max NfD NfH)
    refine ⟨C * (Cf + C₁ + 0), N, by positivity, hN, ?_⟩
    intro τ r
    set c : ℝ := |r| ^ k' with hcdef
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    set f : ℍ → ℂ := fun τ' => (c : ℂ) * G r τ' with hfdef
    set h₁ : ℍ → ℂ := fun τ' => (c : ℂ) * iteratedDeriv l (fun s : ℝ => h s τ') r with hh₁def
    have hprop : Work.Asymptotics.Propagates k Set.univ f h₁ 0 := by
      refine ⟨isOpen_univ, ?_, ?_, ?_, ?_, ?_⟩
      · exact (hh_holo l r).const_smul (c : ℂ)
      · exact mdifferentiable_const
      · exact mdifferentiableOn_univ.mpr ((hG.holo r).const_smul (c : ℂ))
      · intro τ' _ _ _
        simp only [hfdef]
        rw [T2op_const_mul]
        simp only [Pi.mul_apply]
        rw [hG.defT]
      · intro τ' _ _ _
        simp only [hfdef]
        rw [S2op_const_mul]
        simp only [Pi.mul_apply]
        rw [hG.defS, mul_zero]
        rfl
    have hb1 : ∀ τ' ∈ Work.Asymptotics.DomainD,
        ‖f τ'‖ ≤ Cf * (Work.Kernels.scale τ') ^ (max NfD NfH) := by
      intro τ' hτ'
      have h0 := hbdD τ' hτ' r
      have h1 : ‖f τ'‖ = c * ‖G r τ'‖ := by
        show ‖(c : ℂ) * G r τ'‖ = c * ‖G r τ'‖
        exact norm_ofReal_mul c (G r τ') hc0
      have h2 : ‖G r τ'‖ = ‖iteratedDeriv l (fun s : ℝ => Ψ s τ') r‖ := by
        rw [hG.ident r τ']
      rw [h1, h2, hcdef]
      exact le_trans h0 (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ') (le_max_left _ _)) hCf)
    have hb2 : ∀ τ' : ℍ, ‖h₁ τ'‖ ≤ C₁ * (Work.Kernels.scale τ') ^ (max NfD NfH) := by
      intro τ'
      have h0 := hbdH τ' r
      have h1 : ‖h₁ τ'‖ = c * ‖iteratedDeriv l (fun s : ℝ => h s τ') r‖ := by
        show ‖(c : ℂ) * iteratedDeriv l (fun s : ℝ => h s τ') r‖
          = c * ‖iteratedDeriv l (fun s : ℝ => h s τ') r‖
        exact norm_ofReal_mul c (iteratedDeriv l (fun s : ℝ => h s τ') r) hc0
      rw [h1, hcdef]
      exact le_trans h0 (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ') (le_max_right _ _)) hC₁)
    have hb3 : ∀ τ' : ℍ, ‖(0 : ℍ → ℂ) τ'‖
        ≤ 0 * (Work.Kernels.scale τ') ^ (max NfD NfH) := by
      intro τ'; simp
    have hmain := hbound f h₁ 0 Cf C₁ 0 hprop hCf hC₁ le_rfl hb1 hb2 hb3 τ
    have hnorm : ‖f τ‖ = |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖ := by
      show ‖(c : ℂ) * G r τ‖ = |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
      rw [norm_ofReal_mul c (G r τ) hc0, hcdef, hG.ident r τ]
    rw [← hnorm]
    exact hmain


/-- Propagation of `r`-smoothness and of the weighted `r`-seminorm bounds from `𝒟` to `ℍ` for a
family of global solutions `Ψ r` of `(T-I)²Ψ = h`, `S(T-I)²Ψ = 0`. -/
theorem propagate_rSmooth_seminorm (k : ℤ) (Ψ h : ℝ → UpperHalfPlane → ℂ)
    (hΨ : ∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (Ψ r))
    (hT : ∀ (r : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (Ψ r) τ = h r τ)
    (hS : ∀ (r : ℝ) (τ : UpperHalfPlane), Work.Asymptotics.S2op k (Ψ r) τ = 0)
    (hh_smooth : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (fun r : ℝ => h r τ))
    (hh_holo : ∀ (l : ℕ) (r : ℝ),
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ => h s τ) r))
    (hh_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => h s τ) r‖ ≤ C * (Work.Kernels.scale τ) ^ N)
    (hD_smooth : ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
      ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ))
    (hD_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → ∀ r : ℝ,
        |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    (∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ)) ∧
    ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  exact main_aux k Ψ h hΨ hT hS hh_smooth hh_holo hh_bd hD_smooth hD_bd

end Work.CKFinal
