import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.window_ops
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.gauss_moments_le` — Gaussian moment bounds for the coherent-state transform

FS's `thm:Kafz` replaces the condensate operators by the complex numbers `z`, `z̄` and
integrates the resulting symbol against the Gaussian measure `dν(z) = e^{-‖z‖²} d²z/π`.
The two estimates needed to control the *window* (a Fock vector all of whose monomials
carry at most `n` particles) are

    `∫ ‖z‖² ‖Φ(split Ψ)(z)‖² dν ≤ (n+1) ⟪Ψ,Ψ⟫`,   `∫ ‖z‖ ‖Φ(split Ψ)(z)‖² dν ≤ √(n+1) ⟪Ψ,Ψ⟫`.

Both follow from the Bargmann isometry and the `c`-number substitution:

* `∫ ‖z‖²‖Φψz‖² dν = ‖Φ^{a₀†ψ}‖²_{L²} = ⟪a₀†ψ, a₀†ψ⟫ = ⟪ψ, (n₀+1)ψ⟫`, so it is
  `⟨a₀†ψ, a₀†ψ⟩ = ⟪ψ, n₀ψ⟫ + ⟪ψ,ψ⟫`, and `n₀` is the lattice operator multiplying the
  monomial `x^α` by `α 0 ≤ |α| ≤ n`, whence the bound with `(n+1)`;
* the second is the pointwise AM-GM `2‖z‖ ≤ t + ‖z‖²/t` at `t = √(n+1)` applied to the
  first, using `⟪Ψ,Ψ⟫ = ∫‖Φψz‖² dν`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## 1. The pointwise identity `⟪Φ(a₀†ψ)z, Φ(a₀†ψ)z⟫ = ‖z‖² ‖Φψz‖²` -/

/-- The inner product of a vector with itself, in the `Complex.ofReal` form of the
squared norm (rather than the `RCLike.ofReal` form of `inner_self_eq_norm_sq_to_K`). -/
lemma gm_inner_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  change Complex.ofReal ‖v‖ ^ 2 = Complex.ofReal (‖v‖ ^ 2)
  rw [← Complex.ofReal_pow]

lemma gm_inner_Phi_a0d_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : Work.BoseB4.FockCore E) (z : ℂ) :
    inner ℂ (Work.BoseB4.Phi (Work.BoseB4.a0d ψ) z) (Work.BoseB4.Phi (Work.BoseB4.a0d ψ) z)
      = ((‖z‖ ^ 2 * ‖Work.BoseB4.Phi ψ z‖ ^ 2 : ℝ) : ℂ) := by
  rw [gm_inner_self (Work.BoseB4.Phi (Work.BoseB4.a0d ψ) z), Work.BoseB4.Phi_a0d, norm_smul,
    Complex.norm_conj]
  congr 1
  ring

/-! ## 2. Integrability of the relevant real functions against `gauss` -/

/-- If the `ℂ`-valued function `z ↦ ↑(g z)` is integrable then so is the real-valued
`g` (the norm of `↑(g z)` is `|g z|`, and `g ≥ 0`). -/
lemma gm_integrable_of_ofReal {g : ℂ → ℝ} (hg : ∀ z, 0 ≤ g z)
    (h : Integrable (fun z => ((g z : ℝ) : ℂ)) Work.BoseB4.gauss) :
    Integrable g Work.BoseB4.gauss :=
  (h.norm).congr (Filter.Eventually.of_forall fun z => by
    show ‖((g z : ℝ) : ℂ)‖ = g z
    have h1 : ‖((g z : ℝ) : ℂ)‖ = |g z| := RCLike.norm_ofReal (g z)
    rw [h1, abs_of_nonneg (hg z)])

/-- The Bochner integral of a real function computed through the `ℂ`-valued integral of
its coercion: it is the real part. -/
lemma gm_integral_eq_re {g : ℂ → ℝ}
    (h : Integrable g Work.BoseB4.gauss) :
    ∫ z, g z ∂Work.BoseB4.gauss
      = (∫ z, ((g z : ℝ) : ℂ) ∂Work.BoseB4.gauss).re := by
  have h' := Complex.reCLM.integral_comp_comm h.ofReal
  simpa [Complex.reCLM_apply, Complex.ofReal_re] using h'

lemma gm_integrable_Phi_normSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : Work.BoseB4.FockCore E) :
    Integrable (fun z : ℂ => ‖Work.BoseB4.Phi ψ z‖ ^ 2) Work.BoseB4.gauss := by
  refine gm_integrable_of_ofReal (fun z => sq_nonneg _) ?_
  have hc := Work.BoseB4.integrable_kafz_integrand (E := E) 0 0 (1 : E →ₗ[ℂ] E) ψ
  refine hc.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [pow_zero, one_mul, Module.End.one_apply]
  exact gm_inner_self (Work.BoseB4.Phi ψ z)

lemma gm_integrable_Phi_normSq_moment2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : Work.BoseB4.FockCore E) :
    Integrable (fun z : ℂ => ‖z‖ ^ 2 * ‖Work.BoseB4.Phi ψ z‖ ^ 2) Work.BoseB4.gauss := by
  refine gm_integrable_of_ofReal (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
  have hc := Work.BoseB4.integrable_kafz_integrand (E := E) 0 0 (1 : E →ₗ[ℂ] E)
    (Work.BoseB4.a0d ψ)
  refine hc.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [pow_zero, one_mul, Module.End.one_apply]
  rw [gm_inner_Phi_a0d_self ψ z]

/-! ## 3. The two Gaussian moments of `Φ(split Ψ)` -/

lemma gm_gauss_Phi_normSq (Ψ : Work.BoseB4.RealFock m) :
    ∫ z, ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 ∂Work.BoseB4.gauss
      = Work.BoseB4.bomb m Ψ Ψ := by
  rw [gm_integral_eq_re (gm_integrable_Phi_normSq (Work.BoseB4.split Ψ))]
  have h2 : ∫ z, ((‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 : ℝ) : ℂ)
        ∂Work.BoseB4.gauss
      = Work.BoseB4.coreInner (Work.BoseB4.split Ψ) (Work.BoseB4.split Ψ) := by
    rw [Work.BoseB4.Bargmann_inner (Work.BoseB4.split Ψ) (Work.BoseB4.split Ψ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (gm_inner_self (Work.BoseB4.Phi (Work.BoseB4.split Ψ) z)).symm
  rw [h2, Work.BoseB4.Split_inner, Complex.ofReal_re]

lemma gm_gauss_Phi_normSq_moment2 (Ψ : Work.BoseB4.RealFock m) :
    ∫ z, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 ∂Work.BoseB4.gauss
      = (Work.BoseB4.coreInner (Work.BoseB4.a0d (Work.BoseB4.split Ψ))
          (Work.BoseB4.a0d (Work.BoseB4.split Ψ))).re := by
  rw [gm_integral_eq_re (gm_integrable_Phi_normSq_moment2 (Work.BoseB4.split Ψ))]
  congr 1
  rw [Work.BoseB4.Bargmann_inner (Work.BoseB4.a0d (Work.BoseB4.split Ψ))
    (Work.BoseB4.a0d (Work.BoseB4.split Ψ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact (gm_inner_Phi_a0d_self (Work.BoseB4.split Ψ) z).symm

/-! ## 4. The condensate number operator under `split` and the operator bound -/

lemma gm_split_n0 (x : Work.BoseB4.RealFock m) :
    Work.BoseB4.split (n0 x) = Work.BoseB4.numOp (Work.BoseB4.split x) := by
  have h1 := LinearMap.congr_fun (Work.BoseB4.Split_cre_zero (m := m))
    (Work.BoseB4.ann m 0 x)
  have h2 := LinearMap.congr_fun (Work.BoseB4.Split_ann_zero (m := m)) x
  simp only [LinearMap.comp_apply] at h1 h2
  show Work.BoseB4.split (Work.BoseB4.cre m 0 (Work.BoseB4.ann m 0 x))
    = Work.BoseB4.numOp (Work.BoseB4.split x)
  rw [h1, h2, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply]
  rfl

lemma gm_n0_apply (Ψ : Work.BoseB4.RealFock m) (α : Fin m →₀ ℕ) :
    (n0 Ψ) α = (α 0 : ℝ) * Ψ α := by
  conv_lhs => rw [← sum_single_support Ψ]
  rw [map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ b ∈ Ψ.support, (n0 (Finsupp.single b (Ψ b))) α
      = (if b = α then ((α 0 : ℝ) * Ψ α) else 0) := by
    intro b _
    have hb : Finsupp.single b (Ψ b) = (Ψ b) • Finsupp.single b (1 : ℝ) := by
      rw [Finsupp.smul_single]; simp
    rw [hb, map_smul, n0_single]
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hba : b = α
    · subst hba; rw [if_pos rfl, Finsupp.single_eq_same]; ring
    · rw [if_neg hba, Finsupp.single_eq_of_ne (Ne.symm hba)]; ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hα : α ∈ Ψ.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro b _ hb; exact if_neg (fun h : b = α => hb h)
    · intro h; exact absurd hα h
  · rw [Finset.sum_eq_zero]
    · rw [Finsupp.notMem_support_iff.mp hα, mul_zero]
    · intro b hb; exact if_neg (fun h : b = α => hα (h ▸ hb))

lemma gm_bomb_n0_le (Ψ : Work.BoseB4.RealFock m) (n : ℕ)
    (h : ∀ α ∈ Ψ.support, deg α ≤ n) :
    Work.BoseB4.bomb m Ψ (n0 Ψ) ≤ (n : ℝ) * Work.BoseB4.bomb m Ψ Ψ := by
  have hsupp : (n0 Ψ).support ⊆ Ψ.support := by
    intro α hα
    by_contra hα'
    rw [Finsupp.mem_support_iff, gm_n0_apply] at hα
    have hψ : Ψ α = 0 := Finsupp.notMem_support_iff.mp hα'
    rw [hψ, mul_zero] at hα
    exact hα rfl
  rw [Work.BoseB4.bomb_apply_union, Work.BoseB4.BombSelf.bomb_self_eq_sum,
    Finset.union_eq_left.mpr hsupp, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  have h0 : (α 0 : ℝ) ≤ (n : ℝ) := by
    have h1 : α 0 ≤ deg α := apply_le_deg α 0
    have h2 : deg α ≤ n := h α hα
    exact_mod_cast le_trans h1 h2
  have hK : 0 ≤ (Ψ α) ^ 2 * Work.BoseB4.mfac α :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Work.BoseB4.BombSelf.mfac_pos α))
  rw [gm_n0_apply]
  calc Work.BoseB4.mfac α * Ψ α * ((α 0 : ℝ) * Ψ α)
      = ((Ψ α) ^ 2 * Work.BoseB4.mfac α) * (α 0 : ℝ) := by ring
    _ ≤ ((Ψ α) ^ 2 * Work.BoseB4.mfac α) * (n : ℝ) := mul_le_mul_of_nonneg_left h0 hK
    _ = (n : ℝ) * ((Ψ α) ^ 2 * Work.BoseB4.mfac α) := by ring

lemma gm_coreInner_a0d_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ψ : Work.BoseB4.FockCore E) :
    Work.BoseB4.coreInner (Work.BoseB4.a0d ψ) (Work.BoseB4.a0d ψ)
      = Work.BoseB4.coreInner ψ (Work.BoseB4.numOp ψ) + Work.BoseB4.coreInner ψ ψ := by
  rw [Work.BoseB4.coreInner, Work.BoseB4.adjoint_a0d ψ (Work.BoseB4.a0d ψ)]
  have h : Work.BoseB4.a0 (Work.BoseB4.a0d ψ)
      = Work.BoseB4.a0d (Work.BoseB4.a0 ψ) + ψ := by
    have hh := LinearMap.congr_fun (Work.BoseB4.ccr (E := E)) ψ
    simpa [LinearMap.comp_apply] using hh
  rw [h, map_add, inner_add_right, Work.BoseB4.coreInner, Work.BoseB4.coreInner]
  rfl

lemma gm_coreInner_a0d_split_le (Ψ : Work.BoseB4.RealFock m) (n : ℕ)
    (h : ∀ α ∈ Ψ.support, deg α ≤ n) :
    (Work.BoseB4.coreInner (Work.BoseB4.a0d (Work.BoseB4.split Ψ))
        (Work.BoseB4.a0d (Work.BoseB4.split Ψ))).re
      ≤ ((n : ℝ) + 1) * Work.BoseB4.bomb m Ψ Ψ := by
  rw [gm_coreInner_a0d_self, ← gm_split_n0 Ψ,
    Work.BoseB4.Split_inner Ψ (n0 Ψ), Work.BoseB4.Split_inner Ψ Ψ,
    ← Complex.ofReal_add, Complex.ofReal_re]
  have hb := gm_bomb_n0_le Ψ n h
  have h0 := Work.BoseB4.Bomb_self_nonneg Ψ
  nlinarith [hb, h0]

/-! ## 5. The target -/

theorem gauss_moments_le {m : ℕ} [NeZero m] (Ψ : Work.BoseB4.RealFock m) (n : ℕ)
    (h : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) ≤ n) :
    (∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 ∂Work.BoseB4.gauss
        ≤ ((n : ℝ) + 1) * Work.BoseB4.bomb m Ψ Ψ) ∧
    (∫ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 ∂Work.BoseB4.gauss
        ≤ Real.sqrt ((n : ℝ) + 1) * Work.BoseB4.bomb m Ψ Ψ) := by
  have hdeg : ∀ α ∈ Ψ.support, deg α ≤ n := fun α hα => h α hα
  have h1 : ∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
        ∂Work.BoseB4.gauss ≤ ((n : ℝ) + 1) * Work.BoseB4.bomb m Ψ Ψ := by
    rw [gm_gauss_Phi_normSq_moment2 Ψ]
    exact gm_coreInner_a0d_split_le Ψ n hdeg
  refine ⟨h1, ?_⟩
  set t : ℝ := Real.sqrt ((n : ℝ) + 1) with ht
  have ht2 : t ^ 2 = (n : ℝ) + 1 := by rw [ht, Real.sq_sqrt]; positivity
  have htpos : 0 < t := by rw [ht]; exact Real.sqrt_pos.mpr (by positivity)
  have htne : t ≠ 0 := ne_of_gt htpos
  have hB : 0 ≤ Work.BoseB4.bomb m Ψ Ψ := Work.BoseB4.Bomb_self_nonneg Ψ
  -- pointwise AM–GM, in the form `(t + ‖z‖²/t)/2 = ‖z‖ + (‖z‖-t)²/(2t)`
  have hsplit : ∀ z : ℂ,
      (t + ‖z‖ ^ 2 / t) / 2 = ‖z‖ + (‖z‖ - t) ^ 2 / (2 * t) := by
    intro z
    field_simp
    ring
  have hpt : ∀ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
      ≤ ((t + ‖z‖ ^ 2 / t) / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 := by
    intro z
    have hf : 0 ≤ ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 := sq_nonneg _
    have hz : ‖z‖ ≤ (t + ‖z‖ ^ 2 / t) / 2 := by
      rw [hsplit z]
      exact le_add_of_nonneg_right
        (div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) htpos.le))
    exact mul_le_mul_of_nonneg_right hz hf
  have hpt2 : ∀ z : ℂ, ((t + ‖z‖ ^ 2 / t) / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
      = (t / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
        + (1 / (2 * t)) * (‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2) := by
    intro z
    field_simp
  have hRHSint : Integrable (fun z : ℂ =>
      ((t + ‖z‖ ^ 2 / t) / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2)
      Work.BoseB4.gauss :=
    (((gm_integrable_Phi_normSq (Work.BoseB4.split Ψ)).const_mul (t / 2)).add
      ((gm_integrable_Phi_normSq_moment2 (Work.BoseB4.split Ψ)).const_mul (1 / (2 * t)))).congr
      (Filter.Eventually.of_forall fun z => (hpt2 z).symm)
  have hLHSint : Integrable (fun z : ℂ =>
      ‖z‖ * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2) Work.BoseB4.gauss := by
    refine Integrable.mono'
      ((gm_integrable_Phi_normSq (Work.BoseB4.split Ψ)).add
        (gm_integrable_Phi_normSq_moment2 (Work.BoseB4.split Ψ))) ?_ ?_
    · exact (continuous_norm.aestronglyMeasurable).mul
        (gm_integrable_Phi_normSq (Work.BoseB4.split Ψ)).1
    · filter_upwards with z
      have hf : 0 ≤ ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 := sq_nonneg _
      have hz1 : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg z) hf)]
      calc ‖z‖ * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
          ≤ (1 + ‖z‖ ^ 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hz1 hf
        _ = ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
            + ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 := by ring
  have hIntR : ∫ z : ℂ, ((t + ‖z‖ ^ 2 / t) / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
        ∂Work.BoseB4.gauss
      = (t / 2) * Work.BoseB4.bomb m Ψ Ψ
        + (1 / (2 * t)) * (∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
            ∂Work.BoseB4.gauss) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt2),
      integral_add ((gm_integrable_Phi_normSq (Work.BoseB4.split Ψ)).const_mul (t / 2))
        ((gm_integrable_Phi_normSq_moment2 (Work.BoseB4.split Ψ)).const_mul (1 / (2 * t))),
      integral_const_mul, integral_const_mul, gm_gauss_Phi_normSq]
  calc ∫ z : ℂ, ‖z‖ * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2 ∂Work.BoseB4.gauss
      ≤ ∫ z : ℂ, ((t + ‖z‖ ^ 2 / t) / 2) * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
          ∂Work.BoseB4.gauss := integral_mono hLHSint hRHSint (fun z => hpt z)
    _ = (t / 2) * Work.BoseB4.bomb m Ψ Ψ
        + (1 / (2 * t)) * (∫ z : ℂ, ‖z‖ ^ 2 * ‖Work.BoseB4.Phi (Work.BoseB4.split Ψ) z‖ ^ 2
            ∂Work.BoseB4.gauss) := hIntR
    _ ≤ (t / 2) * Work.BoseB4.bomb m Ψ Ψ
        + (1 / (2 * t)) * (((n : ℝ) + 1) * Work.BoseB4.bomb m Ψ Ψ) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 ?_)
          positivity
    _ = (t / 2) * Work.BoseB4.bomb m Ψ Ψ
        + (1 / (2 * t)) * (t ^ 2 * Work.BoseB4.bomb m Ψ Ψ) := by rw [← ht2]
    _ = t * Work.BoseB4.bomb m Ψ Ψ := by
          have hstep : (1 / (2 * t)) * (t ^ 2 * Work.BoseB4.bomb m Ψ Ψ)
              = (t / 2) * Work.BoseB4.bomb m Ψ Ψ := by
            field_simp
          rw [hstep]; ring

end Work.BoseBoxFock
