/-
# `Work.FTS.PhiStar.Gegenbauer.eFam_complete` — completeness of the Dirichlet eigenbasis

The Dirichlet eigenfunctions of `Work.Elliptic.Lzero` on `(0, π/2)` are

  `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`   (`= cos θ · gC (2m+1) (sin θ)`),

with eigenvalues `lam m = 2m(2m+5)` (`eFam_Lzero`); they are mutually orthogonal with respect
to the self-adjoint weight `cos θ dθ` (`eFam_orthogonal`).  This file proves that they are also
*complete*: a function `g` which is orthogonal to every `eFam m` (and which is square-integrable
against `cos θ dθ`) vanishes a.e. on `Iθ = [0, π/2]`.

**Route.**  Write `ψ := g · cos`.  Since `e_m = cos · gC(2m+1)(sin)`, the hypothesis is exactly
`∫_{Iθ} ψ · e_m = 0`.  The function `ψ` is a.e. strongly measurable and in `L²(Iθ)` (because
`ψ² = g²cos² ≤ g²cos` on `Iθ`).  Now

* the span of `{e_m : m ≤ k}` equals the span of `{gen j = cos · sin^{2j+1} : j ≤ k}`
  (triangular change of basis, `gC_span_eq`: `Y k` lies in the span of `B 0, …, B k`), so all
  the moments `∫_{Iθ} ψ · gen j` vanish;
* the recurrence `sin (2(x+1)θ) = 2 cos(2θ) sin(2xθ) − sin(2(x−1)θ)` shows (by induction on the
  level) that each `sin (2(m+1)θ)` lies in the span of `{gen j : j ≤ m}`, hence all the sine
  moments of `ψ` vanish;
* the (already proved) completeness of the Dirichlet sine system
  `Work.FTS.EllipticEst.sin_system_complete` gives `ψ =ᵐ 0`, and since `cos θ ≠ 0` a.e. on `Iθ`
  this yields `g =ᵐ 0`.

Everything is phrased in terms of the "vanishing weighted integral" submodule `vanSub φ T` of
functions `f` with `∫_{Iθ} φ · T f = 0`, which makes both triangularity steps a single
`Submodule.span_le` application.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_span_eq
import Submission.Work.FTS.PhiStar.Gegenbauer.odd_powers_complete_fixed
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Gegenbauer

open MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## The generators `gen k = cos · sin ^ (2k+1)` and two linear operators -/

/-- The generator family `gen k θ = cos θ · sin θ ^ (2k+1)`. -/
def gen (k : ℕ) : ℝ → ℝ := fun θ => Real.cos θ * Real.sin θ ^ (2 * k + 1)

lemma gen_apply (k : ℕ) (θ : ℝ) :
    gen k θ = Real.cos θ * Real.sin θ ^ (2 * k + 1) := rfl

/-- The operator `f ↦ cos · (f ∘ sin)`. -/
def sinOp : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := fun θ => Real.cos θ * f (Real.sin θ)
  map_add' f g := by
    funext θ
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma sinOp_apply (f : ℝ → ℝ) (θ : ℝ) : sinOp f θ = Real.cos θ * f (Real.sin θ) := rfl

/-- The operator `f ↦ cos (2·) · f`. -/
def cos2Op : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := fun θ => Real.cos (2 * θ) * f θ
  map_add' f g := by
    funext θ
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma cos2Op_apply (f : ℝ → ℝ) (θ : ℝ) : cos2Op f θ = Real.cos (2 * θ) * f θ := rfl

/-- `sinOp` applied to the odd monomial `Y k` is the generator `gen k`. -/
lemma sinOp_Y (k : ℕ) : sinOp (Y k) = gen k := rfl

/-- `sinOp` applied to `B k = gC (2k+1)` is the eigenfunction `eFam k`. -/
lemma sinOp_B (k : ℕ) : sinOp (B k) = eFam k := rfl

/-! ## The submodule of functions with vanishing weighted integral -/

/-- For a weight `φ : ℝ → ℝ` and an `ℝ`-linear operator `T` on functions, the set of functions
`f` such that `φ · T f` is integrable on `Iθ` with vanishing integral is a submodule of
`ℝ → ℝ`. -/
def vanSub (φ : ℝ → ℝ) (T : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ)) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Integrable (fun x => φ x * T f x) (volume.restrict Work.Spaces.Iθ) ∧
    ∫ x in Work.Spaces.Iθ, φ x * T f x = 0}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    have h0 : (fun x : ℝ => φ x * T (0 : ℝ → ℝ) x) = (0 : ℝ → ℝ) := by
      funext x
      simp
    rw [h0]
    exact ⟨integrable_zero ℝ ℝ (volume.restrict Work.Spaces.Iθ), by simp⟩
  add_mem' := by
    intro f g hf hg
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hg1, hg2⟩ := hg
    have hpt : (fun x : ℝ => φ x * T (f + g) x) = fun x : ℝ => φ x * T f x + φ x * T g x := by
      funext x
      rw [map_add]
      simp only [Pi.add_apply, mul_add]
    rw [Set.mem_ofPred_eq, hpt]
    refine ⟨hf1.add hg1, ?_⟩
    rw [integral_add hf1 hg1, hf2, hg2, add_zero]
  smul_mem' := by
    intro c f hf
    obtain ⟨hf1, hf2⟩ := hf
    have hpt : (fun x : ℝ => φ x * T (c • f) x) = fun x : ℝ => c * (φ x * T f x) := by
      funext x
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Set.mem_ofPred_eq, hpt]
    refine ⟨hf1.const_mul c, ?_⟩
    rw [integral_const_mul, hf2, mul_zero]

/-! ## The span induction producing the sine modes -/

/-- Multiplication by `cos (2θ)` raises the level by one:
`Submodule.span {gen j : j ≤ N} → Submodule.span {gen j : j ≤ N+1}`. -/
lemma cos2Op_mem_span_gen (N : ℕ) {f : ℝ → ℝ}
    (hf : f ∈ Submodule.span ℝ (gen '' Set.Iic N)) :
    cos2Op f ∈ Submodule.span ℝ (gen '' Set.Iic (N + 1)) := by
  have hle : Submodule.span ℝ (gen '' Set.Iic N)
      ≤ Submodule.comap cos2Op (Submodule.span ℝ (gen '' Set.Iic (N + 1))) := by
    rw [Submodule.span_le]
    rintro f ⟨k, hk, rfl⟩
    show cos2Op (gen k) ∈ Submodule.span ℝ (gen '' Set.Iic (N + 1))
    have hkN : k ≤ N := Set.mem_Iic.mp hk
    have hpt : cos2Op (gen k) = gen k - (2 : ℝ) • gen (k + 1) := by
      funext θ
      have hcos : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
        rw [Real.cos_two_mul']
        nlinarith [Real.sin_sq_add_cos_sq θ]
      simp only [cos2Op_apply, gen_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hcos, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by omega, pow_add]
      ring
    rw [hpt]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨k, Set.mem_Iic.mpr (by omega), rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k + 1, Set.mem_Iic.mpr (by omega), rfl⟩))
  exact hle hf

/-- `sin (4θ) = 2 cos (2θ) sin (2θ)`. -/
lemma sin_four_mul (θ : ℝ) : Real.sin (4 * θ) = 2 * (Real.cos (2 * θ) * Real.sin (2 * θ)) := by
  have h : (4 : ℝ) * θ = 2 * θ + 2 * θ := by ring
  rw [h, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  ring

/-- The base case of the induction: `sin (2θ) = 2 · gen 0`. -/
lemma sin_two_eq_smul_gen_zero :
    (fun θ : ℝ => Real.sin (2 * (((0 : ℕ) : ℝ) + 1) * θ)) = (2 : ℝ) • gen 0 := by
  funext θ
  simp only [gen_apply, Pi.smul_apply, smul_eq_mul]
  rw [show 2 * (((0 : ℕ) : ℝ) + 1) * θ = 2 * θ by push_cast; ring, Real.sin_two_mul]
  ring

/-- The second base case: `sin (4θ) = 2 cos(2θ) sin (2θ)`. -/
lemma sin_four_eq_smul_cos2Op :
    (fun θ : ℝ => Real.sin (2 * (((1 : ℕ) : ℝ) + 1) * θ))
      = (2 : ℝ) • cos2Op (fun θ : ℝ => Real.sin (2 * (((0 : ℕ) : ℝ) + 1) * θ)) := by
  funext θ
  simp only [cos2Op_apply, Pi.smul_apply, smul_eq_mul]
  rw [show 2 * (((1 : ℕ) : ℝ) + 1) * θ = 4 * θ by push_cast; ring,
    show 2 * (((0 : ℕ) : ℝ) + 1) * θ = 2 * θ by push_cast; ring, sin_four_mul]

/-- The induction step: `sin (2(x+2)θ) = 2 cos(2θ) sin(2(x+1)θ) − sin(2xθ)`
(the Chebyshev-type recurrence, with the three frequencies written separately). -/
lemma sin_three_term (k : ℕ) (θ : ℝ) :
    Real.sin (2 * (((k + 2 : ℕ) : ℝ) + 1) * θ)
      = 2 * (Real.cos (2 * θ) * Real.sin (2 * (((k + 1 : ℕ) : ℝ) + 1) * θ))
        - Real.sin (2 * (((k : ℕ) : ℝ) + 1) * θ) := by
  have h1 : 2 * (((k + 2 : ℕ) : ℝ) + 1) * θ
      = 2 * (((k + 1 : ℕ) : ℝ) + 1) * θ + 2 * θ := by push_cast; ring
  have h2 : 2 * (((k : ℕ) : ℝ) + 1) * θ
      = 2 * (((k + 1 : ℕ) : ℝ) + 1) * θ - 2 * θ := by push_cast; ring
  rw [h1, Real.sin_add, h2, Real.sin_sub]
  ring

/-- **The sine modes lie in the span of the generators.**  For every `m`, the function
`θ ↦ sin (2(m+1)θ)` is a finite linear combination of `gen j`, `j ≤ m`. -/
lemma sin_succ_mem_span_gen_aux (m : ℕ) :
    (fun θ : ℝ => Real.sin (2 * ((m : ℝ) + 1) * θ))
      ∈ Submodule.span ℝ (gen '' Set.Iic m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      rw [sin_two_eq_smul_gen_zero]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, Set.mem_Iic.mpr le_rfl, rfl⟩)
    | 1 =>
      have h0 : (fun θ : ℝ => Real.sin (2 * (((0 : ℕ) : ℝ) + 1) * θ))
          ∈ Submodule.span ℝ (gen '' Set.Iic 0) := ih 0 (by omega)
      have hA : cos2Op (fun θ : ℝ => Real.sin (2 * (((0 : ℕ) : ℝ) + 1) * θ))
          ∈ Submodule.span ℝ (gen '' Set.Iic 1) := by
        have h := cos2Op_mem_span_gen 0 h0
        simpa using h
      rw [sin_four_eq_smul_cos2Op]
      exact Submodule.smul_mem _ _ hA
    | k + 2 =>
      -- the two ingredients of the recurrence
      have hf : (fun θ : ℝ => Real.sin (2 * (((k + 1 : ℕ) : ℝ) + 1) * θ))
          ∈ Submodule.span ℝ (gen '' Set.Iic (k + 1)) := ih (k + 1) (by omega)
      have hA : cos2Op (fun θ : ℝ => Real.sin (2 * (((k + 1 : ℕ) : ℝ) + 1) * θ))
          ∈ Submodule.span ℝ (gen '' Set.Iic (k + 2)) := by
        have h := cos2Op_mem_span_gen (k + 1) hf
        simpa using h
      have hlast : (fun θ : ℝ => Real.sin (2 * (((k : ℕ) : ℝ) + 1) * θ))
          ∈ Submodule.span ℝ (gen '' Set.Iic (k + 2)) :=
        Submodule.span_mono (Set.image_mono (fun j hj => by
          simp only [Set.mem_Iic] at hj ⊢
          omega)) (ih k (by omega))
      have hrec : (fun θ : ℝ => Real.sin (2 * (((k + 2 : ℕ) : ℝ) + 1) * θ))
          = (2 : ℝ) • cos2Op (fun θ : ℝ => Real.sin (2 * (((k + 1 : ℕ) : ℝ) + 1) * θ))
            - (fun θ : ℝ => Real.sin (2 * (((k : ℕ) : ℝ) + 1) * θ)) := by
        funext θ
        simp only [cos2Op_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact sin_three_term k θ
      rw [hrec]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hA) hlast

/-! ## Two elementary `θ`-facts -/

/-- `cos θ ≠ 0` for a.e. `θ ∈ Iθ`. -/
lemma ae_cos_ne_zero :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Real.cos θ ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have hcount : ({θ : ℝ | ¬ Real.cos θ ≠ 0}).Countable := by
    refine Set.Countable.mono ?_
      (Set.countable_range (fun k : ℤ => (2 * (k : ℝ) + 1) * Real.pi / 2))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hθ
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hθ
    exact ⟨k, hk.symm⟩
  have h0 : volume {θ : ℝ | ¬ Real.cos θ ≠ 0} = 0 := hcount.measure_zero _
  refine le_antisymm ?_ bot_le
  exact le_trans (MeasureTheory.Measure.restrict_apply_le (μ := volume) Work.Spaces.Iθ
    {θ : ℝ | ¬ Real.cos θ ≠ 0}) (le_of_eq h0)

/-! ## The eigenfunctions are complete -/

theorem eFam_complete :
    ∀ g : ℝ → ℝ,
      MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      (∀ m : ℕ, ∫ θ in Work.Spaces.Iθ,
          g θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ = 0) →
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ = 0 := by
  intro g hgm hgint hmom
  set ψ : ℝ → ℝ := fun θ => g θ * Real.cos θ with hψ
  have hψapp : ∀ θ : ℝ, ψ θ = g θ * Real.cos θ := fun θ => by rw [hψ]
  have : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Icc_lt_top
  have hψcos : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => g θ * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hgm.mul Real.continuous_cos.measurable.aestronglyMeasurable
  have hψm : MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hψ]
    exact hψcos
  -- `ψ ∈ L²(Iθ)`
  have hψ2 : MeasureTheory.Integrable (fun θ : ℝ => ψ θ ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hgint (hψcos.pow 2) ?_
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    have hcos0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hsq : (g θ * Real.cos θ) ^ 2 = g θ ^ 2 * Real.cos θ ^ 2 := by ring
    rw [hsq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hgc : 0 ≤ g θ ^ 2 * Real.cos θ := mul_nonneg (sq_nonneg _) hcos0
    have hkey : g θ ^ 2 * Real.cos θ * Real.cos θ ≤ g θ ^ 2 * Real.cos θ * 1 :=
      mul_le_mul_of_nonneg_left hcos1 hgc
    nlinarith [hkey]
  have hψmem : MeasureTheory.MemLp ψ 2 (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hψm]
    refine (MeasureTheory.integrable_congr ?_).mpr hψ2
    refine Filter.Eventually.of_forall fun θ => ?_
    show ‖ψ θ‖ ^ 2 = ψ θ ^ 2
    rw [Real.norm_eq_abs, sq_abs]
  have hψ1 : MeasureTheory.Integrable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hψmem.integrable (by norm_num)
  -- the moments of `ψ` against the eigenfunctions
  have hmomψ : ∀ m : ℕ, ∫ θ in Work.Spaces.Iθ, ψ θ * eFam m θ = 0 := by
    intro m
    rw [← hmom m]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun θ => ?_
    show ψ θ * eFam m θ = g θ * eFam m θ * Real.cos θ
    rw [hψapp θ]
    ring
  -- the eigenfunctions lie in the `cos · (· ∘ sin)`-preimage of the vanishing submodule
  have hEFam : ∀ k : ℕ, eFam k ∈ vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ)) := by
    intro k
    have hcont : Continuous (fun θ : ℝ => eFam k θ) := by
      rw [show eFam k = fun θ : ℝ => Real.cos θ * gC (2 * k + 1) (Real.sin θ) from rfl]
      exact Real.continuous_cos.mul
        (((contDiff_gC (2 * k + 1)).continuous).comp Real.continuous_sin)
    obtain ⟨C, hC⟩ :=
      IsCompact.exists_bound_of_continuousOn (s := Work.Spaces.Iθ) isCompact_Icc hcont.continuousOn
    refine ⟨?_, hmomψ k⟩
    have hb : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ‖eFam k θ‖ ≤ C := by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      exact Filter.Eventually.of_forall fun θ hθ => hC θ hθ
    exact hψ1.mul_bdd hcont.measurable.aestronglyMeasurable hb
  have hB : ∀ k : ℕ, B k ∈ Submodule.comap sinOp
      (vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ))) := by
    intro k
    rw [Submodule.mem_comap, sinOp_B k]
    exact hEFam k
  have hY : ∀ k : ℕ, Y k ∈ Submodule.comap sinOp
      (vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ))) := by
    intro k
    have hle : Submodule.span ℝ (B '' Set.Iic k)
        ≤ Submodule.comap sinOp (vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ))) := by
      rw [Submodule.span_le]
      rintro f ⟨j, hj, rfl⟩
      exact hB j
    exact hle (oddSpan_le_span_B k (Y_mem k))
  -- the generators themselves
  have hgen : ∀ k : ℕ, gen k ∈ vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ)) := by
    intro k
    have h := hY k
    rw [Submodule.mem_comap, sinOp_Y k] at h
    exact h
  have hgenSpan : ∀ m : ℕ, Submodule.span ℝ (gen '' Set.Iic m)
      ≤ vanSub ψ (LinearMap.id : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ)) := fun m =>
    Submodule.span_le.mpr fun f hf => by
      rcases hf with ⟨k, hk, rfl⟩
      exact hgen k
  -- the sine modes lie in the vanishing submodule, so their moments vanish
  have hmom_sin : ∀ n : ℕ,
      ∫ θ in Work.Spaces.Iθ, ψ θ * Real.sin (2 * (((n : ℝ) + 1)) * θ) = 0 := by
    intro n
    exact (hgenSpan n (sin_succ_mem_span_gen_aux n)).2
  have hψ0 : ψ =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] 0 :=
    Work.FTS.EllipticEst.sin_system_complete hψmem hmom_sin
  filter_upwards [hψ0, ae_cos_ne_zero] with θ h1 h2
  rw [hψapp θ] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact h
  · exact absurd h h2

end

end Work.FTS.PhiStar.Gegenbauer
