import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.HeavyFlat.Defs
import Submission.Work.FTS.EllSol.shiftReduceDefs
import Submission.Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## The shifted data `u_k = e^{b_k t}g` and the binomial expansion of `Ω`

The weight `Ω(t) = (1+e^t)^4 e^{-3t} = Σ_{k<5} C(4,k) e^{(k-3)t}` expands as a binomial, so
with `b_k = (k-3)/2` the `k`-th summand is `e^{2 b_k t}` and `Ω` dominates each of them.  The
operator `∂_t - b` acts on `u_k = e^{b_k t}g` as `e^{b_k t}∂_t`.

This block is a self-contained copy of the corresponding statements of
`Work.FTS.EllSol.shiftReduceDefs` / `Work.FTS.EllSol.Shift2Flat.*`, so that this module does not
import those files (whose import graph currently contains a cycle). -/

private def bS (k : ℕ) : ℝ := ((k : ℝ) - 3) / 2

private def cS (k : ℕ) : ℝ := (Nat.choose 4 k : ℝ)

private def shiftD (k : ℕ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Real.exp (bS k * t) * g t θ

@[simp] private theorem shiftD_def (k : ℕ) (g : ℝ → ℝ → ℝ) (t θ : ℝ) :
    shiftD k g t θ = Real.exp (bS k * t) * g t θ := rfl

private theorem cS_nonneg (k : ℕ) : 0 ≤ cS k := by
  rw [cS]; exact Nat.cast_nonneg _

private theorem exp_two_bS (k : ℕ) (t : ℝ) :
    Real.exp (2 * (bS k * t)) = Real.exp (((k : ℝ) - 3) * t) := by
  congr 1
  simp only [bS]
  ring

private theorem omw_pow_four (y : ℝ) :
    (1 + y) ^ 4 = ∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * y ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Nat.choose]
  ring

private theorem omw_eq_exp_sum (t : ℝ) :
    omw t = ∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t) := by
  have hterm : ∀ k : ℕ, Real.exp (((k : ℝ) - 3) * t)
      = (Real.exp t) ^ k * Real.exp (-(3 * t)) := by
    intro k
    have h : ((k : ℝ) - 3) * t = (k : ℝ) * t + (-(3 * t)) := by ring
    rw [h, Real.exp_add, Real.exp_nat_mul]
  have hsum : (∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t))
      = (∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * (Real.exp t) ^ k)
        * Real.exp (-(3 * t)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hterm k]
    ring
  rw [hsum, ← omw_pow_four (Real.exp t), omw]

private theorem exp_shift_le_omw (k : ℕ) (hk : k ≤ 4) (t : ℝ) :
    Real.exp (((k : ℝ) - 3) * t) ≤ omw t := by
  rw [omw_eq_exp_sum t]
  have hmem : k ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ j ∈ Finset.range 5,
      0 ≤ (Nat.choose 4 j : ℝ) * Real.exp (((j : ℝ) - 3) * t) :=
    fun j _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hle : Real.exp (((k : ℝ) - 3) * t)
      ≤ (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t) := by
    have h1 : (1 : ℝ) ≤ (Nat.choose 4 k : ℝ) := by
      have := Nat.choose_pos hk
      exact_mod_cast this
    simpa using mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (((k : ℝ) - 3) * t))
  exact le_trans hle (Finset.single_le_sum hnonneg hmem)

private theorem omw_eq_sum (t : ℝ) :
    omw t = ∑ k ∈ Finset.range 5, cS k * Real.exp (2 * (bS k * t)) := by
  rw [omw_eq_exp_sum t]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cS, ← exp_two_bS]

private theorem exp_bS_le_omw (k : ℕ) (hk : k ≤ 4) (t : ℝ) :
    Real.exp (2 * (bS k * t)) ≤ omw t := by
  rw [exp_two_bS]
  exact exp_shift_le_omw k hk t

private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

private theorem sigE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigE θ := by
  simp only [sigE]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _


private def oS : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_oS : IsOpen oS := isOpen_univ.prod isOpen_Ioo

private lemma measurableSet_oS : MeasurableSet oS := isOpen_oS.measurableSet

private lemma mem_oS {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : (t, θ) ∈ oS :=
  ⟨mem_univ t, hθ⟩

/-- The strip `univ ×ˢ Iθ` differs from the open strip `oS` by the null set
`univ ×ˢ {0, π/2}`, hence the two restricted measures agree. -/
private lemma restrict_strip_eq :
    (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = volume.restrict oS := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ Work.FTS.EllSol.Shift2Flat.shiftSq_volume_prod_endpoints
    rintro p hp
    rw [Set.mem_sdiff, Set.mem_prod] at hp
    obtain ⟨⟨-, h2⟩, hnot⟩ := hp
    simp only [oS, Set.mem_prod, Set.mem_univ, true_and] at hnot
    refine ⟨trivial, ?_⟩
    have hmem : p.2 ∈ Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) := ⟨h2, hnot⟩
    rwa [Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)] at hmem
  · rw [Set.sdiff_eq_empty.mpr, measure_empty]
    exact Set.prod_mono Subset.rfl Set.Ioo_subset_Icc_self

private lemma sin_two_pos_of_mem_oS {p : ℝ × ℝ} (hp : p ∈ oS) : 0 < Real.sin (2 * p.2) := by
  have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := hp.2
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


private theorem sdContDiffAt {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry g) (t, θ) :=
  hsm.contDiffAt (isOpen_oS.mem_nhds (mem_oS hθ))

private theorem sdContDiff_slice_fst {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 2 (fun s : ℝ => g s θ) := by
  have hmap : ContDiffOn ℝ 2 (fun s : ℝ => (s, θ)) Set.univ :=
    contDiffOn_id.prodMk contDiffOn_const
  have hcomp : ContDiffOn ℝ 2 (Function.uncurry g ∘ fun s : ℝ => (s, θ)) Set.univ :=
    hsm.comp hmap fun s _ => mem_oS hθ
  have hfun : (fun s : ℝ => g s θ) = Function.uncurry g ∘ fun s : ℝ => (s, θ) := rfl
  rw [hfun]
  exact contDiffOn_univ.mp hcomp

private theorem sdContDiffOn_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) (t : ℝ) :
    ContDiffOn ℝ 2 (fun θ' : ℝ => g t θ') (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : ContDiffOn ℝ 2 (fun θ' : ℝ => (t, θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hcomp : ContDiffOn ℝ 2 (Function.uncurry g ∘ fun θ' : ℝ => (t, θ'))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.comp hmap fun θ' hθ' => mem_oS hθ'
  exact hcomp.congr fun θ' _ => rfl

private theorem sdContDiffAt_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (fun θ' : ℝ => g t θ') θ :=
  (sdContDiffOn_slice_snd hsm t).contDiffAt (isOpen_Ioo.mem_nhds hθ)

private theorem sdContDiffOn_uncurry_pz {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) V := by
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (1 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  refine hcomp.congr fun p hp => ?_
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

private theorem sdDifferentiableAt_pz_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pz g t θ') θ := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz g)) oS :=
    sdContDiffOn_uncurry_pz isOpen_oS hsm
  have h2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz g)) (t, θ) :=
    h1.contDiffAt (isOpen_oS.mem_nhds (mem_oS hθ))
  have h3 : ContDiffAt ℝ 1 (fun θ' : ℝ => (t, θ')) θ := by fun_prop
  have h4 : ContDiffAt ℝ 1 (fun θ' : ℝ => Work.Spaces.pz g t θ') θ := h2.comp θ h3
  exact h4.differentiableAt (by norm_num)


private theorem hasDerivAt_exp_mul_const (c s : ℝ) :
    HasDerivAt (fun s' : ℝ => Real.exp (c * s')) (c * Real.exp (c * s)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => c * s') c s := by
    simpa using (hasDerivAt_id s).const_mul c
  have h2 : HasDerivAt Real.exp (Real.exp (c * s)) (c * s) := Real.hasDerivAt_exp (c * s)
  simpa only [Function.comp_def, mul_comm] using h2.comp s h1

private theorem deriv_mul_fun {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  rw [show (fun y : ℝ => f y * g y) = f * g from rfl, deriv_mul hf hg]

private theorem deriv_add_fun {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y + g y) x = deriv f x + deriv g x := by
  rw [show (fun y : ℝ => f y + g y) = f + g from rfl, deriv_add hf hg]

private theorem deriv_exp_mul {c : ℝ} {H : ℝ → ℝ} {t : ℝ} (hH : DifferentiableAt ℝ H t) :
    deriv (fun s : ℝ => Real.exp (c * s) * H s) t
      = Real.exp (c * t) * (c * H t + deriv H t) := by
  rw [deriv_mul_fun (hasDerivAt_exp_mul_const c t).differentiableAt hH,
    (hasDerivAt_exp_mul_const c t).deriv]
  ring

/-- The second-order product rule for `s ↦ e^{c s} H s`.  Since the exponential factor is
differentiable everywhere, no regularity beyond `C²` of `H` is needed. -/
private theorem deriv_deriv_exp_mul {c : ℝ} {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (t : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (c * s) * H s)) t
      = Real.exp (c * t) * (c ^ 2 * H t + 2 * c * deriv H t + deriv (deriv H) t) := by
  have hdiff : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hddiff : Differentiable ℝ (deriv H) := hH.differentiable_deriv_two
  have hFeq : deriv (fun s : ℝ => Real.exp (c * s) * H s)
      = fun s : ℝ => Real.exp (c * s) * (c * H s + deriv H s) := by
    funext s
    rw [deriv_exp_mul (hH := hdiff.differentiableAt)]
  rw [hFeq]
  have hE : DifferentiableAt ℝ (fun s : ℝ => Real.exp (c * s)) t :=
    (hasDerivAt_exp_mul_const c t).differentiableAt
  have hcH : DifferentiableAt ℝ (fun s : ℝ => c * H s) t := hdiff.differentiableAt.const_mul c
  have hdH : DifferentiableAt ℝ (deriv H) t := hddiff.differentiableAt
  have hK : DifferentiableAt ℝ (fun s : ℝ => c * H s + deriv H s) t := hcH.add hdH
  rw [deriv_mul_fun hE hK, (hasDerivAt_exp_mul_const c t).deriv, deriv_add_fun hcH hdH,
    deriv_const_mul_field]
  ring




private theorem pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (shiftD k g) t θ
      = Real.exp (bS k * t)
        * (bS k * g t θ + Work.Spaces.pz g t θ) := by
  have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ) := sdContDiff_slice_fst hsm hθ
  show deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ) t
      = Real.exp (bS k * t)
        * (bS k * g t θ + Work.Spaces.pz g t θ)
  exact deriv_exp_mul (c := bS k) (hslice.differentiable (by norm_num)).differentiableAt

private theorem pz_pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
      = Real.exp (bS k * t)
        * (bS k ^ 2 * g t θ
            + 2 * bS k * Work.Spaces.pz g t θ
            + Work.Spaces.pz (Work.Spaces.pz g) t θ) := by
  have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ) := sdContDiff_slice_fst hsm hθ
  show deriv (deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ)) t
      = Real.exp (bS k * t)
        * (bS k ^ 2 * g t θ
            + 2 * bS k * Work.Spaces.pz g t θ
            + Work.Spaces.pz (Work.Spaces.pz g) t θ)
  exact deriv_deriv_exp_mul hslice t

private theorem pth_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ} (t θ : ℝ) :
    Work.Spaces.pth (shiftD k g) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth g t θ := by
  show deriv (fun θ' : ℝ => Real.exp (bS k * t) * g t θ') θ
      = Real.exp (bS k * t) * deriv (fun θ' : ℝ => g t θ') θ
  rw [deriv_const_mul_field]

private theorem pth_pth_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ} (t θ : ℝ) :
    Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pth g) t θ := by
  have h1 : ∀ θ' : ℝ, Work.Spaces.pth (shiftD k g) t θ'
      = Real.exp (bS k * t) * Work.Spaces.pth g t θ' :=
    fun θ' => pth_shiftD t θ'
  show deriv (fun θ' : ℝ => Work.Spaces.pth (shiftD k g) t θ') θ
      = Real.exp (bS k * t)
        * deriv (fun θ' : ℝ => Work.Spaces.pth g t θ') θ
  rw [show (fun θ' : ℝ => Work.Spaces.pth (shiftD k g) t θ')
      = fun θ' : ℝ => Real.exp (bS k * t) * Work.Spaces.pth g t θ'
      from funext h1]
  rw [deriv_const_mul_field]

private theorem pth_pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) t θ
      = Real.exp (bS k * t)
        * (bS k * Work.Spaces.pth g t θ
            + Work.Spaces.pth (Work.Spaces.pz g) t θ) := by
  have hev : (fun θ' : ℝ => Work.Spaces.pz (shiftD k g) t θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => Real.exp (bS k * t)
        * (bS k * g t θ' + Work.Spaces.pz g t θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ') := sdContDiff_slice_fst hsm hθ'
    show deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ') t
        = Real.exp (bS k * t)
          * (bS k * g t θ' + Work.Spaces.pz g t θ')
    exact deriv_exp_mul (c := bS k)
      (hslice.differentiable (by norm_num)).differentiableAt
  have hgmul : DifferentiableAt ℝ
      (fun θ' : ℝ => bS k * g t θ') θ :=
    ((sdContDiffAt_slice_snd hsm hθ).differentiableAt (by norm_num)).const_mul _
  have hgpz : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pz g t θ') θ :=
    sdDifferentiableAt_pz_slice_snd hsm hθ
  show deriv (fun θ' : ℝ => Work.Spaces.pz (shiftD k g) t θ') θ
      = Real.exp (bS k * t)
        * (bS k * Work.Spaces.pth g t θ
            + Work.Spaces.pth (Work.Spaces.pz g) t θ)
  rw [hev.deriv_eq, deriv_const_mul_field]
  have key : deriv (fun θ' : ℝ => bS k * g t θ'
        + Work.Spaces.pz g t θ') θ
      = bS k * Work.Spaces.pth g t θ
        + Work.Spaces.pth (Work.Spaces.pz g) t θ := by
    have h1 : deriv (fun θ' : ℝ => g t θ') θ = Work.Spaces.pth g t θ := rfl
    have h2 : deriv (fun θ' : ℝ => Work.Spaces.pz g t θ') θ
        = Work.Spaces.pth (Work.Spaces.pz g) t θ := rfl
    rw [deriv_add_fun hgmul hgpz, deriv_const_mul_field, h1, h2]
  rw [key]




/-- The four pointwise shift identities for `u_k = e^{b_k t} g` on the open strip
`0 < θ < π/2`: the second `t`-slot, the second `θ`-slot, the first `t`-slot and the mixed
`(θ,t)`-slot of the shifted datum equal `e^{b_k t}` times the corresponding slot of `g`. -/
private theorem shiftD_pointwise {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
        - 2 * bS k * Work.Spaces.pz (shiftD k g) t θ
        + bS k ^ 2 * shiftD k g t θ
      = Real.exp (bS k * t) * Work.Spaces.pz (Work.Spaces.pz g) t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pth g) t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (shiftD k g) t θ - bS k * shiftD k g t θ
      = Real.exp (bS k * t) * Work.Spaces.pz g t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) t θ
        - bS k * Work.Spaces.pth (shiftD k g) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pz g) t θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t θ hθ
    rw [pz_pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ,
      pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, shiftD]
    ring
  · intro t θ _
    exact pth_pth_shiftD (k := k) (g := g) t θ
  · intro t θ hθ
    rw [pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, shiftD]
    ring
  · intro t θ hθ
    rw [pth_pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, pth_shiftD]
    ring


private lemma continuousOn_sigE : ContinuousOn (fun p : ℝ × ℝ => sigE p.2) oS := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) oS :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_oS hp)))

/-- `p ↦ ∂_θ∂_t g (p.1, p.2)` is continuous on the open strip: `∂_t g` is `C¹` there, so its
`θ`-partial is the (continuous) Fréchet derivative against the direction `(0,1)`. -/
private lemma continuousOn_pth_pz {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) oS := by
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz g)) oS :=
    sdContDiffOn_uncurry_pz isOpen_oS hsm
  have hfd : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (Function.uncurry (Work.Spaces.pz g)) p) oS :=
    hC1.continuousOn_fderiv_of_isOpen isOpen_oS le_rfl
  have hev : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (Function.uncurry (Work.Spaces.pz g)) p (0, 1)) oS :=
    hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) oS)
  refine hev.congr (fun p hp => ?_)
  exact Work.Spaces.pth_eq_fderiv (G := Work.Spaces.pz g)
    ((hC1.contDiffAt (isOpen_oS.mem_nhds hp)).differentiableAt (by norm_num))

/-- **The `Ω`-weighted heavy mixed-slot finiteness from the flat shifted one.**  The
decomposition `Ω(t) = (1+e^t)^4 e^{-3t} = Σ_{k<5} C(4,k) e^{2 b_k t}` with `b_k = (k-3)/2`,
together with `e^{b t}∂_t g = (∂_t - b)(e^{b t}g)`, reduces the `Ω`-weighted strip statement to
the flat shifted statement applied to the scaled data `u_k = e^{b_k t}g` (`k < 5`), each of whose
three diagonal slots is dominated by the corresponding `Ω`-weighted slot of `g` because
`e^{2 b_k t} ≤ Ω(t)` (the coefficient of `e^{2b_k t}` in the binomial expansion of `Ω` is
`C(4,k) ≥ 1`); the conclusion is summed over `k < 5` by `lintegral_finset_sum`.  Both the
hypotheses and the conclusion are on the strip `univ ×ˢ Iθ`. -/
theorem omOfFlat : Work.FTS.EllSol.HeavyFlat.FlatHeavy → Work.FTS.EllSol.HeavyFlat.OmHeavy := by
  intro hFlat g hsm h0 hπ hA hP hE
  classical
  -- ### Step 1: the per-shift finiteness, for each `k < 5`
  have key : ∀ k ∈ Finset.range 5,
      ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1)) * sigE p.2) < ⊤ := by
    intro k hk
    have hk4 : k ≤ 4 := by have h5 := Finset.mem_range.mp hk; omega
    -- the shifted datum `u_k = e^{b_k t} g` is smooth on the open strip and vanishes at `θ = 0, π/2`
    have hsmk : ContDiffOn ℝ 2 (Function.uncurry (shiftD k g))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hf : ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.exp (bS k * p.1)) :=
        Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
      have hgoal : Function.uncurry (shiftD k g)
          = fun p : ℝ × ℝ =>
              Real.exp (bS k * p.1) * Function.uncurry g p := by
        funext p; rfl
      rw [hgoal]
      exact hf.contDiffOn.mul hsm
    have h0k : ∀ t : ℝ, shiftD k g t 0 = 0 := by
      intro t; rw [shiftD_def, h0 t, mul_zero]
    have hπk : ∀ t : ℝ, shiftD k g t (Real.pi / 2) = 0 := by
      intro t; rw [shiftD_def, hπ t, mul_zero]
    have hexp : ∀ t : ℝ, Real.exp (2 * bS k * t)
        ≤ Work.FTS.EllSol.omegaAux t := by
      intro t
      rw [show 2 * bS k * t = 2 * (bS k * t) by ring]
      exact exp_bS_le_omw k hk4 t
    have hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigE θ :=
      fun θ hθ => sigE_nonneg hθ
    have hpw := shiftD_pointwise (k := k) (g := g) hsm
    -- the three shifted diagonal slots are integrable on the strip
    have hI1 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (shiftD k g) p.1 p.2
          - bS k * shiftD k g p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pz (shiftD k g) t θ
          - bS k * shiftD k g t θ)
        (v := fun t θ => Work.Spaces.pz g t θ) (σ := sigE) hexp hσ hA
        (fun t θ hθ => hpw.2.2.1 t θ hθ)
    have hI2 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) p.1 p.2
          - 2 * bS k
            * Work.Spaces.pz (shiftD k g) p.1 p.2
          + bS k ^ 2 * shiftD k g p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
          - 2 * bS k * Work.Spaces.pz (shiftD k g) t θ
          + bS k ^ 2 * shiftD k g t θ)
        (v := fun t θ => Work.Spaces.pz (Work.Spaces.pz g) t θ) (σ := sigE) hexp hσ hP
        (fun t θ hθ => hpw.1 t θ hθ)
    have hI3 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ)
        (v := fun t θ => Work.Spaces.pth (Work.Spaces.pth g) t θ) (σ := sigE) hexp hσ hE
        (fun t θ hθ => hpw.2.1 t θ hθ)
    have hkfin := hFlat (bS k) (shiftD k g)
      hsmk h0k hπk hI1 hI2 hI3
    -- identify the shifted `(1,1)`-slot with `e^{2 b_k t}` times the slot of `g`
    have hconv1 : ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)
        = ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_oS] with p hp
      have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := hp.2
      rw [hpw.2.2.2 p.1 p.2 hθ]
      congr 1
      rw [mul_pow, show Real.exp (bS k * p.1) ^ 2
            = Real.exp (2 * (bS k * p.1)) by
          rw [pow_two, ← Real.exp_add]; ring_nf]
      ring
    have hconv2 : ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2)
        = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2) := by
      rw [restrict_strip_eq]
    rw [hconv1, hconv2]
    exact hkfin
  -- ### Step 2: the decomposition of the `Ω`-weighted integrand
  have haesm : ∀ k ∈ Finset.range 5, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)))
      (volume.restrict oS) := by
    intro k hk
    have hY : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
        (volume.restrict oS) := (continuousOn_pth_pz hsm).aemeasurable measurableSet_oS
    have hσ : AEMeasurable (fun p : ℝ × ℝ => sigE p.2) (volume.restrict oS) :=
      continuousOn_sigE.aemeasurable measurableSet_oS
    have he : AEMeasurable (fun p : ℝ × ℝ =>
        Real.exp (2 * (bS k * p.1))) (volume.restrict oS) := by
      refine Measurable.aemeasurable ?_
      have h : Measurable (fun p : ℝ × ℝ =>
          Real.exp ((2 * bS k) * p.1)) :=
        Real.measurable_exp.comp
          ((measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * bS k)).mul
            measurable_fst)
      simpa only [mul_assoc] using h
    have h1 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2) (volume.restrict oS) := by
      have h := hY.mul hY
      have hfun : ((fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
            * fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
          = fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 := by
        funext p; rw [Pi.mul_apply, sq]
      rwa [hfun] at h
    have h2 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1))) (volume.restrict oS) :=
      h1.mul he
    have h3 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1)) * sigE p.2)
        (volume.restrict oS) := h2.mul hσ
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h3.const_mul (cS k))
  have hGk : ∀ k ∈ Finset.range 5,
      ∫⁻ p in oS, ENNReal.ofReal (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2))
      = ENNReal.ofReal (cS k) *
          ∫⁻ p in oS, ENNReal.ofReal
            ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
              * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
    intro k hk
    have hfac : (fun p : ℝ × ℝ => ENNReal.ofReal (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)))
        = fun p : ℝ × ℝ => ENNReal.ofReal (cS k)
          * ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
      funext p
      exact ENNReal.ofReal_mul (cS_nonneg k)
    rw [hfac, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hdecomp : ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      = ∑ k ∈ Finset.range 5, ENNReal.ofReal (cS k)
          * ∫⁻ p in oS, ENNReal.ofReal
              ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
                * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
    have hae : (fun p : ℝ × ℝ => ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2))
        =ᵐ[volume.restrict oS] (fun p : ℝ × ℝ => ∑ k ∈ Finset.range 5,
          ENNReal.ofReal (cS k *
            ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
              * Real.exp (2 * (bS k * p.1)) * sigE p.2))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_oS] with p hp
      have hsig : 0 ≤ sigE p.2 :=
        le_of_lt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_oS hp) _)
      have homw : omw p.1 = ∑ k ∈ Finset.range 5, cS k
          * Real.exp (2 * (bS k * p.1)) :=
        omw_eq_sum p.1
      have hsplit : (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * (∑ k ∈ Finset.range 5, cS k
                * Real.exp (2 * (bS k * p.1))) * sigE p.2
          = ∑ k ∈ Finset.range 5, cS k
              * ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
                * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [homw, hsplit]
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.range 5)
        (f := fun k => cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2))
        (fun k _ => mul_nonneg (cS_nonneg k)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) hsig))]
    rw [lintegral_congr_ae hae, MeasureTheory.lintegral_finsetSum' _ haesm]
    exact Finset.sum_congr rfl (fun k hk => hGk k hk)
  -- ### Step 3: the sum is finite
  have hfin : ∫⁻ p in oS, ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2) < ⊤ := by
    rw [hdecomp]
    refine ENNReal.sum_lt_top.mpr (fun k hk => ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (key k hk)
  have hgoal : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      = ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2) := by
    rw [restrict_strip_eq]
  rw [hgoal]
  exact hfin

end

end Work.FTS.EllSol.HeavyFlat

