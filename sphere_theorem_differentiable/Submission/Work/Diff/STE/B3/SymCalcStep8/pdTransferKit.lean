import Mathlib
import Submission.Work.Diff.STE.B3.perTransferDef
import Submission.Work.Diff.STE.B3.periodicIntegralLeCube
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.SymCalcStep8.pd_periodization
import Submission.Work.Diff.STE.B3.SymCalcStep8.pd_CSqZ_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.flatCut_CSqZ_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.perTransfer_CSqZ_le_all
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_CSqZ_le
import Submission.Work.Diff.STE.B3.SymCalcStep8.pdList_flatCut
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairOp_aux
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_mul_comm_CSqZ_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The order-zero commutator `[∂ᵢ, L S_ε L^♭]` of the transfer-cut

This file proves the analytic heart of the sharp order bound for `[Λ^k, L S_ε L^♭]`
(`L = perTransfer γ τ`, `L^♭ = perTransfer γinv σ`, `S_ε = flatCut ρ ε`): the first-order
commutator `[∂ᵢ, L S_ε L^♭]` is an operator of **order `0`**, uniformly in `ε ∈ (0,1]`, at every
integer Sobolev level.

The mechanism (the `fd`-form of the transfer calculus): the lifts
`perTransfer γ τ = M_a ∘ compMap tl`, `perTransfer γinv σ = M_b ∘ compMap sl` of
`perTransfer_eq_mul_compMap_fd` give, by the product rule and the chain rule,

`∂ᵢ ∘ L = M_{∂ᵢa} ∘ compMap tl + Σ_k M_{∂ᵢ tl_k} ∘ L ∘ ∂_k`,

and the same for `L^♭`.  Expanding `[∂ᵢ, L S_ε L^♭]` this way leaves a term
`Σ_{k,j} M_{∂ᵢtl_k} L S_ε M_{∂_k sl_j} L^♭ ∂_j` whose "`S_ε`-free" part carries the multiplier
`Φ_j = Σ_k (∂_k sl_j ∘ tl) · ∂ᵢ tl_k = ∂ᵢ (sl_j ∘ tl)`; and `sl ∘ tl ≡ id` on `{a ≠ 0}` (a proved
consequence of the two `fd` hypotheses and `γinv ≡ 1` on `τ '' tsupport γ`), so `Φ_j = δ_{ij}`
there.  A factor `a` annihilates the remainder, the two "bad" terms cancel exactly, and what is
left is a sum of the three shapes

* `M_{∂ᵢa} ∘ compMap tl ∘ S_ε ∘ L^♭`,
* `M_{∂ᵢtl_k} ∘ L ∘ S_ε ∘ M_{∂_k b} ∘ compMap sl`,
* `M_{∂ᵢtl_k} ∘ L ∘ [S_ε, M_{∂_k sl_j}] ∘ L^♭ ∘ ∂_j`,

each of which is order `0` (the transfers are order `0` on every `Hᵗ`, and the Friedrichs
commutator `[S_ε, M_h]` gains one derivative, which pays for the outer `∂_j`).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The chain rule for `∂ᵢ` of a pull-back `V ∘ tl` -/

/-- The `k`-th component of the `i`-th partial derivative of a vector-valued map `tl`. -/
noncomputable def dT (i k : ι) (tl : (ι → ℝ) → (ι → ℝ)) (z : ι → ℝ) : ℝ :=
  Work.Diff.STE.pdR i (fun x : ι → ℝ => tl x k) z

lemma fderiv_apply_single (tl : (ι → ℝ) → (ι → ℝ)) (z : ι → ℝ)
    (h : DifferentiableAt ℝ tl z) (i k : ι) :
    (fderiv ℝ tl z (Pi.single i 1)) k = dT i k tl z := by
  rw [dT, Work.Diff.STE.pdR]
  rw [show (fun x : ι → ℝ => tl x k)
      = (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ) ∘ tl from rfl]
  rw [fderiv_comp z (ContinuousLinearMap.differentiableAt _) h,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- **The chain rule** for `∂ᵢ (V ∘ tl)`. -/
lemma pd_compMap_eq_sum (i : ι) (V : (ι → ℝ) → ℂ) (tl : (ι → ℝ) → (ι → ℝ)) (z : ι → ℝ)
    (hV : DifferentiableAt ℝ V (tl z)) (htl : DifferentiableAt ℝ tl z) :
    Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.compMap tl V) z
      = ∑ k, ((dT i k tl z : ℝ) : ℂ) * Work.Diff.STE.pd k V (tl z) := by
  rw [Work.Diff.STE.pd, show Work.Diff.STE.B3.SymCalc.compMap tl V = V ∘ tl from rfl,
    fderiv_comp z hV htl, ContinuousLinearMap.comp_apply]
  rw [show (fderiv ℝ V (tl z)) (fderiv ℝ tl z (Pi.single i 1))
      = ∑ k, ((fderiv ℝ tl z (Pi.single i 1)) k) • (fderiv ℝ V (tl z) (Pi.single k (1:ℝ))) from
    (by conv_lhs => rw [← Finset.univ_sum_single (fderiv ℝ tl z (Pi.single i 1))]
        rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [show Pi.single k ((fderiv ℝ tl z (Pi.single i 1)) k)
              = ((fderiv ℝ tl z (Pi.single i 1)) k) • (Pi.single k (1:ℝ) : ι → ℝ) by
            funext j; by_cases h : j = k <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne, h]]
          rw [map_smul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Work.Diff.STE.pd, Complex.real_smul, fderiv_apply_single tl z htl i k]

/-! ## §2. The derivative of a lift `V ↦ a · (V ∘ tl)` -/

/-- **The first-order rule for a lift.**  If `L V = a · (V ∘ tl)` for every `V`, then

  `∂ᵢ (L W) = (∂ᵢa) · (W ∘ tl) + a · Σ_k (∂ᵢtl_k) · ((∂_k W) ∘ tl)`. -/
lemma pd_of_lift (i : ι) (L : ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ)) (a : (ι → ℝ) → ℂ)
    (tl : (ι → ℝ) → (ι → ℝ))
    (hL : ∀ V : (ι → ℝ) → ℂ, L V = fun z => a z * V (tl z))
    (ha : Differentiable ℝ a) (htl : Differentiable ℝ tl)
    (W : (ι → ℝ) → ℂ) (hW : Differentiable ℝ W) :
    Work.Diff.STE.pd i (L W)
      = fun z => Work.Diff.STE.pd i a z * W (tl z)
          + a z * ∑ k, ((dT i k tl z : ℝ) : ℂ) * Work.Diff.STE.pd k W (tl z) := by
  funext z
  rw [hL W]
  show (fderiv ℝ (fun z : ι → ℝ => a z * W (tl z)) z) (Pi.single i 1) = _
  rw [show (fun z : ι → ℝ => a z * W (tl z)) = (fun z => a z * (W ∘ tl) z) from rfl]
  rw [fderiv_fun_mul (ha.differentiableAt) ((hW.differentiableAt).comp z (htl.differentiableAt))]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  rw [show (fderiv ℝ (W ∘ tl) z) (Pi.single i 1)
        = ∑ k, ((dT i k tl z : ℝ) : ℂ) * Work.Diff.STE.pd k W (tl z) from
      (pd_compMap_eq_sum i W tl z (hW.differentiableAt) (htl.differentiableAt))]
  rw [show Work.Diff.STE.pd i a z = fderiv ℝ a z (Pi.single i 1) from rfl]
  ring

/-- The same rule, stated with the defining identity of `L` at a single argument (this is the
form used in the assembly, where `L` is one of the two transfers and the argument is known to be
`1`-periodic). -/
lemma pd_of_lift_at (i : ι) (L : ((ι → ℝ) → ℂ) → ((ι → ℝ) → ℂ)) (a : (ι → ℝ) → ℂ)
    (tl : (ι → ℝ) → (ι → ℝ)) (W : (ι → ℝ) → ℂ)
    (hL : L W = fun z => a z * W (tl z))
    (ha : Differentiable ℝ a) (htl : Differentiable ℝ tl) (hW : Differentiable ℝ W) :
    Work.Diff.STE.pd i (L W)
      = fun z => Work.Diff.STE.pd i a z * W (tl z)
          + a z * ∑ k, ((dT i k tl z : ℝ) : ℂ) * Work.Diff.STE.pd k W (tl z) := by
  funext z
  rw [hL]
  show (fderiv ℝ (fun z : ι → ℝ => a z * W (tl z)) z) (Pi.single i 1) = _
  rw [show (fun z : ι → ℝ => a z * W (tl z)) = (fun z => a z * (W ∘ tl) z) from rfl]
  rw [fderiv_fun_mul (ha.differentiableAt) ((hW.differentiableAt).comp z (htl.differentiableAt))]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  rw [show (fderiv ℝ (W ∘ tl) z) (Pi.single i 1)
        = ∑ k, ((dT i k tl z : ℝ) : ℂ) * Work.Diff.STE.pd k W (tl z) from
      (pd_compMap_eq_sum i W tl z (hW.differentiableAt) (htl.differentiableAt))]
  rw [show Work.Diff.STE.pd i a z = fderiv ℝ a z (Pi.single i 1) from rfl]
  ring

/-- `∂_k` of a Friedrichs cutoff. -/
lemma pd_flatCut (k : ι) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {V : (ι → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVp : Work.Diff.STE.Periodic1 V) :
    Work.Diff.STE.pd k (Work.Diff.STE.B3.SymCalc.flatCut ρ ε V)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.pd k V) := by
  have := pdList_flatCut ρ hρ ε V hV hVp [k]
  simpa [Work.Diff.STE.pdList] using this

/-! ## §3. The `fd` transfer calculus: the closed forms of the two transfers on periodic inputs -/

/-- **The lift identity in the shape used below.**  This is the statement produced by
`perTransfer_eq_mul_compMap_fd` (with `tl` the folded transition map and `a` its periodisation)
and it is what makes the whole calculus work: on `1`-periodic inputs the transfer is the
multiplication by `a` composed with the pull-back by `tl`. -/
structure LiftData (γ : (ι → ℝ) → ℂ) (τ : (ι → ℝ) → (ι → ℝ)) (tl : (ι → ℝ) → (ι → ℝ))
    (a : (ι → ℝ) → ℂ) : Prop where
  lift : ∀ V : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 V →
    Work.Diff.STE.B3.perTransfer γ τ V = fun z => a z * V (tl z)

/-- **The folded map agrees with `τ` on the support of `γ`** (as a map of the torus): for every
`1`-periodic `V` and every `y` with `γ y ≠ 0` one has `V (tl y) = V (τ y)`.

This is the `fd` collision argument applied to the lift identity at the point `y`: the lattice sum
`Σ_m γ (y + m) V (τ (y + m))` has a single non-zero term, because for `m ≠ 0` the point `y + m`
lies outside `tsupport γ`. -/
lemma lift_eq_of_coeff_ne {γ : (ι → ℝ) → ℂ} {τ tl : (ι → ℝ) → (ι → ℝ)} {a : (ι → ℝ) → ℂ}
    (h : LiftData γ τ tl a)
    (hfd : ∀ z ∈ tsupport γ, ∀ m : ι → ℤ, m ≠ 0 →
      z + Work.Diff.STE.iVec m ∉ tsupport γ)
    (V : (ι → ℝ) → ℂ) (hV : Work.Diff.STE.Periodic1 V) {y : ι → ℝ} (hy : γ y ≠ 0) :
    V (tl y) = V (τ y) := by
  classical
  have hsingle : (∑' m : ι → ℤ, γ (y + Work.Diff.STE.iVec m) * V (τ (y + Work.Diff.STE.iVec m)))
      = γ y * V (τ y) := by
    refine (tsum_eq_single (0 : ι → ℤ) ?_).trans ?_
    · intro n hn
      have h0 : γ (y + Work.Diff.STE.iVec n) = 0 := by
        by_contra hc
        have hmem : y + Work.Diff.STE.iVec n ∈ tsupport γ :=
          subset_tsupport γ (Function.mem_support.mpr hc)
        exact hfd y (subset_tsupport γ (Function.mem_support.mpr hy)) n hn hmem
      rw [h0, zero_mul]
    · rw [Work.Diff.STE.iVec_zero, add_zero]
  have hkey := congrFun (h.lift V hV) y
  rw [Work.Diff.STE.B3.perTransfer] at hkey
  have ha : a y = γ y := by
    have h1 : (∑' m : ι → ℤ, γ (y + Work.Diff.STE.iVec m)) = γ y := by
      refine (tsum_eq_single (0 : ι → ℤ) ?_).trans ?_
      · intro n hn
        by_contra hc
        have hmem : y + Work.Diff.STE.iVec n ∈ tsupport γ :=
          subset_tsupport γ (Function.mem_support.mpr hc)
        exact hfd y (subset_tsupport γ (Function.mem_support.mpr hy)) n hn hmem
      · rw [Work.Diff.STE.iVec_zero, add_zero]
    have h2 : (∑' m : ι → ℤ, γ (y + Work.Diff.STE.iVec m)) = a y := by
      have h3 := congrFun (h.lift (fun _ : ι → ℝ => (1 : ℂ)) (by intro i x; rfl)) y
      rw [Work.Diff.STE.B3.perTransfer] at h3
      simpa using h3
    rw [← h2, h1]
  rw [hsingle] at hkey
  rw [ha] at hkey
  exact mul_left_cancel₀ hy hkey.symm

/-! ## §4. The chain rule `∂ᵢ (sl_j ∘ tl) = δ_{ij}` on `{a ≠ 0}` -/

/-- The character `e_j` as an explicit exponential. -/
lemma fourierExp_single (j : ι) (y : ι → ℝ) :
    Work.Diff.STE.fourierExp (Pi.single j (1 : ℤ)) y
      = Complex.exp ((2 * Real.pi * Complex.I) * (y j : ℂ)) := by
  rw [Work.Diff.STE.fourierExp, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]; ring_nf
  · intro b _ hb; rw [Pi.single_eq_of_ne hb]; simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The character family is `1`-periodic. -/
lemma periodic1_fourierExp (m : ι → ℤ) : Work.Diff.STE.Periodic1 (Work.Diff.STE.fourierExp m) :=
  fun i x => Work.Diff.STE.periodicIn_fourierExp m i x

/-- **`sl ∘ tl` is congruent to the identity on `{a ≠ 0}`.**  If `V (sl (tl z)) = V z` for every
`1`-periodic `V` and every `z` with `a z ≠ 0`, then each component of `sl (tl z) - z` is an
integer (this is the character test `V = e_j`). -/
lemma sub_mem_lattice {sl tl : (ι → ℝ) → (ι → ℝ)} {a : (ι → ℝ) → ℂ}
    (hQP : ∀ V : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 V →
      ∀ z : ι → ℝ, a z ≠ 0 → V (sl (tl z)) = V z)
    (z : ι → ℝ) (hz : a z ≠ 0) (j : ι) :
    ∃ n : ℤ, sl (tl z) j = z j + n := by
  have hV : Work.Diff.STE.Periodic1 (Work.Diff.STE.fourierExp (Pi.single j (1 : ℤ))) :=
    periodic1_fourierExp _
  have h := hQP _ hV z hz
  rw [fourierExp_single, fourierExp_single] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 : ((sl (tl z) j : ℝ) : ℂ) - ((z j : ℝ) : ℂ) = (n : ℂ) := by
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (((sl (tl z) j : ℝ) : ℂ)
        - ((z j : ℝ) : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination hn
    have h4 := congrArg (fun w : ℂ => w / (2 * (Real.pi : ℂ) * Complex.I)) h3
    rw [mul_div_cancel_left₀ _ Complex.two_pi_I_ne_zero,
      mul_div_cancel_right₀ _ Complex.two_pi_I_ne_zero] at h4
    rw [h4]
  have h5 : ((sl (tl z) j - z j : ℝ) : ℂ) = ((n : ℤ) : ℂ) := by
    rw [Complex.ofReal_sub]
    exact h2
  have h6 : sl (tl z) j - z j = ((n : ℤ) : ℝ) := Complex.ofReal_injective h5
  linarith


/-- The `i`-th `pdR` of a component is the corresponding component of the derivative. -/
lemma pdR_proj (f : (ι → ℝ) → (ι → ℝ)) (z : ι → ℝ) (h : DifferentiableAt ℝ f z) (i j : ι) :
    Work.Diff.STE.pdR i (fun x => f x j) z = (fderiv ℝ f z (Pi.single i 1)) j := by
  rw [Work.Diff.STE.pdR]
  rw [show (fun x : ι → ℝ => f x j)
      = (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) ∘ f from rfl]
  rw [fderiv_comp z (ContinuousLinearMap.differentiableAt _) h, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **`sl ∘ tl - id` is locally constant on `{a ≠ 0}`.**  It is continuous there and takes its
values in `ℤ^ι` (by `sub_mem_lattice`), hence is locally constant, hence has vanishing
derivative. -/
lemma fderiv_sub_id_eq_zero {sl tl : (ι → ℝ) → (ι → ℝ)} {a : (ι → ℝ) → ℂ}
    (hQP : ∀ V : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 V →
      ∀ z : ι → ℝ, a z ≠ 0 → V (sl (tl z)) = V z)
    (hcont : Continuous (fun z : ι → ℝ => sl (tl z) - z)) (hacont : Continuous a)
    {z : ι → ℝ} (hz : a z ≠ 0) :
    fderiv ℝ (fun z : ι → ℝ => sl (tl z) - z) z = 0 := by
  classical
  set Ψ : (ι → ℝ) → (ι → ℝ) := fun z => sl (tl z) - z with hΨ
  have hint : ∀ y : ι → ℝ, a y ≠ 0 → ∀ j : ι, ∃ m : ℤ, Ψ y j = (m : ℝ) := by
    intro y hy j
    obtain ⟨m, hm⟩ := sub_mem_lattice (sl := sl) (tl := tl) (a := a)
      hQP y hy j
    exact ⟨m, by rw [hΨ]; simp only [Pi.sub_apply]; push_cast; linarith⟩
  have hcontΨ : Continuous Ψ := by rw [hΨ]; exact hcont
  have hne : {y : ι → ℝ | a y ≠ 0} ∈ nhds z :=
    (hacont.continuousAt (x := z)).eventually (isOpen_ne.mem_nhds hz)
  have hcoord : ∀ j : ι, ∀ᶠ y in nhds z, Ψ y j = Ψ z j := by
    intro j
    obtain ⟨m, hm⟩ := hint z hz j
    have h1 : ∀ᶠ y in nhds z, |Ψ y j - Ψ z j| < 1 / 2 := by
      have hc : Continuous (fun y : ι → ℝ => Ψ y j) :=
        (continuous_apply j).comp hcontΨ
      have h2 := (hc.continuousAt (x := z)).eventually
        (Metric.ball_mem_nhds (Ψ z j) (by norm_num : (0:ℝ) < 1/2))
      filter_upwards [h2] with y hy
      rw [Real.dist_eq] at hy
      exact hy
    filter_upwards [h1, hne] with y hy1 hy2
    obtain ⟨m', hm'⟩ := hint y hy2 j
    have h5 : |(((m' : ℤ)) : ℝ) - (((m : ℤ)) : ℝ)| < 1 / 2 := by
      rw [← hm', ← hm]; exact hy1
    have h9 : (((m' - m : ℤ)) : ℝ) = 0 := by
      have hb : (((m' - m : ℤ)) : ℝ) < 1 := by
        have := (abs_lt.mp h5).2; push_cast at this ⊢; linarith
      have ha : (-1 : ℝ) < (((m' - m : ℤ)) : ℝ) := by
        have := (abs_lt.mp h5).1; push_cast at this ⊢; linarith
      have h9a : (m' - m : ℤ) < 1 := by exact_mod_cast hb
      have h9b : (-1 : ℤ) < m' - m := by exact_mod_cast ha
      have : (m' - m : ℤ) = 0 := by omega
      rw [this]; simp
    have hmm : m' = m := by
      have : m' - m = 0 := by exact_mod_cast h9
      omega
    rw [hm', hm, hmm]
  have hall : ∀ᶠ y in nhds z, Ψ y = Ψ z := by
    have h := Filter.eventually_all.mpr hcoord
    filter_upwards [h] with y hy
    exact funext hy
  have heq : (fun _ : ι → ℝ => Ψ z) =ᶠ[nhds z] Ψ :=
    hall.mono (fun y hy => hy.symm)
  have hderiv : fderiv ℝ Ψ z = 0 := by
    rw [← Filter.EventuallyEq.fderiv_eq heq]
    simp [fderiv_const]
  rwa [hΨ] at hderiv


/-- `pd` of a real-valued function pushed into `ℂ`. -/
lemma pd_ofReal (f : (ι → ℝ) → ℝ) (y : ι → ℝ) (h : DifferentiableAt ℝ f y) (k : ι) :
    Work.Diff.STE.pd k (fun x => ((f x : ℝ) : ℂ)) y = ((Work.Diff.STE.pdR k f y : ℝ) : ℂ) := by
  rw [Work.Diff.STE.pd, Work.Diff.STE.pdR]
  rw [show (fun x : ι → ℝ => ((f x : ℝ) : ℂ)) = ⇑Complex.ofRealCLM ∘ f from rfl]
  rw [fderiv_comp y (ContinuousLinearMap.differentiableAt _) h, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

/-- `fun x ↦ f x j` is differentiable wherever `f` is. -/
lemma differentiableAt_proj {f : (ι → ℝ) → (ι → ℝ)} {y : ι → ℝ}
    (h : DifferentiableAt ℝ f y) (j : ι) : DifferentiableAt ℝ (fun x => f x j) y := by
  exact ((ContinuousLinearMap.proj j).differentiableAt).comp y h

/-- the `ℂ`-valued version of a real-valued differentiable function -/
lemma differentiableAt_ofReal {f : (ι → ℝ) → ℝ} {y : ι → ℝ}
    (h : DifferentiableAt ℝ f y) : DifferentiableAt ℝ (fun x => ((f x : ℝ) : ℂ)) y :=
  (Complex.ofRealCLM.differentiableAt).comp y h

/-- **The chain-rule vanishing `Σ_k ∂ᵢtl_k · (∂_k sl_j ∘ tl) = δ_{ij}` on `{a ≠ 0}`.**  This is
`∂ᵢ (sl_j ∘ tl) = δ_{ij}`, read through the chain rule; it holds because `sl ∘ tl - id` is locally
constant on `{a ≠ 0}` (see `fderiv_sub_id_eq_zero`). -/
lemma pd_sl_tl_eq {sl tl : (ι → ℝ) → (ι → ℝ)} {a : (ι → ℝ) → ℂ}
    (hQP : ∀ V : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 V →
      ∀ z : ι → ℝ, a z ≠ 0 → V (sl (tl z)) = V z)
    (hsl : ContDiff ℝ (⊤ : ℕ∞) sl) (htl : ContDiff ℝ (⊤ : ℕ∞) tl) (hacont : Continuous a)
    {z : ι → ℝ} (hz : a z ≠ 0) (i j : ι) :
    (∑ k, ((dT i k tl z : ℝ) : ℂ) * ((dT k j sl (tl z) : ℝ) : ℂ))
      = if j = i then 1 else 0 := by
  have hcontΨ : Continuous (fun z : ι → ℝ => sl (tl z) - z) :=
    (hsl.continuous.comp htl.continuous).sub continuous_id
  have hdΨ := fderiv_sub_id_eq_zero (sl := sl) (tl := tl) hQP hcontΨ hacont hz
  have hdifΨ : DifferentiableAt ℝ (fun z : ι → ℝ => sl (tl z) - z) z :=
    ((hsl.contDiffAt.differentiableAt (by simp)).comp z
      (htl.contDiffAt.differentiableAt (by simp))).sub differentiableAt_id
  have hid : fderiv ℝ (fun z : ι → ℝ => sl (tl z)) z = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    have hfun : (fun z : ι → ℝ => sl (tl z)) = fun z => (sl (tl z) - z) + z := by
      funext z; exact (sub_add_cancel (sl (tl z)) z).symm
    rw [hfun]
    change fderiv ℝ (fun y : ι → ℝ => (fun z : ι → ℝ => sl (tl z) - z) y
      + (fun z : ι → ℝ => z) y) z = ContinuousLinearMap.id ℝ (ι → ℝ)
    rw [fderiv_fun_add (f := fun z : ι → ℝ => sl (tl z) - z) (g := fun z : ι → ℝ => z)
        hdifΨ differentiableAt_id,
      hdΨ, show (fun z : ι → ℝ => z) = id from rfl, fderiv_id, zero_add]
  have hchain : Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.compMap tl
        (fun y : ι → ℝ => ((sl y j : ℝ) : ℂ))) z
      = ∑ k, ((dT i k tl z : ℝ) : ℂ) * ((dT k j sl (tl z) : ℝ) : ℂ) := by
    rw [pd_compMap_eq_sum i _ tl z
      (differentiableAt_ofReal (differentiableAt_proj
        (hsl.contDiffAt.differentiableAt (by simp)) j))
      (htl.contDiffAt.differentiableAt (by simp))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_ofReal (fun y => sl y j) (tl z)
      (differentiableAt_proj (hsl.contDiffAt.differentiableAt (by simp)) j) k]
    rfl
  rw [← hchain]
  have hstep : Work.Diff.STE.pd i (Work.Diff.STE.B3.SymCalc.compMap tl
        (fun y : ι → ℝ => ((sl y j : ℝ) : ℂ))) z
      = ((Work.Diff.STE.pdR i (fun z : ι → ℝ => sl (tl z) j) z : ℝ) : ℂ) := by
    rw [show Work.Diff.STE.B3.SymCalc.compMap tl (fun y : ι → ℝ => ((sl y j : ℝ) : ℂ))
        = (fun z : ι → ℝ => ((sl (tl z) j : ℝ) : ℂ)) from rfl]
    exact pd_ofReal (fun z : ι → ℝ => sl (tl z) j) z
      (differentiableAt_proj ((hsl.contDiffAt.comp z htl.contDiffAt).differentiableAt (by simp)) j) i
  rw [hstep, pdR_proj (fun z : ι → ℝ => sl (tl z)) z
      ((hsl.contDiffAt.comp z htl.contDiffAt).differentiableAt (by simp)) i j,
    hid]
  simp only [ContinuousLinearMap.id_apply, Pi.single_apply]
  split_ifs <;> norm_num


/-! ## §5. The commutator identity for `∂ᵢ` -/

/-- Pointwise multiplication, as an operator on functions. -/
noncomputable def mu (h V : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ := h * V

/-- The Friedrichs bracket `[S_ε, M_h] V = S_ε (h · V) - h · S_ε V`. -/
noncomputable def fbr (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (h V : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  fun y => Work.Diff.STE.B3.SymCalc.flatCut ρ ε (mu h V) y
    - h y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε V y

lemma mu_add (h V₁ V₂ : (ι → ℝ) → ℂ) : mu h (V₁ + V₂) = mu h V₁ + mu h V₂ := by
  simp only [mu]; exact mul_add h V₁ V₂

lemma periodic1_mu {h V : (ι → ℝ) → ℂ} (hh : Work.Diff.STE.Periodic1 h)
    (hV : Work.Diff.STE.Periodic1 V) : Work.Diff.STE.Periodic1 (mu h V) :=
  fun i x => by simp only [mu, Pi.mul_apply, hh i x, hV i x]

lemma contDiff_mu {h V : (ι → ℝ) → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) : ContDiff ℝ (⊤ : ℕ∞) (mu h V) :=
  hh.mul hV

lemma flatCut_zero (ρ : (ι → ℝ) → ℝ) (ε : ℝ) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun _ : ι → ℝ => 0) = fun _ : ι → ℝ => 0 := by
  have h0 : Work.Diff.STE.fourierCoeff (fun _ : ι → ℝ => (0 : ℂ)) = fun _ => 0 := by
    funext k; simp [Work.Diff.STE.fourierCoeff]
  rw [Work.Diff.STE.B3.SymCalc.flatCut, h0]
  funext x
  simp [Work.Diff.STE.seriesFun, Work.Diff.STE.trunc]

lemma flatCut_sum {β : Type*} (s : Finset β) (f : β → (ι → ℝ) → ℂ)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (hf : ∀ b ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f b)) (hfp : ∀ b ∈ s, Work.Diff.STE.Periodic1 (f b)) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => ∑ b ∈ s, f b x)
      = fun x => ∑ b ∈ s, Work.Diff.STE.B3.SymCalc.flatCut ρ ε (f b) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using flatCut_zero ρ ε
  | insert a s ha ih =>
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (f a) := hf a (Finset.mem_insert_self a s)
      have h6 : Work.Diff.STE.Periodic1 (f a) := hfp a (Finset.mem_insert_self a s)
      have h2 : ∀ b ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f b) :=
        fun b hb => hf b (Finset.mem_insert_of_mem hb)
      have h4 : ∀ b ∈ s, Work.Diff.STE.Periodic1 (f b) :=
        fun b hb => hfp b (Finset.mem_insert_of_mem hb)
      have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ b ∈ s, f b x) :=
        ContDiff.sum fun b hb => h2 b hb
      have h5 : Work.Diff.STE.Periodic1 (fun x => ∑ b ∈ s, f b x) :=
        fun i x => Finset.sum_congr rfl (fun b hb => h4 b hb i x)
      have key := Work.Diff.STE.B3.SymCalcStep7.flatCut_add ρ hρ ε h1 h6 h3 h5
      have hsum : (fun x => ∑ b ∈ insert a s, f b x) = f a + fun x => ∑ b ∈ s, f b x := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hsum, key, ih h2 h4]
      funext x; rw [Finset.sum_insert ha]; rfl


/-! ## §6. The two identifications of the leading terms with transfers -/

/-- The folded map agrees with `τ` **on the whole support** of `γ` (the identity holds on the open
set `{γ ≠ 0}` by `lift_eq_of_coeff_ne` and extends by continuity). -/
lemma lift_eq_of_mem_tsupport {γ : (ι → ℝ) → ℂ} {τ tl : (ι → ℝ) → (ι → ℝ)} {a : (ι → ℝ) → ℂ}
    (h : LiftData γ τ tl a)
    (hfd : ∀ z ∈ tsupport γ, ∀ m : ι → ℤ, m ≠ 0 →
      z + Work.Diff.STE.iVec m ∉ tsupport γ)
    (hτc : Continuous τ) (htlc : Continuous tl)
    (V : (ι → ℝ) → ℂ) (hV : Work.Diff.STE.Periodic1 V) (hVc : Continuous V)
    {y : ι → ℝ} (hy : y ∈ tsupport γ) : V (tl y) = V (τ y) := by
  have hclosed : IsClosed {y : ι → ℝ | V (tl y) = V (τ y)} :=
    isClosed_eq (hVc.comp htlc) (hVc.comp hτc)
  have hsub : {y : ι → ℝ | γ y ≠ 0} ⊆ {y : ι → ℝ | V (tl y) = V (τ y)} :=
    fun y hy => lift_eq_of_coeff_ne h hfd V hV hy
  have hcl : tsupport γ ⊆ closure {y : ι → ℝ | γ y ≠ 0} := fun y hy => hy
  exact hclosed.closure_subset_iff.mpr hsub (hcl hy)

/-- **`M_{∂ᵢa} ∘ compMap tl = perTransfer (∂ᵢγ) τ`** on `1`-periodic functions. -/
lemma mul_compMap_eq_perTransfer {γ : (ι → ℝ) → ℂ} {τ tl : (ι → ℝ) → (ι → ℝ)}
    {a : (ι → ℝ) → ℂ}
    (hpd : ∀ i' : ι, Work.Diff.STE.pd i' a
      = fun z => ∑' m : ι → ℤ, Work.Diff.STE.pd i' γ (z + Work.Diff.STE.iVec m))
    (hpdγ_sub : ∀ (i : ι) (y : ι → ℝ), Work.Diff.STE.pd i γ y ≠ 0 → y ∈ tsupport γ)
    (hmodts : ∀ V : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 V → ∀ y : ι → ℝ, y ∈ tsupport γ →
      V (tl y) = V (τ y))
    (htlp : Work.Diff.STE.Periodic1 tl)
    (i : ι) (V : (ι → ℝ) → ℂ) (hV : Work.Diff.STE.Periodic1 V) :
    (fun z : ι → ℝ => Work.Diff.STE.pd i a z * V (tl z))
      = Work.Diff.STE.B3.perTransfer (Work.Diff.STE.pd i γ) τ V := by
  funext z
  rw [hpd i, Work.Diff.STE.B3.perTransfer, ← tsum_mul_right]
  refine tsum_congr fun m => ?_
  by_cases hm : Work.Diff.STE.pd i γ (z + Work.Diff.STE.iVec m) = 0
  · rw [hm, zero_mul, zero_mul]
  · have hmem : z + Work.Diff.STE.iVec m ∈ tsupport γ := hpdγ_sub i _ hm
    have hVtl : Work.Diff.STE.Periodic1 (fun w : ι → ℝ => V (tl w)) := fun a x => by
      show V (tl (x + Pi.single a 1)) = V (tl x)
      rw [htlp a x]
    rw [← hmodts V hV _ hmem, Work.Diff.STE.B3.periodic1_add_iVec hVtl z m]


/-! ## §7. The order-zero statement, as a named predicate; summability of the weights -/

/-- The transfer-cut operator `A_ε = perTransfer γ τ ∘ flatCut ρ ε ∘ perTransfer γinv σ`. -/
noncomputable def cutOp (γ γinv : (ι → ℝ) → ℂ) (τ σ : (ι → ℝ) → (ι → ℝ))
    (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (W : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  Work.Diff.STE.B3.perTransfer γ τ
    (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.perTransfer γinv σ W))

/-- **The order-zero statement for `[∂ᵢ, A_ε]`**: the first-order commutator of the transfer-cut
with a partial derivative gains one full derivative, uniformly in `ε ∈ (0,1]`, at every integer
Sobolev level. -/
def HasPdBound (γ γinv : (ι → ℝ) → ℂ) (τ σ : (ι → ℝ) → (ι → ℝ))
    (ρ : (ι → ℝ) → ℝ) (i : ι) : Prop :=
  ∀ t : ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ W : (ι → ℝ) → ℂ,
    ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
    CSqZ t (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
        Work.Diff.STE.pd i (cutOp γ γinv τ σ ρ ε W) z
          - cutOp γ γinv τ σ ρ ε (Work.Diff.STE.pd i W) z))
      ≤ C * CSqZ t (Work.Diff.STE.fourierCoeff W)

/-- **Summability of the weighted Fourier coefficients** of a smooth `1`-periodic function, at
every integer exponent. -/
lemma summable_CSqZ_fourierCoeff (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfp : Work.Diff.STE.Periodic1 f) (t : ℤ) :
    Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t
      * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) := by
  by_cases ht : 0 ≤ t
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, t ≤ (N : ℤ) := ⟨t.toNat, by omega⟩
    exact summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff f) t N hN
      (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hfp N)
  · have h1 : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ (0 : ℤ)
        * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2) :=
      summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff f) 0 0 le_rfl
        (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hfp 0)
    exact summable_wt_zpow_mul_normSq (Work.Diff.STE.fourierCoeff f) t 0 (by omega) h1


/-- **The folded map agrees with `τ` on the whole support of `γ`, for *every* `1`-periodic `V`.**
The pointwise identity `V (tl y) = V (τ y)` is first proved for continuous `V`
(`lift_eq_of_mem_tsupport`); applied to the characters this shows that `tl y - τ y` is a lattice
vector on `tsupport γ`, whence the identity for an arbitrary `1`-periodic `V`. -/
lemma lift_eq_tau_tsupport_all {γ : (ι → ℝ) → ℂ} {τ tl : (ι → ℝ) → (ι → ℝ)}
    {a : (ι → ℝ) → ℂ}
    (hLift : LiftData γ τ tl a)
    (hfd : ∀ z ∈ tsupport γ, ∀ m : ι → ℤ, m ≠ 0 →
      z + Work.Diff.STE.iVec m ∉ tsupport γ)
    (hτc : Continuous τ) (htlc : Continuous tl)
    (V : (ι → ℝ) → ℂ) (hV : Work.Diff.STE.Periodic1 V) :
    ∀ y ∈ tsupport γ, V (tl y) = V (τ y) := by
  -- step 1: the coordinate differences are integers on the support
  have hlat : ∀ (j : ι) (y : ι → ℝ), y ∈ tsupport γ →
      tl y j - τ y j ∈ (Set.range (fun n : ℤ => (n : ℝ))) := by
    intro j y hy
    have h := lift_eq_of_mem_tsupport hLift hfd hτc htlc
      (Work.Diff.STE.fourierExp (Pi.single j (1 : ℤ))) (periodic1_fourierExp _)
      (Work.Diff.STE.contDiff_fourierExp _).continuous hy
    rw [fourierExp_single, fourierExp_single] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * (((tl y j : ℝ) : ℂ)
        - ((τ y j : ℝ) : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination hn
    have h4 := congrArg (fun w : ℂ => w / (2 * (Real.pi : ℂ) * Complex.I)) h3
    rw [mul_div_cancel_left₀ _ Complex.two_pi_I_ne_zero,
      mul_div_cancel_right₀ _ Complex.two_pi_I_ne_zero] at h4
    have h5 : (((tl y j - τ y j : ℝ)) : ℂ) = ((n : ℤ) : ℂ) := by
      rw [Complex.ofReal_sub]; exact h4
    exact (Complex.ofReal_injective h5).symm
  -- step 2: assemble the lattice vector
  intro y hy
  choose k hk using fun j => hlat j y hy
  have hky : tl y = τ y + Work.Diff.STE.iVec k := by
    funext j
    rw [Pi.add_apply, Work.Diff.STE.iVec_apply]
    have := hk j
    linarith
  rw [hky, Work.Diff.STE.B3.periodic1_add_iVec hV (τ y) k]


/-- **Smoothness and `1`-periodicity of a transfer.**  For smooth `c` with compact support and
smooth `T`, `W` (no periodicity of `W` needed) the periodisation `perTransfer c T W` is smooth and
`1`-periodic. -/
lemma perTransfer_contDiff_of (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcs : HasCompactSupport c) (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (W : (ι → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perTransfer c T W) ∧
      Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perTransfer c T W) := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => c z * W (T z)) := hc.mul (hW.comp hT)
  have hcs' : HasCompactSupport (fun z : ι → ℝ => c z * W (T z)) := by
    refine HasCompactSupport.mono hcs ?_
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; exact hx (by rw [h0, zero_mul])
  exact Work.Diff.STE.B3.SymCalcStep8.periodization_compact_contDiff _ hΦ hcs'

end Work.Diff.STE.B3.SymCalcStep8
