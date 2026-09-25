import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.fderiv_bmPotential
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-! ## Generic multilinear-norm lemmas

The `(k+1)`-st iterated derivative of a function of one complex variable is the Fréchet derivative
of its `k`-th iterated derivative, so bounds on the scalar functions `z ↦ D^k F(z)[u]` (uniform in
the tuple `u` of `k` directions, with the natural factor `∏ ‖u_l‖`) give bounds on `D^{k+1}F`.
-/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On an open set, the first iterated derivative within the set applied to a constant tuple is the
Fréchet derivative. -/
lemma fderiv_eq_iteratedFDerivWithin_one {f : E → ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    {z : E} (hz : z ∈ Ω) (v : E) :
    fderiv ℝ f z v = iteratedFDerivWithin ℝ 1 f Ω z (fun _ => v) := by
  rw [iteratedFDerivWithin_one_apply (hΩ.uniqueDiffWithinAt hz) (fun _ => v),
    fderivWithin_of_isOpen hΩ hz]

/-- **Operator norm bound for the top iterated derivative, from bounds on the scalar functions
`z ↦ D^k F(z)[u]`.** -/
lemma norm_iteratedFDeriv_succ_le_of_bound {F : E → ℂ} {k : ℕ} {B : ℝ} {Ω : Set E}
    (hdiff : Differentiable ℝ (iteratedFDeriv ℝ k F))
    (hB : 0 ≤ B)
    (h : ∀ z ∈ Ω, ∀ u : Fin k → E,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ B * ∏ l, ‖u l‖) :
    ∀ z ∈ Ω, ‖iteratedFDeriv ℝ (k + 1) F z‖ ≤ B := by
  intro z hz
  refine ContinuousMultilinearMap.opNorm_le_bound hB fun w => ?_
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (hdiff z) (m := w)]
  calc ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z (w 0)‖
      ≤ ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z‖ * ‖w 0‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (B * ∏ l : Fin k, ‖w l.succ‖) * ‖w 0‖ :=
        mul_le_mul_of_nonneg_right (h z hz (Fin.tail w)) (norm_nonneg _)
    _ = B * ∏ i : Fin (k + 1), ‖w i‖ := by rw [Fin.prod_univ_succ]; ring

/-- **Hölder bound for the top iterated derivative, from Hölder bounds on the scalar functions
`z ↦ D^k F(z)[u]`.** -/
lemma norm_iteratedFDeriv_succ_sub_le_of_holder {F : E → ℂ} {k : ℕ} {α B : ℝ} {Ω : Set E}
    (hdiff : ∀ z ∈ Ω, DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z)
    (hB : 0 ≤ B)
    (h : ∀ z ∈ Ω, ∀ z' ∈ Ω, ∀ u : Fin k → E, z ≠ z' →
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
          - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ B * (∏ l, ‖u l‖) * ‖z - z'‖ ^ α) :
    ∀ z ∈ Ω, ∀ z' ∈ Ω, z ≠ z' →
      ‖iteratedFDeriv ℝ (k + 1) F z - iteratedFDeriv ℝ (k + 1) F z'‖
        ≤ B * ‖z - z'‖ ^ α := by
  intro z hz z' hz' hzz
  refine ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg hB (Real.rpow_nonneg (norm_nonneg _) α)) fun w => ?_
  rw [sub_apply,
    DifferentiableAt.iteratedFDeriv_succ_apply_left' (hdiff z hz) (m := w),
    DifferentiableAt.iteratedFDeriv_succ_apply_left' (hdiff z' hz') (m := w),
    ← ContinuousLinearMap.sub_apply]
  calc ‖(fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z
          - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z') (w 0)‖
      ≤ ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z
          - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y (Fin.tail w)) z'‖ * ‖w 0‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (B * (∏ l : Fin k, ‖w l.succ‖) * ‖z - z'‖ ^ α) * ‖w 0‖ :=
        mul_le_mul_of_nonneg_right (h z hz z' hz' (Fin.tail w) hzz) (norm_nonneg _)
    _ = B * ‖z - z'‖ ^ α * ∏ i : Fin (k + 1), ‖w i‖ := by rw [Fin.prod_univ_succ]; ring

end Generic

/-- **Top-order Schauder bounds for the Bochner–Martinelli potential**, given the order-zero
estimate as a hypothesis.

Assume the order-zero estimate for the polydisc `polydisc c r`: for every `C¹` family `g`
vanishing where `∃ i, r i ≤ ‖z i - c i‖`,
`‖bmPotential g‖_{C^{1,α}(polydisc c r)} ≤ C₀ Σ_j ‖g_j‖_{C^{0,α}}`.  Then for every `k` there is
`C` such that every family `f` with `C^{k+1}` components supported in `polydisc c (r/2)`
satisfies

`‖D^{k+1} (bmPotential f)‖_{sup on polydisc c (r/2)} ≤ C Σ_j ‖f_j‖_{C^{k,α}(ℂⁿ)}`

and the same with the sup replaced by the Hölder-`α` seminorm of `D^{k+1}`.

Proof route.  By the commutation identity at order `k`, for each tuple `u` of `k` directions the
function `z ↦ D^k (bmPotential f)(z)[u]` equals `bmPotential (D^k f · u)`, whose data is `C¹`
and vanishes outside `polydisc c r`; the hypothesis therefore bounds its `C^{1,α}` norm on
`polydisc c r` by `C₀ Σ_j ‖D^k f_j · u‖_{C^{0,α}} ≤ C₀ (∏ ‖u_l‖) Σ_j ‖f_j‖_{C^{k,α}}`.  The
`(k+1)`-st iterated derivative of the potential is the Fréchet derivative of the
multilinear-map-valued function `z ↦ D^k (bmPotential f)(z)` (`iteratedFDeriv_succ_apply_left`),
and that Fréchet derivative is bounded by the supremum over tuples `u` of the derivatives of the
scalar functions `z ↦ D^k (bmPotential f)(z)[u]`; the uniform Hölder-`α` bound above (which is
uniform in `u` with the factor `∏ ‖u_l‖`) makes the remainder estimate uniform, giving both the
operator norm of `D^{k+1}` and its Hölder seminorm. -/
theorem bmPotential_top_bound {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
        (iterDerivNorm (k + 1) (bmPotential f) (polydisc c (fun j => r j / 2))
            ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) Set.univ) ∧
        (holderSeminorm (k + 1) α (bmPotential f) (polydisc c (fun j => r j / 2))
            ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) Set.univ) := by
  obtain ⟨C₀, hC₀pos, hbase'⟩ := hbase
  have hC₀nn : 0 ≤ C₀ := hC₀pos.le
  refine ⟨C₀, hC₀pos, ?_⟩
  intro f hf hfsup
  set Ω : Set (Fin n → ℂ) := polydisc c r with hΩdef
  set Ω' : Set (Fin n → ℂ) := polydisc c (fun j => r j / 2) with hΩ'def
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact isOpen_polydisc c r
  have hΩ'open : IsOpen Ω' := by rw [hΩ'def]; exact isOpen_polydisc c _
  have hsub : Ω' ⊆ Ω := by
    rw [hΩdef, hΩ'def]
    exact polydisc_mono (fun j => div_le_self (le_of_lt (hr j)) (by norm_num))
  have hcs : ∀ j, HasCompactSupport (f j) := fun j =>
    hasCompactSupport_of_halfPolydisc hr (fun z hz => hfsup j z hz)
  have hF : ContDiff ℝ (k + 1) (bmPotential f) :=
    bmPotential_contDiff_of_hasCompactSupport hn hf hcs
  have hF1 : ContDiff ℝ 1 (iteratedFDeriv ℝ k (bmPotential f)) :=
    ContDiff.iteratedFDeriv_right (i := k) (m := 1) hF
      (by exact le_of_eq (add_comm (1 : WithTop ℕ∞) (↑k : WithTop ℕ∞)))
  have hFdiff : Differentiable ℝ (iteratedFDeriv ℝ k (bmPotential f)) :=
    hF1.differentiable one_ne_zero
  by_cases hT : (∑ j, holderNorm k α (f j) Set.univ) = ⊤
  · have hne0 : ENNReal.ofReal C₀ ≠ 0 := by simpa [hC₀pos.ne']
    have hmul : ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ) = ⊤ := by
      rw [hT, ENNReal.mul_top hne0]
    exact ⟨le_trans le_top (le_of_eq hmul.symm), le_trans le_top (le_of_eq hmul.symm)⟩
  · set S : ℝ := ∑ j, (holderNorm k α (f j) Set.univ).toReal with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]; exact Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
    have hT_eq : (∑ j, holderNorm k α (f j) Set.univ) = ENNReal.ofReal S := by
      rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
      exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal
        (ne_top_of_le_ne_top hT
          (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)))).symm
    -- the commutation identity at order `k`
    have hcomm : ∀ u : Fin k → (Fin n → ℂ),
        (fun y => iteratedFDeriv ℝ k (bmPotential f) y u)
          = bmPotential (fun j y' => iteratedFDeriv ℝ k (f j) y' u) := by
      intro u
      funext y
      exact bmPotential_iteratedFDeriv hn hr
        (fun j => (hf j).of_le (by exact_mod_cast Nat.le_succ k))
        (fun j z hz => hfsup j z hz) u y
    -- the data `D^k f_j · u` is `C¹` and vanishes outside `polydisc c r`
    have hreg : ∀ u : Fin k → (Fin n → ℂ),
        (∀ j, ContDiff ℝ 1 (fun y => iteratedFDeriv ℝ k (f j) y u)) ∧
        (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → iteratedFDeriv ℝ k (f j) z u = 0) := by
      intro u
      constructor
      · intro j
        exact (ContinuousLinearMap.contDiff (ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin k => (Fin n → ℂ)) ℂ u)).comp
          (ContDiff.iteratedFDeriv_right (i := k) (m := 1) (hf j)
            (by exact le_of_eq (add_comm (1 : WithTop ℕ∞) (↑k : WithTop ℕ∞))))
      · intro j z hz
        obtain ⟨i, hi⟩ := hz
        have hev : (f j) =ᶠ[𝓝 z] (0 : (Fin n → ℂ) → ℂ) := by
          refine Filter.mem_of_superset (Metric.ball_mem_nhds z (half_pos (hr i))) ?_
          intro w hw
          apply hfsup j w
          refine ⟨i, ?_⟩
          have h1 : ‖w i - z i‖ ≤ dist w z := by
            rw [dist_eq_norm]
            exact norm_le_pi_norm (w - z) i
          have h2 : ‖z i - c i‖ ≤ ‖w i - c i‖ + ‖w i - z i‖ := by
            have h4 : ‖z i - c i‖ ≤ ‖z i - w i‖ + ‖w i - c i‖ := by
              calc ‖z i - c i‖ = ‖(z i - w i) + (w i - c i)‖ := by ring_nf
                _ ≤ ‖z i - w i‖ + ‖w i - c i‖ := norm_add_le _ _
            rw [norm_sub_rev (z i) (w i)] at h4
            linarith
          have h3 : dist w z < r i / 2 := by
            simpa only [Metric.mem_ball, dist_comm] using hw
          linarith
        have h2 : iteratedFDeriv ℝ k (f j) z = iteratedFDeriv ℝ k (0 : (Fin n → ℂ) → ℂ) z :=
          (hev.iteratedFDeriv ℝ k).eq_of_nhds
        rw [h2]
        simp
    -- the `C^{0,α}` norm of `D^k f_j · u` is bounded by `∏ ‖u_l‖` times the `C^{k,α}` norm of `f_j`
    have hSum : ∀ u : Fin k → (Fin n → ℂ),
        (∑ j, holderNorm 0 α (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ)
          ≤ (∑ j, holderNorm k α (f j) Set.univ) * ENNReal.ofReal (∏ l, ‖u l‖) := by
      intro u
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have h1 : iterDerivNorm 0 (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ
          ≤ iterDerivNorm k (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖) := by
        rw [iterDerivNorm_zero]
        refine iSup₂_le fun z _ => ?_
        refine le_trans (ENNReal.ofReal_le_ofReal
          (ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ k (f j) z) u)) ?_
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
        refine mul_le_mul_left ?_ _
        rw [← iteratedFDerivWithin_univ]
        exact le_iterDerivNorm k (f j) Set.univ (mem_univ z)
      have h2 : holderSeminorm 0 α (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ
          ≤ holderSeminorm k α (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖) := by
        refine iSup₂_le fun z _ => iSup₂_le fun z' _ => iSup_le fun hz => ?_
        have hb : 0 < ‖z - z'‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) α
        have h0 : ‖iteratedFDerivWithin ℝ 0 (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ z
              - iteratedFDerivWithin ℝ 0 (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ z'‖
            = ‖(iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z') u‖ := by
          simp only [iteratedFDerivWithin_zero_eq, iteratedFDeriv_zero_eq_comp,
            Function.comp_apply]
          rw [← map_sub, LinearIsometryEquiv.norm_map, sub_apply]
        have hk : iteratedFDerivWithin ℝ k (f j) Set.univ z = iteratedFDeriv ℝ k (f j) z :=
          iteratedFDerivWithin_of_isOpen k isOpen_univ (mem_univ z)
        have hk' : iteratedFDerivWithin ℝ k (f j) Set.univ z' = iteratedFDeriv ℝ k (f j) z' :=
          iteratedFDerivWithin_of_isOpen k isOpen_univ (mem_univ z')
        rw [h0]
        calc ENNReal.ofReal
              (‖(iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z') u‖ / ‖z - z'‖ ^ α)
            ≤ ENNReal.ofReal ((‖iteratedFDerivWithin ℝ k (f j) Set.univ z
                  - iteratedFDerivWithin ℝ k (f j) Set.univ z'‖ / ‖z - z'‖ ^ α)
                * ∏ l, ‖u l‖) := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [hk, hk']
              have hA : ‖(iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z') u‖
                  ≤ ‖iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z'‖
                    * ∏ l, ‖u l‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
              calc ‖(iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z') u‖
                    / ‖z - z'‖ ^ α
                  ≤ (‖iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z'‖
                      * ∏ l, ‖u l‖) / ‖z - z'‖ ^ α :=
                    div_le_div_of_nonneg_right hA hb.le
                _ = (‖iteratedFDeriv ℝ k (f j) z - iteratedFDeriv ℝ k (f j) z'‖
                      / ‖z - z'‖ ^ α) * ∏ l, ‖u l‖ := by ring
          _ = ENNReal.ofReal (‖iteratedFDerivWithin ℝ k (f j) Set.univ z
                  - iteratedFDerivWithin ℝ k (f j) Set.univ z'‖ / ‖z - z'‖ ^ α)
                * ENNReal.ofReal (∏ l, ‖u l‖) := ENNReal.ofReal_mul (by positivity)
          _ ≤ holderSeminorm k α (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖) :=
              mul_le_mul_left
                (le_holderSeminorm k α (f j) Set.univ (mem_univ z) (mem_univ z') hz) _
      have h3 : iterDerivNorm k (f j) Set.univ + holderSeminorm k α (f j) Set.univ
          ≤ holderNorm k α (f j) Set.univ := by
        rw [holderNorm]
        exact Finset.single_le_sum
          (f := fun i => iterDerivNorm i (f j) Set.univ + holderSeminorm i α (f j) Set.univ)
          (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self k))
      calc iterDerivNorm 0 (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ
            + holderSeminorm 0 α (fun y => iteratedFDeriv ℝ k (f j) y u) Set.univ
          ≤ iterDerivNorm k (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖)
            + holderSeminorm k α (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖) :=
            add_le_add h1 h2
        _ = (iterDerivNorm k (f j) Set.univ + holderSeminorm k α (f j) Set.univ)
              * ENNReal.ofReal (∏ l, ‖u l‖) := by rw [add_mul]
        _ ≤ holderNorm k α (f j) Set.univ * ENNReal.ofReal (∏ l, ‖u l‖) :=
            mul_le_mul_left h3 _
    -- the `C^{1,α}` estimate for `bmPotential (D^k f · u)` on `Ω`
    have hbnd : ∀ u : Fin k → (Fin n → ℂ),
        holderNorm 1 α (bmPotential (fun j y' => iteratedFDeriv ℝ k (f j) y' u)) Ω
          ≤ ENNReal.ofReal (C₀ * S * ∏ l, ‖u l‖) := by
      intro u
      rw [hΩdef]
      refine le_trans (hbase' _ (hreg u).1 (hreg u).2) ?_
      refine le_trans (mul_le_mul' le_rfl (hSum u)) ?_
      rw [hT_eq,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C₀ * S), ENNReal.ofReal_mul hC₀nn,
        mul_assoc]
    -- extract the pointwise bounds
    have hpoint : ∀ u : Fin k → (Fin n → ℂ),
        (∀ z ∈ Ω', ‖fderiv ℝ (bmPotential (fun j y' => iteratedFDeriv ℝ k (f j) y' u)) z‖
            ≤ C₀ * S * ∏ l, ‖u l‖) ∧
        (∀ z ∈ Ω', ∀ z' ∈ Ω', z ≠ z' →
          ‖fderiv ℝ (bmPotential (fun j y' => iteratedFDeriv ℝ k (f j) y' u)) z
              - fderiv ℝ (bmPotential (fun j y' => iteratedFDeriv ℝ k (f j) y' u)) z'‖
            ≤ (C₀ * S * ∏ l, ‖u l‖) * ‖z - z'‖ ^ α) := by
      intro u
      set ψ : Fin n → (Fin n → ℂ) → ℂ := fun j y' => iteratedFDeriv ℝ k (f j) y' u with hψdef
      have hbndu := hbnd u
      have hW : ∀ z ∈ Ω, ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z‖
          ≤ ENNReal.ofReal (C₀ * S * ∏ l, ‖u l‖) := by
        intro z hz
        exact le_trans (le_iterDerivNorm 1 (bmPotential ψ) Ω hz)
          (le_trans (iterDerivNorm_le_holderNorm 1 α (bmPotential ψ) Ω le_rfl) hbndu)
      have hWu : ∀ z ∈ Ω,
          ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z‖ ≤ C₀ * S * ∏ l, ‖u l‖ :=
        fun z hz => (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (hW z hz)
      constructor
      · intro z hz
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [fderiv_eq_iteratedFDerivWithin_one hΩopen (hsub hz) v]
        calc ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z (fun _ => v)‖
            ≤ ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z‖ * ∏ _ : Fin 1, ‖v‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z‖ * ‖v‖ := by simp
          _ ≤ (C₀ * S * ∏ l, ‖u l‖) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (hWu z (hsub hz)) (norm_nonneg _)
      · intro z hz z' hz' hzz
        have hb : 0 < ‖z - z'‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
        have hsem : ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z
            - iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z'‖
            ≤ (C₀ * S * ∏ l, ‖u l‖) * ‖z - z'‖ ^ α := by
          have h := (ENNReal.ofReal_le_ofReal_iff (by positivity :
            (0 : ℝ) ≤ C₀ * S * ∏ l, ‖u l‖)).mp
            (le_trans (le_holderSeminorm 1 α (bmPotential ψ) Ω (hsub hz) (hsub hz') hzz)
              (le_trans (holderSeminorm_le_holderNorm 1 α (bmPotential ψ) Ω le_rfl) hbndu))
          have h' := mul_le_mul_of_nonneg_right h hb.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hb)] at h'
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [ContinuousLinearMap.sub_apply, fderiv_eq_iteratedFDerivWithin_one hΩopen (hsub hz) v,
          fderiv_eq_iteratedFDerivWithin_one hΩopen (hsub hz') v, ← sub_apply]
        calc ‖(iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z
              - iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z') (fun _ => v)‖
            ≤ ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z
                - iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z'‖ * ∏ _ : Fin 1, ‖v‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z
                - iteratedFDerivWithin ℝ 1 (bmPotential ψ) Ω z'‖ * ‖v‖ := by simp
          _ ≤ ((C₀ * S * ∏ l, ‖u l‖) * ‖z - z'‖ ^ α) * ‖v‖ :=
              mul_le_mul_of_nonneg_right hsem (norm_nonneg _)
          _ = (C₀ * S * ∏ l, ‖u l‖) * ‖z - z'‖ ^ α * ‖v‖ := by ring
    -- assemble
    have hA : ∀ z ∈ Ω', ‖iteratedFDeriv ℝ (k + 1) (bmPotential f) z‖ ≤ C₀ * S :=
      norm_iteratedFDeriv_succ_le_of_bound hFdiff (mul_nonneg hC₀nn hSnn)
        (fun z hz u => by rw [hcomm u]; exact (hpoint u).1 z hz)
    have hB : ∀ z ∈ Ω', ∀ z' ∈ Ω', z ≠ z' →
        ‖iteratedFDeriv ℝ (k + 1) (bmPotential f) z
          - iteratedFDeriv ℝ (k + 1) (bmPotential f) z'‖ ≤ (C₀ * S) * ‖z - z'‖ ^ α :=
      norm_iteratedFDeriv_succ_sub_le_of_holder (fun z _ => hFdiff.differentiableAt)
        (mul_nonneg hC₀nn hSnn)
        (fun z hz z' hz' u hzz => by rw [hcomm u]; exact (hpoint u).2 z hz z' hz' hzz)
    constructor
    · rw [iterDerivNorm]
      refine iSup₂_le fun z hz => ?_
      rw [show iteratedFDerivWithin ℝ (k + 1) (bmPotential f) Ω' z
          = iteratedFDeriv ℝ (k + 1) (bmPotential f) z from
          iteratedFDerivWithin_of_isOpen (k + 1) hΩ'open hz]
      refine le_trans (ENNReal.ofReal_le_ofReal (hA z hz)) ?_
      rw [hT_eq, ENNReal.ofReal_mul hC₀nn]
    · rw [holderSeminorm]
      refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz => ?_
      rw [show iteratedFDerivWithin ℝ (k + 1) (bmPotential f) Ω' z
            = iteratedFDeriv ℝ (k + 1) (bmPotential f) z from
            iteratedFDerivWithin_of_isOpen (k + 1) hΩ'open hz,
          show iteratedFDerivWithin ℝ (k + 1) (bmPotential f) Ω' z'
            = iteratedFDeriv ℝ (k + 1) (bmPotential f) z' from
            iteratedFDerivWithin_of_isOpen (k + 1) hΩ'open hz']
      have hb : 0 < ‖z - z'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzz)) α
      calc ENNReal.ofReal
            (‖iteratedFDeriv ℝ (k + 1) (bmPotential f) z
              - iteratedFDeriv ℝ (k + 1) (bmPotential f) z'‖ / ‖z - z'‖ ^ α)
          ≤ ENNReal.ofReal (((C₀ * S) * ‖z - z'‖ ^ α) / ‖z - z'‖ ^ α) :=
            ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hB z hz z' hz' hzz) hb.le)
        _ = ENNReal.ofReal (C₀ * S) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hb)]
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal S := ENNReal.ofReal_mul hC₀nn
        _ = ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ) := by rw [hT_eq]

end Work.CR.Flat.Cauchy
