import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

/-! ## The reusable ingredients of the *value*-bound argument

The proof of `EpsRHSP_slotSup_val` below is a *value*-bound version of `EpsRHSP_slotSup`: every
derivative falling on the mollified profile is moved onto the (smooth, compactly supported)
mollifier kernel with `mixed_Jeps_kernel_partial` at `j' = i' = 0`, and the routed kernel
`Kd (Jker ρ ε) j i` is supported in the ball of radius `ε`, so only the *values* of the profile
at the shifted points enter.  The three lemmas collected here are exactly that argument, split
into reusable pieces. -/

/-! ### Support of the routed kernel -/

/-- A partial derivative at `p` of a function that vanishes on a whole neighbourhood of `p` is
zero.  (`partFst` is the plain `∂₁` of the kernel calculus of `mixed_Jeps_kernel_partial`.) -/
theorem partFst_eq_zero_of_eq_zero_off {u : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) (hu : ∀ q ∉ S, u q = 0) {p : ℝ × ℝ} (hp : p ∉ S) :
    partFst u p = 0 := by
  have h0 : u =ᶠ[nhds p] 0 := by
    filter_upwards [hS.isOpen_compl.mem_nhds hp] with q hq
    exact hu q hq
  have hcont : ContinuousAt (fun s : ℝ => (s, p.2)) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hg : (fun s : ℝ => u (s, p.2)) =ᶠ[nhds p.1] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  show deriv (fun s : ℝ => u (s, p.2)) p.1 = 0
  rw [hg.deriv_eq, deriv_const]

/-- The `∂₂`-analogue of `partFst_eq_zero_of_eq_zero_off`. -/
theorem partSnd_eq_zero_of_eq_zero_off {u : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsClosed S) (hu : ∀ q ∉ S, u q = 0) {p : ℝ × ℝ} (hp : p ∉ S) :
    partSnd u p = 0 := by
  have h0 : u =ᶠ[nhds p] 0 := by
    filter_upwards [hS.isOpen_compl.mem_nhds hp] with q hq
    exact hu q hq
  have hcont : ContinuousAt (fun t : ℝ => (p.1, t)) p.2 :=
    continuousAt_const.prodMk continuousAt_id
  have hg : (fun t : ℝ => u (p.1, t)) =ᶠ[nhds p.2] (fun _ => 0) :=
    hcont.tendsto.eventually h0
  show deriv (fun t : ℝ => u (p.1, t)) p.2 = 0
  rw [hg.deriv_eq, deriv_const]

/-- **The routed kernel vanishes outside the ball of radius `ε`.**  `Jker ρ ε` vanishes on the
open complement of `Metric.closedBall 0 ε`, and by `partFst_eq_zero_of_eq_zero_off` each partial
derivative of a function that vanishes on a *neighbourhood* of `p` also vanishes at `p`;
iterating gives the claim for `Kd (Jker ρ ε) a b = ∂₁^a ∂₂^b (Jker ρ ε)`. -/
theorem Kd_Jker_eq_zero_of_notMem {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) : ∀ p ∉ Metric.closedBall (0 : ℝ × ℝ) ε, Kd (Jker ρ ε) a b p = 0 := by
  induction a with
  | zero =>
    induction b with
    | zero => intro p hp; exact Jker_eq_zero_of_not_mem hρ hε hp
    | succ b ih =>
      intro p hp
      rw [Kd_zero_succ]
      exact partSnd_eq_zero_of_eq_zero_off Metric.isClosed_closedBall ih hp
  | succ a ih =>
    intro p hp
    rw [Kd_succ_eq]
    exact partFst_eq_zero_of_eq_zero_off Metric.isClosed_closedBall ih hp

/-! ### An integral bound for a kernel supported in the ball -/

/-- **Integral bound.**  If `K` is integrable, vanishes off `Metric.closedBall 0 ε`, and `F` is
bounded by `B` on that ball, then `|∫ K·F| ≤ (∫ |K|) · B`.  The pointwise estimate
`‖K p · F p‖ ≤ |K p| · B` holds trivially where `K p = 0` and by the support of `K` elsewhere, so
no integrability of the product is needed (`norm_integral_le_of_norm_le`). -/
theorem abs_integral_mul_le_of_support {K : ℝ × ℝ → ℝ} {ε B : ℝ} (hKint : Integrable K)
    (hsupp : ∀ p ∉ Metric.closedBall (0 : ℝ × ℝ) ε, K p = 0)
    {F : ℝ × ℝ → ℝ} (hF : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε → |F p| ≤ B) :
    |∫ p : ℝ × ℝ, K p * F p| ≤ (∫ p : ℝ × ℝ, |K p|) * B := by
  have hg : Integrable (fun p : ℝ × ℝ => |K p| * B) := hKint.abs.mul_const B
  have hle : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), ‖K p * F p‖ ≤ |K p| * B :=
    Eventually.of_forall fun p => by
      by_cases hKp : K p = 0
      · simp [hKp]
      · have hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
          by_contra hcon
          exact hKp (hsupp p hcon)
        have hp' : max |p.1| |p.2| ≤ ε := by
          simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
            Real.norm_eq_abs] using hp
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hF p (le_trans (le_max_left _ _) hp') (le_trans (le_max_right _ _) hp'))
          (abs_nonneg _)
  calc |∫ p : ℝ × ℝ, K p * F p|
      = ‖∫ p : ℝ × ℝ, K p * F p‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ p : ℝ × ℝ, |K p| * B := norm_integral_le_of_norm_le hg hle
    _ = (∫ p : ℝ × ℝ, |K p|) * B := integral_mul_const B _

/-! ### The mass of the routed kernels, and the slot bound for `J_ε f` -/

/-- The `L¹`-mass of the kernel that has been routed `j` times in `z` and `i` times in `θ`.
It is finite (`Kd (Jker ρ ε) j i` is continuous with compact support) and depends only on `ρ`,
`ε` and the slot — this is where the `ε`-dependence of the constant of `EpsRHSP_slotSup_val`
comes from.  (`Kd_Jker_eq_zero_of_notMem` shows that, like `Jker ρ ε` itself, it may be
integrated over the ball of radius `ε` alone.) -/
noncomputable def Kmass (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (j i : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ, |Kd (Jker ρ ε) j i p|

theorem Kmass_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (j i : ℕ) : 0 ≤ Kmass ρ ε j i :=
  integral_nonneg fun p => abs_nonneg (Kd (Jker ρ ε) j i p)

/-- The total mass over the fifteen slots of order `≤ 4`, which dominates every single one of
them (together with the factor `2 ^ i` coming from the `θ`-routing). -/
noncomputable def KmassTot (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, (2 : ℝ) ^ i * Kmass ρ ε j i

theorem KmassTot_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : 0 ≤ KmassTot ρ ε := by
  unfold KmassTot
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (Kmass_nonneg ρ ε j i)

/-- Every slot of order `≤ 4` is dominated by the total mass. -/
theorem two_pow_mul_Kmass_le_KmassTot (ρ : ℝ × ℝ → ℝ) (ε : ℝ) {j i : ℕ} (hji : j + i ≤ 4) :
    (2 : ℝ) ^ i * Kmass ρ ε j i ≤ KmassTot ρ ε := by
  have hj : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ i' ∈ Finset.range 5, (0 : ℝ) ≤ (2 : ℝ) ^ i' * Kmass ρ ε j i' :=
    fun i' _ => mul_nonneg (by positivity) (Kmass_nonneg ρ ε j i')
  calc (2 : ℝ) ^ i * Kmass ρ ε j i
      ≤ ∑ i' ∈ Finset.range 5, (2 : ℝ) ^ i' * Kmass ρ ε j i' :=
        Finset.single_le_sum (f := fun i' => (2 : ℝ) ^ i' * Kmass ρ ε j i') hinner hi
    _ ≤ KmassTot ρ ε := by
        unfold KmassTot
        refine Finset.single_le_sum
          (f := fun j' => ∑ i' ∈ Finset.range 5, (2 : ℝ) ^ i' * Kmass ρ ε j' i')
          (fun j' _ => ?_) hj
        exact Finset.sum_nonneg fun i' _ =>
          mul_nonneg (by positivity) (Kmass_nonneg ρ ε j' i')

/-- **The routed-kernel slot bound for the mollified profile**: from a *value* bound `|f| ≤ B`
on the shifted region of `(z,θ)` one gets

  `|D_z^j D_θ^i (J_ε f) z θ| ≤ 2^i · (∫ ‖Kd (Jker ρ ε) j i‖) · B`.

`mixed_Jeps_kernel_partial` with `j' = i' = 0` expresses `D_z^jD_θ^i (J_ε f) z θ` as
`2^i ∫ p, ∂₁^j∂₂^i (Jker ρ ε) p · f (zShift z p.1) (thShift θ p.2)`, and
`abs_integral_mul_le_of_support` bounds that integral, the routed kernel being supported in the
ball of radius `ε`. -/
theorem abs_mixed_Jeps_le_val {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε B : ℝ} (hε : 0 < ε)
    {f : Work.FTS.Galerkin.Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |f (zShift z p.1) (thShift θ p.2)| ≤ B)
    (j i : ℕ) :
    |Work.Spaces.mixed j i (Jeps ρ ε f) z θ| ≤ (2 : ℝ) ^ i * Kmass ρ ε j i * B := by
  have hkey := mixed_Jeps_kernel_partial ρ hρ hε hsm hz hθ j i 0 0 (Nat.zero_le j) (Nat.zero_le i)
  have hKcont : Continuous (Kd (Jker ρ ε) j i) :=
    (Kd_smooth _ (fun n => Jker_smooth hρ ε) j i 1).continuous
  have hKint : Integrable (Kd (Jker ρ ε) j i) :=
    hKcont.integrable_of_hasCompactSupport
      (Kd_compact _ (Jker_hasCompactSupport hρ.moll hε) j i)
  have hbound := abs_integral_mul_le_of_support (K := Kd (Jker ρ ε) j i) hKint
    (fun p hp => Kd_Jker_eq_zero_of_notMem hρ.moll hε j i p hp)
    (F := fun p => f (zShift z p.1) (thShift θ p.2)) hF
  have hcongr : (∫ p : ℝ × ℝ, iteratedDeriv j (fun s : ℝ => iteratedDeriv i
        (fun t : ℝ => Jker ρ ε (s, t)) p.2) p.1 * f (zShift z p.1) (thShift θ p.2))
      = ∫ p : ℝ × ℝ, Kd (Jker ρ ε) j i p * f (zShift z p.1) (thShift θ p.2) := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Kd_eq]
  rw [hkey]
  simp only [Nat.sub_zero, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
  rw [hcongr]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ i)]
  calc (2 : ℝ) ^ i * |∫ p : ℝ × ℝ, Kd (Jker ρ ε) j i p * f (zShift z p.1) (thShift θ p.2)|
      ≤ (2 : ℝ) ^ i * ((∫ p : ℝ × ℝ, |Kd (Jker ρ ε) j i p|) * B) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (2 : ℝ) ^ i * (∫ p : ℝ × ℝ, |Kd (Jker ρ ε) j i p|) * B := by ring

/-- **Slot bounds of the projected right-hand side from a *value* bound on the pre-mollified
right-hand side** (single scale `ε`).

This is `Work.FTS.StrongEps.EpsRHSP_slotSup` with its hypothesis `hsup` replaced: instead of
uniform bounds on the mixed slots of `epsWP` on the window `K'` one only needs a uniform *value*
bound of `epsWP` on `K'`.  The price is that the produced constant depends on `ε` — which is
harmless for the intended consumer (`E5G.slice_lip_norm`, whose `hslotb` hypothesis only feeds the
integrability bookkeeping of its proof and never its final constant), and is why no uniformity in
`ε` is claimed here.

The reason the value bound suffices: every derivative of `J_ε (epsWP s)` can be moved onto the
(smooth, compactly supported) mollifier kernel.  `Work.FTS.StrongEps.mixed_Jeps_kernel_partial`
with `j' = i' = 0` gives

  `D_z^jD_θ^i (J_ε f) z θ = 2^i ∫ p, ∂₁^j∂₂^i (Jker ρ ε) p · f (zShift z p.1) (thShift θ p.2)`,

and `Kd (Jker ρ ε) j i` is supported in the ball of radius `ε` (`Jker_ne_zero_support`), so only
the values of `f = epsWP s` at the shifted points (which lie in `K'`) enter; the mass of the
routed kernel is finite for the fixed `ε > 0`.  The correction term
`(L₁₂ (J_ε (epsWP s)) 0 / pzNorm) • bump` is handled as in `EpsRHSP_slotSup` (via
`Work.FTS.StrongEps.abs_L12_Jeps_le` and the fixed bounded profile `bump`). -/
theorem EpsRHSP_slotSup_val {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ 1 → |q.2| ≤ 1 →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K',
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s p.1 p.2| ≤ B)
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ p ∈ K, |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, B, hB, hbdd⟩ := hwin
  obtain ⟨KW, hKW, hnorm'⟩ := hnorm
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨B * KmassTot ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hB (KmassTot_nonneg ρ ε))
      (mul_nonneg (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le) hCb0)
  · intro j i hji s hs p hp
    obtain ⟨hmems, hnormbs⟩ := hnorm' s hs
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
        Work.FTS.StrongEps.Quad := (hreg s hs).forall
    -- the *value* bound of `epsWP` transfers to the shifted points inside the kernel's ball
    have hF : ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s
            (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)| ≤ B :=
      fun q hq1 hq2 => hbdd s hs
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2)
        (hshift p hp q (le_trans hq1 hε.2) (le_trans hq2 hε.2))
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
        ≤ B * KmassTot ρ ε := by
      refine le_trans (abs_mixed_Jeps_le_val (ρ := ρ) hρ hε.1 hsm hz hθ hF j i) ?_
      calc (2 : ℝ) ^ i * Kmass ρ ε j i * B
          = ((2 : ℝ) ^ i * Kmass ρ ε j i) * B := by ring
        _ ≤ KmassTot ρ ε * B :=
            mul_le_mul_of_nonneg_right (two_pow_mul_Kmass_le_KmassTot ρ ε hji) hB
        _ = B * KmassTot ρ ε := by ring
    have hcorr : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0|
          ≤ CL * KW := hCL hα hε.1 hε.2 hKW hsm hmems hnormbs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le)
    have hsplit : Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ B * KmassTot ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb :=
          add_le_add hmain hcorr

end Work.FTS.StrongEps
