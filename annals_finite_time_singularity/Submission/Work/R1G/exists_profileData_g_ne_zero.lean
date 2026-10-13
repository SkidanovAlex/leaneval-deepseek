/-
# `Work.R1G.exists_profileData_g_ne_zero`

**The non-trivial `ProfileData`.**  The delivered inhabitant of
`Work.ConstructionInstance.ProfileData` (`profileData_inhabited`) has `g = 0`.  Here we build a
`ProfileData` whose perturbation is **nonzero in the interior of the quadrant**:

  `P.g = λ·gA`,   `gA z θ = z²/(1+z²)⁴ · sin(2θ)`,   `λ = p²/(K·(HkNorm p 2 gA + 1))`,

with `p = profExp α`, `K = 10⁷`.  The perturbation `gA` (module `Work.R1G.AnG`) is *analytic*, so
`SmoothNbhd` holds (`⊤` is the analytic order in this workspace), it vanishes at `θ = 0`, `θ = π/2`
and at `z = 0` (to second order), it decays like `z⁻⁶` and it is dominated by the angular vanishing
factor `Γ(α,·)`; the *amplitude* `λ` is chosen so that the `ℋ²`-size `100/√(γ-1)·‖g‖_{ℋ²}` — which
is exactly the constant `Cg` of `ProfileData` — is below the `St5` threshold
`p·Γ(p,π/4)/(4c(p))`: the amplitude is `O(p²)` and the threshold is `Θ(p)` as `p → 0`, so a
`p²`-small amplitude works for every `p ∈ (0,1]`.  The modulation is the standard normalised one
`λ̄(t) = 1 - t/2` at `T = 2` (as in `profileData_inhabited`), so `∃ P, P.g ≠ 0 ∧ P.λ̄ = 1 - t/2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.Defs
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.R1G.AnG
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.HkMem_gA
import Submission.Work.R1G.holderZ_gA
import Submission.Work.R1G.holderTh_gA
import Submission.Work.R1G.bound_z_pz_gA
import Submission.Work.R1G.van_gA
import Submission.Work.R1G.aesm_profile_of_continuous
import Submission.Work.R1G.HkNorm_const_mul
import Submission.Work.R1G.Gam_pi_div_four_lower
import Submission.Work.R1G.hasDerivAt_profile_of_differentiable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.R1G

/-! ## Scalar homogeneity of the weighted `H^k` operators

These elementary normalisations of `Work.Spaces.HkIntegrand` under `f ↦ c·f` are used to transfer
the estimates for `gA` to the amplitude-scaled perturbation `λ·gA`. -/

theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  rw [Work.Spaces.pz, Work.Spaces.pz]
  exact deriv_const_mul_field c

theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  rw [Work.Spaces.pth, Work.Spaces.pth]
  exact deriv_const_mul_field c

theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  rw [Work.Spaces.Dz, Work.Spaces.Dz, pz_const_mul]
  ring

theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  rw [Work.Spaces.Dth, Work.Spaces.Dth, pth_const_mul]
  ring

theorem pzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih, pz_const_mul, Work.Spaces.pzIter_succ]

theorem pthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih, pth_const_mul, Work.Spaces.pthIter_succ]

theorem DzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DzIter_succ, ih, Dz_const_mul, Work.Spaces.DzIter_succ]

theorem DthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.DthIter_succ, ih, Dth_const_mul, Work.Spaces.DthIter_succ]

theorem mixed_const_mul (c : ℝ) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

theorem HkIntegrand_const_mul (A c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt A z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h, mixed_const_mul]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [h1, h2]
  ring

/-! ## Continuity of the perturbation -/

theorem continuous_gA_curried : Continuous (fun p : ℝ × ℝ => Zf p.1 * Tf p.2) :=
  (contDiff_Zf.continuous.comp continuous_fst).mul
    (contDiff_Tf.continuous.comp continuous_snd)

theorem continuous_gA : Continuous (Function.uncurry gA) := by
  have h3 : Function.uncurry gA = fun p : ℝ × ℝ => Zf p.1 * Tf p.2 := by
    funext p
    show gA p.1 p.2 = Zf p.1 * Tf p.2
    rw [gA]
  rw [h3]
  exact continuous_gA_curried

/-! ## The main theorem -/

/-- **The construction, with its visible point.**  Besides `P.g ≠ 0` (the requested form) the
construction exhibits the perturbation as nonzero at the *interior point* `(z,θ) = (1/2, π/4)` of
the open quadrant — so the profile `F_* + P.g` really differs from `F_*` on the quadrant. -/
theorem exists_profileData_g_ne_zero_visible {α : NNReal} (hα : 0 < (α : ℝ))
    (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ P : Work.ConstructionInstance.ProfileData α,
      (∃ z θ : ℝ, 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 ∧ P.g z θ ≠ 0)
        ∧ P.lam = (fun t : ℝ => 1 - t / 2) := by
  have hp : 0 < Work.ConstructionInstance.profExp α := Work.ConstructionInstance.profExp_pos hα
  have hp1 : Work.ConstructionInstance.profExp α ≤ 1 := by
    rw [Work.ConstructionInstance.profExp]; linarith
  have hαhalf : (α : ℝ) ≤ 1 / 2 := by linarith
  have hpnn : (0 : ℝ) ≤ Work.ConstructionInstance.profExp α := hp.le
  -- the amplitude
  set K : ℝ := 10 ^ 7 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; norm_num
  set C1 : ℝ := Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 gA with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; exact Real.sqrt_nonneg _
  set rate : ℝ := (Work.ConstructionInstance.profExp α) ^ 2 / (K * (C1 + 1)) with hratedef
  have hC1p1 : 0 < C1 + 1 := by linarith
  have hratepos : 0 < rate := by rw [hratedef]; positivity
  set g : ℝ → ℝ → ℝ := fun z θ => rate * gA z θ with hgdef
  -- analyticity, vanishing and differentiability of the perturbation
  have hsmooth : Work.Spaces.SmoothNbhd g := by
    have h0 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => gA p.1 p.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := smoothNbhd_gA
    have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => rate * gA p.1 p.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
      ContDiffOn.mul contDiffOn_const h0
    have hfun : Function.uncurry g = fun p : ℝ × ℝ => rate * gA p.1 p.2 := by
      funext p
      show g p.1 p.2 = rate * gA p.1 p.2
      rw [hgdef]
    rw [Work.Spaces.SmoothNbhd, hfun]
    exact h1
  have hvt : Work.Spaces.VanishTheta g := by
    constructor
    · intro z
      show g z 0 = 0
      rw [hgdef]
      show rate * gA z 0 = 0
      rw [gA_zero_theta, mul_zero]
    · intro z
      show g z (Real.pi / 2) = 0
      rw [hgdef]
      show rate * gA z (Real.pi / 2) = 0
      rw [gA_pi_div_two, mul_zero]
  have hquad0 : ∀ θ : ℝ, g 0 θ = 0 := by
    intro θ
    rw [hgdef]
    show rate * gA 0 θ = 0
    rw [gA_zero_z, mul_zero]
  have hquad : ∀ θ : ℝ, Work.Spaces.pz g 0 θ = 0 := by
    intro θ
    have h1 : Work.Spaces.pz g = fun z θ => rate * Work.Spaces.pz gA z θ := by
      rw [hgdef, pz_const_mul]
    rw [h1]
    show rate * Work.Spaces.pz gA 0 θ = 0
    rw [pz_gA, deriv_Zf]
    norm_num
  have hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' : ℝ => Work.ConstructionInstance.profile
          (Work.ConstructionInstance.profExp α) g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile
          (Work.ConstructionInstance.profExp α) g) z θ) z := by
    intro z θ hz
    refine hasDerivAt_profile_of_differentiable (p := Work.ConstructionInstance.profExp α) ?_ hz
    intro z' θ'
    have h1 : (fun z'' : ℝ => g z'' θ') = fun z'' => (rate * Tf θ') * Zf z'' := by
      funext z''
      rw [hgdef]
      show rate * gA z'' θ' = (rate * Tf θ') * Zf z''
      rw [gA]
      ring
    rw [h1]
    exact (differentiableAt_Zf z').const_mul (rate * Tf θ')
  have hcont : Continuous (Function.uncurry g) := by
    have hfun : Function.uncurry g = fun p : ℝ × ℝ => rate * (Zf p.1 * Tf p.2) := by
      funext p
      show g p.1 p.2 = rate * (Zf p.1 * Tf p.2)
      rw [hgdef]
      show rate * gA p.1 p.2 = rate * (Zf p.1 * Tf p.2)
      rw [gA]
    rw [hfun]
    exact continuous_const.mul continuous_gA_curried
  -- the two uniform moduli and the `W^{1,∞}`-bound
  obtain ⟨CvA, hCvAnn, hvanA⟩ := van_gA (α : ℝ) hα hαhalf
  obtain ⟨LgA, hLgAnn, hzkA⟩ := holderZ_gA (α : ℝ) hα (by linarith)
  obtain ⟨LtA, hLtAnn, hzthA⟩ := holderTh_gA (α : ℝ) hα (by linarith)
  obtain ⟨CpA, hCpAnn, hg2A⟩ := bound_z_pz_gA
  -- the decay and the `ℋ²`-membership
  have hdec : Work.Spaces.DecayInZ 2 g := by
    intro j i hij θ hθ
    have h1 : Work.Spaces.pthIter i g = fun z θ => rate * Work.Spaces.pthIter i gA z θ := by
      rw [hgdef, pthIter_const_mul]
    have h2 : (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z θ)
        = fun z => rate * (Work.Spaces.pzIter j (Work.Spaces.pthIter i gA) z θ) := by
      rw [h1, pzIter_const_mul]
    rw [h2]
    simpa using (DecayInZ_gA j i hij θ hθ).const_mul rate
  have hmem : Work.Spaces.HkMem (Work.ConstructionInstance.profExp α) 2 g := by
    have hA := HkMem_gA (Work.ConstructionInstance.profExp α) hp hp1
    refine ⟨?_, ?_⟩
    · intro z hz
      have heq : (fun θ => Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 g z θ)
          = fun θ => rate ^ 2
              * Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 gA z θ := by
        funext θ
        rw [hgdef]
        exact HkIntegrand_const_mul _ _ _ _ _ _
      rw [heq]
      exact (hA.1 z hz).const_mul (rate ^ 2)
    · have heq2 : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 g z θ)
          = fun z => rate ^ 2 * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 gA z θ := by
        funext z
        rw [show (fun θ => Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 g z θ)
            = fun θ => rate ^ 2
                * Work.Spaces.HkIntegrand (Work.ConstructionInstance.profExp α) 2 gA z θ from by
          funext θ
          rw [hgdef]
          exact HkIntegrand_const_mul _ _ _ _ _ _]
        rw [MeasureTheory.integral_const_mul]
      rw [heq2]
      exact hA.2.const_mul (rate ^ 2)
  -- the `St5`-constant `Cg` and its bound
  set Cg : ℝ := 100 / Real.sqrt (Work.Spaces.gam (Work.ConstructionInstance.profExp α) - 1)
      * Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 g with hCgdef
  have hCgnn : 0 ≤ Cg := by
    rw [hCgdef]
    refine mul_nonneg (div_nonneg (by norm_num) ?_) (Real.sqrt_nonneg _)
    rw [Work.Spaces.gam_sub_one]
    positivity
  have hHkNg : Work.Spaces.HkNorm (Work.ConstructionInstance.profExp α) 2 g = rate * C1 := by
    rw [hgdef]
    exact HkNorm_const_mul (Work.ConstructionInstance.profExp α) rate hratepos.le 2 gA
  have hrate_bound : rate * C1 ≤ (Work.ConstructionInstance.profExp α) ^ 2 / K := by
    rw [hratedef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hKpos]
    nlinarith [hC1nn, hp, hKpos]
  have hfacnn : 0 ≤ 100 / Real.sqrt ((Work.ConstructionInstance.profExp α) / 10) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hstep1 : Cg ≤ 100 / Real.sqrt ((Work.ConstructionInstance.profExp α) / 10)
      * ((Work.ConstructionInstance.profExp α) ^ 2 / K) := by
    rw [hCgdef, Work.Spaces.gam_sub_one, hHkNg]
    exact mul_le_mul_of_nonneg_left hrate_bound hfacnn
  have hkey : 100 / Real.sqrt ((Work.ConstructionInstance.profExp α) / 10)
      * ((Work.ConstructionInstance.profExp α) ^ 2 / K)
      = 100 * Real.sqrt 10 * ((Work.ConstructionInstance.profExp α)
          * Real.sqrt (Work.ConstructionInstance.profExp α)) / K := by
    rw [Real.sqrt_div hp.le 10]
    have hsp : Real.sqrt (Work.ConstructionInstance.profExp α)
        * Real.sqrt (Work.ConstructionInstance.profExp α) = Work.ConstructionInstance.profExp α := by
      rw [← sq]
      exact Real.sq_sqrt hp.le
    field_simp
    nlinarith [hsp]
  have hfinal : 100 * Real.sqrt 10 * ((Work.ConstructionInstance.profExp α)
      * Real.sqrt (Work.ConstructionInstance.profExp α)) / K
      ≤ (Work.ConstructionInstance.profExp α) / 320 := by
    have hsp1 : Real.sqrt (Work.ConstructionInstance.profExp α) ≤ 1 := Real.sqrt_le_one.mpr hp1
    have hspnn : 0 ≤ Real.sqrt (Work.ConstructionInstance.profExp α) := Real.sqrt_nonneg _
    have hs10 : Real.sqrt 10 ≤ 4 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg 10]
    rw [div_le_iff₀ hKpos]
    have hb : Real.sqrt 10 * (Work.ConstructionInstance.profExp α
        * Real.sqrt (Work.ConstructionInstance.profExp α))
        ≤ 4 * (Work.ConstructionInstance.profExp α * 1) := by
      refine mul_le_mul hs10 ?_ ?_ (by norm_num)
      · exact mul_le_mul_of_nonneg_left hsp1 hpnn
      · exact mul_nonneg hpnn hspnn
    nlinarith [hb, hKdef, hpnn]
  have hthreshold : (Work.ConstructionInstance.profExp α) / 320
      ≤ Work.ConstructionInstance.profExp α
          * Work.Spaces.Gam (Work.ConstructionInstance.profExp α) (Real.pi / 4)
          / (4 * Work.Spaces.c (Work.ConstructionInstance.profExp α)) := by
    have hc := Work.Spaces.c_bounds (Work.ConstructionInstance.profExp α) hp hp1
    have hGam := Gam_pi_div_four_lower hp hp1
    have hcpos : 0 < Work.Spaces.c (Work.ConstructionInstance.profExp α) := by linarith [hc.1]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Work.Spaces.c (Work.ConstructionInstance.profExp α))]
    nlinarith [hc.1, hc.2, hGam, hp.le, hcpos]
  have hsmall : Cg ≤ Work.ConstructionInstance.profExp α
      * Work.Spaces.Gam (Work.ConstructionInstance.profExp α) (Real.pi / 4)
      / (4 * Work.Spaces.c (Work.ConstructionInstance.profExp α)) :=
    le_trans hstep1 (le_trans (le_of_eq hkey) (le_trans hfinal hthreshold))
  -- the perturbation is nonzero at the visible point
  have hgvis : g (1 / 2) (Real.pi / 4) ≠ 0 :=
    ne_of_gt (mul_pos hratepos gA_half_pi_div_four_pos)
  refine ⟨{ hα := hα
            g := g
            hvt := hvt
            hsmooth := hsmooth
            hquad0 := hquad0
            hquad := hquad
            Cg := Cg
            hCg := hCgnn
            hdec := hdec
            hmem := hmem
            hCgbig := le_refl _
            Cv := rate * CvA
            hCv := mul_nonneg hratepos.le hCvAnn
            hvan := ?_
            Lg := rate * LgA
            hLg := mul_nonneg hratepos.le hLgAnn
            hzk := ?_
            Lθ := rate * LtA
            hLθ := mul_nonneg hratepos.le hLtAnn
            hzth := ?_
            Cg' := rate * CpA
            hg2 := ?_
            hgdiff := hgdiff
            hsmall := hsmall
            hmeasP := aesm_profile_of_continuous (p := Work.ConstructionInstance.profExp α) hcont
            hα13 := hα13
            T := 2
            hT := by norm_num
            lam := fun t : ℝ => 1 - t / 2
            hlam := fun t ht => by linarith [ht.2]
            hlam0 := by norm_num
            K := 1 / 2
            hK := by norm_num
            hK12 := le_refl (1 / 2)
            hlamdif := fun t _ => Work.ConstructionInstance.hasDerivAt_lamStd t
            hlamd := fun t _ => by rw [Work.ConstructionInstance.hderivval t]; norm_num
            hlam_le := fun t ht => by linarith [ht.2]
            hlam_low := fun t ht => le_of_eq (by ring)
            L := (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1
            hL := by positivity
            hLbig := by
              have h : (2 * (2 : ℝ)) = 4 := by norm_num
              rw [h]
              exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
            M := 20 * Work.ConstructionInstance.profExp α + Cg
            hM := by positivity
            hMprof := le_refl _
            M₁ := (1 / 2) * (20 * Work.ConstructionInstance.profExp α + Cg + rate * CpA)
            hM₁ := by positivity
            hM₁big := le_refl _
            R := 2 * ((4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1)
            hR := by positivity
            hRbig := le_refl _ },
        ⟨⟨1 / 2, Real.pi / 4, by norm_num, by linarith [Real.pi_pos],
          by linarith [Real.pi_pos], hgvis⟩, rfl⟩⟩
  · -- `hvan`
    intro z θ hz hθ
    have h1 : g z θ = rate * gA z θ := by rw [hgdef]
    rw [h1, abs_mul, abs_of_nonneg hratepos.le]
    calc rate * |gA z θ| ≤ rate * (CvA * Work.ConstructionInstance.Gamma (α : ℝ) θ) :=
          mul_le_mul_of_nonneg_left (hvanA z θ hz hθ) hratepos.le
      _ = rate * CvA * Work.ConstructionInstance.Gamma (α : ℝ) θ := by ring
  · -- `hzk`
    intro z z' θ hz hz' hθ
    have h1 : g z θ - g z' θ = rate * (gA z θ - gA z' θ) := by
      rw [hgdef]; ring
    rw [h1, abs_mul, abs_of_nonneg hratepos.le]
    calc rate * |gA z θ - gA z' θ| ≤ rate * (LgA * |z - z'| ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hzkA z z' θ hz hz' hθ) hratepos.le
      _ = rate * LgA * |z - z'| ^ (α : ℝ) := by ring
  · -- `hzth`
    intro z θ θ' hz hθ hθ'
    have h1 : g z θ - g z θ' = rate * (gA z θ - gA z θ') := by
      rw [hgdef]; ring
    rw [h1, abs_mul, abs_of_nonneg hratepos.le]
    calc rate * |gA z θ - gA z θ'| ≤ rate * (LtA * |θ - θ'| ^ (α : ℝ)) :=
          mul_le_mul_of_nonneg_left (hzthA z θ θ' hz hθ hθ') hratepos.le
      _ = rate * LtA * |θ - θ'| ^ (α : ℝ) := by ring
  · -- `hg2`
    intro z θ hz hθ
    have h1 : z * Work.Spaces.pz g z θ = rate * (z * Work.Spaces.pz gA z θ) := by
      rw [hgdef, pz_const_mul]; ring
    rw [h1, abs_mul, abs_of_nonneg hratepos.le]
    exact mul_le_mul_of_nonneg_left (hg2A z θ hz hθ) hratepos.le

/-- **The requested lemma**: a `ProfileData` with a nonzero perturbation and the normalised
modulation `λ̄(t) = 1 - t/2`, obtained from the stronger `exists_profileData_g_ne_zero_visible`. -/
theorem exists_profileData_g_ne_zero {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ P : Work.ConstructionInstance.ProfileData α,
      P.g ≠ 0 ∧ P.lam = (fun t : ℝ => 1 - t / 2) := by
  obtain ⟨P, ⟨z, θ, -, -, -, hne⟩, hlam⟩ := exists_profileData_g_ne_zero_visible hα hα13
  exact ⟨P, fun hzero => hne (by simp [hzero]), hlam⟩

end Work.R1G
