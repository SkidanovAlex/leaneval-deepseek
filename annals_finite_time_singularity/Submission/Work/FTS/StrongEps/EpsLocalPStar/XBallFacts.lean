import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS_LocDatum3a.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The uniform `ℋᵏ`-size of the projected-mollified profile, from the `X`-ball -/

/-- **The profile `W_u = Pz (J_ε u)` is `ℋᵏ`-bounded (`k ≤ 6`) by the `X`-size of the datum.**
For a smooth kernel `ρ` there is a constant `C > 0` with

  `|W_u|_{ℋᵏ} ≤ C (C/ε)⁶ (1 + R)`   for every `k ≤ 6`, every `α ∈ (0,1]`, every `ε ∈ (0,1]`,
  every `R ≥ 0` and every `u` with `SmoothOpen u`, `EpsMem α u` and `EpsSq α u ≤ R`.

This is `HkSq_JepsPz_le` at level `k` followed by `HkNorm = √HkSq`, the square root being absorbed
by `√(C(C/ε)^{2k}R) ≤ √C (C/ε)⁶ (1+R)`. -/
theorem exists_Wp_bound_of_EpsMem (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ R : ℝ, 0 ≤ R →
      ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.StrongEps.EpsMem α f →
        Work.FTS.StrongEps.EpsSq α f ≤ R → ∀ k : ℕ, k ≤ 6 →
        Work.Spaces.HkNorm α k (Work.FTS.StrongEps.EpsRLX.Wp ρ ε f)
          ≤ C * (C / ε) ^ 6 * (1 + R) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  set K : ℝ := max 1 C₀ with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hC₀K : C₀ ≤ K := le_max_right _ _
  refine ⟨K, hKpos, ?_⟩
  intro α hα ε hε R hR f hf hmem hEps k hk
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hKe : (1 : ℝ) ≤ K / ε := by
    rw [le_div_iff₀ hε0]; linarith
  have hb0 : 0 ≤ C₀ / ε := div_nonneg hC₀pos.le hε0.le
  have hbK : C₀ / ε ≤ K / ε := div_le_div_of_nonneg_right hC₀K hε0.le
  have hpow0 : 0 ≤ K / ε := div_nonneg hKpos.le hε0.le
  -- the `ℋᵏ`-bound of `HkSq_JepsPz_le`, with the exponent upgraded to `12`
  have hbase : Work.Spaces.HkSq α k (Work.FTS.StrongEps.EpsRLX.Wp ρ ε f)
      ≤ K * (K / ε) ^ 12 * R := by
    have h := hC₀ α hα ε hε0 hε1 k hk f hf hmem
    have h1 : C₀ * (C₀ / ε) ^ (2 * k) ≤ K * (K / ε) ^ 12 := by
      have h2 : (C₀ / ε) ^ (2 * k) ≤ (K / ε) ^ (2 * k) := pow_le_pow_left₀ hb0 hbK _
      have h2k : 2 * k ≤ 12 := by omega
      have h3 : (K / ε) ^ (2 * k) ≤ (K / ε) ^ 12 := pow_le_pow_right₀ hKe h2k
      exact mul_le_mul hC₀K (h2.trans h3) (pow_nonneg hb0 _) hKpos.le
    calc Work.Spaces.HkSq α k (Work.FTS.StrongEps.EpsRLX.Wp ρ ε f)
        ≤ C₀ * (C₀ / ε) ^ (2 * k) * Work.FTS.StrongEps.EpsSq α f := h
      _ ≤ C₀ * (C₀ / ε) ^ (2 * k) * R :=
          mul_le_mul_of_nonneg_left hEps (mul_nonneg hC₀pos.le (pow_nonneg hb0 _))
      _ ≤ K * (K / ε) ^ 12 * R := mul_le_mul_of_nonneg_right h1 hR
  -- take the square root: `√(K (K/ε)¹²R) ≤ K (K/ε)⁶ (1+R)` because `R ≤ (1+R)² ≤ K (1+R)²`
  have hsix : ((K / ε) ^ 6) ^ 2 = (K / ε) ^ 12 := by ring
  have hsq : (K * (K / ε) ^ 6 * (1 + R)) ^ 2 = K ^ 2 * (K / ε) ^ 12 * (1 + R) ^ 2 := by
    rw [mul_pow, mul_pow, hsix]
  have hmid : K * (K / ε) ^ 12 * R ≤ K ^ 2 * (K / ε) ^ 12 * (1 + R) ^ 2 := by
    have hp : 0 ≤ (K / ε) ^ 12 := pow_nonneg hpow0 12
    have hR1 : R ≤ (1 + R) ^ 2 := by nlinarith [hR]
    have hKK : K ≤ K ^ 2 := by nlinarith [hK1]
    have hKR : K * R ≤ K ^ 2 * (1 + R) ^ 2 :=
      calc K * R ≤ K * (1 + R) ^ 2 := mul_le_mul_of_nonneg_left hR1 hKpos.le
        _ ≤ K ^ 2 * (1 + R) ^ 2 :=
            mul_le_mul_of_nonneg_right hKK (by positivity)
    calc K * (K / ε) ^ 12 * R = (K * R) * (K / ε) ^ 12 := by ring
      _ ≤ (K ^ 2 * (1 + R) ^ 2) * (K / ε) ^ 12 := mul_le_mul_of_nonneg_right hKR hp
      _ = K ^ 2 * (K / ε) ^ 12 * (1 + R) ^ 2 := by ring
  rw [Work.Spaces.HkNorm]
  calc Real.sqrt (Work.Spaces.HkSq α k (Work.FTS.StrongEps.EpsRLX.Wp ρ ε f))
      ≤ Real.sqrt (K * (K / ε) ^ 12 * R) := Real.sqrt_le_sqrt hbase
    _ ≤ Real.sqrt ((K * (K / ε) ^ 6 * (1 + R)) ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; exact hmid)
    _ = K * (K / ε) ^ 6 * (1 + R) := Real.sqrt_sq (by positivity)

/-! ## `ℋ⁴`-membership of the unprojected mollified datum, from the class of the profile -/

/-- **The reverse of `PZeroAux.PzJepsHkMem`.**  `Wp ρ ε u = Pz (J_ε u) = J_ε u − (L₁₂(J_ε u)(0)/pzNorm)·bump`,
so the honesty of the *unprojected* datum `J_ε u` follows from that of the profile and of the
correction profile, i.e. from `ClassC α (Wp ρ ε u)` (whose `mem8` field gives `HkMem α 8` of the
profile). -/
theorem HkMem_Jeps_of_ClassC_Wp {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε)
    (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hcl : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)) :
    Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) := by
  have hWmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
    Work.FTS.OpenPkg.HkMem_mono_open hcl.reg 4 (by norm_num) hcl.mem8
  have hpt : ∀ z θ : ℝ, Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      = Work.FTS.StrongEps.Jeps ρ ε u z θ
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ := by
    intro z θ
    rw [Work.FTS.StrongEps.EpsRLX.Wp, Work.FTS.StrongEps.Pz_apply]
  have heq : Work.FTS.StrongEps.Jeps ρ ε u
      = fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        + (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0 / Work.FTS.StrongEps.pzNorm)
          * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [hpt z θ]
    ring
  rw [heq]
  exact Work.FTS.EllipticEst.HkMem_add_open hcl.reg
    (Work.FTS.StrongEps.PZeroAux.smoothOpen_const_mul_gen _
      Work.FTS.StrongEps.smoothOpen_bump)
    hWmem
    (Work.FTS.StrongEps.PZeroAux.HkMem_const_mul_gen _
      (Work.FTS.StrongEps.PZeroAux.classC_Pz_hkMem_bump α 4))

/-! ## The structural identity `W_u - W_v = W_{u-v}` in the `X`-ball -/

/-- **The difference of two projected-mollified profiles is the profile of the difference**, under
the *weak* (`X`-ball) hypotheses on the two data: `SmoothOpen` of both and the class condition on
both profiles.

The proof is the `HkMem α 6`-free version of `EpsRLX.Wp_sub_eq`: the affinity of `P₀` requires
`L₁₂ (J_ε u − J_ε v)(0) = L₁₂(J_ε u)(0) − L₁₂(J_ε v)(0)`, which `EComparison.L12_sub_HkMem`
supplies from the `ℋ⁴`-membership produced by `HkMem_Jeps_of_ClassC_Wp`; the additivity of `J_ε`
is `Jeps_sub_eq`, which needs only the open-quadrant smoothness. -/
theorem Wp_sub_eq_of_ClassC {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u v : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hclu : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u))
    (hclv : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) :
    Work.FTS.StrongEps.EpsRLX.Wp ρ ε u - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) := by
  have hJu := HkMem_Jeps_of_ClassC_Wp hρ hα hε hu hclu
  have hJv := HkMem_Jeps_of_ClassC_Wp hρ hα hε hv hclv
  have hJsu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hu)
  have hJsv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hv)
  have hL : Work.Construction.L12
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hJsu hJsv hJu hJv 0 (Set.mem_Ici.mpr le_rfl)
  have hJ : (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
        - Work.FTS.StrongEps.Jeps ρ ε v z θ)
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsRLX.Jeps_sub_eq hρ.moll hε hu hv
  calc Work.FTS.StrongEps.EpsRLX.Wp ρ ε u - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v) := rfl
    _ = Work.FTS.StrongEps.Pz
          (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) :=
        Work.FTS.StrongEps.EpsRLX.Pz_sub_eq hL
    _ = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ)) := by
        rw [hJ]
    _ = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) := rfl

/-! ## The `ℋ⁵`-size of the profile difference, from the `X`-size of the datum difference -/

/-- **The Lipschitz ingredient of the `X`-gate.**  For two admissible data the level-`5` `ℋ`-size of
the difference of the projected-mollified profiles is controlled by the `X`-size of the difference
of the data, with the mollifier cost `(C/ε)^12`:

  `HkSq α 5 (W_u − W_v) ≤ C (C/ε)^12 EpsSq α (u − v)`.

`Wp_sub_eq_of_ClassC` replaces `W_u − W_v` by `W_{u−v}` and `HkSq_JepsPz_le` (at `k = 5`, whose
hypotheses `SmoothOpen (u−v)` and `EpsMem α (u−v)` are available here) estimates the latter. -/
theorem HkSq_Wp_sub_le_of_ClassC (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {u v : Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
      Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
      Work.Spaces.HkSq α 5 (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  set K : ℝ := max 1 C₀ with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  refine ⟨K, hKpos, ?_⟩
  intro α hα ε hε u v hu hv hclu hclv hmem
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP hu hv
  have hid := Wp_sub_eq_of_ClassC hα hρ hε0 hu hv hclu hclv
  have hbase := hC₀ α hα ε hε0 hε1 5 (by norm_num) (fun z θ => u z θ - v z θ) hsm hmem
  rw [show (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) from hid]
  refine hbase.trans ?_
  have hS : 0 ≤ Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) :=
    Work.FTS.StrongEps.EpsSq_nonneg α _
  have hb0 : 0 ≤ C₀ / ε := div_nonneg hC₀pos.le hε0.le
  have hbK : C₀ / ε ≤ K / ε := div_le_div_of_nonneg_right (le_max_right _ _) hε0.le
  have hb1 : (1 : ℝ) ≤ K / ε := by
    rw [le_div_iff₀ hε0]; linarith
  have h2 : (C₀ / ε) ^ (2 * 5) ≤ (K / ε) ^ 12 :=
    (pow_le_pow_left₀ hb0 hbK 10).trans (pow_le_pow_right₀ hb1 (by norm_num))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (le_max_right _ _) h2 (pow_nonneg hb0 10) hKpos.le) hS

end Work.FTS.StrongEps.EpsLocalPStar
