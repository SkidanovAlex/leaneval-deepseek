import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.GalFields.Norm.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Row1
import Submission.Work.FTS.Nonlinear.Open.Row2
import Submission.Work.FTS.Nonlinear.Open.Row3
import Submission.Work.FTS.Nonlinear.Open.Row4
import Submission.Work.FTS.Nonlinear.Open.Row5
import Submission.Work.FTS.Nonlinear.Open.Row6
import Submission.Work.FTS.Nonlinear.Open.Row7
import Submission.Work.FTS.Nonlinear.Open.Splits
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dz
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.FinalClock.L12LinearSub
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.MuFix.MufunS
import Submission.Work.FTS.StrongPersist.L3Rhs.Assembly
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The angular profiles `c2m` and `s2`, and the generic helpers -/

/-- `(z,θ) ↦ c2m θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  have hsnd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hcos : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.contDiff_cos.comp (contDiff_const.mul hsnd)
  have hsin2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
    (Real.contDiff_sin.comp hsnd).pow 2
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) :=
    hcos.sub hsin2
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2) := h1.of_le le_top
  exact h2.contDiffOn.mono (Set.subset_univ _)

/-- `(z,θ) ↦ sin(2θ)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_two_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin (2 * θ)) := by
  have hsnd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp (contDiff_const.mul hsnd)
  have h2 : ContDiff ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    h1.of_le le_top
  exact h2.contDiffOn.mono (Set.subset_univ _)

/-- The negation of a `SmoothOpen` function is `SmoothOpen`. -/
theorem smoothOpen_neg' {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) :=
  hf.neg

/-- `|c2m θ| ≤ 1000`. -/
theorem abs_c2m_le_thousand (θ : ℝ) : |Work.Construction.c2m θ| ≤ 1000 := by
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hs : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_le_one θ]
  have hcm : Work.Construction.c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl
  rw [hcm]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hc hs
    _ ≤ 1000 := by norm_num

/-- `|D_θ^i (c2m)| ≤ 1000 sin(2θ)` on `Iθ` for `1 ≤ i ≤ 4`. -/
theorem DthIter_c2m_le_sin (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) (θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
  rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
    Real.rpow_natCast _ 2] at h
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
  calc |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) ^ 2 := h
    _ ≤ 1000 * Real.sin (2 * θ) := by linarith

/-- `∂_z` is additive on the open quadrant for a pointwise decomposition `f = f' + k` of
`SmoothOpen` data. -/
theorem pz_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz f z θ = Work.Spaces.pz f' z θ + Work.Spaces.pz k z θ := by
  intro z θ hz hθ0 hθ1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have hd' : DifferentiableAt ℝ (Function.uncurry f') (z, θ) :=
    ((hf'.forall 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
      (by norm_num)
  have hdk : DifferentiableAt ℝ (Function.uncurry k) (z, θ) :=
    ((hk.forall 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
      (by norm_num)
  have h1 : DifferentiableAt ℝ (fun z' => f' z' θ) z :=
    Work.Spaces.differentiableAt_curry_left hd'
  have h2 : DifferentiableAt ℝ (fun z' => k z' θ) z :=
    Work.Spaces.differentiableAt_curry_left hdk
  have hkey : (fun z' => f z' θ) = fun z' => f' z' θ + k z' θ := by
    funext z'
    exact h z' θ
  simp only [Work.Spaces.pz]
  rw [hkey]
  exact deriv_add h1 h2

/-- `∂_θ` is additive on the open quadrant for a pointwise decomposition `f = f' + k` of
`SmoothOpen` data. -/
theorem pth_add_of_smoothOpen {f f' k : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f') (hk : Work.FTS.EllipticEst.SmoothOpen k)
    (h : ∀ z θ, f z θ = f' z θ + k z θ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ + Work.Spaces.pth k z θ := by
  intro z θ hz hθ0 hθ1
  have h1 : DifferentiableAt ℝ (fun θ' => f' z θ') θ :=
    Work.FTS.NonlinRows.differentiableAt_slice_snd_of_smoothOpen hf' hz ⟨hθ0, hθ1⟩
  have h2 : DifferentiableAt ℝ (fun θ' => k z θ') θ :=
    Work.FTS.NonlinRows.differentiableAt_slice_snd_of_smoothOpen hk hz ⟨hθ0, hθ1⟩
  have hkey : (fun θ' => f z θ') = fun θ' => f' z θ' + k z θ' := by
    funext θ'
    exact h z θ'
  simp only [Work.Spaces.pth]
  rw [hkey]
  exact deriv_add h1 h2

/-- **Linearity of `L₁₂` in the profile**: for `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest `a`, `b`
and `z ≥ 0`, `L₁₂(a)(z) - L₁₂(b)(z) = L₁₂(a-b)(z)`. -/
theorem L12_sub_eq_of_smoothOpen {α : ℝ} {a b : ℝ → ℝ → ℝ}
    (hasm : Work.FTS.EllipticEst.SmoothOpen a) (hbsm : Work.FTS.EllipticEst.SmoothOpen b)
    (hamem : Work.Spaces.HkMem α 4 a) (hbmem : Work.Spaces.HkMem α 4 b) :
    ∀ z, 0 ≤ z → Work.Construction.L12 a z - Work.Construction.L12 b z
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) z := by
  intro z hz
  set b' : ℝ → ℝ → ℝ := fun z θ => -b z θ with hb'def
  have h1 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ :=
    fun s hs => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hasm hamem
      (lt_of_le_of_lt hz hs)
  have h2 : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * b' s θ / s) Work.Spaces.Iθ := by
    intro s hs
    have h := Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hbsm hbmem
      (lt_of_le_of_lt hz hs)
    refine (h.neg).congr ?_
    filter_upwards with θ
    simp only [hb'def, Pi.neg_apply]
    ring
  have h3 : MeasureTheory.IntegrableOn (Work.Construction.L12dens a) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hasm hamem).mono_set
      (fun s hs => lt_of_le_of_lt hz hs)
  have h4 : MeasureTheory.IntegrableOn (Work.Construction.L12dens b') (Set.Ioi z) := by
    have hb4 : MeasureTheory.IntegrableOn
        (fun s => -(Work.Construction.L12dens b s)) (Set.Ioi z) :=
      ((Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hbsm hbmem).mono_set
        (fun s hs => lt_of_le_of_lt hz hs)).neg
    refine hb4.congr ?_
    filter_upwards with s
    show -(Work.Construction.L12dens b s) = Work.Construction.L12dens b' s
    rw [hb'def]
    show -(Work.FM.L12dens Work.Spaces.K b s)
      = Work.FM.L12dens Work.Spaces.K (fun z θ => -b z θ) s
    exact (Work.FTS.FinalClock.L12dens_neg' (K := Work.Spaces.K) (f := b) (s := s)).symm
  have hadd := (Work.FTS.LocData.L12_add_mul (c := (0 : ℝ)) (a := a) (b := b') (z := z)
    h1 h2 h3 h4).1
  have hb'neg : Work.Construction.L12 b' z = -Work.Construction.L12 b z := by
    rw [hb'def]
    exact Work.Construction.L12_neg b z
  have hfun : (fun z θ => a z θ - b z θ) = fun z θ => a z θ + b' z θ := by
    funext z θ
    simp only [hb'def]
    exact sub_eq_add_neg (a z θ) (b z θ)
  rw [hfun, hadd, hb'neg]
  ring

/-- From an `HkSq`-comparison, the corresponding `Xn`-comparison. -/
theorem Xn_le_of_HkSq_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : Work.Spaces.HkSq α 4 f ≤ C * Work.Spaces.HkSq α 4 g) :
    Work.FTS.Nonlin.Xn α f ≤ Real.sqrt C * Work.FTS.Nonlin.Xn α g := by
  have h1 : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 g) :=
    Real.sqrt_le_sqrt h
  have h2 : Real.sqrt (C * Work.Spaces.HkSq α 4 g)
      = Real.sqrt C * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hC _
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt (C * Work.Spaces.HkSq α 4 g) := h1
    _ = Real.sqrt C * Work.FTS.Nonlin.Xn α g := by
        rw [h2]
        rfl

/-! ## The nine pieces of the difference `N₀(g) - N₀(g')` -/

/-- `(1/α)·L₁₂(g)·h` — the first half of the `N₀₃`-difference. -/
def P1 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 g z * h z θ)

/-- `(1/α)·L₁₂(h)·g'` — the second half of the `N₀₃`-difference. -/
def P2 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (1 / α) * (Work.Construction.L12 h z * g' z θ)

/-- `(3/2α)·D_θF_*·L₁₂(h)` — the `N₀₄ᵃ`-difference. -/
def P3 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) *
    (Work.Spaces.Dth (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z)

/-- `(3/2α)·L₁₂(g)·D_θh` — the first half of the `N₀₄ᵇ`-difference. -/
def P4 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 g z * Work.Spaces.Dth h z θ)

/-- `(3/2α)·L₁₂(h)·D_θg'` — the second half of the `N₀₄ᵇ`-difference. -/
def P5 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (3 / (2 * α)) * (Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)

/-- `-c2m·(D_zF_*·L₁₂(h))` — the `N₀₅ᵃ`-difference. -/
def P6 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ *
    (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * Work.Construction.L12 h z))

/-- `-c2m·(L₁₂(g)·D_zh)` — the first half of the `N₀₅ᵇ`-difference. -/
def P7 (α : ℝ) (g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ * (Work.Construction.L12 g z * Work.Spaces.Dz h z θ))

/-- `-c2m·(L₁₂(h)·D_zg')` — the second half of the `N₀₅ᵇ`-difference. -/
def P8 (α : ℝ) (g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Construction.c2m θ * (Work.Construction.L12 h z * Work.Spaces.Dz g' z θ))

/-- `-(c2m·L₁₂(F_*))·D_zh` — the `N₀₆`-difference. -/
def P9 (α : ℝ) (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -((Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
    * Work.Spaces.Dz h z θ)

/-! ## The right-nested sum of the nine pieces, the constants, and the package constants -/

/-- The right-nested sum `P1 + (P2 + … + P9)` of the nine pieces. -/
def Rsum (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  P1 α g h + (P2 α g' h + (P3 α h + (P4 α g h + (P5 α g' h + (P6 α h
    + (P7 α g h + (P8 α g' h + P9 α h)))))))

/-- The factor `(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·|h|_{ℋ⁵}` of the estimates. -/
def TOf (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : ℝ :=
  (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g') * Work.FTS.GalFields.Xn5 α h

theorem TOf_nonneg (α : ℝ) (g g' h : ℝ → ℝ → ℝ) : 0 ≤ TOf α g g' h := by
  rw [TOf]
  exact mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 g,
    Work.Spaces.HkNorm_nonneg α 5 g']) (Work.Spaces.HkNorm_nonneg α 5 h)

/-- The package constant of `D_θF_*` in the norm `𝒲^{4,∞}`. -/
noncomputable def CFdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.DthFstar_W

theorem CFdef_spec : 0 < CFdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ CFdef * α ^ 2 :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.DthFstar_W

theorem CFdef_pos : 0 < CFdef := CFdef_spec.1

/-- The package constant of `D_zF_*` in the norm `𝒲^{4,∞}`. -/
noncomputable def Cdzdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.DzFstar_W

theorem Cdzdef_spec : 0 < Cdzdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
    Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ Cdzdef * α :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.DzFstar_W

theorem Cdzdef_pos : 0 < Cdzdef := Cdzdef_spec.1

/-- The package constant of `c2m·L₁₂(F_*)` in the norm `𝒲^{4,∞}`. -/
noncomputable def Cwdef : ℝ := Classical.choose Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

theorem Cwdef_spec : 0 < Cwdef ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ Cwdef * α :=
  Classical.choose_spec Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

theorem Cwdef_pos : 0 < Cwdef := Cwdef_spec.1

/-- **Multiplication by `c2m` preserves `ℋ⁴` and its energy**, with a universal constant: the
angular factor `c2m` is bounded by `1000` and its `D_θ`-iterates (orders `1..4`) are
`≤ 1000 sin 2θ`, which is exactly the hypothesis of `ang_mul_HkSq_le`. -/
theorem c2m_mul_HkSq_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.c2m θ * f z θ) ∧
    Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * f z θ)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  refine ⟨C1 * 1000 ^ 2, by positivity, ?_⟩
  intro α f hα hα1 hfsm hfmem
  exact hC1 α hα hα1 (fun θ => Work.Construction.c2m θ) 1000 (by norm_num)
    smoothOpen_c2m_ang (fun θ _ => abs_c2m_le_thousand θ)
    (fun i hi hi4 θ hθ => DthIter_c2m_le_sin i hi hi4 θ hθ) f hfsm hfmem

/-- The universal constant of the `c2m`-multiplier. -/
noncomputable def Cangdef : ℝ := Classical.choose c2m_mul_HkSq_le

theorem Cangdef_spec : 0 < Cangdef ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.c2m θ * f z θ) ∧
    Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * f z θ)
      ≤ Cangdef * Work.Spaces.HkSq α 4 f :=
  Classical.choose_spec c2m_mul_HkSq_le

theorem Cangdef_pos : 0 < Cangdef := Cangdef_spec.1

/-! ## The nine per-piece constants -/

noncomputable def kA1 (α Ci : ℝ) : ℝ := (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci

noncomputable def kA2 (α Ci : ℝ) : ℝ := (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci

noncomputable def kA3 (α Ci CF : ℝ) : ℝ :=
  (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci)

noncomputable def kA4 (α Ci : ℝ) : ℝ := (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA5 (α Ci : ℝ) : ℝ := (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA6 (α Ci Cdz : ℝ) : ℝ :=
  Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci)

noncomputable def kA7 (α Ci : ℝ) : ℝ := Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA8 (α Ci : ℝ) : ℝ := Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)

noncomputable def kA9 (α Ci Cw : ℝ) : ℝ := Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α)

/-- The sum of the nine per-piece constants. -/
noncomputable def ksum (α Ci CF Cdz Cw : ℝ) : ℝ :=
  kA1 α Ci + kA2 α Ci + kA3 α Ci CF + kA4 α Ci + kA5 α Ci
    + kA6 α Ci Cdz + kA7 α Ci + kA8 α Ci + kA9 α Ci Cw

theorem ksum_nonneg {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) : 0 ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA1_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA1 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA2_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA2 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA3_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA3 α Ci CF ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA4_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA4 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA5_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA5 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA6_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA6 α Ci Cdz ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA7_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA7 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA8_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA8 α Ci ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h9 : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cw * α) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

theorem kA9_le_ksum {α Ci CF Cdz Cw : ℝ} (hα : 0 < α) (hCi : 0 < Ci) (hCF : 0 < CF)
    (hCdz : 0 < Cdz) (hCw : 0 < Cw) :
    kA9 α Ci Cw ≤ ksum α Ci CF Cdz Cw := by
  have h1 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h2 : 0 ≤ (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci := by positivity
  have h3 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci) := by positivity
  have h4 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h5 : 0 ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h6 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdz * α) * Ci) := by positivity
  have h7 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  have h8 : 0 ≤ Real.sqrt Cangdef * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci) := by positivity
  rw [ksum, kA1, kA2, kA3, kA4, kA5, kA6, kA7, kA8, kA9]
  linarith

end Work.FTS.GalFields.RHS
