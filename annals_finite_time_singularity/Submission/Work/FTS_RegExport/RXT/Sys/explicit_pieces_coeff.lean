import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.Construction.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.L12_FK_jets_of_datum
import Submission.Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-!
# `Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff`

The four explicit pieces of the forcing decomposition whose `mixed`-jets of order `≤ 2` are
bounded uniformly in `τ ∈ [0,S]` on the open quadrant:

* `L₁₂(F(τ))(z)·c2m θ` and `L₁₂(F(τ))(z)` (`F(τ) = Ftau (pExp α) (GR α g) τ`);
* `sin²θ·𝔽K(F(τ))(z)`;
* `Uop (pExp α) (Θ (pExp α) F(τ))(z,θ) / sin 2θ`, which on the open quadrant is the radial
  combination `-(3/(4β))·L₁₂(F(τ))(z) + (1/4)·𝔽K(F(τ))(z)` (`β = pExp α ≤ 1`).

The proof reduces everything to the iterated radial jets of `L₁₂(F(τ))` and `𝔽K(F(τ))`
(`L12_FK_jets_of_datum`, fed by the datum witness `Ftau_datum_of_LimApprox`), and to the
elementary angular jets of `c2m` and `sin²` computed below.

`C⁴`-smoothness of the slices of `g` (hence `C²` of `F(τ)`) is extracted from `LimApprox` by
`sliceC4_of_LimApprox` via the subsequence-extraction `slice_contDiffOn_four`.
-/

/-! ## §1 The `C⁴`-regularity of the slices of a `LimApprox` family -/

/-- **The `C⁴`-regularity of the slices**, extracted from `LimApprox` by the subsequence
extraction `slice_contDiffOn_four` (the limit of the locally uniformly convergent subsequence
is `slice g τ`, by uniqueness of limits, since the whole sequence converges pointwise to it). -/
theorem sliceC4_of_LimApprox {α C₀ T : ℝ} (hα : 0 < α) (hT : 0 < T)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox α C₀ Φs E g) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 := by
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  intro τ hτ
  refine Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four (B := B) hα
    (G := fun n => Work.FTS.Galerkin.slice (gn n) τ) (f := Work.FTS.Galerkin.slice g τ)
    ?_ ?_ ?_ ?_
  · intro n k
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hC n τ hτ).1.reg k
  · intro n
    exact Work.FTS.OpenPkg.HkMem_mono_open (hC n τ hτ).1.reg 6 (by norm_num) (hC n τ hτ).1.mem
  · intro n
    exact (hC n τ hτ).2.2
  · intro z θ hzθ
    exact hjet τ hτ 0 0 (by norm_num) z θ hzθ

/-! ## §2 Separable data: the product rule for `mixed` -/

/-- `D_z`-iterates of the zero function. -/
theorem DzIter_zero_fun (j : ℕ) :
    Work.Spaces.DzIter j (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- The `θ`-iterated operator commutes with multiplication by a `z`-only factor. -/
theorem DthIter_mul_left_z (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- The `z`-iterated operator commutes with multiplication by a `θ`-only factor. -/
theorem DzIter_mul_theta_factor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ)
      = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- `D_θ^i` of a function of `θ` alone does not depend on the radial variable. -/
theorem DthIter_z_indep (G : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => G θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
      intro z z' θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ') θ
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ')
          from funext (fun θ' => ih z z' θ')]

/-- **The `mixed`-jets of a separable datum `h(z)·G(θ)` split.** -/
theorem mixed_mul_rad_ang (h : ℝ → ℝ) (G : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z * G θ) z θ
      = Work.Elliptic.DzdIter j h z * Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ := by
  rw [Work.Spaces.mixed, DthIter_mul_left_z i h (fun _ θ' => G θ')]
  rw [show (fun z θ => h z * Work.Spaces.DthIter i (fun _ θ' => G θ') z θ)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ * h z from by
    funext z θ
    rw [mul_comm, DthIter_z_indep G i z 0 θ]]
  rw [DzIter_mul_theta_factor j (fun θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ)
    (fun z _ => h z)]
  simp only
  have hrad : Work.Spaces.DzIter j (fun z x => h z) z θ = Work.Elliptic.DzdIter j h z :=
    Work.Elliptic.DzIter_rad h j z θ
  rw [hrad, mul_comm]

/-- **The `mixed`-jets of a radial datum** vanish as soon as one `θ`-derivative is taken. -/
theorem mixed_radial (h : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z) z θ
      = if i = 0 then Work.Elliptic.DzdIter j h z else 0 := by
  rcases i with _ | k
  · rw [Work.Spaces.mixed, Work.Spaces.DthIter_zero, if_pos rfl]
    exact Work.Elliptic.DzIter_rad h j z θ
  · rw [Work.Spaces.mixed, if_neg (by omega), Work.Elliptic.DthIter_rad_succ h k,
      DzIter_zero_fun]

/-! ## §3 The angular jets of `c2m` and `sin²` -/

theorem deriv_c2m (θ : ℝ) : deriv Work.Construction.c2m θ = -3 * Real.sin (2 * θ) := by
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    refine (HasDerivAt.congr_of_eventuallyEq
      ((Real.hasDerivAt_cos (2 * θ)).comp θ h1)
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    ring
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    have hp := (Real.hasDerivAt_sin θ).pow 2
    refine (HasDerivAt.congr_of_eventuallyEq hp
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    norm_num
  have hd : deriv ((fun θ' : ℝ => Real.cos (2 * θ')) - (fun θ' : ℝ => Real.sin θ' ^ 2)) θ
      = -2 * Real.sin (2 * θ) - 2 * Real.sin θ * Real.cos θ := (hcos.sub hsin).deriv
  change deriv (fun θ' : ℝ => Real.cos (2 * θ') - Real.sin θ' ^ 2) θ = -3 * Real.sin (2 * θ)
  rw [show deriv (fun θ' : ℝ => Real.cos (2 * θ') - Real.sin θ' ^ 2) θ
      = deriv ((fun θ' : ℝ => Real.cos (2 * θ')) - (fun θ' : ℝ => Real.sin θ' ^ 2)) θ
      from rfl, hd, Real.sin_two_mul]
  ring

theorem deriv_sinsq (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have hp := (Real.hasDerivAt_sin θ).pow 2
  rw [(HasDerivAt.congr_of_eventuallyEq hp
    (Filter.Eventually.of_forall (fun x => rfl)) : HasDerivAt
      (fun θ' : ℝ => Real.sin θ' ^ 2) (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ).deriv]
  norm_num

theorem deriv_sinsq_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ') ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h0 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') (2 : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    refine (HasDerivAt.congr_of_eventuallyEq
      ((Real.hasDerivAt_sin (2 * θ)).comp θ h1)
      (Filter.Eventually.of_forall (fun x => rfl))).congr_deriv ?_
    ring
  rw [(HasDerivAt.congr_of_eventuallyEq (h0.pow 2)
    (Filter.Eventually.of_forall (fun x => rfl)) : HasDerivAt
      (fun θ' : ℝ => Real.sin (2 * θ') ^ 2)
      (2 * Real.sin (2 * θ) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ).deriv]
  norm_num
  ring

theorem DthIter_one_c2m (θ : ℝ) :
    Work.Spaces.DthIter 1 (fun _ θ' => Work.Construction.c2m θ') 0 θ
      = -3 * Real.sin (2 * θ) ^ 2 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [deriv_c2m]
  ring

theorem DthIter_two_c2m (θ : ℝ) :
    Work.Spaces.DthIter 2 (fun _ θ' => Work.Construction.c2m θ') 0 θ
      = -12 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  rw [Work.Spaces.DthIter_succ]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => Work.Spaces.DthIter 1
        (fun _ θ' => Work.Construction.c2m θ') 0 θ') = fun θ' => -3 * Real.sin (2 * θ') ^ 2
      from funext DthIter_one_c2m]
  rw [deriv_const_mul_field, deriv_sinsq_two]
  ring

/-- `|D_θ^i c2m| ≤ 12` for `i ≤ 2`. -/
theorem DthIter_c2m_le (i : ℕ) (hi : i ≤ 2) (θ : ℝ) :
    |Work.Spaces.DthIter i (fun _ θ' => Work.Construction.c2m θ') 0 θ| ≤ 12 := by
  interval_cases i
  · show |Work.Construction.c2m θ| ≤ 12
    rw [Work.Construction.c2m]
    have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact Real.sin_sq_le_one θ
    have h3 : |Real.cos (2 * θ) - Real.sin θ ^ 2| ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| :=
      abs_sub _ _
    linarith
  · rw [DthIter_one_c2m, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_le_one (2 * θ)]
  · rw [DthIter_two_c2m, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12), abs_of_nonneg (sq_nonneg _)]
    have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.sin_sq_le_one (2 * θ)]

theorem DthIter_one_sinsq (θ : ℝ) :
    Work.Spaces.DthIter 1 (fun _ θ' => Real.sin θ' ^ 2) 0 θ = Real.sin (2 * θ) ^ 2 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [deriv_sinsq, Real.sin_two_mul]
  ring

theorem DthIter_two_sinsq (θ : ℝ) :
    Work.Spaces.DthIter 2 (fun _ θ' => Real.sin θ' ^ 2) 0 θ
      = 4 * Real.sin (2 * θ) ^ 2 * Real.cos (2 * θ) := by
  rw [Work.Spaces.DthIter_succ]
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' : ℝ => Work.Spaces.DthIter 1
        (fun _ θ' => Real.sin θ' ^ 2) 0 θ') = fun θ' => Real.sin (2 * θ') ^ 2
      from funext DthIter_one_sinsq]
  rw [deriv_sinsq_two]
  ring

/-- `|D_θ^i (sin²)| ≤ 4` for `i ≤ 2`. -/
theorem DthIter_sinsq_le (i : ℕ) (hi : i ≤ 2) (θ : ℝ) :
    |Work.Spaces.DthIter i (fun _ θ' => Real.sin θ' ^ 2) 0 θ| ≤ 4 := by
  interval_cases i
  · show |Real.sin θ ^ 2| ≤ 4
    rw [abs_of_nonneg (sq_nonneg _)]
    linarith [Real.sin_sq_le_one θ]
  · rw [DthIter_one_sinsq, abs_of_nonneg (sq_nonneg _)]
    linarith [Real.sin_sq_le_one (2 * θ)]
  · rw [DthIter_two_sinsq, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg (sq_nonneg _)]
    have h3 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [Real.sin_sq_le_one (2 * θ)]

/-! ## §4 The closed form of `Uop (Θ F)/sin 2θ` on the open quadrant -/

/-- On the open quadrant, `Uop α (Θ α F) / sin 2θ = -(3/(4α))·L₁₂(F) + (1/4)·𝔽K(F)`, given the
index-raising identity `∂_z L₁₂(F) = -𝔽K(F)/z`. -/
theorem Uop_Theta_div {β : ℝ} (hβ : 0 < β) {F : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hder : HasDerivAt (fun z' => Work.Construction.L12 F z')
      (-(Work.Construction.FK F z) / z) z) :
    Work.Construction.Uop β (Work.Construction.Theta β F) z θ / Real.sin (2 * θ)
      = -(3 / (4 * β)) * Work.Construction.L12 F z
        + (1 / 4) * Work.Construction.FK F z := by
  have hs : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) <;> linarith
  have hT : Work.Construction.Theta β F z θ
      = ((1 / (4 * β)) * Real.sin (2 * θ)) * Work.Construction.L12 F z := by
    rw [Work.Construction.Theta, Work.Construction.s2_eq]
  have hDt : deriv (fun z' : ℝ => Work.Construction.Theta β F z' θ) z
      = ((1 / (4 * β)) * Real.sin (2 * θ)) * (-(Work.Construction.FK F z) / z) := by
    rw [show (fun z' : ℝ => Work.Construction.Theta β F z' θ)
        = fun z' => ((1 / (4 * β)) * Real.sin (2 * θ)) * Work.Construction.L12 F z' from by
      funext z'; rw [Work.Construction.Theta, Work.Construction.s2_eq]]
    rw [deriv_const_mul_field, hder.deriv]
  rw [Work.Construction.Uop]
  simp only [Work.Spaces.pz]
  rw [hT, hDt]
  have hb : β ≠ 0 := ne_of_gt hβ
  have hz' : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

/-! ## §5 The target -/

theorem explicit_pieces_coeff {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ j i : ℕ, j + i ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z θ| ≤ C ∧
      |Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ
          / Real.sin (2 * θ)) z θ| ≤ C := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hc4 := sliceC4_of_LimApprox (α := Work.FTS.Regularity.pExp α) (C₀ := C₀) (T := S)
    hβ hS hA
  have hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0 :=
    fun τ hτ => (hc4 τ hτ).of_le (by norm_num)
  obtain ⟨Cd, hCd1, hCd⟩ := Ftau_datum_of_LimApprox hα hα13 hA S hS hc2
  obtain ⟨K, hK0, hK⟩ := L12_FK_jets_of_datum
  have hM0 : 0 ≤ K * Cd ^ 4 := mul_nonneg hK0.le (by positivity)
  have hQ0 : 0 ≤ 3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4 := by positivity
  have hQM : 0 ≤ (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4) * (K * Cd ^ 4) :=
    mul_nonneg hQ0 hM0
  set Cbig : ℝ := 12 * (K * Cd ^ 4) + (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4)
    * (K * Cd ^ 4) + 1 with hCbig
  have hCpos : 0 < Cbig := by rw [hCbig]; linarith
  have hb12 : 12 * (K * Cd ^ 4) ≤ Cbig := by rw [hCbig]; linarith
  have hb1 : K * Cd ^ 4 ≤ Cbig := by rw [hCbig]; linarith
  have hb4 : 4 * (K * Cd ^ 4) ≤ Cbig := by rw [hCbig]; linarith
  have hbQ : (3 / (4 * Work.FTS.Regularity.pExp α) + 1 / 4) * (K * Cd ^ 4) ≤ Cbig := by
    rw [hCbig]; linarith
  refine ⟨Cbig, hCpos, ?_⟩
  intro τ hτ j i hji z θ hz hθ0 hθ1
  have hj2 : j ≤ 2 := by omega
  have hi2 : i ≤ 2 := by omega
  have hzmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hKg := hK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) τ) Cd hCd1 (hCd τ hτ)
  have hLb := (hKg z hz).1 j hj2 |>.1
  have hFb := (hKg z hz).1 j hj2 |>.2.1
  have hCb := (hKg z hz).1 j hj2 |>.2.2 (-(3 / (4 * Work.FTS.Regularity.pExp α))) (1 / 4)
  have hzle : (0 : ℝ) ≤ Cbig := le_of_lt hCpos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mixed_mul_rad_ang (fun z => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
      Work.Construction.c2m j i z θ, abs_mul]
    have h2 := DthIter_c2m_le i hi2 θ
    have hmm := mul_le_mul hLb h2 (abs_nonneg _) hM0
    linarith
  · rw [mixed_radial (fun z => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) j i z θ]
    split_ifs with hi0
    · linarith
    · simp only [abs_zero]
      exact hzle
  · have hf : (fun z θ : ℝ => (Real.sin θ) ^ 2 * Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
        = fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * (Real.sin θ) ^ 2 := by
      funext z' θ'; ring
    rw [hf, mixed_mul_rad_ang (fun z => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
      (fun θ => (Real.sin θ) ^ 2) j i z θ, abs_mul]
    have h2 := DthIter_sinsq_le i hi2 θ
    have hmm := mul_le_mul hFb h2 (abs_nonneg _) hM0
    linarith
  · have hEq : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ)) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => -(3 / (4 * Work.FTS.Regularity.pExp α))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      simp only [Function.uncurry]
      exact Uop_Theta_div hβ hp.1 hp.2.1 hp.2.2 ((hKg p.1 hp.1).2.2.1)
    rw [mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzmem,
      mixed_radial (fun z => -(3 / (4 * Work.FTS.Regularity.pExp α))
        * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z
        + (1 / 4) * Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) j i z θ]
    split_ifs with hi0
    · have habs : |-(3 / (4 * Work.FTS.Regularity.pExp α))|
          = 3 / (4 * Work.FTS.Regularity.pExp α) := by
        rw [abs_neg, abs_of_pos (by positivity : 0 < 3 / (4 * Work.FTS.Regularity.pExp α))]
      have habs2 : |(1 / 4 : ℝ)| = 1 / 4 := abs_of_nonneg (by norm_num)
      rw [habs, habs2] at hCb
      linarith
    · simp only [abs_zero]
      exact hzle

end Work.FTS_RegExport.RXT.Sys
