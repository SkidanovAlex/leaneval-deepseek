import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.slice_ibp_gen
import Submission.Work.Coercivity.EDz_eq_wip
import Submission.Work.Coercivity.Dz_near_zero_bound
import Submission.Work.Coercivity.box_deriv_ftc
import Submission.Work.Coercivity.slice_Z16

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The angular weight `sin(2θ)^{-η}` (so that `Weta z θ = w z ^ 2 * sig θ`). -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-Spaces.eta)

theorem Weta_eq_sig (z θ : ℝ) : Weta z θ = Spaces.w z ^ 2 * sig θ := rfl

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ sig θ :=
  Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- The product-measure form of a joint integrability hypothesis on the quadrant. -/
theorem integrableOn_prod_eq {g : ℝ → ℝ → ℝ}
    (h : IntegrableOn (Function.uncurry g) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => g p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  have hvol : volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.prod_restrict _ _).symm
  rw [IntegrableOn, hvol] at h
  exact h

/-! ### The pointwise `𝓛(D_z f)`-identity on a slice -/

/-- The pointwise identity behind the `Z₁`-part of the `D_z`-coercivity: for `z > 0` and
`θ ∈ Iθ`,
`𝓛(D_z f)·D_z f·w²  =  ½ (D_z f)² w²  +  ½ ∂_z( z (D_z f · w)² )`. -/
theorem L_Dz_mul_w_sq (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
      = (1 / 2) * ((Spaces.Dz f z θ) ^ 2 * Spaces.w z ^ 2)
        + (1 / 2) * deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z := by
  have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hf : HasDerivAt (fun z' => Spaces.Dz f z' θ) (Spaces.pz (Spaces.Dz f) z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice (Spaces.Dz f) (Spaces.SmoothNbhd.Dz hsm) hθ hzmem
  have hL := L_mul_w_deriv hz hf
  have hw : HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z := hasDerivAt_w (ne_of_gt hz)
  have hpz : Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ
      = Spaces.pz (Spaces.Dz f) z θ * Spaces.w z - Spaces.Dz f z θ * (2 * (1 + z) / z ^ 3) :=
    pz_mul_w (ne_of_gt hz) hf
  have hgw : HasDerivAt (fun z' => Spaces.Dz f z' θ * Spaces.w z')
      (Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ) z := by
    rw [hpz]
    exact (hf.mul hw).congr_deriv (by ring)
  have hg2 : HasDerivAt (fun z' => (Spaces.Dz f z' θ * Spaces.w z') ^ 2)
      (2 * (Spaces.Dz f z θ * Spaces.w z) *
        Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ) z := by
    have h := hgw.mul hgw
    have h' : HasDerivAt (fun z' => (Spaces.Dz f z' θ * Spaces.w z') ^ 2)
        (Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ
            * (Spaces.Dz f z θ * Spaces.w z)
          + (Spaces.Dz f z θ * Spaces.w z)
            * Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ) z :=
      h.congr_of_eventuallyEq (Eventually.of_forall (fun z' => by
        simp only [Pi.mul_apply]; ring))
    exact h'.congr_deriv (by ring)
  have hderiv : deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
      = (Spaces.Dz f z θ * Spaces.w z) ^ 2
        + z * (2 * (Spaces.Dz f z θ * Spaces.w z) *
            Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ) := by
    have hprod : HasDerivAt (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2)
        (1 * (Spaces.Dz f z θ * Spaces.w z) ^ 2
          + z * (2 * (Spaces.Dz f z θ * Spaces.w z) *
              Spaces.pz (fun z θ' => Spaces.Dz f z θ' * Spaces.w z) z θ)) z :=
      ((hasDerivAt_id z).mul hg2).congr_of_eventuallyEq
        (Eventually.of_forall (fun z' => by simp only [Pi.mul_apply, id_eq]))
    simpa using hprod.deriv
  rw [hderiv, show L (Spaces.Dz f) z θ * Spaces.Dz f z θ * Spaces.w z ^ 2
        = (L (Spaces.Dz f) z θ * Spaces.w z) * (Spaces.Dz f z θ * Spaces.w z) by ring, hL]
  ring



/-! ### The two limit passages `R → ∞` -/

/-- `Ioi 0` is the increasing union of the intervals `(0,n)`. -/
theorem iUnion_Ioo_eq_Ioi : (⋃ n : ℕ, Set.Ioo (0:ℝ) (n : ℝ)) = Set.Ioi (0:ℝ) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨n, h1, _⟩; exact h1
  · intro hx
    refine ⟨Nat.ceil x + 1, hx, ?_⟩
    have hle : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    push_cast
    linarith

/-- `Ioi 0` and `Iz` differ by the null set `{0}`. -/
theorem iz_ae_eq_Ioi : Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi (0:ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show Spaces.Iz \ Set.Ioi (0:ℝ) = {0} from by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Spaces.Iz, Set.mem_Ici, not_lt]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩]
    rw [Real.volume_singleton]
  · rw [show Set.Ioi (0:ℝ) \ Spaces.Iz = ∅ from by
      rw [Spaces.Iz, Set.sdiff_eq_empty]; exact Set.Ioi_subset_Ici_self]
    rw [MeasureTheory.measure_empty]

/-- The truncated integrals of `(D_z f)² · Weta` over `(0,n) × Iθ` converge to `EDz f`. -/
theorem tendsto_EDz_trunc (f : ℝ → ℝ → ℝ)
    (hint2 : IntegrableOn
      (Function.uncurry (fun z θ => (Spaces.Dz f z θ * Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Tendsto (fun n : ℕ => ∫ z in Set.Ioo 0 (n : ℝ),
        ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ) atTop (𝓝 (EDz f)) := by
  have hint2' : IntegrableOn
      (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2 * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine hint2.congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Weta]
    ring
  have hφ := integrableOn_prod_eq hint2'
  have hFon : IntegrableOn (fun z => ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      Spaces.Iz := hφ.integral_prod_left
  have hEDz : EDz f = ∫ z, (∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      ∂(volume.restrict Spaces.Iz) := by
    rw [EDz_eq_wip, wip]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => ?_))
    simp only [Weta]
    ring
  have hfi : IntegrableOn (fun z => ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      (⋃ n : ℕ, Set.Ioo 0 (n : ℝ)) := by
    rw [iUnion_Ioo_eq_Ioi]
    exact hFon.mono_set Set.Ioi_subset_Ici_self
  have hlim := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun z => ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
    (s := fun n : ℕ => Set.Ioo 0 (n : ℝ)) (fun n => measurableSet_Ioo)
    (fun i j hij => Set.Ioo_subset_Ioo_right (by exact_mod_cast hij)) hfi
  have hpt : (∫ z in (⋃ n : ℕ, Set.Ioo 0 (n : ℝ)),
      ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ) = EDz f := by
    rw [iUnion_Ioo_eq_Ioi, hEDz]
    exact (MeasureTheory.setIntegral_congr_set iz_ae_eq_Ioi).symm
  rwa [hpt] at hlim

/-- The truncated integrals of `Z16 f · D_z f · Weta` over `(0,n) × Iθ` converge to the
weighted inner product `wip Weta (Z16 f) (Dz f)`. -/
theorem tendsto_wip_Z16_trunc (f : ℝ → ℝ → ℝ)
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Tendsto (fun n : ℕ => ∫ z in Set.Ioo 0 (n : ℝ),
        ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ) atTop
      (𝓝 (wip Weta (Z16 f) (Spaces.Dz f))) := by
  have hφ := integrableOn_prod_eq hint
  have hFon : IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ) Spaces.Iz :=
    hφ.integral_prod_left
  have hwip : wip Weta (Z16 f) (Spaces.Dz f)
      = ∫ z, (∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
          ∂(volume.restrict Spaces.Iz) := rfl
  have hfi : IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      (⋃ n : ℕ, Set.Ioo 0 (n : ℝ)) := by
    rw [iUnion_Ioo_eq_Ioi]
    exact hFon.mono_set Set.Ioi_subset_Ici_self
  have hlim := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun z => ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
    (s := fun n : ℕ => Set.Ioo 0 (n : ℝ)) (fun n => measurableSet_Ioo)
    (fun i j hij => Set.Ioo_subset_Ioo_right (by exact_mod_cast hij)) hfi
  have hpt : (∫ z in (⋃ n : ℕ, Set.Ioo 0 (n : ℝ)),
      ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ) = wip Weta (Z16 f) (Spaces.Dz f) := by
    rw [iUnion_Ioo_eq_Ioi, hwip]
    exact (MeasureTheory.setIntegral_congr_set iz_ae_eq_Ioi).symm
  rwa [hpt] at hlim


/-- `∫ x, c * F x = c * ∫ x, F x` in the form needed below (`integral_const_mul` is
stated with `•`). -/
theorem integral_const_mul_real {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℝ)
    (F : α → ℝ) : (∫ x, c * F x ∂μ) = c * ∫ x, F x ∂μ := by
  simpa only [smul_eq_mul] using MeasureTheory.integral_const_mul c F

/-! ### The truncated box inequality -/

/-- On the truncated quadrant `(0,R) × Iθ`, `Z16 f · D_z f · Weta` dominates `47/100` of
`(D_z f)² · Weta`.  This is the coercive estimate with the (favourable) `z`-boundary term
retained. -/
theorem box_bound (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint2 : IntegrableOn
      (Function.uncurry (fun z θ => (Spaces.Dz f z θ * Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Spaces.eta))) (Spaces.Iz ×ˢ Spaces.Iθ))
    {R : ℝ} (hR : 0 < R) :
    (47 / 100) * (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      ≤ ∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ := by
  obtain ⟨C, δ, hCpos, hδ, hbnd⟩ := Dz_near_zero_bound f hsm hbd
  let Bf : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, (Spaces.Dz f z θ) ^ 2 * Weta z θ
  let Cf : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ,
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z * sig θ
  let Df : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ,
    Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ
  let gf : ℝ → ℝ := fun z => 3 * (1 - Spaces.eta) / (1 + z)
  let P : Measure (ℝ × ℝ) := (volume.restrict (Set.Ioo 0 R)).prod (volume.restrict Spaces.Iθ)
  -- ## The slice identity
  have hslice : ∀ z, 0 < z → (∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      = (1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z := by
    intro z hz
    have h := slice_Z16 f hsm z hz
    dsimp only [Bf, Cf, Df, gf, sig]
    exact h
  -- ## Joint integrability of `(D_z f)² Weta` on the box
  have hΦ : Integrable (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) P := by
    have hsub : Set.Ioo 0 R ×ˢ Spaces.Iθ ⊆ Spaces.Iz ×ˢ Spaces.Iθ := by
      intro p hp
      exact ⟨Set.mem_Ici.mpr (le_of_lt hp.1.1), hp.2⟩
    have h1 : IntegrableOn
        (Function.uncurry (fun z θ => (Spaces.Dz f z θ) ^ 2 * Weta z θ))
        (Set.Ioo 0 R ×ˢ Spaces.Iθ) := by
      refine (hint2.mono_set hsub).congr ?_
      filter_upwards with p
      obtain ⟨z, θ⟩ := p
      simp only [Function.uncurry_apply_pair, Weta]
      ring
    have hvol : volume.restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) = P := by
      dsimp only [P]
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [IntegrableOn, hvol] at h1
    exact h1
  have hB : IntegrableOn Bf (Set.Ioo 0 R) := hΦ.integral_prod_left
  have hzp : ∀ᵐ p ∂P, p.1 ∈ Set.Ioo 0 R := by
    dsimp only [P]
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    exact Eventually.of_forall (fun θ => hz)
  have hθp : ∀ᵐ p ∂P, p.2 ∈ Set.Icc (0:ℝ) (Real.pi / 2) := by
    dsimp only [P]
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)]
    filter_upwards [] with z
    exact MeasureTheory.ae_restrict_mem measurableSet_Icc
  -- ## Joint integrability of the `gf · cos(2θ) · (D_z f)² Weta` integrand
  have hΨ : Integrable (fun p : ℝ × ℝ =>
      gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)) P := by
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (3 * (1 - Spaces.eta)) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖) P :=
      hΦ.norm.const_mul _
    refine hmaj.mono' ?_ ?_
    · have h1 : Measurable (fun p : ℝ × ℝ => gf p.1 * Real.cos (2 * p.2)) := by
        dsimp only [gf]; fun_prop
      refine (h1.aestronglyMeasurable.mul hΦ.aestronglyMeasurable).congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply]
      ring
    · filter_upwards [hzp] with p hp
      have hp1 : 0 < p.1 := hp.1
      have hgf0 : 0 ≤ gf p.1 := by
        dsimp only [gf]
        exact div_nonneg (by norm_num [Spaces.eta]) (by linarith)
      have hgfle : gf p.1 ≤ 3 * (1 - Spaces.eta) := by
        dsimp only [gf]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.1)]
        have h3 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) := by norm_num [Spaces.eta]
        have h4 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) * p.1 := mul_nonneg h3 (le_of_lt hp1)
        linarith
      calc ‖gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)‖
          = gf p.1 * |Real.cos (2 * p.2)| * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by
            simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgf0]
            ring
        _ ≤ 3 * (1 - Spaces.eta) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by
            have h2 : gf p.1 * |Real.cos (2 * p.2)| ≤ 3 * (1 - Spaces.eta) * 1 :=
              mul_le_mul hgfle (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num [Spaces.eta])
            calc gf p.1 * |Real.cos (2 * p.2)| * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖
                ≤ (3 * (1 - Spaces.eta) * 1) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ :=
                  mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
              _ = 3 * (1 - Spaces.eta) * ‖(Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2‖ := by ring
  have hgD : IntegrableOn (fun z => gf z * Df z) (Set.Ioo 0 R) := by
    have h := hΨ.integral_prod_left
    refine h.congr (Eventually.of_forall (fun z => ?_))
    show (∫ θ, gf z * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ)
        ∂(volume.restrict Spaces.Iθ)) = gf z * Df z
    rw [integral_const_mul_real]
  -- ## Joint integrability of `Z16 f · D_z f · Weta` on the box
  have hG : IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ)
      (Set.Ioo 0 R) := by
    have hsub : Set.Ioo 0 R ×ˢ Spaces.Iθ ⊆ Spaces.Iz ×ˢ Spaces.Iθ := by
      intro p hp
      exact ⟨Set.mem_Ici.mpr (le_of_lt hp.1.1), hp.2⟩
    have h1 : IntegrableOn
        (Function.uncurry (fun z θ => Z16 f z θ * Spaces.Dz f z θ * Weta z θ))
        (Set.Ioo 0 R ×ˢ Spaces.Iθ) := hint.mono_set hsub
    have hvol : volume.restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) = P := by
      dsimp only [P]
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [IntegrableOn, hvol] at h1
    exact h1.integral_prod_left
  have hG' : IntegrableOn (fun z => (1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z)
      (Set.Ioo 0 R) := by
    refine hG.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    exact hslice z hz.1
  have hC : IntegrableOn Cf (Set.Ioo 0 R) := by
    have heq : (fun z => 2 * ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) - Bf z
        - 2 * (gf z * Df z)) = Cf := by
      funext z; ring
    rw [← heq]
    exact ((hG'.const_mul 2).sub hB).sub (hgD.const_mul 2)
  -- ## The split into the three pieces
  have hsplit : (∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z))
      = (1 / 2) * (∫ z in Set.Ioo 0 R, Bf z) + (1 / 2) * (∫ z in Set.Ioo 0 R, Cf z)
        + (∫ z in Set.Ioo 0 R, gf z * Df z) := by
    have hcongr : (∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z))
        = ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + ((1 / 2) * Cf z + gf z * Df z)) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
      ring
    have hfg : Integrable (fun z => (1 / 2) * Cf z + gf z * Df z)
        (volume.restrict (Set.Ioo 0 R)) := (hC.const_mul (1 / 2)).add hgD
    have hbfg : Integrable (fun z => (1 / 2) * Bf z + ((1 / 2) * Cf z + gf z * Df z))
        (volume.restrict (Set.Ioo 0 R)) := (hB.const_mul (1 / 2)).add hfg
    rw [hcongr, MeasureTheory.integral_add (hB.const_mul (1 / 2)) hfg,
      MeasureTheory.integral_add (hC.const_mul (1 / 2)) hgD,
      integral_const_mul_real, integral_const_mul_real]
    ring
  -- ## The `C`-piece is nonnegative
  have hCnn : 0 ≤ ∫ z in Set.Ioo 0 R, Cf z := by
    have hbox := box_deriv_ftc f hsm hbd
      ⟨C, δ, hCpos, hδ, fun z hz θ hθ => (hbnd z hz θ hθ).2.2⟩ hR
    dsimp only [Cf, sig] at hbox ⊢
    rw [hbox]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (mul_nonneg (le_of_lt hR) (sq_nonneg _)) (sig_nonneg hθ)
  -- ## The `g·D`-piece dominates `-(3(1-η))` times the `B`-piece
  have hgDlb : -(3 * (1 - Spaces.eta)) * (∫ z in Set.Ioo 0 R, Bf z)
      ≤ ∫ z in Set.Ioo 0 R, gf z * Df z := by
    have hBint : (∫ z in Set.Ioo 0 R, Bf z)
        = ∫ p, (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 ∂P := by
      rw [MeasureTheory.integral_prod
        (fun p : ℝ × ℝ => (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) hΦ]
    have hDint : (∫ z in Set.Ioo 0 R, gf z * Df z)
        = ∫ p, gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P := by
      rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
        gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)) hΨ]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun z => ?_))
      show gf z * Df z = ∫ θ in Spaces.Iθ,
        gf z * (Real.cos (2 * θ) * (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      rw [integral_const_mul_real]
    rw [hBint, hDint]
    have hmono : (∫ p, -(3 * (1 - Spaces.eta)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P)
        ≤ ∫ p, gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) ∂P := by
      refine MeasureTheory.integral_mono_ae (hΦ.const_mul _) hΨ ?_
      filter_upwards [hzp, hθp] with p hp hθ
      have hp1 : 0 < p.1 := hp.1
      have hgf0 : 0 ≤ gf p.1 := by
        dsimp only [gf]
        exact div_nonneg (by norm_num [Spaces.eta]) (by linarith)
      have hgfle : gf p.1 ≤ 3 * (1 - Spaces.eta) := by
        dsimp only [gf]
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + p.1)]
        have h3 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) := by norm_num [Spaces.eta]
        have h4 : (0:ℝ) ≤ 3 * (1 - Spaces.eta) * p.1 := mul_nonneg h3 (le_of_lt hp1)
        linarith
      have hφnn : 0 ≤ (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2 :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sig_nonneg hθ))
      have hcos : -(3 * (1 - Spaces.eta)) ≤ gf p.1 * Real.cos (2 * p.2) := by
        have h1 : gf p.1 * (-1) ≤ gf p.1 * Real.cos (2 * p.2) :=
          mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (2 * p.2)) hgf0
        have h2 : -(3 * (1 - Spaces.eta)) ≤ gf p.1 * (-1) := by
          rw [mul_neg, mul_one]; linarith [hgfle]
        linarith [h1, h2]
      calc -(3 * (1 - Spaces.eta)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2)
          ≤ (gf p.1 * Real.cos (2 * p.2)) * ((Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) :=
            mul_le_mul_of_nonneg_right hcos hφnn
        _ = gf p.1 * (Real.cos (2 * p.2) * (Spaces.Dz f p.1 p.2) ^ 2 * Weta p.1 p.2) := by ring
    rw [integral_const_mul_real] at hmono
    linarith [hmono]
  -- ## Assembly
  have heta : (3:ℝ) * (1 - Spaces.eta) = 3 / 100 := by norm_num [Spaces.eta]
  have hmain : (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z)
      ≤ ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) := by
    rw [hsplit]
    have hXeq : (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z)
        = (1 / 2) * (∫ z in Set.Ioo 0 R, Bf z)
          - (3 * (1 - Spaces.eta)) * (∫ z in Set.Ioo 0 R, Bf z) := by
      rw [heta]; ring
    rw [hXeq]
    linarith [hCnn, hgDlb]
  calc (47 / 100) * (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ,
        (Spaces.Dz f z θ) ^ 2 * Weta z θ)
      = (47 / 100) * (∫ z in Set.Ioo 0 R, Bf z) := rfl
    _ ≤ ∫ z in Set.Ioo 0 R, ((1 / 2) * Bf z + (1 / 2) * Cf z + gf z * Df z) := hmain
    _ = ∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, Z16 f z θ * Spaces.Dz f z θ * Weta z θ := by
        refine (MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun z hz => ?_)).symm
        exact hslice z hz.1

end Work.Coercivity
