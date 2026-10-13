import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The assembly of the row

The whole estimate is carried by the identity

`∫_z∫_θ ρ·(D_z^bD_θ^a u)·(D_z^bD_θ^a f) = ∑_{k≤b} C(b,k)·∫_z (D_z^kL₁₂f)·(∫_θ ρ·(D_z^{b-k}D_θ^{a+1}f)·(D_z^bD_θ^a f))`

for `u = L₁₂(f)·D_θf` (Leibniz for the radial coefficient `L₁₂ f`), the two bounds

* `k = 0`: the signed `θ`-integral is the `θ`-integration by parts of the extra angular
  derivative (`h0le`);
* `k ≥ 1`: the `θ`-slot product is dominated by `HkIntegrand α 6 f`, and the coefficient
  `D_z^kL₁₂ f` is bounded by `C₄|f|_{ℋ⁴}` (`k ≤ 4`) resp. `C₆|f|_{ℋ⁶}` (`k ≥ 5`), the two
  remaining `k ≥ 5` slots being priced by Cauchy–Schwarz (`hcs`). -/
theorem T4bRowSlot_core {Ccs C0 C4 C6 : ℝ} (hCcspos : 0 < Ccs) (hC0pos : 0 < C0)
    (hC4pos : 0 < C4) (hC6pos : 0 < C6)
    (hsup4 : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ C4 * Work.Spaces.HkNorm α 4 g)
    (hsup6 : ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 7 g → Work.Construction.L12 g 0 = 0 →
      ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z|
          ≤ C6 * Work.Spaces.HkNorm α 6 g)
    (hlr : ∀ (X : ℝ → ℝ) (g : ℝ → ℝ → ℝ), ContDiffOn ℝ 6 X (Set.Ioi 0) →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ (b a : ℕ), b ≤ 6 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => X z * g z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k X z * Work.Spaces.mixed (b - k) a g z θ))
    (hcs : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b k : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.TransportS.IsLeafW α a ρ → 5 ≤ k → k ≤ b → a + b ≤ 6 →
      (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
          ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ * Work.Spaces.mixed b a f z θ|)
        ≤ Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
    (h0le : ∀ α ∈ Set.Ioc 0 1, ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, Work.Construction.L12 f z *
          (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b (a + 1) f z θ
            * Work.Spaces.mixed b a f z θ)|
        ≤ C0 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  refine ⟨(C0 + 384 * (C4 + C6 * Ccs)) + 1, by positivity, ?_⟩
  intro α hα f a b ρ hso hm6 hm7 _hvanish _haxis hl12 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hb6 : b ≤ 6 := by omega
  -- ## the uniform bounds on the `z`-jets of the radial coefficient `L₁₂(f)`
  have hs4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hsup4 α f hα0 hα1 hso hm6 hl12 k hk z hz
  have hs6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun k hk z hz => hsup6 α f hα0 hα1 hso hm6 hm7 hl12 k hk z hz
  -- ## the Leibniz identity on the open quadrant
  have hleib : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * Work.Spaces.mixed (b - k) (a + 1) f z θ) := by
    intro z θ hz h1
    have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
      have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
        (by norm_num : 2 ≤ 7)).1
      rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
      exact h
    rw [hlr (fun z => Work.Construction.L12 f z) (Work.Spaces.Dth f) hXsm hso.Dth b a
      (by omega) z θ hz h1.1 h1.2]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Work.FTS.StrongPersist.H6Pair6Aux.mixed_Dth_eq]
  -- ## the `θ`-slice identity
  have hPhi_eq : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
          (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    intro z hz
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ρ z θ * Work.Spaces.mixed b a
            (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
            * Work.Spaces.mixed b a f z θ
          = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
              * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                  * (ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
      refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => ?_)
      rw [hleib z θ hz ⟨h1, h2⟩]
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [MeasureTheory.integral_congr_ae hpt]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [MeasureTheory.integral_const_mul]
    · intro k hk
      exact ((Psi_slice_int (k := k) hα0 hso hleaf hm7 hab hz).const_mul _).const_mul _
  -- ## the `z`-integral identity
  have hInt : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
          * (∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    rw [MeasureTheory.integral_congr_ae (ae_Iz_of_pos hPhi_eq)]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [MeasureTheory.integral_const_mul]
    · intro k hk
      have hkb : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hK : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
        split_ifs
        · exact mul_nonneg (le_of_lt hC4pos) (Work.Spaces.HkNorm_nonneg α 4 f)
        · exact mul_nonneg (le_of_lt hC6pos) (Work.Spaces.HkNorm_nonneg α 6 f)
      exact (DzdX_Psi_int (k := k) hα0 hso hleaf hm7 hab (by omega) hK
        (fun z hz => by
          split_ifs with h4
          · exact hs4 k h4 z hz
          · exact hs6 k (by omega) z hz)).const_mul _

  -- ## the `k = 0` term (the `θ`-integration by parts of the extra angular derivative)
  have hk0 : |(b.choose 0 : ℝ) * (∫ z in Work.Spaces.Iz,
        Work.Elliptic.DzdIter 0 (fun z => Work.Construction.L12 f z) z
          * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - 0) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ))|
      ≤ C0 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
    have h := h0le α hα f a b ρ hso hm6 hm7 hl12 hab hleaf
    simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, mul_assoc,
      Work.Elliptic.DzdIter_zero] using h
  -- ## the tail terms
  have hterm : ∀ k ∈ Finset.range b,
      |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|
        ≤ 64 * ((C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) := by
    intro k hk
    have hkb : k + 1 ≤ b := by have := Finset.mem_range.mp hk; omega
    have hk6 : k + 1 ≤ 6 := by omega
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hc64 : (b.choose (k + 1) : ℝ) ≤ 64 := by
      have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hb6
      have h3 : b.choose (k + 1) ≤ 2 ^ b := Nat.choose_le_two_pow b (k + 1)
      have h4 : b.choose (k + 1) ≤ 64 := by
        have h5 := le_trans h3 h2
        norm_num at h5
        exact h5
      exact_mod_cast h4
    have hXnn : 0 ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f :=
      mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f)
    have hinner_abs : (∫ z in Work.Spaces.Iz,
          ‖Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)‖)
        = ∫ z in Work.Spaces.Iz,
            |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
            * |∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ| := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      simp only [Real.norm_eq_abs, abs_mul]
    have hPsiint : IntegrableOn (fun z => |∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
          * Work.Spaces.mixed b a f z θ|) Work.Spaces.Iz :=
      (Psi_intz (k := k + 1) hα0 hso hleaf hm7 hab).abs
    have hinner : |∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ)|
        ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
      by_cases h4 : k + 1 ≤ 4
      · have hstep : (∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|)
            ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (hPsiint.const_mul _) ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact mul_le_mul_of_nonneg_right (hs4 (k + 1) h4 z hz) (abs_nonneg _)
        have hPsi_le : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ|) ≤ Work.Spaces.HkSq α 6 f := by
          rw [Work.Spaces.HkSq]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hm6.2 ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact Psi_le_int6 (k := k + 1) hα0 hso hleaf hm6 hab hk1 hkb hz
        calc |∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)|
            ≤ ∫ z in Work.Spaces.Iz, ‖Work.Elliptic.DzdIter (k + 1)
                (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)‖ :=
              (by rw [← Real.norm_eq_abs]; exact MeasureTheory.norm_integral_le_integral_norm _)
          _ = ∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ| := hinner_abs
          _ ≤ (C4 * Work.Spaces.HkNorm α 4 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := hstep
          _ ≤ (C4 * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkSq α 6 f :=
              mul_le_mul_of_nonneg_left hPsi_le
                (mul_nonneg (le_of_lt hC4pos) (Work.Spaces.HkNorm_nonneg α 4 f))
          _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              have h1 : C4 ≤ C4 + C6 * Ccs := by
                nlinarith [le_of_lt hC6pos, le_of_lt hCcspos]
              calc C4 * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
                  = C4 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by ring
                _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :=
                    mul_le_mul_of_nonneg_right h1
                      (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f))
      · have h5 : 5 ≤ k + 1 := by omega
        have hstep : (∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|)
            ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (hPsiint.const_mul _) ?_
          filter_upwards [ae_Iz_of_pos (fun z hz => hz)] with z hz
          exact mul_le_mul_of_nonneg_right (hs6 (k + 1) hk6 z hz) (abs_nonneg _)
        have hPsi_le : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
              * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ|)
            ≤ Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f :=
          hcs α hα f a b (k + 1) ρ hso hm6 hleaf h5 hkb hab
        have hsq6 : Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f
            = Work.Spaces.HkSq α 6 f := by
          simp only [Work.Spaces.HkNorm]
          rw [← sq, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
        calc |∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)|
            ≤ ∫ z in Work.Spaces.Iz, ‖Work.Elliptic.DzdIter (k + 1)
                (fun z => Work.Construction.L12 f z) z
                * (∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)‖ :=
              (by rw [← Real.norm_eq_abs]; exact MeasureTheory.norm_integral_le_integral_norm _)
          _ = ∫ z in Work.Spaces.Iz,
              |Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z|
              * |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ| := hinner_abs
          _ ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|) := hstep
          _ ≤ (C6 * Work.Spaces.HkNorm α 6 f)
              * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f) :=
              mul_le_mul_of_nonneg_left hPsi_le
                (mul_nonneg (le_of_lt hC6pos) (Work.Spaces.HkNorm_nonneg α 6 f))
          _ = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              rw [show C6 * Work.Spaces.HkNorm α 6 f
                    * (Ccs * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)
                  = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f
                      * (Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)) from by ring,
                hsq6]
          _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
              have h1 : C6 * Ccs ≤ C4 + C6 * Ccs := by linarith [le_of_lt hC4pos]
              calc (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
                  = (C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := rfl
                _ ≤ (C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) :=
                    mul_le_mul_of_nonneg_right h1
                      (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f))
    calc |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|
        = (b.choose (k + 1) : ℝ) * |∫ z in Work.Spaces.Iz,
            Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
              * (∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                  * Work.Spaces.mixed b a f z θ)| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ 64 * ((C4 + C6 * Ccs) * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul hc64 hinner (abs_nonneg _) (by norm_num)
  -- ## the whole pairing
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
        (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ|
      ≤ (C0 + 384 * (C4 + C6 * Ccs))
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) := by
    rw [hInt]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_range_succ']
    have htail : (∑ k ∈ Finset.range b,
        |(b.choose (k + 1) : ℝ) * (∫ z in Work.Spaces.Iz,
          Work.Elliptic.DzdIter (k + 1) (fun z => Work.Construction.L12 f z) z
            * (∫ θ in Work.Spaces.Iθ, ρ z θ
                * Work.Spaces.mixed (b - (k + 1)) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|)
        ≤ 6 * (64 * ((C4 + C6 * Ccs)
            * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f))) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hb6' : (b : ℝ) ≤ 6 := by exact_mod_cast hb6
      have hnn : 0 ≤ 64 * ((C4 + C6 * Ccs)
          * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)) :=
        mul_nonneg (by norm_num) (mul_nonneg
          (add_nonneg (le_of_lt hC4pos) (mul_nonneg (le_of_lt hC6pos) (le_of_lt hCcspos)))
          (mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkSq_nonneg α 6 f)))
      exact mul_le_mul_of_nonneg_right hb6' hnn
    refine le_trans (add_le_add htail hk0) ?_
    · rw [show 6 * (64 * ((C4 + C6 * Ccs)
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)))
            + C0 * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
          = (C0 + 384 * (C4 + C6 * Ccs))
              * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f) from by ring]
  rw [Work.FTS.TransportS.slotPairing]
  refine le_trans hmain ?_
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have hpos : 0 < α ^ (3 : ℝ) := Real.rpow_pos_of_pos hα0 3
    rw [Real.rpow_neg hα0.le]
    exact (one_le_inv₀ hpos).mpr (Real.rpow_le_one hα0.le hα1 (by norm_num))
  have key : Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
      ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1 : Work.Spaces.HkNorm α 4 f ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by
      have h2 : Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := by linarith
      calc Work.Spaces.HkNorm α 4 f ≤ 1 + Work.Spaces.HkNorm α 4 f := h2
        _ = (1 + Work.Spaces.HkNorm α 4 f) ^ 1 := by ring
        _ ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : Work.Spaces.HkSq α 6 f ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
    calc Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f
        ≤ (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul h1 h4 hSnn (by positivity)
      _ ≤ (α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          calc (1 + Work.Spaces.HkNorm α 4 f) ^ 4
              = 1 * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 := by ring
            _ ≤ α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 :=
                mul_le_mul_of_nonneg_right hα3 (by positivity)
      _ = α ^ (-(3 : ℝ)) * (1 + Work.Spaces.HkNorm α 4 f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
  calc (C0 + 384 * (C4 + C6 * Ccs))
        * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f)
      ≤ (C0 + 384 * (C4 + C6 * Ccs)) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ ((C0 + 384 * (C4 + C6 * Ccs)) + 1) * (α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith
    _ = ((C0 + 384 * (C4 + C6 * Ccs)) + 1) * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkNorm α 4 f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux
