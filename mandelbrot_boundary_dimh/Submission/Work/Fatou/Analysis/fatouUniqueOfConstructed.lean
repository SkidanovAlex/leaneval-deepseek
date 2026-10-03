import Mathlib
import Submission.Work.Fatou.Constructed
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.fatouTransfer
import Submission.Work.FatouCH.psiOfEntire
import Submission.Work.FatouCH.uniqueSetup
import Submission.Work.Fatou.Analysis.fatouDerivEstimate
import Submission.Work.Fatou.Analysis.UniqueDefs
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.Qreg.fatouFundamental
import Submission.Work.Fatou.Analysis.exists_fundStrip_rep
import Submission.Work.Fatou.Analysis.exists_ball_subset_Qreg
import Submission.Work.Fatou.Analysis.exists_norm_le_on_fundStrip

namespace Work.Fatou.Analysis

open MandelDim Set Metric
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F Φ₀ Φ ψ : ℂ → ℂ}

/-- **Forward transfer, natural shifts.**  If `Φ₀` satisfies the orbit relation A.2.1(i) and
`Φ₀ z' = Φ₀ z + n` (`n : ℕ`), then `z' = F^[n] z` with the whole orbit piece in the region, and
iterating the Abel equation of any Fatou coordinate `Φ` along that piece gives
`Φ z' = Φ z + n`. -/
theorem transfer_nat_of_orbitRel (horb : OrbitRel b₁ b₂ F Φ₀)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂))
    {z z' : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hz' : z' ∈ MandelDim.Qreg b₁ b₂) (n : ℕ)
    (h : Φ₀ z' = Φ₀ z + (n : ℂ)) : Φ z' = Φ z + (n : ℂ) := by
  obtain ⟨horbit, hiter⟩ := horb z hz z' hz' n h
  have h2 := Work.FatouCH.iterate_abel hΦ horbit
  rwa [hiter] at h2

/-- **Forward transfer, integer shifts.**  The `ℤ`-shift relation of the constructed coordinate
`Φ₀` transfers to an arbitrary Fatou coordinate `Φ` on the same region (the orbit relation for `Φ`
itself is *not* needed). -/
theorem transfer_of_orbitRel (horb : OrbitRel b₁ b₂ F Φ₀)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) :
    ∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂, ∀ k : ℤ,
      Φ₀ z' = Φ₀ z + (k : ℂ) → Φ z' = Φ z + (k : ℂ) := by
  intro z hz z' hz' k h
  by_cases hk : 0 ≤ k
  · have hkn : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast (Int.toNat_of_nonneg hk)
    have h' : Φ₀ z' = Φ₀ z + ((k.toNat : ℕ) : ℂ) := by rw [hkn]; exact h
    have h2 := transfer_nat_of_orbitRel horb hΦ hz hz' k.toNat h'
    rwa [hkn] at h2
  · have hkpos : (0 : ℤ) < -k := by omega
    have hmn : (((-k).toNat : ℕ) : ℂ) = ((-k : ℤ) : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
    have h2 : Φ₀ z = Φ₀ z' + (((-k : ℤ)) : ℂ) := by
      rw [h, Int.cast_neg]; ring
    have h' : Φ₀ z = Φ₀ z' + (((-k).toNat : ℕ) : ℂ) := by rw [hmn]; exact h2
    have h3 := transfer_nat_of_orbitRel horb hΦ hz' hz (-k).toNat h'
    rw [hmn] at h3
    rw [h3, Int.cast_neg]
    ring

/-- **The chain rule for `ψ`.**  If `ψ` is holomorphic and `ψ (Φ₀ z) = Φ z` for all `z` in the
open region, then `deriv ψ (Φ₀ z) = deriv Φ z / deriv Φ₀ z`. -/
theorem deriv_psi_eq (hψΦ : ∀ z ∈ MandelDim.Qreg b₁ b₂, ψ (Φ₀ z) = Φ z)
    (hdψ : Differentiable ℂ ψ) (hΦ₀ : MandelDim.IsFatouCoordOn F Φ₀ (MandelDim.Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) :
    deriv ψ (Φ₀ z) = deriv Φ z / deriv Φ₀ z := by
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := Work.FatouCH.qreg_isOpen b₁ b₂
  have heq : (fun z : ℂ => ψ (Φ₀ z)) =ᶠ[𝓝 z] Φ := by
    filter_upwards [hQ.mem_nhds hz] with z' hz'
    exact hψΦ z' hz'
  have hcomp : deriv (fun z : ℂ => ψ (Φ₀ z)) z = deriv ψ (Φ₀ z) * deriv Φ₀ z :=
    deriv_comp z (hdψ.differentiableAt) (hΦ₀.1.differentiableAt (hQ.mem_nhds hz))
  have hderivΦ : deriv Φ z = deriv ψ (Φ₀ z) * deriv Φ₀ z := by
    rw [← hcomp, heq.deriv_eq]
  have hne : deriv Φ₀ z ≠ 0 := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hQ z hz
    exact Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr
      (hΦ₀.1.analyticAt (hQ.mem_nhds hz)) (hΦ₀.2.1.mono hsub)
  rw [hderivΦ, mul_div_cancel_right₀ (deriv ψ (Φ₀ z)) hne]

/-- **Shishikura A.2.4(i) at a single point.**  With `v = F - id` and a ball of radius `R ≥ R₁`
inside the region, `deriv Φ` is within `C₂/R` of `1/v`. -/
theorem deriv_estimate_at {R₁ C₁ C₂ : ℝ}
    (hest : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DerivEst R₁ C₁ C₂ Φ v z₀ R)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂))
    {s : ℂ} {R : ℝ} (hR : R₁ ≤ R) (hball : Metric.ball s R ⊆ MandelDim.Qreg b₁ b₂) :
    ‖deriv Φ s - 1 / (F s - s)‖ ≤ C₂ / R := by
  have h := hest Φ (fun z => F z - z) s R
  refine h hR (hΦ.1.mono hball) (hΦ.2.1.mono hball)
    ((hNT.1.mono hball).sub differentiableOn_id) ?_ ?_
  · intro z hz
    have hz' := (hNT.2 z (hball hz)).1
    have he : (F z - z) - 1 = F z - (z + 1) := by ring
    rw [he]
    linarith
  · intro z hz hzF
    have hF : F z ∈ Metric.ball s R := by
      rwa [show z + (fun z => F z - z) z = F z from by ring] at hzF
    have habel := hΦ.2.2 z (hball hz) (hball hF)
    rwa [show z + (fun z => F z - z) z = F z from by ring]

/-- A continuous `1`-periodic function with an explicit modulus bound outside a horizontal band is
bounded.  (Used to upgrade "`deriv ψ → 1` at both ends" to "`deriv ψ` is bounded".) -/
theorem isBounded_range_of_periodic (g : ℂ → ℂ) (hg : Function.Periodic g (1 : ℂ))
    (hgcont : Continuous g) {Y C : ℝ} (hY : ∀ w : ℂ, Y ≤ |w.im| → ‖g w‖ ≤ C) :
    Bornology.IsBounded (Set.range g) := by
  have hKclosed : IsClosed {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ Y} := by
    have h1 : IsClosed {w : ℂ | (0 : ℝ) ≤ w.re} :=
      isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {w : ℂ | w.re ≤ (1 : ℝ)} :=
      isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {w : ℂ | |w.im| ≤ Y} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have hset : {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ Y}
        = {w : ℂ | (0 : ℝ) ≤ w.re} ∩ {w : ℂ | w.re ≤ (1 : ℝ)} ∩ {w : ℂ | |w.im| ≤ Y} := by
      ext w; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [hset]
    exact (h1.inter h2).inter h3
  have hK : IsCompact {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ Y} :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) (2 * (|Y| + 1))) hKclosed
      (fun w hw => by
        rw [Metric.mem_closedBall, dist_zero_right]
        have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        have h2 : |w.re| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1], hw.2.1⟩
        have h3 : |w.im| ≤ |Y| := le_trans hw.2.2 (le_abs_self Y)
        have h4 : (0 : ℝ) ≤ |Y| := abs_nonneg Y
        linarith)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgcont.continuousOn
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max C (max B 0), fun y hy => ?_⟩
  obtain ⟨w, rfl⟩ := hy
  by_cases hw : Y ≤ |w.im|
  · exact le_trans (hY w hw) (le_max_left _ _)
  · have hwlt : |w.im| < Y := lt_of_not_ge hw
    set k : ℤ := ⌊w.re⌋ with hk
    have hwk : w - (k : ℂ) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ |w.im| ≤ Y} := by
      refine ⟨?_, ?_, ?_⟩
      · have h1 : (w - (k : ℂ)).re = w.re - (k : ℝ) := by simp
        have := Int.floor_le w.re
        linarith
      · have h1 : (w - (k : ℂ)).re = w.re - (k : ℝ) := by simp
        have := Int.lt_floor_add_one w.re
        linarith
      · have : (w - (k : ℂ)).im = w.im := by simp
        rw [this]; exact le_of_lt hwlt
    have hshift : g w = g (w - (k : ℂ)) := by
      have h := (hg.int_mul k) (w - (k : ℂ))
      have hw' : w - (k : ℂ) + ((k : ℂ) * 1) = w := by ring
      rwa [hw'] at h
    rw [hshift]
    exact le_trans (hB _ hwk) (le_trans (le_max_left _ _) (le_max_right _ _))

/-- **`Re` of the fundamental strip is bounded above.**  Via `devH` (which is within `1/32` of
the translation `ζ ↦ x₀ + ζ` on the unit strip), a point of `fundStrip F (Qreg b₁ b₂) xOf` has
real part `< xOf + 1 + 1/32`. -/
theorem fundStrip_re_upper {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}
    (hadm : MandelDim.QAdm b₁ b₂) (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    {s : ℂ} (hs : s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂)) :
    s.re < Work.Fatou.xOf b₁ b₂ + 1 + 1 / 32 := by
  obtain ⟨-, honto, -⟩ :=
    Work.Fatou.Surface.devH_fundStrip (b₁ := b₁) (b₂ := b₂) (F := F) hadm hNT
  obtain ⟨ζ, hζ0, hζ1, hζeq⟩ := honto s hs
  rw [← hζeq]
  rcases le_or_gt ζ.re (1 / 8) with h | h
  · rw [Work.Fatou.devH_of_le_one_eighth h]
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  · have hsub := Work.Fatou.devH_sub_le hadm hNT h.le (by linarith)
    have hre := Work.Fatou.abs_re_sub_le hsub
    have h1 : (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F ζ).re
        ≤ Work.Fatou.xOf b₁ b₂ + ζ.re + 1 / 32 := by
      have h2 := (abs_le.mp hre).2
      simp only [Complex.add_re, Complex.ofReal_re] at h2
      linarith
    linarith

/-- **Uniqueness of the Fatou coordinate from the constructed coordinate.**

`Work.Fatou.FatouConstructed` supplies, for each admissible region and near-translation `F`, a
coordinate `Φ₀` which is a Fatou coordinate (`IsFatouCoordOn`: holomorphic, injective, Abel),
surjective modulo `ℤ`, and satisfies the orbit relation A.2.1(i) *for `Φ₀` itself*:
`Φ₀ z' = Φ₀ z + k` (`k : ℕ`) forces `z' = F^[k] z` with the intermediate iterates in `Qreg`.

Claim: any two Fatou coordinates on `Qreg b₁ b₂` differ by a constant.

Proof: the orbit relation of `Φ₀` transfers the `ℤ`-shift relation to any other Fatou coordinate
`Φ`, so the `ℤ`-equivariant extension `ψ` of `Φ ∘ Φ₀⁻¹` (`Work.FatouCH.psiOf`) is entire and
satisfies `ψ (u+1) = ψ u + 1`.  Taking the representative `s ∈ fundStrip` of `w` modulo `ℤ` and
applying Lemma A.2.4(i) (`Work.Fatou.Analysis.fatouDerivEstimate`) to `Φ` and to `Φ₀` on balls of
radius `R → ∞` inside `Qreg` around `s` gives `deriv ψ w → 1` as `|Im w| → ∞`.  Since `deriv ψ`
is `1`-periodic, it is bounded, hence constant (Liouville), hence `1`; so `ψ - id` is constant and
`Φ = Φ₀ + b` on the region.  Applying this to `Φ₁` and to `Φ₂` gives the claim. -/
theorem fatouUniqueOfConstructed (hC : Work.Fatou.FatouConstructed) : MandelDim.FatouUnique := by
  intro b₁ b₂ F Φ₁ Φ₂ hadm hNT hΦ₁ hΦ₂
  obtain ⟨Φ₀, hΦ₀, hsurj, horb⟩ := hC b₁ b₂ F hadm hNT
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := Work.FatouCH.qreg_isOpen b₁ b₂
  have hex : Work.FatouCH.FatouRepExists (MandelDim.Qreg b₁ b₂) Φ₀ := by
    intro u
    obtain ⟨z, hz, n, hn⟩ := hsurj u
    exact ⟨(z, -n), hz, by rw [hn]; push_cast; ring⟩
  obtain ⟨R₁, C₁, C₂, hR₁pos, hC₁pos, hC₂pos, hest⟩ :=
    exists_derivEst_of_fatouDerivEstimate Work.Fatou.Analysis.fatouDerivEstimate
  -- geometric inputs, proved in sibling files
  have hrep_fact : ∀ w : ℂ, ∃ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂)
      (Work.Fatou.xOf b₁ b₂), ∃ n : ℤ, Φ₀ s + (n : ℂ) = w :=
    fun w => exists_fundStrip_rep hadm hNT hΦ₀ hsurj horb w
  have hgeo_fact : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, Work.Fatou.xOf b₁ b₂ - 1 / 32 ≤ s.re →
      s.re ≤ Work.Fatou.xOf b₁ b₂ + 1 + 1 / 32 → ∀ R : ℝ,
      2 * R + K ≤ |s.im| → Metric.ball s R ⊆ MandelDim.Qreg b₁ b₂ :=
    exists_ball_subset_Qreg b₁ b₂ hadm
  have hbound_fact : ∀ M : ℝ, ∃ B : ℝ, ∀ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂)
      (Work.Fatou.xOf b₁ b₂), |s.im| ≤ M → ‖Φ₀ s‖ ≤ B := by
    intro M
    exact exists_norm_le_on_fundStrip hadm hNT hΦ₀ M
  have hre_upper : ∀ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂),
      s.re < Work.Fatou.xOf b₁ b₂ + 1 + 1 / 32 := fun s hs => fundStrip_re_upper hadm hNT hs
  -- the main step: every Fatou coordinate on the region is `Φ₀` plus a constant
  have key : ∀ Φ : ℂ → ℂ, MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂) →
      ∃ c : ℂ, ∀ z ∈ MandelDim.Qreg b₁ b₂, Φ z = Φ₀ z + c := by
    intro Φ hΦ
    have htrans := transfer_of_orbitRel (Φ₀ := Φ₀) horb hΦ
    set ψ : ℂ → ℂ := Work.FatouCH.psiOf (MandelDim.Qreg b₁ b₂) Φ₀ Φ hex with hψdef
    have hψΦ : ∀ z ∈ MandelDim.Qreg b₁ b₂, ψ (Φ₀ z) = Φ z := by
      intro z hz
      have h := Work.FatouCH.psiOf_apply_rep hex htrans (u := Φ₀ z) hz (0 : ℤ)
        (by simp)
      simpa [hψdef] using h
    have hdψ : Differentiable ℂ ψ := by
      rw [hψdef]
      exact Work.FatouCH.psiOf_entire hex hQ hΦ₀.1 hΦ₀.2.1 hΦ.1 htrans
    have hper : ∀ u : ℂ, ψ (u + 1) = ψ u + 1 := by
      intro u
      rw [hψdef]
      exact Work.FatouCH.psiOf_add_one hex htrans u
    -- `deriv ψ` is `1`-periodic
    have hderiv_per : Function.Periodic (deriv ψ) (1 : ℂ) := by
      intro u
      have hcomp : deriv (fun v : ℂ => ψ (v + 1)) u
          = deriv ψ (u + 1) * deriv (fun v : ℂ => v + 1) u :=
        deriv_comp u (hdψ.differentiableAt) (differentiableAt_id.add_const 1)
      have hderiv_shift : deriv (fun v : ℂ => v + 1) u = 1 := by
        have hfun : (fun v : ℂ => v + 1) = (fun v : ℂ => id v + 1) := rfl
        rw [hfun, deriv_add_const, deriv_id]
      have hfun : (fun v : ℂ => ψ (v + 1)) = fun v => ψ v + 1 := by
        funext v; exact hper v
      rw [hfun, deriv_add_const] at hcomp
      rw [hderiv_shift, mul_one] at hcomp
      exact hcomp.symm
    have hderiv_int : ∀ (m : ℤ) (v : ℂ), deriv ψ (v + (m : ℂ)) = deriv ψ v := by
      intro m v
      have h := (hderiv_per.int_mul m) v
      simpa using h
    -- the two ends: `deriv ψ → 1` as `|Im| → ∞`
    have hlim : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ w : ℂ, Y ≤ |w.im| → ‖deriv ψ w - 1‖ ≤ ε := by
      intro ε hε
      obtain ⟨K, hK0, hK⟩ := hgeo_fact
      set R : ℝ := max R₁ (max 1 (max (4 * C₂ / ε + 1) (4 * C₂ + 1))) with hRdef
      have hR₁ : R₁ ≤ R := le_max_left _ _
      have hbig1 : 4 * C₂ / ε + 1 ≤ R :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hbig2 : 4 * C₂ + 1 ≤ R :=
        le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hRpos : 0 < R := lt_of_lt_of_le hR₁pos hR₁
      have hCR : C₂ / R ≤ 1 / 4 := by
        rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 4)]
        linarith
      have h4CR : 4 * C₂ / R ≤ ε := by
        rw [div_le_iff₀ hRpos]
        have h2 : ε * (4 * C₂ / ε + 1) ≤ ε * R := mul_le_mul_of_nonneg_left hbig1 hε.le
        have h3 : ε * (4 * C₂ / ε + 1) = 4 * C₂ + ε := by field_simp
        rw [h3] at h2
        linarith
      obtain ⟨B, hB⟩ := hbound_fact (2 * R + K)
      refine ⟨|B| + 1, fun w hw => ?_⟩
      set k : ℤ := ⌊w.re⌋ with hk
      set u : ℂ := w - (k : ℂ) with hu
      have hw_eq : w = u + (k : ℂ) := by simp [hu]
      have hu_re_eq : u.re = w.re - (k : ℝ) := by rw [hu]; simp
      have hu_re1 : 0 ≤ u.re := by
        have := Int.floor_le w.re
        linarith [hu_re_eq]
      have hu_re2 : u.re ≤ 1 := by
        have := Int.lt_floor_add_one w.re
        linarith [hu_re_eq]
      have hu_im : u.im = w.im := by simp [hu]
      have hderiv_w : deriv ψ w = deriv ψ u := by
        rw [hw_eq]; exact hderiv_int k u
      obtain ⟨s, hs, n, hn⟩ := hrep_fact u
      have hΦ₀s_im : (Φ₀ s).im = u.im := by
        have h := congrArg Complex.im hn
        simpa using h
      have hbig : 2 * R + K ≤ |s.im| := by
        by_contra hcon
        have hle : |s.im| ≤ 2 * R + K := le_of_lt (not_le.mp hcon)
        have hBs := hB s hs hle
        have him : |(Φ₀ s).im| ≤ B := le_trans (Complex.abs_im_le_norm _) hBs
        rw [hΦ₀s_im, hu_im] at him
        have h1 : |B| + 1 ≤ |w.im| := hw
        have h2 : B ≤ |B| := le_abs_self B
        linarith
      have hre := hre_upper s hs
      have hball : Metric.ball s R ⊆ MandelDim.Qreg b₁ b₂ :=
        hK s (by linarith [hs.2.1]) (by linarith [hre]) R hbig
      have hsR : s ∈ Metric.ball s R := Metric.mem_ball_self hRpos
      have hestΦ := deriv_estimate_at hest hNT hΦ hR₁ hball
      have hestΦ₀ := deriv_estimate_at hest hNT hΦ₀ hR₁ hball
      have hFs : ‖F s - s‖ ≤ 33 / 32 := by
        have h := (hNT.2 s (hball hsR)).1
        have he : F s - s = (F s - (s + 1)) + 1 := by ring
        rw [he]
        calc ‖F s - (s + 1) + 1‖ ≤ ‖F s - (s + 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ 1 / 32 + 1 := by rw [norm_one]; linarith
          _ = 33 / 32 := by norm_num
      have hFspos : 0 < ‖F s - s‖ := by
        have h := (hNT.2 s (hball hsR)).1
        have h2 : (1 : ℝ) ≤ ‖F s - s‖ + ‖F s - s - 1‖ := by
          have h3 := norm_sub_le (F s - s) (F s - s - 1)
          have h4 : F s - s - (F s - s - 1) = (1 : ℂ) := by ring
          rw [h4, norm_one] at h3
          exact h3
        have he : F s - s - 1 = F s - (s + 1) := by ring
        rw [he] at h2
        linarith
      have hinv : 32 / 33 ≤ ‖1 / (F s - s)‖ := by
        have hx : ‖1 / (F s - s)‖ = 1 / ‖F s - s‖ := by rw [norm_div, norm_one]
        rw [hx, le_div_iff₀ hFspos]
        calc (32 : ℝ) / 33 * ‖F s - s‖ ≤ 32 / 33 * (33 / 32) :=
              mul_le_mul_of_nonneg_left hFs (by norm_num)
          _ = 1 := by norm_num
      have hΦ₀norm : (1 : ℝ) / 2 ≤ ‖deriv Φ₀ s‖ := by
        have hsmall : ‖deriv Φ₀ s - 1 / (F s - s)‖ ≤ 1 / 4 := le_trans hestΦ₀ hCR
        have h1 : ‖1 / (F s - s)‖ ≤ ‖deriv Φ₀ s‖ + ‖deriv Φ₀ s - 1 / (F s - s)‖ := by
          have h3 := norm_sub_le (deriv Φ₀ s) (deriv Φ₀ s - 1 / (F s - s))
          have h4 : deriv Φ₀ s - (deriv Φ₀ s - 1 / (F s - s)) = 1 / (F s - s) := by ring
          rwa [h4] at h3
        linarith
      have hΦ₀pos : 0 < ‖deriv Φ₀ s‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hΦ₀norm
      have hΦ₀ne : deriv Φ₀ s ≠ 0 := norm_pos_iff.mp hΦ₀pos
      have hchain := deriv_psi_eq hψΦ hdψ hΦ₀ hs.1
      have hψu : deriv ψ u = deriv Φ s / deriv Φ₀ s := by
        rw [← hn, hderiv_int n (Φ₀ s), hchain]
      have hdiff : ‖deriv Φ s - deriv Φ₀ s‖ ≤ 2 * (C₂ / R) := by
        have heq : deriv Φ s - deriv Φ₀ s
            = (deriv Φ s - 1 / (F s - s)) - (deriv Φ₀ s - 1 / (F s - s)) := by ring
        calc ‖deriv Φ s - deriv Φ₀ s‖
            = ‖(deriv Φ s - 1 / (F s - s)) - (deriv Φ₀ s - 1 / (F s - s))‖ := by rw [heq]
          _ ≤ ‖deriv Φ s - 1 / (F s - s)‖ + ‖deriv Φ₀ s - 1 / (F s - s)‖ := norm_sub_le _ _
          _ ≤ C₂ / R + C₂ / R := add_le_add hestΦ hestΦ₀
          _ = 2 * (C₂ / R) := by ring
      calc ‖deriv ψ w - 1‖ = ‖deriv Φ s / deriv Φ₀ s - 1‖ := by rw [hderiv_w, hψu]
        _ = ‖(deriv Φ s - deriv Φ₀ s) / deriv Φ₀ s‖ := by
              congr 1
              rw [div_sub_one hΦ₀ne]
        _ = ‖deriv Φ s - deriv Φ₀ s‖ / ‖deriv Φ₀ s‖ := norm_div _ _
        _ ≤ (2 * (C₂ / R)) / ((1 : ℝ) / 2) :=
              div_le_div₀ (by positivity) hdiff (by norm_num) hΦ₀norm
        _ = 4 * C₂ / R := by ring
        _ ≤ ε := h4CR
    -- `deriv ψ` is bounded, hence constant, hence `1`
    have hGdiff : Differentiable ℂ (fun u : ℂ => deriv ψ u - 1) :=
      (hdψ.deriv).sub (differentiable_const (1 : ℂ))
    have hGbdd : Bornology.IsBounded (Set.range (fun u : ℂ => deriv ψ u - 1)) := by
      obtain ⟨Y, hY⟩ := hlim 1 (by norm_num)
      exact isBounded_range_of_periodic _ (fun u => by rw [hderiv_per u]) hGdiff.continuous hY
    obtain ⟨c, hc⟩ := hGdiff.exists_const_forall_eq_of_bounded hGbdd
    have hc' : ∀ u : ℂ, deriv ψ u - 1 = c := hc
    have hczero : c = 0 := by
      have hnorm : ‖c‖ = 0 := by
        by_contra hne
        have hpos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hne)
        obtain ⟨Y, hY⟩ := hlim (‖c‖ / 2) (by linarith)
        have him : (Complex.I * ((Y + 1 : ℝ) : ℂ)).im = Y + 1 := by simp [Complex.mul_im]
        have hw : Y ≤ |(Complex.I * ((Y + 1 : ℝ) : ℂ)).im| := by
          rw [him]
          linarith [le_abs_self (Y + 1)]
        have h := hY (Complex.I * ((Y + 1 : ℝ) : ℂ)) hw
        rw [hc _] at h
        linarith
      exact norm_eq_zero.mp hnorm
    have hderiv_one : ∀ u : ℂ, deriv ψ u = 1 := by
      intro u
      have h := hc' u
      rw [hczero] at h
      exact sub_eq_zero.mp h
    have hDconst : ∀ u v : ℂ, ψ u - u = ψ v - v := by
      have hf : Differentiable ℂ (ψ - id) := hdψ.sub differentiable_id
      have h0 : ∀ u : ℂ, deriv (ψ - id) u = 0 := by
        intro u
        rw [deriv_sub (hdψ.differentiableAt) differentiableAt_id, deriv_id, hderiv_one u]
        ring
      intro u v
      have := is_const_of_deriv_eq_zero hf h0 u v
      simpa using this
    refine ⟨ψ 0, fun z hz => ?_⟩
    have h1 : ψ (Φ₀ z) = Φ z := hψΦ z hz
    have h2 := hDconst (Φ₀ z) 0
    rw [sub_zero] at h2
    calc Φ z = ψ (Φ₀ z) := h1.symm
      _ = Φ₀ z + ψ 0 := by linear_combination h2
  obtain ⟨c₁, hc₁⟩ := key Φ₁ hΦ₁
  obtain ⟨c₂, hc₂⟩ := key Φ₂ hΦ₂
  refine ⟨c₂ - c₁, fun z hz => ?_⟩
  rw [hc₂ z hz, hc₁ z hz]
  ring

end

end Work.Fatou.Analysis
