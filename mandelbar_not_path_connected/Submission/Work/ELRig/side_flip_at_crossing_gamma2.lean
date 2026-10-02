/-
# ELRig — the side flip at a transversal crossing of the second lift `γ₂`

The `γ₂`-analogue of `Work.ELRig.side_flip_at_crossing`.

The proof reduces the statement to the already proved `γ₁` statement
(`Work.ELRig.side_flip_at_crossing`), using the anti-symmetry `L.anti : γ₂ s = star (γ₁ s) + 1/2`
of the two lifts:

* the reflection `ι w = star w + 1/2` of the `Ψ`-plane carries `γ₂` to `γ₁` and the horizontal
  line through `γ₂ s₀` to the horizontal line through `γ₁ s₀`; hence the crossing of `γ₂` at `s₀`
  is exactly the (downward) crossing of `γ₁` at `s₀`, i.e. the same disjunction that the `γ₁`
  theorem speaks about;
* the `Ψ`-images of the two lines are related by the antiholomorphic square root
  `g = (T_c)^[5]`: `Ψ (star w + 1/2) = g (Ψ w)`;
* on the far-left half plane the side of the pair a point belongs to is read off from its
  external angle (`Work.ELRig.g2_mem_pairSide_iff_InArc`), and the external angle of a
  `g`-image is `θ ↦ -32 θ mod 1` (`Work.ELRig.g2_extAngle_gamma`).  Near the lift point the
  angle is within `(α₂ - α₁)/32` of `α₁`, and on that range the angle map preserves the far arc
  (`Work.ELRig.g2_InArc_alpha_iff_fract`).
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.side_flip_at_crossing
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.Top.extAngle_close_of_Phi_close
import Submission.Work.Top.mem_paramRay_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}

/-! ## Numerical facts about the two root angles -/

theorem g2_alpha1_lt_alpha2 : Work.EL.alpha1 < Work.EL.alpha2 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem g2_alpha2_lt_alpha1_add_one : Work.EL.alpha2 < Work.EL.alpha1 + 1 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem g2_alpha2_add_diff_lt_one :
    Work.EL.alpha2 + (Work.EL.alpha2 - Work.EL.alpha1) < 1 := by
  norm_num [Work.EL.alpha1, Work.EL.alpha2]

theorem g2_diff_div_32_lt_diff :
    (Work.EL.alpha2 - Work.EL.alpha1) / 32 < Work.EL.alpha2 - Work.EL.alpha1 := by
  have h := g2_alpha1_lt_alpha2
  linarith

/-- **The far arc `(α₁, α₂)` is the interval `(α₁, α₂)`.** -/
theorem g2_InArc_alpha_iff {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    Work.EL.InArc x Work.EL.alpha1 Work.EL.alpha2 ↔
      Work.EL.alpha1 < x ∧ x < Work.EL.alpha2 := by
  have hα1 : (0 : ℝ) < Work.EL.alpha1 := by norm_num [Work.EL.alpha1]
  have hα1' : Work.EL.alpha1 < 1 := by norm_num [Work.EL.alpha1]
  have hα2 : Work.EL.alpha2 < 1 := by norm_num [Work.EL.alpha2]
  have hd0 : (0 : ℝ) < Work.EL.alpha2 - Work.EL.alpha1 := by linarith [g2_alpha1_lt_alpha2]
  have hd1 : Work.EL.alpha2 - Work.EL.alpha1 < 1 := by
    have := g2_alpha2_lt_alpha1_add_one
    linarith
  have harc : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2
      = Work.EL.alpha2 - Work.EL.alpha1 :=
    Int.fract_eq_self.mpr ⟨le_of_lt hd0, hd1⟩
  rw [Work.EL.InArc, harc]
  constructor
  · intro h
    by_cases hpos : 0 ≤ x - Work.EL.alpha1
    · have hfr : Int.fract (x - Work.EL.alpha1) = x - Work.EL.alpha1 :=
        Int.fract_eq_self.mpr ⟨hpos, by linarith [hx.2, hα1]⟩
      rw [hfr] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have hneg : x - Work.EL.alpha1 < 0 := lt_of_not_ge hpos
      have hfr : Int.fract (x - Work.EL.alpha1) = x - Work.EL.alpha1 + 1 := by
        rw [Int.fract_eq_iff]
        exact ⟨by linarith [hx.1, hα1'], by linarith [hneg], ⟨-1, by push_cast; ring⟩⟩
      rw [hfr] at h
      have hlt : x < Work.EL.alpha2 - 1 := by linarith [h.2]
      linarith [hx.1]
  · rintro ⟨h1, h2⟩
    have hfr : Int.fract (x - Work.EL.alpha1) = x - Work.EL.alpha1 :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith [hx.2, hα1]⟩
    rw [hfr]
    exact ⟨by linarith, by linarith⟩

/-- **The angle map `θ ↦ -32 θ mod 1` preserves the far arc near `α₁`.** -/
theorem g2_InArc_alpha_iff_fract {θ : ℝ} (hθ : θ ∈ Set.Ico (0 : ℝ) 1)
    (hclose : |θ - Work.EL.alpha1| < (Work.EL.alpha2 - Work.EL.alpha1) / 32) :
    Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 ↔
      Work.EL.InArc (Int.fract (-32 * θ)) Work.EL.alpha1 Work.EL.alpha2 := by
  have hα1 : (0 : ℝ) < Work.EL.alpha1 := by norm_num [Work.EL.alpha1]
  set φ : ℝ := θ - Work.EL.alpha1 with hφdef
  have hφabs : |φ| < (Work.EL.alpha2 - Work.EL.alpha1) / 32 := by rw [hφdef]; exact hclose
  have h32abs : |32 * φ| < Work.EL.alpha2 - Work.EL.alpha1 := by
    have hcont : (32 : ℝ) * ((Work.EL.alpha2 - Work.EL.alpha1) / 32)
        = Work.EL.alpha2 - Work.EL.alpha1 := by ring
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    calc (32 : ℝ) * |φ| < 32 * ((Work.EL.alpha2 - Work.EL.alpha1) / 32) :=
          mul_lt_mul_of_pos_left hφabs (by norm_num)
      _ = Work.EL.alpha2 - Work.EL.alpha1 := hcont
  obtain ⟨h32lo, h32hi⟩ := abs_lt.mp h32abs
  have h32a : (-32 : ℝ) * Work.EL.alpha1 = Work.EL.alpha2 - 12 := by
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hfr : Int.fract (-32 * θ) = Work.EL.alpha2 - 32 * φ := by
    have h1 : -32 * θ = (Work.EL.alpha2 - 32 * φ) + ((-12 : ℤ) : ℝ) := by
      rw [hφdef]; push_cast; linarith [h32a]
    rw [h1, Int.fract_add_intCast]
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · linarith [h32hi, hα1]
    · linarith [h32lo, g2_alpha2_add_diff_lt_one]
  have hθlt : θ < Work.EL.alpha2 := by
    have h1 : φ < (Work.EL.alpha2 - Work.EL.alpha1) / 32 := (abs_lt.mp hφabs).2
    have h2 := g2_diff_div_32_lt_diff
    rw [hφdef] at h1
    linarith
  have hθeq : θ = Work.EL.alpha1 + φ := by rw [hφdef]; ring
  rw [g2_InArc_alpha_iff hθ,
    g2_InArc_alpha_iff (x := Int.fract (-32 * θ))
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    hfr, hθeq]
  constructor
  · intro h
    have hφpos : 0 < φ := by linarith [h.1]
    exact ⟨by linarith [h32hi], by linarith [hφpos]⟩
  · intro h
    have h1 : 32 * φ < Work.EL.alpha2 - Work.EL.alpha1 := by linarith [h.1]
    have h2 : 0 < 32 * φ := by linarith [h.2]
    have hφpos : 0 < φ := by nlinarith
    exact ⟨by linarith [hφpos], by nlinarith⟩

/-! ## The side of a point off the filled Julia set is read off from its angle -/

theorem g2_mem_pairSide_iff_InArc {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) (hside : Work.EL.PairSides hN P)
    (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {z : ℂ} (hzK : z ∉ Work.EL.K c)
    (hzc : z ∉ Work.EL.pairCurve P) :
    z ∈ Work.EL.pairSide P ↔
      Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) P.a P.b := by
  set θ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z with hθdef
  have hmem : z ∈ Work.EL.paramRay hN θ := Work.Top.mem_paramRay_extAngle hN hzK
  constructor
  · intro hz
    by_contra hnot
    have hexa : ∀ k : ℤ, θ ≠ P.a + (k : ℝ) := by
      intro k hk
      have h2 : Work.EL.paramRay hN θ = Work.EL.paramRay hN P.a := by
        rw [hk]; exact Work.ELTop.paramRay_add_int hN P.a k
      exact hzc ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inl (by rw [← h2]; exact hmem)))
    have hexb : ∀ k : ℤ, θ ≠ P.b + (k : ℝ) := by
      intro k hk
      have h2 : Work.EL.paramRay hN θ = Work.EL.paramRay hN P.b := by
        rw [hk]; exact Work.ELTop.paramRay_add_int hN P.b k
      exact hzc ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inr (Or.inr (by rw [← h2]; exact hmem))))
    rcases Work.ELTop.InArc_or_InArc_near hab hb1 hexa hexb with harc | harc
    · exact hnot harc
    · exact (Set.disjoint_left.mp hside.disjoint hz)
        (Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN P hab hb1 harc hmem)
  · intro harc
    exact Work.ELTop.paramRay_subset_pairSide_of_InArc hN P hab hb1 harc hmem

/-! ## The external angle of a `g`-image -/

theorem g2_star_mul_exp_pow (r θ : ℝ) :
    (star (((r : ℂ)) * Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)))^32
      = ((r^32 : ℝ) : ℂ) * Complex.exp (-(64 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) := by
  have hZ : star (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = -(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) := by
    rw [Complex.star_def]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
    ring
  have hexp : star (Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I))
      = Complex.exp (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) := by
    rw [show star (Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I))
        = Complex.exp (star (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)) from
      (Complex.exp_conj _).symm, hZ]
  rw [star_mul, hexp, Complex.star_def, Complex.conj_ofReal, mul_pow, ← Complex.exp_nat_mul,
    Complex.ofReal_pow]
  rw [show (((32 : ℕ) : ℂ) * (-(2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)))
      = -(64 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) by ring]
  ring

theorem g2_exp_neg_64 (θ : ℝ) : Complex.exp (-(64 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I))
    = Complex.exp (2 * (Real.pi : ℂ) * ((Int.fract (-32 * θ) : ℝ) : ℂ) * Complex.I) := by
  have hFM : ((Int.fract (-32 * θ) : ℝ) : ℂ) + ((⌊-32 * θ⌋ : ℤ) : ℂ) = -32 * (θ : ℂ) := by
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_add, Int.fract_add_floor]
    push_cast; ring
  have harg : -(64 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * ((Int.fract (-32 * θ) : ℝ) : ℂ) * Complex.I
        + ((⌊-32 * θ⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [show 2 * (Real.pi : ℂ) * ((Int.fract (-32 * θ) : ℝ) : ℂ) * Complex.I
          + ((⌊-32 * θ⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = 2 * (Real.pi : ℂ) * Complex.I
          * (((Int.fract (-32 * θ) : ℝ) : ℂ) + ((⌊-32 * θ⌋ : ℤ) : ℂ)) by ring,
      hFM]
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The external angle of a `g`-image.** -/
theorem g2_extAngle_gamma {c : ℂ} (d : Work.EL.RootParabolic c) {z : ℂ}
    (hz : z ∉ Work.EL.K c) (hgz : (Tantibar c)^[5] z ∉ Work.EL.K c) :
    Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) ((Tantibar c)^[5] z)
      = Int.fract (-32 * Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z) := by
  set θ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hθdef
  have hzEsc : Work.ParamRays.Escaping c z :=
    (Work.ParamRays.escaping_iff_not_bounded c z).mpr
      (by simpa [Work.EL.K, Work.ParamRays.filledJulia] using hz)
  have hlevel : 1 < ‖d.φ z‖ := by
    rw [← Work.EL.dynPhi_of_notMem (c := c) (φ := d.φ) hz]
    exact d.hN.Phi_mem_exteriorDisc hz
  have hpol : d.φ z
      = ((‖d.φ z‖ : ℝ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) := by
    have h := Work.Top.Phi_eq_norm_mul_exp_extAngle (Mb := Work.EL.K c)
      (Φ := Work.EL.dynPhi c d.φ) d.hN (c := z) (d.hN.Phi_ne_zero hz)
    rw [Work.EL.dynPhi_of_notMem (c := c) (φ := d.φ) hz] at h
    exact h
  have hφ4 : d.φ (Work.ParamRays.orbit c z 4) = d.φ z ^ 16 := by
    have h := Work.ParamRays.IsDynBottcher.functional_iterate d.bottcher hzEsc 2
    simpa using h
  have hEsc4 : Work.ParamRays.Escaping c (Work.ParamRays.orbit c z 4) := hzEsc.iterate 4
  have h5 : d.φ ((Tantibar c)^[5] z) = star (d.φ z) ^ 32 := by
    have h1 : (Tantibar c)^[5] z = Tantibar c (Work.ParamRays.orbit c z 4) := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, Function.iterate_succ_apply']
      rfl
    rw [h1, d.bottcher.2.1 _ hEsc4, hφ4]
    show star (d.φ z ^ 16) ^ 2 = star (d.φ z) ^ 32
    rw [star_pow]; ring
  have hray : d.φ ((Tantibar c)^[5] z)
      = Work.Top.NakaneData.rayPoint (Int.fract (-32 * θ)) (‖d.φ z‖ ^ 32) := by
    conv_lhs => rw [h5, hpol]
    rw [g2_star_mul_exp_pow]
    rw [Work.Top.NakaneData.rayPoint, g2_exp_neg_64]
  have hmem : (Tantibar c)^[5] z ∈ Work.Top.NakaneData.paramRay d.hN (Int.fract (-32 * θ)) := by
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    exact ⟨hgz, ‖d.φ z‖ ^ 32, one_lt_pow₀ hlevel (by norm_num : (32 : ℕ) ≠ 0), by
      rw [Work.EL.dynPhi_of_notMem (c := c) (φ := d.φ) hgz]; exact hray⟩
  exact Work.Top.extAngle_of_mem_paramRay d.hN (Int.fract_nonneg _) (Int.fract_lt_one _) hmem

/-! ## The reflection `w ↦ star w + 1/2` permutes the two lifts -/

theorem g2_range_sub_one (L : Work.ELRig.RayCylLift d fl) :
    ∀ w : ℂ, (w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) ↔
      (w - 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
  intro w
  constructor
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · refine Or.inl ⟨s - 1, ?_⟩
      have h := L.per₁ (s - 1)
      rw [show s - 1 + 1 = s from by ring] at h
      rw [h]; ring
    · refine Or.inr ⟨s - 1, ?_⟩
      have h := L.per₂ (s - 1)
      rw [show s - 1 + 1 = s from by ring] at h
      rw [h]; ring
  · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · refine Or.inl ⟨s + 1, ?_⟩
      rw [L.per₁ s, hs]; ring
    · refine Or.inr ⟨s + 1, ?_⟩
      rw [L.per₂ s, hs]; ring

theorem g2_range_swap (L : Work.ELRig.RayCylLift d fl) :
    ∀ w : ℂ, (star w + 1/2 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) ↔
      (w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
  have hsub : ∀ u : ℂ, (u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) →
      (star u + 1/2 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) := by
    rintro u (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Or.inr ⟨s, L.anti s⟩
    · refine Or.inl ⟨s + 1, ?_⟩
      rw [L.per₁ s, L.anti s]
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
  intro w
  constructor
  · intro hw
    have h2 : star (star w + 1/2) + 1/2 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := hsub _ hw
    have h3 : star (star w + 1/2) + 1/2 = w + 1 := by
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    rw [h3] at h2
    simpa using (g2_range_sub_one L (w + 1)).mp h2
  · intro hw
    exact hsub w hw

/-! ## Local data near the two lift points -/

theorem g2_exists_extAngle_close {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ε > 0, ∀ q : ℂ, ‖q - L.γ₁ s₀‖ < ε →
      fl.Ψ q ∉ Work.EL.K c ∧
      |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ q) - Work.EL.alpha1|
        < (Work.EL.alpha2 - Work.EL.alpha1) / 32 := by
  have hθ₀ : (0 : ℝ) < Work.EL.alpha1 := by norm_num [Work.EL.alpha1]
  have hθ₁ : Work.EL.alpha1 < 1 := by norm_num [Work.EL.alpha1]
  have hη : (0 : ℝ) < (Work.EL.alpha2 - Work.EL.alpha1) / 32 := by
    have := g2_alpha1_lt_alpha2; linarith
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.Top.extAngle_close_of_Phi_close (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c d.φ) d.hN
      (θ := Work.EL.alpha1) (R := L.τ s₀) hθ₀ hθ₁ (L.hτ1 s₀) hη
  have hKp : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have hΦp : Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s₀))
      = Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) := by
    rw [L.hΨ₁ s₀]
    exact Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s₀)
  have hΦcont : ContinuousOn (Work.EL.dynPhi c d.φ) (Work.EL.K c)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : (Set.domRestrict (Work.EL.K c)ᶜ (Work.EL.dynPhi c d.φ))
        = fun z => ((d.hN.e z : Work.Top.exteriorDisc) : ℂ) := by
      funext z; exact d.hN.he z
    rw [h]
    exact continuous_subtype_val.comp d.hN.e.continuous
  have hcontΦ : ContinuousAt (fun q : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ q)) (L.γ₁ s₀) :=
    (hΦcont.continuousAt
      ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hKp)).comp
      fl.Ψ_diff.continuous.continuousAt
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.continuousAt_iff.mp hcontΦ δ hδpos
  obtain ⟨δ', hδ'pos, hδ'⟩ :=
    Metric.isOpen_iff.mp ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl)
      (fl.Ψ (L.γ₁ s₀)) hKp
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp fl.Ψ_diff.continuous.continuousAt δ' hδ'pos
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun q hq => ?_⟩
  have hq₁ : dist q (L.γ₁ s₀) < ε₁ :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (min_le_left _ _)
  have hq₂ : dist q (L.γ₁ s₀) < ε₂ :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (min_le_right _ _)
  have hqK : fl.Ψ q ∉ Work.EL.K c :=
    hδ' (Metric.mem_ball.mpr (hε₂ hq₂))
  refine ⟨hqK, ?_⟩
  have h1 := hε₁ hq₁
  rw [hΦp] at h1
  exact hδ (fl.Ψ q) hqK (by rwa [dist_eq_norm] at h1)

theorem g2_exists_psi_ne_K {s₀ : ℝ} :
    ∃ ε > 0, ∀ w : ℂ, ‖w - L.γ₂ s₀‖ < ε → fl.Ψ w ∉ Work.EL.K c := by
  have hKp : fl.Ψ (L.γ₂ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₂ s₀]
    exact Work.EL.rayPt_notMem_K d.hN (one_lt_pow₀ (L.hτ1 s₀) (by norm_num))
  obtain ⟨δ', hδ'pos, hδ'⟩ :=
    Metric.isOpen_iff.mp ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl)
      (fl.Ψ (L.γ₂ s₀)) hKp
  obtain ⟨ε, hεpos, hε⟩ := Metric.continuousAt_iff.mp fl.Ψ_diff.continuous.continuousAt δ' hδ'pos
  refine ⟨ε, hεpos, fun w hw => hδ' (Metric.mem_ball.mpr (hε (by rw [dist_eq_norm]; exact hw)))⟩

/-! ## The pointwise comparison of the two pair sides -/

theorem g2_far_swap (P : Work.EL.CoPair d.hN) (hside : Work.EL.PairSides d.hN P)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2)
    {q w : ℂ} (hw : w = star q + 1/2)
    (hKq : fl.Ψ q ∉ Work.EL.K c) (hKw : fl.Ψ w ∉ Work.EL.K c)
    (hcq : fl.Ψ q ∉ Work.EL.pairCurve P) (hcw : fl.Ψ w ∉ Work.EL.pairCurve P)
    (hclose : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ q)
      - Work.EL.alpha1| < (Work.EL.alpha2 - Work.EL.alpha1) / 32) :
    (fl.Ψ q ∈ Work.EL.pairSide P) ↔ (fl.Ψ w ∈ Work.EL.pairSide P) := by
  have hab : P.a < P.b := by rw [hPa, hPb]; exact g2_alpha1_lt_alpha2
  have hb1 : P.b < P.a + 1 := by rw [hPa, hPb]; exact g2_alpha2_lt_alpha1_add_one
  have h1 := g2_mem_pairSide_iff_InArc P hside hab hb1 hKq hcq
  rw [hPa, hPb] at h1
  have h2 := g2_mem_pairSide_iff_InArc P hside hab hb1 hKw hcw
  rw [hPa, hPb] at h2
  have hψ : fl.Ψ w = (Tantibar c)^[5] (fl.Ψ q) := by rw [hw, fl.Ψ_anti]
  have hgK : (Tantibar c)^[5] (fl.Ψ q) ∉ Work.EL.K c := by rw [← hψ]; exact hKw
  have hθ : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)
      = Int.fract (-32 * Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ q)) := by
    rw [hψ]
    exact g2_extAngle_gamma d hKq hgK
  rw [h1, h2, hθ]
  exact g2_InArc_alpha_iff_fract (Work.Top.NakaneData.extAngle_mem_Ico _ _) hclose

/-! ## The main theorem -/

theorem side_flip_at_crossing_gamma2 {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {s₀ : ℝ} (hre : (L.γ₂ s₀).re < -L.R)
    (hsimple : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₂ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₂ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s).im < (L.γ₂ s₀).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s₀).im < (L.γ₂ s).im)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s₀).im < (L.γ₂ s).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s).im < (L.γ₂ s₀).im))) ↔
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      (fl.Ψ (L.γ₂ s₀ + t) ∈ Work.EL.pairSide P ↔
        ¬ (fl.Ψ (L.γ₂ s₀ - t) ∈ Work.EL.pairSide P))) := by
  classical
  have hanti₀ : L.γ₂ s₀ = star (L.γ₁ s₀) + 1/2 := L.anti s₀
  have hre₁ : (L.γ₁ s₀).re < -L.R := by
    have h : (L.γ₂ s₀).re = (L.γ₁ s₀).re + 1/2 := by
      rw [hanti₀]; simp
    linarith
  -- ## the transfer of the simplicity hypothesis to `γ₁`
  obtain ⟨δs, hδspos, hsimple₂⟩ := hsimple
  have hsimple₁body : ∀ t ∈ Set.Ioo (0 : ℝ) δs,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro t ht
    obtain ⟨h1, h2⟩ := hsimple₂ t ht
    have hep : L.γ₁ s₀ + (t : ℂ) = (star (L.γ₂ s₀ + (t : ℂ)) + 1/2) - 1 := by
      rw [L.anti s₀]
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    have hem : L.γ₁ s₀ - (t : ℂ) = (star (L.γ₂ s₀ - (t : ℂ)) + 1/2) - 1 := by
      rw [L.anti s₀]
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    constructor
    · intro hc
      have hc' : (star (L.γ₂ s₀ + (t : ℂ)) + 1/2) - 1
          ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by rw [← hep]; exact hc
      exact h1 ((g2_range_swap L _).mp
        ((g2_range_sub_one L (star (L.γ₂ s₀ + (t : ℂ)) + 1/2)).mpr hc'))
    · intro hc
      have hc' : (star (L.γ₂ s₀ - (t : ℂ)) + 1/2) - 1
          ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by rw [← hem]; exact hc
      exact h2 ((g2_range_swap L _).mp
        ((g2_range_sub_one L (star (L.γ₂ s₀ - (t : ℂ)) + 1/2)).mpr hc'))
  have hsimple₁ : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
    ⟨δs, hδspos, hsimple₁body⟩
  -- ## the `γ₁` theorem
  have hγ₁ := side_flip_at_crossing d fl L P hPa hPb hPy hside hre₁ hsimple₁
  -- ## the disjunction of the statement is the disjunction of the `γ₁` statement
  have hIm : ∀ s : ℝ, (L.γ₂ s).im = -(L.γ₁ s).im := by
    intro s
    rw [L.anti s]; simp
  have hiffA : ∀ ε : ℝ,
      ((∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s).im < (L.γ₂ s₀).im) ↔
       (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s₀).im < (L.γ₁ s).im)) := by
    intro ε; constructor
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀] at this; linarith
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀]; linarith
  have hiffB : ∀ ε : ℝ,
      ((∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s₀).im < (L.γ₂ s).im) ↔
       (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s).im < (L.γ₁ s₀).im)) := by
    intro ε; constructor
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀] at this; linarith
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀]; linarith
  have hiffC : ∀ ε : ℝ,
      ((∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s₀).im < (L.γ₂ s).im) ↔
       (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s).im < (L.γ₁ s₀).im)) := by
    intro ε; constructor
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀] at this; linarith
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀]; linarith
  have hiffD : ∀ ε : ℝ,
      ((∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s).im < (L.γ₂ s₀).im) ↔
       (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s₀).im < (L.γ₁ s).im)) := by
    intro ε; constructor
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀] at this; linarith
    · intro h s hs
      have := h s hs; rw [hIm s, hIm s₀]; linarith
  have hLHS :
      ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s).im < (L.γ₂ s₀).im) ∧
          (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s₀).im < (L.γ₂ s).im)) ∨
        (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₂ s₀).im < (L.γ₂ s).im) ∧
          (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₂ s).im < (L.γ₂ s₀).im)))
      ↔
      ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s).im < (L.γ₁ s₀).im) ∧
          (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s₀).im < (L.γ₁ s).im)) ∨
        (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s₀).im < (L.γ₁ s).im) ∧
          (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s).im < (L.γ₁ s₀).im))) := by
    constructor
    · rintro (⟨ε, hε, h1, h2⟩ | ⟨ε, hε, h1, h2⟩)
      · right; exact ⟨ε, hε, (hiffA ε).mp h1, (hiffB ε).mp h2⟩
      · left; exact ⟨ε, hε, (hiffC ε).mp h1, (hiffD ε).mp h2⟩
    · rintro (⟨ε, hε, h1, h2⟩ | ⟨ε, hε, h1, h2⟩)
      · right; exact ⟨ε, hε, (hiffC ε).mpr h1, (hiffD ε).mpr h2⟩
      · left; exact ⟨ε, hε, (hiffA ε).mpr h1, (hiffB ε).mpr h2⟩
  -- ## the pointwise comparison of the two flips
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := g2_exists_extAngle_close (c := c) (d := d) (fl := fl) (L := L) hre₁
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := g2_exists_psi_ne_K (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀)
  have hmargin₁ : 0 < -L.R - (L.γ₁ s₀).re := by linarith [hre₁]
  have hmargin₂ : 0 < -L.R - (L.γ₂ s₀).re := by linarith [hre]
  set δ₀ : ℝ := min (min δs (min ε₁ ε₂))
    (min (-L.R - (L.γ₁ s₀).re) (-L.R - (L.γ₂ s₀).re)) with hδ₀def
  have hδ₀pos : 0 < δ₀ :=
    lt_min (lt_min hδspos (lt_min hε₁pos hε₂pos)) (lt_min hmargin₁ hmargin₂)
  have hδ₀δs : δ₀ ≤ δs := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀ε₁ : δ₀ ≤ ε₁ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀ε₂ : δ₀ ≤ ε₂ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₀m₁ : δ₀ ≤ -L.R - (L.γ₁ s₀).re := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀m₂ : δ₀ ≤ -L.R - (L.γ₂ s₀).re := le_trans (min_le_right _ _) (min_le_right _ _)
  have hdist₁ : ∀ t : ℝ, 0 < t → ‖L.γ₁ s₀ + (t : ℂ) - L.γ₁ s₀‖ = t := by
    intro t ht
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hdist₁m : ∀ t : ℝ, 0 < t → ‖L.γ₁ s₀ - (t : ℂ) - L.γ₁ s₀‖ = t := by
    intro t ht
    rw [show L.γ₁ s₀ - (t : ℂ) - L.γ₁ s₀ = -((t : ℂ)) by ring, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
  have hdist₂ : ∀ t : ℝ, 0 < t → ‖L.γ₂ s₀ + (t : ℂ) - L.γ₂ s₀‖ = t := by
    intro t ht
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hdist₂m : ∀ t : ℝ, 0 < t → ‖L.γ₂ s₀ - (t : ℂ) - L.γ₂ s₀‖ = t := by
    intro t ht
    rw [show L.γ₂ s₀ - (t : ℂ) - L.γ₂ s₀ = -((t : ℂ)) by ring, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
  have hreQ : ∀ t : ℝ, 0 < t → t < -L.R - (L.γ₁ s₀).re →
      (L.γ₁ s₀ + (t : ℂ)).re < -L.R ∧ (L.γ₁ s₀ - (t : ℂ)).re < -L.R := by
    intro t ht htm
    have h1 : (L.γ₁ s₀ + (t : ℂ)).re = (L.γ₁ s₀).re + t := by
      simp only [Complex.add_re, Complex.ofReal_re]
    have h2 : (L.γ₁ s₀ - (t : ℂ)).re = (L.γ₁ s₀).re - t := by
      simp only [Complex.sub_re, Complex.ofReal_re]
    rw [h1, h2]; constructor <;> linarith
  have hreW : ∀ t : ℝ, 0 < t → t < -L.R - (L.γ₂ s₀).re →
      (L.γ₂ s₀ + (t : ℂ)).re < -L.R ∧ (L.γ₂ s₀ - (t : ℂ)).re < -L.R := by
    intro t ht htm
    have h1 : (L.γ₂ s₀ + (t : ℂ)).re = (L.γ₂ s₀).re + t := by
      simp only [Complex.add_re, Complex.ofReal_re]
    have h2 : (L.γ₂ s₀ - (t : ℂ)).re = (L.γ₂ s₀).re - t := by
      simp only [Complex.sub_re, Complex.ofReal_re]
    rw [h1, h2]; constructor <;> linarith
  have hpoint : ∀ t ∈ Set.Ioo (0 : ℝ) δ₀,
      ((fl.Ψ (L.γ₂ s₀ + t) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₂ s₀ - t) ∈ Work.EL.pairSide P)) ↔
        (fl.Ψ (L.γ₁ s₀ + t) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₁ s₀ - t) ∈ Work.EL.pairSide P))) := by
    intro t ht
    have htε₁ : t < ε₁ := lt_of_lt_of_le ht.2 hδ₀ε₁
    have htε₂ : t < ε₂ := lt_of_lt_of_le ht.2 hδ₀ε₂
    have htδ : t < δs := lt_of_lt_of_le ht.2 hδ₀δs
    have htm₁ : t < -L.R - (L.γ₁ s₀).re := lt_of_lt_of_le ht.2 hδ₀m₁
    have htm₂ : t < -L.R - (L.γ₂ s₀).re := lt_of_lt_of_le ht.2 hδ₀m₂
    obtain ⟨hsp, hsm⟩ := hsimple₂ t ⟨ht.1, htδ⟩
    obtain ⟨h₁p, h₁m⟩ := hsimple₁body t ⟨ht.1, htδ⟩
    have hq₁ := hε₁ (L.γ₁ s₀ + (t : ℂ)) (by rw [hdist₁ t ht.1]; exact htε₁)
    have hq₂ := hε₁ (L.γ₁ s₀ - (t : ℂ)) (by rw [hdist₁m t ht.1]; exact htε₁)
    have hw₁ := hε₂ (L.γ₂ s₀ + (t : ℂ)) (by rw [hdist₂ t ht.1]; exact htε₂)
    have hw₂ := hε₂ (L.γ₂ s₀ - (t : ℂ)) (by rw [hdist₂m t ht.1]; exact htε₂)
    have hswapp : L.γ₂ s₀ + (t : ℂ) = star (L.γ₁ s₀ + (t : ℂ)) + 1/2 := by
      rw [L.anti s₀]
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    have hswapm : L.γ₂ s₀ - (t : ℂ) = star (L.γ₁ s₀ - (t : ℂ)) + 1/2 := by
      rw [L.anti s₀]
      apply Complex.ext <;>
        simp [Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring
    have hp := g2_far_swap (c := c) (d := d) (fl := fl) P hside hPa hPb
      hswapp hq₁.1 hw₁
      (fun hc => h₁p ((RayCylLift.preimage_pairCurve L P hPa hPb hPy _
        (hreQ t ht.1 htm₁).1).mp hc))
      (fun hc => hsp ((RayCylLift.preimage_pairCurve L P hPa hPb hPy _
        (hreW t ht.1 htm₂).1).mp hc))
      hq₁.2
    have hm := g2_far_swap (c := c) (d := d) (fl := fl) P hside hPa hPb
      hswapm hq₂.1 hw₂
      (fun hc => h₁m ((RayCylLift.preimage_pairCurve L P hPa hPb hPy _
        (hreQ t ht.1 htm₁).2).mp hc))
      (fun hc => hsm ((RayCylLift.preimage_pairCurve L P hPa hPb hPy _
        (hreW t ht.1 htm₂).2).mp hc))
      hq₂.2
    rw [hp, hm]
  -- ## the two `∃δ` statements are equivalent
  have hflip :
      (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
        (fl.Ψ (L.γ₂ s₀ + t) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₂ s₀ - t) ∈ Work.EL.pairSide P))) ↔
      (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
        (fl.Ψ (L.γ₁ s₀ + t) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (L.γ₁ s₀ - t) ∈ Work.EL.pairSide P))) := by
    constructor
    · rintro ⟨δ, hδ, h⟩
      refine ⟨min δ δ₀, lt_min hδ hδ₀pos, fun t ht => ?_⟩
      exact (hpoint t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩).mp
        (h t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩)
    · rintro ⟨δ, hδ, h⟩
      refine ⟨min δ δ₀, lt_min hδ hδ₀pos, fun t ht => ?_⟩
      exact (hpoint t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩).mpr
        (h t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩)
  exact hLHS.trans (hγ₁.trans hflip.symm)

end

end Work.ELRig
