import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdentP.Dev2

open Work.FTS.BSIdent

open Filter Set MeasureTheory
open scoped Topology

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The odd extension of `Φ(·,·,τ)` as a two-variable function. -/
noncomputable def GG (Φ : Work.FTS.BSIdent.Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun w θ => Work.FTS.BSIdent.PhiOdd Φ w θ τ

theorem GG_apply (w θ : ℝ) : GG Φ τ w θ = Work.FTS.BSIdent.PhiOdd Φ w θ τ := rfl

theorem abs_pi_div_two_lt : |Real.pi / 2| < Real.pi / 2 + 1 := by
  rw [abs_of_pos (by linarith [Real.pi_pos])]; linarith

/-- The slice-in-`θ` version of `hsm`. -/
theorem contDiffAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  hsm w θ hw (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])

theorem continuousAt_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ) :=
  (contDiffAt_Phi hsm hw hθ).continuousAt

theorem continuousAt_pdR_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdR_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

theorem continuousAt_pdZ_Phi {τ : ℝ} {Φ : Work.FTS.BSIdent.Fam}
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    {w θ : ℝ} (hw : 0 < w) (hθ : |θ| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2) (w, θ) :=
  (Work.FTS.BSIdent.Defs.contDiffAt_pdZ_uncurry_one (contDiffAt_Phi hsm hw hθ)).continuousAt

/-! ## The slice identities for `GG` -/

theorem GG_of_pos {w θ : ℝ} (hθ : 0 < θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ.le

theorem GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) : GG Φ τ w θ = Φ w θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg hθ

theorem GG_of_neg {w θ : ℝ} (hθ : θ < 0) : GG Φ τ w θ = -(Φ w (-θ) τ) :=
  Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ)

theorem pdR_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_pos (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_nonneg {w θ : ℝ} (hθ : 0 ≤ θ) :
    Work.Cyl.pdR (GG Φ τ) w θ = Work.Cyl.pdR (fun w θ => Φ w θ τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => Φ w' θ τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) hθ
  simp only [Work.Cyl.pdR, h]

theorem pdR_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdR (GG Φ τ) w θ = -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) w θ := by
  have h : (fun w' => GG Φ τ w' θ) = (fun w' => -(Φ w' (-θ) τ)) := by
    funext w'; exact GG_of_neg (Φ := Φ) (τ := τ) hθ
  have h2 : deriv (fun w' : ℝ => -(Φ w' (-θ) τ)) w
      = -deriv (fun w' : ℝ => Φ w' (-θ) τ) w := by
    rw [show (fun w' : ℝ => -(Φ w' (-θ) τ)) = -(fun w' : ℝ => Φ w' (-θ) τ) from rfl,
      deriv.neg]
  simp only [Work.Cyl.pdR, h, h2]

theorem pdZ_GG_of_pos {w θ : ℝ} (hθ : 0 < θ) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w θ := by
  simp only [Work.Cyl.pdZ]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hθ] with θ' hθ'
  exact GG_of_pos (Φ := Φ) (τ := τ) hθ'

theorem pdZ_GG_of_neg {w θ : ℝ} (hθ : θ < 0) :
    Work.Cyl.pdZ (GG Φ τ) w θ = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w (-θ) := by
  simp only [Work.Cyl.pdZ]
  have h : (fun θ' => GG Φ τ w θ') =ᶠ[𝓝 θ] (fun θ' => -(Φ w (-θ') τ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hθ] with θ' hθ'
    exact GG_of_neg (Φ := Φ) (τ := τ) hθ'
  rw [Filter.EventuallyEq.deriv_eq h]
  have h3 : deriv (fun θ' : ℝ => -(Φ w (-θ') τ)) θ
      = - deriv (fun θ' : ℝ => Φ w (-θ') τ) θ := by
    rw [show (fun θ' : ℝ => -(Φ w (-θ') τ)) = -(fun θ' : ℝ => Φ w (-θ') τ) from rfl,
      deriv.neg]
  have h2 : deriv (fun θ' : ℝ => Φ w (-θ') τ) θ
      = - deriv (fun θ'' : ℝ => Φ w θ'' τ) (-θ) :=
    deriv_comp_neg (fun θ'' : ℝ => Φ w θ'' τ) θ
  rw [h3, h2, neg_neg]

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` near `θ = ±π/2` -/

theorem continuousAt_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ) (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2)) (g := fun q : ℝ × ℝ => Φ q.1 q.2 τ) h1 hneg
  have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdR_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdR_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdZ_GG_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, Real.pi / 2) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, Real.pi / 2) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_snd)
    show (0:ℝ) < Real.pi / 2
    linarith [Real.pi_pos]
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, Real.pi / 2)]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt).congr hev

theorem continuousAt_pdZ_GG_neg_pi_div_two {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w →
      -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, -(Real.pi / 2)) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, -(Real.pi / 2)) := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_snd continuous_const)
    show -(Real.pi / 2) < (0:ℝ)
    linarith [Real.pi_pos]
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2)) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      (w₀, -(Real.pi / 2)) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, -(Real.pi / 2))) := by
      simpa using (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ abs_pi_div_two_lt)
    exact ContinuousAt.comp (x := (w₀, -(Real.pi / 2)))
      (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      =ᶠ[𝓝 (w₀, -(Real.pi / 2))]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.congr hev

/-! ## Continuity of `GG`, `pdR GG` at `θ = 0` -/

theorem continuousAt_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, 0) := by
  have hval : GG Φ τ w₀ 0 = 0 := by
    rw [GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl]; exact h0 w₀ hw₀
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (0:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [h0 w₀ hw₀] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Φ p.1 p.2 τ)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => GG Φ τ p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hnegΦ : Tendsto (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (w₀, 0) :=
        continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have hbase := hcont.tendsto.comp hneg
      rwa [h0 w₀ hw₀] at hbase
    have hc : Tendsto (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ))
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hnegΦ.neg
    have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

theorem continuousAt_pdR_GG_zero {w₀ : ℝ} (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, 0) := by
  have hslice : (fun w' => GG Φ τ w' 0) = (fun w' => Φ w' 0 τ) := by
    funext w'; exact GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl
  have hval : Work.Cyl.pdR (GG Φ τ) w₀ 0 = 0 := by
    show deriv (fun w' => GG Φ τ w' 0) w₀ = 0
    rw [hslice]
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hpdR0 : Work.Cyl.pdR (fun w θ => Φ w θ τ) w₀ 0 = 0 := by
    show deriv (fun w' => Φ w' 0 τ) w₀ = 0
    have hev : (fun w' : ℝ => Φ w' 0 τ) =ᶠ[𝓝 w₀] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hw₀] with w' hw'
      exact h0 w' hw'
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  have hST : ({p : ℝ × ℝ | 0 ≤ p.2} ∪ {p : ℝ × ℝ | ¬ 0 ≤ p.2}) = Set.univ :=
    Set.union_compl_self _
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hw₀' : (0:ℝ) < w₀ := by linarith
  have h1 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝 (w₀, 0)) (𝓝 0) := by
      have hcont := (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0).tendsto
      rwa [hpdR0] at hcont
    have hc' : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)) (𝓝 0) :=
      hc.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | 0 ≤ p.2}))
    have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_nonneg (Φ := Φ) (τ := τ) hp).symm
    exact hc'.congr' hev
  have h2 : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2)
      (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
    have hneg : Tendsto (fun p : ℝ × ℝ => (p.1, -p.2)) (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0))
        (𝓝 (w₀, 0)) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, 0) :=
        continuousAt_fst.prodMk continuousAt_snd.neg
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ × ℝ | ¬ 0 ≤ p.2}))
      simpa using this
    have hbaseΦ : Tendsto (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      have hcont : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
          (w₀, 0) := continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀' hθ0
      have h1' := hcont.tendsto.comp hneg
      rwa [hpdR0] at h1'
    have hc : Tendsto (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        (𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)) (𝓝 0) := by
      simpa using hbaseΦ.neg
    have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
        =ᶠ[𝓝[{p : ℝ × ℝ | ¬ 0 ≤ p.2}] (w₀, 0)]
        (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) (not_le.mp hp)).symm
    exact hc.congr' hev
  have hcomb := tendsto_sup.mpr ⟨h1, h2⟩
  rw [← nhdsWithin_union, hST, nhdsWithin_univ] at hcomb
  rw [ContinuousAt, hval]
  exact hcomb

/-! ## Continuity of `GG`, `pdR GG`, `pdZ GG` at interior points -/

theorem continuousAt_GG_of_pos {w₀ θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ₀
  have hev : (fun p : ℝ × ℝ => Φ p.1 p.2 τ) =ᶠ[𝓝 (w₀, θ₀)]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀').congr hev

theorem continuousAt_GG_of_neg {w₀ θ₀ : ℝ} (hθ₀ : θ₀ < 0)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hθ₀
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hθ₀'' : |(-θ₀)| < Real.pi / 2 + 1 := by rwa [abs_neg]
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Φ p.1 (-p.2) τ) (w₀, θ₀) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Φ q.1 q.2 τ)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀)) := by
      simpa using (continuousAt_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀'')
    exact ContinuousAt.comp (x := (w₀, θ₀)) (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Φ q.1 q.2 τ) h1 hneg
  have hev : (fun p : ℝ × ℝ => -(Φ p.1 (-p.2) τ)) =ᶠ[𝓝 (w₀, θ₀)]
      (fun p : ℝ × ℝ => GG Φ τ p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdR_GG_of_pos {w₀ θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ₀
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) p.1 p.2) =ᶠ[𝓝 (w₀, θ₀)]
      (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀').congr hev

theorem continuousAt_pdR_GG_of_neg {w₀ θ₀ : ℝ} (hθ₀ : θ₀ < 0)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hθ₀
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hθ₀'' : |(-θ₀)| < Real.pi / 2 + 1 := by rwa [abs_neg]
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      (w₀, θ₀) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀)) := by
      simpa using (continuousAt_pdR_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀'')
    exact ContinuousAt.comp (x := (w₀, θ₀)) (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdR (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => -Work.Cyl.pdR (fun w θ => Φ w (-θ) τ) p.1 p.2)
      =ᶠ[𝓝 (w₀, θ₀)] (fun p : ℝ × ℝ => Work.Cyl.pdR (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdR_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.neg.congr hev

theorem continuousAt_pdZ_GG_of_pos {w₀ θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | 0 < p.2} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hθ₀
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 p.2) =ᶠ[𝓝 (w₀, θ₀)]
      (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_pos (Φ := Φ) (τ := τ) hp).symm
  exact (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀').congr hev

theorem continuousAt_pdZ_GG_of_neg {w₀ θ₀ : ℝ} (hθ₀ : θ₀ < 0)
    (hsm : ∀ w θ : ℝ, 0 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw₀ : 0 < w₀) (hθ₀' : |θ₀| < Real.pi / 2 + 1) :
    ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) (w₀, θ₀) := by
  have hnb : {p : ℝ × ℝ | p.2 < 0} ∈ 𝓝 (w₀, θ₀) :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hθ₀
  have hneg : ContinuousAt (fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀) :=
    continuousAt_fst.prodMk continuousAt_snd.neg
  have hθ₀'' : |(-θ₀)| < Real.pi / 2 + 1 := by rwa [abs_neg]
  have hcomp : ContinuousAt (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      (w₀, θ₀) := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2)
        ((fun p : ℝ × ℝ => (p.1, -p.2)) (w₀, θ₀)) := by
      simpa using (continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm hw₀ hθ₀'')
    exact ContinuousAt.comp (x := (w₀, θ₀)) (f := fun p : ℝ × ℝ => (p.1, -p.2))
      (g := fun q : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) q.1 q.2) h1 hneg
  have hev : (fun p : ℝ × ℝ => Work.Cyl.pdZ (fun w θ => Φ w θ τ) p.1 (-p.2))
      =ᶠ[𝓝 (w₀, θ₀)] (fun p : ℝ × ℝ => Work.Cyl.pdZ (GG Φ τ) p.1 p.2) := by
    filter_upwards [hnb] with p hp
    exact (pdZ_GG_of_neg (Φ := Φ) (τ := τ) hp).symm
  exact hcomp.congr hev

end Work.FTS.BSIdentP.Dev2
