import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Submission.PaperBand.McStraight
import Submission.PaperBand.BendSegments

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Local flow of the kernel field (Lemma `mc`, preimage side)

The kernel vector field `Vf f` of the shape operator is straightening
(`McStraight.Vf_deriv_parallel`).  Here we prove the local consequences by
following its integral curves (Picard–Lindelöf flows, Mathlib
`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`):

* a flow `α` through any interior point `x₀` with `Vf f x₀ ≠ 0` stays inside
  the interior of the strip where the field does not vanish
  (`exists_good_flow`);
* along the flow the field stays parallel to its initial value
  (`Vf_parallel_along_flow`), hence the flow curve is straight (`α` equals
  `x₀ + φ(t)•w₀`, `flow_on_line`), and the direction `w₀` lies in the kernel
  of the shape operator at every point of the flow
  (`w₀_mem_ker_along_flow`);
* consequently, near `x₀` the whole straight segment
  `{x₀ + s•w₀}` is a *kernel segment* (`kernel_segment_around`): each of its
  points satisfies `dN f (x₀ + s•w₀) w₀ = 0`.  By
  `BendSegments.affine_on_kernel_segment` / `normal_const_on_kernel_segment`
  the image of such a segment is a straight bend with constant normal — the
  local content of Lemma `mc`.
-/

noncomputable section
namespace Submission.PaperBand

/-! ## One-dimensional analysis helpers -/

/-- The vector `(v₂, −v₁)` perpendicular to `v = (v₁, v₂)` in the plane. -/
abbrev perp2 (v : ℝ²) : ℝ² := !₂[-v 1, v 0]

/-- A vector is orthogonal to its perpendicular. -/
lemma inner_self_perp2 (v : ℝ²) : inner ℝ v (perp2 v) = 0 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

/-- A vector orthogonal to the perpendicular of a nonzero vector `w` is a
scalar multiple of `w`. -/
lemma smul_of_inner_perp2_eq_zero {u w : ℝ²} (hw : w ≠ 0)
    (h : inner ℝ u (perp2 w) = 0) : ∃ c : ℝ, u = c • w := by
  rw [PiLp.inner_apply] at h
  have hsum : -(u 0 * w 1) + u 1 * w 0 = 0 := by
    simpa [Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc] using h
  have hdet : u 0 * w 1 = u 1 * w 0 := by linarith
  exact exists_smul_of_det_zero hw hdet

/-- Derivative of an inner product with a constant second argument. -/
lemma hasDerivAt_inner_const {u : ℝ → ℝ²} {v : ℝ²} {w : ℝ²} {t : ℝ}
    (hu : HasDerivAt u v t) :
    HasDerivAt (fun s : ℝ => inner ℝ (u s) w) (inner ℝ v w) t := by
  have h := HasDerivAt.inner ℝ hu (hasDerivAt_const t w)
  simpa using h

/-- A quotient of two differentiable functions has zero derivative when the
derivatives are proportional (with the same factor). -/
lemma hasDerivAt_div_zero_of_par {B A : ℝ → ℝ} {b a : ℝ} {s : ℝ}
    (hB : HasDerivAt B b s) (hA : HasDerivAt A a s) (hAn : A s ≠ 0)
    (hpar : b * A s = B s * a) : HasDerivAt (fun t : ℝ => B t / A t) 0 s := by
  have hdiv : HasDerivAt (fun t : ℝ => B t / A t) ((b * A s - B s * a) / (A s)^2) s :=
    hB.div hA hAn
  have hval : (b * A s - B s * a) / (A s)^2 = 0 := by
    have hnum : b * A s - B s * a = 0 := by linarith
    rw [hnum, zero_div]
  simpa [hval] using hdiv

/-- If a differentiable curve has derivative everywhere parallel to itself,
then near 0 it stays parallel to its value at 0. -/
lemma direction_const_of_parallel {u u1 : ℝ → ℝ²} {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt u (u1 t) t)
    (hpar : ∀ t ∈ Set.Ioo (-ε) ε, ∃ l : ℝ, u1 t = l • u t)
    (hu0 : u 0 ≠ 0) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (-δ) δ, ∃ c : ℝ, u t = c • u 0 := by
  let w₀ : ℝ² := u 0
  let p : ℝ² := perp2 w₀
  let A : ℝ → ℝ := fun s => inner ℝ (u s) w₀
  let B : ℝ → ℝ := fun s => inner ℝ (u s) p
  have hA0 : A 0 ≠ 0 := by
    dsimp [A, w₀]
    intro hz
    apply hu0
    exact inner_self_eq_zero.mp hz
  have hAcont0 : ContinuousAt A 0 := by
    have hudiff0 : DifferentiableAt ℝ u 0 :=
      (hu 0 (by constructor <;> linarith [hε])).differentiableAt
    have hinner : DifferentiableAt ℝ (fun s : ℝ => inner ℝ (u s) w₀) 0 :=
      DifferentiableAt.inner ℝ hudiff0 (differentiableAt_const w₀)
    simpa [A] using hinner.continuousAt
  have hEv : ∀ᶠ s in 𝓝 (0 : ℝ), A s ≠ 0 := hAcont0.eventually_ne hA0
  rcases Metric.eventually_nhds_iff_ball.mp hEv with ⟨η, hη0, hη⟩
  have hAne : ∀ s ∈ Set.Ioo (-η) η, A s ≠ 0 := by
    intro s hs
    have hsI : s ∈ Set.Ioo (0 - η) (0 + η) := by
      rw [Set.mem_Ioo] at hs ⊢
      constructor <;> linarith
    exact hη s (by simpa [Real.ball_eq_Ioo] using hsI)
  let δ : ℝ := min (ε / 2) (η / 2)
  have hδ0 : 0 < δ := by dsimp [δ]; exact lt_min (by positivity) (by positivity)
  have hε2 : ε / 2 < ε := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hε]
  have hη2 : η / 2 < η := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hη0]
  have hδε : δ < ε := by dsimp [δ]; exact lt_of_le_of_lt (min_le_left _ _) hε2
  have hδη : δ < η := by dsimp [δ]; exact lt_of_le_of_lt (min_le_right _ _) hη2
  let C : ℝ → ℝ := fun s => B s / A s
  have hCzero : ∀ s ∈ Set.Icc (-δ) δ, HasDerivAt C 0 s := by
    intro s hs
    have hs' : -δ ≤ s ∧ s ≤ δ := Set.mem_Icc.mp hs
    have hsI : s ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hsA : s ∈ Set.Ioo (-η) η := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    rcases hpar s hsI with ⟨l, hl⟩
    have hul : HasDerivAt u (l • u s) s := by
      have hh := hu s hsI
      rw [hl] at hh
      exact hh
    have hA' : HasDerivAt A (l * A s) s := by
      have hinn := hasDerivAt_inner_const (u := u) (v := l • u s) (w := w₀) (t := s) hul
      have hAval : inner ℝ (l • u s) w₀ = l * inner ℝ (u s) w₀ := by
        rw [inner_smul_left]
        simp
      have hA2 : HasDerivAt (fun s : ℝ => inner ℝ (u s) w₀) (l * inner ℝ (u s) w₀) s := by
        simpa [hAval] using hinn
      simpa [A] using hA2
    have hB' : HasDerivAt B (l * B s) s := by
      have hinn := hasDerivAt_inner_const (u := u) (v := l • u s) (w := p) (t := s) hul
      have hBval : inner ℝ (l • u s) p = l * inner ℝ (u s) p := by
        rw [inner_smul_left]
        simp
      have hB2 : HasDerivAt (fun s : ℝ => inner ℝ (u s) p) (l * inner ℝ (u s) p) s := by
        simpa [hBval] using hinn
      simpa [B] using hB2
    have hparAB : (l * B s) * A s = B s * (l * A s) := by ring
    simpa [C] using (hasDerivAt_div_zero_of_par hB' hA' (hAne s hsA) hparAB)
  have hCcont : ContinuousOn C (Set.Icc (-δ) δ) := by
    intro s hs
    exact (hCzero s hs).continuousAt.continuousWithinAt
  have hCder : ∀ s ∈ Set.Ico (-δ) δ, HasDerivWithinAt C 0 (Set.Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (-δ) δ := Set.Ico_subset_Icc_self hs
    exact (hCzero s hsIcc).hasDerivWithinAt
  have hCconst := constant_of_has_deriv_right_zero (a := -δ) (b := δ) hCcont hCder
  have hC0 : C 0 = 0 := by
    dsimp [C, B, A, w₀, p]
    rw [inner_self_perp2, zero_div]
  refine ⟨δ, hδ0, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc (-δ) δ := by
    rcases Set.mem_Ioo.mp ht with ⟨h1, h2⟩
    rw [Set.mem_Icc]
    constructor <;> linarith
  have ht0 : C 0 = C (-δ) := hCconst 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hδ0])
  have hCt : C t = 0 := by
    calc C t = C (-δ) := hCconst t htIcc
         _ = C 0 := ht0.symm
         _ = 0 := hC0
  have hBt : B t = 0 := by
    rcases Set.mem_Ioo.mp ht with ⟨hlo, hhi⟩
    have hAne' : A t ≠ 0 := hAne t (Set.mem_Ioo.mpr (by constructor <;> linarith))
    have hCt' : B t / A t = 0 := by simpa [C] using hCt
    calc
      B t = (B t / A t) * A t := by field_simp [hAne']
      _ = 0 * A t := by rw [hCt']
      _ = 0 := by ring
  have hBt' : inner ℝ (u t) (perp2 (u 0)) = 0 := by
    simpa [B, p, w₀] using hBt
  exact smul_of_inner_perp2_eq_zero hu0 hBt'

/-- A scalar function with zero derivative on an interval around 0 and value 0
at 0 is identically zero on the whole interval. -/
lemma eq_zero_of_hasDerivAt_zero_of_eq_zero {f : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt f 0 t) (hf0 : f 0 = 0) :
    ∀ t ∈ Set.Ioo (-ε) ε, f t = 0 := by
  intro t ht
  rcases Set.mem_Ioo.mp ht with ⟨h1, h2⟩
  have hte : |t| < ε := abs_lt.mpr ⟨h1, h2⟩
  let η : ℝ := (ε + |t|) / 2
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by
    dsimp [η]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have htη : |t| < η := by
    dsimp [η]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have htIcc : t ∈ Set.Icc (-η) η := by
    rw [Set.mem_Icc]
    rcases abs_le.mp (le_of_lt htη) with ⟨htle, hnegle⟩
    constructor
    · exact htle
    · exact hnegle
  have hcont : ContinuousOn f (Set.Icc (-η) η) := by
    intro s hs
    rcases Set.mem_Icc.mp hs with ⟨hs1, hs2⟩
    have hs' : s ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact (hf s hs').continuousAt.continuousWithinAt
  have hder : ∀ x ∈ Set.Ico (-η) η, HasDerivWithinAt f 0 (Set.Ici x) x := by
    intro x hx
    rcases Set.mem_Ico.mp hx with ⟨hx1, hx2⟩
    have hx' : x ∈ Set.Ioo (-ε) ε := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact (hf x hx').hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero (a := -η) (b := η) hcont hder
  have hfneg : f (-η) = 0 := by
    have h0 := hconst 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
    exact h0.symm.trans hf0
  exact (hconst t htIcc).trans hfneg

/-- If a curve `γ` starts at `x₀` and its derivative is everywhere parallel to
a fixed nonzero vector `w₀`, then `γ` stays on the affine line through `x₀`
parallel to `w₀`. -/
lemma curve_on_line_of_deriv_parallel {γ u : ℝ → ℝ²} {w₀ x₀ : ℝ²} {ε : ℝ} (hε : 0 < ε)
    (hγ0 : γ 0 = x₀) (hder : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt γ (u t) t)
    (hpar : ∀ t ∈ Set.Ioo (-ε) ε, ∃ c : ℝ, u t = c • w₀) (hw₀ : w₀ ≠ 0) :
    ∀ t ∈ Set.Ioo (-ε) ε, ∃ c : ℝ, γ t - x₀ = c • w₀ := by
  intro t₀ ht₀
  let p : ℝ² := perp2 w₀
  let D : ℝ → ℝ := fun t => inner ℝ (γ t - x₀) p
  have hDzero : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt D 0 t := by
    intro t ht
    have hγ' : HasDerivAt (fun s : ℝ => γ s - x₀) (u t) t := by
      change HasDerivAt ((fun s : ℝ => γ s) - (fun _ : ℝ => x₀)) (u t) t
      simpa using (hder t ht).sub (hasDerivAt_const t x₀)
    have hinn := hasDerivAt_inner_const (u := fun s : ℝ => γ s - x₀) (v := u t) (w := p) (t := t)
      hγ'
    rcases hpar t ht with ⟨c, hc⟩
    have hup : inner ℝ (u t) p = 0 := by
      rw [hc]
      rw [inner_smul_left]
      rw [inner_self_perp2]
      simp
    simpa [D, hup] using hinn
  have hD0 : D 0 = 0 := by
    dsimp [D]
    rw [hγ0]
    simp
  have hDt : D t₀ = 0 := eq_zero_of_hasDerivAt_zero_of_eq_zero hε hDzero hD0 t₀ ht₀
  have hu : inner ℝ (γ t₀ - x₀) (perp2 w₀) = 0 := by
    simpa [D] using hDt
  exact smul_of_inner_perp2_eq_zero hw₀ hu


/-- Membership in the API's flow interval `Ioo (0-ε) (0+ε)` is the same as
membership in the symmetric interval `Ioo (-ε) ε`. -/
lemma mem_Ioo_symm_zero {ε t : ℝ} : t ∈ Set.Ioo (0 - ε) (0 + ε) ↔ t ∈ Set.Ioo (-ε) ε := by
  rw [Set.mem_Ioo, Set.mem_Ioo]
  rw [show (0 : ℝ) - ε = -ε by ring]
  rw [show (0 : ℝ) + ε = ε by ring]

/-- In `ℝ` the ball of radius `ε` around 0 is the symmetric interval. -/
lemma mem_ball_zero_iff_Ioo {ε t : ℝ} : t ∈ Metric.ball (0 : ℝ) ε ↔ t ∈ Set.Ioo (-ε) ε := by
  rw [Real.ball_eq_Ioo]
  exact mem_Ioo_symm_zero

/-! ## Local flows of the kernel field -/

/-- A local flow of the kernel field through an interior point with nonzero
field value exists and stays (on a smaller interval) inside the interior of
the strip where the field does not vanish. -/
lemma exists_good_flow {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x₀ : ℝ²}
    (hx₀ : x₀ ∈ stripInterior) (hw₀ : Vf f x₀ ≠ 0) :
    ∃ α : ℝ → ℝ², α 0 = x₀ ∧ ∃ ε > 0,
      (∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (Vf f (α t)) t) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, α t ∈ stripInterior ∧ Vf f (α t) ≠ 0) := by
  rcases ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (f := Vf f) (contDiffAt_Vf_one hf x₀ hx₀) 0 with ⟨α, hα0, ε₁, hε₁, hα⟩
  have hα0mem : α 0 ∈ stripInterior := by simpa [hα0] using hx₀
  have hαcont0 : ContinuousAt α 0 := (hα 0 (by constructor <;> linarith [hε₁])).continuousAt
  have hU : {t : ℝ | α t ∈ stripInterior} ∈ 𝓝 (0 : ℝ) :=
    hαcont0.preimage_mem_nhds (IsOpen.mem_nhds stripInterior_isOpen hα0mem)
  have hV : {t : ℝ | Vf f (α t) ≠ 0} ∈ 𝓝 (0 : ℝ) := by
    have hcontV0 : ContinuousAt (fun t : ℝ => Vf f (α t)) 0 :=
      (continuousAt_Vf hf (α 0) hα0mem).comp hαcont0
    have hw₀' : Vf f (α 0) ≠ 0 := by simpa [hα0] using hw₀
    exact hcontV0.preimage_mem_nhds (isOpen_ne.mem_nhds hw₀')
  rcases Metric.mem_nhds_iff.mp hU with ⟨η₁, hη₁0, hη₁⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨η₂, hη₂0, hη₂⟩
  let η : ℝ := min η₁ η₂
  have hη0 : 0 < η := by dsimp [η]; exact lt_min hη₁0 hη₂0
  have hη₁' : η ≤ η₁ := by dsimp [η]; exact min_le_left _ _
  have hη₂' : η ≤ η₂ := by dsimp [η]; exact min_le_right _ _
  let ε : ℝ := min (ε₁ / 2) (η / 2)
  have hε0 : 0 < ε := by dsimp [ε]; exact lt_min (by positivity) (by positivity)
  have hεη : ε < η := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_right _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hη0])
  have hε₁' : ε < ε₁ := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hε₁])
  refine ⟨α, hα0, ε, hε0, ?_, ?_⟩
  · intro t ht
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    have htε₁ : t ∈ Set.Ioo (-ε₁) ε₁ := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact hα t (mem_Ioo_symm_zero.mpr htε₁)
  · intro t ht
    have htη' : t ∈ Set.Ioo (-η) η := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
      constructor <;> linarith
    have htη : t ∈ Metric.ball (0 : ℝ) η := mem_ball_zero_iff_Ioo.mpr htη'
    have ht₁ : t ∈ Metric.ball (0 : ℝ) η₁ := by
      rw [Metric.mem_ball] at htη ⊢
      exact htη.trans_le hη₁'
    have ht₂ : t ∈ Metric.ball (0 : ℝ) η₂ := by
      rw [Metric.mem_ball] at htη ⊢
      exact htη.trans_le hη₂'
    exact ⟨by simpa using hη₁ ht₁, by simpa using hη₂ ht₂⟩

/-- **Kernel flow is straight**: along the local flow of the kernel field the
field stays parallel to its initial value (so the flow curve is a straight
segment of the flat band), and the initial direction lies in the kernel of the
shape operator at every point of the flow. -/
lemma flow_kernel_straight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x₀ : ℝ²}
    (hx₀ : x₀ ∈ stripInterior) (hw₀ : Vf f x₀ ≠ 0) :
    ∃ α : ℝ → ℝ², α 0 = x₀ ∧ ∃ δ > 0,
      ∀ t ∈ Set.Ioo (-δ) δ,
        HasDerivAt α (Vf f (α t)) t ∧ α t ∈ stripInterior ∧
        (∃ c : ℝ, Vf f (α t) = c • Vf f x₀) ∧ dN f (α t) (Vf f x₀) = 0 := by
  let w₀ : ℝ² := Vf f x₀
  rcases exists_good_flow hf hx₀ hw₀ with ⟨α, hα0, ε, hε, hα, hgood⟩
  let u : ℝ → ℝ² := fun t => Vf f (α t)
  let u1 : ℝ → ℝ² := fun t => fderiv ℝ (Vf f) (α t) (Vf f (α t))
  have hu : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt u (u1 t) t := by
    intro t ht
    have hd : DifferentiableAt ℝ (Vf f) (α t) := differentiableAt_Vf hf (α t) (hgood t ht).1
    change HasDerivAt (Vf f ∘ α) (fderiv ℝ (Vf f) (α t) (Vf f (α t))) t
    exact hd.hasFDerivAt.comp_hasDerivAt (x := t) (hα t ht)
  have hpar : ∀ t ∈ Set.Ioo (-ε) ε, ∃ l : ℝ, u1 t = l • u t := by
    intro t ht
    rcases Vf_deriv_parallel hf (α t) (hgood t ht).1 (hgood t ht).2 with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    simpa [u, u1] using hl
  have hu0 : u 0 ≠ 0 := by
    simpa [u, hα0] using hw₀
  rcases direction_const_of_parallel (u := u) (u1 := u1) (ε := ε) hε hu hpar hu0 with ⟨δ₀, hδ₀, hdir⟩
  let δ : ℝ := min δ₀ ε
  have hδ0 : 0 < δ := by dsimp [δ]; exact lt_min hδ₀ hε
  have hδle₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left _ _
  have hδleε : δ ≤ ε := by dsimp [δ]; exact min_le_right _ _
  refine ⟨α, hα0, δ, hδ0, ?_⟩
  intro t ht
  have htδ₀ : t ∈ Set.Ioo (-δ₀) δ₀ := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    constructor <;> linarith
  have htε : t ∈ Set.Ioo (-ε) ε := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    constructor <;> linarith
  have hd0 : HasDerivAt α (Vf f (α t)) t := hα t htε
  rcases hdir t htδ₀ with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    intro hz
    have : u t = 0 := by simpa [hz] using hc
    have : Vf f (α t) = 0 := by simpa [u] using this
    exact (hgood t htε).2 this
  have hu0eq : u 0 = w₀ := by dsimp [u, w₀]; rw [hα0]
  have hparc : u t = c • w₀ := by simpa [hu0eq] using hc
  have hrel : Vf f (α t) = c • w₀ := by simpa [u] using hparc
  have hkernel : dN f (α t) w₀ = 0 := by
    have hker0 : dN f (α t) (Vf f (α t)) = 0 := Vf_mem_ker hf (α t) (hgood t htε).1
    have hmain : dN f (α t) (c • w₀) = 0 := by
      rw [← hrel]
      exact hker0
    rw [map_smul] at hmain
    exact (smul_eq_zero.mp hmain).resolve_left hc0
  refine ⟨hd0, (hgood t htε).1, ⟨c, hrel⟩, hkernel⟩


/-! ## Reparameterizing the flow leaf as a straight segment -/

/-- The signed coordinate of `γ t - x₀` along the nonzero vector `w₀`:
`coord γ x₀ w₀ t` is the scalar `c` with `γ t - x₀ = c • w₀` whenever the
curve stays on the line. -/
def coord (γ : ℝ → ℝ²) (x₀ w₀ : ℝ²) (t : ℝ) : ℝ :=
  inner ℝ (γ t - x₀) w₀ / ‖w₀‖ ^ 2

/-- If `γ t - x₀` is parallel to `w₀` then the coordinate `coord γ x₀ w₀ t`
realizes the proportionality. -/
lemma coord_smul_of_parallel {γ : ℝ → ℝ²} {x₀ w₀ : ℝ²} {t : ℝ} (hw : w₀ ≠ 0)
    (hl : ∃ c : ℝ, γ t - x₀ = c • w₀) :
    γ t = x₀ + coord γ x₀ w₀ t • w₀ := by
  rcases hl with ⟨c, hc⟩
  have hcs : c = coord γ x₀ w₀ t := by
    have hinner := congrArg (fun z : ℝ² => inner ℝ z w₀) hc
    have hrhs : inner ℝ (c • w₀) w₀ = c * inner ℝ w₀ w₀ := by
      rw [inner_smul_left]
      simp
    have hmain : inner ℝ (γ t - x₀) w₀ = c * inner ℝ w₀ w₀ := by
      simpa [hrhs] using hinner
    have hn : inner ℝ w₀ w₀ = ‖w₀‖ ^ 2 := real_inner_self_eq_norm_sq w₀
    have hnorm : ‖w₀‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
    calc
      c = (c * inner ℝ w₀ w₀) / inner ℝ w₀ w₀ := by field_simp [hn, hnorm]
      _ = inner ℝ (γ t - x₀) w₀ / inner ℝ w₀ w₀ := by rw [hmain]
      _ = inner ℝ (γ t - x₀) w₀ / ‖w₀‖ ^ 2 := by rw [hn]
  calc
    γ t = x₀ + (γ t - x₀) := by abel
    _ = x₀ + c • w₀ := by rw [hc]
    _ = x₀ + coord γ x₀ w₀ t • w₀ := by rw [hcs]

/-- Derivative of the coordinate function along a differentiable curve. -/
lemma hasDerivAt_coord {γ u : ℝ → ℝ²} {x₀ w₀ : ℝ²} {t : ℝ} (hw : w₀ ≠ 0)
    (hγ : HasDerivAt γ (u t) t) :
    HasDerivAt (fun s : ℝ => coord γ x₀ w₀ s) (inner ℝ (u t) w₀ / ‖w₀‖ ^ 2) t := by
  have hA : HasDerivAt (fun s : ℝ => inner ℝ (γ s) w₀) (inner ℝ (u t) w₀) t := by
    have h := HasDerivAt.inner ℝ hγ (hasDerivAt_const t w₀)
    simpa using h
  have hc : HasDerivAt (fun _ : ℝ => inner ℝ x₀ w₀) 0 t := hasDerivAt_const t (inner ℝ x₀ w₀)
  have hG : HasDerivAt (fun s : ℝ => inner ℝ (γ s) w₀ - inner ℝ x₀ w₀) (inner ℝ (u t) w₀ - 0) t := by
    exact hA.sub hc
  let cst : ℝ := ‖w₀‖ ^ 2
  have hcne : cst ≠ 0 := by
    dsimp [cst]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hcst : HasDerivAt (fun _ : ℝ => cst) 0 t := hasDerivAt_const t cst
  have hdiv0 : HasDerivAt (fun s : ℝ => (inner ℝ (γ s) w₀ - inner ℝ x₀ w₀) / cst)
      (((inner ℝ (u t) w₀ - 0) * cst - (inner ℝ (γ t) w₀ - inner ℝ x₀ w₀) * 0) / cst ^ 2) t := by
    exact HasDerivAt.div hG hcst hcne
  have hfun : (fun s : ℝ => (inner ℝ (γ s) w₀ - inner ℝ x₀ w₀) / cst) =
      (fun s : ℝ => inner ℝ (γ s - x₀) w₀ / ‖w₀‖ ^ 2) := by
    funext s
    dsimp [cst]
    rw [inner_sub_left]
  have hval : ((inner ℝ (u t) w₀ - 0) * cst - (inner ℝ (γ t) w₀ - inner ℝ x₀ w₀) * 0) / cst ^ 2 =
      inner ℝ (u t) w₀ / ‖w₀‖ ^ 2 := by
    dsimp [cst]
    field_simp [hcne]
    ring
  have hres : HasDerivAt (fun s : ℝ => inner ℝ (γ s - x₀) w₀ / ‖w₀‖ ^ 2)
      (((inner ℝ (u t) w₀ - 0) * cst - (inner ℝ (γ t) w₀ - inner ℝ x₀ w₀) * 0) / cst ^ 2) t := by
    rw [hfun] at hdiv0
    exact hdiv0
  have hmain : HasDerivAt (fun s : ℝ => inner ℝ (γ s - x₀) w₀ / ‖w₀‖ ^ 2)
      (inner ℝ (u t) w₀ / ‖w₀‖ ^ 2) t := by
    rw [hval] at hres
    exact hres
  simpa [coord] using hmain

/-- **Local kernel segment**: near an interior point `x₀` with nonzero kernel
field, the whole straight segment `{x₀ + s • w₀}` (with `w₀ = Vf f x₀`) stays
inside the interior of the strip and is a *kernel segment*: its direction
`w₀` is in the kernel of the shape operator at every point of the segment. -/
lemma kernel_segment_around {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x₀ : ℝ²}
    (hx₀ : x₀ ∈ stripInterior) (hw₀ : Vf f x₀ ≠ 0) :
    ∃ δ > (0 : ℝ),
      (∀ s ∈ Set.Ioo (-δ) δ,
        x₀ + s • (Vf f x₀) ∈ stripInterior ∧
        dN f (x₀ + s • (Vf f x₀)) (Vf f x₀) = 0) := by
  rcases flow_kernel_straight hf hx₀ hw₀ with ⟨α, hα0, δf, hδf, hprop⟩
  let u : ℝ → ℝ² := fun t => Vf f (α t)
  have hu' : ∀ t ∈ Set.Ioo (-δf) δf, HasDerivAt α (u t) t := by
    intro t ht
    simpa [u] using (hprop t ht).1
  have hpar : ∀ t ∈ Set.Ioo (-δf) δf, ∃ c : ℝ, u t = c • (Vf f x₀) := by
    intro t ht
    rcases (hprop t ht).2.2.1 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    change Vf f (α t) = c • (Vf f x₀)
    exact hc
  have hline : ∀ t ∈ Set.Ioo (-δf) δf, ∃ c : ℝ, α t - x₀ = c • (Vf f x₀) :=
    curve_on_line_of_deriv_parallel (γ := α) (u := u) (w₀ := Vf f x₀) (x₀ := x₀)
      (ε := δf) hδf hα0 hu' hpar hw₀
  -- the coordinate function along Vf f x₀ and its derivative
  let φ : ℝ → ℝ := fun s => coord α x₀ (Vf f x₀) s
  have hφder : ∀ t ∈ Set.Ioo (-δf) δf,
      HasDerivAt φ (inner ℝ (u t) (Vf f x₀) / ‖Vf f x₀‖ ^ 2) t := by
    intro t ht
    have hd := hasDerivAt_coord (γ := α) (u := u) (x₀ := x₀) (w₀ := Vf f x₀) (t := t) hw₀
      (hu' t ht)
    simpa [φ] using hd
  have hφeq : ∀ t ∈ Set.Ioo (-δf) δf, α t = x₀ + φ t • (Vf f x₀) := by
    intro t ht
    dsimp [φ]
    exact coord_smul_of_parallel hw₀ (hline t ht)
  have hφ0 : φ 0 = 0 := by
    dsimp [φ, coord]
    rw [hα0]
    simp
  have hw₀nz : ‖Vf f x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hw₀
  have hnorm2 : (0 : ℝ) < ‖Vf f x₀‖ ^ 2 := sq_pos_of_ne_zero hw₀nz
  -- u is differentiable at 0, so G := fun t => inner (u t) (Vf f x₀) is continuous at 0
  have hudiff0 : DifferentiableAt ℝ u 0 := by
    have hmem : α 0 ∈ stripInterior := by simpa [hα0] using hx₀
    have hdV : DifferentiableAt ℝ (Vf f) (α 0) := differentiableAt_Vf hf (α 0) hmem
    have hdα : DifferentiableAt ℝ α 0 := (hu' 0 (by constructor <;> linarith [hδf])).differentiableAt
    change DifferentiableAt ℝ (Vf f ∘ α) 0
    exact hdV.comp (x := 0) hdα
  have hGcont0 : ContinuousAt (fun t : ℝ => inner ℝ (u t) (Vf f x₀)) 0 := by
    have hinner : DifferentiableAt ℝ (fun t : ℝ => inner ℝ (u t) (Vf f x₀)) 0 :=
      DifferentiableAt.inner ℝ hudiff0 (differentiableAt_const (Vf f x₀))
    simpa using hinner.continuousAt
  have hG0 : 0 < inner ℝ (u 0) (Vf f x₀) := by
    have hu0w : u 0 = Vf f x₀ := by
      dsimp [u]
      rw [hα0]
    rw [hu0w]
    rw [real_inner_self_eq_norm_sq]
    exact hnorm2
  have hGpos : {t : ℝ | 0 < inner ℝ (u t) (Vf f x₀)} ∈ 𝓝 (0 : ℝ) :=
    hGcont0.preimage_mem_nhds (isOpen_Ioi.mem_nhds hG0)
  rcases Metric.eventually_nhds_iff_ball.mp hGpos with ⟨ηG, hηG0, hηG⟩
  -- pick η with η < δf and G positive on the ball of radius ηG
  let η : ℝ := min (δf / 2) (ηG / 2)
  have hη0 : 0 < η := by dsimp [η]; exact lt_min (by positivity) (by positivity)
  have hηδ : η < δf := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_left _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hδf])
  have hηηG : η < ηG := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_right _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hηG0])
  -- derivative of φ is positive on (-η, η)
  have hLpos : ∀ t ∈ Set.Ioo (-η) η, 0 < inner ℝ (u t) (Vf f x₀) / ‖Vf f x₀‖ ^ 2 := by
    intro t ht
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    have htG : t ∈ Metric.ball (0 : ℝ) ηG := mem_ball_zero_iff_Ioo.mpr (by
      rw [Set.mem_Ioo]
      constructor <;> linarith)
    have hpos : 0 < inner ℝ (u t) (Vf f x₀) := hηG t htG
    exact div_pos hpos hnorm2
  have hφcont : ContinuousOn φ (Set.Icc (-η) η) := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-δf) δf := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp ht with ⟨ht1, ht2⟩
      constructor <;> linarith
    exact (hφder t ht').continuousAt.continuousWithinAt
  have hderivpos : ∀ t ∈ interior (Set.Icc (-η) η), 0 < deriv φ t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-η) η := by
      rw [interior_Icc] at ht
      exact ht
    have ht'' : t ∈ Set.Ioo (-δf) δf := by
      rw [Set.mem_Ioo]
      rw [Set.mem_Ioo] at ht'
      constructor <;> linarith
    have hder : deriv φ t = inner ℝ (u t) (Vf f x₀) / ‖Vf f x₀‖ ^ 2 :=
      (hφder t ht'').deriv
    rw [hder]
    exact hLpos t ht'
  have hmono : StrictMonoOn φ (Set.Icc (-η) η) :=
    strictMonoOn_of_deriv_pos (convex_Icc (-η) η) hφcont hderivpos
  have hφneg : φ (-η) < 0 := by
    have hlt : φ (-η) < φ 0 := hmono (a := -η) (b := 0)
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by linarith)
    rwa [hφ0] at hlt
  have hφpos : 0 < φ η := by
    have hlt : φ 0 < φ η := hmono (a := 0) (b := η)
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by linarith)
    rwa [hφ0] at hlt
  -- output interval
  let δ : ℝ := min (φ η) (-φ (-η))
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith [hφpos]) (by linarith [hφneg])
  refine ⟨δ, hδ0, ?_⟩
  intro s hs
  have hδ1 : δ ≤ φ η := by dsimp [δ]; exact min_le_left _ _
  have hδ2 : δ ≤ -φ (-η) := by dsimp [δ]; exact min_le_right _ _
  have hs1 : s < φ η := lt_of_lt_of_le hs.2 hδ1
  have hs2 : φ (-η) < s := by
    have : -δ < s := hs.1
    exact lt_of_le_of_lt (by linarith) this
  have hmono' : MonotoneOn φ (Set.Icc (-η) η) := hmono.monotoneOn
  have himage : φ '' Set.Icc (-η) η = Set.Icc (φ (-η)) (φ η) :=
    ContinuousOn.image_Icc_of_monotoneOn (le_of_lt (by linarith [hη0])) hφcont hmono'
  have hsI : s ∈ Set.Icc (φ (-η)) (φ η) := by
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hsIn : s ∈ φ '' Set.Icc (-η) η := by
    rw [himage]
    exact hsI
  rcases hsIn with ⟨t, htIcc, hφt⟩
  have ht' : t ∈ Set.Ioo (-δf) δf := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Icc.mp htIcc with ⟨ht1, ht2⟩
    constructor <;> linarith [hηδ]
  have hαt : α t = x₀ + s • (Vf f x₀) := by
    have hφeqt := hφeq t ht'
    rw [hφt] at hφeqt
    exact hφeqt
  have hint : x₀ + s • (Vf f x₀) ∈ stripInterior := by
    rw [← hαt]
    exact (hprop t ht').2.1
  have hker : dN f (x₀ + s • (Vf f x₀)) (Vf f x₀) = 0 := by
    rw [← hαt]
    exact (hprop t ht').2.2.2
  exact ⟨hint, hker⟩


/-- Vector re-combination: `(f - ε•c) + (s+ε)•c = f + s•c`. -/
lemma affine_recombine1 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E) (c : E) (s ε : ℝ) :
    (f - ε • c) + (s + ε) • c = f + s • c := by
  rw [add_smul]
  abel

/-- Vector re-combination: `f + ε•c + (s-ε)•c = f + s•c`. -/
lemma affine_recombine2 {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E) (c : E) (s ε : ℝ) :
    f + ε • c + (s - ε) • c = f + s • c := by
  rw [sub_smul]
  abel

/-- On a kernel segment through `x₀` (with `0 ∈ [A,B]`), the image of the
segment is affine in the direction `v` from `x₀`. -/
lemma affine_from_center {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ v : ℝ²} {A B : ℝ} (hAB : A ≤ 0) (h0B : 0 ≤ B)
    (hseg : ∀ s ∈ Set.Icc A B, x₀ + s • v ∈ stripInterior)
    (hk : ∀ s ∈ Set.Icc A B, dN f (x₀ + s • v) v = 0) :
    ∀ s ∈ Set.Icc A B, f (x₀ + s • v) = f x₀ + s • (fderiv ℝ f x₀ v) := by
  intro s hs
  rcases lt_or_ge s 0 with hsneg | hsnn
  · -- s < 0 : apply over [A, 0]
    have hs0 : s ∈ Set.Icc A 0 := by
      rw [Set.mem_Icc]
      rcases Set.mem_Icc.mp hs with ⟨h1, h2⟩
      constructor <;> linarith
    have hseg0 : ∀ u ∈ Set.Icc A 0, x₀ + u • v ∈ stripInterior := by
      intro u hu
      exact hseg u (by
        rw [Set.mem_Icc]
        rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
        constructor <;> linarith)
    have hk0 : ∀ u ∈ Set.Icc A 0, dN f (x₀ + u • v) v = 0 := by
      intro u hu
      exact hk u (by
        rw [Set.mem_Icc]
        rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
        constructor <;> linarith)
    let c : ℝ³ := fderiv ℝ f (x₀ + A • v) v
    have hmains := affine_on_kernel_segment hf (x := x₀) (v := v) (A := A) (B := 0) hseg0 hk0 s hs0
    have hm0 := affine_on_kernel_segment hf (x := x₀) (v := v) (A := A) (B := 0) hseg0 hk0 0
      (by rw [Set.mem_Icc]; constructor; exact hAB; rfl)
    have hc0 : c = fderiv ℝ f x₀ v := by
      have ht := tangent_const_on_kernel_segment hf (x := x₀) (v := v) (A := A) (B := 0) hseg0 hk0 0
        (by rw [Set.mem_Icc]; constructor; exact hAB; rfl)
      -- ht : fderiv f x₀ v = fderiv f (x₀ + A•v) v
      simpa [c] using ht.symm
    let t : ℝ := -A
    have htpos : 0 ≤ t := by dsimp [t]; linarith
    have hleft : f (x₀ + A • v) = f x₀ - t • c := by
      -- from hm0 : f x₀ = f(x₀+A•v) + (0-A)•c
      have hm0' : f x₀ = f (x₀ + A • v) + t • c := by
        -- (0 - A) = t : since t := -A
        simpa [c, t, sub_eq_add_neg] using hm0
      -- f(x₀ + A v) = f x₀ - t c : a = b + c implies b = a - c
      calc
        f (x₀ + A • v) = f (x₀ + A • v) + t • c - t • c := by abel
        _ = f x₀ - t • c := by
          rw [hm0']
    calc
      f (x₀ + s • v) = f (x₀ + A • v) + (s - A) • c := by
        simpa [c, sub_eq_add_neg] using hmains
      _ = (f x₀ - t • c) + (s + t) • c := by
        have : s - A = s + t := by dsimp [t]; ring
        rw [hleft, this]
      _ = f x₀ + s • c := affine_recombine1 (f x₀) c s t
      _ = f x₀ + s • (fderiv ℝ f x₀ v) := by rw [hc0]
  · -- 0 ≤ s : apply over [0, B]
    have hs0 : s ∈ Set.Icc 0 B := by
      rw [Set.mem_Icc]
      rcases Set.mem_Icc.mp hs with ⟨h1, h2⟩
      constructor <;> linarith
    have hseg0 : ∀ u ∈ Set.Icc 0 B, x₀ + u • v ∈ stripInterior := by
      intro u hu
      exact hseg u (by
        rw [Set.mem_Icc]
        rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
        constructor <;> linarith)
    have hk0 : ∀ u ∈ Set.Icc 0 B, dN f (x₀ + u • v) v = 0 := by
      intro u hu
      exact hk u (by
        rw [Set.mem_Icc]
        rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
        constructor <;> linarith)
    have hmains := affine_on_kernel_segment hf (x := x₀) (v := v) (A := 0) (B := B) hseg0 hk0 s hs0
    simpa [zero_smul] using hmains

/-- **Local bend through an interior point (main branch)**.  When the kernel
vector field does not vanish at an interior point `x₀`, the point lies in the
interior of a straight *pre-bend* segment `{x₀ + s • w₀}` (`w₀ = Vf f x₀`,
`s ∈ Icc (-ε) ε`):  its direction is in the kernel of the shape operator at
every point of the segment, the unit normal of the image is constant along it,
and the image of the segment is the straight segment with the same endpoints
(`f` is affine on it).  This is the local content of Lemma `mc` (paper §2.1)
on the branch where the kernel field is nonzero. -/
lemma bend_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) {x₀ : ℝ²}
    (hx₀ : x₀ ∈ stripInterior) (hw₀ : Vf f x₀ ≠ 0) :
    ∃ w₀ : ℝ², w₀ ≠ 0 ∧ ∃ ε > (0 : ℝ),
      (∀ s ∈ Set.Icc (-ε) ε, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0) ∧
      (∀ s ∈ Set.Icc (-ε) ε, f (x₀ + s • w₀) = f x₀ + s • (fderiv ℝ f x₀ w₀)) ∧
      (∀ s ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + s • w₀) = unitNormal f x₀) := by
  rcases kernel_segment_around hf hx₀ hw₀ with ⟨δ, hδ, hseg⟩
  let ε : ℝ := δ / 2
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by
    dsimp [ε]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [hδ]
  have hkern : ∀ u ∈ Set.Icc (-ε) ε, dN f (x₀ + u • (Vf f x₀)) (Vf f x₀) = 0 := by
    intro u hu
    have huI : u ∈ Set.Ioo (-δ) δ := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
      constructor <;> linarith [hεδ]
    exact (hseg u huI).2
  have hins : ∀ u ∈ Set.Icc (-ε) ε, x₀ + u • (Vf f x₀) ∈ stripInterior := by
    intro u hu
    have huI : u ∈ Set.Ioo (-δ) δ := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
      constructor <;> linarith [hεδ]
    exact (hseg u huI).1
  have hnorm : ∀ u ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + u • (Vf f x₀)) = unitNormal f x₀ := by
    intro u hu
    have hmain := normal_const_on_kernel_segment hf (x := x₀) (v := Vf f x₀) (A := -ε) (B := ε)
      hins hkern u hu
    have h0 := normal_const_on_kernel_segment hf (x := x₀) (v := Vf f x₀) (A := -ε) (B := ε)
      hins hkern 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hε0])
    calc
      unitNormal f (x₀ + u • (Vf f x₀)) = unitNormal f (x₀ + (-ε) • (Vf f x₀)) := hmain
      _ = unitNormal f x₀ := by
        simpa using h0.symm
  have haff : ∀ u ∈ Set.Icc (-ε) ε, f (x₀ + u • (Vf f x₀)) = f x₀ + u • (fderiv ℝ f x₀ (Vf f x₀)) :=
    affine_from_center hf (x₀ := x₀) (v := Vf f x₀) (A := -ε) (B := ε)
      (by linarith) (by linarith [hε0]) hins hkern
  refine ⟨Vf f x₀, hw₀, ε, hε0, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨hins s hs, hkern s hs⟩
  · intro s hs
    exact haff s hs
  · intro s hs
    exact hnorm s hs

end Submission.PaperBand
end
