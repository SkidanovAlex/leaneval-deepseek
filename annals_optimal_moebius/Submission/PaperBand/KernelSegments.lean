import Submission.PaperBand.KernelField

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Kernel segments: uniqueness of direction and local extension

`Submission.PaperBand.KernelField.bend_segment_of_dN_ne_zero` gives a *local*
straight pre-bend segment through every interior point of
`U = {x | dN f x ≠ 0}` (Lemma `mc`, local part).  This file adds the two
structural facts about these local segments that do not need the flat-region
analysis of Proposition `main0`:

* **uniqueness of the direction** (`kernel_direction_parallel`): at an
  interior point with `dN f x ≠ 0` the kernel of the shape operator is a
  line (`Developable.bendDir_is_line`), so any two nonzero kernel directions
  through `x` are parallel.  Hence two local kernel segments through the same
  point of `U` lie on the same straight line
  (`kernel_segment_directions_parallel`).

* **one-sided extension through `U`** (`kernel_segment_extend_right` /
  `kernel_segment_extend_left`): a kernel segment in direction `w₀` which
  reaches an interior point `y = x₀ + ε • w₀` still in `U` can be extended
  past `y`: the local bend through `y` (`bend_segment_of_dN_ne_zero`) lies on
  the same line (direction uniqueness at `y`), so gluing it onto the segment
  keeps the kernel condition for a strictly larger parameter interval.
  This is the mechanism by which a maximal kernel segment can only stop at
  the boundary of the strip (or at a point where `dN = 0`, the flat case
  handled later in `main0`).
-/

noncomputable section
namespace Submission.PaperBand

/-- Re-parameterizing the line `(x₀ + ε•w₀) + t•(c•w₀)` along the base
point `x₀`: both are `x₀ + (ε + t·c)•w₀`. -/
lemma line_reparam {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x₀ : E) (w₀ : E) (ε t c : ℝ) :
    (x₀ + ε • w₀) + t • (c • w₀) = x₀ + (ε + t * c) • w₀ := by
  rw [smul_smul]
  rw [add_smul]
  abel

/-- **Uniqueness of the kernel direction**: at an interior point with nonzero
shape operator, any two nonzero kernel directions are parallel (the kernel
is a line). -/
lemma kernel_direction_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x u v : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0)
    (hu0 : dN f x u = 0) (hv0 : dN f x v = 0) (hu : u ≠ 0) :
    ∃ c : ℝ, v = c • u := by
  rcases bendDir_is_line hf x hx hdN with ⟨v₀, hv₀n, hspan⟩
  have huIn : u ∈ bendDir f x := by rwa [mem_bendDir_iff]
  have hvIn : v ∈ bendDir f x := by rwa [mem_bendDir_iff]
  rw [hspan] at huIn hvIn
  rcases Submodule.mem_span_singleton.mp huIn with ⟨cu, hcu⟩
  rcases Submodule.mem_span_singleton.mp hvIn with ⟨cv, hcv⟩
  -- hcu : cu • v₀ = u, hcv : cv • v₀ = v
  have hcu_ne : cu ≠ 0 := by
    intro hz
    apply hu
    rw [← hcu, hz]
    simp
  refine ⟨cv / cu, ?_⟩
  calc
    v = cv • v₀ := hcv.symm
    _ = (cv * cu⁻¹) • u := by
      rw [← hcu]
      rw [smul_smul]
      congr 1
      field_simp [hcu_ne]
    _ = (cv / cu) • u := by
      congr 1

/-- Two kernel segments whose parameter intervals both contain `0` (i.e.
both pass through the same interior point `x₀` with `dN f x₀ ≠ 0`) have
parallel directions: they lie on the same straight line. -/
lemma kernel_segment_directions_parallel {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {x₀ u v : ℝ²} {A B C D : ℝ}
    (hx₀ : x₀ ∈ stripInterior) (hdN : dN f x₀ ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h1 : ∀ s ∈ Set.Icc A B, x₀ + s • u ∈ stripInterior ∧ dN f (x₀ + s • u) u = 0)
    (h2 : ∀ s ∈ Set.Icc C D, x₀ + s • v ∈ stripInterior ∧ dN f (x₀ + s • v) v = 0)
    (hA0 : A ≤ 0) (h0B : 0 ≤ B) (hC0 : C ≤ 0) (h0D : 0 ≤ D) :
    ∃ c : ℝ, v = c • u := by
  have hku : dN f x₀ u = 0 := by
    simpa using (h1 0 (by rw [Set.mem_Icc]; constructor <;> linarith)).2
  have hkv : dN f x₀ v = 0 := by
    simpa using (h2 0 (by rw [Set.mem_Icc]; constructor <;> linarith)).2
  exact kernel_direction_parallel hf hx₀ hdN hku hkv hu

/-- **The local bend around a kernel-segment endpoint, re-parameterized along
`w₀`**: if a local kernel segment in direction `w₁` passes through
`y₀ = x₀ + ε • w₀` and `w₁ = c • w₀` with `c ≠ 0`, then the kernel condition
of direction `w₀` holds on the whole two-sided parameter window
`[ε − ρ|c|, ε + ρ|c|]` around `y₀`. -/
lemma local_bend_reparam {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ w₁ : ℝ²} {c ε ρ : ℝ} (hρ : 0 < ρ) (hc : w₁ = c • w₀) (hcne : c ≠ 0)
    (h1 : ∀ t ∈ Set.Icc (-ρ) ρ,
      (x₀ + ε • w₀) + t • w₁ ∈ stripInterior ∧ dN f ((x₀ + ε • w₀) + t • w₁) w₁ = 0) :
    ∀ u ∈ Set.Icc (ε - ρ * |c|) (ε + ρ * |c|),
      x₀ + u • w₀ ∈ stripInterior ∧ dN f (x₀ + u • w₀) w₀ = 0 := by
  intro u hu
  have hu1 : ε - ρ * |c| ≤ u := (Set.mem_Icc.mp hu).1
  have hu2 : u ≤ ε + ρ * |c| := (Set.mem_Icc.mp hu).2
  let t : ℝ := (u - ε) / c
  have hcabs : |c| ≠ 0 := abs_ne_zero.mpr hcne
  have hden : 0 < |c| := abs_pos.mpr hcne
  have habs : |t| ≤ ρ := by
    dsimp [t]
    rw [abs_div]
    have hnum1 : -(ρ * |c|) ≤ u - ε := by linarith
    have hnum2 : u - ε ≤ ρ * |c| := by linarith
    have habsu : |u - ε| ≤ ρ * |c| := abs_le.mpr ⟨hnum1, hnum2⟩
    have hle : |u - ε| / |c| ≤ (ρ * |c|) / |c| := by
      exact div_le_div_of_nonneg_right habsu (le_of_lt hden)
    have hsimpl : (ρ * |c|) / |c| = ρ := by
      field_simp [hcabs]
    rwa [hsimpl] at hle
  have ht : t ∈ Set.Icc (-ρ) ρ := by
    rw [Set.mem_Icc]
    exact abs_le.mp habs
  have heq : u = ε + t * c := by
    dsimp [t]
    field_simp [hcne]
    ring
  have hb := h1 t ht
  have hlin : (x₀ + ε • w₀) + t • w₁ = x₀ + u • w₀ := by
    calc
      (x₀ + ε • w₀) + t • w₁ = (x₀ + ε • w₀) + t • (c • w₀) := by rw [hc]
      _ = x₀ + (ε + t * c) • w₀ := line_reparam x₀ w₀ ε t c
      _ = x₀ + u • w₀ := by rw [heq]
  constructor
  · rw [← hlin]
    exact hb.1
  · have hk := hb.2
    rw [hlin] at hk
    rw [hc] at hk
    rw [map_smul] at hk
    exact (smul_eq_zero.mp hk).resolve_left hcne

/-- **One-sided extension to the right**: a kernel segment in direction `w₀`
on the parameter interval `[0, ε]` whose endpoint `x₀ + ε • w₀` is still an
interior point with `dN ≠ 0` can be extended strictly to the right. -/
lemma kernel_segment_extend_right {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} {ε : ℝ} (hw₀ : w₀ ≠ 0) (hε : 0 ≤ ε)
    (hseg : ∀ s ∈ Set.Icc 0 ε, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0)
    (hdN : dN f (x₀ + ε • w₀) ≠ 0) :
    ∃ ε' > ε, ∀ s ∈ Set.Icc 0 ε', x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
  let p : ℝ² := x₀ + ε • w₀
  have hp : p ∈ stripInterior := by
    dsimp [p]
    exact (hseg ε (by rw [Set.mem_Icc]; constructor <;> linarith)).1
  have hdNp : dN f p ≠ 0 := by simpa [p] using hdN
  rcases bend_segment_of_dN_ne_zero hf (x₀ := p) hp hdNp with ⟨w₁, hw₁n, ρ, hρ, h1, _h2, _h3⟩
  have hker_w₀ : dN f p w₀ = 0 := by
    dsimp [p]
    exact (hseg ε (by rw [Set.mem_Icc]; constructor <;> linarith)).2
  have hker_w₁ : dN f p w₁ = 0 := by
    have hb := (h1 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hρ])).2
    simpa using hb
  rcases kernel_direction_parallel hf (x := p) hp hdNp hker_w₀ hker_w₁ hw₀ with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hz
    apply hw₁n
    rw [hc, hz]
    simp
  let δ : ℝ := ρ * |c|
  have hδ : 0 < δ := mul_pos hρ (abs_pos.mpr hc_ne)
  have hwin := local_bend_reparam hf (x₀ := x₀) (w₀ := w₀) (w₁ := w₁) (c := c)
    (ε := ε) (ρ := ρ) hρ hc hc_ne h1
  let ε' : ℝ := ε + δ / 2
  have hε' : ε < ε' := by
    dsimp [ε', δ]
    have : 0 < ρ * |c| / 2 := by positivity
    linarith
  refine ⟨ε', hε', ?_⟩
  intro s hs
  rcases Set.mem_Icc.mp hs with ⟨hs0, hsε'⟩
  by_cases hsε : s ≤ ε
  · exact hseg s (by rw [Set.mem_Icc]; constructor <;> linarith)
  · have hsin : s ∈ Set.Icc (ε - δ) (ε + δ) := by
      rw [Set.mem_Icc]
      constructor
      · have hlow : ε - δ ≤ ε := by linarith [hδ]
        have hgt : ε ≤ s := le_of_not_ge hsε
        linarith
      · have h2 : ε + δ / 2 ≤ ε + δ := by linarith [hδ]
        have hsε'' : s ≤ ε + δ / 2 := by simpa [ε'] using hsε'
        linarith
    exact hwin s hsin

/-- **One-sided extension to the left**: a kernel segment in direction `w₀`
on the parameter interval `[ε, 0]` whose endpoint `x₀ + ε • w₀` is still an
interior point with `dN ≠ 0` can be extended strictly to the left. -/
lemma kernel_segment_extend_left {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} {ε : ℝ} (hw₀ : w₀ ≠ 0) (hε : ε ≤ 0)
    (hseg : ∀ s ∈ Set.Icc ε 0, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0)
    (hdN : dN f (x₀ + ε • w₀) ≠ 0) :
    ∃ ε' < ε, ∀ s ∈ Set.Icc ε' 0, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
  let p : ℝ² := x₀ + ε • w₀
  have hp : p ∈ stripInterior := by
    dsimp [p]
    exact (hseg ε (by rw [Set.mem_Icc]; constructor <;> linarith)).1
  have hdNp : dN f p ≠ 0 := by simpa [p] using hdN
  rcases bend_segment_of_dN_ne_zero hf (x₀ := p) hp hdNp with ⟨w₁, hw₁n, ρ, hρ, h1, _h2, _h3⟩
  have hker_w₀ : dN f p w₀ = 0 := by
    dsimp [p]
    exact (hseg ε (by rw [Set.mem_Icc]; constructor <;> linarith)).2
  have hker_w₁ : dN f p w₁ = 0 := by
    have hb := (h1 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hρ])).2
    simpa using hb
  rcases kernel_direction_parallel hf (x := p) hp hdNp hker_w₀ hker_w₁ hw₀ with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hz
    apply hw₁n
    rw [hc, hz]
    simp
  let δ : ℝ := ρ * |c|
  have hδ : 0 < δ := mul_pos hρ (abs_pos.mpr hc_ne)
  have hwin := local_bend_reparam hf (x₀ := x₀) (w₀ := w₀) (w₁ := w₁) (c := c)
    (ε := ε) (ρ := ρ) hρ hc hc_ne h1
  let ε' : ℝ := ε - δ / 2
  have hε' : ε' < ε := by
    dsimp [ε', δ]
    have : 0 < ρ * |c| / 2 := by positivity
    linarith
  refine ⟨ε', hε', ?_⟩
  intro s hs
  rcases Set.mem_Icc.mp hs with ⟨hsε', hs0⟩
  by_cases hεs : ε ≤ s
  · exact hseg s (by rw [Set.mem_Icc]; constructor <;> linarith)
  · have hsin : s ∈ Set.Icc (ε - δ) (ε + δ) := by
      rw [Set.mem_Icc]
      constructor
      · have h1 : ε - δ ≤ ε - δ / 2 := by linarith [hδ]
        have h2 : ε - δ / 2 ≤ s := by simpa [ε'] using hsε'
        linarith
      · have h3 : s ≤ ε := le_of_not_ge hεs
        have h4 : ε ≤ ε + δ := by linarith [hδ]
        linarith
    exact hwin s hsin

end Submission.PaperBand
end
