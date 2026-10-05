import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- A continuous real function whose values all lie in the discrete set `c • ℤ`, `c > 0`,
is locally constant: around any value `c n` the open interval `(c n - c, c n + c)` of radius `c`
contains no other multiple of `c`. -/
lemma isLocallyConstant_of_exists_int_mul {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : Continuous f) {c : ℝ} (hc : 0 < c) (h : ∀ x, ∃ n : ℤ, f x = c * n) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨n, hn⟩ := h x
  have hxt : f x ∈ Set.Ioo (c * (n : ℝ) - c) (c * (n : ℝ) + c) := by
    rw [hn]; constructor <;> linarith
  have hnbhd : f ⁻¹' Set.Ioo (c * (n : ℝ) - c) (c * (n : ℝ) + c) ∈ nhds x :=
    hf.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hxt)
  filter_upwards [hnbhd] with y hy
  obtain ⟨m, hm⟩ := h y
  have hmn : m = n := by
    have h1 : (n : ℝ) - 1 < (m : ℝ) := by
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt hc)
      have hy1 := hy.1
      rw [hm] at hy1
      linarith
    have h2 : (m : ℝ) < (n : ℝ) + 1 := by
      refine lt_of_mul_lt_mul_left ?_ (le_of_lt hc)
      have hy2 := hy.2
      rw [hm] at hy2
      linarith
    have h3 : (n : ℤ) - 1 < m := by exact_mod_cast h1
    have h4 : m < (n : ℤ) + 1 := by exact_mod_cast h2
    omega
  rw [hm, hn, hmn]

/-- **The monodromy of a continuous lift of a smooth embedded loop is an integer multiple of
`2π`.** If `v` is a smooth embedded `2π`-periodic immersed loop and `σ` is continuous with `v ∘ σ`
again such a loop, then the "period" discrepancy `σ (t + 2π) - σ t` is constant in `t` and is an
integer multiple of `2π`: `σ (t + 2π) = σ t + 2π k` for a single `k : ℤ`.

The proof: `v (σ (t + 2π)) = v (σ t)` because `v ∘ σ` is `2π`-periodic, so by injectivity of `v`
modulo `2π` the function `g t = σ (t + 2π) - σ t` takes all its values in `2π ℤ`. Being continuous
and `2π ℤ`-valued with `2π ℤ` discrete, `g` is locally constant, hence constant on the (pre)connected
line. -/
lemma exists_monodromy_int (v : ℝ → ℂ) (hv : IsSmoothLoop v) (σ : ℝ → ℝ)
    (hσ : Continuous σ) (hw : IsSmoothLoop (fun t => v (σ t))) :
    ∃ k : ℤ, ∀ t, σ (t + 2 * π) = σ t + 2 * π * k := by
  obtain ⟨_, _, hinj, _⟩ := hv
  obtain ⟨_, hper, _, _⟩ := hw
  set g : ℝ → ℝ := fun t => σ (t + 2 * π) - σ t with hgdef
  have hgcont : Continuous g := by
    rw [hgdef]; fun_prop
  have hgint : ∀ t, ∃ n : ℤ, g t = 2 * π * n := by
    intro t
    obtain ⟨m, hm⟩ := hinj (σ (t + 2 * π)) (σ t) (hper t)
    refine ⟨-m, ?_⟩
    rw [hgdef]
    dsimp only
    push_cast
    linarith
  have hlc : IsLocallyConstant g :=
    isLocallyConstant_of_exists_int_mul g hgcont (by positivity) hgint
  have hconst : ∀ t, g t = g 0 :=
    fun t => IsLocallyConstant.apply_eq_of_preconnectedSpace hlc t 0
  obtain ⟨n0, hn0⟩ := hgint 0
  refine ⟨n0, fun t => ?_⟩
  have ht0 : g t = 2 * π * n0 := by rw [hconst t, hn0]
  rw [hgdef] at ht0
  dsimp only at ht0
  linarith

end Work.RPB1a
