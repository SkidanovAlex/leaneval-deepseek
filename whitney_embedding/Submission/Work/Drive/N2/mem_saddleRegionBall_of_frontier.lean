import Mathlib
import Submission.Work.Drive.N2.modelBall

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- **Bound transfer to a closure point.** If `u` is continuous at `x`, `x` lies in the closure
of `s`, and `u ≤ a` on `s`, then `u x ≤ a` (no global regularity of `u` is needed; this is the
form in which bounds on the chart coordinate propagate to a frontier point of the model region,
where the chart is only known to be continuous *at* that point). -/
lemma le_of_mem_closure_of_continuousAt {M : Type*} [TopologicalSpace M] {s : Set M} {u : M → ℝ}
    {x : M} {a : ℝ} (hx : x ∈ closure s) (hu : ContinuousAt u x)
    (h : ∀ y ∈ s, u y ≤ a) : u x ≤ a := by
  by_contra hcon
  have hlt : a < u x := not_le.mp hcon
  have hnb : (𝓝[s] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hpre : u ⁻¹' (Set.Ioi a) ∈ 𝓝 x := hu.preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt)
  obtain ⟨y, hy⟩ := nhdsWithin_neBot.mp hnb hpre
  exact absurd (h y hy.2) (not_le.mpr hy.1)

/-- **The frontier row of the saddle window** (`hfrU`): a frontier point of the model saddle region
`{y ∈ modelBall φ ρ | |Im (Z y)²| < c₀}` at which the level `f` takes a value in the band
`(c - lam η, c + lam η)` lies in the model ball `modelBall φ ρ`.

Indeed, at such a point `x` (which is in the chart source by `hsrc`), the level law `hlev` extends
by continuity from the model ball to `x`, so `Re (Z x)² = (f x - c)/lam` with `|f x - c| < lam η`,
while `|Im (Z x)²| ≤ c₀`; hence `‖φ x‖⁴ = (Re (Z x)²)² + (Im (Z x)²)² < η² + c₀² < ρ⁴`. -/
theorem mem_saddleRegionBall_of_frontier {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))} {Z : M → ℂ}
    (hφsm : ContinuousOn (fun m : M => φ m) φ.source)
    (hf : Continuous f)
    (hZ : ∀ m : M, Z m = (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I)
    {c η c₀ lam ρ : ℝ} (hlam : 0 < lam) (hη : 0 < η) (hρ : 0 < ρ)
    (hρbig : η ^ 2 + c₀ ^ 2 < ρ ^ 4)
    (hsrc : closure (Work.Drive.N2.modelBall φ ρ) ⊆ φ.source)
    (hlev : ∀ y ∈ Work.Drive.N2.modelBall φ ρ, f y = c + lam * ((Z y) ^ 2).re)
    {x : M} (hx : x ∈ frontier {y : M | y ∈ Work.Drive.N2.modelBall φ ρ ∧ |((Z y) ^ 2).im| < c₀})
    (hxval : f x ∈ Set.Ioo (c - lam * η) (c + lam * η)) :
    x ∈ Work.Drive.N2.modelBall φ ρ := by
  set D : Set M := {y : M | y ∈ Work.Drive.N2.modelBall φ ρ ∧ |((Z y) ^ 2).im| < c₀} with hD
  have hxD : x ∈ closure D := frontier_subset_closure hx
  have hDsub : D ⊆ Work.Drive.N2.modelBall φ ρ := fun y hy => hy.1
  have hxcB : x ∈ closure (Work.Drive.N2.modelBall φ ρ) := closure_mono hDsub hxD
  have hxsrc : x ∈ φ.source := hsrc hxcB
  have hφc : ContinuousAt (fun m : M => φ m) x :=
    hφsm.continuousAt (φ.open_source.mem_nhds hxsrc)
  have hF : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => (v 0 : ℂ) + (v 1 : ℂ) * Complex.I) := by
    fun_prop
  have hZc : ContinuousAt (fun m : M => Z m) x := by
    rw [show (fun m : M => Z m)
        = (fun m => (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I) from funext hZ]
    exact hF.continuousAt.comp hφc
  have himc : ContinuousAt (fun m : M => ((Z m) ^ 2).im) x :=
    (Complex.continuous_im.comp (continuous_id.pow 2)).continuousAt.comp hZc
  have hrec : ContinuousAt (fun m : M => ((Z m) ^ 2).re) x :=
    (Complex.continuous_re.comp (continuous_id.pow 2)).continuousAt.comp hZc
  have hcal : ContinuousAt (fun m : M => c + lam * ((Z m) ^ 2).re) x :=
    (hrec.const_mul lam).const_add c
  -- the imaginary part of `Z x ^ 2` is bounded by `± c₀` in absolute value
  have him_le : ((Z x) ^ 2).im ≤ c₀ :=
    le_of_mem_closure_of_continuousAt (s := D) (u := fun m : M => ((Z m) ^ 2).im) (a := c₀)
      hxD himc (fun y hy => le_of_lt (abs_lt.mp hy.2).2)
  have hneg : ContinuousAt (fun m : M => -((Z m) ^ 2).im) x :=
    continuous_neg.continuousAt.comp himc
  have him_ge : -c₀ ≤ ((Z x) ^ 2).im := by
    have h := le_of_mem_closure_of_continuousAt (s := D) (u := fun m : M => -((Z m) ^ 2).im)
      (a := c₀) hxD hneg (fun y hy => by have := (abs_lt.mp hy.2).1; linarith)
    linarith
  have habs : |((Z x) ^ 2).im| ≤ c₀ := abs_le.mpr ⟨him_ge, him_le⟩
  have hc₀nn : 0 ≤ c₀ := le_trans (abs_nonneg _) habs
  have him_sq_le : (((Z x) ^ 2).im) ^ 2 ≤ c₀ ^ 2 := by
    have h : |((Z x) ^ 2).im| ≤ |c₀| := by rwa [abs_of_nonneg hc₀nn]
    exact sq_le_sq.mpr h
  -- the level law extends to `x`
  have hfdiff : f x - (c + lam * ((Z x) ^ 2).re) = 0 := by
    have h1 : f x - (c + lam * ((Z x) ^ 2).re) ≤ 0 :=
      le_of_mem_closure_of_continuousAt (s := Work.Drive.N2.modelBall φ ρ)
        (u := fun m : M => f m - (c + lam * ((Z m) ^ 2).re)) (a := 0)
        hxcB (hf.continuousAt.sub hcal) (fun y hy => by rw [hlev y hy]; simp)
    have h2 : 0 ≤ f x - (c + lam * ((Z x) ^ 2).re) := by
      have h3 : -(f x - (c + lam * ((Z x) ^ 2).re)) ≤ 0 :=
        le_of_mem_closure_of_continuousAt (s := Work.Drive.N2.modelBall φ ρ)
          (u := fun m : M => -(f m - (c + lam * ((Z m) ^ 2).re))) (a := 0)
          hxcB ((hf.continuousAt.sub hcal).neg) (fun y hy => by rw [hlev y hy]; simp)
      linarith
    linarith
  have hfeq : f x = c + lam * ((Z x) ^ 2).re := by linarith
  -- the band gives the real part bound
  have hre_lt : |((Z x) ^ 2).re| < η := by
    have h1 : -(lam * η) < f x - c := by linarith [hxval.1]
    have h2 : f x - c < lam * η := by linarith [hxval.2]
    have habs : |f x - c| < lam * η := abs_lt.mpr ⟨h1, h2⟩
    have hdiv : ((Z x) ^ 2).re = (f x - c) / lam := by
      have hlin : f x - c = lam * ((Z x) ^ 2).re := by linarith
      rw [eq_div_iff (ne_of_gt hlam), hlin]
      ring
    rw [hdiv, abs_div, abs_of_pos hlam, div_lt_iff₀ hlam]
    nlinarith [habs]
  have hre_sq : (((Z x) ^ 2).re) ^ 2 < η ^ 2 := sq_lt_sq.mpr (by rwa [abs_of_pos hη])
  -- the two bounds combine into `‖φ x‖⁴ < ρ⁴`
  have hnorm2 : ‖φ x‖ ^ 2 = Complex.normSq (Z x) := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Complex.normSq_apply, hZ x]
    simp [Real.norm_eq_abs, sq_abs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im]
    ring
  have hpow4 : ‖φ x‖ ^ 4 = Complex.normSq ((Z x) ^ 2) := by
    have h4 : ‖φ x‖ ^ 4 = (‖φ x‖ ^ 2) ^ 2 := by ring
    rw [h4, hnorm2, ← map_pow Complex.normSq (Z x) 2]
  have hlt : ‖φ x‖ ^ 4 < ρ ^ 4 := by
    rw [hpow4, Complex.normSq_apply]
    nlinarith [hre_sq, him_sq_le, hρbig]
  have hnorm_lt : ‖φ x‖ < ρ := lt_of_pow_lt_pow_left₀ 4 (le_of_lt hρ) hlt
  exact ⟨hxsrc, hnorm_lt⟩

end Work.Drive.N2
