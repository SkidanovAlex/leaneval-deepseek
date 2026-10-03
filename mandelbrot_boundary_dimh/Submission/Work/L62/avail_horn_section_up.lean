import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.model_deep_branch
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.branch_unique
import Submission.Work.L62.section_unique_on
import Submission.Work.L62.l62c_basic

/-!
# `Work.L62.avail_horn_section_up` — the deep, `T`-equivariant section of `ĥ = Ẽ - β` over `B^u`

Let `d : ParabData g₀ D` be the §4.1 data of a parabolic germ `g₀` on `D` and `hd : HornData d`
its horn data: `d.E = Φ ∘ φ` is the lifted horn map, `hd.Bu` the upper component of `φ⁻¹(basin)`
(open, connected, simply connected, `T`-invariant, containing `{η < Im ·}`), `hd.v` a lift of the
single critical-value class `{v + k}` of the pushed-down horn map `pushdown d.E`.

Assume (`havoid`) that `Bu` misses the critical values of `ĥ = d.E - β`:
`∀ w ∈ Bu, ∀ k : ℤ, w + β ≠ v + k`.

Then `ĥ` has a **global holomorphic section** `σ : Bu → Bu` over the simply connected base `Bu`,
and one can choose the *deep* sheet: the section with `σ w - w - β → 0` at the upper end.  It is
automatically `T`-equivariant (`σ (y + 1) = σ y + 1`).  This is the input of the Schwarz–Cartan
argument of §6 (`Work.L62.avail_descent_upper` + `Work.L62.avail_up`) which shows that the upper
end can only be available when `0 < Im β`.

## Structure of the proof

* `avail_tendsto_upperEnd_sub_I`: a vertical translation preserves the upper end
  (`upperEnd = comap im atTop`).
* `avail_deep_branch_nosign`: the deep inverse branch of `ĥ` on a half plane, **with no sign
  hypothesis on `β`**.  It is obtained from `Work.L62.model_deep_branch` (which needs the drift
  hypothesis `κ ≤ Im β`, `κ > 0`) by the following change of variable: put `K := max 0 (1 - Im β)`
  and `β' := β + iK` (so `Im β' ≥ 1`), take the drift branch `H'` of `d.E - β'` and let
  `H w := H' (w - iK)`; then `H w = w + β + o(1)` and `d.E (H w) - β = w`.  This is the whole point
  of the sign-free form: the present lemma must *not* assume `0 < Im β` (that is a *consequence*,
  proved downstream).
* `exists_section_horn` (lifted Lemma 5.3) extends the section from a point of `Bu` over the whole
  simply connected base `Bu`;
* `section_unique_on` identifies the global section with the deep branch on the deep half plane
  (uniqueness of sections of a local biholomorphism over a connected base), which gives both the
  asymptotic expansion `σ w = w + β + o(1)` and the `T`-equivariance: `σ₁ y := σ (y + 1) - 1` is
  again a section, and `σ₁ = σ` by `branch_unique` after noting that they agree deep in the upper
  half plane (where `ρ` is `1`-periodic).
-/

namespace Work.L62

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## Elementary filters -/

/-- A vertical translation preserves the upper end `upperEnd = comap im atTop`. -/
theorem avail_tendsto_upperEnd_sub_I (K : ℝ) :
    Filter.Tendsto (fun w : ℂ => w - (K : ℂ) * Complex.I) MandelDim.upperEnd MandelDim.upperEnd := by
  rw [MandelDim.upperEnd, Filter.tendsto_comap_iff]
  have h1 : (Complex.im ∘ fun w : ℂ => w - (K : ℂ) * Complex.I)
      = fun w : ℂ => w.im - K := by
    funext w
    rw [Function.comp_apply, Complex.sub_im, Complex.mul_I_im]
    simp
  rw [h1]
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨K + b, fun y hy w hw => ?_⟩
  have h2 : w.im - K = y - K := by rw [hw]
  rw [h2]
  linarith

/-- The imaginary part of the translation `w ↦ w - i K`. -/
theorem avail_sub_I_im (w : ℂ) (K : ℝ) :
    (w - (K : ℂ) * Complex.I).im = w.im - K := by
  rw [Complex.sub_im, Complex.mul_I_im]
  simp

/-! ## The sign-free deep branch -/

/-- **The deep inverse branch of `ĥ = d.E - β`, with no sign hypothesis on `β`.**  On a half plane
`{y₀ < Im ·}` strictly above `hd.η` there are holomorphic `H`, `ρ` with `H w ∈ Bu`,
`d.E (H w) - β = w`, `H w = w + β + ρ w`, `ρ` `1`-periodic and `ρ w → 0` at the upper end.

The proof is a change of variable in `Work.L62.model_deep_branch`: that lemma produces the branch
of `d.E - β'` for `β' = β + iK` with `K = max 0 (1 - Im β)` (so `Im β' ≥ 1`, the drift hypothesis
`κ = 1 ≤ Im β'`); shifting the variable by `-iK` turns it into the branch of `d.E - β`. -/
theorem avail_deep_branch_nosign {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} :
    ∃ y₀ : ℝ, hd.η < y₀ ∧ ∃ (H ρ : ℂ → ℂ),
      DifferentiableOn ℂ H {w : ℂ | y₀ < w.im} ∧
      (∀ w : ℂ, y₀ < w.im → H w ∈ hd.Bu ∧ d.E (H w) - β = w ∧ H w = w + β + ρ w) ∧
      DifferentiableOn ℂ ρ {w : ℂ | y₀ < w.im} ∧
      (∀ w : ℂ, y₀ < w.im → ρ (w + 1) = ρ w) ∧
      Filter.Tendsto ρ MandelDim.upperEnd (nhds 0) := by
  set κ : ℝ := 1 with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; norm_num
  set K : ℝ := max 0 (κ - β.im) with hKdef
  have hKnn : 0 ≤ K := le_max_left _ _
  set β' : ℂ := β + (K : ℂ) * Complex.I with hβ'def
  have hβ'im : β'.im = β.im + K := by
    rw [hβ'def, Complex.add_im, Complex.mul_I_im]
    simp
  have hImβ' : κ ≤ β'.im := by
    rw [hβ'im]
    have h : κ - β.im ≤ K := by rw [hKdef]; exact le_max_right _ _
    linarith
  obtain ⟨y, hy⟩ := model_deep_branch d hd hκ0 hImβ'
  obtain ⟨H', ρ', y'', hy''1, hH'diff, hH'prop, hH'eq, hρ'diff, hρ'per, -, -, -, hρ'lim⟩ :=
    hy y le_rfl
  set y₀ : ℝ := max (hd.η + 1) (y'' + K + 1) with hy₀def
  have hy₀η : hd.η < y₀ := by
    rw [hy₀def]; linarith [le_max_left (hd.η + 1) (y'' + K + 1)]
  have hy₀y'' : y'' + K < y₀ := by
    rw [hy₀def]; linarith [le_max_right (hd.η + 1) (y'' + K + 1)]
  set c : ℂ := (K : ℂ) * Complex.I with hcdef
  have hcim : c.im = K := by rw [hcdef, Complex.mul_I_im]; simp
  -- the shifted point lies in the deep half plane used by `H'`
  have hmem : ∀ w : ℂ, y₀ < w.im → y'' < (w - c).im := by
    intro w hw
    have hc : (w - c).im = w.im - K := by rw [hcdef, avail_sub_I_im]
    rw [hc]
    linarith
  refine ⟨y₀, hy₀η, fun w => H' (w - c), fun w => ρ' (w - c), ?_, ?_, ?_, ?_, ?_⟩
  · -- differentiability of `H`
    exact hH'diff.comp (differentiableOn_id.sub_const c) (fun w hw => hmem w hw)
  · intro w hw
    obtain ⟨-, hBu, hE⟩ := hH'prop (w - c) (hmem w hw)
    have hE' : d.E (H' (w - c)) = (w - c) + β' := sub_eq_iff_eq_add.mp hE
    have h4 : H' (w - c) = (w - c) + β' + ρ' (w - c) := hH'eq (w - c) (hmem w hw)
    rw [hβ'def] at hE' h4
    show H' (w - c) ∈ hd.Bu ∧ d.E (H' (w - c)) - β = w ∧ H' (w - c) = w + β + ρ' (w - c)
    refine ⟨hBu, ?_, ?_⟩
    · rw [hE']; ring
    · rw [h4]; ring
  · exact hρ'diff.comp (differentiableOn_id.sub_const c) (fun w hw => hmem w hw)
  · intro w hw
    have hw' : y'' < (w - c).im := hmem w hw
    have hstep : w + 1 - c = (w - c) + 1 := by ring
    show ρ' (w + 1 - c) = ρ' (w - c)
    rw [hstep]
    exact hρ'per (w - c) hw'
  · have hcomp := hρ'lim.comp (avail_tendsto_upperEnd_sub_I K)
    have : (ρ' ∘ fun w : ℂ => w - (K : ℂ) * Complex.I) = fun w : ℂ => ρ' (w - c) := by
      funext w; rw [Function.comp_apply, hcdef]
    rwa [this] at hcomp

/-! ## The section over `Bu` -/

theorem avail_horn_section_up {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ}
    (havoid : ∀ w ∈ hd.Bu, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)) :
    ∃ (y₀ x₀ : ℂ) (σ : ℂ → ℂ), y₀ ∈ hd.Bu ∧ x₀ ∈ hd.Bu ∧ d.E x₀ - β = y₀ ∧
      DifferentiableOn ℂ σ hd.Bu ∧ σ y₀ = x₀ ∧
      (∀ y ∈ hd.Bu, σ y ∈ hd.Bu ∧ d.E (σ y) - β = y) ∧
      (∀ y ∈ hd.Bu, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0) := by
  -- the deep branch of `ĥ = d.E - β` on the half plane `W = {y₀d < Im ·}`
  obtain ⟨y₀d, hy₀d, H, ρ, hHdiff, hHprop, hρdiff, hρper, hρlim⟩ := avail_deep_branch_nosign d hd
  set W : Set ℂ := {w : ℂ | y₀d < w.im} with hWdef
  have hWo : IsOpen W := isOpen_lt continuous_const Complex.continuous_im
  have hWpc : IsPreconnected W := (convex_halfSpace_im_gt y₀d).isPreconnected
  have hWsub : W ⊆ hd.Bu := fun w hw => hd.upper (lt_trans hy₀d hw)
  -- a base point deep in `W ⊆ Bu`
  set w₀ : ℂ := ((y₀d + 1 : ℝ) : ℂ) * Complex.I with hw₀def
  have hw₀im : w₀.im = y₀d + 1 := by rw [hw₀def, Complex.mul_I_im, Complex.ofReal_re]
  have hw₀W : w₀ ∈ W := by
    rw [hWdef, Set.mem_ofPred_eq, hw₀im]; linarith
  have hw₀Bu : w₀ ∈ hd.Bu := hWsub hw₀W
  obtain ⟨hx₀Bu, hx₀eq, -⟩ := hHprop w₀ hw₀W
  -- Lemma 5.3 over the simply connected base `Bu`
  obtain ⟨σ, hσdiff, hσw₀, hσsec⟩ :=
    exists_section_horn d hd hd.Bu_open hd.Bu_sc havoid hw₀Bu hx₀Bu hx₀eq
  -- uniqueness: the global section is the deep branch on `W`
  have hagree : ∀ w ∈ W, σ w = H w :=
    section_unique_on d hd hWo hWpc hWsub (hσdiff.mono hWsub) hHdiff
      (fun w hw => ⟨(hσsec w (hWsub hw)).2, (hσsec w (hWsub hw)).1⟩)
      (fun w hw => ⟨(hHprop w hw).2.1, (hHprop w hw).1⟩)
      hw₀W hσw₀
  -- the asymptotic expansion at the upper end
  have hdeepMem : {w : ℂ | y₀d + 1 < w.im} ∈ MandelDim.upperEnd := by
    rw [MandelDim.upperEnd, Filter.mem_comap]
    exact ⟨Set.Ioi (y₀d + 1), Ioi_mem_atTop _, subset_rfl⟩
  have hasym : Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0) := by
    refine hρlim.congr' ?_
    filter_upwards [hdeepMem] with w hw
    have hwW : w ∈ W := by rw [hWdef, Set.mem_ofPred_eq]; linarith
    rw [hagree w hwW, (hHprop w hwW).2.2]
    ring
  -- `T`-equivariance
  have hshift : MapsTo (fun y : ℂ => y + 1) hd.Bu hd.Bu := fun y hy => (hd.Bu_T y).mp hy
  have hσ₁diff : DifferentiableOn ℂ (fun y : ℂ => σ (y + 1) - 1) hd.Bu := by
    have hτ : DifferentiableOn ℂ (fun y : ℂ => y + 1) hd.Bu :=
      differentiableOn_id.add_const 1
    exact (hσdiff.comp hτ hshift).sub_const 1
  have hσ₁sec : ∀ w ∈ hd.Bu,
      d.E (σ (w + 1) - 1) - β = w ∧ σ (w + 1) - 1 ∈ hd.Bu := by
    intro w hw
    have hw1 : w + 1 ∈ hd.Bu := (hd.Bu_T w).mp hw
    obtain ⟨hz, hzsec⟩ := hσsec (w + 1) hw1
    have hzm : σ (w + 1) - 1 ∈ hd.Bu :=
      (hd.Bu_T (σ (w + 1) - 1)).mpr (by simpa using hz)
    have hEsub : d.E (σ (w + 1) - 1) = d.E (σ (w + 1)) - 1 := by
      have h := E_add_one_Bu d hd (w := σ (w + 1) - 1) hzm
      rw [show σ (w + 1) - 1 + 1 = σ (w + 1) by ring] at h
      exact eq_sub_iff_add_eq.mpr h.symm
    refine ⟨?_, hzm⟩
    have hzE : d.E (σ (w + 1)) = (w + 1) + β := sub_eq_iff_eq_add.mp hzsec
    rw [hEsub, hzE]
    ring
  have hσ₁w₀ : σ (w₀ + 1) - 1 = σ w₀ := by
    have hw₀1W : w₀ + 1 ∈ W := by
      rw [hWdef, Set.mem_ofPred_eq, Complex.add_im, Complex.one_im, add_zero, hw₀im]
      linarith
    rw [hagree (w₀ + 1) hw₀1W, hσw₀, (hHprop (w₀ + 1) hw₀1W).2.2,
      (hHprop w₀ hw₀W).2.2, hρper w₀ hw₀W]
    ring
  have hequiv : ∀ y ∈ hd.Bu, σ (y + 1) = σ y + 1 := by
    have hb := branch_unique d hd hσ₁diff hσdiff
      (fun w hw => ⟨(hσ₁sec w hw).1, (hσ₁sec w hw).2⟩)
      (fun w hw => ⟨(hσsec w hw).2, (hσsec w hw).1⟩)
      hw₀Bu hσ₁w₀
    intro y hy
    exact sub_eq_iff_eq_add.mp (hb y hy)
  exact ⟨w₀, H w₀, σ, hw₀Bu, hx₀Bu, hx₀eq, hσdiff, hσw₀, hσsec, hequiv, hasym⟩

end

end Work.L62
