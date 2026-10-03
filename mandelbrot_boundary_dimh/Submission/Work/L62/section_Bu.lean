import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.branch_unique
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.model_deep_branch
import Submission.Work.L62.section_unique_on

/-!
# `Work.L62.section_Bu` — the global inverse branch of `ĥ = Ẽ - β` over the upper horn `Bu`

Let `d : ParabData g₀ D` be §4.1 data for a parabolic germ and `hd : HornData d` its horn data,
so that `d.E = Φ ∘ φ` is the lifted horn map, `hd.Bu` the upper component of `φ⁻¹(B)` (open,
connected, simply connected, `T`-invariant, containing `{η < Im}`), and `hd.v` a lift of the single
critical-value class of the pushed-down horn map.

Hypothesis (`havoid`): `Bu + β` misses the critical values `v + ℤ`, i.e. `Bu` misses the critical
(and singular) values of `ĥ = d.E - β`, so that `ĥ : Bu → Bu`-fibred covering has a global
holomorphic section over the simply connected base `Bu`.

Conclusion: there is a holomorphic section `σ` of `ĥ` over `Bu` taking values in `Bu`, normalised at
some `y₀ ∈ Bu` by `σ y₀ = x₀` with `d.E x₀ - β = y₀`, which is `T`-equivariant
(`σ (y+1) = σ y + 1`) and satisfies `σ w - w - β → 0` at the upper end.

Construction:

* `deep_local_branch` (below) provides, deep in the upper half plane, the *local* inverse branch
  `H` of `ĥ` with `H w = w + β + ρ w`, `ρ` `1`-periodic and `ρ w → 0` at the upper end.  It follows
  from `model_deep_branch` (proved in this workspace for `0 < Im β`) by the shift trick
  `β' = β + (|Im β| + 1) I`, which brings an arbitrary `β` into that range.
* `exists_section_horn` (Lemma 5.3, already in the workspace) extends a section from a point of `Bu`
  over the whole of the base `Bu` (simply connected, critical values avoided).
* `section_unique_on` (proved in `Submission/Work/L62/section_unique_on.lean`) shows this global
  section agrees with `H` on the deep half plane
  (uniqueness of sections of a local biholomorphism over a connected base), which delivers the
  asymptotic expansion of `σ`.
* `branch_unique` applied to `σ₁ y = σ (y+1) - 1` and `σ` delivers the `T`-equivariance: `σ₁` is
  again a section, and the two agree on the deep half plane by the explicit `1`-periodicity of `ρ`.
-/

namespace Work.L62

open MandelDim Set Filter Topology Complex
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- **The deep local branch of `ĥ = d.E - β`, for an arbitrary `β`.**  `model_deep_branch` needs
`0 < Im β`; here `β' = β + c` with `c = (|Im β| + 1) I` has `0 < Im β'`, and the branch of
`d.E - β'` post-composed with `w ↦ w - c` is a branch of `d.E - β`. -/
theorem deep_local_branch {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} :
    ∃ y₀ : ℝ, hd.η < y₀ ∧ ∃ (H ρ : ℂ → ℂ),
      DifferentiableOn ℂ H {w : ℂ | y₀ < w.im} ∧
      (∀ w : ℂ, y₀ < w.im → H w ∈ hd.Bu ∧ d.E (H w) - β = w ∧ H w = w + β + ρ w) ∧
      DifferentiableOn ℂ ρ {w : ℂ | y₀ < w.im} ∧
      (∀ w : ℂ, y₀ < w.im → ρ (w + 1) = ρ w) ∧
      Filter.Tendsto ρ MandelDim.upperEnd (nhds 0) := by
  set c : ℂ := ((|β.im| + 1 : ℝ) : ℂ) * Complex.I with hcdef
  have hcim : c.im = |β.im| + 1 := by rw [hcdef, Complex.mul_I_im, Complex.ofReal_re]
  have hcpos : 0 < c.im := by rw [hcim]; linarith [abs_nonneg β.im]
  set β' : ℂ := β + c with hβ'def
  have hβ'im : β'.im = β.im + (|β.im| + 1) := by rw [hβ'def, Complex.add_im, hcim]
  have hβ'pos : 0 < β'.im := by
    rw [hβ'im]
    linarith [neg_le_abs β.im]
  have hκpos : 0 < β'.im / 2 := by linarith
  obtain ⟨y, hy⟩ := model_deep_branch d hd (β := β') hκpos (by linarith)
  obtain ⟨H', ρ', y', hy'le, hH'd, hH'prop, hH'eq, hρ'd, hρ'per, -, -, -, hρ'lim⟩ :=
    hy (max y (hd.η + 1)) (le_max_left _ _)
  have hy'η : hd.η + 1 ≤ y' := le_trans (le_max_right y (hd.η + 1)) hy'le
  have hdeep : ∀ {w : ℂ}, y' + c.im < w.im → y' < (w - c).im := by
    intro w hw
    rw [Complex.sub_im, hcim]
    linarith
  refine ⟨y' + c.im, by linarith, fun w => H' (w - c), fun w => ρ' (w - c),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- differentiability of `H' ∘ (· - c)` on the deep half plane
    have hmap : MapsTo (fun w : ℂ => w - c) {w : ℂ | y' + c.im < w.im} {w : ℂ | y' < w.im} :=
      fun w hw => hdeep hw
    have hdτ : DifferentiableOn ℂ (fun w : ℂ => w - c) {w : ℂ | y' + c.im < w.im} := by fun_prop
    exact hH'd.comp hdτ hmap
  · -- the section properties
    intro w hw
    obtain ⟨-, hBu, hEq⟩ := hH'prop (w - c) (hdeep hw)
    have hEq2 := hH'eq (w - c) (hdeep hw)
    refine ⟨hBu, ?_, ?_⟩
    · show d.E (H' (w - c)) - β = w
      have hE : d.E (H' (w - c)) = (w - c) + β' := sub_eq_iff_eq_add.mp hEq
      rw [hE, hβ'def]; ring
    · show H' (w - c) = w + β + ρ' (w - c)
      rw [hEq2, hβ'def]; ring
  · -- differentiability of `ρ' ∘ (· - c)`
    have hmap : MapsTo (fun w : ℂ => w - c) {w : ℂ | y' + c.im < w.im} {w : ℂ | y' < w.im} :=
      fun w hw => hdeep hw
    have hdτ : DifferentiableOn ℂ (fun w : ℂ => w - c) {w : ℂ | y' + c.im < w.im} := by fun_prop
    exact hρ'd.comp hdτ hmap
  · -- `1`-periodicity
    intro w hw
    show ρ' ((w + 1) - c) = ρ' (w - c)
    rw [show w + 1 - c = (w - c) + 1 by ring]
    exact hρ'per (w - c) (hdeep hw)
  · -- the limit at the upper end
    have him : Filter.Tendsto (fun w : ℂ => Complex.im w)
        (Filter.comap Complex.im Filter.atTop) Filter.atTop :=
      Filter.tendsto_atTop.mpr fun b => by
        show {w : ℂ | b ≤ w.im} ∈ Filter.comap Complex.im Filter.atTop
        rw [Filter.mem_comap]
        exact ⟨Set.Ici b, Ici_mem_atTop b, subset_rfl⟩
    have h2 : Filter.Tendsto (fun w : ℂ => (w - c).im)
        (Filter.comap Complex.im Filter.atTop) Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      filter_upwards [Filter.tendsto_atTop.mp him (b + c.im)] with w hw
      rw [Complex.sub_im]
      linarith
    have hshift : Filter.Tendsto (fun w : ℂ => w - c) MandelDim.upperEnd MandelDim.upperEnd := by
      rw [MandelDim.upperEnd, Filter.tendsto_comap_iff]
      simpa only [Function.comp_def] using h2
    exact hρ'lim.comp hshift

theorem section_Bu {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ}
    (havoid : ∀ w ∈ hd.Bu, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)) :
    ∃ (y₀ x₀ : ℂ) (σ : ℂ → ℂ), y₀ ∈ hd.Bu ∧ x₀ ∈ hd.Bu ∧ d.E x₀ - β = y₀ ∧
      DifferentiableOn ℂ σ hd.Bu ∧ σ y₀ = x₀ ∧
      (∀ y ∈ hd.Bu, σ y ∈ hd.Bu ∧ d.E (σ y) - β = y) ∧
      (∀ y ∈ hd.Bu, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w - β) MandelDim.upperEnd (nhds 0) := by
  -- the deep local branch of `ĥ = d.E - β`, valid for every `β`
  obtain ⟨y₀d, hy₀d, H, ρ, hHdiff, hHprop, hρdiff, hρper, hρlim⟩ :=
    deep_local_branch d hd (β := β)
  -- the deep half plane `W` lies in `Bu`
  set W : Set ℂ := {w : ℂ | y₀d < w.im} with hWdef
  have hWo : IsOpen W := by
    rw [hWdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hWpc : IsPreconnected W := by
    rw [hWdef]; exact (convex_halfSpace_im_gt y₀d).isPreconnected
  have hWsub : W ⊆ hd.Bu := fun w hw => hd.upper (lt_trans hy₀d (by rw [hWdef] at hw; exact hw))
  -- a base point deep in `W ⊂ Bu`
  set w₀ : ℂ := ((y₀d + 1 : ℝ) : ℂ) * Complex.I with hw₀def
  have hw₀im : w₀.im = y₀d + 1 := by
    rw [hw₀def, Complex.mul_I_im, Complex.ofReal_re]
  have hw₀W : w₀ ∈ W := by
    rw [hWdef, Set.mem_ofPred_eq, hw₀im]; linarith
  have hw₀Bu : w₀ ∈ hd.Bu := hWsub hw₀W
  obtain ⟨hHw₀Bu, hHw₀eq, -⟩ := hHprop w₀ hw₀W
  -- Lemma 5.3: a global holomorphic section of `ĥ` over the simply connected base `Bu`
  obtain ⟨σ, hσdiff, hσw₀, hσsec⟩ :=
    exists_section_horn d hd hd.Bu_open hd.Bu_sc havoid hw₀Bu hHw₀Bu hHw₀eq
  -- uniqueness of the section: `σ` agrees with the deep branch `H` on `W`
  have hσW : DifferentiableOn ℂ σ W := hσdiff.mono hWsub
  have hagree : ∀ w ∈ W, σ w = H w :=
    section_unique_on d hd hWo hWpc hWsub hσW hHdiff
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
  -- `T`-equivariance: `σ₁ y = σ (y+1) - 1` is again a section and agrees with `σ` at `w₀`
  have hshift : MapsTo (fun y : ℂ => y + 1) hd.Bu hd.Bu := fun y hy => (hd.Bu_T y).mp hy
  have hσ₁diff : DifferentiableOn ℂ (fun y : ℂ => σ (y + 1) - 1) hd.Bu := by
    have hτ : DifferentiableOn ℂ (fun y : ℂ => y + 1) hd.Bu := by fun_prop
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
  exact ⟨w₀, H w₀, σ, hw₀Bu, hHw₀Bu, hHw₀eq, hσdiff, hσw₀, hσsec, hequiv, hasym⟩

end

end Work.L62
