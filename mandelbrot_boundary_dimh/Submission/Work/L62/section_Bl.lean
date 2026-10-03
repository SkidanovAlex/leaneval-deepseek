import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.exists_section_horn
import Submission.Work.L62.branch_unique
import Submission.Work.L62.l62c_basic
import Submission.Work.L62.deep_preimage_aux
import Submission.Work.L62.section_unique

/-!
# L62 — the lifted inverse branch of `E - β` over the lower horn `Bl` (Lemma 5.3, lower end)

`section_Bl` produces, for every `β` such that `hd.Bl` misses the critical class `v + ℤ - β`, a
holomorphic section `σ` of `ĥ = d.E - β` over `hd.Bl` (`d.E (σ y) - β = y` and `σ y ∈ hd.Bl` for
`y ∈ hd.Bl`) which is

* `T`-equivariant (`σ (y + 1) = σ y + 1`), so that it pushes down to a section of the pushed-down
  horn map on the cylinder, and
* normalised at the lower end: `σ w - w - (β - cl) → 0` there, where `cl` is the translation
  constant of `d.E - id` at the lower end (`hcl`).

In the pushed-down picture this is the inverse branch of the horn map at the puncture `0` (the
lower end of the cylinder) that Shishikura extends to `B^ℓ ∪ {∞}` by Lemma 5.3 (Proposition 5.3:
the pushed-down horn map is a covering onto `ℂ*` ramified only over `v`, and `B^ℓ ∪ {∞}` is simply
connected and misses `v`).

## Proof

1. `d.E` is holomorphic on `hd.Bl ⊆ d.DE` and `T`-equivariant there, and `g := d.E - id - cl` is
   holomorphic on `hd.Bl`, `1`-periodic, and `g w → 0` at the lower end uniformly (`hcl`).
2. `Work.L62.deep_preimage_aux` (the deep inverse branch of an asymptotically translating map) gives on
   a deep half plane `{im < Lz}` a holomorphic `u` with `u z + cl + g (u z) = z`, i.e.
   `d.E (u z) = z`, whose value is moreover the *unique* solution in the deep half plane `{im < L}`.
   Hence `σ_H y := u (y + β)` is a section of `ĥ` on a deep half plane, it is `T`-equivariant
   (`σ_H (y+1)` and `σ_H y + 1` are both deep solutions of `d.E v = y + 1 + β`), and it carries the
   lower-end normalisation.
3. `hd.Bl` is open, simply connected (`hd.Bl_sc`) and, by `havoid`, avoids the critical values
   `v + ℤ - β` of `ĥ`; so `Work.L62.lift_section` extends `σ_H` to a holomorphic section `σ` of `ĥ`
   over all of `hd.Bl`, and `Work.L62.section_unique` identifies the extension with `σ_H` on the
   deep half plane.
4. `T`-equivariance on all of `hd.Bl`: the two maps `y ↦ σ (y+1) - 1` and `y ↦ σ y` are both
   sections of `ĥ` over the preconnected `hd.Bl` and agree at a deep point, so `section_unique`
   gives equality everywhere.
5. The normalisation transfers from `σ_H` because a deep half plane is a neighbourhood of the
   lower end.
-/

namespace Work.L62

open MandelDim Set Filter Topology Complex
open scoped Topology

noncomputable section

theorem section_Bl {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    (havoid : ∀ w ∈ hd.Bl, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ)) :
    ∃ (y₀ x₀ : ℂ) (σ : ℂ → ℂ), y₀ ∈ hd.Bl ∧ x₀ ∈ hd.Bl ∧ d.E x₀ - β = y₀ ∧
      DifferentiableOn ℂ σ hd.Bl ∧ σ y₀ = x₀ ∧
      (∀ y ∈ hd.Bl, σ y ∈ hd.Bl ∧ d.E (σ y) - β = y) ∧
      (∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0) := by
  -- (0) basic structure of the horn map on `Bl`
  have hsubE : hd.Bl ⊆ d.DE := fun w hw => hd.sub (Or.inr hw)
  have hEdiff : DifferentiableOn ℂ d.E hd.Bl :=
    d.Φ_holo.comp (d.φ_holo.mono (fun w hw => (hsubE hw).1)) (fun w hw => (hsubE hw).2)
  have hEeq : ∀ w ∈ hd.Bl, d.E (w + 1) = d.E w + 1 := fun w hw => E_add_one_Bl d hd hw
  have hcov : IsCoveringMapOn (fun z : hd.Bl => d.E z - β) hd.Bl :=
    (hd.cov_l.homeomorph_comp (Homeomorph.subRight β)).mono (fun y hy k => havoid y hy k)
  have hp : DifferentiableOn ℂ (fun z : ℂ => d.E z - β) hd.Bl := hEdiff.sub_const β
  -- (1) the deep inverse branch of `w ↦ w + cl + (E w - w - cl)` = `E`
  have hgdiff : DifferentiableOn ℂ (fun w => d.E w - w - cl) hd.Bl :=
    (hEdiff.sub differentiableOn_id).sub_const cl
  have hglim : Filter.Tendsto (fun w => d.E w - w - cl) MandelDim.lowerEnd (nhds 0) := by
    have h1 := hcl.sub_const cl
    simpa using h1
  obtain ⟨L, Lz, hLY, u, hu_diff, hu_mem, hu_uniq, hu_tend⟩ :=
    deep_preimage_aux (D := hd.Bl) (g := fun w => d.E w - w - cl) (cl := cl) (Y := -hd.η)
      hd.Bl_open hd.lower hgdiff hglim (hd.cl_im_pos cl hcl)
  -- (2) the deep section `y ↦ u (y + β)` and its properties
  have hσH_mem : ∀ y : ℂ, y.im < Lz - β.im → u (y + β) ∈ hd.Bl := by
    intro y hy
    have hz : (y + β).im < Lz := by rw [Complex.add_im]; linarith
    exact hd.lower (lt_trans (hu_mem (y + β) hz).1 hLY)
  have hσH_sec : ∀ y : ℂ, y.im < Lz - β.im → d.E (u (y + β)) - β = y := by
    intro y hy
    have hz : (y + β).im < Lz := by rw [Complex.add_im]; linarith
    have h1 : u (y + β) + cl + (d.E (u (y + β)) - u (y + β) - cl) = y + β :=
      (hu_mem (y + β) hz).2
    have h2 : d.E (u (y + β)) = y + β := by linear_combination h1
    rw [h2]
    ring
  have hσH_diff : DifferentiableOn ℂ (fun y => u (y + β)) {y : ℂ | y.im < Lz - β.im} :=
    hu_diff.comp (differentiableOn_id.add_const β) (fun y hy => by
      rw [Set.mem_ofPred_eq] at hy ⊢
      rw [Complex.add_im]
      linarith)
  have hσH_T : ∀ y : ℂ, y.im < Lz - β.im → u ((y + 1) + β) = u (y + β) + 1 := by
    intro y hy
    have hz : ((y + 1) + β).im < Lz := by
      rw [Complex.add_im, Complex.add_im, Complex.one_im, add_zero]
      linarith
    have hz' : (y + β).im < Lz := by rw [Complex.add_im]; linarith
    have hv : (u (y + β) + 1).im < L := by
      rw [Complex.add_im, Complex.one_im, add_zero]
      exact (hu_mem (y + β) hz').1
    refine (hu_uniq ((y + 1) + β) hz (u (y + β) + 1) hv ?_).symm
    have hT : d.E (u (y + β) + 1) = d.E (u (y + β)) + 1 :=
      hEeq (u (y + β)) (hσH_mem y hy)
    have hu : u (y + β) + cl + (d.E (u (y + β)) - u (y + β) - cl) = y + β :=
      (hu_mem (y + β) hz').2
    rw [hT]
    linear_combination hu
  have hσH_lim : Filter.Tendsto (fun y => u (y + β) - y - (β - cl)) MandelDim.lowerEnd (nhds 0) := by
    have hcomp : Filter.Tendsto (fun y : ℂ => y + β) MandelDim.lowerEnd MandelDim.lowerEnd := by
      rw [MandelDim.lowerEnd, Filter.tendsto_comap_iff]
      have h0 : Filter.Tendsto (fun y : ℂ => y.im) (Filter.comap Complex.im Filter.atBot)
          Filter.atBot :=
        (Filter.tendsto_comap_iff).mp Filter.tendsto_id
      have h1 : Filter.Tendsto (fun y : ℂ => y.im + β.im)
          (Filter.comap Complex.im Filter.atBot) Filter.atBot :=
        Filter.tendsto_atBot_add_const_right _ β.im h0
      have h2 : (Complex.im ∘ fun y : ℂ => y + β) = fun y : ℂ => y.im + β.im := by
        funext y
        simp [Complex.add_im]
      rw [h2]
      exact h1
    have h1 : Filter.Tendsto (fun y => u (y + β) - (y + β) + cl) MandelDim.lowerEnd (nhds 0) :=
      hu_tend.comp hcomp
    have h2 : (fun y : ℂ => u (y + β) - (y + β) + cl) = fun y => u (y + β) - y - (β - cl) := by
      funext y; ring
    rwa [h2] at h1
  -- (3) the extension of the deep section to all of `hd.Bl`
  set c : ℝ := min (Lz - β.im) (-hd.η) with hc
  have hc_le1 : c ≤ Lz - β.im := by rw [hc]; exact min_le_left _ _
  have hc_le2 : c ≤ -hd.η := by rw [hc]; exact min_le_right _ _
  have hYd_sub_deep : {y : ℂ | y.im < c} ⊆ {y : ℂ | y.im < Lz - β.im} :=
    fun y hy => lt_of_lt_of_le hy hc_le1
  have hYd_sub_Bl : {y : ℂ | y.im < c} ⊆ hd.Bl :=
    fun y hy => hd.lower (lt_of_lt_of_le hy hc_le2)
  have hYd_open : IsOpen {y : ℂ | y.im < c} := isOpen_lt Complex.continuous_im continuous_const
  have hYd_pc : IsPreconnected {y : ℂ | y.im < c} := (convex_halfSpace_im_lt c).isPreconnected
  set y₁ : ℂ := ((c - 1 : ℝ) : ℂ) * I with hy₁
  have hy₁_mem : y₁ ∈ {y : ℂ | y.im < c} := by
    rw [hy₁]
    simp only [Set.mem_ofPred_eq, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  have hy₁_Bl : y₁ ∈ hd.Bl := hYd_sub_Bl hy₁_mem
  set x₁ : ℂ := u (y₁ + β) with hx₁
  have hx₁_mem : x₁ ∈ hd.Bl := hσH_mem y₁ (hYd_sub_deep hy₁_mem)
  have hx₁_sec : d.E x₁ - β = y₁ := hσH_sec y₁ (hYd_sub_deep hy₁_mem)
  obtain ⟨σ, hσ_diff, hσ_y₁, hσ_sec⟩ :=
    lift_section (X := hd.Bl) hd.Bl_open (p := fun z : ℂ => d.E z - β) hp
      (Y := hd.Bl) hd.Bl_open hd.Bl_sc hcov hy₁_Bl hx₁_mem hx₁_sec
  -- (4) identify `σ` with the deep section on the deep half plane
  have hσ_eq : ∀ y ∈ {y : ℂ | y.im < c}, σ y = u (y + β) :=
    section_unique (X := hd.Bl) hd.Bl_open hYd_open hYd_pc hYd_sub_Bl hp
      (hσ_diff.mono hYd_sub_Bl) (hσH_diff.mono hYd_sub_deep)
      (fun y hy => hσ_sec y (hYd_sub_Bl hy))
      (fun y hy => ⟨hσH_mem y (hYd_sub_deep hy), hσH_sec y (hYd_sub_deep hy)⟩)
      hy₁_mem (by rw [hσ_y₁, hx₁])
  have hσ_eq_y₁1 : σ (y₁ + 1) = u ((y₁ + 1) + β) := hσ_eq (y₁ + 1) (by
    have : (y₁ + 1).im = y₁.im := by rw [Complex.add_im, Complex.one_im, add_zero]
    rw [Set.mem_ofPred_eq, this]; exact hy₁_mem)
  -- (5) T-equivariance of `σ` on `hd.Bl`
  have hσ_T : ∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1 := by
    have hs₁_diff : DifferentiableOn ℂ (fun y => σ (y + 1) - 1) hd.Bl :=
      ((hσ_diff.comp (differentiableOn_id.add_const 1)
        (fun y hy => (hd.Bl_T y).mp hy))).sub_const 1
    have hs₁_sec : ∀ y ∈ hd.Bl, (σ (y + 1) - 1) ∈ hd.Bl ∧
        (fun z : ℂ => d.E z - β) (σ (y + 1) - 1) = y := by
      intro y hy
      have hy1 : y + 1 ∈ hd.Bl := (hd.Bl_T y).mp hy
      have h1 : σ (y + 1) ∈ hd.Bl := (hσ_sec (y + 1) hy1).1
      have h2 : d.E (σ (y + 1)) - β = y + 1 := (hσ_sec (y + 1) hy1).2
      have hw : σ (y + 1) - 1 ∈ hd.Bl := (hd.Bl_T (σ (y + 1) - 1)).mpr (by simpa using h1)
      have h3 := hEeq (σ (y + 1) - 1) hw
      have harg : σ (y + 1) - 1 + 1 = σ (y + 1) := by ring
      rw [harg] at h3
      constructor
      · exact hw
      · show d.E (σ (y + 1) - 1) - β = y
        have h4 : d.E (σ (y + 1)) = y + 1 + β := (sub_eq_iff_eq_add).mp h2
        have h5 : d.E (σ (y + 1) - 1) = y + β := by
          have h6 : d.E (σ (y + 1) - 1) = d.E (σ (y + 1)) - 1 :=
            (eq_sub_iff_add_eq).mpr h3.symm
          rw [h6, h4]
          ring
        rw [h5]; ring
    have hss : ∀ y ∈ hd.Bl, (fun y => σ (y + 1) - 1) y = σ y :=
      section_unique (X := hd.Bl) hd.Bl_open hd.Bl_open hd.Bl_conn.isPreconnected
        (subset_refl hd.Bl) hp hs₁_diff hσ_diff hs₁_sec hσ_sec hy₁_Bl ?_
    · intro y hy
      have h := hss y hy
      show σ (y + 1) = σ y + 1
      rw [← h]
      ring
    · -- agreement at the deep point `y₁`
      have hT := hσH_T y₁ (hYd_sub_deep hy₁_mem)
      rw [hσ_eq_y₁1, hσ_y₁]
      change u ((y₁ + 1) + β) - 1 = u (y₁ + β)
      rw [hT]
      ring
  -- (6) the asymptotics of `σ`
  have hσ_lim : Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0) := by
    have hmem : {y : ℂ | y.im < c} ∈ MandelDim.lowerEnd := by
      rw [MandelDim.lowerEnd, Filter.mem_comap]
      exact ⟨Set.Iic (c - 1), Filter.Iic_mem_atBot (c - 1),
        fun z hz => lt_of_le_of_lt hz (sub_one_lt c)⟩
    have hev : (fun w : ℂ => σ w - w - (β - cl))
        =ᶠ[MandelDim.lowerEnd] (fun w : ℂ => u (w + β) - w - (β - cl)) := by
      refine Filter.eventually_of_mem hmem ?_
      intro w hw
      show σ w - w - (β - cl) = u (w + β) - w - (β - cl)
      rw [hσ_eq w hw]
    exact hσH_lim.congr' hev.symm
  exact ⟨y₁, x₁, σ, hy₁_Bl, hx₁_mem, hx₁_sec, hσ_diff, hσ_y₁, hσ_sec, hσ_T, hσ_lim⟩


end

end Work.L62
