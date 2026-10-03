import Mathlib
import Submission.Work.Horn.horn_chart
import Submission.Work.L62.deep_preimage_aux
import Submission.Work.L62.section_unique

/-!
# The deep, `T`-equivariant section of the lifted horn map over the lower component

Let `d : ParabData f₀ D₀` be §4.1 data (`d.E = Φ ∘ φ` the lifted horn map), `Bl ⊆ d.DE` an open
simply connected `T`-invariant set containing the lower half plane `{Im < -η}` and avoiding the
critical value class `v + ℤ`, over which `d.E` is a covering map onto `ℂ ∖ (v + ℤ)`, and suppose
`d.E w - w → cl` at the lower end.

Then `d.E` has a *holomorphic, `T`-equivariant section* `s` over `Bl` (`d.E (s y) = y`,
`s (y+1) = s y + 1`), and there is a deep point `x₀ ∈ Bl` whose upward unit segment, downward ray
and the images of both under `d.E` all stay in `Bl`, and on which `s` is the inverse branch of `d.E`
(`s (d.E (x₀ ± i t)) = x₀ ± i t`).

Proof sketch:

* the deep inverse branch `u` of `d.E` (the solution of `d.E (u z) = z` in a deep half plane) is
  produced by `Work.L62.deep_preimage_aux`; that lemma assumes `0 < cl.im`, which is *not*
  available here (it is the conclusion of `horn_cl_im_pos`, downstream), so we apply it to the
  shifted constant `cl + c·I` with `c > -cl.im` and shift the resulting branch back;
* the deep branch is a section of `d.E` over a deep half plane, so `Work.L62.lift_section` extends
  it to a holomorphic section `σ` over the simply connected `Bl`;
* `Work.L62.section_unique` identifies `σ` with the deep branch on a deep half plane, which gives
  the lower-end asymptotics `σ w - w + cl → 0`;
* `Work.Horn.section_add_one_eq` upgrades the asymptotics to `T`-equivariance;
* the deep point `x₀` is chosen so that `x₀` and all `x₀ ± i t` (`0 ≤ t ≤ 1`, resp. `t ≥ 0`) lie in
  the deep half plane where `σ` is the unique inverse branch of `d.E`.
-/

namespace Work.Horn

open Filter Topology Complex Set
open scoped Topology

noncomputable section

theorem horn_section_deep (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀)
    (Bl : Set ℂ) (η : ℝ) (cl v : ℂ)
    (hBlO : IsOpen Bl) (hBlS : SimplyConnectedSpace Bl) (htBl : MandelDim.IsTInvariant Bl)
    (hlo : {w : ℂ | w.im < -η} ⊆ Bl) (hsub : Bl ⊆ d.DE)
    (hcov : IsCoveringMapOn (fun x : Bl => d.E x) {y | ∀ k : ℤ, y ≠ v + k})
    (hnoV : ∀ k : ℤ, v + k ∉ Bl)
    (hlow : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖d.E w - w - cl‖ < ε) :
    ∃ (x₀ : ℂ) (s : ℂ → ℂ), x₀ ∈ Bl ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        x₀ + Complex.I * (t : ℂ) ∈ Bl ∧ d.E (x₀ + Complex.I * (t : ℂ)) ∈ Bl) ∧
      (∀ t : ℝ, 0 ≤ t →
        x₀ - Complex.I * (t : ℂ) ∈ Bl ∧ d.E (x₀ - Complex.I * (t : ℂ)) ∈ Bl) ∧
      DifferentiableOn ℂ s Bl ∧ s (d.E x₀) = x₀ ∧
      (∀ y ∈ Bl, s y ∈ Bl ∧ d.E (s y) = y) ∧
      (∀ w ∈ Bl, s (w + 1) = s w + 1) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        s (d.E (x₀ + Complex.I * (t : ℂ))) = x₀ + Complex.I * (t : ℂ)) ∧
      (∀ t : ℝ, 0 ≤ t → s (d.E (x₀ - Complex.I * (t : ℂ))) = x₀ - Complex.I * (t : ℂ)) := by
  classical
  -- ## 0. Basic facts about `Bl` and `d.E`
  have hSsub : Bl ⊆ {y : ℂ | ∀ k : ℤ, y ≠ v + k} := fun y hy k hk => hnoV k (hk ▸ hy)
  have hcovBl : IsCoveringMapOn (fun x : Bl => d.E x) Bl := hcov.mono hSsub
  have hEhol : DifferentiableOn ℂ d.E Bl := (differentiableOn_E d).mono hsub
  have hEeq : ∀ w ∈ Bl, w + 1 ∈ Bl → d.E (w + 1) = d.E w + 1 :=
    fun w hw hw1 => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hw) (hsub hw1)
  have hBlpc : IsPreconnected Bl := isPreconnected_of_simplyConnected hBlS
  -- ## 1. the deep inverse branch of `d.E`
  -- `g = d.E - id - cl` is holomorphic on `Bl` and tends to `0` at the lower end
  set g : ℂ → ℂ := fun w => d.E w - w - cl with hgdef
  have hgdiff : DifferentiableOn ℂ g Bl := (hEhol.sub differentiableOn_id).sub_const cl
  have hglim : Filter.Tendsto g MandelDim.lowerEnd (nhds 0) := by
    rw [tendsto_lowerEnd_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := hlow ε hε
    refine ⟨R, fun w hw => ?_⟩
    have h := hR w hw
    have h2 : g w - 0 = d.E w - w - cl := by rw [hgdef]; ring
    rw [h2]
    exact h
  -- shift the constant `cl` by `c·I` so that `deep_preimage_aux` applies
  set c : ℝ := 1 - cl.im with hcdef
  have hcl' : 0 < (cl + Complex.I * (c : ℂ)).im := by
    simp only [Complex.add_im, Complex.I_mul_im, Complex.ofReal_re]
    rw [hcdef]; linarith
  obtain ⟨L, Lz, hLY, uc, huc_diff, huc_mem, huc_uniq, huc_tend⟩ :=
    Work.L62.deep_preimage_aux (D := Bl) (Y := -η) (g := g) (cl := cl + Complex.I * (c : ℂ))
      hBlO hlo hgdiff hglim hcl'
  -- shift the branch back: `u z := uc (z + c·I)` is the deep inverse branch of `d.E`
  set u : ℂ → ℂ := fun z => uc (z + Complex.I * (c : ℂ)) with hudef
  have hu_eq : ∀ z : ℂ, u z = uc (z + Complex.I * (c : ℂ)) := fun z => rfl
  have hg_eq : ∀ w : ℂ, g w = d.E w - w - cl := fun w => rfl
  have hLz' : ∀ z : ℂ, z.im < Lz - c → (z + Complex.I * (c : ℂ)).im < Lz := by
    intro z hz
    simp only [Complex.add_im, Complex.I_mul_im, Complex.ofReal_re]
    linarith
  have hu_diff : DifferentiableOn ℂ u {z : ℂ | z.im < Lz - c} := by
    rw [hudef]
    refine huc_diff.comp ((differentiableOn_id.add_const _)) (fun z hz => hLz' z hz)
  have hu_mem : ∀ z : ℂ, z.im < Lz - c → (u z).im < L ∧ d.E (u z) = z := by
    intro z hz
    have h := huc_mem (z + Complex.I * (c : ℂ)) (hLz' z hz)
    constructor
    · rw [hu_eq]; exact h.1
    · have h2 : u z + cl + g (u z) = z := by
        rw [hu_eq]
        linear_combination h.2
      have h3 : d.E (u z) = u z + cl + g (u z) := by
        rw [hg_eq]; ring
      exact h3.trans h2
  have hu_uniq : ∀ z : ℂ, z.im < Lz - c → ∀ v : ℂ, v.im < L → d.E v = z → v = u z := by
    intro z hz v hv hEv
    have h1 : v + (cl + Complex.I * (c : ℂ)) + g v = z + Complex.I * (c : ℂ) := by
      rw [hg_eq]
      linear_combination hEv
    have h := huc_uniq (z + Complex.I * (c : ℂ)) (hLz' z hz) v hv h1
    rw [hu_eq]; exact h
  have hu_tend : Filter.Tendsto (fun z : ℂ => u z - z + cl) MandelDim.lowerEnd (nhds 0) := by
    have hshift : Filter.Tendsto (fun z : ℂ => z + Complex.I * (c : ℂ)) MandelDim.lowerEnd
        MandelDim.lowerEnd := by
      rw [MandelDim.lowerEnd, Filter.tendsto_comap_iff]
      have h0 : Filter.Tendsto (fun y : ℂ => y.im) (Filter.comap Complex.im Filter.atBot)
          Filter.atBot := (Filter.tendsto_comap_iff).mp Filter.tendsto_id
      have h1 : Filter.Tendsto (fun y : ℂ => y.im + (Complex.I * (c : ℂ)).im)
          (Filter.comap Complex.im Filter.atBot) Filter.atBot :=
        Filter.tendsto_atBot_add_const_right _ _ h0
      have h2 : (Complex.im ∘ fun y : ℂ => y + Complex.I * (c : ℂ))
          = fun y : ℂ => y.im + (Complex.I * (c : ℂ)).im := by
        funext y
        simp only [Function.comp_apply, Complex.add_im]
      rw [h2]
      exact h1
    have h := huc_tend.comp hshift
    have h1 : Filter.Tendsto (fun z : ℂ => uc (z + Complex.I * (c : ℂ))
        - (z + Complex.I * (c : ℂ)) + (cl + Complex.I * (c : ℂ))) MandelDim.lowerEnd (nhds 0) := h
    have h2 : (fun z : ℂ => uc (z + Complex.I * (c : ℂ)) - (z + Complex.I * (c : ℂ))
          + (cl + Complex.I * (c : ℂ))) = fun z : ℂ => u z - z + cl := by
      funext z
      rw [hu_eq z]
      ring
    rwa [h2] at h1
  -- ## 2. the deep half plane on which `σ` will be identified with `u`
  set c₀ : ℝ := min (Lz - c) (-η) with hc₀def
  have hc₀_le1 : c₀ ≤ Lz - c := min_le_left _ _
  have hc₀_le2 : c₀ ≤ -η := min_le_right _ _
  have hD₀_sub_Bl : {y : ℂ | y.im < c₀} ⊆ Bl := fun y hy => hlo (lt_of_lt_of_le hy hc₀_le2)
  have hD₀_sub_deep : {y : ℂ | y.im < c₀} ⊆ {z : ℂ | z.im < Lz - c} :=
    fun y hy => lt_of_lt_of_le hy hc₀_le1
  have hD₀_open : IsOpen {y : ℂ | y.im < c₀} := isOpen_lt Complex.continuous_im continuous_const
  have hD₀_pc : IsPreconnected {y : ℂ | y.im < c₀} := (convex_halfSpace_im_lt c₀).isPreconnected
  have hu_Bl : ∀ y : ℂ, y.im < c₀ → u y ∈ Bl := fun y hy =>
    hlo (lt_trans (hu_mem y (hD₀_sub_deep hy)).1 hLY)
  have hu_deep_mem : ∀ y : ℂ, y.im < c₀ → u y ∈ Bl ∧ d.E (u y) = y := fun y hy =>
    ⟨hu_Bl y hy, (hu_mem y (hD₀_sub_deep hy)).2⟩
  -- ## 3. extend the deep section to all of `Bl`
  set y₁ : ℂ := ((c₀ - 1 : ℝ) : ℂ) * Complex.I with hy₁def
  have hy₁_im : y₁.im = c₀ - 1 := by rw [hy₁def]; simp
  have hy₁_mem : y₁ ∈ {y : ℂ | y.im < c₀} := by
    show y₁.im < c₀
    rw [hy₁_im]; linarith
  have hy₁_Bl : y₁ ∈ Bl := hD₀_sub_Bl hy₁_mem
  have hx₁_Bl : u y₁ ∈ Bl := hu_Bl y₁ hy₁_mem
  have hE_y₁ : d.E (u y₁) = y₁ := (hu_mem y₁ (hD₀_sub_deep hy₁_mem)).2
  obtain ⟨σ, hσ_diff, hσ_y₁, hσ_sec⟩ :=
    Work.L62.lift_section (X := Bl) hBlO (p := d.E) hEhol (Y := Bl) hBlO hBlS hcovBl
      hy₁_Bl hx₁_Bl hE_y₁
  -- ## 4. `σ` agrees with the deep branch on the deep half plane
  have hσ_eq : ∀ y ∈ {y : ℂ | y.im < c₀}, σ y = u y :=
    Work.L62.section_unique (X := Bl) hBlO hD₀_open hD₀_pc hD₀_sub_Bl hEhol
      (hσ_diff.mono hD₀_sub_Bl) (hu_diff.mono hD₀_sub_deep)
      (fun y hy => hσ_sec y (hD₀_sub_Bl hy))
      (fun y hy => hu_deep_mem y hy)
      hy₁_mem (by rw [hσ_y₁])
  -- ## 5. `σ` is the inverse branch of `d.E` at deep points
  have hσ_inv : ∀ z : ℂ, z.im < L → (d.E z).im < c₀ → σ (d.E z) = z := by
    intro z hzL hzE
    have h1 : z = u (d.E z) :=
      hu_uniq (d.E z) (lt_of_lt_of_le hzE hc₀_le1) z hzL rfl
    rw [hσ_eq (d.E z) hzE]
    exact h1.symm
  -- ## 6. the lower-end asymptotics of `σ`
  have hσ_asymp : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ Bl, w.im < R → ‖σ w - (w - cl)‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ :=
      (tendsto_lowerEnd_iff (f := fun z : ℂ => u z - z + cl) (cl := 0)).mp hu_tend ε hε
    refine ⟨min R c₀, fun w _ hwR => ?_⟩
    have hwR' : w.im < R := lt_of_lt_of_le hwR (min_le_left _ _)
    have hwc₀ : w.im < c₀ := lt_of_lt_of_le hwR (min_le_right _ _)
    rw [hσ_eq w hwc₀]
    have h1 : ‖u w - w + cl‖ < ε := by simpa using hR w hwR'
    have h2 : ‖u w - (w - cl)‖ = ‖u w - w + cl‖ := by
      rw [show u w - (w - cl) = u w - w + cl by ring]
    rw [h2]
    exact h1
  -- ## 7. `T`-equivariance of `σ`
  have hσ_T : ∀ w ∈ Bl, σ (w + 1) = σ w + 1 := by
    have hη' : (0 : ℝ) < max η 1 := lt_of_lt_of_le zero_lt_one (le_max_right η 1)
    have hlow' : {w : ℂ | w.im < -(max η 1)} ⊆ Bl := by
      intro z hz
      have hz1 : z.im < -(max η 1) := hz
      have hz2 : z.im < -η := by
        have h1 : η ≤ max η 1 := le_max_left η 1
        linarith
      exact hlo hz2
    have hcl'' : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ Bl, u.im < R → ‖d.E u - u - cl‖ < ε := by
      intro ε hε
      obtain ⟨R, hR⟩ := hlow ε hε
      exact ⟨R, fun u _ hu => hR u hu⟩
    exact fun w hw => section_add_one_eq (E := d.E) (D := Bl) (s := σ) (cl := cl) (η := max η 1)
      hη' hBlO hBlpc hlow' htBl hEhol hEeq hcl'' hσ_diff
      (fun y hy => (hσ_sec y hy).1) (fun y hy => (hσ_sec y hy).2) hσ_asymp w hw
  -- ## 8. the deep point `x₀` and the two vertical families
  obtain ⟨R₁, hR₁⟩ := hlow (1 / 2) (by norm_num)
  set R₂ : ℝ := min (min (R₁ - 1) (-η - 1)) (min (L - 1) (c₀ - cl.im - 3 / 2)) with hR₂def
  have hR₂_1 : R₂ ≤ R₁ - 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR₂_2 : R₂ ≤ -η - 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR₂_3 : R₂ ≤ L - 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR₂_4 : R₂ ≤ c₀ - cl.im - 3 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set x₀ : ℂ := ((R₂ - 1 : ℝ) : ℂ) * Complex.I with hx₀def
  have hx₀_im : x₀.im = R₂ - 1 := by rw [hx₀def]; simp
  have hx₀_le : x₀.im ≤ R₂ := by rw [hx₀_im]; linarith
  -- the crucial estimate: below `R₂` the value of `d.E` is below `c₀`
  have hEdeep : ∀ w : ℂ, w.im ≤ R₂ → (d.E w).im < c₀ := by
    intro w hw
    have hw₁ : w.im < R₁ := by have := hR₂_1; linarith
    have h1 := hR₁ w hw₁
    have h2 : (d.E w - w - cl).im ≤ ‖d.E w - w - cl‖ := Complex.im_le_norm _
    have h3 : (d.E w - w - cl).im = (d.E w).im - w.im - cl.im := by simp
    have h4 : w.im + cl.im + 1 / 2 < c₀ := by have := hR₂_4; linarith
    linarith
  have keymem : ∀ w : ℂ, w.im ≤ R₂ → w ∈ Bl ∧ d.E w ∈ Bl := by
    intro w hw
    have hwη : w.im < -η := by have := hR₂_2; linarith
    exact ⟨hlo hwη, hlo (lt_of_lt_of_le (hEdeep w hw) hc₀_le2)⟩
  have key : ∀ w : ℂ, w.im ≤ R₂ → σ (d.E w) = w := by
    intro w hw
    refine hσ_inv w ?_ (hEdeep w hw)
    have := hR₂_3; linarith
  have hx₀_Bl : x₀ ∈ Bl := (keymem x₀ hx₀_le).1
  have hx₀_sec : σ (d.E x₀) = x₀ := key x₀ hx₀_le
  have him_add : ∀ t : ℝ, (x₀ + Complex.I * (t : ℂ)).im = x₀.im + t := by
    intro t; simp
  have him_sub : ∀ t : ℝ, (x₀ - Complex.I * (t : ℂ)).im = x₀.im - t := by
    intro t; simp
  have hplus : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      x₀ + Complex.I * (t : ℂ) ∈ Bl ∧ d.E (x₀ + Complex.I * (t : ℂ)) ∈ Bl := by
    intro t _ ht1
    exact keymem _ (by rw [him_add]; linarith)
  have hminus : ∀ t : ℝ, 0 ≤ t →
      x₀ - Complex.I * (t : ℂ) ∈ Bl ∧ d.E (x₀ - Complex.I * (t : ℂ)) ∈ Bl := by
    intro t _
    exact keymem _ (by rw [him_sub]; linarith)
  have hσplus : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      σ (d.E (x₀ + Complex.I * (t : ℂ))) = x₀ + Complex.I * (t : ℂ) := by
    intro t _ ht1
    exact key _ (by rw [him_add]; linarith)
  have hσminus : ∀ t : ℝ, 0 ≤ t →
      σ (d.E (x₀ - Complex.I * (t : ℂ))) = x₀ - Complex.I * (t : ℂ) := by
    intro t _
    exact key _ (by rw [him_sub]; linarith)
  exact ⟨x₀, σ, hx₀_Bl, hplus, hminus, hσ_diff, hx₀_sec, hσ_sec, hσ_T, hσplus, hσminus⟩

end

end Work.Horn
