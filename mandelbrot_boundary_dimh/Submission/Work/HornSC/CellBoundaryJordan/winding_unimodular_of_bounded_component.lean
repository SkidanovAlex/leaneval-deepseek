import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.grid_circle_map
import Submission.Work.HornSC.CellBoundaryJordan.arg_lift_periodic
import Submission.Work.HornSC.CellBoundaryJordan.hasArg_iff_arg_lift
import Submission.Work.HornSC.Tools
import Submission.Work.PlanarSC.not_two_preconnected_pieces_of_two_jordan
import Submission.Work.HornSC.CellBoundaryJordan.rootCircleMap
import Submission.Work.HornSC.CellBoundaryJordan.boundedComponentIn_iff_period_ne_zero
import Submission.Work.HornSC.CellBoundaryJordan.subset_or_subset_of_bounded_components

/-!
# The winding number of a Jordan curve about a point of a bounded complementary component

Let `γ : C(Circle, ℂ)` be injective (a Jordan curve), let `a ∉ range γ` lie in a *bounded* connected
component of `ℂ \ range γ`, and let `θ : ℝ → ℂ` be a continuous lift of the closed curve
`t ↦ γ (exp (2 π i t)) - a` through `exp`, with drift `m`: `θ (t+1) = θ t + m · 2 π i`.  Then
`m = 1` or `m = -1`: the winding number of a Jordan curve about a point of its bounded complementary
region is `±1`.

The proof first shows `m ≠ 0` (a closed curve winds trivially about the points of the *unbounded*
component, and non-trivially about the points of a bounded one).  For `m > 0` we form the `m`-th
root curve `g` (`g z ^ m = γ z - a`, again an injective circle map) and observe that the `m`
rotated copies `ζ^k · g` (`ζ = exp (2 π i / m)`) are pairwise disjoint Jordan curves with `0` in
their interiors; the nesting lemma for two disjoint Jordan curves then gives `A₀ ⊆ A₁` or
`A₁ ⊆ A₀` for the two interior components, and the `ζ`-rotation identity `A₁ = ζ · A₀` (plus the
finite order of `ζ`) forces `A₁ = A₀`, hence equal boundaries, contradicting disjointness.  The case
`m < 0` is reduced to `m > 0` by inversion in `a`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set Filter
open scoped Topology

/-! ## An elementary rotation lemma -/

/-- **A set is invariant under multiplication by a finite order unit as soon as it is contained in
its own image.** -/
private lemma image_mul_eq_of_subset {ρ : ℂ} {n : ℕ} (hn : 0 < n) (hρn : ρ ^ n = 1) {S : Set ℂ}
    (h : S ⊆ (fun w : ℂ => ρ * w) '' S) : (fun w : ℂ => ρ * w) '' S = S := by
  have hstep : ∀ k : ℕ,
      (fun w : ℂ => ρ ^ k * w) '' S ⊆ (fun w : ℂ => ρ ^ (k + 1) * w) '' S := by
    intro k
    have h1 : (fun w : ℂ => ρ ^ k * w) '' S
        ⊆ (fun w : ℂ => ρ ^ k * w) '' ((fun w : ℂ => ρ * w) '' S) := Set.image_mono h
    rw [Set.image_image] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    funext x
    rw [pow_succ]
    ring
  have hchain : ∀ j : ℕ,
      (fun w : ℂ => ρ * w) '' S ⊆ (fun w : ℂ => ρ ^ (j + 1) * w) '' S := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => exact ih.trans (hstep (j + 1))
  have hlast : (fun w : ℂ => ρ ^ (n - 1 + 1) * w) '' S = S := by
    have h1 : n - 1 + 1 = n := by omega
    rw [h1]
    have h2 : (fun w : ℂ => ρ ^ n * w) = id := by
      funext w
      rw [hρn]
      simp
    rw [h2, Set.image_id]
  exact le_antisymm ((hchain (n - 1)).trans (le_of_eq hlast)) h

/-! ## The main step: a positive drift must be `1` -/

private theorem eq_one_of_pos {γ : C(Circle, ℂ)} (hγ : Function.Injective γ) {a : ℂ}
    (hbdd : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a))
    {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθexp : ∀ t, Complex.exp (θ t) = γ (Circle.exp (2 * Real.pi * t)) - a)
    {m : ℤ} (hθper : ∀ t, θ (t + 1) = θ t + (m : ℂ) * (2 * Real.pi * Complex.I))
    (hm : 0 < m) : m = 1 := by
  by_contra hne
  -- write `m = n` with `n : ℕ`, `n ≥ 2`
  set n : ℕ := m.toNat with hndef
  have hmn : (n : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnne : (n : ℂ) ≠ 0 := by
    have h : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn0)
    exact_mod_cast h
  have hθpern : ∀ t, θ (t + 1) = θ t + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro t
    have hcast : (m : ℂ) = (n : ℂ) := by
      rw [← hmn]; push_cast; ring
    rw [hθper t, hcast]
  -- the shifted curve and its `n`-th root
  let γa : C(Circle, ℂ) := ⟨fun z => γ z - a, by fun_prop⟩
  have hγa : Function.Injective γa := fun x y h => hγ (sub_left_inj.mp h)
  have hθexpa : ∀ t, Complex.exp (θ t) = γa (Circle.exp (2 * Real.pi * t)) := fun t => hθexp t
  obtain ⟨g, hginj, hgpow, hgval⟩ := rootCircleMap hγa hθc hθexpa hn0 hθpern
  have h0g : (0 : ℂ) ∉ Set.range g := by
    rintro ⟨z, hz⟩
    obtain ⟨s, hs⟩ := Circle.exp_surjective z
    have h1 : g (Circle.exp (2 * Real.pi * (s / (2 * Real.pi)))) = g z := by
      rw [mul_div_cancel₀ s (by positivity : (2 : ℝ) * Real.pi ≠ 0), hs]
    rw [← h1] at hz
    have h := hgval (s / (2 * Real.pi))
    rw [hz] at h
    exact Complex.exp_ne_zero _ h.symm
  -- the rotation `ζ` of order `n`
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) with hζdef
  have hζprim : IsPrimitiveRoot ζ n := by
    rw [hζdef]; exact Complex.isPrimitiveRoot_exp n (by omega)
  have hζpow : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζne1 : ζ ≠ 1 := hζprim.ne_one (by omega)
  have hζne0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : n ≠ 0)] at hζpow
    exact one_ne_zero hζpow.symm
  -- the rotated curve
  let gζ : C(Circle, ℂ) := ⟨fun z => ζ * g z, by fun_prop⟩
  have hgζinj : Function.Injective gζ := by
    intro x y h
    exact hginj (mul_left_cancel₀ hζne0 h)
  have h0gζ : (0 : ℂ) ∉ Set.range gζ := by
    rintro ⟨z, hz⟩
    exact h0g ⟨z, (mul_eq_zero.mp hz).resolve_left hζne0⟩
  -- the two curves are disjoint
  have hdisj : Disjoint (Set.range g) (Set.range gζ) := by
    rw [Set.disjoint_left]
    rintro w ⟨z1, rfl⟩ ⟨z2, hz2⟩
    have hz2' : ζ * g z2 = g z1 := hz2
    have h1 : (g z1) ^ n = (ζ * g z2) ^ n := by rw [hz2']
    rw [mul_pow, hζpow, one_mul, hgpow z1, hgpow z2] at h1
    have h3 : z1 = z2 := hγ (sub_left_inj.mp h1)
    subst h3
    have h4 : g z1 = 0 := by
      have h5 : (1 - ζ) * g z1 = 0 := by rw [sub_mul, one_mul, hz2', sub_self]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 (by intro h7; rw [sub_eq_zero] at h7; exact hζne1 h7.symm)
      · exact h6
    exact h0g ⟨z1, h4⟩
  -- the lifts of `g` and of `ζ · g` put `0` in bounded components of both complements
  have hbdd0 : Bornology.IsBounded (connectedComponentIn ((Set.range g)ᶜ) 0) := by
    let ψ : ℝ → ℂ := fun t => θ t / (n : ℂ)
    have hψc : Continuous ψ := hθc.div_const _
    have hψexp : ∀ t, Complex.exp (ψ t) = g (Circle.exp (2 * Real.pi * t)) - 0 := by
      intro t
      show Complex.exp (θ t / (n : ℂ)) = _
      rw [hgval t]
      ring
    have hψper : ∀ t, ψ (t + 1) = ψ t + (1 : ℤ) * (2 * Real.pi * Complex.I) := by
      intro t
      show θ (t + 1) / (n : ℂ) = _
      rw [hθpern t, add_div, mul_div_cancel_left₀ _ hnne]
      push_cast
      ring
    exact (boundedComponentIn_iff_period_ne_zero hginj h0g hψc hψexp (m := 1)
      hψper).mpr (by norm_num)
  have hbdd1 : Bornology.IsBounded (connectedComponentIn ((Set.range gζ)ᶜ) 0) := by
    let ψζ : ℝ → ℂ := fun t => θ t / (n : ℂ) + 2 * Real.pi * Complex.I / (n : ℂ)
    have hψζc : Continuous ψζ :=
      Continuous.add (hθc.div_const _) continuous_const
    have hψζexp : ∀ t, Complex.exp (ψζ t) = gζ (Circle.exp (2 * Real.pi * t)) - 0 := by
      intro t
      show Complex.exp (θ t / (n : ℂ) + 2 * Real.pi * Complex.I / (n : ℂ)) = _
      rw [Complex.exp_add, ← hgval t, ← hζdef]
      simp only [gζ, ContinuousMap.coe_mk, sub_zero]
      ring
    have hψζper : ∀ t, ψζ (t + 1) = ψζ t + (1 : ℤ) * (2 * Real.pi * Complex.I) := by
      intro t
      show θ (t + 1) / (n : ℂ) + 2 * Real.pi * Complex.I / (n : ℂ) = _
      rw [hθpern t, add_div, mul_div_cancel_left₀ _ hnne]
      push_cast
      ring
    exact (boundedComponentIn_iff_period_ne_zero hgζinj h0gζ hψζc hψζexp (m := 1)
      hψζper).mpr (by norm_num)
  -- frontier facts
  have hnotpre : ¬ IsPreconnected ((Set.range g)ᶜ) := by
    obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, -, -, hcov⟩ :=
      Commons.Topology.Jordan.plane_separation g hginj
    exact Work.PlanarSC.not_isPreconnected_compl_range_of_separation hUo hVo hUc hVc hUV hcov
  have hnotpreζ : ¬ IsPreconnected ((Set.range gζ)ᶜ) := by
    obtain ⟨U, V, hUo, hVo, hUc, hVc, hUV, -, -, hcov⟩ :=
      Commons.Topology.Jordan.plane_separation gζ hgζinj
    exact Work.PlanarSC.not_isPreconnected_compl_range_of_separation hUo hVo hUc hVc hUV hcov
  have hfr0 : frontier (connectedComponentIn ((Set.range g)ᶜ) 0) = Set.range g :=
    Commons.Topology.Connected.frontier_component_compl_range g hginj hnotpre 0 h0g
  have hfr1 : frontier (connectedComponentIn ((Set.range gζ)ᶜ) 0) = Set.range gζ :=
    Commons.Topology.Connected.frontier_component_compl_range gζ hgζinj hnotpreζ 0 h0gζ
  -- the rotation identity `A₁ = ζ · A₀`
  have himg : connectedComponentIn ((Set.range gζ)ᶜ) 0
      = (fun w : ℂ => ζ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0) := by
    have hcoe : (⇑(Homeomorph.mulLeft₀ ζ hζne0) : ℂ → ℂ) = fun w => ζ * w := by
      funext w
      show Equiv.mulLeft₀ ζ hζne0 w = ζ * w
      rw [Equiv.mulLeft₀_apply]
    have h0 : (Homeomorph.mulLeft₀ ζ hζne0) 0 = 0 := by
      show Equiv.mulLeft₀ ζ hζne0 0 = 0
      simp [Equiv.mulLeft₀_apply]
    have himgset : (Homeomorph.mulLeft₀ ζ hζne0) '' (Set.range g) = Set.range gζ := by
      rw [hcoe]
      ext w
      constructor
      · rintro ⟨v, ⟨z, rfl⟩, rfl⟩
        exact ⟨z, rfl⟩
      · rintro ⟨z, rfl⟩
        exact ⟨g z, ⟨z, rfl⟩, rfl⟩
    have hcompl : (Homeomorph.mulLeft₀ ζ hζne0) '' (Set.range g)ᶜ
        = (Set.range gζ)ᶜ := by
      rw [Set.image_compl_eq (f := ⇑(Homeomorph.mulLeft₀ ζ hζne0))
        (Homeomorph.mulLeft₀ ζ hζne0).bijective, himgset]
    have hφ := Homeomorph.image_connectedComponentIn (Homeomorph.mulLeft₀ ζ hζne0)
      (s := (Set.range g)ᶜ) (x := 0) h0g
    rw [hcompl, h0] at hφ
    rw [hcoe] at hφ
    exact hφ.symm
  -- the nesting lemma for two disjoint Jordan curves
  have hnest := subset_or_subset_of_bounded_components hginj hgζinj hdisj h0g h0gζ hbdd0 hbdd1
  have hne0 : (Set.range g).Nonempty := ⟨g (Circle.exp 0), Set.mem_range_self _⟩
  rcases hnest with hsub | hsub
  · -- `A₀ ⊆ A₁ = ζ · A₀`
    have hiter : (fun w : ℂ => ζ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0)
        = connectedComponentIn ((Set.range g)ᶜ) 0 := by
      refine image_mul_eq_of_subset hn0 hζpow ?_
      rw [← himg]
      exact hsub
    have hAeq : connectedComponentIn ((Set.range g)ᶜ) 0
        = connectedComponentIn ((Set.range gζ)ᶜ) 0 := by
      rw [himg, hiter]
    have hrange : Set.range g = Set.range gζ := by
      calc Set.range g = frontier (connectedComponentIn ((Set.range g)ᶜ) 0) := hfr0.symm
        _ = frontier (connectedComponentIn ((Set.range gζ)ᶜ) 0) := by rw [hAeq]
        _ = Set.range gζ := hfr1
    obtain ⟨w, hw⟩ := hne0
    exact (Set.disjoint_left.mp hdisj) hw (hrange ▸ hw)
  · -- `A₁ = ζ · A₀ ⊆ A₀`
    have hsub' : connectedComponentIn ((Set.range g)ᶜ) 0
        ⊆ (fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0) := by
      have h1 : (fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range gζ)ᶜ) 0)
          ⊆ (fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0) :=
        Set.image_mono hsub
      have h2 : (fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range gζ)ᶜ) 0)
          = connectedComponentIn ((Set.range g)ᶜ) 0 := by
        rw [himg, Set.image_image]
        have h3 : (fun x : ℂ => ζ⁻¹ * (ζ * x)) = id := by
          funext x
          show ζ⁻¹ * (ζ * x) = x
          rw [← mul_assoc, inv_mul_cancel₀ hζne0, one_mul]
        rw [h3, Set.image_id]
      rwa [h2] at h1
    have hζinvpow : (ζ⁻¹) ^ n = 1 := by rw [inv_pow, hζpow, inv_one]
    have hiter : (fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0)
        = connectedComponentIn ((Set.range g)ᶜ) 0 := image_mul_eq_of_subset hn0 hζinvpow hsub'
    have hζA : (fun w : ℂ => ζ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0)
        = connectedComponentIn ((Set.range g)ᶜ) 0 := by
      have h : (fun w : ℂ => ζ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0)
          = (fun w : ℂ => ζ * w) ''
            ((fun w : ℂ => ζ⁻¹ * w) '' (connectedComponentIn ((Set.range g)ᶜ) 0)) := by
        rw [hiter]
      rw [Set.image_image] at h
      have h3 : (fun x : ℂ => ζ * (ζ⁻¹ * x)) = id := by
        funext x
        show ζ * (ζ⁻¹ * x) = x
        rw [← mul_assoc, mul_inv_cancel₀ hζne0, one_mul]
      rw [h3, Set.image_id] at h
      exact h
    have hAeq : connectedComponentIn ((Set.range g)ᶜ) 0
        = connectedComponentIn ((Set.range gζ)ᶜ) 0 := by
      rw [himg, hζA]
    have hrange : Set.range g = Set.range gζ := by
      calc Set.range g = frontier (connectedComponentIn ((Set.range g)ᶜ) 0) := hfr0.symm
        _ = frontier (connectedComponentIn ((Set.range gζ)ᶜ) 0) := by rw [hAeq]
        _ = Set.range gζ := hfr1
    obtain ⟨w, hw⟩ := hne0
    exact (Set.disjoint_left.mp hdisj) hw (hrange ▸ hw)

/-! ## The main theorem -/

theorem winding_unimodular_of_bounded_component {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {a : ℂ} (ha : a ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a))
    {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθexp : ∀ t, Complex.exp (θ t) = γ (Circle.exp (2 * Real.pi * t)) - a)
    {m : ℤ} (hθper : ∀ t, θ (t + 1) = θ t + (m : ℂ) * (2 * Real.pi * Complex.I)) :
    m = 1 ∨ m = -1 := by
  have hm0 : m ≠ 0 := (boundedComponentIn_iff_period_ne_zero hγ ha hθc hθexp hθper).mp hbdd
  rcases lt_trichotomy m 0 with hlt | heq | hgt
  · -- `m < 0`: invert the configuration in the point `a`
    have hne : ∀ z : Circle, γ z - a ≠ 0 := fun z h => ha ⟨z, sub_eq_zero.mp h⟩
    let γ₃ : C(Circle, ℂ) := ⟨fun z => (γ z - a)⁻¹ + a,
      ((γ.continuous.sub continuous_const).fun_inv₀ hne).add continuous_const⟩
    have hγ₃inj : Function.Injective γ₃ := by
      intro x y h
      have h1 : (γ x - a)⁻¹ = (γ y - a)⁻¹ := by
        have h2 : (γ x - a)⁻¹ + a = (γ y - a)⁻¹ + a := h
        exact add_right_cancel h2
      have h2 : γ x - a = γ y - a := by
        rw [← inv_inv (γ x - a), ← inv_inv (γ y - a), h1]
      exact hγ (sub_left_inj.mp h2)
    have ha₃ : a ∉ Set.range γ₃ := by
      rintro ⟨z, hz⟩
      have h1 : (γ z - a)⁻¹ + a = a := hz
      have h2 : (γ z - a)⁻¹ = 0 :=
        add_right_cancel (b := a) (show (γ z - a)⁻¹ + a = 0 + a from by rw [zero_add]; exact h1)
      exact inv_ne_zero (hne z) h2
    have hθ₁c : Continuous (fun t : ℝ => -(θ t)) := hθc.neg
    have hθ₁exp : ∀ t, Complex.exp (-(θ t)) = γ₃ (Circle.exp (2 * Real.pi * t)) - a := by
      intro t
      rw [Complex.exp_neg, hθexp t]
      simp only [γ₃, ContinuousMap.coe_mk]
      ring
    have hθ₁per : ∀ t, -(θ (t + 1)) = -(θ t) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      intro t
      rw [hθper t]
      push_cast
      ring
    have hbdd₃ : Bornology.IsBounded (connectedComponentIn ((Set.range γ₃)ᶜ) a) :=
      (boundedComponentIn_iff_period_ne_zero hγ₃inj ha₃ hθ₁c hθ₁exp hθ₁per).mpr (by omega)
    have hres : -m = 1 := eq_one_of_pos hγ₃inj hbdd₃ hθ₁c hθ₁exp hθ₁per (by omega)
    omega
  · exact absurd heq hm0
  · exact Or.inl (eq_one_of_pos hγ hbdd hθc hθexp hθper hgt)

end Work.HornSC.CellBoundaryJordan
