import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology
/-- The powers of a unit complex number of infinite order are dense in the unit circle.
Hints: transfer to the additive circle: `AddCircle.denseRange_zsmul_iff` says the multiples of `a`
are dense in `AddCircle p` iff `addOrderOf a = 0`; or argue directly with the pigeonhole principle:
two of `1, lam, …, lam^N` have distance `< 2π/N`, so `lam ^ k` is close to `1` for some `1 ≤ k ≤ N`,
and then the multiples of `lam ^ k` give an ε-net of the circle. -/
theorem sphere_subset_closure_range_pow {lam : ℂ} (hlam : ‖lam‖ = 1) (hlam' : ¬ IsOfFinOrder lam) :
    Metric.sphere (0:ℂ) 1 ⊆ closure (Set.range fun k : ℕ => lam ^ k) := by
  -- transport `lam` to the unit circle `Circle`
  let L : Circle := ⟨lam, mem_sphere_zero_iff_norm.2 hlam⟩
  have hLcoe : (L : ℂ) = lam := rfl
  have hLcoe_pow : ∀ k : ℕ, ((L ^ k : Circle) : ℂ) = lam ^ k := fun k => by
    rw [Circle.coe_pow, hLcoe]
  -- pick `a : ℝ/ℤ` with `toCircle a = L`
  obtain ⟨a, ha⟩ := (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective L
  rw [AddCircle.homeomorphCircle_apply] at ha
  -- `a` has infinite additive order, because `lam` is not a root of unity
  have hord : addOrderOf a = 0 := by
    rw [addOrderOf_eq_zero_iff]
    intro hfin
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hfin
    obtain ⟨n, hn, hna⟩ := hfin
    apply hlam'
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hn, ?_⟩
    have h1 : ((L ^ n : Circle) : ℂ) = 1 := by
      rw [← ha, ← AddCircle.toCircle_nsmul a n, hna, AddCircle.toCircle_zero]
      rfl
    simpa only [Circle.coe_pow, hLcoe, Circle.coe_one] using h1
  -- the multiples of `a` are dense, for `ℤ` and hence for `ℕ`
  have hdense : DenseRange (fun n : ℤ => n • a : ℤ → AddCircle (1:ℝ)) :=
    (AddCircle.denseRange_zsmul_iff (a := a)).mpr hord
  have hdenseNat : DenseRange (fun k : ℕ => k • a : ℕ → AddCircle (1:ℝ)) :=
    denseRange_zsmul_iff_nsmul.mp hdense
  -- the map `ψ` from the circle of length `1` to the unit circle in `ℂ`
  let ψ : AddCircle (1:ℝ) → ℂ := fun x => (AddCircle.toCircle x : ℂ)
  have hψapply : ∀ x, ψ x = ((AddCircle.toCircle x : Circle) : ℂ) := fun x => rfl
  have hψcont : Continuous ψ := continuous_subtype_val.comp AddCircle.continuous_toCircle
  have hψrange : Set.range ψ = Metric.sphere (0:ℂ) 1 := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      rw [mem_sphere_zero_iff_norm]
      simp only [hψapply]
      simp
    · intro y hy
      obtain ⟨x, hx⟩ :=
        (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective (⟨y, hy⟩ : Circle)
      rw [AddCircle.homeomorphCircle_apply] at hx
      exact ⟨x, by rw [hψapply, hx]⟩
  -- the image of the dense set of multiples of `a` is dense in the sphere
  have hds : Dense (Set.range (fun k : ℕ => k • a : ℕ → AddCircle (1:ℝ))) := hdenseNat
  have hsub := Continuous.range_subset_closure_image_dense hψcont hds
  rw [hψrange] at hsub
  have himg : (ψ '' Set.range (fun k : ℕ => k • a : ℕ → AddCircle (1:ℝ)))
      = Set.range (fun k : ℕ => lam ^ k) := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext k
    simp only [Function.comp_apply, hψapply, AddCircle.toCircle_nsmul, ha]
    exact hLcoe_pow k
  rw [himg] at hsub
  exact hsub

end Work.LandLeaves
