import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.Galerkin.Ode

theorem hasDerivWithinAt_glue
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hfg : f b = g b) {v : ℝ → E}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (v x) (Set.Icc a b) x)
    (hg : ∀ x ∈ Set.Icc b c, HasDerivWithinAt g (v x) (Set.Icc b c) x) :
    ∀ x ∈ Set.Icc a c,
      HasDerivWithinAt (fun y : ℝ => if y ≤ b then f y else g y) (v x) (Set.Icc a c) x := by
  intro x hx
  rcases lt_trichotomy x b with hxb | hxb | hbx
  · -- Case `x < b`: locally the glued function agrees with `f`, and `f`'s derivative
    -- within `Icc a b` transfers to `Icc a c` because `Icc a b` contains a relative
    -- neighbourhood of `x` in `Icc a c`.
    have hmem : Set.Icc a b ∈ 𝓝[Set.Icc a c] x := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Iio b, isOpen_Iio, hxb, ?_⟩
      rintro y ⟨hy1, hy2⟩
      exact ⟨hy2.1, le_of_lt hy1⟩
    have hev : (fun y : ℝ => if y ≤ b then f y else g y) =ᶠ[𝓝[Set.Icc a c] x] f := by
      filter_upwards [show Set.Iic b ∈ 𝓝[Set.Icc a c] x from
        nhdsWithin_le_nhds (Iic_mem_nhds hxb)] with y hy
      exact ite_eq_left hy
    exact ((hf x ⟨hx.1, hxb.le⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq hev
      (ite_eq_left hxb.le)
  · -- Case `x = b`: on `Icc a b` the glued function is `f`, on `Icc b c` it is `g`;
    -- the two within-derivatives at `b` glue by the union rule for `HasDerivWithinAt`.
    rw [hxb]
    have h1 : HasDerivWithinAt (fun y : ℝ => if y ≤ b then f y else g y) (v b) (Set.Icc a b) b :=
      (hf b ⟨hab, le_rfl⟩).congr (fun y hy => ite_eq_left hy.2) (ite_eq_left le_rfl)
    have h2 : HasDerivWithinAt (fun y : ℝ => if y ≤ b then f y else g y) (v b) (Set.Icc b c) b :=
      (hg b ⟨le_rfl, hbc⟩).congr
        (fun y hy => by
          by_cases hyb : y ≤ b
          · rw [ite_eq_left hyb, show y = b from le_antisymm hyb hy.1, hfg]
          · exact ite_eq_right hyb)
        (by rw [ite_eq_left le_rfl, hfg])
    have hu := h1.union h2
    rwa [Set.Icc_union_Icc_eq_Icc hab hbc] at hu
  · -- Case `b < x`: symmetric to the first case, with `g` in place of `f`.
    have hmem : Set.Icc b c ∈ 𝓝[Set.Icc a c] x := by
      rw [mem_nhdsWithin]
      refine ⟨Set.Ioi b, isOpen_Ioi, hbx, ?_⟩
      rintro y ⟨hy1, hy2⟩
      exact ⟨le_of_lt hy1, hy2.2⟩
    have hev : (fun y : ℝ => if y ≤ b then f y else g y) =ᶠ[𝓝[Set.Icc a c] x] g := by
      filter_upwards [show Set.Ioi b ∈ 𝓝[Set.Icc a c] x from
        nhdsWithin_le_nhds (Ioi_mem_nhds hbx)] with y hy
      exact ite_eq_right (not_le.mpr hy)
    exact ((hg x ⟨hbx.le, hx.2⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq hev
      (ite_eq_right (not_le.mpr hbx))

end Work.FTS.Galerkin.Ode
