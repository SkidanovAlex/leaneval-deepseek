import Mathlib

namespace Work.WilE4.CAD

/-- If a continuous function `F : X × ℝ → ℝ` is non-zero on the segment `{x₀} × [a,b]`, then for
all `x` near `x₀` the sign of `F (x, y)` on `[a, b]` is the sign of `F (x₀, y)`. -/
theorem sign_stable_Icc {X : Type*} [TopologicalSpace X] {F : X × ℝ → ℝ} (hF : Continuous F)
    {x₀ : X} {a b : ℝ} (hne : ∀ y ∈ Set.Icc a b, F (x₀, y) ≠ 0) :
    Filter.Eventually (fun x => ∀ y ∈ Set.Icc a b,
      SignType.sign (F (x, y)) = SignType.sign (F (x₀, y))) (nhds x₀) := by
  -- For each point `y` of `[a,b]` we find a product neighbourhood `U ×ˢ I` of `(x₀, y)` on which the
  -- sign of `F` equals the (non-zero) sign of `F (x₀, y)`: `F` is continuous, so it stays on the
  -- same side of `0` on a neighbourhood of a point where it is non-zero.
  have key : ∀ p : {y : ℝ // y ∈ Set.Icc a b}, ∃ U : Set X, ∃ I : Set ℝ,
      IsOpen U ∧ x₀ ∈ U ∧ IsOpen I ∧ p.val ∈ I ∧
      (∀ x ∈ U, ∀ z ∈ I, SignType.sign (F (x, z)) = SignType.sign (F (x₀, p.val))) := by
    rintro ⟨y, hy⟩
    have hne0 : F (x₀, y) ≠ 0 := hne y hy
    rcases lt_trichotomy (F (x₀, y)) 0 with hlt | heq | hgt
    · have hS : IsOpen (F ⁻¹' (Set.Iio 0)) := hF.isOpen_preimage _ isOpen_Iio
      rcases (isOpen_prod_iff.mp hS x₀ y hlt) with ⟨u, v, hu, hv, hxu, hyv, hsub⟩
      exact ⟨u, v, hu, hxu, hv, hyv, fun x hx z hz => by
        rw [sign_neg (hsub (Set.mem_prod.mpr ⟨hx, hz⟩)), sign_neg hlt]⟩
    · exact absurd heq hne0
    · have hS : IsOpen (F ⁻¹' (Set.Ioi 0)) := hF.isOpen_preimage _ isOpen_Ioi
      rcases (isOpen_prod_iff.mp hS x₀ y hgt) with ⟨u, v, hu, hv, hxu, hyv, hsub⟩
      exact ⟨u, v, hu, hxu, hv, hyv, fun x hx z hz => by
        rw [sign_pos (hsub (Set.mem_prod.mpr ⟨hx, hz⟩)), sign_pos hgt]⟩
  choose U I hUo hxU hIo hyI hsign using key
  -- The second coordinates of these neighbourhoods cover the compact interval `[a,b]`.
  have hcover : Set.Icc a b ⊆ ⋃ p : {y : ℝ // y ∈ Set.Icc a b}, I p := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyI ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover I (fun p => hIo p) hcover
  -- Intersecting the finitely many first coordinates gives a neighbourhood of `x₀` on which the
  -- sign is everywhere the same as on `{x₀} × [a,b]`.
  refine Filter.eventually_iff_exists_mem.mpr ⟨⋂ p ∈ t, U p, ?_, ?_⟩
  · exact IsOpen.mem_nhds (isOpen_biInter_finset (fun p _ => hUo p))
      (Set.mem_biInter (fun p _ => hxU p))
  · intro x hx y hy
    rcases Set.mem_iUnion₂.mp (ht hy) with ⟨p, hpt, hyp⟩
    rw [hsign p x (Set.mem_iInter₂.mp hx p hpt) y hyp, hsign p x₀ (hxU p) y hyp]

end Work.WilE4.CAD
