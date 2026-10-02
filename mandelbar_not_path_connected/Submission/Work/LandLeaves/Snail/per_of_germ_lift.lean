import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Periodicity of a germ lift

Let `F` be a holomorphic lift of `f` under the exponential map on the half plane
`{Z : ℂ | Z.re < X}`, i.e. `exp (F Z) = f (exp Z)` there, and suppose that
`F Z - Z → log λ` as `Re Z → -∞`.  Then `F` is equivariant under the translation
by `2 π I`:

`F (Z + 2 π I) = F Z + 2 π I` for every `Z` with `Re Z < X`.

The proof is the standard one.  The function `H Z = F (Z + 2 π I) - F Z` is
holomorphic on the (convex, hence preconnected) half plane, and takes values in
the discrete set `2 π I ℤ` because `exp (H Z) = 1`.  Hence `H` is constant,
say `H ≡ a`.  Writing
`H Z = (F (Z + 2πI) - (Z + 2πI)) - (F Z - Z) + 2πI`
and letting `Re Z → -∞` shows that `H Z → 2πI`, so `a = 2πI`.
-/

open Complex Filter

namespace Work.LandLeaves.Snail

theorem per_of_germ_lift {f F : ℂ → ℂ} {lam : ℂ} {X : ℝ}
    (hdiff : DifferentiableOn ℂ F {Z : ℂ | Z.re < X})
    (hexp : ∀ Z : ℂ, Z.re < X → Complex.exp (F Z) = f (Complex.exp Z))
    (hdrift : Filter.Tendsto (fun Z : ℂ => F Z - Z)
      (Filter.comap Complex.re Filter.atBot) (nhds (Complex.log lam))) :
    ∀ Z : ℂ, Z.re < X → F (Z + 2 * (Real.pi : ℂ) * I) = F Z + 2 * (Real.pi : ℂ) * I := by
  -- the period
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hc_re : c.re = 0 := by simp [c]
  -- the half plane
  have hUopen : IsOpen {Z : ℂ | Z.re < X} := isOpen_lt Complex.continuous_re continuous_const
  have hUpre : IsPreconnected {Z : ℂ | Z.re < X} := (convex_halfSpace_re_lt X).isPreconnected
  have hmap : Set.MapsTo (fun W : ℂ => W + c) {Z : ℂ | Z.re < X} {Z : ℂ | Z.re < X} := by
    intro W hW
    show (W + c).re < X
    rw [Complex.add_re, hc_re, add_zero]
    exact hW
  -- `H` is holomorphic on the half plane
  have hHdiff : DifferentiableOn ℂ (fun W : ℂ => F (W + c) - F W) {Z : ℂ | Z.re < X} :=
    (hdiff.comp (differentiableOn_id.add_const c) hmap).sub hdiff
  -- `exp (H Z) = 1`
  have hHval : ∀ W : ℂ, W.re < X → Complex.exp (F (W + c) - F W) = 1 := by
    intro W hW
    have hWc : W + c ∈ {Z : ℂ | Z.re < X} := hmap hW
    have h1 : Complex.exp (F (W + c)) = f (Complex.exp (W + c)) := hexp (W + c) hWc
    have h2 : Complex.exp (W + c) = Complex.exp W := Complex.exp_periodic W
    have h3 : Complex.exp (F W) = f (Complex.exp W) := hexp W hW
    have h4 : Complex.exp (F (W + c)) = Complex.exp (F W) := by rw [h1, h2, ← h3]
    exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp h4
  -- hence the derivative of `H` vanishes
  have hderiv0 : Set.EqOn (deriv (fun Y : ℂ => F (Y + c) - F Y)) 0 {Z : ℂ | Z.re < X} := by
    intro W hW
    have hHdiffAt : DifferentiableAt ℂ (fun Y : ℂ => F (Y + c) - F Y) W :=
      hHdiff.differentiableAt (hUopen.mem_nhds hW)
    have heq : (fun Y : ℂ => Complex.exp (F (Y + c) - F Y)) =ᶠ[nhds W] (fun _ => (1 : ℂ)) :=
      Filter.eventually_of_mem (hUopen.mem_nhds hW) (fun Y hY => hHval Y hY)
    have hd1 : deriv (fun Y : ℂ => Complex.exp (F (Y + c) - F Y)) W = 0 := by
      rw [heq.deriv_eq]; exact deriv_const W 1
    have hchain := deriv_comp W (h := fun Y : ℂ => F (Y + c) - F Y) (h₂ := Complex.exp)
      (Complex.differentiableAt_exp) hHdiffAt
    rw [Complex.deriv_exp] at hchain
    have hthis : Complex.exp (F (W + c) - F W) * deriv (fun Y : ℂ => F (Y + c) - F Y) W = 0 := by
      rw [← hchain]; exact hd1
    rw [hHval W hW, one_mul] at hthis
    simpa using hthis
  -- so `H` is constant on the half plane
  obtain ⟨a, ha⟩ := hUopen.exists_is_const_of_deriv_eq_zero hUpre hHdiff hderiv0
  -- the shift `W ↦ W + c` is a morphism for the filter `comap re atBot`
  have hmaps : Tendsto (fun W : ℂ => W + c) (comap Complex.re atBot) (comap Complex.re atBot) := by
    rw [Filter.tendsto_comap_iff]
    rw [show (Complex.re ∘ fun W : ℂ => W + c) = Complex.re from by
      ext W; simp [Complex.add_re, hc_re]]
    exact Filter.tendsto_comap
  -- drifting along `comap re atBot`, `H` tends to `c`
  have hA : Tendsto (fun W : ℂ => F (W + c) - (W + c)) (comap Complex.re atBot)
      (nhds (Complex.log lam)) := hdrift.comp hmaps
  have hC : Tendsto (fun W : ℂ => (F (W + c) - (W + c)) - (F W - W)) (comap Complex.re atBot)
      (nhds 0) := by
    have := hA.sub hdrift; simpa using this
  have hD : Tendsto (fun W : ℂ => ((F (W + c) - (W + c)) - (F W - W)) + c)
      (comap Complex.re atBot) (nhds c) := by
    have := hC.add_const c; simpa using this
  have hHlim : Tendsto (fun W : ℂ => F (W + c) - F W) (comap Complex.re atBot) (nhds c) := by
    refine hD.congr' (Filter.Eventually.of_forall (fun W => ?_))
    ring
  -- the half plane is a set of the filter, so `H` also tends to `a`
  have hU_mem : {Z : ℂ | Z.re < X} ∈ comap Complex.re (atBot : Filter ℝ) :=
    Filter.preimage_mem_comap (Filter.Iio_mem_atBot X)
  have hHev : (fun W : ℂ => F (W + c) - F W) =ᶠ[comap Complex.re atBot] (fun _ => a) :=
    Filter.eventually_of_mem hU_mem (fun W hW => ha W hW)
  have hHlim_a : Tendsto (fun W : ℂ => F (W + c) - F W) (comap Complex.re atBot) (nhds a) :=
    Filter.Tendsto.congr' hHev.symm tendsto_const_nhds
  -- uniqueness of limits
  have hNeBot : (comap Complex.re (atBot : Filter ℝ)).NeBot :=
    Filter.atBot_neBot.comap_of_surj Complex.re_surjective
  have hac : a = c :=
    @tendsto_nhds_unique ℂ ℂ _ _ (fun W : ℂ => F (W + c) - F W)
      (comap Complex.re (atBot : Filter ℝ)) a c hNeBot hHlim_a hHlim
  intro Z hZ
  have hZc : F (Z + c) - F Z = a := ha Z hZ
  have hfin : F (Z + c) = F Z + c := sub_eq_iff_eq_add'.mp (hZc.trans hac)
  show F (Z + c) = F Z + c
  exact hfin

end Work.LandLeaves.Snail
