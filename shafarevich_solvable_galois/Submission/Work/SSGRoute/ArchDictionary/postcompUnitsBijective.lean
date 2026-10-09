import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open Additive

/-- Postcomposition with `e : Fˣ →* Lˣ` is a bijection on the additive homomorphism
groups out of a `2`-torsion group `V`.

Injectivity is injectivity of `e`; surjectivity holds because any `φ : V →+ Additive Lˣ`
lands in the `2`-torsion of `Lˣ`, which for a field is `{1, -1} ⊆ e(Fˣ)` (using
`e (-1) = -1`). -/
theorem postcompUnitsBijective {F L V : Type} [Field F] [Field L] [AddCommGroup V]
    (e : Fˣ →* Lˣ) (hinj : Function.Injective e) (hneg : e (-1) = -1)
    (hnegne : (-1 : Lˣ) ≠ 1)
    (hV : ∀ v : V, (2 : ℕ) • v = 0) :
    Function.Bijective (fun g : V →+ Additive Fˣ => (MonoidHom.toAdditive e).comp g) := by
  classical
  let f : Additive Fˣ →+ Additive Lˣ := MonoidHom.toAdditive e
  have hf_apply : ∀ x : Additive Fˣ, f x = ofMul (e (Additive.toMul x)) := by
    intro x; simp [f]
  -- `f` is injective because `e` is
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h : e (Additive.toMul x) = e (Additive.toMul y) := by
      have hh := congrArg Additive.toMul hxy
      simpa [hf_apply] using hh
    have h2 := hinj h
    rw [← ofMul_toMul x, h2, ofMul_toMul y]
  constructor
  · -- injectivity of `g ↦ f.comp g`
    intro g g' hgg'
    apply AddMonoidHom.ext
    intro v
    apply hfinj
    have hv := congrArg (fun (ψ : V →+ Additive Lˣ) => ψ v) hgg'
    exact hv
  · -- surjectivity: every `φ` takes values in `e(Fˣ)`
    intro φ
    have hφ : ∀ v : V, ∃ x : Fˣ, ofMul (e x) = φ v := by
      intro v
      -- `φ v` lies in the `2`-torsion of `Lˣ`
      have hv : (2 : ℕ) • φ v = 0 := by
        have hh := map_nsmul φ 2 v
        rw [hV v, map_zero] at hh
        exact hh.symm
      have h0 : Additive.toMul (0 : Additive Lˣ) = 1 := rfl
      have h1 : Additive.toMul (φ v) ^ 2 = 1 := by
        have hh : Additive.toMul (φ v) ^ 2 = Additive.toMul (0 : Additive Lˣ) := by
          rw [← toMul_nsmul]; exact congrArg Additive.toMul hv
        rw [h0] at hh; exact hh
      -- in a field the only solutions of `x ^ 2 = 1` are `±1`
      have h2 : ((Additive.toMul (φ v) : Lˣ) : L) ^ 2 = 1 := by
        have hh := congrArg (fun z : Lˣ => (z : L)) h1
        simpa using hh
      rcases sq_eq_one_iff.mp h2 with h3 | h3
      · refine ⟨1, ?_⟩
        have hthis : Additive.toMul (φ v) = 1 := Units.ext h3
        rw [map_one, ← hthis, ofMul_toMul]
      · refine ⟨-1, ?_⟩
        have hthis : Additive.toMul (φ v) = -1 :=
          Units.ext (by rw [h3, Units.val_neg, Units.val_one])
        rw [hneg, ← hthis, ofMul_toMul]
    let gfun : V → Additive Fˣ := fun v => ofMul (Classical.choose (hφ v))
    have hg : ∀ v, f (gfun v) = φ v := by
      intro v
      rw [hf_apply]
      show ofMul (e (Classical.choose (hφ v))) = φ v
      exact Classical.choose_spec (hφ v)
    have gadd : ∀ a b : V, gfun (a + b) = gfun a + gfun b := by
      intro a b
      apply hfinj
      rw [map_add f, hg (a + b), hg a, hg b, map_add φ]
    refine ⟨AddMonoidHom.mk' gfun gadd, ?_⟩
    apply AddMonoidHom.ext
    intro v
    rw [AddMonoidHom.comp_apply]
    show f (gfun v) = φ v
    exact hg v

end Work.SSGRoute.ArchDictionary
