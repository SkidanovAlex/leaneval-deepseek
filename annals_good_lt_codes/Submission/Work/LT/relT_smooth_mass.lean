import Mathlib
import Submission.Work.LT.relT_defs

namespace Work.LT

/-! **Transport of the `χ`-isotypic `ℓ²`-mass along a dual permutation of character indices.**

`relT_smooth_mass` packages the elementary computation that underlies the "smoothness" estimate
for the Fourier mass: if applying the Fourier transform along the column subgroup to the left
translate `g ↦ f (y * g)` of `f` has the effect, on the character index, of a fixed *injective*
map `M` (the dual of the transvection by `y`), then the `ℓ²`-mass of any finite set `B` of
characters is transported by `M` from `B` to `B.image M`:

`l2sq (∑_{z∈B} fhat z (L_y f)) = ∑_{w ∈ B.image M} l2sq (fhat w f)`.

The two ingredients are (i) the sub-sum Plancherel hypothesis `hplan`, giving the splitting of
the mass of a sum into a sum of masses, and (ii) the invariance of `l2sq` under left translation
`g ↦ y * g` (`Equiv.sum_comp` with `Equiv.mulLeft y`), together with `Finset.sum_image` for the
injective reindexing. -/

theorem relT_smooth_mass :
    ∀ (p : ℕ) [Fact p.Prime] {a b c : Fin 3},
      ∀ (hplan : ∀ (h : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
            (B : Finset (ZMod p × ZMod p)),
            l2sq (fun g => ∑ z ∈ B, fhat p a b c z h g) = ∑ z ∈ B, l2sq (fhat p a b c z h))
        (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
        (y : Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
        (M : ZMod p × ZMod p → ZMod p × ZMod p) (hMinj : Function.Injective M),
        (∀ (z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z (fun x => f (y * x)) g = fhat p a b c (M z) f (y * g)) →
        ∀ B : Finset (ZMod p × ZMod p),
          l2sq (fun g => ∑ z ∈ B, fhat p a b c z (fun x => f (y * x)) g)
            = ∑ w ∈ B.image M, l2sq (fhat p a b c w f) := by
  intro p hp a b c hplan f y M hMinj hM B
  -- The `ℓ²`-mass of a single isotypic component is unchanged when the index is moved by `M`.
  have per_z : ∀ z, l2sq (fhat p a b c z (fun x => f (y * x))) = l2sq (fhat p a b c (M z) f) := by
    intro z
    unfold l2sq
    -- rewrite the summand pointwise using the dual-transvection hypothesis ...
    rw [Finset.sum_congr rfl (fun g _ => by rw [hM z g])]
    -- ... and reindex `g ↦ y * g`, a bijection of the group.
    rw [← Equiv.sum_comp (Equiv.mulLeft y)
      (fun g => Complex.normSq (fhat p a b c (M z) f g))]
    rfl
  -- Split the mass of the sum using the sub-sum Plancherel hypothesis.
  rw [hplan (fun x => f (y * x)) B]
  have hsum : ∑ z ∈ B, l2sq (fhat p a b c z (fun x => f (y * x)))
      = ∑ z ∈ B, l2sq (fhat p a b c (M z) f) :=
    Finset.sum_congr rfl (fun z _ => per_z z)
  -- Reindex `∑_{z ∈ B} g (M z) = ∑_{w ∈ B.image M} g w` using injectivity of `M`.
  rw [hsum, Finset.sum_image (g := M) (s := B) (fun x hx y hy hxy => hMinj hxy)]

end Work.LT
