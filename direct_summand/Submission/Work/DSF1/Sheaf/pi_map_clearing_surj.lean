import Mathlib

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

/-- If each component `φ b : F b ⟶ F' b` clears the denominator `h` (every element of `F' b`
is, up to multiplication by some power of `h`, in the image of `φ b`), then the product map
`Pi.map φ` clears the denominator `h` as well, with a *single* power of `h` working for the
whole finite product. -/
lemma pi_map_clearing_surj {R : Type} [CommRing R] {β : Type} [Fintype β]
    (F F' : β → ModuleCat R) (φ : ∀ b, F b ⟶ F' b) (h : R)
    (hcomp : ∀ b (z : ↥(F' b)), ∃ (k : ℕ) (t : ↥(F b)), (φ b).hom t = h ^ k • z) :
    ∀ z : ↥(∏ᶜ F'), ∃ (k : ℕ) (t : ↥(∏ᶜ F)),
      (CategoryTheory.Limits.Pi.map φ).hom t = h ^ k • z := by
  classical
  intro z
  -- Work componentwise: for each `b`, the `b`-th projection of `z` is hit by `φ b` up to
  -- a power of `h`.
  have hcomp' : ∀ b, ∃ (k : ℕ) (t : ↥(F b)),
      (φ b).hom t = h ^ k • (Pi.π F' b).hom z :=
    fun b => hcomp b ((Pi.π F' b).hom z)
  choose k s hs using hcomp'
  -- A single exponent dominating all the componentwise ones.
  have hK : ∀ b, k b ≤ ∑ y, k y := fun b =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ b)
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi F).inv.hom
    (fun b => h ^ ((∑ y, k y) - k b) • s b), ?_⟩
  -- Verify equality componentwise, using the projections.
  have hkey : ∀ b, (Pi.π F' b).hom
      ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
        (fun b => h ^ ((∑ y, k y) - k b) • s b)))
      = (Pi.π F' b).hom (h ^ (∑ y, k y) • z) := by
    intro b
    have hstep : (Pi.π F' b).hom
        ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
          (fun b => h ^ ((∑ y, k y) - k b) • s b)))
        = (φ b).hom ((Pi.π F b).hom ((ModuleCat.piIsoPi F).inv.hom
          (fun b => h ^ ((∑ y, k y) - k b) • s b))) := by
      have hh := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (Limits.Pi.map_π φ b))
        ((ModuleCat.piIsoPi F).inv.hom (fun b => h ^ ((∑ y, k y) - k b) • s b))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      exact hh
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hs b, smul_smul, ← pow_add, Nat.sub_add_cancel (hK b)]
    exact (map_smul (Pi.π F' b).hom (h ^ (∑ y, k y)) z).symm
  -- The product projections jointly detect equality: compose with the inverse isomorphism
  -- to a concrete function module.
  have h1 : (ModuleCat.piIsoPi F').hom.hom
      ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
        (fun b => h ^ ((∑ y, k y) - k b) • s b)))
      = (ModuleCat.piIsoPi F').hom.hom (h ^ (∑ y, k y) • z) := by
    funext b
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey b
  have h2 := congrArg (ModuleCat.piIsoPi F').inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

end Work.DSF1.Sheaf
