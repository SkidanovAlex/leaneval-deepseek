import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Ext-side definitions for the base case `φ¹` at the trivial module `𝔽_p`

This file collects the *definitions* (with their elementary proofs) that the proof of
`Work.SSGRoute.phi1_trivial_mono` and the lemmas it is split into use:

* `unitMulByP` — multiplication by `p` on the trivial representation `Coeff = ULift ℤ`;
* `unitToZMod` — the quotient map `Coeff ↠ 𝔽_p`;
* `coeffSES` — the short complex `0 → ℤ --p--> ℤ → 𝔽_p → 0` of trivial representations, and
  `coeffSES_shortExact`;
* `powHomCls` — the map `ℤ → C_L`, `1 ↦ a`, attached to a `Gal(L/k)`-fixed element `a` of the
  idèle class group `C_L` (the `H⁰`-slot of the cup product at the level of coefficients).

The point of the Ext-side computation is that the connecting map of `coeffSES`,
`(coeffSES G p).extClass ∈ Ext¹(𝔽_p, ℤ)`, identifies `Ext¹_G(𝔽_p, C)` with `C^G / pC^G`: every
class is `extClass.comp (mk₀ φ)` for a `G`-map `φ : ℤ → C`, and it vanishes exactly when `φ`
factors through `unitMulByP`.
-/

namespace Work.SSGRoute.Phi1

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

variable (G : Type) [Group G]

/-- Multiplication by `p` on the trivial representation with coefficients `Coeff = ULift ℤ`. -/
def unitMulByP (p : ℕ) : unitRep G ⟶ unitRep G :=
  Rep.ofHom
    { toLinearMap := (p : Coeff) • (1 : Coeff →ₗ[Coeff] Coeff)
      isIntertwining' := fun g => by
        ext x
        simp }

@[simp] lemma unitMulByP_apply (p : ℕ) (x : Coeff) :
    (Rep.Hom.hom (unitMulByP G p)) x = (p : Coeff) * x := rfl

/-- The quotient map `Coeff = ULift ℤ → 𝔽_p`. -/
def unitToZMod (p : ℕ) : unitRep G ⟶ Rep.trivial Coeff G (ZMod p) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => (x.down : ZMod p)
          map_add' := fun x y => by simp [Int.cast_add]
          map_smul' := fun c x => by
            show ((c • x).down : ZMod p) = (RingHom.id Coeff) c • (x.down : ZMod p)
            simp [ULift.smul_def] }
      isIntertwining' := fun g => by
        rw [Rep.trivial_ρ, Rep.trivial_ρ]
        ext x
        simp }

@[simp] lemma unitToZMod_apply (p : ℕ) (x : Coeff) :
    (Rep.Hom.hom (unitToZMod G p)) x = (x.down : ZMod p) := rfl

/-- **The coefficient sequence** `0 → ℤ --(p)--> ℤ → 𝔽_p → 0` of trivial representations. -/
def coeffSES (p : ℕ) : ShortComplex (Rep Coeff G) :=
  ShortComplex.mk (unitMulByP G p) (unitToZMod G p) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show (((p : Coeff) * x).down : ZMod p) = 0
    simp)

/-- **The coefficient sequence is short exact** (`p` prime, in particular `p ≠ 0`). -/
theorem coeffSES_shortExact (p : ℕ) [Fact p.Prime] : (coeffSES G p).ShortExact := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp_int : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (coeffSES G p) ?_ ?_ ?_
  · rw [coeffSES, Rep.mono_iff_injective]
    intro x y hxy
    have h : (p : Coeff) * x = (p : Coeff) * y := hxy
    have h' : (p : ℤ) * x.down = (p : ℤ) * y.down := congrArg ULift.down h
    have := mul_left_cancel₀ hp_int h'
    exact ULift.ext this
  · rw [coeffSES, Rep.epi_iff_surjective]
    intro y
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective y
    refine ⟨ULift.up n, ?_⟩
    show ((n : ℤ) : ZMod p) = y
    simpa using hn
  · rintro x hx
    have hx' : ((x.down : ℤ) : ZMod p) = 0 := hx
    have hdvd : (p : ℤ) ∣ x.down := (ZMod.intCast_zmod_eq_zero_iff_dvd x.down p).mp hx'
    obtain ⟨m, hm⟩ := hdvd
    refine ⟨ULift.up m, ?_⟩
    show (unitMulByP G p) (ULift.up m) = x
    rw [unitMulByP_apply]
    apply ULift.ext
    show (p : ℤ) * m = x.down
    rw [hm]

variable {G}

/-- **The `H⁰`-slot of the cup product for a class-group representation**: for a `G`-fixed element
`a` of `classesK k L`, the `G`-map `ℤ → C_L`, `1 ↦ a`. -/
def powHomCls (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    (a : classesK k L) (hafix : ∀ σ : L ≃ₐ[k] L, (classesK k L).ρ σ a = a) :
    unitRep (L ≃ₐ[k] L) ⟶ classesK k L :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun n => n • a
          map_add' := fun m n => by
            show (m + n) • a = m • a + n • a
            exact add_smul m n a
          map_smul' := fun c n => by
            show (c • n) • a = (RingHom.id Coeff) c • (n • a)
            rw [smul_eq_mul, RingHom.id_apply]
            exact (smul_smul c n a).symm }
      isIntertwining' := fun σ => by
        rw [Rep.trivial_ρ]
        apply LinearMap.ext
        intro n
        show (n • a : classesK k L) = (classesK k L).ρ σ (n • a)
        rw [map_smul, hafix σ] }

@[simp] lemma powHomCls_apply (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] (a : classesK k L)
    (hafix : ∀ σ : L ≃ₐ[k] L, (classesK k L).ρ σ a = a) (n : Coeff) :
    (Rep.Hom.hom (powHomCls k L a hafix)) n = n • a := rfl

end

end Work.SSGRoute.Phi1

namespace Work.SSGRoute.Phi1

open CategoryTheory
open SSGRoute.PTExt

/-- **The `Ext`/group-cohomology bridge package** (node `E0b`, restricted to coefficient changes
at a fixed group).

The statement of the package is that there is a family of additive isomorphisms
`groupCohomology A n ≃+ extH A n`, natural in the coefficient module at a fixed group (`naturality`)
and compatible with the connecting maps of short exact sequences up to sign (`delta`).  Packaging
it as a structure keeps the statements in the files that use it short. -/
structure ExtGroupCohomologyBridge where
  /-- the additive isomorphisms `Hⁿ(G, A) ≃ Extⁿ_G(ℤ, A)`. -/
  e : ∀ (n : ℕ) (G : Type) [Group G] (A : Rep SSGRoute.PTExt.Coeff G),
    groupCohomology A n ≃+ SSGRoute.PTExt.extH A n
  /-- naturality in the coefficient module (at the fixed group). -/
  naturality : ∀ (n : ℕ) (G : Type) [Group G] (A B : Rep SSGRoute.PTExt.Coeff G) (φ : A ⟶ B)
    (y : groupCohomology A n),
    e n G B ((groupCohomology.map (MonoidHom.id G) φ n).hom y) =
      ((e n G A y).comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero n))
  /-- compatibility with the connecting maps of short exact sequences, up to sign. -/
  delta : ∀ (n : ℕ) (G : Type) [Group G] (S : ShortComplex (Rep SSGRoute.PTExt.Coeff G))
    (hS : S.ShortExact) (y : groupCohomology S.X₃ n),
    e (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
        (e n G S.X₃ y).comp hS.extClass rfl ∨
      e (n + 1) G S.X₁ ((groupCohomology.δ hS n (n + 1) rfl).hom y) =
        -((e n G S.X₃ y).comp hS.extClass rfl)

end Work.SSGRoute.Phi1
