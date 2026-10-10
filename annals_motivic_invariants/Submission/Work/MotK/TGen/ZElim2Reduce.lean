import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZElim2Reduce`

Reduction of the irreducibility of the plane eliminant `ZElim2 a b h` to the irreducibility
of the normalised quintic `g0p (b/a)` over the algebraic closure.

`ZElim2 a b h` is `a^8` times the diagonal substitution `(X0,X1) ↦ (w²X0, wX1)` (`w^5 = h`)
of `g0p (b/a)` (see `ZElim2_identity` below); over an algebraically closed field a fifth root
`w` of `h` always exists, the substitution is an invertible linear change of variables, and
base change along `K → K̄` reflects irreducibility.  Hence irreducibility over `K̄` of `g0p (b/a)`
implies irreducibility over `K` of `ZElim2 a b h`.

The two ingredients are proved in full here: the substitution is an `AlgEquiv` (`zsEquiv`,
giving `irreducible_zshom`), and `MvPolynomial.map` along an injective field hom reflects
irreducibility (`irreducible_of_map_irreducible`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.MotK.TGen

open MvPolynomial

/-- The diagonal substitution `(X₀,X₁) ↦ (s²X₀, sX₁)` of `K[X₀,X₁]`, as a `K`-algebra
endomorphism. -/
private noncomputable def zsHom {L : Type*} [CommSemiring L] (s : L) :
    MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L :=
  MvPolynomial.aeval
    ![MvPolynomial.C (s ^ 2) * MvPolynomial.X 0, MvPolynomial.C s * MvPolynomial.X 1]

private lemma zsHom_comp {L : Type*} [CommSemiring L] (s t : L) :
    (zsHom t).comp (zsHom s) = zsHom (t * s) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [zsHom] <;> ring

private lemma zsHom_one {L : Type*} [CommSemiring L] :
    zsHom (1 : L) = AlgHom.id L (MvPolynomial (Fin 2) L) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [zsHom]

/-- The diagonal substitution as an algebra equivalence (invertible when `s ≠ 0`). -/
private noncomputable def zsEquiv {L : Type*} [Field L] (s : L) (hs : s ≠ 0) :
    MvPolynomial (Fin 2) L ≃ₐ[L] MvPolynomial (Fin 2) L :=
  AlgEquiv.ofAlgHom (zsHom s) (zsHom s⁻¹)
    (by rw [zsHom_comp, mul_inv_cancel₀ hs, zsHom_one])
    (by rw [zsHom_comp, inv_mul_cancel₀ hs, zsHom_one])

/-- An invertible diagonal substitution preserves irreducibility. -/
private lemma irreducible_zshom {L : Type*} [Field L] (s : L) (hs : s ≠ 0)
    (p : MvPolynomial (Fin 2) L) : Irreducible (zsHom s p) ↔ Irreducible p := by
  rw [show zsHom s p = zsEquiv s hs p from rfl]
  exact MulEquiv.irreducible_iff (zsEquiv s hs)

/-- **Base change along an injective field hom reflects irreducibility**: if the image of `f`
under `K[X₀,X₁] → L[X₀,X₁]` is irreducible, so is `f`.  (Contrapositive: a factorisation over
`K` survives coefficient extension, because `map` preserves the total degree for injective
coefficient maps, so it sends non-units to non-units.) -/
private lemma irreducible_of_map_irreducible {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (f : MvPolynomial (Fin 2) K)
    (h : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hφ : Function.Injective φ := φ.injective
  have hunit : ∀ g : MvPolynomial (Fin 2) K, IsUnit (MvPolynomial.map φ g) → IsUnit g := by
    intro g hg
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hg ⊢
    obtain ⟨r, hr, hgr⟩ := hg
    have hdeg : (MvPolynomial.map φ g).totalDegree = g.totalDegree := by
      rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree,
        MvPolynomial.support_map_of_injective g hφ]
    have h0 : g.totalDegree = 0 := by
      rw [← hdeg, hgr, MvPolynomial.totalDegree_C]
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
    refine ⟨g.coeff 0, ?_, h0⟩
    apply isUnit_iff_ne_zero.mpr
    have hcoeff : φ (g.coeff 0) = r := by
      rw [← MvPolynomial.coeff_map φ g 0, hgr]; simp
    intro hc
    exact hr.ne_zero (by rw [← hcoeff, hc, map_zero])
  refine ⟨?_, ?_⟩
  · intro hu
    exact h.not_isUnit (hu.map (MvPolynomial.map φ))
  · intro a b hab
    have hmap : MvPolynomial.map φ f = MvPolynomial.map φ a * MvPolynomial.map φ b := by
      rw [← map_mul, hab]
    exact (h.isUnit_or_isUnit hmap).imp (hunit a) (hunit b)

/-- Scaling the parameter by a fifth power is an invertible diagonal change of variables:
`ZElim2 a b (h·s⁵) = zsHom s (ZElim2 a b h)`. -/
private lemma ZElim2_scale' {L : Type*} [Field L] (a b h s : L) :
    Work.MotK.TwCensus.ZElim2 a b (h * s ^ 5)
      = zsHom s (Work.MotK.TwCensus.ZElim2 a b h) := by
  simp only [zsHom, Work.MotK.TwCensus.ZElim2, MvPolynomial.aeval_C, map_add, map_sub,
    map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  first | refl_ring1 | ring

/-- The normal form of `ZElim2` at the parameter `1`: `ZElim2 a b 1 = a⁸ · g0p (b/a)`. -/
private lemma ZElim2_one {L : Type*} [Field L] (a b : L) (ha : a ≠ 0) :
    MvPolynomial.C (a ^ 8) * Work.MotK.TGen.g0p (b / a)
      = Work.MotK.TwCensus.ZElim2 a b 1 := by
  have key : ∀ r : L, MvPolynomial.C (a ^ 8) * Work.MotK.TGen.g0p r
      = Work.MotK.TwCensus.ZElim2 a (a * r) 1 := by
    intro r
    simp only [Work.MotK.TGen.g0p, Work.MotK.TwCensus.ZElim2, map_add, map_mul, map_pow, map_one]
    first | refl_ring1 | ring
  have hb_eq : b = a * (b / a) := by field_simp
  conv_rhs => rw [hb_eq]
  exact key (b / a)

/-- The explicit twisting identity: with `w⁵ = h`, the plane eliminant `ZElim2 a b h` is `a⁸` times
the diagonal substitution `(X₀,X₁) ↦ (w²X₀, wX₁)` of `g0p (b/a)`. -/
private lemma ZElim2_identity {L : Type*} [Field L] (a b h w : L) (ha : a ≠ 0) (hw : w ^ 5 = h) :
    Work.MotK.TwCensus.ZElim2 a b h
      = MvPolynomial.C (a ^ 8) * zsHom w (Work.MotK.TGen.g0p (b / a)) := by
  rw [← hw, show w ^ 5 = 1 * w ^ 5 from (one_mul _).symm, ZElim2_scale', ← ZElim2_one a b ha]
  rw [map_mul]
  simp only [zsHom, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem ZElim2Reduce (K : Type) [Field K] (hk : ringChar K ≠ 5) (a b h : K) (ha : a ≠ 0)
    (hb : b ≠ 0) (hh : h ≠ 0)
    (hirr : Irreducible (Work.MotK.TGen.g0p (algebraMap K (AlgebraicClosure K) (b / a)))) :
    Irreducible (Work.MotK.TwCensus.ZElim2 a b h) := by
  set L := AlgebraicClosure K
  have hφ : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hha : algebraMap K L a ≠ 0 := fun h0 => ha (hφ (by rw [h0, map_zero]))
  have hhh : algebraMap K L h ≠ 0 := fun h0 => hh (hφ (by rw [h0, map_zero]))
  -- a fifth root of `h` in the algebraic closure
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K L h) (by norm_num : (0 : ℕ) < 5)
  have hwne : w ≠ 0 := by
    intro h0
    exact hhh (by rw [← hw, h0]; norm_num)
  -- coefficient extension of `ZElim2 a b h`
  have hmap : MvPolynomial.map (algebraMap K L) (Work.MotK.TwCensus.ZElim2 a b h)
      = Work.MotK.TwCensus.ZElim2 (algebraMap K L a) (algebraMap K L b)
          (algebraMap K L h) := by
    simp only [Work.MotK.TwCensus.ZElim2, map_add, map_sub, map_mul, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X, map_ofNat]
  have hid : MvPolynomial.map (algebraMap K L) (Work.MotK.TwCensus.ZElim2 a b h)
      = MvPolynomial.C ((algebraMap K L a) ^ 8)
        * zsHom w (Work.MotK.TGen.g0p ((algebraMap K L b) / (algebraMap K L a))) := by
    rw [hmap]
    exact ZElim2_identity (algebraMap K L a) (algebraMap K L b) (algebraMap K L h) w hha hw
  have hirr' : Irreducible (Work.MotK.TGen.g0p ((algebraMap K L b) / (algebraMap K L a))) := by
    rw [← map_div₀ (algebraMap K L) b a]
    exact hirr
  have h1 : Irreducible (zsHom w (Work.MotK.TGen.g0p ((algebraMap K L b) / (algebraMap K L a)))) :=
    (irreducible_zshom w hwne _).mpr hirr'
  have hCa : IsUnit (MvPolynomial.C ((algebraMap K L a) ^ 8) : MvPolynomial (Fin 2) L) := by
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
    exact ⟨_, isUnit_iff_ne_zero.mpr (pow_ne_zero 8 hha), rfl⟩
  have h2 : Irreducible (MvPolynomial.C ((algebraMap K L a) ^ 8)
      * zsHom w (Work.MotK.TGen.g0p ((algebraMap K L b) / (algebraMap K L a)))) :=
    (irreducible_isUnit_mul hCa).mpr h1
  rw [← hid] at h2
  exact irreducible_of_map_irreducible (algebraMap K L) (Work.MotK.TwCensus.ZElim2 a b h) h2

end Work.MotK.TGen
