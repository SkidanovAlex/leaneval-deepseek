import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.PoleCond
import Submission.Work.MotC2.SubstCoeffs
import Submission.Work.MotC2.ExistsVariableChange
import Submission.Work.MotC2.AutEExplicit
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

/-!
## Auxiliary lemmas for `Work.MotC2.VariableChange`

* `mem_affRing` — `affRing E` is exactly the image of the coordinate ring `Coord E` in `L(E)`;
* `coordX_ne_const` / `genX_ne_const` — `x` is not a constant in `L(E)`, proved from the
  fact that `{1, y}` is a basis of `Coord E` over `L[X]`;
* `funcAlgEquiv_ext_genX_genY` — two `L`-algebra automorphisms of `L(E)` agreeing on `x` and `y` are equal
  (since `x`, `y` generate `L(E)` over `L` as a field).
-/

variable {L : Type*} [Field L]

/-- `affRing E` is the image of the coordinate ring `Coord E` inside `L(E)`. -/
private lemma mem_affRing_image (E : WeierstrassCurve L) (x : Func E) :
    x ∈ affRing E ↔ ∃ r : Coord E, algebraMap (Coord E) (Func E) r = x := by
  unfold affRing
  set φ : Coord E →ₐ[L] Func E := Algebra.algHom L _ _ with hφ
  constructor
  · intro hx
    have hle : Algebra.adjoin L (Set.range (algebraMap (Coord E) (Func E))) ≤ φ.range :=
      Algebra.adjoin_le (by rintro y ⟨r, rfl⟩; exact ⟨r, rfl⟩)
    obtain ⟨r, hr⟩ := (AlgHom.mem_range (φ := φ)).mp (hle hx)
    exact ⟨r, hr⟩
  · rintro ⟨r, rfl⟩
    exact Algebra.subset_adjoin ⟨r, rfl⟩

/-- The class of `X` in `L[X,Y]/(W_E)` is not a constant. -/
private lemma coordX_ne_const (E : WeierstrassCurve L) (a : L) :
    coordX E ≠ algebraMap L (Coord E) a := by
  intro h
  have h1 : algebraMap (Polynomial L) (Coord E) Polynomial.X = algebraMap L (Coord E) a := by
    rw [algebraMap_X_eq_coordX, h]
  have h1' : algebraMap (Polynomial L) (Coord E) (Polynomial.C a) = algebraMap L (Coord E) a := by
    rw [Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply L (Polynomial L) (Coord E)]
  have h2 : algebraMap (Polynomial L) (Coord E) (Polynomial.X - Polynomial.C a) = 0 := by
    rw [map_sub, h1, h1', sub_self]
  have h3 : (Polynomial.X - Polynomial.C a) • (1 : Coord E) = 0 := by
    rw [← Algebra.algebraMap_eq_smul_one]; exact h2
  have h4 : Polynomial.X - Polynomial.C a = 0 := by
    have hh := CoordinateRing.smul_basis_eq_zero (W' := E)
      (p := Polynomial.X - Polynomial.C a) (q := 0) (by simpa using h3)
    exact hh.1
  exact Polynomial.X_sub_C_ne_zero a h4

/-- The coordinate `x` of `L(E)` is not a constant. -/
private lemma genX_ne_const (E : WeierstrassCurve L) (a : L) :
    genX E ≠ algebraMap L (Func E) a := by
  intro h
  have h1 : algebraMap (Coord E) (Func E) (coordX E)
      = algebraMap (Coord E) (Func E) (algebraMap L (Coord E) a) := by
    rw [← IsScalarTower.algebraMap_apply L (Coord E) (Func E)]
    exact h
  exact coordX_ne_const E a
    (IsFractionRing.injective (Coord E) (Func E) h1)

/-- Two `L`-algebra automorphisms of the function field `L(E)` which agree on `x` and `y` are
equal: they agree on the whole coordinate ring `Coord E` (as `L`-algebra homomorphisms out of an
`AdjoinRoot` are determined by their value on the root `y` and on `L[X]`), and `L(E)` is the
fraction field of `Coord E`. -/
private lemma funcAlgEquiv_ext_genX_genY (E : WeierstrassCurve L) (f g : Func E ≃ₐ[L] Func E)
    (hX : f (genX E) = g (genX E)) (hY : f (genY E) = g (genY E)) : f = g := by
  have h : f.toAlgHom = g.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Coord E))
    apply AdjoinRoot.algHom_ext' (S := L) (R := Polynomial L)
      (p := WeierstrassCurve.Affine.polynomial E)
    · apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply]
      exact hX
    · exact hY
  ext z
  exact AlgHom.congr_fun h z

/-
Route.  From `hO` (Θ fixes the local ring `infPlace E` of the point at infinity) one gets
`(Θ (genX E)) * (infW E)^2 ∈ infPlace E` and `(Θ (genY E)) * (infW E)^3 ∈ infPlace E`
(this is `Work.MotC2.PoleCond`).  With `hR`, both `Θ (genX E)` and `Θ (genY E)` lie in `affRing E`
(they are the images of elements of `Coord E`), so `PoleOrder` applies and gives
`Θ (genX E) = a + b·genX E`, `Θ (genY E) = c + d·genX E + e·genY E` with `a,…,e ∈ L`.
Substituting into the Weierstrass relation (`Relations`) and comparing coefficients as polynomials
in `genX E, genY E` (using `smul_basis_eq_zero` for the uniqueness of the decomposition
`p(x) + q(x)y`; this is `Work.MotC2.SubstCoeffs`) gives six scalar relations in `a, b, c, d, e`;
they say precisely that `C = (e/b, a, d/b, c)` is an admissible `WeierstrassCurve.VariableChange`
with `C • E = E` and that the substitution is `x ↦ u²x + r`, `y ↦ u³y + s u²x + t` with
`u = e/b`, `r = a`, `s = d/b`, `t = c` (`Work.MotC2.ExistsVariableChange`); the case `e = 0` is
impossible because it forces `Θ (genX E) = a ∈ L`.  Finally `Work.MotC2.AutEExplicit` says that such
a `C` is either `1` or the negation `(-1, 0, -a₁, -a₃)`, which gives the two cases of the
conclusion.
-/
theorem VariableChange (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (hj0 : E.j ≠ 0) (hj : E.j ≠ 1728) (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E)
    (hR : Subalgebra.map Θ.toAlgHom (Work.MotC2.affRing E) = Work.MotC2.affRing E)
    (hO : Subalgebra.map Θ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E) :
    Θ = 1 ∨ (Θ (Work.MotC2.genX E) = Work.MotC2.genX E ∧
      Θ (Work.MotC2.genY E) = - Work.MotC2.genY E -
        algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E -
        algebraMap L (Work.MotC2.Func E) E.a₃) := by
  -- Step 1: `Θ x` and `Θ y` lie in `affRing E`, hence in the image of the coordinate ring.
  have hxmem : Θ (genX E) ∈ affRing E := by
    have h1 : genX E ∈ affRing E := (mem_affRing_image E _).mpr ⟨coordX E, rfl⟩
    have h2 : Θ (genX E) ∈ Subalgebra.map Θ.toAlgHom (affRing E) :=
      Subalgebra.mem_map.mpr ⟨genX E, h1, rfl⟩
    rwa [hR] at h2
  obtain ⟨r₁, hr₁⟩ := (mem_affRing_image E _).mp hxmem
  have hymem : Θ (genY E) ∈ affRing E := by
    have h1 : genY E ∈ affRing E := (mem_affRing_image E _).mpr ⟨coordY E, rfl⟩
    have h2 : Θ (genY E) ∈ Subalgebra.map Θ.toAlgHom (affRing E) :=
      Subalgebra.mem_map.mpr ⟨genY E, h1, rfl⟩
    rwa [hR] at h2
  obtain ⟨r₂, hr₂⟩ := (mem_affRing_image E _).mp hymem
  -- Step 2: the pole conditions at infinity.
  obtain ⟨hpx, hpy⟩ := PoleCond L E Θ hO
  rw [← hr₁] at hpx
  rw [← hr₂] at hpy
  -- Step 3: pole order at the point at infinity.
  obtain ⟨a, b, hab⟩ := ((PoleOrder L E).1 r₁).mp hpx
  obtain ⟨c, d, e, hcde⟩ := ((PoleOrder L E).2 r₂).mp hpy
  have hx : Θ (genX E) = algebraMap L (Func E) a + algebraMap L (Func E) b * genX E := by
    rw [← hr₁, hab]
  have hy : Θ (genY E) = algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
      algebraMap L (Func E) e * genY E := by
    rw [← hr₂, hcde]
  -- Step 4: the substituted Weierstrass relation, and its coefficient relations.
  have hrel : (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
          algebraMap L (Func E) e * genY E) ^ 2
        + algebraMap L (Func E) E.a₁ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) *
            (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
              algebraMap L (Func E) e * genY E)
        + algebraMap L (Func E) E.a₃ *
            (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
              algebraMap L (Func E) e * genY E)
      = (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 3
        + algebraMap L (Func E) E.a₂ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 2
        + algebraMap L (Func E) E.a₄ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E)
        + algebraMap L (Func E) E.a₆ := by
    have h := congrArg (⇑Θ) (genY_sq_relation E)
    simp only [map_add, map_mul, map_pow, AlgEquiv.commutes] at h
    rw [hx, hy] at h
    exact h
  obtain ⟨h3, hQ1, hQ0, hP2, hP1, hP0⟩ := SubstCoeffs L E a b c d e hrel
  -- Step 5: `e ≠ 0` (otherwise `Θ x` would be the constant `a`).
  have he : e ≠ 0 := by
    intro he0
    have hb0 : b = 0 := by
      have h := h3
      rw [he0] at h
      exact eq_zero_of_pow_eq_zero (n := 3) (by simpa using h.symm)
    have hxc : Θ (genX E) = algebraMap L (Func E) a := by
      rw [hx, hb0]
      simp
    have hxa : genX E = algebraMap L (Func E) a := by
      have h := congrArg (⇑Θ.symm) hxc
      simpa using h
    exact genX_ne_const E a hxa
  have hb : b ≠ 0 := by
    intro hb0
    exact he (eq_zero_of_pow_eq_zero (n := 2) (by rw [h3, hb0]; ring))
  -- Step 6: build the variable change `(e/b, a, d/b, c)` stabilising `E`.
  obtain ⟨C, hCsmul, hCr, hCu, hCs, hCt⟩ :=
    ExistsVariableChange L E a b c d e hb he h3 hQ1 hQ0 hP2 hP1 hP0
  have hb1_of : (e = b ∨ e = -b) → b = 1 := by
    rintro (h' | h')
    · have h : b ^ 3 = b ^ 2 := by rw [← h3, h']
      exact mul_left_cancel₀ (pow_ne_zero 2 hb) (by rw [mul_one, ← pow_succ]; exact h)
    · have h : b ^ 3 = b ^ 2 := by rw [← h3, h']; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hb) (by rw [mul_one, ← pow_succ]; exact h)
  rcases AutEExplicit L E hj0 hj C hCsmul with hC1 | ⟨hu, hr, hs, ht⟩
  · -- `C = 1`, so `Θ` is the identity.
    left
    have hC1' : (C.u : L) = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
      rw [hC1]
      exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨hu1, hr0, hs0, ht0⟩ := hC1'
    have hreb : e / b = 1 := by rw [← hCu, hu1]
    have heb : e = b := by
      have h := hreb
      rw [div_eq_iff hb] at h
      simpa using h
    have ha0 : a = 0 := by rw [← hCr, hr0]
    have hc0 : c = 0 := by rw [← hCt, ht0]
    have hd0 : d = 0 := by
      have h : d / b = 0 := by rw [← hCs, hs0]
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' hb
    have hb1 : b = 1 := hb1_of (Or.inl heb)
    have he1 : e = 1 := by rw [heb, hb1]
    refine funcAlgEquiv_ext_genX_genY E Θ 1 ?_ ?_
    · show Θ (genX E) = genX E
      rw [hx, ha0, hb1]; simp
    · show Θ (genY E) = genY E
      rw [hy, hc0, hd0, he1]; simp
  · -- `C` is the negation, so `Θ` is the negation formula.
    right
    have hu' : (C.u : L) = -1 := by rw [hu]; rfl
    have hreb : e / b = -1 := by rw [← hCu]; exact hu'
    have heb : e = -b := by
      have h := hreb
      rw [div_eq_iff hb] at h
      simpa using h
    have hb1 : b = 1 := hb1_of (Or.inr heb)
    have he1 : e = -1 := by rw [heb, hb1]
    have ha0 : a = 0 := by rw [← hCr, hr]
    have hc0 : c = -E.a₃ := by rw [← hCt, ht]
    have hd0 : d = -E.a₁ := by
      have h : d / b = -E.a₁ := by rw [← hCs, hs]
      rw [div_eq_iff hb] at h
      simpa [hb1] using h
    constructor
    · show Θ (genX E) = genX E
      rw [hx, ha0, hb1]; simp
    · show Θ (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
        algebraMap L (Func E) E.a₃
      rw [hy, hc0, hd0, he1]
      simp only [map_neg, map_one, neg_mul, one_mul]
      first | refl_ring1 | ring

end Work.MotC2
