import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_hypTorus

/-!
# `hypTorus F d` is cyclic for `d ≠ 0`

The "non-split torus" `hypTorus F d = closure {!![a, d*b; b, a] | a² - d·b² = 1}` of `SL(2,F)` is
a finite subgroup of an abelian group: for `ρ` with `ρ*ρ = d` in a commutative ring `R`, the
assignment `!![a, d*b; b, a] ↦ a + b·ρ` is multiplicative (`hypHom`), and it is injective in the
two cases:

* `d = c²` a square: map into the field `F` using `ρ = c` (`hypHom_id_injective`);
* `d` a nonsquare: map into the field `quadAlg F d = F[X]/(X²-d)` using `ρ = root`
  (`hypHom_root_injective`).

A finite subgroup of the units of an integral domain is cyclic (`isCyclic_of_injective_ringHom`),
which gives the result.
-/

open scoped MatrixGroups
open Matrix Polynomial

namespace Work.L2F.Conic

variable {F : Type*} [Field F]

/-! ## The quadratic algebra `F[X]/(X²-d)` -/

noncomputable section QuadPoly

/-- The polynomial `X² - d`. -/
abbrev quadPoly (d : F) : Polynomial F := Polynomial.X ^ 2 - Polynomial.C d

end QuadPoly

lemma quadPoly_monic (d : F) : (quadPoly d).Monic := monic_X_pow_sub_C d (by norm_num)

lemma quadPoly_natDegree (d : F) : (quadPoly d).natDegree = 2 := by
  rw [natDegree_X_pow_sub_C]

lemma quadPoly_degree (d : F) : (quadPoly d).degree = 2 := by
  rw [degree_X_pow_sub_C (by norm_num) d]; norm_num

lemma quadPoly_isRoot (d x : F) : (quadPoly d).IsRoot x ↔ x ^ 2 = d := by
  unfold quadPoly
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]

/-- If `d` is not a square then `X² - d` is irreducible. -/
lemma quadPoly_irreducible (d : F) (h : ∀ a : F, a * a ≠ d) : Irreducible (quadPoly d) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadPoly_natDegree]; norm_num
  · intro x hx
    rw [quadPoly_isRoot] at hx
    exact h x (by rw [← pow_two]; exact hx)

/-- If `d` is not a square then `X² - d` is prime, so its quotient is a domain. -/
lemma quadPoly_prime (d : F) (h : ∀ a : F, a * a ≠ d) : Prime (quadPoly d) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (quadPoly_irreducible d h)

/-- `F` embeds in its quadratic algebra. -/
lemma quadAlg_of_injective (d : F) : Function.Injective (AdjoinRoot.of (quadPoly d)) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos (quadPoly_monic d)
    (by rw [quadPoly_degree]; norm_num)

/-- The class of `X`, i.e. the formal square root of `d`, satisfies `root * root = d`. -/
lemma quadAlg_root_sq (d : F) :
    AdjoinRoot.root (quadPoly d) * AdjoinRoot.root (quadPoly d)
      = AdjoinRoot.of (quadPoly d) d := by
  have h : (quadPoly d).eval₂ (AdjoinRoot.of (quadPoly d)) (AdjoinRoot.root (quadPoly d)) = 0 :=
    AdjoinRoot.eval₂_root (quadPoly d)
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  linear_combination h

/-! ## The multiplicative map `!![a, d*b; b, a] ↦ a + b·ρ` -/

section Hom

/-- The underlying function of the map `x ↦ a + b·ρ` on `hypTorus F d`. -/
noncomputable def hypHomFun (d : F) {R : Type*} [CommRing R] (g : F →+* R) (ρ : R)
    (x : Work.L2F.hypTorus F d) : R :=
  g (((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)
    + g (((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) * ρ

/-- On an element of the given form, `hypHomFun` evaluates to `g a + g b · ρ`. -/
lemma hypHomFun_apply_form (d : F) {R : Type*} [CommRing R] (g : F →+* R) (ρ : R)
    (x : Work.L2F.hypTorus F d) (a b : F)
    (hx : (((x : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      = !![a, d * b; b, a]) :
    hypHomFun d g ρ x = g a + g b * ρ := by
  unfold hypHomFun
  rw [hx]
  simp

/-- For `ρ*ρ = g d`, the map `!![a, d*b; b, a] ↦ a + b·ρ` is a monoid homomorphism
`hypTorus F d →* R`. -/
noncomputable def hypHom (d : F) {R : Type*} [CommRing R] (g : F →+* R) (ρ : R)
    (hρ : ρ * ρ = g d) : Work.L2F.hypTorus F d →* R where
  toFun := hypHomFun d g ρ
  map_one' := by
    unfold hypHomFun
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
    simp
  map_mul' := by
    intro x y
    obtain ⟨a, b, hab, hx⟩ :=
      (mem_hypTorus F d (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
    obtain ⟨c, e, hce, hy⟩ :=
      (mem_hypTorus F d (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
    have hprod : (((x * y : Work.L2F.hypTorus F d) : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
        = !![a * c + d * (b * e), d * (a * e + b * c);
             a * e + b * c, a * c + d * (b * e)] := by
      rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
    rw [hypHomFun_apply_form d g ρ (x * y) (a * c + d * (b * e)) (a * e + b * c) hprod,
        hypHomFun_apply_form d g ρ x a b hx,
        hypHomFun_apply_form d g ρ y c e hy]
    rw [show (g a + g b * ρ) * (g c + g e * ρ)
          = g a * g c + g b * g e * (ρ * ρ) + (g b * g c + g a * g e) * ρ from by ring,
        hρ]
    simp only [map_add, map_mul]
    ring

@[simp] lemma hypHom_apply (d : F) {R : Type*} [CommRing R] (g : F →+* R) (ρ : R)
    (hρ : ρ * ρ = g d) (x : Work.L2F.hypTorus F d) :
    hypHom d g ρ hρ x = hypHomFun d g ρ x := rfl

end Hom

/-! ## Injectivity in the split (square) case -/

section Split

/-- If `d = c²` with `c ≠ 0` and `2 ≠ 0`, the map `!![a, d*b; b, a] ↦ a + b·c` into the field `F`
is injective.  Indeed `(a + bc)(a - bc) = a² - db² = 1`, so `a - bc` is the inverse of `a + bc`;
equality of the two elements therefore forces equality of the "conjugates", and adding/subtracting
gives `2a = 2a'` and `2bc = 2b'c`. -/
lemma hypHom_id_injective (d c : F) (hρ : c * c = RingHom.id F d) (hc0 : c ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    Function.Injective (hypHom d (RingHom.id F) c hρ) := by
  have hc : c * c = d := hρ
  intro x y hxy
  obtain ⟨a, b, hab, hx⟩ :=
    (mem_hypTorus F d (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
  obtain ⟨a', b', ha'b', hy⟩ :=
    (mem_hypTorus F d (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
  have ex : hypHom d (RingHom.id F) c hρ x = a + b * c := by
    rw [hypHom_apply, hypHomFun_apply_form d (RingHom.id F) c x a b hx]
    simp
  have ey : hypHom d (RingHom.id F) c hρ y = a' + b' * c := by
    rw [hypHom_apply, hypHomFun_apply_form d (RingHom.id F) c y a' b' hy]
    simp
  rw [ex, ey] at hxy
  -- `hxy : a + b*c = a' + b'*c`
  have huv : (a + b * c) * (a - b * c) = 1 := by
    have h1 : (a + b * c) * (a - b * c) = a ^ 2 - d * b ^ 2 := by rw [← hc]; ring
    rw [h1]; exact hab
  have hu'v' : (a' + b' * c) * (a' - b' * c) = 1 := by
    have h1 : (a' + b' * c) * (a' - b' * c) = a' ^ 2 - d * b' ^ 2 := by rw [← hc]; ring
    rw [h1]; exact ha'b'
  have hvv : a - b * c = a' - b' * c := by
    rw [← inv_eq_of_mul_eq_one_right huv, ← inv_eq_of_mul_eq_one_right hu'v', hxy]
  have h2a : 2 * a = 2 * a' := by linear_combination hxy + hvv
  have h2b : 2 * (b * c) = 2 * (b' * c) := by linear_combination hxy - hvv
  have haa : a = a' := mul_left_cancel₀ h2 h2a
  have hbb : b * c = b' * c := mul_left_cancel₀ h2 h2b
  have hb : b = b' := mul_right_cancel₀ hc0 hbb
  have hmat : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [hx, hy, haa, hb]
  exact Subtype.ext (Subtype.ext hmat)

end Split

/-! ## Injectivity in the non-split (nonsquare) case -/

section NonSplit

/-- If `d` is not a square and `2 ≠ 0`, the map `!![a, d*b; b, a] ↦ a + b·root` into the
quadratic algebra `quadAlg F d` is injective.  Indeed `(a + b·r)(a - b·r) = a² - db² = 1`, so
`a - b·r` is the inverse of `a + b·r`; equality of the two elements forces equality of the
conjugates, whence `2a = 2a'` and `2b·r = 2b'·r`.  Then `(b - b')·r = 0` gives `r = 0` if
`b ≠ b'`, contradicting `r·r = d ≠ 0`. -/
lemma hypHom_root_injective (d : F) (h2 : (2 : F) ≠ 0) (hnsq : ∀ a : F, a * a ≠ d) :
    Function.Injective (hypHom d (AdjoinRoot.of (quadPoly d))
      (AdjoinRoot.root (quadPoly d)) (quadAlg_root_sq d)) := by
  haveI : IsDomain (Work.L2F.quadAlg F d) :=
    AdjoinRoot.isDomain_of_prime (quadPoly_prime d hnsq)
  have hd : d ≠ 0 := fun h => hnsq 0 (by rw [h, mul_zero])
  have hinj : Function.Injective (AdjoinRoot.of (quadPoly d)) := quadAlg_of_injective d
  intro x y hxy
  obtain ⟨a, b, hab, hx⟩ :=
    (mem_hypTorus F d (x : Matrix.SpecialLinearGroup (Fin 2) F)).mp x.2
  obtain ⟨a', b', ha'b', hy⟩ :=
    (mem_hypTorus F d (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
  have ex : hypHom d (AdjoinRoot.of (quadPoly d)) (AdjoinRoot.root (quadPoly d))
        (quadAlg_root_sq d) x
      = AdjoinRoot.of (quadPoly d) a
        + AdjoinRoot.of (quadPoly d) b * AdjoinRoot.root (quadPoly d) :=
    hypHomFun_apply_form d (AdjoinRoot.of (quadPoly d)) (AdjoinRoot.root (quadPoly d)) x a b hx
  have ey : hypHom d (AdjoinRoot.of (quadPoly d)) (AdjoinRoot.root (quadPoly d))
        (quadAlg_root_sq d) y
      = AdjoinRoot.of (quadPoly d) a'
        + AdjoinRoot.of (quadPoly d) b' * AdjoinRoot.root (quadPoly d) :=
    hypHomFun_apply_form d (AdjoinRoot.of (quadPoly d)) (AdjoinRoot.root (quadPoly d)) y a' b' hy
  rw [ex, ey] at hxy
  -- `hxy : ↑a + ↑b*r = ↑a' + ↑b'*r`
  let r := AdjoinRoot.root (quadPoly d)
  have hrsq : r * r = AdjoinRoot.of (quadPoly d) d := quadAlg_root_sq d
  have hxy' : AdjoinRoot.of (quadPoly d) a + AdjoinRoot.of (quadPoly d) b * r
      = AdjoinRoot.of (quadPoly d) a' + AdjoinRoot.of (quadPoly d) b' * r := hxy
  -- the two elements are units with inverses the conjugates
  have huv : (AdjoinRoot.of (quadPoly d) a + AdjoinRoot.of (quadPoly d) b * r)
      * (AdjoinRoot.of (quadPoly d) a - AdjoinRoot.of (quadPoly d) b * r) = 1 := by
    have h1 : (AdjoinRoot.of (quadPoly d) a + AdjoinRoot.of (quadPoly d) b * r)
        * (AdjoinRoot.of (quadPoly d) a - AdjoinRoot.of (quadPoly d) b * r)
        = AdjoinRoot.of (quadPoly d) a ^ 2
          - AdjoinRoot.of (quadPoly d) b ^ 2 * (r * r) := by ring
    rw [h1, hrsq]
    have h2' : AdjoinRoot.of (quadPoly d) a ^ 2
          - AdjoinRoot.of (quadPoly d) b ^ 2 * AdjoinRoot.of (quadPoly d) d
        = AdjoinRoot.of (quadPoly d) (a ^ 2 - d * b ^ 2) := by
      rw [map_sub, map_mul, map_pow, map_pow]; ring
    rw [h2', hab]; simp
  have hu'v' : (AdjoinRoot.of (quadPoly d) a' + AdjoinRoot.of (quadPoly d) b' * r)
      * (AdjoinRoot.of (quadPoly d) a' - AdjoinRoot.of (quadPoly d) b' * r) = 1 := by
    have h1 : (AdjoinRoot.of (quadPoly d) a' + AdjoinRoot.of (quadPoly d) b' * r)
        * (AdjoinRoot.of (quadPoly d) a' - AdjoinRoot.of (quadPoly d) b' * r)
        = AdjoinRoot.of (quadPoly d) a' ^ 2
          - AdjoinRoot.of (quadPoly d) b' ^ 2 * (r * r) := by ring
    rw [h1, hrsq]
    have h2' : AdjoinRoot.of (quadPoly d) a' ^ 2
          - AdjoinRoot.of (quadPoly d) b' ^ 2 * AdjoinRoot.of (quadPoly d) d
        = AdjoinRoot.of (quadPoly d) (a' ^ 2 - d * b' ^ 2) := by
      rw [map_sub, map_mul, map_pow, map_pow]; ring
    rw [h2', ha'b']; simp
  -- `u ≠ 0`
  have hu0 : AdjoinRoot.of (quadPoly d) a + AdjoinRoot.of (quadPoly d) b * r ≠ 0 := by
    intro hh
    have h0 : (0 : Work.L2F.quadAlg F d)
        * (AdjoinRoot.of (quadPoly d) a - AdjoinRoot.of (quadPoly d) b * r) = 1 := by
      rw [← hh]; exact huv
    rw [zero_mul] at h0
    exact zero_ne_one h0
  -- equality of the conjugates
  have hvv : AdjoinRoot.of (quadPoly d) a - AdjoinRoot.of (quadPoly d) b * r
      = AdjoinRoot.of (quadPoly d) a' - AdjoinRoot.of (quadPoly d) b' * r := by
    have h0 : (AdjoinRoot.of (quadPoly d) a + AdjoinRoot.of (quadPoly d) b * r)
        * ((AdjoinRoot.of (quadPoly d) a - AdjoinRoot.of (quadPoly d) b * r)
           - (AdjoinRoot.of (quadPoly d) a' - AdjoinRoot.of (quadPoly d) b' * r)) = 0 := by
      rw [mul_sub, huv, hxy', hu'v', sub_self]
    rcases mul_eq_zero.mp h0 with hh | hh
    · exact absurd hh hu0
    · exact sub_eq_zero.mp hh
  have h2a : 2 * AdjoinRoot.of (quadPoly d) a
      = 2 * AdjoinRoot.of (quadPoly d) a' := by linear_combination hxy' + hvv
  have h2b : 2 * (AdjoinRoot.of (quadPoly d) b * r)
      = 2 * (AdjoinRoot.of (quadPoly d) b' * r) := by linear_combination hxy' - hvv
  have haa : a = a' := by
    apply mul_left_cancel₀ h2
    have h' : AdjoinRoot.of (quadPoly d) (2 * a)
        = AdjoinRoot.of (quadPoly d) (2 * a') := by
      simpa only [map_mul, map_ofNat] using h2a
    exact hinj h'
  have h20 : (2 : Work.L2F.quadAlg F d) ≠ 0 := by
    rw [show (2 : Work.L2F.quadAlg F d) = AdjoinRoot.of (quadPoly d) (2 : F)
          from (map_ofNat (AdjoinRoot.of (quadPoly d)) 2).symm]
    intro hh
    exact h2 (hinj (by rw [hh, map_zero]))
  have hb : b = b' := by
    by_contra hbne
    have hbr : AdjoinRoot.of (quadPoly d) b * r = AdjoinRoot.of (quadPoly d) b' * r := by
      have h0 : (2 : Work.L2F.quadAlg F d)
          * (AdjoinRoot.of (quadPoly d) b * r - AdjoinRoot.of (quadPoly d) b' * r) = 0 := by
        rw [mul_sub, h2b, sub_self]
      rcases mul_eq_zero.mp h0 with hh | hh
      · exact absurd hh h20
      · exact sub_eq_zero.mp hh
    have hzero : AdjoinRoot.of (quadPoly d) (b - b') * r = 0 := by
      rw [map_sub, sub_mul]; linear_combination hbr
    have hcoef : AdjoinRoot.of (quadPoly d) (b - b') ≠ 0 :=
      fun hh => hbne (sub_eq_zero.mp (hinj (by rw [hh, map_zero])))
    have hrz : r = 0 := by
      rcases mul_eq_zero.mp hzero with hh | hh
      · exact absurd hh hcoef
      · exact hh
    have : AdjoinRoot.of (quadPoly d) d = 0 := by rw [← hrsq, hrz, mul_zero]
    exact hd (hinj (by rw [this, map_zero]))
  have hmat : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ((y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [hx, hy, haa, hb]
  exact Subtype.ext (Subtype.ext hmat)

end NonSplit

/-! ## The main theorem -/

theorem hypTorus_cyclic (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (d : F) (hd : d ≠ 0) :
    IsCyclic (Work.L2F.hypTorus F d) := by
  rcases Classical.em (∃ c : F, c * c = d) with ⟨c, hc⟩ | h
  · -- split case: `d = c²` is a square
    have hc0 : c ≠ 0 := fun h0 => hd (by rw [← hc, h0, mul_zero])
    have hρ : c * c = RingHom.id F d := by rw [RingHom.id_apply]; exact hc
    exact isCyclic_of_injective_ringHom (hypHom d (RingHom.id F) c hρ)
      (hypHom_id_injective d c hρ hc0 h2)
  · -- non-split case: `d` is a nonsquare, map into the field `F[X]/(X²-d)`
    have hnsq : ∀ a : F, a * a ≠ d := fun a ha => h ⟨a, ha⟩
    haveI : IsDomain (Work.L2F.quadAlg F d) :=
      AdjoinRoot.isDomain_of_prime (quadPoly_prime d hnsq)
    exact isCyclic_of_injective_ringHom _ (hypHom_root_injective d h2 hnsq)

end Work.L2F.Conic
