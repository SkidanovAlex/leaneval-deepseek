import Mathlib
import Submission.Work.MotAS.ASRulDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRul.I2` — the AS link identity `P^AS (R^AS z) = s'^AS(z) · z`

The statement is `w`-free, but it is not a formal consequence of the definitions: the transported
identity `Work.MotAS.kleinPAS_kleinRAS` (`Submission/Work/MotAS/ASLink.lean`) is available only in
a ring carrying an explicit root `w` of the Artin–Schreier polynomial `X⁵ - X - g`.

The strategy here is therefore to *adjoin* that root universally: work in
`S = AdjoinRoot (X⁵ - X - g)` over `R` (where `5 = 0` and `w⁵ = w + g` both hold), apply
`kleinPAS_kleinRAS` there, and push the resulting equality back along the injective structure map
`R → S` (`AdjoinRoot.of.injective_of_monic_of_degree_pos`), using the ring-hom naturality of the
AS data (`kleinPAS`, `kleinRAS`, `kleinSecDualAS` are integer-coefficient polynomial expressions).

The auxiliary ring-hom naturality lemmas are proved by `simp only` with the `map_*` lemmas for a
ring homomorphism, which is a purely syntactic rewriting (no polynomial expansion is performed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Work.MotAS.ASRul

open Polynomial

/-! ## The Artin–Schreier polynomial `X⁵ - X - g` -/

/-- The Artin–Schreier polynomial `X ^ 5 - X - g`. -/
noncomputable def ASpoly {R : Type*} [CommRing R] (g : R) : Polynomial R :=
  Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g

theorem ASpoly_monic {R : Type*} [CommRing R] [Nontrivial R] (g : R) : (ASpoly g).Monic := by
  rw [ASpoly]
  have h1 : (Polynomial.X : Polynomial R) ^ 5 - Polynomial.X - Polynomial.C g
      = Polynomial.X ^ 5 + (-(Polynomial.X) - Polynomial.C g) := by ring
  rw [h1]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem ASpoly_degree_pos {R : Type*} [CommRing R] [Nontrivial R] (g : R) :
    0 < (ASpoly g).degree := by
  have hmon : (ASpoly g).Monic := ASpoly_monic g
  have hnd : (ASpoly g).natDegree = 5 := by rw [ASpoly]; compute_degree!
  rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hnd]
  norm_num

/-! ## Ring-hom naturality of the AS link data -/

theorem map_kleinPAS0 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS0 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinPAS0 a b g y) := by
  simp only [Work.MotAS.kleinPAS0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS1 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinPAS1 a b g y) := by
  simp only [Work.MotAS.kleinPAS1, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS2 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS2 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinPAS2 a b g y) := by
  simp only [Work.MotAS.kleinPAS2, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS3 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS3 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinPAS3 a b g y) := by
  simp only [Work.MotAS.kleinPAS3, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS4 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinPAS4 a b g y) := by
  simp only [Work.MotAS.kleinPAS4, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinPAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS (φ a) (φ b) (φ g) (fun k => φ (y k))
      = fun k => φ (Work.MotAS.kleinPAS a b g y k) := by
  funext k
  fin_cases k
  · exact map_kleinPAS0 φ a b g y
  · exact map_kleinPAS1 φ a b g y
  · exact map_kleinPAS2 φ a b g y
  · exact map_kleinPAS3 φ a b g y
  · exact map_kleinPAS4 φ a b g y

theorem map_kleinRAS0 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS0 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinRAS0 a b g y) := by
  simp only [Work.MotAS.kleinRAS0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS1 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinRAS1 a b g y) := by
  simp only [Work.MotAS.kleinRAS1, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS2 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS2 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinRAS2 a b g y) := by
  simp only [Work.MotAS.kleinRAS2, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS3 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS3 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinRAS3 a b g y) := by
  simp only [Work.MotAS.kleinRAS3, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS4 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS4 (φ a) (φ b) (φ g) (fun k => φ (y k))
      = φ (Work.MotAS.kleinRAS4 a b g y) := by
  simp only [Work.MotAS.kleinRAS4, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

theorem map_kleinRAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinRAS (φ a) (φ b) (φ g) (fun k => φ (y k))
      = fun k => φ (Work.MotAS.kleinRAS a b g y k) := by
  funext k
  fin_cases k
  · exact map_kleinRAS0 φ a b g y
  · exact map_kleinRAS1 φ a b g y
  · exact map_kleinRAS2 φ a b g y
  · exact map_kleinRAS3 φ a b g y
  · exact map_kleinRAS4 φ a b g y

theorem map_kleinSecDualAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b g : R) (z : Fin 5 → R) :
    Work.MotAS.kleinSecDualAS (φ a) (φ b) (φ g) (fun i => φ (z i))
      = φ (Work.MotAS.kleinSecDualAS a b g z) := by
  simp only [Work.MotAS.kleinSecDualAS, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]

/-! ## The identity -/

theorem I2 {R : Type*} [CommRing R] (a b g : R) (h5 : (5 : R) = 0) (z : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g z)
      = fun i => Work.MotAS.kleinSecDualAS a b g z * z i := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · haveI := hR
    have hw : (AdjoinRoot.root (ASpoly g)) ^ 5
        = AdjoinRoot.root (ASpoly g) + AdjoinRoot.of (ASpoly g) g := by
      have h0 : (AdjoinRoot.mk (ASpoly g)) (ASpoly g) = 0 := AdjoinRoot.mk_self
      rw [ASpoly] at h0
      simp only [map_sub, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h0
      show (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)) ^ 5
          = AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)
            + AdjoinRoot.of (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) g
      have h1 : (AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)) ^ 5
            - AdjoinRoot.root (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g)
          = AdjoinRoot.of (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) g :=
        sub_eq_zero.mp h0
      rw [← h1]
      abel
    have h5S : (5 : AdjoinRoot (ASpoly g)) = 0 := by
      rw [show (5 : AdjoinRoot (ASpoly g))
            = AdjoinRoot.of (ASpoly g) (5 : R) from
          (map_ofNat (AdjoinRoot.of (ASpoly g)) 5).symm, h5, map_zero]
    have hgen := Work.MotAS.kleinPAS_kleinRAS (AdjoinRoot.of (ASpoly g) a)
      (AdjoinRoot.of (ASpoly g) b) (AdjoinRoot.of (ASpoly g) g)
      (AdjoinRoot.root (ASpoly g)) h5S hw (fun k => AdjoinRoot.of (ASpoly g) (z k))
    rw [map_kleinRAS (AdjoinRoot.of (ASpoly g)) a b g z,
      map_kleinPAS (AdjoinRoot.of (ASpoly g)) a b g (Work.MotAS.kleinRAS a b g z),
      map_kleinSecDualAS (AdjoinRoot.of (ASpoly g)) a b g z] at hgen
    funext i
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos (ASpoly_monic g) (ASpoly_degree_pos g) ?_
    have hi := congrFun hgen i
    simpa only [map_mul] using hi

end Work.MotAS.ASRul
