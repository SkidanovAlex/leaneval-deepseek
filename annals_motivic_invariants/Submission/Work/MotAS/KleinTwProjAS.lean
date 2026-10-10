import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.KleinTwProjASGuide
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotK.KleinIdents
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The projective (ratio) form of the AS link identity I1^AS

`R^AS ∘ P^AS` is a scalar multiple of the identity, in cross-multiplied form:
`kleinRAS (kleinPAS y) i * y j = kleinRAS (kleinPAS y) j * y i`.

The proof follows the route of `Submission/Work/MotAS/KleinTwProjASGuide.lean` and avoids any large
`ring` certificate.  The mathematical content is isolated in

* `Work.MotAS.kleinTwProjAS_of_root`: *inside a ring that happens to contain a root `w` of
  `X⁵ - X - g`* — i.e. an element with `w ^ 5 = w + g` — the transported Crauder–Katz identities
  (`asTransportP`, `asTransportR`, `Work.MotK.kleinR_kleinP`) compute `R^AS ∘ P^AS` and
  `asM_mulVec_injective` cancels the Vandermonde matrix `asM w`;
* `Work.MotAS.map_kleinPAS` / `Work.MotAS.map_kleinRAS`: the AS link data are polynomial in their
  arguments, so any ring homomorphism commutes with them (proved componentwise, the polynomial
  identities being closed by `simp` + `ring`).

The general statement is then obtained by adjoining a formal root:
`S := AdjoinRoot (X⁵ - X - C g)` over `R` carries a root `w` (`AdjoinRoot.root`), the identity
holds in `S` for the images of `a, b, g, y`, and `AdjoinRoot.of` is injective (`AdjoinRoot` is a
monic quotient), so the identity descends to `R`.  (A trivial ring is handled separately, since
there every equality holds.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-! ## §1  A ring homomorphism commutes with the AS link data

`kleinPAS` and `kleinRAS` are polynomial expressions in `a, b, g` and the coordinates, so the image
of the tuple under a ring homomorphism `φ` is the tuple of images.  The componentwise statements
are proved first (each is a single polynomial identity), the tuples are then assembled. -/

section MapLemmas

variable {S : Type*} [CommRing S]

theorem map_kleinPAS0 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS0 (φ a) (φ b) (φ g) (fun i => φ (y i)) = φ (kleinPAS0 a b g y) := by
  simp only [kleinPAS0, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinPAS1 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS1 (φ a) (φ b) (φ g) (fun i => φ (y i)) = φ (kleinPAS1 a b g y) := by
  simp only [kleinPAS1, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinPAS2 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS2 (φ a) (φ b) (φ g) (fun i => φ (y i)) = φ (kleinPAS2 a b g y) := by
  simp only [kleinPAS2, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinPAS3 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS3 (φ a) (φ b) (φ g) (fun i => φ (y i)) = φ (kleinPAS3 a b g y) := by
  simp only [kleinPAS3, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinPAS4 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS4 (φ a) (φ b) (φ g) (fun i => φ (y i)) = φ (kleinPAS4 a b g y) := by
  simp only [kleinPAS4, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

/-- `φ` commutes with the transported Pfaffian tuple. -/
theorem map_kleinPAS (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    kleinPAS (φ a) (φ b) (φ g) (fun i => φ (y i)) = fun i => φ (kleinPAS a b g y i) := by
  funext i
  fin_cases i
  · exact map_kleinPAS0 φ a b g y
  · exact map_kleinPAS1 φ a b g y
  · exact map_kleinPAS2 φ a b g y
  · exact map_kleinPAS3 φ a b g y
  · exact map_kleinPAS4 φ a b g y

theorem map_kleinRAS0 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS0 (φ a) (φ b) (φ g) (fun i => φ (z i)) = φ (kleinRAS0 a b g z) := by
  simp only [kleinRAS0, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinRAS1 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS1 (φ a) (φ b) (φ g) (fun i => φ (z i)) = φ (kleinRAS1 a b g z) := by
  simp only [kleinRAS1, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinRAS2 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS2 (φ a) (φ b) (φ g) (fun i => φ (z i)) = φ (kleinRAS2 a b g z) := by
  simp only [kleinRAS2, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinRAS3 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS3 (φ a) (φ b) (φ g) (fun i => φ (z i)) = φ (kleinRAS3 a b g z) := by
  simp only [kleinRAS3, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

theorem map_kleinRAS4 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS4 (φ a) (φ b) (φ g) (fun i => φ (z i)) = φ (kleinRAS4 a b g z) := by
  simp only [kleinRAS4, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_one,
    map_zero, map_neg]
  try ring

/-- `φ` commutes with the transported inverse quadro-cubic tuple. -/
theorem map_kleinRAS (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    kleinRAS (φ a) (φ b) (φ g) (fun i => φ (z i)) = fun i => φ (kleinRAS a b g z i) := by
  funext i
  fin_cases i
  · exact map_kleinRAS0 φ a b g z
  · exact map_kleinRAS1 φ a b g z
  · exact map_kleinRAS2 φ a b g z
  · exact map_kleinRAS3 φ a b g z
  · exact map_kleinRAS4 φ a b g z

end MapLemmas

/-! ## §2  The identity in a ring containing a root of `X⁵ - X - g`

This is the actual transport/cancellation argument, carried out entirely inside `R`. -/

theorem kleinTwProjAS_of_root (h5 : (5 : R) = 0) (a b g w : R) (hw : w ^ 5 = w + g)
    (y : Fin 5 → R) (i j : Fin 5) :
    kleinRAS a b g (kleinPAS a b g y) i * y j
      = kleinRAS a b g (kleinPAS a b g y) j * y i := by
  -- the source Galois-coordinate vector
  set ξ : Fin 5 → R := (asM w).mulVec y with hξ
  -- transport of the Pfaffians
  have hP : Work.MotK.kleinP a b ξ = (asN w).mulVec (kleinPAS a b g y) := by
    rw [hξ]
    exact asTransportP a b g w h5 hw y
  -- transport of the inverse quadro-cubic map
  have hR : Work.MotK.kleinR a b ((asN w).mulVec (kleinPAS a b g y))
      = (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y)) :=
    asTransportR a b g w h5 hw (kleinPAS a b g y)
  -- the split identity `R ∘ P = s · id`
  have hC : Work.MotK.kleinR a b (Work.MotK.kleinP a b ξ)
      = fun i => Work.MotK.kleinSec a b ξ * ξ i :=
    funext fun i => Work.MotK.kleinR_kleinP a b ξ i
  have h1 : (asM w).mulVec (kleinRAS a b g (kleinPAS a b g y))
      = fun i => Work.MotK.kleinSec a b ξ * ξ i := by
    rw [← hR, ← hP]
    exact hC
  -- linearity of `mulVec` on the right-hand side
  have h2 : (asM w).mulVec (fun i => Work.MotK.kleinSec a b ξ * y i)
      = fun i => Work.MotK.kleinSec a b ξ * ξ i := by
    funext i
    simp only [Matrix.mulVec_apply_eq_sum, hξ]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the Vandermonde matrix `asM w` is invertible, so cancel it
  have h3 : kleinRAS a b g (kleinPAS a b g y)
      = fun i => Work.MotK.kleinSec a b ξ * y i :=
    asM_mulVec_injective h5 w (by rw [h1, h2])
  -- multiply the `i`-th and `j`-th components
  calc kleinRAS a b g (kleinPAS a b g y) i * y j
      = Work.MotK.kleinSec a b ξ * y i * y j := by simp only [h3]
    _ = Work.MotK.kleinSec a b ξ * y j * y i := by ring
    _ = kleinRAS a b g (kleinPAS a b g y) j * y i := by simp only [h3]

/-! ## §3  The general statement, by adjoining a formal root of `X⁵ - X - g` -/

theorem KleinTwProjAS {R : Type*} [CommRing R] (h5 : (5 : R) = 0) (a b g : R) (y : Fin 5 → R)
    (i j : Fin 5) :
    kleinRAS a b g (kleinPAS a b g y) i * y j = kleinRAS a b g (kleinPAS a b g y) j * y i := by
  classical
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · -- the zero ring: every equality holds
    haveI : Subsingleton R := hsub
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := hnt
    -- the monic Artin–Schreier polynomial whose root relation defines the Galois coordinates
    set P : Polynomial R := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g with hPdef
    have hPmonic : P.Monic := by rw [hPdef]; monicity!
    have hPndeg : P.natDegree = 5 := by rw [hPdef]; compute_degree!
    have hPdegpos : (0 : WithBot ℕ) < P.degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, hPndeg]
      norm_num
    -- characteristic `5` and the root relation in the adjoined ring
    have h5S : (5 : AdjoinRoot P) = 0 := by
      have h5R : ((5 : ℕ) : R) = 0 := by simpa using h5
      have h' : ((5 : ℕ) : AdjoinRoot P) = 0 := by
        rw [← map_natCast (AdjoinRoot.of P) 5, h5R, map_zero]
      simpa using h'
    have hwS : (AdjoinRoot.root P) ^ 5 = AdjoinRoot.root P + AdjoinRoot.of P g := by
      have h := AdjoinRoot.eval₂_root P
      rw [hPdef] at h
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      linear_combination (norm := first | refl_ring1 | ring1) h
    -- the identity holds in the adjoined ring
    have hmain := kleinTwProjAS_of_root (R := AdjoinRoot P) h5S (AdjoinRoot.of P a)
      (AdjoinRoot.of P b) (AdjoinRoot.of P g) (AdjoinRoot.root P) hwS
      (fun k => AdjoinRoot.of P (y k)) i j
    -- rewrite the adjoined data as the image of the data in `R`
    have hmain' : AdjoinRoot.of P (kleinRAS a b g (kleinPAS a b g y) i)
          * AdjoinRoot.of P (y j)
        = AdjoinRoot.of P (kleinRAS a b g (kleinPAS a b g y) j)
          * AdjoinRoot.of P (y i) := by
      simpa only [map_kleinPAS (AdjoinRoot.of P) a b g y,
        map_kleinRAS (AdjoinRoot.of P) a b g (kleinPAS a b g y)] using hmain
    -- descend along the (injective) embedding `R → AdjoinRoot P`
    refine AdjoinRoot.of.injective_of_monic_of_degree_pos hPmonic hPdegpos ?_
    rw [map_mul, map_mul]
    exact hmain'

end Work.MotAS
