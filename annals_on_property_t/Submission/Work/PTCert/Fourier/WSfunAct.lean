import Mathlib
import Submission.Work.PTCert.TFDefs
import Submission.Work.PTCert.Math

/-!
# `WSfunAct`: equivariance of the Fourier-twisted bilinear form `WSfun`

`WSfun act sgn M S x y = ∑_a χ_S(a) · sgn a y · M x (act a y)`,
where `χ_S` is the sign character of `(ℤ/2)^m` attached to `S` and `sgn`/`act` encode a
*signed permutation* action `ρ(a) e_x = sgn a x · e_{act a x}` of `(ℤ/2)^m`
(cocycle condition `hsgn`, unit modulus `hsgnval`) under which the matrix `M` is invariant
up to signs (`hMinv`).

The main result is the two-variable equivariance
`WSfun (act a x) (act b y) = χ_S(a+b) · sgn a x · sgn b y · WSfun x y`.

It is obtained from the two one-variable identities
* `WSfun_fst' : WSfun (act a x) z = χ_S a · sgn a x · WSfun x z`   (reindex by `c ↦ a+c`),
* `WSfun_snd' : WSfun x (act b y) = χ_S b · sgn b y · WSfun x y`   (reindex by `c ↦ c+b`).
-/

namespace Work.PTCert.Fourier

open Submission.PTCert
open scoped BigOperators

set_option linter.unusedVariables false

/-! ## Elementary consequences of the signed-permutation hypotheses -/

/-- `(ℤ/2)^m` has exponent two. -/
private lemma h_addself {m : ℕ} (a : Fin m → ZMod 2) : a + a = 0 := by
  funext i; exact CharTwo.add_self_eq_zero (a i)

/-- Every sign is `±1`, hence of unit modulus. -/
private lemma h_sgn_sq {m : ℕ} {ι : Type} {sgn : (Fin m → ZMod 2) → ι → ℝ}
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1) (a : Fin m → ZMod 2) (x : ι) :
    sgn a x * sgn a x = 1 := by
  rcases hsgnval a x with h | h <;> rw [h] <;> norm_num

/-- The identity sign is trivial: `sgn 0 x = 1`. -/
private lemma h_sgn_zero {m : ℕ} {ι : Type} {act : (Fin m → ZMod 2) → ι → ι}
    {sgn : (Fin m → ZMod 2) → ι → ℝ}
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1) (x : ι) : sgn 0 x = 1 := by
  have h := hsgn 0 0 x
  rw [zero_add, hact0] at h
  calc sgn 0 x = sgn 0 x * sgn 0 x := h
    _ = 1 := h_sgn_sq hsgnval 0 x

/-- `(ℤ/2)^m` acts through involutions: `act b (act b y) = y`. -/
private lemma h_act_self {m : ℕ} {ι : Type} {act : (Fin m → ZMod 2) → ι → ι}
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hact0 : ∀ x, act 0 x = x) (b : Fin m → ZMod 2) (y : ι) :
    act b (act b y) = y := by
  rw [← hact b b y, h_addself, hact0]

/-- The sign of an involution is symmetric: `sgn b (act b y) = sgn b y`. -/
private lemma h_sgn_act_self {m : ℕ} {ι : Type} {sgn : (Fin m → ZMod 2) → ι → ℝ}
    {act : (Fin m → ZMod 2) → ι → ι}
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1) (b : Fin m → ZMod 2) (y : ι) :
    sgn b (act b y) = sgn b y := by
  have h := hsgn b b y
  rw [h_addself, h_sgn_zero hact0 hsgn hsgnval y] at h
  have hsq := h_sgn_sq hsgnval b y
  calc sgn b (act b y) = sgn b (act b y) * 1 := (mul_one _).symm
    _ = sgn b (act b y) * (sgn b y * sgn b y) := by rw [hsq]
    _ = (sgn b (act b y) * sgn b y) * sgn b y := by ring
    _ = 1 * sgn b y := by rw [← h]
    _ = sgn b y := one_mul _

/-- Twisted invariance of `M`, obtained by multiplying `hMinv` by the unit `sgn g u * sgn g v`. -/
private lemma h_Minv {m : ℕ} {ι : Type} {act : (Fin m → ZMod 2) → ι → ι}
    {sgn : (Fin m → ZMod 2) → ι → ℝ} {M : Matrix ι ι ℝ}
    (hMinv : ∀ a x y, sgn a x * sgn a y * M (act a x) (act a y) = M x y)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1)
    (g : Fin m → ZMod 2) (u v : ι) :
    M (act g u) (act g v) = sgn g u * sgn g v * M u v := by
  have h := hMinv g u v
  have h1 := h_sgn_sq hsgnval g u
  have h2 := h_sgn_sq hsgnval g v
  have key : (sgn g u * sgn g v) * (sgn g u * sgn g v) = 1 := by
    calc (sgn g u * sgn g v) * (sgn g u * sgn g v)
        = (sgn g u * sgn g u) * (sgn g v * sgn g v) := by ring
      _ = 1 * 1 := by rw [h1, h2]
      _ = 1 := one_mul 1
  calc M (act g u) (act g v)
      = ((sgn g u * sgn g v) * (sgn g u * sgn g v)) * M (act g u) (act g v) := by
          rw [key, one_mul]
    _ = (sgn g u * sgn g v) * ((sgn g u * sgn g v) * M (act g u) (act g v)) := by ring
    _ = (sgn g u * sgn g v) * M u v := by rw [h]
    _ = sgn g u * sgn g v * M u v := by ring

/-- Cocycle identity in the form used for the second argument. -/
private lemma h_sgn_add_act {m : ℕ} {ι : Type} {act : (Fin m → ZMod 2) → ι → ι}
    {sgn : (Fin m → ZMod 2) → ι → ℝ}
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1) (e b : Fin m → ZMod 2) (y : ι) :
    sgn (e + b) (act b y) = sgn e y * sgn b y := by
  rw [hsgn e b (act b y), h_act_self hact hact0 b y, h_sgn_act_self hact0 hsgn hsgnval b y]

/-- Translation reindexing of a sum over `(ℤ/2)^m`. -/
private lemma sum_add_right' {m : ℕ} (F : (Fin m → ZMod 2) → ℝ) (b : Fin m → ZMod 2) :
    (∑ c, F c) = ∑ c, F (c + b) := (Equiv.sum_comp (Equiv.addRight b) F).symm

/-- Translation reindexing of a sum over `(ℤ/2)^m`. -/
private lemma sum_add_left' {m : ℕ} (F : (Fin m → ZMod 2) → ℝ) (a : Fin m → ZMod 2) :
    (∑ c, F c) = ∑ c, F (a + c) := (Equiv.sum_comp (Equiv.addLeft a) F).symm

/-! ## The two one-variable equivariances -/

/-- Second-argument equivariance: `WSfun x (act b y) = χ_S b · sgn b y · WSfun x y`. -/
private lemma WSfun_snd' {m : ℕ} {ι : Type}
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ)
    (M : Matrix ι ι ℝ)
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1)
    (S : Finset (Fin m))
    (hchi : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2), chiS S (a + b) = chiS S a * chiS S b)
    (b : Fin m → ZMod 2) (x y : ι) :
    WSfun act sgn M S x (act b y) = chiS S b * sgn b y * WSfun act sgn M S x y := by
  have e1 : WSfun act sgn M S x (act b y)
      = ∑ c, chiS S c * sgn c (act b y) * M x (act (c + b) y) := by
    rw [WSfun]
    apply Finset.sum_congr rfl
    intro c _
    rw [hact c b y]
  rw [e1]
  rw [sum_add_right' (fun c => chiS S c * sgn c (act b y) * M x (act (c + b) y)) b]
  rw [show (∑ c, chiS S (c + b) * sgn (c + b) (act b y) * M x (act (c + b + b) y))
        = ∑ c, chiS S c * chiS S b * (sgn c y * sgn b y) * M x (act c y) from
      Finset.sum_congr rfl (fun c _ => by
        rw [hchi S c b, h_sgn_add_act hact hact0 hsgn hsgnval c b y,
            show c + b + b = c from by rw [add_assoc, h_addself, add_zero]])]
  rw [WSfun, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- First-argument equivariance: `WSfun (act a x) z = χ_S a · sgn a x · WSfun x z`. -/
private lemma WSfun_fst' {m : ℕ} {ι : Type}
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ)
    (M : Matrix ι ι ℝ)
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1)
    (hMinv : ∀ a x y, sgn a x * sgn a y * M (act a x) (act a y) = M x y)
    (S : Finset (Fin m))
    (hchi : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2), chiS S (a + b) = chiS S a * chiS S b)
    (a : Fin m → ZMod 2) (x z : ι) :
    WSfun act sgn M S (act a x) z = chiS S a * sgn a x * WSfun act sgn M S x z := by
  have key : ∀ c, M (act a x) (act c z)
      = sgn a x * sgn a (act (a + c) z) * M x (act (a + c) z) := by
    intro c
    have hac : act a (act (a + c) z) = act c z := by
      rw [← hact a (a + c) z,
          show a + (a + c) = c from by rw [← add_assoc, h_addself, zero_add]]
    rw [← hac]
    exact h_Minv hMinv hsgnval a x (act (a + c) z)
  have e1 : WSfun act sgn M S (act a x) z
      = ∑ c, chiS S c * sgn c z * (sgn a x * sgn a (act (a + c) z) * M x (act (a + c) z)) := by
    rw [WSfun]
    apply Finset.sum_congr rfl
    intro c _
    rw [key c]
  rw [e1]
  rw [sum_add_left' (fun c => chiS S c * sgn c z *
      (sgn a x * sgn a (act (a + c) z) * M x (act (a + c) z))) a]
  rw [show (∑ c, chiS S (a + c) * sgn (a + c) z *
              (sgn a x * sgn a (act (a + (a + c)) z) * M x (act (a + (a + c)) z)))
        = ∑ c, chiS S a * sgn a x * (chiS S c * sgn c z * M x (act c z)) from
      Finset.sum_congr rfl (fun c _ => by
        rw [show a + (a + c) = c from by rw [← add_assoc, h_addself, zero_add],
            hchi S a c, hsgn a c z]
        have hX := h_sgn_sq hsgnval a (act c z)
        calc (chiS S a * chiS S c) * (sgn a (act c z) * sgn c z) *
                (sgn a x * sgn a (act c z) * M x (act c z))
            = chiS S a * sgn a x *
                (chiS S c * (sgn a (act c z) * sgn a (act c z)) * sgn c z * M x (act c z)) := by ring
          _ = chiS S a * sgn a x *
                (chiS S c * 1 * sgn c z * M x (act c z)) := by rw [hX]
          _ = chiS S a * sgn a x * (chiS S c * sgn c z * M x (act c z)) := by ring)]
  rw [WSfun, Finset.mul_sum]

/-! ## The main statement -/

theorem WSfunAct {m : ℕ} {ι : Type}
    (act : (Fin m → ZMod 2) → ι → ι) (sgn : (Fin m → ZMod 2) → ι → ℝ)
    (M : Matrix ι ι ℝ)
    (hact : ∀ a b x, act (a + b) x = act a (act b x))
    (hact0 : ∀ x, act 0 x = x)
    (hsgn : ∀ a b x, sgn (a + b) x = sgn a (act b x) * sgn b x)
    (hsgnval : ∀ a x, sgn a x = 1 ∨ sgn a x = -1)
    (hMinv : ∀ a x y, sgn a x * sgn a y * M (act a x) (act a y) = M x y)
    (S : Finset (Fin m))
    (hchi : ∀ (S : Finset (Fin m)) (a b : Fin m → ZMod 2), chiS S (a + b) = chiS S a * chiS S b)
    (a b : Fin m → ZMod 2) (x y : ι) :
    WSfun act sgn M S (act a x) (act b y)
      = chiS S (a + b) * sgn a x * sgn b y * WSfun act sgn M S x y := by
  rw [WSfun_fst' act sgn M hact hact0 hsgn hsgnval hMinv S hchi a x (act b y)]
  rw [WSfun_snd' act sgn M hact hact0 hsgn hsgnval S hchi b x y]
  rw [hchi S a b]
  ring

end Work.PTCert.Fourier
