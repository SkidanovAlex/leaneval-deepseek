import Submission.ZagierHoffmanProof.DegNu
import Submission.ZagierHoffmanProof.EndgameDeg

/-!
# The `θ_ν`-degree on the field `ratLevelF ν` and on `ratLevelF ν[X]`

`PLAN.md` §«SESSION 357» §6(ii): the ABP rows of the two-term datum have coefficients in
`ambKperf F = ⋃_ν ratLevelF ν`, a **field** of rational functions of `θ_ν` — not in the ring
`ambA F ν = F_q[θ_ν]` on which `DegNu.degNu` is defined.  Hence the `θ_ν`-degree of the rows has to
be built on the field `ratLevelF ν = F_q(θ_ν)`: for `x = a/b` with `a, b ∈ A_ν`, `b ≠ 0`, set

  `Dν x := (degNu F ν a : ℤ) - (degNu F ν b : ℤ)`.

This module carries out **step 1** of that construction in the *representative* form that the
application actually uses — no `Subfield.closure` induction and no fraction-field API are needed:

* `degNu_div_welldef` — `Dν` is well defined on `a/b`;
* `degNu_div_mul` — `Dν` is additive over products;
* `degNu_div_add_le` — `Dν` is nonarchimedean on sums;
Everything is stated for two representative pairs `a/b` and `c/e` in `A_ν`.  (The remaining piece of
step 1 — the *cancellation* form `Dν x < Dν y ⟹ Dν (x+y) = Dν y`, which is the `hDq` input of
`Step7Endgame.dvd_pred_of_deg_data_scaled` — reduces to the polynomial statement
`degNu ν (x+y) = degNu ν y` for `degNu ν x < degNu ν y`, i.e. the `natDegree`-additivity of the
witness polynomials; it is not in this module yet.)

⚠ Note the well-definedness statement **needs the representatives to be nonzero**: `0 = 0/1 = 0/θ_ν`
and `Dν` at `0` is `-∞` mathematically, so `Dν` is only a `ℤ`-valued function off `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. Step 1: `Dν` is well defined on `a / b` -/

/-- `degNu ν` is subadditive over products (the zero cases are the only content). -/
lemma degNu_mul_le {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν) :
    degNu F ν (x * y) ≤ degNu F ν x + degNu F ν y := by
  rcases eq_or_ne x 0 with h0 | hx0
  · rw [h0, zero_mul, degNu_zero]; exact Nat.zero_le _
  rcases eq_or_ne y 0 with h0 | hy0
  · rw [h0, mul_zero, degNu_zero]; exact Nat.zero_le _
  · rw [degNu_mul F hx hy hx0 hy0]

/-- ★ **Step 1 of §6(ii): the `θ_ν`-degree of a quotient of `A_ν`-elements is well defined.**  If
`a/b = c/e` with `a, b, c, e ∈ A_ν`, `b, e ≠ 0` and `a ≠ 0`, then
`degNu ν a - degNu ν b = degNu ν c - degNu ν e`. -/
theorem degNu_div_welldef {ν : ℕ} {a b c e : Ambient F}
    (ha : a ∈ ambA F ν) (hb : b ∈ ambA F ν) (hb0 : b ≠ 0)
    (hc : c ∈ ambA F ν) (he : e ∈ ambA F ν) (he0 : e ≠ 0) (ha0 : a ≠ 0)
    (h : a / b = c / e) :
    (degNu F ν a : ℤ) - (degNu F ν b : ℤ)
      = (degNu F ν c : ℤ) - (degNu F ν e : ℤ) := by
  have hae : a * e = c * b := (div_eq_div_iff hb0 he0).mp h
  have hae0 : a * e ≠ 0 := mul_ne_zero ha0 he0
  have hcb0 : c * b ≠ 0 := by rw [← hae]; exact hae0
  have hc0 : c ≠ 0 := fun h0 => hcb0 (by rw [h0, zero_mul])
  have h2 : degNu F ν a + degNu F ν e = degNu F ν c + degNu F ν b := by
    have h3 := congrArg (fun z : Ambient F => degNu F ν z) hae
    rwa [degNu_mul F ha he ha0 he0, degNu_mul F hc hb hc0 hb0] at h3
  omega

/-! ## §2. Additivity and the nonarchimedean properties of `Dν` -/

/-- **`Dν` is additive over products**: `Dν ((a/b)·(c/e)) = Dν (a/b) + Dν (c/e)`. -/
theorem degNu_div_mul {ν : ℕ} {a b c e : Ambient F}
    (ha : a ∈ ambA F ν) (hb : b ∈ ambA F ν) (hb0 : b ≠ 0)
    (hc : c ∈ ambA F ν) (he : e ∈ ambA F ν) (he0 : e ≠ 0)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0) :
    (degNu F ν (a * c) : ℤ) - (degNu F ν (b * e) : ℤ)
      = ((degNu F ν a : ℤ) - (degNu F ν b : ℤ))
        + ((degNu F ν c : ℤ) - (degNu F ν e : ℤ)) := by
  rw [degNu_mul F ha hc ha0 hc0, degNu_mul F hb he hb0 he0]
  push_cast
  ring

/-- **`Dν` is nonarchimedean**: `Dν ((a/b) + (c/e)) ≤ max (Dν (a/b)) (Dν (c/e))`. -/
theorem degNu_div_add_le {ν : ℕ} {a b c e : Ambient F}
    (ha : a ∈ ambA F ν) (hb : b ∈ ambA F ν) (hb0 : b ≠ 0)
    (hc : c ∈ ambA F ν) (he : e ∈ ambA F ν) (he0 : e ≠ 0) :
    (degNu F ν (a * e + c * b) : ℤ) - (degNu F ν (b * e) : ℤ)
      ≤ max ((degNu F ν a : ℤ) - (degNu F ν b : ℤ))
          ((degNu F ν c : ℤ) - (degNu F ν e : ℤ)) := by
  have hnum : (degNu F ν (a * e + c * b) : ℤ)
      ≤ max ((degNu F ν a : ℤ) + (degNu F ν e : ℤ))
          ((degNu F ν c : ℤ) + (degNu F ν b : ℤ)) := by
    have h1 : (degNu F ν (a * e + c * b) : ℤ)
        ≤ max ((degNu F ν (a * e) : ℤ)) ((degNu F ν (c * b) : ℤ)) := by
      exact_mod_cast degNu_add_le F (ambA_mul_mem F ha he) (ambA_mul_mem F hc hb)
    have h2 : (degNu F ν (a * e) : ℤ) ≤ (degNu F ν a : ℤ) + (degNu F ν e : ℤ) := by
      exact_mod_cast degNu_mul_le (F := F) ha he
    have h3 : (degNu F ν (c * b) : ℤ) ≤ (degNu F ν c : ℤ) + (degNu F ν b : ℤ) := by
      exact_mod_cast degNu_mul_le (F := F) hc hb
    exact h1.trans (max_le_max h2 h3)
  have hbe : (degNu F ν (b * e) : ℤ) = (degNu F ν b : ℤ) + (degNu F ν e : ℤ) := by
    rw [degNu_mul F hb he hb0 he0]; push_cast; ring
  have hmax : max ((degNu F ν a : ℤ) + (degNu F ν e : ℤ))
        ((degNu F ν c : ℤ) + (degNu F ν b : ℤ)) - ((degNu F ν b : ℤ) + (degNu F ν e : ℤ))
      = max ((degNu F ν a : ℤ) - (degNu F ν b : ℤ))
          ((degNu F ν c : ℤ) - (degNu F ν e : ℤ)) := by
    have key : ∀ x y z : ℤ, max x y - z = max (x - z) (y - z) := by
      intro x y z
      rcases le_total x y with h | h
      · rw [max_eq_right h, max_eq_right (sub_le_sub_right h z)]
      · rw [max_eq_left h, max_eq_left (sub_le_sub_right h z)]
    rw [key]
    congr 1 <;> ring
  have hfin := sub_le_sub_right hnum ((degNu F ν b : ℤ) + (degNu F ν e : ℤ))
  rw [hmax] at hfin
  rw [hbe]
  exact hfin

/-! ## §3. Step 1 completed: the cancellation form of `Dν`

The remaining input of §6(ii) is the *cancellation* form of the nonarchimedean property: if the two
degrees differ, the sum has the larger one.  For `A_ν` this is the additivity of `natDegree` of the
witness polynomials (`degNu_eq_of_eval` + `Polynomial.natDegree_add_eq_right_of_natDegree_lt`). -/

/-- ★ **`degNu` is a degree: if the degrees differ, the sum has the larger one.** -/
lemma degNu_add_of_lt {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν)
    (h : degNu F ν x < degNu F ν y) :
    degNu F ν (x + y) = degNu F ν y := by
  obtain ⟨p, hp⟩ := (mem_ambA_iff F ν x).mp hx
  obtain ⟨q, hq⟩ := (mem_ambA_iff F ν y).mp hy
  have hx' : degNu F ν x = p.natDegree := degNu_eq_of_eval F hx hp
  have hy' : degNu F ν y = q.natDegree := degNu_eq_of_eval F hy hq
  have hpq : (p + q).eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x + y := by
    rw [Polynomial.eval₂_add, hp, hq]
  calc degNu F ν (x + y)
      = (p + q).natDegree := degNu_eq_of_eval F ((ambASub F ν).add_mem hx hy) hpq
    _ = q.natDegree :=
        Polynomial.natDegree_add_eq_right_of_natDegree_lt (by rw [hx', hy'] at h; exact h)
    _ = degNu F ν y := hy'.symm

/-- ★ **The cancellation form of `Dν`**: if `Dν (a/b) < Dν (c/e)` then
`Dν ((a/b) + (c/e)) = Dν (c/e)`. -/
theorem degNu_div_add_lt {ν : ℕ} {a b c e : Ambient F}
    (ha : a ∈ ambA F ν) (hb : b ∈ ambA F ν) (hb0 : b ≠ 0)
    (hc : c ∈ ambA F ν) (he : e ∈ ambA F ν) (he0 : e ≠ 0)
    (ha0 : a ≠ 0) (hc0 : c ≠ 0)
    (h : (degNu F ν a : ℤ) - (degNu F ν b : ℤ)
      < (degNu F ν c : ℤ) - (degNu F ν e : ℤ)) :
    (degNu F ν (a * e + c * b) : ℤ) - (degNu F ν (b * e) : ℤ)
      = (degNu F ν c : ℤ) - (degNu F ν e : ℤ) := by
  have hlt : degNu F ν (a * e) < degNu F ν (c * b) := by
    rw [degNu_mul F ha he ha0 he0, degNu_mul F hc hb hc0 hb0]
    omega
  have hbe : degNu F ν (b * e) = degNu F ν b + degNu F ν e := degNu_mul F hb he hb0 he0
  rw [degNu_add_of_lt (ambA_mul_mem F ha he) (ambA_mul_mem F hc hb) hlt, hbe,
    degNu_mul F hc hb hc0 hb0]
  push_cast
  ring

/-! ## §4. Step 2 (first half): the `θ_ν`-degree of `polyTwist 1 p`

`degPolyNu F ν` is already the `θ_ν`-degree of a polynomial with `A_ν`-coefficients
(`degPolyNu F ν p = degPoly (twNu ν p)`), so no new definition is needed at the polynomial level:
the "lift to `ratLevelF ν[X]`" of §6(ii) step 2 is realised by **clearing denominators**
(`AbpDescentRestrict.mem_ratLevelF_iff` gives `x = p/q` with `p, q ∈ A_ν`, and a finite product of
denominators makes `d · Z`, `d · Q`, `d · Y` have `A_ν`-coefficients, while the identities (R)/(A)
are *preserved* by scaling `Z`, `Q`, `Y` by one common `d`).

The one ingredient that is new is that `polyTwist 1` multiplies the `θ_ν`-degree by `q`. -/

/-- ★ **Step 2's hinge**: `degPolyNu F ν (polyTwist 1 p) = q · degPolyNu F ν p` for `p` with
`A_ν`-coefficients.  This is the level-`ν` form of `EndgameDeg.degPoly_polyTwist`. -/
theorem degPolyNu_polyTwist_one {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) :
    degPolyNu F ν (polyTwist (q := Nat.card F) 1 p) = Nat.card F * degPolyNu F ν p := by
  have hcoeff : ∀ n, (twNu F ν (polyTwist (q := Nat.card F) 1 p)).coeff n
      = (polyTwist (q := Nat.card F) 1 (twNu F ν p)).coeff n := by
    intro n
    rw [twNu_coeff, polyTwist_one_coeff, polyTwist_one_coeff, twNu_coeff, ← pow_mul, ← pow_mul,
      Nat.mul_comm (Nat.card F) (Nat.card F ^ ν)]
  have heq : twNu F ν (polyTwist (q := Nat.card F) 1 p)
      = polyTwist (q := Nat.card F) 1 (twNu F ν p) :=
    Polynomial.ext hcoeff
  rw [degPolyNu, heq]
  exact degPoly_polyTwist F (twNu F ν p) (fun n => twNu_coeff_mem_ambA0 F hp n)

/-! ## §5. Step 2 (second half): multiplicativity of `degPolyNu`

The missing `mul` lemma of the `DegNu` API.  It is `EndgameDeg.degPoly_mul` transported along
`twNu ν`; the only work is `twNu ν (p*q) = twNu ν p * twNu ν q` and the fact that `twNu ν` is
injective off `0`. -/

/-- `twNu ν` is multiplicative. -/
lemma twNu_mul (ν : ℕ) (p q : Polynomial (Ambient F)) :
    twNu F ν (p * q) = twNu F ν p * twNu F ν q := by
  induction ν with
  | zero =>
      have h0 : twNu F 0 p = p := Polynomial.ext fun n => by simp [twNu_coeff]
      have h1 : twNu F 0 q = q := Polynomial.ext fun n => by simp [twNu_coeff]
      have h2 : twNu F 0 (p * q) = p * q := Polynomial.ext fun n => by simp [twNu_coeff]
      rw [h0, h1, h2]
  | succ n ih => simp only [twNu_succ, ih, polyTwist_mul]

/-- `twNu ν` kills only `0`. -/
lemma twNu_ne_zero {ν : ℕ} {p : Polynomial (Ambient F)} (hp0 : p ≠ 0) :
    twNu F ν p ≠ 0 := by
  intro h
  refine hp0 (Polynomial.ext fun n => ?_)
  have hc := congrArg (fun r : Polynomial (Ambient F) => r.coeff n) h
  rw [twNu_coeff, Polynomial.coeff_zero] at hc
  have hq : Nat.card F ≠ 0 := by have := two_le_ambCard F; omega
  exact (pow_eq_zero_iff (pow_ne_zero ν hq)).mp hc

/-- ★★ **Step 2's product lemma**: `degPolyNu F ν` is additive over products (for nonzero factors). -/
theorem degPolyNu_mul {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    degPolyNu F ν (p * q) = degPolyNu F ν p + degPolyNu F ν q := by
  have hp' : ∀ n, (twNu F ν p).coeff n ∈ ambA F 0 := fun n => twNu_coeff_mem_ambA0 F hp n
  have hq' : ∀ n, (twNu F ν q).coeff n ∈ ambA F 0 := fun n => twNu_coeff_mem_ambA0 F hq n
  rw [degPolyNu, twNu_mul]
  exact degPoly_mul F (twNu F ν p) (twNu F ν q) hp' hq'
    (twNu_ne_zero hp0) (twNu_ne_zero hq0)

/-! ## §6. Step 3: the degrees of `W`, `L^q`, `H_w`, `P`, `A₁`

The building block of all five: the `θ_ν`-degree of `θ^q` is `q^{ν+1}` (the multiplier of `σ` is
`q`, and `θ` has `θ_ν`-degree `q^ν`).  This is what makes `deg_ν W = q^{ν+1}` for
`W = X - C(θ^q)` and `deg_ν (L^q) = q^{ν+1}` for `L = X - θ`. -/

/-- ★ **Step 3's building block**: `θ ∈ A_ν` has `θ_ν`-degree `q^ν` (`degNu_ambTheta`), and squaring
the `σ`-multiplier gives `degNu ν (θ^q) = q · q^ν = q^{ν+1}`. -/
lemma degNu_ambTheta_pow_card (ν : ℕ) :
    degNu F ν ((ambTheta F) ^ Nat.card F) = Nat.card F ^ (ν + 1) := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  rw [degNu_pow_card F hmem, degNu_ambTheta F ν, ← pow_succ']

/-! ## §7. Step 3, row one: the degree of `W = X − C(θ^q)`

First the two prerequisites: `twNu ν` fixes `X` and raises a constant to the `q^ν`-th power, so
`twNu ν (X − C(θ^q)) = X − C(θ^(q^(ν+1)))` and `degPolyNu_le_iff`/`degPoly_X_sub_C` finish. -/

/-- `twNu ν` fixes `X`. -/
lemma twNu_X (ν : ℕ) : twNu F ν (Polynomial.X : Polynomial (Ambient F)) = Polynomial.X := by
  have hq : Nat.card F ^ ν ≠ 0 := pow_ne_zero ν (by have := two_le_ambCard F; omega)
  ext n
  rw [twNu_coeff, Polynomial.coeff_X]
  split_ifs <;> simp [zero_pow hq]

/-- `twNu ν` raises a constant to the `q^ν`-th power. -/
lemma twNu_C (ν : ℕ) (a : Ambient F) :
    twNu F ν (Polynomial.C a) = Polynomial.C (a ^ (Nat.card F ^ ν)) := by
  have hq : Nat.card F ^ ν ≠ 0 := pow_ne_zero ν (by have := two_le_ambCard F; omega)
  ext n
  simp only [twNu_coeff, Polynomial.coeff_C]
  split_ifs <;> simp [zero_pow hq]

/-- `twNu ν` and `X − C a`: the last joint of row one. -/
lemma twNu_X_sub_C (ν : ℕ) (a : Ambient F) :
    twNu F ν (Polynomial.X - Polynomial.C a)
      = Polynomial.X - Polynomial.C (a ^ (Nat.card F ^ ν)) := by
  have hq : Nat.card F ^ ν ≠ 0 := pow_ne_zero ν (by have := two_le_ambCard F; omega)
  ext n
  rw [twNu_coeff, ← frobPowHom_apply]
  simp only [coeff_X_sub_C]
  rw [map_sub]
  congr 1
  · split_ifs <;> simp [zero_pow hq]
  · split_ifs <;> simp [frobPowHom_apply, zero_pow hq]

/-- ★★ **Step 3, row one**: the `θ_ν`-degree of `W = X − C(θ^q)` is `q^(ν+1)`. -/
theorem degPolyNu_X_sub_theta_pow (ν : ℕ) :
    degPolyNu F ν (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
      = Nat.card F ^ (ν + 1) := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  have hpow : (ambTheta F) ^ Nat.card F ∈ ambA F ν := ambA_pow_card_mem F hmem
  have h0 : ((ambTheta F) ^ Nat.card F) ^ (Nat.card F ^ ν) ∈ ambA F 0 :=
    ambA_pow_pow_card_mem F hpow
  rw [degPolyNu, twNu_X_sub_C, degPoly_X_sub_C F h0, ← degNu_eq_degTheta_pow F hpow]
  exact degNu_ambTheta_pow_card (F := F) ν

/-! ## §8. Step 3, row two: the degree of `X^q − X`

Its coefficients are constants (`0`, `±1`), so they lie in `ambF F ⊆ ambA F ν` and have `θ_ν`-degree
`0`; `degPolyNu_le_iff` then gives `degPolyNu F ν (X^q − X) = 0`. -/

/-- The coefficients of `X^q − X` are in `ambF F` (they are `0`, `1`, `−1`). -/
lemma coeff_X_pow_sub_X_mem_ambF (n : ℕ) :
    (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n ∈ ambF F := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  refine (ambF F).sub_mem ?_ ?_
  · split_ifs with h
    · exact (ambF F).one_mem
    · exact (ambF F).zero_mem
  · split_ifs with h
    · exact (ambF F).one_mem
    · exact (ambF F).zero_mem

/-- ★★ **Step 3, row two**: `degPolyNu F ν (X^q − X) = 0`. -/
theorem degPolyNu_X_pow_sub_X (ν : ℕ) :
    degPolyNu F ν (Polynomial.X ^ Nat.card F - Polynomial.X) = 0 := by
  have hcoeffF : ∀ n,
      (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n ∈ ambF F :=
    fun n => coeff_X_pow_sub_X_mem_ambF n
  have hcoeff : ∀ n,
      (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hcoeffF n))
  refine Nat.eq_zero_of_le_zero ((degPolyNu_le_iff F hcoeff).mpr (fun n => ?_))
  rw [degNu_ambF F (hcoeffF n)]

/-! ## §9. Step 3, row three: the degree of `L^q = (X − θ)^q`

Row one's twin: `twNu_X_sub_C` gives `twNu ν (X − θ) = X − C(θ^(q^ν))`, `twNu_pow` moves the `q`-th
power outside, `degPoly_pow`+`degPoly_X_sub_C` reduce it to `q · degTheta (θ^(q^ν)) = q · q^ν`. -/

/-- `twNu ν` fixes `1`. -/
lemma twNu_one (ν : ℕ) : twNu F ν (1 : Polynomial (Ambient F)) = 1 := by
  rw [← Polynomial.C_1, twNu_C ν 1, one_pow, Polynomial.C_1]

/-- `twNu ν` is multiplicative on powers. -/
lemma twNu_pow (ν : ℕ) (p : Polynomial (Ambient F)) (k : ℕ) :
    twNu F ν (p ^ k) = (twNu F ν p) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact twNu_one ν
  | succ n ih => rw [pow_succ, pow_succ, twNu_mul, ih]

/-- The coefficients of `X − C b` for `b ∈ A_0` lie in `A_0`. -/
lemma coeff_X_sub_C_mem_ambA_zero {b : Ambient F} (hb : b ∈ ambA F 0) (n : ℕ) :
    (Polynomial.X - Polynomial.C b : Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [coeff_X_sub_C]
  refine (ambASub F 0).sub_mem ?_ ?_
  · split_ifs with h
    · exact ambA_one_mem F 0
    · exact (ambASub F 0).zero_mem
  · split_ifs with h
    · exact hb
    · exact (ambASub F 0).zero_mem

/-- ★★ **Step 3, row three**: `degPolyNu F ν ((X − θ)^q) = q^(ν+1)`. -/
theorem degPolyNu_X_sub_theta_pow_card (ν : ℕ) :
    degPolyNu F ν ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F)
      = Nat.card F ^ (ν + 1) := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  have h0 : (ambTheta F) ^ (Nat.card F ^ ν) ∈ ambA F 0 := ambA_pow_pow_card_mem F hmem
  have hcoeff : ∀ n,
      (Polynomial.X - Polynomial.C ((ambTheta F) ^ (Nat.card F ^ ν)) :
        Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    fun n => coeff_X_sub_C_mem_ambA_zero h0 n
  have hne : (Polynomial.X - Polynomial.C ((ambTheta F) ^ (Nat.card F ^ ν)) :
      Polynomial (Ambient F)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff 1) h
    rw [coeff_X_sub_C, Polynomial.coeff_zero] at h1
    norm_num at h1
  rw [degPolyNu, twNu_pow, twNu_X_sub_C,
    degPoly_pow F _ hcoeff hne (Nat.card F), degPoly_X_sub_C F h0,
    ← degNu_eq_degTheta_pow F hmem, degNu_ambTheta F ν, ← pow_succ']

/-! ## §10. Step 3, row four: constants

`H_w = P + (w − q)·L^q` is a sum of two rows already done, weighted by the *constant* `(w − q)`; the
degrees of such sums need the degree of `C c`, and that is `degNu ν c` by `twNu_C` + `degPoly_C` +
`degNu_eq_degTheta_pow`. -/

/-- ★ **The degree of a constant multiple**: `degPolyNu F ν (C c · p) = degNu F ν c + degPolyNu F ν p`
for `c ∈ A_ν ∖ {0}` and `p` with `A_ν`-coefficients. -/
theorem degPolyNu_C_mul {ν : ℕ} {c : Ambient F} (hc : c ∈ ambA F ν) (hc0 : c ≠ 0)
    {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F ν) (hp0 : p ≠ 0) :
    degPolyNu F ν (Polynomial.C c * p) = degNu F ν c + degPolyNu F ν p := by
  have hcp : Polynomial.C c * p ≠ 0 := by
    rw [Polynomial.C_mul']
    exact smul_ne_zero hc0 hp0
  have hcoe : ∀ n, (Polynomial.C c).coeff n ∈ ambA F ν := by
    intro n
    rw [Polynomial.coeff_C]
    split_ifs with h
    · exact hc
    · exact (ambASub F ν).zero_mem
  rw [degPolyNu_mul hcoe hp (Polynomial.C_ne_zero.mpr hc0) hp0, degPolyNu_C F hc]

/-- ★ **`degPolyNu` is insensitive to sign** — the tool that turns the `H_w` inequality `≥` into an
application of `degPolyNu_add_le` to the difference `(w − q)·L^q = H_w − P`. -/
theorem degPolyNu_neg {ν : ℕ} {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F ν) :
    degPolyNu F ν (-p) = degPolyNu F ν p := by
  have hneg : ∀ n, (-p).coeff n ∈ ambA F ν := by
    intro n
    rw [Polynomial.coeff_neg]
    exact (ambASub F ν).neg_mem (hp n)
  refine le_antisymm ?_ ?_
  · refine (degPolyNu_le_iff F hneg).mpr (fun n => ?_)
    rw [Polynomial.coeff_neg, degNu_neg F (hp n)]
    exact degPolyNu_coeff_le F hp n
  · refine (degPolyNu_le_iff F hp).mpr (fun n => ?_)
    have h1 : (-(-p)).coeff n = p.coeff n := by rw [neg_neg]
    rw [← h1, Polynomial.coeff_neg, degNu_neg F (hneg n)]
    exact degPolyNu_coeff_le F hneg n

/-! ## §12. The natural-number constants

Every weight in the endgame (`ambH`'s `(w − q)`, the coefficient weights) enters as a **natural-number
coercion** `((n : ℕ) : Ambient F)`.  Such a constant is `ambCoeff ((n : ℕ) : F)`, hence lies in
`ambF F` and has `θ_ν`-degree `0` (`degNu_ambF`). -/

/-- ★ **Natural-number constants live in `ambF F`** (they are `ambCoeff` of a natural number of `F`). -/
lemma natCast_mem_ambF (n : ℕ) : ((n : ℕ) : Ambient F) ∈ ambF F := by
  have h : (ambCoeff F) ((n : ℕ) : F) = ((n : ℕ) : Ambient F) := map_natCast (ambCoeff F) n
  rw [← h]
  exact ambCoeff_mem_ambF F _

/-- ★ **Natural-number constants have `θ_ν`-degree `0`.** -/
lemma degNu_natCast (ν n : ℕ) : degNu F ν ((n : ℕ) : Ambient F) = 0 :=
  degNu_ambF F (natCast_mem_ambF n)

/-! ## §13. `ambH`'s `else`-branch (§19.1)

`ATPoly.ambH` is `if n ≤ q then 1 else …`, so the endgame rows need it in the `else`-branch form
(where `w > q`, i.e. `k = w − q ≥ 1`).  ⚠ The `then`-branch lemma `ambH_of_le` **already exists** —
only the `else`-branch is new. -/

/-- ★ **`ambH` in the `else`-branch** (`q < w`): `H_w = (X^q − X) + (w − q)·(X^q − C(θ^q))`. -/
lemma ambH_of_lt {w : ℕ} (hwq : Nat.card F < w) :
    ambH F w = Polynomial.X ^ Nat.card F - Polynomial.X
      + Polynomial.C ((w - Nat.card F : ℕ) : Ambient F)
        * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
  rw [ambH, if_neg (not_le.mpr hwq)]

/-- ★ **`ambH` in factored form** (§19.2): the `L^q` factor is written as `(X − C θ)^q`, matching
`degPolyNu_X_sub_theta_pow_card` (row three).  The bridge is `X_sub_C_pow_card`. -/
lemma ambH_factor_of_lt {w : ℕ} (hwq : Nat.card F < w) :
    ambH F w = Polynomial.X ^ Nat.card F - Polynomial.X
      + Polynomial.C ((w - Nat.card F : ℕ) : Ambient F)
        * (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F := by
  rw [ambH_of_lt hwq, ← X_sub_C_pow_card F (ambTheta F)]

/-- ★ **The inequality form of the constant-multiple degree**, valid also at `c = 0` (the exact form
`degPolyNu_C_mul` needs `c ≠ 0`).  This is what the `H_w` upper bound consumes. -/
theorem degPolyNu_C_mul_le {ν : ℕ} {c : Ambient F} (hc : c ∈ ambA F ν)
    {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F ν) :
    degPolyNu F ν (Polynomial.C c * p) ≤ degNu F ν c + degPolyNu F ν p := by
  by_cases hc0 : c = 0
  · rw [hc0, Polynomial.C_0, zero_mul, degPolyNu_zero, degNu_zero]
    exact Nat.zero_le _
  by_cases hp0 : p = 0
  · rw [hp0, mul_zero, degPolyNu_zero]
    exact Nat.zero_le _
  · rw [degPolyNu_C_mul hc hc0 hp hp0]

/-! ## §14. Step 3, row four: the `H_w` upper bound (unconditional, cf. §24) -/

/-- `A_ν`-coefficients are preserved by powers. -/
lemma coeff_pow_mem_ambA {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (k n : ℕ) : (p ^ k).coeff n ∈ ambA F ν := by
  revert n
  induction k with
  | zero =>
      intro n
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs with h
      · exact ambA_one_mem F ν
      · exact (ambASub F ν).zero_mem
  | succ m ih =>
      intro n
      rw [pow_succ, Polynomial.coeff_mul]
      exact Subring.sum_mem (ambASub F ν)
        (fun x _ => (ambASub F ν).mul_mem (ih x.1) (hp x.2))

/-- ★★★ **Step 3, row four**: `deg_ν (H_w) ≤ q^(ν+1)`, **unconditionally in `w`**.  This is the row
the θ-degree obstruction consumes (§24); the exact value needs `((w − q : ℕ) : F) ≠ 0` (§23) and is
deferred to the `k = q−1` case. -/
theorem degPolyNu_ambH_le (ν w : ℕ) :
    degPolyNu F ν (ambH F w) ≤ Nat.card F ^ (ν + 1) := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  have hp : ∀ n, (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := fun n =>
    ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (coeff_X_pow_sub_X_mem_ambF n))
  have hL : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := fun n =>
    ambA_mono F (Nat.zero_le ν) (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero n)
  have hLq : ∀ n, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν :=
    fun n => coeff_pow_mem_ambA hL (Nat.card F) n
  have hc : ((w - Nat.card F : ℕ) : Ambient F) ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (natCast_mem_ambF (w - Nat.card F)))
  have hq : ∀ n, (Polynomial.C ((w - Nat.card F : ℕ) : Ambient F)
      * (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := by
    intro n
    rw [Polynomial.coeff_mul]
    refine Subring.sum_mem (ambASub F ν) (fun x _ => (ambASub F ν).mul_mem ?_ ?_)
    · rw [Polynomial.coeff_C]
      split_ifs with h
      · exact hc
      · exact (ambASub F ν).zero_mem
    · exact hLq x.2
  by_cases hle : w ≤ Nat.card F
  · rw [ambH_of_le F hle, ← Polynomial.C_1, degPolyNu_C F (ambA_one_mem F ν), degNu_one F]
    exact Nat.zero_le _
  · rw [ambH_factor_of_lt (not_le.mp hle)]
    refine le_trans (degPolyNu_add_le F hp hq) (max_le ?_ ?_)
    · rw [degPolyNu_X_pow_sub_X]; exact Nat.zero_le _
    · refine le_trans (degPolyNu_C_mul_le hc hLq) ?_
      rw [degNu_natCast, zero_add, degPolyNu_X_sub_theta_pow_card]

/-- ★★ **Step 3, row five**: a polynomial whose coefficients are constants of `ambF F` has
`θ_ν`-degree `0`.  This is the `degPolyNu` twin of `EndgameBound.degPoly_eq_zero_of_coeff_mem_ambF`,
and covers `A₁`, `A₂` (both `(A.map ambCoeff) * gammaPolyTup F 𝔰`, whose coefficients are products of
`ambCoeff`-values and `Γ`-polynomial coefficients). -/
theorem degPolyNu_eq_zero_of_coeff_mem_ambF {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambF F) : degPolyNu F ν p = 0 := by
  have hcoeff : ∀ n, p.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hp n))
  refine Nat.eq_zero_of_le_zero ((degPolyNu_le_iff F hcoeff).mpr (fun n => ?_))
  rw [degNu_ambF F (hp n)]

/-! ## §15. Step 3, row six: the sign bridge for the `(A)`-row

The `(A)`-row is stated with `C(θ^q) − X^q` (cf. `TwRows.tw_Y_mul_P_eq`), while row three gives the
degree of `(X − C θ)^q`; the two differ by the sign that `X_sub_C_pow_card` supplies. -/

/-- ★ `C(θ^q) − X^q = −(X − C θ)^q` — the bridge between the `(A)`-row's shape and row three. -/
lemma C_theta_pow_sub_X_pow_eq_neg :
    (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F))
      = -((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F) := by
  rw [X_sub_C_pow_card F (ambTheta F)]
  ring

/-- ★ The degree of the `(A)`-row's second factor: `deg_ν (C(θ^q) − X^q) = q^(ν+1)`. -/
lemma degPolyNu_C_theta_pow_sub_X_pow (ν : ℕ) :
    degPolyNu F ν (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      = Nat.card F ^ (ν + 1) := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  have hL : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := fun n =>
    ambA_mono F (Nat.zero_le ν) (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero n)
  have hLq : ∀ n, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν :=
    fun n => coeff_pow_mem_ambA hL (Nat.card F) n
  rw [C_theta_pow_sub_X_pow_eq_neg, degPolyNu_neg hLq, degPolyNu_X_sub_theta_pow_card]

/-! ## §16. Step 3, row six: the three-factor product step

The `(A)`-row carries three factors (`A₂ · (C(θ^q) − X^q) · Q`), so `degPolyNu_mul` is needed twice;
these two lemmas are the reusable form of that bookkeeping. -/

/-- `A_ν`-coefficients are preserved by products. -/
lemma coeff_mul_mem_ambA {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν) (n : ℕ) :
    (p * q).coeff n ∈ ambA F ν := by
  rw [Polynomial.coeff_mul]
  exact Subring.sum_mem (ambASub F ν) (fun x _ => (ambASub F ν).mul_mem (hp x.1) (hq x.2))

/-- ★ **`degPolyNu` is additive over a three-factor product** — the `(A)`-row's shape. -/
theorem degPolyNu_mul3 {ν : ℕ} {p q r : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν)
    (hr : ∀ n, r.coeff n ∈ ambA F ν) (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0) :
    degPolyNu F ν (p * q * r) = degPolyNu F ν p + degPolyNu F ν q + degPolyNu F ν r := by
  rw [degPolyNu_mul (coeff_mul_mem_ambA hp hq) hr (mul_ne_zero hp0 hq0) hr0,
    degPolyNu_mul hp hq hp0 hq0]

/-! ## §17. Step 3, row six (final): the `(A)`-row degree identity

From `Y · (X^q − X) = A₂ · (C(θ^q) − X^q) · Q` (`TwRows.tw_Y_mul_P_eq`) conclude
`deg_ν Y = deg_ν Q + q^(ν+1)`.  This is the identity §24's `hDq`/`hE` computation consumes. -/

/-- ★★★ **The `(A)`-row degree identity**: `deg_ν Y = deg_ν Q + q^(ν+1)`. -/
theorem degPolyNu_Y_of_row {ν : ℕ} {Y A₂ Q : Polynomial (Ambient F)}
    (hY : ∀ n, Y.coeff n ∈ ambA F ν) (hQ : ∀ n, Q.coeff n ∈ ambA F ν)
    (hA2 : ∀ n, A₂.coeff n ∈ ambF F)
    (hY0 : Y ≠ 0) (hQ0 : Q ≠ 0) (hA20 : A₂ ≠ 0)
    (hrow : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    degPolyNu F ν Y = degPolyNu F ν Q + Nat.card F ^ (ν + 1) := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hA2ν : ∀ n, A₂.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA2 n))
  have hPmem : ∀ n, (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := fun n =>
    ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (coeff_X_pow_sub_X_mem_ambF n))
  have hLmem : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff n
      ∈ ambA F ν := fun n =>
    ambA_mono F (Nat.zero_le ν) (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero n)
  have hCXmem : ∀ n, (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := by
    intro n
    rw [C_theta_pow_sub_X_pow_eq_neg, Polynomial.coeff_neg]
    exact (ambASub F ν).neg_mem (coeff_pow_mem_ambA hLmem (Nat.card F) n)
  have hP0 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff 1) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_zero] at h1
    rw [if_neg (by omega : ¬ (1 = Nat.card F)), if_pos rfl, zero_sub] at h1
    exact one_ne_zero (neg_eq_zero.mp h1)
  have hCX0 : (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff (Nat.card F)) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at h1
    rw [if_neg (by omega : ¬ (Nat.card F = 0)), if_pos rfl, zero_sub] at h1
    exact one_ne_zero (neg_eq_zero.mp h1)
  have hL : degPolyNu F ν (Y * (Polynomial.X ^ Nat.card F - Polynomial.X))
      = degPolyNu F ν Y := by
    rw [degPolyNu_mul hY hPmem hY0 hP0, degPolyNu_X_pow_sub_X, add_zero]
  have hR : degPolyNu F ν (A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F)
        - Polynomial.X ^ Nat.card F) * Q)
      = degPolyNu F ν Q + Nat.card F ^ (ν + 1) := by
    rw [degPolyNu_mul3 hA2ν hCXmem hQ hA20 hCX0 hQ0,
      degPolyNu_eq_zero_of_coeff_mem_ambF hA2, degPolyNu_C_theta_pow_sub_X_pow, zero_add]
    omega
  rw [← hL, hrow, hR]

/-! ## §18. The degreewise read-off of (R): its two arithmetic tools

§31 scopes item (i) as a single lemma "read (R) degreewise".  It needs (a) `A_ν`-coefficients to be
preserved by sums, and (b) the three-term upper bound `degPolyNu (Z + Y + Q·A₁·H_w) ≤ max(…)`, since
that sum has three summands.  Both are here. -/

/-- `A_ν`-coefficients are preserved by sums. -/
lemma coeff_add_mem_ambA {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν) (n : ℕ) :
    (p + q).coeff n ∈ ambA F ν := by
  rw [Polynomial.coeff_add]
  exact (ambASub F ν).add_mem (hp n) (hq n)

/-- ★ **The three-term upper bound**: `degPolyNu F ν (p + q + r) ≤ max (max dp dq) dr`. -/
theorem degPolyNu_add3_le {ν : ℕ} {p q r : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν)
    (hr : ∀ n, r.coeff n ∈ ambA F ν) :
    degPolyNu F ν (p + q + r)
      ≤ max (max (degPolyNu F ν p) (degPolyNu F ν q)) (degPolyNu F ν r) := by
  have hpq : ∀ n, (p + q).coeff n ∈ ambA F ν := fun n => coeff_add_mem_ambA hp hq n
  refine le_trans (degPolyNu_add_le F hpq hr) (max_le ?_ (le_max_right _ _))
  exact le_trans (degPolyNu_add_le F hp hq) (le_max_left _ _)

/-- `A_ν`-coefficients are preserved by three-factor products. -/
lemma coeff_mul_mem_ambA3 {ν : ℕ} {p q r : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν)
    (hr : ∀ n, r.coeff n ∈ ambA F ν) (n : ℕ) : (p * q * r).coeff n ∈ ambA F ν :=
  coeff_mul_mem_ambA (coeff_mul_mem_ambA hp hq) hr n

/-- ★ **`ambH F w` has `A_ν`-coefficients** — the membership the `Q · A₁ · H_w` slot needs (§31/§32). -/
lemma coeff_ambH_mem_ambA (ν w n : ℕ) : (ambH F w).coeff n ∈ ambA F ν := by
  have hP : ∀ m, (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff m
      ∈ ambA F ν := fun m =>
    ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (coeff_X_pow_sub_X_mem_ambF m))
  have hL : ∀ m, (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)).coeff m
      ∈ ambA F ν := fun m =>
    ambA_mono F (Nat.zero_le ν) (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero m)
  have hLq : ∀ m, ((Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F :
      Polynomial (Ambient F)).coeff m ∈ ambA F ν :=
    fun m => coeff_pow_mem_ambA hL (Nat.card F) m
  have hCc : ∀ m, (Polynomial.C ((w - Nat.card F : ℕ) : Ambient F) :
      Polynomial (Ambient F)).coeff m ∈ ambA F ν := by
    intro m
    rw [Polynomial.coeff_C]
    split_ifs with h
    · exact ambA_mono F (Nat.zero_le ν)
        (ambF_subset_ambA_zero (natCast_mem_ambF (w - Nat.card F)))
    · exact (ambASub F ν).zero_mem
  by_cases hle : w ≤ Nat.card F
  · rw [ambH_of_le F hle, Polynomial.coeff_one]
    split_ifs with h
    · exact ambA_one_mem F ν
    · exact (ambASub F ν).zero_mem
  · rw [ambH_factor_of_lt (not_le.mp hle)]
    exact coeff_add_mem_ambA hP (coeff_mul_mem_ambA hCc hLq) n

/-- ★ **The inequality form of `degPolyNu_mul`** — valid also when a factor vanishes.  This is what
the `G`-bound of §31/§32 step 3 consumes, where none of `Q`, `A₁`, `H_w` is known to be nonzero. -/
theorem degPolyNu_mul_le {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν) :
    degPolyNu F ν (p * q) ≤ degPolyNu F ν p + degPolyNu F ν q := by
  by_cases hp0 : p = 0
  · rw [hp0, zero_mul, degPolyNu_zero]
    exact Nat.zero_le _
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, degPolyNu_zero]
    exact Nat.zero_le _
  · rw [degPolyNu_mul hp hq hp0 hq0]

/-- ★★ **§32 step 3**: the `Q · A₁ · H_w` bound.  With `A₁` of `ambF F`-coefficients (so `degν A₁ = 0`,
`degPolyNu_eq_zero_of_coeff_mem_ambF`) and any `H` with `degν H ≤ q^(ν+1)` (e.g. `H_w`, §26):

  `deg_ν (Q · A₁ · H) ≤ deg_ν Q + q^(ν+1)`.

No nonvanishing hypothesis is needed — this is the inequality route, not `degPolyNu_mul3`. -/
theorem degPolyNu_mul_ambF_le {ν : ℕ} {Q A₁ H : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hA₁ : ∀ n, A₁.coeff n ∈ ambF F)
    (hH : ∀ n, H.coeff n ∈ ambA F ν)
    (hHle : degPolyNu F ν H ≤ Nat.card F ^ (ν + 1)) :
    degPolyNu F ν (Q * A₁ * H) ≤ degPolyNu F ν Q + Nat.card F ^ (ν + 1) := by
  have hA₁ν : ∀ n, A₁.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ n))
  have hQA : ∀ n, (Q * A₁).coeff n ∈ ambA F ν := fun n => coeff_mul_mem_ambA hQ hA₁ν n
  have h1 : degPolyNu F ν (Q * A₁) ≤ degPolyNu F ν Q := by
    refine le_trans (degPolyNu_mul_le hQ hA₁ν) ?_
    rw [degPolyNu_eq_zero_of_coeff_mem_ambF hA₁, add_zero]
  refine le_trans (le_trans (degPolyNu_mul_le hQA hH) (add_le_add h1 hHle)) ?_
  omega

/-- ★★ **§32 step 4, left side of (R)**: `deg_ν (Q · σ Z) ≤ deg_ν Q + q · deg_ν Z`.
This is `degPolyNu_mul_le` once `σ`'s effect on the degree is known (`degPolyNu_polyTwist_one`, §10);
`polyTwist`'s coefficients stay in `A_ν` (`ABPKperf.polyTwist_coeff_mem_ambA`). -/
theorem degPolyNu_mul_polyTwist_le {ν : ℕ} {Q Z : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hZ : ∀ n, Z.coeff n ∈ ambA F ν) :
    degPolyNu F ν (Q * polyTwist (q := Nat.card F) 1 Z)
      ≤ degPolyNu F ν Q + Nat.card F * degPolyNu F ν Z :=
  le_trans (degPolyNu_mul_le hQ (polyTwist_coeff_mem_ambA F hZ 1))
    (le_of_eq (congrArg (fun x => degPolyNu F ν Q + x) (degPolyNu_polyTwist_one hZ)))

/-- ★★★ **§32 step 4, the `W^w` factor**: `degPolyNu F ν (p^k) = k · degPolyNu F ν p` for `p` with
`A_ν`-coefficients and `p ≠ 0`.  With `p := X − C(θ^q)` and §14 this gives `deg_ν W^w = w · q^(ν+1)`. -/
theorem degPolyNu_pow {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hp0 : p ≠ 0) (k : ℕ) :
    degPolyNu F ν (p ^ k) = k * degPolyNu F ν p := by
  induction k with
  | zero =>
      rw [pow_zero, ← Polynomial.C_1, degPolyNu_C F (ambA_one_mem F ν), degNu_one F, Nat.zero_mul]
  | succ m ih =>
      rw [pow_succ, degPolyNu_mul (coeff_pow_mem_ambA hp m) hp (pow_ne_zero m hp0) hp0, ih]
      ring

/-- ★★ **§37 sub-goal 2(a), done at every level**: `X − C(θ^q)` has `A_ν`-coefficients.  The route is
`ambA_pow_card_mem F` applied to `θ ∈ ambA F ν` (which gives `θ^q ∈ ambA F ν` for **every** `ν`),
**not** `coeff_X_sub_C_mem_ambA_zero`, whose hypothesis is `θ^q ∈ ambA F 0` — true only at `ν = 0`. -/
lemma coeff_X_sub_C_theta_pow_mem_ambA (ν n : ℕ) :
    (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := by
  have hmem : ambTheta F ∈ ambA F ν :=
    ambA_mono F (Nat.zero_le ν) ambTheta_mem_ambA_zero
  have hpow : (ambTheta F) ^ Nat.card F ∈ ambA F ν := ambA_pow_card_mem F hmem
  rw [coeff_X_sub_C]
  refine (ambASub F ν).sub_mem ?_ ?_
  · split_ifs with h
    · exact ambA_one_mem F ν
    · exact (ambASub F ν).zero_mem
  · split_ifs with h
    · exact hpow
    · exact (ambASub F ν).zero_mem

/-- ★★ **§37 sub-goal 2(b)**: `W^w` has `A_ν`-coefficients — `coeff_pow_mem_ambA` (§26) on §38. -/
lemma coeff_X_sub_C_theta_pow_pow_mem_ambA (ν w n : ℕ) :
    ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν :=
  coeff_pow_mem_ambA (coeff_X_sub_C_theta_pow_mem_ambA ν) w n

/-- ★★ **§37 sub-goal 3**: the `(Z + Y + Q·A₁·H_w)` slot of (R) has `A_ν`-coefficients —
`coeff_mul_mem_ambA3` (§16/§33) for `Q·A₁·H_w` (`A₁` of `ambF F`-coefficients via §27's hypothesis
shape, `H_w` via §33), then `coeff_add_mem_ambA` (§32) twice. -/
lemma coeff_R_slot_mem_ambA {ν w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hZ : ∀ n, Z.coeff n ∈ ambA F ν) (hY : ∀ n, Y.coeff n ∈ ambA F ν)
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (n : ℕ) :
    (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambA F ν := by
  have hA₁ν : ∀ m, A₁.coeff m ∈ ambA F ν :=
    fun m => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ m))
  have hQA : ∀ m, (Q * A₁ * ambH F w).coeff m ∈ ambA F ν :=
    fun m => coeff_mul_mem_ambA3 hQ hA₁ν (fun m => coeff_ambH_mem_ambA ν w m) m
  exact coeff_add_mem_ambA (coeff_add_mem_ambA hZ hY) hQA n

/-- ★★ **§37 sub-goal 4**: `X − C(θ^q) ≠ 0` — its `n = 1` coefficient is `1`. -/
lemma X_sub_C_theta_pow_ne_zero :
    (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) : Polynomial (Ambient F)) ≠ 0 := by
  refine fun h => ?_
  have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff 1) h
  rw [coeff_X_sub_C, Polynomial.coeff_zero] at h1
  simp at h1

/-- ★★★ **§36/§40 assembly, the right side of (R)**: the three-factor bound
`deg_ν (σQ · W^w · G) ≤ q·deg_ν Q + w·q^(ν+1) + E_G` from the two factor degrees (§10 for `σ`,
§36+§14 for `W^w`) and any bound `deg_ν G ≤ E_G`. -/
theorem degPolyNu_R_side_le {ν w : ℕ} {Q G : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hG : ∀ n, G.coeff n ∈ ambA F ν) {EG : ℕ}
    (hGle : degPolyNu F ν G ≤ EG) :
    degPolyNu F ν (polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * G)
      ≤ Nat.card F * degPolyNu F ν Q + w * Nat.card F ^ (ν + 1) + EG := by
  have hσQ : ∀ n, (polyTwist (q := Nat.card F) 1 Q).coeff n ∈ ambA F ν :=
    polyTwist_coeff_mem_ambA F hQ 1
  have hWmem : ∀ n, (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := fun n =>
    coeff_X_sub_C_theta_pow_mem_ambA ν n
  have hWw : ∀ n, ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := fun n =>
    coeff_X_sub_C_theta_pow_pow_mem_ambA ν w n
  have hσQd : degPolyNu F ν (polyTwist (q := Nat.card F) 1 Q)
      = Nat.card F * degPolyNu F ν Q := degPolyNu_polyTwist_one hQ
  have hWwd : degPolyNu F ν ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w)
      = w * Nat.card F ^ (ν + 1) := by
    rw [degPolyNu_pow hWmem X_sub_C_theta_pow_ne_zero w, degPolyNu_X_sub_theta_pow]
  refine le_trans (le_trans (degPolyNu_mul_le (coeff_mul_mem_ambA hσQ hWw) hG)
    (add_le_add (degPolyNu_mul_le hσQ hWw) (le_refl _))) ?_
  rw [hσQd, hWwd]
  omega

/-- ★★★ **§41 piece 1: the exact (equality) form of the right side of (R)** — the reverse comparison.
`degPolyNu_mul3` (§16) with §10/§36/§14 for the three factor degrees.  The nonvanishing of `σ Q` is
taken as a hypothesis (in the application it follows from `Q ≠ 0`); `W^w ≠ 0` comes from §40. -/
theorem degPolyNu_R_side_eq {ν w : ℕ} {Q G : Polynomial (Ambient F)}
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hG : ∀ n, G.coeff n ∈ ambA F ν)
    (hσQ0 : polyTwist (q := Nat.card F) 1 Q ≠ 0) (hG0 : G ≠ 0) :
    degPolyNu F ν (polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * G)
      = Nat.card F * degPolyNu F ν Q + w * Nat.card F ^ (ν + 1) + degPolyNu F ν G := by
  have hσQ : ∀ n, (polyTwist (q := Nat.card F) 1 Q).coeff n ∈ ambA F ν :=
    polyTwist_coeff_mem_ambA F hQ 1
  have hWmem : ∀ n, (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := fun n =>
    coeff_X_sub_C_theta_pow_mem_ambA ν n
  have hWw : ∀ n, ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := fun n =>
    coeff_X_sub_C_theta_pow_pow_mem_ambA ν w n
  have hWw0 : ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w :
      Polynomial (Ambient F)) ≠ 0 := pow_ne_zero w X_sub_C_theta_pow_ne_zero
  rw [degPolyNu_mul3 hσQ hWw hG hσQ0 hWw0 hG0, degPolyNu_polyTwist_one hQ,
    degPolyNu_pow hWmem X_sub_C_theta_pow_ne_zero w, degPolyNu_X_sub_theta_pow]

/-- ★★★ **§41 piece 3**: the bound for the `(R)`-slot `G := Z + Y + Q·A₁·H`, with
`E_G := max (max (deg_ν Z) (deg_ν Y)) (deg_ν Q + q^(ν+1))`.  `degPolyNu_add3_le` (§32) for the
three-term sum and §34 for the third summand; `H` is arbitrary with `deg_ν H ≤ q^(ν+1)` (e.g.
`H := ambH F w` via §26). -/
theorem degPolyNu_R_slot_le {ν : ℕ} {Z Y Q A₁ H : Polynomial (Ambient F)}
    (hZ : ∀ n, Z.coeff n ∈ ambA F ν) (hY : ∀ n, Y.coeff n ∈ ambA F ν)
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hA₁ : ∀ n, A₁.coeff n ∈ ambF F)
    (hH : ∀ n, H.coeff n ∈ ambA F ν) (hHle : degPolyNu F ν H ≤ Nat.card F ^ (ν + 1)) :
    degPolyNu F ν (Z + Y + Q * A₁ * H)
      ≤ max (max (degPolyNu F ν Z) (degPolyNu F ν Y))
          (degPolyNu F ν Q + Nat.card F ^ (ν + 1)) := by
  have hA₁ν : ∀ n, A₁.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ n))
  have hQA : ∀ n, (Q * A₁ * H).coeff n ∈ ambA F ν := fun n => coeff_mul_mem_ambA3 hQ hA₁ν hH n
  refine le_trans (degPolyNu_add3_le hZ hY hQA) (max_le (le_max_left _ _) ?_)
  exact le_trans (degPolyNu_mul_ambF_le hQ hA₁ hH hHle) (le_max_right _ _)

end ZagierHoffmanPositiveChar































