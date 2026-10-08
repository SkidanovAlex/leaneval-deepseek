import Mathlib
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Vtriv` acts trivially on the centre of `A(K,θ)`

`Vtriv θ` is the subgroup of `Aut(A(K,θ))` (`K = GF(2ⁿ)`, `θ` a field automorphism of odd
order, `θ ≠ 1`) consisting of the automorphisms inducing the identity on `A/Z(A)`.  The
statement proved here is that every such automorphism fixes the centre `Z(A) = {(0,b)}`
pointwise.

## The mathematics

Write `A := A(K,θ)`, so that `(a,b) * (c,d) = (a+c, b+d+a·θc)`, and `Z(A) = {(0,b)}`.

Let `φ ∈ Vtriv θ`, i.e. `φ x * x⁻¹ ∈ Z(A)` for all `x`.  Passing to the first coordinate
this forces `(φ x).a = x.a` — every `φ ∈ Vtriv` preserves the first coordinate.  Define the
correction `W x := (φ x).b + x.b`, so that `φ x = ⟨x.a, x.b + W x⟩`.  Because `φ` is a
homomorphism, `W` is additive, `W (x·y) = W x + W y`.

Applying this to `x = ⟨a,0⟩`, `y = ⟨c,0⟩` gives `W ⟨a+c, a·θc⟩ = W ⟨a,0⟩ + W ⟨c,0⟩`; writing
`P a := W ⟨a,0⟩` and `Q b := W ⟨0,b⟩` (which is additive), and using
`W ⟨u,v⟩ = P u + Q v`, this becomes the *cocycle identity*

  `P (a+c) + Q (a·θc) = P a + P c`.

The left-hand side is symmetric in `a` and `c`, so `Q (a·θc) = Q (c·θa)`.  Two consequences:
* `Q (θ a) = Q a` (take `c = 1`), and
* `Q (θ² a · c) = Q (a · c)` (take `a ↦ θ a` and use the previous line).

Hence for all `a` with `θ² a ≠ a` and all `c`, writing `w = θ²a + a ≠ 0`,
`Q (w·c) = Q (θ²a·c) + Q (a·c) = 0`.  As `w ≠ 0` the products `w·c` exhaust `K`, so
`Q ≡ 0`.  Since `Q b = W ⟨0,b⟩`, we get `φ ⟨0,b⟩ = ⟨0,b⟩`, i.e. `φ` fixes `Z(A)`.

Finally `odd (orderOf θ)` and `θ ≠ 1` give `θ² ≠ 1`, so such an `a` exists (this is exactly
where the oddness hypothesis is used).
-/

noncomputable section

namespace Work.ZassenhausSuzuki.SzAuto

open SzA

variable {n : ℕ}

/-- The "correction" `W x = (φ x).b + x.b` measuring the failure of `φ` to preserve the
second coordinate.  In characteristic two it is additive whenever `φ` is a homomorphism
preserving the first coordinate. -/
def VtrivW (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (φ : MulAut (SzA (GaloisField 2 n) θ)) (x : SzA (GaloisField 2 n) θ) : GaloisField 2 n :=
  (φ x).b + x.b

/-- `W` restricted to the first coordinate axis. -/
def VtrivP (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (φ : MulAut (SzA (GaloisField 2 n) θ)) (a : GaloisField 2 n) : GaloisField 2 n :=
  VtrivW θ φ ⟨a, 0⟩

/-- `W` restricted to the centre (the second coordinate axis). -/
def VtrivQ (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (φ : MulAut (SzA (GaloisField 2 n) θ)) (b : GaloisField 2 n) : GaloisField 2 n :=
  VtrivW θ φ ⟨0, b⟩

/-- An automorphism of `A(K,θ)` trivial on `A/Z(A)` preserves the first coordinate. -/
theorem Vtriv_coord_a (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (x : SzA (GaloisField 2 n) θ) :
    (φ x).a = x.a := by
  have h := (SzA.mem_center_iff θ hθ (φ x * x⁻¹)).mp (hφ x)
  simp only [SzA.mul_a, SzA.inv_a] at h
  simpa using eq_neg_of_add_eq_zero_left h

/-- The correction `W` is additive on `A(K,θ)`. -/
theorem VtrivW_mul (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (x y : SzA (GaloisField 2 n) θ) :
    VtrivW θ φ (x * y) = VtrivW θ φ x + VtrivW θ φ y := by
  have hx := Vtriv_coord_a θ hθ hφ x
  have hy := Vtriv_coord_a θ hθ hφ y
  have h := congrArg SzA.b (map_mul φ x y)
  rw [SzA.mul_b] at h
  rw [hx, hy] at h
  simp only [VtrivW]
  rw [h, SzA.mul_b]
  linear_combination CharTwo.add_self_eq_zero (x.a * θ y.a)

/-- `φ x` in coordinates, with the correction `W`. -/
theorem Vtriv_coord (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (x : SzA (GaloisField 2 n) θ) :
    φ x = ⟨x.a, x.b + VtrivW θ φ x⟩ := by
  have hx := Vtriv_coord_a θ hθ hφ x
  ext
  · exact hx
  · simp only [VtrivW]
    rw [← add_assoc, add_comm x.b ((φ x).b), add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- `W ⟨u,v⟩ = P u + Q v`. -/
theorem VtrivW_mk (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (u v : GaloisField 2 n) :
    VtrivW θ φ ⟨u, v⟩ = VtrivP θ φ u + VtrivQ θ φ v := by
  have h := VtrivW_mul θ hθ hφ (⟨u, 0⟩ : SzA (GaloisField 2 n) θ) (⟨0, v⟩ : SzA (GaloisField 2 n) θ)
  rw [show (⟨u, 0⟩ : SzA (GaloisField 2 n) θ) * ⟨0, v⟩ = ⟨u, v⟩ from by ext <;> simp] at h
  simpa only [VtrivP, VtrivQ] using h

/-- **The cocycle identity** `P (a+c) + Q (a·θc) = P a + P c`. -/
theorem VtrivP_add_cocycle (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (a c : GaloisField 2 n) :
    VtrivP θ φ (a + c) + VtrivQ θ φ (a * θ c) = VtrivP θ φ a + VtrivP θ φ c := by
  have h := VtrivW_mul θ hθ hφ (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) (⟨c, 0⟩ : SzA (GaloisField 2 n) θ)
  rw [show (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) * ⟨c, 0⟩ = ⟨a + c, a * θ c⟩ from by
        ext <;> simp] at h
  rw [VtrivW_mk θ hθ hφ] at h
  simpa only [VtrivP, VtrivQ] using h

/-- Symmetry of the cocycle in its two arguments, read on `Q`. -/
theorem VtrivQ_symm (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (a c : GaloisField 2 n) :
    VtrivQ θ φ (a * θ c) = VtrivQ θ φ (c * θ a) := by
  have h1 := VtrivP_add_cocycle θ hθ hφ a c
  have h2 := VtrivP_add_cocycle θ hθ hφ c a
  rw [add_comm c a] at h2
  rw [add_comm (VtrivP θ φ a)] at h1
  exact add_left_cancel (h1.trans h2.symm)

/-- `Q` is invariant under `θ`. -/
theorem VtrivQ_theta (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (a : GaloisField 2 n) :
    VtrivQ θ φ (θ a) = VtrivQ θ φ a := by
  have h := VtrivQ_symm θ hθ hφ a 1
  simpa using h.symm

/-- Additivity of `Q` (the restriction of `W` to the centre). -/
theorem VtrivQ_add (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (b d : GaloisField 2 n) :
    VtrivQ θ φ (b + d) = VtrivQ θ φ b + VtrivQ θ φ d := by
  have h := VtrivW_mul θ hθ hφ (⟨0, b⟩ : SzA (GaloisField 2 n) θ) (⟨0, d⟩ : SzA (GaloisField 2 n) θ)
  rw [show (⟨0, b⟩ : SzA (GaloisField 2 n) θ) * ⟨0, d⟩ = ⟨0, b + d⟩ from by ext <;> simp] at h
  simpa only [VtrivQ] using h

/-- `Q` is invariant under `θ²` in the sense `Q (θ²a · c) = Q (a · c)`. -/
theorem VtrivQ_theta2 (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) (a c : GaloisField 2 n) :
    VtrivQ θ φ (θ (θ a) * c) = VtrivQ θ φ (a * c) := by
  have h := VtrivQ_symm θ hθ hφ (θ a) c
  rw [← map_mul] at h
  rw [VtrivQ_theta θ hθ hφ (a * c)] at h
  rw [mul_comm c (θ (θ a))] at h
  exact h.symm

/-- `θ² ≠ 1` when `θ ≠ 1` has odd order. -/
theorem sq_ne_one_of_odd_order (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) : θ * θ ≠ 1 := by
  intro h
  have hdvd : orderOf θ ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rwa [pow_two]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hθ (orderOf_eq_one_iff.mp h1)
  · rw [h2] at hodd
    exact Nat.not_odd_iff_even.mpr (by decide) hodd

/-- **`Q ≡ 0`.**  The oddness of `orderOf θ` is used here: it supplies `a` with `θ²a ≠ a`. -/
theorem VtrivQ_eq_zero (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ))
    {φ : MulAut (SzA (GaloisField 2 n) θ)} (hφ : φ ∈ Vtriv θ) :
    ∀ b, VtrivQ θ φ b = 0 := by
  have hθ2 := sq_ne_one_of_odd_order θ hθ hodd
  obtain ⟨a0, ha0⟩ : ∃ a, θ (θ a) ≠ a := by
    by_contra h
    push Not at h
    exact hθ2 (by ext x; simpa using h x)
  have hw : θ (θ a0) + a0 ≠ 0 := by
    intro h
    apply ha0
    have h' : θ (θ a0) = -a0 := add_eq_zero_iff_eq_neg.mp h
    rwa [CharTwo.neg_eq] at h'
  intro b
  set c : GaloisField 2 n := b / (θ (θ a0) + a0) with hc
  have hbc : (θ (θ a0) + a0) * c = b := by
    rw [hc, mul_div_cancel₀ b hw]
  rw [← hbc, add_mul, VtrivQ_add θ hθ hφ, VtrivQ_theta2 θ hθ hφ a0 c]
  exact CharTwo.add_self_eq_zero _

theorem Vtriv_fixes_center {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) :
    ∀ φ ∈ Vtriv θ, ∀ z ∈ Subgroup.center (SzA (GaloisField 2 n) θ), φ z = z := by
  intro φ hφ z hz
  have hz0 : z.a = 0 := (SzA.mem_center_iff θ hθ z).mp hz
  have hzeq : z = ⟨0, z.b⟩ := by ext <;> simp [hz0]
  have hWz : VtrivW θ φ z = 0 := by
    rw [hzeq]
    show VtrivQ θ φ z.b = 0
    exact VtrivQ_eq_zero θ hθ hodd hφ z.b
  rw [Vtriv_coord θ hθ hφ z, hz0, hWz, add_zero, hzeq]

end Work.ZassenhausSuzuki.SzAuto
