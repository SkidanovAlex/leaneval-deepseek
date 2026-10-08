import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.szAut_semilinear_ph_zs
import Submission.Work.ZassenhausSuzuki.not_iterate_eq_of_ringAut_ne_ph_zs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Aut(A(K,θ))`-elements of order `q-1` are torus automorphisms modulo the centre

This file proves `Work.ZassenhausSuzuki.SzAuto.aut_V_action_scalar`: if `z` is an automorphism of
Higman's group `A(K,θ)` (`K = GF(2ⁿ)`, `θ` a non-trivial automorphism of odd order) whose order is
`2ⁿ - 1 = |Kˣ|`, then `z` agrees with a Suzuki torus automorphism `h_λ` up to the centre
`Z(A) = {(0,b)}`.

The proof proceeds in three steps.

* *Reduction to linear algebra.*  An automorphism `z` of `A = A(K,θ)` preserves the centre
  `Z = {(0,b)}` (characteristic) and the quotient `A/Z ≅ (K,+)`.  Writing
  `φ a = (z ⟨a,0⟩).a` and `ψ b = (z ⟨0,b⟩).b` we obtain two additive bijections of `K` linked by
  the identity `ψ (a * θ a) = φ a * θ (φ a)` (the image of `z(x²) = z(x)²`).  Moreover
  `orderOf φ = orderOf z = 2ⁿ - 1`.

* *Field-theoretic core* (`szAut_semilinear`, `szAut_scalar`).  If `φ, ψ` are additive bijections
  of `K` with `ψ (a * θ a) = φ a * θ (φ a)` for all `a`, then `φ = λ · σ` for some `λ ∈ Kˣ` and
  `σ ∈ Aut(K)`; if in addition `orderOf φ = 2ⁿ - 1` then `σ = 1`, i.e. `φ` is the scalar
  multiplication by `λ`.  (This is the classical statement that the induced transformation of a
  cyclic Hua subgroup of order `q-1` on `A/Z` is scalar; Higman 1963, Theorem 2.)

* *Assembly.*  From `φ a = λ a` we get `z x * (h_λ x)⁻¹ ∈ Z` for every `x`, which is the goal.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Work.ZassenhausSuzuki

namespace Work.ZassenhausSuzuki.SzAuto

section Structural

variable {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n)

/-- The centre of `A(K,θ)` is exactly the set of elements with vanishing first coordinate. -/
theorem center_eq (hθ : θ ≠ 1) :
    (Subgroup.center (SzA (GaloisField 2 n) θ) : Set (SzA (GaloisField 2 n) θ))
      = {x | x.a = 0} := by
  ext x
  exact Work.ZassenhausSuzuki.SzA.mem_center_iff θ hθ x

/-- Membership in the centre in coordinates. -/
theorem mem_center_iff' (hθ : θ ≠ 1) (x : SzA (GaloisField 2 n) θ) :
    x ∈ Subgroup.center (SzA (GaloisField 2 n) θ) ↔ x.a = 0 :=
  Work.ZassenhausSuzuki.SzA.mem_center_iff θ hθ x

/-- The first coordinate of `z ⟨a,0⟩`: the induced map of `z` on `A/Z ≅ K`. -/
noncomputable def linMap (z : MulAut (SzA (GaloisField 2 n) θ)) :
    GaloisField 2 n → GaloisField 2 n :=
  fun a => (z ⟨a, 0⟩).a

/-- The second coordinate of `z ⟨a,0⟩`. -/
noncomputable def bMap (z : MulAut (SzA (GaloisField 2 n) θ)) :
    GaloisField 2 n → GaloisField 2 n :=
  fun a => (z ⟨a, 0⟩).b

/-- The action of `z` on the centre `Z = {(0,b)}`, as a map of `K`. -/
noncomputable def cenMap (z : MulAut (SzA (GaloisField 2 n) θ)) :
    GaloisField 2 n → GaloisField 2 n :=
  fun b => (z ⟨0, b⟩).b

variable {θ}

@[simp] theorem linMap_apply (z : MulAut (SzA (GaloisField 2 n) θ)) (a : GaloisField 2 n) :
    linMap θ z a = (z ⟨a, 0⟩).a := rfl

@[simp] theorem bMap_apply (z : MulAut (SzA (GaloisField 2 n) θ)) (a : GaloisField 2 n) :
    bMap θ z a = (z ⟨a, 0⟩).b := rfl

@[simp] theorem cenMap_apply (z : MulAut (SzA (GaloisField 2 n) θ)) (b : GaloisField 2 n) :
    cenMap θ z b = (z ⟨0, b⟩).b := rfl

/-- `z` maps the centre into itself. -/
theorem z_mem_center (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    {y : SzA (GaloisField 2 n) θ} (hy : y ∈ Subgroup.center (SzA (GaloisField 2 n) θ)) :
    z y ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
  have hmap : (Subgroup.center (SzA (GaloisField 2 n) θ)).map
      (z : SzA (GaloisField 2 n) θ →* SzA (GaloisField 2 n) θ)
      = Subgroup.center (SzA (GaloisField 2 n) θ) := Subgroup.map_center_eq z
  rw [← hmap]
  exact ⟨y, hy, rfl⟩

/-- The first coordinate of `z ⟨0,b⟩` vanishes. -/
theorem z_zero_b_a (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (b : GaloisField 2 n) : (z ⟨0, b⟩).a = 0 := by
  have h : (⟨0, b⟩ : SzA (GaloisField 2 n) θ) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
    (mem_center_iff' (θ := θ) hθ _).mpr rfl
  have h2 := z_mem_center (θ := θ) hθ z h
  rwa [mem_center_iff' (θ := θ) hθ] at h2

/-- `z` acts on the centre by `(0,b) ↦ (0, cenMap z b)`. -/
theorem z_zero_b (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (b : GaloisField 2 n) : z ⟨0, b⟩ = ⟨0, cenMap θ z b⟩ := by
  ext
  · exact z_zero_b_a (θ := θ) hθ z b
  · rfl

/-- Normal form of `z` on a general element. -/
theorem z_apply (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (a b : GaloisField 2 n) :
    z ⟨a, b⟩ = ⟨linMap θ z a, bMap θ z a + cenMap θ z b⟩ := by
  have hdec : (⟨a, b⟩ : SzA (GaloisField 2 n) θ) = ⟨a, 0⟩ * ⟨0, b⟩ := by
    ext <;> simp
  rw [hdec, map_mul, z_zero_b (θ := θ) hθ z b]
  ext <;> simp

end Structural
section AdditiveFacts

variable {n : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}

/-- `z` preserves the centre, so `a ↦ (z ⟨a,0⟩).a` vanishes only on `0`. -/
theorem linMap_eq_zero (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    {a : GaloisField 2 n} (ha : linMap θ z a = 0) : a = 0 := by
  have hcent : z ⟨a, 0⟩ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
    (mem_center_iff' (θ := θ) hθ _).mpr (by simpa using ha)
  have hmap : (Subgroup.center (SzA (GaloisField 2 n) θ)).map
      ((z⁻¹ : MulAut (SzA (GaloisField 2 n) θ)) : SzA (GaloisField 2 n) θ →*
        SzA (GaloisField 2 n) θ) = Subgroup.center (SzA (GaloisField 2 n) θ) :=
    Subgroup.map_center_eq (z⁻¹ : MulAut (SzA (GaloisField 2 n) θ))
  have hcent' : z⁻¹ (z ⟨a, 0⟩) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
    rw [← hmap]
    exact ⟨z ⟨a, 0⟩, hcent, rfl⟩
  have hx : z⁻¹ (z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ)) = ⟨a, 0⟩ := by simp
  rw [hx] at hcent'
  have h0 : (⟨a, 0⟩ : SzA (GaloisField 2 n) θ).a = 0 := (mem_center_iff' (θ := θ) hθ _).mp hcent'
  simpa using h0

/-- The induced map on `A/Z` is additive. -/
theorem linMap_add (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (a a' : GaloisField 2 n) : linMap θ z (a + a') = linMap θ z a + linMap θ z a' := by
  have h1 : (⟨a, 0⟩ * ⟨a', 0⟩ : SzA (GaloisField 2 n) θ) = ⟨a + a', a * θ a'⟩ := by
    ext <;> simp
  have h := map_mul z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) (⟨a', 0⟩ : SzA (GaloisField 2 n) θ)
  rw [h1] at h
  have h2 : (z (⟨a + a', a * θ a'⟩ : SzA (GaloisField 2 n) θ)).a
      = linMap θ z (a + a') := by
    rw [z_apply (θ := θ) hθ z (a + a') (a * θ a')]
  have h3 : (z ⟨a, 0⟩ * z ⟨a', 0⟩ : SzA (GaloisField 2 n) θ).a
      = linMap θ z a + linMap θ z a' := rfl
  have h4 := congrArg (fun x : SzA (GaloisField 2 n) θ => x.a) h
  rw [h2, h3] at h4
  exact h4

/-- The induced map on the centre is additive. -/
theorem cenMap_add (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (b b' : GaloisField 2 n) : cenMap θ z (b + b') = cenMap θ z b + cenMap θ z b' := by
  have h1 : (⟨0, b⟩ * ⟨0, b'⟩ : SzA (GaloisField 2 n) θ) = ⟨0, b + b'⟩ := by
    ext <;> simp
  have h := map_mul z (⟨0, b⟩ : SzA (GaloisField 2 n) θ) (⟨0, b'⟩ : SzA (GaloisField 2 n) θ)
  rw [h1, z_zero_b (θ := θ) hθ z b, z_zero_b (θ := θ) hθ z b'] at h
  have h2 := congrArg (fun x : SzA (GaloisField 2 n) θ => x.b) h
  simpa using h2

/-- Injectivity of the induced map on the centre. -/
theorem cenMap_injective (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ)) :
    Function.Injective (cenMap θ z) := by
  intro b b' h
  have hz : z ⟨0, b⟩ = z ⟨0, b'⟩ := by
    rw [z_zero_b (θ := θ) hθ z b, z_zero_b (θ := θ) hθ z b', h]
  exact congrArg (fun x : SzA (GaloisField 2 n) θ => x.b) (z.injective hz)

/-- The key relation: `ψ (a θ a) = φ a · θ (φ a)` (image of `z (x²) = z x ²`). -/
theorem cenMap_mul_theta (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ))
    (a : GaloisField 2 n) :
    cenMap θ z (a * θ a) = linMap θ z a * θ (linMap θ z a) := by
  have h1 : (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) * ⟨a, 0⟩ = ⟨0, a * θ a⟩ := SzA.sq_eq θ _
  have h2 : z ((⟨a, 0⟩ : SzA (GaloisField 2 n) θ) * ⟨a, 0⟩) = ⟨0, cenMap θ z (a * θ a)⟩ := by
    rw [h1]
    exact z_zero_b (θ := θ) hθ z _
  have h3 : z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) * z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ)
      = ⟨0, linMap θ z a * θ (linMap θ z a)⟩ := by
    have hzz : (⟨linMap θ z a, bMap θ z a⟩ : SzA (GaloisField 2 n) θ)
        * ⟨linMap θ z a, bMap θ z a⟩ = ⟨0, linMap θ z a * θ (linMap θ z a)⟩ :=
      SzA.sq_eq θ _
    have heta : z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) = ⟨linMap θ z a, bMap θ z a⟩ := rfl
    rw [heta]
    exact hzz
  have h4 := map_mul z (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) (⟨a, 0⟩ : SzA (GaloisField 2 n) θ)
  rw [h2, h3] at h4
  exact congrArg (fun x : SzA (GaloisField 2 n) θ => x.b) h4

end AdditiveFacts
section OrderFacts

variable {n : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}

/-- Composition of ring automorphisms. -/
theorem ringEquiv_mul_apply (f g : GaloisField 2 n ≃+* GaloisField 2 n) (w : GaloisField 2 n) :
    (f * g) w = f (g w) := rfl

/-- `x ↦ x * θ x` is injective when `θ` has odd order. -/
theorem mul_theta_injective (hθ : θ ≠ 1) (hodd : Odd (orderOf θ)) :
    Function.Injective (fun x : GaloisField 2 n => x * θ x) := by
  have hθinj : Function.Injective (θ : GaloisField 2 n → GaloisField 2 n) := θ.injective
  intro x y hxy
  change x * θ x = y * θ y at hxy
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [zero_mul] at hxy
    rcases mul_eq_zero.mp hxy with h | h
    · exact h
    · exact (map_eq_zero_iff θ hθinj).mp h
  · have hx : x ≠ 0 := by
      intro hx0
      subst hx0
      simp only [zero_mul] at hxy
      rcases mul_eq_zero.mp hxy.symm with h | h
      · exact hy h
      · exact hy ((map_eq_zero_iff θ hθinj).mp h)
    have hθy : θ y ≠ 0 := fun h => hy ((map_eq_zero_iff θ hθinj).mp h)
    set z := x / y with hzdef
    have hz0 : z ≠ 0 := by rw [hzdef]; exact div_ne_zero hx hy
    have hzy : z * θ z = 1 := by
      have hzθ : z * θ z = (x * θ x) / (y * θ y) := by
        rw [hzdef, map_div₀, div_mul_div_comm]
      have key : z * θ z * (y * θ y) = y * θ y := by
        rw [hzθ, hxy, div_mul_cancel₀ _ (mul_ne_zero hy hθy)]
      exact mul_right_cancel₀ (mul_ne_zero hy hθy) (by simpa using key)
    have h1 : θ z = z⁻¹ := by
      have h := congrArg (fun t : GaloisField 2 n => z⁻¹ * t) hzy
      rw [mul_one] at h
      have h' : z⁻¹ * (z * θ z) = θ z := by
        rw [← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
      rwa [h'] at h
    have h2 : θ (θ z) = z := by rw [h1, map_inv₀, h1, inv_inv]
    obtain ⟨k, hk⟩ := hodd
    have hker : θ ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one θ
    have hgen : θ = (θ ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hker, one_mul]
    have h2z : (θ ^ 2) z = z := by
      rw [pow_two, ringEquiv_mul_apply]
      exact h2
    have hfix : ∀ j : ℕ, ((θ ^ 2) ^ j) z = z := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ', ringEquiv_mul_apply, ih, h2z]
    have h3 : θ z = z := by rw [hgen]; exact hfix (k + 1)
    have h4 : z = z⁻¹ := by rw [← h1, h3]
    have h5 : z = 1 := by
      have h6 : z * z = 1 := by
        nth_rewrite 1 [h4]
        exact inv_mul_cancel₀ hz0
      rcases mul_self_eq_one_iff.mp h6 with h | h
      · exact h
      · rw [h, CharTwo.neg_eq]
    have h7 : x = y := by
      rw [hzdef] at h5
      exact (div_eq_one_iff_eq hy).mp h5
    exact h7

/-- `x ↦ x * θ x` is bijective when `θ` has odd order. -/
theorem mul_theta_bijective (hθ : θ ≠ 1) (hodd : Odd (orderOf θ)) :
    Function.Bijective (fun x : GaloisField 2 n => x * θ x) :=
  ⟨mul_theta_injective hθ hodd,
    (Finite.injective_iff_surjective).mp (mul_theta_injective hθ hodd)⟩

/-- The induced map on `A/Z` of a product of automorphisms. -/
theorem linMap_comp (hθ : θ ≠ 1) (z₁ z₂ : MulAut (SzA (GaloisField 2 n) θ))
    (a : GaloisField 2 n) : linMap θ (z₁ * z₂) a = linMap θ z₁ (linMap θ z₂ a) := by
  have h1 : (z₁ * z₂) (⟨a, 0⟩ : SzA (GaloisField 2 n) θ) = z₁ (z₂ ⟨a, 0⟩) :=
    MulAut.mul_apply (SzA (GaloisField 2 n) θ) z₁ z₂ _
  have h2 : z₂ (⟨a, 0⟩ : SzA (GaloisField 2 n) θ)
      = (⟨linMap θ z₂ a, bMap θ z₂ a⟩ : SzA (GaloisField 2 n) θ) := rfl
  change ((z₁ * z₂) ⟨a, 0⟩).a = linMap θ z₁ (linMap θ z₂ a)
  rw [h1, h2, z_apply (θ := θ) hθ z₁ (linMap θ z₂ a) (bMap θ z₂ a)]

@[simp] theorem linMap_one (a : GaloisField 2 n) :
    linMap θ (1 : MulAut (SzA (GaloisField 2 n) θ)) a = a := rfl

@[simp] theorem cenMap_one (b : GaloisField 2 n) :
    cenMap θ (1 : MulAut (SzA (GaloisField 2 n) θ)) b = b := rfl

/-- Iterated form of `linMap_comp`. -/
theorem linMap_pow_apply (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ)) (m : ℕ)
    (a : GaloisField 2 n) : linMap θ (z ^ m) a = (linMap θ z)^[m] a := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', linMap_comp (θ := θ) hθ z (z ^ m) a, ih, Function.iterate_succ_apply']

/-- If the induced map on `A/Z` is the identity, then so is the induced map on the centre. -/
theorem cenMap_eq_id_of_linMap_eq_id (hθ : θ ≠ 1) (hodd : Odd (orderOf θ))
    (z : MulAut (SzA (GaloisField 2 n) θ)) (h : ∀ a, linMap θ z a = a) :
    ∀ b, cenMap θ z b = b := by
  intro b
  obtain ⟨a, rfl⟩ := (mul_theta_bijective hθ hodd).2 b
  rw [cenMap_mul_theta (θ := θ) hθ z a, h a]

/-- If `φ^m = id` then `z^m = 1`. -/
theorem z_pow_eq_one (hθ : θ ≠ 1) (hoddθ : Odd (orderOf θ))
    (z : MulAut (SzA (GaloisField 2 n) θ)) (hoddz : Odd (orderOf z)) (m : ℕ)
    (h : ∀ a, (linMap θ z)^[m] a = a) : z ^ m = 1 := by
  have hlin : ∀ a, linMap θ (z ^ m) a = a := by
    intro a
    rw [linMap_pow_apply (θ := θ) hθ z m a, h a]
  have hcen : ∀ b, cenMap θ (z ^ m) b = b := cenMap_eq_id_of_linMap_eq_id hθ hoddθ (z ^ m) hlin
  have hform : ∀ a b, (z ^ m) (⟨a, b⟩ : SzA (GaloisField 2 n) θ)
      = ⟨a, bMap θ (z ^ m) a + b⟩ := by
    intro a b
    rw [z_apply (θ := θ) hθ (z ^ m) a b, hlin a, hcen b]
  have hsq : (z ^ m) ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, b⟩ := x
    have h1x : (1 : MulAut (SzA (GaloisField 2 n) θ)) (⟨a, b⟩ : SzA (GaloisField 2 n) θ)
        = ⟨a, b⟩ := rfl
    rw [pow_two, MulAut.mul_apply (SzA (GaloisField 2 n) θ), hform a b,
      hform a (bMap θ (z ^ m) a + b), h1x, SzA.ext_iff]
    exact ⟨rfl, by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]⟩
  have hdvd : orderOf (z ^ m) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hdvd2 : orderOf (z ^ m) ∣ orderOf z := orderOf_pow_dvd m
  have hcop : Nat.Coprime 2 (orderOf z) := Nat.coprime_two_left.mpr hoddz
  have hone : orderOf (z ^ m) ∣ 1 := by
    have h3 := Nat.dvd_gcd hdvd hdvd2
    rwa [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)

/-- `2 ^ n - 1` is odd for `n ≥ 1`. -/
theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  refine ⟨2 ^ (n - 1) - 1, ?_⟩
  have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
    ring
  have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  omega

end OrderFacts
section Main

variable {n : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}

/-- The induced map `φ` on `A/Z` has order `2ⁿ - 1` when `z` does. -/
theorem linMap_order (hθ : θ ≠ 1) (hodd : Odd (orderOf θ))
    (z : MulAut (SzA (GaloisField 2 n) θ)) (hz : orderOf z = 2 ^ n - 1) :
    (∀ a, (linMap θ z)^[2 ^ n - 1] a = a) ∧
      (∀ m : ℕ, 0 < m → (∀ a, (linMap θ z)^[m] a = a) → 2 ^ n - 1 ∣ m) := by
  have hpos : 0 < orderOf z := by
    rw [orderOf_pos_iff]; exact isOfFinOrder_of_finite z
  rw [hz] at hpos
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hpos
    · exact h
  constructor
  · intro a
    rw [← linMap_pow_apply (θ := θ) hθ z (2 ^ n - 1) a]
    have hzp : z ^ (2 ^ n - 1) = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    rw [hzp, linMap_one]
  · intro m hm0 hm
    have hzm : z ^ m = 1 :=
      z_pow_eq_one hθ hodd z (by rw [hz]; exact odd_two_pow_sub_one hn) m hm
    rw [← hz]
    exact orderOf_dvd_iff_pow_eq_one.mpr hzm

/-- The induced map `φ` on `A/Z` is injective. -/
theorem linMap_injective (hθ : θ ≠ 1) (z : MulAut (SzA (GaloisField 2 n) θ)) :
    Function.Injective (linMap θ z) := by
  intro a a' haa
  have h0 : linMap θ z (a + a') = 0 := by
    rw [linMap_add (θ := θ) hθ z a a', haa, CharTwo.add_self_eq_zero]
  have h1 : a + a' = 0 := linMap_eq_zero (θ := θ) hθ z h0
  have h2 : a = -a' := eq_neg_of_add_eq_zero_left h1
  rwa [CharTwo.neg_eq] at h2

end Main

section Final

/-- Placeholder for the delegated semilinear classification. -/
theorem szAut_semilinear_ph {n : ℕ} (hn : 1 ≤ n) (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (hθ : θ ≠ 1) (hodd : Odd (orderOf θ)) (φ ψ : GaloisField 2 n → GaloisField 2 n)
    (hφadd : ∀ x y, φ (x + y) = φ x + φ y) (hφinj : Function.Injective φ)
    (hψadd : ∀ x y, ψ (x + y) = ψ x + ψ y) (hψinj : Function.Injective ψ)
    (hS : ∀ x, ψ (x * θ x) = φ x * θ (φ x)) :
    ∃ lam : (GaloisField 2 n)ˣ, ∃ σ : GaloisField 2 n ≃+* GaloisField 2 n,
      ∀ x, φ x = (lam : GaloisField 2 n) * σ x := szAut_semilinear_ph_zs hn θ hθ hodd φ ψ hφadd hφinj hψadd hψinj hS

/-- Placeholder for the delegated order computation for `x ↦ λ σ x`, `σ ≠ 1`. -/
theorem not_iterate_eq_of_ringAut_ne_ph {n : ℕ} (hn : 1 ≤ n) (lam : (GaloisField 2 n)ˣ)
    (σ : GaloisField 2 n ≃+* GaloisField 2 n) (hσ : σ ≠ 1) :
    ¬ (∀ x : GaloisField 2 n, ((fun y => (lam : GaloisField 2 n) * σ y)^[2 ^ n - 1]) x = x ∧
       ∀ m : ℕ, 0 < m → m < 2 ^ n - 1 →
         ∃ x : GaloisField 2 n, ((fun y => (lam : GaloisField 2 n) * σ y)^[m]) x ≠ x) := not_iterate_eq_of_ringAut_ne_ph_zs hn lam σ hσ

/-- The semilinear classification plus the order condition yields scalarity. -/
theorem core_scalar {n : ℕ} (hn : 1 ≤ n) (θ : GaloisField 2 n ≃+* GaloisField 2 n)
    (hθ : θ ≠ 1) (hodd : Odd (orderOf θ)) (φ ψ : GaloisField 2 n → GaloisField 2 n)
    (hφadd : ∀ x y, φ (x + y) = φ x + φ y) (hφinj : Function.Injective φ)
    (hψadd : ∀ x y, ψ (x + y) = ψ x + ψ y) (hψinj : Function.Injective ψ)
    (hS : ∀ x, ψ (x * θ x) = φ x * θ (φ x))
    (hpow : ∀ x, (φ^[2 ^ n - 1]) x = x)
    (hmin : ∀ m : ℕ, 0 < m → m < 2 ^ n - 1 → ∃ x, (φ^[m]) x ≠ x) :
    ∃ lam : (GaloisField 2 n)ˣ, ∀ x, φ x = (lam : GaloisField 2 n) * x := by
  obtain ⟨lam, σ, hσ⟩ := szAut_semilinear_ph hn θ hθ hodd φ ψ hφadd hφinj hψadd hψinj hS
  by_cases h1 : σ = 1
  · refine ⟨lam, ?_⟩
    intro x
    rw [hσ x, h1]
    rfl
  · exfalso
    have hnot := not_iterate_eq_of_ringAut_ne_ph hn lam σ h1
    apply hnot
    have hconv : ∀ m x, ((fun y => (lam : GaloisField 2 n) * σ y)^[m]) x = (φ^[m]) x := by
      intro m
      induction m with
      | zero => intro x; rfl
      | succ m ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        exact (hσ ((φ^[m]) x)).symm
    intro x
    refine ⟨?_, ?_⟩
    · rw [hconv (2 ^ n - 1) x]; exact hpow x
    · intro m hm hlt
      obtain ⟨y, hy⟩ := hmin m hm hlt
      exact ⟨y, fun h => hy (by rw [← hconv m y]; exact h)⟩

/-- **Automorphisms of `A(K,θ)` of order `|Kˣ|` are torus automorphisms modulo the centre.**

An automorphism `z` of Higman's group `A(K,θ)` (`K = GF(2ⁿ)`, `θ ≠ 1` of odd order) of order
`2ⁿ - 1` acts on the quotient `A/Z ≅ (K,+)` by a scalar, i.e. differs from some Suzuki torus
automorphism `h_λ` by a central automorphism. -/
theorem aut_V_action_scalar {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) (z : MulAut (SzA (GaloisField 2 n) θ))
    (hz : orderOf z = 2 ^ n - 1) :
    ∃ lam : (GaloisField 2 n)ˣ, ∀ x : SzA (GaloisField 2 n) θ,
      (z x) * (SzA.hLam θ (lam : GaloisField 2 n) x)⁻¹
        ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
  have hpos : 0 < orderOf z := by
    rw [orderOf_pos_iff]; exact isOfFinOrder_of_finite z
  rw [hz] at hpos
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hpos
    · exact h
  obtain ⟨hpow, hmin_div⟩ := linMap_order (θ := θ) hθ hodd z hz
  have hmin : ∀ m : ℕ, 0 < m → m < 2 ^ n - 1 → ∃ a, (linMap θ z)^[m] a ≠ a := by
    intro m hm0 hmlt
    by_contra hcon
    push_neg at hcon
    have hdiv := hmin_div m hm0 hcon
    have hle := Nat.le_of_dvd hm0 hdiv
    omega
  obtain ⟨lam, hlam⟩ := core_scalar hn θ hθ hodd (linMap θ z) (cenMap θ z)
    (linMap_add hθ z) (linMap_injective hθ z) (cenMap_add hθ z) (cenMap_injective hθ z)
    (cenMap_mul_theta hθ z) hpow hmin
  refine ⟨lam, ?_⟩
  rintro ⟨a, b⟩
  rw [mem_center_iff' (θ := θ) hθ, z_apply (θ := θ) hθ z a b, hlam a]
  simp only [SzA.mul_a, SzA.inv_a, SzA.hLam_a]
  ring

end Final






end Work.ZassenhausSuzuki.SzAuto
