import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base case `X = Fin 2` of the residual-generation statement

Let `A = 𝔽₂[X^*]` for `X = Fin 2`, with the two letters `a = 0`, `b = 1`, and let `σ` be the
(fixed-point-free, involutive) transposition of `Fin 2`.  `σA` is the induced `𝔽₂`-linear
involution of `A` (`σA (single x) = single (σ x)`, multiplicative).

We prove the lemma `base_fin_two`: for `v` in the `𝔽₂`-span `W` of the degree-`4` left-nested
commutators `⁅⁅⁅x₁,x₂⁆,x₃⁆,x₄⁆` with `σA v = v`, there is `w ∈ W` with
`v - (w + σA w)` lying in the span of the "self-paired" elements `u * σA u + σA u * u`, `u ∈ T`
(the degree-`2` part `span{x*x, x*y + y*x}` of the restricted free Lie algebra).

The proof is a small explicit linear-algebra computation: `W` has the three-element basis

* `B0 = ⁅⁅⁅a,b⁆,a⁆,a⁆`      (`= a²ba + ba³ + a³b + aba²`),
* `B1 = ⁅⁅⁅a,b⁆,a⁆,b⁆`      (`= a²b² + b²a²`  `= Θ(a²)`),
* `B2 = ⁅⁅⁅a,b⁆,b⁆,b⁆`      (`= ab³ + b²ab + bab² + b³a`),

`σA` interchanges `B0` and `B2` and fixes `B1`, and `B0 + B2 = σA B0 + B0 ≠ 0`.  A `σA`-fixed
`v ∈ W` is `a•B0 + b•B1 + c•B2` with `(a+c) • (B0+B2) = 0`, hence `c = a`; then
`w := a•B0` is in `W` and `v - (w + σA w) = b • B1 = b • Θ(a²)` lies in the required span.
-/

namespace Work.SSGRoute

set_option linter.unusedVariables false

section BaseFinTwo

local instance : DecidableEq (FreeMonoid (Fin 2)) := Equiv.decidableEq FreeMonoid.toList

/-- In a `ZMod 2`-algebra, `t + t = 0`. -/
theorem bft_add_self {A : Type*} [Ring A] [Algebra (ZMod 2) A] (t : A) : t + t = 0 := by
  have h : t + t = ((1 : ZMod 2) + 1) • t := by rw [add_smul, one_smul]
  rw [h, show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul]

/-- In a `ZMod 2`-algebra, `x + (x + x) = x`. -/
theorem bft_add3 {A : Type*} [Ring A] [Algebra (ZMod 2) A] (x : A) : x + (x + x) = x := by
  rw [← add_assoc, bft_add_self, zero_add]

/-- The two letters `0`, `1` of `Fin 2` inside `𝔽₂[Fin 2^*]`. -/
noncomputable def bftE (i : Fin 2) : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  MonoidAlgebra.single (FreeMonoid.of i) 1

/-- `⁅a,b⁆` for `a = 0`, `b = 1`. -/
noncomputable def bftA : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  brk (Fin 2) (bftE 0) (bftE 1)

/-- `⁅⁅⁅a,b⁆,a⁆,a⁆`. -/
noncomputable def bftB0 : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  brk4 (Fin 2) ((0 : Fin 2), 1, 0, 0)

/-- `⁅⁅⁅a,b⁆,a⁆,b⁆`. -/
noncomputable def bftB1 : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  brk4 (Fin 2) ((0 : Fin 2), 1, 0, 1)

/-- `⁅⁅⁅a,b⁆,b⁆,b⁆`. -/
noncomputable def bftB2 : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) :=
  brk4 (Fin 2) ((0 : Fin 2), 1, 1, 1)

theorem bft_brk_comm (a b : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) :
    brk (Fin 2) a b = brk (Fin 2) b a := by
  simp only [brk]; abel

theorem bft_brk_sq_left (a b : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) :
    brk (Fin 2) (a * a) b = brk (Fin 2) (brk (Fin 2) a b) a := by
  simp only [brk]; noncomm_ring
  simp only [two_smul, bft_add_self, add_zero]

theorem bft_brk_brk (a b c : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) :
    brk (Fin 2) a (brk (Fin 2) b c)
      = brk (Fin 2) (brk (Fin 2) a b) c + brk (Fin 2) (brk (Fin 2) a c) b := by
  simp only [brk]; noncomm_ring
  simp only [two_smul, bft_add_self, add_zero]

theorem bft_brk_self (x : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) :
    brk (Fin 2) x x = 0 := by
  simp only [brk]; rw [bft_add_self]

/-- Swapping the first two letters of a `brk4`-tuple does not change the bracket. -/
theorem bft_brk4_swap12 (a b c d : Fin 2) :
    brk4 (Fin 2) (a, b, c, d) = brk4 (Fin 2) (b, a, c, d) := by
  show brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE a) (bftE b)) (bftE c)) (bftE d)
      = brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE b) (bftE a)) (bftE c)) (bftE d)
  rw [bft_brk_comm (bftE a) (bftE b)]

/-- `⁅x,y⁆` for distinct letters is the generator `⁅a,b⁆`. -/
theorem bft_brk_ne (a b : Fin 2) (hab : a ≠ b) :
    brk (Fin 2) (bftE a) (bftE b) = bftA := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · rfl
  · rw [bft_brk_comm]; rfl
  · exact absurd rfl hab

/-- Jacobi: `⁅⁅⁅a,b⁆,b⁆,a⁆ = ⁅⁅⁅a,b⁆,a⁆,b⁆`. -/
theorem bft_jacobi_swap :
    brk (Fin 2) (brk (Fin 2) bftA (bftE 1)) (bftE 0)
      = brk (Fin 2) (brk (Fin 2) bftA (bftE 0)) (bftE 1) := by
  have h := bft_brk_brk bftA (bftE 0) (bftE 1)
  have hA : brk (Fin 2) (bftE 0) (bftE 1) = bftA := rfl
  rw [hA] at h
  have h0 : brk (Fin 2) bftA bftA = 0 := bft_brk_self bftA
  rw [h0] at h
  -- `h : 0 = P + Q`
  set P := brk (Fin 2) (brk (Fin 2) bftA (bftE 0)) (bftE 1) with hP
  set Q := brk (Fin 2) (brk (Fin 2) bftA (bftE 1)) (bftE 0) with hQ
  have hsum : P + Q = 0 := h.symm
  have hQP : Q = P := by
    calc Q = Q + 0 := (add_zero Q).symm
      _ = Q + (P + Q) := by rw [← hsum]
      _ = P + (Q + Q) := by abel
      _ = P + 0 := by rw [bft_add_self Q]
      _ = P := add_zero P
  exact hQP

/-- The four `brk4`-reduced elements `⁅⁅⁅a,b⁆,u⁆,w⁆` for `u, w : Fin 2` all lie in
`span{B0, B1, B2}`. -/
theorem bft_A_mem (u w : Fin 2) :
    brk (Fin 2) (brk (Fin 2) bftA (bftE u)) (bftE w)
      ∈ Submodule.span (ZMod 2)
          ({bftB0, bftB1, bftB2} : Set (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))) := by
  have hS : ∀ x ∈ ({bftB0, bftB1, bftB2} : Set (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))),
      x ∈ Submodule.span (ZMod 2)
        ({bftB0, bftB1, bftB2} : Set (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))) :=
    fun x hx => Submodule.subset_span hx
  fin_cases u <;> fin_cases w
  · exact hS bftB0 (by simp)
  · exact hS bftB1 (by simp)
  · exact bft_jacobi_swap.symm ▸ hS bftB1 (by simp)
  · exact hS bftB2 (by simp)

/-- Every generator `⁅⁅⁅x₁,x₂⁆,x₃⁆,x₄⁆` of `Wsub (Fin 2)` lies in `span{B0, B1, B2}`. -/
theorem bft_brk4_mem (t : Fin 2 × Fin 2 × Fin 2 × Fin 2) :
    brk4 (Fin 2) t
      ∈ Submodule.span (ZMod 2)
          ({bftB0, bftB1, bftB2} : Set (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))) := by
  obtain ⟨t1, t2, t3, t4⟩ := t
  by_cases h12 : t1 = t2
  · have h0 : brk4 (Fin 2) (t1, t2, t3, t4) = 0 := by
      show brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE t1) (bftE t2)) (bftE t3)) (bftE t4) = 0
      rw [h12, bft_brk_self (bftE t2)]
      simp only [brk, mul_zero, zero_mul, add_zero]
    rw [h0]
    exact Submodule.zero_mem _
  · rw [show brk4 (Fin 2) (t1, t2, t3, t4)
          = brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE t1) (bftE t2)) (bftE t3)) (bftE t4)
        from rfl,
        bft_brk_ne t1 t2 h12]
    exact bft_A_mem t3 t4

/-- The monomial expansion of `B0 = ⁅⁅⁅a,b⁆,a⁆,a⁆`. -/
theorem bftB0_eq :
    bftB0 = MonoidAlgebra.single
        (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 0)
        (1 : ZMod 2)
      + MonoidAlgebra.single
        (FreeMonoid.of (1 : Fin 2) * FreeMonoid.of 0 * FreeMonoid.of 0 * FreeMonoid.of 0) 1
      + MonoidAlgebra.single
        (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 0 * FreeMonoid.of 0 * FreeMonoid.of 1) 1
      + MonoidAlgebra.single
        (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 0) 1 := by
  have h1 : bftB0
      = brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 0)) (bftE 0) := rfl
  rw [h1]
  rw [show brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 0)
        = brk (Fin 2) (bftE 0 * bftE 0) (bftE 1)
      from (bft_brk_sq_left (bftE 0) (bftE 1)).symm]
  simp only [brk, bftE, MonoidAlgebra.single_mul_single, mul_one, mul_assoc, add_mul, mul_add]
  abel

/-- The monomial expansion of `B2 = ⁅⁅⁅a,b⁆,b⁆,b⁆`. -/
theorem bftB2_eq :
    bftB2 = MonoidAlgebra.single
        (FreeMonoid.of (1 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 1)
        (1 : ZMod 2)
      + MonoidAlgebra.single
        (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 1 * FreeMonoid.of 1) 1
      + MonoidAlgebra.single
        (FreeMonoid.of (1 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 1 * FreeMonoid.of 0) 1
      + MonoidAlgebra.single
        (FreeMonoid.of (1 : Fin 2) * FreeMonoid.of 0 * FreeMonoid.of 1 * FreeMonoid.of 1) 1 := by
  have h1 : bftB2
      = brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 1)) (bftE 1) := rfl
  rw [h1]
  rw [show brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 1)
        = brk (Fin 2) (bftE 1 * bftE 1) (bftE 0)
      from by
        rw [bft_brk_comm (bftE 0) (bftE 1)]
        exact (bft_brk_sq_left (bftE 1) (bftE 0)).symm]
  simp only [brk, bftE, MonoidAlgebra.single_mul_single, mul_one, mul_assoc, add_mul, mul_add]
  abel

/-- `B0 + B2` has coefficient `1` at the word `a b a a`. -/
theorem bftD_coeff :
    (bftB0 + bftB2).coeff
        (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 0) = 1 := by
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, bftB0_eq, bftB2_eq]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  decide

/-- `B0 + B2 ≠ 0`. -/
theorem bftD_ne_zero : bftB0 + bftB2 ≠ 0 := by
  intro h
  have hc := bftD_coeff
  rw [h] at hc
  simp at hc

/-- `B1 = Θ(a²)`, where `Θ(u) = u * σA u + σA u * u`. -/
theorem bftB1_theta
    (σ : Fin 2 ≃ Fin 2)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1)
    (hσ0 : σ 0 = 1) :
    bftB1 = (bftE 0 * bftE 0) * σA (bftE 0 * bftE 0)
      + σA (bftE 0 * bftE 0) * (bftE 0 * bftE 0) := by
  have hσE : ∀ i : Fin 2, σA (bftE i) = bftE (σ i) := fun i => hgen i
  have hσsq : σA (bftE 0 * bftE 0) = bftE 1 * bftE 1 := by
    rw [hmul, hσE 0, hσ0]
  have h1 : bftB1 = brk (Fin 2) (bftE 1 * bftE 1) (bftE 0 * bftE 0) := by
    show brk (Fin 2) (brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 0)) (bftE 1)
        = brk (Fin 2) (bftE 1 * bftE 1) (bftE 0 * bftE 0)
    rw [show brk (Fin 2) (brk (Fin 2) (bftE 0) (bftE 1)) (bftE 0)
          = brk (Fin 2) (bftE 0 * bftE 0) (bftE 1)
        from (bft_brk_sq_left (bftE 0) (bftE 1)).symm]
    rw [bft_brk_comm (bftE 0 * bftE 0) (bftE 1)]
    exact (bft_brk_sq_left (bftE 1) (bftE 0 * bftE 0)).symm
  rw [h1, hσsq]
  simp only [brk]
  abel

/-- `a * a` lies in `Tsub (Fin 2)`. -/
theorem bftE_sq_mem_Tsub : bftE 0 * bftE 0 ∈ Tsub (Fin 2) := by
  have hg : (fun p : Fin 2 × Fin 2 =>
      MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
        * MonoidAlgebra.single (FreeMonoid.of p.1) 1
      + (MonoidAlgebra.single (FreeMonoid.of p.2) 1
          * MonoidAlgebra.single (FreeMonoid.of p.1) 1
        + MonoidAlgebra.single (FreeMonoid.of p.1) 1
          * MonoidAlgebra.single (FreeMonoid.of p.2) 1)) ((0 : Fin 2), 0)
      = bftE 0 * bftE 0 := by
    simp only [bftE, bft_add3]
  simp only [Tsub]
  rw [← hg]
  exact Submodule.subset_span ⟨((0 : Fin 2), 0), rfl⟩

theorem base_fin_two
    (σ : Fin 2 ≃ Fin 2) (hσ : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1) :
    ∀ v ∈ Wsub (Fin 2), σA v = v →
      ∃ w ∈ Wsub (Fin 2),
        v - (w + σA w) ∈ Submodule.span (ZMod 2) (Set.range fun u :
            {u : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) // u ∈ Tsub (Fin 2)} =>
          (u : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2))) * σA u
            + σA u * (u : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))) := by
  classical
  intro v hv hfix
  -- `σ 0 = 1` and `σ 1 = 0`.
  have hσ0 : σ 0 = 1 := by
    apply Fin.ext
    have h := hfree 0
    have hne : (σ 0).val ≠ 0 := fun hv => h (Fin.ext hv)
    have hlt : (σ 0).val < 2 := (σ 0).isLt
    omega
  have hσ1 : σ 1 = 0 := by
    apply Fin.ext
    have h := hfree 1
    have hne : (σ 1).val ≠ 1 := fun hv => h (Fin.ext hv)
    have hlt : (σ 1).val < 2 := (σ 1).isLt
    omega
  -- the action of `σA` on the basis
  have hsigB0 : σA bftB0 = bftB2 := by
    rw [show bftB0 = brk4 (Fin 2) ((0 : Fin 2), 1, 0, 0) from rfl,
      sigmaA_brk4 (Fin 2) σ σA hmul hone hgen ((0 : Fin 2), 1, 0, 0), hσ0, hσ1]
    exact bft_brk4_swap12 1 0 1 1
  have hsigB1 : σA bftB1 = bftB1 := by
    rw [show bftB1 = brk4 (Fin 2) ((0 : Fin 2), 1, 0, 1) from rfl,
      sigmaA_brk4 (Fin 2) σ σA hmul hone hgen ((0 : Fin 2), 1, 0, 1), hσ0, hσ1]
    rw [bft_brk4_swap12 (1 : Fin 2) 0 1 0]
    exact bft_jacobi_swap
  have hsigB2 : σA bftB2 = bftB0 := by
    rw [show bftB2 = brk4 (Fin 2) ((0 : Fin 2), 1, 1, 1) from rfl,
      sigmaA_brk4 (Fin 2) σ σA hmul hone hgen ((0 : Fin 2), 1, 1, 1), hσ0, hσ1]
    exact bft_brk4_swap12 1 0 0 0
  -- `v` lies in the span of the basis
  have hWle : Wsub (Fin 2)
      ≤ Submodule.span (ZMod 2)
          ({bftB0, bftB1, bftB2} : Set (MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)))) := by
    rw [show Wsub (Fin 2)
        = Submodule.span (ZMod 2) (Set.range (brk4 (Fin 2))) from rfl]
    exact Submodule.span_le.mpr (by rintro x ⟨t, rfl⟩; exact bft_brk4_mem t)
  obtain ⟨a, z, hz, hva⟩ :=
    (Submodule.mem_span_insert).mp (hWle hv)
  obtain ⟨b, c, hbc⟩ := (Submodule.mem_span_pair).mp hz
  have hv_eq : v = a • bftB0 + (b • bftB1 + c • bftB2) := by rw [hva, hbc]
  have hsv : σA v = a • bftB2 + b • bftB1 + c • bftB0 := by
    rw [hv_eq, map_add, map_add, map_smul, map_smul, map_smul, hsigB0, hsigB1, hsigB2]
    abel
  -- `(a+c) • (B0+B2) = 0`
  have hsum : v + σA v = (a + c) • (bftB0 + bftB2) := by
    rw [hsv, hv_eq, smul_add]
    rw [show (a • bftB0 + (b • bftB1 + c • bftB2)) + (a • bftB2 + b • bftB1 + c • bftB0)
          = (a • bftB0 + c • bftB0) + (b • bftB1 + b • bftB1) + (a • bftB2 + c • bftB2)
        from by abel]
    rw [bft_add_self (b • bftB1), add_zero, ← add_smul, ← add_smul]
  have hzero : (a + c) • (bftB0 + bftB2) = 0 := by
    rw [← hsum, hfix]
    exact bft_add_self v
  -- hence `a + c = 0`
  have hac : a + c = 0 := by
    have h := congrArg
      (fun x : MonoidAlgebra (ZMod 2) (FreeMonoid (Fin 2)) =>
        x.coeff (FreeMonoid.of (0 : Fin 2) * FreeMonoid.of 1 * FreeMonoid.of 0 * FreeMonoid.of 0))
      hzero
    simp only [MonoidAlgebra.coeff_smul_apply, bftD_coeff] at h
    simpa using h
  have hca : c = a := by
    calc c = 0 + c := (zero_add c).symm
      _ = (a + a) + c := by rw [bft_add_self a]
      _ = a + (a + c) := by abel
      _ = a + 0 := by rw [hac]
      _ = a := add_zero a
  -- the witness
  refine ⟨a • bftB0,
    Submodule.smul_mem _ a (Submodule.subset_span (show bftB0 ∈ Set.range (brk4 (Fin 2)) from
      ⟨((0 : Fin 2), 1, 0, 0), rfl⟩)), ?_⟩
  have hw : a • bftB0 + σA (a • bftB0) = a • bftB0 + a • bftB2 := by
    rw [map_smul, hsigB0]
  have hres : v - (a • bftB0 + σA (a • bftB0)) = b • bftB1 := by
    rw [hw, hv_eq, hca]
    abel
  rw [hres]
  -- `b • B1 = b • Θ(a²)` lies in the required span
  refine Submodule.smul_mem _ b ?_
  refine Submodule.subset_span ⟨⟨bftE 0 * bftE 0, bftE_sq_mem_Tsub⟩, ?_⟩
  exact (bftB1_theta σ σA hmul hgen hσ0).symm

end BaseFinTwo

end Work.SSGRoute
