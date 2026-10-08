import Mathlib
import Submission.Work.ZassenhausSuzuki.fixTheta_cube_aux
import Submission.Work.ZassenhausSuzuki.szTilde_comm_of_fix
import Submission.Work.ZassenhausSuzuki.szTilde_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `D`-element `e (∼P)⁻¹ (∼Q) (∼R)⁻¹ = ⟨0, λ + λ⁻¹⟩` of the 5.14 computation

Let `G` carry a split rank-one Zassenhaus configuration `H = Q ⋊ D` with root group
`Q ≃* A(K,θ) = SzA K θ` (`K = GF(2^m)`, `θ ≠ 1` of odd order) through which `D = twoPoint H t`
acts by the standard torus `Λ = h(Kˣ)` (`htorus`), and let `∼ = szTilde hsplit` be the Suzuki
reflection map of the root group (`∼ x = g (g x)⁻¹`, BG 3.1 (j), `SzTildeDefs.lean`).

For `λ ∈ Fix θ ∖ {1}` the element
`d := (∼ z_{γ})⁻¹ · (∼ z_{λ²+λ⁻²}) · (∼ z_{δ})⁻¹`,
where `z_b = zc e b = e.symm ⟨0,b⟩` and `γ = (1+λ⁻¹)²`, `δ = (1+λ)²`, has `e`-coordinates
`⟨0, λ + λ⁻¹⟩` (non-zero, since `λ ≠ λ⁻¹`).

The computation is entirely local: writing `p = 1 + λ⁻¹`, `q = λ + λ⁻¹` (so that
`p + q = 1 + λ =: r`) and `κ = (e (∼ z_1)).b`, the reflection of a central involution
`z_b` (`b ≠ 0`) has `e`-coordinates `⟨σ b, κ b⟩`, where `σ b` is the `(1+θ)`-root of `b`
(`(σ b)·θ(σ b) = b`), i.e. `σ(γ) = p`, `σ(λ²+λ⁻²) = q`, `σ(δ) = r`.  The triple product in
`A(K,θ)` is then a straightforward computation (`szA_triple`), closed by
`p·θ q = q·θ p` (here `θ p = p`, `θ q = q`).

* `szTilde_zc_coords` — the coordinates `⟨σ b, κ b⟩` of `∼ z_b`;
* `szA_triple` — the local computation `(x)⁻¹ y (z)⁻¹ = ⟨0, p θ(p+q)⟩` in `A(K,θ)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-! ## Elementary characteristic-two facts about `1 + x` and `x + x⁻¹` -/

/-- In characteristic two, `1 + x = 0` forces `x = 1`. -/
theorem eq_one_of_one_add_eq_zero {K : Type*} [Field K] [CharP K 2] {x : K}
    (h : 1 + x = 0) : x = 1 := by
  have hx := eq_neg_of_add_eq_zero_right h
  rwa [CharTwo.neg_eq] at hx

/-- In characteristic two, `x ≠ 1` gives `1 + x ≠ 0`. -/
theorem one_add_ne_zero {K : Type*} [Field K] [CharP K 2] {x : K} (h : x ≠ 1) :
    1 + x ≠ 0 := fun h0 => h (eq_one_of_one_add_eq_zero h0)

/-- In characteristic two, `x ≠ 1` gives `1 + x⁻¹ ≠ 0`. -/
theorem one_add_inv_ne_zero {K : Type*} [Field K] [CharP K 2] {x : K} (h : x ≠ 1) :
    1 + x⁻¹ ≠ 0 := fun h0 => h (inv_eq_one.mp (eq_one_of_one_add_eq_zero h0))

/-- In characteristic two, `x ≠ 0, 1` gives `x + x⁻¹ ≠ 0`.  (From `x + x⁻¹ = 0` one gets
`x² = 1`, hence `(x+1)² = x² + 1 = 0`, hence `x = 1`.) -/
theorem add_inv_ne_zero {K : Type*} [Field K] [CharP K 2] {x : K} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    x + x⁻¹ ≠ 0 := by
  intro h
  have hm : x * x = 1 := by
    have hx : x * (x + x⁻¹) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_inv_cancel₀ h0] at hx
    have hx' : x * x = -1 := eq_neg_of_add_eq_zero_left (a := x * x) (b := 1) hx
    rwa [CharTwo.neg_eq] at hx'
  have hsq : (x + 1) * (x + 1) = 0 := by
    have hexp : (x + 1) * (x + 1) = x * x + (x + x) + 1 := by ring
    rw [hexp, hm, CharTwo.add_self_eq_zero x, add_zero, CharTwo.add_self_eq_zero 1]
  have hx1 : x + 1 = 0 := mul_self_eq_zero.mp hsq
  exact h1 (eq_one_of_one_add_eq_zero (by rwa [add_comm] at hx1))

/-- In characteristic two, `x ≠ 0, 1` gives `x² + (x⁻¹)² ≠ 0`, since `x² + (x⁻¹)² = (x + x⁻¹)²`
(`x ↦ x²` is additive in characteristic two). -/
theorem sq_add_inv_sq_ne_zero {K : Type*} [Field K] [CharP K 2] {x : K} (h0 : x ≠ 0)
    (h1 : x ≠ 1) : x ^ 2 + x⁻¹ ^ 2 ≠ 0 := by
  have hne : x + x⁻¹ ≠ 0 := add_inv_ne_zero h0 h1
  have hsq : x ^ 2 + x⁻¹ ^ 2 = (x + x⁻¹) ^ 2 := by
    have hexp : (x + x⁻¹) ^ 2 = x ^ 2 + (x * x⁻¹ + x * x⁻¹) + x⁻¹ ^ 2 := by ring
    rw [hexp, CharTwo.add_self_eq_zero (x * x⁻¹), add_zero]
  rw [hsq]
  exact pow_ne_zero 2 hne

/-! ## The local computation in `A(K,θ)`

If `p, q ∈ K` satisfy `p·θq = q·θp`, then the three elements
`(p, κ·pθp)⁻¹`, `(q, κ·qθq)`, `(p+q, κ·(p+q)θ(p+q))⁻¹` of `A(K,θ)` multiply to
`(0, p·θ(p+q))`.  This is the coordinate form of BG's 5.14 computation: the first coordinates
cancel because `(p+q) + (-p) + (-(p+q)) = 0`, the `κ`-terms cancel because
`pθp + qθq + (p+q)θ(p+q) = pθq + qθp = 0`, and the `q·θ(p+q)` term together with the two
copies of `(p+q)·θ(p+q)` leaves `p·θ(p+q)`. -/
theorem szA_triple {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) {p q κ : K}
    (hcomm : p * θ q + q * θ p = 0) :
    (⟨p, κ * (p * θ p)⟩ : SzA K θ)⁻¹ * ⟨q, κ * (q * θ q)⟩
        * (⟨p + q, κ * ((p + q) * θ (p + q))⟩)⁻¹
      = ⟨0, p * θ (p + q)⟩ := by
  have hθ : θ (p + q) = θ p + θ q := map_add θ p q
  ext
  · simp only [SzA.mul_a, SzA.inv_a, hθ, CharTwo.neg_eq]
    exact CharTwo.add_self_eq_zero (p + q)
  · simp only [SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b, hθ, CharTwo.neg_eq]
    have hZ : p * θ p + q * θ q + (p + q) * (θ p + θ q) = 0 := by
      linear_combination hcomm + (CharTwo.add_self_eq_zero (p * θ p))
        + (CharTwo.add_self_eq_zero (q * θ q))
    linear_combination κ * hZ + (CharTwo.add_self_eq_zero ((p + q) * (θ p + θ q)))

/-! ## The coordinates of the reflection of a central involution -/

/-- **The `e`-coordinates of `∼ z_b`.**  If `c · θ c = b` with `b ≠ 0` (so that `c` is the
`(1+θ)`-root of the non-zero central coordinate `b`), then
`e (∼ (zc e b)) = ⟨c, κ · (c · θ c)⟩` with `κ = (e (∼ (zc e 1))).b`: the second coordinate is
`szTilde_zc_b`, and the first is `c` because `x ↦ x·θx` is injective and
`(e (∼ z_b)).a · θ (e (∼ z_b)).a = b = c·θc` (`szTilde_coord_sq`). -/
theorem szTilde_zc_coords {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {b c : GaloisField 2 m} (hb : b ≠ 0) (hc : c * θ c = b) :
    e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e b))
      = (⟨c, (e (Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e 1))).b
            * (c * θ c)⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  classical
  refine SzA.ext ?_ ?_
  · refine mul_theta_injective θ hθodd ?_
    show (e (szTilde hsplit (zc e b))).a * θ ((e (szTilde hsplit (zc e b))).a) = c * θ c
    rw [szTilde_coord_sq hsplit hzass hθ1 hθodd htorus (a := zc e b) (b := b)
      (by rw [zc_coe]) hb, hc]
  · rw [szTilde_zc_b hsplit hzass hθ1 hθodd htorus hb, ← hc]

/-! ## The target -/

theorem e_d_mul {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {lam : GaloisField 2 m} (hfix : θ lam = lam) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    e ((Work.ZassenhausSuzuki.szTilde hsplit
          (Work.ZassenhausSuzuki.zc e ((1 + lam⁻¹) ^ 2)))⁻¹
        * Work.ZassenhausSuzuki.szTilde hsplit (Work.ZassenhausSuzuki.zc e (lam ^ 2 + lam⁻¹ ^ 2))
        * (Work.ZassenhausSuzuki.szTilde hsplit
            (Work.ZassenhausSuzuki.zc e ((1 + lam) ^ 2)))⁻¹)
      = (⟨0, lam + lam⁻¹⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
  classical
  -- `p + q = r` for `p = 1 + λ⁻¹`, `q = λ + λ⁻¹`, `r = 1 + λ`
  have hsum : (1 + lam⁻¹) + (lam + lam⁻¹) = 1 + lam := by
    linear_combination CharTwo.add_self_eq_zero lam⁻¹
  -- `θ` fixes `p`, `q`, `r`
  have hcP : (1 + lam⁻¹) * θ (1 + lam⁻¹) = (1 + lam⁻¹) ^ 2 := by
    rw [map_add, map_one, map_inv₀, hfix, pow_two]
  have hcQ : (lam + lam⁻¹) * θ (lam + lam⁻¹) = lam ^ 2 + lam⁻¹ ^ 2 := by
    rw [map_add, map_inv₀, hfix]
    have hexp : (lam + lam⁻¹) * (lam + lam⁻¹)
        = lam ^ 2 + (lam * lam⁻¹ + lam * lam⁻¹) + lam⁻¹ ^ 2 := by ring
    rw [hexp, CharTwo.add_self_eq_zero (lam * lam⁻¹), add_zero]
  have hcR : (1 + lam) * θ (1 + lam) = (1 + lam) ^ 2 := by
    rw [map_add, map_one, hfix, pow_two]
  -- the commutation hypothesis `p θq = q θp` (here `θq = q`, `θp = p`)
  have hcomm : (1 + lam⁻¹) * θ (lam + lam⁻¹) + (lam + lam⁻¹) * θ (1 + lam⁻¹) = 0 := by
    simp only [map_add, map_inv₀, map_one, hfix]
    rw [mul_comm (lam + lam⁻¹) (1 + lam⁻¹)]
    exact CharTwo.add_self_eq_zero ((1 + lam⁻¹) * (lam + lam⁻¹))
  -- the value `p · θ r = λ + λ⁻¹`
  have hb : (1 + lam⁻¹) * θ (1 + lam) = lam + lam⁻¹ := by
    simp only [map_add, map_one, hfix]
    have hlinv : lam⁻¹ * lam = 1 := inv_mul_cancel₀ h0
    linear_combination hlinv + CharTwo.add_self_eq_zero (1 : GaloisField 2 m)
  -- non-vanishing of the three central coordinates
  have hPne : (1 + lam⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (one_add_inv_ne_zero h1)
  have hQne : lam ^ 2 + lam⁻¹ ^ 2 ≠ 0 := sq_add_inv_sq_ne_zero h0 h1
  have hRne : (1 + lam) ^ 2 ≠ 0 := pow_ne_zero 2 (one_add_ne_zero h1)
  -- the coordinates of the three reflections
  have eP := szTilde_zc_coords hsplit hzass hθ1 hθodd htorus hPne hcP
  have eQ := szTilde_zc_coords hsplit hzass hθ1 hθodd htorus hQne hcQ
  have eR := szTilde_zc_coords hsplit hzass hθ1 hθodd htorus hRne hcR
  rw [map_mul, map_mul, map_inv, map_inv, eP, eQ, eR]
  rw [← hsum]
  rw [szA_triple θ hcomm]
  rw [hsum, hb]

end Work.ZassenhausSuzuki
