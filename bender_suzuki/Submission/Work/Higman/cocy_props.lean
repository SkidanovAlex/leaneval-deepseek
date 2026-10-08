import Mathlib
import Submission.Work.Higman.CoordDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {G : Type*} [Group G]

/-! ## Restriction helpers for the recursion on the last coordinate

`coordSec`, `cocy`, `coordSec_zero` and `coordSec_succ` live in
`Submission.Work.Higman.CoordDefs`; here we record the same recursion in terms of the
abbreviations `res`, `lastA`, `resV`, `lastV`.  All the auxiliary material below is `private`,
only `cocy_props` is exported. -/

/-- Restriction of `A : Fin (n+1) → G` to the first `n` coordinates. -/
private def res {n : ℕ} (A : Fin (n + 1) → G) : Fin n → G := fun i => A i.castSucc

/-- The last entry of `A : Fin (n+1) → G`. -/
private def lastA {n : ℕ} (A : Fin (n + 1) → G) : G := A (Fin.last n)

/-- Restriction of `v : Fin (n+1) → ZMod 2` to the first `n` coordinates. -/
private def resV {n : ℕ} (v : Fin (n + 1) → ZMod 2) : Fin n → ZMod 2 := fun i => v i.castSucc

/-- The `.val` of the last coordinate of `v : Fin (n+1) → ZMod 2`. -/
private def lastV {n : ℕ} (v : Fin (n + 1) → ZMod 2) : ℕ := (v (Fin.last n)).val

private theorem coordSec_succ' (n : ℕ) (A : Fin (n + 1) → G) (v : Fin (n + 1) → ZMod 2) :
    coordSec (n + 1) A v = coordSec n (res A) (resV v) * lastA A ^ lastV v := rfl

private theorem resV_add {n : ℕ} (v w : Fin (n + 1) → ZMod 2) :
    resV (v + w) = resV v + resV w := rfl

/-- The last coordinate of `v + w` is the sum of the last coordinates, computed in `ZMod 2`. -/
private theorem lastV_add {n : ℕ} (v w : Fin (n + 1) → ZMod 2) :
    lastV (v + w) = (lastV v + lastV w) % 2 := by
  simp only [lastV, Pi.add_apply, ZMod.val_add]

private theorem lastV_eq_zero_or_one {n : ℕ} (v : Fin (n + 1) → ZMod 2) :
    lastV v = 0 ∨ lastV v = 1 := by
  have h : lastV v < 2 := by simpa only [lastV] using ZMod.val_lt (v (Fin.last n))
  omega

/-! ## Group-theoretic facts -/

/-- `a * b = ⁅a, b⁆ * (b * a)` (the defining property of the commutator). -/
private theorem mul_eq_commutator_mul (a b : G) : a * b = ⁅a, b⁆ * (b * a) := by group

/-- Commutation of a central element. -/
private theorem commute_of_mem_center {z : G} (hz : z ∈ Subgroup.center G) (x : G) :
    Commute z x := by
  rw [commute_iff_eq]
  exact (Subgroup.mem_center_iff.mp hz x).symm

/-- `z * x = x * z` for a central `z`. -/
private theorem center_mul_comm {z : G} (hz : z ∈ Subgroup.center G) (x : G) : z * x = x * z :=
  Commute.eq (commute_of_mem_center hz x)

/-- A central factor can be pulled out of a product. -/
private theorem mul_center_mul {c : G} (h2 : c ∈ Subgroup.center G) (V W d : G) :
    (V * c) * (W * d) = (V * W) * (c * d) := by
  calc (V * c) * (W * d) = V * (c * W * d) := by group
    _ = V * (W * c * d) := by rw [← center_mul_comm h2 W]
    _ = (V * W) * (c * d) := by group

/-- A commutator with a central element is trivial. -/
private theorem commutatorElement_eq_one_of_mem_center {z x : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz x)

/-- The commutator is bilinear in its second variable when all commutators are central. -/
private theorem commutatorElement_mul_right' (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅a, b⁆ b ⁅a, c⁆,
    ← center_mul_comm (hc a c) b]
  group

/-- The commutator is bilinear in its first variable when all commutators are central. -/
private theorem commutatorElement_mul_left' (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (a b c : G) : ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, ← center_mul_comm (hc b c) a]
  group

/-- Every commutator is an involution. -/
private theorem commutatorElement_inv_eq_self (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1) (a b : G) : ⁅a, b⁆⁻¹ = ⁅a, b⁆ := by
  have h : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
    rw [← pow_two]; exact hexp ⁅a, b⁆ (hc a b)
  exact inv_eq_of_mul_eq_one_right h

/-- Commutators are symmetric. -/
private theorem commutatorElement_symm' (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1) (a b : G) : ⁅a, b⁆ = ⁅b, a⁆ := by
  calc ⁅a, b⁆ = ⁅a, b⁆⁻¹⁻¹ := (inv_inv ⁅a, b⁆).symm
    _ = ⁅b, a⁆⁻¹ := by rw [commutatorElement_inv]
    _ = ⁅b, a⁆ := commutatorElement_inv_eq_self hc hexp b a

/-- `T ^ m * (c2 * c3) = (T ^ a * c2) * (T ^ b * c3)` for a central involution `T`. -/
private theorem pow_central_combine {T c2 c3 : G} (h2 : c2 ∈ Subgroup.center G)
    (hT2 : T ^ 2 = 1) {a b m : ℕ} (hm : m = (a + b) % 2) :
    T ^ m * (c2 * c3) = (T ^ a * c2) * (T ^ b * c3) := by
  rw [mul_center_mul h2]
  congr 1
  rw [hm, ← pow_add]
  exact (pow_eq_pow_mod (a + b) hT2).symm

/-! ## The one-step formula for the coordinates -/

/-- Elementary algebraic step: multiplying a section element by `α ^ a`, etc.  This is the
case analysis on the last coordinate: `α ^ a` is either `1` or `α`, and the two new factors
contribute a commutator `⁅α, y⁆` and, when both exponents are `1`, a square `α ^ 2`. -/
private theorem step_alg (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G) (α x y z : G) {a b m : ℕ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hm : m = (a + b) % 2) :
    (x * α ^ a) * (y * α ^ b) * (z * α ^ m)⁻¹
      = (⁅α, y⁆ * (α ^ 2) ^ b) ^ a * (x * y * z⁻¹) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · have hm0 : m = 0 := by simp [hm]
    rw [hm0]
    simp
  · have hm1 : m = 1 := by simp [hm]
    rw [hm1]
    simp only [pow_one, pow_zero, mul_one]
    group
  · have hm1 : m = 1 := by simp [hm]
    rw [hm1]
    simp only [pow_one, pow_zero, mul_one]
    have hcy : α * y = ⁅α, y⁆ * (y * α) := mul_eq_commutator_mul α y
    have hxc : ⁅α, y⁆ * x = x * ⁅α, y⁆ := (Subgroup.mem_center_iff.mp (hc α y) x).symm
    calc (x * α) * y * (z * α)⁻¹
        = x * (α * y) * (α⁻¹ * z⁻¹) := by group
      _ = x * (⁅α, y⁆ * (y * α)) * (α⁻¹ * z⁻¹) := by rw [hcy]
      _ = ⁅α, y⁆ * (x * y * z⁻¹) := by rw [← mul_assoc x, ← hxc]; group
  · have hm0 : m = 0 := by simp [hm]
    rw [hm0]
    simp only [pow_one, pow_zero, mul_one]
    have hcy : α * y = ⁅α, y⁆ * (y * α) := mul_eq_commutator_mul α y
    have hxc : ⁅α, y⁆ * x = x * ⁅α, y⁆ := (Subgroup.mem_center_iff.mp (hc α y) x).symm
    have hzq : α ^ 2 * z⁻¹ = z⁻¹ * α ^ 2 := center_mul_comm (hsq α) z⁻¹
    have hzq' : α ^ 2 * (x * y * z⁻¹) = (x * y * z⁻¹) * α ^ 2 :=
      center_mul_comm (hsq α) _
    calc (x * α) * (y * α) * z⁻¹
        = x * (α * y) * α * z⁻¹ := by group
      _ = x * (⁅α, y⁆ * (y * α)) * α * z⁻¹ := by rw [hcy]
      _ = ⁅α, y⁆ * (x * y * (α * α) * z⁻¹) := by rw [← mul_assoc x, ← hxc]; group
      _ = ⁅α, y⁆ * (x * y * (α ^ 2 * z⁻¹)) := by rw [pow_two]; group
      _ = ⁅α, y⁆ * (x * y * (z⁻¹ * α ^ 2)) := by rw [hzq]
      _ = ⁅α, y⁆ * ((x * y * z⁻¹) * α ^ 2) := by group
      _ = ⁅α, y⁆ * (α ^ 2 * (x * y * z⁻¹)) := by rw [← hzq']
      _ = (⁅α, y⁆ * α ^ 2) * (x * y * z⁻¹) := by group

/-! ## The cocycle step

`Phi A w` collects the correction produced by the last coordinate: the commutator of the last
generator with the section element of `w`, times the square of the last generator. -/

/-- The "last coordinate" correction factor of the cocycle at level `n+1`. -/
private def Phi {n : ℕ} (A : Fin (n + 1) → G) (w : Fin (n + 1) → ZMod 2) : G :=
  ⁅lastA A, coordSec n (res A) (resV w)⁆ * (lastA A ^ 2) ^ lastV w

private theorem Phi_mem_center (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G) {n : ℕ} (A : Fin (n + 1) → G)
    (w : Fin (n + 1) → ZMod 2) : Phi A w ∈ Subgroup.center G := by
  simp only [Phi]
  exact Subgroup.mul_mem _ (hc _ _) (Subgroup.pow_mem _ (hsq _) _)

/-- The cocycle at level `n+1` in terms of the cocycle at level `n` and `Phi`. -/
private theorem cocy_succ (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1) (n : ℕ) (A : Fin (n + 1) → G)
    (v w : Fin (n + 1) → ZMod 2) :
    cocy (n + 1) A v w = Phi A w ^ lastV v * cocy n (res A) (resV v) (resV w) := by
  show cocy (n + 1) A v w
      = (⁅lastA A, coordSec n (res A) (resV w)⁆ * (lastA A ^ 2) ^ lastV w) ^ lastV v
        * cocy n (res A) (resV v) (resV w)
  have h1 : cocy (n + 1) A v w
      = (coordSec n (res A) (resV v) * lastA A ^ lastV v)
        * (coordSec n (res A) (resV w) * lastA A ^ lastV w)
        * (coordSec n (res A) (resV (v + w)) * lastA A ^ lastV (v + w))⁻¹ := by
    simp only [cocy, coordSec_succ']
  rw [h1, lastV_add, cocy]
  exact step_alg hc hsq (lastA A) _ _ _ (lastV_eq_zero_or_one v) (lastV_eq_zero_or_one w)
    (by rfl)

/-- `Phi` is multiplicative in its second argument (uses centrality of the level-`n` cocycle). -/
private theorem Phi_mul (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1) {n : ℕ} (A : Fin (n + 1) → G)
    (w u : Fin (n + 1) → ZMod 2)
    (hcoc : cocy n (res A) (resV w) (resV u) ∈ Subgroup.center G) :
    Phi A (w + u) = Phi A w * Phi A u := by
  show ⁅lastA A, coordSec n (res A) (resV (w + u))⁆ * (lastA A ^ 2) ^ lastV (w + u)
      = (⁅lastA A, coordSec n (res A) (resV w)⁆ * (lastA A ^ 2) ^ lastV w)
        * (⁅lastA A, coordSec n (res A) (resV u)⁆ * (lastA A ^ 2) ^ lastV u)
  rw [resV_add w u, lastV_add w u]
  have hsu : coordSec n (res A) (resV w) * coordSec n (res A) (resV u)
      = cocy n (res A) (resV w) (resV u) * coordSec n (res A) (resV w + resV u) := by
    simp only [cocy]; group
  have hcomm : ⁅lastA A, coordSec n (res A) (resV w)⁆ * ⁅lastA A, coordSec n (res A) (resV u)⁆
      = ⁅lastA A, coordSec n (res A) (resV w + resV u)⁆ := by
    calc ⁅lastA A, coordSec n (res A) (resV w)⁆ * ⁅lastA A, coordSec n (res A) (resV u)⁆
        = ⁅lastA A, coordSec n (res A) (resV w) * coordSec n (res A) (resV u)⁆ :=
          (commutatorElement_mul_right' hc _ _ _).symm
      _ = ⁅lastA A, cocy n (res A) (resV w) (resV u) * coordSec n (res A) (resV w + resV u)⁆ :=
          by rw [hsu]
      _ = ⁅lastA A, cocy n (res A) (resV w) (resV u)⁆
            * ⁅lastA A, coordSec n (res A) (resV w + resV u)⁆ :=
          commutatorElement_mul_right' hc _ _ _
      _ = ⁅lastA A, coordSec n (res A) (resV w + resV u)⁆ := by
          rw [commutatorElement_eq_one_of_mem_center hcoc]; simp
  have hQ : (lastA A ^ 2) ^ ((lastV w + lastV u) % 2)
      = (lastA A ^ 2) ^ lastV w * (lastA A ^ 2) ^ lastV u := by
    rw [← pow_eq_pow_mod (lastV w + lastV u)
      (show (lastA A ^ 2) ^ 2 = 1 from hexp _ (hsq (lastA A))), pow_add]
  rw [← hcomm, hQ, mul_center_mul (Subgroup.pow_mem _ (hsq (lastA A)) (lastV w))]

/-! ## The main induction on the number of coordinates -/

/-- The cocycle is bi-additive and central-valued; proved by induction on the number of
coordinates (peeling off the last coordinate). -/
private lemma cocy_props_aux (hc : ∀ a b : G, ⁅a, b⁆ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1) :
    ∀ (n : ℕ) (A : Fin n → G),
      (∀ v w u : Fin n → ZMod 2, cocy n A (v + w) u = cocy n A v u * cocy n A w u) ∧
      (∀ v w u : Fin n → ZMod 2, cocy n A v (w + u) = cocy n A v w * cocy n A v u) ∧
      (∀ v w : Fin n → ZMod 2, cocy n A v w ∈ Subgroup.center G) := by
  intro n
  induction n with
  | zero =>
      intro A
      refine ⟨?_, ?_, ?_⟩
      · intro v w u; simp [cocy]
      · intro v w u; simp [cocy]
      · intro v w
        simp only [cocy, coordSec_zero, mul_one, inv_one]
        exact Subgroup.one_mem _
  | succ n ih =>
      intro A
      obtain ⟨ih1, ih2, ih3⟩ := ih (res A)
      refine ⟨?_, ?_, ?_⟩
      · intro v w u
        rw [cocy_succ hc hsq hexp, cocy_succ hc hsq hexp, cocy_succ hc hsq hexp]
        rw [resV_add, lastV_add, ih1 (resV v) (resV w) (resV u)]
        exact pow_central_combine (ih3 (resV v) (resV u))
          (hexp _ (Phi_mem_center hc hsq A u)) (by rfl)
      · intro v w u
        rw [cocy_succ hc hsq hexp, cocy_succ hc hsq hexp, cocy_succ hc hsq hexp]
        rw [resV_add, ih2 (resV v) (resV w) (resV u),
          Phi_mul hc hsq hexp A w u (ih3 (resV w) (resV u))]
        rw [Commute.mul_pow (commute_of_mem_center (Phi_mem_center hc hsq A w) (Phi A u))]
        rw [mul_center_mul (ih3 (resV v) (resV w))]
      · intro v w
        rw [cocy_succ hc hsq hexp]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Phi_mem_center hc hsq A w) _)
          (ih3 (resV v) (resV w))

theorem cocy_props {G : Type*} [Group G]
    (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G)
    (hsq : ∀ a : G, a ^ 2 ∈ Subgroup.center G)
    (hexp : ∀ z : G, z ∈ Subgroup.center G → z ^ 2 = 1)
    (n : ℕ) (A : Fin n → G) :
    (∀ v w u : Fin n → ZMod 2, cocy n A (v + w) u = cocy n A v u * cocy n A w u) ∧
    (∀ v w u : Fin n → ZMod 2, cocy n A v (w + u) = cocy n A v w * cocy n A v u) ∧
    (∀ v w : Fin n → ZMod 2, cocy n A v w ∈ Subgroup.center G) :=
  cocy_props_aux hc hsq hexp n A

end Work.Higman
