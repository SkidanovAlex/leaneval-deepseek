import Mathlib
import Submission.Work.Hering.AppVIII.CTwoStepDefs
import Submission.Work.Hering.AppVIII.CTwoStepFacts
import Submission.Work.Hering.AppVIII.cType_mixed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The polar form of the squaring map of `C(3,ε)` (`n = 3`)

For `K = KC 1 = GF(8)` and `ε : K`, the squaring map of the Suzuki 2-group `C(3,ε)` is

  `quadC 1 ε (x,y) = x³ + ε·x⁴·y⁴ + y²   (quadC_one)`,

so its polar form (the "commutator" form) is

  `betaP ε (x,y) (x',y') = x·x'² + x'·x² + ε·(x⁴·y'⁴ + x'⁴·y⁴)`.

`betaP` is biadditive and alternating (`betaP_comm`, `betaP_self`, `betaP_add_left`,
`betaP_add_right`), and it coincides with the polarization
`quadC 1 ε (u+v) + quadC 1 ε u + quadC 1 ε v` (`quadC_polar`).

`W = {u | u.1 = 0}` is totally isotropic for `betaP` (`betaP_W`); in fact it is the *unique*
totally isotropic `𝔽₂`-subspace of `K × K` of order `8` (`fst_eq_zero_of_totally_isotropic`,
proved in `IsotropicUnique.lean`).  That uniqueness is what forces every automorphism of
`C(3,ε)` to stabilise `P₁ = π⁻¹(0 × K)`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.Hering.AppVIII

open Work.Higman

/-- The binomial expansion of the cube in characteristic two. -/
lemma add_pow3 (a b : KC 1) : (a + b) ^ 3 = a ^ 3 + b ^ 3 + a ^ 2 * b + a * b ^ 2 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, CharTwo.add_sq]; ring

/-- The binomial expansion of the fourth power in characteristic two. -/
lemma add_pow4 (a b : KC 1) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, CharTwo.add_sq, CharTwo.add_sq, pow_mul, pow_mul]

/-- The squaring map of `C(3,ε)`, in coordinates. -/
lemma quadC_one (ε : KC 1) (x y : KC 1) : quadC 1 ε (x, y) = x ^ 3 + ε * (x ^ 4 * y ^ 4) + y ^ 2 := by
  rw [quadC_expand]; norm_num

/-- The polar form of the squaring map of `C(3,ε)`, in coordinates. -/
def betaP (ε : KC 1) (u v : KC 1 × KC 1) : KC 1 :=
  u.1 * v.1 ^ 2 + v.1 * u.1 ^ 2 + ε * (u.1 ^ 4 * v.2 ^ 4 + v.1 ^ 4 * u.2 ^ 4)

theorem betaP_comm (ε : KC 1) (u v : KC 1 × KC 1) : betaP ε u v = betaP ε v u := by
  simp only [betaP]; ring

theorem betaP_self (ε : KC 1) (u : KC 1 × KC 1) : betaP ε u u = 0 := by
  simp only [betaP]; ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem betaP_add_left (ε : KC 1) (u u' v : KC 1 × KC 1) :
    betaP ε (u + u') v = betaP ε u v + betaP ε u' v := by
  simp only [betaP, Prod.fst_add, Prod.snd_add]
  rw [CharTwo.add_sq, add_pow4, add_pow4]
  ring_nf

theorem betaP_add_right (ε : KC 1) (u v v' : KC 1 × KC 1) :
    betaP ε u (v + v') = betaP ε u v + betaP ε u v' := by
  simp only [betaP, Prod.fst_add, Prod.snd_add]
  rw [CharTwo.add_sq, add_pow4, add_pow4]
  ring_nf

@[simp] theorem betaP_zero_left (ε : KC 1) (v : KC 1 × KC 1) : betaP ε 0 v = 0 := by
  simp [betaP]

@[simp] theorem betaP_zero_right (ε : KC 1) (u : KC 1 × KC 1) : betaP ε u 0 = 0 := by
  simp [betaP]

/-- `W = {u | u.1 = 0}` is totally isotropic for `betaP`. -/
theorem betaP_W (ε : KC 1) (y y' : KC 1) : betaP ε (0, y) (0, y') = 0 := by
  simp [betaP]

/-- The polar form is the polarization of the squaring map `quadC 1 ε`. -/
theorem quadC_polar (ε : KC 1) (u v : KC 1 × KC 1) :
    quadC 1 ε (u + v) + quadC 1 ε u + quadC 1 ε v = betaP ε u v := by
  obtain ⟨x, y⟩ := u
  obtain ⟨x', y'⟩ := v
  show quadC 1 ε (x + x', y + y') + quadC 1 ε (x, y) + quadC 1 ε (x', y') =
      betaP ε (x, y) (x', y')
  rw [quadC_one, quadC_one, quadC_one, betaP]
  rw [add_pow3 x x', add_pow4 x x', add_pow4 y y', CharTwo.add_sq y y']
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

/-- `W = {u : K × K | u.1 = 0}`, as an additive subgroup. -/
def Wsub : AddSubgroup (KC 1 × KC 1) where
  carrier := {u | u.1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    show (a + b).1 = 0
    have ha' : a.1 = 0 := ha
    have hb' : b.1 = 0 := hb
    rw [Prod.fst_add, ha', hb', add_zero]
  neg_mem' := by
    intro a ha
    show (-a).1 = 0
    simpa using ha

@[simp] theorem mem_Wsub {u : KC 1 × KC 1} : u ∈ Wsub ↔ u.1 = 0 := Iff.rfl

theorem betaP_Wsub (ε : KC 1) (u v : Wsub) :
    betaP ε (u : KC 1 × KC 1) (v : KC 1 × KC 1) = 0 := by
  obtain ⟨⟨x, y⟩, hx⟩ := u
  obtain ⟨⟨x', y'⟩, hx'⟩ := v
  simp only [mem_Wsub] at hx hx'
  simp [betaP, hx, hx']

end Work.Hering.AppVIII
