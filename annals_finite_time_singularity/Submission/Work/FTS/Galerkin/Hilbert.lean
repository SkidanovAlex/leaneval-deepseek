/-
# The GALERKIN area: the weighted `𝓗⁴` inner-product chapter

This module is the *Hilbert-space setup* of audit §4 N6 (steps 1–2): the API of the admissible
inner product `IP` on the weighted space `𝓗⁴` of `Work.Spaces` — its accessor lemmas
(nonnegativity, dominance of `|·|_{ℋ⁴}`, coercivity of `𝓛_Γ^T`, Cauchy–Schwarz), the fact that
`IP` is bilinear (so that `IP f 0 = 0` and the pairing of Galerkin combinations is the Euclidean
pairing of coefficients), and the two consequences that the Galerkin argument actually consumes:

* `IsIPOrthonormal.self`: for an `IP`-orthonormal test sequence,
  `IP (∑ cₖφₖ) (∑ cₖφₖ) = ∑ cₖ²` — the *exactness of the energy identity* (audit step 4);
* `IsIPOrthonormal.sq_sum_le`: consequently the Euclidean norm of the coefficients is controlled
  by the `ℋ⁴`-norm of the Galerkin profile, which is how the a-priori `ℋ⁴`-bound turns into the
  coefficient-ball bound used by the ODE existence theorem.

The bilinearity facts are the unrestricted fields of `Work.Construction.IsH4IP`
(`add_fst`, `add_snd`, `smul_fst`, and `IsH4Inner.smul_snd` derived from symmetry): the
membership-restricted linearity of `Work.Coercivity.IsHkIP` is *not* needed for the pairing
algebra, which is why the Galerkin reduction is purely formal.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Galerkin.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Accessors for the `ℋ⁴` inner product -/

theorem IsH4Inner.IP_self_nonneg {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f : Fn) :
    0 ≤ IP f f := h.isHkIP.2.2.1 f

/-- `IP` dominates the `ℋ⁴`-norm squared on the admissible class. -/
theorem IsH4Inner.dominates {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) {f : Fn}
    (hf : Coercivity.HkAdm α 4 f) : Spaces.HkSq α 4 f ≤ IP f f :=
  h.isHkIP.2.2.2.1 f hf

/-- `IP` is bounded by a multiple of the `ℋ⁴`-norm squared on the admissible class. -/
theorem IsH4Inner.bounded {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fn, Coercivity.HkAdm α 4 f → IP f f ≤ C * Spaces.HkSq α 4 f :=
  h.isHkIP.2.2.2.2.1

/-- **Coercivity of `𝓛_Γ^T`** (Propositions `HkCoercivity` of the paper, audit N2): there is
`c > 0` with `c |f|²_{ℋ⁴} ≤ IP (𝓛_Γ^T f) f` for admissible `f`. -/
theorem IsH4Inner.coercive {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Fn, Coercivity.HkAdm α 4 f →
      c * Spaces.HkSq α 4 f ≤ IP (Coercivity.LGammaT α f) f :=
  h.isHkIP.2.2.2.2.2

/-- **Cauchy–Schwarz** for `IP` against the `ℋ⁴`-norm. -/
theorem IsH4Inner.cs' {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g : Fn) :
    |IP f g| ≤ Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g := h.cs f g

theorem IsH4Inner.le_norm {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g : Fn) :
    IP f g ≤ Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
  le_trans (le_abs_self _) (h.cs' f g)

theorem IsH4Inner.neg_le_norm {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g : Fn) :
    -(Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g) ≤ IP f g := by
  have h1 := h.cs' f g
  have h2 := neg_abs_le (IP f g)
  linarith

/-! ## Bilinearity consequences -/

theorem IsH4Inner.IP_zero_snd {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f : Fn) :
    IP f (fun _ _ => (0 : ℝ)) = 0 := by
  have h0 : ((fun _ _ : ℝ => (0 : ℝ)) + (fun _ _ : ℝ => (0 : ℝ))) = fun _ _ => (0 : ℝ) := by
    funext x y; simp
  have h1 := h.add_snd f (fun _ _ : ℝ => (0 : ℝ)) (fun _ _ : ℝ => (0 : ℝ))
  rw [h0] at h1
  linarith

theorem IsH4Inner.IP_zero_fst {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (g : Fn) :
    IP (fun _ _ => (0 : ℝ)) g = 0 := by
  rw [h.symm]
  exact h.IP_zero_snd g

theorem IsH4Inner.IP_neg_snd {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g : Fn) :
    IP f (fun z θ => -(g z θ)) = -IP f g := by
  have h1 := h.smul_snd (-1) f g
  have h2 : (fun z θ : ℝ => -(g z θ)) = (fun z θ : ℝ => (-1 : ℝ) * g z θ) := by
    funext z θ; simp
  rw [h2, h1, neg_one_mul]

theorem IsH4Inner.IP_neg_fst {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g : Fn) :
    IP (fun z θ => -(f z θ)) g = -IP f g := by
  rw [h.symm, h.IP_neg_snd g f, h.symm]

theorem IsH4Inner.IP_add_fst {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f₁ f₂ g : Fn) :
    IP (fun z θ => f₁ z θ + f₂ z θ) g = IP f₁ g + IP f₂ g := h.add_fst f₁ f₂ g

theorem IsH4Inner.IP_add_snd {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (f g₁ g₂ : Fn) :
    IP f (fun z θ => g₁ z θ + g₂ z θ) = IP f g₁ + IP f g₂ := h.add_snd f g₁ g₂

/-- The `IP`-pairing of a scalar multiple in the first argument. -/
theorem IsH4Inner.IP_smul_fst {α : ℝ} {IP : Fn → Fn → ℝ} (h : IsH4Inner α IP) (c : ℝ)
    (f g : Fn) : IP (fun z θ => c * f z θ) g = c * IP f g := h.smul_fst c f g

/-! ## The pairing property of an `IP`-orthonormal Galerkin basis -/

/-- **The Galerkin span is `IP`-isometric to `ℝⁿ`.**  This is the *usable* form of the
`IP`-orthonormality of the Galerkin basis `φ`: the pairing of two Galerkin combinations is the
Euclidean pairing of their coefficient vectors.  It is derived from the raw orthonormality
`∀ i j, IP (φ i) (φ j) = if i = j then 1 else 0` by `Projection/ip_galFun_pair`
(the derivation needs no membership hypothesis, since the bilinearity fields of
`Work.Construction.IsH4IP` are unrestricted). -/
def IsIPOrthonormal (IP : Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ (n : ℕ) (d c : Fin n → ℝ), IP (galFun φ d) (galFun φ c) = ∑ k : Fin n, d k * c k

/-- The `k`-th test function has coefficient vector `Pi.single k 1`. -/
theorem galFun_single (φ : ℕ → Fn) {n : ℕ} (k : Fin n) :
    galFun φ (Pi.single k (1 : ℝ)) = φ (k : ℕ) := by
  funext z θ
  simp only [galFun]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Coefficient extraction: the `k`-th coefficient of a Galerkin combination is its `IP`-pairing
with the `k`-th test function. -/
theorem IsIPOrthonormal.coeff {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (h : IsIPOrthonormal IP φ)
    (n : ℕ) (c : Fin n → ℝ) (k : Fin n) : IP (galFun φ c) (φ (k : ℕ)) = c k := by
  have h1 := h n c (Pi.single k (1 : ℝ))
  rw [← galFun_single φ k, h1]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **The energy identity is exact** (audit step 4): for an `IP`-orthonormal Galerkin basis the
`IP`-energy of a Galerkin combination is the Euclidean norm squared of its coefficients. -/
theorem IsIPOrthonormal.self {IP : Fn → Fn → ℝ} {φ : ℕ → Fn} (h : IsIPOrthonormal IP φ)
    (n : ℕ) (c : Fin n → ℝ) :
    IP (galFun φ c) (galFun φ c) = ∑ k : Fin n, (c k) ^ 2 := by
  rw [h n c c]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_sq_nonneg {n : ℕ} (c : Fin n → ℝ) : 0 ≤ ∑ k : Fin n, (c k) ^ 2 :=
  Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The Euclidean norm of the coefficients of a Galerkin profile is controlled by the `ℋ⁴`-norm of
the profile, through the upper bound `IP f f ≤ C |f|²_{ℋ⁴}` of the admissible inner product.  This
is how the a-priori `ℋ⁴`-bound becomes the coefficient-ball bound of the Galerkin ODE. -/
theorem IsIPOrthonormal.sq_sum_le {α : ℝ} {IP : Fn → Fn → ℝ} {φ : ℕ → Fn}
    (h : IsIPOrthonormal IP φ) {C : ℝ}
    (hC : ∀ f : Fn, Coercivity.HkAdm α 4 f → IP f f ≤ C * Spaces.HkSq α 4 f)
    {n : ℕ} (c : Fin n → ℝ) (hadm : Coercivity.HkAdm α 4 (galFun φ c)) :
    ∑ k : Fin n, (c k) ^ 2 ≤ C * (Spaces.HkNorm α 4 (galFun φ c)) ^ 2 := by
  have h1 : IP (galFun φ c) (galFun φ c) ≤ C * Spaces.HkSq α 4 (galFun φ c) := hC _ hadm
  have h2 : C * Spaces.HkSq α 4 (galFun φ c) = C * (Spaces.HkNorm α 4 (galFun φ c)) ^ 2 := by
    rw [Spaces.HkNorm, Real.sq_sqrt (Spaces.HkSq_nonneg α 4 (galFun φ c))]
  rw [h.self, h2] at h1
  exact h1

end Work.FTS.Galerkin
