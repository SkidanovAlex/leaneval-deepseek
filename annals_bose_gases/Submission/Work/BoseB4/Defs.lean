import Mathlib.Analysis.InnerProductSpace.l2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Defs` — the bosonic Fock space over `Λ` with the condensate mode singled out

This is the foundational module of node **B4** of `BOSE_AUDIT_LEAD.md` §4: FS §8,
*second quantisation*.  FS work on `𝓕_s(L²(Λ))`, the bosonic Fock space over the
box `Λ`, and single out the **condensate mode** `θ = ℓ^{-3/2}χ_Λ`, so that

    𝓕(L²(Λ)) = 𝓕(ℂθ) ⊗ 𝓕(θ^⊥),

with `a₀ = a(θ)` acting on the first factor and every `a_k`, `k ≠ 0` acting on the
second (because `Q(e^{ikx}χ_Λ) ⊥ θ`, `Q = 1 - P` the projection off the constants).
`thm:Kafz` (the `c`-number substitution) is a statement about the first factor
alone, so we model *exactly* that factor and leave the second abstract:

* `Fock E` — the Hilbert sum `⨁_{n∈ℕ} E`, the `n`-th summand being the subspace
  of the Fock space with `n` condensate quanta.  `E` plays the role of
  `𝓕(θ^⊥)` (the "spectator" space); it is an arbitrary complex Hilbert space.
* `FockCore E = ℕ →₀ E` — the algebraic (finite condensate occupation) core.  All
  of FS §8–§11 is applied to states of *finitely many particles*, which always
  lie in the core, so this is where the operators live (they are unbounded on
  `Fock E`).
* `Embed : FockCore E →ₗ[ℂ] Fock E` — the inclusion, so that inner products can
  be taken.
* `a0`, `a0d` — condensate annihilation/creation `a₀`, `a₀†`, and `numOp = a0d∘a0`
  the condensate number operator `n₀ = a₀†a₀`.
* `lift B` — the levelwise action of an operator on the spectator space.

Conventions (fixed here for the whole chapter):

* `a0` (annihilation) lowers the condensate number: `(a0 Ψ) n = √(n+1) • Ψ (n+1)`;
* `a0d` (creation) raises it: `(a0d Ψ) n = √n • Ψ (n-1)`;
* hence `[a0, a0d] = 1` and `n₀ (e_n ⊗ v) = n • (e_n ⊗ v)`, with `e_n` the
  `n`-th condensate level.  This is the standard normalisation in which the
  level-`n` vector `e_n` has norm `√(n!)`.

The coherent-state (`c`-number substitution) layer lives in
`Submission/Work/BoseB4/Coherent.lean`.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 0. The square roots -/

/-- `√n` as a complex scalar (the coefficient `√n` of the Fock ladder). -/
noncomputable def sq (n : ℕ) : ℂ := ((Real.sqrt (n : ℝ) : ℝ) : ℂ)

@[simp] lemma sq_zero : sq 0 = 0 := by simp [sq]
@[simp] lemma sq_one : sq 1 = 1 := by simp [sq]

lemma sq_mul_sq (m : ℕ) : sq m * sq m = (m : ℂ) := by
  have h : ((Real.sqrt (m : ℝ) : ℝ) : ℂ) * ((Real.sqrt (m : ℝ) : ℝ) : ℂ)
      = ((m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  simpa [sq] using h

/-! ## 1. The Fock space and its algebraic core -/

/-- The **bosonic Fock space** over `ℂθ ⊕ 𝔥` with the condensate mode `θ` singled
out: the Hilbert sum `⨁_{n ∈ ℕ} E` over the number `n` of condensate quanta, where
`E` is the Fock space of the non-condensate modes (`E = 𝓕(θ^⊥)`). -/
abbrev Fock (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Type _ :=
  lp (fun _ : ℕ => E) 2

/-- The **algebraic core** of the Fock space: finitely many condensate quanta.
Equivalently the algebraic direct sum `⨁_{n∈ℕ} E`. -/
abbrev FockCore (E : Type*) [Zero E] := ℕ →₀ E

/-- The `n`-th **condensate level** `e_n ⊗ E`, as a linear isometry into `Fock E`. -/
noncomputable def level (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) : E →L[ℂ] Fock E :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => E) 2 n

/-- The inclusion of the algebraic core into the Fock space, `∑ₙ lp.single n (Ψ n)`. -/
noncomputable def Embed (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    FockCore E →ₗ[ℂ] Fock E :=
  Finsupp.lsum ℂ fun n : ℕ => lp.singleContinuousLinearMap ℂ (fun _ : ℕ => E) 2 n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma Embed_single (n : ℕ) (v : E) :
    Embed E (Finsupp.single n v) = level E n v :=
  Finsupp.lsum_single _ _ _ _

lemma Embed_eq_sum (Ψ : FockCore E) :
    (Embed E Ψ : Fock E) = ∑ m ∈ Ψ.support, lp.single 2 m (Ψ m) := rfl

lemma Embed_apply (Ψ : FockCore E) (n : ℕ) :
    ((Embed E Ψ : Fock E) : ℕ → E) n = Ψ n := by
  rw [Embed_eq_sum, lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single n]
  · rw [lp.coeFn_single, Pi.single_apply, if_pos rfl]
  · intro m _ hm
    rw [lp.coeFn_single, Pi.single_apply, if_neg (Ne.symm hm)]
  · intro hn
    rw [lp.coeFn_single, Pi.single_apply, if_pos rfl]
    simpa [Finsupp.mem_support_iff] using hn

lemma Embed_injective : Function.Injective (Embed E) := by
  intro Ψ Ψ' h
  ext n
  have := congrFun (congrArg (fun f : Fock E => (f : ℕ → E)) h) n
  simpa [Embed_apply] using this

/-- The **core inner product**: the Fock inner product of the images under `Embed`. -/
noncomputable def coreInner (Ψ Ψ' : FockCore E) : ℂ :=
  inner ℂ (Embed E Ψ) (Embed E Ψ')

lemma coreInner_eq_tsum (Ψ Ψ' : FockCore E) :
    coreInner Ψ Ψ' = ∑' n : ℕ, inner ℂ (Ψ n) (Ψ' n) := by
  rw [coreInner, lp.inner_eq_tsum]
  exact tsum_congr fun n => by rw [Embed_apply, Embed_apply]

/-! ## 2. Condensate creation and annihilation -/

/-- Condensate **annihilation** `a₀`: `(a0 Ψ) n = √(n+1) • Ψ (n+1)`. -/
noncomputable def a0 : FockCore E →ₗ[ℂ] FockCore E :=
  Finsupp.lsum ℂ fun n : ℕ =>
    (Finsupp.lsingle (n - 1)).comp (sq n • (1 : E →ₗ[ℂ] E))

/-- Condensate **creation** `a₀†`: `(a0d Ψ) n = √n • Ψ (n-1)`. -/
noncomputable def a0d : FockCore E →ₗ[ℂ] FockCore E :=
  Finsupp.lsum ℂ fun n : ℕ =>
    (Finsupp.lsingle (n + 1)).comp (sq (n + 1) • (1 : E →ₗ[ℂ] E))

@[simp]
lemma a0_single (n : ℕ) (v : E) :
    a0 (Finsupp.single n v) = Finsupp.single (n - 1) (sq n • v) := by
  rw [a0, Finsupp.lsum_single]
  rfl

@[simp]
lemma a0d_single (n : ℕ) (v : E) :
    a0d (Finsupp.single n v) = Finsupp.single (n + 1) (sq (n + 1) • v) := by
  rw [a0d, Finsupp.lsum_single]
  rfl

lemma a0_single_apply (a : ℕ) (b : E) (n : ℕ) :
    a0 (Finsupp.single a b) n = sq (n + 1) • (Finsupp.single a b) (n + 1) := by
  rw [a0_single]
  rcases a with _ | a
  · rw [Finsupp.single_eq_of_ne (by omega : (n + 1 : ℕ) ≠ 0)]
    simp
  · rw [Nat.succ_sub_one]
    by_cases h : n = a
    · subst h
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (by omega : (n : ℕ) ≠ a),
        Finsupp.single_eq_of_ne (by omega : (n + 1 : ℕ) ≠ a + 1), smul_zero]

lemma a0d_single_apply (a : ℕ) (b : E) (n : ℕ) :
    a0d (Finsupp.single a b) n = sq n • (Finsupp.single a b) (n - 1) := by
  rw [a0d_single]
  rcases n with _ | n
  · rw [Finsupp.single_eq_of_ne (by omega : (0 : ℕ) ≠ a + 1)]
    simp
  · rw [Nat.add_sub_cancel]
    by_cases h : a = n
    · subst h
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (by omega : (n : ℕ) ≠ a),
        Finsupp.single_eq_of_ne (by omega : (n + 1 : ℕ) ≠ a + 1), smul_zero]

lemma a0_apply (Ψ : FockCore E) (n : ℕ) : a0 Ψ n = sq (n + 1) • Ψ (n + 1) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, smul_add]
  | single a b => exact a0_single_apply a b n

lemma a0d_apply (Ψ : FockCore E) (n : ℕ) : a0d Ψ n = sq n • Ψ (n - 1) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, smul_add]
  | single a b => exact a0d_single_apply a b n

/-- The condensate **number operator** `n₀ = a₀†a₀`. -/
noncomputable def numOp : FockCore E →ₗ[ℂ] FockCore E := a0d.comp a0

lemma numOp_apply (Ψ : FockCore E) (n : ℕ) : numOp Ψ n = (n : ℂ) • Ψ n := by
  rw [numOp, LinearMap.comp_apply, a0d_apply, a0_apply]
  rcases n with _ | m
  · simp
  · have hidx : (m + 1 - 1) + 1 = m + 1 := by omega
    rw [hidx, smul_smul, sq_mul_sq]

/-- **The canonical commutation relation** `[a₀, a₀†] = 1` on the core. -/
lemma ccr : a0.comp a0d = a0d.comp a0 + (1 : FockCore E →ₗ[ℂ] FockCore E) := by
  refine LinearMap.ext fun Ψ => Finsupp.ext fun n => ?_
  have h1 : ((1 : FockCore E →ₗ[ℂ] FockCore E) Ψ) n = Ψ n := by simp
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Finsupp.add_apply]
  rw [h1]
  rw [a0_apply, a0d_apply, a0d_apply, a0_apply]
  rw [Nat.add_sub_cancel, smul_smul, smul_smul]
  rcases n with _ | m
  · simp
  · have hidx : (m + 1 - 1) + 1 = m + 1 := by omega
    rw [hidx, sq_mul_sq, sq_mul_sq]
    rw [show (((m + 1 + 1 : ℕ)) : ℂ) = ((m : ℂ) + 1 + 1) by push_cast; ring]
    rw [add_smul, one_smul]
    rw [show ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) by push_cast; ring]

/-! ## 3. Lifting spectator operators -/

/-- The levelwise lift of a linear map on the spectator space: `(lift B Ψ) n = B (Ψ n)`.
`B` need not be continuous: on the algebraic core this is a genuine linear map. -/
noncomputable def lift (B : E →ₗ[ℂ] E) : FockCore E →ₗ[ℂ] FockCore E :=
  Finsupp.lsum ℂ fun n : ℕ => (Finsupp.lsingle n).comp B

@[simp]
lemma lift_single (B : E →ₗ[ℂ] E) (n : ℕ) (v : E) :
    lift B (Finsupp.single n v) = Finsupp.single n (B v) := by
  rw [lift, Finsupp.lsum_single]
  rfl

lemma lift_apply (B : E →ₗ[ℂ] E) (Ψ : FockCore E) (n : ℕ) : lift B Ψ n = B (Ψ n) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, map_add]
  | single a b =>
    rw [lift_single]
    by_cases h : n = a
    · subst h; simp
    · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, map_zero]

@[simp]
lemma lift_add (B B' : E →ₗ[ℂ] E) : lift (B + B') = lift B + lift B' := by
  ext Ψ n
  simp

@[simp]
lemma lift_smul (c : ℂ) (B : E →ₗ[ℂ] E) : lift (c • B) = c • lift B := by
  ext Ψ n
  simp

@[simp]
lemma lift_comp (B B' : E →ₗ[ℂ] E) : lift (B.comp B') = (lift B).comp (lift B') := by
  ext Ψ n
  simp

lemma lift_comm_a0d (B : E →ₗ[ℂ] E) : (lift B).comp a0d = a0d.comp (lift B) := by
  ext Ψ n
  simp

lemma lift_comm_a0 (B : E →ₗ[ℂ] E) : (lift B).comp a0 = a0.comp (lift B) := by
  ext Ψ n
  simp

/-! ## 4. Powers and the anti-normal monomials -/

/-- `a₀^p` (`p`-fold condensate annihilation) on the core. -/
noncomputable def a0pow : ℕ → FockCore E →ₗ[ℂ] FockCore E
  | 0 => 1
  | p + 1 => (a0pow p).comp a0

/-- `(a₀†)^p` (`p`-fold condensate creation) on the core. -/
noncomputable def a0dpow : ℕ → FockCore E →ₗ[ℂ] FockCore E
  | 0 => 1
  | p + 1 => (a0dpow p).comp a0d

@[simp] lemma a0pow_zero : a0pow (E := E) 0 = 1 := rfl
@[simp] lemma a0pow_succ (p : ℕ) : a0pow (E := E) (p + 1) = (a0pow p).comp a0 := rfl
@[simp] lemma a0dpow_zero : a0dpow (E := E) 0 = 1 := rfl
@[simp] lemma a0dpow_succ (p : ℕ) : a0dpow (E := E) (p + 1) = (a0dpow p).comp a0d := rfl

/-- FS's **anti-normal monomial** `a₀^p (a₀†)^q` with spectator operator `B`
inserted in the middle, on the algebraic core.  Every operator of FS §8–§11
(`eq:HLambdaSecond`, `eq:Kz`) is a finite sum of these. -/
noncomputable def monoOp (p q : ℕ) (B : E →ₗ[ℂ] E) : FockCore E →ₗ[ℂ] FockCore E :=
  (a0pow p).comp ((a0dpow q).comp (lift B))

/-- The **anti-Wick symbol** of `monoOp p q B` at the coherent parameter `z`:
the substitution rule `a₀^p(a₀†)^q ⊗ B ↦ z^p z̄^q B` of FS `eq:subst-z`, on the
spectator space. -/
noncomputable def symbol (p q : ℕ) (B : E →ₗ[ℂ] E) (z : ℂ) : E →ₗ[ℂ] E :=
  (z ^ p * (starRingEnd ℂ z) ^ q) • B

end Work.BoseB4
