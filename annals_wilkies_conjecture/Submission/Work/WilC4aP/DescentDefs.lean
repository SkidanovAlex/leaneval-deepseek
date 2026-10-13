/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): vocabulary for the
  Newton-polygon (descent) proof of the complex Puiseux theorem
  (`Work.WilC4aP.complex_puiseux_descent`).

  The descent proves, by strong induction on the degree, that a monic polynomial with
  holomorphic coefficients at `0` has its roots given by finitely many functions holomorphic
  at `0` after some ramification `s = u ^ N`.  Because every intermediate step only produces
  identities valid in a neighbourhood of `u = 0` (and the radius shrinks at each step), it is
  convenient to record the factorization as an *eventual* statement (`FactoredNear`); it is
  converted into the ball-wise `FactoredOn` of `Submission.Work.WilC4aP.Basic` at the very end.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false
noncomputable section

open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- **Eventual factorization.** Near `u = 0` the fibre of `P` over the ramification
`s = u ^ N` is the product of the linear factors `X - η j u`. -/
def FactoredNear {m : ℕ} (P : Polynomial (ℂ → ℂ)) (N : ℕ) (η : Fin m → ℂ → ℂ) : Prop :=
  ∀ᶠ u in 𝓝 (0 : ℂ), Pz P (u ^ N) = ∏ j, (X - C (η j u))

/-- **The complex Puiseux statement, in germ form**: the branches are holomorphic at `0` and
the factorization holds near `0`.  This is the form proved by the descent; it implies
`ComplexPuiseux` by shrinking the radius. -/
def ComplexPuiseuxGerm : Prop :=
  ∀ {m : ℕ} (P : Polynomial (ℂ → ℂ)), P.Monic → P.natDegree = m → HolCoeffs P 0 →
    ∃ (N : ℕ) (η : Fin m → ℂ → ℂ), 0 < N ∧ (∀ j, AnalyticAt ℂ (η j) 0) ∧ FactoredNear P N η

/-- The monomial `t ↦ t ^ a`, as a coefficient function. -/
def tpow (a : ℕ) : ℂ → ℂ := fun t => t ^ a

@[simp] lemma tpow_apply (a : ℕ) (t : ℂ) : tpow a t = t ^ a := rfl

/-- Substitution of `t ↦ t ^ q` into a coefficient function, as a ring homomorphism. -/
def powComp (q : ℕ) : (ℂ → ℂ) →+* (ℂ → ℂ) where
  toFun f := f ∘ tpow q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma powComp_apply (q : ℕ) (f : ℂ → ℂ) : powComp q f = f ∘ tpow q := rfl

/-- The family of branches of a product `G * H`: the `k` branches of `G` (taken at `u ^ N₂`)
followed by the `m - k` branches of `H` (taken at `u ^ N₁`). -/
def prodFamily {m k : ℕ} (hkm : k + (m - k) = m) (N₁ N₂ : ℕ) (η₁ : Fin k → ℂ → ℂ)
    (η₂ : Fin (m - k) → ℂ → ℂ) : Fin m → ℂ → ℂ :=
  fun j => Sum.elim (fun i => fun u => η₁ i (u ^ N₂)) (fun i => fun u => η₂ i (u ^ N₁))
    (finSumFinEquiv.symm (Fin.cast hkm.symm j))

/-- If `f` is analytic at `0`, so is `u ↦ f (u ^ N)` for `N > 0`. -/
lemma AnalyticAt.comp_pow' {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {N : ℕ} (hN : 0 < N) :
    AnalyticAt ℂ (fun u : ℂ => f (u ^ N)) 0 :=
  AnalyticAt.comp_of_eq (g := f) (f := fun u : ℂ => u ^ N) (y := 0) (x := 0) hf
    (analyticAt_id.pow N) (zero_pow hN.ne')

/-- Every member of `prodFamily` is analytic at `0` when the members of `η₁` and `η₂` are. -/
theorem prodFamily_analytic {m k N₁ N₂ : ℕ} (hkm : k + (m - k) = m) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) {η₁ : Fin k → ℂ → ℂ} {η₂ : Fin (m - k) → ℂ → ℂ}
    (h₁ : ∀ j, AnalyticAt ℂ (η₁ j) 0) (h₂ : ∀ j, AnalyticAt ℂ (η₂ j) 0) :
    ∀ j, AnalyticAt ℂ (prodFamily hkm N₁ N₂ η₁ η₂ j) 0 := by
  intro j
  show AnalyticAt ℂ (Sum.elim (fun i : Fin k => fun u : ℂ => η₁ i (u ^ N₂))
    (fun i : Fin (m - k) => fun u : ℂ => η₂ i (u ^ N₁))
    (finSumFinEquiv.symm (Fin.cast hkm.symm j))) 0
  rcases e : finSumFinEquiv.symm (Fin.cast hkm.symm j) with i | i
  · change AnalyticAt ℂ (fun u : ℂ => η₁ i (u ^ N₂)) 0
    exact AnalyticAt.comp_pow' (h₁ i) hN₂
  · change AnalyticAt ℂ (fun u : ℂ => η₂ i (u ^ N₁)) 0
    exact AnalyticAt.comp_pow' (h₂ i) hN₁

end Work.WilC4aP
