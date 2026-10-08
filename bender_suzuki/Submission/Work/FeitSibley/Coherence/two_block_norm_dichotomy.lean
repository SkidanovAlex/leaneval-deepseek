import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.CharCore.cfInner_self_vchar_nat
import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.Inner
import Submission.Work.FeitSibley.Coherence.cfInner_bessel
import Submission.Work.FeitSibley.Coherence.sum_normSq_cfInner_eq
import Submission.Work.FeitSibley.Coherence.int_two_block_arith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-block norm dichotomy (Peterfalvi II, Appendice XII, step (7))

`T` is a generalized character of `G` of norm `1 + a²` (`a ≥ 2`), `ρ` is an isometry on the
lattice `ℤ[𝒮(Q')]` and the Fourier coefficients `⟨T, ρ y⟩` take the value `c - a` at the single
point `y₀ ∈ 𝒮(Q')` of the block and the value `c` everywhere else on it.  Since `ρ` is an
isometry and `𝒮(Q')` is orthonormal, Bessel's inequality

`∑_{y ∈ 𝒮(Q')} |⟨T, ρ y⟩|² ≤ ‖T‖² = 1 + a²`

forces `(c - a)² + (|𝒮(Q')| - 1) c² ≤ 1 + a²`; together with `a ∣ c` (proved elsewhere from the
congruence `ψ ≡ ψ(1) mod |Q|`) and `|𝒮(Q')| ≥ 2` this leaves exactly `c = 0`, or `c = a` with
`|𝒮(Q')| = 2`.
-/

set_option linter.unusedVariables false

namespace Work.FeitSibley.Coherence

/-- The abstract form of the two-block norm dichotomy: no group theory enters, only Bessel's
inequality for an orthonormal family (`cfInner_bessel`), the evaluation of the resulting sum
(`sum_normSq_cfInner_eq`) and the integer arithmetic (`int_two_block_arith`). -/
theorem two_block_norm_dichotomy_abstract {G ι : Type*} [Fintype G] [DecidableEq ι]
    (S : Finset ι) (e : ι → G → ℂ) (T : G → ℂ) {y₀ : ι} (hy₀ : y₀ ∈ S)
    {a : ℕ} (ha2 : 2 ≤ a) {c : ℤ} (hadvd : (a : ℤ) ∣ c)
    (horth : ∀ x ∈ S, ∀ y ∈ S, Work.Coherence.cfInner (e x) (e y) = if x = y then 1 else 0)
    (hTnorm : Work.Coherence.cfInner T T = 1 + (a : ℂ) ^ 2)
    (hc : ∀ y ∈ S, Work.Coherence.cfInner T (e y) =
      if y = y₀ then (c : ℂ) - (a : ℂ) else (c : ℂ))
    (hcard : 2 ≤ S.card) :
    c = 0 ∨ (c = (a : ℤ) ∧ S.card = 2) := by
  classical
  -- Bessel's inequality for the orthonormal family `e` on `S`
  have hb := cfInner_bessel S e T horth
  -- the sum of the squared moduli of the Fourier coefficients, evaluated
  have hs := sum_normSq_cfInner_eq S e T hy₀ c a hc
  -- `‖T‖²` is the integer `1 + a²`
  have hT : (Work.Coherence.cfInner T T).re = (((1 + (a : ℤ) ^ 2 : ℤ)) : ℝ) := by
    rw [hTnorm]
    have h1 : (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + (a : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.ofReal_re]
    push_cast
    ring
  have hineqR : (((c - (a : ℤ)) ^ 2 + ((S.card : ℤ) - 1) * c ^ 2 : ℤ) : ℝ)
      ≤ (((1 + (a : ℤ) ^ 2 : ℤ)) : ℝ) := by
    rw [← hs, ← hT]
    exact hb
  have hineq : (c - (a : ℤ)) ^ 2 + ((S.card : ℤ) - 1) * c ^ 2 ≤ 1 + (a : ℤ) ^ 2 :=
    Int.cast_le.mp hineqR
  have hz := int_two_block_arith (a := (a : ℤ)) (c := c) (n := (S.card : ℤ))
    (by exact_mod_cast hcard) (by exact_mod_cast ha2) hadvd hineq
  rcases hz with h0 | ⟨h1, h2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, by exact_mod_cast h2⟩

theorem two_block_norm_dichotomy {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {T : G → ℂ} (hTV : Work.Coherence.IsVChar T)
    {ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hρiso : Work.Coherence.IsometryOnAll
      (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h)) ρ)
    {y₀ : ↥h.H → ℂ}
    (hy₀ : y₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h))
    {a : ℕ} (ha2 : 2 ≤ a) {c : ℤ} (hadvd : (a : ℤ) ∣ c)
    (hTnorm : Work.Coherence.cfInner T T = 1 + (a : ℂ)^2)
    (hc : ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
        Work.Coherence.cfInner T (ρ y) = if y = y₀ then (c : ℂ) - (a : ℂ) else (c : ℂ))
    (hcard : 2 ≤ (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h)).card) :
    c = 0 ∨ (c = (a : ℤ) ∧
      (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h)).card = 2) := by
  classical
  -- `ρ` is an isometry on `ℤ[𝒮(Q')]` and `𝒮(Q')` is orthonormal, so the images `ρ y` are
  -- orthonormal as well
  have horth : ∀ x ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      Work.Coherence.cfInner (ρ x) (ρ y) = if x = y then 1 else 0 := by
    intro x hx y hy
    rw [hρiso.inner_eq x (Work.Coherence.self_mem_zSpan hx) y
      (Work.Coherence.self_mem_zSpan hy)]
    exact scriptSR_Qcomm_orthonormal h x hx y hy
  exact two_block_norm_dichotomy_abstract
    (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h))
    (fun y => ρ y) T hy₀ ha2 hadvd horth hTnorm hc hcard

end Work.FeitSibley.Coherence
