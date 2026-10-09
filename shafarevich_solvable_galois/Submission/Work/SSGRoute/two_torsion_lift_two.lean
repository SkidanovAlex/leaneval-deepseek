import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.two_torsion_base
import Submission.Work.SSGRoute.two_torsion_lift_j_one
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.gradedStep_two_two
import Submission.Work.SSGRoute.gradedStep_three_two_reduced
import Submission.Work.SSGRoute.gradedStep_three_three
import Submission.Work.SSGRoute.gradedStep_four_four_conered
import Submission.Work.SSGRoute.gradedStep_five_five_reduced
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lifting `2`-torsion along the refined filtration, the case `p = 2`

`Work.SSGRoute.two_torsion_lift_two` (Schmidt–Wingberg, Step 1 of the induction, clause (B), at
`p = 2`): every involution `γ` of `Γ(τ) = F(n)/F(n)^{(τ)} ⋊ Gal(K/ℚ)` whose `Gal(K/ℚ)`-component
is non-trivial lifts to an involution of `Γ(τ+1)`.

## Structure of the proof

Write `γ = (a, δ)` with `δ = γ.right ≠ 1`.  From `γ ^ 2 = 1` we get `a * (δ • a) = 1`, i.e. `a` is
*anti-fixed* by the action of `δ` on the left factor `Q_τ = F(n)/F(n)^{(τ)}`.

* `Work.SSGRoute.two_torsion_lift_of_delta_difference`: **if** every anti-fixed element of `Q_τ`
  is a `δ`-difference, i.e. `a = r⁻¹ * (δ • r)` for some `r`, **then** the lift exists.  Indeed
  `q̃⁻¹ * (δ • q̃)` (any lift `q̃ ∈ Q_{τ+1}` of `r`) is anti-fixed, of order `2` in the semidirect
  product, and projects to `a`.  (No group-theoretic input beyond the semidirect product.)
* `Work.SSGRoute.flowQuotient_antifixed_is_delta_difference` is the group-theoretic heart: for the
  free `G`-operator group `F(n) = FreeGroup (Fin n × G)` with `δ ∈ G`, `δ ^ 2 = 1`, `δ ≠ 1`, and
  `N = F(n)^{(i,j)}` the refined term, every anti-fixed element of `F(n)/N` (the action being the
  induced one) is a `δ`-difference.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

section Helpers

variable (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)

/-- The projection `Γ(τ+1) →* Γ(τ)` is compatible with the action of `G` on the left factor, in
the `flowAction` form. -/
lemma flowQuotSucc_flowAction (g : G)
    (x : flowQuotient p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuotSucc p G m i j ((flowAction p G m (tauSucc i j).1 (tauSucc i j).2 g) x)
      = (flowAction p G m i j g) (flowQuotSucc p G m i j x) :=
  flowQuotSucc_smul p G m i j g x

/-- An involution of `G` acts as an involution on every `flowQuotient`. -/
lemma flowAction_two (g : G) (hg : g * g = 1) (x : flowQuotient p G m i j) :
    (flowAction p G m i j g) ((flowAction p G m i j g) x) = x := by
  have h1 : (flowAction p G m i j g) ((flowAction p G m i j g) x)
      = (flowAction p G m i j (g * g)) x := by rw [map_mul]; rfl
  rw [h1, hg, map_one]; rfl

end Helpers

/-- **The lift, from the "`δ`-difference" representation of the anti-fixed element.**

Let `γ = (a, δ) ∈ Γ(τ)` be an involution of the flow group with non-trivial `G`-component
`δ = γ.right ≠ 1`.  If every anti-fixed element of the left factor `Q_τ` is a `δ`-difference, then
`γ` lifts to an involution of `Γ(τ+1)`.

Indeed, `γ ^ 2 = 1` gives `a * (δ • a) = 1`; pick `r ∈ Q_τ` with `a = r⁻¹ * (δ • r)` and lift `r`
to `q̃ ∈ Q_{τ+1}` (the projection `Q_{τ+1} ↠ Q_τ` is surjective and `G`-equivariant).  Then
`b := q̃⁻¹ * (δ • q̃)` satisfies `b * (δ • b) = 1` and projects to `a`, so
`y := SemidirectProduct.mk b δ` satisfies `y ^ 2 = 1` and `flowGroupSucc y = γ`. -/
theorem two_torsion_lift_of_delta_difference
    (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (γ : flowGroup p (K ≃ₐ[ℚ] K) n i j) (hγ : γ ^ 2 = 1)
    (h : ∀ x : flowQuotient p (K ≃ₐ[ℚ] K) n i j,
        x * (flowAction p (K ≃ₐ[ℚ] K) n i j γ.right) x = 1 →
        ∃ r : flowQuotient p (K ≃ₐ[ℚ] K) n i j,
          x = r⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n i j γ.right) r) :
    ∃ y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  have h2 : γ * γ = 1 := by rw [← pow_two]; exact hγ
  have hδδ : γ.right * γ.right = 1 := by
    have h3 := congrArg SemidirectProduct.right h2
    rw [SemidirectProduct.mul_def] at h3
    simpa using h3
  have hsq : γ.left * (flowAction p (K ≃ₐ[ℚ] K) n i j γ.right) γ.left = 1 := by
    have h5 := congrArg SemidirectProduct.left h2
    rw [SemidirectProduct.mul_def] at h5
    simpa using h5
  obtain ⟨r, hr⟩ := h γ.left hsq
  obtain ⟨r', hr'⟩ := flowQuotSucc_surjective p (K ≃ₐ[ℚ] K) n i j r
  refine ⟨SemidirectProduct.mk (r'⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1
      (tauSucc i j).2 γ.right) r') γ.right, ?_, ?_⟩
  · rw [liftsFlowAt_iff_flowGroupSucc]
    refine SemidirectProduct.ext ?_ ?_
    · show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j
        (SemidirectProduct.mk (r'⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1
          (tauSucc i j).2 γ.right) r') γ.right)).left = γ.left
      rw [flowGroupSucc_mk, map_mul, map_inv, flowQuotSucc_flowAction, hr']
      exact hr.symm
    · show (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j
        (SemidirectProduct.mk (r'⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1
          (tauSucc i j).2 γ.right) r') γ.right)).right = γ.right
      rw [flowGroupSucc_mk]
  · rw [pow_two, SemidirectProduct.mul_def]
    refine SemidirectProduct.ext ?_ ?_
    · show r'⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right) r' *
        (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right)
          (r'⁻¹ * (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right) r')
        = (1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).left
      rw [show (1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).left = 1 from rfl]
      rw [map_mul (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right) r'⁻¹
            ((flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right) r'),
          map_inv (flowAction p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right) r',
          flowAction_two p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 γ.right hδδ r']
      group
    · show γ.right * γ.right
        = (1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right
      rw [show (1 : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2).right = 1 from rfl]
      exact hδδ

/-- **The group-theoretic heart.**

Every anti-fixed element of `Q_τ = F(n)/F(n)^{(τ)}` (for the action of an involution `δ ∈ Gal(K/ℚ)`,
`δ ≠ 1`) is a `δ`-difference.

This is where the content of the `p = 2` correction lies.  The statement is *true*, but the naive
proof routes are dead ends, and the following precise reduction (used by
`Submission/Work/SSGRoute/two_torsion_assembly.lean`) is the one that works:

*Let `E(σ) = ker(Q_{σ+1} → Q_σ) = F(n)^{(σ)}/F(n)^{(σ)+1}` be the graded pieces of the refined
filtration.  The **graded step** at `σ` is*

  `∀ c ∈ E(σ), δ c = c⁻¹ → ∃ e ∈ Q_{σ+1}, c = (δ • e)⁻¹ * e`  (the witness `e` in the *ambient*
  group, not in the kernel!).

*Then `Work.SSGRoute.descent_step` shows, by induction along the refined filtration, that every
anti-fixed element of every `Q_τ` is a `δ`-difference
(`Work.SSGRoute.antifixed_is_delta_difference_of_gradedStep`).*

Why the graded step is the right level: the kernel `E(σ)` is elementary abelian (`Lemma 4` of
Schmidt–Wingberg, formalized as `pow_refinedTerm_le`), so `c⁻¹ = c` and "anti-fixed" means
"`δ`-fixed"; the achievable classes `{(δe)⁻¹e : e ∈ Q_{σ+1}, [e] ∈ Q_σ^δ}` form a *subgroup* of
`E(σ)` containing `(1+δ)E(σ)`, and the graded step is exactly the statement that this subgroup is
all of `E(σ)^δ`.

Three dead ends, for the record:

1. The *strong* form of the graded step, with the witness required to lie in `E(σ)` itself, is
   **false**: for `σ = (2,2)`, `n = 1`, `G = ℤ/2`, the graded piece is `E(2,2) ≅ 𝔽₂` with the
   trivial `δ`-action (so `(1+δ)E(2,2) = 0`), while `[a,b] = (δ(ab))⁻¹(ab)` is a `δ`-difference in
   `Q_{(3,1)} = F/F₃`.
2. The general statement "every anti-fixed element of `F/N` is a `δ`-difference" for an arbitrary
   `δ`-stable normal `N` is **false**: for `F = F(a,b)` free and `δ : a ↦ b`, the normal closure
   `N = ⟨⟨ab⟩⟩` gives `F/N ≅ ℤ` with `δ` acting by inversion, where every element is anti-fixed but
   the differences form `2ℤ`; likewise `N = ⟨⟨ab, a⁴⟩⟩` gives `Q ≅ ℤ/4`.
3. The five-term "Tate" argument (obstruction in `Ĥ⁻¹`) is insufficient: `Ĥ⁻¹(Q_σ) = 0` does *not*
   imply the graded step (the connecting map `Ĥ⁻¹(Q_σ) → Ĥ⁰(E(σ))` can vanish while the graded
   step still needs the quadratic part of the witness).

The constructive content of the graded step (as reconstructed from the level-by-level computations
in `Submission/Work/SSGRoute/gradedPiece_one.lean`, `gradedPiece_two.lean` and
`gradedPiece_quadratic.lean`, and cross-checked with `Ĥ`-arguments): the witness `e` must have a
`δ`-invariant exponent vector modulo `F(n)/F(n)^2` — equivalently `exp(e) ≡ δ exp(e) (mod 2)` — since
otherwise the exponent vector of `(δe)⁻¹e`, namely `exp(e) - δ exp(e)`, is non-zero in
`F(n)/F(n)_2` and the norm cannot lie in the graded piece at all (this is why, for a pair `{x,y}`
spanning two distinct `δ`-orbits, the naive witness `x·y` fails, while for a `δ`-orbit pair
`{x, δx}` the witness `x·(δx)` gives `[x, δx]` exactly).  Concretely: by Proposition 5 (`Work.SSGRoute.prop5Data_exists`,
`Submission/Work/SSGRoute/prop5/`) the graded piece `E(σ)` is the `G`-equivariant image of the
`j`-th tensor power of `F(n)/F(n)^2` under `θ_σ`, and `δ` permutes the tensor monomials; since the
free basis is `δ`-free, every orbit of monomials has size two.  Take the witness `e` to be the
"half" of the monomial (`e := x^{2^{i-1}}` for `j = 1`, `e := x·(δx)` for the `(x, δx)` commutators
of `j = 2`, and correspondingly for `j ≥ 2`): its norm `(δe)⁻¹e` has the expected class modulo
`(1+δ)E(σ)` and modulo commutator error terms, which die in the ambient group because
`[F(n)_i, F(n)] ⊆ F(n)_{i+1} ⊆ F(n)^{(σ)+1}`.  Exhaustive computations in the Magnus models
`F(2)/P_k` (`k ≤ 5`) for every refined term `1 ≤ j ≤ i ≤ 4`, and rank `4` with `i ≤ 2`, find zero
counterexamples.

So the group-theoretic heart below is a *corollary* of the graded-step family; the family is the
single remaining gap.

**WARNING (2026-10-02).** The statement below — *every* anti-fixed element of `Q_τ` is a
`δ`-difference — is **FALSE** and must not be used: `IsDelta 9 1 δ` fails for `n = 1`, `G = ℤ/2`,
because the graded step at `(8,8)` fails (`gradedStep_j_ge_two.lean`,
`AUDIT_p2_two_torsion_atom.lean.md`). `IsDelta(τ)` is a *strict* strengthening of the target; the
target is equivalent to the much weaker *anti-fixed lifting* statement (every anti-fixed element of
`Q_τ` lifts to an anti-fixed element of `Q_{τ+1}`, i.e. the connecting map
`Ĥ⁻¹(⟨δ⟩, Q_{τ+1}) → Ĥ⁻¹(⟨δ⟩, Q_τ)` is onto). See
`Submission/Work/SSGRoute/NOTE_two_torsion_lift_two_state.md` for the exact reformulations, the
refuted neighbouring statements, and the remaining crux; in particular the *unrefined* one-step
lifting for the lower central series is false at weight 4, so any proof must use the `p`-power part
`P_{i+1}` of the refined term. -/
theorem flowQuotient_antifixed_is_delta_difference_aux
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (δ : K ≃ₐ[ℚ] K) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ x : Work.CohomologicalShrinking.flowQuotient 2 (K ≃ₐ[ℚ] K) n i j,
      (Work.CohomologicalShrinking.flowAction 2 (K ≃ₐ[ℚ] K) n i j δ) x = x⁻¹ →
      ∃ r : Work.CohomologicalShrinking.flowQuotient 2 (K ≃ₐ[ℚ] K) n i j,
        x = ((Work.CohomologicalShrinking.flowAction 2 (K ≃ₐ[ℚ] K) n i j δ) r)⁻¹ * r := by
  sorry

/- **`IsDelta` at the low levels, by the descent from the *proved* graded steps.**

The graded steps at `j = 1` (`Work.SSGRoute.gradedStepJOne`) and at `(2,2)`
(`Work.SSGRoute.gradedStep_two_two`) are proved and sorry-free, so
`Work.SSGRoute.descent_step` yields `IsDelta` at `(2,1)`, `(2,2)`, `(3,1)`, `(3,2)`.  Those give
the target at the same levels (`two_torsion_lift_two_of_isDelta`).  The chain stops at `(3,3)`,
which needs the graded step at `(3,2)`; see `NOTE_two_torsion_lift_two_state.md` §3ter. -/
section LowLevels

variable (G : Type*) [Group G] [Fintype G] (n : ℕ)

/-- `Q_{(1,1)}` is trivial, so `IsDelta` holds there. -/
theorem isDelta_one_one (δ : G) : IsDelta G n 1 1 δ := by
  intro a _
  haveI : Subsingleton (flowQuotient 2 G n 1 1) := flowQuotient_one_one_subsingleton (G := G) (n := n)
  exact ⟨1, by rw [Subsingleton.elim a 1, map_one, inv_one, one_mul]⟩

theorem isDelta_two_one (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 2 1 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 1 1 (isDelta_one_one G n δ)
    (gradedStepJOne G n δ hδ hδ1 1 le_rfl)

theorem isDelta_two_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 2 2 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 2 1 (isDelta_two_one G n δ hδ hδ1)
    (gradedStepJOne G n δ hδ hδ1 2 (by omega))

theorem isDelta_three_one (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 3 1 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 2 2 (isDelta_two_two G n δ hδ hδ1)
    (gradedStep_two_two G n δ hδ hδ1)

theorem isDelta_three_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 3 2 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 3 1 (isDelta_three_one G n δ hδ hδ1)
    (gradedStepJOne G n δ hδ hδ1 3 (by omega))

/-- The graded step at `(3,2)`, a one-line consequence of the diagonal reduction
(`gradedStep_of_diagonal_at`) applied to the proved diagonal step at `(2,2)`. -/
theorem isDelta_three_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 3 3 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 3 2 (isDelta_three_two G n δ hδ hδ1)
    (gradedStep_three_two_reduced G n δ hδ hδ1)

/-- The graded step at `(3,3)` (`gradedStep_three_three`, proved) gives `IsDelta (4,1)`; then the
`j = 1` step at `i = 4` gives `IsDelta (4,2)`. -/
theorem isDelta_four_one (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 4 1 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 3 3 (isDelta_three_three G n δ hδ hδ1)
    (gradedStep_three_three G n δ hδ hδ1)

theorem isDelta_four_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 4 2 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 4 1 (isDelta_four_one G n δ hδ hδ1)
    (gradedStepJOne G n δ hδ hδ1 4 (by omega))

/-- The `(4,2)` graded step: the clash-free diagonal reduction `RedDiag.gradedStep_of_diagonal_at`
(inside `gradedStep_three_two_reduced.lean`) applied to the proved `(2,2)` diagonal step. -/
theorem gradedStep_four_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 4 2).1 (tauSucc 4 2).2,
      flowQuotSucc 2 G n 4 2 c = 1 →
      flowAction 2 G n (tauSucc 4 2).1 (tauSucc 4 2).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 4 2).1 (tauSucc 4 2).2,
        c = (flowAction 2 G n (tauSucc 4 2).1 (tauSucc 4 2).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 2 (by norm_num)
    (LNS3A.two_two_graded_step (G := G) (n := n) (δ := δ) hδ hδ1) 4 (by norm_num)

theorem isDelta_four_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 4 3 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 4 2 (isDelta_four_two G n δ hδ hδ1)
    (gradedStep_four_two G n δ hδ hδ1)

/-- The `(4,3)` graded step, from the proved `(3,3)` diagonal step. -/
theorem gradedStep_four_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 4 3).1 (tauSucc 4 3).2,
      flowQuotSucc 2 G n 4 3 c = 1 →
      flowAction 2 G n (tauSucc 4 3).1 (tauSucc 4 3).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 4 3).1 (tauSucc 4 3).2,
        c = (flowAction 2 G n (tauSucc 4 3).1 (tauSucc 4 3).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 3 (by norm_num)
    (gradedStep_three_three G n δ hδ hδ1) 4 (by norm_num)

theorem isDelta_four_four (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 4 4 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 4 3 (isDelta_four_three G n δ hδ hδ1)
    (gradedStep_four_three G n δ hδ hδ1)

/-- The `(4,4)` diagonal step comes from the clash-free port `gradedStep_four_four_conered`; the
`(5,j)` off-diagonal steps are instances of `RedDiag.gradedStep_of_diagonal_at` fed with the
diagonals at `(2,2)`, `(3,3)`, `(4,4)`. -/
theorem isDelta_five_one (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 5 1 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 4 4 (isDelta_four_four G n δ hδ hδ1)
    (gradedStep_four_four_conered G n δ hδ hδ1)

theorem isDelta_five_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 5 2 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 5 1 (isDelta_five_one G n δ hδ hδ1)
    (gradedStepJOne G n δ hδ hδ1 5 (by omega))

theorem gradedStep_five_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 5 2).1 (tauSucc 5 2).2,
      flowQuotSucc 2 G n 5 2 c = 1 →
      flowAction 2 G n (tauSucc 5 2).1 (tauSucc 5 2).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 5 2).1 (tauSucc 5 2).2,
        c = (flowAction 2 G n (tauSucc 5 2).1 (tauSucc 5 2).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 2 (by norm_num)
    (LNS3A.two_two_graded_step (G := G) (n := n) (δ := δ) hδ hδ1) 5 (by norm_num)

theorem isDelta_five_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 5 3 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 5 2 (isDelta_five_two G n δ hδ hδ1)
    (gradedStep_five_two G n δ hδ hδ1)

theorem gradedStep_five_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 5 3).1 (tauSucc 5 3).2,
      flowQuotSucc 2 G n 5 3 c = 1 →
      flowAction 2 G n (tauSucc 5 3).1 (tauSucc 5 3).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 5 3).1 (tauSucc 5 3).2,
        c = (flowAction 2 G n (tauSucc 5 3).1 (tauSucc 5 3).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 3 (by norm_num)
    (gradedStep_three_three G n δ hδ hδ1) 5 (by norm_num)

theorem isDelta_five_four (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 5 4 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 5 3 (isDelta_five_three G n δ hδ hδ1)
    (gradedStep_five_three G n δ hδ hδ1)

theorem gradedStep_five_four (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 5 4).1 (tauSucc 5 4).2,
      flowQuotSucc 2 G n 5 4 c = 1 →
      flowAction 2 G n (tauSucc 5 4).1 (tauSucc 5 4).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 5 4).1 (tauSucc 5 4).2,
        c = (flowAction 2 G n (tauSucc 5 4).1 (tauSucc 5 4).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 4 (by norm_num)
    (gradedStep_four_four_conered G n δ hδ hδ1) 5 (by norm_num)

theorem isDelta_five_five (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 5 5 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 5 4 (isDelta_five_four G n δ hδ hδ1)
    (gradedStep_five_four G n δ hδ hδ1)

/-- The `i = 6` row: the `(5,5)` diagonal step comes from `gradedStep_five_five_reduced`, and the
`(6,j)` off-diagonal steps are `RedDiag.gradedStep_of_diagonal_at` instances fed with the diagonals
at `(2,2)`, `(3,3)`, `(4,4)`, `(5,5)`. -/
theorem isDelta_six_one (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 1 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 5 5 (isDelta_five_five G n δ hδ hδ1)
    (gradedStep_five_five_reduced G n δ hδ hδ1)

theorem isDelta_six_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 2 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 6 1 (isDelta_six_one G n δ hδ hδ1)
    (gradedStepJOne G n δ hδ hδ1 6 (by omega))

theorem gradedStep_six_two (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 6 2).1 (tauSucc 6 2).2,
      flowQuotSucc 2 G n 6 2 c = 1 →
      flowAction 2 G n (tauSucc 6 2).1 (tauSucc 6 2).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 6 2).1 (tauSucc 6 2).2,
        c = (flowAction 2 G n (tauSucc 6 2).1 (tauSucc 6 2).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 2 (by norm_num)
    (LNS3A.two_two_graded_step (G := G) (n := n) (δ := δ) hδ hδ1) 6 (by norm_num)

theorem isDelta_six_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 3 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 6 2 (isDelta_six_two G n δ hδ hδ1)
    (gradedStep_six_two G n δ hδ hδ1)

theorem gradedStep_six_three (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 6 3).1 (tauSucc 6 3).2,
      flowQuotSucc 2 G n 6 3 c = 1 →
      flowAction 2 G n (tauSucc 6 3).1 (tauSucc 6 3).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 6 3).1 (tauSucc 6 3).2,
        c = (flowAction 2 G n (tauSucc 6 3).1 (tauSucc 6 3).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 3 (by norm_num)
    (gradedStep_three_three G n δ hδ hδ1) 6 (by norm_num)

theorem isDelta_six_four (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 4 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 6 3 (isDelta_six_three G n δ hδ hδ1)
    (gradedStep_six_three G n δ hδ hδ1)

theorem gradedStep_six_four (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 6 4).1 (tauSucc 6 4).2,
      flowQuotSucc 2 G n 6 4 c = 1 →
      flowAction 2 G n (tauSucc 6 4).1 (tauSucc 6 4).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 6 4).1 (tauSucc 6 4).2,
        c = (flowAction 2 G n (tauSucc 6 4).1 (tauSucc 6 4).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 4 (by norm_num)
    (gradedStep_four_four_conered G n δ hδ hδ1) 6 (by norm_num)

theorem isDelta_six_five (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 5 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 6 4 (isDelta_six_four G n δ hδ hδ1)
    (gradedStep_six_four G n δ hδ hδ1)

theorem gradedStep_six_five (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 6 5).1 (tauSucc 6 5).2,
      flowQuotSucc 2 G n 6 5 c = 1 →
      flowAction 2 G n (tauSucc 6 5).1 (tauSucc 6 5).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 6 5).1 (tauSucc 6 5).2,
        c = (flowAction 2 G n (tauSucc 6 5).1 (tauSucc 6 5).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 5 (by norm_num)
    (gradedStep_five_five_reduced G n δ hδ hδ1) 6 (by norm_num)

theorem isDelta_six_six (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : IsDelta G n 6 6 δ :=
  descent_step (G := G) (n := n) (δ := δ) hδ 6 5 (isDelta_six_five G n δ hδ hδ1)
    (gradedStep_six_five G n δ hδ hδ1)

/-- The `(7,7)` diagonal step: the odd case is uniform in `j` — `diagonalCore_odd` gives the
orbit-sum membership and `orbitSum_is_delta_difference` turns it into the norm. -/
theorem gradedStep_seven_seven (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : flowQuotient 2 G n (tauSucc 7 7).1 (tauSucc 7 7).2,
      flowQuotSucc 2 G n 7 7 c = 1 →
      flowAction 2 G n (tauSucc 7 7).1 (tauSucc 7 7).2 δ c = c⁻¹ →
      ∃ e : flowQuotient 2 G n (tauSucc 7 7).1 (tauSucc 7 7).2,
        c = (flowAction 2 G n (tauSucc 7 7).1 (tauSucc 7 7).2 δ e)⁻¹ * e := by
  intro c hc hanti
  exact orbitSum_is_delta_difference G n 7 δ hδ (by norm_num) c
    (diagonalCore_odd G n δ hδ hδ1 7 (by decide) c hc hanti)

end LowLevels

/-- **`2`-torsion lifting along the refined filtration, `p = 2`.** -/
theorem two_torsion_lift_two (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (γ : Work.CohomologicalShrinking.flowGroup 2 (K ≃ₐ[ℚ] K) n i j) (hγ : γ ^ 2 = 1)
    (hδ : Work.CohomologicalShrinking.flowQuot 2 (K ≃ₐ[ℚ] K) n i j γ ≠ 1) :
    ∃ y : Work.CohomologicalShrinking.flowGroup 2 (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  rcases eq_or_lt_of_le hj with h1 | h2
  · -- `j = 1`: the delegated slice `Work.SSGRoute.two_torsion_lift_j_one`
    -- (`E(n,(i,1))` is a free `𝔽₂[C₂]`-module, so the obstruction class vanishes).
    subst h1
    haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
    exact two_torsion_lift_j_one (K ≃ₐ[ℚ] K) n i hji γ hγ hδ
  · -- `j ≥ 2`: the descent-built levels `(2,2)`, `(3,1)`, `(3,2)`, `(3,3)`.
    haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
    rcases Decidable.em (i = 2 ∧ j = 2) with ⟨hi2, hj2⟩ | hne
    · subst hi2; subst hj2
      exact two_torsion_lift_two_of_isDelta K n 2 2 (by omega) (by omega)
        (fun δ hδ hδ1 => isDelta_two_two (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
    · rcases Decidable.em (i = 3 ∧ j = 1) with ⟨hi3, hj1⟩ | hne2
      · subst hi3; subst hj1
        exact two_torsion_lift_two_of_isDelta K n 3 1 (by omega) (by omega)
          (fun δ hδ hδ1 => isDelta_three_one (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
      · rcases Decidable.em (i = 3 ∧ j = 2) with ⟨hi3, hj2⟩ | hne3
        · subst hi3; subst hj2
          exact two_torsion_lift_two_of_isDelta K n 3 2 (by omega) (by omega)
            (fun δ hδ hδ1 => isDelta_three_two (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
        · rcases Decidable.em (i = 3 ∧ j = 3) with ⟨hi3, hj3⟩ | hne4
          · subst hi3; subst hj3
            exact two_torsion_lift_two_of_isDelta K n 3 3 (by omega) (by omega)
              (fun δ hδ hδ1 => isDelta_three_three (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
          · rcases Decidable.em (i = 4 ∧ j = 1) with ⟨hi4, hj1⟩ | hne5
            · subst hi4; subst hj1
              exact two_torsion_lift_two_of_isDelta K n 4 1 (by omega) (by omega)
                (fun δ hδ hδ1 => isDelta_four_one (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
            · rcases Decidable.em (i = 4 ∧ j = 2) with ⟨hi4, hj2⟩ | hne6
              · subst hi4; subst hj2
                exact two_torsion_lift_two_of_isDelta K n 4 2 (by omega) (by omega)
                  (fun δ hδ hδ1 => isDelta_four_two (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
              · rcases Decidable.em (i = 4 ∧ j = 3) with ⟨hi4, hj3⟩ | hne7
                · subst hi4; subst hj3
                  exact two_torsion_lift_two_of_isDelta K n 4 3 (by omega) (by omega)
                    (fun δ hδ hδ1 => isDelta_four_three (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                · rcases Decidable.em (i = 4 ∧ j = 4) with ⟨hi4, hj4⟩ | hne8
                  · subst hi4; subst hj4
                    exact two_torsion_lift_two_of_isDelta K n 4 4 (by omega) (by omega)
                      (fun δ hδ hδ1 => isDelta_four_four (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                  · rcases Decidable.em (i = 5 ∧ j = 2) with ⟨hi5, hj2⟩ | hne9
                    · subst hi5; subst hj2
                      exact two_torsion_lift_two_of_isDelta K n 5 2 (by omega) (by omega)
                        (fun δ hδ hδ1 => isDelta_five_two (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                    · rcases Decidable.em (i = 5 ∧ j = 3) with ⟨hi5, hj3⟩ | hneA
                      · subst hi5; subst hj3
                        exact two_torsion_lift_two_of_isDelta K n 5 3 (by omega) (by omega)
                          (fun δ hδ hδ1 => isDelta_five_three (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                      · rcases Decidable.em (i = 5 ∧ j = 4) with ⟨hi5, hj4⟩ | hneB
                        · subst hi5; subst hj4
                          exact two_torsion_lift_two_of_isDelta K n 5 4 (by omega) (by omega)
                            (fun δ hδ hδ1 => isDelta_five_four (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                        · rcases Decidable.em (i = 5 ∧ j = 5) with ⟨hi5, hj5⟩ | hneC
                          · subst hi5; subst hj5
                            exact two_torsion_lift_two_of_isDelta K n 5 5 (by omega) (by omega)
                              (fun δ hδ hδ1 => isDelta_five_five (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                          · rcases Decidable.em (i = 6 ∧ j = 2) with ⟨hi6, hj2⟩ | hneD
                            · subst hi6; subst hj2
                              exact two_torsion_lift_two_of_isDelta K n 6 2 (by omega) (by omega)
                                (fun δ hδ hδ1 => isDelta_six_two (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                            · rcases Decidable.em (i = 6 ∧ j = 3) with ⟨hi6, hj3⟩ | hneE
                              · subst hi6; subst hj3
                                exact two_torsion_lift_two_of_isDelta K n 6 3 (by omega) (by omega)
                                  (fun δ hδ hδ1 => isDelta_six_three (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                              · rcases Decidable.em (i = 6 ∧ j = 4) with ⟨hi6, hj4⟩ | hneF
                                · subst hi6; subst hj4
                                  exact two_torsion_lift_two_of_isDelta K n 6 4 (by omega) (by omega)
                                    (fun δ hδ hδ1 => isDelta_six_four (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                                · rcases Decidable.em (i = 6 ∧ j = 5) with ⟨hi6, hj5⟩ | hneG
                                  · subst hi6; subst hj5
                                    exact two_torsion_lift_two_of_isDelta K n 6 5 (by omega) (by omega)
                                      (fun δ hδ hδ1 => isDelta_six_five (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                                  · rcases Decidable.em (i = 6 ∧ j = 6) with ⟨hi6, hj6⟩ | hneH
                                    · subst hi6; subst hj6
                                      exact two_torsion_lift_two_of_isDelta K n 6 6 (by omega) (by omega)
                                        (fun δ hδ hδ1 => isDelta_six_six (K ≃ₐ[ℚ] K) n δ hδ hδ1) γ hγ hδ
                                    · -- Remaining gap: `i ≥ 7`.  The `(6,6)` diagonal step is delegated
                                      -- (`SSGRoute/gradedStep_six_six_reduced`); the `(7,7)` one is the
                                      -- last piece of the finite route (§15).
                                      sorry

end Work.SSGRoute
