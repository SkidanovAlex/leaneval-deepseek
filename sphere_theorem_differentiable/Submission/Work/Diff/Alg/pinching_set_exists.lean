import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.Chat_exhaust
import Submission.Work.Diff.Alg.Pinch.Chat_pinch
import Submission.Work.Diff.Alg.Pinch.Chat_pinch_tail
import Submission.Work.Diff.Alg.Pinch.exists_invariant_set_Chat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
ROUTE. The whole route is in REFS/BrendleSchoen_quarter_pinched_0705.0766.txt §2–3 (Props 11–17).
Also use REFS/BohmWilking_curvature_operators_math0606187.txt (Lemmas 3.4, 3.5, Thm 4.1) and
REFS/Wilking_Lie_algebraic_invariant_conditions_1011.3561.txt.
Our `InPIC2` is BS's cone Ĉ: nonnegative complex sectional curvature. For n ≥ 4 it is equivalent to BS's frame condition
(BS Prop 21, Brendle's book Prop 7.18). You may prefer Wilking's theorem: for an Ad_{SO(n,C)}-invariant set S ⊂ so(n,C), the
cone {R : R(φ, φ̄) ≥ 0 ∀ φ ∈ S} is invariant under R' = Q(R). With S = decomposable complex 2-forms, this is
exactly InPIC2. The proof is short and algebraic, with no case analysis in dimensions.
Pieces (file them in parallel, each an exact statement over `Curv4 n`):
(a) ODE machinery. Q is polynomial, hence locally Lipschitz.
    Hamilton's lemma: a closed convex set in a finite-dimensional space is ODE-invariant iff Q(R) lies in the tangent cone
    at every boundary point. Use the BS Prop 11 proof: the ε-perturbation R_ε' = Q(R_ε) + ε·Iso and continuous dependence.
    State one general lemma: `closed F` + `∀ R ∈ F, ∀ ℓ supporting F at R, ℓ(Q R) ≥ 0` (with strict slack for a perturbed
    field) implies ODEInvariant F.
(b) PIC2 is Q-invariant (Wilking or BS Props 5–12).
(c) BW cones Ĉ(s) = ℓ_{a,b}(Ĉ ∩ {Ric ≥ p·scal/n}) (BS Props 13, 14, with a,b,p given there).
    ℓ_{a,b}(R) = R + b·Ric₀∧id + (a/n)·scal·id∧id, with ∧ the Kulkarni–Nomizu product
    (A∧B)ijkl = A_ik B_jl − A_il B_jk − A_jk B_il + A_jl B_ik.
    Transversal invariance comes from the BW identity for ℓ_{a,b}⁻¹ Q(ℓ_{a,b} R) (BW Thm 2.1 / Lemma 3.4-3.5).
    The pinching property is BS Prop 15 (iii).
(d) BS Prop 16 (one step) and Prop 17 (the intersection F = ⋂ F_j). This is purely soft once (a)–(c) exist.
Dimension notes: n = 2 is trivial, since F = {R alg-curv : R = s·Iso, s ≥ 0} works and every element is 1-pinched.
So is n = 3 via the n ≥ 3 BW formulas. If a formula in BS/BW assumes n ≥ 4, check it for n = 3 or treat n = 3 separately.
Sanity check first (a cheap lemma): Q (Iso n) = (2*(n-1)) • Iso n.

ASSEMBLY (this file): `PinchingSetExists n` follows from the Brendle–Schoen/Böhm–Wilking route:
* `Pinch.Chat_exhaust`: the family `Ĉ(s)` exhausts the interior of `Ĉ`, so the compact `K ⊂ int Ĉ` sits in a single `Ĉ(s₀)`;
* `Pinch.exists_invariant_set_Chat` (Böhm–Wilking Thm 4.1): for `ε, h₀ > 0` there is a closed convex `O(n)`-invariant
  ODE-invariant `F` containing `Ĉ(ε) ∩ {scal ≤ h₀}` and with `F \ Ĉ(s)` bounded for all `s ≥ ε`;
* `Pinch.Chat_pinch_tail` (BS Prop 15 (iii)): for each `δ < 1`, `Ĉ(s) \ {0}` is `δ`-pinched for *every*
  `s ≥ s₁` on the tail of the family (note: the family is **not** monotone in `s` on the first branch
  `s ≤ 1/2`, so the tail form -- not a monotonicity of `Ĉ` -- is what the argument needs).
Then `F` is a pinching set containing `K`: the non-`δ`-pinched part of `F` lies in the bounded set `F \ Ĉ(s)`.

NOTE (import hygiene, fixed in this area): the duplicate helper declarations `ric_ell`, `ric_zero`
of `Work.Diff.Alg.Pinch.Ccone_transversal_a_aux` were renamed to `ric_ellAux`, `ric_zeroAux`
(after these two, the modules `Ccone_transversal_a_aux` and `Ccone_transversal_b` / `linv_Q_ell`
-- and with them `Chat_transversal`, `chat_odeInvariant`, `Chat_shifted_transversal` -- can all be
imported in one file; Lean rejects duplicate imported names when the declarations differ). -/

namespace Work.Diff.Alg

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- `scalAlg` is continuous: it is a finite sum of coordinate functions. -/
lemma continuous_scalAlg (n : ℕ) : Continuous (fun R : Curv4 n => scalAlg R) := by
  simp only [scalAlg]
  fun_prop

/-- On a compact set of curvature arrays the scalar curvature is bounded above by a positive number. -/
lemma exists_scalAlg_bound {n : ℕ} {K : Set (Curv4 n)} (hK : IsCompact K) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ R ∈ K, scalAlg R ≤ h₀ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_scalAlg n).continuousOn
  refine ⟨|C| + 1, by positivity, fun R hR => ?_⟩
  have h1 : scalAlg R ≤ |C| :=
    (le_abs_self (scalAlg R)).trans ((hC R hR).trans (le_abs_self C))
  linarith

/-- The zero tensor is `δ`-pinched for every `δ < 1` (indeed for every `δ`). -/
lemma isPinchedAlg_zero (n : ℕ) (δ : ℝ) : IsPinchedAlg δ (0 : Curv4 n) := by
  intro u v u' v' _ _
  simp [secK, R4]

theorem pinching_set_exists (n : ℕ) (hn : 2 ≤ n) : PinchingSetExists n := by
  intro K hK hKi
  -- the Böhm–Wilking family `Ĉ(s)` exhausts the interior of the PIC2 cone
  obtain ⟨s₀, hs₀, hKs₀⟩ := Pinch.Chat_exhaust n hn K hK hKi
  -- bound the scalar curvature on the compact set `K`
  obtain ⟨h₀, hh₀, hKb⟩ := exists_scalAlg_bound hK
  -- Böhm–Wilking Theorem 4.1 (Brendle–Schoen Prop. 16/17): the invariant set
  obtain ⟨F, hFc, hFcv, hFalg, hFrot, hFode, hFsub, hFbd⟩ :=
    Pinch.exists_invariant_set_Chat n hn s₀ h₀ hs₀ hh₀
  refine ⟨F, ⟨⟨hFc, hFcv, hFalg, hFrot, hFode⟩, ?_⟩, ?_⟩
  · -- for each `δ < 1` the non-`δ`-pinched part of `F` is bounded
    intro δ hδ
    -- pinching holds on the whole tail `Ĉ(s)`, `s ≥ s₁`, of the Brendle–Schoen family
    obtain ⟨s₁, hs₁, htail⟩ := Pinch.Chat_pinch_tail n hn δ hδ
    have hs₀s : s₀ ≤ max s₀ s₁ := le_max_left _ _
    have hs₁s : s₁ ≤ max s₀ s₁ := le_max_right _ _
    refine Bornology.IsBounded.subset (hFbd (max s₀ s₁) hs₀s) ?_
    rintro R ⟨hRF, hRnp⟩
    refine ⟨hRF, fun hRC => hRnp ?_⟩
    by_cases hR0 : R = 0
    · subst hR0
      exact isPinchedAlg_zero n δ
    · exact htail (max s₀ s₁) hs₁s R hRC hR0
  · -- `K ⊆ Ĉ(s₀) ∩ {scal ≤ h₀} ⊆ F`
    intro R hR
    exact hFsub ⟨hKs₀ R hR, hKb R hR⟩

end Work.Diff.Alg

#print axioms Work.Diff.Alg.pinching_set_exists
