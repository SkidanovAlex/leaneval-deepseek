import Submission.UnifDeps
import Submission.Work.SimplyConnected.Plane
import Submission.Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family

/-!
# The ABS data of the simply connected case

Anghel–Bruin–Stan ([ABS], *Uniformization of Riemann surfaces revisited*, arXiv:2008.12189) prove
the non-compact simply connected case of uniformization in three steps:

1. **Exhaustion** ([ABS, Theorem 12]): `X` is exhausted by compact simply connected sub-surfaces
   with connected boundary;
2. **The disc lemma** ([ABS, Theorem 10]): a compact simply connected sub-surface of a Riemann
   surface with exactly one boundary component is biholomorphic to the unit disc (through Perron's
   method: the Green function of the piece, its harmonic conjugate — which exists because the piece
   is simply connected — and the properness/injectivity argument);
3. **Diagonal extraction** ([ABS, §7]): the normalised biholomorphisms of the pieces converge, after
   a diagonal extraction along the exhaustion, to a global *injective* holomorphic `X → ℂ`;
   Riemann's mapping theorem (Mathlib's first half of it,
   `Commons.Analysis.Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero`) then finishes.

This module implements the **interface of that argument**, with the two data packages as
Prop-valued definitions and the reductions between them *proved*:

* `Work.SC.HasDiscExhaustion X x₀` — steps 1 and 2 combined: an exhaustion of `X` by open connected
  sets `Ω n`, each mapped biholomorphically by `χ n` onto a disc `ball 0 (r n)`, normalised at `x₀`
  (value `0` and chart derivative `1`), with `χ n` extended by `0` outside `Ω n`;
* `Work.SC.UniformBoundAt X x₀` — the normal-family bound for univalent maps (Landau/Koebe,
  [ABS, Appendix AC]): the value of `ψ` on a compact subset of an open connected `Ω ⊇ x₀` is bounded
  in terms of `Ω` and the compact set only;
* `Work.SC.HasUnivalentExhaustion X x₀` — the exact hypotheses of the extraction lemma
  `Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family`.

The two proved reductions are

* `Work.SC.hasUnivalentExhaustion_of_hasDiscExhaustion` : disc exhaustion + normal-family bound
  ⟹ univalent exhaustion;
* `Work.SC.uniformization_of_simplyConnected_of_univalentExhaustion` (and
  `…_of_discExhaustion`) : ⟹ the deliverable
  (`Nonempty (X ≃ₘ⟮mℂ,mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ,mℂ⟯ UpperHalfPlane)`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The ABS exhaustion of `X` by discs.**  An increasing sequence of open connected sets `Ω n`
covering `X`, all containing `x₀`, each mapped by an explicit normalised `χ n` biholomorphically
onto the disc of radius `r n` around `0`, with `χ n = 0` outside `Ω n`.

This is the conclusion of steps 1 and 2 of the ABS proof ([ABS, Theorems 12 and 10]). -/
def HasDiscExhaustion (x₀ : X) : Prop :=
  ∃ (Ω : ℕ → Set X) (χ : ℕ → X → ℂ) (r : ℕ → ℝ),
    (∀ n, 0 < r n) ∧ (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, x₀ ∈ Ω n) ∧ (∀ n, Ω n ⊆ Ω (n + 1)) ∧ (⋃ n, Ω n = Set.univ) ∧
      (∀ n, ∀ x ∈ Ω n, Submission.HolomorphicOnXAt (χ n) x) ∧
      (∀ n, Set.InjOn (χ n) (Ω n)) ∧ (∀ n, χ n x₀ = 0) ∧
      (∀ n, χ n '' Ω n = Metric.ball (0 : ℂ) (r n)) ∧
      (∀ n, deriv (χ n ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1) ∧
      (∀ n x, x ∉ Ω n → χ n x = 0)

/-- **The univalent exhaustion of `X`.**  An increasing sequence of open sets `Ω n` covering `X`,
all containing `x₀`, together with functions `ψ n` which are holomorphic and injective on `Ω n`,
normalised at `x₀` (value `0` and chart derivative `1`), vanishing outside `Ω n` and uniformly
bounded on compact subsets.

These are exactly the hypotheses of the extraction lemma
`Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family`. -/
def HasUnivalentExhaustion (x₀ : X) : Prop :=
  ∃ (Ω : ℕ → Set X) (ψ : ℕ → X → ℂ),
    (∀ n, IsOpen (Ω n)) ∧ (∀ n, x₀ ∈ Ω n) ∧ (∀ n, Ω n ⊆ Ω (n + 1)) ∧
      (⋃ n, Ω n = Set.univ) ∧
      (∀ n, ∀ x ∈ Ω n, Submission.HolomorphicOnXAt (ψ n) x) ∧
      (∀ n, Set.InjOn (ψ n) (Ω n)) ∧ (∀ n, ψ n x₀ = 0) ∧
      (∀ n, deriv (ψ n ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1) ∧
      (∀ K : Set X, IsCompact K → ∃ B : ℝ, ∀ n, ∀ x ∈ K, ‖ψ n x‖ ≤ B)

/-- **The normal-family bound for univalent maps** (Landau/Koebe; [ABS, Appendix AC]).
A function which is injective and holomorphic on an open connected set `Ω` containing `x₀`, with
`ψ x₀ = 0` and chart derivative `1` at `x₀`, is bounded on the compact subsets of any open connected
`U` with `x₀ ∈ U ⊆ Ω` by a constant depending only on `U` and the compact set — never on `ψ`.

This is the statement delegated as
`Submission.Work.SimplyConnected.Parabolic.norm_le_of_univalent_normalized` ([ABS] derive it from
Landau's theorem and the Koebe growth bound, `Submission.exists_growth_bound_normalized_injective`). -/
def UniformBoundAt (x₀ : X) : Prop :=
  ∀ {U : Set X}, IsOpen U → IsConnected U → x₀ ∈ U → ∀ K : Set X, IsCompact K → K ⊆ U →
    ∃ B : ℝ, ∀ {Ω : Set X}, IsOpen Ω → IsConnected Ω → U ⊆ Ω → ∀ {ψ : X → ℂ},
      (∀ x ∈ Ω, Submission.HolomorphicOnXAt ψ x) → Set.InjOn ψ Ω → ψ x₀ = 0 →
      deriv (ψ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 → ∀ x ∈ K, ‖ψ x‖ ≤ B

/-- **The extraction endgame.**  A univalent exhaustion produces a global injective holomorphic
`X → ℂ`: this is the ABS §7 diagonal extraction, in the form of the proved lemma
`Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family`. -/
theorem exists_injective_holomorphic_of_univalentExhaustion [SimplyConnectedSpace X]
    {x₀ : X} (h : HasUnivalentExhaustion (X := X) x₀) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g Set.univ ∧ Function.Injective g := by
  obtain ⟨Ω, ψ, hΩo, hx, hmono, hcov, hhol, hinj, h0, hder, hbd⟩ := h
  obtain ⟨g, hghol, hginj, -, -⟩ :=
    Work.SimplyConnected.Parabolic.exists_injective_holomorphic_of_univalent_family
      (x₀ := x₀) hΩo hmono hcov hx hhol hinj h0 hder
      (fun _U _ hUc hxU K hK _ => hbd K hK)
  exact ⟨g, hghol, hginj⟩

/-- **The deliverable from a univalent exhaustion.** -/
theorem uniformization_of_simplyConnected_of_univalentExhaustion [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) {x₀ : X} (h : HasUnivalentExhaustion (X := X) x₀) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) := by
  obtain ⟨g, hghol, hginj⟩ := exists_injective_holomorphic_of_univalentExhaustion h
  exact uniformization_of_simplyConnected_of_injective_into_plane hX hghol hginj

/-- A bound for the finitely many indices `n < m` of a sequence of reals. -/
private theorem exists_bound_of_lt (r : ℕ → ℝ) (m : ℕ) : ∃ R : ℝ, ∀ n, n < m → r n ≤ R := by
  induction m with
  | zero => exact ⟨0, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨max R (r k), fun n hn => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · exact le_trans (hR n h) (le_max_left _ _)
      · subst h; exact le_max_right _ _⟩

/-- **A disc exhaustion produces a univalent exhaustion** (given the normal-family bound): take the
normalised disc maps `χ n` as the univalent family.  On a compact `K ⊆ Ω m` the value is bounded by
the normal-family bound for the indices `n ≥ m` and by the disc radii for the finitely many smaller
indices. -/
theorem hasUnivalentExhaustion_of_hasDiscExhaustion {x₀ : X}
    (hU : UniformBoundAt (X := X) x₀) (h : HasDiscExhaustion (X := X) x₀) :
    HasUnivalentExhaustion (X := X) x₀ := by
  obtain ⟨Ω, χ, r, hr, hΩo, hΩc, hx, hmono, hcov, hχhol, hχinj, hχ0, hχimg, hχder, hχzero⟩ := h
  have hmonoΩ : ∀ n m : ℕ, n ≤ m → Ω n ⊆ Ω m := monotone_nat_of_le_succ hmono
  have hbnd : ∀ K : Set X, IsCompact K → ∃ B : ℝ, ∀ n, ∀ x ∈ K, ‖χ n x‖ ≤ B := by
    intro K hK
    have hsub : K ⊆ ⋃ n, Ω n := by rw [hcov]; exact subset_univ K
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ω hΩo hsub
    obtain ⟨m, hm⟩ : ∃ m, K ⊆ Ω m := by
      refine ⟨t.sup id, fun x hx => ?_⟩
      have hx' : x ∈ ⋃ n ∈ t, Ω n := ht hx
      obtain ⟨n, hnt, hxn⟩ : ∃ n, n ∈ t ∧ x ∈ Ω n := by
        simpa only [Set.mem_iUnion, exists_prop] using hx'
      exact hmonoΩ n (t.sup id) (Finset.le_sup (f := id) hnt) hxn
    obtain ⟨B₁, hB₁⟩ := hU (hΩo m) (hΩc m) (hx m) K hK hm
    obtain ⟨R, hR⟩ := exists_bound_of_lt r m
    refine ⟨max B₁ (max R 0), fun n x hxK => ?_⟩
    by_cases hn : m ≤ n
    · have hxΩ : x ∈ Ω n := hmonoΩ m n hn (hm hxK)
      have := hB₁ (Ω := Ω n) (ψ := χ n) (hΩo n) (hΩc n) (hmonoΩ m n hn) (hχhol n) (hχinj n)
        (hχ0 n) (hχder n) x hxK
      exact le_trans this (le_max_left _ _)
    · have hnlt : n < m := lt_of_not_ge hn
      by_cases hxn : x ∈ Ω n
      · have hmem : χ n x ∈ Metric.ball (0 : ℂ) (r n) := by
          rw [← hχimg n]; exact ⟨x, hxn, rfl⟩
        have hlt : ‖χ n x‖ < r n := by
          rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
        exact le_trans (le_of_lt hlt)
          (le_trans (hR n hnlt) (le_trans (le_max_left _ _) (le_max_right _ _)))
      · rw [hχzero n x hxn, norm_zero]
        exact le_trans (le_max_right R 0) (le_max_right B₁ (max R 0))
  exact ⟨Ω, χ, hΩo, hx, hmono, hcov, hχhol, hχinj, hχ0, hχder, hbnd⟩

/-- **The deliverable from a disc exhaustion and the normal-family bound.** -/
theorem uniformization_of_simplyConnected_of_discExhaustion [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) {x₀ : X} (hU : UniformBoundAt (X := X) x₀)
    (h : HasDiscExhaustion (X := X) x₀) :
    Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) ∨
      Nonempty (X ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ UpperHalfPlane) :=
  uniformization_of_simplyConnected_of_univalentExhaustion hX
    (hasUnivalentExhaustion_of_hasDiscExhaustion hU h)

end Work.SC

namespace Work.SimplyConnected

alias hasUnivalentExhaustion_of_hasDiscExhaustion :=
  Work.SC.hasUnivalentExhaustion_of_hasDiscExhaustion
alias uniformization_of_simplyConnected_of_univalentExhaustion :=
  Work.SC.uniformization_of_simplyConnected_of_univalentExhaustion
alias uniformization_of_simplyConnected_of_discExhaustion :=
  Work.SC.uniformization_of_simplyConnected_of_discExhaustion

end Work.SimplyConnected

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The ABS data from an exhaustion by simply connected pieces and the disc lemma on pieces.**

Hypotheses:

* `hExh` — [ABS, Theorem 12]: an exhaustion of `X` by open connected simply connected sets `Ω n`
  with compact closure, connected frontier, nested with `closure (Ω n) ⊆ Ω (n+1)`;
* `hPiece` — [ABS, Theorem 10]: every such piece carries a normalised biholomorphism onto a disc.

Conclusion: `Work.SC.HasDiscExhaustion X x₀`, which (with `Work.SC.UniformBoundAt`) yields the
deliverable (`Work.SC.uniformization_of_simplyConnected_of_discExhaustion`).

The only point to check is that each `Ω n` is a *proper* subset of `X`: `closure (Ω n)` is compact
and `X` is not compact, so `Ω n ≠ univ`.  (This is where the non-compactness of `X` is needed: on a
compact surface a member of the exhaustion could be biholomorphic to `ℂ`, which admits no
biholomorphism onto a disc.) -/
theorem hasDiscExhaustion_of_pieceData (hX : ¬ CompactSpace X) {x₀ : X}
    (hExh : ∃ Ω : ℕ → Set X, (∀ n, IsOpen (Ω n)) ∧ (∀ n, IsConnected (Ω n)) ∧
      (∀ n, IsSimplyConnected (Ω n)) ∧ (∀ n, IsCompact (closure (Ω n))) ∧
      (∀ n, IsConnected (frontier (Ω n))) ∧ (∀ n, closure (Ω n) ⊆ Ω (n + 1)) ∧
      x₀ ∈ Ω 0 ∧ (⋃ n, Ω n) = Set.univ)
    (hPiece : ∀ {Ω : Set X}, IsOpen Ω → IsConnected Ω → IsSimplyConnected Ω → Ω ≠ Set.univ →
      IsCompact (closure Ω) → IsConnected (frontier Ω) → ∀ x₀ ∈ Ω, ∃ (r : ℝ) (χ : X → ℂ),
        0 < r ∧ (∀ x ∈ Ω, Submission.HolomorphicOnXAt χ x) ∧ Set.InjOn χ Ω ∧ χ x₀ = 0 ∧
        χ '' Ω = Metric.ball (0 : ℂ) r ∧
        deriv (χ ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 1 ∧ (∀ x ∉ Ω, χ x = 0)) :
    HasDiscExhaustion (X := X) x₀ := by
  obtain ⟨Ω, hΩo, hΩc, hΩs, hcomp, hbc, hmono, hx₀, hcov⟩ := hExh
  have hne : ∀ n, Ω n ≠ Set.univ := by
    intro n h
    have hcl : closure (Ω n) = Set.univ := by rw [h]; exact closure_univ
    exact hX (isCompact_univ_iff.mp (hcl ▸ hcomp n))
  have hxΩ : ∀ n, x₀ ∈ Ω n := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ k ih => exact hmono k (subset_closure ih)
  have hmono' : ∀ n, Ω n ⊆ Ω (n + 1) := fun n => (subset_closure).trans (hmono n)
  choose r χ hr hχhol hχinj hχ0 hχimg hχder hχzero using
    fun n => hPiece (hΩo n) (hΩc n) (hΩs n) (hne n) (hcomp n) (hbc n) x₀ (hxΩ n)
  exact ⟨Ω, χ, r, hr, hΩo, hΩc, hxΩ, hmono', hcov, hχhol, hχinj, hχ0, hχimg, hχder, hχzero⟩

end Work.SC

namespace Work.SimplyConnected

alias hasDiscExhaustion_of_pieceData := Work.SC.hasDiscExhaustion_of_pieceData

end Work.SimplyConnected
