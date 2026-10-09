import Mathlib
import Submission.Work.CohomologicalShrinking.All
import Submission.Work.GenericKernelReduction.All
import Submission.Work.Tate.All
import Submission.Shafarevich
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# Shafarevich route — shared vocabulary (DEFINITIONS ONLY; create verbatim, do not edit)

To be created by the orchestrator as `Submission/Work/SSGRoute/Interfaces.lean` with the imports

  import Mathlib
  import Submission.Work.CohomologicalShrinking.All
  import Submission.Work.GenericKernelReduction.All
  import Submission.Work.Tate.All
  import Submission.Shafarevich

Every top-level lemma of `requests/ssg/` is stated in this vocabulary.  Nothing here is `sorry`.

Conventions.  `Ω` is an algebraic closure of the base number field `k` and `Ω ≃ₐ[k] Ω` (Krull
topology) is `G_k`.  A *finite place* of `Ω` is a valuation subring `A` of `Ω` whose restriction
to `k` is not `k` itself; its decomposition group is the stabiliser of `A` (pointwise action),
its inertia group the elements acting trivially on the residue field.  Real places of `k` are
represented by involutions of `G_k` (Artin–Schreier: every element of order 2 is a complex
conjugation).  Continuous cochains with values in a discrete finite module are the locally
constant ones.
-/

open scoped Pointwise TensorProduct

namespace SSGRoute

/-! ## Places of an algebraic closure -/

section Places

variable (k : Type) {Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- `A` is a place of `Ω` over a *finite* prime of `k`. -/
def IsFinPlace (A : ValuationSubring Ω) : Prop :=
  A.comap (algebraMap k Ω) ≠ ⊤

/-- The decomposition group `D_A ≤ G_k` of a place `A` of `Ω`. -/
abbrev decomp (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  MulAction.stabilizer (Ω ≃ₐ[k] Ω) A

/-- `σ` lies in the inertia group `I_A`: it stabilises `A` and acts trivially on its residue
field. -/
def IsInertia (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) : Prop :=
  σ ∈ decomp k A ∧ ∀ x : Ω, x ∈ A → A.valuation (σ x - x) < 1

/-- `A` lies over a prime of `k` that ramifies in the finite normal extension `N/k`. -/
def IsRamifiedIn (N : IntermediateField k Ω) (A : ValuationSubring Ω) : Prop :=
  ∃ σ : Ω ≃ₐ[k] Ω, IsInertia k A σ ∧ σ ∉ N.fixingSubgroup

/-- `A` lies over a prime of `k` that splits completely in `N/k` (equivalently `D_A ≤ G_N`). -/
def IsSplitIn (N : IntermediateField k Ω) (A : ValuationSubring Ω) : Prop :=
  decomp k A ≤ N.fixingSubgroup

/-- The restriction `G_k →* Gal(N/k)` to a normal subextension. -/
noncomputable abbrev res (N : IntermediateField k Ω) [Normal k N] : (Ω ≃ₐ[k] Ω) →* (N ≃ₐ[k] N) :=
  AlgEquiv.restrictNormalHom N

/-- `B` is a `G_k`-conjugate of `A`, i.e. `A` and `B` lie over the same prime of `k`. -/
def IsConjPlace (A B : ValuationSubring Ω) : Prop :=
  ∃ σ : Ω ≃ₐ[k] Ω, σ • A = B

end Places

/-! ## Continuous cochains on subgroups of a profinite group -/

section Cochains

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

/-- `f` is locally constant on `H` (continuity for a discrete coefficient module). -/
def IsLocConstOn (H : Subgroup Γ) (f : Γ → M) : Prop :=
  ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ ∀ g ∈ H, ∀ u ∈ U, u ∈ H → f (g * u) = f g

/-- `f` is a (crossed-homomorphism) `1`-cocycle on `H`, `Γ` acting through `act`. -/
def IsCocycleOn (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + act g • f h

/-- `f` is a `1`-coboundary on `H`. -/
def IsCoboundaryOn (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) : Prop :=
  ∃ m : M, ∀ g ∈ H, f g = act g • m - m

/-- `c` is an inhomogeneous `2`-cocycle on `Γ`. -/
def IsCocycle2 (act : Γ →* G) (c : Γ → Γ → M) : Prop :=
  ∀ g h l : Γ, act g • c h l - c (g * h) l + c g (h * l) - c g h = 0

/-- `c` is locally constant (continuous) on `Γ × Γ`. -/
def IsLocConst2 (c : Γ → Γ → M) : Prop :=
  ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
    ∀ g h u v : Γ, u ∈ U → v ∈ U → c (g * u) (h * v) = c g h

/-- `c` is the coboundary of a continuous `1`-cochain on `H × H`. -/
def IsCoboundary2On (act : Γ →* G) (H : Subgroup Γ) (c : Γ → Γ → M) : Prop :=
  ∃ b : Γ → M, IsLocConstOn H b ∧
    ∀ g ∈ H, ∀ h ∈ H, c g h = act g • b h - b (g * h) + b g

end Cochains

/-- `T` is the `𝔽_p`-dual `μ_p^∨ = Hom(μ_p, 𝔽_p)` of the roots of unity, as a module over a group
`G` through which `Γ` acts on `T` via `act`: `T` is a line and `σ` acts on it by the inverse of
the cyclotomic character (`σ ζ = ζ^c ⇒ c · (σ t) = t`). -/
def IsCyclotomicDual (p : ℕ) {Γ G T Ω : Type} [Group Γ] [Group G] [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction G T] [Field Ω] [MulSemiringAction Γ Ω]
    (act : Γ →* G) (ζ : Ω) : Prop :=
  Module.finrank (ZMod p) T = 1 ∧
    ∀ (σ : Γ) (c : ℕ), σ • ζ = ζ ^ c → ∀ t : T, c • (act σ • t) = t

/-! ## Theorem 15 of Schmidt–Wingberg over `ℚ`: solutions of the generic embedding problem -/

/-- `Ω = ℚ̄`. -/
abbrev QBar : Type := AlgebraicClosure ℚ

/-- `G_ℚ`. -/
abbrev GalQ : Type := QBar ≃ₐ[ℚ] QBar

section Flow

open Work.CohomologicalShrinking

/-- `μ_{p^{i+1}} ⊆ K` (the exponent condition of the induction step `τ ↦ τ+1` for `τ = (i,j)`;
it also forces `K` to be totally imaginary, since `p^{i+1} ≥ 4` for `i ≥ 1`). -/
def HasRootsOfUnity (p : ℕ) (K : IntermediateField ℚ QBar) (i : ℕ) : Prop :=
  ∃ ζ : QBar, ζ ∈ K ∧ IsPrimitiveRoot ζ (p ^ (i + 1))

/-- A (proper, continuous) solution `φ : G_ℚ ↠ F(n)/F(n)^{(i,j)} ⋊ Gal(K/ℚ)` of the split generic
embedding problem over `K/ℚ`. -/
def IsFlowSolution (p : ℕ) (K : IntermediateField ℚ QBar) [Normal ℚ K] (n i j : ℕ)
    (φ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  Function.Surjective φ ∧ IsOpen (φ.ker : Set GalQ) ∧
    ∀ σ : GalQ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = AlgEquiv.restrictNormalHom K σ

/-- The places over `Ram(K/ℚ) ∪ {p}` (the set `T¹` of the paper minus `∞`). -/
def IsT1Place (p : ℕ) (K : IntermediateField ℚ QBar)
    (A : ValuationSubring QBar) : Prop :=
  IsFinPlace ℚ A ∧ (A.valuation (p : QBar) < 1 ∨ IsRamifiedIn ℚ K A)

/-- The local conditions (i), (ii) of Theorem 15 for a homomorphism `φ : G_ℚ → X` whose field
contains `K`:
(i) every place over `Ram(K/ℚ) ∪ {p} ∪ {∞}` is completely decomposed in `N/K`;
(ii) a place ramified in `N/K` lies over a prime split completely in `K/ℚ`, and its local
extension `N_A/ℚ_ℓ` is cyclic and totally ramified. -/
def ScholzConditions (p : ℕ) (K : IntermediateField ℚ QBar) {X : Type}
    [Group X] (φ : GalQ →* X) : Prop :=
  (∀ A : ValuationSubring QBar, IsT1Place p K A →
      ∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup → φ σ = 1) ∧
  (∀ c : GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → φ c = 1) ∧
  (∀ A : ValuationSubring QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ φ σ ≠ 1) →
      (∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      IsCyclic ((decomp ℚ A).map φ) ∧
      ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧ φ τ = φ σ)

/-- **A Scholz solution** (Theorem 15 of Schmidt–Wingberg): a proper solution satisfying (i), (ii). -/
def IsScholzSolution (p : ℕ) (K : IntermediateField ℚ QBar) [Normal ℚ K] (n i j : ℕ)
    (φ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  IsFlowSolution p K n i j φ ∧ ScholzConditions p K φ

/-- `y ∈ F(n)/F(n)^{(τ')} ⋊ G` lies over `x ∈ F(n)/F(n)^{(τ)} ⋊ G` (for `τ ≤ τ'`): same `G`-component
and the two left components are images of one element of `F(n)`. -/
def LiftsFlowAt {p : ℕ} {K : IntermediateField ℚ QBar} {n i j i' j' : ℕ}
    (y : flowGroup p (K ≃ₐ[ℚ] K) n i' j') (x : flowGroup p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  y.right = x.right ∧
    ∃ z : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n)),
      y.left = (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i' j') ∧
      x.left = (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j)

/-- `ψ` lifts `φ` through the projection `F(n)/F(n)^{(τ')} ⋊ G → F(n)/F(n)^{(τ)} ⋊ G`. -/
def LiftsFlow {p : ℕ} {K : IntermediateField ℚ QBar} {n i j i' j' : ℕ}
    (ψ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i' j')
    (φ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  ∀ σ : GalQ, LiftsFlowAt (ψ σ) (φ σ)

/-- **Stage 2** of the induction step `τ = (i,j) ↦ τ+1` at level `n` (after Steps 1–2 of the
paper): a Scholz solution `φ` at `τ` that has a continuous (not necessarily proper) lift `ψ` to
`τ+1`, and whose local group extension at every place over `Ram(K/ℚ) ∪ {p}` splits (there is a
local lift `l` of `φ|_{D_A}` that factors through `φ(D_A)`). -/
def IsSolvableStage (p : ℕ) (K : IntermediateField ℚ QBar) [Normal ℚ K] (n i j : ℕ) : Prop :=
  ∃ (φ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2),
    IsScholzSolution p K n i j φ ∧ LiftsFlow ψ φ ∧ IsOpen (ψ.ker : Set GalQ) ∧
    ∀ A : ValuationSubring QBar, IsT1Place p K A →
      ∃ l : ↥(decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        (∀ σ : ↥(decomp ℚ A), LiftsFlowAt (l σ) (φ σ)) ∧
        (∀ σ : ↥(decomp ℚ A), φ σ = 1 → l σ = 1)

/-- **Stage 3** (after Step 3 of the paper): a Scholz solution `φ` at `τ` with a *proper* lift `ψ`
at `τ+1` which satisfies (i), and whose places ramified in `N_{τ+1}/K` either are completely
decomposed in `N_τ/ℚ` or have cyclic totally ramified local extension. -/
def IsProperStage (p : ℕ) (K : IntermediateField ℚ QBar) [Normal ℚ K] (n i j : ℕ) : Prop :=
  ∃ (φ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2),
    IsScholzSolution p K n i j φ ∧ LiftsFlow ψ φ ∧
    IsFlowSolution p K n (tauSucc i j).1 (tauSucc i j).2 ψ ∧
    (∀ A : ValuationSubring QBar, IsT1Place p K A →
      ∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1) ∧
    (∀ c : GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1) ∧
    ∀ A : ValuationSubring QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((decomp ℚ A).map ψ) ∧ ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧ ψ τ = ψ σ))

end Flow

end SSGRoute
