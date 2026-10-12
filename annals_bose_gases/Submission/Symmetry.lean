import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.KineticLower
import Submission.OneParticle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bosonic symmetry of the trial space (core)

`boxEnergy` is the infimum over *all* (not necessarily permutation-symmetric)
trial functions in `CInfty0Box`.  The classical literature (Fournais--Solovej,
final_v2.tex line ~325) states that the infimum over all functions equals the
infimum over symmetric (bosonic) ones for `0 ≤ v`.  This module provides the
machinery:

  * the permutation action `actPerm` on the configuration space and the
    predicate `PermInvariant` (bosonic symmetry);
  * the symmetric trial space `SymBox` (a `CInfty0Box` whose functions are
    permutation invariant) and the symmetric ground-state energy
    `symBoxEnergy`;
  * the trivial direction `boxEnergy_le_symBoxEnergy` (the symmetric space is
    a subspace of the full space, so the full infimum is no larger);
  * the symmetrization average `symAvg f := (1/N!)·Σ_σ f∘actPerm σ` with its
    basic properties (`symAvg_sym`, `symAvg_of_sym`).

The reverse inequality `symBoxEnergy_le_boxEnergy` (the "Perron--Frobenius"
direction: for `0 ≤ v` the ground state may be chosen symmetric — equivalently
antisymmetric components never lower the energy) is NOT elementary: the naive
claim `q(SΨ) ≤ q(Ψ)` is false (it is equivalent to `q(SΨ) ≤ q((1−S)Ψ)`).
It is stated as a target in `Submission/SymmetryGoal.lean` (not imported),
to be proved by a spectral / ground-state-positivity argument later.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- The permutation `σ` acts on configurations by relabelling the particles:
`(actPerm σ x) i = x (σ i)`. -/
noncomputable def actPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) (x : X N) : X N :=
  fun i => x (σ i)

/-- A function is permutation invariant (bosonic) if it is unchanged under
every relabelling of the particles. -/
def PermInvariant (N : ℕ) (f : X N → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ x : X N, f (actPerm N σ x) = f x

/-- Composition law of the permutation action:
`σ · (τ · x) = (σ ∘ τ) · x` (the outer permutation is composed on the left). -/
lemma actPerm_comp (N : ℕ) (σ τ : Equiv.Perm (Fin N)) (x : X N) :
    actPerm N σ (actPerm N τ x) = actPerm N (σ.trans τ) x := by
  ext i
  rfl

/-- The box is invariant under every permutation of the particles. -/
lemma actPerm_mem_box_iff {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) (x : X N) :
    actPerm N σ x ∈ box N L ↔ x ∈ box N L := by
  constructor
  · intro h i k
    simpa [actPerm] using h (σ.symm i) k
  · intro h i k
    simpa [actPerm] using h (σ i) k

/-! ## The open box and the permutation symmetrisation machinery -/

/-- The open box `(0,L)^{3N}`, strictly inside the (closed) box. -/
def openBox (N : ℕ) (L : ℝ) : Set (X N) := {x | ∀ i k, (x i).ofLp k ∈ Set.Ioo 0 L}

lemma openBox_isOpen {N : ℕ} (L : ℝ) : IsOpen (openBox N L) := by
  rw [show openBox N L = ⋂ i : Fin N, ⋂ k : Fin 3,
      (fun x : X N => (x i).ofLp k) ⁻¹' Set.Ioo 0 L by
        ext x; simp [openBox]]
  exact isOpen_iInter_of_finite (fun i =>
    isOpen_iInter_of_finite (fun k =>
      IsOpen.preimage (by fun_prop : Continuous fun x : X N => (x i).ofLp k) isOpen_Ioo))

lemma openBox_subset_box {N : ℕ} {L : ℝ} : openBox N L ⊆ box N L := by
  intro x hx
  rw [mem_box_iff]
  intro i k
  exact Set.Ioo_subset_Icc_self (hx i k)

/-- The open box lies strictly inside the box, hence in its interior. -/
lemma openBox_subset_interior_box {N : ℕ} (L : ℝ) : openBox N L ⊆ interior (box N L) := by
  exact interior_maximal (openBox_subset_box (N := N) (L := L)) (openBox_isOpen L)

/-- The open box is invariant under every permutation of the particles. -/
lemma actPerm_mem_openBox_iff {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) (x : X N) :
    actPerm N σ x ∈ openBox N L ↔ x ∈ openBox N L := by
  constructor
  · intro h i k
    simpa [actPerm, openBox] using h (σ.symm i) k
  · intro h i k
    simpa [actPerm, openBox] using h (σ i) k

/-- The permutation `σ` as a continuous ℝ-linear map on the configuration space. -/
noncomputable def actPermL (N : ℕ) (σ : Equiv.Perm (Fin N)) : X N →L[ℝ] X N :=
  ⟨{ toFun := fun x => actPerm N σ x
     map_add' := by intro x y; ext i; rfl
     map_smul' := by intro a x; ext i; rfl },
   LinearMap.continuous_of_finiteDimensional _⟩

/-- Permutations of the particles act continuously. -/
lemma actPerm_continuous {N : ℕ} (σ : Equiv.Perm (Fin N)) : Continuous (actPerm N σ) := by
  exact (actPermL N σ).continuous

/-- Precomposition with a particle permutation preserves smoothness. -/
lemma permComp_contDiff {N : ℕ} (σ : Equiv.Perm (Fin N)) {f : X N → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x : X N => f (actPerm N σ x)) := by
  exact (ContDiff.comp_continuousLinearMap (f := f) (g := (actPermL N σ)) hf)

/-- The topological support of `f ∘ T` is contained in the preimage of the
topological support of `f` under a continuous `T`. -/
lemma tsupport_comp_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (T : X → Y) (hT : Continuous T) :
    tsupport (f ∘ T) ⊆ T ⁻¹' (tsupport f) := by
  intro x hx
  have hsup : Function.support (f ∘ T) ⊆ T ⁻¹' (tsupport f) := by
    intro y hy
    exact subset_tsupport f (by simpa using hy)
  exact closure_minimal hsup ((isClosed_tsupport f).preimage hT) hx

/-- The topological support of a finite sum is contained in the union of the
topological supports of the summands. -/
lemma tsupport_fintype_sum_subset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    (f : ι → X → ℝ) :
    tsupport (fun x => ∑ i, f i x) ⊆ ⋃ i, tsupport (f i) := by
  have hsum : Function.support (fun x => ∑ i, f i x) ⊆ ⋃ i : ι, tsupport (f i) := by
    intro y hy
    have hne : (∑ i : ι, f i y) ≠ 0 := hy
    have hex : ∃ i, f i y ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      simpa using (Finset.sum_eq_zero (s := Finset.univ) (fun i hi => h i))
    rcases hex with ⟨i, hfi⟩
    exact Set.mem_iUnion.mpr ⟨i, subset_tsupport (f i) hfi⟩
  calc
    tsupport (fun x => ∑ i, f i x) = closure (Function.support (fun x => ∑ i, f i x)) := rfl
    _ ⊆ ⋃ i : ι, tsupport (f i) :=
      closure_minimal hsum (isClosed_iUnion_of_finite (fun i => isClosed_tsupport (f i)))

/-- A permutation of a function supported in the open box is supported there too. -/
lemma perm_tsupport_openBox {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) {f : X N → ℝ}
    (hf : tsupport f ⊆ openBox N L) :
    tsupport (fun x : X N => f (actPerm N σ x)) ⊆ openBox N L := by
  calc
    tsupport (fun x => f (actPerm N σ x)) ⊆ (actPerm N σ) ⁻¹' (tsupport f) := by
      simpa [Function.comp_def] using (tsupport_comp_preimage (f := f) (T := actPerm N σ)
        (actPerm_continuous σ))
    _ ⊆ (actPerm N σ) ⁻¹' openBox N L := Set.preimage_mono hf
    _ ⊆ openBox N L := by
      intro x hx
      exact (actPerm_mem_openBox_iff σ x).mp hx

/-- The permutation average of a function supported in the open box is
supported there too. -/
lemma permSum_tsupport_openBox {N : ℕ} {L : ℝ} {f : X N → ℝ}
    (hf : tsupport f ⊆ openBox N L) :
    tsupport (fun x : X N => ∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)) ⊆ openBox N L := by
  calc
    tsupport (fun x : X N => ∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x))
        ⊆ ⋃ σ : Equiv.Perm (Fin N), tsupport (fun x => f (actPerm N σ x)) :=
          tsupport_fintype_sum_subset (fun σ x => f (actPerm N σ x))
    _ ⊆ openBox N L := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨σ, hxσ⟩
      exact perm_tsupport_openBox σ hf hxσ

/-- A symmetric trial state: a `CInfty0Box` function that is permutation
invariant. -/
structure SymBox (N : ℕ) (L : ℝ) extends CInfty0Box N L where
  /-- Bosonic symmetry: invariant under particle relabellings. -/
  sym : PermInvariant N toFun

instance (N : ℕ) (L : ℝ) : CoeFun (SymBox N L) (fun _ ↦ X N → ℝ) where
  coe Ψ := Ψ.toFun

/-- The (bosonic) symmetric ground-state energy of `N` particles in a box of
side `L`. -/
noncomputable def symBoxEnergy (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  ⨅ Ψ : SymBox N L, ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] /
    ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2

/-- The quotient of a symmetric state as a general state (same value). -/
lemma symBox_quot_eq {N : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : SymBox N L) :
    ⟪(Ψ.toCInfty0Box : X N → ℝ), 𝓗 N v (Ψ.toCInfty0Box : X N → ℝ)⟫_[N,L] /
      ‖(Ψ.toCInfty0Box : X N → ℝ)‖_[N,L] ^ 2 =
    ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] /
      ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2 := by
  rfl

/-- The Rayleigh quotient over the full trial space (as a function of the
trial state). -/
noncomputable def fullQuot (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) : ℝ :=
  ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2

/-- The Rayleigh quotient over the symmetric trial space. -/
noncomputable def symQuot (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : SymBox N L) : ℝ :=
  ⟪(Ψ : X N → ℝ), 𝓗 N v (Ψ : X N → ℝ)⟫_[N,L] / ‖(Ψ : X N → ℝ)‖_[N,L] ^ 2

/-- The two quotients coincide for symmetric states (forgetful map). -/
lemma fullQuot_symQuot {N : ℕ} {L : ℝ} (v : ℝ³ → ℝ) (Ψ : SymBox N L) :
    fullQuot N L v Ψ.toCInfty0Box = symQuot N L v Ψ := by
  rfl

/-- The Rayleigh quotient of every admissible state is nonnegative for `0 ≤ v`. -/
lemma fullQuot_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box N L) : 0 ≤ fullQuot N L v Ψ := by
  unfold fullQuot
  exact div_nonneg (boxEnergy_num_nonneg hL hv Ψ) (sq_nonneg _)

/-- The set of Rayleigh quotients over the full trial space is bounded below
(by zero) for `0 ≤ v`. -/
lemma fullQuot_bddBelow {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    BddBelow (Set.range (fun Ψ : CInfty0Box N L => fullQuot N L v Ψ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨Ψ, rfl⟩
  exact fullQuot_nonneg hL hv Ψ

/-- The symmetric trial space is nonempty (`0 < L`): the permutation average of
a bump supported in the open box. -/
lemma nonempty_SymBox (N : ℕ) {L : ℝ} (hL : 0 < L) : Nonempty (SymBox N L) := by
  -- centre of the box: every particle at (L/2, L/2, L/2)
  let c : X N := fun _ : Fin N => WithLp.toLp 2 (fun _ : Fin 3 => L / 2)
  have hcO : c ∈ openBox N L := by
    intro i k
    dsimp [c, openBox]
    have hpos : 0 < L / 2 := by linarith
    have hlt : L / 2 < L := by linarith
    exact ⟨hpos, hlt⟩
  have hO_nhds : openBox N L ∈ 𝓝 c := (openBox_isOpen (N := N) L).mem_nhds hcO
  obtain ⟨f, hts, _hcs, hcd, _hrange, hfval⟩ :=
    exists_contDiff_tsupport_subset (E := X N) (s := openBox N L) (x := c) (n := ⊤) hO_nhds
  -- the permutation average (un-normalised) of `f`
  let G : X N → ℝ := fun x => ∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)
  have hcdG : ContDiff ℝ ∞ G := by
    dsimp [G]
    exact ContDiff.sum (s := Finset.univ) (fun σ hσ => permComp_contDiff σ hcd)
  have htsG : tsupport G ⊆ openBox N L := by
    dsimp [G]
    exact permSum_tsupport_openBox hts
  have hsymG : PermInvariant N G := by
    intro σ x
    dsimp [G]
    calc
      (∑ τ : Equiv.Perm (Fin N), f (actPerm N τ (actPerm N σ x)))
          = ∑ τ : Equiv.Perm (Fin N), f (actPerm N (τ.trans σ) x) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rfl
      _ = ∑ τ : Equiv.Perm (Fin N), f (actPerm N τ x) := by
            change (∑ τ : Equiv.Perm (Fin N), f (actPerm N (σ * τ) x)) =
              ∑ τ : Equiv.Perm (Fin N), f (actPerm N τ x)
            exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => f (actPerm N τ x))
  have hneG : G ≠ 0 := by
    intro hG0
    have hc : G c ≠ 0 := by
      dsimp [G]
      have hperm : ∀ σ : Equiv.Perm (Fin N), actPerm N σ c = c := by
        intro σ
        ext i
        rfl
      have hfσ : ∀ σ : Equiv.Perm (Fin N), f (actPerm N σ c) = 1 := by
        intro σ
        rw [hperm σ, hfval]
      calc
        (∑ σ : Equiv.Perm (Fin N), f (actPerm N σ c)) = ∑ σ : Equiv.Perm (Fin N), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hfσ σ
        _ = (Fintype.card (Equiv.Perm (Fin N)) : ℝ) := by simp
        _ = (Nat.factorial N : ℝ) := by simp [Fintype.card_perm]
        _ ≠ 0 := by positivity
    exact hc (congrFun hG0 c)
  refine ⟨⟨⟨G, ?_, ?_, ?_⟩, hsymG⟩⟩
  · exact hcdG.contDiffOn
  · exact htsG.trans (openBox_subset_interior_box (N := N) L)
  · exact hneG

/-- Trivial direction: the full (non-symmetric) infimum is no larger than the
symmetric one.  (For the reverse — the Perron--Frobenius direction — see
`Submission/SymmetryGoal.lean`.) -/
theorem boxEnergy_le_symBoxEnergy {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L)
    (hv : 0 ≤ v) : boxEnergy N L v ≤ symBoxEnergy N L v := by
  haveI : Nonempty (SymBox N L) := nonempty_SymBox N hL
  have hbdd : BddBelow (Set.range (fun Ψ : CInfty0Box N L => fullQuot N L v Ψ)) :=
    fullQuot_bddBelow hL hv
  change (⨅ Ψ : CInfty0Box N L, fullQuot N L v Ψ) ≤
    (⨅ Ψ : SymBox N L, symQuot N L v Ψ)
  apply le_ciInf
  intro Ψs
  calc
    (⨅ Ψ : CInfty0Box N L, fullQuot N L v Ψ) ≤ fullQuot N L v Ψs.toCInfty0Box :=
      ciInf_le hbdd Ψs.toCInfty0Box
    _ = symQuot N L v Ψs := fullQuot_symQuot v Ψs

/-- The symmetrization average: `(symAvg f)(x) = (1/N!)·Σ_σ f(σ·x)`. -/
noncomputable def symAvg (N : ℕ) (f : X N → ℝ) : X N → ℝ :=
  fun x => (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)

/-- The average of a function over the permutation group is invariant. -/
lemma symAvg_sym (N : ℕ) (f : X N → ℝ) : PermInvariant N (symAvg N f) := by
  intro σ x
  dsimp [symAvg]
  congr 1
  calc
    (∑ τ : Equiv.Perm (Fin N), f (actPerm N τ (actPerm N σ x)))
        = ∑ τ : Equiv.Perm (Fin N), f (actPerm N (τ.trans σ) x) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          rfl
    _ = ∑ τ : Equiv.Perm (Fin N), f (actPerm N τ x) := by
          change (∑ τ : Equiv.Perm (Fin N), f (actPerm N (σ * τ) x)) =
            ∑ τ : Equiv.Perm (Fin N), f (actPerm N τ x)
          exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ => f (actPerm N τ x))

/-- An already invariant function is fixed by the average. -/
lemma symAvg_of_sym {N : ℕ} {f : X N → ℝ} (hf : PermInvariant N f) : symAvg N f = f := by
  funext x
  dsimp [symAvg]
  calc
    (1 / (Nat.factorial N : ℝ)) * (∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x))
        = (1 / (Nat.factorial N : ℝ)) * (∑ σ : Equiv.Perm (Fin N), f x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hf σ x
    _ = f x := by
          have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
          rw [show (∑ σ : Equiv.Perm (Fin N), f x) = (Nat.factorial N : ℝ) * f x by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
            simp [nsmul_eq_mul]]
          field_simp [hfac]

/-- The symmetrization average of a smooth compactly supported function is
smooth and supported inside the same box. -/
lemma symAvg_contDiff {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (symAvg N f) := by
  change ContDiff ℝ ∞ (fun x : X N =>
      (1 / (Nat.factorial N : ℝ)) * (∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)))
  have hsum : ContDiff ℝ ∞ (fun x : X N => ∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)) := by
    exact ContDiff.sum (s := Finset.univ) (fun σ hσ => permComp_contDiff σ hf)
  exact ContDiff.const_smul (1 / (Nat.factorial N : ℝ)) hsum

/-- The symmetrization average preserves the support inside the box. -/
lemma symAvg_support_box {N : ℕ} {L : ℝ} {f : X N → ℝ}
    (hsup : Function.support f ⊆ box N L) :
    Function.support (symAvg N f) ⊆ box N L := by
  intro x hx
  have hne : (symAvg N f) x ≠ 0 := hx
  have hs : (∑ σ : Equiv.Perm (Fin N), f (actPerm N σ x)) ≠ 0 := by
    intro hs0
    apply hne
    dsimp [symAvg]
    rw [hs0, mul_zero]
  have hex : ∃ σ : Equiv.Perm (Fin N), f (actPerm N σ x) ≠ 0 := by
    by_contra h
    push Not at h
    apply hs
    simpa using (Finset.sum_eq_zero (s := Finset.univ) (fun σ hσ => h σ))
  rcases hex with ⟨σ, hfσ⟩
  exact (actPerm_mem_box_iff σ x).mp (hsup hfσ)

end BoseGases

end Submission
