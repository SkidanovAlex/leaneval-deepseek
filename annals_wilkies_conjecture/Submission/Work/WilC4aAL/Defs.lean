/-
  Work.WilC4aAL.Defs

  Vocabulary for area C4a-AL of the Annals Challenge problem
  `annals_wilkies_conjecture` (Binyamini–Novikov–Zak, *Wilkie's conjecture for Pfaffian
  structures*): the sub-hole `WilkiesDesign.CG.C4a.C4a_arcLift`.

  Mathematical content of the area.  Let `Pᵢ(s,z) = mpoly (c i) s z = z^{dᵢ} + Σ_{j<dᵢ} cᵢⱼ(s) z^j`
  be monic polynomials in `z` with coefficients `cᵢⱼ` analytic at `0`.  Suppose that for every
  small `s > 0` there is a real `z` realising a prescribed sign vector `σ` of the values
  `Pᵢ(s,z)`.  Then there is a *single* real-analytic `ζ` with
  `sign (Pᵢ(r^N, ζ r)) = σ i` for all small `r > 0` (and a fixed `N`).  This is the analytic
  curve-selection step "sign conditions ⇒ analytic selector along the Puiseux branch" that the
  curve-selection induction `C4a_CS_step` consumes.

  The vocabulary below is what the statements in this directory use:
  * `AnalyticBranches` : a family of branches, each analytic at `0`;
  * `BranchCover`      : the real zero set of every `Pᵢ` for small `r` is covered by the
                         branch values (`mpoly (c i) r z = 0 → z = ζ i j r`);
  * `SignVectorOk`     : the sign conditions `σ` are realised at `(r,z)`;
  * `SameSign`         : two reals have the same sign vector at parameter `r`;
  * `CandIdx`, `cand`  : the fixed finite list of *cell representatives* built from the
                         branches (midpoints of pairs of branches) and the two constants `±C`
                         (which lie below/above every branch).
-/
import Submission.Work.Wilkies.CG.C4a.Spec

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

/-- A family of real branches `ζ i j : ℝ → ℝ`, each analytic at `0`. -/
def AnalyticBranches {k : ℕ} (m : Fin k → ℕ) (ζ : ∀ i, Fin (m i) → ℝ → ℝ) : Prop :=
  ∀ i j, AnalyticAt ℝ (ζ i j) 0

/-- **Branch cover of the real zero set.** For all sufficiently small `r > 0`, every real zero
of `z ↦ mpoly (c i) r z` is the value of one of the branches `ζ i j`. -/
def BranchCover {k : ℕ} {d : Fin k → ℕ} (c : ∀ i, Fin (d i) → ℝ → ℝ)
    (m : Fin k → ℕ) (ζ : ∀ i, Fin (m i) → ℝ → ℝ) : Prop :=
  ∃ r₀ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₀, ∀ (i : Fin k) (z : ℝ),
    mpoly (c i) r z = 0 → ∃ j, z = ζ i j r

/-- The sign vector `σ` is realised at the parameter value `r` by the real number `z`. -/
def SignVectorOk {k : ℕ} {d : Fin k → ℕ} (c : ∀ i, Fin (d i) → ℝ → ℝ)
    (σ : Fin k → SignType) (r z : ℝ) : Prop :=
  ∀ i, SignType.sign (mpoly (c i) r z) = σ i

/-- `z` and `z'` have the same sign vector at the parameter value `r`. -/
def SameSign {k : ℕ} {d : Fin k → ℕ} (c : ∀ i, Fin (d i) → ℝ → ℝ) (r z z' : ℝ) : Prop :=
  ∀ i, SignType.sign (mpoly (c i) r z) = SignType.sign (mpoly (c i) r z')

/-- Index type of the cell representatives used in the selection lemma: either a pair of
branches (whose midpoint is taken), or one of the two constants `±C`. -/
def CandIdx (ι : Type*) : Type _ := (ι × ι) ⊕ Bool

instance instFintypeCandIdx {ι : Type*} [Fintype ι] : Fintype (CandIdx ι) :=
  inferInstanceAs (Fintype ((ι × ι) ⊕ Bool))

instance instDecidableEqCandIdx {ι : Type*} [DecidableEq ι] : DecidableEq (CandIdx ι) :=
  inferInstanceAs (DecidableEq ((ι × ι) ⊕ Bool))

instance instNonemptyCandIdx {ι : Type*} : Nonempty (CandIdx ι) :=
  ⟨Sum.inr true⟩

/-- Cell representatives attached to a branch family `ξ` and a constant `C`:
`(ξ t + ξ u)/2` for each pair, and the constants `C`, `-C`.  When `C` bounds every branch these
representatives meet every cell of the decomposition of `ℝ` by the branch values. -/
def cand {ι : Type*} (ξ : ι → ℝ → ℝ) (C : ℝ) : CandIdx ι → ℝ → ℝ
  | Sum.inl tu => fun r => (ξ tu.1 r + ξ tu.2 r) / 2
  | Sum.inr true => fun _ => C
  | Sum.inr false => fun _ => -C

end Work.WilC4aAL
