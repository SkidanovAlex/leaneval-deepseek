import Mathlib
import Submission.ChainAlignment
import Submission.IntervalCoverU
import Submission.WalkAlignment

open LeanEval.KnotTheory.Quadrisecant
open Set
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

/-!
# Milestone-2 (iv) step 6, brick (b) — the list → ℕ bridging: rebuilding
the ℕ-indexed piece family from an aligned head and tail list

`ChainAlignment.lean` (S121) proved the alignment theorems over LISTS of
pieces: `exists_aligned_subpieces` produces the aligned sub-pieces as a
head `sp` and a tail list `qs` (with `List.Forall₂ IsSubPiece` against
the original tail and `AlignedTotality (sp :: qs)`); `WalkAlignment.lean`
(S122) instantiated them at the S115 walk data (`walk_prefix_alignment`).
The ℕ-indexed identification theorem
`chain_transport_class_coordinate` (S119, `IntervalChainU.lean`), however,
is stated over a ℕ-family `p : ℕ → MonoPiece` and the tail list
`chainTail p 0 n` — so the aligned output must be REBUILT as a ℕ-family
before the class-coordinate identification can be applied to it.  This
module is that BRIDGE:

1. **`familyFromAligned`** — the ℕ-family rebuilt from an aligned head
   and tail list: `q 0 = sp`, `q (j+1) = qs[j]` (via `List.getD`, with
   default `p (j+1)`), so past the list the family falls back to `p`
   (`familyFromAligned_zero`, `familyFromAligned_succ`,
   `familyFromAligned_get` — the values of `q` inside the list,
   `familyFromAligned_beyond` — the values past the list);
2. **tail-chain arithmetic** — `chainTail_length` (the length of
   `chainTail p k n` is `n`) and `chainTail_get_eq` (the elements of
   `chainTail p k n` are `p (k+i+1)`) — the elementary facts that let the
   tail equality be proved elementwise;
3. **the bridging lemma** — `chainTail_familyFromAligned`: if
   `qs.length = n` then `chainTail (familyFromAligned p sp qs) 0 n = qs`
   — the tail of the rebuilt family is exactly the aligned list, so
   `ChainDomain (q 0 :: chainTail q 0 n)` is the aligned
   `ChainDomain (sp :: qs)` (proved by `List.ext_get`: lengths equal by
   `chainTail_length`; elements equal by `chainTail_get_eq` +
   `familyFromAligned_get`);
4. **the walk instance** — `walk_aligned_family`: from the S115 walk
   overlap data and an orbit `htr` of a start parameter through the first
   `n` walk junction pieces, there is a ℕ-family `q` that is a sub-piece
   family of the walk pieces on the whole prefix (`q 0` a sub-piece of
   piece `0` containing `x₀`, `chainTail q 0 n` aligned against
   `chainTail w 0 n`) with forward totality
   `AlignedTotality (q 0 :: chainTail q 0 n)` — the exact shape the
   covering lemma will consume (it carries the walk data, the totality
   over the whole aligned prefix, and the correspondence to the original
   chain in one bundle).

The next slice (recorded in the ROADMAP): feed `q` into
`chain_transport_class_coordinate` (transfer `hsub`/`hsem` to the
sub-piece family from the S120 walk data), obtaining the monotone
injective class-coordinate identification over the whole aligned start
interval, and then the partial-union covering statement.  Everything
here is elementary and verified (no axioms, no `sorry`).
-/

/-- Rebuild a ℕ-indexed piece family from an aligned head and tail list:
index `0` is `sp`, index `j+1` reads `qs[j]` (`getD`, default `p (j+1)`),
so beyond the list the family falls back to `p`. -/
def familyFromAligned (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece) : ℕ → MonoPiece
  | 0 => sp
  | j + 1 => qs.getD j (p (j + 1))

/-- The head of the rebuilt family is the aligned head. -/
lemma familyFromAligned_zero (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece) :
    familyFromAligned p sp qs 0 = sp := by
  rfl

/-- The successor values of the rebuilt family read the tail list
(`getD`). -/
lemma familyFromAligned_succ (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece) (j : ℕ) :
    familyFromAligned p sp qs (j + 1) = qs.getD j (p (j + 1)) := by
  rfl

/-- Inside the list, the rebuilt family reads the actual list elements. -/
lemma familyFromAligned_get (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece)
    (i : Fin qs.length) :
    familyFromAligned p sp qs (i.1 + 1) = qs.get i := by
  rw [familyFromAligned_succ]
  exact List.getD_eq_get qs (p (i.1 + 1)) i

/-- The length of a tail chain is its tail length. -/
lemma chainTail_length (p : ℕ → MonoPiece) : ∀ k n : ℕ, (chainTail p k n).length = n := by
  intro k n
  revert k
  induction n with
  | zero => intro k; simp [chainTail]
  | succ n ih => intro k; simp [chainTail, ih (k + 1)]

/-- The elements of a tail chain are the indexed pieces (`p (k+i+1)`). -/
lemma chainTail_get_eq (p : ℕ → MonoPiece) (k n : ℕ) (i : ℕ)
    (hi : i < (chainTail p k n).length) :
    (chainTail p k n).get ⟨i, hi⟩ = p (k + i + 1) := by
  revert k i hi
  induction n with
  | zero =>
      intro k i hi
      simp [chainTail] at hi
  | succ n ih =>
      intro k i hi
      have hlt : i < (p (k + 1) :: chainTail p (k + 1) n).length := by
        simpa [chainTail] using hi
      rcases i with _ | i'
      · change (p (k + 1) :: chainTail p (k + 1) n).get ⟨0, hlt⟩ = p (k + 0 + 1)
        simp
      · change (p (k + 1) :: chainTail p (k + 1) n).get ⟨i' + 1, hlt⟩ = p (k + (i' + 1) + 1)
        rw [List.get_cons_succ]
        have hi' : i' < (chainTail p (k + 1) n).length := by
          have hl : (p (k + 1) :: chainTail p (k + 1) n).length =
              (chainTail p (k + 1) n).length + 1 := by
            rw [List.length_cons]
          omega
        rw [ih (k + 1) i' hi']
        congr 1
        omega

/-- **List → ℕ bridging for an aligned prefix.**  If `qs` is the tail
list of an aligned prefix of length `n`, the ℕ-family
`q := familyFromAligned p sp qs` has `chainTail q 0 n = qs` — the tail of
the rebuilt family is exactly the aligned list (so `ChainDomain
(q 0 :: chainTail q 0 n)` is the aligned `ChainDomain (sp :: qs)`). -/
lemma chainTail_familyFromAligned (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece)
    (n : ℕ) (hqsl : qs.length = n) :
    chainTail (familyFromAligned p sp qs) 0 n = qs := by
  apply List.ext_get
  · rw [chainTail_length]
    exact hqsl.symm
  · intro i h₁ h₂
    have hi₁ : i < n := by
      have hl := chainTail_length (familyFromAligned p sp qs) 0 n
      omega
    have hconv : 0 + i + 1 = i + 1 := by omega
    rw [chainTail_get_eq (familyFromAligned p sp qs) 0 n i h₁]
    rw [hconv]
    exact familyFromAligned_get p sp qs ⟨i, h₂⟩

/-- Beyond the aligned prefix the rebuilt family agrees with `p`. -/
lemma familyFromAligned_beyond (p : ℕ → MonoPiece) (sp : MonoPiece) (qs : List MonoPiece)
    (n i : ℕ) (hi : n < i) (hqsl : qs.length = n) :
    familyFromAligned p sp qs i = p i := by
  rcases i with _ | i'
  · exfalso
    omega
  · rw [familyFromAligned_succ]
    rw [List.getD_eq_default qs (p (i' + 1)) (by omega : qs.length ≤ i')]

/-- A `Forall₂` correspondence forces equal lengths. -/
lemma forall₂_length_eq {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons h₁ h₂ ih =>
      rw [List.length_cons, List.length_cons, ih]

/-! ## The walk instance -/

/-- **Walk-aligned family (the bridging at the walk data).**  From the
S115 walk overlap data and an orbit `htr` of a start parameter through
the first `n` walk junction pieces, there is a ℕ-family `q` of pieces
that is a sub-piece family of the walk pieces on the whole prefix — `q 0`
a sub-piece of walk piece `0` containing `x₀`, `chainTail q 0 n` the
sub-pieces of the corresponding chain pieces in order — along which
every transport lands forward (`AlignedTotality (q 0 :: chainTail q 0
n)`).  (Assembly: `walk_prefix_alignment` gives `sp`/`qs`; the ℕ-family
`q := familyFromAligned w sp qs` has `q 0 = sp` and `chainTail q 0 n =
qs` by `chainTail_familyFromAligned`, with `qs.length = n` from the
`Forall₂` correspondence against `chainTail w 0 n`.) -/
theorem walk_aligned_family {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (cl : ℕ → OSub r) (e : ℕ → ℕ)
    (hoverlap : ∀ n : ℕ, (OChartTraceSet h hqf hgp (cl (e n)) ∩
        OChartTraceSet h hqf hgp (cl (e (n + 1)))).Nonempty) (n : ℕ)
    (x₀ : ChartInterval (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
      (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi)
    (htr : transports (walkJunctionPiece h hqf hgp cl e hoverlap 0)
      (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) x₀) :
    ∃ q : ℕ → MonoPiece,
      (∃ hsub : Set.Ioo (q 0).lo (q 0).hi ⊆ Set.Ioo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).lo
          (walkJunctionPiece h hqf hgp cl e hoverlap 0).hi,
          q 0 = subMonoPiece (walkJunctionPiece h hqf hgp cl e hoverlap 0) hsub) ∧
      ((x₀ : ℝ) ∈ Set.Ioo (q 0).lo (q 0).hi) ∧
      AlignedTotality (q 0 :: chainTail q 0 n) ∧
      List.Forall₂ IsSubPiece (chainTail q 0 n)
        (chainTail (walkJunctionPiece h hqf hgp cl e hoverlap) 0 n) := by
  rcases walk_prefix_alignment h hqf hgp cl e hoverlap n x₀ htr with ⟨sp, qs, hsp, hx₀sp, htot, hcorr⟩
  let q : ℕ → MonoPiece := familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap) sp qs
  have hqsl : qs.length = n := by
    rw [forall₂_length_eq hcorr, chainTail_length]
  have htail : chainTail q 0 n = qs := by
    exact chainTail_familyFromAligned (walkJunctionPiece h hqf hgp cl e hoverlap) sp qs n hqsl
  have hq0 : q 0 = sp := by rfl
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · rcases hsp with ⟨hsub, heq⟩
    refine ⟨hsub, ?_⟩
    exact heq
  · exact hx₀sp
  · rw [hq0, htail]
    exact htot
  · rw [htail]
    exact hcorr

end LeanEval.KnotTheory.Quadrisecant
