/-
  Area E7 / the `CoreLT_succ` endgame, node **E2B**: the `Σ`-branch of the per-base-cell refinement.

  If the base cell `b` happens to lie inside the `π_n`-image of a member `S₀` of the `Σ`-family
  `P.Sig` (i.e. inside the *base* projection of a vertical-pair stratum), then no new decomposition
  has to be built: the cells of `B` lying over `b` already do the job.

  * They decompose the fibre `cubeC (n+1) ∩ {Fin.init · ∈ b}` (`DimAPI.cylDecomp_fiber`), and each
    of them projects onto `b` — so clauses (a) (first disjunct), (b) and (c) of `RefineConcl` are
    immediate.
  * Clause (d) — compatibility of the cells over `b` with the *outer* pieces `π_{n+1}(X i)` — is the
    genuine Σ-content, and is supplied by the machinery of §B1:

    - `P.specZ` provides, for every piece `T` and every `S ∈ P.Sig`, a fibre product
      `Z_{T,S} ∈ P.Zl` with `π_{n+1}(Z_{T,S}) = π_{n+1}(absSet T) ∩ {Fin.init · ∈ π_n(S)}`;
    - `CompatHyp` says the cells of `B` are compatible with `π_{n+1}(Z_{T,S})` (for every member of
      `P.Zl`);
    - since the cells over `b` have base image `b ⊆ π_n(S₀)`, they lie in the "`U`" of the identity
      `π_{n+1}(Z) = π_{n+1}(absSet T) ∩ U`, so `E2_sigmaCase` (`compat_of_fibreProd`) converts the
      compatibility with `π_{n+1}(Z)` into compatibility with `π_{n+1}(absSet T)`;
    - finally `PiecesSpec` identifies `π_{n+1}(X i)` with the (list-)union of the `π_{n+1}(absSet T)`
      over the pieces `T` with `T.1 = i`, and compatibility transfers to that union
      (`compat_of_iUnion_list_map`, the `map`-form of `CoreStep.compat_of_iUnion_list`).
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Vocab
import Submission.Work.WilE7.Endgame.E2B.Pkg
import Submission.Work.WilE7.Endgame.E2_sigmaCase

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair)

/-! ## §1. Compatibility with a list-indexed union -/

/-- **Compatibility transfers to a list-indexed union.**  If `S` is the union of the sets `f B` over
a list `l` and `κ` is contained in, or disjoint from, each of them, then the same holds with `S`.
This is the `map`-form of `Work.WilE7.CoreStep.compat_of_iUnion_list`, which the `Pie`-coverage
of `PiecesSpec` produces. -/
theorem compat_of_iUnion_list_map {X Y : Type*} {l : List Y} {f : Y → Set X} {S κ : Set X}
    (hS : S = ⋃ B ∈ l, f B) (h : ∀ B ∈ l, κ ⊆ f B ∨ Disjoint κ (f B)) :
    κ ⊆ S ∨ Disjoint κ S := by
  by_cases hsome : ∃ B ∈ l, κ ⊆ f B
  · obtain ⟨B, hB, hBκ⟩ := hsome
    left
    intro x hx
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨B, hB, hBκ hx⟩
  · right
    rw [Set.disjoint_left]
    intro x hx hxS
    rw [hS, Set.mem_iUnion₂] at hxS
    obtain ⟨B, hB, hxB⟩ := hxS
    by_cases hsub : κ ⊆ f B
    · exact hsome ⟨B, hB, hsub⟩
    · exact Set.disjoint_left.mp ((h B hB).resolve_left hsub) hx hxB

/-! ## §2. The Σ-branch -/

/-- The first tool of the Σ-branch: for the fixed Σ-witness `S₀`, every piece `T ∈ P.Pie` is either
covered by, or disjoint from, `π_{n+1}(absSet T)`, the compatibility being inherited from the fibre
product `Z_{T,S₀} ∈ P.Zl` and the base containment `b ⊆ π_n(S₀)`. -/
theorem sigma_dichotomy {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)}
    {Y : Fin l → SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (hB : CompatHyp c c2 P B)
    (b : Set (Fin n → ℝ)) {S₀ : SemiPf (n + pPair n m)} (hS₀mem : S₀ ∈ P.Sig)
    (hS₀ : b ⊆ projFirst n (pPair n m) '' S₀.set)
    {κ : Set (Fin (n + 1) → ℝ)} (hκ : κ ∈ B.filter (fun κ => Fin.init '' κ = b)) :
    ∀ q : Fin P.Pie.length,
      κ ⊆ projFirst (n + 1) m '' absSet (P.Pie.get q).2 ∨
        Disjoint κ (projFirst (n + 1) m '' absSet (P.Pie.get q).2) := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hS₀mem
  have hdec : IsCylDecompOn (n + 1) (cubeC (n + 1)) B := hB.1
  have hZl := hB.2.1
  intro q
  obtain ⟨i', -, hZ⟩ := P.specZ.2 q j
  rw [hj] at hZ
  have hcompat : ∀ κ' ∈ B.filter (fun κ => Fin.init '' κ = b),
      κ' ⊆ projFirst (n + 1) (m + pPair n m) '' (P.Zl.get i').set ∨
        Disjoint κ' (projFirst (n + 1) (m + pPair n m) '' (P.Zl.get i').set) :=
    fun κ' hκ' => hZl i' κ' (Finset.mem_filter.mp hκ').1
  exact (E2_sigmaCase B hdec b (Finset.mem_image.mpr ⟨κ, (Finset.mem_filter.mp hκ).1,
    (Finset.mem_filter.mp hκ).2⟩) (P.Pie.get q).2 S₀ (P.Zl.get i') hZ hS₀ hcompat).2.2.2 κ hκ

theorem sigmaRefine {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (hB : CompatHyp c c2 P B)
    (b : Set (Fin n → ℝ)) (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hSig : ∃ S ∈ P.Sig, b ⊆ WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) :
    RefineConcl c c2 P B b := by
  obtain ⟨S₀, hS₀mem, hS₀⟩ := hSig
  refine ⟨B.filter (fun κ => Fin.init '' κ = b), Or.inl ?_, ?_, ?_, ?_⟩
  · -- every cell over `b` is a cell of `B`
    intro κ hκ
    exact (Finset.mem_filter.mp hκ).1
  · -- the cells over `b` decompose the fibre over `b`
    exact Work.WilE7.DimAPI.cylDecomp_fiber (cubeC (n + 1)) B hB.1 b hb
  · -- every cell over `b` projects onto `b`
    intro κ hκ
    exact (Finset.mem_filter.mp hκ).2
  · -- the Σ-content: compatibility with the outer pieces `π_{n+1}(X i)`
    intro i κ hκ
    have hdichF := sigma_dichotomy c c2 P B hB b hS₀mem hS₀ hκ
    -- the pieces with `p.1 = i` cover `π_{n+1}(X i)`
    refine compat_of_iUnion_list_map (P.specPieces.2.2.2.1 i) ?_
    intro A hA
    obtain ⟨hAPie, -⟩ := List.mem_filter.mp hA
    obtain ⟨q, hq⟩ := List.mem_iff_get.mp hAPie
    rw [← hq]
    exact hdichF q

end

end Work.WilE7.Endgame.E2B
