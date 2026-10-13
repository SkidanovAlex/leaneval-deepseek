import Mathlib
import Submission.Work.WilE7.Endgame.E2B.GSheets
import Submission.Work.WilE7.Endgame.Bv2.refAux
import Submission.Work.WilE7.Endgame.Bv2.refDec
import Submission.Work.WilE7.Endgame.E2_activeFamily

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair absPairSet absLevelPairSet)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## Structural lemmas about `IsCylDecompOn`

The base cell `b` of the `G`-branch is the `π_n`-image of a member `κ` of the decomposition `B` of
`cubeC (n+1)` (the hypothesis `hb`), hence it is a cell of dimension `n` and it is nonempty.  These
two facts are exactly what `E2Pkg.hSheet` needs from the base cell besides its activity. -/

/-- Every member of a cylindrical decomposition `IsCylDecompOn n A C` is a cell. -/
theorem isCell_of_mem_isCylDecompOn : ∀ {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))}, IsCylDecompOn n A C → ∀ c ∈ C, IsCell n c := by
  intro n
  induction n with
  | zero =>
      intro A C h c hc
      rcases h with ⟨-, hC⟩ | ⟨-, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hc
        subst hc
        exact IsCell.zero
      · subst hC
        exact absurd hc (Finset.notMem_empty c)
  | succ n _ => intro A C h c hc; exact (h.1 c hc).1

/-- Every member of a cylindrical decomposition `IsCylDecompOn n A C` is nonempty. -/
theorem nonempty_of_mem_isCylDecompOn : ∀ {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))}, IsCylDecompOn n A C → ∀ c ∈ C, c.Nonempty := by
  intro n
  induction n with
  | zero =>
      intro A C h c hc
      rcases h with ⟨-, hC⟩ | ⟨-, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hc
        subst hc
        exact ⟨fun i => i.elim0, trivial⟩
      · subst hC
        exact absurd hc (Finset.notMem_empty c)
  | succ n _ => intro A C h c hc; exact (h.1 c hc).2

/-- The active subfamily of a list of strata: the members whose `π_n`-image captures `b`.
No "active or avoided" dichotomy is needed: the subfamily is cut out by classical decidability of
the activity predicate, and it contains every active member of the list. -/
theorem exists_activeFamily {n m : ℕ} (Cand : List (Stratum 0 (n + (m + 1))))
    (b : Set (Fin n → ℝ)) :
    ∃ (r : ℕ) (Sf : Fin r → Stratum 0 (n + (m + 1))),
      r ≤ Cand.length ∧
      (∀ i, Sf i ∈ Cand) ∧
      (∀ i, b ⊆ projFirst n (m + 1) '' absSet (Sf i)) ∧
      (∀ S ∈ Cand, b ⊆ projFirst n (m + 1) '' absSet S → ∃ i, Sf i = S) := by
  classical
  let Q : Stratum 0 (n + (m + 1)) → Prop := fun S => b ⊆ projFirst n (m + 1) '' absSet S
  let L : List (Stratum 0 (n + (m + 1))) := Cand.filter (fun S => decide (Q S))
  have hL : ∀ S, S ∈ L ↔ S ∈ Cand ∧ Q S := by
    intro S
    have h1 : S ∈ L ↔ S ∈ Cand ∧ decide (Q S) = true := by
      simp only [L, List.mem_filter]
    rw [h1, decide_eq_true_iff]
  refine ⟨L.length, fun i => L.get i, ?_, ?_, ?_, ?_⟩
  · exact List.length_filter_le _ _
  · intro i
    exact List.mem_of_mem_filter (List.get_mem L i)
  · intro i
    exact ((hL _).mp (List.get_mem L i)).2
  · intro S hS hbS
    have hSL : S ∈ L := (hL S).mpr ⟨hS, hbS⟩
    obtain ⟨i, hi⟩ := List.exists_mem_iff_get.mp ⟨S, hSL, rfl⟩
    exact ⟨i, hi.symm⟩

/-! ## The sheet data of the `G`-branch -/

theorem gcaseSheetsData {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)}
    {Y : Fin l → WilkiesDesign.E.SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (hB : CompatHyp c c2 P B)
    (b : Set (Fin n → ℝ)) (hb : b ∈ B.image (fun κ => Fin.init '' κ))
    (hG : GHyp c c2 P b) :
    ∃ G : GSheets c c2 P b, True := by
  classical
  -- `b` is a cell, hence nonempty
  have hB' : IsCylDecompOn n (Fin.init '' (cubeC (n + 1))) (B.image (fun κ => Fin.init '' κ)) :=
    hB.1.2.2.2
  have hcellb : IsCell n b := isCell_of_mem_isCylDecompOn hB' b hb
  have hneb : b.Nonempty := nonempty_of_mem_isCylDecompOn hB' b hb
  -- the active candidates
  obtain ⟨r, S, hSlen, hScand, hSact, hScomp⟩ := exists_activeFamily (n := n) (m := m) P.Cand b
  -- the sheets over `b` of every active candidate, from the sheet provision `P.hSheet`
  have hsheet : ∀ t : Fin r, ∃ (kk : ℕ) (s : Fin kk → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
      0 < kk ∧ (∀ j, ContinuousOn (s j) b) ∧
      (∀ x ∈ b, Function.Injective fun j : Fin kk => s j x) ∧
      (∀ (j : Fin kk) (x : Fin n → ℝ), x ∈ b → Fin.append x (s j x) ∈ absSet (S t)) ∧
      (∀ x ∈ b, (fiber (absSet (S t)) x).ncard = kk) ∧
      (∀ z ∈ absSet (S t), projFirst n (m + 1) z ∈ b →
        ∃ j : Fin kk, s j (projFirst n (m + 1) z) = projSnd n (m + 1) z) ∧
      kk ≤ c.Ps.eval (c.Dq.eval D) := by
    intro t
    have hcand := P.specCand (S t) (hScand t)
    obtain ⟨Wl, hWlg, hWlun, hWlpb⟩ := P.specSig.2.2.2.1 (S t) (hScand t)
    exact P.hSheet (S t) b P.Sig Wl hcand.1 hcand.2.1 hcand.2.2.1 hcand.2.2.2.2
      hcellb hneb (hSact t) (fun Z hZ => hG.1 Z hZ) (P.specSig.2.2.1 (S t) (hScand t))
      (fun W hW => (hWlg W hW).1) (fun W hW => (hWlg W hW).2) hWlun hWlpb
  let kc : Fin r → ℕ := fun t => (hsheet t).choose
  let sc : (t : Fin r) → Fin (kc t) → (Fin n → ℝ) → (Fin (m + 1) → ℝ) :=
    fun t => (hsheet t).choose_spec.choose
  have hkpos : ∀ t, 0 < kc t := fun t => (hsheet t).choose_spec.choose_spec.1
  have hcont : ∀ t j, ContinuousOn (sc t j) b :=
    fun t j => (hsheet t).choose_spec.choose_spec.2.1 j
  have hinj : ∀ t x, x ∈ b → Function.Injective fun j => sc t j x :=
    fun t x hx => (hsheet t).choose_spec.choose_spec.2.2.1 x hx
  have hsub : ∀ t j x, x ∈ b → Fin.append x (sc t j x) ∈ absSet (S t) :=
    fun t j x hx => (hsheet t).choose_spec.choose_spec.2.2.2.1 j x hx
  have hcard : ∀ t x, x ∈ b → (fiber (absSet (S t)) x).ncard = kc t :=
    fun t x hx => (hsheet t).choose_spec.choose_spec.2.2.2.2.1 x hx
  have hcov : ∀ t z, z ∈ absSet (S t) → projFirst n (m + 1) z ∈ b →
      ∃ j, sc t j (projFirst n (m + 1) z) = projSnd n (m + 1) z :=
    fun t z hz hzb => (hsheet t).choose_spec.choose_spec.2.2.2.2.2.1 z hz hzb
  have hcle : ∀ t, kc t ≤ c.Ps.eval (c.Dq.eval D) :=
    fun t => (hsheet t).choose_spec.choose_spec.2.2.2.2.2.2
  refine ⟨?_, trivial⟩
  exact GSheets.mk r S hScand hSact
    (fun t => (P.specCand (S t) (hScand t)).1)
    (fun t => (P.specCand (S t) (hScand t)).2.1)
    (fun t => (P.specCand (S t) (hScand t)).2.2.1)
    (fun t => (P.specCand (S t) (hScand t)).2.2.2.2)
    kc hkpos sc hcont hinj hsub hcov hcard hcle hScomp hSlen

end

end Work.WilE7.Endgame.E2B
