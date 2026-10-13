/-
  WilG5 — reindexing package (module 2 of the G5 development).

  Here we build the coordinate-reindexing operations that the F-lemma application needs:

    * `reindex_mem` — the *balanced* reindexing: for any map `σ : Fin M → Fin M` and any
      Ω-set `A ⊆ ℝ^M`, the set `{x | x ∘ σ ∈ A}` is again an Ω-set.  The construction is
      `{x | x ∘ σ ∈ A} = projN M (liftLast M A ∩ relSetSwap σ)`: the joint set has the
      target point in its first block and the point of `A` in its last block, with the
      polynomial relation `w j = x (σ j)` in between; `projN` then forgets the `w`-block.

  This is the first genuinely "non-append" reindexing lemma of the development and it is
  what makes arbitrary coordinate permutations available.  The next module
  (`Work.WilG5.Reindex2`) uses it, together with the explicit permutations that move a
  coordinate block to the front, to obtain `coordPre_mem`, `coordImage_mem` and
  `lastN_mem` (see the header of `Basic` for the counterexample that rules out the naive
  recursion for `lastN`).
-/
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-- `lidx M i` and `Fin.natAdd M i` are the same index of `Fin (M + M)`. -/
theorem lidx_eq_natAdd {M : ℕ} (i : Fin M) : lidx M i = Fin.natAdd M i :=
  Fin.ext rfl

/-- The joint set `{(x,w) : w ∈ A, w j = x (σ j)}` projects onto `{x : x ∘ σ ∈ A}`. -/
theorem projN_liftLast_relSetSwap {M : ℕ} (σ : Fin M → Fin M) (A : Set (Fin M → ℝ)) :
    projN M (liftLast M A ∩ relSetSwap σ) = {x : Fin M → ℝ | x ∘ σ ∈ A} := by
  ext x
  constructor
  · rintro ⟨w, hw, hrel⟩
    have hwA : w ∈ A := by
      have hfun : (fun i : Fin M => Fin.append x w (lidx M i)) = w := by
        funext i
        rw [lidx_eq_natAdd, Fin.append_right]
      simpa [liftLast, hfun] using hw
    have hwx : (fun j : Fin M => x (σ j)) = w := by
      funext j
      have := hrel j
      rw [Fin.append_right, Fin.append_left] at this
      exact this.symm
    show (fun j : Fin M => x (σ j)) ∈ A
    rw [hwx]; exact hwA
  · intro hx
    refine ⟨x ∘ σ, ?_, ?_⟩
    · simp only [liftLast, Set.mem_ofPred_eq]
      have hfun : (fun i : Fin M => (Fin.append x (x ∘ σ)) (lidx M i)) = (x ∘ σ) := by
        funext i
        rw [lidx_eq_natAdd, Fin.append_right]
      rw [hfun]; exact hx
    · simp only [relSetSwap, Set.mem_ofPred_eq]
      intro j
      show (Fin.append x (x ∘ σ)) (Fin.natAdd M j) = (Fin.append x (x ∘ σ)) (Fin.castAdd M (σ j))
      rw [Fin.append_right, Fin.append_left]
      rfl

/-- **Balanced reindexing.**  For any `σ : Fin M → Fin M`, the preimage of an Ω-set under
`x ↦ x ∘ σ` is an Ω-set. -/
theorem reindex_mem {M F D : ℕ} (σ : Fin M → Fin M) {A : Set (Fin M → ℝ)}
    (h : A ∈ S.Ω F D M) :
    {x : Fin M → ℝ | x ∘ σ ∈ A} ∈
      S.Ω (max (F + M) (4 * (M + M) + 8) + 1 + M) (D + (2 * M + 4)) M := by
  have hLift : liftLast M A ∈ S.Ω (F + M) D (M + M) := liftLast_mem (S := S) M F D h
  have hRel : relSetSwap σ ∈ S.Ω (4 * (M + M) + 8) (2 * M + 4) (M + M) :=
    relSetSwap_mem (S := S) σ
  have hLift' : liftLast M A ∈ S.Ω (max (F + M) (4 * (M + M) + 8)) D (M + M) :=
    mem_mono hLift _ _ (le_max_left _ _) (le_refl _)
  have hRel' : relSetSwap σ ∈
      S.Ω (max (F + M) (4 * (M + M) + 8)) (2 * M + 4) (M + M) :=
    mem_mono hRel _ _ (le_max_right _ _) (le_refl _)
  have hJ := S.inter (fun i : Fin 2 => if i = 0 then D else 2 * M + 4)
    (fun i : Fin 2 => if i = 0 then liftLast M A else relSetSwap σ)
    (by intro i
        fin_cases i
        · simpa using hLift'
        · simpa using hRel')
  rw [show (∑ i : Fin 2, if i = 0 then D else 2 * M + 4) = D + (2 * M + 4) from by
    simp [Fin.sum_univ_two]] at hJ
  have hJset : (⋂ i : Fin 2, if i = 0 then liftLast M A else relSetSwap σ) =
      liftLast M A ∩ relSetSwap σ := by
    ext z; simp [Fin.forall_fin_two]
  rw [hJset] at hJ
  have hproj := projN_mem (S := S) M _ _ hJ
  rw [← projN_liftLast_relSetSwap σ A]
  exact hproj

/-- Reindexing along a bijection, in the form used for coordinate permutations. -/
theorem reindex_perm_mem {M F D : ℕ} (σ : Fin M ≃ Fin M) {A : Set (Fin M → ℝ)}
    (h : A ∈ S.Ω F D M) :
    {x : Fin M → ℝ | x ∘ σ ∈ A} ∈
      S.Ω (max (F + M) (4 * (M + M) + 8) + 1 + M) (D + (2 * M + 4)) M :=
  reindex_mem (S := S) (σ : Fin M → Fin M) h


/-! ## Index-type transports

`Eq.ndrec` (`▸`) along an arithmetic equality of the index type is the tool that converts
between the different *type expressions* for the same number of coordinates (e.g. `M + k`
versus `k + M`), which the axioms force upon us; see the header of `Basic` for the reason.
The two lemmas below are the interface: how to read a membership in a transported set, and
how an `Ω`-membership transports. -/

/-- Membership in a set transported along an arithmetic equality of the index type. -/
theorem mem_ndrec {N N' : ℕ} (h : N = N') (T : Set (Fin N → ℝ)) (w : Fin N' → ℝ) :
    w ∈ (h ▸ T) ↔ (fun i : Fin N => w (Fin.cast h i)) ∈ T := by
  cases h; simp

/-- `Ω`-membership transports along arithmetic equalities of the index type. -/
theorem omega_ndrec {N N' F D : ℕ} (h : N = N') {A : Set (Fin N → ℝ)}
    (hA : A ∈ S.Ω F D N) : (h ▸ A) ∈ S.Ω F D N' := by
  cases h; simpa using hA

end Work.WilG5
