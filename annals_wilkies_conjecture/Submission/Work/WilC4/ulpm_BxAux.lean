/-
  WilC4/ulpm_BxAux : auxiliary lemmas for `Work.WilC4.ulpm_Bx`.

  * `tubF v c m` is the tuple `(v 0, c, m)` on `Fin (k+2)`, and `Sfib_definable_fixed` makes the
    level set `Sfib Y c m` `∅`-definable *with `c`, `m` as parameters* (they are language
    constants of `LRc`), which is what feeds `oMin_structure` to bound the number of boundary
    points of the level set.
  * `Bx_fibre_bdd`: the fibres of the crossing family `Bx Y E` are *uniformly* bounded, using
    uniform finiteness of the boundary points of the level sets (o-minimality at `ℝ`) together
    with `exists_alt_bound` applied to the (reindexed) defining formula of `Bx`.
-/
import Mathlib
import Submission.Work.WilC4.ulpm_BxDefs
import Submission.Work.WilC4.mono_real
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.encard_le_of_not_altChain
import Submission.Work.WilC4.ClusterTool

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

variable {k : ℕ}

/-! ## 1. The tuple `(v 0, c, m)` -/

/-- The tuple `(v 0, c, m)` on `Fin (k+2)`: coordinate `0` is `v 0`, the coordinates `1, …, k` are
the parameters `c`, the last coordinate is the value `m`. -/
def tubF (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) : Fin (k + 2) → ℝ :=
  Fin.cons (α := fun _ => ℝ) (v 0) (Fin.snoc (α := fun _ => ℝ) c m)

@[simp] lemma tubF_zero (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) : tubF v c m 0 = v 0 := by
  simp [tubF]

@[simp] lemma tubF_last (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) :
    tubF v c m (Fin.last (k + 1)) = m := by
  simp [tubF]

@[simp] lemma tubF_succ (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) (i : Fin k) :
    tubF v c m (Fin.succ (Fin.castSucc i)) = c i := by
  simp [tubF, Fin.snoc_castSucc]

@[simp] lemma cOfF_tubF (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) :
    cOfF (tubF v c m) = c := by
  funext i; simp [cOfF]

@[simp] lemma mOfF_tubF (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) :
    mOfF (tubF v c m) = m := by
  simp [mOfF]

/-- `tubF v c m` lies in the parametrised level set iff `v 0` lies in the level set at `(c,m)`. -/
theorem tubF_mem_Sfam (Y : Set (Fin (k + 2) → ℝ)) (v : Fin 1 → ℝ) (c : Fin k → ℝ) (m : ℝ) :
    tubF v c m ∈ Sfam Y ↔ v 0 ∈ Sfib Y c m := by
  simp only [Sfam, Sfib, Set.mem_setOf_eq, cOfF_tubF, tubF_zero, mOfF_tubF]

/-- `tubF · c m` is a `∅`-definable map (every real is an `LRc` constant). -/
theorem tubF_definableMap (c : Fin k → ℝ) (m : ℝ) :
    Set.DefinableMap LRc (∅ : Set ℝ) (fun v : Fin 1 → ℝ => tubF v c m) := by
  intro i
  induction i using Fin.lastCases with
  | last =>
      simpa [tubF] using
        (defFun_const (ρ := Fin 1) m)
  | cast j =>
      induction j using Fin.cases with
      | zero =>
          simpa [tubF] using
            (Set.DefinableFun.proj (L := LRc) (A := (∅ : Set ℝ)) (i := (0 : Fin 1)))
      | succ l =>
          simpa [tubF] using
            (defFun_const (ρ := Fin 1) (c l))

/-- **The level set is definable with the parameters made explicit.**  For fixed `c` and `m` (real
constants of `LRc`) the fibre `{v : Fin 1 → ℝ | v 0 ∈ Sfib Y c m}` is `∅`-definable, hence
`Set.univ`-definable; this is the input of `oMin_structure`. -/
theorem Sfib_definable_fixed {Y : Set (Fin (k + 2) → ℝ)}
    (hSfam : (∅ : Set ℝ).Definable LRc (Sfam Y)) (c : Fin k → ℝ) (m : ℝ) :
    (∅ : Set ℝ).Definable LRc {v : Fin 1 → ℝ | v 0 ∈ Sfib Y c m} := by
  have h := Set.Definable.preimage_map (tubF_definableMap (k := k) c m) hSfam
  convert h using 1
  ext v
  exact (tubF_mem_Sfam Y v c m).symm

/-! ## 2. Uniform finiteness of the fibres of `Bx` -/

/-- **The uniform bound.**  The fibres of the crossing family are bounded by a single natural
number.  Proof: `BxP Y E` is `∅`-definable, so `exists_alt_bound` bounds the number of convex
components of all its fibres at once; each fibre is finite, because it is a finite union (over
`Mid E`, finite since `E` is) of boundary sets of level sets, and the boundary of a definable
subset of `ℝ` is finite by o-minimality. -/
theorem Bx_fibre_bdd (hOM : OMinModels) (Y : Set (Fin (k + 2) → ℝ)) (E : Set ℝ)
    (hSfam : (∅ : Set ℝ).Definable LRc (Sfam Y)) (hMidfin : (Mid E).Finite)
    (hBxdef : (∅ : Set ℝ).Definable LRc (Bx Y E)) :
    ∃ N : ℕ, ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ Bx Y E}.encard ≤ N := by
  classical
  -- the reindexed crossing family is definable, hence given by a formula
  have hBxP : (∅ : Set ℝ).Definable LRc (BxP Y E) := hBxdef.preimage_comp (eIdx k)
  obtain ⟨φ, hφ⟩ := Set.empty_definable_iff.mp hBxP
  obtain ⟨N, hN⟩ := exists_alt_bound hOM φ
  refine ⟨N, fun c => ?_⟩
  -- the identification of the fibre with the `φ`-fibre
  have hiden : {t : ℝ | φ.Realize (Sum.elim c (fun _ : Fin 1 => t))} =
      {t : ℝ | Fin.cons t c ∈ Bx Y E} := by
    ext t
    simp only [Set.mem_setOf_eq]
    have h1 : (Sum.elim c (fun _ : Fin 1 => t)) ∈ BxP Y E ↔
        φ.Realize (Sum.elim c (fun _ : Fin 1 => t)) := by
      rw [hφ]; exact Iff.rfl
    rw [← h1, mem_BxP_iff]
  -- finiteness of the fibre
  have hfib : {x : ℝ | Fin.cons x c ∈ Bx Y E} =
      ⋃ m ∈ (Mid E : Set ℝ), {x : ℝ | WilC2.IsBnd (Sfib Y c m) x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact mem_Bx_iff Y E c x
  have hbnd : ∀ m : ℝ, ({x : ℝ | WilC2.IsBnd (Sfib Y c m) x}).Finite := by
    intro m
    set X : Set (Fin 1 → ℝ) := {v | v 0 ∈ Sfib Y c m} with hXdef
    have hXu : (Set.univ : Set ℝ).Definable LRc X :=
      (Sfib_definable_fixed (k := k) hSfam c m).mono (Set.empty_subset _)
    obtain ⟨s, hs, heq⟩ := oMin_structure hOM hXu
    have hS : Sfib Y c m = ⋃₀ (s : Set (Set ℝ)) := by
      ext t
      have h := Set.ext_iff.mp heq (fun _ : Fin 1 => t)
      simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, hXdef, Fin.zero_eta] at h
      exact h
    exact bnd_finite_of_ordConnected hs hS
  have hfin : ({x : ℝ | Fin.cons x c ∈ Bx Y E}).Finite := by
    rw [hfib]
    exact hMidfin.biUnion (fun m _ => hbnd m)
  have hnc : ¬ AltChain N ({x : ℝ | Fin.cons x c ∈ Bx Y E}) := by
    rw [← hiden]
    exact hN c
  exact encard_le_of_not_altChain hfin hnc

end Work.WilC4
