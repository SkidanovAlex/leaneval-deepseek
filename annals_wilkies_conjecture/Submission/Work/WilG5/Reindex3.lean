/-
  WilG5 — third reindexing module: the general coordinate reindexing along a map `ι`.

  With `lastN_mem` (module `Reindex2`) the two remaining reindexing operations of the G5 plan
  become `liftFirst` + relation set + `lastN`, with no explicit permutation:

  * `coordImage_mem`: for `A ⊆ ℝ^N` and any `ι : Fin m → Fin N`,
    `coordImage ι A = {u | ∃ x ∈ A, x ∘ ι = u}` equals
    `lastN m (liftFirst m A ∩ relSetSwap ι)` — the joint set has `x` in its first `N`
    coordinates and `u` in its last `m`, with the polynomial relation `u j = x (ι j)`;
  * `coordPre_mem`: for `A ⊆ ℝ^m`, `coordPre ι A = {x | x ∘ ι ∈ A}` equals
    `lastN N (liftFirst N A ∩ relSet ι)` — here `u` sits in the first `m` coordinates and `x`
    in the last `N`.

  Note: no injectivity of `ι` is needed; both descriptions are exact for any `ι`.
-/
import Submission.Work.WilG5.Reindex2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG5

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 1. `coordImage`: the image of an Ω-set under `x ↦ x ∘ ι` -/

theorem coordImage_eq_lastN {m N : ℕ} (ι : Fin m → Fin N) (A : Set (Fin N → ℝ)) :
    coordImage ι A = lastN m (liftFirst m A ∩ relSetSwap ι) := by
  ext u
  constructor
  · rintro ⟨x, hx, hxu⟩
    refine ⟨x, ?_, ?_⟩
    · have hfun : (fun i : Fin N => Fin.append x u (Fin.castAdd m i)) = x := by
        funext i; rw [Fin.append_left]
      simpa [liftFirst, hfun] using hx
    · simp only [relSetSwap, Set.mem_ofPred_eq]
      intro j
      rw [Fin.append_right, Fin.append_left]
      exact (congrFun hxu j).symm
  · rintro ⟨x, hx, hrel⟩
    have hxA : x ∈ A := by
      have hfun : (fun i : Fin N => Fin.append x u (Fin.castAdd m i)) = x := by
        funext i; rw [Fin.append_left]
      simpa [liftFirst, hfun] using hx
    refine ⟨x, hxA, ?_⟩
    funext j
    have := hrel j
    rw [Fin.append_right, Fin.append_left] at this
    exact this.symm

theorem coordImage_mem {m N F D : ℕ} {ι : Fin m → Fin N} {A : Set (Fin N → ℝ)}
    (h : A ∈ S.Ω F D N) :
    coordImage ι A ∈ S.Ω (F + 64 * (N + m) + 64) (D + 32 * (N + m) + 32) m := by
  have hLift : liftFirst m A ∈ S.Ω (F + m) D (N + m) := liftFirst_mem (S := S) m F D h
  have hRel : relSetSwap ι ∈ S.Ω (4 * (m + N) + 8) (2 * m + 4) (N + m) := relSetSwap_mem (S := S) ι
  have hLift' : liftFirst m A ∈ S.Ω (max (F + m) (4 * (m + N) + 8)) D (N + m) :=
    mem_mono hLift _ _ (le_max_left _ _) (le_refl _)
  have hRel' : relSetSwap ι ∈ S.Ω (max (F + m) (4 * (m + N) + 8)) (2 * m + 4) (N + m) :=
    mem_mono hRel _ _ (le_max_right _ _) (le_refl _)
  have hJ := S.inter (fun i : Fin 2 => if i = 0 then D else 2 * m + 4)
    (fun i : Fin 2 => if i = 0 then liftFirst m A else relSetSwap ι)
    (by intro i
        fin_cases i
        · simpa using hLift'
        · simpa using hRel')
  rw [show (∑ i : Fin 2, if i = 0 then D else 2 * m + 4) = D + (2 * m + 4) from by
    simp [Fin.sum_univ_two]] at hJ
  have hJset : (⋂ i : Fin 2, if i = 0 then liftFirst m A else relSetSwap ι) =
      liftFirst m A ∩ relSetSwap ι := by
    ext z; simp [Fin.forall_fin_two]
  rw [hJset] at hJ
  have hLN := lastN_mem (S := S) (n := N) m (max (F + m) (4 * (m + N) + 8) + 1)
    (D + (2 * m + 4)) hJ
  rw [coordImage_eq_lastN ι A]
  exact mem_mono hLN _ _ (by omega) (by omega)

/-! ## 2. `coordPre`: the preimage of an Ω-set under `x ↦ x ∘ ι` -/

theorem coordPre_eq_lastN {m N : ℕ} (ι : Fin m → Fin N) (A : Set (Fin m → ℝ)) :
    coordPre ι A = lastN N (liftFirst N A ∩ relSet ι) := by
  ext x
  constructor
  · intro hx
    have hx' : (fun i : Fin m => x (ι i)) ∈ A := hx
    refine ⟨x ∘ ι, ?_, ?_⟩
    · have hfun : (fun i : Fin m => Fin.append (x ∘ ι) x (Fin.castAdd N i)) =
          fun i : Fin m => x (ι i) := by
        funext i; rw [Fin.append_left]; rfl
      simpa [liftFirst, hfun] using hx'
    · simp only [relSet, Set.mem_ofPred_eq]
      intro j
      rw [Fin.append_left, Fin.append_right]
      rfl
  · rintro ⟨u, hu, hrel⟩
    have huA : u ∈ A := by
      have hfun : (fun i : Fin m => Fin.append u x (Fin.castAdd N i)) = u := by
        funext i; rw [Fin.append_left]
      simpa [liftFirst, hfun] using hu
    have hux : (fun j : Fin m => x (ι j)) = u := by
      funext j
      have := hrel j
      rw [Fin.append_left, Fin.append_right] at this
      exact this.symm
    show (x ∘ ι) ∈ A
    rw [show (x ∘ ι) = (fun j : Fin m => x (ι j)) from rfl, hux]
    exact huA

theorem coordPre_mem {m N F D : ℕ} {ι : Fin m → Fin N} {A : Set (Fin m → ℝ)}
    (h : A ∈ S.Ω F D m) :
    coordPre ι A ∈ S.Ω (F + 64 * (N + m) + 64) (D + 32 * (N + m) + 32) N := by
  have hLift : liftFirst N A ∈ S.Ω (F + N) D (m + N) := liftFirst_mem (S := S) N F D h
  have hRel : relSet ι ∈ S.Ω (4 * (m + N) + 8) (2 * m + 4) (m + N) := relSet_mem (S := S) ι
  have hLift' : liftFirst N A ∈ S.Ω (max (F + N) (4 * (m + N) + 8)) D (m + N) :=
    mem_mono hLift _ _ (le_max_left _ _) (le_refl _)
  have hRel' : relSet ι ∈ S.Ω (max (F + N) (4 * (m + N) + 8)) (2 * m + 4) (m + N) :=
    mem_mono hRel _ _ (le_max_right _ _) (le_refl _)
  have hJ := S.inter (fun i : Fin 2 => if i = 0 then D else 2 * m + 4)
    (fun i : Fin 2 => if i = 0 then liftFirst N A else relSet ι)
    (by intro i
        fin_cases i
        · simpa using hLift'
        · simpa using hRel')
  rw [show (∑ i : Fin 2, if i = 0 then D else 2 * m + 4) = D + (2 * m + 4) from by
    simp [Fin.sum_univ_two]] at hJ
  have hJset : (⋂ i : Fin 2, if i = 0 then liftFirst N A else relSet ι) =
      liftFirst N A ∩ relSet ι := by
    ext z; simp [Fin.forall_fin_two]
  rw [hJset] at hJ
  have hLN := lastN_mem (S := S) (n := m) N (max (F + N) (4 * (m + N) + 8) + 1)
    (D + (2 * m + 4)) hJ
  rw [coordPre_eq_lastN ι A]
  exact mem_mono hLN _ _ (by omega) (by omega)

end Work.WilG5
