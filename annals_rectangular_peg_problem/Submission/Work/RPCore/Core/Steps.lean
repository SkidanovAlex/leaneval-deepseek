import Submission.Work.RPCore.Flow.HamFlow
import Submission.Work.RPCore.Flow.Phi_contDiff
import Submission.Work.RPCore.Flow.Phi_symplectic
import Submission.Work.RPCore.Flow.Phi_nearId
import Submission.Work.RPCore.Flow.Phi_slab
import Submission.Work.RPCore.Flow.Phi_Tk
import Submission.Work.RPCore.Flow.Phi_unique
import Submission.Work.RPCore.GenFun.exists_type2GF
import Submission.Work.RPCore.GenFun.wrot_isType2GF
import Submission.Work.RPCore.Chain.chainAction_crit
import Submission.Work.RPV.VBasic
import Submission.Work.RPCore.Chain.C4Defs

/-!
# The `3N`-step slicing of `Φ_1⁻¹ ∘ τ_θ ∘ Φ_1`

This file contains the elementary (but index-heavy) part of the assembly of
`Work.RPCore.Core.core`: the decomposition of the composite

  `Φ_1⁻¹ ∘ τ_θ ∘ Φ_1 = (Phi Hh 1 0) ∘ (tau θ) ∘ (Phi Hh 0 1)`

into `3N` elementary steps:

* indices `0 ≤ j < N` : the flow slices `Phi Hh (j/N) ((j+1)/N)` of `Φ_1`,
* indices `N ≤ j < 2N` : the rotations `tau δ` (`N δ = θ`),
* indices `2N ≤ j < 3N` : the flow slices `Phi Hh ((3N-j)/N) ((3N-j-1)/N)` of `Φ_1⁻¹`.

`stepMap` is the family of the `3N` maps, `chainSeq Hh N δ x` is the chain of intermediate
points, and `chainSeq_step` records the chain relation `stepMap i (chainSeq i) = chainSeq (i+1)`
which identifies the fold of the chain with the composite (`foldl_ofFn_chain'`).

`sliceGF`/`gfFam` provide the type-2 generating functions of the steps: `Wrot δ` on the middle
block and the generating function of the corresponding flow slice elsewhere (see
`GenFun.exists_type2GF`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPCore.Core

open Work.RPV Work.RPCore.Chain

/-! ## The time parameters of the slicing -/

/-- The `k`-th subdivision point of `[0,1]` into `N` parts: `k / N`. -/
def ph (N k : ℕ) : ℝ := (k : ℝ) / N

theorem ph_zero (N : ℕ) : ph N 0 = 0 := by simp [ph]

theorem ph_self (N : ℕ) (hN : 1 ≤ N) : ph N N = 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [ph]
  field_simp

theorem ph_succ_sub (N k : ℕ) : ph N (k + 1) - ph N k = 1 / N := by
  simp only [ph]
  push_cast
  ring

theorem ph_pred_sub (N m : ℕ) (hm : 1 ≤ m) : |ph N (m - 1) - ph N m| = 1 / N := by
  have h : ph N (m - 1) - ph N m = -(1 / (N : ℝ)) := by
    simp only [ph]
    rw [Nat.cast_sub hm, Nat.cast_one]
    field_simp
    ring
  rw [h, abs_neg, abs_of_nonneg (by positivity)]

theorem ph_mem_Icc (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N) :
    ph N k ∈ Set.Icc (-1 : ℝ) 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  constructor
  · have : 0 ≤ ph N k := div_nonneg hk0 (le_of_lt hN0)
    linarith
  · rw [ph, div_le_iff₀ hN0]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith

theorem ph_nonneg (N k : ℕ) (hN : 1 ≤ N) : 0 ≤ ph N k := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [ph]
  positivity

/-! ## The step maps and the chain of intermediate points -/

/-- The `j`-th step of the `3N`-step decomposition of `Φ_1⁻¹ ∘ τ_θ ∘ Φ_1`. -/
def stepMap (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (j : Fin (n + 1)) : PS → PS :=
  if _h : (j : ℕ) < N then Phi Hh (ph N (j : ℕ)) (ph N ((j : ℕ) + 1))
  else if _h2 : (j : ℕ) < 2 * N then tau δ
  else Phi Hh (ph N (3 * N - (j : ℕ))) (ph N (3 * N - (j : ℕ) - 1))

def chainSeq (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (x : PS) (k : Fin (n + 2)) : PS :=
  if _h : (k : ℕ) ≤ N then Phi Hh 0 (ph N (k : ℕ)) x
  else if _h2 : (k : ℕ) ≤ 2 * N then
    tau ((((k : ℕ) : ℝ) - (N : ℝ)) * δ) (Phi Hh 0 1 x)
  else Phi Hh 1 (ph N (3 * N - (k : ℕ))) (tau ((N : ℝ) * δ) (Phi Hh 0 1 x))

theorem stepMap_of_lt (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) {j : Fin (n + 1)}
    (h : (j : ℕ) < N) :
    stepMap Hh n N δ j = Phi Hh (ph N (j : ℕ)) (ph N ((j : ℕ) + 1)) := by
  unfold stepMap
  rw [dif_pos h]

theorem stepMap_of_mid (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) {j : Fin (n + 1)}
    (h1 : ¬ ((j : ℕ) < N)) (h2 : (j : ℕ) < 2 * N) : stepMap Hh n N δ j = tau δ := by
  unfold stepMap
  rw [dif_neg h1, dif_pos h2]

theorem stepMap_of_late (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) {j : Fin (n + 1)}
    (h1 : ¬ ((j : ℕ) < N)) (h2 : ¬ ((j : ℕ) < 2 * N)) :
    stepMap Hh n N δ j = Phi Hh (ph N (3 * N - (j : ℕ))) (ph N (3 * N - (j : ℕ) - 1)) := by
  unfold stepMap
  rw [dif_neg h1, dif_neg h2]

theorem chainSeq_of_le (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (x : PS) {k : Fin (n + 2)}
    (h : (k : ℕ) ≤ N) : chainSeq Hh n N δ x k = Phi Hh 0 (ph N (k : ℕ)) x := by
  unfold chainSeq
  rw [dif_pos h]

theorem chainSeq_of_mid (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (x : PS) {k : Fin (n + 2)}
    (h1 : ¬ ((k : ℕ) ≤ N)) (h2 : (k : ℕ) ≤ 2 * N) :
    chainSeq Hh n N δ x k = tau ((((k : ℕ) : ℝ) - (N : ℝ)) * δ) (Phi Hh 0 1 x) := by
  unfold chainSeq
  rw [dif_neg h1, dif_pos h2]

theorem chainSeq_of_late (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (x : PS) {k : Fin (n + 2)}
    (h1 : ¬ ((k : ℕ) ≤ N)) (h2 : ¬ ((k : ℕ) ≤ 2 * N)) :
    chainSeq Hh n N δ x k =
      Phi Hh 1 (ph N (3 * N - (k : ℕ))) (tau ((N : ℝ) * δ) (Phi Hh 0 1 x)) := by
  unfold chainSeq
  rw [dif_neg h1, dif_neg h2]


/-! ## The chain relation -/

theorem chainSeq_zero (Hh : CptPerHam) (n N : ℕ) (δ : ℝ) (x : PS) :
    chainSeq Hh n N δ x 0 = x := by
  unfold chainSeq
  rw [dif_pos (by simp : ((0 : Fin (n + 2)) : ℕ) ≤ N)]
  simp [ph, Phi_self]

theorem chainSeq_last (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (x : PS) :
    chainSeq Hh n N δ x (Fin.last (n + 1)) =
      Phi Hh 1 0 (tau ((N : ℝ) * δ) (Phi Hh 0 1 x)) := by
  have hk : ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) = 3 * N := by
    rw [Fin.val_last]; omega
  have h1 : ¬ (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) ≤ N) := by rw [hk]; omega
  have h2 : ¬ (((Fin.last (n + 1) : Fin (n + 2)) : ℕ) ≤ 2 * N) := by rw [hk]; omega
  unfold chainSeq
  rw [dif_neg h1, dif_neg h2, hk]
  rw [show 3 * N - 3 * N = 0 from by omega, ph_zero]

theorem chainSeq_step (Hh : CptPerHam) (n N : ℕ) (hN : 1 ≤ N) (hn : n + 1 = 3 * N) (δ : ℝ)
    (x : PS) :
    ∀ i : Fin (n + 1), stepMap Hh n N δ i (chainSeq Hh n N δ x i.castSucc) =
      chainSeq Hh n N δ x i.succ := by
  intro i
  have hiN : (i : ℕ) < 3 * N := by omega
  rcases lt_trichotomy (i : ℕ) N with hlt | heq | hgt
  · rw [stepMap_of_lt Hh n N δ hlt,
      chainSeq_of_le Hh n N δ x (k := i.castSucc) (by simp only [Fin.val_castSucc]; omega),
      chainSeq_of_le Hh n N δ x (k := i.succ)
        (by simp only [Fin.val_succ]; omega)]
    simp only [Fin.val_castSucc, Fin.val_succ]
    exact Phi_add Hh 0 (ph N (i : ℕ)) (ph N ((i : ℕ) + 1)) x
  · rw [stepMap_of_mid Hh n N δ (by omega) (by omega),
      chainSeq_of_le Hh n N δ x (k := i.castSucc) (by simp only [Fin.val_castSucc]; omega),
      chainSeq_of_mid Hh n N δ x (k := i.succ) (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [heq, ph_self N hN]
    congr 1
    push_cast
    ring
  · rcases lt_trichotomy (i : ℕ) (2 * N) with hlt2 | heq2 | hgt2
    · rw [stepMap_of_mid Hh n N δ (by omega) hlt2,
        chainSeq_of_mid Hh n N δ x (k := i.castSucc) (by simp only [Fin.val_castSucc]; omega)
          (by simp only [Fin.val_castSucc]; omega),
        chainSeq_of_mid Hh n N δ x (k := i.succ) (by simp only [Fin.val_succ]; omega)
          (by simp only [Fin.val_succ]; omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [tau_add]
      congr 1
      push_cast
      ring
    · rw [stepMap_of_late Hh n N δ (by omega) (by omega),
        chainSeq_of_mid Hh n N δ x (k := i.castSucc) (by simp only [Fin.val_castSucc]; omega)
          (by simp only [Fin.val_castSucc]; omega),
        chainSeq_of_late Hh n N δ x (k := i.succ) (by simp only [Fin.val_succ]; omega)
          (by simp only [Fin.val_succ]; omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [heq2]
      rw [show 3 * N - 2 * N = N from by omega,
        show 3 * N - (2 * N + 1) = N - 1 from by omega, ph_self N hN]
      rw [show (((2 * N : ℕ) : ℝ) - (N : ℝ)) * δ = (N : ℝ) * δ from by push_cast; ring]
    · rw [stepMap_of_late Hh n N δ (by omega) (by omega),
        chainSeq_of_late Hh n N δ x (k := i.castSucc) (by simp only [Fin.val_castSucc]; omega)
          (by simp only [Fin.val_castSucc]; omega),
        chainSeq_of_late Hh n N δ x (k := i.succ) (by simp only [Fin.val_succ]; omega)
          (by simp only [Fin.val_succ]; omega)]
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [Phi_add Hh 1 (ph N (3 * N - (i : ℕ))) (ph N (3 * N - (i : ℕ) - 1))
        (tau ((N : ℝ) * δ) (Phi Hh 0 1 x))]
      rw [show 3 * N - ((i : ℕ) + 1) = 3 * N - (i : ℕ) - 1 from by omega]

theorem foldl_ofFn_chain' {α : Type*} (m : ℕ) (fs : Fin m → α → α) (ys : Fin (m + 1) → α)
    (h : ∀ i : Fin m, fs i (ys i.castSucc) = ys i.succ) :
    List.foldl (fun acc f => f acc) (ys 0) (List.ofFn fs) = ys (Fin.last m) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
    have hh : ∀ i : Fin n,
        (fun i : Fin n => fs i.castSucc) i
          ((fun i : Fin (n + 1) => ys i.castSucc) i.castSucc) =
          (fun i : Fin (n + 1) => ys i.castSucc) i.succ := by
      intro i
      show fs i.castSucc (ys (i.castSucc).castSucc) = ys (i.succ).castSucc
      rw [h i.castSucc, Fin.succ_castSucc]
    have hih := ih (fun i : Fin n => fs i.castSucc) (fun i : Fin (n + 1) => ys i.castSucc) hh
    change fs (Fin.last n)
      (List.foldl (fun acc f => f acc) (ys ((0 : Fin (n + 1)).castSucc))
        (List.ofFn fun i : Fin n => fs i.castSucc)) = ys (Fin.last (n + 1))
    rw [hih, h (Fin.last n), Fin.succ_last]

end Work.RPCore.Core
