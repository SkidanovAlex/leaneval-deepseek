import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.rot_contract4
import Submission.Work.Diff.Alg.Pinch.rot_toolkit
import Submission.Work.Diff.Alg.Pinch.rot_knProd
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2
import Submission.Work.Diff.Alg.Pinch.ric_rot
import Submission.Work.Diff.Alg.Pinch.scalAlg_rot
import Submission.Work.Diff.Alg.Pinch.isAlgCurv_rot
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-invariance of the Brendle–Schoen pinching family `Ĉ(s)`

`Work.Diff.Alg.Pinch.Chat n s = Ĉ(s)` (Brendle–Schoen §3) is the image of the cone
`Dpic p = {IsAlgCurv} ∩ {InPIC2} ∩ {RicPinch p}` under the linear Böhm–Wilking transform
`ell a b` (with the parameters of `Chat`).  Each of the three defining conditions of `Dpic p` is
invariant under an orthogonal change of frame — `IsAlgCurv` (`isAlgCurv_rot`), `InPIC2`
(`Cone.inPIC2_rot`) and `RicPinch` (`chat_RicPinch_rot` below) — and `ell a b` is `O(n)`-equivariant
(`chat_ell_rot`).  Hence the family `Ĉ(s)` is `O(n)`-invariant:

`rot A R ∈ Chat n s ↔ R ∈ Chat n s` for `A ∈ O(n)`.

## Note on imports and duplicates

The helper lemmas below are deliberately given a `chat_`-prefixed name: the "obvious" names
`ell_rot`, `ric0_rot`, `rot2_id2`, `rot_transpose_rot` are already used by
`Work.Diff.Alg.Pinch.exists_invariant_set_Chat`, while `Work.Diff.Alg.Pinch.Dtensor_rot` uses
`rot2_id2`/`ric0_rot` as well — and no single file may import both of those modules.  This file
imports neither, so that it can be combined with either of them.
`Work.Diff.Alg.Pinch.ricPinch_rot` (the "official" module for the `RicPinch` half) currently
imports the stub files `sum_ric_quadform` / `norm_mulVec`, which do not elaborate (their `n` is
unbound) and are unproved, and is therefore unusable; its statement is reproved here as
`chat_RicPinch_rot` from the proved primitives `Work.Diff.Alg.collapse2`
(`Submission.Work.Diff.Alg.rot_contract4`), `ric_rot`, `scalAlg_rot` and `sum_ai_id2`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary `O(n)` bookkeeping -/

/-- The transpose of an orthogonal matrix is orthogonal. -/
lemma chat_transpose_mem_orthogonalGroup (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    A.transpose ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff', Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA

/-- `rot A.transpose` is a left inverse of `rot A` for an orthogonal `A`. -/
lemma chat_rot_transpose_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    rot A.transpose (rot A R) = R := by
  rw [rt_rot_mul, (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hA, rt_rot_one]

/-! ## `O(n)`-equivariance of the Böhm–Wilking transform -/

/-- For an orthogonal `A`, the `(0,2)`-action fixes the Kronecker delta `id2 n`. -/
lemma chat_rot2_id2 (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    rot2 A (id2 n) = id2 n := by
  funext i j
  have hrow : (∑ a, A i a * A j a) = if i = j then 1 else 0 := by
    have h := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hA
    have h2 := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h2
  calc rot2 A (id2 n) i j
      = ∑ a, ∑ b, A i a * A j b * (if a = b then 1 else 0) := rfl
    _ = ∑ a, A i a * A j a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [show ¬ (a = b) from fun h => hb h.symm]
        · intro h; exact absurd (Finset.mem_univ a) h
    _ = if i = j then 1 else 0 := hrow
    _ = id2 n i j := by simp [id2]

/-- `ric0` is `ric` minus `scalAlg / n` times the identity. -/
lemma chat_ric0_eq (S : Curv4 n) :
    ric0 S = ric S - (scalAlg S / (n : ℝ)) • id2 n := by
  funext i j
  simp only [ric0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- The traceless Ricci tensor transforms as a `(0,2)`-tensor under an orthogonal change of
frame. -/
lemma chat_ric0_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ric0 (rot A R) = rot2 A (ric0 R) := by
  rw [chat_ric0_eq (rot A R), chat_ric0_eq R, ric_rot n A hA R, scalAlg_rot n A hA R,
    rot2_sub, rot2_smul, chat_rot2_id2 A hA]

/-- The Böhm–Wilking transform `ell a b` is `O(n)`-equivariant. -/
lemma chat_ell_rot (a b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    rot A (ell a b R) = ell a b (rot A R) := by
  have h1 : rot A (knProd (ric0 R) (id2 n)) = knProd (rot2 A (ric0 R)) (id2 n) := by
    rw [rot_knProd, chat_rot2_id2 A hA]
  have h2 : rot A (knProd (id2 n) (id2 n)) = knProd (id2 n) (id2 n) := by
    rw [rot_knProd, chat_rot2_id2 A hA]
  rw [ell, rot_add_lin, rot_add_lin, rot_smul_lin, rot_smul_lin, h1, h2]
  rw [ell, chat_ric0_rot A hA R, scalAlg_rot n A hA R]

/-! ## `O(n)`-invariance of `RicPinch p` -/

/-- `RicPinch p` is invariant under an orthogonal change of frame. -/
lemma chat_RicPinch_rot (p : ℝ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Curv4 n}
    (h : RicPinch p R) : RicPinch p (rot A R) := by
  -- the rotated Ricci tensor is the two-sided action `rot2 A (ric R)`
  have hric : ∀ i j : Fin n, ric (rot A R) i j = ∑ a, ∑ b, A i a * A j b * ric R a b := by
    intro i j
    rw [ric_rot n A hA R]
    rfl
  have hscal : scalAlg (rot A R) = scalAlg R := scalAlg_rot n A hA R
  intro v
  -- pull `v` back to `w = A.transpose *ᵥ v`, so that `A *ᵥ w = v`
  set w : Fin n → ℝ := A.transpose.mulVec v with hw
  have hAw : A.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA,
      Matrix.one_mulVec]
  -- the Ricci quadratic form of `rot A R` at `v = A w` is that of `R` at `w`
  have hq : (∑ i, ∑ j, ric (rot A R) i j * v i * v j)
      = ∑ a, ∑ b, ric R a b * w a * w b := by
    rw [← hAw]
    have hstep : (∑ i, ∑ j, ric (rot A R) i j * (A.mulVec w) i * (A.mulVec w) j)
        = ∑ i, ∑ j, (A.mulVec w) i * (A.mulVec w) j * (∑ a, ∑ b, A i a * A j b * ric R a b) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hric i j]
      ring
    rw [hstep, Work.Diff.Alg.collapse2 hA (ric R) w w]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  -- and so is the Euclidean norm
  have hnorm : (∑ i, v i * v i) = ∑ i, w i * w i := by
    rw [← hAw]
    calc (∑ i, (A.mulVec w) i * (A.mulVec w) i)
        = ∑ i, ∑ j, (A.mulVec w) i * (A.mulVec w) j * id2 n i j :=
          (sum_ai_id2 (fun i => (A.mulVec w) i) (fun i => (A.mulVec w) i)).symm
      _ = ∑ i, ∑ j, (A.mulVec w) i * (A.mulVec w) j * rot2 A (id2 n) i j := by
          rw [chat_rot2_id2 A hA]
      _ = ∑ a, ∑ b, w a * w b * id2 n a b := Work.Diff.Alg.collapse2 hA (id2 n) w w
      _ = ∑ i, w i * w i := sum_ai_id2 (fun a => w a) (fun a => w a)
  rw [hscal, hq, hnorm]
  exact h w

/-! ## `O(n)`-invariance of `Dpic` and of the cones `Ccone a b p` -/

/-- The cone `Dpic p` is invariant under an orthogonal change of frame. -/
lemma chat_Dpic_rot_mem {p : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Curv4 n}
    (hR : R ∈ Dpic (n := n) p) : rot A R ∈ Dpic (n := n) p :=
  ⟨isAlgCurv_rot n A hR.1, Cone.inPIC2_rot n A R hR.2.1, chat_RicPinch_rot p hA hR.2.2⟩

/-- The cone `Dpic p` is invariant under an orthogonal change of frame. -/
theorem chat_Dpic_rot (p : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    rot A R ∈ Dpic (n := n) p ↔ R ∈ Dpic (n := n) p := by
  refine ⟨fun h => ?_, fun h => chat_Dpic_rot_mem hA h⟩
  have hAt := chat_transpose_mem_orthogonalGroup A hA
  have h' := chat_Dpic_rot_mem (p := p) hAt h
  rwa [chat_rot_transpose_rot A hA R] at h'

/-- The Böhm–Wilking cone `Ccone a b p = ell a b '' Dpic p` is invariant under an orthogonal change
of frame. -/
lemma chat_Ccone_rot_mem (a b p : ℝ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Curv4 n}
    (hR : R ∈ Ccone (n := n) a b p) : rot A R ∈ Ccone (n := n) a b p := by
  obtain ⟨S, hS, hSR⟩ := hR
  exact ⟨rot A S, chat_Dpic_rot_mem hA hS, by rw [← chat_ell_rot a b A hA S, hSR]⟩

/-- The Böhm–Wilking cone `Ccone a b p = ell a b '' Dpic p` is invariant under an orthogonal change
of frame. -/
theorem chat_Ccone_rot (a b p : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    rot A R ∈ Ccone (n := n) a b p ↔ R ∈ Ccone (n := n) a b p := by
  refine ⟨fun h => ?_, fun h => chat_Ccone_rot_mem a b p hA h⟩
  have hAt := chat_transpose_mem_orthogonalGroup A hA
  have h' := chat_Ccone_rot_mem a b p hAt h
  rwa [chat_rot_transpose_rot A hA R] at h'

/-! ## The main theorem -/

theorem chat_rot (n : ℕ) (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {s : ℝ} (hs : 0 < s)
    {R : Submission.Diff.Alg.Curv4 n} :
    Submission.Diff.Alg.rot A R ∈ Work.Diff.Alg.Pinch.Chat n s ↔
      R ∈ Work.Diff.Alg.Pinch.Chat n s := by
  by_cases h : s ≤ 1 / 2
  · rw [Chat_eq_Ccone n h]
    exact chat_Ccone_rot (chatA n s) s (chatP n s) A hA R
  · rw [Chat, if_neg h]
    exact chat_Ccone_rot s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) A hA R

end Work.Diff.Alg.Pinch
