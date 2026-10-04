import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.GE.rot_pair
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evX

open scoped BigOperators
open Submission.Diff Submission.Diff.Alg

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-!
# Frame independence of the level-`(a,b)` reaction monomial on a fixed `4`-tuple

The target `Work.Diff.EXT.evX.KptArr_frame_indepV` says that

`∑ᵢⱼₖₗ 𝔅(∇^a Rm, ∇^b Rm)_{ijkl} ⟨e i, v₀⟩⟨e j, v₁⟩⟨e k, v₂⟩⟨e l, v₃⟩`

is independent of the `g`-orthonormal frame `e` of `TₓM`.  Here `𝔅 = reactionBilin` is the polarized
reaction, `∇^a Rm` is represented at the point level by the array `KptArr g x a d₁ e`, and `hF` is
the `O(n)`-equivariance of `𝔅` that is available as a hypothesis.

Both sides are the value, on the four vectors `v 0, …, v 3`, of the `(0,4)`-tensor
`𝔅(Rm^{(a)}, Rm^{(b)})`; the value of a tensor on vectors is computed from its frame components by
expanding the vectors in the frame, so it does not depend on the frame.

## Route

1. `KptArr_eq_rot`: the frame change of the tower array,
   `KptArr g x a d e' = rot A (KptArr g x a d e)` whenever `e' i = ∑ j, A i j • e j`.  This is the
   multilinearity of `Kpt` (the packaged `KptLin`) applied to the four curvature slots, expanded one
   slot at a time (`Kpt_append_update_sum`, whose plumbing is `append_update`).
2. `rot_vec_contract`: the algebraic contraction identity: for `A` orthogonal, contracting `rot A X`
   with the four `A`-transformed coefficient vectors is the same as contracting `X` with the
   original ones (via the rank-one tensor `outer4` and `Work.Diff.GE.rot_pair`).
3. Assembly: `Work.Diff.GE.onFrame_orthogonal_change` produces `A`; `hF` transfers `𝔅` through
   `rot A`; the pairing vectors transform by `A` (bilinearity of `g.inner x`), and step 2 collapses
   the four index pairs.
-/

/-! ## The plumbing of `Fin.append` -/

/-- Updating the last four slots of an appended tuple is appending the updated four-tuple. -/
private lemma append_update {α : Type*} {a : ℕ} (d : Fin a → α) (u : Fin 4 → α) (t : Fin 4)
    (y : α) :
    Function.update (Fin.append d u) (Fin.natAdd a t) y = Fin.append d (Function.update u t y) := by
  funext s
  refine Fin.addCases (motive := fun s =>
    Function.update (Fin.append d u) (Fin.natAdd a t) y s
      = Fin.append d (Function.update u t y) s) (fun r => ?_) (fun r => ?_) s
  · have hne : (Fin.castAdd 4 r : Fin (a + 4)) ≠ Fin.natAdd a t := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    rw [Function.update_of_ne hne, Fin.append_left, Fin.append_left]
  · by_cases htr : t = r
    · subst htr
      simp only [Fin.append_right, Function.update_self]
    · have hne : (Fin.natAdd a r : Fin (a + 4)) ≠ Fin.natAdd a t := by
        intro h
        exact htr ((Fin.natAdd_inj a).mp h).symm
      rw [Fin.append_right, Function.update_of_ne hne, Fin.append_right,
        Function.update_of_ne (fun h => htr h.symm)]

/-- `KptLin` computes `Kpt` (definitional unfolding of the packaged multilinear map). -/
private lemma KptLin_apply' (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (x : M) (a : ℕ) (w : Fin (a + 4) → TangentSpace I x) :
    (Work.Diff.EXT.KptLin hLC g x a) w = Work.Diff.EXT.Kpt g x a w := rfl

/-- **One slot of the multilinear expansion.**  If the `t`-th entry of the four-tuple `u` is a
finite linear combination `∑ r, c r • w r`, then the tower component `Kpt g x a (d ++ u)` expands
into the corresponding combination of tower components with the `t`-th slot replaced. -/
private lemma Kpt_append_update_sum
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (a : ℕ)
    (d : Fin a → TangentSpace I x) (t : Fin 4) {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (w : ι → TangentSpace I x) (u : Fin 4 → TangentSpace I x)
    (hu : u t = ∑ r, c r • w r) :
    Work.Diff.EXT.Kpt g x a (Fin.append d u)
      = ∑ r, c r * Work.Diff.EXT.Kpt g x a (Fin.append d (Function.update u t (w r))) := by
  have hsum := MultilinearMap.map_update_sum (Work.Diff.EXT.KptLin hLC g x a)
    (Finset.univ : Finset ι) (Fin.natAdd a t) (fun r => c r • w r) (Fin.append d u)
  have hsmul : ∀ r : ι, (Work.Diff.EXT.KptLin hLC g x a)
      (Function.update (Fin.append d u) (Fin.natAdd a t) (c r • w r))
      = c r * Work.Diff.EXT.Kpt g x a
          (Function.update (Fin.append d u) (Fin.natAdd a t) (w r)) := by
    intro r
    rw [MultilinearMap.map_update_smul, KptLin_apply', smul_eq_mul]
  calc Work.Diff.EXT.Kpt g x a (Fin.append d u)
      = (Work.Diff.EXT.KptLin hLC g x a)
          (Function.update (Fin.append d u) (Fin.natAdd a t) (u t)) := by
        rw [← KptLin_apply', ← Fin.append_right d u t, Function.update_eq_self]
    _ = (Work.Diff.EXT.KptLin hLC g x a)
          (Function.update (Fin.append d u) (Fin.natAdd a t) (∑ r, c r • w r)) := by rw [hu]
    _ = ∑ r, (Work.Diff.EXT.KptLin hLC g x a)
          (Function.update (Fin.append d u) (Fin.natAdd a t) (c r • w r)) := by rw [hsum]
    _ = ∑ r, c r * Work.Diff.EXT.Kpt g x a
          (Function.update (Fin.append d u) (Fin.natAdd a t) (w r)) := by
        exact Finset.sum_congr rfl (fun r _ => hsmul r)
    _ = ∑ r, c r * Work.Diff.EXT.Kpt g x a (Fin.append d (Function.update u t (w r))) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [append_update]

/-! ## Frame change of the tower array -/

/-- **Frame change of the level-`a` tower array.**  If the frame `e'` is the `A`-transform of the
frame `e` (`e' i = ∑ j, A i j • e j`), then the array of components of `∇^a Rm` transforms by `rot A`
in each of its four curvature indices.  Only multilinearity of `Kpt g x a` is used. -/
private theorem KptArr_eq_rot
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (a : ℕ)
    (d : Fin a → TangentSpace I x)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • e j) :
    Work.Diff.EXT.KptArr g x a d e' = rot A (Work.Diff.EXT.KptArr g x a d e) := by
  funext i j k l
  let u : Fin 4 → TangentSpace I x := ![e' i, e' j, e' k, e' l]
  have hu0 : u 0 = ∑ r, A i r • e r := by simpa [u] using hA i
  have hu1 : u 1 = ∑ r, A j r • e r := by simpa [u] using hA j
  have hu2 : u 2 = ∑ r, A k r • e r := by simpa [u] using hA k
  have hu3 : u 3 = ∑ r, A l r • e r := by simpa [u] using hA l
  have h1 := Kpt_append_update_sum hLC g x a d 0 (fun r => A i r) e u hu0
  have h2 : ∀ p, Work.Diff.EXT.Kpt g x a (Fin.append d (Function.update u 0 (e p)))
      = ∑ q, A j q * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update u 0 (e p)) 1 (e q))) := by
    intro p
    refine Kpt_append_update_sum hLC g x a d 1 (fun r => A j r) e
      (Function.update u 0 (e p)) ?_
    rw [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
    exact hu1
  have h3 : ∀ p q, Work.Diff.EXT.Kpt g x a
        (Fin.append d (Function.update (Function.update u 0 (e p)) 1 (e q)))
      = ∑ r, A k r * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update (Function.update u 0 (e p)) 1 (e q))
            2 (e r))) := by
    intro p q
    refine Kpt_append_update_sum hLC g x a d 2 (fun r => A k r) e
      (Function.update (Function.update u 0 (e p)) 1 (e q)) ?_
    rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 1),
      Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0)]
    exact hu2
  have h4 : ∀ p q r, Work.Diff.EXT.Kpt g x a
        (Fin.append d (Function.update (Function.update (Function.update u 0 (e p)) 1 (e q))
          2 (e r)))
      = ∑ s, A l s * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update (Function.update (Function.update u 0
            (e p)) 1 (e q)) 2 (e r)) 3 (e s))) := by
    intro p q r
    refine Kpt_append_update_sum hLC g x a d 3 (fun s => A l s) e
      (Function.update (Function.update (Function.update u 0 (e p)) 1 (e q)) 2 (e r)) ?_
    rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 1),
      Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
    exact hu3
  have hfinal : ∀ p q r s, Function.update (Function.update (Function.update (Function.update u 0
        (e p)) 1 (e q)) 2 (e r)) 3 (e s) = ![e p, e q, e r, e s] := by
    intro p q r s
    funext t
    fin_cases t <;> simp [u]
  calc Work.Diff.EXT.KptArr g x a d e' i j k l
      = Work.Diff.EXT.Kpt g x a (Fin.append d u) := rfl
    _ = ∑ p, A i p * Work.Diff.EXT.Kpt g x a (Fin.append d (Function.update u 0 (e p))) := h1
    _ = ∑ p, A i p * (∑ q, A j q * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update u 0 (e p)) 1 (e q)))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [h2 p]
    _ = ∑ p, A i p * (∑ q, A j q * (∑ r, A k r * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update (Function.update u 0 (e p)) 1 (e q))
            2 (e r))))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        refine congrArg (fun z => A i p * z) ?_
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [h3 p q]
    _ = ∑ p, A i p * (∑ q, A j q * (∑ r, A k r * (∑ s, A l s * Work.Diff.EXT.Kpt g x a
          (Fin.append d (Function.update (Function.update (Function.update (Function.update u 0
            (e p)) 1 (e q)) 2 (e r)) 3 (e s)))))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        refine congrArg (fun z => A i p * z) ?_
        refine Finset.sum_congr rfl (fun q _ => ?_)
        refine congrArg (fun z => A j q * z) ?_
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [h4 p q r]
    _ = ∑ p, A i p * (∑ q, A j q * (∑ r, A k r * (∑ s, A l s * Work.Diff.EXT.Kpt g x a
          (Fin.append d ![e p, e q, e r, e s])))) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        refine congrArg (fun z => A i p * z) ?_
        refine Finset.sum_congr rfl (fun q _ => ?_)
        refine congrArg (fun z => A j q * z) ?_
        refine Finset.sum_congr rfl (fun r _ => ?_)
        refine congrArg (fun z => A k r * z) ?_
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [hfinal p q r s]
    _ = rot A (Work.Diff.EXT.KptArr g x a d e) i j k l := by
        have hrot : rot A (Work.Diff.EXT.KptArr g x a d e) i j k l
            = ∑ p, ∑ q, ∑ r, ∑ s, A i p * A j q * A k r * A l s *
                Work.Diff.EXT.Kpt g x a (Fin.append d ![e p, e q, e r, e s]) := by
          simp only [rot, Work.Diff.EXT.KptArr]
        rw [hrot]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        refine Finset.sum_congr rfl (fun q _ => ?_)
        refine Finset.sum_congr rfl (fun r _ => ?_)
        refine Finset.sum_congr rfl (fun s _ => ?_)
        ring

/-! ## The algebraic contraction identity -/

/-- The rank-one four-tensor `B ⊗ C ⊗ D ⊗ E`. -/
private noncomputable def outer4 {n : ℕ} (B C D E : Fin n → ℝ) : Curv4 n :=
  fun a b c d => B a * C b * D c * E d

/-- `rot A` of a rank-one four-tensor is the rank-one four-tensor of the `A`-transformed vectors. -/
private theorem rot_outer4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B C D E : Fin n → ℝ)
    (i j k l : Fin n) :
    rot A (outer4 B C D E) i j k l
      = (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d) := by
  have key : (∑ a, A i a * B a) * (∑ b, A j b * C b) * (∑ c, A k c * D c)
        * (∑ d, A l d * E d)
      = ∑ a, ∑ b, ∑ c, ∑ d,
          A i a * A j b * A k c * A l d * (B a * C b * D c * E d) := by
    have h1 : (∑ a, A i a * B a) * (∑ b, A j b * C b)
        = ∑ a, ∑ b, (A i a * B a) * (A j b * C b) := Finset.sum_mul_sum _ _ _ _
    have h2 : (∑ a, ∑ b, (A i a * B a) * (A j b * C b)) * (∑ c, A k c * D c)
        = ∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul_sum]
    have h3 : (∑ a, ∑ b, ∑ c, (A i a * B a) * (A j b * C b) * (A k c * D c))
          * (∑ d, A l d * E d)
        = ∑ a, ∑ b, ∑ c, ∑ d,
            (A i a * B a) * (A j b * C b) * (A k c * D c) * (A l d * E d) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul_sum]
    rw [h1, h2, h3]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [key]
  simp only [rot, outer4]

/-- **Algebraic contraction identity.**  For an orthogonal `A`, contracting `rot A X` with the four
`A`-transformed coefficient vectors `B, C, D, E` is the same as contracting `X` with the original
coefficient vectors. -/
private theorem rot_vec_contract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (B C D E : Fin n → ℝ) (X : Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l, rot A X i j k l *
        ((∑ r, A i r * B r) * (∑ r, A j r * C r) * (∑ r, A k r * D r)
          * (∑ r, A l r * E r)))
      = ∑ i, ∑ j, ∑ k, ∑ l, X i j k l * (B i * C j * D k * E l) := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, rot A X i j k l *
        ((∑ r, A i r * B r) * (∑ r, A j r * C r) * (∑ r, A k r * D r)
          * (∑ r, A l r * E r)))
      = ∑ i, ∑ j, ∑ k, ∑ l, rot A X i j k l * rot A (outer4 B C D E) i j k l := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    rw [rot_outer4]
  rw [h1, Work.Diff.GE.rot_pair A hA X (outer4 B C D E)]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  simp only [outer4]

/-! ## The target -/

theorem KptArr_frame_indepV
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (hF : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
      ∀ X Y : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
        Work.Diff.EXT.reactionBilin (Submission.Diff.Alg.rot A X) (Submission.Diff.Alg.rot A Y)
          = Submission.Diff.Alg.rot A (Work.Diff.EXT.reactionBilin X Y))
    (g : Submission.Diff.SMet I M) (x : M) (a b : ℕ)
    (d₁ : Fin a → TangentSpace I x) (d₂ : Fin b → TangentSpace I x)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (he' : Submission.Diff.IsONFrame g x e')
    (v : Fin 4 → TangentSpace I x) :
    (∑ i, ∑ j, ∑ k, ∑ l,
        Work.Diff.EXT.reactionBilin (Work.Diff.EXT.KptArr g x a d₁ e)
            (Work.Diff.EXT.KptArr g x b d₂ e) i j k l
          * (g.inner x (e i) (v 0) * g.inner x (e j) (v 1) * g.inner x (e k) (v 2)
              * g.inner x (e l) (v 3)))
      = (∑ i, ∑ j, ∑ k, ∑ l,
        Work.Diff.EXT.reactionBilin (Work.Diff.EXT.KptArr g x a d₁ e')
            (Work.Diff.EXT.KptArr g x b d₂ e') i j k l
          * (g.inner x (e' i) (v 0) * g.inner x (e' j) (v 1) * g.inner x (e' k) (v 2)
              * g.inner x (e' l) (v 3))) := by
  classical
  obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x e e' he he'
  have hK1 : Work.Diff.EXT.KptArr g x a d₁ e'
      = Submission.Diff.Alg.rot A (Work.Diff.EXT.KptArr g x a d₁ e) :=
    KptArr_eq_rot hLC g x a d₁ e e' A hAe
  have hK2 : Work.Diff.EXT.KptArr g x b d₂ e'
      = Submission.Diff.Alg.rot A (Work.Diff.EXT.KptArr g x b d₂ e) :=
    KptArr_eq_rot hLC g x b d₂ e e' A hAe
  have hinner : ∀ (c : TangentSpace I x) (i : Fin (Module.finrank ℝ E)),
      g.inner x (e' i) c = ∑ j, A i j * g.inner x (e j) c := by
    intro c i
    rw [hAe i]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  rw [hK1, hK2,
    hF A hA (Work.Diff.EXT.KptArr g x a d₁ e) (Work.Diff.EXT.KptArr g x b d₂ e)]
  simp only [hinner]
  exact (rot_vec_contract A hA (fun j => g.inner x (e j) (v 0)) (fun j => g.inner x (e j) (v 1))
    (fun j => g.inner x (e j) (v 2)) (fun j => g.inner x (e j) (v 3))
    (Work.Diff.EXT.reactionBilin (Work.Diff.EXT.KptArr g x a d₁ e)
      (Work.Diff.EXT.KptArr g x b d₂ e))).symm

end Work.Diff.EXT.evX
