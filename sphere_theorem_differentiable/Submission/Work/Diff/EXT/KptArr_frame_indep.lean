import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.GE.onFrame_orthogonal_change
import Submission.Work.Diff.Alg.rot_contract4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Auxiliary pieces

(The two lemmas below are the two independent ingredients of the frame-independence proof.  They
are *base* lemmas: this module is imported by `Submission.Work.Diff.EXT.reaction0_jets`, so it can
only use definitions that do not depend on it.) -/

/-- **The contraction of a `Curv4` array with four coefficient vectors is invariant under an
orthogonal change of frame.**  If `AᵀA = 1` and the vector `cₜ` is replaced by its image `A cₜ`
under `A`, then contracting `rot A Ψ` against the image vectors gives the same number as
contracting `Ψ` against the original vectors. -/
private theorem rotMulVec_contract_aux {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Matrix.transpose A * A = 1) (Ψ : Submission.Diff.Alg.Curv4 n)
    (c0 c1 c2 c3 : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, Submission.Diff.Alg.rot A Ψ i j k l *
        (Matrix.mulVec A c0 i * Matrix.mulVec A c1 j * Matrix.mulVec A c2 k
          * Matrix.mulVec A c3 l))
      = ∑ i, ∑ j, ∑ k, ∑ l, Ψ i j k l * (c0 i * c1 j * c2 k * c3 l) := by
  have horth : A ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mpr hA
  have hL : (∑ i, ∑ j, ∑ k, ∑ l, Submission.Diff.Alg.rot A Ψ i j k l *
        (Matrix.mulVec A c0 i * Matrix.mulVec A c1 j * Matrix.mulVec A c2 k
          * Matrix.mulVec A c3 l))
      = ∑ i, ∑ j, ∑ k, ∑ l, Matrix.mulVec A c0 i * Matrix.mulVec A c1 j
          * Matrix.mulVec A c2 k * Matrix.mulVec A c3 l
          * Submission.Diff.Alg.rot A Ψ i j k l := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    ring
  rw [hL, Work.Diff.Alg.rot_contract4 A horth Ψ c0 c1 c2 c3]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))))
  ring

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

/-- **Frame change of the point-level tower array.**  Expanding a new frame `e'` in an old one,
`e' i = ∑ j, A i j • e j`, multiplies the component array `KptArr g x a d ·` by `A` in each of its
four indices: `KptArr g x a d e' = rot A (KptArr g x a d e)`.  Only the multilinearity of the
packaged evaluation `KptLin` is used. -/
private theorem KptArr_rot_aux (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (a : ℕ) (d : Fin a → TangentSpace I x)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • e j) :
    Work.Diff.EXT.KptArr g x a d e'
      = Submission.Diff.Alg.rot A (Work.Diff.EXT.KptArr g x a d e) := by
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
    _ = Submission.Diff.Alg.rot A (Work.Diff.EXT.KptArr g x a d e) i j k l := by
        have hrot : Submission.Diff.Alg.rot A (Work.Diff.EXT.KptArr g x a d e) i j k l
            = ∑ p, ∑ q, ∑ r, ∑ s, A i p * A j q * A k r * A l s *
                Work.Diff.EXT.Kpt g x a (Fin.append d ![e p, e q, e r, e s]) := by
          simp only [Submission.Diff.Alg.rot, Work.Diff.EXT.KptArr]
        rw [hrot]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        refine Finset.sum_congr rfl (fun q _ => ?_)
        refine Finset.sum_congr rfl (fun r _ => ?_)
        refine Finset.sum_congr rfl (fun s _ => ?_)
        ring

/-! ## The target -/

theorem KptArr_frame_indep
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
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- two orthonormal frames differ by an orthogonal matrix
  obtain ⟨A, hAorth, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change g x e e' he he'
  have htA : Matrix.transpose A * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin (Module.finrank ℝ E)) ℝ).mp hAorth
  -- the component arrays change by `rot A`
  have hKe : KptArr g x a d₁ e' = Submission.Diff.Alg.rot A (KptArr g x a d₁ e) :=
    KptArr_rot_aux hLC g x a d₁ e e' A hAe
  have hKe₂ : KptArr g x b d₂ e' = Submission.Diff.Alg.rot A (KptArr g x b d₂ e) :=
    KptArr_rot_aux hLC g x b d₂ e e' A hAe
  -- the pairings against `e'` are the `A`-images of the pairings against `e`
  have hcoef : ∀ (t : Fin 4) (m : Fin (Module.finrank ℝ E)),
      g.inner x (e' m) (v t) = Matrix.mulVec A (fun p => g.inner x (e p) (v t)) m := by
    intro t m
    rw [hAe m]
    show inner ℝ (∑ j, A m j • e j) (v t) = Matrix.mulVec A (fun p => g.inner x (e p) (v t)) m
    rw [sum_inner]
    simp only [real_inner_smul_left]
    rw [Matrix.mulVec_apply, Matrix.row]
    rfl
  -- `e`-side: the contraction of `Ψ = reactionBilin (∇ᵃRm) (∇ᵇRm)` with the `e`-coordinates
  have hE : (∑ i, ∑ j, ∑ k, ∑ l,
        reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e) i j k l
          * (g.inner x (e i) (v 0) * g.inner x (e j) (v 1) * g.inner x (e k) (v 2)
              * g.inner x (e l) (v 3)))
      = ∑ i, ∑ j, ∑ k, ∑ l,
        reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e) i j k l
          * ((fun m => g.inner x (e m) (v 0)) i * (fun m => g.inner x (e m) (v 1)) j
              * (fun m => g.inner x (e m) (v 2)) k * (fun m => g.inner x (e m) (v 3)) l) :=
    rfl
  -- the rotated contraction
  have hrot : (∑ i, ∑ j, ∑ k, ∑ l,
        Submission.Diff.Alg.rot A (reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e))
            i j k l
          * (Matrix.mulVec A (fun m => g.inner x (e m) (v 0)) i
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 1)) j
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 2)) k
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 3)) l))
      = ∑ i, ∑ j, ∑ k, ∑ l,
        reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e) i j k l
          * ((fun m => g.inner x (e m) (v 0)) i * (fun m => g.inner x (e m) (v 1)) j
              * (fun m => g.inner x (e m) (v 2)) k * (fun m => g.inner x (e m) (v 3)) l) :=
    rotMulVec_contract_aux A htA (reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e))
      (fun m => g.inner x (e m) (v 0)) (fun m => g.inner x (e m) (v 1))
      (fun m => g.inner x (e m) (v 2)) (fun m => g.inner x (e m) (v 3))
  -- the `e'`-side is the rotated contraction
  have hE' : (∑ i, ∑ j, ∑ k, ∑ l,
        Submission.Diff.Alg.rot A (reactionBilin (KptArr g x a d₁ e) (KptArr g x b d₂ e))
            i j k l
          * (Matrix.mulVec A (fun m => g.inner x (e m) (v 0)) i
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 1)) j
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 2)) k
              * Matrix.mulVec A (fun m => g.inner x (e m) (v 3)) l))
      = (∑ i, ∑ j, ∑ k, ∑ l,
        reactionBilin (KptArr g x a d₁ e') (KptArr g x b d₂ e') i j k l
          * (g.inner x (e' i) (v 0) * g.inner x (e' j) (v 1) * g.inner x (e' k) (v 2)
              * g.inner x (e' l) (v 3))) := by
    rw [hKe, hKe₂, hF A hAorth]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hcoef 0 i, hcoef 1 j, hcoef 2 k, hcoef 3 l]
  exact hE.trans (hrot.symm.trans hE')

end Work.Diff.EXT
