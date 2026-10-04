import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_defs
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.pd_integral_zero
import Submission.Work.Diff.STE.garding_base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Iterated partial derivatives: plumbing for the commutator estimate

Elementary facts about `pd`, `pdList`, `pdRList` used by the proof of
`Work.Diff.STE.commutator_estimate`.  All smoothness indices are written as coerced natural
numbers, `((n : ℕ) : WithTop ℕ∞)`, so that the arithmetic is arithmetic in `ℕ`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ContDiff` is monotone in the smoothness index (coerced form). -/
lemma cm_of_le {m n : ℕ} {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ ((n : ℕ) : WithTop ℕ∞) f) (h : m ≤ n) :
    ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) f :=
  hf.of_le (Nat.cast_le.mpr h)

/-- Concatenating lists composes `pdList`. -/
lemma cm_pdList_append (a b : List ι) (f : (ι → ℝ) → ℂ) :
    pdList (a ++ b) f = pdList a (pdList b f) := by
  simp only [pdList, List.foldr_append]

/-- `pdList` lowers the smoothness order by the length of the list. -/
lemma cm_contDiff_pdList (q : List ι) (m : ℕ) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((q.length + m : ℕ)) : WithTop ℕ∞) f) :
    ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (pdList q f) := by
  induction q generalizing m with
  | nil => simpa [pdList] using hf
  | cons i q ih =>
      have h : pdList (i :: q) f = pd i (pdList q f) := rfl
      rw [h]
      have hq : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (pdList q f) := by
        refine ih (m + 1) ?_
        rw [show (((i :: q).length + m : ℕ)) = ((q.length + (m + 1) : ℕ)) by
          simp only [List.length_cons]; omega] at hf
        exact hf
      exact contDiff_pd_of_contDiff i hq (le_refl _)

/-- `pdList` of a `1`-periodic function is periodic in every coordinate. -/
lemma cm_periodicIn_pdList (q : List ι) (f : (ι → ℝ) → ℂ)
    (hsm : ∀ q' : List ι, List.Sublist q' q → Differentiable ℝ (pdList q' f))
    (hper : Periodic1 f) (j : ι) : PeriodicIn j (pdList q f) := by
  induction q with
  | nil => exact hper j
  | cons i q ih =>
      have h : pdList (i :: q) f = pd i (pdList q f) := rfl
      rw [h]
      refine periodicIn_pd_of_differentiable j i (hsm q (List.Sublist.cons i (List.Sublist.refl q))) ?_
      exact ih (fun q' hq' => hsm q' (List.Sublist.trans hq' (List.Sublist.cons i (List.Sublist.refl q))))

/-- Sublists of `q` give differentiable iterates, given enough smoothness. -/
lemma cm_diff_pdList_of_contDiff (q : List ι) (m : ℕ) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((q.length + m + 1 : ℕ)) : WithTop ℕ∞) f) :
    ∀ q' : List ι, List.Sublist q' q → Differentiable ℝ (pdList q' f) := by
  intro q' hq'
  have hle : q'.length + 1 ≤ q.length + m + 1 := by
    have := List.Sublist.length_le hq'
    omega
  have h1 : ContDiff ℝ (((q'.length + 1 : ℕ)) : WithTop ℕ∞) f := cm_of_le hf hle
  exact (cm_contDiff_pdList q' 1 f h1).differentiable (by norm_num)

/-- Clairaut/Schwarz: two partial derivatives commute (pointwise). -/
lemma cm_pd_comm_at {f : (ι → ℝ) → ℂ} {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x) (i j : ι) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : ∀ (b k : ι),
      pd k (pd b f) x = (fderiv ℝ (fderiv ℝ f) x) (Pi.single k 1) (Pi.single b 1) := by
    intro b k
    have h2 : fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single b 1)) x
        = (fderiv ℝ (fderiv ℝ f) x).flip (Pi.single b 1) := by
      rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single b (1 : ℝ)))]
      simp
    have h3 : pd k (pd b f) x
        = ((fderiv ℝ (fderiv ℝ f) x).flip (Pi.single b 1)) (Pi.single k 1) := by
      change fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single b 1)) x (Pi.single k 1) = _
      rw [h2]
    rw [h3, ContinuousLinearMap.flip_apply]
  rw [key j i, key i j]
  exact hsym.eq (Pi.single i 1) (Pi.single j 1)

/-- A single partial derivative may be moved past a `pdList`. -/
lemma cm_pd_pdList_comm (i : ι) (q : List ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) f) :
    pd i (pdList q f) = pdList q (pd i f) := by
  induction q with
  | nil => rfl
  | cons j q ih =>
      have h1 : pd i (pdList (j :: q) f) = fun x => pd i (pd j (pdList q f)) x := rfl
      rw [h1]
      funext x
      have hcd : ContDiffAt ℝ 2 (pdList q f) x := by
        have h2 : ContDiff ℝ (((q.length + 2 : ℕ)) : WithTop ℕ∞) f := by
          rw [show (((j :: q).length + 1 : ℕ)) = ((q.length + 2 : ℕ)) by
            simp only [List.length_cons]] at hf
          exact hf
        exact (cm_contDiff_pdList q 2 f h2).contDiffAt
      rw [cm_pd_comm_at hcd i j]
      have hsm : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) f :=
        cm_of_le hf (by simp only [List.length_cons]; omega)
      rw [ih hsm]
      rfl

/-- Two blocks of partial derivatives may be swapped. -/
lemma cm_pdList_append_comm (a b : List ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((a.length + b.length : ℕ)) : WithTop ℕ∞) f) :
    pdList (a ++ b) f = pdList (b ++ a) f := by
  induction b with
  | nil => simp [cm_pdList_append]
  | cons j b ih =>
      have hsm2 : ContDiff ℝ (((a.length + b.length : ℕ)) : WithTop ℕ∞) f :=
        cm_of_le hf (by simp only [List.length_cons]; omega)
      have hsm1 : ContDiff ℝ (((a.length + 1 : ℕ)) : WithTop ℕ∞) (pdList b f) := by
        have hEq : ((b.length + (a.length + 1) : ℕ)) = ((a.length + (j :: b).length : ℕ)) := by
          simp only [List.length_cons]; omega
        have hf' : ContDiff ℝ (((b.length + (a.length + 1) : ℕ)) : WithTop ℕ∞) f := by
          rw [hEq]; exact hf
        exact cm_contDiff_pdList b (a.length + 1) f hf'
      calc pdList (a ++ (j :: b)) f
          = pdList a (pd j (pdList b f)) := by rw [cm_pdList_append]; rfl
        _ = pd j (pdList a (pdList b f)) := (cm_pd_pdList_comm j a (pdList b f) hsm1).symm
        _ = pd j (pdList (a ++ b) f) := by rw [cm_pdList_append a b f]
        _ = pd j (pdList (b ++ a) f) := by rw [ih hsm2]
        _ = pdList (j :: (b ++ a)) f := rfl
        _ = pdList ((j :: b) ++ a) f := rfl

/-- `∂_c∂_d` commutes with `∂^l`. -/
lemma cm_pdVec_pd_pd (k : ℕ) (l : Fin k → ι) (c d : ι) (u : (ι → ℝ) → ℂ)
    (hu : ContDiff ℝ (((k + 2 : ℕ)) : WithTop ℕ∞) u) :
    pdVec k l (pd c (pd d u)) = pd c (pd d (pdVec k l u)) := by
  have h1 : pdVec k l (pd c (pd d u)) = pdList (List.ofFn l ++ [c, d]) u := by
    rw [pdVec, cm_pdList_append]
    rfl
  have h2 : pd c (pd d (pdVec k l u)) = pdList ([c, d] ++ List.ofFn l) u := by
    rw [pdVec, cm_pdList_append]
    rfl
  rw [h1, h2]
  exact cm_pdList_append_comm (List.ofFn l) [c, d] u (by simpa using hu)

/-- Real-valued partial derivative is `Cᵐ` when the function is `C^{m+1}`. -/
lemma cm_contDiff_pdR (m : ℕ) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) F)
    (i : ι) : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (pdR i F) := by
  have h : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (m := m) (le_refl _)
  have h2 : ContDiff ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun x => (fderiv ℝ F x) (Pi.single i (1 : ℝ))) := by
    have h3 := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.comp h
    simpa [Function.comp_def, ContinuousLinearMap.apply_apply] using h3
  exact h2

/-- `pdRList` lowers the smoothness order by the length of the list. -/
lemma cm_contDiff_pdRList (q : List ι) (m : ℕ) (F : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ (((q.length + m : ℕ)) : WithTop ℕ∞) F) :
    ContDiff ℝ ((m : ℕ) : WithTop ℕ∞) (pdRList q F) := by
  induction q generalizing m with
  | nil => simpa [pdRList] using hF
  | cons i q ih =>
      have h : pdRList (i :: q) F = pdR i (pdRList q F) := rfl
      rw [h]
      have hq : ContDiff ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (pdRList q F) := by
        refine ih (m + 1) ?_
        rw [show (((i :: q).length + m : ℕ)) = ((q.length + (m + 1) : ℕ)) by
          simp only [List.length_cons]; omega] at hF
        exact hF
      exact cm_contDiff_pdR m (pdRList q F) hq i

/-- The coercion `ℝ → ℂ` commutes with iterated partial derivatives. -/
lemma cm_pdList_ofReal (q : List ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ ⊤ F) :
    pdList q (fun y => (F y : ℂ)) = fun y => ((pdRList q F y : ℝ) : ℂ) := by
  induction q with
  | nil => rfl
  | cons i q ih =>
      have h : pdList (i :: q) (fun y => (F y : ℂ))
          = pd i (pdList q (fun y => (F y : ℂ))) := rfl
      rw [h, ih]
      funext x
      have h1 : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) F :=
        hF.of_le (le_top)
      have hd : DifferentiableAt ℝ (pdRList q F) x :=
        (cm_contDiff_pdRList q 1 F h1).differentiable (by norm_num) |>.differentiableAt
      rw [ga_pd_ofReal i (pdRList q F) x hd]
      rfl

/-- An iterated derivative of order `≥ 1` of a periodic function integrates to `0`. -/
lemma cm_integral_pdVec_eq_zero (j : ℕ) (l : Fin j → ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (((j + 1 : ℕ)) : WithTop ℕ∞) f) (hper : Periodic1 f) (hj : 1 ≤ j) :
    ∫ x in unitCube, pdVec j l f x = 0 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hsplit : List.ofFn l
      = (List.ofFn (fun i : Fin j' => l (Fin.castSucc i))).concat (l (Fin.last j')) :=
    List.ofFn_succ' l
  have hsplit' : List.ofFn l
      = List.ofFn (fun i : Fin j' => l (Fin.castSucc i)) ++ [l (Fin.last j')] := by
    rw [hsplit, List.concat_eq_append]
  set q : List ι := List.ofFn (fun i : Fin j' => l (Fin.castSucc i)) with hq
  have hqlen : q.length = j' := by simp [hq]
  have ih1 : pdVec (j' + 1) l f
      = pdList q (pd (l (Fin.last j')) f) := by
    rw [pdVec, hsplit', cm_pdList_append]
    rfl
  have ih2 : pdList q (pd (l (Fin.last j')) f)
      = pd (l (Fin.last j')) (pdList q f) := by
    refine (cm_pd_pdList_comm (l (Fin.last j')) q f ?_).symm
    have h1 : ContDiff ℝ (((j' + 1 : ℕ)) : WithTop ℕ∞) f := cm_of_le hf (by omega)
    exact cm_of_le h1 (by simp [hqlen])
  rw [ih1, ih2]
  refine integral_pd_unitCube_zero (l (Fin.last j')) ?_ ?_
  · have h1 : ContDiff ℝ (((q.length + 1 : ℕ)) : WithTop ℕ∞) f := by
      rw [hqlen]; exact cm_of_le hf (by omega)
    exact cm_contDiff_pdList q 1 f h1
  · refine cm_periodicIn_pdList q f (fun q' hq' => ?_) hper (l (Fin.last j'))
    have h1 : ContDiff ℝ (((q.length + 0 + 1 : ℕ)) : WithTop ℕ∞) f := by
      rw [hqlen]; exact cm_of_le hf (by omega)
    exact cm_diff_pdList_of_contDiff q 0 f h1 q' hq'


/-- `pd i` is linear over finite sums (pointwise). -/
lemma cm_pd_finset_sum {β : Type*} (i : ι) (S : Finset β) (f : β → (ι → ℝ) → ℂ)
    (hf : ∀ b ∈ S, Differentiable ℝ (f b)) :
    pd i (fun y => ∑ b ∈ S, f b y) = fun y => ∑ b ∈ S, pd i (f b) y := by
  have hfun : (fun y => ∑ b ∈ S, f b y) = (∑ b ∈ S, f b) := by
    funext y
    exact (Finset.sum_apply y S f).symm
  rw [hfun]
  funext y
  simp only [pd]
  rw [fderiv_sum (x := y) (u := S) (fun b hb => (hf b hb).differentiableAt)]
  exact sum_apply S (fun b => fderiv ℝ (f b) y) (Pi.single i (1 : ℝ))

/-- `pdList` is linear over finite sums. -/
lemma cm_pdList_sum {β : Type*} (l : List ι) (S : Finset β) (f : β → (ι → ℝ) → ℂ)
    (hf : ∀ b ∈ S, ∀ q : List ι, List.Sublist q l → q.length < l.length →
      Differentiable ℝ (pdList q (f b))) :
    pdList l (fun y => ∑ b ∈ S, f b y) = fun y => ∑ b ∈ S, pdList l (f b) y := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have h1 : pdList (i :: l) (fun y => ∑ b ∈ S, f b y)
          = pd i (pdList l (fun y => ∑ b ∈ S, f b y)) := rfl
      rw [h1]
      have h2 : pdList l (fun y => ∑ b ∈ S, f b y) = fun y => ∑ b ∈ S, pdList l (f b) y :=
        ih (fun b hb q hq hlen => hf b hb q (List.Sublist.cons i hq) (by
          simp only [List.length_cons]; omega))
      rw [h2]
      refine cm_pd_finset_sum i S (fun b y => pdList l (f b) y) (fun b hb => ?_)
      exact hf b hb l (List.Sublist.cons i (List.Sublist.refl l)) (by simp)

/-- The second-order derivative as the list `[c, d]`. -/
lemma cm_pdList_pair (q : List ι) (c d : ι) (u : (ι → ℝ) → ℂ) :
    pdList q (fun z => pd c (pd d u) z) = pdList (q ++ [c, d]) u := by
  rw [cm_pdList_append]
  rfl

end Work.Diff.STE
