import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.commutator_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform bound for all iterated periodic derivatives of a periodic smooth function

`pdRList q F` is the iterated partial derivative of `F : (ι → ℝ) → ℝ` along the list of
directions `q`.  We prove that there is a single `M ≥ 0` bounding `|pdRList q F|` on all of
`ι → ℝ` for *every* list `q` of length `≤ m`.

The two ingredients are:

* a continuous function on `ι → ℝ` which is `1`-periodic in every coordinate is bounded:
  it is invariant under shifts by integer vectors, so it takes its values on the compact
  closed unit cube `[0,1]^ι`;
* there are only finitely many lists of length `≤ m`, indexed by `Σ ℓ : Fin (m+1), (Fin ℓ → ι)`.

Everything is elementary: no Fourier analysis is used.
-/

noncomputable section

namespace Work.Diff.STE

/-- Index set for the finitely many iterated derivative directions of order `≤ m`: a length
`ℓ ≤ m` together with a direction for each of the `ℓ` derivatives. -/
abbrev ebJetIdx (ι : Type*) (m : ℕ) : Type _ := Σ ℓ : Fin (m + 1), (Fin ℓ.val → ι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Periodicity in one coordinate is invariance under integer multiples of the corresponding
basis vector. -/
lemma eb_periodicIn_shift_int (i : ι) {f : (ι → ℝ) → ℝ} (h : PeriodicIn i f) (n : ℤ)
    (x : ι → ℝ) : f (x + (n : ℝ) • (Pi.single i (1 : ℝ) : ι → ℝ)) = f x := by
  set e : ι → ℝ := Pi.single i (1 : ℝ) with he
  have hper : Function.Periodic (fun t : ℝ => f (x + t • e)) 1 := by
    intro t
    change f (x + (t + 1) • e) = f (x + t • e)
    have hstep : x + (t + 1) • e = (x + t • e) + e := by
      rw [add_smul, one_smul, add_assoc]
    rw [hstep]
    exact h (x + t • e)
  have h2 := hper.zsmul n 0
  simpa [he, zsmul_eq_mul] using h2

/-- Shifting by an integer vector does not change a function that is `1`-periodic in every
coordinate. -/
lemma eb_periodic1_add_intVec {f : (ι → ℝ) → ℝ} (hper : Periodic1 f) (v : ι → ℝ)
    (hv : ∀ i, ∃ n : ℤ, v i = (n : ℝ)) (x : ι → ℝ) : f (x + v) = f x := by
  classical
  have key : ∀ s : Finset ι, f (x + fun i => if i ∈ s then v i else 0) = f x := by
    intro s
    induction s using Finset.induction with
    | empty =>
      have hz : (fun i : ι => if i ∈ (∅ : Finset ι) then v i else 0) = (0 : ι → ℝ) := by
        funext i; simp
      rw [hz]
      simp
    | insert a s ha ih =>
      have hvec : (fun i => if i ∈ insert a s then v i else 0)
          = (fun i => if i ∈ s then v i else 0) + (v a) • (Pi.single a (1 : ℝ) : ι → ℝ) := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [ha, Pi.single_eq_same, smul_eq_mul]
        · simp only [Pi.add_apply, Pi.smul_apply]
          rw [Pi.single_eq_of_ne hi]
          simp [Finset.mem_insert, hi]
      rw [hvec, ← add_assoc]
      obtain ⟨n, hn⟩ := hv a
      rw [hn]
      exact (eb_periodicIn_shift_int a (hper a) n
        (x + fun i => if i ∈ s then v i else 0)).trans ih
  have hfin := key Finset.univ
  rwa [show (fun i => if i ∈ (Finset.univ : Finset ι) then v i else 0) = v from by
    funext i; simp] at hfin

/-- A continuous function on `ι → ℝ` which is `1`-periodic in every coordinate is bounded. -/
lemma eb_exists_bound_of_continuous_periodic1 {f : (ι → ℝ) → ℝ} (hc : Continuous f)
    (hper : Periodic1 f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  classical
  set S : Set ℝ := (fun x : ι → ℝ => |f x|) '' Set.Icc (0 : ι → ℝ) 1 with hS
  have hcomp : IsCompact (Set.Icc (0 : ι → ℝ) (1 : ι → ℝ)) := isCompact_Icc
  have hbdd : BddAbove S := (hcomp.image hc.abs).bddAbove
  have hmem0 : |f 0| ∈ S :=
    ⟨0, by rw [Set.mem_Icc, Pi.le_def]; exact ⟨fun _ => le_rfl, fun _ => zero_le_one⟩, rfl⟩
  refine ⟨sSup S, le_trans (abs_nonneg _) (le_csSup hbdd hmem0), fun x => ?_⟩
  have hred : (fun i => Int.fract (x i)) ∈ Set.Icc (0 : ι → ℝ) 1 := by
    rw [Set.mem_Icc, Pi.le_def]
    exact ⟨fun i => Int.fract_nonneg (x i), fun i => le_of_lt (Int.fract_lt_one (x i))⟩
  have hshift : f x = f (fun i => Int.fract (x i)) := by
    have h := eb_periodic1_add_intVec hper (fun i => (Int.floor (x i) : ℝ))
      (fun i => ⟨Int.floor (x i), rfl⟩) (fun i => Int.fract (x i))
    have hxy : (fun i => Int.fract (x i)) + (fun i => (Int.floor (x i) : ℝ)) = x := by
      funext i
      exact Int.fract_add_floor (x i)
    rw [hxy] at h
    exact h
  rw [hshift]
  exact le_csSup hbdd ⟨_, hred, rfl⟩

/-- `pdRList` of an analytic function is continuous. -/
lemma eb_continuous_pdRList (q : List ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ ⊤ F) :
    Continuous (pdRList q F) :=
  (cm_contDiff_pdRList q 0 F (hF.of_le le_top)).continuous

/-- `pdRList` of a `1`-periodic function is `1`-periodic. -/
lemma eb_periodic1_pdRList (q : List ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hper : Periodic1 F) : Periodic1 (pdRList q F) := by
  intro j
  have hfc : ContDiff ℝ ⊤ (fun y : ι → ℝ => (F y : ℂ)) := ga_contDiff_ofReal hF
  have hsm : ∀ q' : List ι, List.Sublist q' q →
      Differentiable ℝ (pdList q' (fun y : ι → ℝ => (F y : ℂ))) :=
    cm_diff_pdList_of_contDiff q 0 _ (hfc.of_le le_top)
  have hperC : Periodic1 (fun y : ι → ℝ => (F y : ℂ)) := fun i x => by
    show ((F (x + Pi.single i 1) : ℝ) : ℂ) = ((F x : ℝ) : ℂ)
    rw [hper i x]
  have h1 := cm_periodicIn_pdList q (fun y : ι → ℝ => (F y : ℂ)) hsm hperC j
  rw [cm_pdList_ofReal q F hF] at h1
  intro x
  have h := h1 x
  change ((pdRList q F (x + Pi.single j 1) : ℝ) : ℂ) = ((pdRList q F x : ℝ) : ℂ) at h
  exact Complex.ofReal_injective h

/-- The `Fin k`-indexed iterated derivative is continuous. -/
lemma eb_continuous_pdRVec (k : ℕ) (l : Fin k → ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ ⊤ F) :
    Continuous (pdRVec k l F) := by
  simpa [pdRVec] using eb_continuous_pdRList (List.ofFn l) F hF

/-- The `Fin k`-indexed iterated derivative is `1`-periodic. -/
lemma eb_periodic1_pdRVec (k : ℕ) (l : Fin k → ι) (F : (ι → ℝ) → ℝ) (hF : ContDiff ℝ ⊤ F)
    (hper : Periodic1 F) : Periodic1 (pdRVec k l F) := by
  simpa [pdRVec] using eb_periodic1_pdRList (List.ofFn l) F hF hper

theorem exists_bound_pdRList {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (F : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ ⊤ F) (hper : Periodic1 F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : List ι, q.length ≤ m → ∀ x : ι → ℝ, |pdRList q F x| ≤ M := by
  classical
  haveI : Nonempty (ebJetIdx ι m) := ⟨⟨⟨0, Nat.zero_lt_succ m⟩, Fin.elim0⟩⟩
  have hb : ∀ s : ebJetIdx ι m, ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : ι → ℝ, |pdRVec s.1.val s.2 F x| ≤ M :=
    fun s => eb_exists_bound_of_continuous_periodic1
      (eb_continuous_pdRVec s.1.val s.2 F hF) (eb_periodic1_pdRVec s.1.val s.2 F hF hper)
  refine ⟨Finset.univ.sup' Finset.univ_nonempty
    (fun s : ebJetIdx ι m => Classical.choose (hb s)), ?_, ?_⟩
  · refine le_trans (Classical.choose_spec (hb ⟨⟨0, Nat.zero_lt_succ m⟩, Fin.elim0⟩)).1 ?_
    exact Finset.le_sup' (fun s : ebJetIdx ι m => Classical.choose (hb s)) (Finset.mem_univ _)
  · intro q hq x
    have hlt : q.length < m + 1 := Nat.lt_succ_of_le hq
    have hval : pdRVec q.length (fun i : Fin q.length => q.get i) F = pdRList q F := by
      rw [pdRVec, List.ofFn_get]
    have hb' : |pdRVec q.length (fun i : Fin q.length => q.get i) F x| ≤
        Classical.choose (hb ⟨⟨q.length, hlt⟩, fun i : Fin q.length => q.get i⟩) :=
      (Classical.choose_spec (hb ⟨⟨q.length, hlt⟩, fun i : Fin q.length => q.get i⟩)).2 x
    calc |pdRList q F x|
        = |pdRVec q.length (fun i : Fin q.length => q.get i) F x| := by simp only [hval]
      _ ≤ Classical.choose (hb ⟨⟨q.length, hlt⟩, fun i : Fin q.length => q.get i⟩) := hb'
      _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun s : ebJetIdx ι m => Classical.choose (hb s)) :=
          Finset.le_sup' (fun s : ebJetIdx ι m => Classical.choose (hb s)) (Finset.mem_univ _)

end Work.Diff.STE
