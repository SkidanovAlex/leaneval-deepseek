import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.energy_le_of_coeff_bounds
import Submission.Work.Diff.STE.ENormSq_pairing_le
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniqueness for the flat torus DeTurck Cauchy problem

This file proves `Work.Diff.STE.flat.torus_uniqueness`: two smooth `1`-periodic positive definite
solutions of the flat quasilinear parabolic system `∂ₜu = Φ(·, jet u)` with a nonlinearity of
DeTurck shape and with the same initial datum agree.

The proof is the classical `L²` energy argument.  Writing `w = u - v` and using the DeTurck shape
`Φ (x,(A,L,B)) = secOpFlat A B + N (x,(A,L))` one has the *exact* decomposition

  `∂ₜw_{ij} = Σ_{c,d} a^{cd} ∂_c∂_d w_{ij} + R_{ij}`,   `a^{cd} := ((reMat A_u)⁻¹)^{cd}`,

with a remainder `R` that is a Lipschitz function of `(w, ∂w)` alone (uniformly on the strip).
Since `a` is smooth, symmetric and uniformly elliptic, Gårding's estimate on the torus gives

  `d/dt ‖w‖²_{L²} ≤ K ‖w‖²_{L²}`,

and Grönwall finishes.

## Layout

* `hasFDerivAt_slice_of_hasFDerivWithinAt` : the `x`-slice of a function differentiable within
  `Ico 0 T × univ` is differentiable, with the within-derivative composed with `inr`.
* `contDiffOn_pd_slice`, `contDiffOn_pdList_slice` : joint smoothness of the iterated
  `x`-partial derivatives of a jointly smooth function on `Ico 0 T × univ`.
* `ContinuousOn.det`, `contDiffOn_matrixInv_entry` : smoothness of the determinant and of the
  entries of the inverse of a (jointly) smooth matrix function, away from `det = 0`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

open MeasureTheory Set Filter
open scoped Topology Matrix

variable {n : ℕ}

/-! ## Slices and partial derivatives -/

/-- If `f` is differentiable within `S = Ico 0 T × univ` at `(t,x)`, then the slice
`y ↦ f (t,y)` is differentiable at `x`, with derivative the `S`-derivative of `f` composed with
`inr`. -/
lemma hasFDerivAt_slice_of_hasFDerivWithinAt {n : ℕ} {f : ℝ × (Fin n → ℝ) → ℂ}
    {f' : (ℝ × (Fin n → ℝ)) →L[ℝ] ℂ} {T t : ℝ} {x : Fin n → ℝ} (ht : t ∈ Set.Ico (0:ℝ) T)
    (hf : HasFDerivWithinAt f f' (Set.Ico (0:ℝ) T ×ˢ Set.univ) (t,x)) :
    HasFDerivAt (fun y : Fin n → ℝ => f (t,y))
      (f'.comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))) x := by
  have hg : HasFDerivAt (fun y : Fin n → ℝ => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) x :=
    hasFDerivAt_prodMk_right t x
  have hmem : ∀ᶠ y in nhds x, (t,y) ∈ (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    Filter.Eventually.of_forall fun y => ⟨ht, Set.mem_univ y⟩
  exact hf.comp_hasFDerivAt x hg hmem

/-- The `x`-partial derivative of a function that is jointly `C^∞` on `Ico 0 T × univ`
is again jointly `C^∞` there. -/
lemma contDiffOn_pd_slice {n : ℕ} {F : ℝ → (Fin n → ℝ) → ℂ} {T : ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) (c : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => pd c (F p.1) p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  set S : Set (ℝ × (Fin n → ℝ)) := Set.Ico (0:ℝ) T ×ˢ Set.univ with hS
  have huniq : UniqueDiffOn ℝ S := (uniqueDiffOn_Ico 0 T).prod uniqueDiffOn_univ
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)) =>
        (fderivWithin ℝ (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2) S q.1) q.2) (S ×ˢ Set.univ) :=
    contDiffOn_fderivWithin_apply hF huniq (by simp)
  have hlin : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => (p, ((0 : ℝ), (Pi.single c 1 : Fin n → ℝ)))) S :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) =>
        (fderivWithin ℝ (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2) S p) (0, Pi.single c 1)) S :=
    hd.comp hlin (fun p hp => ⟨hp, Set.mem_univ _⟩)
  refine hcomp.congr (fun p hp => ?_)
  obtain ⟨t,x⟩ := p
  show pd c (F t) x
    = (fderivWithin ℝ (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2) S (t,x)) (0, Pi.single c 1)
  have hder : HasFDerivWithinAt (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      (fderivWithin ℝ (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2) S (t,x)) S (t,x) :=
    ((hF.contDiffWithinAt hp).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hsl := hasFDerivAt_slice_of_hasFDerivWithinAt hp.1 hder
  rw [show pd c (F t) x = fderiv ℝ (fun y : Fin n → ℝ => F t y) x (Pi.single c 1) from rfl,
    hsl.fderiv]
  rfl

/-- Joint smoothness of the iterated `x`-partial derivatives of a jointly smooth function
on `Ico 0 T × univ`. -/
lemma contDiffOn_pdList_slice {n : ℕ} (T : ℝ) (l : List (Fin n)) :
    ∀ (F : ℝ → (Fin n → ℝ) → ℂ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
        (Set.Ico (0:ℝ) T ×ˢ Set.univ) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => pdList l (F p.1) p.2)
        (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  induction l with
  | nil => intro F hF; simpa [pdList] using hF
  | cons c l ih =>
      intro F hF
      exact contDiffOn_pd_slice (F := fun t x => pdList l (F t) x) (ih F hF) c

/-- The time slice of a function that is jointly `C^∞` on `Ico 0 T × univ` is `C^∞`. -/
lemma contDiff_slice_of_contDiffOn {n : ℕ} {F : ℝ → (Fin n → ℝ) → ℂ} {T t : ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) (ht : t ∈ Set.Ico (0:ℝ) T) :
    ContDiff ℝ (⊤ : ℕ∞) (F t) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => (t, y)) :=
    contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo (fun y : Fin n → ℝ => (t, y)) Set.univ
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := fun y _ => ⟨ht, Set.mem_univ y⟩
  have h := hF.comp hg.contDiffOn hmap
  rw [contDiffOn_univ] at h
  exact h

/-! ## Entrywise consequences of joint smoothness -/

/-- The time slice of a real-valued function that is jointly `C^∞` on `Ico 0 T × univ`. -/
lemma contDiff_slice_of_contDiffOn_real {n : ℕ} {F : ℝ → (Fin n → ℝ) → ℝ} {T t : ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) (ht : t ∈ Set.Ico (0:ℝ) T) :
    ContDiff ℝ (⊤ : ℕ∞) (F t) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => (t, y)) :=
    contDiff_const.prodMk contDiff_id
  have hmap : Set.MapsTo (fun y : Fin n → ℝ => (t, y)) Set.univ
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := fun y _ => ⟨ht, Set.mem_univ y⟩
  have h := hF.comp hg.contDiffOn hmap
  rw [contDiffOn_univ] at h
  exact h

/-- The entries of a jointly smooth matrix function are jointly smooth. -/
lemma contDiffWithinAt_apply₂ {n : ℕ} {F : ℝ × (Fin n → ℝ) → MatC n}
    {S : Set (ℝ × (Fin n → ℝ))} {p : ℝ × (Fin n → ℝ)}
    (hF : ContDiffWithinAt ℝ (⊤ : ℕ∞) F S p) (i j : Fin n) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun q => F q i j) S p :=
  (contDiffWithinAt_pi.mp (contDiffWithinAt_pi.mp hF i)) j

lemma contDiffOn_entry_of_contDiffOn {n : ℕ} {F : ℝ × (Fin n → ℝ) → MatC n}
    {S : Set (ℝ × (Fin n → ℝ))} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => F q i j) S :=
  fun q hq => contDiffWithinAt_apply₂ (hF q hq) i j

/-- The real part of an entry of a jointly smooth matrix function is jointly smooth. -/
lemma contDiffOn_reMat_entry {n : ℕ} {F : ℝ × (Fin n → ℝ) → MatC n}
    {S : Set (ℝ × (Fin n → ℝ))} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => reMat (F q) i j) S := by
  intro p hp
  have h := (contDiffWithinAt_apply₂ (hF p hp) i j)
  have h2 := (Complex.reCLM.contDiff).comp_contDiffWithinAt h
  have h3 : (⇑Complex.reCLM ∘ fun q : ℝ × (Fin n → ℝ) => F q i j) = fun q => (F q i j).re := by
    funext q; simp [Complex.reCLM_apply]
  rw [h3] at h2
  simpa [reMat_apply] using h2

/-! ## A representative of `x` modulo the period lattice -/

lemma periodic1_zsmul {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β} (hf : Periodic1 f)
    (i : Fin n) (k : ℤ) (z : Fin n → ℝ) :
    f (z + (k : ℝ) • Pi.single i (1:ℝ)) = f z := by
  have hnat : ∀ m : ℕ, f (z + (m : ℝ) • Pi.single i (1:ℝ)) = f z := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        have hvec : z + (((m:ℝ) + 1) • Pi.single i (1:ℝ))
            = (z + (m : ℝ) • Pi.single i (1:ℝ)) + Pi.single i 1 := by
          rw [add_smul, one_smul]; abel
        rw [hcast, hvec, hf i, ih]
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa using hnat m
  · push_neg at hk
    have hz : ∀ m : ℕ, f (z - (m : ℝ) • Pi.single i (1:ℝ)) = f z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          have hvec : z - (((m:ℝ) + 1) • Pi.single i (1:ℝ))
              = (z - (m : ℝ) • Pi.single i (1:ℝ)) - Pi.single i 1 := by
            rw [add_smul, one_smul]; abel
          have h2 : ((z - (m : ℝ) • Pi.single i (1:ℝ)) - Pi.single i 1) + Pi.single i 1
              = z - (m : ℝ) • Pi.single i (1:ℝ) := by abel
          have h3 := hf i ((z - (m : ℝ) • Pi.single i (1:ℝ)) - Pi.single i 1)
          rw [h2] at h3
          rw [hcast, hvec, ← h3, ih]
    have hk' : k = - ((-k).natAbs : ℤ) := by omega
    rw [hk', Int.cast_neg, neg_smul]
    exact hz _

lemma periodic1_sum {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β} (hf : Periodic1 f)
    (c : Fin n → ℤ) (z : Fin n → ℝ) :
    f (z + ∑ i, (c i : ℝ) • Pi.single i (1:ℝ)) = f z := by
  classical
  have h : ∀ s : Finset (Fin n), f (z + ∑ i ∈ s, (c i : ℝ) • Pi.single i (1:ℝ)) = f z := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        have hv : z + ((c a : ℝ) • Pi.single a 1 + ∑ i ∈ s, (c i:ℝ) • Pi.single i 1)
            = (z + ∑ i ∈ s, (c i:ℝ) • Pi.single i 1) + (c a : ℝ) • Pi.single a 1 := by abel
        rw [hv, periodic1_zsmul hf a (c a), ih]
  simpa using h Finset.univ

/-- A representative of `x` modulo the lattice `ℤ^n`, lying in `[0,1]^n`. -/
noncomputable def periodicRep {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  x - ∑ i, (((⌈x i⌉ : ℤ) - 1 : ℤ) : ℝ) • Pi.single i (1:ℝ)

lemma periodicRep_apply {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    periodicRep x i = x i - (((⌈x i⌉ : ℤ) - 1 : ℤ) : ℝ) := by
  rw [periodicRep, Pi.sub_apply]
  congr 1
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma periodicRep_mem {n : ℕ} (x : Fin n → ℝ) : ∀ i, periodicRep x i ∈ Set.Icc (0:ℝ) 1 := by
  intro i
  rw [periodicRep_apply]
  push_cast
  constructor
  · have h := Int.ceil_lt_add_one (x i); linarith
  · have h := Int.le_ceil (x i); linarith

/-- A periodic function takes the same value at `x` and at `periodicRep x`. -/
lemma Periodic1.apply_periodicRep {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β} (hf : Periodic1 f)
    (x : Fin n → ℝ) : f (periodicRep x) = f x := by
  have hx : periodicRep x + ∑ i, (((⌈x i⌉ : ℤ) - 1 : ℤ) : ℝ) • Pi.single i (1:ℝ) = x := by
    rw [periodicRep]; abel
  have hsum := periodic1_sum hf (fun i => (⌈x i⌉ : ℤ) - 1) (periodicRep x)
  rw [hx] at hsum
  exact hsum.symm

/-! ## Periodicity bookkeeping -/

lemma Periodic1.entry {n : ℕ} {f : Torus n} (hf : Periodic1 f) (i j : Fin n) :
    Periodic1 (fun x => f x i j) := fun k x => by
  have h := hf k x
  exact congrFun (congrFun h i) j

lemma PeriodicIn.reMat_entry {n : ℕ} {f : Torus n} (i : Fin n) (hf : PeriodicIn i f)
    (a b : Fin n) : PeriodicIn i (fun x => reMat (f x) a b) := fun x => by
  have h := hf x
  simp only [reMat_apply]
  rw [show f (x + Pi.single i 1) a b = f x a b from congrFun (congrFun h a) b]

lemma PeriodicIn.matrixInv_entry {n : ℕ} {i : Fin n}
    {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hA : PeriodicIn i A) (a b : Fin n) :
    PeriodicIn i (fun x => (A x)⁻¹ a b) := fun x => by
  have h := hA x
  show (A (x + Pi.single i 1))⁻¹ a b = (A x)⁻¹ a b
  rw [h]

lemma Periodic1.matrixInv_entry {n : ℕ} {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hA : Periodic1 A) (a b : Fin n) : Periodic1 (fun x => (A x)⁻¹ a b) :=
  fun i => PeriodicIn.matrixInv_entry (hA i) a b

/-! ## Smoothness of the determinant and of the inverse of a matrix function -/

/-- The determinant of a jointly smooth matrix function is jointly smooth. -/
lemma contDiffOn_det {n : ℕ} {T : ℝ} {M : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => M p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => (M p.1 p.2).det)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  have h : (fun p : ℝ × (Fin n → ℝ) => (M p.1 p.2).det)
      = fun p => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ∏ i : Fin n, M p.1 p.2 (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [h]
  refine ContDiffOn.sum (fun σ _ => ?_)
  exact ContDiffOn.mul contDiffOn_const (contDiffOn_prod (fun i _ => hM (σ i) i))

/-- The entries of the adjugate of a jointly smooth matrix function are jointly smooth. -/
lemma contDiffOn_adjugate_entry {n : ℕ} {T : ℝ}
    {M : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => M p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ)) (c d : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => (M p.1 p.2).adjugate c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  have hfun : (fun p : ℝ × (Fin n → ℝ) => (M p.1 p.2).adjugate c d)
      = fun p => ((M p.1 p.2).updateRow d (Pi.single c 1)).det := by
    funext p; exact Matrix.adjugate_apply (M p.1 p.2) c d
  rw [hfun]
  have h : (fun p : ℝ × (Fin n → ℝ) => ((M p.1 p.2).updateRow d (Pi.single c 1)).det)
      = fun p => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
          ∏ i : Fin n, (M p.1 p.2).updateRow d (Pi.single c 1) (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [h]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine ContDiffOn.mul contDiffOn_const (contDiffOn_prod (fun i _ => ?_))
  by_cases hid : σ i = d
  · have h1 : (fun p : ℝ × (Fin n → ℝ) =>
        (M p.1 p.2).updateRow d (Pi.single c 1) (σ i) i)
        = fun _ => (Pi.single c 1 : Fin n → ℝ) i := by
      funext p; rw [Matrix.updateRow_apply]; simp [hid]
    rw [h1]; exact contDiffOn_const
  · have h1 : (fun p : ℝ × (Fin n → ℝ) =>
        (M p.1 p.2).updateRow d (Pi.single c 1) (σ i) i)
        = fun p => M p.1 p.2 (σ i) i := by
      funext p; rw [Matrix.updateRow_apply]; simp [hid]
    rw [h1]; exact hM (σ i) i

/-- The entries of the inverse of a jointly smooth matrix function are jointly smooth, away from
the set where the determinant vanishes. -/
lemma contDiffOn_matrixInv_entry {n : ℕ} {T : ℝ}
    {M : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => M p.1 p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (M t x).det ≠ 0) (c d : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => ((M p.1 p.2)⁻¹) c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
  have h : (fun p : ℝ × (Fin n → ℝ) => ((M p.1 p.2)⁻¹) c d)
      = fun p => Ring.inverse (M p.1 p.2).det * (M p.1 p.2).adjugate c d := by
    funext p; rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  rw [h]
  refine ContDiffOn.mul ?_ (contDiffOn_adjugate_entry hM c d)
  intro p hp
  obtain ⟨t,x⟩ := p
  have hd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (Fin n → ℝ) => (M q.1 q.2).det) (Set.Ico (0:ℝ) T ×ˢ Set.univ) (t,x) :=
    contDiffOn_det hM (t,x) hp
  have hne : (M t x).det ≠ 0 := hdet t hp.1 x
  have hthis : (fun q : ℝ × (Fin n → ℝ) => Ring.inverse (M q.1 q.2).det)
      = fun q => ((fun q : ℝ × (Fin n → ℝ) => (M q.1 q.2).det) q)⁻¹ := by
    funext q; rw [Ring.inverse_eq_inv]
  rw [hthis]
  exact (contDiffAt_inv ℝ hne).comp_contDiffWithinAt (t,x) hd

/-! ## The residual of the linearization -/

/-- A real matrix satisfying a strict quadratic-form lower bound is invertible. -/
lemma det_ne_zero_of_quadratic {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, B i j * ξ i * ξ j) : B.det ≠ 0 := by
  intro hdet
  have hker : (Matrix.toLin' B).ker ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
    exact hdet
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hBv : Matrix.mulVec B v = 0 := by
    have h' := hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at h'
    exact h'
  have hvsum : 0 < ∑ i, (v i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact sq_pos_of_ne_zero hi
  have h2 := h v
  have hzero : ∑ i, ∑ j, B i j * v i * v j = 0 := by
    have h1 : ∀ i, ∑ j, B i j * v i * v j = v i * (Matrix.mulVec B v) i := by
      intro i
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), hBv]
    simp
  rw [hzero] at h2
  nlinarith

/-- Continuity of `w ↦ (reMat w.1).det`. -/
lemma continuous_det_reMat {n : ℕ} :
    Continuous fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det := by
  have h : (fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det)
      = fun w : MatC n × (Fin n → MatC n) =>
          ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) *
          ∏ i : Fin n, (w.1 (σ i) i).re := by
    funext w; rw [Matrix.det_apply']; rfl
  rw [h]
  refine continuous_finsetSum _ (fun σ _ => Continuous.mul continuous_const ?_)
  refine continuous_finsetProd _ (fun i _ => ?_)
  exact Complex.continuous_re.comp
    ((continuous_apply i).comp ((continuous_apply (σ i)).comp continuous_fst))

/-- `secOpFlat` is additive in its second argument. -/
lemma secOpFlat_sub {n : ℕ} (A : MatC n) (B B' : Fin n → Fin n → MatC n) :
    secOpFlat A (B - B') = secOpFlat A B - secOpFlat A B' := by
  funext i j
  simp only [secOpFlat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `reMat` is real-linear. -/
lemma reMat_smul_add {n : ℕ} (a b : ℝ) (A B : MatC n) :
    reMat (a • A + b • B) = a • reMat A + b • reMat B := by
  ext i j
  simp only [reMat_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
    Matrix.smul_apply]
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- The difference of two inverses. -/
lemma inv_sub_inv_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_assoc, Matrix.mul_nonsing_inv B hB,
    Matrix.nonsing_inv_mul A hA, mul_one, one_mul]

/-- The norm of a real number viewed as a complex number. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- A constant double sum. -/
lemma sum_sum_const {n : ℕ} (X : ℝ) :
    (∑ _ : Fin n, ∑ _ : Fin n, X) = (n : ℝ) * ((n : ℝ) * X) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Entrywise bound for the difference of two inverses. -/
lemma inv_sub_inv_entry_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) {K₁ K₂ K₃ : ℝ} (hK₁ : ∀ i j, ‖A⁻¹ i j‖ ≤ K₁)
    (hK₂ : ∀ i j, ‖B⁻¹ i j‖ ≤ K₂) (hK₃ : ∀ i j, ‖B i j - A i j‖ ≤ K₃) (c d : Fin n) :
    ‖(A⁻¹ - B⁻¹) c d‖ ≤ (n : ℝ) ^ 2 * |K₁ * K₂ * K₃| := by
  rw [inv_sub_inv_eq A B hA hB, Matrix.mul_apply]
  calc ‖∑ p, (A⁻¹ * (B - A)) c p * B⁻¹ p d‖
      ≤ ∑ p, ‖(A⁻¹ * (B - A)) c p * B⁻¹ p d‖ := norm_sum_le _ _
    _ = ∑ p, ‖(∑ q, A⁻¹ c q * (B - A) q p) * B⁻¹ p d‖ := by
        refine Finset.sum_congr rfl (fun p _ => ?_); rw [Matrix.mul_apply]
    _ = ∑ p, ‖∑ q, A⁻¹ c q * (B - A) q p * B⁻¹ p d‖ := by
        refine Finset.sum_congr rfl (fun p _ => ?_); rw [Finset.sum_mul]
    _ ≤ ∑ p, ∑ q, ‖A⁻¹ c q * (B - A) q p * B⁻¹ p d‖ :=
        Finset.sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p, ∑ q, |K₁ * K₂ * K₃| := by
        refine Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => ?_))
        have h3 : ‖(B - A) q p‖ ≤ K₃ := by simpa [Matrix.sub_apply] using hK₃ q p
        have h1 : ‖A⁻¹ c q‖ ≤ |K₁| := (hK₁ c q).trans (le_abs_self _)
        have h2 : ‖B⁻¹ p d‖ ≤ |K₂| := (hK₂ p d).trans (le_abs_self _)
        have h3' : ‖(B - A) q p‖ ≤ |K₃| := h3.trans (le_abs_self _)
        rw [norm_mul, norm_mul]
        calc ‖A⁻¹ c q‖ * ‖(B - A) q p‖ * ‖B⁻¹ p d‖ ≤ |K₁| * |K₃| * |K₂| :=
              mul_le_mul (mul_le_mul h1 h3' (norm_nonneg _) (abs_nonneg _)) h2 (norm_nonneg _)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = |K₁ * K₂ * K₃| := by rw [abs_mul, abs_mul]; ring
    _ = (n : ℝ) ^ 2 * |K₁ * K₂ * K₃| := by
        rw [sum_sum_const]; ring

/-- **The residual of the linearization is Lipschitz.**  For DeTurck-shaped `Φ`, on the compact
set of jets whose metric matrix is positive definite, uniformly elliptic with constant `lam` and
has bounded entries (as do its inverse, the first and the second jet), the residual
`Φ (x,J₁) - Φ (x,J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)` is Lipschitz in the directions
`J₁.1 - J₂.1` and `J₁.2.1 - J₂.2.1` only. -/
theorem nDiff_bound {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Jet n → MatC n) (hshape : IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (0:ℝ) 1) →
      ∀ (J₁ J₂ : Jet n),
      PosDefM J₁.1 → PosDefM J₂.1 →
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat J₁.1 i j * ξ i * ξ j) →
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat J₂.1 i j * ξ i * ξ j) →
      (∀ i j, ‖J₁.1 i j‖ ≤ M) → (∀ i j, ‖J₂.1 i j‖ ≤ M) →
      (∀ i j, ‖((reMat J₁.1)⁻¹) i j‖ ≤ M) → (∀ i j, ‖((reMat J₂.1)⁻¹) i j‖ ≤ M) →
      (∀ c i j, ‖J₁.2.1 c i j‖ ≤ M) → (∀ c i j, ‖J₂.2.1 c i j‖ ≤ M) →
      (∀ c d i j, ‖J₁.2.2 c d i j‖ ≤ M) → (∀ c d i j, ‖J₂.2.2 c d i j‖ ≤ M) →
      ‖Φ (x, J₁) - Φ (x, J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)‖
        ≤ C * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) := by
  obtain ⟨hΦsm, N, hNsm, hNshape, _hNper⟩ := hshape
  -- the admissible (convex, compact) set of values
  set s : Set (MatC n × (Fin n → MatC n)) :=
    {w | (∀ i j, ‖w.1 i j‖ ≤ M) ∧
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j) ∧
      (∀ c i j, ‖w.2 c i j‖ ≤ M)} with hsdef
  have hs_dom : s ⊆ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} :=
    fun w hw => det_ne_zero_of_quadratic hlam hw.2.1
  have hs_conv : Convex ℝ s := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    obtain ⟨hA₁, hE₁, hL₁⟩ := hw₁
    obtain ⟨hA₂, hE₂, hL₂⟩ := hw₂
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hw : (a • w₁ + b • w₂).1 i j = a • w₁.1 i j + b • w₂.1 i j := rfl
      rw [hw]
      calc ‖a • w₁.1 i j + b • w₂.1 i j‖ ≤ ‖a • w₁.1 i j‖ + ‖b • w₂.1 i j‖ := norm_add_le _ _
        _ = a * ‖w₁.1 i j‖ + b * ‖w₂.1 i j‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left (hA₁ i j) ha)
            (mul_le_mul_of_nonneg_left (hA₂ i j) hb)
        _ = M := by rw [← add_mul, hab, one_mul]
    · intro ξ
      have hre : reMat (a • w₁ + b • w₂).1 = a • reMat w₁.1 + b • reMat w₂.1 := by
        have h1 : (a • w₁ + b • w₂).1 = a • w₁.1 + b • w₂.1 := rfl
        rw [h1, reMat_smul_add]
      rw [hre]
      have hsplit : ∑ i, ∑ j, (a * reMat w₁.1 i j + b * reMat w₂.1 i j) * ξ i * ξ j
          = a * (∑ i, ∑ j, reMat w₁.1 i j * ξ i * ξ j)
            + b * (∑ i, ∑ j, reMat w₂.1 i j * ξ i * ξ j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hsplit]
      have h3 : a * (lam * ∑ i, (ξ i) ^ 2)
          ≤ a * (∑ i, ∑ j, reMat w₁.1 i j * ξ i * ξ j) := mul_le_mul_of_nonneg_left (hE₁ ξ) ha
      have h4 : b * (lam * ∑ i, (ξ i) ^ 2)
          ≤ b * (∑ i, ∑ j, reMat w₂.1 i j * ξ i * ξ j) := mul_le_mul_of_nonneg_left (hE₂ ξ) hb
      have h5 : a * (lam * ∑ i, (ξ i) ^ 2) + b * (lam * ∑ i, (ξ i) ^ 2)
          = lam * ∑ i, (ξ i) ^ 2 := by rw [← add_mul, hab, one_mul]
      linarith
    · intro c i j
      have hw : (a • w₁ + b • w₂).2 c i j = a • w₁.2 c i j + b • w₂.2 c i j := rfl
      rw [hw]
      calc ‖a • w₁.2 c i j + b • w₂.2 c i j‖ ≤ ‖a • w₁.2 c i j‖ + ‖b • w₂.2 c i j‖ :=
            norm_add_le _ _
        _ = a * ‖w₁.2 c i j‖ + b * ‖w₂.2 c i j‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * M + b * M := add_le_add (mul_le_mul_of_nonneg_left (hL₁ c i j) ha)
            (mul_le_mul_of_nonneg_left (hL₂ c i j) hb)
        _ = M := by rw [← add_mul, hab, one_mul]
  have hs_sub : s ⊆ Metric.closedBall (0 : MatC n × (Fin n → MatC n)) M := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    refine max_le ?_ ?_
    · rw [pi_norm_le_iff_of_nonneg hM]
      intro i
      rw [pi_norm_le_iff_of_nonneg hM]
      exact hw.1 i
    · rw [pi_norm_le_iff_of_nonneg hM]
      intro c
      rw [pi_norm_le_iff_of_nonneg hM]
      intro i
      rw [pi_norm_le_iff_of_nonneg hM]
      exact hw.2.2 c i
  have hs_closed : IsClosed s := by
    have h1 : IsClosed {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M} := by
      rw [show {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M}
          = ⋂ (i : Fin n), ⋂ (j : Fin n), {w | ‖w.1 i j‖ ≤ M} by ext w; simp]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (by fun_prop) continuous_const
    have h2 : IsClosed {w : MatC n × (Fin n → MatC n) |
        ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j} := by
      rw [show {w : MatC n × (Fin n → MatC n) |
          ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j}
          = ⋂ (ξ : Fin n → ℝ), {w | lam * ∑ i, (ξ i) ^ 2 ≤
              ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j} by ext w; simp]
      refine isClosed_iInter fun ξ => isClosed_le continuous_const ?_
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      have h1 : Continuous (fun w : MatC n × (Fin n → MatC n) => reMat w.1 i j) :=
        Complex.continuous_re.comp
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
      exact (h1.mul continuous_const).mul continuous_const
    have h3 : IsClosed {w : MatC n × (Fin n → MatC n) | ∀ c i j, ‖w.2 c i j‖ ≤ M} := by
      rw [show {w : MatC n × (Fin n → MatC n) | ∀ c i j, ‖w.2 c i j‖ ≤ M}
          = ⋂ (c : Fin n), ⋂ (i : Fin n), ⋂ (j : Fin n), {w | ‖w.2 c i j‖ ≤ M} by ext w; simp]
      exact isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (by fun_prop) continuous_const
    have hs_eq : s = {w : MatC n × (Fin n → MatC n) | ∀ i j, ‖w.1 i j‖ ≤ M} ∩
        {w | ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat w.1 i j * ξ i * ξ j} ∩
        {w | ∀ c i j, ‖w.2 c i j‖ ≤ M} := by
      ext w; simp [hsdef, and_assoc]
    rw [hs_eq]
    exact (h1.inter h2).inter h3
  have hs_compact : IsCompact s :=
    (isCompact_closedBall (0 : MatC n × (Fin n → MatC n)) M).of_isClosed_subset hs_closed hs_sub
  -- the domain is open
  have hOpen : IsOpen ((Set.univ : Set (Fin n → ℝ)) ×ˢ
      {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) := by
    refine isOpen_univ.prod ?_
    simpa using isOpen_ne.preimage continuous_det_reMat
  have hcont : ContinuousOn (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) =>
      fderiv ℝ N p) (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) :=
    hNsm.continuousOn_fderiv_of_isOpen hOpen (by simp)
  have hKsub : (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) ×ˢ s ⊆
      (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) :=
    fun p hp => ⟨trivial, hs_dom hp.2⟩
  obtain ⟨CN₀, hCN₀⟩ :=
    (((isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).prod hs_compact).exists_bound_of_continuousOn
      (hcont.mono hKsub))
  set CN : ℝ := max CN₀ 0 with hCNdef
  have hCNnn : 0 ≤ CN := le_max_right _ _
  have hCN : ∀ p ∈ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) ×ˢ s,
      ‖fderiv ℝ N p‖ ≤ CN := fun p hp => (hCN₀ p hp).trans (le_max_left _ _)
  refine ⟨(n : ℝ) ^ 4 * M ^ 3 + CN,
    by nlinarith [hCNnn, show (0:ℝ) ≤ (n : ℝ) ^ 4 * M ^ 3 by positivity], ?_⟩
  intro x hx J₁ J₂ hpd₁ hpd₂ hell₁ hell₂ hA₁ hA₂ hI₁ hI₂ hL₁ hL₂ hB₁ hB₂
  have hxmem : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) := fun i _ => hx i
  have hdet₁ : (reMat J₁.1).det ≠ 0 := (Matrix.PosDef.det_pos hpd₁).ne'
  have hdet₂ : (reMat J₂.1).det ≠ 0 := (Matrix.PosDef.det_pos hpd₂).ne'
  have hΦ₁ := hNshape x J₁.1 J₁.2.1 J₁.2.2 hdet₁
  have hΦ₂ := hNshape x J₂.1 J₂.2.1 J₂.2.2 hdet₂
  -- the algebraic decomposition of the residual
  have hdecomp : Φ (x, J₁) - Φ (x, J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)
      = (secOpFlat J₁.1 J₂.2.2 - secOpFlat J₂.1 J₂.2.2)
        + (N (x, (J₁.1, J₁.2.1)) - N (x, (J₂.1, J₂.2.1))) := by
    rw [hΦ₁, hΦ₂, secOpFlat_sub J₁.1 J₁.2.2 J₂.2.2]
    abel
  -- bound on the linear part
  have hlin : ‖secOpFlat J₁.1 J₂.2.2 - secOpFlat J₂.1 J₂.2.2‖
      ≤ (n : ℝ) ^ 4 * M ^ 3 * ‖J₁.1 - J₂.1‖ := by
    have hrepr : secOpFlat J₁.1 J₂.2.2 - secOpFlat J₂.1 J₂.2.2
        = ∑ c, ∑ d, (((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ) • (J₂.2.2 c d) := by
      funext i j
      simp only [secOpFlat, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [← sub_mul]
      congr 1
      simp [Matrix.sub_apply]
    -- entrywise bound for the difference of inverses
    have hQ : ∀ c d : Fin n, ‖(((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ)‖
        ≤ (n : ℝ) ^ 2 * M ^ 2 * ‖J₁.1 - J₂.1‖ := by
      intro c d
      have h3 : ∀ i j : Fin n, ‖(reMat J₂.1) i j - (reMat J₁.1) i j‖ ≤ ‖J₁.1 - J₂.1‖ := by
        intro i j
        have h4 : (reMat J₂.1) i j - (reMat J₁.1) i j = ((J₂.1 - J₁.1) i j).re := by
          simp [reMat_apply, Pi.sub_apply, Complex.sub_re]
        rw [h4]
        have h5 : ‖(J₂.1 - J₁.1) i j‖ ≤ ‖J₁.1 - J₂.1‖ := by
          have h6 : J₂.1 - J₁.1 = -(J₁.1 - J₂.1) := by abel
          rw [h6, Pi.neg_apply, Pi.neg_apply, norm_neg]
          exact le_trans (norm_le_pi_norm ((J₁.1 - J₂.1) i) j) (norm_le_pi_norm (J₁.1 - J₂.1) i)
        exact (Complex.abs_re_le_norm _).trans h5
      have h := inv_sub_inv_entry_le (reMat J₁.1) (reMat J₂.1)
        ((Matrix.isUnit_iff_isUnit_det (reMat J₁.1)).mp (Matrix.PosDef.isUnit hpd₁))
        ((Matrix.isUnit_iff_isUnit_det (reMat J₂.1)).mp (Matrix.PosDef.isUnit hpd₂))
        (K₁ := M) (K₂ := M) (K₃ := ‖J₁.1 - J₂.1‖) hI₁ hI₂ h3 c d
      have h2 : ‖(((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ)‖
          = ‖((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d‖ := by
        have hh : (((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ)
            = (((reMat J₁.1)⁻¹ c d : ℝ) : ℂ) - (((reMat J₂.1)⁻¹ c d : ℝ) : ℂ) := by
          rw [Matrix.sub_apply]; push_cast; ring
        rw [hh, show (↑((reMat J₁.1)⁻¹ c d) - ↑((reMat J₂.1)⁻¹ c d) : ℂ)
            = (((reMat J₁.1)⁻¹ c d - (reMat J₂.1)⁻¹ c d : ℝ) : ℂ) by push_cast; ring,
          norm_ofReal_complex, Real.norm_eq_abs, Matrix.sub_apply]
      rw [h2]
      refine h.trans (le_of_eq ?_)
      rw [abs_of_nonneg (by positivity)]
      ring
    have hentry : ∀ c d : Fin n,
        ‖(((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ) • (J₂.2.2 c d)‖
          ≤ ((n : ℝ) ^ 2 * M ^ 2 * ‖J₁.1 - J₂.1‖) * M := by
      intro c d
      have hBcd : ‖J₂.2.2 c d‖ ≤ M := by
        rw [pi_norm_le_iff_of_nonneg hM]
        intro i
        rw [pi_norm_le_iff_of_nonneg hM]
        exact hB₂ c d i
      rw [norm_smul]
      exact mul_le_mul (hQ c d) hBcd (norm_nonneg _) (by positivity)
    rw [hrepr]
    calc ‖∑ c, ∑ d, (((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ) • (J₂.2.2 c d)‖
        ≤ ∑ c, ‖∑ d, (((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ) • (J₂.2.2 c d)‖ :=
          norm_sum_le Finset.univ _
      _ ≤ ∑ c, ∑ d, ‖(((reMat J₁.1)⁻¹ - (reMat J₂.1)⁻¹) c d : ℂ) • (J₂.2.2 c d)‖ :=
          Finset.sum_le_sum (fun c _ => norm_sum_le Finset.univ _)
      _ ≤ ∑ c, ∑ d, ((n : ℝ) ^ 2 * M ^ 2 * ‖J₁.1 - J₂.1‖) * M :=
          Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => hentry c d))
      _ = (n : ℝ) ^ 4 * M ^ 3 * ‖J₁.1 - J₂.1‖ := by
          rw [sum_sum_const]; ring
  -- the MVT bound for the `N`-part
  have hNbd : ‖N (x, (J₁.1, J₁.2.1)) - N (x, (J₂.1, J₂.2.1))‖
      ≤ CN * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) := by
    have hw₁ : (J₁.1, J₁.2.1) ∈ s := ⟨hA₁, hell₁, hL₁⟩
    have hw₂ : (J₂.1, J₂.2.1) ∈ s := ⟨hA₂, hell₂, hL₂⟩
    have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (C := CN) (f := fun w : MatC n × (Fin n → MatC n) => N (x, w))
      (f' := fun w => (fderiv ℝ N (x, w)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (MatC n × (Fin n → MatC n))))
      (fun w hw => ?_) (fun w hw => ?_) hs_conv hw₂ hw₁
    · refine hmvt.trans ?_
      rw [Prod.norm_def]
      have h1 : max ‖J₁.1 - J₂.1‖ ‖J₁.2.1 - J₂.2.1‖ ≤ ‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖ :=
        max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left h1 (le_trans (norm_nonneg _) (hCN (x, (J₂.1, J₂.2.1))
        ⟨hxmem, hw₂⟩))
    · -- the within-derivative
      have hmem : (x, w) ∈ Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} :=
        ⟨trivial, hs_dom hw⟩
      have hN : HasFDerivWithinAt N (fderiv ℝ N (x, w))
          (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) (x, w) :=
        (((hNsm.contDiffAt (hOpen.mem_nhds hmem)).differentiableAt (by simp)).hasFDerivAt).hasFDerivWithinAt
      have hinr : HasFDerivAt (fun w' : MatC n × (Fin n → MatC n) => (x, w'))
          (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (MatC n × (Fin n → MatC n))) w :=
        hasFDerivAt_prodMk_right x w
      have hmem' : ∀ᶠ w' in nhds w, (x, w') ∈
          (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) := by
        refine Filter.mem_of_superset
          ((isOpen_ne.preimage continuous_det_reMat).mem_nhds (hs_dom hw)) (fun w' hw' => ?_)
        exact ⟨trivial, hw'⟩
      exact (hN.comp_hasFDerivAt w hinr hmem').hasFDerivWithinAt
    · -- the derivative bound
      have hb := hCN (x, w) ⟨hxmem, hw⟩
      have hinr : ‖ContinuousLinearMap.inr ℝ (Fin n → ℝ) (MatC n × (Fin n → MatC n))‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
        simp [ContinuousLinearMap.inr_apply, Prod.norm_def]
      calc ‖(fderiv ℝ N (x, w)).comp
            (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (MatC n × (Fin n → MatC n)))‖
          ≤ ‖fderiv ℝ N (x, w)‖ * ‖ContinuousLinearMap.inr ℝ (Fin n → ℝ)
              (MatC n × (Fin n → MatC n))‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ CN * 1 := mul_le_mul hb hinr (norm_nonneg _) hCNnn
        _ = CN := mul_one CN
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  calc ‖secOpFlat J₁.1 J₂.2.2 - secOpFlat J₂.1 J₂.2.2‖
        + ‖N (x, (J₁.1, J₁.2.1)) - N (x, (J₂.1, J₂.2.1))‖
      ≤ (n : ℝ) ^ 4 * M ^ 3 * ‖J₁.1 - J₂.1‖
        + CN * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) := add_le_add hlin hNbd
    _ ≤ ((n : ℝ) ^ 4 * M ^ 3 + CN) * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) := by
        have h1 : (n : ℝ) ^ 4 * M ^ 3 * ‖J₁.1 - J₂.1‖
            ≤ (n : ℝ) ^ 4 * M ^ 3 * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) (by positivity)
        have h2 : CN * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖)
            ≤ ((n : ℝ) ^ 4 * M ^ 3 + CN) * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)
        linarith

/-! ## Differentiation of the `L²` energy -/

lemma ofReal_normSq_eq_mul_star' (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The pointwise derivative of `s ↦ ‖f s‖ ^ 2`. -/
lemma hasDerivAt_normsq {f : ℝ → ℂ} {z' : ℂ} {t : ℝ} (h : HasDerivAt f z' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * (z' * star (f t)).re) t := by
  have hmul : HasDerivAt (fun s => f s * star (f s)) (z' * star (f t) + f t * star z') t :=
    h.mul h.star
  have hre : HasDerivAt (fun s => Complex.reCLM (f s * star (f s)))
      (Complex.reCLM (z' * star (f t) + f t * star z')) t :=
    (Complex.reCLM.hasFDerivAt (x := f t * star (f t))).comp_hasDerivAt t hmul
  have hfun : (fun s => Complex.reCLM (f s * star (f s))) = fun s => ‖f s‖ ^ 2 := by
    funext s
    rw [Complex.reCLM_apply, ← ofReal_normSq_eq_mul_star', Complex.ofReal_re]
  rw [hfun] at hre
  refine hre.congr_deriv ?_
  have hstar : f t * star z' = star (z' * star (f t)) := by
    rw [star_mul, star_star, mul_comm]
  rw [hstar, Complex.reCLM_apply, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- **Derivative of the `L²` energy.**  If `W` is jointly continuous on `Ico 0 T × univ`, `W'`
likewise, and `W'` is the time derivative of `W`, then the energy `s ↦ ∫ ‖W s x‖ ^ 2` is
differentiable at every interior time with the expected derivative. -/
theorem hasDerivAt_integral_normSq_slice {n : ℕ} (hn : 1 ≤ n)
    (W W' : ℝ → (Fin n → ℝ) → ℂ) (T : ℝ)
    (hW : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => W p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hW' : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => W' p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (hd : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x,
      HasDerivWithinAt (fun s => W s x) (W' t x) (Set.Ico (0:ℝ) T) t)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) T) :
    HasDerivAt (fun s => ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖W s x‖ ^ 2)
      (2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n), (W' t x * star (W t x)).re) t := by
  set δ : ℝ := min (t / 2) ((T - t) / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith [ht.1]) (by linarith [ht.2])
  have hδle : δ ≤ t / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδle' : δ ≤ (T - t) / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hlo : 0 < t - δ := by linarith
  have hhi : t + δ < T := by linarith
  set s : Set ℝ := Set.Ioo (t - δ) (t + δ) with hsdef
  have hs_mem : s ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith [hδpos], by linarith [hδpos]⟩
  have hs_Ioo : ∀ x ∈ s, x ∈ Set.Ioo (t - δ) (t + δ) := fun x hx => hx
  have hs_sub : s ⊆ Set.Ico (0:ℝ) T :=
    fun x hx => ⟨by linarith [(hs_Ioo x hx).1, hlo], by linarith [(hs_Ioo x hx).2, hhi]⟩
  have hs_Icc : ∀ x ∈ s, x ∈ Set.Icc (t - δ) (t + δ) :=
    fun x hx => ⟨le_of_lt (hs_Ioo x hx).1, le_of_lt (hs_Ioo x hx).2⟩
  have hIcc_sub : Set.Icc (t - δ) (t + δ) ⊆ Set.Ico (0:ℝ) T :=
    fun x hx => ⟨by linarith [hx.1, hlo], by linarith [hx.2, hhi]⟩
  -- the compact set of times and cubes
  have hKcompact : IsCompact (Set.Icc (t - δ) (t + δ) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : Set.Icc (t - δ) (t + δ) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))
      ⊆ Set.Ico (0:ℝ) T ×ˢ Set.univ :=
    fun p hp => ⟨hIcc_sub hp.1, Set.mem_univ _⟩
  obtain ⟨CW, hCW⟩ := hKcompact.exists_bound_of_continuousOn (hW.mono hKsub)
  obtain ⟨CW', hCW'⟩ := hKcompact.exists_bound_of_continuousOn (hW'.mono hKsub)
  set C : ℝ := |2 * CW * CW'| with hCdef
  have hCnn : 0 ≤ C := abs_nonneg _
  -- slices are continuous
  have hsliceW : ∀ x ∈ Set.Ioo (0:ℝ) T, Continuous (fun y : Fin n → ℝ => W x y) := by
    intro x hx
    have h2 := hW.comp (s := Set.univ) (t := Set.Ico (0:ℝ) T ×ˢ Set.univ)
      (g := fun p : ℝ × (Fin n → ℝ) => W p.1 p.2)
      (f := fun y : Fin n → ℝ => (x, y))
      (continuousOn_const.prodMk continuousOn_id)
      (fun y _ => ⟨⟨le_of_lt hx.1, hx.2⟩, Set.mem_univ y⟩)
    have h3 : ((fun p : ℝ × (Fin n → ℝ) => W p.1 p.2) ∘ fun y : Fin n → ℝ => (x, y))
        = fun y => W x y := rfl
    rw [h3, continuousOn_univ] at h2
    exact h2
  have hsliceW' : ∀ x ∈ Set.Ioo (0:ℝ) T, Continuous (fun y : Fin n → ℝ => W' x y) := by
    intro x hx
    have h2 := hW'.comp (s := Set.univ) (t := Set.Ico (0:ℝ) T ×ˢ Set.univ)
      (g := fun p : ℝ × (Fin n → ℝ) => W' p.1 p.2)
      (f := fun y : Fin n → ℝ => (x, y))
      (continuousOn_const.prodMk continuousOn_id)
      (fun y _ => ⟨⟨le_of_lt hx.1, hx.2⟩, Set.mem_univ y⟩)
    have h3 : ((fun p : ℝ × (Fin n → ℝ) => W' p.1 p.2) ∘ fun y : Fin n → ℝ => (x, y))
        = fun y => W' x y := rfl
    rw [h3, continuousOn_univ] at h2
    exact h2
  have hcube_sub : Work.Diff.STE.unitCube (ι := Fin n) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) :=
    fun x hx i hi => ⟨le_of_lt (hx i hi).1, (hx i hi).2⟩
  -- the domination bound
  have hbdd : ∀ᵐ a ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))),
      ∀ x ∈ s, ‖2 * (W' x a * star (W x a)).re‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ioc))] with a ha x hx
    have hxIcc : x ∈ Set.Icc (t - δ) (t + δ) := hs_Icc x hx
    have haIcc : a ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) := hcube_sub ha
    have h1 : ‖W x a‖ ≤ CW := hCW (x, a) ⟨hxIcc, haIcc⟩
    have h2 : ‖W' x a‖ ≤ CW' := hCW' (x, a) ⟨hxIcc, haIcc⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * |(W' x a * star (W x a)).re| ≤ 2 * ‖W' x a * star (W x a)‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
      _ = 2 * (‖W' x a‖ * ‖W x a‖) := by rw [norm_mul, norm_star]
      _ ≤ 2 * (CW' * CW) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h2 h1 (norm_nonneg _) ?_) (by norm_num)
          exact (norm_nonneg _).trans h2
      _ = 2 * CW * CW' := by ring
      _ ≤ C := by rw [hCdef]; exact le_abs_self _
  -- the pointwise derivative
  have hdiff : ∀ᵐ a ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))),
      ∀ x ∈ s, HasDerivAt (fun x : ℝ => ‖W x a‖ ^ 2) (2 * (W' x a * star (W x a)).re) x := by
    filter_upwards with a x hx
    have hxIoo : x ∈ Set.Ioo (0:ℝ) T :=
      ⟨by linarith [(hs_Ioo x hx).1, hlo], by linarith [(hs_Ioo x hx).2, hhi]⟩
    have hmem : Set.Ico (0:ℝ) T ∈ 𝓝 x :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxIoo) (fun y hy => ⟨hy.1.le, hy.2⟩)
    exact hasDerivAt_normsq ((hd x ⟨hxIoo.1.le, hxIoo.2⟩ a).hasDerivAt hmem)
  -- measurability and integrability
  have hF_meas : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (fun a : Fin n → ℝ => ‖W x a‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) := by
    refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun x hx => ?_)
    exact (((hsliceW x hx).norm.pow 2)).aestronglyMeasurable
  have hF'int_meas : AEStronglyMeasurable
      (fun a : Fin n → ℝ => 2 * (W' t a * star (W t a)).re)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) := by
    refine (Continuous.aestronglyMeasurable ?_)
    exact continuous_const.mul (Complex.continuous_re.comp ((hsliceW' t ht).mul (hsliceW t ht).star))
  have hF_int : Integrable (fun a : Fin n → ℝ => ‖W t a‖ ^ 2)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
    (ContinuousOn.integrableOn_compact (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
      ((hsliceW t ht).norm.pow 2).continuousOn).mono_set hcube_sub
  have hbdd_int : Integrable (fun _ : Fin n → ℝ => C)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) := integrable_const _
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (a : Fin n → ℝ) => ‖W x a‖ ^ 2)
    (F' := fun x (a : Fin n → ℝ) => 2 * (W' x a * star (W x a)).re)
    (bound := fun _ : Fin n → ℝ => C)
    hs_mem hF_meas hF_int hF'int_meas hbdd hbdd_int hdiff
  have hident : (∫ a, 2 * (W' t a * star (W t a)).re
        ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))))
      = 2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n), (W' t x * star (W t x)).re := by
    rw [MeasureTheory.integral_const_mul]
  rw [hident] at hderiv
  simpa using hderiv

/-! ## Parametric Gårding estimate -/

/-- The Gårding estimate for a *family* of coefficient matrices: the constant is uniform in the
parameter.  This is a copy of `Work.Diff.STE.garding_estimate` with a parameter `b`. -/
theorem garding_param {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*}
    (A : β → ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ b c d, ContDiff ℝ (⊤ : ℕ∞) (A b c d))
    (hAper : ∀ b c d, Work.Diff.STE.Periodic1 (A b c d))
    (hsym : ∀ b c d x, A b c d x = A b d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ b x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A b c d x * ξ c * ξ d)
    (K₁ : ℝ) (hK₁ : ∀ b c d i x, |Work.Diff.STE.pdR i (A b c d) x| ≤ K₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b (u : (ι → ℝ) → ℂ), ContDiff ℝ 2 u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.L2re (fun x => ∑ c, ∑ d, A b c d x *
          Work.Diff.STE.pd c (Work.Diff.STE.pd d u) x) u
        ≤ -((lam / 2) * ∑ i, ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pd i u x‖ ^ 2)
          + C * ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x‖ ^ 2 := by
  have hA1 : ∀ b c d, ContDiff ℝ 1 (A b c d) := fun b c d => (hA b c d).of_le (by simp)
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnn : 0 ≤ n := by rw [hn]; exact Nat.cast_nonneg _
  set K : ℝ := max K₁ 0 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK' : ∀ b c d i x, |Work.Diff.STE.pdR i (A b c d) x| ≤ K := by
    intro b c d i x; rw [hKdef]; exact le_trans (hK₁ b c d i x) (le_max_left _ _)
  set D : ℝ := K * n + 1 with hDdef
  have hD : 0 < D := by rw [hDdef]; nlinarith [hK, hnn]
  set ε : ℝ := lam / D with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hlam hD
  set C : ℝ := K * n ^ 2 * D / (2 * lam) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hK (sq_nonneg n)) (le_of_lt hD)) (by linarith)
  have ha_eq : K * n * ε / 2 = lam / 2 - lam / (2 * D) := by
    have hDne : D ≠ 0 := ne_of_gt hD
    rw [hεdef]
    field_simp
    ring
  have ha_le : K * n * ε / 2 ≤ lam / 2 := by
    rw [ha_eq]
    have h0 : 0 ≤ lam / (2 * D) := div_nonneg (le_of_lt hlam) (by linarith)
    linarith
  have hb_eq : K * n ^ 2 / (2 * ε) = C := by
    have hDne : D ≠ 0 := ne_of_gt hD
    have hlne : lam ≠ 0 := ne_of_gt hlam
    rw [hεdef, hCdef]
    field_simp
  have hb_le : K * n ^ 2 / (2 * ε) ≤ C := le_of_eq hb_eq
  refine ⟨C, hCnn, fun b u hu hup => ?_⟩
  have hop := Work.Diff.STE.ga_operator_identity (A b) (hA1 b) (fun c d => hAper b c d) u hu hup
  have hell := Work.Diff.STE.elliptic_lower (A b) (hA b) lam (fun x ξ => hpos b x ξ) u hu
  have hfo := Work.Diff.STE.ga_first_order_bound (A b) (hA1 b) K hK (hK' b) u hu ε hε
  set S : ℝ := ∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2 with hS
  set T : ℝ := ∫ x in unitCube, ‖u x‖ ^ 2 with hT
  set J1 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (pdR c (A b c d) x) * Complex.re (pd d u x * star (u x)) with hJ1
  set J2 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (A b c d x) * Complex.re (pd d u x * star (pd c u x)) with hJ2
  rw [← hn] at hfo
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => by positivity))
  have hTnn : 0 ≤ T := by
    rw [hT]; exact integral_nonneg (fun x => by positivity)
  have hJ1' : -(lam / 2) * S - C * T ≤ J1 := by
    have ha' : -(lam / 2) * S ≤ -(K * n * ε / 2) * S :=
      mul_le_mul_of_nonneg_right (neg_le_neg ha_le) hSnn
    have hb' : -C * T ≤ -(K * n ^ 2 / (2 * ε)) * T :=
      mul_le_mul_of_nonneg_right (neg_le_neg hb_le) hTnn
    linarith [hfo, ha', hb']
  rw [hop]
  linarith [hJ1', hell]

/-! ## Linearity of the partial derivatives -/

/-- The partial derivative of a smooth function on the torus is smooth. -/
lemma contDiff_pd {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (pd d f) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h3 := (ContinuousLinearMap.apply ℝ ℂ (Pi.single d (1:ℝ))).contDiff.comp h
  rw [show (⇑((ContinuousLinearMap.apply ℝ ℂ) (Pi.single d (1:ℝ))) ∘ fderiv ℝ f)
      = fun y : Fin n → ℝ => (fderiv ℝ f y) (Pi.single d (1:ℝ)) from by
    funext y; rfl] at h3
  exact h3

/-- The partial derivative is additive in the function. -/
lemma pd_sub_fun {n : ℕ} (c : Fin n) {f g : (Fin n → ℝ) → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    pd c (fun x => f x - g x) = fun x => pd c f x - pd c g x := by
  funext x
  have hsub : (fun x => f x - g x) = f - g := rfl
  simp only [pd]
  rw [hsub, fderiv_sub hf.differentiableAt hg.differentiableAt]
  rfl

/-- The iterated partial derivative is additive in the function. -/
lemma pd_pd_sub_fun {n : ℕ} (c d : Fin n) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    pd c (pd d (fun x => f x - g x)) = fun x => pd c (pd d f) x - pd c (pd d g) x := by
  have h1 := pd_sub_fun d (hf.differentiable (by simp)) (hg.differentiable (by simp))
  rw [h1]
  exact pd_sub_fun c ((contDiff_pd hf d).differentiable (by simp))
    ((contDiff_pd hg d).differentiable (by simp))



/-! ## Uniform bounds along a solution -/

/-- A periodic function bounded on the closed unit cube is bounded everywhere. -/
lemma abs_le_of_periodic1_of_cube {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Periodic1 f) {M : ℝ}
    (h : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1), |f x| ≤ M) :
    ∀ x, |f x| ≤ M := by
  intro x
  rw [← Periodic1.apply_periodicRep hf x]
  exact h (periodicRep x) (fun i _ => periodicRep_mem x i)

/-- A homogeneous quadratic form bounded below on the unit sphere is bounded below
everywhere. -/
lemma elliptic_sphere_hom {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hhom : ∀ (c : ℝ) (ξ : Fin n → ℝ), F (c • ξ) = c ^ 2 * F ξ)
    {lam : ℝ} (h : ∀ ξ : Fin n → ℝ, (∑ i, (ξ i) ^ 2 = 1) → lam ≤ F ξ) :
    ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ F ξ := by
  intro ξ
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i)) :
      0 ≤ ∑ i, (ξ i) ^ 2) with h0 | hpos
  · have hξ : ∀ i, ξ i = 0 := by
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ i))).mp h0.symm
      intro i
      exact pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp (h1 i (Finset.mem_univ i))
    have hF0 : F ξ = 0 := by
      have h2 := hhom 0 ξ
      simp only [zero_smul] at h2
      have h3 : F 0 = 0 := by simpa using h2
      rw [show ξ = 0 from funext hξ, h3]
    rw [hF0, ← h0]
    simp
  · set c : ℝ := (Real.sqrt (∑ i, (ξ i) ^ 2))⁻¹ with hcdef
    have hc2 : c ^ 2 = (∑ i, (ξ i) ^ 2)⁻¹ := by
      rw [hcdef, inv_pow, Real.sq_sqrt (le_of_lt hpos)]
    have hinv : (∑ i, (ξ i) ^ 2)⁻¹ * ∑ i, (ξ i) ^ 2 = 1 :=
      inv_mul_cancel₀ (ne_of_gt hpos)
    have hη : ∑ i, ((c • ξ) i) ^ 2 = 1 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ i, (c * ξ i) ^ 2) = c ^ 2 * ∑ i, (ξ i) ^ 2 from by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)]
      rw [hc2, hinv]
    have h1 := h (c • ξ) hη
    rw [hhom c ξ] at h1
    have h2 : c ^ 2 * ∑ i, (ξ i) ^ 2 = 1 := by rw [hc2, hinv]
    have h3 : lam * ∑ i, (ξ i) ^ 2 ≤ (c ^ 2 * F ξ) * ∑ i, (ξ i) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
    have h4 : (c ^ 2 * F ξ) * ∑ i, (ξ i) ^ 2 = F ξ := by
      calc (c ^ 2 * F ξ) * ∑ i, (ξ i) ^ 2 = F ξ * (c ^ 2 * ∑ i, (ξ i) ^ 2) := by ring
        _ = F ξ * 1 := by rw [h2]
        _ = F ξ := by ring
    linarith [h3, h4.le, h4.ge]

/-! ## Quadratic-form estimates -/

/-- A single term of a finite sum of nonnegative reals is at most the sum. -/
lemma single_le_sum_univ {ι : Type*} [Fintype ι] {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-- Every entry of a matrix is bounded by the sum of the norms of its entries. -/
lemma norm_entry_le_sum_matC {n : ℕ} (A : MatC n) (i j : Fin n) :
    ‖A i j‖ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖A a b‖ := by
  have h1 : ‖A i j‖ ≤ ∑ b : Fin n, ‖A i b‖ :=
    single_le_sum_univ (fun b => norm_nonneg (A i b)) j
  have h2 : (∑ b : Fin n, ‖A i b‖) ≤ ∑ a : Fin n, ∑ b : Fin n, ‖A a b‖ :=
    single_le_sum_univ (fun a => Finset.sum_nonneg (fun b _ => norm_nonneg _)) i
  linarith

/-- A single entry is bounded by the sum of the absolute values of a three-index family. -/
lemma abs_le_sum_three {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) (c d i : Fin n) :
    |f c d i| ≤ ∑ c' : Fin n, ∑ d' : Fin n, ∑ i' : Fin n, |f c' d' i'| := by
  have h1 : |f c d i| ≤ ∑ i' : Fin n, |f c d i'| :=
    single_le_sum_univ (fun i' => abs_nonneg (f c d i')) i
  have h2 : (∑ i' : Fin n, |f c d i'|) ≤ ∑ d' : Fin n, ∑ i' : Fin n, |f c d' i'| :=
    single_le_sum_univ (fun d' => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) d
  have h3 : (∑ d' : Fin n, ∑ i' : Fin n, |f c d' i'|)
      ≤ ∑ c' : Fin n, ∑ d' : Fin n, ∑ i' : Fin n, |f c' d' i'| :=
    single_le_sum_univ (fun c' => Finset.sum_nonneg (fun d' _ =>
      Finset.sum_nonneg (fun i' _ => abs_nonneg _))) c
  linarith

/-- The analogous bound for the first jet. -/
lemma norm_entry_le_sum_pdM {n : ℕ} (u : Torus n) (x : Fin n → ℝ) (c i j : Fin n) :
    ‖pdM c u x i j‖ ≤ ∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c' u x a b‖ := by
  have h1 : ‖pdM c u x i j‖ ≤ ∑ b : Fin n, ‖pdM c u x i b‖ :=
    single_le_sum_univ (fun b => norm_nonneg (pdM c u x i b)) j
  have h2 : (∑ b : Fin n, ‖pdM c u x i b‖) ≤ ∑ a : Fin n, ∑ b : Fin n, ‖pdM c u x a b‖ :=
    single_le_sum_univ (fun a => Finset.sum_nonneg (fun b _ => norm_nonneg _)) i
  have h3 : (∑ a : Fin n, ∑ b : Fin n, ‖pdM c u x a b‖)
      ≤ ∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c' u x a b‖ :=
    single_le_sum_univ (f := fun c' : Fin n => ∑ a : Fin n, ∑ b : Fin n, ‖pdM c' u x a b‖)
      (fun c' => Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
        Finset.sum_nonneg (s := Finset.univ) (fun b _ => norm_nonneg _))) c
  linarith

/-- The analogous bound for the second jet. -/
lemma norm_entry_le_sum_pdM2 {n : ℕ} (u : Torus n) (x : Fin n → ℝ) (c d i j : Fin n) :
    ‖pdM c (pdM d u) x i j‖ ≤
      ∑ c' : Fin n, ∑ d' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c' (pdM d' u) x a b‖ := by
  have h1 : ‖pdM c (pdM d u) x i j‖ ≤ ∑ b : Fin n, ‖pdM c (pdM d u) x i b‖ :=
    single_le_sum_univ (fun b => norm_nonneg (pdM c (pdM d u) x i b)) j
  have h2 : (∑ b : Fin n, ‖pdM c (pdM d u) x i b‖)
      ≤ ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d u) x a b‖ :=
    single_le_sum_univ (fun a => Finset.sum_nonneg (fun b _ => norm_nonneg _)) i
  have h3 : (∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d u) x a b‖)
      ≤ ∑ d' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d' u) x a b‖ :=
    single_le_sum_univ
      (f := fun d' : Fin n => ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d' u) x a b‖)
      (fun d' => Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
        Finset.sum_nonneg (s := Finset.univ) (fun b _ => norm_nonneg _))) d
  have h4 : (∑ d' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d' u) x a b‖)
      ≤ ∑ c' : Fin n, ∑ d' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖pdM c' (pdM d' u) x a b‖ :=
    single_le_sum_univ
      (f := fun c' : Fin n => ∑ d' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        ‖pdM c' (pdM d' u) x a b‖)
      (fun c' => Finset.sum_nonneg (s := Finset.univ) (fun d' _ =>
        Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
          Finset.sum_nonneg (s := Finset.univ) (fun b _ => norm_nonneg _)))) c
  linarith

/-- The analogous bound for the entries of the inverse metric. -/
lemma norm_entry_le_sum_invMat {n : ℕ} (A : MatC n) (i j : Fin n) :
    ‖((reMat A)⁻¹) i j‖ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖((reMat A)⁻¹) a b‖ := by
  have h1 : ‖((reMat A)⁻¹) i j‖ ≤ ∑ b : Fin n, ‖((reMat A)⁻¹) i b‖ :=
    single_le_sum_univ (fun b => norm_nonneg (((reMat A)⁻¹) i b)) j
  have h2 : (∑ b : Fin n, ‖((reMat A)⁻¹) i b‖) ≤ ∑ a : Fin n, ∑ b : Fin n,
      ‖((reMat A)⁻¹) a b‖ :=
    single_le_sum_univ (fun a => Finset.sum_nonneg (fun b _ => norm_nonneg _)) i
  linarith

/-- The `∑∑` form of a matrix quadratic form is the matrix-vector pairing. -/
lemma sum_sum_mul_eq_dotProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (∑ i, ∑ j, A i j * x i * y j) = x ⬝ᵥ (A *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Cauchy–Schwarz for a positive semidefinite quadratic form. -/
lemma posSemidef_cauchy_schwarz {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x y : Fin n → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := fun u v => by
    simpa only [star_trivial] using hA.isHermitian.star_dotProduct_mulVec_comm u v
  have hexp : ∀ t : ℝ, (x + t • y) ⬝ᵥ (A *ᵥ (x + t • y))
      = (y ⬝ᵥ (A *ᵥ y)) * (t * t) + ((x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) * t
        + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  have hquad : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t)
      + ((x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) * t + (x ⬝ᵥ (A *ᵥ x)) := by
    intro t
    rw [← hexp t]
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg (x + t • y)
  have hd := discrim_le_zero (a := y ⬝ᵥ (A *ᵥ y))
    (b := (x ⬝ᵥ (A *ᵥ y)) + (y ⬝ᵥ (A *ᵥ x))) (c := x ⬝ᵥ (A *ᵥ x)) hquad
  rw [discrim] at hd
  have hs := hsym x y
  rw [hs] at hd ⊢
  nlinarith [hd]

/-- Nonnegativity of the quadratic form of a positive semidefinite matrix, in `∑∑` form. -/
lemma posSemidef_sum_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, A i j * x i * x j := by
  have h := hA.dotProduct_mulVec_nonneg x
  simpa only [star_trivial, ← sum_sum_mul_eq_dotProduct A x x] using h

/-- A homogeneous quadratic form is homogeneous. -/
lemma quadForm_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, A i j * (c • ξ) i * (c • ξ) j) = c ^ 2 * ∑ i, ∑ j, A i j * ξ i * ξ j := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- A homogeneous quadratic form bounded above on the unit sphere is bounded above everywhere. -/
lemma quadForm_le_of_sphere {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hhom : ∀ (c : ℝ) (ξ : Fin n → ℝ), F (c • ξ) = c ^ 2 * F ξ)
    {β : ℝ} (h : ∀ ξ : Fin n → ℝ, (∑ i, (ξ i) ^ 2 = 1) → F ξ ≤ β) :
    ∀ ξ : Fin n → ℝ, F ξ ≤ β * ∑ i, (ξ i) ^ 2 := by
  intro ξ
  have h1 := elliptic_sphere_hom (F := fun η => -F η) (lam := -β)
    (fun c η => by rw [hhom]; ring) (fun η hη => by simpa using neg_le_neg (h η hη)) ξ
  linarith

/-- Lower bound for the quadratic form of the inverse matrix, from an upper bound on the
quadratic form of the matrix itself (Cauchy–Schwarz for the positive definite form). -/
lemma inv_quadForm_lower_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (β : ℝ) (hβ : 0 < β)
    (hup : ∀ w : Fin n → ℝ, ∑ i, ∑ j, A i j * w i * w j ≤ β * ∑ i, (w i) ^ 2) :
    ∀ ξ : Fin n → ℝ, β⁻¹ * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j := by
  intro ξ
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det (A := A)).mp hA.isUnit)
  have hAv : A *ᵥ (A⁻¹ *ᵥ ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hcs := posSemidef_cauchy_schwarz hA.posSemidef ξ (A⁻¹ *ᵥ ξ)
  rw [hAv] at hcs
  rw [dotProduct_comm (A⁻¹ *ᵥ ξ) ξ] at hcs
  have h1 : ξ ⬝ᵥ ξ = ∑ i, (ξ i) ^ 2 := by simp only [dotProduct, pow_two]
  have h2 : ξ ⬝ᵥ (A *ᵥ ξ) = ∑ i, ∑ j, A i j * ξ i * ξ j :=
    (sum_sum_mul_eq_dotProduct A ξ ξ).symm
  have h3 : ξ ⬝ᵥ (A⁻¹ *ᵥ ξ) = ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j :=
    (sum_sum_mul_eq_dotProduct A⁻¹ ξ ξ).symm
  rw [h1, h2, h3] at hcs
  have hSnn : 0 ≤ ∑ i, (ξ i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
  have hWnn : 0 ≤ ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j :=
    posSemidef_sum_nonneg hA.posSemidef.inv ξ
  have hupξ := hup ξ
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · rw [← hS0, mul_zero]
    exact hWnn
  · have hstep : (∑ i, (ξ i) ^ 2) * (∑ i, (ξ i) ^ 2)
        ≤ (∑ i, (ξ i) ^ 2) * (β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j)) := by
      calc (∑ i, (ξ i) ^ 2) * (∑ i, (ξ i) ^ 2) = (∑ i, (ξ i) ^ 2) ^ 2 := by ring
        _ ≤ (∑ i, ∑ j, A i j * ξ i * ξ j) * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) := hcs
        _ ≤ (β * ∑ i, (ξ i) ^ 2) * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) :=
            mul_le_mul_of_nonneg_right hupξ hWnn
        _ = (∑ i, (ξ i) ^ 2) * (β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j)) := by ring
    have h2' : ∑ i, (ξ i) ^ 2 ≤ β * (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) :=
      (mul_le_mul_iff_of_pos_left hSpos).mp hstep
    rwa [inv_mul_le_iff₀ hβ]

/-- Uniform bounds for the jets, the inverse metric and the ellipticity constants along a
positive definite solution on `[0,tstar]`. -/
lemma sol_bounds {n : ℕ} (hn : 1 ≤ n) (Φ : (Fin n → ℝ) × Jet n → MatC n)
    {T : ℝ} (u : ℝ → Torus n) (hu : SolvesOn Φ T u)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, PosDefM (u t x))
    {tstar : ℝ} (htstar0 : 0 ≤ tstar) (htstarT : tstar < T) :
    ∃ (M lam K₁ : ℝ), 0 < lam ∧ 0 ≤ M ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
        (∀ i j, ‖u t x i j‖ ≤ M) ∧ (∀ c i j, ‖pdM c (u t) x i j‖ ≤ M) ∧
        (∀ c d i j, ‖pdM c (pdM d (u t)) x i j‖ ≤ M) ∧
        (∀ i j, ‖((reMat (u t x))⁻¹) i j‖ ≤ M)) ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
        lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, reMat (u t x) i j * ξ i * ξ j) ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
        lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, ((reMat (u t x))⁻¹) i j * ξ i * ξ j) ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
        |pdR i (fun y => ((reMat (u t y))⁻¹) c d) x| ≤ K₁) := by
  -- the compact cube
  have hKcompact : IsCompact ((Set.Icc (0:ℝ) tstar) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : (Set.Icc (0:ℝ) tstar) ×ˢ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))
      ⊆ Set.Ico (0:ℝ) T ×ˢ Set.univ :=
    fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 htstarT⟩, Set.mem_univ _⟩
  -- joint smoothness / continuity of everything
  have hval : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_entry_of_contDiffOn hu.1 i j
  have hpd1 : ∀ c i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => pdM c (u p.1) p.2 i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c i j => contDiffOn_pd_slice (F := fun t x => u t x i j) (hval i j) c
  have hpd2 : ∀ c d i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => pdM c (pdM d (u p.1)) p.2 i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c d i j => contDiffOn_pd_slice (F := fun t x => pdM d (u t) x i j) (hpd1 d i j) c
  have hmat : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => reMat (u p.1 p.2) i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_reMat_entry hu.1 i j
  have hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0 :=
    fun t ht x => (Matrix.PosDef.det_pos (hell t ht x)).ne'
  have hinv : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => ((reMat (u p.1 p.2))⁻¹) c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c d => contDiffOn_matrixInv_entry hmat hdet c d
  -- ============ the entrywise bounds ============
  have hFv_nn : ∀ p : ℝ × (Fin n → ℝ), 0 ≤ ∑ a : Fin n, ∑ b : Fin n, ‖u p.1 p.2 a b‖ :=
    fun p => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))
  have hF1_nn : ∀ p : ℝ × (Fin n → ℝ), 0 ≤ ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      ‖pdM c (u p.1) p.2 a b‖ := fun p => Finset.sum_nonneg (fun c _ =>
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _)))
  have hF2_nn : ∀ p : ℝ × (Fin n → ℝ), 0 ≤ ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n,
      ∑ b : Fin n, ‖pdM c (pdM d (u p.1)) p.2 a b‖ := fun p => Finset.sum_nonneg (fun c _ =>
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => norm_nonneg _))))
  have hFi_nn : ∀ p : ℝ × (Fin n → ℝ), 0 ≤ ∑ a : Fin n, ∑ b : Fin n,
      ‖((reMat (u p.1 p.2))⁻¹) a b‖ :=
    fun p => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => norm_nonneg _))
  have hFvcont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      ∑ a : Fin n, ∑ b : Fin n, ‖u p.1 p.2 a b‖) (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
    exact continuous_norm.comp_continuousOn (hval a b).continuousOn
  have hF1cont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (u p.1) p.2 a b‖)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun a _ =>
      continuousOn_finsetSum _ (fun b _ => ?_)))
    exact continuous_norm.comp_continuousOn (hpd1 c a b).continuousOn
  have hF2cont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (pdM d (u p.1)) p.2 a b‖)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun d _ =>
      continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))))
    exact continuous_norm.comp_continuousOn (hpd2 c d a b).continuousOn
  have hFicont : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      ∑ a : Fin n, ∑ b : Fin n, ‖((reMat (u p.1 p.2))⁻¹) a b‖)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun a _ => continuousOn_finsetSum _ (fun b _ => ?_))
    exact continuous_norm.comp_continuousOn (hinv a b).continuousOn
  obtain ⟨Bv, hBv⟩ := hKcompact.exists_bound_of_continuousOn (hFvcont.mono hKsub)
  obtain ⟨B1, hB1⟩ := hKcompact.exists_bound_of_continuousOn (hF1cont.mono hKsub)
  obtain ⟨B2, hB2⟩ := hKcompact.exists_bound_of_continuousOn (hF2cont.mono hKsub)
  obtain ⟨MI, hMI⟩ := hKcompact.exists_bound_of_continuousOn (hFicont.mono hKsub)
  have hpt0 : ((0 : ℝ), (0 : Fin n → ℝ)) ∈
      (Set.Icc (0:ℝ) tstar) ×ˢ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) :=
    ⟨⟨le_rfl, htstar0⟩, fun i _ => ⟨le_rfl, zero_le_one⟩⟩
  have hBv0 : 0 ≤ Bv := by
    have h := hBv (0, 0) hpt0
    rw [Real.norm_of_nonneg (hFv_nn (0, 0))] at h
    exact le_trans (hFv_nn (0, 0)) h
  have hB10 : 0 ≤ B1 := by
    have h := hB1 (0, 0) hpt0
    rw [Real.norm_of_nonneg (hF1_nn (0, 0))] at h
    exact le_trans (hF1_nn (0, 0)) h
  have hB20 : 0 ≤ B2 := by
    have h := hB2 (0, 0) hpt0
    rw [Real.norm_of_nonneg (hF2_nn (0, 0))] at h
    exact le_trans (hF2_nn (0, 0)) h
  have hMI0 : 0 ≤ MI := by
    have h := hMI (0, 0) hpt0
    rw [Real.norm_of_nonneg (hFi_nn (0, 0))] at h
    exact le_trans (hFi_nn (0, 0)) h
  -- ============ the ellipticity constants ============
  have hSphclosed : IsClosed {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hSphsub : {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : (ξ i) ^ 2 ≤ ∑ j, (ξ j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hξ] at h1
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (ξ i), abs_nonneg (ξ i)]
  have hSphcompact : IsCompact {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} :=
    (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset hSphclosed hSphsub
  let ξ₀ : Fin n → ℝ := fun i => if i = (⟨0, hn⟩ : Fin n) then 1 else 0
  have hξ₀ : ξ₀ ∈ {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} := by
    show (∑ i : Fin n, (ξ₀ i) ^ 2) = 1
    simp only [ξ₀]
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hSphne : ({ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1}).Nonempty := ⟨ξ₀, hξ₀⟩
  set S' : Set ((ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) :=
    (Set.Icc (0:ℝ) tstar ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) ×ˢ
      {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} with hS'def
  have hcont1 : ContinuousOn (fun q : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      ∑ i, ∑ j, reMat (u q.1.1 q.1.2) i j * q.2 i * q.2 j) S' := by
    refine continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ => ?_))
    have h2 : ContinuousOn (fun q : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        reMat (u q.1.1 q.1.2) i j) S' :=
      (hmat i j).continuousOn.comp continuous_fst.continuousOn (fun q hq => hKsub hq.1)
    have h3i : ContinuousOn (fun q : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => q.2 i) S' :=
      ((continuous_apply i).comp continuous_snd).continuousOn
    have h3j : ContinuousOn (fun q : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) => q.2 j) S' :=
      ((continuous_apply j).comp continuous_snd).continuousOn
    convert (h2.mul h3i).mul h3j using 1
  obtain ⟨qA, hqA, hminA⟩ :=
    (hKcompact.prod hSphcompact).exists_isMinOn
      ⟨((0, 0), ξ₀), ⟨⟨le_rfl, htstar0⟩, fun i _ => ⟨le_rfl, zero_le_one⟩⟩, hξ₀⟩ hcont1
  obtain ⟨qC, hqC, hmaxC⟩ :=
    (hKcompact.prod hSphcompact).exists_isMaxOn
      ⟨((0, 0), ξ₀), ⟨⟨le_rfl, htstar0⟩, fun i _ => ⟨le_rfl, zero_le_one⟩⟩, hξ₀⟩ hcont1
  have hlamA : 0 < ∑ i, ∑ j, reMat (u qA.1.1 qA.1.2) i j * qA.2 i * qA.2 j := by
    have hpos := hell qA.1.1 ⟨hqA.1.1.1, lt_of_le_of_lt hqA.1.1.2 htstarT⟩ qA.1.2
    have hne : qA.2 ≠ 0 := by
      intro h
      have h2 := hqA.2
      rw [h] at h2
      simp at h2
    have h := hpos.dotProduct_mulVec_pos hne
    simpa [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hqAmax : (∑ i, ∑ j, reMat (u qA.1.1 qA.1.2) i j * qA.2 i * qA.2 j)
      ≤ ∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j := hmaxC hqA
  have hβpos : 0 < ∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j :=
    lt_of_lt_of_le hlamA hqAmax
  have hlamB : 0 < (∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j)⁻¹ :=
    inv_pos.mpr hβpos
  set lam : ℝ := min (∑ i, ∑ j, reMat (u qA.1.1 qA.1.2) i j * qA.2 i * qA.2 j)
    (∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j)⁻¹ with hlamdef
  have hlam : 0 < lam := lt_min hlamA hlamB
  -- the joint smoothness of the (complexified) first derivatives of the inverse
  have hpdC : ∀ c d i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) =>
        pd i (fun y => (((reMat (u p.1 y))⁻¹) c d : ℂ)) p.2) (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    intro c d i
    refine contDiffOn_pd_slice (F := fun t y => (((reMat (u t y))⁻¹) c d : ℂ)) ?_ i
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hinv c d)
  have hK1cont : ContinuousOn (fun q : ℝ × (Fin n → ℝ) =>
      ∑ c : Fin n, ∑ d : Fin n, ∑ i : Fin n,
        |(pd i (fun y => (((reMat (u q.1 y))⁻¹) c d : ℂ)) q.2).re|)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun d _ =>
      continuousOn_finsetSum _ (fun i _ => ?_)))
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hpdC c d i).continuousOn)
  obtain ⟨K₁₀, hK₁₀⟩ := hKcompact.exists_bound_of_continuousOn (hK1cont.mono hKsub)
  have hsliceF : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ c d,
      Differentiable ℝ (fun y => ((reMat (u t y))⁻¹) c d) := by
    intro t ht c d
    exact (contDiff_slice_of_contDiffOn_real (F := fun t y => ((reMat (u t y))⁻¹) c d)
      (hinv c d) ⟨ht.1, lt_trans ht.2 htstarT⟩).differentiable (by simp)
  refine ⟨Bv + B1 + B2 + MI, lam, max K₁₀ 0, hlam, by linarith [hBv0, hB10, hB20, hMI0],
    ?_, ?_, ?_, ?_⟩
  · -- the jet and inverse bounds on the compact cube
    intro t ht x hx
    have hbv : ∑ a : Fin n, ∑ b : Fin n, ‖u t x a b‖ ≤ Bv := by
      have h := hBv (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩
      rwa [Real.norm_of_nonneg (hFv_nn (t, x))] at h
    have hb1 : ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖pdM c (u t) x a b‖ ≤ B1 := by
      have h := hB1 (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩
      rwa [Real.norm_of_nonneg (hF1_nn (t, x))] at h
    have hb2 : ∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        ‖pdM c (pdM d (u t)) x a b‖ ≤ B2 := by
      have h := hB2 (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩
      rwa [Real.norm_of_nonneg (hF2_nn (t, x))] at h
    have hbi : ∑ a : Fin n, ∑ b : Fin n, ‖((reMat (u t x))⁻¹) a b‖ ≤ MI := by
      have h := hMI (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩
      rwa [Real.norm_of_nonneg (hFi_nn (t, x))] at h
    have hsum : Bv ≤ Bv + B1 + B2 + MI := by linarith [hB10, hB20, hMI0]
    have hsum1 : B1 ≤ Bv + B1 + B2 + MI := by linarith [hBv0, hB20, hMI0]
    have hsum2 : B2 ≤ Bv + B1 + B2 + MI := by linarith [hBv0, hB10, hMI0]
    have hsumi : MI ≤ Bv + B1 + B2 + MI := by linarith [hBv0, hB10, hB20]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      exact le_trans (le_trans (norm_entry_le_sum_matC (u t x) i j) hbv) hsum
    · intro c i j
      exact le_trans (le_trans (norm_entry_le_sum_pdM (u t) x c i j) hb1) hsum1
    · intro c d i j
      exact le_trans (le_trans (norm_entry_le_sum_pdM2 (u t) x c d i j) hb2) hsum2
    · intro i j
      exact le_trans (le_trans (norm_entry_le_sum_invMat (u t x) i j) hbi) hsumi
  · -- ellipticity of the metric, everywhere
    intro t ht x ξ
    have hper : Periodic1 (fun z => ∑ i, ∑ j, reMat (u t z) i j * ξ i * ξ j) := by
      intro j z
      have h1 : u t (z + Pi.single j 1) = u t z := hu.2.1 t ⟨ht.1, lt_trans ht.2 htstarT⟩ j z
      simp only [h1]
    rw [← Periodic1.apply_periodicRep hper x]
    refine elliptic_sphere_hom
      (F := fun η : Fin n → ℝ => ∑ i, ∑ j, reMat (u t (periodicRep x)) i j * η i * η j)
      (lam := lam) ?_ ?_ ξ
    · intro c η
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    · intro η hη
      have hq : ((t, periodicRep x), η) ∈
          (Set.Icc (0:ℝ) tstar ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) ×ˢ
            {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} :=
        ⟨⟨⟨ht.1, ht.2.le⟩, fun i _ => periodicRep_mem x i⟩, hη⟩
      exact le_trans (min_le_left _ _) (hminA hq)
  · -- ellipticity of the inverse, everywhere
    intro t ht x ξ
    have hper : Periodic1 (fun z => ∑ i, ∑ j, ((reMat (u t z))⁻¹) i j * ξ i * ξ j) := by
      intro j z
      have h1 : u t (z + Pi.single j 1) = u t z := hu.2.1 t ⟨ht.1, lt_trans ht.2 htstarT⟩ j z
      simp only [h1]
    rw [← Periodic1.apply_periodicRep hper x]
    have hup : ∀ w : Fin n → ℝ,
        ∑ i, ∑ j, reMat (u t (periodicRep x)) i j * w i * w j
          ≤ (∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j) * ∑ i, (w i) ^ 2 := by
      intro w
      refine quadForm_le_of_sphere
        (F := fun η : Fin n → ℝ =>
          ∑ i, ∑ j, reMat (u t (periodicRep x)) i j * η i * η j)
        (quadForm_smul (reMat (u t (periodicRep x)))) ?_ w
      intro η hη
      have hq : ((t, periodicRep x), η) ∈
          (Set.Icc (0:ℝ) tstar ×ˢ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) ×ˢ
            {ξ : Fin n → ℝ | ∑ i, (ξ i) ^ 2 = 1} :=
        ⟨⟨⟨ht.1, ht.2.le⟩, fun i _ => periodicRep_mem x i⟩, hη⟩
      exact hmaxC hq
    have hApos : Matrix.PosDef (reMat (u t (periodicRep x))) :=
      hell t ⟨ht.1, lt_trans ht.2 htstarT⟩ (periodicRep x)
    have hlow := inv_quadForm_lower_bound (reMat (u t (periodicRep x))) hApos
      (∑ i, ∑ j, reMat (u qC.1.1 qC.1.2) i j * qC.2 i * qC.2 j) hβpos hup ξ
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) ?_) hlow
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
  · -- the derivative bound `K₁`
    intro t ht c d i x
    have hper : Periodic1 (fun x => pdR i (fun y => ((reMat (u t y))⁻¹) c d) x) := by
      intro j
      refine Work.Diff.STE.cm_periodicIn_pdR j i ?_ ?_
      · exact hsliceF t ht c d
      · intro z
        show ((reMat (u t (z + Pi.single j 1)))⁻¹) c d = ((reMat (u t z))⁻¹) c d
        rw [hu.2.1 t ⟨ht.1, lt_trans ht.2 htstarT⟩ j z]
    have hcube : ∀ y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
        |pdR i (fun y' => ((reMat (u t y'))⁻¹) c d) y| ≤ K₁₀ := by
      intro y hy
      have hb := hK₁₀ (t, y) ⟨⟨ht.1, ht.2.le⟩, hy⟩
      rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun c' _ => Finset.sum_nonneg (fun d' _ =>
        Finset.sum_nonneg (fun i' _ => abs_nonneg _))))] at hb
      have hpd : |pdR i (fun y' => ((reMat (u t y'))⁻¹) c d) y|
          = |(pd i (fun y' => (((reMat (u t y'))⁻¹) c d : ℂ)) y).re| := by
        rw [ga_pd_ofReal i (fun y' => ((reMat (u t y'))⁻¹) c d) y
          (hsliceF t ht c d).differentiableAt, Complex.ofReal_re]
      rw [hpd]
      exact le_trans (abs_le_sum_three
        (fun c' d' i' => (pd i' (fun y' => (((reMat (u t y'))⁻¹) c' d' : ℂ)) y).re) c d i) hb
    exact le_trans (abs_le_of_periodic1_of_cube hper hcube x) (le_max_left _ _)


/-! ## Auxiliary estimates for the uniqueness theorem -/

/-- A periodic complex-valued function bounded on the closed unit cube is bounded everywhere. -/
lemma norm_le_of_periodic1_of_cube {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : Periodic1 f) {M : ℝ}
    (h : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1), ‖f x‖ ≤ M) :
    ∀ x, ‖f x‖ ≤ M := by
  intro x
  rw [← Periodic1.apply_periodicRep hf x]
  exact h _ (fun i _ => periodicRep_mem x i)

/-- The norm of a complex vector is at most the sum of the norms of its entries. -/
lemma norm_le_sum_norm_fin {n : ℕ} (f : Fin n → ℂ) : ‖f‖ ≤ ∑ i, ‖f i‖ := by
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
  intro i
  exact single_le_sum_univ (fun i' => norm_nonneg (f i')) i

/-- Each entry of a matrix is at most the norm of the matrix. -/
lemma norm_entry_le_norm_matC {n : ℕ} (A : MatC n) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ :=
  le_trans (norm_le_pi_norm (A i) j) (norm_le_pi_norm A i)

/-- The norm of a matrix is at most the sum of the norms of its entries. -/
lemma norm_le_sum_norm_matC {n : ℕ} (A : MatC n) : ‖A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  have hnn : 0 ≤ ∑ i, ∑ j, ‖A i j‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  rw [pi_norm_le_iff_of_nonneg hnn]
  intro i
  exact le_trans (norm_le_sum_norm_fin (fun j => A i j))
    (single_le_sum_univ (fun i' => Finset.sum_nonneg (fun j _ => norm_nonneg _)) i)

/-- The norm of a matrix-valued family is at most the sum of the norms of its entries. -/
lemma norm_le_sum_norm_pi_matC {n : ℕ} (F : Fin n → MatC n) :
    ‖F‖ ≤ ∑ c, ∑ i, ∑ j, ‖F c i j‖ := by
  have hnn : 0 ≤ ∑ c, ∑ i, ∑ j, ‖F c i j‖ := Finset.sum_nonneg (fun c _ =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _)))
  rw [pi_norm_le_iff_of_nonneg hnn]
  intro c
  exact le_trans (norm_le_sum_norm_matC (F c))
    (single_le_sum_univ (fun c' => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => norm_nonneg _))) c)

/-- Grönwall's comparison in homogeneous form: if `y' ≤ C y` on `(0,T)` then
`t ↦ y t * e^{-Ct}` is antitone on `[0,T]`. -/
lemma antitoneOn_mul_exp_of_deriv_le {y y' : ℝ → ℝ} {T C : ℝ}
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivWithinAt y (y' t) (Set.Ioo (0:ℝ) T) t)
    (hineq : ∀ t ∈ Set.Ioo (0:ℝ) T, y' t ≤ C * y t) :
    AntitoneOn (fun t : ℝ => y t * Real.exp (-(C * t))) (Set.Icc 0 T) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (f := fun t : ℝ => y t * Real.exp (-(C * t)))
    (f' := fun t : ℝ => Real.exp (-(C * t)) * (y' t - C * y t)) ?_ ?_ ?_
  · exact hcont.mul (Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).neg))
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hyd := hderiv x hx
    have hexp : HasDerivWithinAt (fun t : ℝ => Real.exp (-(C * t)))
        (Real.exp (-(C * x)) * (-C)) (Set.Ioo (0:ℝ) T) x := by
      have hg : HasDerivAt (fun t : ℝ => -(C * t)) (-C) x := by
        have h' : HasDerivAt (fun t : ℝ => (-C) * t) (-C) x := hasDerivAt_const_mul (-C)
        simpa only [neg_mul] using h'
      exact (hg.exp).hasDerivWithinAt
    refine (hyd.mul hexp).congr_deriv ?_
    ring
  · intro x hx
    rw [interior_Icc] at hx
    have hx' := hineq x hx
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hx')

/-- If `y' ≤ C y` on `(0,T)`, `y ≥ 0` on `[0,T]` and `y 0 = 0`, then `y` vanishes on `[0,T]`. -/
lemma eq_zero_of_deriv_le {y y' : ℝ → ℝ} {T C : ℝ}
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivWithinAt y (y' t) (Set.Ioo (0:ℝ) T) t)
    (hineq : ∀ t ∈ Set.Ioo (0:ℝ) T, y' t ≤ C * y t)
    (hnn : ∀ t ∈ Set.Icc 0 T, 0 ≤ y t) (h0 : y 0 = 0) :
    ∀ t ∈ Set.Icc 0 T, y t = 0 := by
  have hanti := antitoneOn_mul_exp_of_deriv_le hcont hderiv hineq
  intro t ht
  have h0mem : (0:ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hle := hanti h0mem ht ht.1
  have hleft : y t * Real.exp (-(C * t)) ≤ 0 := by
    calc y t * Real.exp (-(C * t)) ≤ y 0 * Real.exp (-(C * 0)) := hle
      _ = 0 := by rw [h0]; ring
  have hyt : y t ≤ 0 := by
    by_contra hcon
    have hpos : 0 < y t := lt_of_not_ge hcon
    have h2 : 0 < y t * Real.exp (-(C * t)) := mul_pos hpos (Real.exp_pos _)
    linarith
  exact le_antisymm hyt (hnn t ht)


open Work.Diff.STE.Flat
open MeasureTheory Set Filter
open scoped Topology Matrix

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ## Continuity of the spatial slice of the difference of the two nonlinearities -/

/-- The spatial jet of a smooth solution is continuous. -/
lemma tj_continuous_jetM_slice {n : ℕ} {Φ : (Fin n → ℝ) × Jet n → MatC n}
    {T : ℝ} {u : ℝ → Torus n} (hu : SolvesOn Φ T u) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Continuous (fun x : Fin n → ℝ => jetM (u t) x) := by
  have h0 : Continuous (fun x : Fin n → ℝ => u t x) := by
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    exact (contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
      (contDiffOn_entry_of_contDiffOn hu.1 i j) ht).continuous
  have h1 : Continuous (fun x : Fin n → ℝ => fun c : Fin n => pdM c (u t) x) := by
    refine continuous_pi (fun c => continuous_pi (fun i => continuous_pi (fun j => ?_)))
    exact (contDiff_slice_of_contDiffOn
      (F := fun τ y => pd c (fun z : Fin n → ℝ => u τ z i j) y)
      (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) c) ht).continuous
  have h2 : Continuous (fun x : Fin n → ℝ => fun c d : Fin n =>
      pdM c (pdM d (u t)) x) := by
    refine continuous_pi (fun c => continuous_pi (fun d => continuous_pi (fun i =>
      continuous_pi (fun j => ?_))))
    exact (contDiff_slice_of_contDiffOn
      (F := fun τ y => pd c (fun z : Fin n → ℝ => pdM d (u τ) z i j) y)
      (contDiffOn_pd_slice (F := fun τ y => pdM d (u τ) y i j)
        (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
          (contDiffOn_entry_of_contDiffOn hu.1 i j) d) c) ht).continuous
  simpa only [jetM] using h0.prodMk (h1.prodMk h2)

/-- The `x`-slice of `Φ (·, jet u)` is continuous where the metric matrix is positive definite. -/
lemma tj_continuous_slice_Phi {n : ℕ} {Φ : (Fin n → ℝ) × Jet n → MatC n}
    (hshape : IsDeTurckNonlin Φ) {T : ℝ} {u : ℝ → Torus n} (hu : SolvesOn Φ T u)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x))
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Continuous (fun x : Fin n → ℝ => Φ (x, jetM (u t) x)) := by
  obtain ⟨hΦsm, -, -, -⟩ := hshape
  have hjet : Continuous (fun x : Fin n → ℝ => jetM (u t) x) := tj_continuous_jetM_slice hu ht
  have hmap : Set.MapsTo (fun x : Fin n → ℝ => (x, jetM (u t) x)) Set.univ
      (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) :=
    fun x _ => ⟨Set.mem_univ _, (Matrix.PosDef.det_pos (hellu t ht x)).ne'⟩
  have hc : ContinuousOn (fun x : Fin n → ℝ => Φ (x, jetM (u t) x)) Set.univ :=
    hΦsm.continuousOn.comp (continuous_id.prodMk hjet).continuousOn hmap
  exact continuousOn_univ.mp hc

/-- The spatial slice of the difference of the two nonlinearities is continuous. -/
lemma tj_tj_continuous_slice_PhiDiff_aux {n : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : IsDeTurckNonlin Φ)
    {T : ℝ} (u v : ℝ → Torus n)
    (hu : SolvesOn Φ T u) (hv : SolvesOn Φ T v)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x))
    (hellv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (v t x))
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) T) (i j : Fin n) :
    Continuous (fun x : Fin n → ℝ =>
      (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j) := by
  have hdiff : Continuous (fun x : Fin n → ℝ =>
      Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) :=
    (tj_continuous_slice_Phi hshape hu hellu ht).sub (tj_continuous_slice_Phi hshape hv hellv ht)
  exact (continuous_apply j).comp ((continuous_apply i).comp hdiff)

/-! ## Auxiliary facts about the `L²` pairing -/

/-- The `L²` pairing is bounded by the integral of the product of the norms. -/
lemma tj_L2re_le_integral_norm_mul {ι : Type*} [Fintype ι] (f g : (ι → ℝ) → ℂ) :
    L2re f g ≤ ∫ x in unitCube (ι := ι), ‖f x‖ * ‖g x‖ := by
  have h1 : L2re f g ≤ ‖∫ x in unitCube (ι := ι), f x * star (g x)‖ := by
    simp only [L2re]
    exact Complex.re_le_norm _
  have h2 : ‖∫ x in unitCube (ι := ι), f x * star (g x)‖
      ≤ ∫ x in unitCube (ι := ι), ‖f x * star (g x)‖ := norm_integral_le_integral_norm _
  have h3 : (∫ x in unitCube (ι := ι), ‖f x * star (g x)‖)
      = ∫ x in unitCube (ι := ι), ‖f x‖ * ‖g x‖ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star]
  linarith [h1, h2, h3]

/-- The `L²` pairing is additive in its first argument. -/
lemma tj_L2re_add_slice {ι : Type*} [Fintype ι] {f₁ f₂ g : (ι → ℝ) → ℂ}
    (h1 : Integrable (fun x => f₁ x * star (g x)) (volume.restrict (unitCube (ι := ι))))
    (h2 : Integrable (fun x => f₂ x * star (g x)) (volume.restrict (unitCube (ι := ι)))) :
    L2re (fun x => f₁ x + f₂ x) g = L2re f₁ g + L2re f₂ g := by
  have hpt : (fun x : ι → ℝ => (f₁ x + f₂ x) * star (g x))
      = fun x => f₁ x * star (g x) + f₂ x * star (g x) := by
    funext x; rw [add_mul]
  have h3 : (∫ x in unitCube (ι := ι), (f₁ x + f₂ x) * star (g x))
      = (∫ x in unitCube (ι := ι), f₁ x * star (g x))
        + ∫ x in unitCube (ι := ι), f₂ x * star (g x) := by
    rw [hpt, integral_add h1 h2]
  simp only [L2re]
  rw [h3, Complex.add_re]

/-! ## The energy inequality -/

theorem tj_uniqueness_energy_ineq {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    {T tstar : ℝ} (u v : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u) (hv : Work.Diff.STE.Flat.SolvesOn Φ T v)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (u t x))
    (hellv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (v t x))
    (htstarT : tstar < T)
    (M lamu K₁ CR : ℝ) (hM : 0 ≤ M) (hlamu : 0 < lamu) (hCR : 0 ≤ CR)
    (hbu : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      (∀ i j, ‖u t x i j‖ ≤ M) ∧ (∀ c i j, ‖Work.Diff.STE.Flat.pdM c (u t) x i j‖ ≤ M) ∧
      (∀ c d i j, ‖Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u t)) x i j‖ ≤ M) ∧
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat (u t x))⁻¹) i j‖ ≤ M))
    (hbv : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      (∀ i j, ‖v t x i j‖ ≤ M) ∧ (∀ c i j, ‖Work.Diff.STE.Flat.pdM c (v t) x i j‖ ≤ M) ∧
      (∀ c d i j, ‖Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v t)) x i j‖ ≤ M) ∧
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat (v t x))⁻¹) i j‖ ≤ M))
    (hellMu : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j)
    (hellMv : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (v t x) i j * ξ i * ξ j)
    (hellIu : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ x, ∀ ξ : Fin n → ℝ,
      lamu * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, ∑ j, ((Work.Diff.STE.Flat.reMat (u t x))⁻¹) i j * ξ i * ξ j)
    (hK₁u : ∀ t ∈ Set.Ico (0 : ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i (fun y => ((Work.Diff.STE.Flat.reMat (u t y))⁻¹) c d) x| ≤ K₁)
    (hres : ∀ t ∈ Set.Ico (0 : ℝ) tstar,
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      ‖Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x) -
          Work.Diff.STE.Flat.secOpFlat (u t x)
            (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u t)) x -
              Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v t)) x)‖ ≤
        CR * ((∑ i, ∑ j, ‖u t x i j - v t x i j‖) +
          (∑ c, ∑ i, ∑ j,
            ‖Work.Diff.STE.Flat.pdM c (u t) x i j - Work.Diff.STE.Flat.pdM c (v t) x i j‖))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (0 : ℝ) tstar,
      (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ((Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x)) i j
            * star (u t x i j - v t x i j)).re)
        ≤ K * (∑ i : Fin n, ∑ j : Fin n, ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
            ‖u t x i j - v t x i j‖ ^ 2) := by
  -- ## 1. the Gårding estimate for the inverse metric matrix of `u`
  have hmatu : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => reMat (u p.1 p.2) i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_reMat_entry hu.1 i j
  have hdetu : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (reMat (u t x)).det ≠ 0 :=
    fun t ht x => (Matrix.PosDef.det_pos (hellu t ht x)).ne'
  have hinvu : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => ((reMat (u p.1 p.2))⁻¹) c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c d => contDiffOn_matrixInv_entry hmatu hdetu c d
  have hperRe : ∀ t ∈ Set.Ico (0:ℝ) tstar,
      Periodic1 (fun x : Fin n → ℝ => reMat (u t x)) := by
    intro t ht i x
    have h : u t (x + Pi.single i 1) = u t x :=
      hu.2.1 t ⟨ht.1, lt_trans ht.2 htstarT⟩ i x
    show reMat (u t (x + Pi.single i 1)) = reMat (u t x)
    rw [h]
  obtain ⟨Cg, hCg, hgard⟩ := garding_param
      (A := fun (b : {τ : ℝ // τ ∈ Set.Ico (0:ℝ) tstar}) (c d : Fin n) (x : Fin n → ℝ) =>
        ((reMat (u b.1 x))⁻¹) c d)
      (fun b c d => contDiff_slice_of_contDiffOn_real
        (F := fun τ y => ((reMat (u τ y))⁻¹) c d)
        (hinvu c d) ⟨b.2.1, lt_trans b.2.2 htstarT⟩)
      (fun b c d => Periodic1.matrixInv_entry (hperRe b.1 b.2) c d)
      (fun b c d x => by
        have h := (hellu b.1 ⟨b.2.1, lt_trans b.2.2 htstarT⟩ x).inv.isHermitian.apply c d
        simpa using h.symm)
      lamu hlamu (fun b x ξ => hellIu b.1 b.2 x ξ) K₁
      (fun b c d i x => hK₁u b.1 b.2 c d i x)
  -- ## 2. the numerical constants
  set N : ℝ := (n : ℝ) with hNdef
  have hNnn : (0:ℝ) ≤ N := by rw [hNdef]; positivity
  set dlt : ℝ := lamu / (8 * (N * N * N * N * N * CR + 1)) with hdltdef
  have hdltpos : 0 < dlt := by
    rw [hdltdef]; exact div_pos hlamu (by positivity)
  have hdltineq : 2 * (N * N * CR) * dlt * (N * N * N) ≤ lamu / 2 := by
    have h1 : 2 * (N * N * CR) * dlt * (N * N * N)
        = lamu * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1))) := by
      rw [hdltdef]; field_simp; ring
    rw [h1]
    have hnn : (0:ℝ) ≤ N * N * N * N * N * CR := by positivity
    have h2 : N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (N * N * N * N * N * CR + 1))]
      linarith
    have h3 : lamu * (N * N * N * N * N * CR / (4 * (N * N * N * N * N * CR + 1)))
        ≤ lamu * (1 / 4) := mul_le_mul_of_nonneg_left h2 hlamu.le
    linarith [h3]
  set Kk : ℝ := 2 * Cg + 2 * (N * N * CR) * (1 + 1 / (4 * dlt)) * (N * N) with hKkdef
  refine ⟨Kk, ?_, ?_⟩
  · rw [hKkdef]
    have h1 : (0:ℝ) ≤ 2 * (N * N * CR) * (1 + 1 / (4 * dlt)) * (N * N) := by positivity
    linarith
  · -- ## 3. the estimate at a fixed time
    intro t ht
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1.le, lt_trans ht.2 htstarT⟩
    have htI : t ∈ Set.Ico (0:ℝ) tstar := ⟨ht.1.le, ht.2⟩
    -- abbreviations
    set W : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => u t x i j - v t x i j with hWdef
    set P : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x =>
      (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j with hPdef
    set secG : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x =>
      ∑ c : Fin n, ∑ d : Fin n, (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x
      with hsecGdef
    set Rf : Fin n → Fin n → (Fin n → ℝ) → ℂ := fun i j x => P i j x - secG i j x with hRfdef
    set A : (Fin n → ℝ) → ℝ := fun x => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ with hAdef
    set B : (Fin n → ℝ) → ℝ := fun x => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
      ‖pdM c (u t) x i j - pdM c (v t) x i j‖ with hBdef
    set Em : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube, ‖W i j x‖ ^ 2 with hEmdef
    set Gr : ℝ := ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
      ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2 with hGrdef
    set IAB : ℝ := ∫ x in unitCube, (A x + B x) * A x with hIABdef
    have hmeas : MeasurableSet (unitCube (ι := Fin n)) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioc)
    -- smoothness / continuity of the slices
    have hWd : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (W i j) := by
      intro i j
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
          (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j - v p.1 p.2 i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
        (contDiffOn_entry_of_contDiffOn hu.1 i j).sub
          (contDiffOn_entry_of_contDiffOn hv.1 i j)
      have hs := contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j - v τ y i j) h1 htT
      have heq : W i j = fun y : Fin n → ℝ => u t y i j - v t y i j := by
        funext x; simp only [hWdef]
      rw [heq]; exact hs
    have hsliceu : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => u t x i j) :=
      fun i j => contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) htT
    have hslicev : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => v t x i j) :=
      fun i j => contDiff_slice_of_contDiffOn (F := fun τ y => v τ y i j)
        (contDiffOn_entry_of_contDiffOn hv.1 i j) htT
    have hpdWd1 : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (W i j) x) :=
      fun c i j => contDiff_pd (hWd i j) c
    have hpdWd2 : ∀ (c d i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd c (pd d (W i j)) x) :=
      fun c d i j => contDiff_pd (contDiff_pd (hWd i j) d) c
    have hpdu : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pdM c (u t) x i j) := by
      intro c i j
      have h := contDiff_slice_of_contDiffOn
        (F := fun τ y => pd c (fun z : Fin n → ℝ => u τ z i j) y)
        (contDiffOn_pd_slice (F := fun τ y => u τ y i j)
          (contDiffOn_entry_of_contDiffOn hu.1 i j) c) htT
      simpa only [pdM] using h
    have hpdv : ∀ (c i j : Fin n),
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pdM c (v t) x i j) := by
      intro c i j
      have h := contDiff_slice_of_contDiffOn
        (F := fun τ y => pd c (fun z : Fin n → ℝ => v τ z i j) y)
        (contDiffOn_pd_slice (F := fun τ y => v τ y i j)
          (contDiffOn_entry_of_contDiffOn hv.1 i j) c) htT
      simpa only [pdM] using h
    have hWcont : ∀ i j, Continuous (W i j) := fun i j => (hWd i j).continuous
    have hAcont : Continuous A := by
      have hAeq : A = fun x : Fin n → ℝ => ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ := by
        funext x; simp only [hAdef]
      rw [hAeq]
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (hWcont i j).norm
    have hBcont : Continuous B := by
      have hBeq : B = fun x : Fin n → ℝ => ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ‖pdM c (u t) x i j - pdM c (v t) x i j‖ := by
        funext x; simp only [hBdef]
      rw [hBeq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun i _ =>
        continuous_finsetSum _ (fun j _ => ?_)))
      exact (((hpdu c i j).continuous).sub ((hpdv c i j).continuous)).norm
    have hPcont : ∀ i j, Continuous (P i j) := by
      intro i j
      have h := tj_tj_continuous_slice_PhiDiff_aux Φ hshape u v hu hv hellu hellv htT i j
      have hPeq : P i j = fun x : Fin n → ℝ =>
          (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j := by
        funext x; simp only [hPdef]
      rw [hPeq]; exact h
    have hsecGcont : ∀ i j, Continuous (secG i j) := by
      intro i j
      have hseq : secG i j = fun x : Fin n → ℝ =>
          ∑ c : Fin n, ∑ d : Fin n,
            (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
        funext x; simp only [hsecGdef]
      rw [hseq]
      refine continuous_finsetSum _ (fun c _ => continuous_finsetSum _ (fun d _ => ?_))
      refine Continuous.mul ?_ ?_
      · refine Complex.continuous_ofReal.comp ?_
        exact (contDiff_slice_of_contDiffOn_real
          (F := fun τ y => ((reMat (u τ y))⁻¹) c d) (hinvu c d) htT).continuous
      · exact (hpdWd2 c d i j).continuous
    have hRfcont : ∀ i j, Continuous (Rf i j) := by
      intro i j
      have hReq : Rf i j = fun x : Fin n → ℝ => P i j x - secG i j x := by
        funext x; simp only [hRfdef]
      rw [hReq]
      exact (hPcont i j).sub (hsecGcont i j)
    -- ## 3a. the Gårding sum
    have hgard_sum : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
        ≤ -lamu * Gr + 2 * Cg * Em := by
      have hpt : ∀ i j : Fin n, 2 * L2re (secG i j) (W i j)
          ≤ -(lamu * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
            + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2) := by
        intro i j
        have hsm : ContDiff ℝ 2 (W i j) := (hWd i j).of_le (by simp)
        have hper : Periodic1 (W i j) := by
          intro k y
          have h1 : u t (y + Pi.single k 1) i j = u t y i j :=
            Periodic1.entry (hu.2.1 t htT) i j k y
          have h2 : v t (y + Pi.single k 1) i j = v t y i j :=
            Periodic1.entry (hv.2.1 t htT) i j k y
          show W i j (y + Pi.single k 1) = W i j y
          simp only [hWdef]
          rw [h1, h2]
        have h := hgard ⟨t, htI⟩ (W i j) hsm hper
        have hseq : secG i j = fun x : Fin n → ℝ =>
            ∑ c : Fin n, ∑ d : Fin n,
              (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
          funext x; simp only [hsecGdef]
        rw [hseq]
        linarith [h]
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          ≤ ∑ i : Fin n, ∑ j : Fin n,
              (-(lamu * (∑ c : Fin n, ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2))
                + 2 * Cg * (∫ x in unitCube, ‖W i j x‖ ^ 2)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
        _ = -lamu * Gr + 2 * Cg * Em := by
            rw [hGrdef, hEmdef]
            simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum, neg_mul]
    -- ## 3b. the residual
    have hsecPeq : ∀ i j x, secG i j x
        = secOpFlat (u t x)
            (fun c d => pdM c (pdM d (u t)) x - pdM c (pdM d (v t)) x) i j := by
      intro i j x
      have hpdW : ∀ (c d : Fin n), pd c (pd d (W i j)) x
          = pdM c (pdM d (u t)) x i j - pdM c (pdM d (v t)) x i j := by
        intro c d
        have h := congrFun (pd_pd_sub_fun c d
          (contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
            (contDiffOn_entry_of_contDiffOn hu.1 i j) htT)
          (contDiff_slice_of_contDiffOn (F := fun τ y => v τ y i j)
            (contDiffOn_entry_of_contDiffOn hv.1 i j) htT)) x
        simpa only [hWdef, pdM] using h
      have hseq : secG i j x = ∑ c : Fin n, ∑ d : Fin n,
          (((reMat (u t x))⁻¹) c d : ℂ) * pd c (pd d (W i j)) x := by
        simp only [hsecGdef]
      rw [hseq]
      simp only [secOpFlat, Pi.sub_apply]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
      rw [hpdW c d]
    have hPeq : ∀ i j, P i j = fun x => secG i j x + Rf i j x := by
      intro i j
      funext x
      have hRfeq : Rf i j x = P i j x - secG i j x := by simp only [hRfdef]
      rw [hRfeq]; ring
    have hRpt : ∀ i j x, x ∈ unitCube (ι := Fin n) →
        ‖Rf i j x‖ ≤ CR * (A x + B x) := by
      intro i j x hx
      have hxIcc : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) :=
        fun k _ => ⟨le_of_lt (Set.mem_pi.mp hx k (Set.mem_univ k)).1,
          (Set.mem_pi.mp hx k (Set.mem_univ k)).2⟩
      have hresx := hres t htI x hxIcc
      have hmati : (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x) -
            secOpFlat (u t x)
              (fun c d => pdM c (pdM d (u t)) x - pdM c (pdM d (v t)) x)) i j
          = Rf i j x := by
        have hthis : Rf i j x = (Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j
            - secG i j x := by
          simp only [hRfdef, hPdef]
        rw [hthis, hsecPeq i j x]
        simp only [Pi.sub_apply]
      rw [← hmati]
      refine le_trans (norm_entry_le_norm_matC _ i j) ?_
      have hAeq : (∑ i : Fin n, ∑ j : Fin n, ‖u t x i j - v t x i j‖) = A x := by
        simp only [hAdef, hWdef]
      have hBeq : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖pdM c (u t) x i j - pdM c (v t) x i j‖) = B x := by
        simp only [hBdef]
      rw [hAeq, hBeq] at hresx
      exact hresx
    have hRsum : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j))
        ≤ 2 * (N * N * CR) * IAB := by
      have hkey : ∀ i j : Fin n, 2 * L2re (Rf i j) (W i j) ≤ 2 * (CR * IAB) := by
        intro i j
        have h1 : L2re (Rf i j) (W i j) ≤ ∫ x in unitCube, ‖Rf i j x‖ * ‖W i j x‖ :=
          tj_L2re_le_integral_norm_mul _ _
        have h2 : (∫ x in unitCube, ‖Rf i j x‖ * ‖W i j x‖)
            ≤ ∫ x in unitCube, CR * (A x + B x) * A x := by
          refine setIntegral_mono_on
            (integrableOn_unitCube_of_continuous_real ((hRfcont i j).norm.mul (hWcont i j).norm))
            (integrableOn_unitCube_of_continuous_real
              ((continuous_const.mul (hAcont.add hBcont)).mul hAcont))
            hmeas (fun x hx => ?_)
          have hRx := hRpt i j x hx
          have hWx : ‖W i j x‖ ≤ A x := by
            have h1 : ‖W i j x‖ ≤ ∑ j' : Fin n, ‖W i j' x‖ :=
              single_le_sum_univ (f := fun j' : Fin n => ‖W i j' x‖) (fun j' => norm_nonneg _) j
            have h2 : (∑ j' : Fin n, ‖W i j' x‖)
                ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ :=
              single_le_sum_univ (f := fun i' : Fin n => ∑ j' : Fin n, ‖W i' j' x‖)
                (fun i' => Finset.sum_nonneg (fun j' _ => norm_nonneg _)) i
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            exact le_trans h1 h2
          have hA0 : 0 ≤ A x := by
            have hAeq : A x = ∑ i' : Fin n, ∑ j' : Fin n, ‖W i' j' x‖ := by
              simp only [hAdef]
            rw [hAeq]
            exact Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun j' _ => norm_nonneg _))
          have hB0 : 0 ≤ B x := by
            have hBeq : B x = ∑ c : Fin n, ∑ i' : Fin n, ∑ j' : Fin n,
                ‖pdM c (u t) x i' j' - pdM c (v t) x i' j'‖ := by
              simp only [hBdef]
            rw [hBeq]
            exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun i' _ =>
              Finset.sum_nonneg (fun j' _ => norm_nonneg _)))
          have hCRAB : 0 ≤ CR * (A x + B x) := mul_nonneg hCR (by linarith)
          calc ‖Rf i j x‖ * ‖W i j x‖
              ≤ (CR * (A x + B x)) * A x := mul_le_mul hRx hWx (norm_nonneg _) hCRAB
            _ = CR * (A x + B x) * A x := by ring
        have h3 : (∫ x in unitCube, CR * (A x + B x) * A x) = CR * IAB := by
          rw [hIABdef]
          rw [show (fun x : Fin n → ℝ => CR * (A x + B x) * A x)
              = fun x => CR * ((A x + B x) * A x) from funext (fun x => by ring)]
          rw [integral_const_mul]
        linarith [h1, h2, h3]
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j))
          ≤ ∑ i : Fin n, ∑ j : Fin n, 2 * (CR * IAB) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hkey i j))
        _ = 2 * (N * N * CR) * IAB := by
            rw [sum_sum_const (n := n), hNdef]
            ring
    -- ## 3c. the pointwise Cauchy-Schwarz bounds and the Young inequality
    have hEcont : Continuous (fun x : Fin n → ℝ =>
        ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) := by
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (hWcont i j).norm.pow 2
    have hGcont : Continuous (fun x : Fin n → ℝ =>
        ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2) := by
      refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        continuous_finsetSum _ (fun c _ => ?_)))
      exact (hpdWd1 c i j).continuous.norm.pow 2
    have hcard : (Fintype.card (Fin n) : ℝ) = N := by rw [Fintype.card_fin, hNdef]
    have hA2pt : ∀ x, A x ^ 2 ≤ N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := by
      intro x
      have h1 : (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2 := by
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin n => ∑ j : Fin n, ‖W i j x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h2 : ∀ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ j : Fin n, ‖W i j x‖ ^ 2 := by
        intro i
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin n => ‖W i j x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have hAeq : A x = ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ := by simp only [hAdef]
      rw [hAeq]
      calc (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖W i j x‖) ^ 2 := h1
        _ ≤ N * ∑ i : Fin n, (N * ∑ j : Fin n, ‖W i j x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h2 i)) hNnn
        _ = N * (N * ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) := by
            simp only [Finset.mul_sum]
    have hB2pt : ∀ x, B x ^ 2
        ≤ N * (N * (N * ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
            ‖pd c (W i j) x‖ ^ 2)) := by
      intro x
      have hcomm : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖ ^ 2)
          = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
      have hpd : ∀ (c i j : Fin n), ‖pdM c (u t) x i j - pdM c (v t) x i j‖
          = ‖pd c (W i j) x‖ := by
        intro c i j
        have hdu : Differentiable ℝ (fun y : Fin n → ℝ => u t y i j) :=
          (hsliceu i j).differentiable (by simp)
        have hdv : Differentiable ℝ (fun y : Fin n → ℝ => v t y i j) :=
          (hslicev i j).differentiable (by simp)
        have h := congrFun (pd_sub_fun c hdu hdv) x
        have h2 : pdM c (u t) x i j - pdM c (v t) x i j
            = pd c (fun y : Fin n → ℝ => u t y i j - v t y i j) x := by
          simpa only [pdM] using h.symm
        have h3 : pd c (W i j) x = pd c (fun y : Fin n → ℝ => u t y i j - v t y i j) x := by
          simp only [hWdef]
        rw [h2, h3]
      have h1 : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := by
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun c : Fin n => ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h2 : ∀ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ i : Fin n, (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := by
        intro c
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun i : Fin n => ∑ j : Fin n, ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have h3 : ∀ (c i : Fin n), (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ j : Fin n, ‖pd c (W i j) x‖ ^ 2 := by
        intro c i
        have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
          (f := fun j : Fin n => ‖pd c (W i j) x‖)
        rw [Finset.card_univ, hcard] at hh
        exact hh
      have hBeq : B x = ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖ := by
        rw [hBdef]
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun j _ => hpd c i j)))
      rw [hBeq]
      calc (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2
          ≤ N * ∑ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2 := h1
        _ ≤ N * ∑ c : Fin n, (N * ∑ i : Fin n, (∑ j : Fin n, ‖pd c (W i j) x‖) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => h2 c)) hNnn
        _ ≤ N * ∑ c : Fin n, (N * ∑ i : Fin n, (N * ∑ j : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) hNnn
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h3 c i)) hNnn
        _ = N * (N * (N * ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            simp only [Finset.mul_sum]
        _ = N * (N * (N * ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2)) := by
            rw [hcomm]
    have hIntW : ∀ i j : Fin n, Integrable (fun x : Fin n → ℝ => ‖W i j x‖ ^ 2)
        (volume.restrict (unitCube (ι := Fin n))) :=
      fun i j => integrableOn_unitCube_of_continuous_real ((hWcont i j).norm.pow 2)
    have hIntpdW : ∀ (c i j : Fin n),
        Integrable (fun x : Fin n → ℝ => ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) :=
      fun c i j => integrableOn_unitCube_of_continuous_real ((hpdWd1 c i j).continuous.norm.pow 2)
    have hEint : (∫ x in unitCube, ∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2) = Em := by
      rw [hEmdef]
      have hI1 : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => ∑ j : Fin n, ‖W i j x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun i =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun j _ => (hWcont i j).norm.pow 2))
      rw [integral_finset_sum Finset.univ (fun i _ => hI1 i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finset_sum Finset.univ (fun j _ => hIntW i j)]
    have hGrint : (∫ x in unitCube, ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
        ‖pd c (W i j) x‖ ^ 2) = Gr := by
      rw [hGrdef]
      have hI1 : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ =>
          ∑ j : Fin n, ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun i =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun j _ =>
            continuous_finsetSum Finset.univ (fun c _ => (hpdWd1 c i j).continuous.norm.pow 2)))
      rw [integral_finset_sum Finset.univ (fun i _ => hI1 i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hI2 : ∀ j : Fin n, Integrable (fun x : Fin n → ℝ =>
          ∑ c : Fin n, ‖pd c (W i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := fun j =>
        integrableOn_unitCube_of_continuous_real
          (continuous_finsetSum Finset.univ (fun c _ => (hpdWd1 c i j).continuous.norm.pow 2))
      rw [integral_finset_sum Finset.univ (fun j _ => hI2 j)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_finset_sum Finset.univ (fun c _ => hIntpdW c i j)]
    have hA2int : (∫ x in unitCube, A x ^ 2) ≤ N * (N * Em) := by
      have hstep : (∫ x in unitCube, A x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := by
        refine setIntegral_mono_on (integrableOn_unitCube_of_continuous_real (hAcont.pow 2))
          (integrableOn_unitCube_of_continuous_real
            (continuous_const.mul (continuous_const.mul hEcont))) hmeas
          (fun x _ => hA2pt x)
      calc (∫ x in unitCube, A x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (∑ i : Fin n, ∑ j : Fin n, ‖W i j x‖ ^ 2)) := hstep
        _ = N * (N * Em) := by
            rw [integral_const_mul, integral_const_mul, hEint]
    have hB2int : (∫ x in unitCube, B x ^ 2) ≤ N * (N * (N * Gr)) := by
      have hstep : (∫ x in unitCube, B x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (N * (∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2))) := by
        refine setIntegral_mono_on (integrableOn_unitCube_of_continuous_real (hBcont.pow 2))
          (integrableOn_unitCube_of_continuous_real
            (continuous_const.mul (continuous_const.mul (continuous_const.mul hGcont))))
          hmeas (fun x _ => hB2pt x)
      calc (∫ x in unitCube, B x ^ 2)
          ≤ ∫ x in unitCube, N * (N * (N * (∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
              ‖pd c (W i j) x‖ ^ 2))) := hstep
        _ = N * (N * (N * Gr)) := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul, hGrint]
    have hYoung : ∀ x, A x * B x ≤ A x ^ 2 / (4 * dlt) + dlt * B x ^ 2 := by
      intro x
      have h1 : 0 < 4 * dlt := by linarith [hdltpos]
      have h2 : 4 * dlt * (A x * B x) ≤ A x ^ 2 + 4 * dlt * (dlt * B x ^ 2) := by
        nlinarith [sq_nonneg (A x - 2 * dlt * B x)]
      calc A x * B x ≤ (A x ^ 2 + 4 * dlt * (dlt * B x ^ 2)) / (4 * dlt) :=
            (le_div_iff₀ h1).mpr (by nlinarith [h2])
        _ = A x ^ 2 / (4 * dlt) + dlt * B x ^ 2 := by
            have hne : (4 * dlt) ≠ 0 := ne_of_gt h1
            field_simp
    have hAB_int : IAB ≤ (1 + 1 / (4 * dlt)) * (N * (N * Em))
        + dlt * (N * (N * (N * Gr))) := by
      rw [hIABdef]
      have hpt : ∀ x, (A x + B x) * A x
          ≤ (1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2 := by
        intro x
        have h1 : (A x + B x) * A x = A x ^ 2 + A x * B x := by ring
        rw [h1]
        have h2 : (1 + 1 / (4 * dlt)) * A x ^ 2 = A x ^ 2 + A x ^ 2 / (4 * dlt) := by
          have hne : (4 * dlt) ≠ 0 := ne_of_gt (by linarith [hdltpos])
          field_simp
        rw [h2]
        linarith [hYoung x]
      have hstep : (∫ x in unitCube, (A x + B x) * A x)
          ≤ ∫ x in unitCube, ((1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2) := by
        refine setIntegral_mono_on
          (integrableOn_unitCube_of_continuous_real ((hAcont.add hBcont).mul hAcont))
          (integrableOn_unitCube_of_continuous_real
            ((continuous_const.mul (hAcont.pow 2)).add (continuous_const.mul (hBcont.pow 2))))
          hmeas (fun x _ => hpt x)
      have hsplit : (∫ x in unitCube, ((1 + 1 / (4 * dlt)) * A x ^ 2 + dlt * B x ^ 2))
          = (1 + 1 / (4 * dlt)) * (∫ x in unitCube, A x ^ 2)
            + dlt * (∫ x in unitCube, B x ^ 2) := by
        rw [integral_add
            (f := fun x : Fin n → ℝ => (1 + 1 / (4 * dlt)) * A x ^ 2)
            (g := fun x : Fin n → ℝ => dlt * B x ^ 2)
            (integrableOn_unitCube_of_continuous_real (continuous_const.mul (hAcont.pow 2)))
            (integrableOn_unitCube_of_continuous_real (continuous_const.mul (hBcont.pow 2))),
          integral_const_mul, integral_const_mul]
      rw [hsplit] at hstep
      have h3 : (1 + 1 / (4 * dlt)) * (∫ x in unitCube, A x ^ 2)
          ≤ (1 + 1 / (4 * dlt)) * (N * (N * Em)) :=
        mul_le_mul_of_nonneg_left hA2int (by positivity)
      have h4 : dlt * (∫ x in unitCube, B x ^ 2) ≤ dlt * (N * (N * (N * Gr))) :=
        mul_le_mul_of_nonneg_left hB2int hdltpos.le
      linarith [hstep, h3, h4]
    -- ## 3d. assembly
    have hsplit2 : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j))
        = (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (secG i j) (W i j))
          + (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (Rf i j) (W i j)) := by
      have h1 : ∀ i j : Fin n, 2 * L2re (P i j) (W i j)
          = 2 * L2re (secG i j) (W i j) + 2 * L2re (Rf i j) (W i j) := by
        intro i j
        have hint1 : Integrable (fun x : Fin n → ℝ => secG i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hsecGcont i j).mul (hWcont i j).star)
        have hint2 : Integrable (fun x : Fin n → ℝ => Rf i j x * star (W i j x))
            (volume.restrict (unitCube (ι := Fin n))) :=
          integrableOn_unitCube_of_continuous ((hRfcont i j).mul (hWcont i j).star)
        have hadd := tj_L2re_add_slice (f₁ := secG i j) (f₂ := Rf i j) (g := W i j) hint1 hint2
        rw [hPeq i j, hadd]
        ring
      calc (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j))
          = ∑ i : Fin n, ∑ j : Fin n, (2 * L2re (secG i j) (W i j)
              + 2 * L2re (Rf i j) (W i j)) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h1 i j))
        _ = _ := by simp only [Finset.sum_add_distrib]
    have hmain : (∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j)) ≤ Kk * Em := by
      rw [hsplit2]
      have hGrnn : 0 ≤ Gr := by
        have hGeq : Gr = ∑ i : Fin n, ∑ j : Fin n, ∑ c : Fin n,
            ∫ x in unitCube, ‖pd c (W i j) x‖ ^ 2 := hGrdef
        rw [hGeq]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
          Finset.sum_nonneg (fun c _ => integral_nonneg (fun x => by positivity))))
      have hstep : 2 * (N * N * CR) * IAB
          ≤ 2 * (N * N * CR) * ((1 + 1 / (4 * dlt)) * (N * (N * Em))
              + dlt * (N * (N * (N * Gr)))) :=
        mul_le_mul_of_nonneg_left hAB_int (by positivity)
      nlinarith [hgard_sum, hRsum, hstep, hGrnn, hdltineq, hKkdef, hNnn]
    -- ## 3e. identification with the goal
    have hconv : ∀ i j : Fin n,
        (∫ x in unitCube, (((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j)
          * star (u t x i j - v t x i j)).re) = L2re (P i j) (W i j) := by
      intro i j
      have heq : (fun x : Fin n → ℝ => (((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j)
            * star (u t x i j - v t x i j)).re)
          = fun x => (P i j x * star (W i j x)).re := by
        funext x; simp only [hPdef, hWdef]
      rw [heq]
      have hint : Integrable (fun x : Fin n → ℝ => P i j x * star (W i j x))
          (volume.restrict (unitCube (ι := Fin n))) :=
        integrableOn_unitCube_of_continuous ((hPcont i j).mul (hWcont i j).star)
      have h := ContinuousLinearMap.integral_comp_comm Complex.reCLM hint
      simpa only [L2re, Complex.reCLM_apply] using h
    have hEmeq : Em = ∑ i : Fin n, ∑ j : Fin n,
        ∫ x in unitCube, ‖u t x i j - v t x i j‖ ^ 2 := by
      simp only [hEmdef, hWdef]
    calc (∑ i : Fin n, ∑ j : Fin n, 2 * ∫ x in unitCube,
          ((Φ (x, jetM (u t) x) - Φ (x, jetM (v t) x)) i j
            * star (u t x i j - v t x i j)).re)
        = ∑ i : Fin n, ∑ j : Fin n, 2 * L2re (P i j) (W i j) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hconv i j]
      _ ≤ Kk * Em := hmain
      _ = Kk * (∑ i : Fin n, ∑ j : Fin n, ∫ x in unitCube,
            ‖u t x i j - v t x i j‖ ^ 2) := by rw [hEmeq]


theorem torus_uniqueness {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (T : ℝ) (u v : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u) (hv : Work.Diff.STE.Flat.SolvesOn Φ T v)
    (hellu : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (u t x))
    (hellv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, Work.Diff.STE.Flat.PosDefM (v t x))
    (h0 : u 0 = v 0) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, u t = v t := by
  intro t₀ ht₀
  have ht₀T : t₀ < T := ht₀.2
  have ht₀nn : 0 ≤ t₀ := ht₀.1
  set tstar : ℝ := (t₀ + T) / 2 with htstardef
  have htstar0 : 0 ≤ tstar := by rw [htstardef]; linarith
  have htstarT : tstar < T := by rw [htstardef]; linarith
  have ht₀tstar : t₀ < tstar := by rw [htstardef]; linarith
  -- ## 1. uniform bounds for the two solutions
  obtain ⟨Mu, lamu, K₁u, hlamu, hMu, hbu, hellMu, hellIu, hK₁u⟩ :=
    sol_bounds hn Φ u hu hellu htstar0 htstarT
  obtain ⟨Mv, lamv, K₁v, hlamv, hMv, hbv, hellMv, hellIv, hK₁v⟩ :=
    sol_bounds hn Φ v hv hellv htstar0 htstarT
  have hMnn : 0 ≤ Mu + Mv := by linarith
  have hlam : 0 < min lamu lamv := lt_min hlamu hlamv
  -- ## 2. the Lipschitz bound for the residual
  obtain ⟨CR, hCR, hres⟩ := nDiff_bound hn Φ hshape (min lamu lamv) hlam (Mu + Mv) hMnn
  -- ## 3. the energy and its derivative
  set E : ℝ → ℝ := fun s => ∑ i : Fin n, ∑ j : Fin n,
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u s x i j - v s x i j‖ ^ 2 with hEdef
  set Ed : ℝ → ℝ := fun t => ∑ i : Fin n, ∑ j : Fin n, 2 *
      ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
        ((Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x)) i j
          * star (u t x i j - v t x i j)).re with hEddef
  -- ## 4. the pointwise residual bound on the closed cube
  have hresid : ∀ (t : ℝ), t ∈ Set.Ico (0:ℝ) tstar → ∀ x : Fin n → ℝ,
      (∀ i : Fin n, x i ∈ Set.Icc (0:ℝ) 1) →
      ‖Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x)
          - Work.Diff.STE.Flat.secOpFlat (u t x)
              (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u t)) x
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v t)) x)‖
        ≤ CR * ((∑ i : Fin n, ∑ j : Fin n, ‖u t x i j - v t x i j‖)
          + (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖Work.Diff.STE.Flat.pdM c (u t) x i j - Work.Diff.STE.Flat.pdM c (v t) x i j‖)) := by
    intro t ht x hx
    have htT : t ∈ Set.Ico (0:ℝ) T := ⟨ht.1, lt_trans ht.2 htstarT⟩
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbu t ht x (fun i _ => hx i)
    obtain ⟨hb1', hb2', hb3', hb4'⟩ := hbv t ht x (fun i _ => hx i)
    have hell1 : ∀ ξ : Fin n → ℝ, min lamu lamv * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j := fun ξ =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (hellMu t ht x ξ)
    have hell2 : ∀ ξ : Fin n → ℝ, min lamu lamv * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (v t x) i j * ξ i * ξ j := fun ξ =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (hellMv t ht x ξ)
    have hmain := hres x hx (Work.Diff.STE.Flat.jetM (u t) x) (Work.Diff.STE.Flat.jetM (v t) x)
      (hellu t htT x) (hellv t htT x) hell1 hell2
      (fun i j => le_trans (hb1 i j) (by linarith))
      (fun i j => le_trans (hb1' i j) (by linarith))
      (fun i j => le_trans (hb4 i j) (by linarith))
      (fun i j => le_trans (hb4' i j) (by linarith))
      (fun c i j => le_trans (hb2 c i j) (by linarith))
      (fun c i j => le_trans (hb2' c i j) (by linarith))
      (fun c d i j => le_trans (hb3 c d i j) (by linarith))
      (fun c d i j => le_trans (hb3' c d i j) (by linarith))
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hCR)
    exact add_le_add (norm_le_sum_norm_matC _) (norm_le_sum_norm_pi_matC _)
  -- ## 5. the derivative of the energy
  have hderiv : ∀ t ∈ Set.Ioo (0:ℝ) tstar, HasDerivAt E (Ed t) t := by
    intro t ht
    have htT : t ∈ Set.Ioo (0:ℝ) T := ⟨ht.1, lt_trans ht.2 htstarT⟩
    have hentry : ∀ i j : Fin n, HasDerivAt
        (fun s => ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u s x i j - v s x i j‖ ^ 2)
        (2 * ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ((Φ (x, Work.Diff.STE.Flat.jetM (u t) x) - Φ (x, Work.Diff.STE.Flat.jetM (v t) x)) i j
            * star (u t x i j - v t x i j)).re) t := by
      intro i j
      have hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := contDiffOn_entry_of_contDiffOn hu.1 i j
      have hv' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2 i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := contDiffOn_entry_of_contDiffOn hv.1 i j
      have hWc : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2 i j - v p.1 p.2 i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := hu'.continuousOn.sub hv'.continuousOn
      have hjetu : ContinuousOn
          (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.jetM (u p.1) p.2)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
        have h0 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := hu.1.continuousOn
        have h1 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
            fun c : Fin n => Work.Diff.STE.Flat.pdM c (u p.1) p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
          refine continuousOn_pi.mpr (fun c => continuousOn_pi.mpr (fun i =>
            continuousOn_pi.mpr (fun j => ?_)))
          exact (contDiffOn_pd_slice (F := fun s y => u s y i j)
            (contDiffOn_entry_of_contDiffOn hu.1 i j) c).continuousOn
        have h2 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
            fun c d : Fin n => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u p.1)) p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
          refine continuousOn_pi.mpr (fun c => continuousOn_pi.mpr (fun d =>
            continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j => ?_))))
          exact (contDiffOn_pd_slice (F := fun s y => Work.Diff.STE.Flat.pdM d (u s) y i j)
            (contDiffOn_pd_slice (F := fun s y => u s y i j)
              (contDiffOn_entry_of_contDiffOn hu.1 i j) d) c).continuousOn
        simpa only [Work.Diff.STE.Flat.jetM] using h0.prodMk (h1.prodMk h2)
      have hjetv : ContinuousOn
          (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.jetM (v p.1) p.2)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
        have h0 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := hv.1.continuousOn
        have h1 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
            fun c : Fin n => Work.Diff.STE.Flat.pdM c (v p.1) p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
          refine continuousOn_pi.mpr (fun c => continuousOn_pi.mpr (fun i =>
            continuousOn_pi.mpr (fun j => ?_)))
          exact (contDiffOn_pd_slice (F := fun s y => v s y i j)
            (contDiffOn_entry_of_contDiffOn hv.1 i j) c).continuousOn
        have h2 : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
            fun c d : Fin n => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v p.1)) p.2)
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
          refine continuousOn_pi.mpr (fun c => continuousOn_pi.mpr (fun d =>
            continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (fun j => ?_))))
          exact (contDiffOn_pd_slice (F := fun s y => Work.Diff.STE.Flat.pdM d (v s) y i j)
            (contDiffOn_pd_slice (F := fun s y => v s y i j)
              (contDiffOn_entry_of_contDiffOn hv.1 i j) d) c).continuousOn
        simpa only [Work.Diff.STE.Flat.jetM] using h0.prodMk (h1.prodMk h2)
      have hW'c : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
          (Φ (p.2, Work.Diff.STE.Flat.jetM (u p.1) p.2)
            - Φ (p.2, Work.Diff.STE.Flat.jetM (v p.1) p.2)) i j)
          (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
        obtain ⟨hΦsm, -, -, -⟩ := hshape
        have hmap : Set.MapsTo (fun p : ℝ × (Fin n → ℝ) =>
            (p.2, Work.Diff.STE.Flat.jetM (u p.1) p.2))
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n |
              (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}) :=
          fun p hp => ⟨Set.mem_univ _, (Matrix.PosDef.det_pos (hellu p.1 hp.1 p.2)).ne'⟩
        have hcomp := hΦsm.continuousOn.comp (continuousOn_snd.prodMk hjetu) hmap
        have hentry' : Continuous (fun z : Work.Diff.STE.Flat.MatC n => z i j) :=
          (continuous_apply j).comp (continuous_apply i)
        refine (hentry'.comp_continuousOn hcomp).sub ?_
        have hmap2 : Set.MapsTo (fun p : ℝ × (Fin n → ℝ) =>
            (p.2, Work.Diff.STE.Flat.jetM (v p.1) p.2))
            (Set.Ico (0:ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ {w : Work.Diff.STE.Flat.Jet n |
              (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}) :=
          fun p hp => ⟨Set.mem_univ _, (Matrix.PosDef.det_pos (hellv p.1 hp.1 p.2)).ne'⟩
        have hcomp2 := hΦsm.continuousOn.comp (continuousOn_snd.prodMk hjetv) hmap2
        simpa only [Function.comp_def, Pi.sub_apply] using hentry'.comp_continuousOn hcomp2
      have hd : ∀ s ∈ Set.Ico (0:ℝ) T, ∀ x,
          HasDerivWithinAt (fun r => u r x i j - v r x i j)
            ((Φ (x, Work.Diff.STE.Flat.jetM (u s) x) - Φ (x, Work.Diff.STE.Flat.jetM (v s) x)) i j)
            (Set.Ico (0:ℝ) T) s := by
        intro s hs x
        have h3 := (hu.2.2 s hs x).sub (hv.2.2 s hs x)
        have h4 := hasDerivWithinAt_pi.mp h3 i
        have h5 := hasDerivWithinAt_pi.mp h4 j
        simpa only [Pi.sub_apply] using h5
      exact hasDerivAt_integral_normSq_slice (n := n) hn
        (W := fun r x => u r x i j - v r x i j)
        (W' := fun r x =>
          (Φ (x, Work.Diff.STE.Flat.jetM (u r) x) - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j)
        T hWc hW'c hd htT
    have hsum : HasDerivAt E (Ed t) t := by
      have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
        HasDerivAt.sum (u := Finset.univ) (fun j _ => hentry i j))
      have hfun : (∑ i : Fin n, ∑ j : Fin n,
          fun s => ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u s x i j - v s x i j‖ ^ 2)
            = fun s => ∑ i : Fin n, ∑ j : Fin n,
              ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u s x i j - v s x i j‖ ^ 2 := by
        funext s
        simp only [Finset.sum_apply]
      rw [hfun] at h
      exact h
    exact hsum
  -- ## 6. the differential inequality
  have hineq : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Ioo (0:ℝ) tstar, Ed t ≤ K * E t :=
    tj_uniqueness_energy_ineq hn Φ hshape (tstar := tstar) u v hu hv hellu hellv
      htstarT (Mu + Mv) (min lamu lamv) K₁u CR hMnn (lt_min hlamu hlamv) hCR
      (fun t ht x hx => ⟨(fun i j => le_trans ((hbu t ht x hx).1 i j) (by linarith)),
        (fun c i j => le_trans ((hbu t ht x hx).2.1 c i j) (by linarith)),
        (fun c d i j => le_trans ((hbu t ht x hx).2.2.1 c d i j) (by linarith)),
        (fun i j => le_trans ((hbu t ht x hx).2.2.2 i j) (by linarith))⟩)
      (fun t ht x hx => ⟨(fun i j => le_trans ((hbv t ht x hx).1 i j) (by linarith)),
        (fun c i j => le_trans ((hbv t ht x hx).2.1 c i j) (by linarith)),
        (fun c d i j => le_trans ((hbv t ht x hx).2.2.1 c d i j) (by linarith)),
        (fun i j => le_trans ((hbv t ht x hx).2.2.2 i j) (by linarith))⟩)
      (fun t ht x ξ => le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (hellMu t ht x ξ))
      (fun t ht x ξ => le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (hellMv t ht x ξ))
      (fun t ht x ξ => le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))) (hellIu t ht x ξ))
      hK₁u
      (fun t ht x hx => hresid t ht x (fun i => hx i (Set.mem_univ i)))
  -- ## 7. Grönwall
  obtain ⟨K, hK, hineq'⟩ := hineq
  have hEnn : ∀ s : ℝ, 0 ≤ E s := by
    intro s
    simp only [hEdef]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun x => sq_nonneg _)))
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    have hterm : ∀ i j : Fin n,
        (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u 0 x i j - v 0 x i j‖ ^ 2) = 0 := by
      intro i j
      have hzero : (fun x : Fin n → ℝ => ‖u 0 x i j - v 0 x i j‖ ^ 2) = fun _ => (0 : ℝ) := by
        funext x
        rw [show u 0 x i j - v 0 x i j = 0 from
          sub_eq_zero.mpr (congrFun (congrFun (congrFun h0 x) i) j)]
        simp
      rw [hzero]
      simp
    exact Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => hterm i j))
  -- ## the bound on the difference of the non-linearities
  have hdiffbd : ∀ (r : ℝ), r ∈ Set.Ico (0:ℝ) t₀ → ∀ x : Fin n → ℝ,
      (∀ i : Fin n, x i ∈ Set.Icc (0:ℝ) 1) → ∀ i j : Fin n,
      ‖(Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
          - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j‖
        ≤ CR * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))
            + (n:ℝ) * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))))
          + (n:ℝ) * ((n:ℝ) * ((Mu + Mv) * (2 * (Mu + Mv)))) := by
    intro r hr x hx i j
    have hr' : r ∈ Set.Ico (0:ℝ) tstar := ⟨hr.1, lt_trans hr.2 ht₀tstar⟩
    obtain ⟨ha1, ha2, ha3, ha4⟩ := hbu r hr' x (fun i _ => hx i)
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hbv r hr' x (fun i _ => hx i)
    -- the two sums of differences
    have hA : (∑ i : Fin n, ∑ j : Fin n, ‖u r x i j - v r x i j‖)
        ≤ (n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv))) := by
      have h1 : ∀ i j : Fin n, ‖u r x i j - v r x i j‖ ≤ 2 * (Mu + Mv) := fun i j =>
        le_trans (norm_sub_le _ _) (by linarith [ha1 i j, hb1 i j])
      calc (∑ i : Fin n, ∑ j : Fin n, ‖u r x i j - v r x i j‖)
          ≤ ∑ i : Fin n, ∑ j : Fin n, (2 * (Mu + Mv)) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h1 i j))
        _ = (n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv))) := sum_sum_const _
    have hB : (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        ‖Work.Diff.STE.Flat.pdM c (u r) x i j - Work.Diff.STE.Flat.pdM c (v r) x i j‖)
        ≤ (n:ℝ) * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))) := by
      have h1 : ∀ c i j : Fin n,
          ‖Work.Diff.STE.Flat.pdM c (u r) x i j - Work.Diff.STE.Flat.pdM c (v r) x i j‖
            ≤ 2 * (Mu + Mv) := fun c i j =>
        le_trans (norm_sub_le _ _) (by linarith [ha2 c i j, hb2 c i j])
      have h2 : ∀ c : Fin n, (∑ i : Fin n, ∑ j : Fin n, (2 * (Mu + Mv)))
          = (n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv))) := fun c => sum_sum_const _
      calc (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖Work.Diff.STE.Flat.pdM c (u r) x i j - Work.Diff.STE.Flat.pdM c (v r) x i j‖)
          ≤ ∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n, (2 * (Mu + Mv)) :=
            Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ => h1 c i j)))
        _ = ∑ c : Fin n, (n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv))) :=
            Finset.sum_congr rfl (fun c _ => h2 c)
        _ = (n:ℝ) * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- the principal part
    have hP : ‖(Work.Diff.STE.Flat.secOpFlat (u r x)
        (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
          - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)) i j‖
        ≤ (n:ℝ) * ((n:ℝ) * ((Mu + Mv) * (2 * (Mu + Mv)))) := by
      have hterm : ∀ c d : Fin n,
          ‖(((reMat (u r x))⁻¹) c d : ℂ)
            * (Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x i j
              - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x i j)‖
            ≤ (Mu + Mv) * (2 * (Mu + Mv)) := fun c d => by
        have h1 : |((reMat (u r x))⁻¹) c d| ≤ Mu + Mv := by
          simpa only [Real.norm_eq_abs] using le_trans (ha4 c d) (show Mu ≤ Mu + Mv by linarith)
        have h2 : ‖Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x i j
            - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x i j‖
            ≤ 2 * (Mu + Mv) :=
          le_trans (norm_sub_le _ _) (by linarith [ha3 c d i j, hb3 c d i j])
        rw [norm_mul, norm_ofReal_complex]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
      simp only [Work.Diff.STE.Flat.secOpFlat]
      calc ‖∑ c : Fin n, ∑ d : Fin n, (((reMat (u r x))⁻¹) c d : ℂ)
              * (Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x i j
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x i j)‖
          ≤ ∑ c : Fin n, ∑ d : Fin n, ‖(((reMat (u r x))⁻¹) c d : ℂ)
              * (Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x i j
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x i j)‖ := by
            exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun c _ => norm_sum_le _ _))
        _ ≤ ∑ c : Fin n, ∑ d : Fin n, (Mu + Mv) * (2 * (Mu + Mv)) :=
            Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => hterm c d))
        _ = (n:ℝ) * ((n:ℝ) * ((Mu + Mv) * (2 * (Mu + Mv)))) := by
            rw [sum_sum_const]
    -- combine
    have hmain := hresid r hr' x hx
    have hsplit : ‖(Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
        - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j‖
        ≤ ‖Φ (x, Work.Diff.STE.Flat.jetM (u r) x) - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)
            - Work.Diff.STE.Flat.secOpFlat (u r x)
              (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)‖
          + ‖(Work.Diff.STE.Flat.secOpFlat (u r x)
              (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)) i j‖ := by
      have h1 : (Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
          - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j
          = ((Φ (x, Work.Diff.STE.Flat.jetM (u r) x) - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)
              - Work.Diff.STE.Flat.secOpFlat (u r x)
                (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                  - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x))
            + Work.Diff.STE.Flat.secOpFlat (u r x)
                (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                  - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)) i j := by
        simp only [Pi.add_apply, Pi.sub_apply]
        abel
      rw [h1]
      simp only [Pi.add_apply]
      exact le_trans (norm_add_le _ _) (add_le_add (norm_entry_le_norm_matC _ i j) le_rfl)
    calc ‖(Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
          - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j‖
        ≤ ‖Φ (x, Work.Diff.STE.Flat.jetM (u r) x) - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)
            - Work.Diff.STE.Flat.secOpFlat (u r x)
              (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)‖
          + ‖(Work.Diff.STE.Flat.secOpFlat (u r x)
              (fun c d => Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (u r)) x
                - Work.Diff.STE.Flat.pdM c (Work.Diff.STE.Flat.pdM d (v r)) x)) i j‖ := hsplit
      _ ≤ CR * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))
            + (n:ℝ) * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))))
          + (n:ℝ) * ((n:ℝ) * ((Mu + Mv) * (2 * (Mu + Mv)))) := by
        have h1 : CR * ((∑ i : Fin n, ∑ j : Fin n, ‖u r x i j - v r x i j‖)
            + (∑ c : Fin n, ∑ i : Fin n, ∑ j : Fin n,
                ‖Work.Diff.STE.Flat.pdM c (u r) x i j - Work.Diff.STE.Flat.pdM c (v r) x i j‖))
            ≤ CR * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv)))
              + (n:ℝ) * ((n:ℝ) * ((n:ℝ) * (2 * (Mu + Mv))))) :=
          mul_le_mul_of_nonneg_left (add_le_add hA hB) hCR
        linarith [hmain, h1, hP]
  -- ## continuity of the energy at time zero
  have hcont0 : ContinuousWithinAt E (Set.Icc 0 t₀) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    set N : ℝ := (n:ℝ) with hNdef
    have hNnn : 0 ≤ N := by rw [hNdef]; positivity
    set BL : ℝ := CR * (N * (N * (2 * (Mu + Mv))) + N * (N * (N * (2 * (Mu + Mv)))))
      + N * (N * ((Mu + Mv) * (2 * (Mu + Mv)))) with hBLdef
    have hBLnn : 0 ≤ BL := by
      rw [hBLdef]
      have h1 : (0:ℝ) ≤ N * (N * (2 * (Mu + Mv))) := by positivity
      have h2 : (0:ℝ) ≤ N * (N * (N * (2 * (Mu + Mv)))) := by positivity
      have h3 : (0:ℝ) ≤ N * (N * ((Mu + Mv) * (2 * (Mu + Mv)))) := by positivity
      linarith [mul_nonneg hCR (add_nonneg h1 h2), h3]
    set Cε : ℝ := N * N * BL ^ 2 + 1 with hCεdef
    have hCεpos : 0 < Cε := by rw [hCεdef]; positivity
    refine ⟨min (t₀ + 1) (Real.sqrt (ε / Cε)),
      lt_min (by linarith) (Real.sqrt_pos.mpr (by positivity)), ?_⟩
    intro s hs hsδ
    have hst₀ : s ≤ t₀ := hs.2
    have hmeas : MeasurableSet (Work.Diff.STE.unitCube (ι := Fin n)) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioc)
    have hδ' : s < min (t₀ + 1) (Real.sqrt (ε / Cε)) := by
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hs.1] at hsδ
    have hδ2 : s < Real.sqrt (ε / Cε) := lt_of_lt_of_le hδ' (min_le_right _ _)
    -- the pointwise bound
    have hsT : s ∈ Set.Ico (0:ℝ) T := ⟨hs.1, lt_of_le_of_lt hst₀ (lt_trans ht₀tstar htstarT)⟩
    have hptw : ∀ x : Fin n → ℝ, (∀ i : Fin n, x i ∈ Set.Icc (0:ℝ) 1) → ∀ i j : Fin n,
        ‖u s x i j - v s x i j‖ ≤ BL * s := by
      intro x hx i j
      have hder : ∀ r ∈ Set.Icc (0:ℝ) t₀,
          HasDerivWithinAt (fun ρ : ℝ => u ρ x i j - v ρ x i j)
            ((Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
              - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j) (Set.Icc (0:ℝ) t₀) r := by
        intro r hr
        have hrT : r ∈ Set.Ico (0:ℝ) T := ⟨hr.1, lt_of_le_of_lt hr.2 (lt_trans ht₀tstar htstarT)⟩
        have h3 := (hu.2.2 r hrT x).sub (hv.2.2 r hrT x)
        have h4 := hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp h3 i) j
        exact h4.mono (fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 (lt_trans ht₀tstar htstarT)⟩)
      have hbd : ∀ r ∈ Set.Ico (0:ℝ) t₀,
          ‖(Φ (x, Work.Diff.STE.Flat.jetM (u r) x)
            - Φ (x, Work.Diff.STE.Flat.jetM (v r) x)) i j‖ ≤ BL := by
        intro r hr
        exact hdiffbd r hr x hx i j
      have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun ρ : ℝ => u ρ x i j - v ρ x i j)
        (f' := fun ρ : ℝ => (Φ (x, Work.Diff.STE.Flat.jetM (u ρ) x)
          - Φ (x, Work.Diff.STE.Flat.jetM (v ρ) x)) i j)
        (a := 0) (b := t₀) (C := BL) hder hbd s ⟨hs.1, hst₀⟩
      have h0eq : u 0 x i j - v 0 x i j = 0 :=
        sub_eq_zero.mpr (congrFun (congrFun (congrFun h0 x) i) j)
      rw [h0eq, sub_zero, sub_zero] at hmvt
      exact hmvt
    -- the energy bound
    have hEbd : E s < ε := by
      have h1 : E s ≤ ∑ i : Fin n, ∑ j : Fin n, (BL * s) ^ 2 := by
        simp only [hEdef]
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        have hcontc : Continuous (fun x : Fin n → ℝ => ‖u s x i j - v s x i j‖ ^ 2) := by
          have h1' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => u s x i j) :=
            contDiff_slice_of_contDiffOn (F := fun ρ x => u ρ x i j)
              (contDiffOn_entry_of_contDiffOn hu.1 i j) hsT
          have h2' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => v s x i j) :=
            contDiff_slice_of_contDiffOn (F := fun ρ x => v ρ x i j)
              (contDiffOn_entry_of_contDiffOn hv.1 i j) hsT
          exact (h1'.continuous.sub h2'.continuous).norm.pow 2
        have hvol1 : (volume : Measure (Fin n → ℝ)) (Work.Diff.STE.unitCube (ι := Fin n)) = 1 := by
          rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
          simp
        have hvol : (volume : Measure (Fin n → ℝ)).real
            (Work.Diff.STE.unitCube (ι := Fin n)) = 1 := by
          show (((volume : Measure (Fin n → ℝ))
            (Work.Diff.STE.unitCube (ι := Fin n))).toReal) = 1
          rw [hvol1, ENNReal.toReal_one]
        have hcmp := setIntegral_mono_on (f := fun x : Fin n → ℝ => ‖u s x i j - v s x i j‖ ^ 2)
          (g := fun _ : Fin n → ℝ => (BL * s) ^ 2)
          (Work.Diff.STE.integrableOn_unitCube_of_continuous_real hcontc)
          (Work.Diff.STE.integrableOn_unitCube_of_continuous_real continuous_const)
          hmeas (fun x hx => by
            have hle := hptw x (fun k => ⟨le_of_lt (hx k (Set.mem_univ k)).1,
              (hx k (Set.mem_univ k)).2⟩) i j
            nlinarith [hle, norm_nonneg (u s x i j - v s x i j), mul_nonneg hBLnn hs.1])
        calc (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u s x i j - v s x i j‖ ^ 2)
            ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n), (BL * s) ^ 2 := hcmp
          _ = (BL * s) ^ 2 := by rw [setIntegral_const, hvol, one_smul]
      have h2 : (∑ i : Fin n, ∑ j : Fin n, (BL * s) ^ 2) = N * (N * (BL * s) ^ 2) := by
        rw [sum_sum_const, hNdef]
      have hsnn : 0 ≤ s := hs.1
      have h4 : s ^ 2 < (Real.sqrt (ε / Cε)) ^ 2 := by
        rw [sq_lt_sq, abs_of_nonneg hsnn, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hδ2
      have h5 : s ^ 2 < ε / Cε := by
        rwa [Real.sq_sqrt (by positivity)] at h4
      have hden : 0 < Cε := hCεpos
      have hnum : N * N * BL ^ 2 < Cε := by rw [hCεdef]; linarith
      have h6 : N * N * BL ^ 2 * (ε / Cε) < ε := by
        calc N * N * BL ^ 2 * (ε / Cε) = (N * N * BL ^ 2 / Cε) * ε := by ring
          _ < 1 * ε := by
              refine mul_lt_mul_of_pos_right ?_ hε
              rw [div_lt_one hden]
              exact hnum
          _ = ε := by ring
      have h3 : N * (N * (BL * s) ^ 2) < ε := by
        have hmid : N * (N * (BL * s) ^ 2) = N * N * BL ^ 2 * s ^ 2 := by ring
        rw [hmid]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt h5) (by positivity)) h6
      linarith [h1, h2, h3]
    rw [hE0, Real.dist_eq, sub_zero, abs_of_nonneg (hEnn s)]
    exact hEbd
  have hEcont : ContinuousOn E (Set.Icc 0 t₀) := by
    intro s hs
    by_cases h0s : s = 0
    · rw [h0s]; exact hcont0
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h0s)
      have hslt : s < tstar := lt_of_le_of_lt hs.2 ht₀tstar
      exact ((hderiv s ⟨hspos, hslt⟩).continuousAt).continuousWithinAt
  have hEt₀ : E t₀ = 0 :=
    eq_zero_of_deriv_le (C := K) hEcont
      (fun t ht => (hderiv t ⟨ht.1, lt_trans ht.2 ht₀tstar⟩).hasDerivWithinAt)
      (fun t ht => hineq' t ⟨ht.1, lt_trans ht.2 ht₀tstar⟩)
      (fun t _ => hEnn t) hE0 t₀ ⟨ht₀nn, le_rfl⟩
  -- ## 8. the pointwise conclusion
  have hclosed : ∀ (i j : Fin n) (x : Fin n → ℝ),
      x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) → u t₀ x i j - v t₀ x i j = 0 := by
    intro i j x hx
    have hterm : (∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u t₀ x i j - v t₀ x i j‖ ^ 2) = 0 := by
      have h1 : (∑ i : Fin n, ∑ j : Fin n,
          ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖u t₀ x i j - v t₀ x i j‖ ^ 2) = 0 := hEt₀
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        integral_nonneg (fun x => sq_nonneg _)))).mp h1
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        integral_nonneg (fun x => sq_nonneg _))).mp (h2 i (Finset.mem_univ i))
      exact h3 j (Finset.mem_univ j)
    have hcont : Continuous (fun x : Fin n → ℝ => u t₀ x i j - v t₀ x i j) :=
      ((contDiff_slice_of_contDiffOn (F := fun s x => u s x i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) ht₀).continuous).sub
      ((contDiff_slice_of_contDiffOn (F := fun s x => v s x i j)
        (contDiffOn_entry_of_contDiffOn hv.1 i j) ht₀).continuous)
    exact eq_zero_on_closedCube_of_integral_normSq_eq_zero _ hcont hterm x hx
  funext x i j
  have hper : Periodic1 (fun y : Fin n → ℝ => u t₀ y i j - v t₀ y i j) := by
    intro k y
    show u t₀ (y + Pi.single k 1) i j - v t₀ (y + Pi.single k 1) i j = u t₀ y i j - v t₀ y i j
    have h1 : u t₀ (y + Pi.single k 1) i j = u t₀ y i j :=
      Periodic1.entry (hu.2.1 t₀ ht₀) i j k y
    have h2 : v t₀ (y + Pi.single k 1) i j = v t₀ y i j :=
      Periodic1.entry (hv.2.1 t₀ ht₀) i j k y
    rw [h1, h2]
  exact sub_eq_zero.mp (eq_zero_of_eq_zero_on_closedCube
    (fun y : Fin n → ℝ => u t₀ y i j - v t₀ y i j) hper (hclosed i j) x)

end Work.Diff.STE.flat
