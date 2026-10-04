import Mathlib
import Submission.Work.Diff.EXT.evX.MonDefs
import Submission.Work.Diff.EXT.evX.Partition
import Submission.Work.Diff.EXT.evX.MonoD_extStepV
import Submission.Work.Diff.EXT.evX.KptArr_frame_indepV
import Submission.Work.Diff.GE.kato_geodesic_frame
import Submission.Work.Diff.EXT.reactionMap_rot
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.GE.EvolB.kato_jet_correction_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.GE

namespace Work.Diff.EXT.evX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Locality and additivity of `mvfderiv` -/

/-- `mvfderiv` depends only on the germ. -/
theorem mvfderiv_congr_of_eventuallyEq {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- **Additivity of `mvfderiv` over a finite sum** (of differentiable functions). -/
theorem mvfderiv_sum {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (h : ∀ i, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) (f i) x) :
    mvfderiv I (fun y => ∑ i, f i y) x v = ∑ i, mvfderiv I (f i) x v := by
  classical
  have hdiff : ∀ t : Finset ι, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => ∑ i ∈ t, f i y) x := by
    intro t
    refine (MDifferentiableAt.sum (t := t) (f := f) (fun i _ => h i)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Finset.sum_apply]
  have key : ∀ s : Finset ι,
      mvfderiv I (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [show (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = (fun _ : M => (0 : ℝ)) from by
        funext y; simp]
      rw [mvfderiv_const]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [show (fun y : M => ∑ i ∈ insert a s, f i y)
          = ((f a) + (fun y : M => ∑ i ∈ s, f i y)) from by
            funext y; rw [Finset.sum_insert ha]; rfl]
      rw [mvfderiv_add (h a) (hdiff s), add_apply, ih]
  simpa using key Finset.univ

/-! ## `O(n)`-equivariance of `reactionBilin` -/

section Rot

theorem rot_add' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S + T) = rot A S + rot A T := by
  funext i j k l
  simp only [rot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rot_smul' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (S : Curv4 n) :
    rot A (c • S) = c • rot A S := by
  funext i j k l
  simp only [rot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

theorem rot_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (S : Curv4 n) :
    rot A (-S) = -rot A S := by
  rw [← neg_one_smul ℝ S, rot_smul', neg_one_smul]

/-- `reactionBilin` written with a scalar (no function-level division). -/
theorem reactionBilin_smul {n : ℕ} (Z W : Curv4 n) :
    Work.Diff.EXT.reactionBilin Z W
      = (2 : ℝ)⁻¹ • (Work.Diff.GE.reactionMap (Z + W) - Work.Diff.GE.reactionMap Z
          - Work.Diff.GE.reactionMap W) := by
  funext i j k l
  simp only [Work.Diff.EXT.reactionBilin, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    div_eq_mul_inv]
  ring

/-- **`O(n)`-equivariance of the polarized reaction** `reactionBilin`. -/
theorem reactionBilin_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X Y : Curv4 n) :
    Work.Diff.EXT.reactionBilin (rot A X) (rot A Y)
      = rot A (Work.Diff.EXT.reactionBilin X Y) := by
  have h1 : rot A X + rot A Y = rot A (X + Y) := (rot_add' A X Y).symm
  have hsub : rot A (Work.Diff.GE.reactionMap (X + Y) - Work.Diff.GE.reactionMap X
        - Work.Diff.GE.reactionMap Y)
      = rot A (Work.Diff.GE.reactionMap (X + Y)) - rot A (Work.Diff.GE.reactionMap X)
        - rot A (Work.Diff.GE.reactionMap Y) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, rot_add', rot_add', rot_neg', rot_neg']
    funext i j k l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    ring
  rw [reactionBilin_smul (rot A X) (rot A Y), reactionBilin_smul X Y, h1,
    Work.Diff.EXT.reactionMap_rot A hA X, Work.Diff.EXT.reactionMap_rot A hA Y,
    Work.Diff.EXT.reactionMap_rot A hA (X + Y), ← hsub,
    (rot_smul' A (2 : ℝ)⁻¹ (Work.Diff.GE.reactionMap (X + Y) - Work.Diff.GE.reactionMap X
      - Work.Diff.GE.reactionMap Y)).symm]

end Rot

/-! ## The shuffle bookkeeping of the `Fin.cons` index maps -/

theorem map₁_cons_true (n : ℕ) (ε : Fin n → Bool) :
    map₁ (n + 1) (Fin.cons true ε)
      = Fin.cons 0 (fun r : Fin (cntT n ε) => (map₁ n ε r).succ) := by
  funext r
  refine Fin.cases ?_ ?_ r
  · show dsf (n + 1) (Fin.cons true ε) 0 = (0 : Fin (4 + (n + 1)))
    rw [dsf_cons_true_zero]
    exact Fin.ext rfl
  · intro r'
    show dsf (n + 1) (Fin.cons true ε) (r'.val + 1) = (dsf n ε r'.val).succ
    rw [dsf_cons_true_succ]

theorem map₁_cons_false (n : ℕ) (ε : Fin n → Bool) :
    map₁ (n + 1) (Fin.cons false ε) = fun r : Fin (cntT n ε) => (map₁ n ε r).succ := by
  funext r
  show dsf (n + 1) (Fin.cons false ε) r.val = (dsf n ε r.val).succ
  rw [dsf_cons_false]

theorem map₂_cons_true (n : ℕ) (ε : Fin n → Bool) :
    map₂ (n + 1) (Fin.cons true ε) = fun r : Fin (cntF n ε) => (map₂ n ε r).succ := by
  funext r
  show dsg (n + 1) (Fin.cons true ε) r.val = (dsg n ε r.val).succ
  rw [dsg_cons_true]

theorem map₂_cons_false (n : ℕ) (ε : Fin n → Bool) :
    map₂ (n + 1) (Fin.cons false ε)
      = Fin.cons 0 (fun r : Fin (cntF n ε) => (map₂ n ε r).succ) := by
  funext r
  refine Fin.cases ?_ ?_ r
  · show dsg (n + 1) (Fin.cons false ε) 0 = (0 : Fin (4 + (n + 1)))
    rw [dsg_cons_false_zero]
    exact Fin.ext rfl
  · intro r'
    show dsg (n + 1) (Fin.cons false ε) (r'.val + 1) = (dsg n ε r'.val).succ
    rw [dsg_cons_false_succ]

theorem sPos_succ_fun (n : ℕ) : sPos (n + 1) = fun t : Fin 4 => (sPos n t).succ := by
  funext t; exact sPos_succ n t

/-- The positions of the four slots are `≥ n`, while the directions are `< n`. -/
theorem sPos_injective (n : ℕ) : Function.Injective (sPos n) := by
  intro t t' h
  have := congrArg Fin.val h
  simp only [sPos] at this
  omega

/-- `Work.Diff.EXT.SmoothF` and `Work.Diff.GE.SmoothFieldT` are the same notion of smoothness. -/
theorem SmoothF_to_SmoothFieldT {X : Π y : M, TangentSpace I y}
    (h : Work.Diff.EXT.SmoothF X) : Work.Diff.GE.SmoothFieldT (I := I) (M := M) X := by
  unfold Work.Diff.EXT.SmoothF at h
  unfold Work.Diff.GE.SmoothFieldT
  exact h

/-! ## Frame independence of the monomial -/

/-- **Frame independence of the value of a monomial.**  `MonoD` is a contraction of the two tower
arrays with the four pairings; for two `g`-orthonormal frames at the point, the resulting scalar is
the same (`KptArr_frame_indepV`). -/
theorem MonoD_frame_indep (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (y : M) (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e e' : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (he' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e' i))
    (hON : Submission.Diff.IsONFrame g y (fun i => e i y))
    (hON' : Submission.Diff.IsONFrame g y (fun i => e' i y))
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y
      = Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e' F y := by
  have hrw : ∀ (e₀ : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e₀ i)) →
      Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e₀ F y
        = ∑ i, ∑ j, ∑ k, ∑ l,
            Work.Diff.EXT.reactionBilin
              (Work.Diff.EXT.KptArr g y a (fun r => (F (d₁ r)) y) (fun i => e₀ i y))
              (Work.Diff.EXT.KptArr g y b (fun r => (F (d₂ r)) y) (fun i => e₀ i y)) i j k l
            * (g.inner y (e₀ i y) (F (s 0) y) * g.inner y (e₀ j y) (F (s 1) y)
              * g.inner y (e₀ k y) (F (s 2) y) * g.inner y (e₀ l y) (F (s 3) y)) := by
    intro e₀ he₀
    simp only [Work.Diff.EXT.MonoD]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))))
    rw [Work.Diff.EXT.rmSym_eq_reactionBilin,
      Work.Diff.EXT.TowerArr_eq_KptArr (I := I) (M := M) hLC g a (fun r => F (d₁ r))
        (fun r => hF (d₁ r)) e₀ he₀ y,
      Work.Diff.EXT.TowerArr_eq_KptArr (I := I) (M := M) hLC g b (fun r => F (d₂ r))
        (fun r => hF (d₂ r)) e₀ he₀ y]
  rw [hrw e he, hrw e' he']
  exact KptArr_frame_indepV (I := I) (M := M) hLC reactionBilin_rot g y a b
    (fun r => (F (d₁ r)) y) (fun r => (F (d₂ r)) y)
    (fun i => e i y) (fun i => e' i y) hON hON' (fun t => F (s t) y)

/-- **Frame independence of the value of the word monomial `Monε`.** -/
theorem Monε_frame_indep (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (n : ℕ) (ε : Fin n → Bool)
    (e e' : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (he' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e' i))
    (x : M) (hON : Submission.Diff.IsONFrame g x (fun i => e i x))
    (hON' : Submission.Diff.IsONFrame g x (fun i => e' i x))
    (F : Fin (4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) :
    Monε (I := I) (M := M) g n ε e F x = Monε (I := I) (M := M) g n ε e' F x :=
  MonoD_frame_indep (I := I) (M := M) hLC g x (4 + n) (cntT n ε) (cntF n ε) (map₁ n ε)
    (map₂ n ε) (sPos n) e e' he he' hON hON' F hF

/-- **Frame independence of the value of `Monε`, in germ form.** -/
theorem Monε_frame_eventuallyEq (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (n : ℕ) (ε : Fin n → Bool)
    (e e' : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (he' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e' i))
    {x : M} (hON : ∀ᶠ z in 𝓝 x, Submission.Diff.IsONFrame g z (fun i => e i z))
    (hON' : ∀ᶠ z in 𝓝 x, Submission.Diff.IsONFrame g z (fun i => e' i z))
    (F : Fin (4 + n) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) :
    (fun z => Monε (I := I) (M := M) g n ε e F z)
      =ᶠ[𝓝 x] (fun z => Monε (I := I) (M := M) g n ε e' F z) := by
  filter_upwards [hON, hON'] with z hz hz'
  exact Monε_frame_indep (I := I) (M := M) hLC g n ε e e' he he' z hz hz' F hF

/-! ## A clean geodesic orthonormal frame at a point -/

/-- The Kato/`EvolB` jet correction: a globally smooth field with prescribed value and vanishing
covariant derivative at a point. -/
theorem kato_jet_correction_clean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M) (u : TangentSpace I x) :
    ∃ Y : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% Y) ∧ Y x = u ∧ cov Y x = 0 :=
  Work.Diff.GE.EvolB.kato_jet_correction_B cov x u

/-- **A geodesic orthonormal frame at a point** (without `Boundaryless`/`CompactSpace`
hypotheses). -/
theorem geodesic_frame_clean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M),
      (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W i)) ∧
      (∀ᶠ y in nhds x, Submission.Diff.IsONFrame g y (fun i => W i y)) ∧
      (∀ i, W i x = Submission.Diff.onFrame g x i) ∧
      (∀ m j, Submission.Diff.lcOf g (W j) x (W m x) = 0) := by
  classical
  set e : katoIdx E → TangentSpace I x := onFrame g x with hedef
  have he : IsONFrame g x e := isONFrame_onFrame g x
  choose V hVs hVx hVc using fun i => kato_jet_correction_clean (I := I) (M := M) (lcOf g) x (e i)
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (CMDiff ∞ (T% (katoFrame g x V i)))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (lcOf g (katoFrame g x V i) x = 0)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (lcOf g (katoFrame g x V j) x = 0)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVx i, hVx j, he i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVx i, he i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hUc : lcOf g (katoU g V (katoFrame g x V) i) x = 0 :=
          katoU_cov_zero g x V (katoFrame g x V) i (hVs i)
            (fun j hj => (hIH j hj).1) (hVc i) (fun j hj => (hIH j hj).2.2.1)
            (fun j hj => (hIH j hj).2.1) hON
        have hdf := katoGram_mvfderiv_zero g x V (katoFrame g x V) i hUs hUc
        have hψs : CMDiff ∞ (katoBump (I := I) (katoGram g V (katoFrame g x V) i) x) :=
          (katoBump_spec hGs hfx).1
        have hdF := katoNorm_mvfderiv_zero g x V (katoFrame g x V) i hGs hψs hdf
        have hdC := katoC_mvfderiv_zero g x V (katoFrame g x V) i hFs hFpos hdF
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hWc : lcOf g (katoFrame g x V i) x = 0 := by
          have hUsd : MDiffAt (T% (katoU g V (katoFrame g x V) i)) x :=
            hUs.contMDiffAt.mdifferentiableAt (by simp)
          have hCsd : MDiffAt (katoC g x V (katoFrame g x V) i) x :=
            hCs.contMDiffAt.mdifferentiableAt (by simp)
          have hdC0 : mvfderiv I (katoC g x V (katoFrame g x V) i) x = 0 := by
            ext v; exact hdC v
          rw [katoFrame_eq g x V i,
            show katoStep g x V (katoFrame g x V) i
              = (katoC g x V (katoFrame g x V) i) • (katoU g V (katoFrame g x V) i) from rfl,
            (lcOf g).isCovariantDerivativeOn.leibniz hUsd hCsd, hdC0, hUc, hCx]
          simp
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hWc, hdiag_i, hoff_i⟩
  refine ⟨katoFrame g x V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.2
  · intro i
    rw [(key (i.val + 1) i (Nat.lt_succ_self _)).2.1]
    exact hVx i
  · intro m j
    rw [(key (m.val + 1) m (Nat.lt_succ_self _)).2.1,
      (key (j.val + 1) j (Nat.lt_succ_self _)).2.2.1]
    rw [hVx m]
    rfl

/-- The Kato geodesic condition in linear-map form implies `lcOf g (Ef j) x = 0`. -/
theorem lcOf_eq_zero_of_geodesic (g : Submission.Diff.SMet I M) {y : M}
    (Ef : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (hON : Submission.Diff.IsONFrame g y (fun i => Ef i y))
    (h : ∀ m j, Submission.Diff.lcOf g (Ef j) y (Ef m y) = 0)
    (j : Fin (Module.finrank ℝ E)) :
    Submission.Diff.lcOf g (Ef j) y = 0 := by
  ext v
  have hv : v = ∑ m, g.inner y v (Ef m y) • Ef m y :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g y (fun i => Ef i y) hON v).symm
  rw [hv, map_sum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [map_smul, h m j, smul_zero]

/-! ## Differentiability of the monomial -/

/-- **The monomial of level `(a,b)` is differentiable in the base point.** -/
theorem MonoD_mdiffAt (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u))
    (x : M) :
    MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
      (fun y : M => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y) x := by
  classical
  rw [show (fun y : M => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y)
      = (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l,
          Work.Diff.EXT.rmSym (Work.Diff.EXT.TowerArr g a (fun r => F (d₁ r)) e y)
            (Work.Diff.EXT.TowerArr g b (fun r => F (d₂ r)) e y) i j k l
          * (g.inner y (e i y) (F (s 0) y) * g.inner y (e j y) (F (s 1) y)
            * g.inner y (e k y) (F (s 2) y) * g.inner y (e l y) (F (s 3) y)))
      from rfl]
  let G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → M → ℝ := fun i j k l => fun y =>
    Work.Diff.EXT.rmSym (Work.Diff.EXT.TowerArr g a (fun r => F (d₁ r)) e y)
      (Work.Diff.EXT.TowerArr g b (fun r => F (d₂ r)) e y) i j k l
    * (g.inner y (e i y) (F (s 0) y) * g.inner y (e j y) (F (s 1) y)
      * g.inner y (e k y) (F (s 2) y) * g.inner y (e l y) (F (s 3) y))
  change MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
    (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l, G i j k l y) x
  refine mdifferentiableAt_sum_pt Finset.univ
    (fun i : Fin (Module.finrank ℝ E) => fun y : M => ∑ j, ∑ k, ∑ l, G i j k l y) ?_
  intro i _
  refine mdifferentiableAt_sum_pt Finset.univ
    (fun j : Fin (Module.finrank ℝ E) => fun y : M => ∑ k, ∑ l, G i j k l y) ?_
  intro j _
  refine mdifferentiableAt_sum_pt Finset.univ
    (fun k : Fin (Module.finrank ℝ E) => fun y : M => ∑ l, G i j k l y) ?_
  intro k _
  refine mdifferentiableAt_sum_pt Finset.univ
    (fun l : Fin (Module.finrank ℝ E) => G i j k l) ?_
  intro l _
  refine (mdiffAt_curv4_comp (n := Module.finrank ℝ E) ?_ i j k l).mul ?_
  · exact mdifferentiableAt_bilin_pair
      (fun p : Curv4 (Module.finrank ℝ E) × Curv4 (Module.finrank ℝ E) =>
        Work.Diff.EXT.rmSym p.1 p.2)
      (rmSym_isBoundedBilinearMap (Module.finrank ℝ E))
      (mdifferentiableAt_curv4_of_components (fun p q r s =>
        TowerArr_mdiffAt hLC g a (fun r => F (d₁ r)) (fun r => hF (d₁ r)) e he x p q r s))
      (mdifferentiableAt_curv4_of_components (fun p q r s =>
        TowerArr_mdiffAt hLC g b (fun r => F (d₂ r)) (fun r => hF (d₂ r)) e he x p q r s))
  · exact (((metricPairing_mdiffAt g (he i) (hF (s 0)) x).mul
        (metricPairing_mdiffAt g (he j) (hF (s 1)) x)).mul
        (metricPairing_mdiffAt g (he k) (hF (s 2)) x)).mul
        (metricPairing_mdiffAt g (he l) (hF (s 3)) x)

/-! ## The combinatorial splitting of the words -/

/-- A word is its first letter followed by its tail. -/
def piFinSuccEquiv (j : ℕ) : (Fin (j + 1) → Bool) ≃ Bool × (Fin j → Bool) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i'; rfl
  right_inv p := by
    obtain ⟨b, g⟩ := p
    refine Prod.ext ?_ ?_
    · rfl
    · funext i; rfl

/-- **The sum over the words splits by the first letter.** -/
theorem sum_cons_eq (j : ℕ) (f : (Fin (j + 1) → Bool) → ℝ) :
    (∑ ε : Fin j → Bool, f (Fin.cons true ε)) + (∑ ε : Fin j → Bool, f (Fin.cons false ε))
      = ∑ ε' : Fin (j + 1) → Bool, f ε' := by
  classical
  have hsum : (∑ ε' : Fin (j + 1) → Bool, f ε')
      = ∑ b : Bool, ∑ ε : Fin j → Bool, f (Fin.cons b ε) := by
    rw [← Fintype.sum_equiv (piFinSuccEquiv j).symm
        (fun p : Bool × (Fin j → Bool) => f (Fin.cons p.1 p.2)) (fun ε' => f ε')
        (fun p => rfl)]
    rw [Fintype.sum_prod_type]
  rw [hsum, Fintype.sum_bool]

/-! ## The recursion of the word monomials -/

/-- **One `extStep` splits the level-`n` monomial of the word `ε` into its two children**, in a
frame which is *parallel* at the evaluation point (the frame we reduce to by frame independence). -/
theorem Monε_extStepV (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (y : M)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hgeo : ∀ i, Submission.Diff.lcOf g (e i) y = 0)
    (n : ℕ) (ε : Fin n → Bool)
    (F : Fin (4 + n + 1) → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) :
    Work.Diff.EXT.extStep (I := I) (M := M) g (Monε (I := I) (M := M) g n ε e) F y
      = Monε (I := I) (M := M) g (n + 1) (Fin.cons true ε) e F y
        + Monε (I := I) (M := M) g (n + 1) (Fin.cons false ε) e F y := by
  obtain ⟨hI1, hI2, hD12, hD1s, hD2s, hcov⟩ := Partition (I := I) (M := M) n ε
  have hcard := cnt_add n ε
  have hmain := MonoD_extStepV (I := I) (M := M) hLC g y e he hgeo (4 + n)
    (cntT n ε) (cntF n ε) (by omega) (map₁ n ε) (map₂ n ε) (sPos n) hI1 hI2
    (sPos_injective n) hD12 hD1s hD2s hcov F hF
  simp only [Monε] at hmain ⊢
  rw [hmain, map₁_cons_true, map₁_cons_false, map₂_cons_true, map₂_cons_false, sPos_succ_fun]
  rfl

/-! ## The `n`-th jet of the level-`0` reaction -/

/-- **The `n`-th jet of the level-`0` reaction is the sum of the `2^n` monomials of the binary words.**
`Work.Diff.EXT.evX.Monε g n ε e` is the packed monomial `MonoD g (4+n) (cntT n ε) (cntF n ε) (map₁ n ε)
(map₂ n ε) (sPos n) e` of the word `ε : Fin n → Bool` (the `t`-th covariant derivative was applied to
the first factor iff `ε t = true`), and `Monε g 0 ε₀ e` is the level-`0` reaction operator written with
the frame field `e`.  The claim is the operator identity `jetAll g n 4 (Monε g 0 ε₀ e) = ∑_ε Monε g n ε e`.

Route: induction on `n` (`n` quantified before the point, so that the induction hypothesis is available
at every point near the evaluation point — it is needed there because `extStep` differentiates the
operator in space; `hON` at nearby points follows from `hON` at `x` by `eventually_nhds_nhds`).  The step
is `jetAll g (n+1) 4 S = extStep g (jetAll g n 4 S)`; `Work.Diff.EXT.evX.Monε_extStep` (`Base.lean`,
proved) splits `extStep g (Monε g n ε e)` into the two children
`Monε g (n+1) (Fin.cons true ε) e + Monε g (n+1) (Fin.cons false ε) e`; the base case `n = 0` is the
singleton sum (`Subsingleton.elim`); finally
`∑_{ε : Fin n → Bool} f (Fin.cons true ε) + ∑_ε f (Fin.cons false ε) = ∑_{ε' : Fin (n+1) → Bool} f ε'`
via the equiv `(Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool)`, `ε ↦ (ε 0, fun t => ε t.succ)` with inverse
`Fin.cons`, `Equiv.sum_comp` and `Fintype.sum_prod_type`.

Plumbing needed on the way: `Work.Diff.GE.Kato3.mvfderiv_sum` (additivity of `mvfderiv` over a finite sum
of `C^∞` functions) applied to the operator sum, hence the `C^∞`-smoothness of `x ↦ Monε g n ε e F' x`
(`Work.Diff.GE.TensProp` / `Work.Diff.GE.tensProp_all` give the smoothness of the `ckt`-expressions in
`Submission/Work/Diff/EXT/curvNormK_frame_indep.lean`; `rmSym` and the pairings are polynomial), and the
fact that the sum over the words is the same operator as the one appearing in the induction hypothesis
(the terms are the same functions). -/
theorem jetAll_eq_MonSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (ε₀ : Fin 0 → Bool) :
    ∀ (n : ℕ) (x : M),
      (∀ᶠ z in nhds x, Submission.Diff.IsONFrame g z (fun i => e i z)) →
      ∀ (F : Fin (4 + n) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ u, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F u)) →
      Work.Diff.EXT.jetAll (I := I) (M := M) g n 4
          (Work.Diff.EXT.evX.Monε (I := I) (M := M) g 0 ε₀ e) F x
        = Finset.univ.sum (fun ε : Fin n → Bool =>
            Work.Diff.EXT.evX.Monε (I := I) (M := M) g n ε e F x) := by
  classical
  intro n
  induction n with
  | zero =>
    intro x hON F hF
    have huniq : ∀ b : Fin 0 → Bool, b = ε₀ := fun b => funext fun i => Fin.elim0 i
    have hsingle : (Finset.univ : Finset (Fin 0 → Bool)) = {ε₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨Finset.mem_univ ε₀, fun b _ => huniq b⟩
    rw [hsingle, Finset.sum_singleton]
    rfl
  | succ n ih =>
    intro x hON F hF
    -- the orthonormality hypothesis at every nearby point
    have hP : ∀ᶠ z in 𝓝 x, ∀ᶠ w in 𝓝 z, Submission.Diff.IsONFrame g w (fun i => e i w) := by
      obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hON
      refine mem_of_superset (hUo.mem_nhds hxU) fun z hz => ?_
      exact mem_of_superset (hUo.mem_nhds hz) hUsub
    have hONx : Submission.Diff.IsONFrame g x (fun i => e i x) := by
      obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp hON
      exact hUsub hxU
    -- a smooth frame which is orthonormal near `x` and parallel at `x`
    obtain ⟨W, hWs, hWON, hWx, hWgeo₀⟩ := geodesic_frame_clean (I := I) (M := M) g x
    have hWONx : Submission.Diff.IsONFrame g x (fun i => W i x) := by
      rw [funext hWx]; exact isONFrame_onFrame g x
    have hWgeo : ∀ i, Submission.Diff.lcOf g (W i) x = 0 :=
      fun i => lcOf_eq_zero_of_geodesic g W hWONx hWgeo₀ i
    -- the recursion of the jet
    rw [show Work.Diff.EXT.jetAll (I := I) (M := M) g (n + 1) 4
          (Monε (I := I) (M := M) g 0 ε₀ e) F x
        = Work.Diff.EXT.extStep (I := I) (M := M) g
            (fun F' y => Work.Diff.EXT.jetAll (I := I) (M := M) g n 4
              (Monε (I := I) (M := M) g 0 ε₀ e) F' y) F x from rfl]
    simp only [Work.Diff.EXT.extStep]
    -- the germ of the level-`n` operator is the sum of the monomials
    have hger : (fun z => Work.Diff.EXT.jetAll (I := I) (M := M) g n 4
          (Monε (I := I) (M := M) g 0 ε₀ e) (fun i : Fin (4 + n) => F i.succ) z)
        =ᶠ[𝓝 x] (fun z => ∑ ε : Fin n → Bool,
            Monε (I := I) (M := M) g n ε e (fun i : Fin (4 + n) => F i.succ) z) := by
      filter_upwards [hP] with z hz
      exact ih z hz _ (fun u => hF u.succ)
    rw [mvfderiv_congr_of_eventuallyEq hger]
    -- the Leibniz corrections
    have hcorr : ∀ u : Fin (4 + n),
        Work.Diff.EXT.jetAll (I := I) (M := M) g n 4 (Monε (I := I) (M := M) g 0 ε₀ e)
            (Function.update (fun i : Fin (4 + n) => F i.succ) u
              (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x
          = ∑ ε : Fin n → Bool, Monε (I := I) (M := M) g n ε e
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x := by
      intro u
      refine ih x hON _ (fun r => ?_)
      rcases eq_or_ne r u with h | h
      · subst h
        simpa only [Function.update_self] using
          SmoothF_to_SmoothFieldT (Work.Diff.EXT.dirF_smooth hLC g (hF r.succ) (hF 0))
      · rw [Function.update_of_ne h]; exact hF r.succ
    have hcorr2 : (∑ u : Fin (4 + n), Work.Diff.EXT.jetAll (I := I) (M := M) g n 4
            (Monε (I := I) (M := M) g 0 ε₀ e)
            (Function.update (fun i : Fin (4 + n) => F i.succ) u
              (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x)
        = ∑ u : Fin (4 + n), ∑ ε : Fin n → Bool, Monε (I := I) (M := M) g n ε e
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x :=
      Finset.sum_congr rfl (fun u _ => hcorr u)
    rw [hcorr2]
    -- additivity of `mvfderiv` over the sum over the words
    have hdiffε : ∀ ε : Fin n → Bool, MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun z => Monε (I := I) (M := M) g n ε e (fun i : Fin (4 + n) => F i.succ) z) x :=
      fun ε => MonoD_mdiffAt (I := I) (M := M) hLC g (4 + n) (cntT n ε) (cntF n ε) (map₁ n ε)
        (map₂ n ε) (sPos n) e he (fun i => F i.succ) (fun u => hF u.succ) x
    rw [mvfderiv_sum (f := fun ε : Fin n → Bool => fun z =>
          Monε (I := I) (M := M) g n ε e (fun i : Fin (4 + n) => F i.succ) z) x (F 0 x) hdiffε]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    -- each word now splits
    have hεMon : ∀ ε : Fin n → Bool,
        (mvfderiv I (fun z => Monε (I := I) (M := M) g n ε e
              (fun i : Fin (4 + n) => F i.succ) z) x) (F 0 x)
          - ∑ u : Fin (4 + n), Monε (I := I) (M := M) g n ε e
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x
        = Monε (I := I) (M := M) g (n + 1) (Fin.cons true ε) e F x
          + Monε (I := I) (M := M) g (n + 1) (Fin.cons false ε) e F x := by
      intro ε
      have hgerε : (fun z => Monε (I := I) (M := M) g n ε e
            (fun i : Fin (4 + n) => F i.succ) z)
          =ᶠ[𝓝 x] (fun z => Monε (I := I) (M := M) g n ε W
            (fun i : Fin (4 + n) => F i.succ) z) :=
        Monε_frame_eventuallyEq (I := I) (M := M) hLC g n ε e W he hWs hON hWON
          (fun i : Fin (4 + n) => F i.succ) (fun u => hF u.succ)
      have hcorrW : ∀ u : Fin (4 + n),
          Monε (I := I) (M := M) g n ε e
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x
            = Monε (I := I) (M := M) g n ε W
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x := by
        intro u
        refine Monε_frame_indep (I := I) (M := M) hLC g n ε e W he hWs x hONx hWONx _
          (fun r => ?_)
        rcases eq_or_ne r u with h | h
        · subst h
          simpa only [Function.update_self] using
            SmoothF_to_SmoothFieldT (Work.Diff.EXT.dirF_smooth hLC g (hF r.succ) (hF 0))
        · rw [Function.update_of_ne h]; exact hF r.succ
      have hsw : Work.Diff.EXT.extStep (I := I) (M := M) g
            (Monε (I := I) (M := M) g n ε e) F x
          = Work.Diff.EXT.extStep (I := I) (M := M) g
            (Monε (I := I) (M := M) g n ε W) F x := by
        simp only [Work.Diff.EXT.extStep]
        rw [mvfderiv_congr_of_eventuallyEq hgerε]
        congr 1
        exact Finset.sum_congr rfl (fun u _ => hcorrW u)
      rw [show (mvfderiv I (fun z => Monε (I := I) (M := M) g n ε e
              (fun i : Fin (4 + n) => F i.succ) z) x) (F 0 x)
            - ∑ u : Fin (4 + n), Monε (I := I) (M := M) g n ε e
              (Function.update (fun i : Fin (4 + n) => F i.succ) u
                (Work.Diff.EXT.dirF g ((fun i : Fin (4 + n) => F i.succ) u) (F 0))) x
          = Work.Diff.EXT.extStep (I := I) (M := M) g
              (Monε (I := I) (M := M) g n ε e) F x from rfl]
      rw [hsw, Monε_extStepV (I := I) (M := M) hLC g x W hWs hWgeo n ε F hF,
        Monε_frame_indep (I := I) (M := M) hLC g (n + 1) (Fin.cons true ε) W e hWs he x
          hWONx hONx F hF,
        Monε_frame_indep (I := I) (M := M) hLC g (n + 1) (Fin.cons false ε) W e hWs he x
          hWONx hONx F hF]
    rw [Finset.sum_congr rfl (fun ε _ => hεMon ε)]
    rw [Finset.sum_add_distrib]
    exact sum_cons_eq n (fun ε' : Fin (n + 1) → Bool =>
      Monε (I := I) (M := M) g (n + 1) ε' e F x)

end Work.Diff.EXT.evX
