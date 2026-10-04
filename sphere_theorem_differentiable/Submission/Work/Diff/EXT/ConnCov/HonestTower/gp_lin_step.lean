import Mathlib
import Submission.Work.Diff.EXT.ConnCov.HonestTower.Kit
import Submission.Work.Diff.EXT.ATens.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT.ConnCov.HonestTower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **Linearity in the differentiation slot** of the packed honest tower (the analogue of
`Work.Diff.EXT.ckt_lin_dir`). -/
theorem gp_lin_dir_step (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hih : TensPropG (I := I) (M := M) g base k)
    {G : Fin (k + 2) → Tf (I := I) (M := M)}
    (hG : ∀ i, Sm (I := I) (M := M) (G i))
    {X₁ X₂ : Tf (I := I) (M := M)}
    (hX₁ : Sm (I := I) (M := M) X₁) (hX₂ : Sm (I := I) (M := M) X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    gP g base (k + 1) (Fin.cons (f₁ • X₁ + f₂ • X₂) G)
      = f₁ • gP g base (k + 1) (Fin.cons X₁ G)
        + f₂ • gP g base (k + 1) (Fin.cons X₂ G) := by
  have hconsF : ∀ (W : Tf (I := I) (M := M)),
      (fun i : Fin (k + 2) => (Fin.cons W G : Fin (k + 3) → Tf (I := I) (M := M)) i.succ) = G := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) W G i
  have hconsP : ∀ (W : Tf (I := I) (M := M)) (i : Fin (k + 2)),
      (Fin.cons W G : Fin (k + 3) → Tf (I := I) (M := M)) i.succ = G i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) W G i
  have hzero : ∀ (W : Tf (I := I) (M := M)),
      (Fin.cons W G : Fin (k + 3) → Tf (I := I) (M := M)) 0 = W :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) W G
  rw [gP_succ, gP_succ, gP_succ]
  simp only [hconsF, hconsP, hzero]
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have ht1 : (mvfderiv I (gP g base k G) y) (f₁ y • X₁ y + f₂ y • X₂ y)
      = f₁ y • ((mvfderiv I (gP g base k G) y) (X₁ y))
        + f₂ y • ((mvfderiv I (gP g base k G) y) (X₂ y)) := by
    simp only [map_add, map_smul]
  have hs : (∑ q : Fin (k + 2), gP g base k
        (Function.update G q (Work.Diff.EXT.dirFA g (G q) (f₁ • X₁ + f₂ • X₂))) y)
      = f₁ y • (∑ q : Fin (k + 2), gP g base k
            (Function.update G q (Work.Diff.EXT.dirFA g (G q) X₁)) y)
        + f₂ y • (∑ q : Fin (k + 2), gP g base k
            (Function.update G q (Work.Diff.EXT.dirFA g (G q) X₂)) y) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Work.Diff.EXT.dirFA_add_dir]
    have hq := (hih G hG).2.1 q (Work.Diff.EXT.dirFA g (G q) X₁) (Work.Diff.EXT.dirFA g (G q) X₂)
      f₁ f₂ (Work.Diff.EXT.dirFA_smooth hLC g (hG q) hX₁)
      (Work.Diff.EXT.dirFA_smooth hLC g (hG q) hX₂) hf₁ hf₂
    rw [hq]
    simp only [Pi.add_apply, Pi.smul_apply']
  rw [ht1, hs]
  simp only [smul_sub, smul_eq_mul]
  ring

/-- **Linearity in a slot of the tail** of the packed honest tower (the analogue of
`Work.Diff.EXT.ckt_lin_tail`). -/
theorem gp_lin_tail_step (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hih : TensPropG (I := I) (M := M) g base k)
    {G : Fin (k + 2) → Tf (I := I) (M := M)}
    (hG : ∀ i, Sm (I := I) (M := M) (G i))
    {v0 X₁ X₂ : Tf (I := I) (M := M)}
    (hv0 : Sm (I := I) (M := M) v0)
    (hX₁ : Sm (I := I) (M := M) X₁) (hX₂ : Sm (I := I) (M := M) X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) (j : Fin (k + 2)) :
    gP g base (k + 1) (Fin.cons v0 (Function.update G j (f₁ • X₁ + f₂ • X₂)))
      = f₁ • gP g base (k + 1) (Fin.cons v0 (Function.update G j X₁))
        + f₂ • gP g base (k + 1) (Fin.cons v0 (Function.update G j X₂)) := by
  have hconsF : ∀ (W : Fin (k + 2) → Tf (I := I) (M := M)),
      (fun i : Fin (k + 2) =>
        (Fin.cons v0 W : Fin (k + 3) → Tf (I := I) (M := M)) i.succ) = W := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) v0 W i
  have hconsP : ∀ (W : Fin (k + 2) → Tf (I := I) (M := M)) (i : Fin (k + 2)),
      (Fin.cons v0 W : Fin (k + 3) → Tf (I := I) (M := M)) i.succ = W i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) v0 W i
  have hzero : ∀ (W : Fin (k + 2) → Tf (I := I) (M := M)),
      (Fin.cons v0 W : Fin (k + 3) → Tf (I := I) (M := M)) 0 = v0 :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 3) => Tf (I := I) (M := M)) v0 W
  rw [gP_succ, gP_succ, gP_succ]
  simp only [hconsF, hconsP, hzero]
  have hAW : gP g base k (Function.update G j (f₁ • X₁ + f₂ • X₂))
      = f₁ • gP g base k (Function.update G j X₁)
        + f₂ • gP g base k (Function.update G j X₂) :=
    (hih G hG).2.1 j X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
  have hadd : ∀ {A B : Tf (I := I) (M := M)},
      Sm (I := I) (M := M) A → Sm (I := I) (M := M) B →
      gP g base k (Function.update G j (A + B))
        = gP g base k (Function.update G j A) + gP g base k (Function.update G j B) := by
    intro A B hA hB
    have h := (hih G hG).2.1 j A B (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hA hB
      (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have hAB : (fun _ : M => (1 : ℝ)) • A + (fun _ : M => (1 : ℝ)) • B = A + B := by
      funext z; simp
    have hA' : (fun _ : M => (1 : ℝ)) • gP g base k (Function.update G j A)
        = gP g base k (Function.update G j A) := by funext z; simp
    have hB' : (fun _ : M => (1 : ℝ)) • gP g base k (Function.update G j B)
        = gP g base k (Function.update G j B) := by funext z; simp
    rw [hAB, hA', hB'] at h
    exact h
  have hS1 : CMDiff ∞ (gP g base k (Function.update G j X₁)) :=
    (hih _ (sm_update hG hX₁)).1
  have hS2 : CMDiff ∞ (gP g base k (Function.update G j X₂)) :=
    (hih _ (sm_update hG hX₂)).1
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have hT : (mvfderiv I (gP g base k (Function.update G j (f₁ • X₁ + f₂ • X₂))) y) (v0 y)
      = f₁ y • ((mvfderiv I (gP g base k (Function.update G j X₁)) y) (v0 y))
        + ((mvfderiv I f₁ y) (v0 y)) • (gP g base k (Function.update G j X₁) y)
        + f₂ y • ((mvfderiv I (gP g base k (Function.update G j X₂)) y) (v0 y))
        + ((mvfderiv I f₂ y) (v0 y)) • (gP g base k (Function.update G j X₂) y) := by
    rw [hAW]
    rw [mvfderiv_two_smulA f₁ f₂ (gP g base k (Function.update G j X₁))
      (gP g base k (Function.update G j X₂)) y (v0 y)
      (hf₁.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
      (hS1.mdifferentiableAt (by simp)) (hS2.mdifferentiableAt (by simp))]
    simp only [smul_eq_mul]
  have hstep : ∀ q : Fin (k + 2), q ≠ j →
      gP g base k (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
        (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0))
      = f₁ • gP g base k (Function.update (Function.update G j X₁) q
            (Work.Diff.EXT.dirFA g ((Function.update G j X₁) q) v0))
        + f₂ • gP g base k (Function.update (Function.update G j X₂) q
            (Work.Diff.EXT.dirFA g ((Function.update G j X₂) q) v0)) := by
    intro q hqj
    have h1 : Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
        (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)
        = Function.update (Function.update G q (Work.Diff.EXT.dirFA g (G q) v0)) j
            (f₁ • X₁ + f₂ • X₂) := by
      rw [Function.update_of_ne hqj]
      exact (Function.update_comm hqj (Work.Diff.EXT.dirFA g (G q) v0) (f₁ • X₁ + f₂ • X₂) G).symm
    have h2 : Function.update (Function.update G q (Work.Diff.EXT.dirFA g (G q) v0)) j X₁
        = Function.update (Function.update G j X₁) q
            (Work.Diff.EXT.dirFA g ((Function.update G j X₁) q) v0) := by
      rw [Function.update_of_ne hqj]
      exact Function.update_comm hqj (Work.Diff.EXT.dirFA g (G q) v0) X₁ G
    have h3 : Function.update (Function.update G q (Work.Diff.EXT.dirFA g (G q) v0)) j X₂
        = Function.update (Function.update G j X₂) q
            (Work.Diff.EXT.dirFA g ((Function.update G j X₂) q) v0) := by
      rw [Function.update_of_ne hqj]
      exact Function.update_comm hqj (Work.Diff.EXT.dirFA g (G q) v0) X₂ G
    rw [h1]
    have hlin := (hih (Function.update G q (Work.Diff.EXT.dirFA g (G q) v0))
      (sm_update hG (Work.Diff.EXT.dirFA_smooth hLC g (hG q) hv0))).2.1 j X₁ X₂ f₁ f₂
      hX₁ hX₂ hf₁ hf₂
    rw [hlin, h2, h3]
  have hjterm : gP g base k (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) j
        (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) j) v0)) y
      = f₁ y • (gP g base k (Function.update (Function.update G j X₁) j
            (Work.Diff.EXT.dirFA g ((Function.update G j X₁) j) v0)) y)
        + f₂ y • (gP g base k (Function.update (Function.update G j X₂) j
            (Work.Diff.EXT.dirFA g ((Function.update G j X₂) j) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (gP g base k (Function.update G j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (gP g base k (Function.update G j X₂) y) := by
    have hidem : Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) j
        (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) j) v0)
        = Function.update G j (Work.Diff.EXT.dirFA g (f₁ • X₁ + f₂ • X₂) v0) := by
      rw [Function.update_self]
      funext q
      by_cases hq : q = j
      · subst hq; rw [Function.update_self, Function.update_self]
      · simp only [Function.update_of_ne hq]
    rw [hidem, Work.Diff.EXT.dirFA_leibniz (g := g) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
      (v0 := v0) hX₁ hX₂ hf₁ hf₂]
    have hE1 : CMDiff ∞ (fun z : M => (mvfderiv I f₁ z) (v0 z)) :=
      mvfderiv_apply_contMDiff hf₁ hv0
    have hE2 : CMDiff ∞ (fun z : M => (mvfderiv I f₂ z) (v0 z)) :=
      mvfderiv_apply_contMDiff hf₂ hv0
    rw [add_assoc (f₁ • Work.Diff.EXT.dirFA g X₁ v0
        + (fun z : M => (mvfderiv I f₁ z) (v0 z)) • X₁)
        (f₂ • Work.Diff.EXT.dirFA g X₂ v0) ((fun z : M => (mvfderiv I f₂ z) (v0 z)) • X₂)]
    rw [hadd ((hf₁.smul_section (Work.Diff.EXT.dirFA_smooth hLC g hX₁ hv0)).add_section
          (hE1.smul_section hX₁))
        ((hf₂.smul_section (Work.Diff.EXT.dirFA_smooth hLC g hX₂ hv0)).add_section
          (hE2.smul_section hX₂))]
    rw [(hih G hG).2.1 j (Work.Diff.EXT.dirFA g X₁ v0) X₁ f₁
        (fun z : M => (mvfderiv I f₁ z) (v0 z))
        (Work.Diff.EXT.dirFA_smooth hLC g hX₁ hv0) hX₁ hf₁ hE1]
    rw [(hih G hG).2.1 j (Work.Diff.EXT.dirFA g X₂ v0) X₂ f₂
        (fun z : M => (mvfderiv I f₂ z) (v0 z))
        (Work.Diff.EXT.dirFA_smooth hLC g hX₂ hv0) hX₂ hf₂ hE2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply', Function.update_idem,
      Function.update_self, smul_eq_mul]
    ring
  have hne : (∑ q ∈ Finset.univ.erase j, gP g base k
        (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
          (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y * (∑ q ∈ Finset.univ.erase j, gP g base k
            (Function.update (Function.update G j X₁) q
              (Work.Diff.EXT.dirFA g ((Function.update G j X₁) q) v0)) y)
        + f₂ y * (∑ q ∈ Finset.univ.erase j, gP g base k
            (Function.update (Function.update G j X₂) q
              (Work.Diff.EXT.dirFA g ((Function.update G j X₂) q) v0)) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqj : q ≠ j := (Finset.mem_erase.mp hq).1
    rw [hstep q hqj]
    simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  have hS : (∑ q : Fin (k + 2), gP g base k
        (Function.update (Function.update G j (f₁ • X₁ + f₂ • X₂)) q
          (Work.Diff.EXT.dirFA g ((Function.update G j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y • (∑ q : Fin (k + 2), gP g base k
            (Function.update (Function.update G j X₁) q
              (Work.Diff.EXT.dirFA g ((Function.update G j X₁) q) v0)) y)
        + f₂ y • (∑ q : Fin (k + 2), gP g base k
            (Function.update (Function.update G j X₂) q
              (Work.Diff.EXT.dirFA g ((Function.update G j X₂) q) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (gP g base k (Function.update G j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (gP g base k (Function.update G j X₂) y) := by
    rw [← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j)]
    rw [hjterm, hne]
    simp only [smul_add, smul_eq_mul]
    ring
  rw [hT, hS]
  simp only [smul_sub, smul_add, smul_eq_mul]
  ring

end Work.Diff.EXT.ConnCov.HonestTower
