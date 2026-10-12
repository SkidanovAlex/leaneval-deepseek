import ChallengeDeps
import Submission.Work.BoseRowQ2.GchiReduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.GchiIdentify` — the honest operators as `besselOpMat`

The honest model's operators are *by construction* superpositions of the coordinate
modes (`Work.BoseB4.b7FockData`: `a k = annOf m (f k)`, `aDag k = creOf m (f k)`;
`Work.BoseBoxFock.tildeDataHon`: `ta s = annOf m (g s)`, `taDag s = creOf m (g s)`).
This module reads off the consequent matrix representations

    allNumOp = besselOpMat F ,   NH = besselOpMat T ,   Gop = besselOpMat A ,

with `F`, `T`, `A` the `Fin m × Fin m` matrices of `Work.BoseRowQ2`'s
`FINDING_rowGchi_honest_session1.md` §1:

    F l l' = Σ_{k ∈ Lab N}  f k l · f k l' ,
    T l l' = Σ_{k ∈ excited} η_H k · f k l · f k l' ,
    A l l' = Σ_{s,s' ∈ excited} fL s fL s' χ̂²(s'−s) · g s' l · g s l' .

Together with `Work.BoseRowQ2.besselOpMat_le_of_mat` these reduce `GchiAt` (FS l.3253)
to the one-body matrix inequality `A ⪯ (1+ε)F + (Cχ/(32ε))T`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseB7A Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseRowsFS

/-! ## 0. Linear-algebra toolbox for `besselOpMat` -/

/-- `besselOpMat` is additive over a finite sum of matrices (pointwise form). -/
theorem besselOpMat_sum_finset {ι : Type*} {m : ℕ} (s : Finset ι)
    (M : ι → Fin m → Fin m → ℝ) :
    besselOpMat m (fun l l' => ∑ i ∈ s, M i l l') = ∑ i ∈ s, besselOpMat m (M i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 : (fun l l' => ∑ i ∈ (∅ : Finset ι), M i l l') = 0 := by
      funext l l'; simp
    rw [h0]; simp [besselOpMat]
  · intro a s has ih
    have hstep : (fun l l' => ∑ i ∈ insert a s, M i l l')
        = M a + (fun l l' => ∑ i ∈ s, M i l l') := by
      funext l l'
      simp only [Finset.sum_insert has, Pi.add_apply]
    rw [hstep, besselOpMat_add, ih, Finset.sum_insert has]

/-- `besselOpMat` is additive over a finite sum of matrices. -/
theorem besselOpMat_sum {ι : Type*} [Fintype ι] {m : ℕ} (M : ι → Fin m → Fin m → ℝ) :
    besselOpMat m (fun l l' => ∑ i, M i l l') = ∑ i, besselOpMat m (M i) := by
  simpa using besselOpMat_sum_finset (m := m) (s := Finset.univ) M

/-- `besselOpMat` is homogeneous. -/
theorem besselOpMat_smul {m : ℕ} (c : ℝ) (M : Fin m → Fin m → ℝ) :
    besselOpMat m (c • M) = c • besselOpMat m M := by
  simp only [besselOpMat, Pi.smul_apply, smul_eq_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  exact (smul_smul c (M l l') _).symm

/-! ## 1. The honest operators -/

section Honest

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
  {fc fu : Work.BoseBoxFix.LowCut}

/-- The honest Fock data's annihilation operator at a label is the coordinate annihilation
of the χ-mode vector (`Work.BoseB4.b7FockData`). -/
lemma honF_a (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k : Lab (HM μ).N) :
    (honF v h fc fu HM μ).a k = annOf (HM μ).m ((HM μ).f k) := rfl

/-- The honest Fock data's creation operator at a label. -/
lemma honF_aDag (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (k : Lab (HM μ).N) :
    (honF v h fc fu HM μ).aDag k = creOf (HM μ).m ((HM μ).f k) := rfl

/-- The honest θ-mode annihilation at a label. -/
lemma honT_ta (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (s : Lab (HM μ).N) :
    (honT v h fc fu HM μ).ta s = annOf (HM μ).m ((HM μ).g s) := rfl

/-- The honest θ-mode creation at a label. -/
lemma honT_taDag (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (s : Lab (HM μ).N) :
    (honT v h fc fu HM μ).taDag s = creOf (HM μ).m ((HM μ).g s) := rfl

/-- **`allNumOp` is `besselOpMat` of the χ-frame.** -/
theorem allNumOp_eq_besselOpMat (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honF v h fc fu HM μ).allNumOp
      = besselOpMat (HM μ).m
          (fun l l' => ∑ k : Lab (HM μ).N, (HM μ).f k l * (HM μ).f k l') := by
  rw [FockData.allNumOp]
  rw [show (∑ k : Lab (HM μ).N, (honF v h fc fu HM μ).nOp k)
      = ∑ k : Lab (HM μ).N,
          besselOpMat (HM μ).m (fun l l' => (HM μ).f k l * (HM μ).f k l') from
      Finset.sum_congr rfl fun k _ => by
        rw [FockData.nOp, honF_a, honF_aDag]
        exact creOf_comp_annOf_eq_besselOpMat _ _]
  exact (besselOpMat_sum (m := (HM μ).m)
    (M := fun k : Lab (HM μ).N => fun l l' => (HM μ).f k l * (HM μ).f k l')).symm

/-- **`NH` is `besselOpMat` of the `η_H`-weighted χ-frame.** -/
theorem NH_eq_besselOpMat (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honT v h fc fu HM μ).NH
      = besselOpMat (HM μ).m
          (fun l l' => (1 / 32) * ∑ k ∈ excited (Lab (HM μ).N),
            etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
                * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
              * ((HM μ).f k l * (HM μ).f k l')) := by
  show (1 / 32 : ℝ) • (∑ k ∈ excited (Lab (HM μ).N),
        etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
          • ((creOf (HM μ).m ((HM μ).f k)).comp (annOf (HM μ).m ((HM μ).f k))))
      = besselOpMat (HM μ).m
          (fun l l' => (1 / 32) * ∑ k ∈ excited (Lab (HM μ).N),
            etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
                * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
              * ((HM μ).f k l * (HM μ).f k l'))
  have hinner : (∑ k ∈ excited (Lab (HM μ).N),
        etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
          • ((creOf (HM μ).m ((HM μ).f k)).comp (annOf (HM μ).m ((HM μ).f k))))
      = besselOpMat (HM μ).m
          (fun l l' => ∑ k ∈ excited (Lab (HM μ).N),
            etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
                * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
              * ((HM μ).f k l * (HM μ).f k l')) := by
    rw [show (∑ k ∈ excited (Lab (HM μ).N),
          etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
              * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
            • ((creOf (HM μ).m ((HM μ).f k)).comp (annOf (HM μ).m ((HM μ).f k))))
        = ∑ k ∈ excited (Lab (HM μ).N),
            besselOpMat (HM μ).m
              (fun l l' => etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
                  * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
                * ((HM μ).f k l * (HM μ).f k l')) from
        Finset.sum_congr rfl fun k _ => by
          have h1 : ((creOf (HM μ).m ((HM μ).f k)).comp (annOf (HM μ).m ((HM μ).f k)))
              = besselOpMat (HM μ).m (fun l l' => (HM μ).f k l * (HM μ).f k l') :=
            creOf_comp_annOf_eq_besselOpMat _ _
          rw [h1]
          exact (besselOpMat_smul (m := (HM μ).m) _ _).symm.trans
            (congrArg (besselOpMat (HM μ).m)
              (by funext l l'; simp only [Pi.smul_apply, smul_eq_mul]))]
    rw [besselOpMat_sum_finset]
  rw [hinner]
  exact (besselOpMat_smul (m := (HM μ).m) (1/32) _).symm.trans
    (congrArg (besselOpMat (HM μ).m) (by
      funext l l'
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]))

/-- **`Gop` is `besselOpMat` of the masked θ-frame.** -/
theorem Gop_eq_besselOpMat (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (honT v h fc fu HM μ).Gop (honE v h fc fu HM μ)
      = besselOpMat (HM μ).m
          (fun l l' => ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
            ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
              * (honE v h fc fu HM μ).hatChiSq (s' - s))
              * ((HM μ).g s' l * (HM μ).g s l')) := by
  show (∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
        ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
            * (honE v h fc fu HM μ).hatChiSq (s' - s))
          • ((honT v h fc fu HM μ).taDag s' ∘ₗ (honT v h fc fu HM μ).ta s))
      = besselOpMat (HM μ).m
          (fun l l' => ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
            ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
              * (honE v h fc fu HM μ).hatChiSq (s' - s))
              * ((HM μ).g s' l * (HM μ).g s l'))
  have hstep : ∀ s s' : Lab (HM μ).N,
      ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
          * (honE v h fc fu HM μ).hatChiSq (s' - s))
        • ((honT v h fc fu HM μ).taDag s' ∘ₗ (honT v h fc fu HM μ).ta s)
      = besselOpMat (HM μ).m
          (fun l l' => ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
              * (honE v h fc fu HM μ).hatChiSq (s' - s))
              * ((HM μ).g s' l * (HM μ).g s l')) := by
    intro s s'
    have h1 : ((honT v h fc fu HM μ).taDag s' ∘ₗ (honT v h fc fu HM μ).ta s)
        = besselOpMat (HM μ).m (fun l l' => (HM μ).g s' l * (HM μ).g s l') := by
      rw [honT_taDag, honT_ta]
      exact creOf_comp_annOf_eq_besselOpMat _ _
    rw [h1]
    exact (besselOpMat_smul (m := (HM μ).m) _ _).symm.trans
      (congrArg (besselOpMat (HM μ).m)
        (by funext l l'; simp only [Pi.smul_apply, smul_eq_mul]))
  rw [show (∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
        ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
            * (honE v h fc fu HM μ).hatChiSq (s' - s))
          • ((honT v h fc fu HM μ).taDag s' ∘ₗ (honT v h fc fu HM μ).ta s))
      = ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
          besselOpMat (HM μ).m
            (fun l l' => ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
                * (honE v h fc fu HM μ).hatChiSq (s' - s))
                * ((HM μ).g s' l * (HM μ).g s l')) from
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => hstep s s']
  rw [besselOpMat_sum_finset]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [besselOpMat_sum_finset]

/-! ## 2. The three one-body matrices, and the reduction -/

section Mats

variable (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ)

/-- **The `Gop` matrix**: the localised `Σ_j Q_{L,j} χ_Λ² Q_{L,j}` in the θ-frame. -/
noncomputable def GchiA : Fin (HM μ).m → Fin (HM μ).m → ℝ := fun l l' =>
  ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
    ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
      * (honE v h fc fu HM μ).hatChiSq (s' - s))
      * ((HM μ).g s' l * (HM μ).g s l')

/-- **The χ-frame matrix** whose `besselOpMat` is `allNumOp = Σ_k a_k†a_k`. -/
noncomputable def GchiF : Fin (HM μ).m → Fin (HM μ).m → ℝ := fun l l' =>
  ∑ k : Lab (HM μ).N, (HM μ).f k l * (HM μ).f k l'

/-- **The `η_H`-weighted χ-frame** whose `besselOpMat` is `NH = n₊^H`. -/
noncomputable def GchiT : Fin (HM μ).m → Fin (HM μ).m → ℝ := fun l l' =>
  (1 / 32) * ∑ k ∈ excited (Lab (HM μ).N),
    etaH fu (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
        * Real.sqrt (μ * _root_.BoseGases.a v)) ((honF v h fc fu HM μ).kmom k)
      * ((HM μ).f k l * (HM μ).f k l')

/-- `besselOpMat` of the `GchiA` matrix is `Gop`. -/
theorem besselOpMat_GchiA :
    besselOpMat (HM μ).m (GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
      = (honT v h fc fu HM μ).Gop (honE v h fc fu HM μ) :=
  (Gop_eq_besselOpMat (v := v) (h := h) (fc := fc) (fu := fu) HM μ).symm

/-- `besselOpMat` of the `GchiF` matrix is `allNumOp`. -/
theorem besselOpMat_GchiF :
    besselOpMat (HM μ).m (GchiF HM μ)
      = (honF v h fc fu HM μ).allNumOp :=
  (allNumOp_eq_besselOpMat (v := v) (h := h) (fc := fc) (fu := fu) HM μ).symm

/-- `besselOpMat` of the `GchiT` matrix is `n₊^H` (`T.NH`). -/
theorem besselOpMat_GchiT :
    besselOpMat (HM μ).m (GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
      = (honT v h fc fu HM μ).NH :=
  (NH_eq_besselOpMat (v := v) (h := h) (fc := fc) (fu := fu) HM μ).symm

end Mats

/-- **The reduction of FS l.3253 to one-body linear algebra.**  If the matrix
`(1+ε)·GchiF + (Cχ/(32ε))·GchiT − GchiA` is symmetric and positive semidefinite (as a
quadratic form on `Fin m → ℝ`), then `GchiAt` holds at that datum.  This is the exact
interface between `Work.BoseRowQ2.Rows` and the one-body estimates; proving the matrix
inequality (the "smooth mask" estimate) is the analytic content of the row. -/
theorem GchiAt_of_mat {Cχ : ℝ} (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsym : ∀ l l' : Fin (HM μ).m,
      ((1 + ε) * GchiF HM μ l l'
        + (Cχ / ε) * GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l'
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
      = ((1 + ε) * GchiF HM μ l' l
        + (Cχ / ε) * GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ l' l
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l' l))
    (hpsd : ∀ u : Fin (HM μ).m → ℝ,
      0 ≤ ∑ l, ∑ l', u l *
        ((1 + ε) * GchiF HM μ l l'
          + (Cχ / ε) * GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l'
          - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l') * u l') :
    GchiAt (v := v) (h := h) (fc := fc) (fu := fu) Cχ HM μ ε := by
  intro Ψ
  have key := besselOpMat_le_of_mat (m := (HM μ).m)
    (A := GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
    (B := fun l l' => (1 + ε) * GchiF HM μ l l')
    (C := fun l l' => (Cχ / ε) * GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
    (fun l l' => hsym l l') (fun u => hpsd u) Ψ
  rw [show (fun l l' => (1 + ε) * GchiF HM μ l l') = (1 + ε) • GchiF HM μ from by
        funext l l'; simp only [Pi.smul_apply, smul_eq_mul],
      show (fun l l' => Cχ / ε * GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l')
          = (Cχ / ε) • GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ from by
        funext l l'; simp only [Pi.smul_apply, smul_eq_mul]] at key
  rw [besselOpMat_smul, besselOpMat_smul] at key
  rw [besselOpMat_GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ,
    besselOpMat_GchiF (v := v) (h := h) (fc := fc) (fu := fu) HM μ,
    besselOpMat_GchiT (v := v) (h := h) (fc := fc) (fu := fu) HM μ] at key
  rw [← Work.BoseB7.FockData.qw_smul, ← Work.BoseB7.FockData.qw_smul]
  exact key
end Honest

end Work.BoseRowQ2
