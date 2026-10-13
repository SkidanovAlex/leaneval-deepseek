/-
  WilC4/deepThetaG_definableB : an independent proof of the `∅`-definability of `DeepThetaG`.

  This is a *backup* for `Submission/Work/WilC4/deepThetaG_definable.lean` (which is the version
  assembled from `DRatBody_definable` etc.).  It only relies on the already-proved pieces
  `Submission.Work.WilC4.DeepThetaGDefs` (definitions and the semantic identifications),
  `Submission.Work.WilC4.DRDeep_definable` (the deepness atom) and
  `Submission.Work.WilC4.definable_isGLB_family` (the graph of a glb over a definable family).

  **This is the version that `Submission.Work.WilC4.deep_ratio_scale_bdd` uses**: the primary
  chain needs `Submission.Work.WilC4.DRatBody_definable`, which at the time of writing is still
  unproved, so importing `deepThetaG_definable` would make `deep_ratio_scale_bdd` depend on an
  unproved declaration.  Nothing here is `private`, and all the auxiliary names live in the
  namespace `Work.WilC4.DRB` so that they cannot clash with the primary chain.

  The only work here is the definability of the fourteen quantifier-free conjuncts `drP1 … drP14`
  of `DRatBody`, their intersection, and the final glb assembly.

  The main file `Submission.Work.WilC4.deep_ratio_scale_bdd` imports
  `Submission.Work.WilC4.deepThetaG_definable` (the primary version).
-/
import Mathlib
import Submission.Work.WilC4.DeepThetaGDefs
import Submission.Work.WilC4.DRDeep_definable
import Submission.Work.WilC4.definable_isGLB_family

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

/- The auxiliaries are collected in a namespace of their own so that no name here can clash
with the primary development (`Submission.Work.WilC4.deepThetaG_definable`). -/
namespace DRB

/-! ## 1. The fourteen conjuncts of `DRatBody` -/

theorem drP1_definable : (Set.univ : Set ℝ).Definable LRc (drP1 (k := k)) :=
  CandBodyDefs.univ_of_empty (definable_lt_const (ρ := DRIdx k) (0 : ℝ) (dx : DRIdx k))

theorem drP2_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (drP2 (k := k) Y) :=
  CandBodyDefs.univ_of_empty (GrSub_definable hY embD dx dy)

theorem drP3_definable : (Set.univ : Set ℝ).Definable LRc (drP3 (k := k)) := by
  have h := definable_ne_LRc (σ := DRIdx k) (MvPolynomial.X (dy : DRIdx k)) 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, drP3, Set.mem_setOf_eq, MvPolynomial.eval_X, map_zero]

theorem drP4_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (drP4 (k := k) Y) :=
  CandBodyDefs.univ_of_empty (GrSub_definable hY embD dz dy2)

theorem drP5_definable : (Set.univ : Set ℝ).Definable LRc (drP5 (k := k)) := by
  have h := definable_eval_eq_LRc (σ := DRIdx k)
    (MvPolynomial.X (dz : DRIdx k) - MvPolynomial.C 2 * MvPolynomial.X (dx : DRIdx k)) 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, drP5, Set.mem_setOf_eq, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, sub_eq_zero]

theorem drP6_definable : (Set.univ : Set ℝ).Definable LRc (drP6 (k := k)) := by
  have h := definable_eval_eq_LRc (σ := DRIdx k)
    (MvPolynomial.X (dw : DRIdx k) * MvPolynomial.X (dy : DRIdx k) -
      MvPolynomial.X (dy2 : DRIdx k)) 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, drP6, Set.mem_setOf_eq, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_X, sub_eq_zero]

theorem drP7_definable : (Set.univ : Set ℝ).Definable LRc (drP7 (k := k)) := by
  have h1 := definable_le_LRc (σ := DRIdx k) (MvPolynomial.X (dβ : DRIdx k))
    (MvPolynomial.X (dw : DRIdx k))
  have h2 := definable_le_LRc (σ := DRIdx k) (MvPolynomial.X (dw : DRIdx k))
    (-(MvPolynomial.X (dβ : DRIdx k)))
  have h := h1.union h2
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, drP7, Set.mem_setOf_eq, Set.mem_union, MvPolynomial.eval_X,
    MvPolynomial.eval_neg]

theorem drP8_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (drP8 (k := k) Y) :=
  CandBodyDefs.univ_of_empty (GrSub_definable hY embD dz2 dv)

theorem drP9_definable : (Set.univ : Set ℝ).Definable LRc (drP9 (k := k)) := by
  have h := definable_eval_eq_LRc (σ := DRIdx k)
    (MvPolynomial.X (dz2 : DRIdx k) -
      MvPolynomial.X (dβ : DRIdx k) * MvPolynomial.X (dx : DRIdx k)) 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, drP9, Set.mem_setOf_eq, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_X, sub_eq_zero]

theorem drP10_definable {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (drP10 (k := k) Y) :=
  CandBodyDefs.univ_of_empty (GrSub_definable hY embD dq0 dy0)

theorem drP11_definable : (Set.univ : Set ℝ).Definable LRc (drP11 (k := k)) :=
  definable_isDivR (dx : DRIdx k) (dβ : DRIdx k) (dq0 : DRIdx k)

theorem drP12_definable : (Set.univ : Set ℝ).Definable LRc (drP12 (k := k)) :=
  definable_isDivR (dv : DRIdx k) (dy : DRIdx k) (dA : DRIdx k)

theorem drP13_definable : (Set.univ : Set ℝ).Definable LRc (drP13 (k := k)) :=
  definable_isDivR (dy : DRIdx k) (dy0 : DRIdx k) (dB : DRIdx k)

theorem drP14_eq_max : drP14 (k := k) =
    {g : DRIdx k → ℝ | g dA ≤ g dt} ∩ {g : DRIdx k → ℝ | g dB ≤ g dt} ∩
      ({g : DRIdx k → ℝ | g dt = g dA} ∪ {g : DRIdx k → ℝ | g dt = g dB}) := by
  ext g
  simp only [drP14, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h]; exact le_max_left _ _
    · rw [h]; exact le_max_right _ _
    · rcases max_cases (g dA) (g dB) with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact Or.inl (h.trans hm)
      · exact Or.inr (h.trans hm)
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · have hmaxle : max (g dA) (g dB) ≤ g dt := max_le h1 h2
      have hdtt : g dt ≤ max (g dA) (g dB) := by rw [h3]; exact le_max_left _ _
      exact (le_antisymm hmaxle hdtt).symm
    · have hmaxle : max (g dA) (g dB) ≤ g dt := max_le h1 h2
      have hdtt : g dt ≤ max (g dA) (g dB) := by rw [h3]; exact le_max_right _ _
      exact (le_antisymm hmaxle hdtt).symm

theorem drP14_definable : (Set.univ : Set ℝ).Definable LRc (drP14 (k := k)) := by
  rw [drP14_eq_max]
  have h1 := definable_le_LRc (σ := DRIdx k) (MvPolynomial.X (dA : DRIdx k))
    (MvPolynomial.X (dt : DRIdx k))
  have h2 := definable_le_LRc (σ := DRIdx k) (MvPolynomial.X (dB : DRIdx k))
    (MvPolynomial.X (dt : DRIdx k))
  have h3 := definable_eval_eq_LRc (σ := DRIdx k)
    (MvPolynomial.X (dt : DRIdx k) - MvPolynomial.X (dA : DRIdx k)) 0
  have h4 := definable_eval_eq_LRc (σ := DRIdx k)
    (MvPolynomial.X (dt : DRIdx k) - MvPolynomial.X (dB : DRIdx k)) 0
  have h3' : (Set.univ : Set ℝ).Definable LRc
      {g : DRIdx k → ℝ | g dt = g dA} := by
    convert h3 using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, sub_eq_zero]
  have h4' : (Set.univ : Set ℝ).Definable LRc
      {g : DRIdx k → ℝ | g dt = g dB} := by
    convert h4 using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_X, sub_eq_zero]
  have h1' : (Set.univ : Set ℝ).Definable LRc {g : DRIdx k → ℝ | g dA ≤ g dt} := by
    convert h1 using 1
    ext g; simp [MvPolynomial.eval_X]
  have h2' : (Set.univ : Set ℝ).Definable LRc {g : DRIdx k → ℝ | g dB ≤ g dt} := by
    convert h2 using 1
    ext g; simp [MvPolynomial.eval_X]
  exact ((h1'.inter h2').inter (h3'.union h4'))

/-! ## 2. The body and its projections -/

theorem DRatBody_definable_b {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (DRatBody (k := k) Y) := by
  rw [DRatBody_eq_pieces]
  have h1 : (Set.univ : Set ℝ).Definable LRc (drP1 (k := k)) := drP1_definable
  have h2 : (Set.univ : Set ℝ).Definable LRc (drP2 (k := k) Y) := drP2_definable hY
  have h3 : (Set.univ : Set ℝ).Definable LRc (drP3 (k := k)) := drP3_definable
  have h4 : (Set.univ : Set ℝ).Definable LRc (drP4 (k := k) Y) := drP4_definable hY
  have h5 : (Set.univ : Set ℝ).Definable LRc (drP5 (k := k)) := drP5_definable
  have h6 : (Set.univ : Set ℝ).Definable LRc (drP6 (k := k)) := drP6_definable
  have h7 : (Set.univ : Set ℝ).Definable LRc (drP7 (k := k)) := drP7_definable
  have h8 : (Set.univ : Set ℝ).Definable LRc (drP8 (k := k) Y) := drP8_definable hY
  have h9 : (Set.univ : Set ℝ).Definable LRc (drP9 (k := k)) := drP9_definable
  have h10 : (Set.univ : Set ℝ).Definable LRc (drP10 (k := k) Y) := drP10_definable hY
  have h11 : (Set.univ : Set ℝ).Definable LRc (drP11 (k := k)) := drP11_definable
  have h12 : (Set.univ : Set ℝ).Definable LRc (drP12 (k := k)) := drP12_definable
  have h13 : (Set.univ : Set ℝ).Definable LRc (drP13 (k := k)) := drP13_definable
  have h14 : (Set.univ : Set ℝ).Definable LRc (drP14 (k := k)) := drP14_definable
  have h12' := h1.inter h2
  have h13' := h12'.inter h3
  have h14' := h13'.inter h4
  have h15' := h14'.inter h5
  have h16' := h15'.inter h6
  have h17' := h16'.inter h7
  have h18' := h17'.inter h8
  have h19' := h18'.inter h9
  have h20' := h19'.inter h10
  have h21' := h20'.inter h11
  have h22' := h21'.inter h12
  have h23' := h22'.inter h13
  exact h23'.inter h14

theorem DRg_definable_b {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (Set.univ : Set ℝ).Definable LRc (DRg (k := k) Y B₀) := by
  have hBody : (Set.univ : Set ℝ).Definable LRc (DRatBody (k := k) Y) :=
    DRB.DRatBody_definable_b hY
  have hDeep : (Set.univ : Set ℝ).Definable LRc (DRDeep (k := k) B₀) :=
    (DRDeep_definable hB₀).mono (Set.subset_univ _)
  exact (hBody.inter hDeep).exists_of_finite (α := Fin 2) (β := Fin k ⊕ Fin 11)

/-- For `u : Fin 2 → ℝ` and `t : ℝ`, the tuple `Fin.snoc (Fin.init u) t` is `![u 0, t]`. -/
theorem snoc_init_eq_vec2 (u : Fin 2 → ℝ) (t : ℝ) :
    Fin.snoc (Fin.init u) t = ![u 0, t] := by
  funext i
  fin_cases i
  · simp [Fin.init]
  · show Fin.snoc (Fin.init u) t (Fin.last 1) = ![u 0, t] (Fin.last 1)
    rw [Fin.snoc_last]
    simp

end DRB

theorem deepThetaG_definable_b {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (DeepThetaG (k := k) Y B₀) := by
  have hg : (Set.univ : Set ℝ).Definable LRc (DRg (k := k) Y B₀) := DRB.DRg_definable_b hY hB₀
  have hg' : (∅ : Set ℝ).Definable LRc (DRg (k := k) Y B₀) :=
    (definable_univ_iff_empty).mp hg
  have hglb := definable_isGLB_family (n := 1) hg'
  have heq : {u : Fin 2 → ℝ |
        IsGLB {t : ℝ | Fin.snoc (Fin.init u) t ∈ DRg (k := k) Y B₀} (u (Fin.last 1))} =
      {u : Fin 2 → ℝ | IsGLB (DeepRatSet (k := k) Y B₀ (u 0)) (u 1)} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    have hset : {t : ℝ | Fin.snoc (Fin.init u) t ∈ DRg (k := k) Y B₀} =
        DeepRatSet (k := k) Y B₀ (u 0) := by
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [DRB.snoc_init_eq_vec2]
      simpa using mem_DRg_iff Y B₀ ![u 0, t]
    rw [hset]
    rw [show (Fin.last (1 : ℕ)) = (1 : Fin 2) from Fin.ext rfl]
  rw [heq] at hglb
  have h1 : (Set.univ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | 1 ≤ v 0} := by
    have h := definable_le_LRc (σ := Fin 2) (MvPolynomial.C 1) (MvPolynomial.X 0)
    convert h using 1
    ext v
    simp [MvPolynomial.eval_X]
  have h1' : (∅ : Set ℝ).Definable LRc {v : Fin 2 → ℝ | 1 ≤ v 0} :=
    (definable_univ_iff_empty).mp h1
  have hset2 : DeepThetaG (k := k) Y B₀ =
      ({v : Fin 2 → ℝ | 1 ≤ v 0} ∩
        {u : Fin 2 → ℝ | IsGLB (DeepRatSet (k := k) Y B₀ (u 0)) (u 1)}) := by
    rw [DeepThetaG]
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hset2]
  exact h1'.inter hglb

end Work.WilC4
