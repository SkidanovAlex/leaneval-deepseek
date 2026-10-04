import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.HAuxDefs
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.GtTowerSuccEqSwap
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.SlotAddAOfLocal
import Submission.Work.Diff.EXT.ConnCov.RicTr.DT.DeltaBaseTensStep
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.DT

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- Smoothness of a one-slot update of a tuple of smooth fields. -/
theorem smE_update_aux {k : ℕ} {v : Fin k → TF (I := I) (M := M)} (i : Fin k)
    {W : TF (I := I) (M := M)} (hv : ∀ j, SmE I M (v j)) (hW : SmE I M W) :
    ∀ j, SmE I M (Function.update v i W j) := by
  intro j
  by_cases h : j = i
  · rw [h, Function.update_self]; exact hW
  · rw [Function.update_of_ne h (f := v)]; exact hv j

/-- Smoothness of the δ-tower on smooth fields. -/
theorem deltaTower_sm
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ j : ℕ, VOpSm (I := I) (M := M) (deltaTower G t j) := by
  intro j
  induction j with
  | zero =>
      intro v X Y hv hX hY
      change SmE I M (fun y : M =>
        (lcOf (G t)) X y (Y y) - (lcOf (G 0)) X y (Y y))
      intro x
      exact ((lcOf_apply_smE hLC (G t) X Y hX hY) x).sub_section
        ((lcOf_apply_smE hLC (G 0) X Y hX hY) x)
  | succ j ih =>
      intro v X Y hv hX hY
      have hv' : ∀ i : Fin j, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hU : ∀ i : Fin j, SmE I M (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y)) :=
        fun i => lcOf_apply_smE hLC (G 0) (v i.succ) (v 0) (hv i.succ) hv0
      change SmE I M (fun x : M =>
        (lcOf (G 0)) (deltaTower G t j (fun i : Fin j => v i.succ) X Y) x (v 0 x)
          - (∑ i : Fin j, deltaTower G t j
              (Function.update (fun j' : Fin j => v j'.succ) i
                (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) X Y x)
          - deltaTower G t j (fun i : Fin j => v i.succ)
              (fun y => (lcOf (G 0)) X y (v 0 y)) Y x
          - deltaTower G t j (fun i : Fin j => v i.succ) X
              (fun y => (lcOf (G 0)) Y y (v 0 y)) x)
      intro x
      have h1 := (lcOf_apply_smE hLC (G 0)
        (deltaTower G t j (fun i : Fin j => v i.succ) X Y) (v 0)
        (ih _ X Y hv' hX hY) hv0) x
      have h2 : ContMDiffAt I I.tangent ∞ (T% (fun y : M => ∑ i : Fin j,
          deltaTower G t j
            (Function.update (fun j' : Fin j => v j'.succ) i
              (fun y => (lcOf (G 0)) (v i.succ) y (v 0 y))) X Y y)) x :=
        ContMDiffAt.sum_section (s := (Finset.univ : Finset (Fin j)))
          (fun i _ => (ih _ X Y (smE_update_aux i hv' (hU i)) hX hY) x)
      have h3 := (ih _ _ Y hv' (lcOf_apply_smE hLC (G 0) X (v 0) hX hv0) hY) x
      have h4 := (ih _ X _ hv' hX (lcOf_apply_smE hLC (G 0) Y (v 0) hY hv0)) x
      exact ((h1.sub_section h2).sub_section h3).sub_section h4

/-- The `SlotAdd` and smoothness of the `aOf`-tower (`∇^{G 0, k}aOf G t`). -/
theorem aOf_tower_slotAdd_sm
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ k : ℕ,
      SlotAdd (tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) k)
        ∧ ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
            (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmE I M C →
            SmF I M (tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t)
              k v A B C) :=
  tower_slotAdd_smF hLC (G 0) (base := fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t)
    (slotAdd_aOf_local hLC G t)
    (fun _ A B C hA hB hC => aOf_smF hLC G t hA hB hC)

/-! ## Additivity and smoothness of the metric tower -/

theorem gtTower_zero_apply (G : ℝ → SMet I M) (t : ℝ)
    (d : Fin 0 → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M)) :
    gtTower G t 0 d Y Z = gtBase G t d Y Z := rfl

/-- Additivity of the metric tower in its *first* value slot. -/
theorem gtTower_add_val0
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ i : ℕ, ∀ (d : Fin i → TF (I := I) (M := M))
      (Y₁ Y₂ Z : TF (I := I) (M := M)),
      (∀ j, SmE I M (d j)) → SmE I M Y₁ → SmE I M Y₂ → SmE I M Z →
      gtTower G t i d (Y₁ + Y₂) Z = gtTower G t i d Y₁ Z + gtTower G t i d Y₂ Z := by
  intro i
  induction i with
  | zero =>
      intro d Y₁ Y₂ Z hd hY₁ hY₂ hZ
      funext x
      show (G t).inner x ((Y₁ + Y₂) x) (Z x)
        = (G t).inner x (Y₁ x) (Z x) + (G t).inner x (Y₂ x) (Z x)
      rw [show (Y₁ + Y₂) x = Y₁ x + Y₂ x from rfl, map_add, ContinuousLinearMap.add_apply]
  | succ i ih =>
      intro d Y₁ Y₂ Z hd hY₁ hY₂ hZ
      have hdc : ∀ j : Fin i, SmE I M ((fun j : Fin i => d (Fin.castSucc j)) j) :=
        fun j => hd (Fin.castSucc j)
      have hν : gtTower G t (i + 1) d (Y₁ + Y₂) Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) (Y₁ + Y₂) Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z (Y₁ + Y₂) := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d (Y₁ + Y₂) Z hd
          (hY₁.add_section hY₂) hZ x
      have h1 : gtTower G t (i + 1) d Y₁ Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₁ Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₁ := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y₁ Z hd hY₁ hZ x
      have h2 : gtTower G t (i + 1) d Y₂ Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₂ Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₂ := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y₂ Z hd hY₂ hZ x
      have hadd := (aOf_tower_slotAdd_sm hLC G t i).1
      rw [hν, h1, h2,
        hadd.2.2.1 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y₁ Y₂ Z
          hdc (hd (Fin.last i)) hY₁ hY₂ hZ,
        hadd.2.2.2 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y₁ Y₂
          hdc (hd (Fin.last i)) hZ hY₁ hY₂]
      funext x
      simp only [Pi.add_apply]
      ring

/-- Additivity of the metric tower in its *second* value slot. -/
theorem gtTower_add_val1
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ i : ℕ, ∀ (d : Fin i → TF (I := I) (M := M))
      (Y Z₁ Z₂ : TF (I := I) (M := M)),
      (∀ j, SmE I M (d j)) → SmE I M Y → SmE I M Z₁ → SmE I M Z₂ →
      gtTower G t i d Y (Z₁ + Z₂) = gtTower G t i d Y Z₁ + gtTower G t i d Y Z₂ := by
  intro i
  induction i with
  | zero =>
      intro d Y Z₁ Z₂ hd hY hZ₁ hZ₂
      funext x
      show (G t).inner x (Y x) ((Z₁ + Z₂) x)
        = (G t).inner x (Y x) (Z₁ x) + (G t).inner x (Y x) (Z₂ x)
      rw [show (Z₁ + Z₂) x = Z₁ x + Z₂ x from rfl, map_add]
  | succ i ih =>
      intro d Y Z₁ Z₂ hd hY hZ₁ hZ₂
      have hdc : ∀ j : Fin i, SmE I M ((fun j : Fin i => d (Fin.castSucc j)) j) :=
        fun j => hd (Fin.castSucc j)
      have hν : gtTower G t (i + 1) d Y (Z₁ + Z₂)
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y (Z₁ + Z₂)
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) (Z₁ + Z₂) Y := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y (Z₁ + Z₂) hd
          hY (hZ₁.add_section hZ₂) x
      have h1 : gtTower G t (i + 1) d Y Z₁
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z₁
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z₁ Y := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y Z₁ hd hY hZ₁ x
      have h2 : gtTower G t (i + 1) d Y Z₂
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z₂
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z₂ Y := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y Z₂ hd hY hZ₂ x
      have hadd := (aOf_tower_slotAdd_sm hLC G t i).1
      rw [hν, h1, h2,
        hadd.2.2.2 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z₁ Z₂
          hdc (hd (Fin.last i)) hY hZ₁ hZ₂,
        hadd.2.2.1 (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z₁ Z₂ Y
          hdc (hd (Fin.last i)) hZ₁ hZ₂ hY]
      funext x
      simp only [Pi.add_apply]
      ring

/-- Smoothness of the metric tower on smooth fields. -/
theorem gtTower_sm
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ i : ℕ, ∀ (d : Fin i → TF (I := I) (M := M)) (Y Z : TF (I := I) (M := M)),
      (∀ j, SmE I M (d j)) → SmE I M Y → SmE I M Z →
      SmF I M (gtTower G t i d Y Z) := by
  intro i
  induction i with
  | zero =>
      intro d Y Z hd hY hZ
      exact gtBase_sm hLC G t (fun i => i.elim0) Y Z (fun i => i.elim0) hY hZ
  | succ i ih =>
      intro d Y Z hd hY hZ
      have hdc : ∀ j : Fin i, SmE I M ((fun j : Fin i => d (Fin.castSucc j)) j) :=
        fun j => hd (Fin.castSucc j)
      have hν : gtTower G t (i + 1) d Y Z
          = tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z
            + tower (lcOf (G 0)) (fun (_ : Fin 0 → TF (I := I) (M := M)) => aOf G t) i
                (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y := by
        funext x
        simpa only [Pi.add_apply] using gtTower_succ_eq_swap hLC G t i d Y Z hd hY hZ x
      rw [hν]
      have hsm := (aOf_tower_slotAdd_sm hLC G t i).2
      intro x
      exact ((hsm _ _ _ _ hdc (hd (Fin.last i)) hY hZ) x).add
        ((hsm _ _ _ _ hdc (hd (Fin.last i)) hZ hY) x)

/-- Smoothness of the terms of the expansion on smooth fields. -/
theorem selTerm_sm (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) :
    ∀ (c i j : ℕ) (F : Fin i → Fin c) (G' : Fin j → Fin c)
      (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ k, SmE I M (v k)) → SmE I M A → SmE I M B → SmE I M C →
      SmF I M (selTerm G t c i j F G' v A B C) := by
  intro c i j F G' v A B C hv hA hB hC
  have hd : ∀ p : Fin i, SmE I M ((fun k => v (F k)) p) := fun p => hv (F p)
  have hd' : ∀ p : Fin j, SmE I M ((fun k => v (G' k)) p) := fun p => hv (G' p)
  have hW : SmE I M (deltaTower G t j (fun k => v (G' k)) B A) :=
    deltaTower_sm hLC G t j _ B A hd' hB hA
  exact gtTower_sm hLC G t i _ _ _ hd hW hC

/-- **The two selections cover `Fin c`.**  If `F : Fin i → Fin c` and `G' : Fin j → Fin c` are
injective with disjoint ranges and `i + j = c`, then every `k : Fin c` is in one of the two ranges
(the cardinalities add up to `c`). -/
theorem range_union_eq_univ {c i j : ℕ} (hc : i + j = c) (F : Fin i → Fin c) (G' : Fin j → Fin c)
    (hf : Function.Injective F) (hg : Function.Injective G')
    (hdisj : Disjoint (Set.range F) (Set.range G')) :
    ∀ k : Fin c, k ∈ Set.range F ∪ Set.range G' := by
  have hdisj' : Disjoint (Finset.univ.image F) (Finset.univ.image G') := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_image] at hk hk'
    obtain ⟨a, _, ha⟩ := hk
    obtain ⟨b, _, hb⟩ := hk'
    exact Set.disjoint_left.mp hdisj (Set.mem_range.mpr ⟨a, ha⟩) (Set.mem_range.mpr ⟨b, hb⟩)
  have hcF : (Finset.univ.image F).card = i := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hcG : (Finset.univ.image G').card = j := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hcard : (Finset.univ.image F ∪ Finset.univ.image G').card = Fintype.card (Fin c) := by
    rw [Finset.card_union_of_disjoint hdisj', hcF, hcG, Fintype.card_fin, hc]
  have huniv : Finset.univ.image F ∪ Finset.univ.image G' = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  intro k
  have hk : k ∈ Finset.univ.image F ∪ Finset.univ.image G' := by rw [huniv]; exact Finset.mem_univ k
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hk
  rcases hk with ⟨p, _, hp⟩ | ⟨p, _, hp⟩
  · exact Or.inl (Set.mem_range.mpr ⟨p, hp⟩)
  · exact Or.inr (Set.mem_range.mpr ⟨p, hp⟩)

end Work.Diff.EXT.ConnCov.DT
