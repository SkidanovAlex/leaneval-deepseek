/-
  WilG4a : area G4a of the Wilkie/Pfaffian project (BNZ §5.1, the `n = 1` base case).

  This module proves that the `ℝ`-coordinates version `FLem1 S p` of the family lemma
  (BNZ Lemma 5.1 for `n = 1`, phrased for real variables and the `iteratedDeriv` API)
  implies the frozen Fin-coordinates version `WilkiesDesign.CG.FLem S p 1`.

  The translation is the evident one: a chart `φ` of the `Fin 1 → ℝ` cube corresponds to
  the real chart `l ↦ t ↦ φ l (t)` (here `curryChart`), and the family `F` on the cube
  corresponds to the real family `uncurryFam F i l s = F i l (fun _ => s)`.  The two
  non-trivial points are

  * `famGraph_eq_graphFam`: `famGraph ψ` (the frozen `n = 1` graph) is `graphFam` of the
    corresponding real family;

  * the calculus bridge between the `Fin 1 → ℝ` cube (with `iteratedFDeriv` and operator
    norms) and the real interval `I = (0,1)` (with `iteratedDeriv`): `contDiffOn_fin1` and
    `norm_iteratedFDeriv_fin1`.  Both go through the linear isometry equivalence
    `(Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, `x ↦ x 0`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign WilkiesDesign.CG

/-! ## The graphs of the two encodings -/

/-- `famGraph` (the frozen `n = 1` graph, in `Fin`-coordinates) of a family
`ψ : ℝᵖ → (Fin 1 → ℝ) → ℝ` is the `graphFam` of the corresponding real family
`l ↦ t ↦ ψ l (fun _ => t)`. -/
theorem famGraph_eq_graphFam {p : ℕ} (ψ : (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    famGraph ψ = Work.WilG4a.graphFam (fun l t => ψ l (fun _ => t)) := by
  ext z
  simp only [famGraph, Work.WilG4a.graphFam, graphOf, Set.mem_ofPred_eq]
  have h1 : (fun i : Fin p => Fin.init z (Fin.castAdd 1 i)) =
      (fun i : Fin p => Fin.init z (Fin.castSucc i)) := by
    funext i
    simp only [Fin.init]
    congr 1
  have h2 : (fun j : Fin 1 => Fin.init z (Fin.natAdd p j)) =
      (fun _ : Fin 1 => Fin.init z (Fin.last p)) := by
    funext j
    congr 1
    ext
    simp only [Fin.natAdd, Fin.val_last]
    omega
  rw [h1, h2]

/-! ## The calculus bridge `(Fin 1 → ℝ) ↔ ℝ` -/

/-- The linear isometry equivalence `(Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ`, `x ↦ x 0`. -/
def gR : (Fin 1 → ℝ) ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := LinearEquiv.funUnique (Fin 1) ℝ ℝ
  norm_map' := by intro x; simp [Pi.norm_def]

theorem gR_apply (x : Fin 1 → ℝ) : gR x = x 0 := by
  show x default = x 0
  rw [Fin.default_eq_zero]

/-- The operator norm of the `m`-th Fréchet derivative of the "lifted" real function
`t ↦ H (t 0)` at a point of the cube is the absolute value of the `m`-th ordinary
derivative of `H`. -/
theorem norm_iteratedFDeriv_fin1 (H : ℝ → ℝ) (m : ℕ) (x : Fin 1 → ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : Fin 1 → ℝ => H (t 0)) x‖ = |iteratedDeriv m H (x 0)| := by
  have hfun : (fun t : Fin 1 → ℝ => H (t 0)) = H ∘ gR := by
    funext t
    rw [Function.comp_apply, gR_apply]
  rw [hfun, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, gR_apply,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]

/-- Smoothness of `t ↦ H (t 0)` on the cube is smoothness of `H` on the interval. -/
theorem contDiffOn_fin1 {H : ℝ → ℝ} {r : ℕ} :
    ContDiffOn ℝ r (fun t : Fin 1 → ℝ => H (t 0)) (openCube 1) ↔
      ContDiffOn ℝ r H (Work.WilG4a.I) := by
  have hfun : (fun t : Fin 1 → ℝ => H (t 0)) =
      H ∘ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) := by
    funext t
    simp [Function.comp, ContinuousLinearEquiv.coe_funUnique, Fin.default_eq_zero]
  have hpre : (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) ⁻¹' (Work.WilG4a.I) =
      openCube 1 := by
    ext x
    simp [Work.WilG4a.I, openCube, ContinuousLinearEquiv.coe_funUnique, Fin.default_eq_zero]
  rw [hfun, ← hpre]
  exact ContinuousLinearEquiv.contDiffOn_comp_iff
    (e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) (s := Work.WilG4a.I)

/-! ## The two chart dictionaries -/

/-- A real chart `φ` becomes a chart of the `Fin 1 → ℝ` cube: the single coordinate of the
graph is `φ l (x 0)`. -/
def curryChart {p : ℕ} (φ : (Fin p → ℝ) → ℝ → ℝ) :
    Fin 1 → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ := fun _ l x => φ l (x 0)

@[simp] theorem curryChart_apply {p : ℕ} (φ : (Fin p → ℝ) → ℝ → ℝ) (j : Fin 1)
    (l : Fin p → ℝ) (x : Fin 1 → ℝ) : curryChart φ j l x = φ l (x 0) := rfl

/-- A family on the `Fin 1 → ℝ` cube becomes a family on the reals. -/
def uncurryFam {p k : ℕ} (F : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) :
    Fin k → (Fin p → ℝ) → ℝ → ℝ := fun i l s => F i l (fun _ => s)

@[simp] theorem uncurryFam_apply {p k : ℕ} (F : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ)
    (i : Fin k) (l : Fin p → ℝ) (s : ℝ) : uncurryFam F i l s = F i l (fun _ => s) := rfl

/-! ## The transfer -/

theorem fleem_one_of_fleem1 (S : WilkiesDesign.SOMin) (p : ℕ) (h : Work.WilG4a.FLem1 S p) : WilkiesDesign.CG.FLem S p 1 := by
  intro F0
  obtain ⟨a, b, c, hbc⟩ := h F0
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε0 hε1 Λ F hΩ hI
  obtain ⟨Φ₁, hcard, hcharts, hcov⟩ :=
    hbc D r k ε hε0 hε1 Λ (uncurryFam F)
      (fun i => by
        have heq : graphFam (uncurryFam F i) = famGraph (F i) := by
          rw [famGraph_eq_graphFam (ψ := F i)]
          congr 1
        rw [heq]
        exact hΩ i)
      (fun i l hl s hs => by
        exact hI i l hl (fun _ => s) (fun j => by simpa using hs))
  refine ⟨Φ₁.image curryChart, ?_, ?_, ?_⟩
  · have h1 : ((Φ₁.image curryChart).card : ℝ) ≤ (Φ₁.card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    exact le_trans h1 hcard
  · intro φ' hφ'
    rw [Finset.mem_image] at hφ'
    obtain ⟨φ, hφ, rfl⟩ := hφ'
    obtain ⟨hgraph, hrest⟩ := hcharts φ hφ
    refine ⟨?_, ?_⟩
    · intro j
      have hfe : (fun l t => curryChart φ j l (fun _ => t)) = φ := by
        funext l t
        simp only [curryChart_apply]
      rw [famGraph_eq_graphFam, hfe]
      exact hgraph
    · intro l hl
      obtain ⟨hin, hCD⟩ := hrest l hl
      refine ⟨?_, ?_⟩
      · intro t ht j
        simp only [curryChart_apply]
        exact hin (t 0) (ht 0)
      · refine fun i => ⟨?_, ?_⟩
        · have hH : (fun t : Fin 1 → ℝ => F i l (fun j => curryChart φ j l t)) =
              (fun t : Fin 1 → ℝ => (fun s : ℝ => uncurryFam F i l (φ l s)) (t 0)) := by
            funext t
            simp only [curryChart_apply, uncurryFam_apply]
          rw [hH]
          exact (contDiffOn_fin1 (H := fun s : ℝ => uncurryFam F i l (φ l s))).mpr (hCD i).1
        · intro m hm t ht
          have hH : (fun u : Fin 1 → ℝ => F i l (fun j => curryChart φ j l u)) =
              (fun u : Fin 1 → ℝ => (fun s : ℝ => uncurryFam F i l (φ l s)) (u 0)) := by
            funext u
            simp only [curryChart_apply, uncurryFam_apply]
          have hE : ‖iteratedFDeriv ℝ m
              (fun u : Fin 1 → ℝ => (fun s : ℝ => uncurryFam F i l (φ l s)) (u 0)) t‖ =
              |iteratedDeriv m (fun s : ℝ => uncurryFam F i l (φ l s)) (t 0)| :=
            norm_iteratedFDeriv_fin1 (fun s : ℝ => uncurryFam F i l (φ l s)) m t
          rw [hH, hE]
          exact (hCD i).2 m hm (t 0) (ht 0)
  · intro l hl x hx
    obtain ⟨φ, hφ, t, ht, hb⟩ := hcov l hl (x 0) (hx 0)
    refine ⟨curryChart φ, Finset.mem_image.mpr ⟨φ, hφ, rfl⟩, fun _ : Fin 1 => t, ?_, ?_⟩
    · intro j
      simpa using ht
    · intro i
      have h1 : F i l (fun j => curryChart φ j l (fun _ : Fin 1 => t)) =
          uncurryFam F i l (φ l t) := by
        simp only [curryChart_apply, uncurryFam_apply]
      have h2 : F i l x = uncurryFam F i l (x 0) := by
        rw [uncurryFam_apply]
        congr 1
        funext j
        fin_cases j
        rfl
      rw [h1, h2]
      exact hb i

end Work.WilG4a
