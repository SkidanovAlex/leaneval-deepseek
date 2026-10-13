/-
# `Work.FTS_RegExport.RXT.jc3_asm` — the assembly of the joint continuity

The order-≤3 mixed slots of the strong solution are jointly continuous on the slab.  The proof
splits the displacement of the point `(z,θ,τ)` into its space part, controlled by the
Lipschitz bound `hSpace`, and its time part, controlled by `RXT.tau_cont_mixed` (the Landau
step, fed by the time-Lipschitz bound `hTau` for the order-≤2 slots).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.jc3_tau

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The elementary estimate `K · (2 · (ε/(4(K+1)))) < ε/2` for `K ≥ 0`, `ε > 0`. -/
lemma mul_two_div_lt {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    K * (2 * (ε / (4 * (K + 1)))) < ε / 2 := by
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  have h1 : (0:ℝ) < 4 * (K + 1) := by linarith
  field_simp
  nlinarith

theorem jc3_of_pieces {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T)
    (hSpace : ∀ {a b c d : ℝ}, 0 < a → a ≤ b → 0 < c → c ≤ d → d < Real.pi / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 3 →
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ| ≤ C * |z - z'|) ∧
        (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'| ≤ C * |θ - θ'|))
    (hTau : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ τ' ∈ Set.Icc (0:ℝ) T,
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ| ≤ L * |τ - τ'|)
    (hLandau : ∀ {V W : ℝ → ℝ → ℝ} {x₀ δc L K : ℝ}, 0 < δc → 0 ≤ L → 0 ≤ K →
      (∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |V x τ - V x τ'| ≤ L * |τ - τ'|) →
      (∀ τ : ℝ, 0 ≤ τ → ContinuousOn (fun x => W x τ) (Set.Icc x₀ (x₀ + δc))) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        |W x τ - W x₀ τ| ≤ K * |x - x₀|) →
      (∀ τ : ℝ, 0 ≤ τ → ∀ x ∈ Set.Icc x₀ (x₀ + δc),
        HasDerivAt (fun x' => V x' τ) (W x τ) x) →
      ∀ τ τ' : ℝ, 0 ≤ τ → 0 ≤ τ' → |τ - τ'| ≤ δc ^ 2 →
        |W x₀ τ - W x₀ τ'| ≤ (2 * L + K) * Real.sqrt |τ - τ'|) :
    ∀ j i : ℕ, j + i ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) := by
  intro j i hji
  rintro ⟨z, θ, τ⟩ hp
  change ContinuousWithinAt (fun q : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g q.2.2) q.1 q.2.1)
    (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) (z, θ, τ)
  rw [Set.mem_prod] at hp
  obtain ⟨hz, hp⟩ := hp
  rw [Set.mem_prod] at hp
  obtain ⟨hθmem, hτmem⟩ := hp
  have hzpos : 0 < z := hz
  have hθ0 : 0 < θ := hθmem.1
  have hθπ : θ < Real.pi / 2 := hθmem.2
  -- the box around `(z,θ)`
  set dθ : ℝ := min (θ / 2) ((Real.pi / 2 - θ) / 2) with hdθdef
  have hdθpos : 0 < dθ := by
    rw [hdθdef]; exact lt_min (by linarith) (by linarith)
  have hdθle : dθ ≤ (Real.pi / 2 - θ) / 2 := by rw [hdθdef]; exact min_le_right _ _
  have hdθle' : dθ ≤ θ / 2 := by rw [hdθdef]; exact min_le_left _ _
  have hθlopos : 0 < θ - dθ := by linarith
  have hθhilt : θ + dθ < Real.pi / 2 := by linarith
  obtain ⟨Cs, hCsnn, hCslip⟩ := hSpace (a := z / 2) (b := 3 * z / 2) (c := θ - dθ)
    (d := θ + dθ) (by linarith) (by linarith) hθlopos (by linarith) hθhilt
  obtain ⟨Lτ, hLτnn, hLτ⟩ := hTau
  have hθmem' : θ ∈ Set.Icc (θ - dθ) (θ + dθ) := ⟨by linarith, by linarith⟩
  have hzmem' : z ∈ Set.Icc (z / 2) (3 * z / 2) := ⟨by linarith, by linarith⟩
  -- the time-continuity of the jet at the point
  have hτcont : ContinuousWithinAt
      (fun σ : ℝ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g σ) z θ)
      (Set.Icc (0:ℝ) T) τ :=
    tau_cont_mixed hT hzpos hθ0 hθπ hdθpos hdθle hLτnn hCsnn hji
      (fun σ hσ => hOK.1.1.c4 σ hσ.1) hLτ
      (fun σ hσ j' i' hj'i' => (hCslip σ hσ j' i' hj'i').1)
      (fun σ hσ j' i' hj'i' => (hCslip σ hσ j' i' hj'i').2)
      hLandau hτmem
  -- the ε-δ assembly
  refine Metric.continuousWithinAt_iff.mpr ?_
  intro ε hε
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousWithinAt_iff.mp hτcont (ε / 2) (by linarith)
  set δx : ℝ := min (min δ₁ (ε / (4 * (Cs + 1)))) (min (z / 2) (dθ / 2)) with hδxdef
  have hδxpos : 0 < δx := by
    rw [hδxdef]
    refine lt_min (lt_min hδ₁pos (by positivity)) (lt_min (by linarith) (by linarith))
  refine ⟨δx, hδxpos, ?_⟩
  intro q hq hdist
  obtain ⟨z', θ', τ'⟩ := q
  change dist (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ')
    (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ) < ε
  rw [Set.mem_prod] at hq
  obtain ⟨hz', hq⟩ := hq
  rw [Set.mem_prod] at hq
  obtain ⟨hθ'mem, hτ'mem⟩ := hq
  have hz'pos : 0 < z' := hz'
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at hdist
  have hδxle1 : δx ≤ z / 2 := by
    rw [hδxdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδxle2 : δx ≤ dθ / 2 := by
    rw [hδxdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδxle3 : δx ≤ δ₁ := by
    rw [hδxdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδxle4 : δx ≤ ε / (4 * (Cs + 1)) := by
    rw [hδxdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdz : |z' - z| < δx := lt_of_le_of_lt (le_max_left _ _) hdist
  have hdθ' : |θ' - θ| < δx :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hdist
  have hdτ' : |τ' - τ| < δx :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hdist
  have hz'in : z' ∈ Set.Icc (z / 2) (3 * z / 2) := by
    have h := abs_lt.mp (lt_of_lt_of_le hdz hδxle1)
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hθ'in : θ' ∈ Set.Icc (θ - dθ) (θ + dθ) := by
    have h := abs_lt.mp (lt_of_lt_of_le hdθ' hδxle2)
    exact ⟨by linarith [h.2, hdθpos], by linarith [h.1]⟩
  have hslip := hCslip τ' hτ'mem j i hji
  have h1 : |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
        - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
      ≤ Cs * |z' - z| + Cs * |θ' - θ| := by
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
        ≤ |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ'|
          + |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ| := abs_sub_le _ _ _
      _ ≤ Cs * |z' - z| + Cs * |θ' - θ| :=
          add_le_add (hslip.1 z' hz'in θ' hθ'in z hzmem')
            (hslip.2 z hzmem' θ' hθ'in θ hθmem')
  have h2 : |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ
      - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| < ε / 2 := by
    have h := hδ₁ hτ'mem (by rw [Real.dist_eq]; exact lt_of_lt_of_le hdτ' hδxle3)
    rwa [Real.dist_eq] at h
  have h3 : Cs * |z' - z| + Cs * |θ' - θ| < ε / 2 := by
    have h4 : |z' - z| + |θ' - θ| ≤ 2 * (ε / (4 * (Cs + 1))) :=
      le_of_lt (by linarith [add_lt_add hdz hdθ', hδxle4])
    have h5 : Cs * (|z' - z| + |θ' - θ|) ≤ Cs * (2 * (ε / (4 * (Cs + 1)))) :=
      mul_le_mul_of_nonneg_left h4 hCsnn
    have h6 : Cs * (2 * (ε / (4 * (Cs + 1)))) < ε / 2 := mul_two_div_lt hCsnn hε
    calc Cs * |z' - z| + Cs * |θ' - θ| = Cs * (|z' - z| + |θ' - θ|) := by ring
      _ ≤ Cs * (2 * (ε / (4 * (Cs + 1)))) := h5
      _ < ε / 2 := h6
  calc dist (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ')
        (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ)
      = |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| := Real.dist_eq _ _
    _ ≤ |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z' θ'
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ|
          + |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ') z θ
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| := abs_sub_le _ _ _
    _ < ε := by linarith [h1, h2, h3]

end Work.FTS_RegExport.RXT
