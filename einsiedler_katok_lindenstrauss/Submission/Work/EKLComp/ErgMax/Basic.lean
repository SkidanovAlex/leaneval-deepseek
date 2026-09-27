import Mathlib
import Submission.Work.EKLContract.Interfaces

/-!
# C4c — the ergodic maximiser: vocabulary

Definitions used by `Submission.Work.EKLComp.prove_ErgodicMax` (component C4c of the frozen EKL
contract).  Nothing here changes the frozen contract; it only names the objects of the
`A`-averaging argument.

* `a0v`     : the exponent vector `![-2,1,1]`, so that `aDiag a0v = a0`.
* `g1`, `g2` : the two generators `![-1,1,0]`, `![-1,0,1]` of `A⁺`; `aDiag (r•g1 + s•g2) = aPlus r s`.
* `avg ν N` : the `A⁺`-average `(N⁴)⁻¹ ∑_{0 ≤ i,j < N²} (aDiag (i/N g1 + j/N g2))_* ν`.
* `IsFace`, `IsClosedProb`, `IsCompactProb` : the (topological) face vocabulary of the
  Bauer/Krein–Milman step, phrased for sets of measures on `X₃`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

/-! ## The exponent vectors -/

/-- The exponent vector of `a₀ = aDiag ![-2,1,1]`. -/
def a0v : Fin 3 → ℝ := ![-2, 1, 1]

@[simp] theorem aDiag_a0v : aDiag a0v = a0 := rfl

/-- The first generator `![-1,1,0]` of `A⁺`. -/
def g1 : Fin 3 → ℝ := ![-1, 1, 0]

/-- The second generator `![-1,0,1]` of `A⁺`. -/
def g2 : Fin 3 → ℝ := ![-1, 0, 1]

/-- The grid vector `(i/N) g1 + (j/N) g2`. -/
def shift (N i j : ℕ) : Fin 3 → ℝ := ((i : ℝ) / N) • g1 + ((j : ℝ) / N) • g2

/-- `aDiag (shift N i j) = aPlus (i/N) (j/N)`: the grid really is the `A⁺`-grid. -/
theorem aDiag_shift (N i j : ℕ) :
    aDiag (shift N i j) = aPlus ((i : ℝ) / N) ((j : ℝ) / N) := by
  rw [aPlus]
  congr 1
  funext k
  fin_cases k <;> simp [shift, g1, g2] <;> ring

/-- `aPlus` is multiplicative in the parameters. -/
theorem aPlus_add (r s r' s' : ℝ) :
    aPlus r s * aPlus r' s' = aPlus (r + r') (s + s') := by
  rw [aPlus, aPlus, aPlus, aDiag_add]
  congr 1
  funext k
  fin_cases k <;> simp <;> ring

/-- `aPlus` commutes with its own translates. -/
theorem aPlus_add_comm (r s r' s' : ℝ) :
    aPlus r s * aPlus r' s' = aPlus r' s' * aPlus r s := by
  rw [aPlus_add, aPlus_add, add_comm r r', add_comm s s']

/-! ## The action -/

/-- Left multiplication by `g`, as a self-map of `X₃`. -/
def act (g : SL3) : X3 → X3 := fun x => g • x

@[simp] theorem act_apply (g : SL3) (x : X3) : act g x = g • x := rfl

theorem continuous_act (g : SL3) : Continuous (act g) := continuous_const_smul g

theorem measurable_act (g : SL3) : Measurable (act g) := (continuous_act g).measurable

theorem act_mul (g h : SL3) : act (g * h) = act g ∘ act h := by
  funext x; simp [act, mul_smul]

theorem act_one : act (1 : SL3) = id := by
  funext x; simp [act]

/-! ## Continuity of the objects involved -/

theorem continuous_aDiag : Continuous (fun t : Fin 3 → ℝ => aDiag t) := by
  have h : Continuous (fun t : Fin 3 → ℝ =>
      ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) := by
    simp only [toMat_aDiag]
    fun_prop
  exact Continuous.subtype_mk h (fun t => (aDiag t).2)

theorem continuous_aPlus : Continuous (fun p : ℝ × ℝ => aPlus p.1 p.2) := by
  unfold aPlus
  exact continuous_aDiag.comp (by fun_prop)

theorem continuous_smul' : Continuous (fun p : SL3 × X3 => p.1 • p.2) := continuous_smul

theorem continuous_aPlus_smul :
    Continuous (fun p : (ℝ × ℝ) × X3 => aPlus p.1.1 p.1.2 • p.2) := by
  have h : Continuous (fun p : (ℝ × ℝ) × X3 => ((aPlus p.1.1 p.1.2, p.2) : SL3 × X3)) :=
    (continuous_aPlus.comp (by fun_prop)).prodMk continuous_snd
  exact continuous_smul'.comp h

/-! ## Forward invariance of `Drho` -/

/-- `Drho ρ` is invariant under the forward semigroup `A⁺`. -/
theorem aPlus_maps_Drho {ρ r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) {x : X3}
    (hx : x ∈ Drho ρ) : aPlus r s • x ∈ Drho ρ := by
  intro r' s' hr' hs'
  have h : aPlus r' s' • (aPlus r s • x) = aPlus (r + r') (s + s') • x := by
    rw [← mul_smul, aPlus_add, add_comm r' r, add_comm s' s]
  rw [h]
  exact hx (r + r') (s + s') (by linarith) (by linarith)

/-! ## The averaging measure -/

/-- `n N = N²`, the number of grid points per direction. -/
def n (N : ℕ) : ℕ := N * N

/-- The averaging measure `(n N)⁻² ∑_{i,j < n N} (aDiag (shift N i j))_* ν`. -/
def avg (ν : Measure X3) (N : ℕ) : Measure X3 :=
  (((n N * n N : ℕ) : ℝ≥0∞))⁻¹ •
    ∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j)))

theorem avg_def (ν : Measure X3) (N : ℕ) :
    avg ν N = (((n N * n N : ℕ) : ℝ≥0∞))⁻¹ •
      ∑ i : Fin (n N), ∑ j : Fin (n N), ν.map (act (aDiag (shift N i j))) := rfl

/-! ## Faces and the topology transferred from `ProbabilityMeasure` -/

/-- `M`-faces: sets closed under "being the left end of a nontrivial convex combination in `M`". -/
structure IsFace (M F : Set (Measure X3)) : Prop where
  subset : F ⊆ M
  mem_of_smul_add : ∀ μ₁ ∈ M, ∀ μ₂ ∈ M, ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 →
    a • μ₁ + b • μ₂ ∈ F → μ₁ ∈ F

/-- A set of measures on `X₃` is closed when the corresponding set of probability measures is. -/
def IsClosedProb (S : Set (Measure X3)) : Prop :=
  IsClosed {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S}

/-- A set of measures on `X₃` is compact when the corresponding set of probability measures is. -/
def IsCompactProb (S : Set (Measure X3)) : Prop :=
  IsCompact {μ : ProbabilityMeasure X3 | (μ : Measure X3) ∈ S}



theorem isFace_refl (M : Set (Measure X3)) : IsFace M M := by
  refine ⟨fun _ h => h, ?_⟩
  intro μ₁ h₁ μ₂ h₂ a b ha hb hab h
  exact h₁

theorem IsFace.mono {M M' F : Set (Measure X3)} (h : IsFace M F) (hFM' : F ⊆ M')
    (hM'M : M' ⊆ M) : IsFace M' F := by
  obtain ⟨hsub, hleft⟩ := h
  refine ⟨hFM', ?_⟩
  intro μ₁ h₁ μ₂ h₂ a b ha hb hab hc
  exact hleft μ₁ (hM'M h₁) μ₂ (hM'M h₂) a b ha hb hab hc

theorem IsFace.trans {M F G : Set (Measure X3)} (hFG : IsFace F G) (hMF : IsFace M F) :
    IsFace M G := by
  obtain ⟨hGF, hleftFG⟩ := hFG
  obtain ⟨hFM, hleftMF⟩ := hMF
  refine ⟨hGF.trans hFM, ?_⟩
  intro μ₁ h₁ μ₂ h₂ a b ha hb hab h
  have hab' : b + a = 1 := by rw [add_comm]; exact hab
  have h' : b • μ₂ + a • μ₁ ∈ G := by rw [add_comm]; exact h
  exact hleftFG μ₁ (hleftMF μ₁ h₁ μ₂ h₂ a b ha hb hab (hGF h)) μ₂
    (hleftMF μ₂ h₂ μ₁ h₁ b a hb ha hab' (hGF h')) a b ha hb hab h

theorem isFace_sInter {M : Set (Measure X3)} {S : Set (Set (Measure X3))} (hS : S.Nonempty)
    (h : ∀ F ∈ S, IsFace M F) : IsFace M (⋂₀ S) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨F, hF⟩ := hS
    exact (IsFace.subset (h F hF)) (hx F hF)
  · intro μ₁ h₁ μ₂ h₂ a b ha hb hab hh
    rw [Set.mem_sInter] at hh ⊢
    exact fun F hF => (IsFace.mem_of_smul_add (h F hF)) μ₁ h₁ μ₂ h₂ a b ha hb hab (hh F hF)

/-! ## The two entropy clauses of `P_EntropyBasics` used by C4c

`E2c` and `E3c` are clauses (E2) (conjugacy) and (E3) (affinity) of the frozen
`Work.EKLContract.P_EntropyBasics`, in the unbundled form used here: this keeps the C4c
development independent of the other five clauses. -/

/-- Clause (E2) of `P_EntropyBasics`: conjugacy invariance of the entropy. -/
def E2c : Prop :=
  ∀ {X : Type} [mX : MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
    ∀ (T φ ψ : X → X), Measurable T → Measurable φ → Measurable ψ →
      MeasurePreserving T μ μ → Function.LeftInverse ψ φ → Function.RightInverse ψ φ →
      (∀ x, φ (T x) = T (φ x)) → ent (μ.map φ) T = ent μ T

/-- Clause (E3) of `P_EntropyBasics`: affinity of the entropy in the measure. -/
def E3c : Prop :=
  ∀ {X : Type} [mX : MeasurableSpace X] (μ : Measure X), IsProbabilityMeasure μ →
    ∀ (ν : Measure X), IsProbabilityMeasure ν → ∀ (T : X → X) (c : ℝ≥0∞), c ≤ 1 →
      Measurable T → MeasurePreserving T μ μ → MeasurePreserving T ν ν →
      ent (c • μ + (1 - c) • ν) T = c * ent μ T + (1 - c) * ent ν T

end

end Work.EKLComp.ErgMax
