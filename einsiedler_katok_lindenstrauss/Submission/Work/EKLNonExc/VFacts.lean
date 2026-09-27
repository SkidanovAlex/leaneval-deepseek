import Mathlib
import Submission.Work.EKLNonExc.Defs

/-!
# `V`-facts: the displacement neighbourhoods of `1 ∈ SL₃(ℝ)`

This module proves `Work.EKLNonExc.VFacts`, the elementary topological package about the
max-entry displacement neighbourhoods

`V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - δᵢⱼ| < δ}`

of the identity, together with the companion *closed* box `clBox δ` of `Defs.lean`:

1. `clBox δ` is compact for every `δ : ℝ`;
2. the sets `V δ` form a neighbourhood basis of `1 ∈ SL₃(ℝ)`;
3. `V`-arithmetic: for every `δ > 0` there is `ε > 0` with `h * g⁻¹ ∈ V δ` for all
   `g, h ∈ V ε` (the form in which the "return sets" of the C9 argument are shown to be
   fine sets);
4. for every `x ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)` and `δ > 0` the orbit image
   `{g • x | g ∈ V δ}` is open in `X₃`.

The proofs are metric-free apart from a single place (1) and (2), where the matrix space
`ℝ^{3×3}` is used as a proper metric space (sup-metric on the product of the entries) in order to
produce a small explicit box: `V δ` is the preimage of the open ball of radius `δ` around the
identity matrix, and `clBox δ` that of the closed ball.  Since `Matrix (Fin 3) (Fin 3) ℝ` is
definitionally the finite product `Fin 3 → Fin 3 → ℝ`, every metric statement is written with the
product type as the ambient space; the subtype topology of `SL₃(ℝ)` (a closed subspace, `det = 1`)
is the induced one, and the projection `mkX : SL₃(ℝ) → X₃` is open (quotient by the subgroup
`Γ₃ = SL₃(ℤ)`).
-/

namespace Work.EKLNonExc

open MeasureTheory Filter Topology
open Work.EKLContract

noncomputable section

/-! ## Metric bookkeeping for the matrix space

`Matrix (Fin 3) (Fin 3) ℝ` is the definitional finite product `Fin 3 → Fin 3 → ℝ`; the product
sup-metric is the one we use, and all metric statements below are therefore phrased in the
product type (this keeps the `topology = product topology` identification definitional). -/

/-- `V` is monotone in `δ`. -/
lemma V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- Membership in the closed ball of the product metric is the entrywise `≤ δ` condition. -/
lemma mem_closedBall_iff {δ : ℝ} (hδ : 0 ≤ δ) {f : Fin 3 → Fin 3 → ℝ} :
    f ∈ Metric.closedBall (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) δ ↔
      ∀ i j, |f i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ := by
  rw [Metric.mem_closedBall, dist_pi_le_iff hδ]
  constructor
  · intro h i j
    have h2 := (dist_pi_le_iff hδ).mp (h i) j
    rwa [Real.dist_eq] at h2
  · intro h i
    rw [dist_pi_le_iff hδ]
    intro j
    rw [Real.dist_eq]
    exact h i j

/-! ## `V δ` is a neighbourhood basis of the identity -/

/-- The sets `V δ` (`δ > 0`) form a neighbourhood basis of the identity of `SL₃(ℝ)`: every
neighbourhood of `1` contains some `V δ`.  This is a restatement of the fact that the topology of
`SL₃(ℝ)` is the (induced) product topology of the nine matrix entries. -/
theorem V_nhds_basis : ∀ W ∈ 𝓝 (1 : SL3), ∃ δ > 0, V δ ⊆ W := by
  intro W hW
  -- pass to the ambient matrix space, where the sup-metric is available
  obtain ⟨W', hW'mem, hW'sub⟩ :=
    (mem_nhds_induced (f := (Subtype.val : SL3 → Matrix (Fin 3) (Fin 3) ℝ))
      (a := (1 : SL3)) (s := W)).mp hW
  have hW'mem' : W' ∈ 𝓝 ((fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) :
      Fin 3 → Fin 3 → ℝ) := hW'mem
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hW'mem'
  refine ⟨η / 2, by linarith, fun g hg => ?_⟩
  have hmem : (fun i j => ((g : Matrix (Fin 3) (Fin 3) ℝ) i j)) ∈
      Metric.ball ((fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) : Fin 3 → Fin 3 → ℝ) η := by
    rw [Metric.mem_ball, dist_pi_lt_iff hη]
    intro i
    rw [dist_pi_lt_iff hη]
    intro j
    rw [Real.dist_eq]
    exact lt_trans (by simpa using hg i j) (by linarith)
  exact hW'sub (hball hmem)

/-! ## Compactness of the closed box -/

/-- The closed box `clBox δ` is closed: it is the finite intersection of the closed entrywise
conditions `|g i j - δᵢⱼ| ≤ δ`. -/
theorem clBox_isClosed (δ : ℝ) : IsClosed (clBox δ) := by
  have h : clBox δ = ⋂ i : Fin 3, ⋂ j : Fin 3,
      {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ} := by
    ext g; simp [clBox]
  rw [h]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_le (by fun_prop) continuous_const

/-- `clBox δ` is the preimage of the closed ball of radius `δ` around the identity matrix under
the (closed) embedding `SL₃(ℝ) ↪ ℝ^{3×3}`; hence it is compact.  For `δ < 0` it is empty. -/
theorem clBox_isCompact (δ : ℝ) : IsCompact (clBox δ) := by
  have key : ∀ δ : ℝ, 0 ≤ δ → IsCompact (clBox δ) := by
    intro δ hδ
    have hbox : clBox δ =
        (fun g : SL3 => (fun i j => (g : Matrix (Fin 3) (Fin 3) ℝ) i j)) ⁻¹'
          Metric.closedBall ((fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) :
            Fin 3 → Fin 3 → ℝ) δ := by
      ext g
      rw [mem_clBox, Set.mem_preimage, mem_closedBall_iff hδ]
    rw [hbox]
    have hclosed : IsClosed {A : Matrix (Fin 3) (Fin 3) ℝ | A.det = 1} :=
      isClosed_eq (continuous_id.matrix_det (n := Fin 3) (R := ℝ)) continuous_const
    have hemb : IsClosedEmbedding
        (fun g : SL3 => (fun i j => (g : Matrix (Fin 3) (Fin 3) ℝ) i j)) :=
      hclosed.isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage (isCompact_closedBall _ δ)
  by_cases h : 0 ≤ δ
  · exact key δ h
  · rw [not_le] at h
    exact (key 0 le_rfl).of_isClosed_subset (clBox_isClosed δ) (clBox_mono h.le)

/-! ## `V`-arithmetic and open orbit images -/

/-- For every `δ > 0` there is `ε > 0` such that `h * g⁻¹ ∈ V δ` for all `g, h ∈ V ε`: the map
`(h, g) ↦ h * g⁻¹` is continuous at `(1, 1)`, and the `V`'s are a neighbourhood basis. -/
theorem V_mul_inv {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ g ∈ V ε, ∀ h ∈ V ε, h * g⁻¹ ∈ V δ := by
  have hopen : IsOpen (V δ) := (Work.EKLContract.Lemmas.V_open_one δ hδ).1
  have h1 : (1 : SL3) * (1 : SL3)⁻¹ ∈ V δ := by
    simpa using (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  have hcont : Continuous fun p : SL3 × SL3 => p.1 * p.2⁻¹ :=
    continuous_fst.mul continuous_snd.inv
  have hmem : (fun p : SL3 × SL3 => p.1 * p.2⁻¹) ⁻¹' V δ ∈ 𝓝 ((1 : SL3), (1 : SL3)) :=
    hcont.continuousAt.preimage_mem_nhds (hopen.mem_nhds h1)
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hmem
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := hmem
  obtain ⟨ε₁, hε₁, hV₁⟩ := V_nhds_basis t₁ ht₁
  obtain ⟨ε₂, hε₂, hV₂⟩ := V_nhds_basis t₂ ht₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg h hh => ?_⟩
  have hg₂ : g ∈ t₂ := hV₂ (V_mono (min_le_right _ _) hg)
  have hh₁ : h ∈ t₁ := hV₁ (V_mono (min_le_left _ _) hh)
  exact hsub (Set.mk_mem_prod hh₁ hg₂)

/-- The orbit image `{g • x | g ∈ V δ}` is open in `X₃`: the orbit map factors as the open
quotient map `mkX : SL₃(ℝ) → X₃` precomposed with the homeomorphism `g ↦ g * k`
(for `x = mkX k`), and images of open sets are open for both. -/
theorem orbitImage_isOpen (x : X3) (δ : ℝ) (hδ : 0 < δ) :
    IsOpen {y : X3 | ∃ g ∈ V δ, y = g • x} := by
  induction x using Quotient.ind with
  | _ k =>
      have hset : {y : X3 | ∃ g ∈ V δ, y = g • (QuotientGroup.mk k : X3)}
          = QuotientGroup.mk '' ((fun g : SL3 => g * k) '' V δ) := by
        ext y
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact ⟨g * k, ⟨g, hg, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
          exact ⟨g, hg, rfl⟩
      rw [hset]
      exact QuotientGroup.isOpenMap_coe _
        (isOpenMap_mul_right k _ (Work.EKLContract.Lemmas.V_open_one δ hδ).1)

/-! ## The package -/

theorem VFacts :
    (∀ δ : ℝ, IsCompact (Work.EKLNonExc.clBox δ)) ∧
    (∀ W : Set Work.EKLContract.SL3, (∃ U : Set Work.EKLContract.SL3,
        IsOpen U ∧ (1 : Work.EKLContract.SL3) ∈ U ∧ U ⊆ W) →
      ∃ δ : ℝ, 0 < δ ∧ Work.EKLContract.V δ ⊆ W) ∧
    (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ Work.EKLContract.V ε,
      ∀ h ∈ Work.EKLContract.V ε, h * g⁻¹ ∈ Work.EKLContract.V δ) ∧
    (∀ x : Work.EKLContract.X3, ∀ δ : ℝ, 0 < δ →
      IsOpen {y : Work.EKLContract.X3 | ∃ g ∈ Work.EKLContract.V δ, y = g • x}) := by
  refine ⟨clBox_isCompact, ?_, ?_, orbitImage_isOpen⟩
  · intro W hW
    obtain ⟨U, hUopen, h1U, hUW⟩ := hW
    exact V_nhds_basis W (mem_of_superset (hUopen.mem_nhds h1U) hUW)
  · intro δ hδ
    exact V_mul_inv hδ

end

end Work.EKLNonExc
