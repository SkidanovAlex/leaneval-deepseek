import Mathlib
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLNonExc.DinjAux.WSets
import Submission.Work.EKLNonExc.DinjAux.VNhds
import Submission.Work.EKLNonExc.DinjAux.complDinj
import Submission.Work.EKLComp.exists_isCompact_image

/-!
# Facts about `Dinj` (EKL's sets `D_ℓ`)

`Dinj δ` is the set of points `x ∈ X₃` such that the orbit map `g ↦ g • x` is injective on the
entrywise box `V δ`.  We prove the three facts used by the `C9` argument:

* `Dinj δ` is closed: its complement is `mkX '' Lbad δ`, where `Lbad δ` is the open set of
  `k` admitting a nontrivial `Γ₃`-conjugate with displacement in `Wset δ = (V δ)⁻¹ * V δ`;
  `mkX` is an open map.
* every point lies in some `Dinj δ` (the stabiliser of `x` is a conjugate of the discrete group
  `Γ₃`, hence has a gap at the identity);
* every compact set is contained in some `Dinj δ` (a compact lift `C ⊆ SL₃(ℝ)` of `K`, uniform
  conjugation of `Wset δ` into a neighbourhood of `1` meeting `Γ₃` only in `1`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.EKLNonExc

open Work.EKLContract Filter Topology

noncomputable section

/-- Any neighbourhood of `1` contains `Wset δ = (V δ)⁻¹ * V δ` for some `δ > 0`. -/
lemma exists_Wset_subset {v : Set SL3} (hv : v ∈ 𝓝 (1 : SL3)) :
    ∃ δ > 0, DinjAux.Wset δ ⊆ v := by
  obtain ⟨w, hw, hwsub⟩ := exists_nhds_split_inv (s := v) hv
  have hwinv : w⁻¹ ∈ 𝓝 (1 : SL3) := inv_mem_nhds_one SL3 hw
  have hw2 : w ∩ w⁻¹ ∈ 𝓝 (1 : SL3) := Filter.inter_mem hw hwinv
  obtain ⟨δ, hδ, hδsub⟩ := DinjAux.VNhds hw2
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rw [DinjAux.mem_Wset] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have ha1 : a⁻¹ ∈ V δ := Set.mem_inv.mp ha
  have haW : a ∈ w := by
    have h2 : a⁻¹ ∈ w ∩ w⁻¹ := hδsub ha1
    simpa using (Set.mem_inv.mp h2.2)
  have hbinvW : b⁻¹ ∈ w := by
    have h2 : b ∈ w ∩ w⁻¹ := hδsub hb
    exact h2.2
  have := hwsub a haW b⁻¹ hbinvW
  simpa using this

/-- Uniform conjugation: on a compact set `C`, all the conjugates `k⁻¹ w k` (`k ∈ C`,
`w ∈ Wset δ`) lie in a given neighbourhood of `1` for `δ` small. -/
lemma uniformConj {C : Set SL3} (hC : IsCompact C) {B : Set SL3} (hB : B ∈ 𝓝 (1 : SL3)) :
    ∃ δ > 0, ∀ k ∈ C, ∀ w ∈ DinjAux.Wset δ, k⁻¹ * w * k ∈ B := by
  have hcont : Continuous (fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) := by fun_prop
  have hn : IsOpen (interior ((fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) ⁻¹' B)) := isOpen_interior
  have hsub : C ×ˢ ({1} : Set SL3) ⊆
      interior ((fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) ⁻¹' B) := by
    rintro ⟨k, w⟩ ⟨hk, rfl⟩
    rw [mem_interior_iff_mem_nhds]
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hB)
  obtain ⟨u, v, huopen, hvopen, hCu, hv1, huv⟩ :=
    generalized_tube_lemma hC isCompact_singleton hn hsub
  have hvnhds : v ∈ 𝓝 (1 : SL3) := hvopen.mem_nhds (hv1 (Set.mem_singleton 1))
  obtain ⟨δ, hδ, hδsub⟩ := exists_Wset_subset hvnhds
  refine ⟨δ, hδ, fun k hk w hw => ?_⟩
  have hmem : (k, w) ∈ u ×ˢ v := ⟨hCu hk, hδsub hw⟩
  have hmem2 : (k, w) ∈ (fun p : SL3 × SL3 => p.1⁻¹ * p.2 * p.1) ⁻¹' B :=
    interior_subset (huv hmem)
  exact hmem2

/-- `Dinj δ` is closed. -/
lemma isClosed_Dinj (δ : ℝ) : IsClosed (Dinj δ) := by
  have hopen : IsOpen (Dinj δ)ᶜ := by
    rw [DinjAux.complDinj δ]
    exact Work.EKLContract.Lemmas.thick_isOpenMap_mkX _ (DinjAux.isOpen_Lbad δ)
  simpa using hopen.isClosed_compl

/-- Every compact subset of `X₃` is contained in `Dinj δ` for some `δ > 0`. -/
lemma compact_subset_Dinj {K : Set X3} (hK : IsCompact K) : ∃ δ > 0, K ⊆ Dinj δ := by
  obtain ⟨C, hC, hKC⟩ := Work.EKLComp.exists_isCompact_image K hK
  obtain ⟨B, hBnhds, hBΓ⟩ := DinjAux.exists_nhds_inter_Γ3
  obtain ⟨δ, hδ, hunif⟩ := uniformConj hC hBnhds
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨k, hkC, rfl⟩ := hKC hx
  intro g h gg hh heq
  have hΓ : k⁻¹ * g⁻¹ * h * k ∈ Γ3 := (DinjAux.smul_mkX_eq_iff g h k).mp heq
  have hW : g⁻¹ * h ∈ DinjAux.Wset δ :=
    DinjAux.mem_Wset.mpr ⟨g⁻¹, by rw [Set.mem_inv]; simpa using gg, h, hh, rfl⟩
  have hBmem : k⁻¹ * (g⁻¹ * h) * k ∈ B := hunif k hkC (g⁻¹ * h) hW
  have hboth : k⁻¹ * g⁻¹ * h * k ∈ (B ∩ (Γ3 : Set SL3) : Set SL3) := by
    refine ⟨?_, hΓ⟩
    rwa [show k⁻¹ * g⁻¹ * h * k = k⁻¹ * (g⁻¹ * h) * k from by group]
  rw [hBΓ] at hboth
  have heq1 : k⁻¹ * g⁻¹ * h * k = 1 := hboth
  have hgh : g⁻¹ * h = 1 := by
    have : g⁻¹ * h = k * (k⁻¹ * g⁻¹ * h * k) * k⁻¹ := by group
    rw [this, heq1]; group
  exact inv_mul_eq_one.mp hgh

theorem DinjFacts :
    (∀ δ : ℝ, IsClosed (Work.EKLNonExc.Dinj δ)) ∧
    (∀ x : Work.EKLContract.X3, ∃ δ : ℝ, 0 < δ ∧ x ∈ Work.EKLNonExc.Dinj δ) ∧
    (∀ K : Set Work.EKLContract.X3, IsCompact K → ∃ δ : ℝ, 0 < δ ∧ K ⊆ Work.EKLNonExc.Dinj δ) := by
  refine ⟨isClosed_Dinj, ?_, fun K hK => compact_subset_Dinj hK⟩
  intro x
  obtain ⟨δ, hδ, hsub⟩ := compact_subset_Dinj (isCompact_singleton (x := x))
  exact ⟨δ, hδ, hsub (Set.mem_singleton x)⟩

end

end Work.EKLNonExc
