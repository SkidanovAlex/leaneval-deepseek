import Mathlib
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLComp.X3Background

/-!
# `Work.EKLRelCross.exists_shrink_nhds`

For a closed subgroup `U ≤ SL₃(ℝ)` acting freely at a point `x₀ ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)`, and for
any `R ≥ 0`, there is a compact neighbourhood `E` of `x₀` such that two elements `u, u'` of the
closed ball `Ucl U R` that identify two points `x, x' ∈ E` differ by an element of the unit ball
`Ucl U 1`:

  `u • x = u' • x'  ⟹  u' * u⁻¹ ∈ Ucl U 1  ∧  u⁻¹ * u' ∈ Ucl U 1`.

The proof works with the *return-pair* set

  `RetPair U R F = {(u,u') ∈ Ucl U R × Ucl U R | ∃ x x' ∈ F, u • x = u' • x'}`

of a closed set `F`.  Each `RetPair U R F` is closed (image of a closed subset of a compact set),
and as `F` shrinks through the compact neighbourhoods of `x₀` these sets form a decreasing
directed family of closed sets whose intersection is the diagonal
`{(u,u) : u ∈ Ucl U R}` (here freeness of the action at `x₀` is used).  The diagonal lies in the
open set `W = {p | p.2 * p.1⁻¹ ∈ V (1/2) ∧ p.1⁻¹ * p.2 ∈ V (1/2)}`, whose intersection with
`Ucl U R × Ucl U R` is contained in the set where the two conclusions hold; the finite
intersection property of compact sets (`IsCompact.elim_directed_family_closed`) then yields a
single compact neighbourhood `E` with `RetPair U R E ⊆ W`.
-/

open Filter Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- `Ucl U R` is closed in `SL₃(ℝ)`: it is the intersection of the closed subgroup `U` with the
closed entrywise condition `|g i j - 1 i j| ≤ R`. -/
theorem isClosed_Ucl {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ) :
    IsClosed (Ucl U R) := by
  have h1 : Ucl U R = (U : Set SL3) ∩
      {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R} := by
    ext g; constructor <;> intro h <;> exact h
  rw [h1]
  refine IsClosed.inter hU ?_
  rw [show {g : SL3 | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R}
      = ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R} from by
    ext g; simp]
  exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_le (by fun_prop) continuous_const))

/-- `Ucl U R` is compact for a closed subgroup `U`: it is a closed subset of the compact entrywise
box of radius `1 + R` intersected with `U`. -/
theorem isCompact_Ucl {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ) :
    IsCompact (Ucl U R) := by
  refine (fsb_isCompact_box U hU (1 + R)).of_isClosed_subset (isClosed_Ucl hU R) ?_
  rintro g ⟨hgU, hbox⟩
  refine ⟨fun i j => ?_, hgU⟩
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |((g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
    _ ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ R + 1 := add_le_add (hbox i j) hone
    _ = 1 + R := by ring

/-- The set of return pairs of a set `F ⊆ X₃`: pairs `(u,u')` of elements of the closed `U`-ball
of radius `R` that identify two points of `F`. -/
def RetPair (U : Subgroup SL3) (R : ℝ) (F : Set X3) : Set (SL3 × SL3) :=
  {p | p.1 ∈ Ucl U R ∧ p.2 ∈ Ucl U R ∧ ∃ x ∈ F, ∃ x' ∈ F, p.1 • x = p.2 • x'}

/-- `RetPair U R F` is closed for compact `F`.  It is the image of a closed subset of the compact
set `(Ucl U R × Ucl U R) × (F × F)` under the continuous projection to the first factor. -/
theorem isClosed_RetPair {U : Subgroup SL3} (hU : IsClosed (U : Set SL3)) (R : ℝ)
    {F : Set X3} (hF : IsCompact F) : IsClosed (RetPair U R F) := by
  have hKc : IsCompact (Ucl U R) := isCompact_Ucl hU R
  have hclosed : IsClosed (Ucl U R) := isClosed_Ucl hU R
  have hFc : IsClosed F := hF.isClosed
  have hQclosed : IsClosed {q : (SL3 × SL3) × (X3 × X3) |
      q.1.1 ∈ Ucl U R ∧ q.1.2 ∈ Ucl U R ∧ q.2.1 ∈ F ∧ q.2.2 ∈ F ∧
        q.1.1 • q.2.1 = q.1.2 • q.2.2} := by
    have h1 : IsClosed {q : (SL3 × SL3) × (X3 × X3) | q.1.1 ∈ Ucl U R} :=
      hclosed.preimage (by fun_prop)
    have h2 : IsClosed {q : (SL3 × SL3) × (X3 × X3) | q.1.2 ∈ Ucl U R} :=
      hclosed.preimage (by fun_prop)
    have h3 : IsClosed {q : (SL3 × SL3) × (X3 × X3) | q.2.1 ∈ F} := hFc.preimage (by fun_prop)
    have h4 : IsClosed {q : (SL3 × SL3) × (X3 × X3) | q.2.2 ∈ F} := hFc.preimage (by fun_prop)
    have h5 : IsClosed {q : (SL3 × SL3) × (X3 × X3) | q.1.1 • q.2.1 = q.1.2 • q.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have heq : {q : (SL3 × SL3) × (X3 × X3) |
        q.1.1 ∈ Ucl U R ∧ q.1.2 ∈ Ucl U R ∧ q.2.1 ∈ F ∧ q.2.2 ∈ F ∧
          q.1.1 • q.2.1 = q.1.2 • q.2.2}
        = {q | q.1.1 ∈ Ucl U R} ∩ {q | q.1.2 ∈ Ucl U R} ∩ {q | q.2.1 ∈ F} ∩ {q | q.2.2 ∈ F}
          ∩ {q | q.1.1 • q.2.1 = q.1.2 • q.2.2} := by
      ext q; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
    rw [heq]
    exact (((h1.inter h2).inter h3).inter h4).inter h5
  have hQcomp : IsCompact {q : (SL3 × SL3) × (X3 × X3) |
      q.1.1 ∈ Ucl U R ∧ q.1.2 ∈ Ucl U R ∧ q.2.1 ∈ F ∧ q.2.2 ∈ F ∧
        q.1.1 • q.2.1 = q.1.2 • q.2.2} :=
    ((hKc.prod hKc).prod (hF.prod hF)).of_isClosed_subset hQclosed (by
      rintro q ⟨hq1, hq2, hq3, hq4, hq5⟩
      exact ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩)
  have himg : Prod.fst '' {q : (SL3 × SL3) × (X3 × X3) |
      q.1.1 ∈ Ucl U R ∧ q.1.2 ∈ Ucl U R ∧ q.2.1 ∈ F ∧ q.2.2 ∈ F ∧
        q.1.1 • q.2.1 = q.1.2 • q.2.2} = RetPair U R F := by
    ext p
    rw [RetPair]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, hq.2.1, q.2.1, hq.2.2.1, q.2.2, hq.2.2.2.1, hq.2.2.2.2⟩
    · rintro ⟨hp1, hp2, x, hx, x', hx', hpx⟩
      exact ⟨(p, (x, x')), ⟨hp1, hp2, hx, hx', hpx⟩, rfl⟩
  rw [← himg]
  exact (hQcomp.image continuous_fst).isClosed

theorem exists_shrink_nhds {U : Subgroup Work.EKLContract.SL3} (hU : IsClosed (U : Set Work.EKLContract.SL3)) (x₀ : Work.EKLContract.X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x₀ = u₂ • x₀ → u₁ = u₂) {R : ℝ} (hR : 0 ≤ R) :
    ∃ E : Set Work.EKLContract.X3, IsCompact E ∧ x₀ ∈ interior E ∧
      ∀ x ∈ E, ∀ x' ∈ E, ∀ u ∈ Work.EKLRelCross.Ucl U R, ∀ u' ∈ Work.EKLRelCross.Ucl U R, u • x = u' • x' →
        u' * u⁻¹ ∈ Work.EKLRelCross.Ucl U 1 ∧ u⁻¹ * u' ∈ Work.EKLRelCross.Ucl U 1 := by
  classical
  have hKc : IsCompact (Ucl U R) := isCompact_Ucl hU R
  -- The open neighbourhood `W` of the diagonal on which the two conclusions hold.
  let W : Set (SL3 × SL3) :=
    {p : SL3 × SL3 | p.2 * p.1⁻¹ ∈ V (1 / 2 : ℝ) ∧ p.1⁻¹ * p.2 ∈ V (1 / 2 : ℝ)}
  have hVopen : IsOpen (V (1 / 2 : ℝ)) :=
    (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).1
  have hV1 : (1 : SL3) ∈ V (1 / 2 : ℝ) :=
    (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).2
  have hWopen : IsOpen W := by
    have h1 : Continuous (fun p : SL3 × SL3 => p.2 * p.1⁻¹) :=
      continuous_snd.mul continuous_fst.inv
    have h2 : Continuous (fun p : SL3 × SL3 => p.1⁻¹ * p.2) :=
      continuous_fst.inv.mul continuous_snd
    have h : W = (fun p : SL3 × SL3 => p.2 * p.1⁻¹) ⁻¹' (V (1 / 2 : ℝ))
        ∩ (fun p : SL3 × SL3 => p.1⁻¹ * p.2) ⁻¹' (V (1 / 2 : ℝ)) := rfl
    rw [h]
    exact (hVopen.preimage h1).inter (hVopen.preimage h2)
  have hdiagW : ∀ u ∈ Ucl U R, (u, u) ∈ W := by
    intro u hu
    refine ⟨?_, ?_⟩
    · show u * u⁻¹ ∈ V (1 / 2 : ℝ)
      rw [mul_inv_cancel]; exact hV1
    · show u⁻¹ * u ∈ V (1 / 2 : ℝ)
      rw [inv_mul_cancel]; exact hV1
  -- Compact neighbourhoods of `x₀`.
  let ι := {F : Set X3 // IsCompact F ∧ x₀ ∈ interior F}
  haveI hneι : Nonempty ι := by
    obtain ⟨s, hsc, hs⟩ := exists_compact_mem_nhds x₀
    exact ⟨⟨s, hsc, mem_interior_iff_mem_nhds.mpr hs⟩⟩
  let Pf : ι → Set (SL3 × SL3) := fun F => RetPair U R F.1
  have hPf_closed : ∀ F : ι, IsClosed (Pf F) := fun F => isClosed_RetPair hU R F.2.1
  have hmono : ∀ F₁ F₂ : ι, F₁.1 ⊆ F₂.1 → Pf F₁ ⊆ Pf F₂ := by
    intro F₁ F₂ hsub p hp
    obtain ⟨x, hx, x', hx', hpx⟩ := hp.2.2
    exact ⟨hp.1, hp.2.1, x, hsub hx, x', hsub hx', hpx⟩
  have hdir : Directed (· ⊇ ·) Pf := by
    intro F₁ F₂
    refine ⟨⟨F₁.1 ∩ F₂.1, F₁.2.1.inter F₂.2.1, ?_⟩, ?_, ?_⟩
    · rw [interior_inter]; exact ⟨F₁.2.2, F₂.2.2⟩
    · exact hmono _ F₁ Set.inter_subset_left
    · exact hmono _ F₂ Set.inter_subset_right
  -- The compact set `Ucl U R × Ucl U R` avoiding `W`.
  have h𝒦c : IsCompact (Ucl U R ×ˢ Ucl U R) := hKc.prod hKc
  have hsc : IsCompact ((Ucl U R ×ˢ Ucl U R) ∩ Wᶜ) :=
    h𝒦c.of_isClosed_subset (h𝒦c.isClosed.inter hWopen.isClosed_compl) Set.inter_subset_left
  -- The shrinking lemma: any point with distinct images of `x₀` is excluded by a small `F`.
  have shrinking : ∀ p : SL3 × SL3, p.1 ∈ Ucl U R → p.2 ∈ Ucl U R →
      p.1 • x₀ ≠ p.2 • x₀ → ∃ F : ι, p ∉ Pf F := by
    intro p hp1 hp2 hx0
    have hCclosed : IsClosed {q : X3 × X3 | p.1 • q.1 = p.2 • q.2} :=
      isClosed_eq ((continuous_const_smul p.1).comp continuous_fst)
        ((continuous_const_smul p.2).comp continuous_snd)
    have hx0C : (x₀, x₀) ∉ {q : X3 × X3 | p.1 • q.1 = p.2 • q.2} := hx0
    have hO : ({q : X3 × X3 | p.1 • q.1 = p.2 • q.2})ᶜ ∈ 𝓝 (x₀, x₀) :=
      hCclosed.isOpen_compl.mem_nhds hx0C
    rw [nhds_prod_eq] at hO
    obtain ⟨O₁, hO₁, O₂, hO₂, hsub⟩ := Filter.mem_prod_iff.mp hO
    obtain ⟨U₁, hU₁sub, hU₁open, hx₀U₁⟩ := mem_nhds_iff.mp hO₁
    obtain ⟨U₂, hU₂sub, hU₂open, hx₀U₂⟩ := mem_nhds_iff.mp hO₂
    obtain ⟨K₁, hK₁c, hx₀K₁, hK₁sub⟩ := exists_compact_subset hU₁open hx₀U₁
    obtain ⟨K₂, hK₂c, hx₀K₂, hK₂sub⟩ := exists_compact_subset hU₂open hx₀U₂
    refine ⟨⟨K₁ ∩ K₂, hK₁c.inter hK₂c, ?_⟩, ?_⟩
    · rw [interior_inter]; exact ⟨hx₀K₁, hx₀K₂⟩
    · intro hp
      obtain ⟨x, hx, x', hx', hpx⟩ := hp.2.2
      have hxO₁ : x ∈ O₁ := hU₁sub (hK₁sub hx.1)
      have hxO₂ : x' ∈ O₂ := hU₂sub (hK₂sub hx'.2)
      have hnotC : (x, x') ∉ {q : X3 × X3 | p.1 • q.1 = p.2 • q.2} := hsub ⟨hxO₁, hxO₂⟩
      exact hnotC hpx
  -- The intersection of the return-pair sets meets `W`'s complement trivially.
  have hst : ((Ucl U R ×ˢ Ucl U R) ∩ Wᶜ) ∩ ⋂ F : ι, Pf F = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hpKW, hpAll⟩
    simp only [Set.mem_iInter] at hpAll
    have hpK : p ∈ Ucl U R ×ˢ Ucl U R := hpKW.1
    have hpW : p ∉ W := hpKW.2
    have hp1 : p.1 ∈ Ucl U R := (Set.mem_prod.mp hpK).1
    have hp2 : p.2 ∈ Ucl U R := (Set.mem_prod.mp hpK).2
    have hne : p.1 ≠ p.2 := by
      intro h
      refine hpW ?_
      show (p.1, p.2) ∈ W
      rw [h]; exact hdiagW p.2 hp2
    have hx0 : p.1 • x₀ ≠ p.2 • x₀ := fun h => hne (hfree p.1 hp1.1 p.2 hp2.1 h)
    obtain ⟨F, hF⟩ := shrinking p hp1 hp2 hx0
    exact hF (hpAll F)
  -- Finite intersection property.
  obtain ⟨F, hF⟩ := IsCompact.elim_directed_family_closed hsc Pf hPf_closed (Set.disjoint_iff_inter_eq_empty.mpr hst) hdir
  refine ⟨F.1, F.2.1, F.2.2, ?_⟩
  intro x hx x' hx' u hu u' hu' hux
  have hmem : (u, u') ∈ Pf F := ⟨hu, hu', x, hx, x', hx', hux⟩
  have hmemW : (u, u') ∈ W := by
    by_contra hcon
    exact (Set.eq_empty_iff_forall_notMem.mp (Set.disjoint_iff_inter_eq_empty.mp hF)) (u, u')
      ⟨⟨Set.mem_prod.mpr ⟨hu, hu'⟩, hcon⟩, hmem⟩
  obtain ⟨h1, h2⟩ := hmemW
  refine ⟨⟨U.mul_mem hu'.1 (U.inv_mem hu.1), ?_⟩, ⟨U.mul_mem (U.inv_mem hu.1) hu'.1, ?_⟩⟩
  · intro i j
    have := h1 i j
    linarith
  · intro i j
    have := h2 i j
    linarith

end Work.EKLRelCross
