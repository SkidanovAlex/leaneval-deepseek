import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.Ksub_compact
import Submission.Work.Mostow.BaryContinuity

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Topology
/-! **T3 of the strata chapter: `resStd` is a homomorphism on the setwise stabiliser of the
standard stratum, and a discrete subgroup of the stabiliser has discrete image and finite kernel.**

Route (see also `_rhd_test.lean` in this directory, which contains a nearly complete proof of this
very statement: it defines `φ : C →* PO k 1` and uses `finite_nearStab` together with
`hdist 0 (h • 0) = hdist 0 (φ h • 0)` to show that near-stabiliser sets in the image are finite;
prefer that route over a compactness/subsequence argument).
* *Homomorphism.*  For `g, h ∈ SetStabStd k m`, `Work.Mostow.stab_eq_blk` (PROVED) gives
  `g = blk k m (resStd k m g) (nrmStd k m g)` and `h = blk k m (resStd k m h) (nrmStd k m h)`;
  `g * h ∈ SetStabStd k m` (the stabiliser is a subgroup) so also
  `g * h = blk k m (resStd k m (g * h)) (nrmStd k m (g * h))`.  Comparing the two expressions for
  `g * h` through the action on Fermi points (`Work.Mostow.blk_smul_fermi`, PROVED) and the
  injectivity of `blk` (from `Work.Mostow.blk_hom`, PROVED) gives the multiplicative laws for
  `resStd` and for `nrmStd`.
* *Kernel finite.*  If `resStd k m c = 1` then `c = blk k m 1 (nrmStd k m c)` fixes `coordEmb k m v`
  for every `v`, in particular `coordEmb k m 0`; so the kernel is contained in
  `{c ∈ C | hdist 0 (c • 0) ≤ 1}`, finite by `Work.Mostow.finite_nearStab`.
* *Image discrete.*  Once `resStd` is known to be multiplicative on `C`, its image is a subgroup;
  if a sequence in the image converged to `h`, then discreteness of `C` together with the finiteness
  of the near-stabiliser sets at `h • 0` forces the sequence to be eventually constant. -/

namespace RdsAux

lemma mem_stab_iff {k m : ℕ} {g : PO (k + m) 1} :
    g ∈ SetStabStd k m ↔ ∀ u : E (k + m), u ∈ stdTG k m ↔ g • u ∈ stdTG k m := Iff.rfl

lemma fermi_zero_right (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  simp [fermi, coordEmb, sinhc]

lemma coordEmb_zero (k m : ℕ) : coordEmb k m (0 : E k) = (0 : E (k + m)) := by
  ext i
  refine Fin.addCases (motive := fun i => coordEmb k m 0 i = (0 : E (k + m)) i)
    (fun i => ?_) (fun i => ?_) i
  · simp [coordEmb]
  · simp [coordEmb]

lemma tanC_coordEmb (k m : ℕ) (v : E k) : tanC k m (coordEmb k m v) = v := by
  ext i; simp [tanC, coordEmb]

lemma coordEmb_injective (k m : ℕ) : Function.Injective (coordEmb k m) := by
  intro a b h
  have hh := congrArg (tanC k m) h
  rwa [tanC_coordEmb, tanC_coordEmb] at hh

lemma hdist_coordEmb (k m : ℕ) (hIk : HypIsometryProp k) (hI : HypIsometryProp (k + m))
    (v v' : E k) : hdist (coordEmb k m v) (coordEmb k m v') = hdist v v' := by
  refine Real.cosh_injOn ?_ ?_ ?_
  · exact (HypIsoData.ofProp hI).nonneg _ _
  · exact (HypIsoData.ofProp hIk).nonneg _ _
  · rw [← fermi_zero_right k m v, ← fermi_zero_right k m v', cosh_hdist_fermi k m v v' 0 0]
    simp [sinhc]

lemma blk_smul_coordEmb (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (h : PO k 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E k) :
    blk k m h R • coordEmb k m v = coordEmb k m (h • v) := by
  rw [← fermi_zero_right k m v, blk_smul_fermi k m hAk hIk hA hI h R v 0, map_zero,
    fermi_zero_right]

lemma one_mem_stab (k m : ℕ) (hA : POActionProp (k + m)) :
    (1 : PO (k + m) 1) ∈ SetStabStd k m := by
  rw [mem_stab_iff]
  intro u
  rw [(POBasic.ofProp hA).one_smul u]

lemma mul_mem_stab (k m : ℕ) (hA : POActionProp (k + m)) {g h : PO (k + m) 1}
    (hg : g ∈ SetStabStd k m) (hh : h ∈ SetStabStd k m) : g * h ∈ SetStabStd k m := by
  rw [mem_stab_iff] at hg hh ⊢
  intro u
  rw [(POBasic.ofProp hA).mul_smul g h u, hh u, hg (h • u)]

lemma inv_mem_stab (k m : ℕ) (hA : POActionProp (k + m)) {g : PO (k + m) 1}
    (hg : g ∈ SetStabStd k m) : g⁻¹ ∈ SetStabStd k m := by
  rw [mem_stab_iff] at hg ⊢
  intro u
  have h1 := hg (g⁻¹ • u)
  have h2 : g • (g⁻¹ • u) = u := by
    rw [show g • (g⁻¹ • u) = (g * g⁻¹) • u from ((POBasic.ofProp hA).mul_smul g g⁻¹ u).symm,
      mul_inv_cancel g, (POBasic.ofProp hA).one_smul]
  rw [h2] at h1
  exact h1.symm

lemma stab_form (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) :
    g = blk k m (resStd k m g) (nrmStd k m g) :=
  stab_eq_blk k m hAk hIk hA hI g hg

lemma resStd_smul_coordEmb (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) (v : E k) :
    g • coordEmb k m v = coordEmb k m (resStd k m g • v) := by
  calc g • coordEmb k m v = blk k m (resStd k m g) (nrmStd k m g) • coordEmb k m v := by
        conv_lhs => rw [stab_form k m hAk hIk hA hI hg]
    _ = coordEmb k m (resStd k m g • v) := blk_smul_coordEmb k m hAk hIk hA hI _ _ v

lemma resStd_smul_zero (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) :
    g • (0 : E (k + m)) = coordEmb k m (resStd k m g • (0 : E k)) := by
  rw [← coordEmb_zero k m, resStd_smul_coordEmb k m hAk hIk hA hI hg]

lemma hdist_disp (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) :
    hdist (0 : E (k + m)) (g • (0 : E (k + m))) = hdist (0 : E k) (resStd k m g • (0 : E k)) := by
  rw [← coordEmb_zero k m, resStd_smul_coordEmb k m hAk hIk hA hI hg,
    hdist_coordEmb k m hIk hI]

lemma resStd_mul (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g h : PO (k + m) 1} (hg : g ∈ SetStabStd k m) (hh : h ∈ SetStabStd k m) :
    resStd k m (g * h) = resStd k m g * resStd k m h := by
  have hgh : g * h ∈ SetStabStd k m := mul_mem_stab k m hA hg hh
  have e1 := stab_form k m hAk hIk hA hI hgh
  have e2 : g * h = blk k m (resStd k m g * resStd k m h) (nrmStd k m g * nrmStd k m h) := by
    conv_lhs => rw [stab_form k m hAk hIk hA hI hg, stab_form k m hAk hIk hA hI hh]
    rw [← (blk_hom k m hAk hIk hA hI).1]
  exact ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _ (e1.symm.trans e2)).1

lemma resStd_one (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) :
    resStd k m (1 : PO (k + m) 1) = 1 := by
  have h1 : (1 : PO (k + m) 1) ∈ SetStabStd k m := one_mem_stab k m hA
  have e1 := stab_form k m hAk hIk hA hI h1
  have e2 : blk k m (resStd k m 1) (nrmStd k m 1) = blk k m 1 1 := by
    rw [← e1, (blk_hom k m hAk hIk hA hI).2.1]
  exact ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _ e2).1

lemma resStd_inv (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    {g : PO (k + m) 1} (hg : g ∈ SetStabStd k m) :
    resStd k m g⁻¹ = (resStd k m g)⁻¹ := by
  have h2 := resStd_mul k m hAk hIk hA hI (inv_mem_stab k m hA hg) hg
  rw [inv_mul_cancel g, resStd_one k m hAk hIk hA hI] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

set_option maxHeartbeats 1000000 in
/-- A subgroup of `PO k 1` whose orbit balls at `0` are finite is discrete. -/
lemma isDiscrete_range (k : ℕ) (hAk : POActionProp k)
    (H : Subgroup (PO k 1))
    (hfin : ∀ R : ℝ, {h : PO k 1 | h ∈ H ∧ hdist (0 : E k) (h • (0 : E k)) ≤ R}.Finite) :
    IsDiscrete (SetLike.coe H) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro h hhH
  have hSfin : ({h' : PO k 1 | h' ∈ H ∧ hdist (0 : E k) (h' • (0 : E k)) ≤
      hdist (0 : E k) (h • (0 : E k)) + 1} : Set (PO k 1)).Finite := hfin _
  refine ⟨{g : PO k 1 | hdist (0 : E k) (g • (0 : E k)) <
        hdist (0 : E k) (h • (0 : E k)) + 1} ∩
      ({h' : PO k 1 | h' ∈ H ∧ hdist (0 : E k) (h' • (0 : E k)) ≤
        hdist (0 : E k) (h • (0 : E k)) + 1} \ {h})ᶜ, ?_, ?_⟩
  · refine IsOpen.inter ?_ ?_
    · have hball : IsOpen {y : E k | hdist (0 : E k) y < hdist (0 : E k) (h • (0 : E k)) + 1} :=
        isOpen_lt (continuous_hdist_zero (n := k)) continuous_const
      exact hball.preimage (continuous_smul_zero hAk)
    · exact (hSfin.subset Set.sdiff_subset).isClosed.isOpen_compl
  · ext g
    constructor
    · rintro ⟨⟨hlt, hnotin⟩, hgH⟩
      by_contra hne
      refine hnotin ⟨⟨hgH, ?_⟩, hne⟩
      show hdist (0 : E k) (g • (0 : E k)) ≤ hdist (0 : E k) (h • (0 : E k)) + 1
      exact le_of_lt hlt
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, hhH⟩
      · show hdist (0 : E k) (g • (0 : E k)) < hdist (0 : E k) (g • (0 : E k)) + 1
        exact lt_add_one _
      · intro hh
        exact hh.2 rfl

end RdsAux

set_option maxHeartbeats 1000000 in
theorem resStdDiscreteStrata (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k) (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) : (∀ g h : PO (k + m) 1, g ∈ SetStabStd k m → h ∈ SetStabStd k m → resStd k m (g * h) = resStd k m g * resStd k m h) ∧ ∀ C : Subgroup (PO (k + m) 1), IsDiscrete (SetLike.coe C) → (∀ c ∈ C, c ∈ SetStabStd k m) → IsDiscrete (SetLike.coe (Subgroup.closure (resStd k m '' (C : Set (PO (k + m) 1))))) ∧ {c : PO (k + m) 1 | c ∈ C ∧ resStd k m c = 1}.Finite := by
  refine ⟨fun g h hg hh => RdsAux.resStd_mul k m hAk hIk hA hI hg hh, fun C hC hCsub => ?_⟩
  let H : Subgroup (PO k 1) := Subgroup.closure (resStd k m '' (C : Set (PO (k + m) 1)))
  have hmem : ∀ h ∈ H, ∃ c : C, resStd k m (c : PO (k + m) 1) = h := by
    intro h hh
    refine Subgroup.closure_induction
      (p := fun h _ => ∃ c : C, resStd k m (c : PO (k + m) 1) = h) ?_ ?_ ?_ ?_ hh
    · rintro y ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    · exact ⟨1, RdsAux.resStd_one k m hAk hIk hA hI⟩
    · rintro x y hx hy ihx ihy
      obtain ⟨c₁, hc₁⟩ := ihx
      obtain ⟨c₂, hc₂⟩ := ihy
      exact ⟨c₁ * c₂, by
        rw [show ((c₁ * c₂ : C) : PO (k + m) 1) = (c₁ : PO (k + m) 1) * (c₂ : PO (k + m) 1)
            from rfl,
          RdsAux.resStd_mul k m hAk hIk hA hI (hCsub _ c₁.2) (hCsub _ c₂.2), hc₁, hc₂]⟩
    · rintro x hx ih
      obtain ⟨c, hc⟩ := ih
      exact ⟨c⁻¹, by
        rw [show ((c⁻¹ : C) : PO (k + m) 1) = (c : PO (k + m) 1)⁻¹ from rfl,
          RdsAux.resStd_inv k m hAk hIk hA hI (hCsub _ c.2), hc]⟩
  have hfin : ∀ R : ℝ, {h : PO k 1 | h ∈ H ∧ hdist (0 : E k) (h • (0 : E k)) ≤ R}.Finite := by
    intro R
    have hCfin : ({c : C | hdist (0 : E (k + m)) ((c : PO (k + m) 1) • (0 : E (k + m))) ≤ R} : Set C).Finite :=
      finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hC R
    refine (hCfin.image (fun c : C => resStd k m (c : PO (k + m) 1))).subset ?_
    rintro h ⟨hhH, hhd⟩
    obtain ⟨c, hc⟩ := hmem h hhH
    refine ⟨c, ?_, hc⟩
    show hdist (0 : E (k + m)) ((c : PO (k + m) 1) • (0 : E (k + m))) ≤ R
    rw [← hc] at hhd
    rwa [RdsAux.hdist_disp k m hAk hIk hA hI (hCsub _ c.2)]
  have hdisc : IsDiscrete (SetLike.coe H) := RdsAux.isDiscrete_range k hAk H hfin
  refine ⟨hdisc, ?_⟩
  have hKfin : ({c : C | resStd k m (c : PO (k + m) 1) = 1} : Set C).Finite := by
    refine (finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hC 0).subset ?_
    intro c hc
    have hfix : (c : PO (k + m) 1) • (0 : E (k + m)) = 0 := by
      rw [RdsAux.resStd_smul_zero k m hAk hIk hA hI (hCsub _ c.2), hc,
        (POBasic.ofProp hAk).one_smul (0 : E k), RdsAux.coordEmb_zero k m]
    have h0 : hdist (0 : E (k + m)) (0 : E (k + m)) = 0 :=
      (HypIsoData.ofProp hI).eq_zero 0 0 |>.mpr rfl
    show hdist (0 : E (k + m)) ((c : PO (k + m) 1) • (0 : E (k + m))) ≤ 0
    rw [hfix, h0]
  exact (hKfin.image (fun c : C => (c : PO (k + m) 1))).subset (by
    rintro c ⟨hcC, hrc⟩
    exact ⟨⟨c, hcC⟩, hrc, rfl⟩)

end Work.Mostow
