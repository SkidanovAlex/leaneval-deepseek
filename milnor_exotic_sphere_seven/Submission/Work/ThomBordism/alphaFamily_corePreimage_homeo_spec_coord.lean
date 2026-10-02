import Mathlib
import Submission.Work.ThomBordism.concatBlockCoord
import Submission.Work.ThomBordism.blockSpec_explicit
import Submission.Work.PTGeometric.alphaFamily_corePreimage_homeo_spec

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The *coordinate* form of the core-preimage homeomorphism of the `0`-end

`Work.PTGeometric.alphaFamily_corePreimage_homeo_spec` produces a homeomorphism
`H : {z | alphaFamily G m z ∈ G.core} ≃ₜ (Σ a : Fin m × ι, (Fam a.2).pt)` together with the
*value* of the piece point in coordinates, but it does not say *which* block of the two-level
concatenation `z` falls into, nor does it identify the cube point with the one produced by the
dyadic block recursion `Work.PTGeometric.genLoopListConcatStep`.

This file proves the coordinate form: the homeomorphism can be chosen so that the block index
(`outerStep`, `innerStep`) and the tube cube point (`blockTubePoint`) are read off *explicitly* from
`z`.  The proof is the proof of `alphaFamily_corePreimage_homeo_spec` with
`Work.ThomBordism.blockSpec_explicit` (the step-recursion form of the block decomposition) in place
of `Work.PTGeometric.AFS.blockSpec`, plus the bookkeeping of the two indices.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.ThomBordism

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-- The unfolding of the outer block coordinate. -/
theorem outerStep_eq (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    outerStep G m z = Work.PTGeometric.genLoopListConcatStep (outerCoord G m)
      (List.ofFn (fun _ : Fin m => Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)) z := rfl

/-- The unfolding of the inner block coordinate. -/
theorem innerStep_eq (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    innerStep G m z = Work.PTGeometric.genLoopListConcatStep (innerCoord G m)
      (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)) (outerStep G m z).2 := rfl

/-- The value of `finCongr` on a `Fin`. -/
theorem finCongr_val_nat {n n' : ℕ} (h : n = n') (w : Fin n) :
    ((finCongr h w : Fin n') : ℕ) = (w : ℕ) := by
  simp

/-- The unfolding of the tube cube point. -/
theorem blockTubePoint_eq (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    blockTubePoint G m z = (innerStep G m z).2 ∘ (finCongr (Nat.add_comm k 8)).symm := rfl

theorem alphaFamily_corePreimage_homeo_spec_coord
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    ∃ H : ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
        Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z ∈ G.core} ≃ₜ
      (Σ a : Fin m × ι, (Fam a.2).pt),
      ∀ z, (G.emb (H z).1.2).e (H z).2
            = Work.Tubular.cubeToEuc (8 + k) G.R
                (Work.ThomBordism.blockTubePoint G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1))
        ∧ ((H z).1.1 : ℕ)
            = (Work.ThomBordism.outerStep G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1)).1
        ∧ ((Fintype.equivFin ι (H z).1.2) : ℕ)
            = (Work.ThomBordism.innerStep G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1)).1 := by
  classical
  -- the outer block decomposition, with the dyadic block recursion
  obtain ⟨hO0, hO0spec⟩ := blockSpec_explicit (N := Fin (k + 8)) (X := D.T) (x := D.t₀)
    (outerCoord G m)
    (List.ofFn (fun _ : Fin m => Work.PTGeometric.blockInner (D := D) (Fam := Fam) G))
    (A := G.core) G.isClosed_core G.t0_notMem_core
  obtain ⟨hO1, hO1val⟩ := Work.PTGeometric.sigmaCongr_homeo_spec
    (ι := Fin (List.ofFn (fun _ : Fin m =>
      Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).length) (κ := Fin m)
    (X := fun kk => ↥(((List.ofFn (fun _ : Fin m =>
      Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).get kk) ⁻¹' G.core))
    (Y := fun _ : Fin m => ↥((Work.PTGeometric.blockInner (D := D) (Fam := Fam) G) ⁻¹' G.core))
    (finCongr List.length_ofFn) (fun kk => Homeomorph.setCongr (by rw [List.get_ofFn]))
  have hO1fst : ∀ w : (Σ kk : Fin (List.ofFn (fun _ : Fin m =>
        Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).length,
      ↥(((List.ofFn (fun _ : Fin m =>
        Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).get kk) ⁻¹' G.core)),
      ((hO1 w).1 : ℕ) = (w.1 : ℕ) := by
    intro w
    rw [hO1val w]
    exact finCongr_val_nat List.length_ofFn w.1
  have hO1snd : ∀ w : (Σ kk : Fin (List.ofFn (fun _ : Fin m =>
        Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).length,
      ↥(((List.ofFn (fun _ : Fin m =>
        Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).get kk) ⁻¹' G.core)),
      ((hO1 w).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = (w.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
    intro w
    rw [hO1val w]
    exact Work.PTGeometric.AFS.homeomorph_setCongr_coe _ _
  -- the inner block decomposition, with the dyadic block recursion
  obtain ⟨hI0, hI0spec⟩ := blockSpec_explicit (N := Fin (k + 8)) (X := D.T) (x := D.t₀)
    (innerCoord G m) (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G))
    (A := G.core) G.isClosed_core G.t0_notMem_core
  obtain ⟨hI1, hI1val⟩ := Work.PTGeometric.sigmaCongr_homeo_spec
    (ι := Fin (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).length)
    (κ := Fin (Fintype.card ι))
    (X := fun j => ↥(((List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).get j) ⁻¹' G.core))
    (Y := fun j : Fin (Fintype.card ι) =>
      ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core))
    (finCongr List.length_ofFn) (fun j => Homeomorph.setCongr (by rw [List.get_ofFn, ← finCongr_apply]))
  have hI1fst : ∀ w : (Σ j : Fin (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).length,
      ↥(((List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).get j) ⁻¹' G.core)),
      ((hI1 w).1 : ℕ) = (w.1 : ℕ) := by
    intro w
    rw [hI1val w]
    exact finCongr_val_nat List.length_ofFn w.1
  have hI1snd : ∀ w : (Σ j : Fin (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).length,
      ↥(((List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).get j) ⁻¹' G.core)),
      ((hI1 w).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = (w.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
    intro w
    rw [hI1val w]
    exact Work.PTGeometric.AFS.homeomorph_setCongr_coe _ _
  -- the collapse homeomorphism of each piece, in coordinates
  have hColval : ∀ (j : Fin (Fintype.card ι))
      (s : ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core)),
      (G.emb ((Fintype.equivFin ι).symm j)).e
        ((Classical.choose (Work.PTGeometric.collapse_corePreimage_homeo_spec G
          ((Fintype.equivFin ι).symm j))) s)
        = Work.Tubular.cubeToEuc (8 + k) G.R
            (fun jj => (s : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
              ((finCongr (Nat.add_comm k 8)).symm jj)) :=
    fun j s => Classical.choose_spec
      (Work.PTGeometric.collapse_corePreimage_homeo_spec G ((Fintype.equivFin ι).symm j)) s
  -- the pieces of the final homeomorphism
  obtain ⟨hG3J, hG3Jval⟩ := Work.PTGeometric.sigmaCongr_homeo_spec
    (ι := Fin (Fintype.card ι)) (κ := Fin (Fintype.card ι))
    (X := fun j => ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core))
    (Y := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt)
    (Equiv.refl (Fin (Fintype.card ι)))
    (fun j => Classical.choose (Work.PTGeometric.collapse_corePreimage_homeo_spec G
      ((Fintype.equivFin ι).symm j)))
  obtain ⟨hG3, hG3val⟩ := Work.PTGeometric.sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => (Σ j : Fin (Fintype.card ι),
      ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core)))
    (Y := fun _ : Fin m => (Σ j : Fin (Fintype.card ι),
      (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Equiv.refl (Fin m)) (fun _ => hG3J)
  obtain ⟨hG2, hG2val⟩ := Work.PTGeometric.sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => ↥((Work.PTGeometric.blockInner (D := D) (Fam := Fam) G) ⁻¹' G.core))
    (Y := fun _ : Fin m => (Σ j : Fin (Fintype.card ι),
      ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core)))
    (Equiv.refl (Fin m)) (fun _ => hI0.trans hI1)
  obtain ⟨hIx, hIxval⟩ := Work.PTGeometric.sigmaCongr_homeo_spec
    (ι := Fin (Fintype.card ι)) (κ := ι)
    (X := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt) (Y := fun a => (Fam a).pt)
    ((Fintype.equivFin ι).symm) (fun j => Homeomorph.refl _)
  obtain ⟨hTl, hTlval⟩ := Work.PTGeometric.sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => (Σ j : Fin (Fintype.card ι),
      (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Y := fun _ : Fin m => (Σ a : ι, (Fam a).pt))
    (Equiv.refl (Fin m)) (fun _ => hIx)
  obtain ⟨hPr, hPrval⟩ := Work.PTGeometric.sigmaProd_homeo_spec (m := m) (ι := ι)
    (Z := fun a => (Fam a).pt)
  -- the final homeomorphism
  refine ⟨(hO0.trans hO1).trans (hG2.trans (hG3.trans (hTl.trans hPr))), ?_⟩
  intro z
  set v : (Σ s : Fin m, ↥((Work.PTGeometric.blockInner (D := D) (Fam := Fam) G) ⁻¹' G.core))
    := (hO0.trans hO1) z with hv
  set u : (Σ j : Fin (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).length,
      ↥(((List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).get j) ⁻¹' G.core))
    := hI0 v.2 with hu
  set u' : (Σ j : Fin (Fintype.card ι),
      ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core)) := hI1 u with hu'
  have hG2v : hG2 v = (⟨v.1, u'⟩ :
      (Σ _ : Fin m, Σ j : Fin (Fintype.card ι),
        ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G j) ⁻¹' G.core))) := by
    simp only [hG2val, Homeomorph.trans_apply, Equiv.refl_apply, hu, hu']
    rfl
  have hG3v : hG3 (hG2 v) = (⟨v.1, ⟨u'.1,
      (Classical.choose (Work.PTGeometric.collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩⟩ :
      (Σ _ : Fin m, Σ j : Fin (Fintype.card ι),
        (Fam ((Fintype.equivFin ι).symm j)).pt)) := by
    simp only [hG2v, hG3val, hG3Jval, Equiv.refl_apply]
    rfl
  have hTlv : hTl (hG3 (hG2 v)) = (⟨v.1, ⟨(Fintype.equivFin ι).symm u'.1,
      (Classical.choose (Work.PTGeometric.collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩⟩ :
      (Σ _ : Fin m, Σ a : ι, (Fam a).pt)) := by
    simp only [hG3v, hTlval, hIxval, Homeomorph.refl_apply, Equiv.refl_apply]
    rfl
  have hPrv : hPr (hTl (hG3 (hG2 v))) = (⟨(v.1, (Fintype.equivFin ι).symm u'.1),
      (Classical.choose (Work.PTGeometric.collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩ :
      (Σ a : Fin m × ι, (Fam a.2).pt)) := by
    simp only [hTlv, hPrval]
  -- the two block indices and the tube cube point, read off explicitly
  have hzv1 : (v.1 : ℕ) = (outerStep G m z).1 := by
    have h1 : (v.1 : ℕ) = ((hO0 z).1 : ℕ) := by
      change ((hO1 (hO0 z)).1 : ℕ) = ((hO0 z).1 : ℕ)
      exact hO1fst (hO0 z)
    exact h1.trans ((hO0spec z).1.trans (by rw [outerStep_eq]))
  have hzv2 : (v.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (outerStep G m z).2 := by
    have h1 : (v.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = ((hO0 z).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
      change (((hO1 (hO0 z)).2 : ↥((Work.PTGeometric.blockInner (D := D) (Fam := Fam) G) ⁻¹' G.core)) :
          Fin (k + 8) → Set.Icc (0 : ℝ) 1) = _
      exact hO1snd (hO0 z)
    exact h1.trans ((hO0spec z).2.trans (by rw [outerStep_eq]))
  have hu1 : (u.1 : ℕ) = (innerStep G m z).1 := by
    rw [hu]
    refine ((hI0spec v.2).1).trans ?_
    rw [hzv2, innerStep_eq]
  have hu2 : (u.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (innerStep G m z).2 := by
    rw [hu]
    refine ((hI0spec v.2).2).trans ?_
    rw [hzv2, innerStep_eq]
  have hu'1 : (u'.1 : ℕ) = (innerStep G m z).1 := by
    have h1 : (u'.1 : ℕ) = (u.1 : ℕ) := by
      rw [hu']
      exact hI1fst u
    exact h1.trans hu1
  have hu'2 : ((u'.2 : ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G u'.1) ⁻¹' G.core)) :
      Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (innerStep G m z).2 := by
    have h1 : ((u'.2 : ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G u'.1) ⁻¹' G.core)) :
        Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (u.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
      rw [hu']
      exact hI1snd u
    exact h1.trans hu2
  refine ⟨?_, ?_, ?_⟩
  · change (G.emb ((hPr (hTl (hG3 (hG2 v)))).1.2)).e (hPr (hTl (hG3 (hG2 v)))).2
      = Work.Tubular.cubeToEuc (8 + k) G.R
        (blockTubePoint G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1))
    rw [hPrv]
    rw [show blockTubePoint G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = (fun jj : Fin (8 + k) => ((u'.2 : ↥((Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G u'.1)
            ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
            ((finCongr (Nat.add_comm k 8)).symm jj)) from ?_]
    · exact hColval u'.1 u'.2
    · refine (blockTubePoint_eq G m (z : Fin (k + 8) → Set.Icc (0 : ℝ) 1)).trans ?_
      funext jj
      exact (congrFun hu'2 ((finCongr (Nat.add_comm k 8)).symm jj)).symm
  · change ((hPr (hTl (hG3 (hG2 v)))).1.1 : ℕ) = (outerStep G m z).1
    rw [hPrv]
    exact hzv1
  · change ((Fintype.equivFin ι (hPr (hTl (hG3 (hG2 v)))).1.2) : ℕ) = (innerStep G m z).1
    rw [hPrv, Equiv.apply_symm_apply]
    exact hu'1

end

end Work.ThomBordism
