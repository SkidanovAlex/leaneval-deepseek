import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# Every compact subset of `X₃ = SL₃(ℝ)/Γ₃` is the image of a compact subset of `SL₃(ℝ)`

The projection `mkX : SL₃(ℝ) → X₃` is a continuous *open* surjection.  Consequently, if `K ⊆ X₃`
is compact, it can be covered by finitely many open sets of the form `mkX '' (g • W)`, where
`W ∋ 1` is a relatively compact open neighbourhood of the identity; enlarging each sheet
`g • W` to `g • B` for a fixed compact box `B ⊇ W ∋ 1` gives a compact `C ⊆ SL₃(ℝ)` with
`K ⊆ mkX '' C`.

No Hausdorffness of `X₃` and no local injectivity of `mkX` is needed: we never form the preimage
of `K`, only finite covers by images of compact sets.
-/

namespace Work.EKLComp

open Work.EKLContract

theorem exists_isCompact_image (K : Set Work.EKLContract.X3)
    (hK : IsCompact K) :
    ∃ C : Set Work.EKLContract.SL3, IsCompact C ∧ K ⊆ Work.EKLContract.mkX '' C := by
  -- An open neighbourhood `V 1` of `1` and a compact entrywise box `B ⊇ V 1`.
  have hV := Work.EKLContract.Lemmas.V_open_one (1 : ℝ) (by norm_num)
  obtain ⟨hWopen, hW1⟩ := hV
  let B : Set SL3 := {g | ∀ i j, ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 1) ≤ g i j ∧
    g i j ≤ ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)}
  have hBcpt : IsCompact B :=
    Work.EKLProd.sl3EntryBox_compact
      (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - 1)
      (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + 1)
  have hWsubB : V (1 : ℝ) ⊆ B := by
    intro g hg i j
    have h := hg i j
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- `mkX` is an open map.
  have hmkXopen : IsOpenMap (mkX : SL3 → X3) := QuotientGroup.isOpenMap_coe
  -- The open cover of `X₃` by translates of `V 1`.
  have hUopen : ∀ g : SL3, IsOpen (mkX '' ((fun h : SL3 => g * h) '' (V (1 : ℝ)))) := by
    intro g
    rw [Set.image_image]
    exact (hmkXopen.comp (Homeomorph.mulLeft g).isOpenMap) _ hWopen
  have hcover : K ⊆ ⋃ g : SL3, mkX '' ((fun h : SL3 => g * h) '' (V (1 : ℝ))) := by
    intro x _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    refine Set.mem_iUnion.mpr ⟨h, ?_⟩
    exact ⟨h, ⟨1, hW1, mul_one h⟩, rfl⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun g : SL3 => mkX '' ((fun h : SL3 => g * h) '' (V (1 : ℝ)))) hUopen hcover
  -- The compact set: finitely many translates of the box `B`.
  refine ⟨⋃ g ∈ t, (fun h : SL3 => g * h) '' B, ?_, ?_⟩
  · exact t.isCompact_biUnion (fun g _ => hBcpt.image (by fun_prop))
  · intro x hx
    have hx' : x ∈ ⋃ g ∈ t, mkX '' ((fun h : SL3 => g * h) '' (V (1 : ℝ))) := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨g, hgt, hx''⟩ := hx'
    rw [Set.mem_image] at hx''
    obtain ⟨a, ⟨w, hw, rfl⟩, ha⟩ := hx''
    refine ⟨g * w, ?_, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨g, hgt, w, hWsubB hw, rfl⟩

end Work.EKLComp
