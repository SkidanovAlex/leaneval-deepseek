import Mathlib
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandBaseTwo
import Submission.Work.WilE7.BandAux.bandCompTwo_defs
import Submission.Work.WilE7.BandAux.bandSheetPartTwo_closed
import Submission.Work.WilE7.BandAux.bandSheetPartTwo_disjoint
import Submission.Work.WilE7.BandAux.bandSheetPartTwo_cover
import Submission.Work.WilE7.clopenPartition

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-- **The component of the two-strata band lies on the two sheets `i`, `j`.**

Let `S₁ S₂ : Stratum p (m+1)`, `Z : SemiPf (p+(m+1))`, `C = π_p (connectedComponentIn Z.set u₀)`,
and let `s₁ : Fin k₁ → C → ℝ^{m+1}`, `s₂ : Fin k₂ → C → ℝ^{m+1}` be continuous families of sheets
covering `S₁.X.set` (resp. `S₂.X.set`) over `C`, with `s₁ i x` (resp. `s₂ j x`) the value at `x`.
Let `p₀ = bandPt u₀ (s₁ i x₀) (s₂ j x₀) t₀`, `x₀ = π_p u₀`, be a point of the two-strata band

`bandS3two Z S₁ S₂ = {w | z₁, z₁' ∈ Z.set, z₂ ∈ S₁.X.set, z₂' ∈ S₂.X.set, π z₁ = π z₂,
   π z₁' = π z₂', z₁ = z₁', |t| ≤ 1, v₂ < t < v₂'}`.

Then every point `w` of the connected component of `p₀` has its second block on the sheet `s₁ i`
and its fourth block on the sheet `s₂ j`:

`z₂ w = (bandBase w, s₁ i (bandBase w))`, `z₂' w = (bandBase w, s₂ j (bandBase w))`.

The proof is the partition argument of `bandComp_sheets`: the "base in `C`" part of the set
decomposes into the finitely many clopen pieces `bandSheetPartTwo s₁ s₂ G (a,b)`, indexed by the
pair of sheets; the component of `p₀` lies in the piece `(i, j)` by connectedness, since `p₀` does. -/
theorem bandCompTwo_sheets {p m : ℕ} (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₁ : ∀ i, ContinuousOn (s₁ i) C)
    (hinj₁ : ∀ x ∈ C, Function.Injective fun i : Fin k₁ => s₁ i x)
    (hsub₁ : ∀ i : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ i x) ∈ S₁.X.set)
    (hcov₁ : ∀ z ∈ S₁.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ i : Fin k₁, s₁ i (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₂ : ∀ i, ContinuousOn (s₂ i) C)
    (hinj₂ : ∀ x ∈ C, Function.Injective fun i : Fin k₂ => s₂ i x)
    (hsub₂ : ∀ i : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ i x) ∈ S₂.X.set)
    (hcov₂ : ∀ z ∈ S₂.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ i : Fin k₂, s₂ i (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (i : Fin k₁) (j : Fin k₂) (t₀ : ℝ)
    (hp₀ : Work.WilE7.bandPt u₀ (s₁ i (WilkiesDesign.E.projFirst p (m + 1) u₀))
        (s₂ j (WilkiesDesign.E.projFirst p (m + 1) u₀)) t₀
      ∈ (Work.WilE7.bandS3two Z S₁ S₂).set) :
    ∀ w ∈ connectedComponentIn (Work.WilE7.bandS3two Z S₁ S₂).set
      (Work.WilE7.bandPt u₀ (s₁ i (WilkiesDesign.E.projFirst p (m + 1) u₀))
        (s₂ j (WilkiesDesign.E.projFirst p (m + 1) u₀)) t₀),
      Work.WilE7.bandZ2 w = Fin.append (Work.WilE7.BandAux.bandBase w)
        (s₁ i (Work.WilE7.BandAux.bandBase w)) ∧
      Work.WilE7.bandZ2' w = Fin.append (Work.WilE7.BandAux.bandBase w)
        (s₂ j (Work.WilE7.BandAux.bandBase w)) := by
  classical
  set p₀ := bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀
    with hp₀def
  -- the set of points of the band whose base lies in `C`
  set G : Set (Fin (bandDim p m) → ℝ) :=
    {w | w ∈ (bandS3two Z S₁ S₂).set ∧ bandBase w ∈ C} with hGdef
  have hp₀' : p₀ ∈ (bandS3two Z S₁ S₂).set := by rw [hp₀def]; exact hp₀
  have hp₀cond : bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3two Z S₁ S₂).set := hp₀
  have hOG : connectedComponentIn (bandS3two Z S₁ S₂).set p₀ ⊆ G := fun w hw =>
    ⟨connectedComponentIn_subset _ _ hw,
      bandCompTwo_base S₁ S₂ Z u₀ C hC (s₁ i (projFirst p (m + 1) u₀))
        (s₂ j (projFirst p (m + 1) u₀)) t₀ hp₀cond w (by simpa only [hp₀def] using hw)⟩
  have hp₀G : p₀ ∈ G := hOG (mem_connectedComponentIn hp₀')
  have hGconj : ∀ w ∈ G, w ∈ (bandS3two Z S₁ S₂).set ∧ bandBase w ∈ C := fun w hw => hw
  have hGbase : ∀ w ∈ G, bandBase w ∈ C := fun w hw => hw.2
  have hO_eq : connectedComponentIn (bandS3two Z S₁ S₂).set p₀ = connectedComponentIn G p₀ := by
    refine subset_antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hp₀') hOG
    · exact connectedComponentIn_mono p₀ (fun z hz => hz.1)
  -- the sheet partition of `G`: cover, pairwise disjointness and closedness of the pieces
  have hcover : ∀ x : G, ∃ ij : Fin k₁ × Fin k₂, x ∈ bandSheetPartTwo s₁ s₂ G ij :=
    bandSheetPartTwo_cover S₁ S₂ Z hcov₁ hcov₂ hGconj
  have hdisj : ∀ ij ij' : Fin k₁ × Fin k₂, ij ≠ ij' →
      Disjoint (bandSheetPartTwo s₁ s₂ G ij) (bandSheetPartTwo s₁ s₂ G ij') :=
    fun ij ij' hij => bandSheetPartTwo_disjoint hinj₁ hinj₂ hGbase hij
  have hcl : ∀ ij : Fin k₁ × Fin k₂, IsClosed (bandSheetPartTwo s₁ s₂ G ij) :=
    fun ij => bandSheetPartTwo_closed hcont₁ hcont₂ hGbase ij
  have hclopen : IsClopen (bandSheetPartTwo s₁ s₂ G (i, j)) :=
    clopenPartition (bandSheetPartTwo s₁ s₂ G) hcover hdisj hcl (i, j)
  -- the canonical point lies in the piece `(i, j)`
  have hp₀part : (⟨p₀, hp₀G⟩ : G) ∈ bandSheetPartTwo s₁ s₂ G (i, j) := by
    rw [mem_bandSheetPartTwo]
    constructor
    · change bandZ2 p₀ = Fin.append (bandBase p₀) (s₁ i (bandBase p₀))
      rw [hp₀def, bandZ2_bandPt]
      simp only [bandBase, bandZ1_bandPt]
    · change bandZ2' p₀ = Fin.append (bandBase p₀) (s₂ j (bandBase p₀))
      rw [hp₀def, bandZ2'_bandPt]
      simp only [bandBase, bandZ1_bandPt]
  -- hence the whole component of `p₀` in `G` lies in that piece
  have hcc : connectedComponent (⟨p₀, hp₀G⟩ : G) ⊆ bandSheetPartTwo s₁ s₂ G (i, j) :=
    hclopen.connectedComponent_subset hp₀part
  intro w hw
  have hwG : w ∈ G := hOG hw
  have hwmem : w ∈ connectedComponentIn G p₀ := hO_eq ▸ hw
  rw [mem_connectedComponentIn_subtype hp₀G] at hwmem
  obtain ⟨z, hz, hzv⟩ := hwmem
  have hzw : z = (⟨w, hwG⟩ : G) := Subtype.ext hzv
  have : (⟨w, hwG⟩ : G) ∈ bandSheetPartTwo s₁ s₂ G (i, j) := hzw ▸ (hcc hz)
  rwa [mem_bandSheetPartTwo] at this

end Work.WilE7.BandAux
