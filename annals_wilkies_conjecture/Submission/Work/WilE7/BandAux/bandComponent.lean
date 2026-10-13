/-
  WilE7 (`Work.WilE7.BandAux.bandComponent`): the connected-component argument for the band cell.

  Let `S : Stratum p (m+1)`, `Z : SemiPf (p+(m+1))`, `C = π_p (connectedComponentIn Z.set u₀)` and
  let `s j : C → ℝ^{m+1}` be `k` continuous sheets covering `S.X.set` over `C`.  Write
  `p₀ = bandPt u₀ (s i x₀) (s j x₀) t₀` for `x₀ = π_p u₀` and `t₀` strictly between the two levels,
  and let `O` be the connected component of `p₀` in `(bandS3 Z S).set`.  Then

  * the base projection of every point of `O` lies in `C` (`bandComp_base`);
  * every point of `O` lies on the sheets `i` and `j` (`bandComp_sheets`, by the clopen
    partition of the "base in `C`" part of the set according to the sheet index);
  * every point of the band is the `bandExtract`-image of a point of `O` (`bandComp_cover`).
-/
import Mathlib
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.band_preconn
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.clopenPartition
import Submission.Work.WilE7.sheetComponent

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.BandAux
open Work.WilE7 WilkiesDesign WilkiesDesign.E

variable {p m : ℕ}

/-! ## §1. The base projection and continuity of the coordinates -/

/-- The base projection of a point of the ambient space of `bandS3`: the first `p` coordinates of
its first block. -/
def bandBase (w : Fin (bandDim p m) → ℝ) : Fin p → ℝ := projFirst p (m + 1) (bandZ1 w)

theorem continuous_bandZ1 {p m : ℕ} : Continuous (bandZ1 (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (bandZ1Idx p m i)

theorem continuous_bandZ2 {p m : ℕ} : Continuous (bandZ2 (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (bandZ2Idx p m i)

theorem continuous_bandZ1' {p m : ℕ} : Continuous (bandZ1' (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (bandZ1'Idx p m i)

theorem continuous_bandZ2' {p m : ℕ} : Continuous (bandZ2' (p := p) (m := m)) :=
  continuous_pi fun i => continuous_apply (bandZ2'Idx p m i)

theorem continuous_bandT {p m : ℕ} : Continuous (bandT (p := p) (m := m)) :=
  continuous_apply (bandTIdx p m)

theorem continuous_bandBase {p m : ℕ} : Continuous (bandBase (p := p) (m := m)) :=
  (continuous_projFirst p (m + 1)).comp continuous_bandZ1

/-! ## §2. The base of the component lies in `C` -/

theorem bandComp_base {p m : ℕ} (S : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (v v' : Fin (m + 1) → ℝ) (t₀ : ℝ)
    (hp₀ : bandPt u₀ v v' t₀ ∈ (bandS3 Z S).set) :
    ∀ w ∈ connectedComponentIn (bandS3 Z S).set (bandPt u₀ v v' t₀), bandBase w ∈ C := by
  intro w hw
  have hZ : ∀ y ∈ connectedComponentIn (bandS3 Z S).set (bandPt u₀ v v' t₀),
      bandZ1 y ∈ Z.set :=
    fun y hy => ((bandS3_mem_iff Z S y).mp (connectedComponentIn_subset _ _ hy)).1
  have hmem := imageSubsetConnectedComponentIn
    (s := connectedComponentIn (bandS3 Z S).set (bandPt u₀ v v' t₀))
    isPreconnected_connectedComponentIn continuous_bandZ1.continuousOn
    (mem_connectedComponentIn hp₀) hZ w hw
  rw [bandZ1_bandPt u₀ v v' t₀] at hmem
  show projFirst p (m + 1) (bandZ1 w) ∈ C
  rw [hC]
  exact ⟨bandZ1 w, hmem, rfl⟩

/-! ## §3. The sheet partition of the "base in `C`" part -/

/-- The part of `G` whose second block lies on the sheet `s i` and whose fourth block lies on the
sheet `s j`. -/
def bandSheetPart {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (G : Set (Fin (bandDim p m) → ℝ)) (ij : Fin k × Fin k) : Set G :=
  {w : G | bandZ2 w.1 = Fin.append (bandBase w.1) (s ij.1 (bandBase w.1)) ∧
    bandZ2' w.1 = Fin.append (bandBase w.1) (s ij.2 (bandBase w.1))}

theorem mem_bandSheetPart {p m k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    {G : Set (Fin (bandDim p m) → ℝ)} {ij : Fin k × Fin k} {w : G} :
    w ∈ bandSheetPart s G ij ↔
      (bandZ2 w.1 = Fin.append (bandBase w.1) (s ij.1 (bandBase w.1)) ∧
        bandZ2' w.1 = Fin.append (bandBase w.1) (s ij.2 (bandBase w.1))) := Iff.rfl

/-- Each piece of the sheet partition is closed in `G`. -/
theorem bandSheetPart_closed {p m k : ℕ} {C : Set (Fin p → ℝ)}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} (hcont : ∀ i, ContinuousOn (s i) C)
    {G : Set (Fin (bandDim p m) → ℝ)} (hG : ∀ w ∈ G, bandBase w ∈ C) (ij : Fin k × Fin k) :
    IsClosed (bandSheetPart s G ij) := by
  have hbase : Continuous (fun w : G => bandBase w.1) :=
    continuous_bandBase.comp continuous_subtype_val
  have h2 : Continuous (fun w : G => bandZ2 w.1) :=
    continuous_bandZ2.comp continuous_subtype_val
  have h2' : Continuous (fun w : G => bandZ2' w.1) :=
    continuous_bandZ2'.comp continuous_subtype_val
  have hs1 : Continuous (fun w : G => s ij.1 (bandBase w.1)) :=
    (hcont ij.1).comp_continuous hbase (fun w => hG w.1 w.2)
  have hs2 : Continuous (fun w : G => s ij.2 (bandBase w.1)) :=
    (hcont ij.2).comp_continuous hbase (fun w => hG w.1 w.2)
  have hA1 : Continuous (fun w : G => Fin.append (bandBase w.1) (s ij.1 (bandBase w.1))) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp (hbase.prodMk hs1)
  have hA2 : Continuous (fun w : G => Fin.append (bandBase w.1) (s ij.2 (bandBase w.1))) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp (hbase.prodMk hs2)
  rw [show bandSheetPart s G ij =
      {w : G | bandZ2 w.1 = Fin.append (bandBase w.1) (s ij.1 (bandBase w.1))} ∩
      {w : G | bandZ2' w.1 = Fin.append (bandBase w.1) (s ij.2 (bandBase w.1))} from by
    ext w
    simp only [bandSheetPart, Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact (isClosed_eq h2 hA1).inter (isClosed_eq h2' hA2)

/-- The pieces of the sheet partition are pairwise disjoint (the sheets are pointwise distinct). -/
theorem bandSheetPart_disjoint {p m k : ℕ} {C : Set (Fin p → ℝ)}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    {G : Set (Fin (bandDim p m) → ℝ)} (hG : ∀ w ∈ G, bandBase w ∈ C)
    {ij ij' : Fin k × Fin k} (hij : ij ≠ ij') :
    Disjoint (bandSheetPart s G ij) (bandSheetPart s G ij') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_bandSheetPart] at hx hx'
  have hxb : bandBase x.1 ∈ C := hG x.1 x.2
  have h1 : ij.1 = ij'.1 := by
    refine hinj (bandBase x.1) hxb ?_
    show s ij.1 (bandBase x.1) = s ij'.1 (bandBase x.1)
    have e1 : s ij.1 (bandBase x.1) = projSnd p (m + 1) (bandZ2 x.1) := by
      rw [hx.1, projSnd_append]
    have e1' : s ij'.1 (bandBase x.1) = projSnd p (m + 1) (bandZ2 x.1) := by
      rw [hx'.1, projSnd_append]
    rw [e1, e1']
  have h2 : ij.2 = ij'.2 := by
    refine hinj (bandBase x.1) hxb ?_
    show s ij.2 (bandBase x.1) = s ij'.2 (bandBase x.1)
    have e2 : s ij.2 (bandBase x.1) = projSnd p (m + 1) (bandZ2' x.1) := by
      rw [hx.2, projSnd_append]
    have e2' : s ij'.2 (bandBase x.1) = projSnd p (m + 1) (bandZ2' x.1) := by
      rw [hx'.2, projSnd_append]
    rw [e2, e2']
  exact hij (Prod.ext h1 h2)

/-- The pieces of the sheet partition cover `G` (the sheets cover `S.X.set` over `C`). -/
theorem bandSheetPart_cover {p m k : ℕ} (S : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    {C : Set (Fin p → ℝ)} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (_hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    {G : Set (Fin (bandDim p m) → ℝ)}
    (hG : ∀ w ∈ G, w ∈ (bandS3 Z S).set ∧ bandBase w ∈ C) :
    ∀ x : G, ∃ ij : Fin k × Fin k, x ∈ bandSheetPart s G ij := by
  intro x
  have hxS3 : x.1 ∈ (bandS3 Z S).set := (hG x.1 x.2).1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, -⟩ := (bandS3_mem_iff Z S x.1).mp hxS3
  have hxb : bandBase x.1 ∈ C := (hG x.1 x.2).2
  have hb2 : projFirst p (m + 1) (bandZ2 x.1) ∈ C := by rw [← h5]; exact hxb
  have hb4 : projFirst p (m + 1) (bandZ2' x.1) ∈ C := by
    rw [← (congrArg (projFirst p (m + 1)) h7).trans h6]
    exact hxb
  obtain ⟨a, ha⟩ := hcov (bandZ2 x.1) h2 hb2
  obtain ⟨b, hb⟩ := hcov (bandZ2' x.1) h4 hb4
  refine ⟨(a, b), ?_⟩
  rw [mem_bandSheetPart]
  constructor
  · show bandZ2 x.1 = Fin.append (bandBase x.1) (s a (bandBase x.1))
    show bandZ2 x.1 = Fin.append (projFirst p (m + 1) (bandZ1 x.1))
      (s a (projFirst p (m + 1) (bandZ1 x.1)))
    rw [h5, ha]
    exact (append_projFirst_projSnd (bandZ2 x.1)).symm
  · show bandZ2' x.1 = Fin.append (bandBase x.1) (s b (bandBase x.1))
    show bandZ2' x.1 = Fin.append (projFirst p (m + 1) (bandZ1 x.1))
      (s b (projFirst p (m + 1) (bandZ1 x.1)))
    rw [show projFirst p (m + 1) (bandZ1 x.1) = projFirst p (m + 1) (bandZ2' x.1) from
      (congrArg (projFirst p (m + 1)) h7).trans h6, hb]
    exact (append_projFirst_projSnd (bandZ2' x.1)).symm

/-! ## §4. The component lies on the sheets `i` and `j` -/

theorem bandComp_sheets {p m : ℕ} (S : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (i j : Fin k) (t₀ : ℝ)
    (hp₀ : bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3 Z S).set) :
    ∀ w ∈ connectedComponentIn (bandS3 Z S).set
      (bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀),
      bandZ2 w = Fin.append (bandBase w) (s i (bandBase w)) ∧
      bandZ2' w = Fin.append (bandBase w) (s j (bandBase w)) := by
  classical
  set p₀ := bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  set G : Set (Fin (bandDim p m) → ℝ) :=
    {w | w ∈ (bandS3 Z S).set ∧ bandBase w ∈ C} with hGdef
  have hp₀' : p₀ ∈ (bandS3 Z S).set := by rw [hp₀def]; exact hp₀
  have hp₀cond : bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3 Z S).set := hp₀
  have hOG : connectedComponentIn (bandS3 Z S).set p₀ ⊆ G := fun w hw =>
    ⟨connectedComponentIn_subset _ _ hw,
      bandComp_base S Z u₀ C hC (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀))
        t₀ hp₀cond w (by simpa only [hp₀def] using hw)⟩
  have hp₀G : p₀ ∈ G := hOG (mem_connectedComponentIn hp₀')
  have hGconj : ∀ w ∈ G, w ∈ (bandS3 Z S).set ∧ bandBase w ∈ C := fun w hw => hw
  have hGbase : ∀ w ∈ G, bandBase w ∈ C := fun w hw => hw.2
  have hO_eq : connectedComponentIn (bandS3 Z S).set p₀ = connectedComponentIn G p₀ := by
    refine subset_antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hp₀') hOG
    · exact connectedComponentIn_mono p₀ (fun z hz => hz.1)
  have hcover : ∀ x : G, ∃ ij : Fin k × Fin k, x ∈ bandSheetPart s G ij :=
    bandSheetPart_cover S Z hsub hcov hGconj
  have hdisj : ∀ ij ij' : Fin k × Fin k, ij ≠ ij' →
      Disjoint (bandSheetPart s G ij) (bandSheetPart s G ij') :=
    fun ij ij' hij => bandSheetPart_disjoint hinj hGbase hij
  have hcl : ∀ ij : Fin k × Fin k, IsClosed (bandSheetPart s G ij) :=
    fun ij => bandSheetPart_closed hcont hGbase ij
  have hclopen : IsClopen (bandSheetPart s G (i, j)) :=
    clopenPartition (bandSheetPart s G) hcover hdisj hcl (i, j)
  have hp₀part : (⟨p₀, hp₀G⟩ : G) ∈ bandSheetPart s G (i, j) := by
    rw [mem_bandSheetPart]
    constructor
    · change bandZ2 p₀ = Fin.append (bandBase p₀) (s i (bandBase p₀))
      rw [hp₀def, bandZ2_bandPt]
      simp only [bandBase, bandZ1_bandPt]
    · change bandZ2' p₀ = Fin.append (bandBase p₀) (s j (bandBase p₀))
      rw [hp₀def, bandZ2'_bandPt]
      simp only [bandBase, bandZ1_bandPt]
  have hcc : connectedComponent (⟨p₀, hp₀G⟩ : G) ⊆ bandSheetPart s G (i, j) :=
    hclopen.connectedComponent_subset hp₀part
  intro w hw
  have hwG : w ∈ G := hOG hw
  have hwmem : w ∈ connectedComponentIn G p₀ := hO_eq ▸ hw
  rw [mem_connectedComponentIn_subtype hp₀G] at hwmem
  obtain ⟨z, hz, hzv⟩ := hwmem
  have hzw : z = (⟨w, hwG⟩ : G) := Subtype.ext hzv
  have : (⟨w, hwG⟩ : G) ∈ bandSheetPart s G (i, j) := hzw ▸ (hcc hz)
  rwa [mem_bandSheetPart] at this

/-! ## §5. The parametrisation of the band over the component of `Z` -/

/-- The base component of `Z` through `u₀`. -/
def bandZc {p m : ℕ} (Z : SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) :
    Set (Fin (p + (m + 1)) → ℝ) := connectedComponentIn Z.set u₀

/-- The `j`-th level function of the sheets, as an extended real. -/
def bandLevel {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k) :
    (Fin (p + (m + 1)) → ℝ) → EReal :=
  fun u => ((s j (projFirst p (m + 1) u)) (Fin.last m) : EReal)

/-- The band over the base component of `Z`, between the levels of the sheets `i` and `j`. -/
def bandH {p m k : ℕ} (Z : SemiPf (p + (m + 1))) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (i j : Fin k) (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ bandZc Z u₀ ∧ bandLevel s i q.1 < (q.2 : EReal) ∧
    (q.2 : EReal) < bandLevel s j q.1}

/-- The parametrisation of the band: `(u, t) ↦ bandPt u (s i (π u)) (s j (π u)) t`. -/
def bandPhi {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (i j : Fin k) :
    ((Fin (p + (m + 1)) → ℝ) × ℝ) → Fin (bandDim p m) → ℝ :=
  fun q => bandPt q.1 (s i (projFirst p (m + 1) q.1)) (s j (projFirst p (m + 1) q.1)) q.2

theorem bandPhi_fst_mem {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {i j : Fin k}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ}
    (hq : q ∈ bandH Z s i j u₀) : q.1 ∈ bandZc Z u₀ := by
  rw [bandH] at hq; exact hq.1

theorem continuousOn_bandPhi {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {C : Set (Fin p → ℝ)} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)}
    (u₀ : Fin (p + (m + 1)) → ℝ) (hcont : ∀ i, ContinuousOn (s i) C)
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (i j : Fin k) :
    ContinuousOn (bandPhi s i j) (bandH Z s i j u₀) := by
  have hfst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => q.1)
      (bandH Z s i j u₀) := continuous_fst.continuousOn
  have hsnd : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => q.2)
      (bandH Z s i j u₀) := continuous_snd.continuousOn
  have hpi : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => projFirst p (m + 1) q.1)
      (bandH Z s i j u₀) := (continuous_projFirst p (m + 1)).comp_continuousOn hfst
  have hmap : ∀ q ∈ bandH Z s i j u₀, projFirst p (m + 1) q.1 ∈ C := by
    intro q hq
    rw [bandH] at hq
    rw [hC]
    exact ⟨q.1, hq.1, rfl⟩
  have hsi : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => s i (projFirst p (m + 1) q.1))
      (bandH Z s i j u₀) := (hcont i).comp hpi hmap
  have hsj : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => s j (projFirst p (m + 1) q.1))
      (bandH Z s i j u₀) := (hcont j).comp hpi hmap
  have hA : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (s i (projFirst p (m + 1) q.1)))
      (bandH Z s i j u₀) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hsi)
  have hB : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)))
      (bandH Z s i j u₀) :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hsj)
  have hp1 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1) (s i (projFirst p (m + 1) q.1))))
      (bandH Z s i j u₀) :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hA)
  have hp2 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1))))
      (bandH Z s i j u₀) :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hB)
  have hfirst4 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append
        (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1) (s i (projFirst p (m + 1) q.1))))
        (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1)))))
      (bandH Z s i j u₀) :=
    (Fin.continuous_append (X := ℝ) ((p + (m + 1)) + (p + (m + 1)))
      ((p + (m + 1)) + (p + (m + 1)))).comp_continuousOn (hp1.prodMk hp2)
  have hconst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      (fun _ : Fin 1 => q.2)) (bandH Z s i j u₀) :=
    (continuous_pi (fun _ => continuous_snd)).continuousOn
  exact (Fin.continuous_append (X := ℝ) (bandK p m) 1).comp_continuousOn (hfirst4.prodMk hconst)

/-! ## §6. Coverage: every band point is hit by the component -/

theorem bandComp_cover {p m : ℕ} (S : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (i j : Fin k) (t₀ : ℝ)
    (hp₀ : bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀
      ∈ (bandS3 Z S).set)
    (hlvl : ∀ x ∈ C, (s i x) (Fin.last m) < (s j x) (Fin.last m))
    (y : Fin (p + 1) → ℝ) (hy : Fin.init y ∈ C)
    (h1 : (s i (Fin.init y)) (Fin.last m) < y (Fin.last p))
    (h2 : y (Fin.last p) < (s j (Fin.init y)) (Fin.last m)) :
    ∃ w ∈ connectedComponentIn (bandS3 Z S).set
        (bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀),
      bandExtract w = y := by
  classical
  set p₀ := bandPt u₀ (s i (projFirst p (m + 1) u₀)) (s j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  have hp₀S3 : p₀ ∈ (bandS3 Z S).set := by rw [hp₀def]; exact hp₀
  obtain ⟨hz1, -, -, -, -, -, -, -, hpv2, hpv2'⟩ := (bandS3_mem_iff Z S p₀).mp hp₀S3
  have hu₀Z : u₀ ∈ Z.set := by
    have h := hz1
    rwa [hp₀def, bandZ1_bandPt] at h
  -- the level functions are continuous on the base component
  have hsi : ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ => s i (projFirst p (m + 1) u))
      (bandZc Z u₀) :=
    (hcont i).comp (continuous_projFirst p (m + 1)).continuousOn
      (fun u hu => by rw [hC]; exact ⟨u, hu, rfl⟩)
  have hsj : ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ => s j (projFirst p (m + 1) u))
      (bandZc Z u₀) :=
    (hcont j).comp (continuous_projFirst p (m + 1)).continuousOn
      (fun u hu => by rw [hC]; exact ⟨u, hu, rfl⟩)
  have ha : ContinuousOn (bandLevel s i) (bandZc Z u₀) := by
    change ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      ((s i (projFirst p (m + 1) u)) (Fin.last m) : EReal)) (bandZc Z u₀)
    exact continuous_coe_real_ereal.comp_continuousOn
      ((continuous_apply (Fin.last m)).comp_continuousOn hsi)
  have hb : ContinuousOn (bandLevel s j) (bandZc Z u₀) := by
    change ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      ((s j (projFirst p (m + 1) u)) (Fin.last m) : EReal)) (bandZc Z u₀)
    exact continuous_coe_real_ereal.comp_continuousOn
      ((continuous_apply (Fin.last m)).comp_continuousOn hsj)
  have hab : ∀ u ∈ bandZc Z u₀, bandLevel s i u < bandLevel s j u := by
    intro u hu
    change ((s i (projFirst p (m + 1) u)) (Fin.last m) : EReal) <
      ((s j (projFirst p (m + 1) u)) (Fin.last m) : EReal)
    exact EReal.coe_lt_coe_iff.mpr
      (hlvl (projFirst p (m + 1) u) (by rw [hC]; exact ⟨u, hu, rfl⟩))
  have hHpc : IsPreconnected (bandH Z s i j u₀) := by
    rw [bandH]
    exact band_preconn isPreconnected_connectedComponentIn ha hb hab
  -- the base point of the component lies in `H`
  have hLu₀ : bandLevel s i u₀ < (t₀ : EReal) := by
    have h := hpv2
    rw [hp₀def, bandV2_bandPt, bandT_bandPt] at h
    change ((s i (projFirst p (m + 1) u₀)) (Fin.last m) : EReal) < (t₀ : EReal)
    exact EReal.coe_lt_coe_iff.mpr h
  have hLu₀' : (t₀ : EReal) < bandLevel s j u₀ := by
    have h := hpv2'
    rw [hp₀def, bandV2'_bandPt, bandT_bandPt] at h
    change (t₀ : EReal) < ((s j (projFirst p (m + 1) u₀)) (Fin.last m) : EReal)
    exact EReal.coe_lt_coe_iff.mpr h
  have hHbase : ((u₀, t₀) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ bandH Z s i j u₀ := by
    rw [bandH]
    exact ⟨mem_connectedComponentIn hu₀Z, hLu₀, hLu₀'⟩
  -- every parametrised point lies in the set
  have hF : ∀ q ∈ bandH Z s i j u₀, bandPhi s i j q ∈ (bandS3 Z S).set := by
    intro q hq
    rw [bandH] at hq
    obtain ⟨hqc, hqa, hqb⟩ := hq
    simp only [bandLevel] at hqa hqb
    have hπc : projFirst p (m + 1) q.1 ∈ C := by rw [hC]; exact ⟨q.1, hqc, rfl⟩
    have hsub_i := hsub i _ hπc
    have hsub_j := hsub j _ hπc
    have hbi : |(s i (projFirst p (m + 1) q.1)) (Fin.last m)| ≤ 1 := by
      have h := hsub_i.1 (Fin.natAdd p (Fin.last m))
      rwa [Fin.append_right] at h
    have hbj : |(s j (projFirst p (m + 1) q.1)) (Fin.last m)| ≤ 1 := by
      have h := hsub_j.1 (Fin.natAdd p (Fin.last m))
      rwa [Fin.append_right] at h
    have hqa' : (s i (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 := EReal.coe_lt_coe_iff.mp hqa
    have hqb' : q.2 < (s j (projFirst p (m + 1) q.1)) (Fin.last m) := EReal.coe_lt_coe_iff.mp hqb
    have hcube : |q.2| ≤ 1 := by
      have h1' : -1 ≤ (s i (projFirst p (m + 1) q.1)) (Fin.last m) := (abs_le.mp hbi).1
      have h2' : (s j (projFirst p (m + 1) q.1)) (Fin.last m) ≤ 1 := (abs_le.mp hbj).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact bandPt_mem Z S q.1 (connectedComponentIn_subset Z.set u₀ hqc) _ _ q.2
      hsub_i hsub_j hcube hqa' hqb'
  -- pick a point of the base component over `Fin.init y`
  obtain ⟨u, huZc, hux⟩ : ∃ u ∈ bandZc Z u₀, projFirst p (m + 1) u = Fin.init y := by
    rw [hC] at hy
    exact hy
  set q : (Fin (p + (m + 1)) → ℝ) × ℝ := (u, y (Fin.last p)) with hqdef
  have hqH : q ∈ bandH Z s i j u₀ := by
    rw [bandH]
    refine ⟨?_, ?_, ?_⟩
    · show u ∈ bandZc Z u₀
      exact huZc
    · show bandLevel s i u < (y (Fin.last p) : EReal)
      simp only [bandLevel, hux]
      exact EReal.coe_lt_coe_iff.mpr h1
    · show (y (Fin.last p) : EReal) < bandLevel s j u
      simp only [bandLevel, hux]
      exact EReal.coe_lt_coe_iff.mpr h2
  have hcomp : bandPhi s i j q ∈ connectedComponentIn (bandS3 Z S).set
      (bandPhi s i j (u₀, t₀)) :=
    imageSubsetConnectedComponentIn hHpc (continuousOn_bandPhi u₀ hcont hC i j)
      hHbase hF q hqH
  refine ⟨bandPhi s i j q, ?_, ?_⟩
  · exact hcomp
  · have hz1 : bandZ1 (bandPhi s i j q) = q.1 :=
      bandZ1_bandPt q.1 (s i (projFirst p (m + 1) q.1)) (s j (projFirst p (m + 1) q.1)) q.2
    have hzt : bandT (bandPhi s i j q) = q.2 :=
      bandT_bandPt q.1 (s i (projFirst p (m + 1) q.1)) (s j (projFirst p (m + 1) q.1)) q.2
    rw [bandExtract_eq_snoc, hz1, hzt, hqdef]
    rw [hux]
    exact Fin.snoc_init_self y

end Work.WilE7.BandAux
