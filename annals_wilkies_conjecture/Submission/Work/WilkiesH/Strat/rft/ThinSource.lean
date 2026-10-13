import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Dim.dimLE_mono
import Submission.Work.WilkiesH.Strat.BadCell
import Submission.Work.WilkiesH.Strat.cellData
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilkiesH.Strat.rft.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilkiesH.Strat
open WilkiesDesign WilkiesConjecture
open Work.WilG5
variable {S : WilkiesDesign.SOMin}

/-! ## 6. The thin-source step of the dimension theorem -/

/-- **Thin source step.**  If the source of a graph is thin, the image is one dimension lower. -/
theorem thin_source (hcd : S.SharpCD) (m : ℕ)
    (ih : ∀ m' < m, ∀ (t : ℕ) (G : Set (Fin (m' + t) → ℝ)) (F D : ℕ),
      G ∈ S.Ω F D (m' + t) → GraphOver m' G → WilkiesDesign.DimLE (lastN t G) m') :
    ∀ (t : ℕ) (G : Set (Fin (m + t) → ℝ)) (F D : ℕ), G ∈ S.Ω F D (m + t) →
      GraphOver m G → interior (projN t G) = ∅ → WilkiesDesign.DimLE (lastN t G) (m - 1) := by
  intro t G F D hG hgr hint
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: the source is a subset of a point, so it is empty and `G` is empty
    subst hm
    have hsrc : projN t G = (∅ : Set (Fin 0 → ℝ)) := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hsub : (Set.univ : Set (Fin 0 → ℝ)) ⊆ projN t G := by
        intro y _
        have hyx : y = x := Subsingleton.elim _ _
        rwa [hyx]
      have hne : (interior (projN t G)).Nonempty :=
        ⟨x, interior_mono hsub (by rw [interior_univ]; exact Set.mem_univ x)⟩
      rw [hint] at hne
      exact Set.not_nonempty_empty hne
    have hGempty : G = (∅ : Set (Fin (0 + t) → ℝ)) := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hz' : (fun i : Fin 0 => z (Fin.castAdd t i)) ∈ projN t G :=
        ⟨fun j => z (Fin.natAdd 0 j), by
          have hpt : Fin.append (fun i : Fin 0 => z (Fin.castAdd t i))
              (fun j => z (Fin.natAdd 0 j)) = z := by
            funext i
            rcases Nat.lt_or_ge i.val 0 with h | h
            · omega
            · have hi : i = Fin.natAdd 0 ⟨i.val - 0, by have := i.isLt; omega⟩ := by
                apply Fin.ext
                show i.val = 0 + (i.val - 0)
                omega
              rw [hi, Fin.append_right]
          rwa [hpt]⟩
      rw [hsrc] at hz'
      exact hz'
    rw [hGempty]
    have hempty : lastN t (∅ : Set (Fin (0 + t) → ℝ)) = (∅ : Set (Fin t → ℝ)) := by
      ext y
      rw [mem_lastN']
      simp
    intro ee
    rw [hempty, Set.image_empty, interior_empty]
  · -- `m ≥ 1`
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    set A : Set (Fin (m' + 1) → ℝ) := projN t G with hA
    have hAmem : A ∈ S.Ω (F + t) D (m' + 1) := projN_mem t F D hG
    obtain ⟨a, b, c, H⟩ := hcd (F + t) (m' + 1)
    obtain ⟨CD, hCD, hcomp, hcard, hCDmem⟩ := H D 1 (fun _ : Fin 1 => A) (fun _ => hAmem)
    -- the cells which lie in `A`
    set J : Finset (Set (Fin (m' + 1) → ℝ)) := CD.filter (fun κ => κ ⊆ A) with hJ
    let e : Fin J.card → Set (Fin (m' + 1) → ℝ) :=
      fun i => ((Finset.equivFin J).symm i : ↥J).1
    have he_mem : ∀ i, e i ∈ J := fun i => ((Finset.equivFin J).symm i).2
    have he_surj : ∀ κ ∈ J, ∃ i, e i = κ := by
      intro κ hκ
      exact ⟨Finset.equivFin J ⟨κ, hκ⟩, by simp [e]⟩
    have he_cd : ∀ i, e i ∈ CD := fun i => (Finset.mem_filter.mp (he_mem i)).1
    have he_sub : ∀ i, e i ⊆ A := fun i => (Finset.mem_filter.mp (he_mem i)).2
    have hcover : A = ⋃ i, e i := by
      refine Set.Subset.antisymm ?_ (Set.iUnion_subset he_sub)
      intro x hxA
      obtain ⟨κ, hκCD, hxκ⟩ := hCD.2.2.1 x
      have hκA : κ ⊆ A := by
        rcases hcomp 0 κ hκCD with h | h
        · simpa using h
        · exact absurd hxκ (fun hxκ => Set.disjoint_left.mp h hxκ hxA)
      obtain ⟨i, hi⟩ := he_surj κ (Finset.mem_filter.mpr ⟨hκCD, hκA⟩)
      exact Set.mem_iUnion.mpr ⟨i, hi ▸ hxκ⟩
    -- each cell's image is `DimLE ≤ m'`
    have hterm : ∀ i, WilkiesDesign.DimLE (lastN t (G ∩ liftFirst t (e i))) (m' + 1 - 1) := by
      intro i
      set κ : Set (Fin (m' + 1) → ℝ) := e i with hκ
      have hκCD : κ ∈ CD := he_cd i
      have hκcell : WilkiesDesign.IsCell (m' + 1) κ := (hCD.1 κ hκCD).1
      have hκthin : interior κ = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro y hy
        exact (hint ▸ interior_mono (he_sub i) hy : y ∈ (∅ : Set (Fin (m' + 1) → ℝ)))
      obtain ⟨k, ee, Φ, hcellDim, hsec, hk_le, hkfull⟩ := cellData hκcell
      have hk_small : k ≤ m' := by
        rcases lt_or_eq_of_le hk_le with h | h
        · omega
        · exfalso
          exact Set.not_nonempty_empty (by rw [← hκthin]; exact hkfull h)
      -- transport the graph to the free coordinates of the cell
      set H : Set (Fin (k + t) → ℝ) := coordImage (thinIdx ee) (G ∩ liftFirst t κ) with hH
      have hHmem : H ∈ S.Ω (F + 64 * ((m' + 1 + t) + (k + t)) + 64 + max F (a + t) + 1)
          (D + c.eval D + 32 * ((m' + 1 + t) + (k + t)) + 32) (k + t) := by
        have hlift : liftFirst t κ ∈ S.Ω (a + t) (c.eval D) (m' + 1 + t) :=
          liftFirst_mem t a (c.eval D) (hCDmem κ hκCD)
        have hinter := inter_two_mem (S := S) hG hlift
        exact mem_mono (coordImage_mem (S := S) (ι := thinIdx ee) hinter) _ _ (by omega) (by omega)
      have hHgr : GraphOver k H := by
        intro z hz z' hz' h
        rw [hH, mem_coordImage'] at hz hz'
        obtain ⟨w, hw, hwz⟩ := hz
        obtain ⟨w', hw', hw'z⟩ := hz'
        have hsecwf : ∀ i : Fin k, w (Fin.castAdd t (ee i)) = w' (Fin.castAdd t (ee i)) := by
          intro i
          have h1 : w (Fin.castAdd t (ee i)) = z (Fin.castAdd t i) := by
            have hh := congrFun hwz (Fin.castAdd t i)
            rw [Function.comp_apply, thinIdx_castAdd] at hh
            exact hh
          have h2 : w' (Fin.castAdd t (ee i)) = z' (Fin.castAdd t i) := by
            have hh := congrFun hw'z (Fin.castAdd t i)
            rw [Function.comp_apply, thinIdx_castAdd] at hh
            exact hh
          rw [h1, h2]
          exact h i
        have hsrc : (fun i' : Fin (m' + 1) => w (Fin.castAdd t i')) =
            (fun i' : Fin (m' + 1) => w' (Fin.castAdd t i')) := by
          have h1 := hsec (fun i' : Fin (m' + 1) => w (Fin.castAdd t i')) hw.2
          have h2 := hsec (fun i' : Fin (m' + 1) => w' (Fin.castAdd t i')) hw'.2
          have hfun : (fun i' : Fin (m' + 1) => w (Fin.castAdd t i')) ∘ ee =
              (fun i' : Fin (m' + 1) => w' (Fin.castAdd t i')) ∘ ee := by
            funext i
            exact hsecwf i
          rw [← h1, ← h2, hfun]
        have hww : w = w' := hgr w hw.1 w' hw'.1 (fun i => congrFun hsrc i)
        rw [← hwz, ← hw'z, hww]
      have hHlast : lastN t H = lastN t (G ∩ liftFirst t κ) := by
        ext y
        constructor
        · rintro ⟨u, hu⟩
          rw [hH, mem_coordImage'] at hu
          obtain ⟨w, hw, hwu⟩ := hu
          refine ⟨fun i : Fin (m' + 1) => w (Fin.castAdd t i), ?_⟩
          have hw' : Fin.append (fun i : Fin (m' + 1) => w (Fin.castAdd t i)) y = w := by
            apply eq_of_castAdd_natAdd
            · intro i
              rw [append_castAdd]
            · intro j
              have h1 : w (Fin.natAdd (m' + 1) j) = (Fin.append u y) (Fin.natAdd k j) := by
                rw [← hwu, Function.comp_apply, thinIdx_natAdd]
              rw [append_natAdd, h1, append_natAdd]
          rw [hw']
          exact hw
        · rintro ⟨x, hx⟩
          refine ⟨fun i : Fin k => x (ee i), ?_⟩
          rw [hH, mem_coordImage']
          refine ⟨Fin.append x y, hx, ?_⟩
          funext i
          rcases Nat.lt_or_ge i.val k with hlt | hge
          · have hi : i = Fin.castAdd t ⟨i.val, hlt⟩ := Fin.ext rfl
            rw [hi]
            show Fin.append x y (thinIdx ee (Fin.castAdd t ⟨i.val, hlt⟩)) =
              (Fin.append (fun i => x (ee i)) y) (Fin.castAdd t ⟨i.val, hlt⟩)
            rw [thinIdx_castAdd, Fin.append_left, Fin.append_left]
          · have hi : i = Fin.natAdd k ⟨i.val - k, by have := i.isLt; omega⟩ := by
              apply Fin.ext
              show i.val = k + (i.val - k)
              omega
            rw [hi]
            show Fin.append x y (thinIdx ee (Fin.natAdd k ⟨i.val - k, by have := i.isLt; omega⟩)) =
              (Fin.append (fun i => x (ee i)) y) (Fin.natAdd k ⟨i.val - k, by have := i.isLt; omega⟩)
            rw [thinIdx_natAdd, Fin.append_right, Fin.append_right]
      exact Work.WilkiesH.Dim.dimLE_mono (hHlast ▸ ih k (by omega) t H _ _ hHmem hHgr) hk_small
    -- combine, with `Ω`-bounds uniform in the cell
    obtain ⟨F₀, D₀, hF₀⟩ : ∃ F₀ D₀ : ℕ, ∀ i, lastN t (G ∩ liftFirst t (e i)) ∈ S.Ω F₀ D₀ t := by
      refine ⟨F + 64 * ((m' + 1 + t) + (m' + 1 + t)) + 64 + max F (a + t) + 1 + (m' + 1),
        D + c.eval D + 32 * ((m' + 1 + t) + (m' + 1 + t)) + 32 + (m' + 1), fun i => ?_⟩
      obtain ⟨k, ee, Φ, hcellDim, hsec, hk_le, hkfull⟩ := cellData (hCD.1 (e i) (he_cd i)).1
      have hk_small : k ≤ m' := by
        rcases lt_or_eq_of_le hk_le with h | h
        · omega
        · exfalso
          have hκthin : interior (e i) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro y hy
            exact (hint ▸ interior_mono (he_sub i) hy : y ∈ (∅ : Set (Fin (m' + 1) → ℝ)))
          exact Set.not_nonempty_empty (by rw [← hκthin]; exact hkfull h)
      have hlift : liftFirst t (e i) ∈ S.Ω (a + t) (c.eval D) (m' + 1 + t) :=
        liftFirst_mem t a (c.eval D) (hCDmem (e i) (he_cd i))
      have hinter := inter_two_mem (S := S) hG hlift
      exact mem_mono (lastN_mem t (max F (a + t) + 1) (D + c.eval D) hinter) _ _ (by omega) (by omega)
    have hunion : WilkiesDesign.DimLE (⋃ i, lastN t (G ∩ liftFirst t (e i))) (m' + 1 - 1) :=
      dimLE_iUnion_fin (S := S) hcd (F := F₀) (D := D₀)
        (A := fun i => lastN t (G ∩ liftFirst t (e i))) hF₀ hterm
    have hlast_eq : lastN t G = ⋃ i, lastN t (G ∩ liftFirst t (e i)) := by
      refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun i => ?_)
      · rintro y ⟨x, hx⟩
        have hxA : x ∈ A := ⟨y, hx⟩
        rw [hcover] at hxA
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxA
        refine Set.mem_iUnion.mpr ⟨i, ⟨x, hx, ?_⟩⟩
        rw [mem_liftFirst']
        rwa [funext (fun i' : Fin (m' + 1) => Fin.append_left x y i')]
      · rintro y ⟨x, hx, -⟩
        exact ⟨x, hx⟩
    rw [hlast_eq]
    exact hunion


end Work.WilkiesH.Strat
