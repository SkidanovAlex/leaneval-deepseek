/-
  The two inclusions computing the projection of the non-strict level-fibre set.

  * `lf3_proj_subset`: a point of the projection gives the witnesses of `lfY3`;
  * `lf3_proj_supset`: conversely, the witnesses of `lfY3` build a point of the projection;
  * `nonstrictLevel_subPf`: the projection is `lfY3`, hence `SubPf`.

  NOTE (session notes): this file is the development copy; the live version is
  `Submission/Work/WilE7/SheetData/NonstrictLevelIncl.lean` (same content).
-/
import Mathlib
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre
import Submission.Work.WilE7.SheetData.lf3_mem_W3
import Submission.Work.WilE7.SheetData.lf3DistAtom_eval_pos
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.LevelFibre.lfE_xIdx
import Submission.Work.WilE7.LevelFibre.lfE_lvIdx

set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators
namespace Work.WilE7.SheetData
open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.LevelFibre

variable {p q M k : ℕ}

/-- A point of a semi-Pfaffian set lies in the cube. -/
theorem mem_cubeC_of_mem_set {n : ℕ} (X : SemiPf n) {x : Fin n → ℝ} (h : x ∈ X.set) :
    x ∈ cubeC n :=
  (show x ∈ cubeC n ∧ ∃ B ∈ X.basics, B.holds X.c x from h).1

/-! ## §1. Coordinate identities for the block layout -/

theorem lf3XpIdx_castAdd (l : Fin k) (a : Fin p) :
    lf3XpIdx (p := p) (q := q) (M := M) l (Fin.castAdd q a) =
      lf3BIdx (p := p) (q := q) (M := M) l (Fin.castAdd (q + 1) a) := by
  apply congrArg (lfBIdx (p := p) (q := q + 1) (M := M) l)
  apply Fin.ext
  simp [lfXc, Fin.castAdd]

theorem lf3XpIdx_natAdd (l : Fin k) (j : Fin q) :
    lf3XpIdx (p := p) (q := q) (M := M) l (Fin.natAdd p j) =
      lf3LvIdx (p := p) (q := q) (M := M) j l := by
  apply congrArg (lfBIdx (p := p) (q := q + 1) (M := M) l)
  apply Fin.ext
  simp [lfXc, lfLvc, Fin.natAdd, Fin.castSucc]

theorem lf3XpIdx_slk (l : Fin k) :
    lf3SlkIdx (p := p) (q := q) (M := M) l =
      lf3BIdx (p := p) (q := q) (M := M) l (Fin.natAdd p (Fin.last q)) := rfl

/-! ## §2. A function on `Fin k` that is non-decreasing at consecutive indices -/

theorem monotone_of_adj_succ {α : Type*} [LinearOrder α] {k : ℕ} {f : Fin k → α}
    (h : ∀ (l : Fin k) (hl : l.val + 1 < k), f l ≤ f ⟨l.val + 1, hl⟩) : Monotone f := by
  intro a b hab
  obtain ⟨d, hd⟩ : ∃ d, b.val = a.val + d := ⟨b.val - a.val, by omega⟩
  have key : ∀ d (hd : a.val + d < k), f a ≤ f (⟨a.val + d, hd⟩ : Fin k) := by
    intro d
    induction d with
    | zero =>
      intro hd
      have he : (⟨a.val + 0, hd⟩ : Fin k) = a := Fin.ext (by simp)
      rw [he]
    | succ d ih =>
      intro hd
      have hd' : a.val + d < k := by omega
      have hstep : f (⟨a.val + d, hd'⟩ : Fin k) ≤ f ⟨a.val + (d + 1), hd⟩ := by
        have h1 := h ⟨a.val + d, hd'⟩ (by omega)
        have he : (⟨(⟨a.val + d, hd'⟩ : Fin k).val + 1, by omega⟩ : Fin k) =
            (⟨a.val + (d + 1), hd⟩ : Fin k) := rfl
        rwa [he] at h1
      exact le_trans (ih hd') hstep
  have hb : (⟨a.val + d, by rw [← hd]; exact b.isLt⟩ : Fin k) = b := Fin.ext hd.symm
  rw [← hb]
  exact key d _

/-! ## §3. The two inclusions -/

theorem lf3_proj_subset (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M))
    (e : Fin (lfD p (q + 1) M k) ≃ Fin ((p + 1) + lfM p (q + 1) M k))
    (hx : ∀ a : Fin p, e (lf3XIdx (q := q) (M := M) (k := k) a) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc a))
    (ht : e (lf3LvIdx (p := p) (q := q) (M := M) j i) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.last p)) :
    projFirst (p + 1) (lfM p (q + 1) M k) '' (SemiPf.reindex e (lfW3 j X XC)).set ⊆
      lfY3 (p := p) (q := q) (M := M) (k := k) j i X XC := by
  rintro y ⟨Z, hZ, hZy⟩
  set U : Fin (lfD p (q + 1) M k) → ℝ := fun d => Z (e d) with hUdef
  have hU : U ∈ (lfW3 j X XC).set := by
    rw [Work.WilE7.reindex_set] at hZ
    exact hZ
  obtain ⟨hXC, hblkX, hblkC, hbase, hslack, hdist⟩ := (lf3_mem_W3 j X XC U).mp hU
  have hcubeU : U ∈ cubeC (lfD p (q + 1) M k) := mem_cubeC_of_mem_set (lfW3 j X XC) hU
  -- the two projected coordinates
  have hZa : ∀ a : Fin p, Z (Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc a)) =
      y (Fin.castSucc a) := fun a => congrFun hZy (Fin.castSucc a)
  have hZt : Z (Fin.castAdd (lfM p (q + 1) M k) (Fin.last p)) = y (Fin.last p) :=
    congrFun hZy (Fin.last p)
  have hUx : ∀ a : Fin p, U (lf3XIdx (q := q) (M := M) (k := k) a) = Fin.init y a := by
    intro a
    rw [hUdef]
    show Z (e (lf3XIdx (q := q) (M := M) (k := k) a)) = Fin.init y a
    rw [hx a]
    exact hZa a
  have hUt : U (lf3LvIdx (p := p) (q := q) (M := M) j i) = y (Fin.last p) := by
    rw [hUdef]
    show Z (e (lf3LvIdx (p := p) (q := q) (M := M) j i)) = y (Fin.last p)
    rw [ht]
    exact hZt
  refine ⟨?_, fun l c => U (lf3XpIdx (p := p) (q := q) (M := M) l c), ?_, ?_, ?_, ?_, ?_⟩
  · -- the `C`-witness
    refine ⟨fun t => U (lf3WIdx (q := q) (M := M) (k := k) t), ?_⟩
    have key : Fin.append (Fin.init y) (fun t => U (lf3WIdx (q := q) (M := M) (k := k) t)) =
        projFirst (p + M) ((p + (q + 1)) * k) U := by
      funext c
      refine Fin.addCases (fun a => ?_) (fun t => ?_) c
      · show Fin.append (Fin.init y) (fun t => U (lf3WIdx (q := q) (M := M) (k := k) t))
          (Fin.castAdd M a) = U (Fin.castAdd ((p + (q + 1)) * k) (Fin.castAdd M a))
        rw [Fin.append_left]
        exact (hUx a).symm
      · show Fin.append (Fin.init y) (fun t => U (lf3WIdx (q := q) (M := M) (k := k) t))
          (Fin.natAdd p t) = U (Fin.castAdd ((p + (q + 1)) * k) (Fin.natAdd p t))
        rw [Fin.append_right]
        rfl
    rw [key]
    exact hXC
  · -- the fibre points lie in `X.set`
    intro l
    change (fun c : Fin (p + q) => U (lf3XpIdx (p := p) (q := q) (M := M) l c)) ∈ X.set
    have he : (fun c : Fin (p + q) => U (lf3XpIdx (p := p) (q := q) (M := M) l c)) =
        projFirst (p + q) 1 (blk (projSnd (p + M) ((p + (q + 1)) * k) U) l) :=
      funext fun c => rfl
    rw [he]
    exact hblkX l
  · -- the base coordinates
    intro l
    funext a
    show U (lf3XpIdx (p := p) (q := q) (M := M) l (Fin.castAdd q a)) = Fin.init y a
    rw [lf3XpIdx_castAdd, hbase l a, hUx a]
  · -- the levels are non-decreasing
    intro l l' hll
    have hlev : ∀ l : Fin k, U (lf3XpIdx (p := p) (q := q) (M := M) l (Fin.natAdd p j)) =
        U (lf3LvIdx (p := p) (q := q) (M := M) j l) :=
      fun l => congrArg U (lf3XpIdx_natAdd l j)
    change U (lf3XpIdx (p := p) (q := q) (M := M) l (Fin.natAdd p j)) ≤
      U (lf3XpIdx (p := p) (q := q) (M := M) l' (Fin.natAdd p j))
    rw [hlev l, hlev l']
    have hmono : Monotone (fun l : Fin k =>
        U (lf3LvIdx (p := p) (q := q) (M := M) j l)) := by
      refine monotone_of_adj_succ ?_
      intro l hl
      have h0 := hslack (⟨l.val, by omega⟩ : Fin (k - 1))
      have hb := hcubeU (lf3SlkIdx (p := p) (q := q) (M := M) l)
      rw [abs_le] at hb
      have hsub : U (lf3LvIdx (p := p) (q := q) (M := M) j l) ≤
          U (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val + 1, hl⟩) := by
        have h0' : U (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val + 1, hl⟩) -
            U (lf3LvIdx (p := p) (q := q) (M := M) j l) - 1 -
            U (lf3SlkIdx (p := p) (q := q) (M := M) l) = 0 := by
          have h := h0
          simpa only [Fin.val_mk] using h
        linarith [h0', hb.1]
      exact hsub
    exact hmono (le_of_lt hll)
  · -- pairwise distinct
    intro l l' hne
    exact (lf3DistAtom_eval_pos U).mp hdist l l' hne
  · -- the pinned level
    show U (lf3XpIdx (p := p) (q := q) (M := M) i (Fin.natAdd p j)) = y (Fin.last p)
    rw [lf3XpIdx_natAdd]
    exact hUt

theorem lf3_proj_supset (j : Fin q) (i : Fin k)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M))
    (e : Fin (lfD p (q + 1) M k) ≃ Fin ((p + 1) + lfM p (q + 1) M k))
    (hx : ∀ a : Fin p, e (lf3XIdx (q := q) (M := M) (k := k) a) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc a))
    (ht : e (lf3LvIdx (p := p) (q := q) (M := M) j i) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.last p)) :
    lfY3 (p := p) (q := q) (M := M) (k := k) j i X XC ⊆
      projFirst (p + 1) (lfM p (q + 1) M k) '' (SemiPf.reindex e (lfW3 j X XC)).set := by
  intro y hy
  obtain ⟨⟨w, hw⟩, z, hzX, hzproj, hzmono, hzdist, hzpin⟩ := hy
  have hN : 0 < p + (q + 1) := by omega
  -- the block functions
  set slk : Fin k → ℝ := fun l =>
    if h : l.val + 1 < k then z ⟨l.val + 1, h⟩ (Fin.natAdd p j) - z l (Fin.natAdd p j) - 1
    else 0 with hslkdef
  set Zb : Fin k → (Fin (p + (q + 1)) → ℝ) := fun l c =>
    if h : c.val < p + q then z l ⟨c.val, h⟩ else slk l with hZbdef
  set U : Fin (lfD p (q + 1) M k) → ℝ :=
    Fin.append (Fin.append (fun a : Fin p => Fin.init y a) w)
      (lfFlat (p := p) (q := q + 1) (k := k) hN Zb) with hUdef
  -- coordinate facts
  have hUw : ∀ t : Fin M, U (lf3WIdx (q := q) (M := M) (k := k) t) = w t := by
    intro t
    rw [hUdef]
    show Fin.append (Fin.append (fun a : Fin p => Fin.init y a) w)
        (lfFlat (p := p) (q := q + 1) (k := k) hN Zb)
        (Fin.castAdd ((p + (q + 1)) * k) (Fin.natAdd p t)) = w t
    rw [Fin.append_left, Fin.append_right]
  have hUx : ∀ a : Fin p, U (lf3XIdx (q := q) (M := M) (k := k) a) = Fin.init y a := by
    intro a
    rw [hUdef]
    show Fin.append (Fin.append (fun a : Fin p => Fin.init y a) w)
        (lfFlat (p := p) (q := q + 1) (k := k) hN Zb)
        (Fin.castAdd ((p + (q + 1)) * k) (Fin.castAdd M a)) = Fin.init y a
    rw [Fin.append_left, Fin.append_left]
  have hUXC : projFirst (p + M) ((p + (q + 1)) * k) U = Fin.append (Fin.init y) w := by
    rw [hUdef]
    exact Work.WilE7.projFirst_append _ _
  have hUb : ∀ (l : Fin k) (c : Fin (p + (q + 1))),
      U (lf3BIdx (p := p) (q := q) (M := M) l c) = Zb l c := by
    intro l c
    rw [hUdef]
    show Fin.append (Fin.append (fun a : Fin p => Fin.init y a) w)
        (lfFlat (p := p) (q := q + 1) (k := k) hN Zb)
        (Fin.natAdd (p + M) (blkIdx (p + (q + 1)) k l c)) = Zb l c
    rw [Fin.append_right]
    exact lfFlat_blkIdx hN Zb l c
  have hUz : ∀ (l : Fin k) (c : Fin (p + q)),
      U (lf3XpIdx (p := p) (q := q) (M := M) l c) = z l c := by
    intro l c
    have h1 : lf3XpIdx (p := p) (q := q) (M := M) l c =
        lf3BIdx (p := p) (q := q) (M := M) l (lfXc c) := rfl
    rw [h1, hUb]
    have hle : (lfXc (p := p) (q := q) c).val < p + q := c.isLt
    simp only [hZbdef, dif_pos hle]
    congr 1
  have hUslk : ∀ l : Fin k, U (lf3SlkIdx (p := p) (q := q) (M := M) l) = slk l := by
    intro l
    have h1 : lf3SlkIdx (p := p) (q := q) (M := M) l =
        lf3BIdx (p := p) (q := q) (M := M) l (lfSlkc (p := p) (q := q)) := rfl
    rw [h1, hUb]
    have hge : ¬ (lfSlkc (p := p) (q := q)).val < p + q := by
      simp [lfSlkc, Fin.natAdd, Fin.last]
    simp only [hZbdef, dif_neg hge]
  have hUlv : ∀ l : Fin k, U (lf3LvIdx (p := p) (q := q) (M := M) j l) =
      z l (Fin.natAdd p j) := by
    intro l
    have h1 : lf3LvIdx (p := p) (q := q) (M := M) j l =
        lf3BIdx (p := p) (q := q) (M := M) l (lfLvc j) := rfl
    rw [h1, hUb]
    have hle : (lfLvc (p := p) (q := q) j).val < p + q := by
      simp [lfLvc, Fin.natAdd, Fin.castSucc]
    simp only [hZbdef, dif_pos hle]
    congr 1
  -- the point set conditions
  have hmem : U ∈ (lfW3 j X XC).set := by
    refine (lf3_mem_W3 j X XC U).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hUXC]; exact hw
    · intro l
      have he : projFirst (p + q) 1 (blk (projSnd (p + M) ((p + (q + 1)) * k) U) l) =
          (fun c : Fin (p + q) => U (lf3XpIdx (p := p) (q := q) (M := M) l c)) :=
        funext fun c => rfl
      rw [he, show (fun c : Fin (p + q) => U (lf3XpIdx (p := p) (q := q) (M := M) l c)) = z l
        from funext (hUz l)]
      exact hzX l
    · intro l
      have he : projSnd (p + q) 1 (blk (projSnd (p + M) ((p + (q + 1)) * k) U) l) =
          (fun _ : Fin 1 => U (lf3SlkIdx (p := p) (q := q) (M := M) l)) := by
        funext c
        have hc : c = 0 := Subsingleton.elim c 0
        rw [hc]
        rfl
      rw [he, hUslk]
      intro c
      fin_cases c
      simp only [cubeC, Set.mem_setOf_eq]
      by_cases h : l.val + 1 < k
      · have hz1 := hzX ⟨l.val + 1, h⟩
        have hz2 := hzX l
        have hb1 : |z ⟨l.val + 1, h⟩ (Fin.natAdd p j)| ≤ 1 :=
          mem_cubeC_of_mem_set X hz1 (Fin.natAdd p j)
        have hb2 : |z l (Fin.natAdd p j)| ≤ 1 := mem_cubeC_of_mem_set X hz2 (Fin.natAdd p j)
        have hml : z l (Fin.natAdd p j) ≤ z ⟨l.val + 1, h⟩ (Fin.natAdd p j) :=
          hzmono l ⟨l.val + 1, h⟩ (by simp [Fin.lt_def])
        simp only [hslkdef, dif_pos h]
        rw [abs_le] at hb1 hb2 ⊢
        constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hml]
      · simp only [hslkdef, dif_neg h]
        norm_num
    · intro l a
      show U (lf3BIdx (p := p) (q := q) (M := M) l (Fin.castAdd (q + 1) a)) =
        U (lf3XIdx (q := q) (M := M) (k := k) a)
      rw [hUb, hUx]
      have hle : (Fin.castAdd (q + 1) a : Fin (p + (q + 1))).val < p + q := by
        simp [Fin.castAdd]; omega
      simp only [hZbdef, dite_eq_left hle]
      have hconv : z l ⟨(Fin.castAdd (q + 1) a : Fin (p + (q + 1))).val, hle⟩ =
          z l (Fin.castAdd q a) := rfl
      rw [hconv]
      exact congrFun (hzproj l) a
    · intro l
      have h0 : U (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val + 1, by omega⟩) -
          U (lf3LvIdx (p := p) (q := q) (M := M) j ⟨l.val, by omega⟩) - 1 -
          U (lf3SlkIdx (p := p) (q := q) (M := M) ⟨l.val, by omega⟩) = 0 := by
        rw [hUlv, hUlv, hUslk]
        have h : (⟨l.val, by omega⟩ : Fin k).val + 1 < k := by
          simp only [Fin.val_mk]; omega
        simp only [hslkdef, dif_pos h]
        ring
      exact h0
    · rw [lf3DistAtom_eval_pos]
      intro l l' hne
      rw [funext (hUz l), funext (hUz l')]
      exact hzdist l l' hne
  -- assemble the reindexed point
  refine ⟨fun a => U (e.symm a), ?_, ?_⟩
  · rw [Work.WilE7.reindex_set]
    show (fun i => U (e.symm (e i))) ∈ (lfW3 j X XC).set
    have hfun : (fun i => U (e.symm (e i))) = U := by
      funext i
      rw [Equiv.symm_apply_apply]
    rw [hfun]
    exact hmem
  · funext b
    rcases Fin.eq_castSucc_or_eq_last b with ⟨ā, rfl⟩ | rfl
    · show U (e.symm (Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc ā))) = y (Fin.castSucc ā)
      have hs : e.symm (Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc ā)) =
          lf3XIdx (q := q) (M := M) (k := k) ā := by
        rw [Equiv.symm_apply_eq, hx ā]
      rw [hs, hUx]
      rfl
    · show U (e.symm (Fin.castAdd (lfM p (q + 1) M k) (Fin.last p))) = y (Fin.last p)
      have hs : e.symm (Fin.castAdd (lfM p (q + 1) M k) (Fin.last p)) =
          lf3LvIdx (p := p) (q := q) (M := M) j i := by
        rw [Equiv.symm_apply_eq, ht]
      rw [hs, hUlv, hzpin]

/-! ## §4. The theorem -/

theorem nonstrictLevel_subPf (i : Fin k) (j : Fin q)
    (X : SemiPf (p + q)) (XC : SemiPf (p + M)) :
    SubPf (p + 1) (lfY3 (p := p) (q := q) (M := M) (k := k) j i X XC) := by
  by_cases hk : k = 0
  · exact Fin.elim0 (hk ▸ i)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hpq : 1 ≤ (p + (q + 1)) * k :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk)
  refine ⟨lfM p (q + 1) M k, lf3Final hpq j i X XC, ?_⟩
  have hx : ∀ a : Fin p, lfEv hpq (Fin.castSucc j) i (lf3XIdx (q := q) (M := M) (k := k) a) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.castSucc a) :=
    fun a => lfE_xIdx hpq (Fin.castSucc j) i (lfD_eq_add p (q + 1) M k hpq) a
  have ht : lfEv hpq (Fin.castSucc j) i (lf3LvIdx (p := p) (q := q) (M := M) j i) =
      Fin.castAdd (lfM p (q + 1) M k) (Fin.last p) :=
    lfE_lvIdx hpq (Fin.castSucc j) i (lfD_eq_add p (q + 1) M k hpq)
  show lfY3 (p := p) (q := q) (M := M) (k := k) j i X XC =
    projFirst (p + 1) (lfM p (q + 1) M k) '' (lf3Final hpq j i X XC).set
  exact Set.Subset.antisymm (lf3_proj_supset j i X XC _ hx ht) (lf3_proj_subset j i X XC _ hx ht)

end Work.WilE7.SheetData
