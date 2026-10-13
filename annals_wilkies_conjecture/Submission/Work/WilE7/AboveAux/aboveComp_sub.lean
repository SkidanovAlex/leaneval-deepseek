import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.BelowAux.connSub_graph

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

/-! ## Auxiliary facts for `aboveComp_sub` -/

/-- The base coordinates of `belowExtract w` are the base coordinates of the first block of `w`. -/
theorem aboveComp_sub_Fin_init {p m : ℕ} (w : Fin (belowDim p m) → ℝ) :
    Fin.init (belowExtract w) = projFirst p (m + 1) (belowZ1 w) := by
  rw [belowExtract_eq_snoc, Fin.init_snoc]

/-- `belowZ1` carries the connected component of `belowPt u₀ v t` inside `aboveS` into the
connected component of `u₀` inside `Z.set`. -/
theorem aboveComp_sub_belowZ1_image
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (v : Fin (m + 1) → ℝ) (t : ℝ)
    (hP : belowPt u₀ v t ∈ (aboveS Z S).set) :
    belowZ1 '' connectedComponentIn (aboveS Z S).set (belowPt u₀ v t)
      ⊆ connectedComponentIn Z.set u₀ := by
  have h := ContinuousOn.image_connectedComponentIn_subset (f := belowZ1 (p := p) (m := m))
    (s := (aboveS Z S).set) (a := belowPt u₀ v t) continuous_belowZ1.continuousOn hP
  rw [belowZ1_belowPt] at h
  refine h.trans (connectedComponentIn_mono u₀ ?_)
  rintro z ⟨u, hu, rfl⟩
  exact ((aboveS_mem_iff Z S u).mp hu).1

/-- Every point of the connected component of `aboveS` through the `1`-point of the top sheet
lies on that same sheet: its second block is `(base, s (k-1) base)`.  This is where the covering
hypothesis `hcov` (the sheets cover `S.X` over `C`) and the injectivity `hinj` (their graphs are
pointwise distinct) are used: the graphs are relatively closed in the union, so a preconnected set
meeting one of them stays inside it. -/
theorem aboveComp_sub_sheet_eq
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∀ w ∈ connectedComponentIn (aboveS Z S).set
        (belowPt u₀
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) 1),
      projSnd p (m + 1) (belowZ2 w) =
        s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) (belowZ2 w)) := by
  intro w hwK
  let v₀ : Fin (m + 1) → ℝ := s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩
    (projFirst p (m + 1) u₀)
  have hu0C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hP : belowPt u₀ v₀ 1 ∈ (aboveS Z S).set :=
    abovePt_mem Z S u₀ hu₀ v₀ 1
      (hsub ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ _ hu0C) (by norm_num) (hgt _ hu0C)
  have hZ1c := aboveComp_sub_belowZ1_image S Z u₀ v₀ 1 hP
  -- the "graph" map of the second block
  let Φ : (Fin (belowDim p m) → ℝ) → (Fin p → ℝ) × (Fin (m + 1) → ℝ) :=
    fun x => (projFirst p (m + 1) (belowZ2 x), projSnd p (m + 1) (belowZ2 x))
  have hΦ : Continuous Φ := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i =>
        (continuous_apply (Fin.castAdd (m + 1) i)).comp continuous_belowZ2
    · exact continuous_pi fun i =>
        (continuous_apply (Fin.natAdd p i)).comp continuous_belowZ2
  have hTconn : IsPreconnected
      (Φ '' (connectedComponentIn (aboveS Z S).set (belowPt u₀ v₀ 1))) :=
    (isPreconnected_connectedComponentIn (F := (aboveS Z S).set) (x := belowPt u₀ v₀ 1)).image
      Φ hΦ.continuousOn
  have hTU : Φ '' (connectedComponentIn (aboveS Z S).set (belowPt u₀ v₀ 1))
      ⊆ {q : (Fin p → ℝ) × (Fin (m + 1) → ℝ) | q.1 ∈ C ∧ ∃ i, q.2 = s i q.1} := by
    rintro q ⟨u, hu, rfl⟩
    have hu' := (aboveS_mem_iff Z S u).mp (connectedComponentIn_subset _ _ hu)
    have hz1u : belowZ1 u ∈ connectedComponentIn Z.set u₀ := hZ1c ⟨u, hu, rfl⟩
    have hb1 : projFirst p (m + 1) (belowZ1 u) ∈ C := by
      rw [hC]; exact ⟨belowZ1 u, hz1u, rfl⟩
    have hb2 : projFirst p (m + 1) (belowZ2 u) ∈ C := by
      rw [← hu'.2.2.1]; exact hb1
    refine ⟨hb2, ?_⟩
    obtain ⟨i, hi⟩ := hcov (belowZ2 u) hu'.2.1 hb2
    exact ⟨i, hi.symm⟩
  have hTj : ∃ q ∈ Φ '' (connectedComponentIn (aboveS Z S).set (belowPt u₀ v₀ 1)),
      q.2 = s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ q.1 := by
    refine ⟨Φ (belowPt u₀ v₀ 1),
      ⟨belowPt u₀ v₀ 1, mem_connectedComponentIn hP, rfl⟩, ?_⟩
    show projSnd p (m + 1) (belowZ2 (belowPt u₀ v₀ 1)) =
      s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩
        (projFirst p (m + 1) (belowZ2 (belowPt u₀ v₀ 1)))
    rw [belowZ2_belowPt, projSnd_append, projFirst_append]
  have hfin := (connSub_graph (C := C) (s := s)
      (j := ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩) hcont hinj hTconn hTU hTj)
    ⟨w, hwK, rfl⟩
  exact hfin.2

/-! ## The main statement -/

theorem aboveComp_sub
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.AboveAux.aboveS Z S).set
          (Work.WilE7.BelowAux.belowPt u₀
            (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀)) 1))
      ⊆ {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) ≤ 1} := by
  let v₀ : Fin (m + 1) → ℝ := s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩
    (projFirst p (m + 1) u₀)
  have hu0C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hP : belowPt u₀ v₀ 1 ∈ (aboveS Z S).set :=
    abovePt_mem Z S u₀ hu₀ v₀ 1
      (hsub ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ _ hu0C) (by norm_num) (hgt _ hu0C)
  have hZ1c := aboveComp_sub_belowZ1_image S Z u₀ v₀ 1 hP
  intro y hy
  obtain ⟨w, hwK, rfl⟩ := hy
  have hsheet := aboveComp_sub_sheet_eq S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt w hwK
  have hw := (aboveS_mem_iff Z S w).mp (connectedComponentIn_subset _ _ hwK)
  refine ⟨?_, ?_, ?_⟩
  · rw [aboveComp_sub_Fin_init, hC]
    exact ⟨belowZ1 w, hZ1c ⟨w, hwK, rfl⟩, rfl⟩
  · rw [belowExtract_apply_last, aboveComp_sub_Fin_init, hw.2.2.1, ← hsheet]
    exact hw.2.2.2.2
  · rw [belowExtract_apply_last]
    exact (abs_le.mp hw.2.2.2.1).2

end Work.WilE7.AboveAux
