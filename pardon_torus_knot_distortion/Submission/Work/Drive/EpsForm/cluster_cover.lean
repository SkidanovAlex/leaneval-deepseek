import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Covering a compact set of reals by finitely many disjoint intervals

Let `K ⊆ ℝ` be compact and `G ⊆ ℝ` open with `K ⊆ G`.  Then `K` can be covered by
finitely many pairwise disjoint closed intervals whose endpoints lie in `K` and which
are contained in `G`.

The proof is the standard "classes of the relation `uIcc x y ⊆ G`" argument: the
relation `spanRel G` is an equivalence relation *on* `K`, its classes are open in `K`,
hence (as `K` is compact) the classes are also closed in `K`; the class of `x ∈ K` has
minimum `sInf` and maximum `sSup`, both in the class, and the closed interval between
them is contained in `G` because the two endpoints of that interval are equivalent.
-/

namespace Work.Drive.EpsForm

open Set

/-! ## The span relation -/

/-- `spanRel G x y` says: the closed interval with endpoints `x` and `y` is contained in `G`. -/
def spanRel (G : Set ℝ) (x y : ℝ) : Prop := Set.uIcc x y ⊆ G

theorem spanRel_self {G : Set ℝ} {x : ℝ} (hx : x ∈ G) : spanRel G x x := by
  intro y hy
  rw [Set.uIcc_self, Set.mem_singleton_iff] at hy
  rwa [hy]

theorem spanRel_symm {G : Set ℝ} {x y : ℝ} (h : spanRel G x y) : spanRel G y x := by
  intro z hz
  apply h
  rwa [Set.uIcc_comm]

theorem uIcc_subset_union_uIcc {x y z w : ℝ} (hw : w ∈ Set.uIcc x z) :
    w ∈ Set.uIcc x y ∪ Set.uIcc y z := by
  rw [Set.mem_uIcc] at hw
  rw [Set.mem_union, Set.mem_uIcc, Set.mem_uIcc]
  rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases le_total w y with h3 | h3
    · left; left; exact ⟨h1, h3⟩
    · right; left; exact ⟨h3, h2⟩
  · rcases le_total w y with h3 | h3
    · right; right; exact ⟨h1, h3⟩
    · left; right; exact ⟨h3, h2⟩

theorem spanRel_trans {G : Set ℝ} {x y z : ℝ} (hxy : spanRel G x y) (hyz : spanRel G y z) :
    spanRel G x z := fun _ hw =>
  (uIcc_subset_union_uIcc hw).elim (fun h => hxy h) (fun h => hyz h)

/-- If `u ∈ Ioo (c - δ) (c + δ)` then the whole interval between `u` and `c` is contained
in that same open interval. -/
theorem uIcc_subset_Ioo_of_mem {c δ u z : ℝ} (hu : u ∈ Set.Ioo (c - δ) (c + δ))
    (hz : z ∈ Set.uIcc u c) : z ∈ Set.Ioo (c - δ) (c + δ) := by
  obtain ⟨hu1, hu2⟩ := hu
  rw [Set.mem_uIcc] at hz
  rw [Set.mem_Ioo]
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-! ## Classes of the span relation -/

/-- The `spanRel G`-class of a point `x`, inside `K`. -/
def Cls (K G : Set ℝ) (x : ℝ) : Set ℝ := {y | y ∈ K ∧ spanRel G y x}

theorem Cls_subset (K G : Set ℝ) (x : ℝ) : Cls K G x ⊆ K := fun _ hy => hy.1

theorem Cls_self_mem {K G : Set ℝ} {x : ℝ} (hxK : x ∈ K) (hxG : x ∈ G) : x ∈ Cls K G x :=
  ⟨hxK, spanRel_self hxG⟩

theorem Cls_eq_of_mem_inter {K G : Set ℝ} {x y v : ℝ} (hx : v ∈ Cls K G x)
    (hy : v ∈ Cls K G y) : Cls K G x = Cls K G y := by
  apply Set.Subset.antisymm
  · intro z hz
    exact ⟨hz.1, spanRel_trans hz.2 (spanRel_trans (spanRel_symm hx.2) hy.2)⟩
  · intro z hz
    exact ⟨hz.1, spanRel_trans hz.2 (spanRel_trans (spanRel_symm hy.2) hx.2)⟩

/-- If `z` lies between `y` and `x` and `y'` is closer to `y` than `z` is, then `z` still
lies between `y'` and `x`. -/
theorem mem_uIcc_of_dist_lt {x y y' z : ℝ} (_hzx : z ≠ x) (hzy : z ≠ y)
    (hz : z ∈ Set.uIcc y x) (hd : dist y y' < |y - z|) : z ∈ Set.uIcc y' x := by
  rw [Real.dist_eq] at hd
  rw [Set.mem_uIcc] at hz ⊢
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hlt : y < z := lt_of_le_of_ne h1 (Ne.symm hzy)
    have hyz : y - z < 0 := by linarith
    rw [abs_of_neg hyz] at hd
    rw [abs_lt] at hd
    exact Or.inl ⟨le_of_lt (by linarith [hd.1]), h2⟩
  · have hlt : z < y := lt_of_le_of_ne h2 hzy
    have hzy' : 0 < y - z := by linarith
    rw [abs_of_pos hzy'] at hd
    rw [abs_lt] at hd
    exact Or.inr ⟨h1, le_of_lt (by linarith [hd.2])⟩

/-- The class of a point of `K` is closed, provided `K` is closed and `G` is open. -/
theorem isClosed_Cls {K G : Set ℝ} (hK : IsClosed K) (_hG : IsOpen G) (hKG : K ⊆ G)
    {x : ℝ} (hxK : x ∈ K) : IsClosed (Cls K G x) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hyK : y ∈ K := hK.closure_subset (closure_mono (Cls_subset K G x) hy)
  refine ⟨hyK, ?_⟩
  intro z hz
  rcases eq_or_ne z y with hzy | hzy
  · rw [hzy]; exact hKG hyK
  · rcases eq_or_ne z x with hzx | hzx
    · rw [hzx]; exact hKG hxK
    · have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hzy))
      obtain ⟨y', hy', hyd⟩ := Metric.mem_closure_iff.mp hy |y - z| hpos
      exact hy'.2 (mem_uIcc_of_dist_lt hzx hzy hz hyd)

/-! ## The interval associated with a class -/

/-- The closed interval spanned by the class of `x`. -/
noncomputable def clsInterval (K G : Set ℝ) (x : ℝ) : ℝ × ℝ :=
  (sInf (Cls K G x), sSup (Cls K G x))

/-! ## The covering lemma -/

theorem exists_disjoint_interval_cover {K : Set ℝ} (hK : IsCompact K) {G : Set ℝ}
    (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ (N : ℕ) (a b : Fin N → ℝ),
      (∀ i, a i ∈ K ∧ b i ∈ K ∧ a i ≤ b i) ∧
      (∀ i, Set.Icc (a i) (b i) ⊆ G) ∧
      (∀ i j : Fin N, i ≠ j → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))) ∧
      (∀ u ∈ K, ∃ i, u ∈ Set.Icc (a i) (b i)) := by
  classical
  by_cases hKe : K.Nonempty
  · have hδ : ∀ x : ↥K, ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (x.1 - δ) (x.1 + δ) ⊆ G := by
      intro x
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hG x.1 (hKG x.2)
      exact ⟨ε, hε, by rwa [Real.ball_eq_Ioo] at hεsub⟩
    choose δ hδpos hδsub using hδ
    have hcover : K ⊆ ⋃ x : ↥K, Set.Ioo (x.1 - δ x) (x.1 + δ x) := by
      intro u hu
      refine Set.mem_iUnion.mpr ⟨⟨u, hu⟩, ?_⟩
      exact Set.mem_Ioo.mpr ⟨by linarith [hδpos ⟨u, hu⟩], by linarith [hδpos ⟨u, hu⟩]⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : ↥K => Set.Ioo (x.1 - δ x) (x.1 + δ x))
      (fun _ => isOpen_Ioo) hcover
    have ht' : ∀ u ∈ K, ∃ x : ↥K, x ∈ (t : Set ↥K) ∧ u ∈ Set.Ioo (x.1 - δ x) (x.1 + δ x) := by
      intro u hu
      obtain ⟨x, hxu⟩ := Set.mem_iUnion.mp (ht hu)
      obtain ⟨hxt, hxu'⟩ := Set.mem_iUnion.mp hxu
      exact ⟨x, hxt, hxu'⟩
    have hclsne : ∀ x : ↥K, (Cls K G x.1).Nonempty :=
      fun x => ⟨x.1, Cls_self_mem x.2 (hKG x.2)⟩
    have hclsclosed : ∀ x : ↥K, IsClosed (Cls K G x.1) :=
      fun x => isClosed_Cls hK.isClosed hG hKG x.2
    have hbdd : Bornology.IsBounded K := hK.isBounded
    have hbddBelow : BddBelow K := (isBounded_iff_bddBelow_bddAbove.mp hbdd).1
    have hbddAbove : BddAbove K := (isBounded_iff_bddBelow_bddAbove.mp hbdd).2
    have hclsBelow : ∀ x : ↥K, BddBelow (Cls K G x.1) :=
      fun x => hbddBelow.mono (Cls_subset K G x.1)
    have hclsAbove : ∀ x : ↥K, BddAbove (Cls K G x.1) :=
      fun x => hbddAbove.mono (Cls_subset K G x.1)
    have hlow : ∀ x : ↥K, sInf (Cls K G x.1) ∈ Cls K G x.1 :=
      fun x => (hclsclosed x).csInf_mem (hclsne x) (hclsBelow x)
    have hhigh : ∀ x : ↥K, sSup (Cls K G x.1) ∈ Cls K G x.1 :=
      fun x => (hclsclosed x).csSup_mem (hclsne x) (hclsAbove x)
    have hle : ∀ x : ↥K, sInf (Cls K G x.1) ≤ sSup (Cls K G x.1) :=
      fun x => csInf_le_csSup (hclsne x) (hclsBelow x) (hclsAbove x)
    have hspan : ∀ x : ↥K, spanRel G (sInf (Cls K G x.1)) (sSup (Cls K G x.1)) := fun x =>
      spanRel_trans (hlow x).2 (spanRel_symm (hhigh x).2)
    have hIcc : ∀ x : ↥K, Set.Icc (sInf (Cls K G x.1)) (sSup (Cls K G x.1)) ⊆ G := fun x => by
      rw [← Set.uIcc_of_le (hle x)]
      exact hspan x
    have hclassIcc : ∀ x : ↥K,
        K ∩ Set.Icc (sInf (Cls K G x.1)) (sSup (Cls K G x.1)) = Cls K G x.1 := by
      intro x
      apply Set.Subset.antisymm
      · rintro z ⟨hzK, hz1, hz2⟩
        refine ⟨hzK, ?_⟩
        have h1 : spanRel G z (sInf (Cls K G x.1)) := by
          intro w hw
          have hw' : w ∈ Set.Icc (sInf (Cls K G x.1)) z := by
            rw [Set.uIcc_comm, Set.uIcc_of_le hz1] at hw
            exact hw
          exact hIcc x (Set.mem_Icc.mpr ⟨hw'.1, le_trans hw'.2 hz2⟩)
        exact spanRel_trans h1 (hlow x).2
      · intro z hz
        exact ⟨hz.1, csInf_le (hclsBelow x) hz, le_csSup (hclsAbove x) hz⟩
    set P : Set (ℝ × ℝ) := (fun x : ↥K => clsInterval K G x.1) '' (t : Set ↥K) with hPdef
    have hPfin : P.Finite :=
      Set.Finite.image (fun x : ↥K => clsInterval K G x.1) t.finite_toSet
    letI : Fintype ↥P := hPfin.fintype
    have hwit : ∀ p : ℝ × ℝ, p ∈ P →
        ∃ x : ↥K, x ∈ (t : Set ↥K) ∧ clsInterval K G x.1 = p := by
      intro p hp
      rw [hPdef] at hp
      obtain ⟨x, hxt, hx⟩ := hp
      exact ⟨x, hxt, hx⟩
    -- the four properties, stated for points of `P`
    have hA : ∀ p : ↥P, p.1.1 ∈ K := by
      intro p
      obtain ⟨x, -, hx⟩ := hwit p.1 p.2
      have h1 : sInf (Cls K G x.1) = p.1.1 := congrArg Prod.fst hx
      exact h1 ▸ Cls_subset K G x.1 (hlow x)
    have hB : ∀ p : ↥P, p.1.2 ∈ K := by
      intro p
      obtain ⟨x, -, hx⟩ := hwit p.1 p.2
      have h2 : sSup (Cls K G x.1) = p.1.2 := congrArg Prod.snd hx
      exact h2 ▸ Cls_subset K G x.1 (hhigh x)
    have hAB : ∀ p : ↥P, p.1.1 ≤ p.1.2 := by
      intro p
      obtain ⟨x, -, hx⟩ := hwit p.1 p.2
      have h1 : sInf (Cls K G x.1) = p.1.1 := congrArg Prod.fst hx
      have h2 : sSup (Cls K G x.1) = p.1.2 := congrArg Prod.snd hx
      exact h1 ▸ h2 ▸ hle x
    have hGp : ∀ p : ↥P, Set.Icc p.1.1 p.1.2 ⊆ G := by
      intro p
      obtain ⟨x, -, hx⟩ := hwit p.1 p.2
      have h1 : sInf (Cls K G x.1) = p.1.1 := congrArg Prod.fst hx
      have h2 : sSup (Cls K G x.1) = p.1.2 := congrArg Prod.snd hx
      exact h1 ▸ h2 ▸ hIcc x
    have hdisj : ∀ p q : ↥P, p ≠ q →
        Disjoint (Set.Icc p.1.1 p.1.2) (Set.Icc q.1.1 q.1.2) := by
      intro p q hpq
      obtain ⟨x, -, hx⟩ := hwit p.1 p.2
      obtain ⟨y, -, hy⟩ := hwit q.1 q.2
      have h1 : sInf (Cls K G x.1) = p.1.1 := congrArg Prod.fst hx
      have h2 : sSup (Cls K G x.1) = p.1.2 := congrArg Prod.snd hx
      have h3 : sInf (Cls K G y.1) = q.1.1 := congrArg Prod.fst hy
      have h4 : sSup (Cls K G y.1) = q.1.2 := congrArg Prod.snd hy
      have hneq : Cls K G x.1 ≠ Cls K G y.1 := by
        intro hEq
        have hmid : clsInterval K G x.1 = clsInterval K G y.1 :=
          congrArg (fun C : Set ℝ => (sInf C, sSup C)) hEq
        exact hpq (Subtype.ext (hx.symm.trans (hmid.trans hy)))
      have hAy : sInf (Cls K G y.1) ∉ Set.Icc (sInf (Cls K G x.1)) (sSup (Cls K G x.1)) := by
        intro hmem
        have hin : sInf (Cls K G y.1) ∈ Cls K G x.1 := by
          rw [← hclassIcc x]
          exact ⟨Cls_subset K G y.1 (hlow y), hmem⟩
        exact hneq (Cls_eq_of_mem_inter hin (hlow y))
      have hAx : sInf (Cls K G x.1) ∉ Set.Icc (sInf (Cls K G y.1)) (sSup (Cls K G y.1)) := by
        intro hmem
        have hin : sInf (Cls K G x.1) ∈ Cls K G y.1 := by
          rw [← hclassIcc y]
          exact ⟨Cls_subset K G x.1 (hlow x), hmem⟩
        exact hneq (Cls_eq_of_mem_inter (hlow x) hin)
      have hd1 : sInf (Cls K G y.1) < sInf (Cls K G x.1) ∨
          sSup (Cls K G x.1) < sInf (Cls K G y.1) := by
        rcases lt_or_ge (sInf (Cls K G y.1)) (sInf (Cls K G x.1)) with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge fun hle' => hAy (Set.mem_Icc.mpr ⟨h, hle'⟩))
      have hd2 : sInf (Cls K G x.1) < sInf (Cls K G y.1) ∨
          sSup (Cls K G y.1) < sInf (Cls K G x.1) := by
        rcases lt_or_ge (sInf (Cls K G x.1)) (sInf (Cls K G y.1)) with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge fun hle' => hAx (Set.mem_Icc.mpr ⟨h, hle'⟩))
      rw [← h1, ← h2, ← h3, ← h4, Set.disjoint_left]
      intro z hz1 hz2
      rcases hd1 with h | h <;> rcases hd2 with h' | h' <;>
        linarith [hz1.1, hz1.2, hz2.1, hz2.2]
    have hcov : ∀ u ∈ K, ∃ p : ↥P, u ∈ Set.Icc p.1.1 p.1.2 := by
      intro u hu
      obtain ⟨x, hxt, hxu⟩ := ht' u hu
      have hmem : u ∈ Cls K G x.1 :=
        ⟨hu, fun z hz => hδsub x (uIcc_subset_Ioo_of_mem hxu hz)⟩
      have hp : clsInterval K G x.1 ∈ P := by
        rw [hPdef]
        exact ⟨x, hxt, rfl⟩
      refine ⟨⟨clsInterval K G x.1, hp⟩, ?_⟩
      show u ∈ Set.Icc (sInf (Cls K G x.1)) (sSup (Cls K G x.1))
      exact Set.mem_Icc.mpr ⟨csInf_le (hclsBelow x) hmem, le_csSup (hclsAbove x) hmem⟩
    refine ⟨Fintype.card ↥P, fun i => ((Fintype.equivFin ↥P).symm i).1.1,
      fun i => ((Fintype.equivFin ↥P).symm i).1.2, ?_, ?_, ?_, ?_⟩
    · intro i
      show ((Fintype.equivFin ↥P).symm i).1.1 ∈ K ∧
        ((Fintype.equivFin ↥P).symm i).1.2 ∈ K ∧
        ((Fintype.equivFin ↥P).symm i).1.1 ≤ ((Fintype.equivFin ↥P).symm i).1.2
      exact ⟨hA _, hB _, hAB _⟩
    · intro i
      show Set.Icc (((Fintype.equivFin ↥P).symm i).1.1)
        (((Fintype.equivFin ↥P).symm i).1.2) ⊆ G
      exact hGp _
    · intro i j hij
      show Disjoint (Set.Icc ((Fintype.equivFin ↥P).symm i).1.1
          ((Fintype.equivFin ↥P).symm i).1.2)
        (Set.Icc ((Fintype.equivFin ↥P).symm j).1.1
          ((Fintype.equivFin ↥P).symm j).1.2)
      exact hdisj _ _ fun h => hij ((Fintype.equivFin ↥P).symm.injective h)
    · intro u hu
      obtain ⟨p, hp⟩ := hcov u hu
      refine ⟨(Fintype.equivFin ↥P) p, ?_⟩
      show u ∈ Set.Icc
        ((Fintype.equivFin ↥P).symm ((Fintype.equivFin ↥P) p)).1.1
        ((Fintype.equivFin ↥P).symm ((Fintype.equivFin ↥P) p)).1.2
      rw [Equiv.symm_apply_apply]
      exact hp
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_⟩ <;>
      simp [Set.not_nonempty_iff_eq_empty.mp hKe]

/-! ## The requested lemma -/

theorem cluster_cover {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hγ : Continuous γ)
    {S : Set ℝ} (hSopen : IsOpen S)
    {W : Set LeanEval.KnotTheory.PardonDistortion.R3} (hWopen : IsOpen W)
    (hW : ∀ t : ℝ, t ∈ frontier S → γ t ∈ W) :
    ∃ (N : ℕ) (a b : Fin N → ℝ),
      (∀ i, a i ∈ frontier S ∧ b i ∈ frontier S ∧ a i ≤ b i) ∧
      (∀ i, ∀ u ∈ Set.Icc (a i) (b i), γ u ∈ W) ∧
      (∀ i j : Fin N, i ≠ j → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))) ∧
      (∀ u ∈ frontier S, u ∈ Set.Icc 0 (2 * Real.pi) → ∃ i, u ∈ Set.Icc (a i) (b i)) := by
  classical
  have hKcpt : IsCompact (frontier S ∩ Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.inter_left isClosed_frontier
  have hGopen : IsOpen (γ ⁻¹' W) := hWopen.preimage hγ
  have hKG : frontier S ∩ Set.Icc 0 (2 * Real.pi) ⊆ γ ⁻¹' W := fun u hu => hW u hu.1
  obtain ⟨N, a, b, h1, h2, h3, h4⟩ := exists_disjoint_interval_cover hKcpt hGopen hKG
  refine ⟨N, a, b, ?_, ?_, h3, ?_⟩
  · intro i
    obtain ⟨ha, hb, hab⟩ := h1 i
    exact ⟨ha.1, hb.1, hab⟩
  · intro i u hu
    exact h2 i hu
  · intro u hu1 hu2
    exact h4 u ⟨hu1, hu2⟩

end Work.Drive.EpsForm
