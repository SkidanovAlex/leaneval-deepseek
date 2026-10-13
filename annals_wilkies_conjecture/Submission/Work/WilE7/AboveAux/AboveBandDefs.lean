/-
  WilE7 (`Submission.Work.WilE7.AboveAux.AboveBandDefs`): the semi-Pfaffian presentation of the
  *open above band* of the top sheet.

  `Work.WilE7.AboveAux.aboveS` presents the *closed* above cell of the top sheet,
      `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ (s j (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) ≤ 1}`,
  by cutting the fibre product `Z ×_{ℝ^p} S.X` (with the vertical cube coordinate `t`) by the
  single inequality `v₂ < t`; the closed upper bound `t ≤ 1` is the cube constraint on `t`.

  Here we present the *open* above band
      `{y | Fin.init y ∈ C ∧ (s j (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧ y (Fin.last p) < 1}`
  by adding a second inequality atom `t < 1` (the atom `abovePtop = 1 - t`) to the same fibre
  product.  Everything else is reused verbatim: the ambient layout `belowDim`, the extraction map
  `belowExtract`, the parametrised point `belowPt` and the coordinate permutation `belowPerm` of
  `Submission.Work.WilE7.BelowAux.BelowDefs`.

  The file records

  * the atoms (`abovePtop`), the point set of the band set (`aboveBandS_mem_iff`), its inclusion
    in the closed above cell (`aboveBandS_subset_aboveS`) and the format under a coordinate
    permutation (`aboveBandS_reindex_fmt`);
  * the canonical point `aboveBandPt` of the band (base `u₀`, top sheet, vertical coordinate the
    midpoint of the top level and `1`) and its membership (`aboveBandPt_mem`);
  * the parametrising region `aboveBandH` of `(base component) × ℝ`, the continuity of `abovePhi`
    on it (`abovePhi_continuousOn_aboveBandH`), the fact that it lands in the band set
    (`abovePhi_mem_aboveBandS`) and its preconnectedness (`aboveBandH_preconn`, from the generic
    `preconn_open_over_graph`).

  The two halves of "the connected component of `aboveBandS` through `aboveBandPt` projects
  exactly onto the open band" are `Work.WilE7.AboveAux.aboveBandComp_sub` and
  `Work.WilE7.AboveAux.aboveBandComp_cov`; the assembly is
  `Submission/Work/WilE7/AboveAux/aboveBand_star.lean`.
-/
import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.AboveAux.abovePhi_mem
import Submission.Work.WilE7.AboveAux.abovePhi_continuous
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.AboveAux
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

/-! ## §1. The preconnectedness of the open region `σ x < t < 1` -/

/-- The region `{(x,t) : x ∈ C, σ x < t < 1}` above the graph of `σ` and below the level `1` is
preconnected, whenever `C` is preconnected and `σ` is continuous on `C` with `σ < 1` on `C`.

It is the continuous image of the preconnected set `C × (0,1)` under the map
`(x,s) ↦ (x, (1-s)·σ x + s)`, which is a bijection onto it because `σ x < 1`.  This is the
mirror of `Work.WilE7.AboveAux.preconn_over_graph` (which treats the closed region
`σ x < t ≤ 1`). -/
theorem preconn_open_over_graph {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {σ : α → ℝ} (hσ : ContinuousOn σ C)
    (hσ1 : ∀ x ∈ C, σ x < 1) :
    IsPreconnected {q : α × ℝ | q.1 ∈ C ∧ σ q.1 < q.2 ∧ q.2 < 1} := by
  have hDpre : IsPreconnected (C ×ˢ Set.Ioo (0 : ℝ) 1) := hC.prod isPreconnected_Ioo
  have hcont : ContinuousOn (fun q : α × ℝ => (q.1, (1 - q.2) * σ q.1 + q.2))
      (C ×ˢ Set.Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.prodMk continuous_fst.continuousOn ?_
    have hσc : ContinuousOn (fun q : α × ℝ => σ q.1) (C ×ˢ Set.Ioo (0 : ℝ) 1) :=
      hσ.comp continuous_fst.continuousOn (fun q hq => hq.1)
    have hlin : ContinuousOn (fun q : α × ℝ => (1 : ℝ) - q.2)
        (C ×ˢ Set.Ioo (0 : ℝ) 1) :=
      ContinuousOn.sub continuous_const.continuousOn continuous_snd.continuousOn
    exact ContinuousOn.add (ContinuousOn.mul hlin hσc) continuous_snd.continuousOn
  have himg : (fun q : α × ℝ => (q.1, (1 - q.2) * σ q.1 + q.2)) ''
        (C ×ˢ Set.Ioo (0 : ℝ) 1)
      = {q : α × ℝ | q.1 ∈ C ∧ σ q.1 < q.2 ∧ q.2 < 1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Set.mem_prod, Set.mem_Ioo] at hp
      obtain ⟨hpC, hp2pos, hp2lt⟩ := hp
      have h1 : σ p.1 < 1 := hσ1 p.1 hpC
      refine ⟨hpC, ?_, ?_⟩
      · nlinarith [mul_pos hp2pos (sub_pos.mpr h1)]
      · nlinarith [mul_pos (sub_pos.mpr hp2lt) (sub_pos.mpr h1)]
    · rintro ⟨hqC, hq2, hq3⟩
      have h1 : σ q.1 < 1 := hσ1 q.1 hqC
      have hden : 0 < 1 - σ q.1 := sub_pos.mpr h1
      refine ⟨(q.1, (q.2 - σ q.1) / (1 - σ q.1)), ?_, ?_⟩
      · rw [Set.mem_prod, Set.mem_Ioo]
        exact ⟨hqC, div_pos (sub_pos.mpr hq2) hden, (div_lt_one hden).mpr (by linarith)⟩
      · have hne : (1 : ℝ) - σ q.1 ≠ 0 := ne_of_gt hden
        have hsval : (1 - (q.2 - σ q.1) / (1 - σ q.1)) * σ q.1 +
            (q.2 - σ q.1) / (1 - σ q.1) = q.2 := by
          field_simp
          ring
        exact Prod.ext rfl hsval
  rw [← himg]
  exact hDpre.image _ hcont

/-! ## §2. The atom `1 - t > 0` -/

/-- The atom `1 - t`, positive exactly when the vertical coordinate lies below the level `1`. -/
def abovePtop (p m r : ℕ) : EAPoly (belowDim p m) r :=
  MvPolynomial.C 1 - MvPolynomial.X (Sum.inl (belowTIdx p m))

theorem eaEval_abovePtop {p m r : ℕ} (c : EAChain (belowDim p m) r)
    (w : Fin (belowDim p m) → ℝ) :
    eaEval c (abovePtop p m r) w = 1 - belowT w := by
  simp [abovePtop, eaEval, belowT]

theorem atomDeg_abovePtop {p m r : ℕ} : atomDeg (abovePtop p m r) ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.C (1 : ℝ) : EAPoly (belowDim p m) r)
    (MvPolynomial.X (Sum.inl (belowTIdx p m)) : EAPoly (belowDim p m) r)
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X] at h
  have h1 : max (0 : ℕ) 1 = 1 := by norm_num
  rw [h1] at h
  simp only [atomDeg, abovePtop]
  omega

/-! ## §3. The construction and its point set -/

/-- The `SemiPf` set of the open above band: the fibre product with the vertical coordinate, cut
by `v₂ < t < 1`. -/
noncomputable def aboveBandS {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.addConds (abovePadded Z S) []
    [abovePlow p m (abovePadded Z S).r, abovePtop p m (abovePadded Z S).r]

/-- **The point set of `aboveBandS`.**  Membership is: `z₁ ∈ Z.set`, `z₂ ∈ S.X.set` over the
same base as `z₁`, `|t| ≤ 1`, `v₂ < t` and `t < 1`. -/
theorem aboveBandS_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (w : Fin (belowDim p m) → ℝ) :
    w ∈ (aboveBandS Z S).set ↔
      belowZ1 w ∈ Z.set ∧ belowZ2 w ∈ S.X.set ∧
      projFirst p (m + 1) (belowZ1 w) = projFirst p (m + 1) (belowZ2 w) ∧
      |belowT w| ≤ 1 ∧ belowV2 w < belowT w ∧ belowT w < 1 := by
  rw [aboveBandS, Work.WilE7.SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true]
  rw [eaEval_abovePlow, eaEval_abovePtop]
  rw [abovePadded_eq]
  simp only [Set.mem_ofPred_eq]
  rw [aboveW1_eq]
  rw [belowZ1_projFirst, belowZ2_projSnd]
  rw [belowT_eq, Work.WilE7.mem_cubeC_one]
  simp only [sub_pos]
  tauto

/-- The open band set is contained in the closed above cell. -/
theorem aboveBandS_subset_aboveS {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S : Stratum p (m + 1)) :
    (aboveBandS Z S).set ⊆ (aboveS Z S).set := by
  intro w hw
  rw [aboveBandS_mem_iff] at hw
  rw [aboveS_mem_iff]
  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1⟩

/-- Reindexing `aboveBandS` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + belowFib p m = belowDim p m`). -/
theorem aboveBandS_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (e : Fin (belowDim p m) ≃ Fin ((p + 1) + belowFib p m)) :
    (Work.WilE7.SemiPf.reindex e (aboveBandS Z S)).fmt = (aboveBandS Z S).fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.reindex, belowFib, belowDim, belowK]
  omega

/-! ## §4. The canonical point of the band -/

/-- The vertical coordinate of the canonical point of the open above band: the midpoint of the
top sheet level at the base point `π u₀` and the level `1`. -/
noncomputable def aboveBandT {p m k : ℕ} (u₀ : Fin (p + (m + 1)) → ℝ)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (hk : 0 < k) : ℝ :=
  ((s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) + 1) / 2

/-- The canonical point of the open above band of the top sheet: base `u₀`, second block the top
sheet, vertical coordinate `aboveBandT`. -/
noncomputable def aboveBandPt {p m k : ℕ} (u₀ : Fin (p + (m + 1)) → ℝ)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (hk : 0 < k) :
    Fin (belowDim p m) → ℝ :=
  belowPt u₀ (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀))
    (aboveBandT u₀ s hk)

/-- The canonical point is the parametrised point of `(u₀, aboveBandT)`. -/
theorem aboveBandPt_eq_abovePhi {p m k : ℕ} (u₀ : Fin (p + (m + 1)) → ℝ)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (hk : 0 < k) :
    abovePhi s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (u₀, aboveBandT u₀ s hk) =
      aboveBandPt u₀ s hk := rfl

theorem aboveBandT_lt_one {p m k : ℕ} {u₀ : Fin (p + (m + 1)) → ℝ}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {hk : 0 < k}
    (h : (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) < 1) :
    aboveBandT u₀ s hk < 1 := by
  rw [aboveBandT]
  linarith

theorem lt_aboveBandT {p m k : ℕ} {u₀ : Fin (p + (m + 1)) → ℝ}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {hk : 0 < k}
    (h : (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) < 1) :
    (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) <
      aboveBandT u₀ s hk := by
  rw [aboveBandT]
  linarith

/-- The canonical point of the band lies in `aboveBandS`. -/
theorem aboveBandPt_mem {p m : ℕ} (S : Stratum p (m + 1)) (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    aboveBandPt u₀ s hk ∈ (aboveBandS Z S).set := by
  have hx₀C : projFirst p (m + 1) u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hmem : Fin.append (projFirst p (m + 1) u₀)
      (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) ∈ S.X.set :=
    hsub _ _ hx₀C
  have hlvl1 := hgt (projFirst p (m + 1) u₀) hx₀C
  have hbnd :
      -1 ≤ (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m) := by
    have h := hmem.1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at h
    linarith [neg_abs_le
      ((s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (projFirst p (m + 1) u₀)) (Fin.last m))]
  simp only [aboveBandPt, aboveBandT, aboveBandS_mem_iff, belowZ1_belowPt, belowZ2_belowPt,
    belowT_belowPt, belowV2_belowPt, projFirst_append]
  refine ⟨?_, hmem, ?_, ?_, ?_, ?_⟩
  · exact connectedComponentIn_subset Z.set u₀ (mem_connectedComponentIn hu₀)
  · trivial
  · rw [abs_le]
    constructor <;> linarith
  · linarith
  · linarith

/-! ## §5. The parametrisation of the band -/

/-- The region of `(base component) × ℝ` parametrising the open above band: the base point runs
over the component of `Z` through `u₀` and the vertical coordinate over `(level of s j, 1)`. -/
def aboveBandH {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ connectedComponentIn Z.set u₀ ∧
    (s j (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 ∧ q.2 < 1}

theorem mem_aboveBandH {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ} :
    q ∈ aboveBandH Z s j u₀ ↔ q.1 ∈ connectedComponentIn Z.set u₀ ∧
      (s j (projFirst p (m + 1) q.1)) (Fin.last m) < q.2 ∧ q.2 < 1 := Iff.rfl

/-- The band region is contained in the closed region `aboveH`. -/
theorem aboveBandH_subset_aboveH {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u₀ : Fin (p + (m + 1)) → ℝ) :
    aboveBandH Z s j u₀ ⊆ aboveH Z s j u₀ := by
  intro q hq
  rw [mem_aboveBandH] at hq
  rw [mem_aboveH]
  exact ⟨hq.1, hq.2.1, le_of_lt hq.2.2⟩

/-- The parametrisation `abovePhi s j` is continuous on the band region `aboveBandH`. -/
theorem abovePhi_continuousOn_aboveBandH {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hcont : ContinuousOn (s j) C) :
    ContinuousOn (abovePhi s j) (aboveBandH Z s j u₀) :=
  (abovePhi_continuous Z u₀ C hC s j hcont).mono (aboveBandH_subset_aboveH Z s j u₀)

/-- The parametrisation of the band region lands in `aboveBandS`. -/
theorem abovePhi_mem_aboveBandS {p m k : ℕ} (S : Stratum p (m + 1))
    (Z : SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set) :
    ∀ q ∈ aboveBandH Z s j u₀, abovePhi s j q ∈ (aboveBandS Z S).set := by
  intro q hq
  rw [mem_aboveBandH] at hq
  obtain ⟨hq1, hqlast, hqtop⟩ := hq
  have hxC : projFirst p (m + 1) q.1 ∈ C := by
    rw [hC]
    exact Set.mem_image_of_mem _ hq1
  have hmem := hsub j (projFirst p (m + 1) q.1) hxC
  have hlvl : -1 ≤ (s j (projFirst p (m + 1) q.1)) (Fin.last m) := by
    have := hmem.1 (Fin.natAdd p (Fin.last m))
    rw [Fin.append_right] at this
    linarith [neg_abs_le ((s j (projFirst p (m + 1) q.1)) (Fin.last m))]
  simp only [abovePhi, aboveBandS_mem_iff, belowZ1_belowPt, belowZ2_belowPt, belowT_belowPt,
    belowV2_belowPt, projFirst_append]
  refine ⟨?_, hmem, trivial, ?_, ?_, hqtop⟩
  · exact connectedComponentIn_subset Z.set u₀ hq1
  · rw [abs_le]
    exact ⟨by linarith, le_of_lt hqtop⟩
  · exact hqlast

/-- The band region is preconnected (the mirror of `preconn_over_graph` for the open region). -/
theorem aboveBandH_preconn {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hcont : ContinuousOn (s j) C)
    (hgt : ∀ x ∈ C, (s j x) (Fin.last m) < 1) :
    IsPreconnected (aboveBandH Z s j u₀) := by
  have hpi : ∀ u ∈ connectedComponentIn Z.set u₀, projFirst p (m + 1) u ∈ C := by
    intro u hu
    rw [hC]
    exact ⟨u, hu, rfl⟩
  have hσ : ContinuousOn
      (fun u : Fin (p + (m + 1)) → ℝ => (s j (projFirst p (m + 1) u)) (Fin.last m))
      (connectedComponentIn Z.set u₀) :=
    (continuous_apply (Fin.last m)).comp_continuousOn
      ((hcont.comp (Work.WilE7.continuous_projFirst p (m + 1)).continuousOn hpi))
  rw [aboveBandH]
  exact preconn_open_over_graph isPreconnected_connectedComponentIn hσ
    (fun u hu => hgt _ (hpi u hu))

end Work.WilE7.AboveAux
