import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.CoreStep.localGraph_on_branch
import Submission.Work.WilE7.eaEval_eventually_eq
import Submission.Work.CoreStep.absSet_point_isolated
import Submission.Work.CoreStep.exists_good_singleton_stratum

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.CoreStep
open Work.WilE7.MainDesign

/-! ### Helpers -/

theorem absSet_subset_cubeC' {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    Work.WilE7.MainDesign.absSet S ⊆ WilkiesDesign.E.cubeC N := by
  rintro z ⟨w, hw, hweq⟩
  rw [← hweq]
  intro i
  exact hw.1 (Fin.cast (Nat.zero_add N).symm i)

theorem cubeC_isCompact' (k : ℕ) : IsCompact (WilkiesDesign.E.cubeC k) := by
  have h : WilkiesDesign.E.cubeC k = Set.univ.pi (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, WilkiesDesign.E.cubeC, Set.mem_Icc]
    exact ⟨fun h i => ⟨neg_le_of_abs_le (h i), le_of_abs_le (h i)⟩,
      fun h i => abs_le.mpr ⟨(h i).1, (h i).2⟩⟩
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem continuous_projFirst' (n m : ℕ) : Continuous (WilkiesDesign.E.projFirst n m) :=
  continuous_pi (fun _ => continuous_apply _)

theorem absPtInv_mem_cubeC {n m : ℕ} {T : WilkiesDesign.E.Stratum 0 (n + (m + 1))}
    {u : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ} (hu : u ∈ T.X.set) :
    Work.WilE7.CoreStep.absPtInv u ∈ WilkiesDesign.E.cubeC (n + (m + 1)) := by
  intro i
  exact hu.1 (Fin.cast (Nat.zero_add (n + (m + 1))).symm i)

theorem pairPt_mem_cubeC {n m : ℕ} {u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ}
    (hu : Work.WilE7.CoreStep.absPtInv u ∈ WilkiesDesign.E.cubeC (n + (m + 1)))
    (hv : Work.WilE7.CoreStep.absPtInv v ∈ WilkiesDesign.E.cubeC (n + (m + 1))) :
    Work.WilE7.CoreStep.pairPt u v ∈ WilkiesDesign.E.cubeC (Work.WilE7.CoreStep.pPair n m) := by
  intro i
  refine Fin.addCases (m := n + (m + 1)) (n := n + (m + 1))
    (motive := fun i => |Work.WilE7.CoreStep.pairPt u v i| ≤ 1) (fun i => ?_) (fun i => ?_) i
  · rw [show Work.WilE7.CoreStep.pairPt u v (Fin.castAdd (n + (m + 1)) i) =
        Work.WilE7.CoreStep.absPtInv u i from Fin.append_left _ _ i]
    exact hu i
  · rw [show Work.WilE7.CoreStep.pairPt u v (Fin.natAdd (n + (m + 1)) i) =
        Work.WilE7.CoreStep.absPtInv v i from Fin.append_right _ _ i]
    exact hv i

theorem pairPtUp_mem_cubeC {n m : ℕ} {u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ}
    (hu : Work.WilE7.CoreStep.absPtInv u ∈ WilkiesDesign.E.cubeC (n + (m + 1)))
    (hv : Work.WilE7.CoreStep.absPtInv v ∈ WilkiesDesign.E.cubeC (n + (m + 1))) :
    Work.WilE7.CoreStep.pairPtUp u v ∈ WilkiesDesign.E.cubeC (0 + Work.WilE7.CoreStep.pPair n m) :=
  fun j => pairPt_mem_cubeC hu hv (Fin.cast (Nat.zero_add (Work.WilE7.CoreStep.pPair n m)) j)

/-! ### `T.j = n + (m+1)` from the no-low-dimensional-stratum hypothesis -/

theorem card_eq_of_no_lowDim {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ) (hu : u ∈ T.X.set) (hv : v ∈ T.X.set)
    (huv : Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v)
    (hbase : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) =
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v))
    (hnolow : ∀ W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m), W.Good →
        W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set →
        Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) :
    T.j = n + (m + 1) := by
  have hj_le : T.j ≤ n + (m + 1) := by
    obtain ⟨-, hrank, -⟩ := hT u hu
    have h1 := Matrix.rank_le_card_width (Matrix.of fun (a : Fin T.j) (l : Fin (n + (m + 1))) =>
      WilkiesDesign.E.eaEval T.X.c
        (WilkiesDesign.E.eaD T.X.c (Fin.natAdd 0 l) (T.h a)) u)
    rw [hrank] at h1
    simpa using h1
  have hj_ge : n + (m + 1) ≤ T.j := by
    obtain ⟨W, hWgood, hWj, hWset⟩ :=
      exists_good_singleton_stratum (Work.WilE7.CoreStep.pairPtUp u v)
        (pairPtUp_mem_cubeC (absPtInv_mem_cubeC hu) (absPtInv_mem_cubeC hv))
    have hWsub : W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set := by
      rw [hWset]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Work.WilE7.CoreStep.mem_absPairSet T u v hu hv hbase
    have hmem : Work.WilE7.CoreStep.pairPtUp u v ∈ W.X.set := by
      rw [hWset]; exact Set.mem_singleton _
    have h1 := hnolow W hWgood hWsub hmem
    rw [hWj] at h1
    omega
  omega

/-! ### Single-branch covering -/

theorem single_branch_covers {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (hjN : T.j = n + (m + 1))
    (C : Set (Fin n → ℝ))
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T)
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T) :
    ∀ u ∈ T.X.set, WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C →
      ∀ V ∈ nhds (Work.WilE7.CoreStep.absPtInv u),
      ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u)),
        C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
          (Work.WilE7.MainDesign.absSet T ∩ V) := by
  intro u hu hCu V hV
  set η : Fin n → ℝ := WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) with hη
  by_contra hcon
  have hfail : ∀ U ∈ nhds η, ∃ x ∈ C ∩ U,
      x ∉ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V) := by
    intro U hU
    by_contra hh
    refine hcon ⟨U, hU, ?_⟩
    intro x hx
    by_contra hx2
    exact hh ⟨x, hx, hx2⟩
  have hsel : ∀ k : ℕ, ∃ x : Fin n → ℝ, x ∈ C ∩ Metric.ball η ((k : ℝ) + 1)⁻¹ ∧
      x ∉ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T ∩ V) :=
    fun k => hfail _ (Metric.ball_mem_nhds η (by positivity))
  choose x hxmem hxnot using hsel
  have hx_ball : ∀ k : ℕ, dist (x k) η < 1 / ((k : ℝ) + 1) := by
    intro k
    have h := Metric.mem_ball.mp ((hxmem k).2)
    rw [← one_div] at h
    exact h
  have hx_C : ∀ k, x k ∈ C := fun k => (hxmem k).1
  have hx_tendsto : Tendsto x atTop (nhds η) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε := by
      have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : ∀ᶠ n : ℕ in atTop, dist (1 / ((n : ℝ) + 1)) 0 < ε :=
        Filter.eventually_atTop.mpr ((Metric.tendsto_atTop.mp hlim) ε hε)
      filter_upwards [h1] with n hn
      rwa [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at hn
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    exact ⟨N, fun n hn => lt_trans (hx_ball n) (hN n hn)⟩
  have hselz : ∀ k : ℕ, ∃ z : Fin (n + (m + 1)) → ℝ,
      z ∈ Work.WilE7.MainDesign.absSet T ∧
        WilkiesDesign.E.projFirst n (m + 1) z = x k :=
    fun k => hCsub (hx_C k)
  choose z hzA hzπ using hselz
  have hz_notV : ∀ k, z k ∉ V := by
    intro k hzV
    exact hxnot k ⟨z k, ⟨hzA k, hzV⟩, hzπ k⟩
  have hz_cube : ∀ k, z k ∈ WilkiesDesign.E.cubeC (n + (m + 1)) :=
    fun k => absSet_subset_cubeC' T (hzA k)
  obtain ⟨w, _hw_cube, φ, hφmono, hφtend⟩ :=
    (cubeC_isCompact' (n + (m + 1))).tendsto_subseq hz_cube
  have hπw : WilkiesDesign.E.projFirst n (m + 1) w = η := by
    have h1 : Tendsto (fun j => WilkiesDesign.E.projFirst n (m + 1) (z (φ j))) atTop
        (nhds (WilkiesDesign.E.projFirst n (m + 1) w)) :=
      ((continuous_projFirst' n (m + 1)).tendsto w).comp hφtend
    have h2 : Tendsto (fun j => WilkiesDesign.E.projFirst n (m + 1) (z (φ j))) atTop (nhds η) := by
      have h3 : Tendsto (fun j => x (φ j)) atTop (nhds η) :=
        hx_tendsto.comp (hφmono.tendsto_atTop)
      simpa only [hzπ] using h3
    exact tendsto_nhds_unique h1 h2
  have hw_cl : w ∈ closure (Work.WilE7.MainDesign.absSet T) :=
    isClosed_closure.mem_of_tendsto hφtend
      (Filter.Eventually.of_forall (fun j => subset_closure (hzA (φ j))))
  have hw_A : w ∈ Work.WilE7.MainDesign.absSet T :=
    hclosed w hw_cl (by rw [hπw]; exact hCu)
  obtain ⟨Wstar, hWo, hWw, hWiso⟩ := absSet_point_isolated T hT hjN hw_A
  have hev : ∀ᶠ j in atTop, z (φ j) ∈ Wstar := hφtend (hWo.mem_nhds hWw)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  have hzJ : z (φ J) = w := hWiso (z (φ J)) (hJ J le_rfl) (hzA (φ J))
  have hxJ : x (φ J) = η := by rw [← hzπ (φ J), hzJ, hπw]
  refine hxnot (φ J) ?_
  rw [hxJ]
  exact ⟨Work.WilE7.CoreStep.absPtInv u,
    ⟨⟨u, hu, rfl⟩, mem_of_mem_nhds hV⟩, hη.symm⟩

/-! ### The target -/

theorem pairCovers_of_no_lowDim {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)
    (hfin : ∀ x : Fin n → ℝ,
      (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite)
    (C : Set (Fin n → ℝ))
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T)
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (hnolow : ∀ u' v' : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ,
      u' ∈ T.X.set → v' ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u') = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v') = x₀ →
      Work.WilE7.CoreStep.absPtInv u' ≠ Work.WilE7.CoreStep.absPtInv v' →
      ∀ W : WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m), W.Good →
        W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set →
        Work.WilE7.CoreStep.pairPtUp u' v' ∈ W.X.set →
        n + (m + 1) - T.j ≤ Work.WilE7.CoreStep.pPair n m - W.j) :
    ∀ u v : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ, u ∈ T.X.set → v ∈ T.X.set →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) = x₀ →
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) = x₀ →
      Work.WilE7.CoreStep.absPtInv u ≠ Work.WilE7.CoreStep.absPtInv v →
      Work.WilE7.CoreStep.PairCovers T C u v := by
  intro u v hu hv hbase_u hbase_v huv
  have hjN : T.j = n + (m + 1) :=
    card_eq_of_no_lowDim T hT u v hu hv huv (hbase_u.trans hbase_v.symm)
      (fun W hW hWsub hWmem => hnolow u v hu hv hbase_u hbase_v huv W hW hWsub hWmem)
  have hbase_uv : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) =
      WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) :=
    hbase_v.trans hbase_u.symm
  intro V hV V' hV'
  have hCu : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C :=
    hbase_u ▸ hx₀
  have hCv : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv v) ∈ C :=
    hbase_v ▸ hx₀
  obtain ⟨U₁, hU₁, hs₁⟩ := single_branch_covers T hT hjN C hCsub hclosed u hu hCu V hV
  obtain ⟨U₂, hU₂, hs₂⟩ := single_branch_covers T hT hjN C hCsub hclosed v hv hCv V' hV'
  refine ⟨U₁ ∩ U₂, Filter.inter_mem hU₁ (hbase_uv ▸ hU₂), ?_, ?_⟩
  · intro x hx
    exact hs₁ ⟨hx.1, hx.2.1⟩
  · intro x hx
    exact hs₂ ⟨hx.1, hx.2.2⟩

end Work.CoreStep
