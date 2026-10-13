import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.CoreStep.mem_absLevelPairSet_elim
import Submission.Work.CoreStep.persist_aux_pairPtUp_mem
import Submission.Work.WilE7.DimAPI.openMap_of_equalDim
import Submission.Work.WilE7.CoreStep.AttainDichotomy
import Submission.Work.WilE7.CoreStep.ProjTopFrontier
import Submission.Work.WilE7.Endgame.pairAvoid_fst_dim_inj
import Submission.Work.WilE7.Endgame.pairAvoid_witness_limit

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt pairPt projTop_last projTop_castSucc
  projTop_init projFirst_pairPt projSnd_pairPt absPtUp_absPtInv absPtInv_absPtUp)

/-! ## Elementary helpers -/

theorem absPt_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    absPt (pairPtUp u v) = pairPt u v := by
  rw [show pairPtUp u v = Work.WilE7.DimAPI.absPtInv (pPair n m) (pairPt u v) from rfl]
  exact Work.WilE7.DimAPI.absPt_absPtInv _ _

theorem projFirst_absPtPairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    projFirst (n + (m + 1)) (n + (m + 1)) (absPt (pairPtUp u v)) = absPtInv u := by
  rw [absPt_pairPtUp, Work.WilE7.CoreStep.projFirst_pairPt]

theorem projTop_sheet {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    projTop n m (absPt (absPtUp (n := n) (m := m) (Fin.append x y))) =
      Fin.snoc x (y (Fin.last m)) := by
  rw [Work.CoreStep.absPt_absPtUp_append]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [projTop_last, Fin.snoc_last]
    simp only [projSnd]
    exact Fin.append_right x y (Fin.last m)
  · intro i'
    rw [projTop_castSucc, Fin.snoc_castSucc]
    simp only [projFirst]
    exact Fin.append_left x y i'

theorem projFirst_sheet {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    projFirst n (m + 1) (absPt (absPtUp (n := n) (m := m) (Fin.append x y))) = x := by
  rw [Work.CoreStep.absPt_absPtUp_append]
  funext i
  exact Fin.append_left x y i

theorem pairBaseFst_absPt_pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    Work.CoreStep.pairBaseFst n m (absPt (pairPtUp u v)) = projFirst n (m + 1) (absPtInv u) := by
  rw [show Work.CoreStep.pairBaseFst n m (absPt (pairPtUp u v))
      = projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1))
          (absPt (pairPtUp u v))) from by
        funext i; exact congrArg _ (Fin.ext rfl)]
  rw [Work.CoreStep.Cross_absPt_pairPtUp,
    show projFirst (n + (m + 1)) (n + (m + 1))
        (Fin.append (absPt u) (absPt v)) = absPt u from funext fun i => Fin.append_left _ _ i]

/-- **Openness**: if the level `ℓ j` is attained at `x₀ ∈ C`, it is attained near `x₀` in `C`. -/
theorem attain_eventually_attain {n m k : ℕ}
    (S T : Stratum 0 (n + (m + 1))) (hS : S.Good) (hT : T.Good) (himm : HImm T)
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ S.X.set)
    (Vl : List (Stratum 0 (pPair n m)))
    (hVgood : ∀ V ∈ Vl, V.Good)
    (hVsub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet S T).set)
    (hVcov : (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set)
    (hlow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C)
    (j : Fin k) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (hAtt : AttainAt T (fun y => (s j y) (Fin.last m)) x₀) :
    ∀ᶠ x in 𝓝[C] x₀, AttainAt T (fun y => (s j y) (Fin.last m)) x := by
  classical
  obtain ⟨v₀, hv₀, hv₀eq⟩ := hAtt
  set u₀ : Fin (pDim n m) → ℝ := absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)) with hu₀
  have hu₀S : u₀ ∈ S.X.set := hsub j x₀ hx₀
  set p₀ : Fin (0 + pPair n m) → ℝ := pairPtUp u₀ v₀ with hp₀
  -- membership of the witness pair point
  have hpmem : p₀ ∈ (absLevelPairSet S T).set := by
    rw [hp₀]
    refine Work.CoreStep.mem_absLevelPairSet S T u₀ v₀ hu₀S hv₀ ?_ ?_
    · rw [hu₀, Work.CoreStep.projFirst_absPtInv_absPtUp_append]
      rw [show absPtInv v₀ = absPt v₀ from rfl, ← projTop_init n m (absPt v₀), hv₀eq, Fin.init_snoc]
    · rw [hu₀, Work.CoreStep.projSnd_absPtInv_absPtUp_append]
      rw [show (projSnd n (m + 1) (absPtInv v₀)) ⟨m, by omega⟩
          = projTop n m (absPtInv v₀) (Fin.last n) from (projTop_last n m (absPtInv v₀)).symm]
      rw [show absPtInv v₀ = absPt v₀ from rfl, hv₀eq, Fin.snoc_last]
  -- the stratum containing it
  have hpcov : p₀ ∈ ⋃ V ∈ Vl, V.X.set := by rw [← hVcov]; exact hpmem
  obtain ⟨V, hVmem, hp₀V⟩ := Set.mem_iUnion₂.mp hpcov
  have hVg : V.Good := hVgood V hVmem
  have hVsub' : V.X.set ⊆ (absLevelPairSet S T).set := hVsub V hVmem
  -- base of the witness pair point
  have hp₀base : Work.CoreStep.pairBaseFst n m (absPt p₀) = x₀ := by
    rw [hp₀, pairBaseFst_absPt_pairPtUp, hu₀,
      Work.CoreStep.projFirst_absPtInv_absPtUp_append]
  -- the stratum is not low, hence top
  have hnotlow : ¬ (pPair n m - V.j < n + (m + 1) - S.j) := by
    intro hlt
    have hdisj := hlow V hVmem hlt
    have hxmem : x₀ ∈ Work.CoreStep.pairSubBaseFst n m V :=
      ⟨absPt p₀, ⟨p₀, hp₀V, rfl⟩, hp₀base⟩
    exact (Set.disjoint_left.mp hdisj) hxmem hx₀
  have htop : pPair n m - V.j = n + (m + 1) - S.j := by
    have hle := (pairAvoid_fst_dim_inj S T hS hT himm V hVg hVsub' p₀ hp₀V).1
    omega
  -- the first-block projection
  set L : (Fin (pPair n m) → ℝ) →ₗ[ℝ] (Fin (n + (m + 1)) → ℝ) :=
    (Work.CoreStep.projFirstCLM (n + (m + 1))).toLinearMap with hL
  have hLapp : ∀ z : Fin (pPair n m) → ℝ,
      L z = projFirst (n + (m + 1)) (n + (m + 1)) z := fun z => rfl
  have hmap : ⇑L '' absSet V ⊆ absSet S := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨zz, hzz, rfl⟩ := hz
    have h := (Work.CoreStep.mem_absLevelPairSet_elim S T (hVsub' hzz)).1
    rwa [hLapp]
  have hinj : ∀ z ∈ V.X.set, ∀ v ∈ (jac V z).ker, L (absPt v) = 0 → v = 0 := by
    intro z hz v hv hv0
    have h2 := (pairAvoid_fst_dim_inj S T hS hT himm V hVg hVsub' z hz).2 v hv
    apply h2
    rwa [hLapp] at hv0
  have hOM := Work.WilE7.DimAPI.openMap_of_equalDim S V hS hVg L hmap hinj htop p₀ hp₀V
    Set.univ Filter.univ_mem
  have hLp₀ : L (absPt p₀) = Fin.append x₀ (s j x₀) := by
    rw [hLapp, hp₀, Work.CoreStep.Cross_absPt_pairPtUp,
      show projFirst (n + (m + 1)) (n + (m + 1))
          (Fin.append (absPt u₀) (absPt v₀)) = absPt u₀ from funext fun i => Fin.append_left _ _ i,
      hu₀, Work.CoreStep.absPt_absPtUp_append]
  have hOM' : ∀ᶠ w in 𝓝 (Fin.append x₀ (s j x₀)), w ∈ absSet S → w ∈ ⇑L '' absSet V := by
    rw [hLp₀] at hOM
    simpa using hOM
  -- pull back along the sheet map
  have hcontg : ContinuousOn (fun x : Fin n → ℝ => Fin.append x (s j x)) C := by
    have h1 : ContinuousOn (fun x : Fin n → ℝ => (x, s j x)) C :=
      continuousOn_id.prodMk (hcont j)
    have h2 : ContinuousOn (fun p : (Fin n → ℝ) × (Fin (m + 1) → ℝ) =>
        Work.WilE9.Ift.appendCLM n (m + 1) p) Set.univ :=
      (Work.WilE9.Ift.appendCLM n (m + 1)).continuous.continuousOn
    have hcomp : ContinuousOn (fun x : Fin n → ℝ =>
        Work.WilE9.Ift.appendCLM n (m + 1) (x, s j x)) C :=
      h2.comp h1 (fun x _ => Set.mem_univ _)
    simpa [Function.comp_def, Work.WilE9.Ift.appendCLM_apply] using hcomp
  refine (show ∀ᶠ x in 𝓝[C] x₀,
      (fun x : Fin n → ℝ => Fin.append x (s j x)) x ∈ ⇑L '' absSet V from ?_).mono ?_
  · have htend : Tendsto (fun x : Fin n → ℝ => Fin.append x (s j x)) (𝓝[C] x₀)
        (𝓝 (Fin.append x₀ (s j x₀))) := hcontg.continuousWithinAt hx₀
    filter_upwards [htend.eventually hOM', self_mem_nhdsWithin] with x hx hxC
    exact hx (by
      have hmem : absPt (absPtUp (n := n) (m := m) (Fin.append x (s j x))) ∈ absSet S :=
        ⟨_, hsub j x hxC, rfl⟩
      rwa [Work.CoreStep.absPt_absPtUp_append] at hmem)
  · rintro x hx
    obtain ⟨w, hw, hwL⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hw
    obtain ⟨hfirst, hsecond, hbaseeq, hleveq, -⟩ :=
      Work.CoreStep.mem_absLevelPairSet_elim S T (hVsub' hz)
    have hbf : Work.CoreStep.blockFirstCLM n m z
        = absPtUp (n := n) (m := m) (Fin.append x (s j x)) := by
      apply Work.WilE7.DimAPI.absPt_injective (n + (m + 1))
      rw [Work.CoreStep.absPt_blockFirstCLM, Work.CoreStep.absPt_absPtUp_append, ← hLapp]
      exact hwL
    refine ⟨Work.CoreStep.blockSndCLM n m z, ?_, ?_⟩
    · have hw : absPt (Work.CoreStep.blockSndCLM n m z) ∈ absSet T := by
        rw [Work.CoreStep.absPt_blockSndCLM]; exact hsecond
      have hmem := (Work.CoreStep.mem_absSet_iff T (absPt (Work.CoreStep.blockSndCLM n m z))).mp hw
      rwa [Work.WilE7.DimAPI.absPtInv_absPt] at hmem
    · rw [Work.CoreStep.absPt_blockSndCLM]
      have hswap : projTop n m (projSnd (n + (m + 1)) (n + (m + 1)) (absPt z))
          = projTop n m (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z)) := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · rw [projTop_last, projTop_last]; exact hleveq.symm
        · intro i'
          rw [projTop_castSucc, projTop_castSucc]
          exact (congrFun hbaseeq i').symm
      rw [hswap, ← Work.CoreStep.absPt_blockFirstCLM, hbf]
      exact projTop_sheet x (s j x)


/-- **Closedness**: if the level `ℓ j` is not attained at `x₀ ∈ C`, it is not attained near `x₀` in `C`. -/
theorem attain_eventually_not_attain {n m k : ℕ}
    (S T : Stratum 0 (n + (m + 1))) (hS : S.Good) (hT : T.Good) (himm : HImm T)
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ S.X.set)
    (Vl : List (Stratum 0 (pPair n m)))
    (hVgood : ∀ V ∈ Vl, V.Good)
    (hVsub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet S T).set)
    (hVcov : (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set)
    (hbound : ∀ V ∈ Vl, ∀ z ∈ V.X.set, pPair n m - V.j ≤ n + (m + 1) - S.j)
    (hlow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C)
    (htop : ∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairFrontierBaseFst n m V) C)
    (j : Fin k) :
    ∀ x₀ ∈ C, ¬ AttainAt T (fun y => (s j y) (Fin.last m)) x₀ →
      ∀ᶠ x in 𝓝[C] x₀, ¬ AttainAt T (fun y => (s j y) (Fin.last m)) x := by
  intro x₀ hx₀ hx₀not
  rw [eventually_nhdsWithin_iff]
  by_contra hcon
  have hfail : ∀ U ∈ 𝓝 x₀, ∃ x ∈ U, x ∈ C ∧ AttainAt T (fun y => (s j y) (Fin.last m)) x := by
    intro U hU
    by_contra hh
    refine hcon (Filter.mem_of_superset hU ?_)
    intro x hx
    simp only [Set.mem_ofPred_eq]
    intro hxC hxAtt
    exact hh ⟨x, hx, ⟨hxC, hxAtt⟩⟩
  have hsel : ∀ t : ℕ, ∃ x : Fin n → ℝ,
      dist x x₀ < ((t : ℝ) + 1)⁻¹ ∧ x ∈ C ∧ AttainAt T (fun y => (s j y) (Fin.last m)) x := by
    intro t
    obtain ⟨x, hxball, hx⟩ := hfail (Metric.ball x₀ ((t : ℝ) + 1)⁻¹)
      (Metric.ball_mem_nhds x₀ (by positivity))
    exact ⟨x, Metric.mem_ball.mp hxball, hx⟩
  choose x hxball hxC hxAtt using hsel
  have hx_tend : Tendsto x atTop (𝓝 x₀) := by
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
    refine ⟨K, fun t ht => ?_⟩
    have h1 : dist (x t) x₀ < ((t : ℝ) + 1)⁻¹ := hxball t
    have h1' : dist (x t) x₀ < 1 / ((t : ℝ) + 1) := by simpa only [one_div] using h1
    have h2 : 1 / ((t : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ ht)
    exact lt_of_lt_of_le (h1'.trans_le h2) (le_of_lt hK)
  exact hx₀not (pairAvoid_witness_limit S T hS hT himm C s hcont hsub Vl hVgood hVsub hVcov hbound
    hlow htop j x₀ hx₀ x hxC hx_tend hxAtt)

/-- **The target theorem.** -/
theorem attain_dichotomy_of_pairAvoid {n m k : ℕ}
    (S T : Stratum 0 (n + (m + 1))) (hS : S.Good) (hT : T.Good) (himm : HImm T)
    (C : Set (Fin n → ℝ)) (hCpc : IsPreconnected C)
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ S.X.set)
    (Vl : List (Stratum 0 (pPair n m)))
    (hVgood : ∀ V ∈ Vl, V.Good)
    (hVsub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet S T).set)
    (hVcov : (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set)
    (hlow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C)
    (htop : ∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairFrontierBaseFst n m V) C)
    (j : Fin k) :
    (∀ x ∈ C, AttainAt T (fun y => (s j y) (Fin.last m)) x) ∨
      (∀ x ∈ C, ¬ AttainAt T (fun y => (s j y) (Fin.last m)) x) := by
  classical
  set ℓ : (Fin n → ℝ) → ℝ := fun y => (s j y) (Fin.last m) with hℓ
  have hbound : ∀ V ∈ Vl, ∀ z ∈ V.X.set, pPair n m - V.j ≤ n + (m + 1) - S.j :=
    fun V hV z hz => (pairAvoid_fst_dim_inj S T hS hT himm V (hVgood V hV) (hVsub V hV) z hz).1
  have hAopen : IsOpen (Work.WilE7.CoreStep.AttainSub T C ℓ) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hy' : AttainAt T (fun y => (s j y) (Fin.last m)) (y : Fin n → ℝ) := by
      rwa [hℓ] at hy
    have h1 : {x : Fin n → ℝ | AttainAt T (fun y => (s j y) (Fin.last m)) x} ∈ 𝓝[C] (y : Fin n → ℝ) :=
      attain_eventually_attain S T hS hT himm C s hcont hsub Vl hVgood hVsub hVcov hlow j y y.2 hy'
    obtain ⟨t, ht, htsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h1
    rw [nhds_subtype]
    exact Filter.mem_comap.mpr ⟨t, ht, fun z hz => htsub ⟨hz, z.2⟩⟩
  have hAclosed : IsClosed (Work.WilE7.CoreStep.AttainSub T C ℓ) := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hy' : ¬ AttainAt T (fun y => (s j y) (Fin.last m)) (y : Fin n → ℝ) := by
      rwa [hℓ] at hy
    have h1 : {x : Fin n → ℝ | ¬ AttainAt T (fun y => (s j y) (Fin.last m)) x} ∈ 𝓝[C] (y : Fin n → ℝ) :=
      attain_eventually_not_attain S T hS hT himm C s hcont hsub Vl hVgood hVsub hVcov hbound
        hlow htop j y y.2 hy'
    obtain ⟨t, ht, htsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h1
    rw [nhds_subtype]
    exact Filter.mem_comap.mpr ⟨t, ht, fun z hz => htsub ⟨hz, z.2⟩⟩
  have huniv : IsPreconnected (Set.univ : Set ↥C) :=
    (Subtype.preconnectedSpace hCpc).isPreconnected_univ
  rcases huniv.subset_or_subset hAopen hAclosed.isOpen_compl disjoint_compl_right
      (fun z _ => (Classical.em (z ∈ Work.WilE7.CoreStep.AttainSub T C ℓ)).elim Or.inl
        (fun h => Or.inr (by simpa using h))) with h | h
  · left
    intro x hx
    exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))
  · right
    intro x hx
    exact h (Set.mem_univ (⟨x, hx⟩ : ↥C))

end Work.WilE7.Endgame
