import Mathlib
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Whitney.Signed.KronAdj
import Submission.Work.Whitney.capTransferPrep
import Submission.Work.Whitney.exists_ballChain
import Submission.Work.Whitney.exists_cone_chain
import Submission.Work.Whitney.lowerCap
import Submission.Work.Whitney.sdIter_isSmallChain_of_AC
import Submission.Work.Whitney.ballPairDegreeOne
import Submission.Work.Whitney.capCycle
import Submission.Work.Cohomology.exists_sub_small_of_boundary_small
import Submission.Work.Cohomology.smallChains_homology_iso_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Whitney.RankOneFiller

open Work.Thom Work.Cohomology

noncomputable section

/-!
# Filler data for the suspension rule (`exists_filler_data`)

The statement (`Work.Whitney.RankOneFiller.exists_filler_data`) demands, for every `k ≥ 1` and every
one-point base `Y`, chains `B, L, Z` with

* `B` a `k`-chain of `Y × Dᵏ` whose boundary is carried by the sphere bundle `DiscB Y k` and which
  represents the relative fundamental class (its pairing with a representative of the model class
  `stepDisc Y k (Mn k Y)` is nonzero);
* `L` a `k`-chain of `X = tcmX Y k 1` carried by the pair `(tcmA, LowerOpenTcm)`;
* `Z` a `(k+1)`-chain with `∂Z = cap_* B + L`, whose boundary is carried by `(tcmA, tcmC)`.

## The construction

`B₀` is produced by `Work.Whitney.exists_ballChain`.  The only extra property `B` needs is that
each of its simplices is either contained in the "first coordinate nonzero" part or in the interior
of the disc; that is what makes the cap image of `B` (and of its lower mirror) carried by the
*unions* `A ∪ C` of the rank-one model product, so that the geometric boundary shape of `Z` is
`(tcmA, tcmC)`-small.  Such a chain is obtained without touching the pairing by
`Work.Cohomology.exists_sub_small_of_boundary_small`: an open cover `Y × Dᵏ = U ∪ V` and a chain
whose *boundary* is small give a chain differing from it by a boundary which *is* `(U,V)`-small.

The lower chain is the **negated lower cap** `L = -lcap_* B`: its boundary is `-∂(cap_* B)` because
the two caps agree on the sphere (`Work.Whitney.capX_eq_lowerCapX_of_mem_discB`), so that
`cap_* B - lcap_* B` is a cycle (`Work.Whitney.capX_sub_lowerCapX_cycle`) and the ambient space
`tcmX Y k 1 ≅ ℝᵏ⁺¹` is contractible, giving `Z` with `∂Z = cap_* B + L`
(`Work.Whitney.exists_cone_chain`).
-/

/-- The part `{u ≠ 0}` of the disc bundle: the preimage of `Work.Whitney.tcmA Y k 1` under the
upper cap (and under the lower cap). -/
def discSmallU (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set (Y × MBall k) :=
  {x | x.2.1 ≠ 0}

/-- The interior part `{‖u‖ < 1}` of the disc bundle: the preimage of `Work.Whitney.tcmC Y k 1`
under the upper cap, and of `Work.Whitney.LowerOpenTcm Y k` under the lower cap. -/
def discSmallV (Y : Type) [TopologicalSpace Y] (k : ℕ) : Set (Y × MBall k) :=
  {x | ‖x.2.1‖ < 1}

theorem isOpen_discSmallU (Y : Type) [TopologicalSpace Y] (k : ℕ) : IsOpen (discSmallU Y k) := by
  have h : discSmallU Y k
      = (fun x : Y × MBall k => (x.2 : EuclideanSpace ℝ (Fin k))) ⁻¹' {v | v ≠ 0} := rfl
  rw [h]
  exact isOpen_compl_singleton.preimage (continuous_subtype_val.comp continuous_snd)

theorem isOpen_discSmallV (Y : Type) [TopologicalSpace Y] (k : ℕ) : IsOpen (discSmallV Y k) := by
  have h : discSmallV Y k
      = (fun x : Y × MBall k => ‖(x.2 : EuclideanSpace ℝ (Fin k))‖) ⁻¹' Set.Iio 1 := rfl
  rw [h]
  exact isOpen_Iio.preimage (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))

theorem discSmall_union_eq_univ (Y : Type) [TopologicalSpace Y] (k : ℕ) :
    discSmallU Y k ∪ discSmallV Y k = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, discSmallU, discSmallV, Set.mem_ofPred_eq]
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x.2.1 = 0
    · right; rw [h, norm_zero]; norm_num
    · left; exact h

/-- **Push-forwards of a small chain are small**, with the two covering sets of the source mapped
into the two covering sets of the target.  (The `(U,∅)` case is
`Work.Whitney.pushChain_isSmallChain_of_mem`.) -/
theorem pushChain_isSmallChain_of_mem_pair {X Z : TopCat} (g : X ⟶ Z) {U U' : Set X}
    {V V' : Set Z} (hUV : ∀ x, x ∈ U → g x ∈ V) (hU'V' : ∀ x, x ∈ U' → g x ∈ V') {n : ℕ}
    (c : (singularChains ℤ X).X n) (hc : IsSmallChain U U' c) :
    IsSmallChain V V' (pushChain X Z g n c) := by
  obtain ⟨c', rfl⟩ := hc
  refine isSmallChain_of_gen (Y := smallSSet U U') (n := n)
    ((smallToSing U U').f n ≫ pushChainHom X Z g n) ?_ c'
  intro σ
  obtain ⟨σ₁, hσ₁⟩ := σ
  have hσ₁' : IsSmall U U' σ₁ := hσ₁
  rw [isSmall_iff] at hσ₁'
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, smallToSing_gen]
  show IsSmallChain V V' (pushChain X Z g n (gen X n σ₁))
  rw [pushChain_gen]
  apply isSmallChain_gen
  rw [isSmall_iff]
  rcases hσ₁' with h | h
  · left
    rw [sdMap_map X Z g n σ₁]
    rintro y ⟨z, rfl⟩
    exact hUV _ (h ⟨z, rfl⟩)
  · right
    rw [sdMap_map X Z g n σ₁]
    rintro y ⟨z, rfl⟩
    exact hU'V' _ (h ⟨z, rfl⟩)

/-- The first `k` coordinates of the lower cap are the disc coordinates. -/
theorem lowerCapX_fst (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k) :
    (lowerCapX Y k q).2.1 = q.2.1 := by
  rw [lowerCapX_apply]
  ext i
  rw [tcmSumLin_symm_fst_coord]
  have hidx : finSumFinEquiv (Sum.inl i) = Fin.castSucc i := Fin.ext rfl
  rw [hidx, lowerCapMap_castSucc]

/-- The second component of `tcmSumLin`'s inverse, on coordinates. -/
theorem tcmSumLin_symm_snd (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin 1) :
    ((tcmSumLin k 1).symm v).2 j = v (finSumFinEquiv (Sum.inr j)) :=
  Work.Thom.finAddEquivProd_snd (𝕜 := ℝ) (n := k) (m := 1) v j

theorem finSumFinEquiv_inr_zero (k : ℕ) :
    finSumFinEquiv (Sum.inr (0 : Fin 1)) = Fin.last k := by
  rw [finSumFinEquiv_apply_right]
  exact Fin.ext rfl

/-- **Linearity of the Kronecker pairing in the chain**: the difference rule. -/
theorem kron_sub_chain (X : SSet) {n : ℕ} (α : Cochain ℤ X n)
    (x y : ↑((X.chainComplex (ModuleCat.of ℤ ℤ)).X n)) :
    kronecker ℤ X α (x - y) = kronecker ℤ X α x - kronecker ℤ X α y :=
  map_sub α x y

/-- The upper cap lands in `tcmC` over the interior of the disc. -/
theorem capX_snd_ne_zero (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k)
    (hq : ‖q.2.1‖ < 1) : (capX Y k q).2.2 ≠ 0 := by
  intro h0
  have h1 : (capX Y k q).2.2 0 = 0 := by rw [h0]; simp
  have h2 : (capX Y k q).2.2 0 = Real.sqrt (1 - ‖q.2.1‖ ^ 2) := by
    rw [capX_apply, tcmSumLin_symm_snd, finSumFinEquiv_inr_zero, capMap_last]
  rw [h2] at h1
  have hpos : 0 < 1 - ‖q.2.1‖ ^ 2 := by
    have hnn := norm_nonneg q.2.1
    nlinarith
  have := Real.sqrt_pos.mpr hpos
  linarith

/-- The lower cap lands in `tcmC` over the interior of the disc. -/
theorem lowerCapX_snd_ne_zero (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k)
    (hq : ‖q.2.1‖ < 1) : (lowerCapX Y k q).2.2 ≠ 0 := by
  intro h0
  have h1 : (lowerCapX Y k q).2.2 0 = 0 := by rw [h0]; simp
  have h2 : (lowerCapX Y k q).2.2 0 = -Real.sqrt (1 - ‖q.2.1‖ ^ 2) := by
    rw [lowerCapX_apply, tcmSumLin_symm_snd, finSumFinEquiv_inr_zero, lowerCapMap_last]
  rw [h2] at h1
  have hpos : 0 < 1 - ‖q.2.1‖ ^ 2 := by
    have hnn := norm_nonneg q.2.1
    nlinarith
  have := Real.sqrt_pos.mpr hpos
  linarith

/-- The lower cap lands in the open lower hemisphere over the interior of the disc. -/
theorem lowerCapX_lastCoord_neg (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k)
    (hq : ‖q.2.1‖ < 1) : lastCoord Y k (lowerCapX Y k q) < 0 := by
  have h : lastCoord Y k (lowerCapX Y k q) = -Real.sqrt (1 - ‖q.2.1‖ ^ 2) := by
    simp only [lastCoord, lowerCapX_apply, ContinuousLinearEquiv.apply_symm_apply,
      lowerCapMap_last]
  rw [h]
  have hpos : 0 < 1 - ‖q.2.1‖ ^ 2 := by
    have hnn := norm_nonneg q.2.1
    nlinarith
  have := Real.sqrt_pos.mpr hpos
  linarith

theorem fillerData (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ (B : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall k))).X k)
      (L : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).X k)
      (Z : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).X (k + 1)),
      Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y k) (∅ : Set (Y × Work.Thom.MBall k))
        ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall k))).d k (k - 1) B)
      ∧ Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y k 1)
          (Work.Whitney.LowerOpenTcm Y k) L
      ∧ Work.Cohomology.IsSmallChain
          {x : Work.Whitney.tcmX Y k 1 | (Work.Whitney.tcmF Y k 1 x).2 ∈ Work.Thom.mLower k}
          (∅ : Set (Work.Whitney.tcmX Y k 1)) L
      ∧ (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).d (k + 1) k Z
          = Work.Cohomology.pushChain (TopCat.of (Y × Work.Thom.MBall k))
              (TopCat.of (Work.Whitney.tcmX Y k 1)) (TopCat.ofHom (Work.Whitney.capX Y k)) k B + L
      ∧ Work.Cohomology.IsSmallChain (Work.Whitney.tcmA Y k 1) (Work.Whitney.tcmC Y k 1)
          ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y k 1))).d (k + 1) k Z)
      ∧ (∃ (b : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MBall k))
              (Work.Thom.DiscB Y k) k)),
          (∃ (hb : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MBall k))
              (Work.Thom.DiscB Y k) k b = 0),
            Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MBall k)) (Work.Thom.DiscB Y k)
                b hb = Work.Thom.stepDisc Y k (Work.Thom.Mn k Y)
              ∧ Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall k)) b.1 B ≠ 0)) := by
  classical
  -- Step 1: the ball chain of the disc pair.
  obtain ⟨B₀, hB₀sm, hB₀pair⟩ := Work.Whitney.exists_ballChain Y k hk
  -- Step 2: replace `B₀` by a chain that is small for the source cover, without changing the
  -- pairings with cocycles.
  have hcov : discSmallU Y k ∪ discSmallV Y k = Set.univ := discSmall_union_eq_univ Y k
  have hdiscU : DiscB Y k ⊆ discSmallU Y k := by
    intro x hx h0
    have h1 : ‖x.2.1‖ = 1 := hx
    rw [h0, norm_zero] at h1
    norm_num at h1
  have hsm' : IsSmallChain (discSmallU Y k) (discSmallV Y k)
      ((singularChains ℤ (TopCat.of (Y × MBall k))).d k (k - 1) B₀) :=
    IsSmallChain.mono_of_subset hdiscU (Set.empty_subset _) hB₀sm
  obtain ⟨c₀, hc₀⟩ := exists_sub_small_of_boundary_small
    (X := TopCat.of (Y × MBall k)) (discSmallU Y k) (discSmallV Y k)
    (isOpen_discSmallU Y k) (isOpen_discSmallV Y k) hcov k B₀ hsm'
  set Bc := B₀ - (singularChains ℤ (TopCat.of (Y × MBall k))).d (k + 1) k c₀ with hBc
  have hBsmall : IsSmallChain (discSmallU Y k) (discSmallV Y k) Bc := by
    rw [hBc]; exact hc₀
  -- Step 3: the boundary of `Bc` agrees with that of `B₀`.
  have hdd : (singularChains ℤ (TopCat.of (Y × MBall k))).d k (k - 1)
      ((singularChains ℤ (TopCat.of (Y × MBall k))).d (k + 1) k c₀) = 0 := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of (Y × MBall k))).X (k + 1) ⟶
        (singularChains ℤ (TopCat.of (Y × MBall k))).X (k - 1)) => g.hom c₀)
      (HomologicalComplex.d_comp_d (singularChains ℤ (TopCat.of (Y × MBall k))) (k + 1) k (k - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hBbound : IsSmallChain (DiscB Y k) (∅ : Set (Y × MBall k))
      ((singularChains ℤ (TopCat.of (Y × MBall k))).d k (k - 1) Bc) := by
    rw [hBc, map_sub, hdd, sub_zero]
    exact hB₀sm
  -- Step 4: the pointwise transport of the source cover through the two caps.
  have hcapA : ∀ x, x ∈ discSmallU Y k → capX Y k x ∈ tcmA Y k 1 := by
    intro x hx
    show (capX Y k x).2.1 ≠ 0
    rw [capX_fst]; exact hx
  have hcapC : ∀ x, x ∈ discSmallV Y k → capX Y k x ∈ tcmC Y k 1 :=
    fun x hx => capX_snd_ne_zero Y k x hx
  have hlcapA : ∀ x, x ∈ discSmallU Y k → lowerCapX Y k x ∈ tcmA Y k 1 := by
    intro x hx
    show (lowerCapX Y k x).2.1 ≠ 0
    rw [lowerCapX_fst]; exact hx
  have hlcapO : ∀ x, x ∈ discSmallV Y k → lowerCapX Y k x ∈ LowerOpenTcm Y k :=
    fun x hx => lowerCapX_lastCoord_neg Y k x hx
  have hlcapC : ∀ x, x ∈ discSmallV Y k → lowerCapX Y k x ∈ tcmC Y k 1 :=
    fun x hx => lowerCapX_snd_ne_zero Y k x hx
  -- Step 5: smallness of the two cap push-forwards.
  have hUsmall : IsSmallChain (tcmA Y k 1) (tcmC Y k 1)
      (pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
        (TopCat.ofHom (capX Y k)) k Bc) :=
    pushChain_isSmallChain_of_mem_pair (TopCat.ofHom (capX Y k)) hcapA hcapC Bc hBsmall
  have hLsmall : IsSmallChain (tcmA Y k 1) (LowerOpenTcm Y k)
      (-pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
        (TopCat.ofHom (lowerCapX Y k)) k Bc) :=
    IsSmallChain.neg (pushChain_isSmallChain_of_mem_pair (TopCat.ofHom (lowerCapX Y k))
      hlcapA hlcapO Bc hBsmall)
  have hLsmallC : IsSmallChain (tcmA Y k 1) (tcmC Y k 1)
      (-pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
        (TopCat.ofHom (lowerCapX Y k)) k Bc) :=
    IsSmallChain.neg (pushChain_isSmallChain_of_mem_pair (TopCat.ofHom (lowerCapX Y k))
      hlcapA hlcapC Bc hBsmall)
  -- Step 6: the cycle `W = cap_* Bc - lcap_* Bc` and its filler.
  set W := pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
      (TopCat.ofHom (capX Y k)) k Bc
    - pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
        (TopCat.ofHom (lowerCapX Y k)) k Bc with hW
  have hcycle : (singularChains ℤ (TopCat.of (tcmX Y k 1))).d k (k - 1) W = 0 := by
    rw [hW]; exact Work.Whitney.capX_sub_lowerCapX_cycle Y k Bc hBbound
  have hSphU : Set.range (TopCat.ofHom (capX Y k))
      ⊆ {x : tcmX Y k 1 | tcmF Y k 1 x ∈ Sph Y (k + 1)} := by
    rintro p ⟨q, rfl⟩
    exact tcmF_capX_mem_Sph Y k q
  have hSphL : Set.range (TopCat.ofHom (lowerCapX Y k))
      ⊆ {x : tcmX Y k 1 | tcmF Y k 1 x ∈ Sph Y (k + 1)} := by
    rintro p ⟨q, rfl⟩
    exact (tcmF_lowerCapX_mem_mLower Y k q).1
  have hWsmall : IsSmallChain {x : tcmX Y k 1 | tcmF Y k 1 x ∈ Sph Y (k + 1)}
      (∅ : Set (tcmX Y k 1)) W := by
    rw [hW]
    exact IsSmallChain.sub
      (pushChain_isSmallChain (TopCat.ofHom (capX Y k)) (Or.inl hSphU) Bc)
      (pushChain_isSmallChain (TopCat.ofHom (lowerCapX Y k)) (Or.inl hSphL) Bc)
  obtain ⟨Zc, hZc⟩ := Work.Whitney.exists_cone_chain Y k hk W hcycle hWsmall
  set Lc := -pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
      (TopCat.ofHom (lowerCapX Y k)) k Bc with hLc
  -- Step 7: the pairing of `Bc` with a representative of the model class.
  obtain ⟨b, hb, hbl⟩ := Work.Cohomology.exists_relClassOf ℤ (TopCat.of (Y × MBall k))
    (DiscB Y k) k (stepDisc Y k (Mn k Y))
  have hpairB₀ : kronecker ℤ (ssB (Y × MBall k)) b.1 B₀ ≠ 0 := hB₀pair b hb hbl
  have hcoch : cochainDiff ℤ (ssB (Y × MBall k)) b.1 = 0 :=
    relClassOf_cochainDiff ℤ (TopCat.of (Y × MBall k)) (DiscB Y k) b hb
  have hpair : kronecker ℤ (ssB (Y × MBall k)) b.1 Bc ≠ 0 := by
    have hzero : kronecker ℤ (ssB (Y × MBall k)) b.1
        ((singularChains ℤ (TopCat.of (Y × MBall k))).d (k + 1) k c₀) = 0 :=
      kronecker_cocycle_boundary ℤ (ssB (Y × MBall k)) b.1 hcoch c₀
    have heq : kronecker ℤ (ssB (Y × MBall k)) b.1 Bc
        = kronecker ℤ (ssB (Y × MBall k)) b.1 B₀ := by
      rw [hBc, kron_sub_chain (ssB (Y × MBall k)) b.1 B₀
          ((singularChains ℤ (TopCat.of (Y × MBall k))).d (k + 1) k c₀), hzero, sub_zero]
    rw [heq]
    exact hpairB₀
  refine ⟨Bc, Lc, Zc, hBbound, ?_, ?_, ?_, ?_, b, hb, hbl, hpair⟩
  · rw [hLc]; exact hLsmall
  · rw [hLc]
    refine IsSmallChain.neg ?_
    refine Work.Whitney.isSmallChain_pushChain_of_image (TopCat.ofHom (lowerCapX Y k))
      {x : tcmX Y k 1 | (tcmF Y k 1 x).2 ∈ mLower k} ?_ k Bc
    intro q
    exact tcmF_lowerCapX_mem_mLower Y k q
  · rw [hZc, hW, hLc]; abel
  · rw [show (singularChains ℤ (TopCat.of (tcmX Y k 1))).d (k + 1) k Zc
        = pushChain (TopCat.of (Y × MBall k)) (TopCat.of (tcmX Y k 1))
            (TopCat.ofHom (capX Y k)) k Bc + Lc from by rw [hZc, hW, hLc]; abel]
    exact IsSmallChain.add hUsmall hLsmallC

end

end Work.Whitney.RankOneFiller
