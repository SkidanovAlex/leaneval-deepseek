import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

namespace Work.Drive.Whitney

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory

noncomputable section

/-! ## The parametrisation of the injectivity-bad parameters

`discBump_sep` says that for two distinct points `p, q` of the open square the four-tuple
`k ↦ discBump k` separates them: some `k₀` has `discBump k₀ p ≠ discBump k₀ q`.  On the piece of
`discSq × discSq` where `discBump k₀ p ≠ discBump k₀ q`, the equation `discMap v p = discMap v q`
can be solved for the `k₀`-block of `v`: the other three blocks determine `v k₀`.  Hence
`badInj` is contained in the union over the four indices `k₀` of the image of the map
`(p, q, w) ↦ v`, whose source has finrank `2 + 2 + 3 * (2 * n) = 6 * n + 4`. -/

/-- The source of the parametrisation attached to the index `k₀`: the pair `(p, q)` of points of
the open square together with the three blocks of `v` other than the block `k₀`. -/
abbrev discInjSrc (n : ℕ) (k₀ : Fin 2 × Fin 2) : Type :=
  (ℝ × ℝ) × (ℝ × ℝ) × ({k : Fin 2 × Fin 2 // k ≠ k₀} → EuclideanSpace ℝ (Fin (2 * n)))

/-- The target of the parametrisation: the space of translation parameters. -/
abbrev discInjTgt (n : ℕ) : Type := (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))

/-- Given `(p, q, w)`, the parameter `v` whose `k₀`-block solves `discMap v p = discMap v q` and
whose other blocks are the prescribed `w`. -/
def discInjParamBlock {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (γ₁ γ₂ : ℝ → M) (k₀ : Fin 2 × Fin 2) :
    discInjSrc n k₀ → discInjTgt n :=
  fun x k => if h : k = k₀ then
      (discBump k₀ x.1 - discBump k₀ x.2.1)⁻¹ •
        ((baseDisc f γ₁ γ₂ x.2.1 - baseDisc f γ₁ γ₂ x.1) +
          ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
            (discBump k'.1 x.2.1 - discBump k'.1 x.1) • x.2.2 k')
    else x.2.2 ⟨k, h⟩

/-- The open domain of the parametrisation: the two points are in the open square and the `k₀`-th
bump separates them. -/
def discInjDomBlock {n : ℕ} (k₀ : Fin 2 × Fin 2) : Set (discInjSrc n k₀) :=
  {x | x.1 ∈ discSq ∧ x.2.1 ∈ discSq ∧ discBump k₀ x.1 ≠ discBump k₀ x.2.1}

@[simp] lemma discInjDomBlock_mem {n : ℕ} {k₀ : Fin 2 × Fin 2} {x : discInjSrc n k₀} :
    x ∈ discInjDomBlock (n := n) k₀ ↔
      x.1 ∈ discSq ∧ x.2.1 ∈ discSq ∧ discBump k₀ x.1 ≠ discBump k₀ x.2.1 := Iff.rfl

/-! ### The value of the parametrisation at the distinguished index and elsewhere -/

lemma discInjParamBlock_ne {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2*n)))
    (γ₁ γ₂ : ℝ → M) (k₀ : Fin 2 × Fin 2) (x : discInjSrc n k₀) {k : Fin 2 × Fin 2}
    (hk : k ≠ k₀) : discInjParamBlock f γ₁ γ₂ k₀ x k = x.2.2 ⟨k, hk⟩ := by
  simp only [discInjParamBlock]
  rw [dif_neg hk]

lemma discInjParamBlock_same {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2*n)))
    (γ₁ γ₂ : ℝ → M) (k₀ : Fin 2 × Fin 2) (x : discInjSrc n k₀) :
    discInjParamBlock f γ₁ γ₂ k₀ x k₀ =
      (discBump k₀ x.1 - discBump k₀ x.2.1)⁻¹ •
        ((baseDisc f γ₁ γ₂ x.2.1 - baseDisc f γ₁ γ₂ x.1) +
          ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
            (discBump k'.1 x.2.1 - discBump k'.1 x.1) • x.2.2 k') := by
  simp only [discInjParamBlock]
  simp

/-! ### Solving for the distinguished block -/

/-- The algebraic content of the recovery: if `discMap v p = discMap v q` then the `k₀`-block of
`v` is determined by the other three blocks. -/
lemma discInjParamBlock_key {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2*n)))
    (γ₁ γ₂ : ℝ → M) (k₀ : Fin 2 × Fin 2) (p q : ℝ × ℝ) (v : discInjTgt n)
    (h : baseDisc f γ₁ γ₂ p + ∑ k : Fin 2 × Fin 2, (discBump k p) • v k
       = baseDisc f γ₁ γ₂ q + ∑ k : Fin 2 × Fin 2, (discBump k q) • v k) :
    (discBump k₀ p - discBump k₀ q) • v k₀
      = (baseDisc f γ₁ γ₂ q - baseDisc f γ₁ γ₂ p)
        + ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀}, (discBump k'.1 q - discBump k'.1 p) • v k'.1 := by
  have h1 : ∑ k : Fin 2 × Fin 2, (discBump k p - discBump k q) • v k
      = baseDisc f γ₁ γ₂ q - baseDisc f γ₁ γ₂ p := by
    have hsub : ∑ k : Fin 2 × Fin 2, (discBump k p - discBump k q) • v k
        = ∑ k, (discBump k p) • v k - ∑ k, (discBump k q) • v k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_smul]
    rw [hsub]
    have hh : (baseDisc f γ₁ γ₂ p + ∑ k, (discBump k p) • v k)
        - (baseDisc f γ₁ γ₂ q + ∑ k, (discBump k q) • v k) = 0 := by rw [h, sub_self]
    have e : (baseDisc f γ₁ γ₂ p + ∑ k, (discBump k p) • v k)
        - (baseDisc f γ₁ γ₂ q + ∑ k, (discBump k q) • v k)
        = ((∑ k, (discBump k p) • v k) - ∑ k, (discBump k q) • v k)
          - (baseDisc f γ₁ γ₂ q - baseDisc f γ₁ γ₂ p) := by abel
    rw [e] at hh
    exact sub_eq_zero.mp hh
  have h2 : ∑ k : Fin 2 × Fin 2, (discBump k p - discBump k q) • v k
      = (discBump k₀ p - discBump k₀ q) • v k₀
        + ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀}, (discBump k'.1 p - discBump k'.1 q) • v k'.1 := by
    rw [← Finset.add_sum_erase _ (fun k : Fin 2 × Fin 2 => (discBump k p - discBump k q) • v k)
      (Finset.mem_univ k₀)]
    congr 1
    rw [Finset.sum_subtype (s := Finset.univ.erase k₀) (p := fun k : Fin 2 × Fin 2 => k ≠ k₀)
      (fun x => by simp) (fun k => (discBump k p - discBump k q) • v k)]
  have h3 : ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀}, (discBump k'.1 q - discBump k'.1 p) • v k'.1
      = - ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀}, (discBump k'.1 p - discBump k'.1 q) • v k'.1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k' _ => by rw [← neg_sub, neg_smul]
  have hmain : (discBump k₀ p - discBump k₀ q) • v k₀
      + (∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀}, (discBump k'.1 p - discBump k'.1 q) • v k'.1)
      = baseDisc f γ₁ γ₂ q - baseDisc f γ₁ γ₂ p := by rw [← h2, h1]
  rw [h3]
  have hgoal : (discBump k₀ p - discBump k₀ q) • v k₀
      = (baseDisc f γ₁ γ₂ q - baseDisc f γ₁ γ₂ p)
        - (∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
            (discBump k'.1 p - discBump k'.1 q) • v k'.1) := by
    rw [eq_sub_iff_add_eq]; exact hmain
  rw [hgoal, sub_eq_add_neg]

/-! ### The domain is open and the parametrisation is `C^1` on it -/

lemma discInjDomBlock_isOpen {n : ℕ} (k₀ : Fin 2 × Fin 2) :
    IsOpen (discInjDomBlock (n := n) k₀) := by
  have hdisc : IsOpen discSq := isOpen_Ioo.prod isOpen_Ioo
  have hc : Continuous (fun x : discInjSrc n k₀ => discBump k₀ x.1 - discBump k₀ x.2.1) :=
    ((contDiff_discBump k₀).continuous.comp continuous_fst).sub
      ((contDiff_discBump k₀).continuous.comp (continuous_fst.comp continuous_snd))
  have hset : discInjDomBlock (n := n) k₀
      = ((fun x : discInjSrc n k₀ => x.1) ⁻¹' discSq)
        ∩ (((fun x : discInjSrc n k₀ => x.2.1) ⁻¹' discSq)
          ∩ ((fun x : discInjSrc n k₀ => discBump k₀ x.1 - discBump k₀ x.2.1)
              ⁻¹' (({0} : Set ℝ)ᶜ))) := by
    ext x; simp [discInjDomBlock, sub_eq_zero]
  rw [hset]
  exact (hdisc.preimage continuous_fst).inter
    ((hdisc.preimage (continuous_fst.comp continuous_snd)).inter
      (hc.isOpen_preimage _ isOpen_compl_singleton))

/-- `baseDisc` is `C^1` when the map and the two arcs are smooth. -/
lemma contDiff_baseDisc_inj {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂) :
    ContDiff ℝ 1 (baseDisc f γ₁ γ₂) := by
  have hg₁ : ContDiff ℝ 1 (fun x : ℝ => f (γ₁ x)) :=
    (contMDiff_iff_contDiff.mp (hf.comp hγ₁)).of_le (by norm_num)
  have hg₂ : ContDiff ℝ 1 (fun x : ℝ => f (γ₂ x)) :=
    (contMDiff_iff_contDiff.mp (hf.comp hγ₂)).of_le (by norm_num)
  have h₁ : ContDiff ℝ 1 (fun p : ℝ × ℝ => f (γ₁ (sigR p.1))) := by
    refine hg₁.comp ?_
    unfold sigR; fun_prop
  have h₂ : ContDiff ℝ 1 (fun p : ℝ × ℝ => f (γ₂ (sigR p.1))) := by
    refine hg₂.comp ?_
    unfold sigR; fun_prop
  have hA : ContDiff ℝ 1 (fun p : ℝ × ℝ => (1 - p.2 : ℝ)) := by fun_prop
  have hB : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℝ)) := by fun_prop
  show ContDiff ℝ 1 (fun p : ℝ × ℝ => (1 - p.2) • f (γ₁ (sigR p.1)) + p.2 • f (γ₂ (sigR p.1)))
  exact (hA.smul h₁).add (hB.smul h₂)

lemma contDiffOn_discInjParamBlock {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (k₀ : Fin 2 × Fin 2) :
    ContDiffOn ℝ 1 (discInjParamBlock f γ₁ γ₂ k₀) (discInjDomBlock (n := n) k₀) := by
  have hbase : ContDiff ℝ 1 (baseDisc f γ₁ γ₂) := contDiff_baseDisc_inj f hf γ₁ γ₂ hγ₁ hγ₂
  have hD : ContDiff ℝ 1 (fun x : discInjSrc n k₀ => discBump k₀ x.1 - discBump k₀ x.2.1) :=
    ((contDiff_discBump k₀).of_le (by simp) |>.comp contDiff_fst).sub
      ((contDiff_discBump k₀).of_le (by simp) |>.comp (contDiff_fst.comp contDiff_snd))
  have hb1 : ContDiff ℝ 1 (fun x : discInjSrc n k₀ => baseDisc f γ₁ γ₂ x.1) :=
    hbase.comp contDiff_fst
  have hb2 : ContDiff ℝ 1 (fun x : discInjSrc n k₀ => baseDisc f γ₁ γ₂ x.2.1) :=
    hbase.comp (contDiff_fst.comp contDiff_snd)
  have hsum : ContDiff ℝ 1 (fun x : discInjSrc n k₀ =>
      ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
        (discBump k'.1 x.2.1 - discBump k'.1 x.1) • x.2.2 k') := by
    refine ContDiff.sum (s := Finset.univ) fun i _ => ?_
    refine (((contDiff_discBump i.1).of_le (by simp) |>.comp
        (contDiff_fst.comp contDiff_snd)).sub
      ((contDiff_discBump i.1).of_le (by simp) |>.comp contDiff_fst)).smul ?_
    fun_prop
  have hR : ContDiff ℝ 1 (fun x : discInjSrc n k₀ =>
      (baseDisc f γ₁ γ₂ x.2.1 - baseDisc f γ₁ γ₂ x.1) +
        ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
          (discBump k'.1 x.2.1 - discBump k'.1 x.1) • x.2.2 k') :=
    (hb2.sub hb1).add hsum
  have hone : ContDiffOn ℝ 1 (fun x : discInjSrc n k₀ =>
      (discBump k₀ x.1 - discBump k₀ x.2.1)⁻¹ •
        ((baseDisc f γ₁ γ₂ x.2.1 - baseDisc f γ₁ γ₂ x.1) +
          ∑ k' : {k : Fin 2 × Fin 2 // k ≠ k₀},
            (discBump k'.1 x.2.1 - discBump k'.1 x.1) • x.2.2 k'))
      (discInjDomBlock (n := n) k₀) :=
    (hD.contDiffOn.inv (fun x hx => sub_ne_zero.mpr hx.2.2)).smul hR.contDiffOn
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = k₀
  · subst hk
    refine hone.congr ?_
    intro x hx
    simp [discInjParamBlock]
  · have hlin : ContDiffOn ℝ 1 (fun x : discInjSrc n k₀ => x.2.2 ⟨k, hk⟩)
        (discInjDomBlock (n := n) k₀) :=
      (by fun_prop : ContDiff ℝ 1 (fun x : discInjSrc n k₀ => x.2.2 ⟨k, hk⟩)).contDiffOn
    refine hlin.congr ?_
    intro x hx
    simp [discInjParamBlock, hk]

/-! ### `badInj` as a union of the images of the parametrisations -/

lemma discBadInj_subset {n : ℕ} {M : Type*} (f : M → EuclideanSpace ℝ (Fin (2*n)))
    (γ₁ γ₂ : ℝ → M) :
    badInj f γ₁ γ₂ ⊆
      ⋃ k₀ : Fin 2 × Fin 2, discInjParamBlock f γ₁ γ₂ k₀ '' discInjDomBlock (n := n) k₀ := by
  rintro v ⟨p, hp, q, hq, hpq, heq⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, discBump k₀ p ≠ discBump k₀ q := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hpq (discBump_sep hp hq hcon)
  refine Set.mem_iUnion.mpr ⟨k₀, ?_⟩
  refine ⟨⟨p, q, fun k' => v k'.1⟩, ⟨hp, hq, hk₀⟩, ?_⟩
  funext k
  by_cases hk : k = k₀
  · rw [hk, discInjParamBlock_same]
    rw [inv_smul_eq_iff₀ (sub_ne_zero.mpr hk₀)]
    exact (discInjParamBlock_key f γ₁ γ₂ k₀ p q v
      (by simpa only [discMap, discPert] using heq)).symm
  · rw [discInjParamBlock_ne f γ₁ γ₂ k₀ _ hk]

/-! ### The finrank of the source -/

lemma finrank_discInjSrc (n : ℕ) (k₀ : Fin 2 × Fin 2) :
    Module.finrank ℝ (discInjSrc n k₀) = 6 * n + 4 := by
  have hcard : Fintype.card {k : Fin 2 × Fin 2 // k ≠ k₀} = 3 := by
    obtain ⟨i, j⟩ := k₀
    fin_cases i <;> fin_cases j <;> decide
  simp only [discInjSrc, Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype,
    finrank_euclideanSpace, Fintype.card_fin, Finset.sum_const, Finset.card_univ, hcard,
    nsmul_eq_mul]
  ring

end

/-- **Hausdorff-dimension bound for the injectivity-bad parameters.**
(The result should live in namespace `Work.Drive.Whitney`.)

`Work.Drive.Whitney.badInj f γ₁ γ₂` (defined in
`Submission.Work.Drive.Whitney.whitneyDiscDefs`) is the set of translation parameters `v` for
which `discMap f γ₁ γ₂ v` is not injective on the open square `discSq`, where
`discMap v p = baseDisc p + ∑ k, discBump k p • v k` and `discBump (i,j) p = uBeta i p.2 * xAlpha j p.1`.

Proof design: for `p ≠ q ∈ discSq` the four-tuple `k ↦ discBump k` separates `p` and `q`
(`Work.Drive.Whitney.discBump_sep`), so `badInj` is the union over the four indices `k₀` of the
pieces where `discBump k₀ p ≠ discBump k₀ q`; on such a piece a bad `v` is recovered from the other
three blocks by solving for the `k₀`-block. Each piece is the image of the `C^1` map
`(p, q, w) ↦ v`, defined on the open subset
`{(p,q) ∈ discSq × discSq | discBump k₀ p ≠ discBump k₀ q} × univ` of
`(ℝ × ℝ) × (ℝ × ℝ) × ({k : Fin 2 × Fin 2 // k ≠ k₀} → EuclideanSpace ℝ (Fin (2 * n)))`,
whose `finrank` is `4 + 3 * (2 * n) = 6 * n + 4`; apply
`Work.Projection.dimH_image_le_of_contDiffOn` and `dimH_union`. -/
theorem dimH_badInj {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂) :
    dimH (Work.Drive.Whitney.badInj f γ₁ γ₂) ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
  have _ := hn
  have hsub := discBadInj_subset (n := n) f γ₁ γ₂
  calc dimH (Work.Drive.Whitney.badInj f γ₁ γ₂)
      ≤ dimH (⋃ k₀ : Fin 2 × Fin 2,
          discInjParamBlock f γ₁ γ₂ k₀ '' discInjDomBlock (n := n) k₀) := dimH_mono hsub
    _ = ⨆ k₀ : Fin 2 × Fin 2,
          dimH (discInjParamBlock f γ₁ γ₂ k₀ '' discInjDomBlock (n := n) k₀) := dimH_iUnion _
    _ ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
        refine iSup_le fun k₀ => ?_
        have h := Work.Projection.dimH_image_le_of_contDiffOn
          (U := discInjDomBlock (n := n) k₀)
          (discInjDomBlock_isOpen (n := n) k₀)
          (contDiffOn_discInjParamBlock f hf γ₁ γ₂ hγ₁ hγ₂ k₀) (Set.Subset.rfl)
        rwa [finrank_discInjSrc n k₀] at h

end Work.Drive.Whitney
