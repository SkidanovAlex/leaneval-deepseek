import Mathlib
import Submission.Work.ThomBordism.nfGenBasic
import Submission.Work.ThomBordism.stdThomGen_span

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-!
# The oriented fibre generator `nfGen` generates the relative cohomology of the fibre pair

`Work.ThomBordism.nfGen hk E ND x : H^k(ν_x, ν_x∖0;ℤ)` is the pullback of the standard generator
`Work.ThomBordism.stdThomGen k` of `H^k(ℝ^k, ℝ^k∖0;ℤ)` along the coordinate reading
`nfRead E ND x : ν_x → ℝ^k` of the fibre in the σ-corrected orthonormal frame `Gauss.gframe`.

Here we prove that it *generates* — `ℤ ∙ nfGen hk E ND x = ⊤` — by exhibiting an explicit inverse of
the reading map: the insertion of a coordinate vector in the corrected frame,

  `nfInv (a) = (x, ∑ j, a j • gframe_j) ∈ ν_x`,

which is a homeomorphism of pairs `(ℝ^k, ℝ^k∖0) ≅ (ν_x, ν_x∖0)` inverse to `nfRead`.  The pullback
along it is then a right inverse of `(nfRead)^*`, so `(nfRead)^*` is surjective and carries the
generator `stdThomGen` to a generator.
-/

/-! ## The insertion of coordinates in the corrected frame -/

/-- **The insertion `ℝ^k → ℝ^{8+k}` given by the corrected normal frame** `gframe` at `x`:
`a ↦ ∑ j, a j • gframe_j`.  It is the inverse of the reading map `nfRead` on the normal fibre. -/
noncomputable def nfIns {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Work.Tubular.Euc k →L[ℝ] Work.Tubular.Euc (8 + k) :=
  ∑ j : Fin k, (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight
    (Gauss.gframe E ND (ND.D.indexAt x) x j)

theorem nfIns_apply {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (a : Work.Tubular.Euc k) :
    nfIns E ND x a = ∑ j : Fin k, Work.ThomBordism.PontryaginThom.eucToFun k a j •
      Gauss.gframe E ND (ND.D.indexAt x) x j := by
  simp only [nfIns, sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply,
    Work.ThomBordism.PontryaginThom.eucToFun_apply]

/-- A vector of the corrected frame is normal. -/
theorem gframe_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) (j : Fin k) :
    Gauss.gframe E ND i x j ∈ Work.Tubular.normalSpace E x := by
  rw [Gauss.gframe_apply]
  exact Submodule.smul_mem _ _ (Work.Tubular.orthFrame_mem E ND i hx j)

/-- The insertion lands in the normal space at `x`. -/
theorem nfIns_mem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (a : Work.Tubular.Euc k) : nfIns E ND x a ∈ Work.Tubular.normalSpace E x := by
  rw [nfIns_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (gframe_mem E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x) j)

/-! ## The corrected frame spans the normal space -/

/-- Rescaling a family by nonzero scalars does not change its span. -/
theorem span_range_smul_of_ne_zero {E : Type*} [AddCommMonoid E] [Module ℝ E] {ι : Type*}
    (u : ι → E) (c : ι → ℝ) (hc : ∀ i, c i ≠ 0) :
    Submodule.span ℝ (Set.range fun i => c i • u i) = Submodule.span ℝ (Set.range u) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rintro _ ⟨i, rfl⟩
    have h : (c i)⁻¹ • (c i • u i) = u i := by
      rw [smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [← h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The corrected frame spans the normal space (the gauge is diagonal with entries `±1`). -/
theorem span_gframe {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) :
    Submodule.span ℝ (Set.range (Gauss.gframe E ND i x)) = Work.Tubular.normalSpace E x := by
  have hg : Gauss.gframe E ND i x
      = fun a : Fin k => (if (a : ℕ) = 0 then Gauss.sigma E ND i x else 1) •
          Work.Tubular.orthFrame E ND i x a :=
    funext fun a => Gauss.gframe_apply E ND i x a
  have hc : ∀ a : Fin k, (if (a : ℕ) = 0 then Gauss.sigma E ND i x else 1) ≠ 0 := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · rw [if_pos ha]
      rcases Gauss.sigma_eq_one_or E ND i x with h | h <;> rw [h] <;> norm_num
    · rw [if_neg ha]; norm_num
  rw [hg, span_range_smul_of_ne_zero _ _ hc, Work.Tubular.span_orthFrame E ND i hx]

/-! ## The inverse of the reading map -/

theorem eucToFun_funToEuc_tubular (n : ℕ) (y : Fin n → ℝ) :
    Work.ThomBordism.PontryaginThom.eucToFun n (Work.Tubular.funToEuc n y) = y := by
  rw [Work.ThomBordism.PontryaginThom.eucToFun_apply]
  rfl

theorem funToEuc_eucToFun_tubular (n : ℕ) (x : Work.Tubular.Euc n) :
    Work.Tubular.funToEuc n (Work.ThomBordism.PontryaginThom.eucToFun n x) = x := by
  rw [Work.ThomBordism.PontryaginThom.eucToFun_apply]
  rfl

/-- **The insertion is a right inverse of the reading map.** -/
theorem nfRead_nfIns {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (a : Work.Tubular.Euc k) :
    readFrame (Gauss.gframe E ND (ND.D.indexAt x) x) (nfIns E ND x a) = a := by
  rw [readFrame_apply]
  have h1 : ∀ j : Fin k, inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j) (nfIns E ND x a)
      = Work.ThomBordism.PontryaginThom.eucToFun k a j := by
    intro j
    rw [nfIns_apply]
    exact (Gauss.orthonormal_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)).inner_right_fintype
      (fun l => Work.ThomBordism.PontryaginThom.eucToFun k a l) j
  simp only [h1]
  exact funToEuc_eucToFun_tubular k a

/-- **The insertion of coordinates in the corrected frame**, as a map into the fibre of the normal
bundle over `x`. -/
noncomputable def nfInv {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    C(Work.Tubular.Euc k, ↥(nfSet E x)) where
  toFun a := ⟨⟨(x, nfIns E ND x a), nfIns_mem E ND x a⟩, rfl⟩
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (continuous_const.prodMk (nfIns E ND x).continuous) (fun a => nfIns_mem E ND x a))
      (fun a => rfl)

theorem nfRead_nfInv {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (a : Work.Tubular.Euc k) : nfRead E ND x (nfInv E ND x a) = a :=
  nfRead_nfIns E ND x a

/-- **The insertion is a left inverse of the reading map.** -/
theorem nfInv_nfRead {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (p : ↥(nfSet E x)) : nfInv E ND x (nfRead E ND x p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (p.2).symm
  · show nfIns E ND x (nfRead E ND x p) = Work.Tubular.NormalTotal.vec p.1
    rw [nfIns_apply]
    have hcoe : ∀ j : Fin k, Work.ThomBordism.PontryaginThom.eucToFun k (nfRead E ND x p) j
        = inner ℝ (Gauss.gframe E ND (ND.D.indexAt x) x j)
            (Work.Tubular.NormalTotal.vec p.1) := by
      intro j
      have hread : nfRead E ND x p
          = readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
              (Work.Tubular.NormalTotal.vec p.1) := rfl
      rw [hread, readFrame_apply, eucToFun_funToEuc_tubular]
    refine Eq.trans (Finset.sum_congr rfl (fun j _ => by rw [hcoe j])) ?_
    exact Work.Tubular.sum_inner_smul_eq_self_of_mem_span
      (Gauss.orthonormal_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x))
      (by rw [span_gframe E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x)]
          exact vec_mem_normalSpace_of_mem_nfSet E p)

/-- The insertion of a nonzero coordinate vector is a nonzero fibre vector. -/
theorem nfInv_mem_nfPunct {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    (a : Work.Tubular.Euc k) (ha : a ≠ 0) :
    nfInv E ND x a ∈ nfPunct E x := by
  show Work.Tubular.NormalTotal.vec (nfInv E ND x a).1 ≠ 0
  intro h0
  have hzero : nfRead E ND x (nfInv E ND x a) = 0 := by
    rw [show nfRead E ND x (nfInv E ND x a)
        = readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
            (Work.Tubular.NormalTotal.vec (nfInv E ND x a).1) from rfl, h0, map_zero]
  rw [nfRead_nfInv] at hzero
  exact ha hzero

/-! ## The reading map induces a surjection on relative cohomology -/

theorem nfRead_surjective {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Function.Surjective (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
      ({0}ᶜ : Set (Work.Tubular.Euc k))
      (fun p hp => nfRead_ne_zero hk E ND x p hp) ℤ k).hom := by
  classical
  have hΦmem : ∀ a ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)), nfInv E ND x a ∈ nfPunct E x :=
    fun a ha => nfInv_mem_nfPunct E ND x a ha
  have hmem : ∀ p ∈ nfPunct E x, nfRead E ND x p ∈ ({0}ᶜ : Set (Work.Tubular.Euc k)) :=
    fun p hp => nfRead_ne_zero hk E ND x p hp
  have hgf : ∀ p ∈ nfPunct E x, nfInv E ND x (nfRead E ND x p) ∈ nfPunct E x :=
    fun p hp => by rw [nfInv_nfRead]; exact hp
  have hcomp_eq : (nfInv E ND x).comp (nfRead E ND x)
      = ContinuousMap.id ↥(nfSet E x) :=
    ContinuousMap.ext fun p => nfInv_nfRead E ND x p
  have hcomp : Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k
      ≫ Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x)) := by
    rw [Work.Thom.relCohMap_compA (A := nfPunct E x)
      (B := ({0}ᶜ : Set (Work.Tubular.Euc k))) (C := nfPunct E x) (nfRead E ND x)
      (nfInv E ND x) hmem hΦmem hgf ℤ k]
    exact (Work.Thom.relCohMap_congrA (A := nfPunct E x) (B := nfPunct E x) hcomp_eq hgf
      (fun _ h => h) ℤ k).trans (Work.Thom.relCohMap_idA (nfPunct E x) ℤ k)
  have hlin : (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x)
        ({0}ᶜ : Set (Work.Tubular.Euc k)) hmem ℤ k).hom.comp
      (Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
        (nfPunct E x) hΦmem ℤ k).hom = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom hcomp
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  intro y
  refine ⟨(Work.Thom.relCohMap (nfInv E ND x) ({0}ᶜ : Set (Work.Tubular.Euc k))
    (nfPunct E x) hΦmem ℤ k).hom y, ?_⟩
  simpa using LinearMap.congr_fun hlin y

/-! ## The generator -/

theorem nfGen_span {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Submodule.span ℤ ({nfGen hk E ND x} : Set (Work.Thom.RelCoh ℤ k ↥(nfSet E x)
      (nfPunct E x))) = ⊤ := by
  rw [nfGen_eq hk E ND x]
  exact Work.Tubular.span_singleton_map_eq_top _ (nfRead_surjective hk E ND x) _
    (stdThomGen_span k hk)

end Work.ThomBordism
