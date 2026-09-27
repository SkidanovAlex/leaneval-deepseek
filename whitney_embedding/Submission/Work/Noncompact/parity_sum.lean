import Mathlib
import Submission.Work.Projection.Basic
import Submission.Work.Projection.compact_embedding

/-!
# The parity (band) sum

Let `M` be a smooth `n`-manifold, `f : M → ℝ` a positive smooth function and, for every `i : ℕ`, let
`φ i : M → ℝ^{2n+1}` be a smooth map which is injective and immersive on the "core band"
`bandCore f i = f ⁻¹' [i, i+1]`.

The bands `band f i = f ⁻¹' (i - 1/4, i + 5/4)` are locally finite, and two bands whose indices
differ by at least `2` are disjoint.  Consequently, for a bump function `ρ i` which equals `1` on
the closed band `f ⁻¹' [i - 1/8, i + 9/8]` and has support `band f i`, the sums

  `Ψ_odd x = ∑ᶠ j, ρ (2j+1) x • φ (2j+1) x`,  `Ψ_even x = ∑ᶠ j, ρ (2j) x • φ (2j) x`

are smooth (the "parity trick": at every point at most one odd and at most one even term is
nonzero), and at a point of the core band `bandCore f i` the sum of the same parity as `i` collapses
to the single term `φ i x`.

This is the elementary construction which turns *local* injective immersions of the bands into a
*global* injective immersion `M → ℝ^{2n+1} × ℝ^{2n+1} × ℝ`, used in the proof of the weak Whitney
embedding theorem for non-compact manifolds.
-/

open scoped Manifold ContDiff BigOperators
open Topology Set Function

namespace Work.Noncompact

noncomputable section

/-- The auxiliary target `ℝ^{2n+1} × (ℝ^{2n+1} × ℝ)` of the parity sum. -/
abbrev ParT (n : ℕ) :=
  EuclideanSpace ℝ (Fin (2*n+1)) × (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [SigmaCompactSpace M]

/-- The `i`-th band of `f`: the preimage of `(i - 1/4, i + 5/4)`. -/
def band (f : M → ℝ) (i : ℕ) : Set M := f ⁻¹' Ioo ((i : ℝ) - 1/4) ((i : ℝ) + 5/4)

/-- The closed sub-band `f ⁻¹' [i - 1/8, i + 9/8]`. -/
def bandClosed (f : M → ℝ) (i : ℕ) : Set M := f ⁻¹' Icc ((i : ℝ) - 1/8) ((i : ℝ) + 9/8)

/-- The core band `f ⁻¹' [i, i + 1]`. -/
def bandCore (f : M → ℝ) (i : ℕ) : Set M := f ⁻¹' Icc (i : ℝ) ((i : ℝ) + 1)

/-- The interior part of the closed band: `f ⁻¹' (i - 1/8, i + 9/8)`. -/
def bandOpen (f : M → ℝ) (i : ℕ) : Set M := f ⁻¹' Ioo ((i : ℝ) - 1/8) ((i : ℝ) + 9/8)

lemma isOpen_band {f : M → ℝ} (hf : Continuous f) (i : ℕ) : IsOpen (band f i) :=
  isOpen_Ioo.preimage hf

lemma isOpen_bandOpen {f : M → ℝ} (hf : Continuous f) (i : ℕ) : IsOpen (bandOpen f i) :=
  isOpen_Ioo.preimage hf

lemma bandOwn_subset_bandClosed {f : M → ℝ} (i : ℕ) : bandOpen f i ⊆ bandClosed f i := by
  intro x hx
  rw [bandOpen, mem_preimage, mem_Ioo] at hx
  rw [bandClosed, mem_preimage, mem_Icc]
  exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩

lemma bandClosed_subset_band {f : M → ℝ} (i : ℕ) : bandClosed f i ⊆ band f i := by
  intro x hx
  rw [bandClosed, mem_preimage, mem_Icc] at hx
  rw [band, mem_preimage, mem_Ioo]
  constructor <;> linarith [hx.1, hx.2]

lemma bandCore_subset_bandClosed {f : M → ℝ} (i : ℕ) : bandCore f i ⊆ bandClosed f i := by
  intro x hx
  rw [bandCore, mem_preimage, mem_Icc] at hx
  rw [bandClosed, mem_preimage, mem_Icc]
  constructor <;> linarith [hx.1, hx.2]

lemma bandCore_subset_band {f : M → ℝ} (i : ℕ) : bandCore f i ⊆ band f i :=
  (bandCore_subset_bandClosed i).trans (bandClosed_subset_band i)

lemma bandCore_subset_bandOpen {f : M → ℝ} (i : ℕ) : bandCore f i ⊆ bandOpen f i := by
  intro x hx
  rw [bandCore, mem_preimage, mem_Icc] at hx
  rw [bandOpen, mem_preimage, mem_Ioo]
  constructor <;> linarith [hx.1, hx.2]

/-- Bands whose indices differ by at least `2` are disjoint. -/
lemma band_disjoint {f : M → ℝ} {i j : ℕ} (hij : i + 2 ≤ j) : band f i ∩ band f j = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  rw [band, mem_preimage, mem_Ioo] at h1 h2
  have hcast : (i : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hij
  linarith [h1.2, h2.1, hcast]

/-- The bands of a continuous function form a locally finite family. -/
lemma locallyFinite_band {f : M → ℝ} (hf : Continuous f) : LocallyFinite (band f) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (f x + 1/2)
  refine ⟨f ⁻¹' Ioo (f x - 1/4) (f x + 1/4), ?_, ?_⟩
  · refine (isOpen_Ioo.preimage hf).mem_nhds ?_
    exact ⟨by linarith, by linarith⟩
  · refine Set.Finite.subset (Set.finite_Iic N) ?_
    rintro i ⟨y, hy1, hy2⟩
    rw [band, mem_preimage, mem_Ioo] at hy1
    rw [mem_preimage, mem_Ioo] at hy2
    have h1 : ((i : ℝ)) < f x + 1/2 := by linarith [hy1.1, hy2.1]
    have h2 : ((i : ℝ)) < (N : ℝ) := by linarith
    exact Nat.cast_le.mp (le_of_lt h2)

/-- For each `i` there is a smooth bump function on `M` which is `1` on the closed band
`bandClosed f i` and has support exactly `band f i`. -/
lemma exists_band_bump {f : M → ℝ} (hfsm : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (i : ℕ) :
    ∃ ρ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ x, 0 ≤ ρ x) ∧ support ρ = band f i ∧
      ∀ x ∈ bandClosed f i, ρ x = 1 := by
  obtain ⟨ρ, hsm, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓡 n) (s := band f i) (t := bandClosed f i)
      (isOpen_band hfsm.continuous i) (by
        have h : bandClosed f i = f ⁻¹' Icc ((i : ℝ) - 1/8) ((i : ℝ) + 9/8) := rfl
        rw [h]; exact isClosed_Icc.preimage hfsm.continuous)
      (bandClosed_subset_band i)
  exact ⟨ρ, hsm, fun x => (hrange (mem_range_self x)).1, hsupp, fun x hx => (hone x).1 hx⟩

/-- The general band sum with parity offset `c`. -/
def bandSum (c : ℕ) (ρ : ℕ → M → ℝ) (φ : ℕ → M → EuclideanSpace ℝ (Fin (2*n+1))) :
    M → EuclideanSpace ℝ (Fin (2*n+1)) :=
  fun x => ∑ᶠ j : ℕ, ρ (2*j+c) x • φ (2*j+c) x

/-- The sum over the even-indexed bands. -/
abbrev evenSum (ρ : ℕ → M → ℝ) (φ : ℕ → M → EuclideanSpace ℝ (Fin (2*n+1))) :
    M → EuclideanSpace ℝ (Fin (2*n+1)) :=
  bandSum (n := n) 0 ρ φ

/-- The sum over the odd-indexed bands. -/
abbrev oddSum (ρ : ℕ → M → ℝ) (φ : ℕ → M → EuclideanSpace ℝ (Fin (2*n+1))) :
    M → EuclideanSpace ℝ (Fin (2*n+1)) :=
  bandSum (n := n) 1 ρ φ

section Smooth

variable {ρ : ℕ → M → ℝ} {φ : ℕ → M → EuclideanSpace ℝ (Fin (2*n+1))} {f : M → ℝ}

/-- The band sum is smooth: the family of supports is locally finite and each summand is smooth. -/
lemma contMDiff_bandSum {c : ℕ} (hρ : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ρ i))
    (hφ : ∀ i, ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (φ i))
    (hρsupp : ∀ i, support (ρ i) = band f i) (hband : LocallyFinite (band f)) :
    ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (bandSum (n := n) c ρ φ) := by
  refine contMDiff_finsum (fun j => ?_) ?_
  · exact (hρ (2*j+c)).smul (hφ (2*j+c))
  · refine (hband.comp_injective (g := fun j : ℕ => 2*j+c) (fun a b h => by
      have h' : 2*a + c = 2*b + c := h
      omega)).subset (fun j => ?_)
    refine (support_smul_subset_left (ρ (2*j+c)) (φ (2*j+c))).trans ?_
    rw [hρsupp (2*j+c)]
    exact fun y hy => hy

/-- If `x` lies in the core band `bandCore f i`, then on a neighbourhood of `x` the band sum (with
parity offset matching `i`) collapses to the single summand `ρ i • φ i`. -/
lemma bandSum_eventuallyEq_single {c : ℕ} (hc : c ≤ 1) (hf : Continuous f)
    (hρsupp : ∀ i, support (ρ i) = band f i)
    {x : M} {i : ℕ} (hx : x ∈ bandCore f i) (hi : i = 2 * (i / 2) + c) :
    bandSum (n := n) c ρ φ =ᶠ[𝓝 x] fun y => ρ i y • φ i y := by
  have hxb : x ∈ band f i := bandCore_subset_band i hx
  have hU : band f i ∈ 𝓝 x := (isOpen_band hf i).mem_nhds hxb
  filter_upwards [hU] with y hy
  have hside : ∀ j : ℕ, j ≠ i / 2 → ρ (2*j+c) y • φ (2*j+c) y = 0 := by
    intro j hj
    have hgap : i + 2 ≤ 2*j + c ∨ 2*j + c + 2 ≤ i := by omega
    have hρ0 : ρ (2*j+c) y = 0 := by
      rw [← Function.notMem_support, hρsupp (2*j+c)]
      intro hmem
      have hd : band f i ∩ band f (2*j+c) = ∅ := by
        rcases hgap with hgap | hgap
        · exact band_disjoint hgap
        · rw [inter_comm]; exact band_disjoint hgap
      have hmem' : y ∈ band f i ∩ band f (2*j+c) := ⟨hy, hmem⟩
      rw [hd] at hmem'
      exact hmem'
    rw [hρ0, zero_smul]
  show (∑ᶠ j : ℕ, ρ (2*j+c) y • φ (2*j+c) y) = ρ i y • φ i y
  rw [finsum_eq_single _ (i / 2) hside, ← hi]

/-- At a point of the core band, the band sum (with matching parity) evaluates to `φ i`. -/
lemma bandSum_eq_single {c : ℕ} (hc : c ≤ 1) (hf : Continuous f)
    (hρsupp : ∀ i, support (ρ i) = band f i)
    (hρone : ∀ i x, x ∈ bandClosed f i → ρ i x = 1)
    {x : M} {i : ℕ} (hx : x ∈ bandCore f i) (hi : i = 2 * (i / 2) + c) :
    bandSum (n := n) c ρ φ x = φ i x := by
  have h := bandSum_eventuallyEq_single (n := n) (φ := φ) (f := f) hc hf hρsupp hx hi
  have hx' : x ∈ bandClosed f i := bandCore_subset_bandClosed i hx
  have h1 : (fun y => ρ i y • φ i y) x = φ i x := by
    simp only [hρone i x hx', one_smul]
  exact h.eq_of_nhds.trans h1

end Smooth

/-- The parity offset of a natural number: `n % 2`. -/
def parityOffset (i : ℕ) : ℕ := i % 2

lemma parityOffset_le_one (i : ℕ) : parityOffset i ≤ 1 := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [parityOffset, h]

lemma eq_two_div_add_parityOffset (i : ℕ) : i = 2 * (i / 2) + parityOffset i := by
  have h := Nat.div_add_mod i 2
  simp only [parityOffset]
  omega

/-- **Parity sum.**  Given a positive smooth function `f : M → ℝ` and, for every `i`, a smooth map
`φ i : M → ℝ^{2n+1}` which is injective and immersive on the core band `bandCore f i`, the map
`Φ x = (Ψ_odd x, Ψ_even x, f x)` (transported linearly into `ℝ^{2n+1+(2n+2)}`) is a smooth injective
immersion of `M`. -/
theorem exists_injective_immersion_of_local_maps {f : M → ℝ}
    (hfsm : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfnonneg : ∀ x, 0 ≤ f x)
    (φ : ℕ → M → EuclideanSpace ℝ (Fin (2*n+1)))
    (hφsm : ∀ i, ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (φ i))
    (hφinj : ∀ i, InjOn (φ i) (bandCore f i))
    (hφimm : ∀ i x, x ∈ bandCore f i →
      Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1)) (φ i) x)) :
    ∃ Φ : M → EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))),
      ContMDiff (𝓡 n) (𝓡 (2*n+1+(2*n+2))) ∞ Φ ∧ Function.Injective Φ ∧
      ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2*n+1+(2*n+2))) Φ x) := by
  classical
  -- bump functions for the bands
  choose ρ hρsm hρnonneg hρsupp hρone using fun i => exists_band_bump (n := n) hfsm i
  have hbandLF : LocallyFinite (band f) := locallyFinite_band hfsm.continuous
  have hodd : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (oddSum (n := n) ρ φ) :=
    (contMDiff_bandSum (c := 1) hρsm hφsm hρsupp hbandLF)
  have heven : ContMDiff (𝓡 n) (𝓡 (2*n+1)) ∞ (evenSum (n := n) ρ φ) :=
    contMDiff_bandSum (c := 0) hρsm hφsm hρsupp hbandLF
  -- linear algebra: transport `ℝ^{2n+1} × ℝ^{2n+1} × ℝ` into `ℝ^{2n+1+(2n+2)}`
  have hfin : Module.finrank ℝ (ParT n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*n+1+(2*n+2)))) := by
    simp only [ParT, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  let L : ParT n ≃L[ℝ] EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) :=
    ContinuousLinearEquiv.ofFinrankEq hfin
  let inner : M → ParT n := fun x => (oddSum (n := n) ρ φ x, (evenSum (n := n) ρ φ x, f x))
  let Φ : M → EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) := fun x => L (inner x)
  have hinner : ContMDiff (𝓡 n) 𝓘(ℝ, ParT n) ∞ inner :=
    ContMDiff.prodMk_space hodd (ContMDiff.prodMk_space heven hfsm)
  have hΦsm : ContMDiff (𝓡 n) (𝓡 (2*n+1+(2*n+2))) ∞ Φ :=
    (L : ParT n →L[ℝ] EuclideanSpace ℝ (Fin (2*n+1+(2*n+2)))).contMDiff.comp hinner
  -- component projections
  set P₁ : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+1)) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1)))
      (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ)).comp (L.symm : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] ParT n) with hP₁
  set P₂ : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] EuclideanSpace ℝ (Fin (2*n+1)) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ).comp
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2*n+1)))
        (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ)).comp
          (L.symm : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] ParT n)) with hP₂
  set P₃ : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2*n+1))) ℝ).comp
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (2*n+1)))
        (EuclideanSpace ℝ (Fin (2*n+1)) × ℝ)).comp
          (L.symm : EuclideanSpace ℝ (Fin (2*n+1+(2*n+2))) →L[ℝ] ParT n)) with hP₃
  have hP1 : ∀ z : ParT n, P₁ (L z) = z.1 := by
    intro z; simp [hP₁, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hP2 : ∀ z : ParT n, P₂ (L z) = z.2.1 := by
    intro z; simp [hP₂, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hP3 : ∀ z : ParT n, P₃ (L z) = z.2.2 := by
    intro z; simp [hP₃, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hP1Φ : ∀ y, P₁ (Φ y) = oddSum (n := n) ρ φ y := fun y => hP1 (inner y)
  have hP2Φ : ∀ y, P₂ (Φ y) = evenSum (n := n) ρ φ y := fun y => hP2 (inner y)
  have hP3Φ : ∀ y, P₃ (Φ y) = f y := fun y => hP3 (inner y)
  -- the band index of a point
  have hfloor : ∀ x : M, x ∈ bandCore f (Nat.floor (f x)) := by
    intro x
    rw [bandCore, mem_preimage, mem_Icc]
    exact ⟨Nat.floor_le (hfnonneg x), le_of_lt (Nat.lt_floor_add_one (f x))⟩
  -- the collapse identity at points of a core band
  have keySum : ∀ (x : M) (i : ℕ), x ∈ bandCore f i →
      bandSum (n := n) (parityOffset i) ρ φ x = φ i x := by
    intro x i hx
    exact bandSum_eq_single (parityOffset_le_one i) hfsm.continuous hρsupp hρone hx
      (eq_two_div_add_parityOffset i)
  refine ⟨Φ, hΦsm, ?_, ?_⟩
  · intro x y hxy
    have h3 : f x = f y := by
      have h := congrArg P₃ hxy
      rw [hP3Φ x, hP3Φ y] at h
      exact h
    have h1 : oddSum (n := n) ρ φ x = oddSum (n := n) ρ φ y := by
      have h := congrArg P₁ hxy
      rw [hP1Φ x, hP1Φ y] at h
      exact h
    have h2 : evenSum (n := n) ρ φ x = evenSum (n := n) ρ φ y := by
      have h := congrArg P₂ hxy
      rw [hP2Φ x, hP2Φ y] at h
      exact h
    set i := Nat.floor (f x) with hi
    have hx : x ∈ bandCore f i := hfloor x
    have hy : y ∈ bandCore f i := by rw [hi, h3]; exact hfloor y
    have hikin : bandSum (n := n) (parityOffset i) ρ φ x = φ i x := keySum x i hx
    have hikin' : bandSum (n := n) (parityOffset i) ρ φ y = φ i y := keySum y i hy
    rcases Nat.mod_two_eq_zero_or_one i with hev | hod
    · have hcx : bandSum (n := n) (parityOffset i) ρ φ x = evenSum (n := n) ρ φ x := by
        simp only [bandSum, evenSum, parityOffset, hev]
      have hcy : bandSum (n := n) (parityOffset i) ρ φ y = evenSum (n := n) ρ φ y := by
        simp only [bandSum, evenSum, parityOffset, hev]
      exact hφinj i hx hy (by rw [← hikin, hcx, h2, ← hcy, hikin'])
    · have hcx : bandSum (n := n) (parityOffset i) ρ φ x = oddSum (n := n) ρ φ x := by
        simp only [bandSum, oddSum, parityOffset, hod]
      have hcy : bandSum (n := n) (parityOffset i) ρ φ y = oddSum (n := n) ρ φ y := by
        simp only [bandSum, oddSum, parityOffset, hod]
      exact hφinj i hx hy (by rw [← hikin, hcx, h1, ← hcy, hikin'])
  · intro x
    have hker : ∀ z : TangentSpace (𝓡 n) x,
        mfderiv (𝓡 n) (𝓡 (2*n+1+(2*n+2))) Φ x z = 0 → z = 0 := by
     intro z hz
     set i := Nat.floor (f x) with hi
     have hx : x ∈ bandCore f i := hfloor x
     have hpar : parityOffset i ≤ 1 := parityOffset_le_one i
     -- near `x`, the matching band sum collapses all the way to `φ i`
     have hsingle : bandSum (n := n) (parityOffset i) ρ φ =ᶠ[𝓝 x] φ i := by
       have h1 := bandSum_eventuallyEq_single (n := n) (φ := φ) (f := f) hpar hfsm.continuous hρsupp hx
         (eq_two_div_add_parityOffset i)
       have hU : bandOpen f i ∈ 𝓝 x :=
         (isOpen_bandOpen hfsm.continuous i).mem_nhds (bandCore_subset_bandOpen i hx)
       refine h1.trans ?_
       filter_upwards [hU] with y hy
       rw [hρone i y (bandOwn_subset_bandClosed i hy), one_smul]
     have hsum : mfderiv (𝓡 n) (𝓡 (2*n+1)) (bandSum (n := n) (parityOffset i) ρ φ) x
         = mfderiv (𝓡 n) (𝓡 (2*n+1)) (φ i) x := hsingle.mfderiv_eq
     -- derivatives of the two sums at `x`
     have hP1z : mfderiv (𝓡 n) (𝓡 (2*n+1)) (oddSum (n := n) ρ φ) x z = 0 := by
       have heq : oddSum (n := n) ρ φ =ᶠ[𝓝 x] fun y => P₁ (Φ y) :=
         Filter.Eventually.of_forall fun y => (hP1Φ y).symm
       rw [heq.mfderiv_eq]
       change ((mfderiv (𝓡 n) (𝓡 (2*n+1)) (⇑P₁ ∘ Φ) x) z) = 0
       rw [Work.Projection.mfderiv_comp_clm (n := n) (M := M) P₁ Φ hΦsm x]
       change P₁ (mfderiv (𝓡 n) (𝓡 (2*n+1+(2*n+2))) Φ x z) = 0
       rw [hz]
       exact map_zero P₁
     have hP2z : mfderiv (𝓡 n) (𝓡 (2*n+1)) (evenSum (n := n) ρ φ) x z = 0 := by
       have heq : evenSum (n := n) ρ φ =ᶠ[𝓝 x] fun y => P₂ (Φ y) :=
         Filter.Eventually.of_forall fun y => (hP2Φ y).symm
       rw [heq.mfderiv_eq]
       change ((mfderiv (𝓡 n) (𝓡 (2*n+1)) (⇑P₂ ∘ Φ) x) z) = 0
       rw [Work.Projection.mfderiv_comp_clm (n := n) (M := M) P₂ Φ hΦsm x]
       change P₂ (mfderiv (𝓡 n) (𝓡 (2*n+1+(2*n+2))) Φ x z) = 0
       rw [hz]
       exact map_zero P₂
     rcases Nat.mod_two_eq_zero_or_one i with hev | hod
     · have hb : bandSum (n := n) (parityOffset i) ρ φ = evenSum (n := n) ρ φ := by
         ext y; simp only [bandSum, evenSum, parityOffset, hev]
       have hφz : mfderiv (𝓡 n) (𝓡 (2*n+1)) (φ i) x z = 0 := by
         rw [← hsum, hb]
         exact hP2z
       exact hφimm i x hx (by rw [hφz, map_zero])
     · have hb : bandSum (n := n) (parityOffset i) ρ φ = oddSum (n := n) ρ φ := by
         ext y; simp only [bandSum, oddSum, parityOffset, hod]
       have hφz : mfderiv (𝓡 n) (𝓡 (2*n+1)) (φ i) x z = 0 := by
         rw [← hsum, hb]
         exact hP1z
       exact hφimm i x hx (by rw [hφz, map_zero])
    intro z w hzw
    exact sub_eq_zero.mp (hker (z - w) (by rw [map_sub, hzw, sub_self]))

end

end Work.Noncompact
