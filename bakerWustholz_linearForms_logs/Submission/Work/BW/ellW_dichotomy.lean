import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ellW_B_mem_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `ellW` dichotomy of `multiplicity_prop`

Let `G = G_a × G_m^N` with `N = r`, let `c : Fin (r-1) → Fin r → ℚ` be `ℚ`-linearly independent,
let `M : Fin ρ → Fin r → ℤ` have `ℚ`-linearly independent rows, and let
`w = (e₀, (0,c_1), …, (0,c_{r-1}))` be the standard operator family (`e₀ = (1,0,…,0)`).
Write `W = span (range w) ⊂ ℂ^{r+1} = Lie G` and let `G' = G_a^ε × ker 𝒵` be the analytic
subgroup cut out by `ε` (`ε = true`: include the `G_a` factor) and by the `ρ` characters with
exponents given by the rows of `M`; `lieSub r ρ ε M = Lie G'`.

This file proves the dichotomy
`ellW w ε M = dim W − dim (W ∩ Lie G') ∈ {k−1, k}` where `k = (if ε then ρ else ρ+1)`:

* `ellW w true M  = (r-1) - d` and `ellW w false M = r - d`, where `d = dim (span c ∩ ker M)`;
* `r - ρ - 1 ≤ d ≤ r - ρ` (dimension formula for `span c` and `ker M` in `ℂ^r`).

Hence `ellW w true M ∈ {ρ-1, ρ}` and `ellW w false M ∈ {ρ, ρ+1}`.
-/

namespace Work.BW

noncomputable section

/-! ## Auxiliary linear algebra -/

/-- The vector `e₀`, a unit vector with a `1` in the first (`G_a`) coordinate. -/
private def eZero (r : ℕ) : Fin (r + 1) → ℂ := Pi.single (0 : Fin (r + 1)) 1

/-- The tail projection `ℂ^{r+1} → ℂ^r`, `v ↦ (v_1, …, v_r)`. -/
private def dTail (r : ℕ) : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun v := fun i => v i.succ
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

/-- `ℂ^r → ℂ^{r+1}`, `u ↦ (0, u)` (zero in the `G_a` coordinate). -/
private def dCons (r : ℕ) : (Fin r → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun u := Fin.cons 0 u
  map_add' x y := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  map_smul' a x := by funext i; refine Fin.cases ?_ ?_ i <;> simp

@[simp] private lemma dTail_apply {r : ℕ} (v : Fin (r + 1) → ℂ) (i : Fin r) :
    dTail r v i = v i.succ := rfl

@[simp] private lemma dTail_cons {r : ℕ} (a : ℂ) (u : Fin r → ℂ) :
    dTail r (Fin.cons a u) = u := by funext i; simp

@[simp] private lemma dTail_dCons {r : ℕ} (u : Fin r → ℂ) : dTail r (dCons r u) = u := by
  funext i; simp [dCons]

private lemma dCons_injective (r : ℕ) : Function.Injective (dCons r) := by
  intro u v h
  have := congrArg (dTail r) h
  simpa using this

@[simp] private lemma dTail_eZero (r : ℕ) : dTail r (eZero r) = 0 := by
  funext i
  simp only [dTail_apply, eZero, Pi.zero_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i)]

/-- The matrix of `M` with entries cast to `ℂ`. -/
private def matC {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) : Matrix (Fin ρ) (Fin r) ℂ :=
  Matrix.of (fun j i => ((M j i : ℂ)))

/-- `u ↦ M u` on column vectors. -/
private def mLin {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) : (Fin r → ℂ) →ₗ[ℂ] (Fin ρ → ℂ) :=
  (matC M).mulVecLin

private lemma mLin_apply {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) (u : Fin r → ℂ) (j : Fin ρ) :
    mLin M u j = ∑ i, ((M j i : ℂ)) * u i := by
  simp only [mLin, matC, Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, Matrix.of_apply]

private lemma mLin_range_eq_top {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    LinearMap.range (mLin M) = ⊤ := by
  have hMℂ : LinearIndependent ℂ (matC M).row := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
      (v := fun j : Fin ρ => fun i : Fin r => ((M j i : ℤ) : ℚ))).mpr hM
    have h2 : (matC M).row = (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ)) := by
      funext j i
      simp [matC, Matrix.row]
    rw [h2]
    exact h
  rw [mLin]
  refine Submodule.eq_top_of_finrank_eq ?_
  change (matC M).rank = Module.finrank ℂ (Fin ρ → ℂ)
  rw [LinearIndependent.rank_matrix hMℂ, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

private lemma finrank_ker_mLin {r ρ : ℕ} (hρr : ρ ≤ r) (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    Module.finrank ℂ ↥(LinearMap.ker (mLin M)) = r - ρ := by
  have h := LinearMap.finrank_range_add_finrank_ker (mLin M)
  rw [mLin_range_eq_top M hM] at h
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

/-- The family `c` with values cast to `ℂ`. -/
private def csVec {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) : Fin (r - 1) → (Fin r → ℂ) :=
  fun m i => ((c m i : ℚ) : ℂ)

/-- The `ℂ`-span of the family `c`. -/
private def spanC {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) : Submodule ℂ (Fin r → ℂ) :=
  Submodule.span ℂ (Set.range (csVec c))

/-- `span c`, transported to the tail coordinates of `ℂ^{r+1}`. -/
private def subU {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) : Submodule ℂ (Fin (r + 1) → ℂ) :=
  (spanC c).map (dCons r)

private lemma finrank_spanC {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c) :
    Module.finrank ℂ ↥(spanC c) = r - 1 := by
  have hcℂ : LinearIndependent ℂ (csVec c) := by
    have h := (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ) (v := c)).mpr hc
    have h2 : csVec c = (fun m : Fin (r - 1) => ⇑(algebraMap ℚ ℂ) ∘ c m) := by
      funext m i
      simp [csVec]
    rw [h2]
    exact h
  rw [spanC, finrank_span_eq_card hcℂ, Fintype.card_fin]

private lemma iInf_ker_eq {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) :
    (⨅ j : Fin ρ, LinearMap.ker
      (∑ i : Fin r, ((M j i : ℂ)) •
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ))
      = LinearMap.ker ((mLin M).comp (dTail r)) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  have h : ∀ j : Fin ρ,
      ((∑ i : Fin r, ((M j i : ℂ)) •
          LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ) v)
        = (mLin M) ((dTail r) v) j := by
    intro j
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
      dTail_apply, mLin_apply]
  constructor
  · intro hv
    funext j
    rw [← h j]
    exact hv j
  · intro hv j
    rw [h j]
    exact congrFun hv j

private lemma lieSub_eq_ker {r ρ : ℕ} (M : Fin ρ → Fin r → ℤ) (ε : Bool) :
    lieSub r ρ ε M = (if ε then ⊤ else LinearMap.ker
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0)) ⊓
      LinearMap.ker ((mLin M).comp (dTail r)) := by
  simp only [lieSub, iInf_ker_eq M]

/-- Rank–nullity for the restriction of `f` to a submodule: `dim (f '' P) = dim P - dim (P ∩ ker f)`. -/
private theorem finrank_map_inf_ker {K : Type*} [Field K] {V W : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (P : Submodule K V) :
    Module.finrank K ↥(P.map f) = Module.finrank K ↥P - Module.finrank K ↥(P ⊓ LinearMap.ker f) := by
  have hker : LinearMap.ker (f.comp P.subtype) = Submodule.comap P.subtype (LinearMap.ker f) :=
    LinearMap.ker_comp P.subtype f
  have hfin : Module.finrank K ↥(LinearMap.ker (f.comp P.subtype))
      = Module.finrank K ↥(P ⊓ LinearMap.ker f) := by
    rw [hker, ← Submodule.finrank_map_subtype_eq P
        (Submodule.comap P.subtype (LinearMap.ker f)), Submodule.map_comap_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.comp P.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, hfin] at hrn
  omega

/-! ## The dichotomy -/

/-- The `ellW` dichotomy of `multiplicity_prop`: for the standard operator family
`w = (∂₀, D_1, …, D_{r-1})` (i.e. `w 0 = e₀` and `w m.succ = (0, c_m)`) with the `c_m`
`ℚ`-linearly independent, and `M` with `ℚ`-linearly independent rows, the codimension
`ellW w ε M = dim W − dim(W ∩ lieSub)` of the analytic subgroup inside `G' = G_a^ε × ker 𝒵`
takes exactly one of the two values `k − 1` and `k`, where `k = (if ε then 0 else 1) + ρ` is the
codimension of `G'` in `G`. -/
theorem ellW_dichotomy {r ρ : ℕ} (hr : 2 ≤ r) (hρr : ρ ≤ r)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (M : Fin ρ → Fin r → ℤ) (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ)))
    (ε : Bool) (w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) :
    ellW (N := r) (q := r - 1 + 1) w ε M = (if ε then ρ else ρ + 1) - 1 ∨
    ellW (N := r) (q := r - 1 + 1) w ε M = (if ε then ρ else ρ + 1) := by
  classical
  -- ## Elementary dimensions
  have hfinA : Module.finrank ℂ ↥(spanC c) = r - 1 := finrank_spanC c hc
  have hfinK : Module.finrank ℂ ↥(LinearMap.ker (mLin M)) = r - ρ := finrank_ker_mLin hρr M hM
  have hfinU : Module.finrank ℂ ↥(subU c) = r - 1 := by
    have e := Submodule.equivMapOfInjective (dCons r) (dCons_injective r) (spanC c)
    have h : Module.finrank ℂ ↥(subU c) = Module.finrank ℂ ↥(spanC c) := by
      rw [subU]
      exact (LinearEquiv.finrank_eq e).symm
    rw [h, hfinA]
  -- ## The span of the operator family
  have hrange : Set.range w = insert (eZero r) (dCons r '' Set.range (csVec c)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ ?_ i
      · exact Or.inl hw0
      · intro m
        exact Or.inr ⟨csVec c m, ⟨m, rfl⟩, (hw1 m).symm⟩
    · rintro (hx | ⟨u, ⟨m, rfl⟩, rfl⟩)
      · exact ⟨0, hw0.trans hx.symm⟩
      · exact ⟨m.succ, hw1 m⟩
  have hWU : Submodule.span ℂ (Set.range w) = ℂ ∙ eZero r ⊔ subU c := by
    calc Submodule.span ℂ (Set.range w)
        = Submodule.span ℂ (insert (eZero r) (dCons r '' Set.range (csVec c))) := by
            rw [hrange]
      _ = ℂ ∙ eZero r ⊔ Submodule.span ℂ (dCons r '' Set.range (csVec c)) :=
            Submodule.span_insert _ _
      _ = ℂ ∙ eZero r ⊔ subU c := by
            rw [← Submodule.map_span (dCons r) (Set.range (csVec c)), subU, spanC]
  have hsU : ℂ ∙ eZero r ⊓ subU c = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxs, hxu⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxs
    rw [subU, spanC] at hxu
    obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hxu
    have hx0 : x 0 = 0 := by rw [← hu]; simp [dCons]
    have haz : a = 0 := by
      have h := hx0
      rw [← ha] at h
      simpa [eZero] using h
    rw [← ha, haz, zero_smul]
  have hsne : eZero r ≠ 0 := by
    intro h
    simpa [eZero] using congrFun h 0
  have hfinW0 : Module.finrank ℂ ↥(ℂ ∙ eZero r ⊔ subU c) = r := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ eZero r) (subU c)
    rw [hsU, finrank_bot, add_zero, finrank_span_singleton hsne, hfinU] at h
    omega
  have hfinW : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) = r := by
    rw [hWU, hfinW0]
  -- ## Bounds for the intersection dimension
  have hd_le : Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) ≤ r - ρ :=
    (Submodule.finrank_mono
      (inf_le_right : spanC c ⊓ LinearMap.ker (mLin M) ≤ LinearMap.ker (mLin M))).trans_eq hfinK
  have hd_ge : r - ρ - 1 ≤ Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (spanC c) (LinearMap.ker (mLin M))
    have htop : Module.finrank ℂ ↥(spanC c ⊔ LinearMap.ker (mLin M)) ≤ r := by
      have hle := Submodule.finrank_mono (le_top : spanC c ⊔ LinearMap.ker (mLin M) ≤ ⊤)
      rwa [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    rw [hfinA, hfinK] at h
    omega
  -- ## The image of the span under the character forms
  have hcomp : ((mLin M).comp (dTail r)).comp (dCons r) = mLin M := by
    ext u
    simp
  have hsubU : (subU c).map ((mLin M).comp (dTail r)) = (spanC c).map (mLin M) := by
    rw [subU, ← Submodule.map_comp (dCons r) ((mLin M).comp (dTail r)) (spanC c), hcomp]
  have hAsub : (ℂ ∙ eZero r).map ((mLin M).comp (dTail r)) = ⊥ := by
    have h0 : ((mLin M).comp (dTail r)) (eZero r) = 0 := by simp
    rw [Submodule.map_span, Set.image_singleton, Submodule.span_singleton_eq_bot]
    exact h0
  -- ## The two cases
  cases ε with
  | true =>
    have hlie : lieSub r ρ true M = LinearMap.ker ((mLin M).comp (dTail r)) := by
      rw [lieSub_eq_ker M true]
      simp
    have hA : ellW (N := r) (q := r - 1 + 1) w true M
        = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) -
          Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓
            LinearMap.ker ((mLin M).comp (dTail r))) := by
      rw [ellW]
      exact congrArg (fun t : ℕ => Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) - t)
        (congrArg (fun s : Submodule ℂ (Fin (r + 1) → ℂ) =>
          Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ s)) hlie)
    have hB : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) -
          Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓
            LinearMap.ker ((mLin M).comp (dTail r))) =
        Module.finrank ℂ ↥((Submodule.span ℂ (Set.range w)).map
          ((mLin M).comp (dTail r))) :=
      (finrank_map_inf_ker ((mLin M).comp (dTail r))
        (Submodule.span ℂ (Set.range w))).symm
    have hC : Module.finrank ℂ ↥((Submodule.span ℂ (Set.range w)).map
          ((mLin M).comp (dTail r))) = Module.finrank ℂ ↥((spanC c).map (mLin M)) := by
      rw [hWU, Submodule.map_sup, hAsub, bot_sup_eq, hsubU]
    have hD : Module.finrank ℂ ↥((spanC c).map (mLin M)) =
        (r - 1) - Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) := by
      rw [finrank_map_inf_ker (mLin M) (spanC c), hfinA]
    have hell : ellW (N := r) (q := r - 1 + 1) w true M
        = (r - 1) - Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) :=
      ((hA.trans hB).trans hC).trans hD
    change ellW (N := r) (q := r - 1 + 1) w true M = ρ - 1 ∨
      ellW (N := r) (q := r - 1 + 1) w true M = ρ
    by_cases hd : Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) = r - ρ
    · left
      rw [hell, hd]
      omega
    · right
      have hd' : Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) = r - ρ - 1 := by omega
      rw [hell, hd']
      omega
  | false =>
    have hlie : lieSub r ρ false M = LinearMap.ker
          (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0) ⊓
        LinearMap.ker ((mLin M).comp (dTail r)) := by
      rw [lieSub_eq_ker M false]
      simp
    have hUproj : ∀ x ∈ subU c, x ∈ LinearMap.ker
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0) := by
      intro x hx
      rw [subU, spanC] at hx
      obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hx
      rw [LinearMap.mem_ker, LinearMap.proj_apply, ← hu]
      simp [dCons]
    have hWker : Submodule.span ℂ (Set.range w) ⊓ LinearMap.ker
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0) = subU c := by
      refine le_antisymm ?_ ?_
      · intro x hx
        obtain ⟨hxW, hxK⟩ := Submodule.mem_inf.mp hx
        rw [hWU] at hxW
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxW
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
        have hz0 : z 0 = 0 := by
          have h := hUproj z hz
          rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h
        have hx0 : x 0 = 0 := by
          have h := hxK
          rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h
        have hsplit : x 0 = y 0 + z 0 := by rw [← hyz, Pi.add_apply]
        have hy0 : y 0 = a := by rw [← ha]; simp [eZero]
        have haz : a = 0 := by
          have h3 : x 0 = a := by simp only [hsplit, hy0, hz0, add_zero]
          rw [h3] at hx0
          exact hx0
        rw [← hyz, ← ha, haz, zero_smul, zero_add]
        exact hz
      · intro x hx
        exact Submodule.mem_inf.mpr
          ⟨by rw [hWU]; exact Submodule.mem_sup_right hx, hUproj x hx⟩
    have hUker : subU c ⊓ LinearMap.ker ((mLin M).comp (dTail r))
        = (spanC c ⊓ LinearMap.ker (mLin M)).map (dCons r) := by
      rw [subU, Submodule.map_inf_eq_map_inf_comap,
        ← LinearMap.ker_comp (dCons r) ((mLin M).comp (dTail r)), hcomp]
    have hfinMap : Module.finrank ℂ ↥((spanC c ⊓ LinearMap.ker (mLin M)).map (dCons r))
        = Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (dCons r) (dCons_injective r)
        (spanC c ⊓ LinearMap.ker (mLin M)))).symm
    have hfin : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ false M)
        = Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) := by
      rw [hlie, ← inf_assoc, hWker, hUker, hfinMap]
    have hell : ellW (N := r) (q := r - 1 + 1) w false M
        = r - Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) := by
      rw [ellW, hfin, hfinW]
    change ellW (N := r) (q := r - 1 + 1) w false M = ρ ∨
      ellW (N := r) (q := r - 1 + 1) w false M = ρ + 1
    by_cases hd : Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) = r - ρ
    · left
      rw [hell, hd]
      omega
    · right
      have hd' : Module.finrank ℂ ↥(spanC c ⊓ LinearMap.ker (mLin M)) = r - ρ - 1 := by omega
      rw [hell, hd']
      omega

end

end Work.BW
