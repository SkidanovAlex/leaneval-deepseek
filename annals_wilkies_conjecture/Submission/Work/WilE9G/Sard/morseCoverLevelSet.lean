import Mathlib
import Submission.Work.WilE9G.Sard.Basic
import Submission.Work.WilE9G.Sard.morseCoverMain

/-!
# Morse's Lemma 3.3: a distance-expanding parametrisation of a regular level set

If `h : ℝ^d → ℝ` is `C^m` at `y` with `h y = 0` and `∇h y ≠ 0`, then a neighbourhood of `y` in the
level set `{h = 0}` is the image of an expanding `C^m` parametrisation `Ψ` from an open set of
`ℝ^{d-1}` (Morse, *The behavior of a function on its critical set*, Lemma 3.3).  This discharges the
hypothesis `Work.WilE9G.Sard.LevelSetParam` of `morseCover_all`.

The proof picks a coordinate direction `j` in which `∇h y ≠ 0`, applies the implicit function
theorem to `(u, t) ↦ h (ins j t u)` to obtain the graph function `φ` of the level set, and then uses
that `ins j (φ u) u` is an isometric (in fact, coordinate-permuting) parametrisation whose first
`d - 1` coordinates are `u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

namespace Work.WilE9G.Sard

open Set Metric Filter
open scoped Topology

noncomputable section

/-! ## Two elementary normalisations -/

/-- A non-zero continuous linear functional on `ℝ^{e}` is non-zero on some standard basis
vector. -/
lemma exists_single_ne_zero {e : ℕ} (T : (Fin e → ℝ) →L[ℝ] ℝ) (hT : T ≠ 0) :
    ∃ j : Fin e, T (Pi.single j 1) ≠ 0 := by
  by_contra h
  push Not at h
  refine hT (ContinuousLinearMap.ext fun v => ?_)
  have hv : v = ∑ i : Fin e, v i • (Pi.single i (1 : ℝ) : Fin e → ℝ) := by
    funext k
    rw [Finset.sum_apply]
    simp [Pi.single_apply, Finset.mem_univ]
  rw [hv, map_sum]
  exact Finset.sum_eq_zero (fun i _ => by rw [map_smul, h i, smul_zero])

/-- Inserting the value `1` at position `j` and `0` in the other coordinates. -/
lemma ins_one_zero {e : ℕ} (j : Fin (e + 1)) :
    ins j (1 : ℝ) (0 : Fin e → ℝ) = Pi.single j 1 := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [ins]
  · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hk
    rw [← hi]
    simp [ins, Fin.succAbove_ne]

/-! ## The implicit function theorem in the form needed -/

/-- **The local graph theorem.**  If `g : ℝ^e × ℝ → ℝ` is `C^m` at `(u₀, v₀)`, vanishes there, and
its partial differential in the second variable does not vanish, then near `u₀` the zero set of `g`
is the graph of a `C^m` function `φ`, and locally this graph is unique. -/
theorem localGraph {e m : ℕ} (hm : 1 ≤ m)
    (g : (Fin e → ℝ) × ℝ → ℝ) (u₀ : Fin e → ℝ) (v₀ : ℝ)
    (hg : ContDiffAt ℝ m g (u₀, v₀)) (hg0 : g (u₀, v₀) = 0)
    (hderiv : (fderiv ℝ g (u₀, v₀)) (0, 1) ≠ 0) :
    ∃ (φ : (Fin e → ℝ) → ℝ) (A : Set (Fin e → ℝ)) (B : Set ℝ),
      IsOpen A ∧ IsOpen B ∧ u₀ ∈ A ∧ v₀ ∈ B ∧ ContDiffOn ℝ m φ A ∧ φ u₀ = v₀ ∧
      (∀ u ∈ A, g (u, φ u) = 0) ∧
      (∀ u ∈ A, ∀ v ∈ B, g (u, v) = 0 → v = φ u) := by
  have hm0 : ((m : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  -- the second partial derivative as a map `ℝ → ℝ`
  set T : ℝ →L[ℝ] ℝ :=
    (fderiv ℝ g (u₀, v₀)) ∘L (ContinuousLinearMap.inr ℝ (Fin e → ℝ) ℝ) with hTdef
  have hTone : (ContinuousLinearMap.inr ℝ (Fin e → ℝ) ℝ) (1 : ℝ) = (0, 1) := rfl
  have hT1 : T 1 = (fderiv ℝ g (u₀, v₀)) (0, 1) := by
    rw [hTdef, ContinuousLinearMap.comp_apply, hTone]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (fderiv ℝ g (u₀, v₀)) (0, 1) = c := ⟨_, rfl⟩
  have hcne : c ≠ 0 := by rw [← hc]; exact hderiv
  have hTapp : ∀ t : ℝ, T t = t * c := by
    intro t
    have ht : t = t • (1 : ℝ) := by simp
    rw [ht, map_smul, hT1, hc]
    simp only [smul_eq_mul]
    ring
  -- the inverse of `T`, hence the invertibility required by the implicit function theorem
  have hinvT : T.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · refine ContinuousLinearMap.ext (fun t => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, hTapp, smul_eq_mul]
      field_simp
    · refine ContinuousLinearMap.ext (fun t => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, hTapp, smul_eq_mul]
      field_simp
  have hinv : ((fderiv ℝ g (u₀, v₀)) ∘L
      (ContinuousLinearMap.inr ℝ (Fin e → ℝ) ℝ)).IsInvertible := by
    rw [← hTdef]; exact hinvT
  -- the implicit function
  let φ : (Fin e → ℝ) → ℝ := hg.implicitFunction hm0 hinv
  have hφ0 : φ u₀ = v₀ := hg.implicitFunction_apply_self hm0 hinv
  have hφcd : ContDiffAt ℝ m φ u₀ := hg.contDiffAt_implicitFunction hm0 hinv
  have hev1 : ∀ᶠ x in 𝓝 u₀, g (x, φ x) = 0 := by
    have h := hg.eventually_apply_implicitFunction hm0 hinv
    simpa [hg0] using h
  have hev2 : ∀ᶠ v in 𝓝 (u₀, v₀), g v = 0 ↔ φ v.1 = v.2 := by
    have h := hg.eventually_apply_eq_iff_implicitFunction hm0 hinv
    simpa [hg0] using h
  -- open neighbourhoods realising the three local statements
  obtain ⟨A₁, hA₁o, hu₀A₁, hA₁cd⟩ : ∃ A₁, IsOpen A₁ ∧ u₀ ∈ A₁ ∧ ContDiffOn ℝ m φ A₁ := by
    obtain ⟨A₀, hA₀, hA₀cd⟩ := hφcd.contDiffOn le_rfl (by simp)
    exact ⟨interior A₀, isOpen_interior, mem_interior_iff_mem_nhds.mpr hA₀,
      hA₀cd.mono interior_subset⟩
  obtain ⟨A₂, hA₂o, hu₀A₂, hA₂⟩ : ∃ A₂, IsOpen A₂ ∧ u₀ ∈ A₂ ∧ ∀ x ∈ A₂, g (x, φ x) = 0 := by
    obtain ⟨s, hs, hPs⟩ := Filter.eventually_iff_exists_mem.mp hev1
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun x hx => hPs x (interior_subset hx)⟩
  obtain ⟨A₃, B, hA₃o, hBo, hu₀A₃, hv₀B, hA₃B⟩ :
      ∃ (A₃ : Set (Fin e → ℝ)) (B : Set ℝ), IsOpen A₃ ∧ IsOpen B ∧ u₀ ∈ A₃ ∧ v₀ ∈ B ∧
        (∀ u ∈ A₃, ∀ v ∈ B, g (u, v) = 0 → v = φ u) := by
    obtain ⟨s, hs, hPs⟩ := Filter.eventually_iff_exists_mem.mp hev2
    rw [nhds_prod_eq] at hs
    obtain ⟨A₃', hA₃', B', hB', hsub⟩ := Filter.mem_prod_iff.mp hs
    refine ⟨interior A₃', interior B', isOpen_interior, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hA₃', mem_interior_iff_mem_nhds.mpr hB', ?_⟩
    intro u hu v hv huv
    have h1 : φ u = v := (hPs (u, v) (hsub ⟨interior_subset hu, interior_subset hv⟩)).mp huv
    exact h1.symm
  refine ⟨φ, A₁ ∩ A₂ ∩ A₃, B, (hA₁o.inter hA₂o).inter hA₃o, hBo, ⟨⟨hu₀A₁, hu₀A₂⟩, hu₀A₃⟩,
    hv₀B, ?_, hφ0, ?_, ?_⟩
  · exact hA₁cd.mono (fun x hx => hx.1.1)
  · intro u hu
    exact hA₂ u hu.1.2
  · intro u hu v hv huv
    exact hA₃B u hu.2 v hv huv

/-! ## Morse's Lemma 3.3 -/

/-- The `d = e + 1` form of `LevelSetParam`. -/
theorem levelSetAux {e m : ℕ} (hm : 1 ≤ m)
    {h : (Fin (e + 1) → ℝ) → ℝ} {y : Fin (e + 1) → ℝ}
    (hh : ContDiffAt ℝ m h y) (hy : h y = 0) (hgrad : fderiv ℝ h y ≠ 0) :
    ∃ (u₀ : Fin e → ℝ) (V : Set (Fin e → ℝ))
      (Ψ : (Fin e → ℝ) → (Fin (e + 1) → ℝ)) (U : Set (Fin (e + 1) → ℝ)),
      IsOpen V ∧ u₀ ∈ V ∧ ContDiffOn ℝ m Ψ V ∧
      (∀ x ∈ V, ∀ z ∈ V, dist x z ≤ dist (Ψ x) (Ψ z)) ∧
      (∀ u ∈ V, h (Ψ u) = 0) ∧
      Ψ u₀ = y ∧ IsOpen U ∧ y ∈ U ∧
      (∀ z ∈ U, h z = 0 → z ∈ Ψ '' V) := by
  classical
  -- a coordinate direction in which the gradient is non-zero
  obtain ⟨j, hj⟩ := exists_single_ne_zero (fderiv ℝ h y) hgrad
  have hm0 : ((m : ℕ∞) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  -- the base point, split into the remaining coordinates and the special one
  set u₀ : Fin e → ℝ := del j y with hu₀
  set v₀ : ℝ := y j with hv₀
  have hy_eq : ins j v₀ u₀ = y := by rw [hv₀, hu₀]; exact ins_del j y
  -- the linear map `(u, t) ↦ ins j t u`, with the pair in the order `(u, t)`
  set L : (Fin e → ℝ) × ℝ →L[ℝ] (Fin (e + 1) → ℝ) :=
    (insCLM e j).comp (ContinuousLinearMap.prod
      (ContinuousLinearMap.snd ℝ (Fin e → ℝ) ℝ)
      (ContinuousLinearMap.fst ℝ (Fin e → ℝ) ℝ)) with hL
  have hL_apply : ∀ (u : Fin e → ℝ) (t : ℝ), L (u, t) = ins j t u := by
    intro u t
    simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', insCLM_apply]
  have hLy : L (u₀, v₀) = y := by rw [hL_apply, hy_eq]
  set g : (Fin e → ℝ) × ℝ → ℝ := h ∘ L with hg
  have hg_cd : ContDiffAt ℝ m g (u₀, v₀) := by
    have hh' : ContDiffAt ℝ m h (L (u₀, v₀)) := by rw [hLy]; exact hh
    exact hh'.comp (u₀, v₀) L.contDiff.contDiffAt
  have hg0 : g (u₀, v₀) = 0 := by
    show h (L (u₀, v₀)) = 0
    rw [hLy]; exact hy
  have hderiv : (fderiv ℝ g (u₀, v₀)) (0, 1) ≠ 0 := by
    have hh_has : HasFDerivAt h (fderiv ℝ h y) (L (u₀, v₀)) := by
      rw [hLy]; exact (hh.differentiableAt hm0).hasFDerivAt
    have hg_has : HasFDerivAt g ((fderiv ℝ h y) ∘L L) (u₀, v₀) :=
      hh_has.comp (u₀, v₀) L.hasFDerivAt
    have h01 : L (0, 1) = Pi.single j 1 := by rw [hL_apply]; exact ins_one_zero j
    rw [hg_has.fderiv]
    show (fderiv ℝ h y) (L (0, 1)) ≠ 0
    rw [h01]; exact hj
  -- the implicit function
  obtain ⟨φ, A, B, hAopen, hBopen, hu₀A, hv₀B, hφ_cd, hφu₀, hφzero, huniq⟩ :=
    localGraph hm g u₀ v₀ hg_cd hg0 hderiv
  refine ⟨u₀, A, (fun u : Fin e → ℝ => ins j (φ u) u), {z : Fin (e + 1) → ℝ | del j z ∈ A ∧ z j ∈ B},
    hAopen, hu₀A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ψ` is `C^m`
    have hpair : ContDiffOn ℝ m (fun u : Fin e → ℝ => (u, φ u)) A :=
      contDiffOn_id.prodMk hφ_cd
    have hcomp := L.contDiff.contDiffOn.comp hpair (fun u _ => Set.mem_univ _)
    have key : (fun u : Fin e → ℝ => ins j (φ u) u)
        = (⇑L ∘ fun u : Fin e → ℝ => (u, φ u)) := by
      funext u
      rw [Function.comp_apply, hL_apply]
    rw [key]
    exact hcomp
  · -- `Ψ` is distance expanding
    intro x _ z _
    refine (dist_pi_le_iff dist_nonneg).mpr ?_
    intro i
    calc dist (x i) (z i)
        = dist (ins j (φ x) x (j.succAbove i)) (ins j (φ z) z (j.succAbove i)) := by simp
      _ ≤ dist (ins j (φ x) x) (ins j (φ z) z) :=
          dist_le_pi_dist (ins j (φ x) x) (ins j (φ z) z) (j.succAbove i)
  · -- `h ∘ Ψ = 0`
    intro u hu
    have h1 : h (L (u, φ u)) = 0 := hφzero u hu
    rw [hL_apply] at h1
    exact h1
  · -- `Ψ u₀ = y`
    show ins j (φ u₀) u₀ = y
    rw [hφu₀]
    exact hy_eq
  · -- `U` is open
    have hcont1 : Continuous fun z : Fin (e + 1) → ℝ => del j z := by
      show Continuous fun z : Fin (e + 1) → ℝ => fun k => z (j.succAbove k)
      exact continuous_pi (fun k => continuous_apply (j.succAbove k))
    have hcont2 : Continuous fun z : Fin (e + 1) → ℝ => z j := continuous_apply j
    have hhU := (hAopen.preimage hcont1).inter (hBopen.preimage hcont2)
    have hset : del j ⁻¹' A ∩ (fun z : Fin (e + 1) → ℝ => z j) ⁻¹' B
        = {z : Fin (e + 1) → ℝ | del j z ∈ A ∧ z j ∈ B} := by
      ext z; simp [Set.mem_inter_iff]
    rwa [hset] at hhU
  · -- `y ∈ U`
    show del j y ∈ A ∧ y j ∈ B
    rw [← hu₀, ← hv₀]
    exact ⟨hu₀A, hv₀B⟩
  · -- every nearby zero of `h` is in the image of `Ψ`
    intro z hz hhz
    obtain ⟨hzA, hzB⟩ := hz
    have hgz : g (del j z, z j) = 0 := by
      have h1 : h (L (del j z, z j)) = 0 := by
        rw [hL_apply, ins_del]; exact hhz
      exact h1
    have huniq' := huniq (del j z) hzA (z j) hzB hgz
    refine ⟨del j z, hzA, ?_⟩
    show ins j (φ (del j z)) (del j z) = z
    rw [← huniq']
    exact ins_del j z

/-- **Morse's Lemma 3.3** (`LevelSetParam`). -/
theorem levelSetParam_holds : LevelSetParam := by
  intro d hd m hm h y hh hy hgrad
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  exact levelSetAux (e := e) hm hh hy hgrad

end

end Work.WilE9G.Sard
