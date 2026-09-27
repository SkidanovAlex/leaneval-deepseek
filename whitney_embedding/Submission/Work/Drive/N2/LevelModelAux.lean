import Mathlib
import Submission.Work.Drive.N2.LevelSetDefs

/-!
# Auxiliary coordinate lemmas for `Work.Drive.N2.levelModelExists`

The model space of the surface is `E2 = ℝ²`.  This file fixes the elementary maps used in the
proof that a non-critical level set of a smooth function is locally a graph:

* `Phi g j` is the self-map of `E2` which keeps the `i`-th coordinate and replaces the `j`-th
  coordinate by `g`;
* `ptF p i j t s` is the point whose `i`-th coordinate is `s` and whose `j`-th coordinate is `t`.

The main mathematical content is `injective_fderiv_Phi`: the derivative of `Phi g j` at `p` is
injective as soon as the partial derivative of `g` at `p` in the direction of the `j`-th coordinate
does not vanish.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- The two coordinates of `ℝ²` are its only coordinates. -/
lemma fin2_eq_or_eq {i j : Fin 2} (hij : j ≠ i) (k : Fin 2) : k = i ∨ k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- A point of `ℝ²` is determined by two distinct coordinates. -/
lemma E2_ext {i j : Fin 2} (hij : j ≠ i) {v w : E2}
    (hi : v.ofLp i = w.ofLp i) (hj : v.ofLp j = w.ofLp j) : v = w := by
  refine PiLp.ext_iff.mpr (fun k => ?_)
  rcases fin2_eq_or_eq hij k with rfl | rfl
  · exact hi
  · exact hj

/-- The coordinate functional `v ↦ v j` as a continuous linear map. -/
noncomputable def proj (j : Fin 2) : E2 →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) j

lemma proj_apply (j : Fin 2) (v : E2) : proj j v = v.ofLp j := by
  simp [proj, EuclideanSpace.proj]


/-- The two coordinates of `ℝ²` written in the standard basis. -/
lemma E2_decomp (v : E2) :
    v = v.ofLp 0 • EuclideanSpace.single 0 (1 : ℝ)
      + v.ofLp 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  have h := (PiLp.basisFun (p := 2) ℝ (Fin 2)).sum_repr v
  rw [Fin.sum_univ_two] at h
  simp only [PiLp.basisFun_repr, PiLp.basisFun_apply] at h
  exact h.symm

/-- `Phi g j` keeps every coordinate of `v` except the `j`-th, which is replaced by `g v`. -/
noncomputable def Phi (g : E2 → ℝ) (j : Fin 2) : E2 → E2 :=
  (fun v : E2 => v) + fun v : E2 => (g v - v.ofLp j) • EuclideanSpace.single j (1 : ℝ)

@[simp] lemma Phi_apply (g : E2 → ℝ) (j : Fin 2) (v : E2) :
    Phi g j v = v + (g v - v.ofLp j) • EuclideanSpace.single j (1 : ℝ) := rfl

lemma Phi_ofLp_self (g : E2 → ℝ) (j : Fin 2) (v : E2) : (Phi g j v).ofLp j = g v := by
  simp [Phi_apply, PiLp.single_eq_same]

lemma Phi_ofLp_of_ne (g : E2 → ℝ) (j : Fin 2) (v : E2) {k : Fin 2} (hk : k ≠ j) :
    (Phi g j v).ofLp k = v.ofLp k := by
  simp [Phi_apply, PiLp.single_eq_of_ne, hk]


lemma add_smul_single_ofLp_self (h : E2) (c : ℝ) (j : Fin 2) :
    (h + c • EuclideanSpace.single j (1 : ℝ)).ofLp j = h.ofLp j + c := by
  simp [PiLp.single_eq_same]

lemma add_smul_single_ofLp_of_ne (h : E2) (c : ℝ) {j k : Fin 2} (hk : k ≠ j) :
    (h + c • EuclideanSpace.single j (1 : ℝ)).ofLp k = h.ofLp k := by
  simp [PiLp.single_eq_of_ne, hk]

/-- The parametrisation of a coordinate line: the point with `i`-th coordinate `s` and `j`-th
coordinate `t`. -/
noncomputable def ptF (p : E2) (i j : Fin 2) (t s : ℝ) : E2 :=
  p + (s - p.ofLp i) • EuclideanSpace.single i (1 : ℝ)
    + (t - p.ofLp j) • EuclideanSpace.single j (1 : ℝ)

lemma ptF_ofLp_i (p : E2) {i j : Fin 2} (hij : j ≠ i) (t s : ℝ) :
    (ptF p i j t s).ofLp i = s := by
  simp [ptF, PiLp.single_eq_same, PiLp.single_eq_of_ne, hij]

lemma ptF_ofLp_j (p : E2) {i j : Fin 2} (hij : j ≠ i) (t s : ℝ) :
    (ptF p i j t s).ofLp j = t := by
  simp [ptF, PiLp.single_eq_same, PiLp.single_eq_of_ne, hij]

/-- `Phi g j v` is the point with `i`-th coordinate `v i` and `j`-th coordinate `g v`. -/
lemma Phi_eq_ptF {g : E2 → ℝ} {i j : Fin 2} (hij : j ≠ i) (p : E2) {v : E2} {t s : ℝ}
    (hi : v.ofLp i = s) (hj : g v = t) : Phi g j v = ptF p i j t s := by
  refine E2_ext hij ?_ ?_
  · rw [Phi_ofLp_of_ne g j v (Ne.symm hij), hi, ptF_ofLp_i p hij]
  · rw [Phi_ofLp_self, hj, ptF_ofLp_j p hij]

/-- The parametrisation `s ↦ ptF p i j t s` is smooth. -/
lemma ptF_contDiff (p : E2) (i j : Fin 2) (t : ℝ) :
    ContDiff ℝ ∞ (fun s : ℝ => ptF p i j t s) := by
  unfold ptF
  fun_prop

/-- `Phi g j` is smooth wherever `g` is. -/
theorem Phi_contDiffOn {g : E2 → ℝ} {U : Set E2} (hg : ContDiffOn ℝ ∞ g U) (j : Fin 2) :
    ContDiffOn ℝ ∞ (Phi g j) U := by
  have h1 : ContDiffOn ℝ ∞ (fun v : E2 => v) U := contDiffOn_id
  have h2 : ContDiffOn ℝ ∞ (fun v : E2 => g v - v.ofLp j) U := hg.sub (by fun_prop)
  have h3 : ContDiffOn ℝ ∞
      (fun v : E2 => (g v - v.ofLp j) • EuclideanSpace.single j (1 : ℝ)) U := h2.smul_const _
  exact h1.add h3

/-- The derivative of `Phi g j` at `p` is the identity plus the `j`-th coordinate of the
differential of `g`, thrown into the `j`-th coordinate direction. -/
theorem hasFDerivAt_Phi {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {p : E2} (hp : p ∈ U) (j : Fin 2) :
    HasFDerivAt (Phi g j)
      (1 + (fderiv ℝ g p - proj j).smulRight (EuclideanSpace.single j (1 : ℝ))) p := by
  have hnz : ∞ ≠ (0 : WithTop ℕ∞) := by simp
  have hgp : HasFDerivAt g (fderiv ℝ g p) p :=
    ((hg.contDiffAt (hU.mem_nhds hp)).differentiableAt hnz).hasFDerivAt
  have hproj : HasFDerivAt (fun v : E2 => v.ofLp j) (proj j) p := by
    have h := (proj j).hasFDerivAt (x := p)
    convert h using 1
    ext v; rw [proj_apply]
  have h2 : HasFDerivAt (fun v : E2 => g v - v.ofLp j) (fderiv ℝ g p - proj j) p :=
    hgp.sub hproj
  have h3 : HasFDerivAt (fun v : E2 => (g v - v.ofLp j) • EuclideanSpace.single j (1 : ℝ))
      ((fderiv ℝ g p - proj j).smulRight (EuclideanSpace.single j (1 : ℝ))) p :=
    h2.smul_const (EuclideanSpace.single j (1 : ℝ))
  have h1 : HasFDerivAt (fun v : E2 => v) (1 : E2 →L[ℝ] E2) p := hasFDerivAt_id p
  simpa only [Phi] using h1.add h3

/-- The value of the derivative of `Phi g j` at `p`. -/
theorem fderiv_Phi {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {p : E2} (hp : p ∈ U) (j : Fin 2) (h : E2) :
    fderiv ℝ (Phi g j) p h
      = h + ((fderiv ℝ g p h) - h.ofLp j) • EuclideanSpace.single j (1 : ℝ) := by
  rw [(hasFDerivAt_Phi hU hg hp j).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.sub_apply, proj_apply]

/-- **The key linear algebra fact.**  If the partial derivative of `g` at `p` in the direction of
the `j`-th coordinate is non-zero, then the derivative of `Phi g j` at `p` is injective. -/
theorem injective_fderiv_Phi {g : E2 → ℝ} {U : Set E2} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    {p : E2} (hp : p ∈ U) (j : Fin 2)
    (hne : fderiv ℝ g p (EuclideanSpace.single j (1 : ℝ)) ≠ 0) :
    Function.Injective (fderiv ℝ (Phi g j) p) := by
  suffices hzero : ∀ h : E2, fderiv ℝ (Phi g j) p h = 0 → h = 0 by
    intro a b hab
    have h : a - b = 0 := by
      apply hzero
      rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp h
  intro h hh
  rw [fderiv_Phi hU hg hp j h] at hh
  -- the equation `h + ((dg h) - h j) • e_j = 0`
  have hj : fderiv ℝ g p h = 0 := by
    have h1 := congrArg (fun w : E2 => w.ofLp j) hh
    rw [add_smul_single_ofLp_self] at h1
    simp only [WithLp.ofLp_zero, Pi.zero_apply] at h1
    linarith
  have hk : ∀ k : Fin 2, k ≠ j → h.ofLp k = 0 := by
    intro k hkj
    have h1 := congrArg (fun w : E2 => w.ofLp k) hh
    rw [add_smul_single_ofLp_of_ne _ _ hkj] at h1
    simpa using h1
  -- hence `h` is a multiple of the `j`-th basis vector
  have hdecomp : h = h.ofLp j • EuclideanSpace.single j (1 : ℝ) := by
    have hs := (PiLp.basisFun (p := 2) ℝ (Fin 2)).sum_repr h
    rw [Finset.sum_eq_single j] at hs
    · rw [PiLp.basisFun_repr, PiLp.basisFun_apply] at hs
      simpa using hs.symm
    · intro k _ hkj
      rw [PiLp.basisFun_repr, hk k hkj, PiLp.basisFun_apply]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hje : h.ofLp j * fderiv ℝ g p (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    have h1 : (fderiv ℝ g p) (h.ofLp j • EuclideanSpace.single j (1 : ℝ)) = 0 := by
      rw [← hdecomp]; exact hj
    rw [map_smul, smul_eq_mul] at h1
    exact h1
  have : h.ofLp j = 0 := by
    rcases mul_eq_zero.mp hje with h' | h'
    · exact h'
    · exact absurd h' hne
  rw [hdecomp, this, zero_smul]

end Work.Drive.N2
