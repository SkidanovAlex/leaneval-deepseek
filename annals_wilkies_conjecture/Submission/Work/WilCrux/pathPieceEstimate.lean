import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.C1Direct.PathGainBound
import Submission.Work.WilG4c.C1Direct.FibrePartialBoundClosed

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

/-!
## Helper material for the single-piece estimate `pathPieceEstimate`

The estimate is proved by exhibiting a *potential function*

`Φ s = F s - η s + M Σ_k σ_k ψ_k(s)`,  `F s = famFun G (w₁ + s•e_i, ψ s)`,

with `σ_k = +1` on the coordinates on which `ψ_k` is monotone on `(l,r)` and `σ_k = -1` on the
coordinates on which it is antitone.  Because such a coordinate is monotone (in the direction
`σ_k`) on `(l,r)`, its derivative `d_k = ψ_k'(u)` satisfies `σ_k d_k = |d_k|` for every `u ∈ (l,r)`;
and the path derivative is `≥ η - M Σ_k |d_k|` by `hgain`, the split `fderiv_append_split` and the
fibre-partial bound `FibrePartialBoundClosed`.  Hence `Φ' ≥ 0` on `(x,y)`, so `Φ` is monotone
there, and the endpoint corrections are bounded by the sphere condition `‖ψ‖ ≤ τ`.

The fibre-direction derivative of `famFun` is computed here from the chain rule (the corresponding
declaration `Work.WilG4c.C1Direct.fderiv_famFun_fibre` is sorry-ed, so it must not be used).
-/

/-! ### The linear map `v ↦ Fin.append 0 v` -/

/-- `v ↦ Fin.append (0 : Fin a → ℝ) v`, as a continuous linear map. -/
def fibreCLM (a b : ℕ) : (Fin b → ℝ) →L[ℝ] (Fin (a + b) → ℝ) :=
  ContinuousLinearMap.pi fun s : Fin (a + b) =>
    Fin.addCases (fun _ : Fin a => (0 : (Fin b → ℝ) →L[ℝ] ℝ))
      (fun j : Fin b => ContinuousLinearMap.proj j) s

@[simp] theorem fibreCLM_apply (a b : ℕ) (v : Fin b → ℝ) :
    fibreCLM a b v = Fin.append (0 : Fin a → ℝ) v := by
  ext s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s <;>
    simp [fibreCLM, ContinuousLinearMap.pi_apply]

/-- The map `z' ↦ Fin.append w z'` is affine with linear part `fibreCLM a b`. -/
theorem hasFDerivAt_append_fixed {a b : ℕ} (w : Fin a → ℝ) (z : Fin b → ℝ) :
    HasFDerivAt (fun z' : Fin b → ℝ => Fin.append w z') (fibreCLM a b) z := by
  have h : (fun z' : Fin b → ℝ => Fin.append w z')
      = fun z' : Fin b → ℝ => Fin.append w (0 : Fin b → ℝ) + fibreCLM a b z' := by
    funext z'
    rw [fibreCLM_apply]
    ext s
    refine Fin.addCases (fun i => ?_) (fun j => ?_) s <;>
      simp [Fin.append_left, Fin.append_right, Pi.add_apply]
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt (fibreCLM a b)).const_add (Fin.append w 0)

/-- `famFun G` composed with `z' ↦ Fin.append w z'` is the slice `G w`. -/
theorem famFun_comp_append {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) :
    (Work.WilG4c.famFun G) ∘ (fun z' : Fin b → ℝ => Fin.append w z') = G w := by
  funext z'
  simp only [Function.comp_apply, Work.WilG4c.famFun, Fin.append_left, Fin.append_right]

/-- **Chain rule for the fibre direction.**  At a point where `famFun G` is differentiable, the
derivative of `famFun G` in the pure fibre direction `(0, v)` is the derivative of the slice
`G w`. -/
theorem fderiv_famFun_fibre_apply {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z v : Fin b → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)
      = fderiv ℝ (G w) z v := by
  have hcomp := famFun_comp_append G w
  have h1 : HasFDerivAt ((Work.WilG4c.famFun G) ∘ (fun z' : Fin b → ℝ => Fin.append w z'))
      ((fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)).comp (fibreCLM a b)) z :=
    hd.hasFDerivAt.comp z (hasFDerivAt_append_fixed w z)
  rw [hcomp] at h1
  rw [h1.fderiv, ContinuousLinearMap.comp_apply, fibreCLM_apply]

/-- The slices of a `famFun` that is differentiable at `(w,z)` are differentiable at `z`. -/
theorem differentiableAt_slice {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    DifferentiableAt ℝ (G w) z := by
  have hcomp := famFun_comp_append G w
  have h1 : HasFDerivAt ((Work.WilG4c.famFun G) ∘ (fun z' : Fin b → ℝ => Fin.append w z'))
      ((fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)).comp (fibreCLM a b)) z :=
    hd.hasFDerivAt.comp z (hasFDerivAt_append_fixed w z)
  rw [hcomp] at h1
  exact h1.differentiableAt

/-- **The fibre-direction derivative of `famFun G` is bounded by `M` times the `ℓ¹`-norm of the
direction.**  Here `hLipw` is the fibre-Lipschitz condition for the *fixed* parameter `w` (which is
what the path hypotheses supply). -/
theorem fibre_deriv_bound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    (z v : Fin b → ℝ) {τ M : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ) (hz : ‖z‖ ≤ τ)
    (hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (hLipw : ∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ → |G w z - G w z'| ≤ M * ‖z - z'‖) :
    |fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)| ≤ M * ∑ k, |v k| := by
  rw [fderiv_famFun_fibre_apply G w z v hC1.differentiableAt_one]
  have hdk : DifferentiableAt ℝ (G w) z := differentiableAt_slice G w z hC1.differentiableAt_one
  have hpartial : ∀ k : Fin b, |fderiv ℝ (G w) z (Pi.single k 1)| ≤ M := by
    intro k
    have h := Work.WilG4c.C1Direct.FibrePartialBoundClosed
      (fun (_ : Fin a → ℝ) (z' : Fin b → ℝ) => G w z') hM hτ
      (fun _ z₁ z₂ h₁ h₂ => hLipw z₁ z₂ h₁ h₂) w z k hz hdk
    simpa using h
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin b → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ, smul_eq_mul]
  have hmap : fderiv ℝ (G w) z v = ∑ k, v k * fderiv ℝ (G w) z (Pi.single k 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [ContinuousLinearMap.map_smul, smul_eq_mul])
  rw [hmap]
  calc |∑ k, v k * fderiv ℝ (G w) z (Pi.single k 1)|
      ≤ ∑ k, |v k * fderiv ℝ (G w) z (Pi.single k 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |v k| * M := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpartial k) (abs_nonneg _)
    _ = M * ∑ k, |v k| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### The sign of a monotone/antitone coordinate -/

/-- The sign attached to coordinate `k`: `+1` if the `k`-th coordinate of `ψ` is monotone on
`(l,r)`, and `-1` otherwise (in which case it is antitone). -/
noncomputable def pathSign {b : ℕ} (ψ : ℝ → (Fin b → ℝ)) (l r : ℝ) (k : Fin b) : ℝ :=
  if MonotoneOn (fun u => ψ u k) (Set.Ioo l r) then 1 else -1

/-- **`σ_k = ±1`, with `+1` exactly on the monotone coordinates.** -/
theorem pathSign_cases {b : ℕ} {ψ : ℝ → (Fin b → ℝ)} {l r : ℝ}
    (hmono : ∀ k : Fin b, MonotoneOn (fun u => ψ u k) (Set.Ioo l r) ∨
      AntitoneOn (fun u => ψ u k) (Set.Ioo l r)) (k : Fin b) :
    (pathSign ψ l r k = 1 ∧ MonotoneOn (fun u => ψ u k) (Set.Ioo l r)) ∨
      (pathSign ψ l r k = -1 ∧ AntitoneOn (fun u => ψ u k) (Set.Ioo l r)) := by
  by_cases hm : MonotoneOn (fun u => ψ u k) (Set.Ioo l r)
  · exact Or.inl ⟨by simp [pathSign, hm], hm⟩
  · rcases hmono k with h | h
    · exact absurd h hm
    · exact Or.inr ⟨by simp [pathSign, hm], h⟩

/-- **The key sign identity.**  On an interval avoiding the break points, a monotone (resp.
antitone) coordinate has a nonnegative (resp. nonpositive) derivative, so multiplying by the
sign `σ_k` produces the absolute value of the derivative. -/
theorem pathSign_mul_deriv_eq_abs {b : ℕ} {ψ : ℝ → (Fin b → ℝ)} {l r u : ℝ}
    (hmono : ∀ k : Fin b, MonotoneOn (fun u => ψ u k) (Set.Ioo l r) ∨
      AntitoneOn (fun u => ψ u k) (Set.Ioo l r)) (k : Fin b) (hu : u ∈ Set.Ioo l r) :
    pathSign ψ l r k * deriv (fun u => ψ u k) u = |deriv (fun u => ψ u k) u| := by
  have hmem : Set.Ioo l r ∈ 𝓝 u := isOpen_Ioo.mem_nhds hu
  rcases pathSign_cases hmono k with ⟨h1, hm⟩ | ⟨h1, ha⟩
  · have hd : 0 ≤ deriv (fun u => ψ u k) u := by
      have h : 0 ≤ derivWithin (fun u => ψ u k) (Set.Ioo l r) u := hm.derivWithin_nonneg
      rwa [derivWithin_of_mem_nhds hmem] at h
    rw [h1, one_mul, abs_of_nonneg hd]
  · have hd : deriv (fun u => ψ u k) u ≤ 0 := by
      have h : derivWithin (fun u => ψ u k) (Set.Ioo l r) u ≤ 0 := ha.derivWithin_nonpos
      rwa [derivWithin_of_mem_nhds hmem] at h
    rw [h1, neg_one_mul, abs_of_nonpos hd]

/-- **Single-piece estimate (the interior step of `PathGainBound`, N4c5).**

Let `F s := famFun G (Fin.append (w₁ + s • e_i) (ψ s))` be the path function.  If `l < x < y < r`
and the open interval `(l,r) ⊆ [0,L]` contains no break point, and on `(l,r)` every coordinate of
`ψ` is monotone or antitone, then `F y - F x ≥ η (y-x) - 2 b M τ`:  the auxiliary function
`Φ s := F s - η s + M Σ_k σ_k ψ_k(s)` (with `σ_k = 1` on monotone coordinates, `-1` on antitone
ones) has nonnegative derivative everywhere on `(x,y)`, hence is monotone there, and each
`V_k = σ_k ψ_k` is squeezed by `‖ψ‖ ≤ τ`.

NOTE: the result must be axiom-clean.  Do NOT use any declaration that currently has a `sorry`
(in particular `Work.WilG4c.C1Direct.path_piece_bound` and
`Work.WilG4c.C1Direct.fderiv_famFun_fibre` are sorry-ed and must not be used); you may use the
sorry-free helpers in `Submission.Work.WilG4c.C1Direct.PathGainBound`
(`path_hasDerivAt`, `fderiv_append_split`) and
`Submission.Work.WilG4c.C1Direct.FibrePartialBoundClosed`, or prove what you need yourself. -/
theorem pathPieceEstimate {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (L τ M η : ℝ) (hτ : 0 < τ) (hM : 0 ≤ M)
    (ψ : ℝ → (Fin b → ℝ)) (brk : Finset ℝ)
    (hsph : ∀ s ∈ Set.Icc 0 L, ‖ψ s‖ ≤ τ)
    (hdiff : ∀ s ∈ Set.Ioo 0 L, s ∉ brk → DifferentiableAt ℝ ψ s)
    (hLip : ∀ s ∈ Set.Icc 0 L, ∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G (w₁ + s • Pi.single i 1) z - G (w₁ + s • Pi.single i 1) z'| ≤ M * ‖z - z'‖)
    (hC1 : ∀ s ∈ Set.Icc 0 L, ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)))
    (hgain : ∀ s ∈ Set.Icc 0 L, η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0))
    {l r x y : ℝ} (hl0 : 0 ≤ l) (hlx : l < x) (hxy : x < y) (hyr : y < r) (hrL : r ≤ L)
    (hno : ∀ u ∈ Set.Ioo l r, u ∉ brk)
    (hmono : ∀ k : Fin b, MonotoneOn (fun u => ψ u k) (Set.Ioo l r) ∨
      AntitoneOn (fun u => ψ u k) (Set.Ioo l r)) :
    Work.WilG4c.famFun G (Fin.append (w₁ + y • Pi.single i 1) (ψ y))
      - Work.WilG4c.famFun G (Fin.append (w₁ + x • Pi.single i 1) (ψ x))
      ≥ η * (y - x) - 2 * ((b : ℝ)) * M * τ := by
  -- ## elementary interval facts
  have hx0 : 0 ≤ x := le_trans hl0 (le_of_lt hlx)
  have hy0 : 0 ≤ y := le_trans hx0 (le_of_lt hxy)
  have hyL : y ≤ L := le_of_lt (lt_of_lt_of_le hyr hrL)
  have hxL : x ≤ L := le_trans (le_of_lt hxy) hyL
  have hxmem : x ∈ Set.Ioo l r := ⟨hlx, lt_trans hxy hyr⟩
  have hymem : y ∈ Set.Ioo l r := ⟨lt_trans hlx hxy, hyr⟩
  have hxsph : ‖ψ x‖ ≤ τ := hsph x ⟨hx0, hxL⟩
  have hysph : ‖ψ y‖ ≤ τ := hsph y ⟨hy0, hyL⟩
  -- ## the path function, the sign vector, the potential
  set F : ℝ → ℝ :=
    fun s => Work.WilG4c.famFun G (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) with hF
  set Ψ : ℝ → ℝ := fun s => ∑ k, pathSign ψ l r k * ψ s k with hΨ
  set Φ : ℝ → ℝ := fun s => F s - η * s + M * Ψ s with hΦ
  set D : ℝ → ℝ := fun u =>
    (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + u • Pi.single i 1) (ψ u))
      (Fin.append (Pi.single i 1) (fderiv ℝ ψ u 1))) - η
      + M * ∑ k, pathSign ψ l r k * (fderiv ℝ ψ u 1) k with hD
  have hFapp : ∀ s : ℝ, F s
      = Work.WilG4c.famFun G (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) := by
    intro s; rw [hF]
  -- ## the pointwise derivative computation
  have hpoint : ∀ u ∈ Set.Icc x y, HasDerivAt Φ (D u) u ∧ 0 ≤ D u := by
    intro u hu
    have hux : x ≤ u := hu.1
    have huy : u ≤ y := hu.2
    have hulu : l < u := lt_of_lt_of_le hlx hux
    have huur : u < r := lt_of_le_of_lt huy hyr
    have hu_lr : u ∈ Set.Ioo l r := ⟨hulu, huur⟩
    have hu0 : 0 ≤ u := le_trans hx0 hux
    have huL : u ≤ L := le_trans huy hyL
    have hu0L : u ∈ Set.Icc (0 : ℝ) L := ⟨hu0, huL⟩
    have hu0L' : u ∈ Set.Ioo (0 : ℝ) L := ⟨lt_of_le_of_lt hl0 hulu, lt_of_lt_of_le huur hrL⟩
    have hunb : u ∉ brk := hno u hu_lr
    have hC1u : ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
        (Fin.append (w₁ + u • Pi.single i 1) (ψ u)) := hC1 u hu0L
    have hdu : DifferentiableAt ℝ ψ u := hdiff u hu0L' hunb
    -- the path function is differentiable at `u`
    have hFd : HasDerivAt F (fderiv ℝ (Work.WilG4c.famFun G)
        (Fin.append (w₁ + u • Pi.single i 1) (ψ u))
        (Fin.append (Pi.single i 1) (fderiv ℝ ψ u 1))) u := by
      rw [hF]
      exact Work.WilG4c.C1Direct.path_hasDerivAt G i w₁ ψ hC1u hdu
    -- split off the fibre direction and bound it
    have hsplit := Work.WilG4c.C1Direct.fderiv_append_split (Work.WilG4c.famFun G)
      (Fin.append (w₁ + u • Pi.single i 1) (ψ u)) (Pi.single i 1) (fderiv ℝ ψ u 1)
    have hgainu : η ≤ fderiv ℝ (Work.WilG4c.famFun G)
        (Fin.append (w₁ + u • Pi.single i 1) (ψ u)) (Fin.append (Pi.single i 1) 0) :=
      hgain u hu0L
    have hfib := fibre_deriv_bound G (w₁ + u • Pi.single i 1) (ψ u) (fderiv ℝ ψ u 1)
      hM hτ (hsph u hu0L) hC1u (hLip u hu0L)
    have hdf : η - M * ∑ k, |(fderiv ℝ ψ u 1) k| ≤
        fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + u • Pi.single i 1) (ψ u))
          (Fin.append (Pi.single i 1) (fderiv ℝ ψ u 1)) := by
      rw [hsplit]
      have h2 : -(M * ∑ k, |(fderiv ℝ ψ u 1) k|) ≤
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + u • Pi.single i 1) (ψ u))
            (Fin.append (0 : Fin a → ℝ) (fderiv ℝ ψ u 1)) := neg_le_of_abs_le hfib
      linarith
    -- the sign identity for the fibre direction
    have hsign : ∑ k, pathSign ψ l r k * (fderiv ℝ ψ u 1) k
        = ∑ k, |(fderiv ℝ ψ u 1) k| := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hdk : (fderiv ℝ ψ u 1) k = deriv (fun u => ψ u k) u :=
        (HasDerivAt.deriv (hasDerivAt_pi.mp hdu.hasFDerivAt.hasDerivAt k)).symm
      rw [hdk]
      exact pathSign_mul_deriv_eq_abs hmono k hu_lr
    have hDnn : 0 ≤ D u := by
      simp only [hD]
      rw [hsign]
      linarith [hdf]
    refine ⟨?_, hDnn⟩
    simp only [hD, hΦ]
    have hlin : HasDerivAt (fun s : ℝ => η * s) η u := by
      simpa using (hasDerivAt_id u).const_mul η
    have hΨd : HasDerivAt Ψ (∑ k, pathSign ψ l r k * (fderiv ℝ ψ u 1) k) u := by
      have hsum := HasDerivAt.sum (u := Finset.univ)
        (A := fun k (s : ℝ) => pathSign ψ l r k * ψ s k)
        (A' := fun k => pathSign ψ l r k * (fderiv ℝ ψ u 1) k) (x := u)
        (fun k _ => (hasDerivAt_pi.mp hdu.hasFDerivAt.hasDerivAt k).const_mul
          (pathSign ψ l r k))
      have hfun : (∑ k, fun s : ℝ => pathSign ψ l r k * ψ s k) = Ψ := by
        rw [hΨ]
        funext s
        rw [Finset.sum_apply]
      rwa [hfun] at hsum
    have h1 := (hFd.sub hlin).add (hΨd.const_mul M)
    exact h1
  have hΦd_all : ∀ u ∈ Set.Icc x y, HasDerivAt Φ (D u) u := fun u hu => (hpoint u hu).1
  have hDnn_all : ∀ u ∈ Set.Icc x y, 0 ≤ deriv Φ u := by
    intro u hu
    rw [(hpoint u hu).1.deriv]
    exact (hpoint u hu).2
  -- ## monotonicity of the potential on `[x,y]`
  have hmonoΦ : MonotoneOn Φ (Set.Icc x y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc x y) ?_ ?_ ?_
    · intro u hu
      exact (hΦd_all u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact ((hΦd_all u ⟨le_of_lt hu.1, le_of_lt hu.2⟩).differentiableAt).differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact hDnn_all u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hΦxy : Φ x ≤ Φ y := hmonoΦ ⟨le_rfl, le_of_lt hxy⟩ ⟨le_of_lt hxy, le_rfl⟩ (le_of_lt hxy)
  -- ## the endpoint correction
  have hterm : ∀ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k) ≤ 2 * τ := by
    intro k
    have hyk : |ψ y k| ≤ τ := by
      have h := norm_le_pi_norm (ψ y) k
      rw [Real.norm_eq_abs] at h
      exact h.trans hysph
    have hxk : |ψ x k| ≤ τ := by
      have h := norm_le_pi_norm (ψ x) k
      rw [Real.norm_eq_abs] at h
      exact h.trans hxsph
    rcases pathSign_cases hmono k with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, one_mul]
      linarith [(abs_le.mp hyk).2, (abs_le.mp hxk).1]
    · rw [h1, neg_one_mul]
      linarith [(abs_le.mp hyk).1, (abs_le.mp hxk).2]
  have hbound0 : ∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k) ≤ 2 * (b : ℝ) * τ := by
    calc ∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k) ≤ ∑ _k : Fin b, (2 * τ) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 2 * (b : ℝ) * τ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- ## assemble
  have h0 : 0 ≤ Φ y - Φ x := sub_nonneg.mpr hΦxy
  have h0' : 0 ≤ (F y - F x) - η * (y - x)
      + M * (∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k)) := by
    have hΨdiff : Ψ y - Ψ x
        = ∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k) := by
      simp only [hΨ]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hexp : Φ y - Φ x = (F y - F x) - η * (y - x)
        + M * (∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k)) := by
      simp only [hΦ]
      rw [show (F y - η * y + M * Ψ y) - (F x - η * x + M * Ψ x)
          = (F y - F x) - η * (y - x) + M * (Ψ y - Ψ x) from by ring, hΨdiff]
    rwa [hexp] at h0
  have hfin : η * (y - x) - 2 * (b : ℝ) * M * τ ≤ F y - F x := by
    have hb1 : M * (∑ k : Fin b, pathSign ψ l r k * (ψ y k - ψ x k))
        ≤ M * (2 * (b : ℝ) * τ) := mul_le_mul_of_nonneg_left hbound0 hM
    have hrw : M * (2 * (b : ℝ) * τ) = 2 * (b : ℝ) * M * τ := by ring
    linarith [h0', hb1, hrw]
  rw [hFapp y, hFapp x] at hfin
  exact hfin

end Work.WilCrux
