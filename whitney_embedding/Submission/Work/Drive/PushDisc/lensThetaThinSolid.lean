import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs
import Submission.Work.Drive.PushDisc.lensWiringConfig
import Submission.Work.Drive.PushDisc.lensThetaGlobal
import Submission.Work.Drive.PushDisc.lensThetaRows
import Submission.Work.Drive.PushDisc.thetaMapDefs
import Submission.Work.Drive.PushDisc.lensNhd
import Submission.Work.Drive.PushDisc.exists_open_injOn_det_ne
import Submission.Work.Drive.PushDisc.exists_globalDiffeo_mdl
import Submission.Work.Drive.PushDisc.boxInjImm
import Submission.Work.Drive.PushDisc.extendSmoothWindow
import Submission.Work.Drive.PushDisc.thetaDiscInjective
import Submission.Work.Drive.PushDisc.lensRowPoints_mem_cthickening

/-!
# `lensThetaThinSolid`: the thin globalisation `D3` of the `θ`-assembly

This file builds a `Work.Drive.PushDisc.LWTheta` datum out of the lens wiring data
(`LWConfig`, `LWFlatTube`, `LWFingerChart`, `LWFingerData`, `LWLensDisc`, `LWFrames`): a global
`C^∞` diffeomorphism `Θg` of the model space `Mdl k = ℝ × ℝ × ℝ^k × ℝ^k` with the three rows

* `Θg (x, 0, u, 0) = (x, 0, u, 0)` for `|x| ≤ X''`, `‖u‖ ≤ ε` (the thin plane tube),
* `Θg (x, y, 0, 0) = Δ (x, y)` on the lens disc (`0 ≤ y ≤ arch x`),
* `Θg (x, arch x, 0, w) = S₂ (x, r • w)` for `|x| < X''`, `‖w‖ < 1` (the finger).

## The construction

Write `θ = thetaMap Δ U W S₂ arch 1`.  The three rows above are *algebraic identities* for `θ`
(on the windows where the data rows hold), so the only issue is turning `θ` into a global
diffeomorphism without destroying them.

* The set of points where `fderiv θ` is injective is open and contains the *lens disc*
  `K₀ = {(x, y, 0, 0) | (x, y) ∈ lensK}` — the derivative of `θ` on the plane `{u = 0, v = 0}` is
  the framing `[∂ₓΔ, ∂_yΔ, U, W]`, independent on the lens by `LWFrames.hframe`
  (`thetaDiscInjective`).  Injectivity of `θ` on `K₀` is `Δ`'s injectivity.
* Hence (openness of the immersion + the inverse function theorem + local injectivity on a compact
  set) there is `δ > 0` with `θ` injective and immersive on the compact convex set
  `C = cthickening δ K₀`, and `exists_open_injOn_det_ne` + `exists_globalDiffeo_mdl` turn `θ` into a
  global diffeomorphism `Γ` agreeing with `θ` on an open neighbourhood `O' ⊇ C` (post-composing with
  `flipX` when the Jacobian sign is negative).
* The tube row and the finger row of `LWTheta` are read off `C`: the tube points
  `(x, 0, u, 0)` and the finger points `(x, arch x, 0, lam • w)` are within `δ` of `K₀` as soon as
  `X'' - 1`, `ε`, `lam` are small enough (`lensRowPoints_mem_cthickening`).
* The finger row is the one place where the *domain* thickness matters: `LWTheta.hfinger` evaluates
  `Θg` at `v = w` with `‖w‖ < 1`, which is far from `K₀`.  This is handled by scaling the `v`
  variable: `Θg := Γ ∘ Λ` with `Λ (x,y,u,v) = (x,y,u,lam • v)`.  Then
  `Θg (x, arch x, 0, w) = Γ (x, arch x, 0, lam • w) = θ (x, arch x, 0, lam • w) = S₂ (x, lam • w)`,
  and `r := lam` is the `r` of the structure.  Since `Lam` is a diffeomorphism of the model space,
  `Θg` is one too.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold
open Set Metric

noncomputable section

variable {k : ℕ}

/-! ## The lens disc of the model space -/

/-- The affine embedding `(x,y) ↦ (x,y,0,0)` of the `(x,y)`-plane into the model space. -/
private noncomputable def lensEmb (k : ℕ) : (ℝ × ℝ) →ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun p := (p.1, p.2, 0, 0)
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' a p := by ext <;> simp

@[simp] private theorem lensEmb_apply (p : ℝ × ℝ) :
    lensEmb k p = ((p.1, p.2, 0, 0) : Work.Drive.Whitney.Mdl k) := rfl

/-- The **lens disc** of the model space: the lens `lensK` in the plane `{u = 0, v = 0}`. -/
private def lensDisc (k : ℕ) : Set (Work.Drive.Whitney.Mdl k) :=
  {ξ | (ξ.1, ξ.2.1) ∈ lensK ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0}

private theorem lensDisc_eq_image : lensDisc k = lensEmb k '' lensK := by
  ext ξ
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(ξ.1, ξ.2.1), h1, by ext <;> simp [h2, h3]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, rfl, rfl⟩

private theorem isCompact_lensDisc : IsCompact (lensDisc k) :=
  lensDisc_eq_image ▸ isCompact_lensK.image (LinearMap.continuous_of_finiteDimensional (lensEmb k))

private theorem convex_lensDisc : Convex ℝ (lensDisc k) :=
  lensDisc_eq_image ▸ convex_lensK.linear_image (lensEmb k)

private theorem zero_mem_lensDisc : (0 : Work.Drive.Whitney.Mdl k) ∈ lensDisc k := by
  refine ⟨?_, rfl, rfl⟩
  refine ⟨by norm_num, le_refl 0, ?_⟩
  norm_num [arch]

/-- **The scaling `Λ` of the `v`-variable**, and its inverse. -/
private noncomputable def kapU (k : ℕ) (lam : ℝ) : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k :=
  fun ξ => (ξ.1, ξ.2.1, ξ.2.2.1, lam • ξ.2.2.2)

private noncomputable def kapUi (k : ℕ) (lam : ℝ) : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k :=
  fun ξ => (ξ.1, ξ.2.1, ξ.2.2.1, lam⁻¹ • ξ.2.2.2)

@[simp] private theorem kapU_apply (lam : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    kapU k lam ξ = (ξ.1, ξ.2.1, ξ.2.2.1, lam • ξ.2.2.2) := rfl

@[simp] private theorem kapUi_apply (lam : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    kapUi k lam ξ = (ξ.1, ξ.2.1, ξ.2.2.1, lam⁻¹ • ξ.2.2.2) := rfl

private theorem kapU_leftInverse {lam : ℝ} (h : lam ≠ 0) :
    Function.LeftInverse (kapUi k lam) (kapU k lam) := by
  intro ξ
  ext <;> simp [smul_smul, inv_mul_cancel₀ h]

private theorem kapU_rightInverse {lam : ℝ} (h : lam ≠ 0) :
    Function.RightInverse (kapUi k lam) (kapU k lam) := by
  intro ξ
  ext <;> simp [smul_smul, mul_inv_cancel₀ h]

private theorem contDiff_kapU (lam : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kapU k lam) := by
  rw [show kapU k lam = (fun ξ : Work.Drive.Whitney.Mdl k =>
    (ξ.1, ξ.2.1, ξ.2.2.1, lam • ξ.2.2.2)) from rfl]
  fun_prop

private theorem contDiff_kapUi (lam : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (kapUi k lam) := by
  rw [show kapUi k lam = (fun ξ : Work.Drive.Whitney.Mdl k =>
    (ξ.1, ξ.2.1, ξ.2.2.1, lam⁻¹ • ξ.2.2.2)) from rfl]
  fun_prop


/-- The arch is smooth. -/
private theorem contDiff_arch' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := by
  rw [show arch = (fun x : ℝ => 1 - x ^ 2) from rfl]
  fun_prop

/-! ## The three rows of `thetaMap`, with the data rows restricted to a window -/

/-- **The plane row of `thetaMap`** (window version). -/
private theorem thetaMap_plane_of_le {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ) (r X : ℝ)
    (hΔ : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hU : ∀ x : ℝ, U (x, 0) = iotaU k)
    (hS₂ : ∀ x : ℝ, |x| ≤ X → S₂ (x, 0) = Δ (x, c x))
    (x : ℝ) (hx : |x| ≤ X) (u : EuclideanSpace ℝ (Fin k)) :
    thetaMap Δ U W S₂ c r (x, 0, u, 0) = (x, 0, u, 0) := by
  have hbracket : S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
      - (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin k) => S₂ (x, v)) 0)
          (r • (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
    rw [smul_zero, map_zero, sub_zero, hS₂ x hx, sub_self]
  have hsumW : (∑ j : Fin k, (r * ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k).2.2.2 j)
      • W (x, 0) j) = 0 := by simp
  rw [thetaMap, hbracket, add_zero, hsumW, add_zero, hU x, hΔ x]
  rw [sum_smul_iotaU k u]
  ext <;> simp

/-- **The disc row of `thetaMap`** (window version). -/
private theorem thetaMap_disc_of_le {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ) (r X : ℝ)
    (hΔ : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hS₂ : ∀ x : ℝ, |x| ≤ X → S₂ (x, 0) = Δ (x, c x))
    (x y : ℝ) (hx : |x| ≤ X) (hy0 : 0 ≤ y) (hy1 : y ≤ c x) :
    thetaMap Δ U W S₂ c r (x, y, 0, 0) = Δ (x, y) := by
  simp only [thetaMap]
  show Δ (x, y) + (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, y) i)
        + (∑ j : Fin k, (r * (0 : EuclideanSpace ℝ (Fin k)) j) • W (x, y) j)
        + (S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
            - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
                (r • (0 : EuclideanSpace ℝ (Fin k)))) = Δ (x, y)
  have h1 : (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, y) i) = 0 := by simp
  have h2 : (∑ j : Fin k, (r * (0 : EuclideanSpace ℝ (Fin k)) j) • W (x, y) j) = 0 := by simp
  have h3 : S₂ (x, r • (0 : EuclideanSpace ℝ (Fin k))) - Δ (x, c x)
      - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0)
          (r • (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
    rw [smul_zero, map_zero, sub_zero, hS₂ x hx, sub_self]
  rw [h1, h2, h3]
  simp

/-- **The finger row of `thetaMap`** (window version). -/
private theorem thetaMap_finger_of_le {k : ℕ} (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (S₂ : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k) (c : ℝ → ℝ) (r X : ℝ)
    (hWc : ∀ x : ℝ, |x| ≤ X → W (x, c x) = V x)
    (hV : ∀ x : ℝ, |x| ≤ X → ∀ w : EuclideanSpace ℝ (Fin k),
      (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => S₂ (x, w')) 0) w
        = ∑ j : Fin k, w j • V x j)
    (x : ℝ) (hx : |x| ≤ X) (v : EuclideanSpace ℝ (Fin k)) :
    thetaMap Δ U W S₂ c r (x, c x, 0, v) = S₂ (x, r • v) := by
  simp only [thetaMap]
  show Δ (x, c x) + (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, c x) i)
        + (∑ j : Fin k, (r * v j) • W (x, c x) j)
        + (S₂ (x, r • v) - Δ (x, c x)
            - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0) (r • v))
      = S₂ (x, r • v)
  have h1 : (∑ i : Fin k, (0 : EuclideanSpace ℝ (Fin k)) i • U (x, c x) i) = 0 := by simp
  have h2 : (∑ j : Fin k, (r * v j) • W (x, c x) j)
      = (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => S₂ (x, w)) 0) (r • v) := by
    rw [hV x hx (r • v)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hWc x hx]
    congr 2
  rw [h1, h2]
  abel


/-! ## The target -/

theorem lensThetaThinSolid {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F)
    (D : Work.Drive.PushDisc.LWLensDisc k M C T F G)
    (Fr : Work.Drive.PushDisc.LWFrames k M C T F G D) :
    Nonempty (Work.Drive.PushDisc.LWTheta k M C T F G D Fr) := by
  classical
  -- ### the map `θ` of the assembly
  set θ : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k :=
    thetaMap D.Δ Fr.U Fr.W G.S₂ arch (1 : ℝ) with hθdef
  -- ### the row `S₂ (x,0) = Δ (x, arch x)` on the window
  have hS₂row : ∀ x : ℝ, |x| ≤ F.X' → G.S₂ (x, 0) = D.Δ (x, arch x) := by
    intro x hx
    have h1 : G.S₂ (x, 0) = T.Φ₀ (C.f (F.c.symm (splitE k (x, 0)))) :=
      G.hS₂ag (x, 0) hx (by simpa using F.hr.le)
    rw [h1, D.hΔ1 x hx]
    exact h1.symm
  -- ### the three rows of `θ`
  have hθplane : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ F.X' →
      θ (x, 0, u, 0) = (x, 0, u, 0) := by
    intro x u hx
    rw [hθdef]
    exact thetaMap_plane_of_le D.Δ Fr.U Fr.W G.S₂ arch 1 F.X' (fun y => D.hΔ0 y)
      (fun y => Fr.hU0 y) (fun y hy => hS₂row y hy) x hx u
  have hθdisc : ∀ x y : ℝ, |x| ≤ F.X' → 0 ≤ y → y ≤ arch x →
      θ (x, y, 0, 0) = D.Δ (x, y) := by
    intro x y hx hy0 hy1
    rw [hθdef]
    exact thetaMap_disc_of_le D.Δ Fr.U Fr.W G.S₂ arch 1 F.X' (fun y => D.hΔ0 y)
      (fun y hy => hS₂row y hy) x y hx hy0 hy1
  have hθfinger : ∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)), |x| ≤ min F.X' Fr.X' →
      θ (x, arch x, 0, v) = G.S₂ (x, v) := by
    intro x v hx
    rw [hθdef]
    simpa using thetaMap_finger_of_le D.Δ Fr.U Fr.W G.S₂ G.V arch 1 (min F.X' Fr.X')
      (fun y hy => Fr.hWtop y (le_trans hy (min_le_right _ _)))
      (fun y hy w => G.hVdef y w (le_trans hy (min_le_left _ _))) x hx v
  -- ### `θ` is smooth
  have hθsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    rw [hθdef]
    have hfun : thetaMap D.Δ Fr.U Fr.W G.S₂ arch (1 : ℝ)
        = (fun ξ : Work.Drive.Whitney.Mdl k =>
          D.Δ (ξ.1, ξ.2.1) + (∑ i : Fin k, ξ.2.2.1 i • Fr.U (ξ.1, ξ.2.1) i)
            + (∑ j : Fin k, ((1 : ℝ) * ξ.2.2.2 j) • Fr.W (ξ.1, ξ.2.1) j)
            + (G.S₂ (ξ.1, (1 : ℝ) • ξ.2.2.2) - D.Δ (ξ.1, arch ξ.1)
                - (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin k) => G.S₂ (ξ.1, w)) 0)
                    ((1 : ℝ) • ξ.2.2.2))) := by
      funext ξ; rfl
    rw [hfun]
    have hΔc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D.Δ := D.hΔsm
    have hUc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr.U := Fr.hUsm
    have hWc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr.W := Fr.hWsm
    have hS₂c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G.S₂ := G.hS₂sm
    have harchc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := contDiff_arch'
    fun_prop
  -- ### `fderiv θ` is injective on the lens disc (THE DELEGATED BRICK)
  have hImmDisc : ∀ p ∈ lensK, Function.Injective (fderiv ℝ θ (p.1, p.2, 0, 0)) := by
    set X₀ : ℝ := min F.X' Fr.X' with hX₀
    have hX₀1 : 1 < X₀ := lt_min F.hX' Fr.hX'
    have hS₂₀ : ∀ x : ℝ, |x| ≤ X₀ → G.S₂ (x, 0) = D.Δ (x, arch x) :=
      fun x hx => hS₂row x (le_trans hx (min_le_left _ _))
    have hWc : ∀ x : ℝ, |x| ≤ X₀ → Fr.W (x, arch x) = G.V x :=
      fun x hx => Fr.hWtop x (le_trans hx (min_le_right _ _))
    have hVd : ∀ x : ℝ, |x| ≤ X₀ → ∀ w : EuclideanSpace ℝ (Fin k),
        (fderiv ℝ (fun w' : EuclideanSpace ℝ (Fin k) => G.S₂ (x, w')) 0) w
          = ∑ j : Fin k, w j • G.V x j :=
      fun x hx w => G.hVdef x w (le_trans hx (min_le_left _ _))
    intro p hp
    rw [hθdef]
    exact thetaDiscInjective D.Δ Fr.U Fr.W G.S₂ G.V arch 1 X₀ one_pos hX₀1 D.hΔsm Fr.hUsm
      Fr.hWsm G.hS₂sm contDiff_arch' hS₂₀ hWc hVd Fr.hframe p hp
  -- ### the point `0` of the good set, and the openness of the good set
  have hGoodOpen : IsOpen {ξ : Work.Drive.Whitney.Mdl k |
      Function.Injective (fderiv ℝ θ ξ)} :=
    ContinuousLinearMap.isOpen_injective.preimage (hθsm.continuous_fderiv (by simp))
  have hDiscGood : lensDisc k ⊆ {ξ : Work.Drive.Whitney.Mdl k |
      Function.Injective (fderiv ℝ θ ξ)} := by
    rintro ξ ⟨h1, h2, h3⟩
    have hξ : ξ = ((ξ.1, ξ.2.1, 0, 0) : Work.Drive.Whitney.Mdl k) := by
      ext <;> simp [h2, h3]
    rw [hξ]
    exact hImmDisc (ξ.1, ξ.2.1) h1
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ :=
    isCompact_lensDisc.exists_cthickening_subset_open hGoodOpen hDiscGood
  -- ### `θ` is injective on the lens disc
  have hθinjDisc : Set.InjOn θ (lensDisc k) := by
    rintro ξ ⟨h1, h2, h3⟩ η ⟨h1', h2', h3'⟩ hξη
    have hξ : ξ = ((ξ.1, ξ.2.1, 0, 0) : Work.Drive.Whitney.Mdl k) := by
      ext <;> simp [h2, h3]
    have hη : η = ((η.1, η.2.1, 0, 0) : Work.Drive.Whitney.Mdl k) := by
      ext <;> simp [h2', h3']
    have hmemξ : |ξ.1| ≤ F.X' := le_trans h1.1 F.hX'.le
    have hmemη : |η.1| ≤ F.X' := le_trans h1'.1 F.hX'.le
    have e1 : θ ξ = D.Δ (ξ.1, ξ.2.1) := by
      rw [hξ]
      exact hθdisc ξ.1 ξ.2.1 hmemξ h1.2.1 h1.2.2
    have e2 : θ η = D.Δ (η.1, η.2.1) := by
      rw [hη]
      exact hθdisc η.1 η.2.1 hmemη h1'.2.1 h1'.2.2
    have hval : D.Δ (ξ.1, ξ.2.1) = D.Δ (η.1, η.2.1) := by
      rw [← e1, ← e2]
      exact hξη
    have hpair : (ξ.1, ξ.2.1) = (η.1, η.2.1) := D.hΔinj h1 h1' hval
    have hp := Prod.ext_iff.mp hpair
    rw [hξ, hη]
    exact Prod.ext hp.1 (Prod.ext hp.2 (Prod.ext rfl rfl))
  -- ### the inverse function theorem: `θ` is injective on a neighbourhood of the disc
  have hloc : ∀ x ∈ lensDisc k, ∃ O : Set (Work.Drive.Whitney.Mdl k),
      IsOpen O ∧ x ∈ O ∧ Set.InjOn θ O :=
    fun x hx => local_injOn_of_injective_fderiv_normed isOpen_univ (Set.mem_univ x)
      hθsm.contDiffOn (hDiscGood hx)
  obtain ⟨Oinj, hOinjopen, hDiscOinj, hOinjinj⟩ :=
    Work.Routing.injOn_nhds_of_compact_of_locallyInjOn isCompact_lensDisc hloc
      (fun x _ => hθsm.continuous.continuousAt) hθinjDisc
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    isCompact_lensDisc.exists_cthickening_subset_open hOinjopen hDiscOinj
  -- ### the compact convex set `C` on which `θ` is injective and immersive
  set δ : ℝ := min (min δ₁ δ₂) 1 with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁pos hδ₂pos) one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδle₁ : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  set Cc : Set (Work.Drive.Whitney.Mdl k) := Metric.cthickening δ (lensDisc k) with hCcdef
  have hCccompact : IsCompact Cc := isCompact_lensDisc.cthickening
  have hCcconvex : Convex ℝ Cc := convex_lensDisc.cthickening δ
  have h0Cc : (0 : Work.Drive.Whitney.Mdl k) ∈ Cc :=
    Metric.self_subset_cthickening (lensDisc k) zero_mem_lensDisc
  have hCcgood : Cc ⊆ {ξ : Work.Drive.Whitney.Mdl k |
      Function.Injective (fderiv ℝ θ ξ)} :=
    (Metric.cthickening_mono hδle₁ (lensDisc k)).trans hδ₁sub
  have hCcinj : Set.InjOn θ Cc :=
    hOinjinj.mono ((Metric.cthickening_mono hδle₂ (lensDisc k)).trans hδ₂sub)
  obtain ⟨O, hOopen, hCO, hInjO, hsign⟩ :=
    exists_open_injOn_det_ne θ hθsm Cc hCccompact (hCcconvex.starConvex h0Cc) h0Cc
      (fun ξ hξ => hCcgood hξ) hCcinj
  -- ### globalisation of `θ` (up to the orientation flip)
  obtain ⟨Γ, Γi, hΓsm, hΓism, hlΓ, hrΓ, O', hO'open, hCO', hagr⟩ :
      ∃ (Γ Γi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γi ∧
        Function.LeftInverse Γi Γ ∧ Function.RightInverse Γi Γ ∧
        ∃ O' : Set (Work.Drive.Whitney.Mdl k), IsOpen O' ∧ Cc ⊆ O' ∧
          ∀ ξ ∈ O', Γ ξ = θ ξ := by
    rcases hsign with hpos | hneg
    · obtain ⟨Ξ, Ξi, hΞsm, hΞism, hl, hr, O', hO', hCO', hO'O, hagr⟩ :=
        exists_globalDiffeo_mdl Cc hCccompact (hCcconvex.starConvex h0Cc) O hOopen hCO θ
          hθsm.contDiffOn hInjO hpos
      exact ⟨Ξ, Ξi, hΞsm, hΞism, hl, hr, O', hO', hCO', hagr⟩
    · have hφsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun ξ : Work.Drive.Whitney.Mdl k => flipX k (θ ξ)) := contDiff_flipX_comp hθsm
      have hφinj : Set.InjOn (fun ξ : Work.Drive.Whitney.Mdl k => flipX k (θ ξ)) O :=
        injOn_flipX_comp hInjO
      have hφdet : ∀ ξ ∈ O,
          0 < (fderiv ℝ (fun ξ : Work.Drive.Whitney.Mdl k => flipX k (θ ξ)) ξ).toLinearMap.det := by
        intro ξ hξ
        rw [det_fderiv_flipX_comp θ ξ ((hθsm.differentiable (by simp)).differentiableAt)]
        linarith [hneg ξ hξ]
      obtain ⟨Ξ, Ξi, hΞsm, hΞism, hl, hr, O', hO', hCO', hO'O, hagr⟩ :=
        exists_globalDiffeo_mdl Cc hCccompact (hCcconvex.starConvex h0Cc) O hOopen hCO
          (fun ξ : Work.Drive.Whitney.Mdl k => flipX k (θ ξ)) hφsm.contDiffOn hφinj hφdet
      refine ⟨fun ξ => flipX k (Ξ ξ), fun ξ => Ξi (flipX k ξ), ?_, ?_, ?_, ?_, O', hO', hCO', ?_⟩
      · exact (contDiff_flipX k).comp hΞsm
      · exact hΞism.comp (contDiff_flipX k)
      · intro ξ
        change Ξi (flipX k (flipX k (Ξ ξ))) = ξ
        rw [flipX_flipX]
        exact hl ξ
      · intro ξ
        change flipX k (Ξ (Ξi (flipX k ξ))) = ξ
        rw [hr (flipX k ξ), flipX_flipX]
      · intro ξ hξ
        change flipX k (Ξ ξ) = θ ξ
        rw [hagr ξ hξ, flipX_flipX]
  -- ### the parameters
  set eps : ℝ := δ / 4 with hepsdef
  have hepspos : 0 < eps := by rw [hepsdef]; linarith
  have hepsle : eps ≤ δ := by rw [hepsdef]; linarith
  set lam : ℝ := min (δ / 4) F.r with hlamdef
  have hlamp : 0 < lam := lt_min (by linarith) F.hr
  have hlamF : lam ≤ F.r := min_le_right _ _
  have hlamδ : lam ≤ δ / 4 := min_le_left _ _
  have h1δ : (1 : ℝ) < 1 + δ / 4 := by linarith
  have hm : (1 : ℝ) < min (min F.X' Fr.X') (1 + δ / 4) := lt_min (lt_min F.hX' Fr.hX') h1δ
  set X'' : ℝ := (1 + min (min F.X' Fr.X') (1 + δ / 4)) / 2 with hX''def
  have hX''lt : X'' < min (min F.X' Fr.X') (1 + δ / 4) := by rw [hX''def]; linarith
  have hX''1 : 1 < X'' := by rw [hX''def]; linarith
  have hX''F : X'' ≤ F.X' :=
    le_trans hX''lt.le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hX''Fr : X'' ≤ Fr.X' :=
    le_trans hX''lt.le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hX''δ : X'' ≤ 1 + δ / 4 := le_trans hX''lt.le (min_le_right _ _)
  -- ### the row points lie in `C`
  have hTube : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X'' → ‖u‖ ≤ eps →
      ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k) ∈ Cc := by
    intro x u hx hu
    rw [hCcdef]
    exact (lensRowPoints_mem_cthickening (k := k) (δ := δ) (X := X'') (ε := eps) (lam := lam)
      hδpos hδle1 hX''δ hepspos.le hepsle hlamp.le hlamδ).1 x u hx hu
  have hFing : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| ≤ X'' → ‖w‖ ≤ 1 →
      ((x, arch x, 0, lam • w) : Work.Drive.Whitney.Mdl k) ∈ Cc := by
    intro x w hx hw
    rw [hCcdef]
    exact (lensRowPoints_mem_cthickening (k := k) (δ := δ) (X := X'') (ε := eps) (lam := lam)
      hδpos hδle1 hX''δ hepspos.le hepsle hlamp.le hlamδ).2 x w hx hw
  -- ### the structure
  have hX''min : X'' ≤ min F.X' Fr.X' := le_min hX''F hX''Fr
  refine ⟨LWTheta.mk lam X'' eps hlamp hlamF hX''1 hX''F hepspos
    (fun ξ => Γ (kapU k lam ξ)) (fun ξ => kapUi k lam (Γi ξ))
    (hΓsm.comp (contDiff_kapU (k := k) lam)) ((contDiff_kapUi (k := k) lam).comp hΓism)
    ?_ ?_ ?_ ?_ ?_⟩
  · intro ξ
    change kapUi k lam (Γi (Γ (kapU k lam ξ))) = ξ
    rw [hlΓ (kapU k lam ξ)]
    exact kapU_leftInverse (k := k) (ne_of_gt hlamp) ξ
  · intro ξ
    change Γ (kapU k lam (kapUi k lam (Γi ξ))) = ξ
    rw [kapU_rightInverse (k := k) (ne_of_gt hlamp) (Γi ξ)]
    exact hrΓ ξ
  · intro x u hx hu
    have hmem : ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k) ∈ O' := hCO' (hTube x u hx hu)
    have hk : kapU k lam ((x, 0, u, 0) : Work.Drive.Whitney.Mdl k) = (x, 0, u, 0) := by
      ext <;> simp
    rw [hk, hagr _ hmem]
    exact hθplane x u (le_trans hx hX''F)
  · intro x y hx hy0 hy1
    have hxabs : |x| ≤ 1 := by
      have h : x ^ 2 ≤ 1 := by
        have h2 : (0:ℝ) ≤ arch x := le_trans hy0 hy1
        rw [arch] at h2
        linarith
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg x]
    have hmem : ((x, y, 0, 0) : Work.Drive.Whitney.Mdl k) ∈ O' :=
      hCO' (Metric.self_subset_cthickening (lensDisc k)
        (show ((x, y, 0, 0) : Work.Drive.Whitney.Mdl k) ∈ lensDisc k from
          ⟨⟨hxabs, hy0, hy1⟩, rfl, rfl⟩))
    have hk : kapU k lam ((x, y, 0, 0) : Work.Drive.Whitney.Mdl k) = (x, y, 0, 0) := by
      ext <;> simp
    rw [hk, hagr _ hmem]
    exact hθdisc x y (le_trans hxabs F.hX'.le) hy0 hy1
  · intro x w hx hw
    have hmem : ((x, arch x, 0, lam • w) : Work.Drive.Whitney.Mdl k) ∈ O' :=
      hCO' (hFing x w (le_of_lt hx) (le_of_lt hw))
    have hk : kapU k lam ((x, arch x, 0, w) : Work.Drive.Whitney.Mdl k)
        = (x, arch x, 0, lam • w) := rfl
    rw [hk, hagr _ hmem]
    exact hθfinger x (lam • w) (le_trans (le_of_lt hx) hX''min)

end

end Work.Drive.PushDisc
