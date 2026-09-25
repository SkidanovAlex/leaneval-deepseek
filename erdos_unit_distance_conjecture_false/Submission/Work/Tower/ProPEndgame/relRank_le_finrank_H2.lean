import Mathlib
import Submission.Work.Tower.ProPEndgame.Defs
import Submission.Work.Tower.Shafarevich.Cohomology.TwistedExt
import Submission.Work.Tower.Shafarevich.Cohomology.tau_unique
import Submission.Work.Tower.Shafarevich.Cohomology.exists_hom_of_coboundary
import Submission.Work.GolodShafarevich.RelatorAug.Vfun_relator_mem_augIdeal

/-!
# The transgression: `dim_{𝔽_p} (R/[R,F]R^p) ≤ dim_{𝔽_p} H²(G, 𝔽_p)`

For a minimal presentation `φ : F_d ↠ G` of a nontrivial finite `p`-group `G`, the `𝔽_p`-vector
space `V = R/([R,R]·[R,F]·R^p)` (`R = ker φ`) embeds into the dual of `H²(G, 𝔽_p)`: for every
`λ : V →ₗ[𝔽_p] 𝔽_p` one constructs a normalized `2`-cocycle `c_λ` on `G` by
`c_λ (g, h) = λ (σ g · σ h · σ (g h)⁻¹)` for a set-theoretic section `σ : G → F_d` of `φ` with
`σ (φ x_i) = x_i` and `σ 1 = 1`; then `τ_{c_λ}` agrees with `λ ∘ relVsMk` on `R`, so `c_λ` is a
coboundary only if `λ ∘ relVsMk` vanishes on the relations of a presentation of `G`, i.e. only if
`λ = 0` (using `R ⊆ F^p[F,F]` for a minimal presentation).

This gives an injection `V^* ↪ H²(G, 𝔽_p)`, hence `dim V ≤ dim H²(G, 𝔽_p)`.
-/

open scoped Classical

namespace Work.Tower.ProPEndgame

open Work.Tower.Shafarevich.Cohomology

variable {d : ℕ} {G : Type} [Group G]

/-! ## The elementary relators attached to a section -/

/-- The element `σ g · σ h · σ (g h)⁻¹` of the free group attached to a section `σ`; it lies in
the kernel of `φ` whenever `σ` is a section of `φ`. -/
private noncomputable def uEl (σ : G → FreeGroup (Fin d)) (g h : G) : FreeGroup (Fin d) :=
  σ g * σ h * (σ (g * h))⁻¹

/-- The element `σ (φ w)⁻¹ · w` of the free group attached to a section `σ`; it lies in the
kernel of `φ` whenever `σ` is a section of `φ`. -/
private noncomputable def dEl (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (w : FreeGroup (Fin d)) : FreeGroup (Fin d) :=
  (σ (φ w))⁻¹ * w

/-- `uEl σ g h` as an element of `φ.ker`. -/
private noncomputable def uKer (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (g h : G) : φ.ker :=
  ⟨uEl σ g h, by
    show φ (σ g * σ h * (σ (g * h))⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hσ, hσ, hσ, mul_inv_cancel]⟩

/-- `dEl φ σ w` as an element of `φ.ker`. -/
private noncomputable def dKer (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (w : FreeGroup (Fin d)) : φ.ker :=
  ⟨dEl φ σ w, by
    show φ ((σ (φ w))⁻¹ * w) = 1
    rw [map_mul, map_inv, hσ, inv_mul_cancel]⟩

private theorem coe_uKer (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (g h : G) :
    ((uKer φ σ hσ g h : φ.ker) : FreeGroup (Fin d)) = uEl σ g h := rfl

private theorem coe_dKer (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (w : FreeGroup (Fin d)) :
    ((dKer φ σ hσ w : φ.ker) : FreeGroup (Fin d)) = dEl φ σ w := rfl

/-! ## The two free-group identities -/

private theorem uEl_mul_uEl (σ : G → FreeGroup (Fin d)) (g h j : G) :
    uEl σ g h * uEl σ (g * h) j =
      σ g * uEl σ h j * (σ g)⁻¹ * uEl σ g (h * j) := by
  simp only [uEl]
  rw [mul_assoc g h j]
  group

private theorem dEl_mul (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (u v : FreeGroup (Fin d)) :
    dEl φ σ (u * v) = (σ (φ (u * v)))⁻¹ * uEl σ (φ u) (φ v) * σ (φ (u * v))
      * ((σ (φ v))⁻¹ * dEl φ σ u * σ (φ v)) * dEl φ σ v := by
  simp only [dEl, uEl, map_mul]
  group

/-! ## The two identities in `V = R/([R,R]·[R,F]·R^p)` -/

/-- `relVsMk` of the identity element is zero. -/
private theorem relVsMk_one (p : ℕ) {F : Type*} [Group F] (R : Subgroup F) :
    relVsMk p R 1 = 0 :=
  relVsMk_eq_zero_of_mem p R 1 (by simpa using Subgroup.one_mem (relFt p R))

/-- The cocycle identity in `V`. -/
private theorem relVsMk_uKer_add (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (g h j : G) :
    relVsMk p φ.ker (uKer φ σ hσ g h) + relVsMk p φ.ker (uKer φ σ hσ (g * h) j) =
      relVsMk p φ.ker (uKer φ σ hσ h j) + relVsMk p φ.ker (uKer φ σ hσ g (h * j)) := by
  have hconj : relVsMk p φ.ker
      (⟨σ g * ((uKer φ σ hσ h j : φ.ker) : FreeGroup (Fin d)) * (σ g)⁻¹,
        (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ h j).2 (σ g)⟩ : φ.ker)
      = relVsMk p φ.ker (uKer φ σ hσ h j) :=
    relVsMk_conj p φ.ker (MonoidHom.normal_ker φ) (uKer φ σ hσ h j) (σ g)
  have hsub : (uKer φ σ hσ g h * uKer φ σ hσ (g * h) j : φ.ker)
      = (⟨σ g * ((uKer φ σ hσ h j : φ.ker) : FreeGroup (Fin d)) * (σ g)⁻¹,
          (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ h j).2 (σ g)⟩ : φ.ker)
        * uKer φ σ hσ g (h * j) := by
    refine Subtype.ext ?_
    simpa only [uKer, uEl, Subgroup.coe_mul, Subgroup.coe_inv] using uEl_mul_uEl σ g h j
  calc relVsMk p φ.ker (uKer φ σ hσ g h) + relVsMk p φ.ker (uKer φ σ hσ (g * h) j)
      = relVsMk p φ.ker (uKer φ σ hσ g h * uKer φ σ hσ (g * h) j) :=
        (relVsMk_mul p φ.ker _ _).symm
    _ = relVsMk p φ.ker
          ((⟨σ g * ((uKer φ σ hσ h j : φ.ker) : FreeGroup (Fin d)) * (σ g)⁻¹,
            (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ h j).2 (σ g)⟩ : φ.ker)
            * uKer φ σ hσ g (h * j)) := congrArg _ hsub
    _ = relVsMk p φ.ker
          (⟨σ g * ((uKer φ σ hσ h j : φ.ker) : FreeGroup (Fin d)) * (σ g)⁻¹,
            (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ h j).2 (σ g)⟩ : φ.ker)
          + relVsMk p φ.ker (uKer φ σ hσ g (h * j)) := relVsMk_mul p φ.ker _ _
    _ = relVsMk p φ.ker (uKer φ σ hσ h j) + relVsMk p φ.ker (uKer φ σ hσ g (h * j)) := by
        rw [hconj]

/-- The `τ`-identity in `V`. -/
private theorem relVsMk_dKer_mul (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (u v : FreeGroup (Fin d)) :
    relVsMk p φ.ker (dKer φ σ hσ (u * v)) =
      relVsMk p φ.ker (uKer φ σ hσ (φ u) (φ v))
        + relVsMk p φ.ker (dKer φ σ hσ u) + relVsMk p φ.ker (dKer φ σ hσ v) := by
  have hconjZ : relVsMk p φ.ker
      (⟨(σ (φ (u * v)))⁻¹ * ((uKer φ σ hσ (φ u) (φ v) : φ.ker) : FreeGroup (Fin d))
          * (σ (φ (u * v)))⁻¹⁻¹,
        (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ (φ u) (φ v)).2 (σ (φ (u * v)))⁻¹⟩
        : φ.ker)
      = relVsMk p φ.ker (uKer φ σ hσ (φ u) (φ v)) :=
    relVsMk_conj p φ.ker (MonoidHom.normal_ker φ) (uKer φ σ hσ (φ u) (φ v))
      (σ (φ (u * v)))⁻¹
  have hconjY : relVsMk p φ.ker
      (⟨(σ (φ v))⁻¹ * ((dKer φ σ hσ u : φ.ker) : FreeGroup (Fin d)) * (σ (φ v))⁻¹⁻¹,
        (MonoidHom.normal_ker φ).conj_mem _ (dKer φ σ hσ u).2 (σ (φ v))⁻¹⟩ : φ.ker)
      = relVsMk p φ.ker (dKer φ σ hσ u) :=
    relVsMk_conj p φ.ker (MonoidHom.normal_ker φ) (dKer φ σ hσ u) (σ (φ v))⁻¹
  have hsub : (dKer φ σ hσ (u * v) : φ.ker)
      = (⟨(σ (φ (u * v)))⁻¹ * ((uKer φ σ hσ (φ u) (φ v) : φ.ker) : FreeGroup (Fin d))
            * (σ (φ (u * v)))⁻¹⁻¹,
          (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ (φ u) (φ v)).2 (σ (φ (u * v)))⁻¹⟩
          : φ.ker)
        * (⟨(σ (φ v))⁻¹ * ((dKer φ σ hσ u : φ.ker) : FreeGroup (Fin d)) * (σ (φ v))⁻¹⁻¹,
            (MonoidHom.normal_ker φ).conj_mem _ (dKer φ σ hσ u).2 (σ (φ v))⁻¹⟩ : φ.ker)
        * dKer φ σ hσ v := by
    refine Subtype.ext ?_
    simpa only [dKer, dEl, uKer, uEl, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      using dEl_mul φ σ u v
  calc relVsMk p φ.ker (dKer φ σ hσ (u * v))
      = relVsMk p φ.ker
          ((⟨(σ (φ (u * v)))⁻¹ * ((uKer φ σ hσ (φ u) (φ v) : φ.ker) : FreeGroup (Fin d))
              * (σ (φ (u * v)))⁻¹⁻¹,
              (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ (φ u) (φ v)).2
                (σ (φ (u * v)))⁻¹⟩ : φ.ker)
            * (⟨(σ (φ v))⁻¹ * ((dKer φ σ hσ u : φ.ker) : FreeGroup (Fin d))
                * (σ (φ v))⁻¹⁻¹,
                (MonoidHom.normal_ker φ).conj_mem _ (dKer φ σ hσ u).2 (σ (φ v))⁻¹⟩ : φ.ker)
            * dKer φ σ hσ v) := congrArg _ hsub
    _ = relVsMk p φ.ker
          (⟨(σ (φ (u * v)))⁻¹ * ((uKer φ σ hσ (φ u) (φ v) : φ.ker) : FreeGroup (Fin d))
              * (σ (φ (u * v)))⁻¹⁻¹,
              (MonoidHom.normal_ker φ).conj_mem _ (uKer φ σ hσ (φ u) (φ v)).2
                (σ (φ (u * v)))⁻¹⟩ : φ.ker)
          + relVsMk p φ.ker
            (⟨(σ (φ v))⁻¹ * ((dKer φ σ hσ u : φ.ker) : FreeGroup (Fin d)) * (σ (φ v))⁻¹⁻¹,
                (MonoidHom.normal_ker φ).conj_mem _ (dKer φ σ hσ u).2 (σ (φ v))⁻¹⟩ : φ.ker)
          + relVsMk p φ.ker (dKer φ σ hσ v) := by
        rw [relVsMk_mul, relVsMk_mul]
    _ = relVsMk p φ.ker (uKer φ σ hσ (φ u) (φ v))
          + relVsMk p φ.ker (dKer φ σ hσ u) + relVsMk p φ.ker (dKer φ σ hσ v) := by
        rw [hconjZ, hconjY]

/-! ## The cocycle `c_λ` and the function `τ_λ` -/

/-- The `2`-cocycle attached to `σ` and `lam : V →ₗ 𝔽_p`. -/
private noncomputable def cocFn (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) : G × G → ZMod p :=
  fun gh => lam (relVsMk p φ.ker (uKer φ σ hσ gh.1 gh.2))

/-- The function `τ_λ (w) = lam (σ (φ w)⁻¹ w)`. -/
private noncomputable def tauFn (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p)
    (w : FreeGroup (Fin d)) : ZMod p :=
  lam (relVsMk p φ.ker (dKer φ σ hσ w))

private theorem cocFn_cocycle (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) (g h j : G) :
    cocFn p φ σ hσ lam (g * h, j) + cocFn p φ σ hσ lam (g, h) =
      cocFn p φ σ hσ lam (h, j) + cocFn p φ σ hσ lam (g, h * j) := by
  have h := congrArg (fun x : relVs p φ.ker => lam x) (relVsMk_uKer_add p φ σ hσ g h j)
  simp only [map_add] at h
  rw [add_comm]
  exact h

private theorem cocFn_one_one (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (hσ1 : σ 1 = 1)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) : cocFn p φ σ hσ lam (1, 1) = 0 := by
  have h1 : uKer φ σ hσ 1 1 = 1 := Subtype.ext (by simp [uKer, uEl, hσ1])
  simp only [cocFn]
  rw [h1, relVsMk_one, map_zero]

private theorem tauFn_one (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (hσ1 : σ 1 = 1)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) : tauFn p φ σ hσ lam 1 = 0 := by
  have h1 : dKer φ σ hσ (1 : FreeGroup (Fin d)) = 1 :=
    Subtype.ext (by simp [dKer, dEl, hσ1])
  simp only [tauFn]
  rw [h1, relVsMk_one, map_zero]

private theorem tauFn_of (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g)
    (hσgen : ∀ i : Fin d, σ (φ (FreeGroup.of i)) = FreeGroup.of i)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) (i : Fin d) :
    tauFn p φ σ hσ lam (FreeGroup.of i) = 0 := by
  have h1 : dKer φ σ hσ (FreeGroup.of i) = 1 :=
    Subtype.ext (by simp [dKer, dEl, hσgen i])
  simp only [tauFn]
  rw [h1, relVsMk_one, map_zero]

private theorem tauFn_mul (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p)
    (u v : FreeGroup (Fin d)) :
    tauFn p φ σ hσ lam (u * v)
      = tauFn p φ σ hσ lam u + tauFn p φ σ hσ lam v + cocFn p φ σ hσ lam (φ u, φ v) := by
  have h := congrArg (fun x : relVs p φ.ker => lam x) (relVsMk_dKer_mul p φ σ hσ u v)
  simp only [map_add] at h
  simp only [tauFn, cocFn]
  rw [h]
  abel

/-! ## The `𝔽_p`-linear structures -/

/-- `lam ↦ c_λ` is `𝔽_p`-linear. -/
private noncomputable def cocLin (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) :
    (relVs p φ.ker →ₗ[ZMod p] ZMod p) →ₗ[ZMod p] (G × G → ZMod p) where
  toFun := cocFn p φ σ hσ
  map_add' lam μ := by
    funext gh
    simp only [cocFn, Pi.add_apply, LinearMap.add_apply, map_add]
  map_smul' s lam := by
    funext gh
    simp only [cocFn, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply]

private theorem cocFn_mem_cocycles₂ (p : ℕ) (φ : FreeGroup (Fin d) →* G)
    (σ : G → FreeGroup (Fin d)) (hσ : ∀ g : G, φ (σ g) = g)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) :
    cocFn p φ σ hσ lam ∈ groupCohomology.cocycles₂
      (Rep.trivial (ZMod p) G (ZMod p)) := by
  refine (groupCohomology.mem_cocycles₂_iff (A := Rep.trivial (ZMod p) G (ZMod p))
    (cocFn p φ σ hσ lam)).mpr ?_
  intro g h j
  have hh := cocFn_cocycle p φ σ hσ lam g h j
  simpa using hh

/-- The `𝔽_p`-linear map `lam ↦ c_λ` into the space of `2`-cocycles. -/
private noncomputable def cocLinC (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) :
    (relVs p φ.ker →ₗ[ZMod p] ZMod p) →ₗ[ZMod p]
      ↥(groupCohomology.cocycles₂ (Rep.trivial (ZMod p) G (ZMod p))) :=
  (cocLin p φ σ hσ).codRestrict _
    (fun lam => cocFn_mem_cocycles₂ p φ σ hσ lam)

/-- **The transgression map** `V^* → H²(G, 𝔽_p)`, `lam ↦ [c_λ]`. -/
private noncomputable def Phi (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) :
    (relVs p φ.ker →ₗ[ZMod p] ZMod p) →ₗ[ZMod p]
      (Work.Tower.Shafarevich.H2Fp p G) :=
  (groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p))).hom.comp (cocLinC p φ σ hσ)

/-- The normalized `2`-cocycle `c_λ` in the shape needed for `ExtGroup.tau`. -/
private noncomputable def cocTw (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (hσ1 : σ 1 = 1)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) : TwistedCocycle p G where
  toFun := cocFn p φ σ hσ lam
  cocycle := fun g h j => cocFn_cocycle p φ σ hσ lam g h j
  map_one_one := cocFn_one_one p φ σ hσ hσ1 lam

/-- `τ_λ` agrees with the characterising `τ` of the cocycle `c_λ`. -/
private theorem ExtGroup.tau_cocTw (p : ℕ) (φ : FreeGroup (Fin d) →* G)
    (σ : G → FreeGroup (Fin d)) (hσ : ∀ g : G, φ (σ g) = g) (hσ1 : σ 1 = 1)
    (hσgen : ∀ i : Fin d, σ (φ (FreeGroup.of i)) = FreeGroup.of i)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) :
    ExtGroup.tau (cocTw p φ σ hσ hσ1 lam) φ = tauFn p φ σ hσ lam :=
  tau_unique (cocFn p φ σ hσ lam) φ (ExtGroup.tau_one _ _)
    (fun u v => ExtGroup.tau_mul _ _ u v) (tauFn_one p φ σ hσ hσ1 lam)
    (fun u v => tauFn_mul p φ σ hσ lam u v)
    (fun i => by rw [ExtGroup.tau_of, tauFn_of p φ σ hσ hσgen])

/-- On `R = ker φ`, the function `τ_λ` is `lam ∘ relVsMk`. -/
private theorem tauFn_eq_on_ker (p : ℕ) (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d))
    (hσ : ∀ g : G, φ (σ g) = g) (hσ1 : σ 1 = 1)
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) (r : φ.ker) :
    tauFn p φ σ hσ lam (r : FreeGroup (Fin d)) = lam (relVsMk p φ.ker r) := by
  have h1 : dKer φ σ hσ (r : FreeGroup (Fin d)) = r :=
    Subtype.ext (by
      show (σ (φ (r : FreeGroup (Fin d))))⁻¹ * (r : FreeGroup (Fin d)) = (r : FreeGroup (Fin d))
      rw [r.2, hσ1, inv_one, one_mul])
  simp only [tauFn]
  rw [h1]

/-! ## A section of a minimal presentation -/

/-- If the images under `φ` of the generators indexed by a finite set `S` generate `G`, then the
minimality of `d` forces `d ≤ S.card`. -/
private theorem card_le_of_closure_eq_top {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (S : Finset (Fin d))
    (hS : Subgroup.closure ((fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d))) = ⊤) :
    d ≤ S.card := by
  let e : Fin (Fintype.card ↥S) ≃ ↥S := (Fintype.equivFin ↥S).symm
  let g : Fin (Fintype.card ↥S) → G := fun t => φ (FreeGroup.of ((e t : ↥S) : Fin d))
  have hrange : Set.range g = (fun i => φ (FreeGroup.of i)) '' (↑S : Set (Fin d)) := by
    ext x; constructor
    · rintro ⟨t, rfl⟩; exact ⟨(e t : ↥S), (e t).2, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨e.symm ⟨s, hs⟩, by simp [g]⟩
  have hcl : Subgroup.closure (Set.range g) = ⊤ := by rw [hrange]; exact hS
  have hψsurj : Function.Surjective (FreeGroup.lift g) := by
    rw [FreeGroup.lift_surjective_iff_closure_range_eq_top]; exact hcl
  have := hmin (Fintype.card ↥S) (FreeGroup.lift g) hψsurj
  rwa [Fintype.card_coe] at this

/-- The images of all generators generate `G` when `φ` is surjective. -/
private theorem closure_image_of_eq_top {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) :
    Subgroup.closure ((fun i => φ (FreeGroup.of i)) ''
      (↑(Finset.univ : Finset (Fin d)) : Set (Fin d))) = ⊤ := by
  rw [Finset.coe_univ, Set.image_univ]
  have h2 : Set.range (fun i : Fin d => φ (FreeGroup.of i))
      = φ '' Set.range (FreeGroup.of : Fin d → FreeGroup (Fin d)) := Set.range_comp φ _
  rw [h2, ← MonoidHom.map_closure φ (Set.range (FreeGroup.of : Fin d → FreeGroup (Fin d))),
    FreeGroup.closure_range_of (Fin d)]
  exact Subgroup.map_top_of_surjective φ hφ

/-- For a minimal presentation the images of the generators in `G` are pairwise distinct. -/
private theorem of_phi_injective_of_minimal {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d') :
    Function.Injective (fun i : Fin d => φ (FreeGroup.of i)) := by
  intro i j hij
  by_contra hne
  have hS : Subgroup.closure ((fun k => φ (FreeGroup.of k)) ''
      (↑(Finset.univ.erase i : Finset (Fin d)) : Set (Fin d))) = ⊤ := by
    rw [eq_top_iff, ← closure_image_of_eq_top φ hφ, Subgroup.closure_le]
    rintro x ⟨k, -, rfl⟩
    by_cases hk : k = i
    · subst hk
      rw [hij]
      exact Subgroup.subset_closure ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ j⟩, rfl⟩
    · exact Subgroup.subset_closure
        ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩, rfl⟩
  have hle := card_le_of_closure_eq_top φ hmin _ hS
  have hlt : (Finset.univ.erase i).card < d := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := i.isLt
    omega
  omega

/-- For a minimal presentation the generators have nontrivial image in `G`. -/
private theorem of_phi_ne_one_of_minimal {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (i : Fin d) : φ (FreeGroup.of i) ≠ 1 := by
  intro h1
  have hS : Subgroup.closure ((fun k => φ (FreeGroup.of k)) ''
      (↑(Finset.univ.erase i : Finset (Fin d)) : Set (Fin d))) = ⊤ := by
    rw [eq_top_iff, ← closure_image_of_eq_top φ hφ, Subgroup.closure_le]
    rintro x ⟨k, -, rfl⟩
    by_cases hk : k = i
    · subst hk
      simp only [h1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure
        ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩, rfl⟩
  have hle := card_le_of_closure_eq_top φ hmin _ hS
  have hlt : (Finset.univ.erase i).card < d := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have := i.isLt
    omega
  omega

/-- A set-theoretic section of a surjection `φ : F_d ↠ G`. -/
private noncomputable def secOf {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) : G → FreeGroup (Fin d) :=
  fun g => if _h : g = 1 then 1
    else if _h' : ∃ i : Fin d, φ (FreeGroup.of i) = g then
      FreeGroup.of (Classical.choose _h')
    else Classical.choose (hφ g)

private theorem secOf_phi {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) (g : G) : φ (secOf φ hφ g) = g := by
  simp only [secOf]
  split_ifs with h1 h2
  · rw [h1]; exact map_one φ
  · exact Classical.choose_spec h2
  · exact Classical.choose_spec (hφ g)

private theorem secOf_one {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) : secOf φ hφ 1 = 1 := by
  unfold secOf
  simp

private theorem secOf_of {d : ℕ} {G : Type} [Group G] (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) (hinj : Function.Injective (fun i : Fin d => φ (FreeGroup.of i)))
    (hne : ∀ i : Fin d, φ (FreeGroup.of i) ≠ 1) (i : Fin d) :
    secOf φ hφ (φ (FreeGroup.of i)) = FreeGroup.of i := by
  simp only [secOf]
  split_ifs with h1 h2
  · exact absurd h1 (hne i)
  · exact congrArg FreeGroup.of (hinj (Classical.choose_spec h2))
  · exact absurd ⟨i, rfl⟩ h2

private theorem exists_section_of_minimal_self {d : ℕ} {G : Type} [Group G]
    (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d') :
    ∃ σ : G → FreeGroup (Fin d),
      (∀ g : G, φ (σ g) = g) ∧ σ 1 = 1 ∧
        ∀ i : Fin d, σ (φ (FreeGroup.of i)) = FreeGroup.of i :=
  ⟨secOf φ hφ, secOf_phi φ hφ, secOf_one φ hφ,
    fun i => secOf_of φ hφ (of_phi_injective_of_minimal φ hφ hmin)
      (of_phi_ne_one_of_minimal φ hφ hmin) i⟩

/-! ## Homomorphisms to `𝔽_p` vanish on the kernel of a minimal presentation -/

/-- A homomorphism `Additive (FreeGroup α) →+ A` evaluated at `w` in terms of the exponent sums
of `w` and the values at the generators. -/
private theorem addHom_eq_sum_expSum {A : Type*} [AddCommGroup A] {α : Type*} [Fintype α] [DecidableEq α]
    (δ : Additive (FreeGroup α) →+ A) (w : FreeGroup α) :
    δ (Additive.ofMul w)
      = ∑ i : α, (Work.GolodShafarevich.expSum i w) • δ (Additive.ofMul (FreeGroup.of i)) := by
  induction w using FreeGroup.induction_on with
  | one => simp [Work.GolodShafarevich.expSum_one]
  | of j =>
      rw [Finset.sum_eq_single j]
      · rw [Work.GolodShafarevich.expSum_of, if_pos rfl, one_zsmul]
      · intro i _ hij
        rw [Work.GolodShafarevich.expSum_of, if_neg hij, zero_zsmul]
      · intro hj; exact absurd (Finset.mem_univ j) hj
  | inv_of j ih =>
      have hsum : (∑ i : α, (Work.GolodShafarevich.expSum i (FreeGroup.of j)⁻¹)
            • δ (Additive.ofMul (FreeGroup.of i)))
          = -(∑ i : α, (Work.GolodShafarevich.expSum i (FreeGroup.of j))
            • δ (Additive.ofMul (FreeGroup.of i))) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [Work.GolodShafarevich.expSum_inv, neg_zsmul])
      rw [show Additive.ofMul (FreeGroup.of j)⁻¹ = -(Additive.ofMul (FreeGroup.of j)) from rfl,
        map_neg, hsum, ← ih]
  | mul x y ihx ihy =>
      rw [show Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y from rfl,
        map_add, ihx, ihy, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [Work.GolodShafarevich.expSum_mul, add_zsmul])

/-- A homomorphism `Additive F_d →+ 𝔽_p` vanishes on the kernel of a minimal presentation. -/
private theorem addHom_eq_zero_of_mem_ker_self {p d : ℕ} (hp : Nat.Prime p) {G : Type} [Group G]
    [Fintype G] [Nontrivial G] (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (δ : Additive (FreeGroup (Fin d)) →+ ZMod p) {w : FreeGroup (Fin d)} (hw : φ w = 1) :
    δ (Additive.ofMul w) = 0 := by
  rw [addHom_eq_sum_expSum δ w]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  obtain ⟨k, hk⟩ :=
    Work.GolodShafarevich.RelatorAug.p_dvd_expSum_of_mem_ker hp hG φ hφ hmin hw i
  have hpz : ((p : ℤ) • δ (Additive.ofMul (FreeGroup.of i))) = 0 := by
    rw [zsmul_eq_mul, show (((p : ℤ) : ZMod p)) = 0 by simp, zero_mul]
  rw [hk, mul_comm, mul_zsmul, hpz, smul_zero]

/-! ## Injectivity of the transgression -/

/-! ## Injectivity of the transgression -/

/-- If the class `[c_λ]` vanishes then `λ = 0`: a coboundary `c_λ` gives a homomorphism
`δ : F_d → 𝔽_p` with `τ_λ = δ` on `R`, and `δ` vanishes on `R` for a minimal presentation. -/
private theorem Phi_apply_eq_zero (p : ℕ) (hp : Nat.Prime p) [Fintype G] [Nontrivial G]
    (hG : IsPGroup p G)
    (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d)) (hσ : ∀ g : G, φ (σ g) = g)
    (hσ1 : σ 1 = 1)
    (hσgen : ∀ i : Fin d, σ (φ (FreeGroup.of i)) = FreeGroup.of i)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d')
    (lam : relVs p φ.ker →ₗ[ZMod p] ZMod p) (h : Phi p φ σ hσ lam = 0) : lam = 0 := by
  have hc : cocFn p φ σ hσ lam ∈
      groupCohomology.coboundaries₂ (Rep.trivial (ZMod p) G (ZMod p)) := by
    have h' : (groupCohomology.H2π (Rep.trivial (ZMod p) G (ZMod p))).hom
        (cocLinC p φ σ hσ lam) = 0 := h
    exact (groupCohomology.H2π_eq_zero_iff (cocLinC p φ σ hσ lam)).mp h'
  obtain ⟨b, hb⟩ := hc
  have hb' : ∀ g h : G, cocFn p φ σ hσ lam (g, h) = b h - b (g * h) + b g := by
    intro g h
    have hh := congrFun hb (g, h)
    simp only [groupCohomology.d₁₂_hom_apply] at hh
    exact hh.symm
  obtain ⟨δ, hδ⟩ := exists_hom_of_coboundary (cocFn p φ σ hσ lam)
    (cocTw p φ σ hσ hσ1 lam).map_one_one b hb' φ
    (ExtGroup.tau (cocTw p φ σ hσ hσ1 lam) φ) (ExtGroup.tau_one _ _)
    (fun u v => ExtGroup.tau_mul _ _ u v)
  refine LinearMap.ext fun x => ?_
  obtain ⟨r, rfl⟩ := relVsMk_surjective p φ.ker x
  show lam (relVsMk p φ.ker r) = 0
  have hφr : φ (r : FreeGroup (Fin d)) = 1 := r.2
  have h1 : lam (relVsMk p φ.ker r) = tauFn p φ σ hσ lam (r : FreeGroup (Fin d)) :=
    (tauFn_eq_on_ker p φ σ hσ hσ1 lam r).symm
  have h2 : ExtGroup.tau (cocTw p φ σ hσ hσ1 lam) φ (r : FreeGroup (Fin d))
      = tauFn p φ σ hσ lam (r : FreeGroup (Fin d)) :=
    congrFun (ExtGroup.tau_cocTw p φ σ hσ hσ1 hσgen lam) _
  have h3 : ExtGroup.tau (cocTw p φ σ hσ hσ1 lam) φ (r : FreeGroup (Fin d))
      = δ (Additive.ofMul (r : FreeGroup (Fin d))) := hδ _ hφr
  have h4 : δ (Additive.ofMul (r : FreeGroup (Fin d))) = 0 :=
    addHom_eq_zero_of_mem_ker_self hp hG φ hφ hmin δ hφr
  rw [h1, ← h2, h3, h4]

private theorem Phi_injective (p : ℕ) (hp : Nat.Prime p) [Fintype G] [Nontrivial G]
    (hG : IsPGroup p G)
    (φ : FreeGroup (Fin d) →* G) (σ : G → FreeGroup (Fin d)) (hσ : ∀ g : G, φ (σ g) = g)
    (hσ1 : σ 1 = 1)
    (hσgen : ∀ i : Fin d, σ (φ (FreeGroup.of i)) = FreeGroup.of i)
    (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d') :
    Function.Injective (Phi p φ σ hσ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro lam hlam
  exact Phi_apply_eq_zero p hp hG φ σ hσ hσ1 hσgen hφ hmin lam hlam

/-! ## The main theorem -/

/-- **The transgression.**  Let `φ : F_d ↠ G` be a *minimal* presentation of a nontrivial finite
`p`-group `G` (the hypothesis `hmin` says that no presentation of `G` has fewer generators), and
let `R = ker φ`.  Then the `𝔽_p`-dimension of `V = R/([R,R]·[R,F]·R^p)`
(`Work.Tower.ProPEndgame.relVs p R`) is at most `dim_{𝔽_p} H²(G, 𝔽_p)`.

Proof.  For `λ : V →ₗ[𝔽_p] 𝔽_p` put `λ̃ = λ ∘ relVsMk p R : R → 𝔽_p`; it is additive and
`F`-invariant (`relVsMk_conj`).  Choose a set-theoretic section `σ : G → F_d` of `φ` with
`σ (φ xᵢ) = xᵢ` and `σ 1 = 1`, and define `c_λ (g, h) = - λ (relVsMk p R ⟨σ g · σ h · σ (g h)⁻¹⟩)`
(the argument lies in `R`).  Then `c_λ` is a normalized `2`-cocycle with values in `𝔽_p` (trivial
action), and `τ' w = λ̃ (σ (φ w)⁻¹ · w)` satisfies `τ' (u * v) = τ' u + τ' v + c_λ (φ u, φ v)`,
`τ' 1 = 0`, `τ' (xᵢ) = 0`, hence agrees with `ExtGroup.tau c_λ φ` by
`Work.Tower.Shafarevich.Cohomology.tau_unique`; for `r ∈ R` this gives `τ' r = λ̃ r`.

The assignment `λ ↦ [c_λ] ∈ H²(G, 𝔽_p)` is `𝔽_p`-linear and injective: if `c_λ` were a coboundary
then `Work.Tower.Shafarevich.Cohomology.exists_hom_of_coboundary` produces
`δ : Additive F_d →+ 𝔽_p` with `τ'|_R = δ|_R`, but for a minimal presentation
`R ⊆ Φ(F_d) = F_d^p[F_d,F]`, so `δ|_R = 0` (a homomorphism into `𝔽_p` kills `p`-th powers and
commutators: `Work.GolodShafarevich.RelatorAug.p_dvd_expSum_of_mem_ker` together with
`Work.GolodShafarevich.freegroup_map_eq_prod_expSum`), whence `λ = 0`.  Therefore
`relRank p R = dim (V →ₗ[𝔽_p] 𝔽_p) ≤ dim H²(G, 𝔽_p)`. -/
theorem relRank_le_finrank_H2 (p : ℕ) [Fact p.Prime] {d : ℕ} {G : Type} [Group G] [Fintype G]
    [Nontrivial G] (hG : IsPGroup p G) (φ : FreeGroup (Fin d) →* G) (hφ : Function.Surjective φ)
    (hmin : ∀ (d' : ℕ) (ψ : FreeGroup (Fin d') →* G), Function.Surjective ψ → d ≤ d') :
    Work.Tower.ProPEndgame.relRank p φ.ker ≤
      Module.finrank (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) := by
  have hp : Nat.Prime p := Fact.out
  obtain ⟨σ, hσ, hσ1, hσgen⟩ := exists_section_of_minimal_self φ hφ hmin
  haveI hfin : Module.Finite (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) := by
    let A : Rep (ZMod p) G := Rep.trivial (ZMod p) G (ZMod p)
    haveI : Module.Finite (ZMod p) (G × G → ZMod p) := Module.Finite.pi
    haveI : Module.Finite (ZMod p) ↥(groupCohomology.cocycles₂ A) :=
      Module.Finite.of_injective (groupCohomology.cocycles₂ A).subtype Subtype.val_injective
    have hsurj : Function.Surjective (groupCohomology.H2π A).hom :=
      (ModuleCat.epi_iff_surjective (groupCohomology.H2π A)).mp inferInstance
    exact Module.Finite.of_surjective (groupCohomology.H2π A).hom hsurj
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Phi p φ σ hσ)
    (Phi_injective p hp hG φ σ hσ hσ1 hσgen hφ hmin)
  calc relRank p φ.ker
      = Module.finrank (ZMod p) (relVs p φ.ker) := rfl
    _ = Module.finrank (ZMod p) (Module.Dual (ZMod p) (relVs p φ.ker)) :=
        (Subspace.dual_finrank_eq (K := ZMod p) (V := relVs p φ.ker)).symm
    _ ≤ Module.finrank (ZMod p) (Work.Tower.Shafarevich.H2Fp p G) := hle

end Work.Tower.ProPEndgame
