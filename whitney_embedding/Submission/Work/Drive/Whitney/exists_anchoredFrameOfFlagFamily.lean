import Mathlib
import Submission.Work.Drive.Whitney.exists_independent_extension_oneStep

namespace Work.Drive.Whitney

open scoped ContDiff InnerProduct

/-!
# The anchored frame of a flag family

Given a smooth family `C` of injective linear maps `ℝ^n → ℝ^m` and a smooth nowhere-zero section `v`
of the ranges, we produce a smooth family of linear automorphisms `Φ` of `ℝ^m` carrying the `i₀`-th
standard basis vector to `v` and the first `n` standard basis vectors into `range (C ·)`.

The proof has three ingredients, all proved here on top of the one-step extension
`Work.Drive.Whitney.exists_independent_extension_oneStep` (a smooth nonvanishing vector field
transverse to a smooth family of `k`-planes over `ℝ²` exists for `k < m`).

* `exists_coeff_of_mem_range` — the *coefficient field* of `v`: a smooth `s` with `C s = v`, built
  from the Moore–Penrose left inverse `(C^* C)^{-1} C^*` of `C` (smoothness of the inverse family
  from `IsInvertible.contDiffAt_map_inverse`); it is nowhere zero because `v` is.
* `exists_smoothFrame_extension_local` — a smooth pointwise-independent `k`-family extends to a
  smooth family of bases: induction on `m - k` from the one-step extension, the case `k = m` being
  the explicit column construction `exists_isoFamily_of_frame_local`.
* `exists_smoothIsoFamily_anchored_local` — a smooth nowhere-zero vector field is the image of any
  prescribed basis vector under a smooth family of linear automorphisms: extend the single vector to
  a frame by the previous item, permute the frame so that the vector sits in the `i₀`-th slot, and
  apply the column construction.

The target then takes `R` with `R e_{i₀} = s`, transports the columns of `C` by `R` (so that the
`i₀`-th column is `v`) and extends the resulting independent `n`-family of sections of `range (C ·)`
to a family of bases of `ℝ^m`.
-/

variable {m n : ℕ}

abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ### The coefficient field of a section of the range -/

/-- The adjoint, as a family. -/
noncomputable def adjFam (C : En n →L[ℝ] En m) : En m →L[ℝ] En n :=
  ContinuousLinearMap.adjoint C

/-- The Gram operator `C^* ∘ C`, which is positive definite when `C` is injective. -/
noncomputable def gram (C : En n →L[ℝ] En m) : En n →L[ℝ] En n :=
  (adjFam C).comp C

theorem adjointCLM_apply (A : En n →L[ℝ] En m) :
    (LinearMap.toContinuousLinearMap
      ({ toFun := fun A : En n →L[ℝ] En m => ContinuousLinearMap.adjoint A
         map_add' := by intro A B; rw [map_add]
         map_smul' := by
           intro c A
           have h := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℝ)
             (E := En n) (F := En m)) c A
           simpa using h } : (En n →L[ℝ] En m) →ₗ[ℝ] (En m →L[ℝ] En n)))
      A = ContinuousLinearMap.adjoint A := rfl

theorem adjFam_contDiff (C : ℝ × ℝ → (En n →L[ℝ] En m))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => adjFam (C p)) := by
  let adjointCLM : ((En n →L[ℝ] En m) →L[ℝ] (En m →L[ℝ] En n)) :=
    LinearMap.toContinuousLinearMap
      ({ toFun := fun A : En n →L[ℝ] En m => ContinuousLinearMap.adjoint A
         map_add' := by intro A B; rw [map_add]
         map_smul' := by
           intro c A
           have h := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℝ)
             (E := En n) (F := En m)) c A
           simpa using h } : (En n →L[ℝ] En m) →ₗ[ℝ] (En m →L[ℝ] En n))
  have h := adjointCLM.contDiff.comp hC
  have hfun : (⇑adjointCLM ∘ C) = fun p : ℝ × ℝ => adjFam (C p) := by
    funext p
    rfl
  rwa [hfun] at h

theorem gram_contDiff (C : ℝ × ℝ → (En n →L[ℝ] En m))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => gram (C p)) :=
  (adjFam_contDiff C hC).clm_comp hC

theorem gram_injective (C : En n →L[ℝ] En m) (hinj : Function.Injective C) :
    Function.Injective (gram C) := by
  intro x y hxy
  have h0 : gram C (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hinner : inner ℝ (gram C (x - y)) (x - y) = ‖C (x - y)‖ ^ 2 := by
    simp only [gram, adjFam, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  rw [h0, inner_zero_left] at hinner
  have hnorm : ‖C (x - y)‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hinner.symm
  have hCz : C (x - y) = 0 := norm_eq_zero.mp hnorm
  have hz : x - y = 0 := hinj (by rw [hCz, map_zero])
  exact sub_eq_zero.mp hz

theorem gram_bijective (C : En n →L[ℝ] En m) (hinj : Function.Injective C) :
    Function.Bijective (gram C) :=
  ⟨gram_injective C hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (gram_injective C hinj)⟩

noncomputable def gramEquiv (C : En n →L[ℝ] En m) (hinj : Function.Injective C) :
    En n ≃L[ℝ] En n :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective (gram C).toLinearMap (gram_bijective C hinj))

theorem gramEquiv_coe (C : En n →L[ℝ] En m) (hinj : Function.Injective C) :
    ((gramEquiv C hinj : En n →L[ℝ] En n)) = gram C := by
  refine ContinuousLinearMap.ext fun x => ?_
  change (LinearEquiv.ofBijective (gram C).toLinearMap (gram_bijective C hinj)) x = gram C x
  rw [LinearEquiv.ofBijective_apply]
  rfl

theorem gram_inverse_contDiff (C : ℝ × ℝ → (En n →L[ℝ] En m))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C)
    (hinj : ∀ p, Function.Injective (C p)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ContinuousLinearMap.inverse (gram (C p))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hinv : (gram (C p)).IsInvertible := ⟨gramEquiv (C p) (hinj p), gramEquiv_coe (C p) (hinj p)⟩
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => gram (C q)) :=
    gram_contDiff C hC
  exact (hinv.contDiffAt_map_inverse).comp p hsm.contDiffAt

/-- **The coefficient field.**  A smooth section `v` of `range (C ·)` where `C` is a smooth family
of injective linear maps is `C` applied to a smooth coefficient field `s`, which is automatically
nowhere zero. -/
theorem exists_coeff_of_mem_range
    (C : ℝ × ℝ → (En n →L[ℝ] En m))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C)
    (hinjC : ∀ p : ℝ × ℝ, Function.Injective (C p))
    (v : ℝ × ℝ → En m) (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (hv0 : ∀ p : ℝ × ℝ, v p ≠ 0)
    (hvP : ∀ p : ℝ × ℝ, v p ∈ LinearMap.range (C p).toLinearMap) :
    ∃ s : ℝ × ℝ → En n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s ∧
      (∀ p, C p (s p) = v p) ∧ (∀ p, s p ≠ 0) := by
  set sf : ℝ × ℝ → En n :=
    fun p => (ContinuousLinearMap.inverse (gram (C p))) ((adjFam (C p)) (v p)) with hsf
  have hprop : ∀ p, C p (sf p) = v p := by
    intro p
    obtain ⟨z, hz⟩ := hvP p
    have hgz : (adjFam (C p)) (C p z) = gram (C p) z := by
      simp only [gram, adjFam, ContinuousLinearMap.comp_apply]
    have hinv : (gram (C p)).IsInvertible :=
      ⟨gramEquiv (C p) (hinjC p), gramEquiv_coe (C p) (hinjC p)⟩
    have h1 : sf p = z := by
      show (ContinuousLinearMap.inverse (gram (C p))) ((adjFam (C p)) (v p)) = z
      have hvz : (adjFam (C p)) (v p) = (gram (C p)) z := by
        rw [← hz]
        exact hgz
      rw [hvz]
      exact hinv.inverse_apply_self z
    rw [h1]
    exact hz
  refine ⟨sf, ?_, hprop, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (adjFam (C p)) (v p)) :=
      (adjFam_contDiff C hC).clm_apply hv
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (ContinuousLinearMap.inverse (gram (C p))) ((adjFam (C p)) (v p))) :=
      (gram_inverse_contDiff C hC hinjC).clm_apply h1
    exact h2
  · intro p hzero
    have h := hprop p
    rw [hzero, map_zero] at h
    exact hv0 p h.symm

/-! ### Two consequences of the one-step extension -/






theorem exists_isoFamily_of_frame_local {m : ℕ}
    (b : ℝ → ℝ → (Fin m → En m))
    (hb : ∀ i : Fin m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => b p.1 p.2 i))
    (hind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2)) :
    ∃ Ψ : ℝ → ℝ → (En m ≃L[ℝ] En m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Ψ p.1 p.2 : En m →L[ℝ] En m)) ∧
      (∀ p : ℝ × ℝ, ∀ i : Fin m,
        Ψ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) i) = b p.1 p.2 i) := by
  classical
  haveI : FiniteDimensional ℝ (En m) := inferInstance
  set cf : Fin m → (En m →L[ℝ] ℝ) :=
    fun i => LinearMap.toContinuousLinearMap
      ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.coord i) with hcf
  have hcf_apply : ∀ (i : Fin m) (x : En m), cf i x = ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.repr x) i := by
    intro i x
    simp only [hcf, Module.Basis.coord_apply, LinearMap.coe_toContinuousLinearMap']
  set T : ℝ × ℝ → (En m →L[ℝ] En m) :=
    fun p => ∑ i, (cf i).smulRight (b p.1 p.2 i) with hT
  have hT_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T := by
    rw [hT]
    refine ContDiff.sum fun i _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (En m) (En m) (cf i)).contDiff.comp (hb i)
  have hT_apply : ∀ (p : ℝ × ℝ) (i : Fin m),
      T p ((EuclideanSpace.basisFun (Fin m) ℝ) i) = b p.1 p.2 i := by
    intro p i
    rw [hT]
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply]
    rw [Finset.sum_eq_single i]
    · rw [hcf_apply]
      simp
    · intro j _ hj
      rw [hcf_apply]
      simp [hj]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hT_gen : ∀ (p : ℝ × ℝ) (c : Fin m → ℝ),
      T p (∑ i, c i • (EuclideanSpace.basisFun (Fin m) ℝ) i) = ∑ i, c i • b p.1 p.2 i := by
    intro p c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT_apply]
  have hT_inj : ∀ p : ℝ × ℝ, Function.Injective (T p) := by
    intro p x y hxy
    have h0 : T p (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hx : x - y = ∑ i, ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.repr (x - y)) i
        • (EuclideanSpace.basisFun (Fin m) ℝ) i :=
      ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.sum_repr (x - y)).symm
    rw [hx, hT_gen] at h0
    have hcoeff : ∀ i, ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.repr (x - y)) i = 0 := by
      intro i
      refine Fintype.linearIndependent_iff.mp (hind p) _ h0 i
    have : x - y = 0 := by
      rw [hx]
      simp only [hcoeff, zero_smul, Finset.sum_const_zero]
    exact sub_eq_zero.mp this
  have hbij : ∀ p : ℝ × ℝ, Function.Bijective ⇑((T p).toLinearMap) := fun p =>
    ⟨hT_inj p, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (hT_inj p)⟩
  let E : ℝ × ℝ → (En m ≃L[ℝ] En m) := fun p =>
    LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective (T p).toLinearMap (hbij p))
  have hE_coe : ∀ p : ℝ × ℝ, ((E p : En m →L[ℝ] En m)) = T p := by
    intro p
    refine ContinuousLinearMap.ext fun x => ?_
    show (LinearEquiv.ofBijective (T p).toLinearMap (hbij p)) x = T p x
    rw [LinearEquiv.ofBijective_apply]
    rfl
  refine ⟨fun s t => E (s, t), ?_, ?_⟩
  · have : (fun p : ℝ × ℝ => (E p : En m →L[ℝ] En m)) = T := by
      funext p; exact hE_coe p
    rw [this]
    exact hT_sm
  · intro p i
    change (E p : En m →L[ℝ] En m) ((EuclideanSpace.basisFun (Fin m) ℝ) i) = b p.1 p.2 i
    rw [hE_coe p]
    exact hT_apply p i



theorem exists_smoothFrame_extension_local {m k : ℕ} (hkm : k ≤ m)
    (b : ℝ → ℝ → (Fin k → En m))
    (hb : ∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => b p.1 p.2 i))
    (hind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2)) :
    ∃ Ψ : ℝ → ℝ → (En m ≃L[ℝ] En m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Ψ p.1 p.2 : En m →L[ℝ] En m)) ∧
      (∀ p : ℝ × ℝ, ∀ i : Fin k,
        Ψ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) = b p.1 p.2 i) := by
  suffices key : ∀ d : ℕ, ∀ k : ℕ, m - k = d → ∀ (hk : k ≤ m),
      ∀ (b : ℝ → ℝ → (Fin k → En m)),
      (∀ i : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => b p.1 p.2 i)) →
      (∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2)) →
      ∃ Ψ : ℝ → ℝ → (En m ≃L[ℝ] En m),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => (Ψ p.1 p.2 : En m →L[ℝ] En m)) ∧
        (∀ p : ℝ × ℝ, ∀ i : Fin k,
          Ψ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hk i))
            = b p.1 p.2 i) by
    exact key (m - k) k rfl hkm b hb hind
  intro d
  induction d with
  | zero =>
      intro k hk hkm' b hb hind
      obtain rfl : m = k := by omega
      obtain ⟨Ψ, h1, h2⟩ := exists_isoFamily_of_frame_local b hb hind
      refine ⟨Ψ, h1, ?_⟩
      intro p i
      rw [show (Fin.castLE hkm' i) = i from Fin.ext rfl]
      exact h2 p i
  | succ d ih =>
      intro k hk hkm' b hb hind
      have hklt : k < m := by omega
      obtain ⟨w, hw_sm, hw_ind⟩ := exists_independent_extension_oneStep hklt b hb hind
      set b' : ℝ → ℝ → (Fin (k+1) → En m) := fun s t => Fin.snoc (b s t) (w s t) with hb'
      have hb'_sm : ∀ i : Fin (k+1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => b' p.1 p.2 i) := by
        intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
        · have hfun : (fun p : ℝ × ℝ => b' p.1 p.2 j.castSucc)
            = fun p : ℝ × ℝ => b p.1 p.2 j := by
            funext p; simp only [hb', Fin.snoc_castSucc]
          rw [hfun]; exact hb j
        · subst hlast
          have hfun : (fun p : ℝ × ℝ => b' p.1 p.2 (Fin.last k))
            = fun p : ℝ × ℝ => w p.1 p.2 := by
            funext p; simp only [hb', Fin.snoc_last]
          rw [hfun]; exact hw_sm
      have hb'_ind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b' p.1 p.2) := by
        intro p
        rw [hb']
        exact hw_ind p
      have hk' : k + 1 ≤ m := hklt
      obtain ⟨Ψ, hΨ_sm, hΨ_cols⟩ := ih (k+1) (by omega) hk' b' hb'_sm hb'_ind
      refine ⟨Ψ, hΨ_sm, ?_⟩
      intro p i
      have h := hΨ_cols p (Fin.castSucc i)
      rw [show (Fin.castLE hk' (Fin.castSucc i)) = Fin.castLE hkm' i from Fin.ext rfl] at h
      rw [h]
      simp only [hb', Fin.snoc_castSucc]

theorem exists_smoothIsoFamily_anchored_local {n : ℕ} (i₀ : Fin n)
    (u : ℝ → ℝ → En n)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => u p.1 p.2))
    (hu0 : ∀ p : ℝ × ℝ, u p.1 p.2 ≠ 0) :
    ∃ Ψ : ℝ → ℝ → (En n ≃L[ℝ] En n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Ψ p.1 p.2 : En n →L[ℝ] En n)) ∧
      (∀ p : ℝ × ℝ, Ψ p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) i₀) = u p.1 p.2) := by
  classical
  have hn1 : 1 ≤ n := by have h := i₀.isLt; omega
  haveI : NeZero n := ⟨by omega⟩
  have hind1 : ∀ p : ℝ × ℝ, LinearIndependent ℝ (fun _ : Fin 1 => u p.1 p.2) := by
    intro p
    rw [Fintype.linearIndependent_iff]
    intro g hg
    intro i
    have h := hg
    rw [Fin.sum_univ_one] at h
    rcases smul_eq_zero.mp h with h0 | h0
    · have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]; exact h0
    · exact absurd h0 (hu0 p)
  obtain ⟨Ψ₀, hΨ₀_sm, hΨ₀_cols⟩ := exists_smoothFrame_extension_local (m := n) (k := 1) hn1
    (fun a b _ => u a b) (fun _ => hu) hind1
  have hΨ₀_0 : ∀ p : ℝ × ℝ, Ψ₀ p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) 0) = u p.1 p.2 := by
    intro p
    have h := hΨ₀_cols p 0
    rwa [show (Fin.castLE hn1 (0 : Fin 1)) = (0 : Fin n) from Fin.ext rfl] at h
  -- the permuted frame family
  let τ : Fin n ≃ Fin n := Equiv.swap i₀ 0
  have hτ : τ i₀ = 0 := Equiv.swap_apply_left i₀ 0
  set f : ℝ → ℝ → (Fin n → En n) :=
    fun a b j => Ψ₀ a b ((EuclideanSpace.basisFun (Fin n) ℝ) (τ j)) with hf
  have hf_sm : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => f p.1 p.2 j) := by
    intro j
    exact hΨ₀_sm.clm_apply contDiff_const
  have hf_ind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (f p.1 p.2) := by
    intro p
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : (∑ j : Fin n, g j • ((EuclideanSpace.basisFun (Fin n) ℝ) (τ j))) = 0 := by
      have h1 : (Ψ₀ p.1 p.2) (∑ j : Fin n,
          g j • ((EuclideanSpace.basisFun (Fin n) ℝ) (τ j))) = 0 := by
        rw [map_sum]
        rw [← hg]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
      exact (Ψ₀ p.1 p.2).injective (by rw [h1, map_zero])
    have h3 : (∑ i : Fin n, g (τ.symm i) • ((EuclideanSpace.basisFun (Fin n) ℝ) i)) = 0 := by
      rw [← h2]
      exact (Fintype.sum_equiv τ
        (fun j => g j • (EuclideanSpace.basisFun (Fin n) ℝ) (τ j))
        (fun i => g (τ.symm i) • (EuclideanSpace.basisFun (Fin n) ℝ) i)
        (fun j => by simp)).symm
    have hbase := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbase
    intro j
    have hz := hbase (fun i => g (τ.symm i)) h3 (τ j)
    simpa using hz
  obtain ⟨Ψ, hΨ_sm, hΨ_cols⟩ := exists_isoFamily_of_frame_local f hf_sm hf_ind
  refine ⟨Ψ, hΨ_sm, ?_⟩
  intro p
  have h := hΨ_cols p i₀
  rw [h]
  show (Ψ₀ p.1 p.2) ((EuclideanSpace.basisFun (Fin n) ℝ) (τ i₀)) = u p.1 p.2
  rw [hτ]
  exact hΨ₀_0 p


/-! ### The target -/

theorem exists_anchoredFrameOfFlagFamily {m n : ℕ} (hnm : n ≤ m) (i₀ : Fin n)
    (C : ℝ → ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => C p.1 p.2))
    (hinjC : ∀ p : ℝ × ℝ, Function.Injective (C p.1 p.2))
    (v : ℝ → ℝ → EuclideanSpace ℝ (Fin m))
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => v p.1 p.2))
    (hvP : ∀ p : ℝ × ℝ, v p.1 p.2 ∈ LinearMap.range (C p.1 p.2).toLinearMap)
    (hv0 : ∀ p : ℝ × ℝ, v p.1 p.2 ≠ 0) :
    ∃ Φ : ℝ → ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Φ p.1 p.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) ∧
      (∀ p : ℝ × ℝ,
        Φ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hnm i₀)) = v p.1 p.2) ∧
      (∀ p : ℝ × ℝ, ∀ j : Fin n,
        Φ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hnm j))
          ∈ LinearMap.range (C p.1 p.2).toLinearMap) := by
  classical
  -- Step 1: the coefficient field of `v` in the columns of `C`.
  obtain ⟨s, hs_sm, hsC, hs0⟩ :=
    exists_coeff_of_mem_range (fun p : ℝ × ℝ => C p.1 p.2) hC hinjC
      (fun p : ℝ × ℝ => v p.1 p.2) hv hv0 hvP
  -- Step 2: the coefficient frame, anchored at the `i₀`-th slot.
  obtain ⟨R, hR_sm, hR_anchor⟩ :=
    exists_smoothIsoFamily_anchored_local i₀ (fun a b => s (a, b)) hs_sm hs0
  -- Step 3: the family of columns `C (R e_j)`.
  set b : ℝ → ℝ → (Fin n → EuclideanSpace ℝ (Fin m)) :=
    fun a b' j => C a b' (R a b' ((EuclideanSpace.basisFun (Fin n) ℝ) j)) with hb
  have hb_sm : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => b p.1 p.2 j) := by
    intro j
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => R p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) j)) :=
      hR_sm.clm_apply contDiff_const
    exact hC.clm_apply h1
  have hb_ind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2) := by
    intro p
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i : Fin n,
        g i • (R p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) i))) = 0 := by
      apply hinjC p
      rw [map_zero, ← hg]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have hbase := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.linearIndependent
    rw [Fintype.linearIndependent_iff] at hbase
    have h0 : (∑ i : Fin n, g i • ((EuclideanSpace.basisFun (Fin n) ℝ) i)) = 0 := by
      apply (R p.1 p.2).injective
      rw [map_zero, ← hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    exact hbase g h0
  -- Step 4: extend the columns to a frame of the ambient space.
  obtain ⟨Φ, hΦ_sm, hΦ_cols⟩ := exists_smoothFrame_extension_local hnm b hb_sm hb_ind
  -- Step 5: conclude.
  refine ⟨Φ, hΦ_sm, ?_, ?_⟩
  · intro p
    rw [hΦ_cols p i₀, hb]
    show C p.1 p.2 (R p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) i₀)) = v p.1 p.2
    rw [hR_anchor p]
    exact hsC p
  · intro p j
    rw [hΦ_cols p j, hb]
    exact LinearMap.mem_range.mpr ⟨R p.1 p.2 ((EuclideanSpace.basisFun (Fin n) ℝ) j), rfl⟩

end Work.Drive.Whitney
