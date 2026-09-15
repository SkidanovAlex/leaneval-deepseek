import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace Commons.Analysis.InnerProductSpace.LinearPMap

/-- If `T` is densely defined and `T†† = T`, then the adjoint `T†` is densely defined.
This is the standard fact that the adjoint of a closed densely defined operator is densely
defined; here the closedness of `T` is captured by `T†† = T`. -/
lemma dense_adjoint_domain {K E F : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace K F]
    [CompleteSpace F] (T : LinearPMap (RingHom.id K) E F) (hT : Dense (T.domain : Set E))
    (hvn : LinearPMap.adjoint (LinearPMap.adjoint T) = T) :
    Dense ((LinearPMap.adjoint T).domain : Set F) := by
  by_contra hh
  have hTzero : ∀ x : T.domain, T x = 0 := by
    intro x
    have hdom : (x : E) ∈ (LinearPMap.adjoint (LinearPMap.adjoint T)).domain := by
      rw [(LinearPMap.ext_iff.mp hvn).1]
      exact x.2
    have hzero : (LinearPMap.adjoint (LinearPMap.adjoint T)) ⟨(x : E), hdom⟩ = 0 :=
      LinearPMap.adjoint_apply_of_not_dense (T := LinearPMap.adjoint T) hh ⟨(x : E), hdom⟩
    have hval := (LinearPMap.ext_iff.mp hvn).2 (x := (x : E)) (hf := hdom) (hg := x.2)
    rw [← hval]
    exact hzero
  have htop : (LinearPMap.adjoint T).domain = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    exact LinearPMap.mem_adjoint_domain_of_exists (T := T) y ⟨0, by intro x; simp [hTzero x]⟩
  rw [htop] at hh
  exact hh (by simpa using dense_univ)

theorem exists_solution_of_bound {K E F G : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace K G] [CompleteSpace G] (T : LinearPMap (RingHom.id K) E F) (S : LinearPMap (RingHom.id K) F G) (hT : Dense (T.domain : Set E)) (hS : Dense (S.domain : Set F)) (hvn : LinearPMap.adjoint (LinearPMap.adjoint T) = T) (hdec : ∀ x : F, ∃ (x' : F) (h1 : x' ∈ S.domain), S ⟨x', h1⟩ = 0 ∧ (∀ (y : F) (hy : y ∈ S.domain), S ⟨y, hy⟩ = 0 → inner K y (x - x') = 0) ∧ (∃ (h5 : x - x' ∈ (LinearPMap.adjoint T).domain), LinearPMap.adjoint T ⟨x - x', h5⟩ = 0)) {C : ℝ} (hC : 0 ≤ C) (v : F) (hv : v ∈ S.domain) (hv0 : S ⟨v, hv⟩ = 0) (hbound : ∀ x : ↥(S.domain ⊓ (LinearPMap.adjoint T).domain), ‖inner K (x : F) v‖ ^ 2 ≤ C * (‖S ⟨(x : F), x.2.1⟩‖ ^ 2 + ‖LinearPMap.adjoint T ⟨(x : F), x.2.2⟩‖ ^ 2)) : ∃ u : E, ∃ hu : u ∈ T.domain, T ⟨u, hu⟩ = v ∧ ‖u‖ ^ 2 ≤ C := by
  have hDenseTadj : Dense ((LinearPMap.adjoint T).domain : Set F) := dense_adjoint_domain T hT hvn
  -- Reformulate `hbound` with the two proofs of membership separated.
  have hbound' : ∀ (x : F) (hS : x ∈ S.domain) (hA : x ∈ (LinearPMap.adjoint T).domain),
      ‖inner K x v‖ ^ 2 ≤ C * (‖S ⟨x, hS⟩‖ ^ 2 + ‖LinearPMap.adjoint T ⟨x, hA⟩‖ ^ 2) := by
    intro x hS hA
    have hxD : x ∈ (S.domain ⊓ (LinearPMap.adjoint T).domain) := Submodule.mem_inf.mpr ⟨hS, hA⟩
    have h := hbound ⟨x, hxD⟩
    have h1 : (⟨x, (⟨x, hxD⟩ : ↥(S.domain ⊓ (LinearPMap.adjoint T).domain)).2.1⟩ : S.domain)
        = ⟨x, hS⟩ := Subtype.ext rfl
    have h2 : (⟨x, (⟨x, hxD⟩ : ↥(S.domain ⊓ (LinearPMap.adjoint T).domain)).2.2⟩
        : (LinearPMap.adjoint T).domain) = ⟨x, hA⟩ := Subtype.ext rfl
    rw [h1, h2] at h
    simpa using h
  -- Step 1: on the domain of the adjoint, the functional is controlled by `T†`.
  have hbnd_sq : ∀ x : (LinearPMap.adjoint T).domain,
      ‖inner K v (x : F)‖ ^ 2 ≤ C * ‖LinearPMap.adjoint T x‖ ^ 2 := by
    intro x
    obtain ⟨x', h1, hSx', horth, h5, hT'x'⟩ := hdec (x : F)
    have hx'mem : x' ∈ (LinearPMap.adjoint T).domain := by
      have hmem := Submodule.sub_mem ((LinearPMap.adjoint T).domain) x.2 h5
      simpa using hmem
    have hT'y : LinearPMap.adjoint T ⟨x', hx'mem⟩ = LinearPMap.adjoint T x := by
      have hsplit : (⟨x', hx'mem⟩ : (LinearPMap.adjoint T).domain) +
          (⟨(x : F) - x', h5⟩ : (LinearPMap.adjoint T).domain) = x := by
        ext
        simp
      rw [← hsplit, LinearPMap.map_add, hT'x', add_zero]
    have horthv : inner K v ((x : F) - x') = 0 := horth v hv hv0
    have hinner_v : inner K v (x : F) = inner K v x' := by
      have h := horthv
      rw [inner_sub_right] at h
      exact sub_eq_zero.mp h
    have hb := hbound' x' h1 hx'mem
    rw [hSx', norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, hT'y] at hb
    rw [norm_inner_symm x' v, ← hinner_v] at hb
    exact hb
  have hbnd : ∀ x : (LinearPMap.adjoint T).domain,
      ‖inner K v (x : F)‖ ≤ Real.sqrt C * ‖LinearPMap.adjoint T x‖ := by
    intro x
    have h := hbnd_sq x
    have ha : (0 : ℝ) ≤ ‖inner K v (x : F)‖ := norm_nonneg _
    calc ‖inner K v (x : F)‖ = Real.sqrt (‖inner K v (x : F)‖ ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ Real.sqrt (C * ‖LinearPMap.adjoint T x‖ ^ 2) := Real.sqrt_le_sqrt h
      _ = Real.sqrt C * Real.sqrt (‖LinearPMap.adjoint T x‖ ^ 2) := Real.sqrt_mul hC _
      _ = Real.sqrt C * ‖LinearPMap.adjoint T x‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
  -- Step 2: build a bounded functional on the range of `T†` and extend it to `E`.
  let A : (LinearPMap.adjoint T).domain →ₗ[K] E := (LinearPMap.adjoint T).toFun
  let ℓ : (LinearPMap.adjoint T).domain →ₗ[K] K :=
    ((innerSL K v).comp ((LinearPMap.adjoint T).domain.subtypeL)).toLinearMap
  have hℓ_apply : ∀ x : (LinearPMap.adjoint T).domain, ℓ x = inner K v (x : F) := by
    intro x; rfl
  have hker : LinearMap.ker A ≤ LinearMap.ker ℓ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hx0 : LinearPMap.adjoint T x = 0 := hx
    have hb := hbnd x
    rw [hx0, norm_zero, mul_zero] at hb
    have h0 : inner K v (x : F) = 0 := by
      have : ‖inner K v (x : F)‖ = 0 := le_antisymm hb (norm_nonneg _)
      exact norm_eq_zero.mp this
    rw [hℓ_apply x, h0]
  let ψ₀ : ((LinearPMap.adjoint T).domain ⧸ LinearMap.ker A) →ₗ[K] K :=
    (LinearMap.ker A).liftQ ℓ hker
  let ψ : A.range →ₗ[K] K := ψ₀.comp A.quotKerEquivRange.symm.toLinearMap
  have hψ_eval : ∀ x : (LinearPMap.adjoint T).domain, ψ (A.rangeRestrict x) = ℓ x := by
    intro x
    have h1 : A.rangeRestrict x = (⟨A x, LinearMap.mem_range.mpr ⟨x, rfl⟩⟩ : A.range) := rfl
    have hsymm : A.quotKerEquivRange.symm (A.rangeRestrict x) = (LinearMap.ker A).mkQ x := by
      rw [h1]
      exact LinearMap.quotKerEquivRange_symm_apply_image A x (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    simp only [ψ, LinearMap.comp_apply]
    change ψ₀ (A.quotKerEquivRange.symm (A.rangeRestrict x)) = ℓ x
    rw [hsymm, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hψ_bound : ∀ m : A.range, ‖ψ m‖ ≤ Real.sqrt C * ‖m‖ := by
    intro m
    obtain ⟨x, hx⟩ : ∃ x, A x = (m : E) := LinearMap.mem_range.mp m.2
    have hm : m = A.rangeRestrict x := Subtype.ext (by simpa using hx.symm)
    rw [hm, hψ_eval x, hℓ_apply x]
    have hnorm : ‖(A.rangeRestrict x : A.range)‖ = ‖LinearPMap.adjoint T x‖ := rfl
    rw [hnorm]
    exact hbnd x
  let ψc : A.range →L[K] K := LinearMap.mkContinuous ψ (Real.sqrt C) hψ_bound
  have hψc_norm : ‖ψc‖ ≤ Real.sqrt C := ψc.opNorm_le_bound (Real.sqrt_nonneg C) hψ_bound
  obtain ⟨g, hg, hgn⟩ := exists_extension_norm_eq A.range ψc
  have hg_apply : ∀ m : A.range, g (m : E) = ψ m := by
    intro m; rw [hg m]; rfl
  let u : E := (InnerProductSpace.toDual K E).symm g
  have hu_norm : ‖u‖ ≤ Real.sqrt C := by
    have h1 : ‖u‖ = ‖g‖ := (InnerProductSpace.toDual K E).symm.norm_map g
    rw [h1, hgn]; exact hψc_norm
  have hu_eval : ∀ x : (LinearPMap.adjoint T).domain,
      inner K u (LinearPMap.adjoint T x) = inner K v (x : F) := by
    intro x
    have h1 : inner K u (LinearPMap.adjoint T x) = g (LinearPMap.adjoint T x) :=
      InnerProductSpace.toDual_symm_apply
    rw [h1]
    have h2 : g (LinearPMap.adjoint T x) = ψ (A.rangeRestrict x) := by
      have := hg_apply (A.rangeRestrict x)
      simpa [A] using this
    rw [h2, hψ_eval x, hℓ_apply x]
  -- Step 3: recover `u ∈ T.domain` with `T u = v`.
  have hu' : u ∈ (LinearPMap.adjoint (LinearPMap.adjoint T)).domain :=
    LinearPMap.mem_adjoint_domain_of_exists (T := LinearPMap.adjoint T) u
      ⟨v, fun x => (hu_eval x).symm⟩
  have hTuv : (LinearPMap.adjoint (LinearPMap.adjoint T)) ⟨u, hu'⟩ = v :=
    LinearPMap.adjoint_apply_eq (T := LinearPMap.adjoint T) hDenseTadj ⟨u, hu'⟩
      (fun x => (hu_eval x).symm)
  have Hu : u ∈ T.domain := by
    rw [← (LinearPMap.ext_iff.mp hvn).1]
    exact hu'
  refine ⟨u, Hu, ?_, ?_⟩
  · rw [← (LinearPMap.ext_iff.mp hvn).2 (x := u) (hf := hu') (hg := Hu)]
    exact hTuv
  · nlinarith [Real.sq_sqrt hC, norm_nonneg u]

end Commons.Analysis.InnerProductSpace.LinearPMap