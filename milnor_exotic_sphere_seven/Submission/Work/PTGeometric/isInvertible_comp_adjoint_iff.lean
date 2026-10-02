import Mathlib
import Submission.Work.PTGeometric.RieszProj.Defs
import Submission.Work.PTGeometric.ell_apply_frame_eq

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Invertibility of `ℓ ∘ Q ∘ ℓ†`

Let `Q ∈ Gr n k` be an orthogonal projection of rank `k` in `ℝⁿ` and let `ℓ : ℝⁿ → ℝᵏ` be linear.
Then the endomorphism `T = ℓ ∘ Q ∘ ℓ†` of `ℝᵏ` is invertible if and only if `ℓ` is injective on the
plane `V = im Q = {z | Q z = z}`.

The proof is the rank count of the "sandwich"
`V --ℓ--> ℝᵏ --Q∘ℓ†--> V --ℓ--> ℝᵏ`:
`T` factors through `ℓ|_V`, so `range T ⊆ ℓ(V)`, whence `finrank (range T) ≤ finrank ℓ(V)`.
Since `finrank V = trace Q = k = finrank ℝᵏ`:

* if `T` is invertible then `finrank (range T) = k`, so `finrank ℓ(V) = k` and `ℓ|_V` is injective;
* conversely if `ℓ|_V` is injective then `finrank ℓ(V) = k`, so `ℓ(V) = ℝᵏ`, hence (arguing with the
  self-adjointness of `Q` and the inner product) `ℓ† v ⊥ V` implies `v = 0`, i.e. `T` is injective,
  hence invertible (finite dimension).
-/

set_option maxHeartbeats 1000000

namespace Work.PTGeometric

/-- The finrank of `Amb m = ℝᵐ`. -/
private theorem finrank_Amb_aux (m : ℕ) : Module.finrank ℝ (Amb m) = m := by
  rw [finrank_euclideanSpace]
  simp

/-- **The rank of a member of the Grassmannian.**  An orthogonal projection in `Gr n k` (a
self-adjoint idempotent of trace `k`) has `k`-dimensional range. -/
private theorem finrank_range_eq_of_mem_Gr_aux {n k : ℕ} {Q : Amb n →L[ℝ] Amb n}
    (hQ : Q ∈ Gr n k) :
    Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) = k := by
  have hcomp : ∀ x : Amb n, Q (Q x) = Q x := by
    intro x
    have h : (Q * Q : Amb n →L[ℝ] Amb n) x = Q x := by rw [hQ.2.1]
    simpa using h
  have hQidem_lin : (Q : Amb n →ₗ[ℝ] Amb n) * (Q : Amb n →ₗ[ℝ] Amb n)
      = (Q : Amb n →ₗ[ℝ] Amb n) := by
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact hcomp y
  have hproj : LinearMap.IsProj (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n))
      (Q : Amb n →ₗ[ℝ] Amb n) :=
    (LinearMap.isProj_range_iff_isIdempotentElem (Q : Amb n →ₗ[ℝ] Amb n)).mpr hQidem_lin
  have h1 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n)
      = (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hproj.trace
  have h2 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hQ.2.2
  have h3 : (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
    rw [← h1, h2]
  exact Nat.cast_injective h3

/-- A continuous linear endomorphism of `ℝᵏ` is invertible if and only if it is injective. -/
private theorem isInvertible_iff_injective_endo_aux {k : ℕ} (A : Amb k →L[ℝ] Amb k) :
    A.IsInvertible ↔ Function.Injective A := by
  refine ⟨fun h => h.injective, fun h => ?_⟩
  have hker : (A : Amb k →ₗ[ℝ] Amb k).ker = ⊥ := LinearMap.ker_eq_bot.mpr h
  have hrange : (A : Amb k →ₗ[ℝ] Amb k).range = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
      (rfl : Module.finrank ℝ (Amb k) = Module.finrank ℝ (Amb k))).mp hker
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hrange,
    ContinuousLinearEquiv.coe_ofBijective A hker hrange⟩

/-- If a linear map out of a finite-dimensional plane `V` is not injective, the dimension of its
range drops below `finrank V`. -/
private theorem finrank_range_lt_of_not_injective_aux {n k : ℕ} (V : Submodule ℝ (Amb n))
    (L : V →ₗ[ℝ] Amb k) (h : ¬ Function.Injective L) :
    Module.finrank ℝ (LinearMap.range L) < Module.finrank ℝ V := by
  have hkerne : LinearMap.ker L ≠ ⊥ := fun hbot => h (LinearMap.ker_eq_bot.mp hbot)
  have hker0 : Module.finrank ℝ (LinearMap.ker L) ≠ 0 := by
    have hlt := Submodule.finrank_lt_finrank_of_lt (s := ⊥) (t := LinearMap.ker L)
      (Ne.bot_lt hkerne)
    rw [finrank_bot] at hlt
    omega
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  omega

/-- For an orthogonal projection `Q` of rank `k` (`Q ∈ Gr n k`) and `ℓ : ℝⁿ → ℝᵏ`, the
endomorphism `ℓ ∘ Q ∘ ℓ†` of `ℝᵏ` is invertible if and only if `ℓ` is injective on the plane
`{z | Q z = z}`. -/
theorem isInvertible_comp_adjoint_iff {n k : ℕ} (ℓ : Amb n →L[ℝ] Amb k) (Q : Amb n →L[ℝ] Amb n)
    (hQ : Q ∈ Gr n k) :
    (ℓ.comp (Q.comp ℓ.adjoint)).IsInvertible ↔
      (∀ z : Amb n, Q z = z → ℓ z = 0 → z = 0) := by
  -- `Q` is self-adjoint and idempotent
  have hQadj : Q.adjoint = Q := hQ.1
  have hcomp : ∀ x : Amb n, Q (Q x) = Q x := by
    intro x
    have h : (Q * Q : Amb n →L[ℝ] Amb n) x = Q x := by rw [hQ.2.1]
    simpa using h
  -- the plane `V = im Q = {z | Q z = z}`
  let V : Submodule ℝ (Amb n) := LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)
  have hVeq : V = LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n) := rfl
  have hVmem : ∀ z : Amb n, z ∈ V ↔ Q z = z := by
    intro z
    constructor
    · intro hz
      rw [hVeq] at hz
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
      rw [← hw]
      exact hcomp w
    · intro hz
      rw [hVeq]
      exact LinearMap.mem_range.mpr ⟨z, hz⟩
  have hVfin : Module.finrank ℝ V = k := by
    simpa [V] using finrank_range_eq_of_mem_Gr_aux (n := n) (k := k) hQ
  -- the restriction of `ℓ` to the plane
  let ℓlin : Amb n →ₗ[ℝ] Amb k := ℓ
  let L : V →ₗ[ℝ] Amb k := ℓlin.comp V.subtype
  have hInjL : (∀ z : Amb n, Q z = z → ℓ z = 0 → z = 0) ↔ Function.Injective L := by
    constructor
    · intro h x y hxy
      have hsub : ((x : V) : Amb n) - ((y : V) : Amb n) ∈ V := V.sub_mem x.2 y.2
      have hQz : Q (((x : V) : Amb n) - ((y : V) : Amb n))
          = ((x : V) : Amb n) - ((y : V) : Amb n) := (hVmem _).mp hsub
      have hxy' : ℓ ((x : V) : Amb n) = ℓ ((y : V) : Amb n) := hxy
      have hℓ : ℓ (((x : V) : Amb n) - ((y : V) : Amb n)) = 0 := by
        rw [map_sub, hxy', sub_self]
      have hz0 := h _ hQz hℓ
      exact Subtype.ext (sub_eq_zero.mp hz0)
    · intro h z hz hzℓ
      have hzV : z ∈ V := (hVmem z).mpr hz
      have hzero : L ⟨z, hzV⟩ = L 0 := by
        rw [map_zero]
        show ℓ z = 0
        exact hzℓ
      have hval : (⟨z, hzV⟩ : V) = 0 := h hzero
      simpa using congrArg Subtype.val hval
  -- `range T` is contained in `ℓ(V) = range L`
  have hrange_le : (ℓ.comp (Q.comp ℓ.adjoint) : Amb k →ₗ[ℝ] Amb k).range ≤ LinearMap.range L := by
    rintro y ⟨x, rfl⟩
    refine ⟨⟨Q (ℓ.adjoint x), ?_⟩, ?_⟩
    · rw [hVeq]
      exact LinearMap.mem_range.mpr ⟨ℓ.adjoint x, rfl⟩
    · show ℓ (Q (ℓ.adjoint x)) = (ℓ.comp (Q.comp ℓ.adjoint)) x
      rfl
  constructor
  · -- invertible `⇒` injective on the plane
    intro hA
    rw [hInjL]
    by_contra hnot
    have hlt : Module.finrank ℝ (LinearMap.range L) < k := by
      have := finrank_range_lt_of_not_injective_aux V L hnot
      rwa [hVfin] at this
    have hge : k ≤ Module.finrank ℝ (LinearMap.range L) := by
      have hsurj : Function.Surjective (ℓ.comp (Q.comp ℓ.adjoint)) := hA.surjective
      have hrtop : (ℓ.comp (Q.comp ℓ.adjoint) : Amb k →ₗ[ℝ] Amb k).range = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hfinA :
          Module.finrank ℝ ((ℓ.comp (Q.comp ℓ.adjoint) : Amb k →ₗ[ℝ] Amb k).range) = k := by
        rw [hrtop, finrank_top, finrank_Amb_aux]
      exact le_of_eq_of_le hfinA.symm (Submodule.finrank_mono hrange_le)
    omega
  · -- injective on the plane `⇒` invertible
    intro hinj
    have hInjL' : Function.Injective L := hInjL.mp hinj
    -- hence `ℓ` maps the plane onto `ℝᵏ`
    have hfinL : Module.finrank ℝ (LinearMap.range L) = k := by
      rw [LinearMap.finrank_range_of_inj hInjL', hVfin]
    have htop : LinearMap.range L = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hfinL, finrank_Amb_aux])
    have hsurjℓ : ∀ y : Amb k, ∃ u : V, ℓ (u : Amb n) = y := by
      intro y
      obtain ⟨u, hu⟩ := LinearMap.range_eq_top.mp htop y
      exact ⟨u, hu⟩
    -- `T` has trivial kernel
    have hSinj0 : ∀ v : Amb k, (ℓ.comp (Q.comp ℓ.adjoint)) v = 0 → v = 0 := by
      intro v hv
      have hv' : ℓ (Q (ℓ.adjoint v)) = 0 := hv
      have hQlv : Q (ℓ.adjoint v) = 0 :=
        hinj (Q (ℓ.adjoint v)) (hcomp (ℓ.adjoint v)) hv'
      have hD : ∀ w : Amb n, Q w = w → inner ℝ (ℓ.adjoint v) w = 0 := by
        intro w hw
        calc inner ℝ (ℓ.adjoint v) w
            = inner ℝ (ℓ.adjoint v) (Q w) := by rw [hw]
          _ = inner ℝ (Q.adjoint (ℓ.adjoint v)) w :=
                (ContinuousLinearMap.adjoint_inner_left Q w (ℓ.adjoint v)).symm
          _ = inner ℝ (Q (ℓ.adjoint v)) w := by rw [hQadj]
          _ = 0 := by rw [hQlv, inner_zero_left]
      have hzero : ∀ y : Amb k, inner ℝ v y = 0 := by
        intro y
        obtain ⟨u, hu⟩ := hsurjℓ y
        have huV : Q (u : Amb n) = (u : Amb n) := (hVmem _).mp u.2
        calc inner ℝ v y
            = inner ℝ v (ℓ (u : Amb n)) := by rw [hu]
          _ = inner ℝ (ℓ.adjoint v) (u : Amb n) :=
                (ContinuousLinearMap.adjoint_inner_left ℓ (u : Amb n) v).symm
          _ = 0 := hD (u : Amb n) huV
      exact inner_self_eq_zero.mp (hzero v)
    have hAinj : Function.Injective (ℓ.comp (Q.comp ℓ.adjoint)) := by
      intro v w hvw
      have h : (ℓ.comp (Q.comp ℓ.adjoint)) (v - w) = 0 := by
        rw [map_sub, hvw, sub_self]
      exact sub_eq_zero.mp (hSinj0 (v - w) h)
    exact (isInvertible_iff_injective_endo_aux (ℓ.comp (Q.comp ℓ.adjoint))).mpr hAinj

end Work.PTGeometric
