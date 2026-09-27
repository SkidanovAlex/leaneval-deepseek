import Mathlib
import Submission.Work.Mostow.jblocksDecomp
import Submission.Work.Mostow.orthonormalSigma
import Submission.Work.Mostow.gapA.screwTrig

set_option linter.style.haveILetI false

namespace Work.Mostow

/-- Given an orthogonal decomposition of a finite-dimensional real inner product space into pieces
`P p` carrying orthogonal complex structures `J p`, such that every element of an abelian family `𝓖`
of isometries acts as a complex scalar `a + b (J p)` on each piece (and commutes with `J p` there),
there is an orthonormal family of "rotation blocks" `(u j, v j)` spanning, on which every element of
`𝓖` acts as a rotation. -/
theorem blocksOfPieces {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (𝓖 : Subgroup (V ≃ₗᵢ[ℝ] V)) {η : Type*} [Fintype η]
    (P : η → Submodule ℝ V) (J : η → V →ₗ[ℝ] V)
    (horth : ∀ p p' : η, p ≠ p' → ∀ x ∈ P p, ∀ y ∈ P p', inner ℝ x y = 0)
    (hspan : ⨆ p, P p = ⊤)
    (hJ2 : ∀ p, ∀ x ∈ P p, J p (J p x) = -x)
    (hJi : ∀ p, ∀ x ∈ P p, ‖J p x‖ = ‖x‖)
    (hJmem : ∀ p, ∀ x ∈ P p, J p x ∈ P p)
    (hJcomm : ∀ T ∈ 𝓖, ∀ p, ∀ x ∈ P p, J p (T x) = T (J p x))
    (hscal : ∀ T ∈ 𝓖, ∀ p, ∃ a b : ℝ, ∀ x ∈ P p, T x = a • x + b • (J p x)) :
    ∃ (κ : Type) (_ : Fintype κ) (u v : κ → V),
      Orthonormal ℝ (fun j : κ × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else v j.1) ∧
      Submodule.span ℝ (Set.range (fun j : κ × Fin 2 =>
        if j.2 = (0 : Fin 2) then u j.1 else v j.1)) = ⊤ ∧
      (∀ T ∈ 𝓖, ∀ j : κ, ∃ t : ℝ, T (u j) = Real.cos t • u j + Real.sin t • v j ∧
          T (v j) = -Real.sin t • u j + Real.cos t • v j) := by
  classical
  -- Each piece carries an orthonormal family of `J p`-blocks spanning it.
  have piece : ∀ p : η, ∃ (κ : Type) (_ : Fintype κ) (u : κ → V),
      (∀ i, u i ∈ P p) ∧
      Orthonormal ℝ (fun j : κ × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else J p (u j.1)) ∧
      Submodule.span ℝ (Set.range (fun j : κ × Fin 2 =>
        if j.2 = (0 : Fin 2) then u j.1 else J p (u j.1))) = P p :=
    fun p => jblocksDecomp (P p) (J p) (hJ2 p) (hJi p) (hJmem p)
  choose κp hF up hup horthp hspanp using piece
  letI : ∀ p, Fintype (κp p) := hF
  -- the per-piece block family
  let blk : ∀ p, κp p × Fin 2 → V :=
    fun p j => if j.2 = (0 : Fin 2) then up p j.1 else J p (up p j.1)
  have hblkmem : ∀ p (j : κp p × Fin 2), blk p j ∈ P p := by
    intro p j
    change (if j.2 = (0 : Fin 2) then up p j.1 else J p (up p j.1)) ∈ P p
    split_ifs with hj
    · exact hup p j.1
    · exact hJmem p _ (hup p j.1)
  -- glue the pieces
  obtain ⟨hGlueOrth, hGlueSpan⟩ :=
    orthonormalSigma (W := V) P horth hspan (κ := fun p => κp p × Fin 2) blk hblkmem horthp hspanp
  -- reindex `Σ p, κp p × Fin 2` as `(Σ p, κp p) × Fin 2`
  let e : (Σ p, κp p) × Fin 2 ≃ (Σ p, κp p × Fin 2) :=
    { toFun := fun x => ⟨x.1.1, (x.1.2, x.2)⟩
      invFun := fun x => (⟨x.1, x.2.1⟩, x.2.2)
      left_inv := by rintro ⟨⟨p, k⟩, b⟩; rfl
      right_inv := by rintro ⟨p, k, b⟩; rfl }
  have hOrthG : Orthonormal ℝ ((fun x : Σ p, κp p × Fin 2 => blk x.1 x.2) ∘ e) :=
    hGlueOrth.comp e e.injective
  have hSpanG : Submodule.span ℝ (Set.range ((fun x : Σ p, κp p × Fin 2 => blk x.1 x.2) ∘ e)) = ⊤ := by
    rw [e.surjective.range_comp (fun x : Σ p, κp p × Fin 2 => blk x.1 x.2), hGlueSpan]
  let u : (Σ p, κp p) → V := fun y => up y.1 y.2
  let v : (Σ p, κp p) → V := fun y => J y.1 (up y.1 y.2)
  have hOrthUV : Orthonormal ℝ
      (fun j : (Σ p, κp p) × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else v j.1) := hOrthG
  have hSpanUV : Submodule.span ℝ (Set.range
      (fun j : (Σ p, κp p) × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else v j.1)) = ⊤ := hSpanG
  -- the rotation property on the `(Σ p, κp p)`-indexed blocks
  have hrot : ∀ T ∈ 𝓖, ∀ j : (Σ p, κp p), ∃ t : ℝ,
      T (u j) = Real.cos t • u j + Real.sin t • v j ∧
      T (v j) = -Real.sin t • u j + Real.cos t • v j := by
    rintro T hT ⟨p, k⟩
    have hx : up p k ∈ P p := hup p k
    obtain ⟨a, b, hab⟩ := hscal T hT p
    have hTx : T (up p k) = a • up p k + b • (J p (up p k)) := hab (up p k) hx
    have hTv : T (J p (up p k)) = -b • up p k + a • (J p (up p k)) := by
      rw [← hJcomm T hT p (up p k) hx, hTx]
      simp only [map_add, map_smul, hJ2 p (up p k) hx]
      module
    have hblk := orthonormal_iff_ite.mp (horthp p)
    have hxx : inner ℝ (up p k) (up p k) = 1 := by
      have hh := hblk (k, (0 : Fin 2)) (k, (0 : Fin 2))
      simpa using hh
    have hxv : inner ℝ (up p k) (J p (up p k)) = 0 := by
      have hne : (k, (0 : Fin 2)) ≠ (k, (1 : Fin 2)) := by simp
      have hh := hblk (k, (0 : Fin 2)) (k, (1 : Fin 2))
      simpa [hne] using hh
    have hvv : inner ℝ (J p (up p k)) (J p (up p k)) = 1 := by
      have hh := hblk (k, (1 : Fin 2)) (k, (1 : Fin 2))
      simpa using hh
    have hx1 : ‖up p k‖ = 1 := by
      have h2 : inner ℝ (up p k) (up p k) = ‖up p k‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [hxx] at h2
      nlinarith [norm_nonneg (up p k)]
    have hv1 : ‖J p (up p k)‖ = 1 := by
      have h2 : inner ℝ (J p (up p k)) (J p (up p k)) = ‖J p (up p k)‖ ^ 2 :=
        real_inner_self_eq_norm_sq _
      rw [hvv] at h2
      nlinarith [norm_nonneg (J p (up p k))]
    have hmain : ‖a • up p k + b • (J p (up p k))‖ = 1 := by
      rw [← hTx, T.norm_map, hx1]
    have hkey := norm_add_sq_real (a • up p k) (b • (J p (up p k)))
    rw [hmain, one_pow] at hkey
    have ha : ‖a • up p k‖ ^ 2 = a ^ 2 := by
      rw [norm_smul, hx1, mul_one, Real.norm_eq_abs, sq_abs]
    have hb : ‖b • (J p (up p k))‖ ^ 2 = b ^ 2 := by
      rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, sq_abs]
    have hc : inner ℝ (a • up p k) (b • (J p (up p k))) = 0 := by
      rw [real_inner_smul_left, real_inner_smul_right, hxv, mul_zero, mul_zero]
    rw [ha, hb, hc] at hkey
    have hab2 : a ^ 2 + b ^ 2 = 1 := by linarith
    obtain ⟨t, ht1, ht2⟩ := gapA.exists_cos_eq_sin_eq a b hab2
    refine ⟨t, ?_, ?_⟩
    · rw [hTx, ← ht1, ← ht2]
    · rw [hTv, ← ht1, ← ht2]
  -- transport to an index set in `Type 0` (the statement demands `κ : Type`)
  let ee : (Σ p, κp p) ≃ Fin (Fintype.card (Σ p, κp p)) := Fintype.equivFin _
  let g : Fin (Fintype.card (Σ p, κp p)) × Fin 2 → (Σ p, κp p) × Fin 2 :=
    fun j => (ee.symm j.1, j.2)
  have hginj : Function.Injective g := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [ee.symm.injective h1, h2]
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, b⟩
    exact ⟨(ee y, b), by simp [g]⟩
  refine ⟨Fin (Fintype.card (Σ p, κp p)), inferInstance,
    (fun i => u (ee.symm i)), (fun i => v (ee.symm i)), ?_, ?_, ?_⟩
  · exact hOrthUV.comp g hginj
  · have h1 : Set.range (fun j : Fin (Fintype.card (Σ p, κp p)) × Fin 2 =>
        if j.2 = (0 : Fin 2) then u (ee.symm j.1) else v (ee.symm j.1))
        = Set.range ((fun j : (Σ p, κp p) × Fin 2 =>
            if j.2 = (0 : Fin 2) then u j.1 else v j.1) ∘ g) := rfl
    rw [h1, hgsurj.range_comp
      (fun j : (Σ p, κp p) × Fin 2 => if j.2 = (0 : Fin 2) then u j.1 else v j.1), hSpanUV]
  · intro T hT i
    exact hrot T hT (ee.symm i)

end Work.Mostow
