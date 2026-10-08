import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12.Gl2Cyclic

/-- If every vector of a nontrivial vector space `V` is an eigenvector of the endomorphism `M`
(up to scaling), then `M` is a scalar endomorphism.

This is the contrapositive engine that turns `∀ c, M ≠ c • 1` into the existence of a
vector `v` with `M v ∉ F ∙ v`. -/
lemma eq_smul_one_of_forall_mem_span_singleton {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Nontrivial V] {M : V →ₗ[F] V} (h : ∀ v : V, M v ∈ Submodule.span F {v}) :
    ∃ c : F, M = c • (1 : V →ₗ[F] V) := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨c₀, hc₀⟩ : ∃ c : F, c • v₀ = M v₀ := Submodule.mem_span_singleton.mp (h v₀)
  have key : ∀ w : V, M w = c₀ • w := by
    intro w
    by_cases hw : w ∈ Submodule.span F ({v₀} : Set V)
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
      rw [← ha, map_smul, ← hc₀]
      calc a • (c₀ • v₀) = (a * c₀) • v₀ := (smul_assoc a c₀ v₀).symm
        _ = (c₀ * a) • v₀ := by rw [mul_comm]
        _ = c₀ • (a • v₀) := smul_assoc c₀ a v₀
    · obtain ⟨c₁, hc₁⟩ : ∃ c : F, c • (v₀ + w) = M (v₀ + w) :=
        Submodule.mem_span_singleton.mp (h (v₀ + w))
      obtain ⟨c₂, hc₂⟩ : ∃ c : F, c • w = M w := Submodule.mem_span_singleton.mp (h w)
      have hli : LinearIndependent F ![v₀, w] :=
        (LinearIndependent.pair_iff' hv₀).mpr
          (fun a ha => hw (Submodule.mem_span_singleton.mpr ⟨a, ha⟩))
      have hsum : M (v₀ + w) = c₀ • v₀ + c₂ • w := by rw [map_add, ← hc₀, ← hc₂]
      have hEq : c₁ • v₀ + c₁ • w = c₀ • v₀ + c₂ • w := by rw [← smul_add, hc₁, hsum]
      have hzero : (c₁ - c₀) • v₀ + (c₁ - c₂) • w = 0 := by
        rw [sub_smul, sub_smul]
        rw [show c₁ • v₀ - c₀ • v₀ + (c₁ • w - c₂ • w)
            = (c₁ • v₀ + c₁ • w) - (c₀ • v₀ + c₂ • w) from by abel]
        rw [hEq, sub_self]
      obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hli) (c₁ - c₀) (c₁ - c₂) hzero
      have hc1 : c₁ = c₀ := sub_eq_zero.mp h1
      have hc2 : c₁ = c₂ := sub_eq_zero.mp h2
      rw [← hc₂, show c₂ = c₀ from by rw [← hc2, hc1]]
  refine ⟨c₀, ?_⟩
  ext w
  rw [key w]
  simp [LinearMap.smul_apply]

/-- The pair `(v, M v)` is linearly dependent exactly when `v = 0` or `M v` is a scalar
multiple of `v`. -/
lemma not_linearIndependent_pair_apply_iff {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (M : V →ₗ[F] V) (v : V) :
    ¬ LinearIndependent F ![v, M v] ↔ v = 0 ∨ M v ∈ Submodule.span F {v} := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h
    push Not at h
    obtain ⟨s, t, hst, hs⟩ := h
    by_cases ht0 : t = 0
    · left
      have hs0 : s ≠ 0 := fun h0 => (hs h0) ht0
      have hv : s • v = 0 := by simpa [ht0] using hst
      rcases smul_eq_zero.mp hv with h' | h'
      · exact absurd h' hs0
      · exact h'
    · right
      rw [Submodule.mem_span_singleton]
      refine ⟨-(t⁻¹ * s), ?_⟩
      have h1 : t • M v = -(s • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm, hst]
      calc (-(t⁻¹ * s)) • v = -((t⁻¹ * s) • v) := by rw [neg_smul]
        _ = -(t⁻¹ • (s • v)) := by rw [mul_smul]
        _ = t⁻¹ • (-(s • v)) := by rw [← smul_neg]
        _ = t⁻¹ • (t • M v) := by rw [← h1]
        _ = M v := inv_smul_smul₀ ht0 (M v)
  · rintro (rfl | hm)
    · intro h
      have h1 := h 1 0 (by simp)
      exact one_ne_zero h1.1
    · intro h
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨a, ha⟩ := hm
      have h1 := h (-a) 1 (by rw [neg_smul, ha]; simp)
      exact one_ne_zero h1.2

/-- Two independent vectors in a two-dimensional space span the whole space. -/
lemma span_pair_eq_top_of_linearIndependent {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {M : V →ₗ[F] V} {v : V}
    (hv : LinearIndependent F ![v, M v]) (h2 : Module.finrank F V = 2) :
    Submodule.span F ({v, M v} : Set V) = ⊤ := by
  have hrange : Set.range (![v, M v] : Fin 2 → V) = ({v, M v} : Set V) := by
    ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
  have hfin : Module.finrank F ↥(Submodule.span F (Set.range (![v, M v] : Fin 2 → V))) = 2 := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have htop := Submodule.eq_top_of_finrank_eq
    (S := Submodule.span F (Set.range (![v, M v] : Fin 2 → V))) (by rw [hfin, h2])
  rwa [hrange] at htop

/-- The centralizer of a non-scalar endomorphism of a two-dimensional vector space consists of
the polynomials in that endomorphism.

The proof is the classical one: since `M` is not a scalar, some vector `v` has `M v ∉ F ∙ v`, so
`{v, M v}` is a basis of `V`. Writing `y v = a • v + b • (M v)` and using that `y` commutes with
`M`, the map `y` and the polynomial `a + b X` evaluated at `M` agree on `v` and on `M v`, hence on
all of `V` (which is spanned by these two vectors). -/
theorem centralizer_eq_polynomials {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : Module.finrank F V = 2) {M : V →ₗ[F] V}
    (hM : ∀ c : F, M ≠ c • (1 : V →ₗ[F] V)) {y : V →ₗ[F] V} (hy : y * M = M * y) :
    ∃ p : Polynomial F, Polynomial.aeval M p = y := by
  have hnt : Nontrivial V := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank F V)
  -- A non-scalar endomorphism has a non-eigenvector.
  obtain ⟨v, hv⟩ : ∃ v : V, LinearIndependent F ![v, M v] := by
    by_contra hc
    push Not at hc
    have hmem : ∀ w : V, M w ∈ Submodule.span F {w} := by
      intro w
      rcases (not_linearIndependent_pair_apply_iff M w).mp (hc w) with h0 | hm
      · subst h0
        simp
      · exact hm
    obtain ⟨c, hc'⟩ := eq_smul_one_of_forall_mem_span_singleton hmem
    exact hM c hc'
  -- The two vectors `v` and `M v` span `V`.
  have hspan : Submodule.span F ({v, M v} : Set V) = ⊤ :=
    span_pair_eq_top_of_linearIndependent hv h2
  -- Expand `y v` in this spanning set.
  obtain ⟨a, b, hab⟩ : ∃ a b : F, a • v + b • M v = y v := by
    have : y v ∈ Submodule.span F ({v, M v} : Set V) := by rw [hspan]; trivial
    exact Submodule.mem_span_pair.mp this
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X, ?_⟩
  have haeval : Polynomial.aeval M (Polynomial.C a + Polynomial.C b * Polynomial.X)
      = a • (1 : V →ₗ[F] V) + b • M := by
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [haeval]
  -- `y` and `a • 1 + b • M` agree on `v` and on `M v`, hence on their span, which is everything.
  ext x
  have hx : x ∈ Submodule.span F ({v, M v} : Set V) := by rw [hspan]; trivial
  have hle : Submodule.span F ({v, M v} : Set V) ≤
      LinearMap.ker ((a • (1 : V →ₗ[F] V) + b • M) - y) := by
    rw [Submodule.span_le]
    intro z hz
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, ← hab]
      simp
    · have hyMv : y (M v) = M (y v) := by
        have h1 := congrArg (fun f : V →ₗ[F] V => f v) hy
        simpa using h1
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        hyMv, ← hab]
      simp
  have hmem := hle hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply] at hmem
  exact sub_eq_zero.mp hmem

end Work.ThmF.ChV12.Gl2Cyclic
