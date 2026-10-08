import Mathlib
import Submission.Work.CharPrelim.FrobeniusBaseChangeSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Extension of scalars preserves the dimension of the fixed space

For a field extension `F → k`, a finite group `L`, an `F`-representation `ρ : Representation F L V`
on a finite-dimensional `F`-vector space `V`, and a finite subgroup `S ≤ L` whose order is
invertible in `k`, the dimension of the `S`-fixed space of the base-changed `k`-representation
`repBaseChange F k ρ` equals the dimension of the `S`-fixed space of `ρ`:
`dim_k (k ⊗ V)^S = dim_F V^S`.

The proof is the standard averaging argument, made purely linear-algebraic so that it is valid in
arbitrary characteristic (the only hypothesis on the order is its invertibility in `k`):

* the fixed space of a representation `σ` of a finite group `H` is the range of the *averaging
  map* `repAvg σ = |H|⁻¹ • ∑_{h ∈ H} σ h` (well defined because `|H|` is invertible, and a
  projection onto `σ.invariants`);
* `repAvg` commutes with extension of scalars,
  `repAvg (repBaseChange F k σ) = (repAvg σ).baseChange k`;
* extension of scalars preserves the dimension of the range of a linear endomorphism,
  `dim_k (range (T.baseChange k)) = dim_F (range T)`.

Note that `Invertible (|S| : k)` forces `char k ∤ |S|`; since `F → k` is injective this also gives
`char F ∤ |S|`, so the same averaging device is available over `F`.

The two ingredients of the last point are proved here as well: base change commutes with taking the
range of a linear map (`range_baseChange`), and base change of a submodule preserves its dimension
(`finrank_baseChange_submodule`).
-/

open scoped TensorProduct

set_option linter.style.haveILetI false

noncomputable section

namespace Work.CharPrelim

section Tensor

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

/-- **Base change commutes with the range of a linear map.**  For a linear map `f : M →ₗ[F] N` and
a field extension `F → k`, the range of the base-changed map `f.baseChange k` is the base change of
the range of `f`. -/
theorem range_baseChange {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module F M] [Module F N] (f : M →ₗ[F] N) :
    (LinearMap.range f).baseChange k = LinearMap.range (f.baseChange k) := by
  rw [Submodule.baseChange_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y hy
    change y ∈ Submodule.map (TensorProduct.mk F k N 1) f.range at hy
    rw [Submodule.mem_map] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    obtain ⟨m, hm⟩ := hn
    exact ⟨1 ⊗ₜ m, by rw [LinearMap.baseChange_tmul, hm]; rfl⟩
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      rw [LinearMap.baseChange_tmul]
      have h1 : (1 : k) ⊗ₜ[F] f n ∈
          Submodule.span k (Submodule.map (TensorProduct.mk F k N 1) (LinearMap.range f)) :=
        Submodule.subset_span (by
          change (TensorProduct.mk F k N 1) (f n) ∈
            Submodule.map (TensorProduct.mk F k N 1) f.range
          rw [Submodule.mem_map]; exact ⟨f n, ⟨n, rfl⟩, rfl⟩)
      have h2 : a ⊗ₜ[F] f n = a • ((1 : k) ⊗ₜ[F] f n) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h2]
      exact Submodule.smul_mem _ a h1
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- **Base change preserves the dimension of a submodule.**  For a submodule `p` of an `F`-module
`V` and a field extension `F → k`, the extension of scalars `p.baseChange k` of `p` has
`k`-dimension equal to the `F`-dimension of `p`. -/
theorem finrank_baseChange_submodule {V : Type*} [AddCommGroup V] [Module F V]
    (p : Submodule F V) :
    Module.finrank k ↥(p.baseChange k) = Module.finrank F ↥p := by
  haveI : Module.Free F ↥p := Module.Free.of_divisionRing F ↥p
  haveI : Module.Flat F k := Module.Flat.of_free
  have hinj : Function.Injective ⇑(p.subtype.baseChange k) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := k) p.subtype
      (Submodule.subtype_injective p)
  rw [show p.baseChange k = LinearMap.range (p.subtype.baseChange k) from rfl]
  rw [← (LinearEquiv.ofInjective (p.subtype.baseChange k) hinj).finrank_eq]
  exact Module.finrank_baseChange

/-- **Base change preserves the dimension of the range of an endomorphism.** -/
theorem finrank_range_baseChange {V : Type*} [AddCommGroup V] [Module F V]
    (T : V →ₗ[F] V) :
    Module.finrank k (LinearMap.range (T.baseChange k)) = Module.finrank F (LinearMap.range T) := by
  rw [← range_baseChange]
  exact finrank_baseChange_submodule (LinearMap.range T)

end Tensor

section Avg

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

/-- The **averaging map** of a representation `σ` of a finite group `H` over a field `F`:
`|H|⁻¹ • ∑_{h ∈ H} σ h`.  When `|H|` is invertible in `F` this is a projection onto the subspace
of `H`-invariant vectors, see `repAvg_range_eq_invariants`. -/
def repAvg {H : Type*} [Group H] [Fintype H] {V : Type*} [AddCommGroup V]
    [Module F V] (σ : Representation F H V) : V →ₗ[F] V :=
  (Fintype.card H : F)⁻¹ • ∑ h : H, σ h

variable {H : Type*} [Group H] [Fintype H] {V : Type*} [AddCommGroup V] [Module F V]

@[simp] lemma repAvg_apply (σ : Representation F H V) (v : V) :
    repAvg σ v = (Fintype.card H : F)⁻¹ • ∑ h : H, σ h v := by
  simp [repAvg]

/-- The averaging map lands in the invariants. -/
lemma repAvg_mem_invariants (σ : Representation F H V) (v : V) :
    repAvg σ v ∈ σ.invariants := by
  rw [Representation.mem_invariants]
  intro h₀
  have key : (σ h₀) * (repAvg σ) = repAvg σ := by
    rw [repAvg, mul_smul_comm, Finset.mul_sum]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulLeft h₀) (fun h : H => σ h)]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp
  rw [← Module.End.mul_apply, key]

/-- The averaging map fixes the invariants (here `|H|` must be nonzero in `F`). -/
lemma repAvg_id (σ : Representation F H V) (hcard : (Fintype.card H : F) ≠ 0) {v : V}
    (hv : v ∈ σ.invariants) : repAvg σ v = v := by
  rw [Representation.mem_invariants] at hv
  rw [repAvg_apply, Finset.sum_congr rfl (fun h _ => hv h), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F (Fintype.card H) v, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- When `|H|` is nonzero in `F`, the range of the averaging map is exactly the subspace of
invariants. -/
lemma repAvg_range_eq_invariants (σ : Representation F H V)
    (hcard : (Fintype.card H : F) ≠ 0) :
    (repAvg σ).range = σ.invariants := by
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact repAvg_mem_invariants σ w
  · intro v hv
    exact ⟨v, repAvg_id σ hcard hv⟩

/-- **The averaging map commutes with extension of scalars.** -/
theorem repAvg_baseChange (σ : Representation F H V) :
    repAvg (repBaseChange F k σ) = (repAvg σ).baseChange k := by
  rw [repAvg, repAvg, LinearMap.baseChange_smul]
  have hsum : LinearMap.baseChange k (∑ h : H, σ h) = ∑ h : H, (σ h).baseChange k :=
    map_sum (LinearMap.baseChangeHom F k V V) (fun h : H => σ h) Finset.univ
  rw [hsum]
  have hXF : (∑ h : H, repBaseChange F k σ h) = (∑ h : H, (σ h).baseChange k) :=
    Finset.sum_congr rfl (fun h _ => repBaseChange_apply F k σ h)
  rw [hXF]
  have hscalar : algebraMap F k ((Fintype.card H : F)⁻¹) = ((Fintype.card H : k)⁻¹) := by
    rw [map_inv₀, map_natCast]
  rw [← algebraMap_smul (A := k) ((Fintype.card H : F)⁻¹)
        (∑ h : H, (σ h).baseChange k), hscalar]

end Avg

/-- Extension of scalars `F → k` preserves the dimension of the fixed space of a finite subgroup
whose order is invertible in `k`. -/
theorem finrank_invariants_baseChange {F : Type*} [Field F] {k : Type*} [Field k]
    [Algebra F k] {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F L V) (S : Subgroup L) [Finite ↥S]
    [Invertible (Nat.card ↥S : k)] :
    Module.finrank k
        ↥(Representation.invariants ((repBaseChange F k ρ).comp S.subtype))
      = Module.finrank F ↥(Representation.invariants (ρ.comp S.subtype)) := by
  letI : Fintype ↥S := Fintype.ofFinite ↥S
  -- `|S|` is nonzero both in `k` (by hypothesis) and in `F` (by injectivity of `F → k`).
  have hcard_k : (Fintype.card ↥S : k) ≠ 0 := by
    have h : (Nat.card ↥S : k) ≠ 0 := Invertible.ne_zero (Nat.card ↥S : k)
    rwa [Nat.card_eq_fintype_card] at h
  have hcard_F : (Fintype.card ↥S : F) ≠ 0 := by
    intro h
    apply hcard_k
    have h1 : algebraMap F k (Fintype.card ↥S : F) = (Fintype.card ↥S : k) :=
      map_natCast (algebraMap F k) (Fintype.card ↥S)
    rw [← h1, h, map_zero]
  have hσ_inv : (repAvg (ρ.comp S.subtype)).range
      = Representation.invariants (ρ.comp S.subtype) :=
    repAvg_range_eq_invariants _ hcard_F
  have hτ_inv : (repAvg ((repBaseChange F k ρ).comp S.subtype)).range
      = Representation.invariants ((repBaseChange F k ρ).comp S.subtype) :=
    repAvg_range_eq_invariants _ hcard_k
  have havg : repAvg ((repBaseChange F k ρ).comp S.subtype)
      = (repAvg (ρ.comp S.subtype)).baseChange k :=
    repAvg_baseChange (ρ.comp S.subtype)
  calc Module.finrank k
        ↥(Representation.invariants ((repBaseChange F k ρ).comp S.subtype))
      = Module.finrank k ↥((repAvg ((repBaseChange F k ρ).comp S.subtype)).range) := by
          rw [hτ_inv]
    _ = Module.finrank k ↥(LinearMap.range ((repAvg (ρ.comp S.subtype)).baseChange k)) := by
          rw [havg]
    _ = Module.finrank F ↥(LinearMap.range (repAvg (ρ.comp S.subtype))) :=
          finrank_range_baseChange _
    _ = Module.finrank F ↥(Representation.invariants (ρ.comp S.subtype)) := by rw [hσ_inv]

end Work.CharPrelim
