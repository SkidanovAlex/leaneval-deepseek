import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.BSLit.Wielandt

/-- An idempotent endomorphism fixes every element of its range. -/
theorem idempotent_eq_self_of_mem_range {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (P : M →ₗ[R] M) (hP : P * P = P) {x : M} (hx : x ∈ LinearMap.range P) : P x = x := by
  obtain ⟨y, rfl⟩ := hx
  have := congrArg (fun (f : M →ₗ[R] M) => f y) hP
  simpa using this

/-- `ZMod (p ^ k)` is a local ring when `p` is prime and `1 ≤ k`.

Indeed `ZMod (p^k)` is nontrivial, and an element `x` is a unit iff `p ∤ x.val`; since two
nonunits have representatives divisible by `p`, their sum has representative divisible by `p`,
hence is a nonunit. -/
theorem isLocalRing_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    IsLocalRing (ZMod (p ^ k)) := by
  have hk0 : 0 < k := hk
  haveI : NeZero (p ^ k) := ⟨(pow_pos hp.pos k).ne'⟩
  have hne1 : (p ^ k) ≠ 1 := by
    have h2 : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    omega
  haveI : Nontrivial (ZMod (p ^ k)) := ZMod.nontrivial_iff.mpr hne1
  have hunit : ∀ x : ZMod (p ^ k), IsUnit x ↔ ¬ p ∣ x.val := by
    intro x
    constructor
    · intro h hdvd
      have h' : IsUnit ((x.val : ℕ) : ZMod (p ^ k)) := by
        rw [ZMod.natCast_zmod_val x]; exact h
      exact ((ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := k) hp hk0).mp h') hdvd
    · intro h
      have h' : IsUnit ((x.val : ℕ) : ZMod (p ^ k)) :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := k) hp hk0).mpr h
      rwa [ZMod.natCast_zmod_val x] at h'
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff] at ha hb ⊢
  have hpa : p ∣ a.val := by
    by_contra h
    exact ha ((hunit a).mpr h)
  have hpb : p ∣ b.val := by
    by_contra h
    exact hb ((hunit b).mpr h)
  have hcast : ((a.val + b.val : ℕ) : ZMod (p ^ k)) = a + b := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val a, ZMod.natCast_zmod_val b]
  intro hcon
  have hnu : ¬ IsUnit (((a.val + b.val : ℕ)) : ZMod (p ^ k)) := fun h =>
    ((ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := k) hp hk0).mp h) (Nat.dvd_add hpa hpb)
  exact hnu (by rw [hcast]; exact hcon)

/-- Over `ZMod (p^k)` (`p` prime, `k ≥ 1`) — a local ring — a finitely generated projective
module is free.  Concretely: the range of an idempotent endomorphism of a free finitely generated
`ZMod (p^k)`-module is again free (and finitely generated).

Route.  `N := LinearMap.range P` is a direct summand of the free module `M` (via the idempotent
`P`), hence projective (`Module.Projective.of_split`) and flat (`Module.Flat.of_projective`);
`N` is f.g. (image of a f.g. module), so it is free by
`Module.free_of_flat_of_isLocalRing` (`Mathlib/RingTheory/LocalRing/Module.lean`), once one has
`IsLocalRing (ZMod (p^k))` — which holds since `p^k ≥ 2` and the ideals of `ZMod (p^k)` form a
chain, the maximal one being `(p)`.  Concretely, with `𝔪 = (p)`, `N/𝔪N` is an `𝔽_p`-space of
dimension `r`; lifts `n₁,…,n_r` of a basis satisfy `N = ∑ᵢ ℤ/p^k · nᵢ` (Nakayama) and are
`ℤ/p^k`-independent, so they form a basis. -/
theorem FreeRangeIdempotent {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k) {M : Type*}
    [AddCommGroup M] [Module (ZMod (p^k)) M] [Module.Free (ZMod (p^k)) M]
    [Module.Finite (ZMod (p^k)) M] (P : M →ₗ[ZMod (p^k)] M) (hP : P * P = P) :
    Module.Free (ZMod (p^k)) (LinearMap.range P) ∧
      Module.Finite (ZMod (p^k)) (LinearMap.range P) := by
  haveI : IsLocalRing (ZMod (p ^ k)) := isLocalRing_zmod_prime_pow Fact.out hk
  -- `LinearMap.range P` is a direct summand of the free module `M`, hence projective and flat,
  -- and it is finitely generated as a quotient of `M`.
  have hfin : Module.Finite (ZMod (p ^ k)) (LinearMap.range P) := by
    refine Module.Finite.of_surjective
      (P.codRestrict (LinearMap.range P) fun x => LinearMap.mem_range_self P x) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hproj : Module.Projective (ZMod (p ^ k)) (LinearMap.range P) := by
    haveI : Module.Projective (ZMod (p ^ k)) M := Module.Projective.of_free
    refine Module.Projective.of_split (LinearMap.range P).subtype
      (P.codRestrict (LinearMap.range P) fun x => LinearMap.mem_range_self P x) ?_
    apply LinearMap.ext
    intro x
    exact Subtype.ext (idempotent_eq_self_of_mem_range P hP x.2)
  haveI := hproj
  haveI : Module.Flat (ZMod (p ^ k)) (LinearMap.range P) := Module.Flat.of_projective
  haveI := hfin
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end Work.BSLit.Wielandt
