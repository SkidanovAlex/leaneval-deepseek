import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-! ## Counting lemmas for the `Bender–Suzuki` project

We prove here that for a free finitely generated module over `ZMod (p^k)` the number of
elements is the `k`-th power of the number of elements of its reduction modulo `p`.

The proof goes through coordinates: choosing a finite basis, one identifies `N` with a
function space `ι → ZMod (p^k)`, for which the reduction mod `p` is `ι → ZMod p`, and the
cardinality of `ZMod (p^k) ⧸ p` is `p`.  -/

/-- For a free module `M` over a commutative ring `R` with finite basis `b : Basis ι R M`
(with `ι` finite), the number of elements of `M` is `(Nat.card R) ^ (Fintype.card ι)`.
(If `M` is infinite both sides are `0`.) -/
theorem natCard_eq_pow_card_of_basis {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) :
    Nat.card M = (Nat.card R) ^ (Fintype.card ι) := by
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_pi]
  simp

/-- The range of the pointwise scalar multiple of the identity on a function space is the
product of the ranges of the corresponding scalars. -/
theorem range_smul_one_pi {R : Type*} [CommRing R] {ι : Type*} (s : R) :
    LinearMap.range (s • (1 : (ι → R) →ₗ[R] (ι → R)))
      = Submodule.pi Set.univ (fun _ : ι => LinearMap.range (s • (1 : R →ₗ[R] R))) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨y, rfl⟩ i; exact ⟨y i, rfl⟩
  · intro h; choose y hy using h; exact ⟨y, funext fun i => by simpa using hy i⟩

/-- Cardinality of the quotient of a finite product of copies of `R` by the pointwise range
of `s • 1`: it is the `Fintype.card ι`-th power of the corresponding quotient of `R`. -/
theorem natCard_pi_quotient_smul_one {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : R) :
    Nat.card ((ι → R) ⧸ LinearMap.range (s • (1 : (ι → R) →ₗ[R] (ι → R))))
      = (Nat.card (R ⧸ LinearMap.range (s • (1 : R →ₗ[R] R)))) ^ (Fintype.card ι) := by
  rw [range_smul_one_pi s,
    Nat.card_congr (Submodule.quotientPi
      (fun _ : ι => LinearMap.range (s • (1 : R →ₗ[R] R)))).toEquiv,
    Nat.card_pi]
  simp

/-- A linear equivalence `e : M ≃ₗ[R] M'` induces an equivalence of the quotients by the ranges
of `s • 1`. -/
noncomputable def quotient_range_smul_one_linearEquiv {R M M' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (s : R) :
    (M ⧸ LinearMap.range (s • (1 : M →ₗ[R] M))) ≃ₗ[R]
      (M' ⧸ LinearMap.range (s • (1 : M' →ₗ[R] M'))) := by
  refine Submodule.Quotient.equiv _ _ e ?_
  have key : (e : M →ₗ[R] M') ∘ₗ (s • (1 : M →ₗ[R] M)) =
      (s • (1 : M' →ₗ[R] M')) ∘ₗ (e : M →ₗ[R] M') := by
    ext x; simp
  have h1 : Submodule.map (e : M →ₗ[R] M') (LinearMap.range (s • (1 : M →ₗ[R] M)))
      = LinearMap.range ((e : M →ₗ[R] M') ∘ₗ (s • (1 : M →ₗ[R] M))) :=
    (LinearMap.range_comp (s • (1 : M →ₗ[R] M)) (e : M →ₗ[R] M')).symm
  rw [h1, key, LinearMap.range_comp, LinearMap.range_eq_top.mpr e.surjective, Submodule.map_top]

/-- For `p` prime and `k ≥ 1`, the reduction `ZMod (p^k) ⧸ p` has exactly `p` elements. -/
theorem natCard_zmod_quot_range_p_smul_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    Nat.card (ZMod (p^k) ⧸
      LinearMap.range ((p : ZMod (p^k)) • (1 : ZMod (p^k) →ₗ[ZMod (p^k)] ZMod (p^k)))) = p := by
  have : NeZero (p^k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have h : p ∣ p^k := by simpa using pow_dvd_pow p hk
  let φ : ZMod (p^k) →+* ZMod p := ZMod.castHom h (ZMod p)
  have hker : RingHom.ker φ
      = LinearMap.range ((p : ZMod (p^k)) • (1 : ZMod (p^k) →ₗ[ZMod (p^k)] ZMod (p^k))) := by
    ext x
    rw [RingHom.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : (x.val : ZMod p) = 0 := by
        rw [ZMod.natCast_val]
        rwa [← ZMod.castHom_apply (h := h) (R := ZMod p)]
      obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hx'
      refine ⟨(t : ZMod (p^k)), ?_⟩
      change (p : ZMod (p^k)) * (t : ZMod (p^k)) = x
      rw [← Nat.cast_mul, ← ht, ZMod.natCast_zmod_val]
    · rintro ⟨y, rfl⟩
      have hp0 : φ (p : ZMod (p^k)) = 0 := by
        rw [ZMod.castHom_apply, ZMod.cast_natCast h p, ZMod.natCast_self]
      change φ ((p : ZMod (p^k)) * y) = 0
      rw [map_mul, hp0, zero_mul]
  rw [← hker]
  exact (Nat.card_congr
      (RingHom.quotientKerEquivOfSurjective (ZMod.castHom_surjective h)).toEquiv).trans
    (Nat.card_zmod p)

/-- For a free finitely generated `ZMod (p^k)`-module `N` (`p` prime, `k ≥ 1`), the number of
elements of `N` is the `k`-th power of the number of elements of its reduction `N ⧸ pN`, where
`pN` is the image of multiplication by `p : ZMod (p^k)`, written here as
`LinearMap.range ((p : ZMod (p^k)) • (1 : N →ₗ N))`.  (Note the elaboration pitfall: `p • ⊤` with
`p : ℕ` is the `n`-fold *submodule sum* `⊤ + ⋯ + ⊤ = ⊤`, which is **not** the intended submodule;
the `•` below is the `ZMod (p^k)`-action on the endomorphism ring.)

Indeed `N ≅ (ZMod (p^k))^r` for some `r` (finite free module), so `Nat.card N = (p^k)^r` and
`N ⧸ pN ≅ (ZMod p)^r` (the quotient is a `ZMod (p^k)`-module killed by `p`, of cardinality `p^r`),
whence `(Nat.card (N ⧸ pN))^k = (p^r)^k = p^{rk} = (p^k)^r`.

Route: use a basis of `N` (`Module.Finite` + `Module.Free`), identify `N ⧸ pN` with the
`p`-reduction of the coordinate space, and count; `Nat.card` of a finite type and
`Nat.card (ZMod n) = n` (`ZMod.card`) are the ingredients; `p · x = (p : ZMod (p^k)) • x`. -/
theorem NatCardQuotPowB {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k) {N : Type*} [AddCommGroup N]
    [Module (ZMod (p^k)) N] [Module.Free (ZMod (p^k)) N] [Module.Finite (ZMod (p^k)) N] :
    Nat.card N =
      (Nat.card (N ⧸ LinearMap.range ((p : ZMod (p^k)) • (1 : N →ₗ[ZMod (p^k)] N))))^k := by
  have hp := Fact.out (p := p.Prime)
  have : Fact (1 < p^k) := ⟨Nat.one_lt_pow (by omega) hp.one_lt⟩
  have : Nontrivial (ZMod (p^k)) := ZMod.nontrivial (p^k)
  have : StrongRankCondition (ZMod (p^k)) := inferInstance
  let b := Module.finBasis (ZMod (p^k)) N
  have hN : Nat.card N = (p^k)^(Module.finrank (ZMod (p^k)) N) := by
    rw [natCard_eq_pow_card_of_basis b, Fintype.card_fin, Nat.card_zmod]
  have hQ : Nat.card (N ⧸ LinearMap.range ((p : ZMod (p^k)) • (1 : N →ₗ[ZMod (p^k)] N)))
      = p^(Module.finrank (ZMod (p^k)) N) := by
    rw [Nat.card_congr (quotient_range_smul_one_linearEquiv b.equivFun (p : ZMod (p^k))).toEquiv,
      natCard_pi_quotient_smul_one
        (R := ZMod (p^k)) (ι := Fin (Module.finrank (ZMod (p^k)) N)) (s := (p : ZMod (p^k))),
      Fintype.card_fin, natCard_zmod_quot_range_p_smul_one hp hk]
  rw [hN, hQ,
    show (p ^ k) ^ Module.finrank (ZMod (p ^ k)) N = p ^ (k * Module.finrank (ZMod (p ^ k)) N)
      from (pow_mul p k _).symm,
    show (p ^ Module.finrank (ZMod (p ^ k)) N) ^ k = p ^ (Module.finrank (ZMod (p ^ k)) N * k)
      from (pow_mul p _ k).symm,
    Nat.mul_comm k (Module.finrank (ZMod (p ^ k)) N)]

end Work.BSLit.Wielandt
