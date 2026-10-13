import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM2p.RootClosure
import Submission.Work.DSM2p.frobSurj_rootClosurePos
import Submission.Work.DSM2p.sum_pow_sub_mem
import Submission.Work.DSM2p.isFrobIsoMod
import Submission.Work.DSM2p.exists_mul_of_pow_mem

/-!
# Level 1 of the `p`-integral tower for the Česnavičius–Scholze cover

`exists_eq_add_varpi_mul_of_pow_mem_CSAlgPos` : if `z ∈ Λ[1/ϖ]` satisfies `z ^ p ∈ A_∞`, then
`z = a + ϖ c` with `a ∈ A_∞ = CSAlgPos` and `c ∈ A' = CSIntegralClosurePos`.  This is the first
step of the computation of the `p`-integral closure (CS §`p-int-cl`, proof of `p-oid-rec`), read
as the statement that `z` lies in `A_∞ + ϖ A'`.

The proof is the one in the ČS source: write `z ^ p = λ + ϖ ^ p y` with `λ ∈ Λ`, `y ∈ A_∞`
(`exists_rootAlg_add_varpi_pow_mul_decomp`), pick `μ ∈ Λ` with `λ ≡ μ ^ p` modulo `(ϖ ^ p)`
(`frobSurj_rootClosurePos`), and compute modulo `(ϖ ^ p)` *inside* `A'` (where `ϖ ^ p` is not a
unit, so `sum_pow_sub_mem` carries information, unlike in `Λ[1/ϖ]`, where `ϖ` is inverted):
`(z - μ) ^ p ≡ z ^ p - μ ^ p ≡ 0`.  Since `(p) = (ϖ ^ p · unit)` in `A'`, this gives
`(z - μ) ^ p = ϖ ^ p c` with `c ∈ A'`, and `p`-integral closedness of `A'` plus
`exists_mul_of_pow_mem` (which needs `ϖ` to be a unit of `Λ[1/ϖ]`) turn this into `z - μ = ϖ c`.
Take `a = μ ∈ Λ ⊆ A_∞`.

**Note for consumers.**  The sibling file
`Submission.Work.DSM2p.exists_sub_mem_span_varpi_of_mem_CSIntegralClosurePos` (a work in progress
of a different author) carries a `sorry` stub with the very same name; the two declarations
cannot be imported into one file, so an importer of this module must not (transitively) import
that one, or must have the stub replaced by an import of this module.  This is why the present
file is self-contained and does *not* import it.
-/

open scoped Classical

-- The rings `RootAlgPos A p` and `RootAlgLocPos A p ϖ` are built from a quotient of an
-- `MvPolynomial` ring and a localization, so the default heartbeat budget is not enough for the
-- (few) instance searches below.
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.DSM2p

universe u

/-- **The `Λ + ϖ ^ p A_∞` decomposition of `A_∞ = CSAlgPos`.**

`A_∞ = Λ[F(T_F)/ϖ ^ m]` is generated as a ring by `Λ` and the fractional elements
`F(T_F)/ϖ ^ m` (`F ∈ 𝒫⁺`, `m ≥ 0`); each of the latter equals `ϖ ^ p · (F(T_F)/ϖ ^ (m + p))`
with the second factor again in `A_∞`, so `A_∞` is the subring `Λ + ϖ ^ p A_∞` of `Λ[1/ϖ]`. -/
theorem exists_rootAlg_add_varpi_pow_mul_decomp (p : ℕ) (A : Type*) [CommRing A]
    (ϖ : A) :
    ∀ x ∈ CSAlgPos A p ϖ, ∃ (l : RootAlgPos A p) (y : RootAlgLocPos A p ϖ),
      y ∈ CSAlgPos A p ϖ ∧
      x = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) l
        + (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p * y := by
  have hmap : algebraMap A (RootAlgLocPos A p ϖ) ϖ
      = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) (algebraMap A (RootAlgPos A p) ϖ) :=
    IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p ϖ) ϖ
  have hmemΛ : ∀ l : RootAlgPos A p,
      algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) l ∈ CSAlgPos A p ϖ :=
    fun l => Subring.subset_closure (Set.mem_union_left _ ⟨l, rfl⟩)
  have hmemϖ : algebraMap A (RootAlgLocPos A p ϖ) ϖ ∈ CSAlgPos A p ϖ := by
    rw [hmap]; exact hmemΛ _
  have hmemGen : ∀ q : MonicPolysPos A × ℕ,
      algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
          (Polynomial.aeval (rootVarPos A p q.1) q.1.1) *
        IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2 ∈ CSAlgPos A p ϖ :=
    fun q => Subring.subset_closure (Set.mem_union_right _ ⟨q, rfl⟩)
  -- the set of elements admitting such a decomposition is a subring of `Λ[1/ϖ]`
  let D : Subring (RootAlgLocPos A p ϖ) :=
    { carrier := {x | ∃ (l : RootAlgPos A p) (y : RootAlgLocPos A p ϖ),
        y ∈ CSAlgPos A p ϖ ∧
        x = algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) l
          + (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p * y}
      mul_mem' := by
        rintro a b ⟨l₁, y₁, hy₁, h₁⟩ ⟨l₂, y₂, hy₂, h₂⟩
        refine ⟨l₁ * l₂,
          y₁ * algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) l₂
            + (algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ) l₁ * y₂
              + (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p * (y₁ * y₂)), ?_, ?_⟩
        · exact add_mem (mul_mem hy₁ (hmemΛ l₂)) (add_mem (mul_mem (hmemΛ l₁) hy₂)
            (mul_mem (pow_mem hmemϖ p) (mul_mem hy₁ hy₂)))
        · rw [h₁, h₂, map_mul]
          ring
      add_mem' := by
        rintro a b ⟨l₁, y₁, hy₁, h₁⟩ ⟨l₂, y₂, hy₂, h₂⟩
        exact ⟨l₁ + l₂, y₁ + y₂, add_mem hy₁ hy₂, by rw [h₁, h₂, map_add]; ring⟩
      zero_mem' := ⟨0, 0, (CSAlgPos A p ϖ).zero_mem, by simp⟩
      one_mem' := ⟨1, 0, (CSAlgPos A p ϖ).zero_mem, by simp⟩
      neg_mem' := by
        rintro a ⟨l, y, hy, h⟩
        exact ⟨-l, -y, neg_mem hy, by rw [h, map_neg]; ring⟩ }
  -- each generator of `CSAlgPos` lies in `D`
  have hgen : (Set.range (algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)) ∪
      Set.range (fun q : MonicPolysPos A × ℕ =>
        algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
            (Polynomial.aeval (rootVarPos A p q.1) q.1.1) *
          IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2)) ⊆ (D : Set _) := by
    rintro y (⟨l, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨l, 0, (CSAlgPos A p ϖ).zero_mem, by simp⟩
    · change algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
            (Polynomial.aeval (rootVarPos A p q.1) q.1.1) *
          IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2 ∈ (D : Set _)
      have hmul : (algebraMap A (RootAlgLocPos A p ϖ) ϖ) *
          IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) = 1 := by
        rw [hmap]
        exact IsLocalization.Away.mul_invSelf (R := RootAlgPos A p)
          (S := RootAlgLocPos A p ϖ) (algebraMap A (RootAlgPos A p) ϖ)
      have hpow : (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p *
          IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ p = 1 := by
        rw [← mul_pow, hmul, one_pow]
      have h1 : IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2
          = (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p *
            IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ (q.2 + p) := by
        calc IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2
            = IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2 * 1 :=
              (mul_one _).symm
          _ = IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2 *
                ((algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p *
                  IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ p) := by
              rw [hpow]
          _ = (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p *
                (IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ q.2 *
                  IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ p) := by
              ring
          _ = (algebraMap A (RootAlgLocPos A p ϖ) ϖ) ^ p *
                IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ (q.2 + p) := by
              rw [pow_add]
      exact ⟨0, algebraMap (RootAlgPos A p) (RootAlgLocPos A p ϖ)
          (Polynomial.aeval (rootVarPos A p q.1) q.1.1) *
          IsLocalization.Away.invSelf (algebraMap A (RootAlgPos A p) ϖ) ^ (q.2 + p),
        hmemGen (q.1, q.2 + p), by rw [map_zero, zero_add, h1]; ring⟩
  intro x hx
  exact Subring.closure_le.mpr hgen hx

/-- **Binomial congruence, `x - y` form.**  If `(p)` lies in the ideal `(a ^ p)` and `x ^ p` and
`y ^ p` agree modulo `(a ^ p)`, then `x - y` is a `p`-th power modulo `(a ^ p)`.

Indeed `x = (x - y) + y`, and modulo `(a ^ p)` the Frobenius is additive
(`sum_pow_sub_mem`), so `x ^ p`, `(x - y) ^ p` and `y ^ p` add up. -/
theorem sub_pow_mem_span_of_sub_pow_mem {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {a x y : R} (hpa : (p : R) ∈ Ideal.span {a ^ p})
    (h : x ^ p - y ^ p ∈ Ideal.span {a ^ p}) :
    (x - y) ^ p ∈ Ideal.span {a ^ p} := by
  have h2 := sum_pow_sub_mem hp a hpa (x - y) y
  rw [sub_add_cancel] at h2
  have key : (x - y) ^ p = (x ^ p - y ^ p) - (x ^ p - (x - y) ^ p - y ^ p) := by ring
  rw [key]
  exact Ideal.sub_mem _ h h2

/-- **Level `1` of the `p`-integral tower.**  If `z ∈ Λ[1/ϖ]` satisfies `z ^ p ∈ A_∞`, then
`z = a + ϖ c` with `a ∈ A_∞` and `c ∈ A'`.

This is the computation of the first step of the `p`-integral closure (Česnavičius–Scholze,
§`p-int-cl`, proof of `p-oid-rec`), read as the statement `z ∈ A_∞ + ϖ A'`: by
`exists_rootAlg_add_varpi_pow_mul_decomp` write `z ^ p = λ + ϖ ^ p y` with `λ ∈ Λ`, `y ∈ A_∞`,
choose `μ ∈ Λ` with `λ ≡ μ ^ p` modulo `(ϖ ^ p)` (`frobSurj_rootClosurePos`) and observe that
`(z - μ) ^ p ∈ ϖ ^ p A'` — the first term because `z ^ p - μ ^ p = ϖ ^ p (·)` with the factor in
`A'`, the cross terms because their binomial coefficients are divisible by `p` and
`z ∈ A'` (p-integral closedness of `A'`) — so the p-integral closedness of `A'` gives
`(z - μ) / ϖ ∈ A'`.

The hypothesis that `Λ[1/ϖ]` is a localization at `ϖ` enters only through `ϖ` being a unit. -/
theorem exists_eq_add_varpi_mul_of_pow_mem_CSAlgPos (p : ℕ) [Fact p.Prime] (A : Type*)
    [CommRing A] (P : DSMap.PerfectoidData p A) (z : RootAlgLocPos A p (P.ϖ 0))
    (hz : z ^ p ∈ CSAlgPos A p (P.ϖ 0)) :
    ∃ (a : ↥(CSAlgPos A p (P.ϖ 0))) (c : ↥(CSIntegralClosurePos A p (P.ϖ 0))),
      z = (a : RootAlgLocPos A p (P.ϖ 0))
        + (algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)) *
          ((c : ↥(CSIntegralClosurePos A p (P.ϖ 0))) : RootAlgLocPos A p (P.ϖ 0)) := by
  have hp : p.Prime := Fact.out
  have hle : CSAlgPos A p (P.ϖ 0) ≤ CSIntegralClosurePos A p (P.ϖ 0) :=
    CSAlgPos_le_CSIntegralClosurePos A p (P.ϖ 0)
  have hΛmem : ∀ l : RootAlgPos A p,
      algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l ∈ CSAlgPos A p (P.ϖ 0) :=
    fun l => Subring.subset_closure (Set.mem_union_left _ ⟨l, rfl⟩)
  have hAmem : ∀ a : A,
      algebraMap A (RootAlgLocPos A p (P.ϖ 0)) a ∈ CSAlgPos A p (P.ϖ 0) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) a]
    exact hΛmem _
  -- (0) the `Λ + ϖ ^ p A_∞` decomposition of `z ^ p`
  obtain ⟨l, y, hy, hzy⟩ := exists_rootAlg_add_varpi_pow_mul_decomp p A (P.ϖ 0) (z ^ p) hz
  -- (1) approximate `λ` by a `p`-th power modulo `ϖ ^ p`
  obtain ⟨m, hm⟩ := frobSurj_rootClosurePos p A P l
  have hm' : l - m ^ p ∈ Ideal.span {(algebraMap A (RootAlgPos A p) (P.ϖ 0)) ^ p} := by
    simpa only [map_pow] using hm
  obtain ⟨t₀, ht₀⟩ := Ideal.mem_span_singleton.mp hm'
  have hμ : (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m) ^ p
      = algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l
        - (algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)) ^ p
          * algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) t₀ := by
    have h : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) (l - m ^ p)
        = algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0))
            ((algebraMap A (RootAlgPos A p) (P.ϖ 0)) ^ p * t₀) := by rw [ht₀]
    simp only [map_sub, map_pow, map_mul] at h
    rw [← IsScalarTower.algebraMap_apply A (RootAlgPos A p)
      (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)] at h
    rw [← h]; ring
  have hzy' : z ^ p - (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m) ^ p
      = (algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)) ^ p
        * (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) t₀ + y) := by
    rw [hzy, hμ]; ring
  -- (2) memberships in `A'`; in particular `z ∈ A'` by p-integral closedness
  have hzA' : z ∈ CSIntegralClosurePos A p (P.ϖ 0) :=
    (pIntClosure_isPIntegrallyClosed p (CSAlgPos A p (P.ϖ 0))) z (hle hz)
  have hμA' : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m
      ∈ CSIntegralClosurePos A p (P.ϖ 0) := hle (hΛmem m)
  have hwA' : algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)
      ∈ CSIntegralClosurePos A p (P.ϖ 0) := hle (hAmem _)
  have hc₁A' : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) t₀ + y
      ∈ CSIntegralClosurePos A p (P.ϖ 0) := hle (add_mem (hΛmem t₀) hy)
  have huA' : z - algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m
      ∈ CSIntegralClosurePos A p (P.ϖ 0) := sub_mem hzA' hμA'
  -- (3) work inside `A'`, where `(ϖ ^ p)` is a proper ideal
  set w' : ↥(CSIntegralClosurePos A p (P.ϖ 0)) :=
    ⟨algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0), hwA'⟩ with hw'def
  set u' : ↥(CSIntegralClosurePos A p (P.ϖ 0)) :=
    ⟨z - algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m, huA'⟩ with hu'def
  -- `(p) ⊆ (ϖ ^ p)` in `A'`, because `P.ϖ 0 ^ p = p * v` with `v` a unit
  have hpa : (p : ↥(CSIntegralClosurePos A p (P.ϖ 0))) ∈ Ideal.span {w' ^ p} := by
    obtain ⟨v, hv⟩ := P.unit
    have hcoe : ∀ a : A,
        ((algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) a :
          ↥(CSIntegralClosurePos A p (P.ϖ 0))) : RootAlgLocPos A p (P.ϖ 0))
          = algebraMap A (RootAlgLocPos A p (P.ϖ 0)) a := fun a => by
      rw [IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) a]
      rfl
    rw [Ideal.mem_span_singleton]
    refine ⟨algebraMap A ↥(CSIntegralClosurePos A p (P.ϖ 0)) (↑(v⁻¹) : A), ?_⟩
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, hcoe, hw'def]
    rw [← map_pow, hv, map_mul, map_natCast, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have h1 : (⟨z, hzA'⟩ : ↥(CSIntegralClosurePos A p (P.ϖ 0))) ^ p
      - (⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m, hμA'⟩ :
          ↥(CSIntegralClosurePos A p (P.ϖ 0))) ^ p
      = w' ^ p * ⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) t₀ + y, hc₁A'⟩ := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, Subring.coe_pow, Subring.coe_mul, hw'def]
    exact hzy'
  have h1mem : (⟨z, hzA'⟩ : ↥(CSIntegralClosurePos A p (P.ϖ 0))) ^ p
      - (⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m, hμA'⟩ :
          ↥(CSIntegralClosurePos A p (P.ϖ 0))) ^ p ∈ Ideal.span {w' ^ p} := by
    rw [h1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hu : u' ^ p ∈ Ideal.span {w' ^ p} := by
    rw [show u' = (⟨z, hzA'⟩ : ↥(CSIntegralClosurePos A p (P.ϖ 0)))
        - (⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m, hμA'⟩ :
            ↥(CSIntegralClosurePos A p (P.ϖ 0))) from rfl]
    exact sub_pow_mem_span_of_sub_pow_mem hp hpa h1mem
  -- (4) back in `Λ[1/ϖ]`: `(z - μ) ^ p = ϖ ^ p c` with `c ∈ A'`
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hu
  have hfin : ∃ c ∈ CSIntegralClosurePos A p (P.ϖ 0),
      (z - algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m) ^ p
        = (algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)) ^ p * c := by
    refine ⟨(c' : RootAlgLocPos A p (P.ϖ 0)), c'.2, ?_⟩
    have h := congrArg (fun t : ↥(CSIntegralClosurePos A p (P.ϖ 0)) =>
      (t : RootAlgLocPos A p (P.ϖ 0))) hc'
    simp only [Subring.coe_pow, Subring.coe_mul] at h
    rw [show ((w' : ↥(CSIntegralClosurePos A p (P.ϖ 0))) : RootAlgLocPos A p (P.ϖ 0))
        = algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0) from rfl] at h
    exact h
  -- (5) `ϖ` is a unit of `Λ[1/ϖ]`, so `exists_mul_of_pow_mem` extracts the quotient
  have hunit : IsUnit (algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)) := by
    rw [IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨w, hwS, hyeq⟩ := exists_mul_of_pow_mem (CSIntegralClosurePos A p (P.ϖ 0))
    (pIntClosure_isPIntegrallyClosed p (CSAlgPos A p (P.ϖ 0))) hunit huA' hfin
  exact ⟨⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) m, hΛmem m⟩,
    ⟨w, hwS⟩, by rw [add_comm]; exact sub_eq_iff_eq_add.mp hyeq⟩

end Work.DSM2p
