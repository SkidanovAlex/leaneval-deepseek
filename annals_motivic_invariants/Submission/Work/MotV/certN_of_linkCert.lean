import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.SpreadClasses
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotA.resEquiv_iff_fractionRing
import Submission.Work.MotA.divCount_rename
import Submission.Work.MotA.awayAlgEquiv_stab

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

/-- Node SPREAD (`S1` + `A3` + class transfer): spread a `K = 𝕜(t)`-level link certificate
(`LinkCert`) over `𝔸¹_t` and stabilise, producing a `𝕜`-level certificate in `n` variables
(`n ≥ 4`).

Route (§4 of the design; the three steps `S1`, `A3`, classes).
* **Setting.** `L : LinkCert (RatFunc 𝕜) F₁ F₂` consists of `F, G ∈ K[x₀,x₁,x₂]` with `F, G ≠ 0`,
  `Φ : K[x]_F ≃ₐ[K] K[x]_G`, and a height-one point `zP` of `𝔸³_K` with `G ∈ zP.asIdeal` whose
  residue field is `RatFunc F₁`, all other height-one points on `V(G)` junk (`GeomRuled`), and all
  height-one points of `V(F)` either with residue field `RatFunc F₂` or junk.
* **`S1` (clearing denominators).**  Write `F, G ∈ 𝕜[t][x]` by clearing denominators of their
  coefficients; `Φ` is `𝕜[t]`-linear after inverting finitely many `t`-polynomials; adjoin those
  `t`-polynomials to `F` and `G`.  `𝕜[t][x] = 𝕜[x][t]` is a UFD (Gauss), so the height-one primes
  of `V(G)` in `𝔸⁴_𝕜` are of two kinds: *horizontal* (whose contraction to `K[x]` is a height-one
  prime, with the same residue field — by localisation) and *vertical* `(g(t))` with
  `g ∈ 𝕜[t]` irreducible, with residue field `Frac (𝕜[t]/(g))[x] = RatFunc 𝕜'(x₀,x₁,x₂)` where
  `𝕜' = 𝕜[t]/(g)`; the latter are junk (`GeomRuled`, non-constants-only over `𝕜`).  The units of
  `K[x]_G` are `c(t) · ∏ g_j^{n_j}` (a scalar times powers of the prime factors of `G`), which is
  what makes `𝕜[t][x]_G` the right intermediate ring for the spreading.
* **`A3` (stabilisation).**  Rename the four variables into `n` variables with
  `Work.MotA.divCount_rename`, `Work.MotA.awayAlgEquiv_stab`, `Work.MotA.quotient_map_rename`
  (only rational junk is added; the extra prime factors are the strict transforms of hyperplanes
  and are rational).
* **Classes.**  On the `G`-side keep only the horizontal lift of `zP`: its class is
  `D_P = Frac (MvPolynomial (Fin (n-3)) F₁)`.  *No other height-one prime of `V(G)` represents the
  same class*: if `x` were such a prime with `JunkClass 𝕜 x` (or an `F`-side prime), then
  `ResEquiv 𝕜 x z` would give `RatFunc F₀ ≅ RatFunc F₁` (for the `F₀` of the junk decomposition),
  hence `F₀ ≅ F₁` by `ratFunc_cancel` (node CAN, `m = 1`, using `hCO : ConstantsOnly 𝕜 F₁`),
  contradicting `GeomRuled 𝕜 F₀` (apply `ConstantsOnly 𝕜 F₁` to the composite
  `F₁ ≅ F₀ →ₐ[𝕜] RatFunc M`); on the `F`-side `RatFunc F₂ ≅ RatFunc F₁` would give `F₁ ≅ F₂` by
  CAN, contradicting `hR : IsEmpty (F₁ ≃ₐ[𝕜] F₂)`.  Note this argument works at `n = 4` as well
  (where `D_P = RatFunc F₁`), since CAN only needs `m ≥ 0`; what is used is
  `RatFunc F₁ ≇ RatFunc F₀`, not `¬ GeomRuled (RatFunc F₁)`. -/
theorem certN_of_linkCert (𝕜 : Type) [Field 𝕜] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra (RatFunc 𝕜) F₁] [Algebra (RatFunc 𝕜) F₂] [Algebra 𝕜 F₁] [Algebra 𝕜 F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (L : LinkCert (RatFunc 𝕜) F₁ F₂) (hCO : ConstantsOnly 𝕜 F₁) (hR : IsEmpty (F₁ ≃ₐ[𝕜] F₂))
    (n : ℕ) (hn : 4 ≤ n) : Nonempty (CertN 𝕜 n) := by
  classical
  -- It suffices to build the certificate in `4 + (n - 4)` variables.
  suffices h : Nonempty (CertN 𝕜 (4 + (n - 4))) by
    rwa [Nat.add_sub_cancel' hn] at h
  -- ## `S1`: spread the `K`-level link over `𝔸¹_t`.
  obtain ⟨cF, cG, hcF, hcG, F', G', hF'ne, hG'ne, hF'eq, hG'eq, ⟨Ψ⟩⟩ :=
    Work.MotA.exists_spread_awayAlgEquiv 𝕜 3 L.F L.G L.hF L.hG L.Φ
  -- ## `A3`: stabilise from `4` to `4 + (n - 4)` variables.
  obtain ⟨Ψn⟩ := Work.MotA.awayAlgEquiv_stab 𝕜 4 (n - 4) F' G' Ψ
  -- ## The distinguished point: the horizontal lift `q` of `zP`, stabilised.
  set q : Ideal (MvPolynomial (Fin 4) 𝕜) :=
    Ideal.comap (Work.MotA.spreadMap 𝕜 3) L.zP.asIdeal with hq
  haveI hzPprime : L.zP.asIdeal.IsPrime := L.zP.isPrime
  haveI hqprime : q.IsPrime := Ideal.comap_isPrime _ _
  have hqht : q.height = 1 := by
    rw [hq, (Work.MotV5.class_of_comap_spread (𝕜 := 𝕜) L.zP.asIdeal).1,
      AlgebraicGeometry.idealHeight_eq_coheight, L.zP_ht]
  let hz₄ : Work.MotA.polySpec 𝕜 4 := ⟨q, hqprime⟩
  have hz₄as : hz₄.asIdeal = q := rfl
  have hz₄ht : Order.coheight hz₄ = 1 := by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight, hz₄as]
    exact hqht
  obtain ⟨π, hπ, hqπ⟩ := (Work.MotA.coheight_eq_one_iff 𝕜 4 hz₄).mp hz₄ht
  have hqπ' : q = Ideal.span {π} := by rw [← hz₄as]; exact hqπ
  have hzht : (q.map (MvPolynomial.rename (Fin.castAdd (n - 4)))).height = 1 := by
    rw [hqπ', Ideal.map_span, Set.image_singleton]
    exact Work.MotA.height_span_singleton_renameCastAdd 𝕜 4 (n - 4) hπ
  have hzmap_prime : (q.map (MvPolynomial.rename (Fin.castAdd (n - 4)))).IsPrime :=
    Work.MotA.renameCastAdd_isPrime 𝕜 4 (n - 4) hqprime
  let z : Work.MotA.polySpec 𝕜 (4 + (n - 4)) :=
    ⟨q.map (MvPolynomial.rename (Fin.castAdd (n - 4))), hzmap_prime⟩
  have hG'q : G' ∈ q := by
    rw [hq]
    exact Ideal.mem_comap.mpr (by
      rw [hG'eq]
      exact Ideal.mul_mem_left L.zP.asIdeal _ L.zP_mem)
  -- The class of `z` is `Frac(MvPolynomial (Fin ((n-4)+1)) F₁)`.
  have hzclass : Nonempty (FractionRing (MvPolynomial (Fin (4 + (n - 4))) 𝕜 ⧸ z.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin ((n - 4) + 1)) F₁)) :=
    class_stab_of_class (n - 4) q (class_comap_zP L)
  refine ⟨{ F := MvPolynomial.rename (Fin.castAdd (n - 4)) F',
            G := MvPolynomial.rename (Fin.castAdd (n - 4)) G',
            hF := ?_, hG := ?_, Φ := Ψn, z := z, z_ht := ?_, z_mem := ?_,
            G_other := ?_, F_none := ?_ }⟩
  · -- `hF`
    intro h
    exact hF'ne (MvPolynomial.rename_injective (Fin.castAdd (n - 4))
      (Fin.castAdd_injective 4 (n - 4)) (by simpa using h))
  · -- `hG`
    intro h
    exact hG'ne (MvPolynomial.rename_injective (Fin.castAdd (n - 4))
      (Fin.castAdd_injective 4 (n - 4)) (by simpa using h))
  · -- `z_ht`
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]
    show (q.map (MvPolynomial.rename (Fin.castAdd (n - 4)))).height = 1
    exact hzht
  · -- `z_mem`
    exact Ideal.mem_map_of_mem _ hG'q
  · -- `G_other`: the only prime divisor of `V(G')` with the class of `z` is `z` itself.
    intro x hx1 hxmem hne hres
    haveI hxprime : x.asIdeal.IsPrime := x.isPrime
    obtain ⟨hp1, hp2⟩ := Work.MotA.height_comap_renameCastAdd 𝕜 4 (n - 4) G' hG'ne x.asIdeal
      x.isPrime (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hx1) hxmem
    set p' : Ideal (MvPolynomial (Fin 4) 𝕜) :=
      Ideal.comap (MvPolynomial.rename (Fin.castAdd (n - 4))) x.asIdeal with hp'
    haveI hp'prime : p'.IsPrime := Ideal.comap_isPrime _ _
    have hG'p : G' ∈ p' := by
      rw [hp']
      exact Ideal.mem_comap.mpr hxmem
    have hP : x.asIdeal = p'.map (MvPolynomial.rename (Fin.castAdd (n - 4))) := by
      rw [hp']
      exact hp2.symm
    rcases Work.MotV5.census_G_alt (𝕜 := 𝕜) L G' cG hcG hG'eq p' hp1 hG'p with
      hpq | ⟨F₀, hF₀, hA₀, hnc, hcls⟩
    · -- the horizontal lift of `zP` is `z` itself
      refine hne (PrimeSpectrum.ext ?_)
      show x.asIdeal = z.asIdeal
      rw [hP, hpq, hq.symm]
    · -- junk class
      exact not_resEquiv_of_class_stab (𝕜 := 𝕜) (k := n - 4) hCO hnc hzclass
        (class_stab_of_class_map (k := n - 4) p' hP hcls) hres
  · -- `F_none`: no prime divisor of `V(F')` has the class of `z`.
    intro x hx1 hxmem hres
    haveI hxprime : x.asIdeal.IsPrime := x.isPrime
    obtain ⟨hp1, hp2⟩ := Work.MotA.height_comap_renameCastAdd 𝕜 4 (n - 4) F' hF'ne x.asIdeal
      x.isPrime (by rw [AlgebraicGeometry.idealHeight_eq_coheight]; exact hx1) hxmem
    set p' : Ideal (MvPolynomial (Fin 4) 𝕜) :=
      Ideal.comap (MvPolynomial.rename (Fin.castAdd (n - 4))) x.asIdeal with hp'
    haveI hp'prime : p'.IsPrime := Ideal.comap_isPrime _ _
    have hF'p : F' ∈ p' := by
      rw [hp']
      exact Ideal.mem_comap.mpr hxmem
    have hP : x.asIdeal = p'.map (MvPolynomial.rename (Fin.castAdd (n - 4))) := by
      rw [hp']
      exact hp2.symm
    rcases Work.MotV5.census_F_alt (𝕜 := 𝕜) L F' cF hcF hF'eq p' hp1 hF'p with
      hcls₂ | ⟨F₀, hF₀, hA₀, hnc, hcls⟩
    · -- the `F₂`-class differs from the class of `z` by `hR`
      exact not_resEquiv_of_class_stab_F₂ (𝕜 := 𝕜) (k := n - 4) hCO hR hzclass
        (class_stab_of_class_map (k := n - 4) p' hP hcls₂) hres
    · -- junk class
      exact not_resEquiv_of_class_stab (𝕜 := 𝕜) (k := n - 4) hCO hnc hzclass
        (class_stab_of_class_map (k := n - 4) p' hP hcls) hres

end Work.MotV
