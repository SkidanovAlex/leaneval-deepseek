import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.spreadMap_injective
import Submission.Work.MotA.exists_denom
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.MotA

open MvPolynomial

/-- **One-sided spreading out.**  Let `Φ : K[x]_{(F)} ≃ₐ[K] K[x]_{(G)}` be a `K`-algebra isomorphism,
`K = RatFunc 𝕜`, and let `F₀ ∈ 𝕜[t,x]` (resp. `G₀`) be the numerator of `F` (resp. `G`) with
respect to `𝕜[t]`, so that `spreadMap 𝕜 n F₀ = C cF0 * F`.  Fix a `t`-polynomial `h ≠ 0` and put
`F' = F₀ * tPoly h`, `G' = G₀ * tPoly h`.

If a family `y j ∈ K[x]_{(G)}` (each lying in the image of `𝕜[t,x]_{G'} → K[x]_{(G)}` for the common
denominator `h`) consists of the images under `Φ` of the generators of `𝕜[t,x]`, and if `yF = Φ (F)`
is accompanied by an inverse `yF'`, then there is a `𝕜`-algebra map
`𝕜[t,x]_{F'} →ₐ[𝕜] 𝕜[t,x]_{G'}` whose composite with `𝕜[t,x]_{G'} → K[x]_{(G)}` agrees with `Φ` on
`𝕜[t,x]`.  Together with the canonical lift `𝕜[t,x]_{G'} → K[x]_{(G)}` this is the "restriction" of
`Φ` to the spread-out localisations. -/
theorem exists_spread_awayMap (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) (RatFunc 𝕜)) (hG : G ≠ 0)
    (Φ : Localization.Away F ≃ₐ[RatFunc 𝕜] Localization.Away G)
    (F₀ G₀ : MvPolynomial (Fin (n + 1)) 𝕜) (cF0 cG0 : Polynomial 𝕜)
    (hF₀ : spreadMap 𝕜 n F₀ = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF0) * F)
    (hG₀ : spreadMap 𝕜 n G₀ = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG0) * G)
    (h : Polynomial 𝕜) (hh : h ≠ 0)
    (F' G' : MvPolynomial (Fin (n + 1)) 𝕜)
    (hF' : F' = F₀ * tPoly 𝕜 n h) (hG' : G' = G₀ * tPoly 𝕜 n h) (hG'ne : G' ≠ 0)
    (hunit : IsUnit (awayMap 𝕜 n G G')) (hcF0dvd : cF0 ∣ h)
    (y : Fin (n + 1) → Localization.Away G) (d : Fin (n + 1) → Polynomial 𝕜)
    (hden : ∀ j, ∀ h' : Polynomial 𝕜, d j ∣ h' →
      ∃ M b, y j * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h')) ^ M = awayMap 𝕜 n G b)
    (hdvd : ∀ j, d j ∣ h)
    (hy : ∀ j, y j = Φ (awayMap 𝕜 n F (MvPolynomial.X j)))
    (yF : Localization.Away G) (dF : Polynomial 𝕜)
    (hdenF : ∀ h' : Polynomial 𝕜, dF ∣ h' →
      ∃ M b, yF * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h')) ^ M = awayMap 𝕜 n G b)
    (hdvdF : dF ∣ h) (hyF : yF = Φ (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜))
      (Localization.Away F) F))
    (yF' : Localization.Away G) (dF' : Polynomial 𝕜)
    (hdenF' : ∀ h' : Polynomial 𝕜, dF' ∣ h' →
      ∃ M b, yF' * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h')) ^ M = awayMap 𝕜 n G b)
    (hdvdF' : dF' ∣ h) (hyF'mul : yF * yF' = 1) :
    ∃ (fbar : Localization.Away G' →ₐ[𝕜] Localization.Away G)
      (ψ : Localization.Away F' →ₐ[𝕜] Localization.Away G'),
      (∀ x : MvPolynomial (Fin (n + 1)) 𝕜,
          fbar (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') x)
            = awayMap 𝕜 n G x) ∧
      Function.Injective fbar ∧
      (∀ x : MvPolynomial (Fin (n + 1)) 𝕜,
          fbar (ψ (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away F') x))
            = Φ (awayMap 𝕜 n F x)) := by
  have hinjG : Function.Injective (awayMap 𝕜 n G) := by
    have hle : Submonoid.powers G ≤ nonZeroDivisors (MvPolynomial (Fin n) (RatFunc 𝕜)) := by
      intro m hm
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff m G).mp hm
      rw [← hk]
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero k hG)
    intro x y hxy
    exact spreadMap_injective 𝕜 n (IsLocalization.injective (Localization.Away G) hle hxy)
  have hunitT : ∀ v : Submonoid.powers G', IsUnit (awayMap 𝕜 n G ↑v) := by
    intro v
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff ↑v G').mp v.2
    rw [← hk]
    simpa using hunit.pow k
  let fbar : Localization.Away G' →ₐ[𝕜] Localization.Away G :=
    IsLocalization.liftAlgHom (f := awayMap 𝕜 n G) hunitT
  have hfbar : ∀ x : MvPolynomial (Fin (n + 1)) 𝕜,
      fbar (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') x)
        = awayMap 𝕜 n G x := fun x => IsLocalization.lift_eq hunitT x
  haveI : IsDomain (Localization.Away G') := Localization.Away.isDomain hG'ne
  have hfbar_inj : Function.Injective fbar := by
    have hle : Submonoid.powers G' ≤ nonZeroDivisors (MvPolynomial (Fin (n + 1)) 𝕜) := by
      intro m hm
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff m G').mp hm
      rw [← hk]
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero k hG'ne)
    have halg : Function.Injective
        (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')) :=
      IsLocalization.injective (Localization.Away G') hle
    intro x y hxy
    have h0 : fbar (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzy : x - y = 0 := by
      obtain ⟨⟨r, m⟩, hsurj⟩ := IsLocalization.surj (Submonoid.powers G') (x - y)
      have h1 : awayMap 𝕜 n G r = 0 := by
        have h := congrArg fbar hsurj
        rw [map_mul, h0, zero_mul, hfbar] at h
        exact h.symm
      have hr : r = 0 := hinjG (h1.trans (map_zero _).symm)
      have hm0 : ((m : MvPolynomial (Fin (n + 1)) 𝕜)) ≠ 0 := by
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (m : MvPolynomial (Fin (n+1)) 𝕜) G').mp m.2
        rw [← hk]
        exact pow_ne_zero k hG'ne
      have h2 : (x - y) * algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')
          (m : MvPolynomial (Fin (n + 1)) 𝕜) = 0 := by rw [hsurj, hr, map_zero]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (halg (by rw [h3, map_zero])) hm0
    exact sub_eq_zero.mp hzy
  let uT : (Localization.Away G')ˣ :=
    (isUnit_algebraMap_self (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') G').unit
  have huT : (↑uT : Localization.Away G') = algebraMap (MvPolynomial (Fin (n + 1)) 𝕜)
      (Localization.Away G') G' := IsUnit.unit_spec _
  have hpre : ∀ v : Localization.Away G,
      (∃ M b, v * (awayMap 𝕜 n G G') ^ M = awayMap 𝕜 n G b) →
      ∃ w : Localization.Away G', fbar w = v := by
    intro v hdata
    obtain ⟨M, b, hMb⟩ := hdata
    refine ⟨(algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') b)
      * (↑(uT⁻¹)) ^ M, ?_⟩
    have h2 : fbar (↑(uT⁻¹)) * awayMap 𝕜 n G G' = 1 := by
      have h3 : (↑(uT⁻¹) : Localization.Away G') * ↑uT = 1 := Units.inv_mul uT
      have h4 := congrArg fbar h3
      rw [map_mul, map_one, huT, hfbar] at h4
      exact h4
    have h2' : awayMap 𝕜 n G G' * fbar (↑(uT⁻¹)) = 1 := by rw [mul_comm, h2]
    have h3 : (awayMap 𝕜 n G G') ^ M * (fbar (↑(uT⁻¹))) ^ M = 1 := by
      rw [← mul_pow, h2', one_pow]
    rw [map_mul, map_pow, hfbar]
    rw [← hMb, mul_assoc, h3, mul_one]
  have hprej : ∀ j : Fin (n + 1), ∃ w : Localization.Away G', fbar w = y j :=
    fun j => hpre (y j) (by rw [hG']; exact hden j h (hdvd j))
  let wj : Fin (n + 1) → Localization.Away G' := fun j => Classical.choose (hprej j)
  have hwj : ∀ j, fbar (wj j) = y j := fun j => Classical.choose_spec (hprej j)
  let g : MvPolynomial (Fin (n + 1)) 𝕜 →ₐ[𝕜] Localization.Away G' := MvPolynomial.aeval wj
  have hg : fbar.comp g = (Φ.restrictScalars 𝕜).toAlgHom.comp (awayMap 𝕜 n F) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X]
    have hcoe : (Φ.restrictScalars 𝕜).toAlgHom (awayMap 𝕜 n F (MvPolynomial.X j))
        = Φ (awayMap 𝕜 n F (MvPolynomial.X j)) := rfl
    rw [hcoe, ← hy j]
    exact hwj j
  have hpreF : ∃ w : Localization.Away G', fbar w = yF :=
    hpre yF (by rw [hG']; exact hdenF h hdvdF)
  let wF : Localization.Away G' := Classical.choose hpreF
  have hwF : fbar wF = yF := Classical.choose_spec hpreF
  have hpreF' : ∃ w : Localization.Away G', fbar w = yF' :=
    hpre yF' (by rw [hG']; exact hdenF' h hdvdF')
  let wF' : Localization.Away G' := Classical.choose hpreF'
  have hwF' : fbar wF' = yF' := Classical.choose_spec hpreF'
  have hwF_unit : IsUnit wF := by
    refine ⟨Units.mkOfMulEqOne wF wF' ?_, rfl⟩
    apply hfbar_inj
    rw [map_mul, hwF, hwF', map_one]
    exact hyF'mul
  have hgX0 : g (MvPolynomial.X 0)
      = algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') (MvPolynomial.X 0) := by
    apply hfbar_inj
    have hh0 := congrFun (congrArg DFunLike.coe hg) (MvPolynomial.X 0)
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at hh0
    have hh0' : fbar (g (MvPolynomial.X 0)) = Φ (awayMap 𝕜 n F (MvPolynomial.X 0)) := hh0
    rw [hh0', hfbar]
    have h1 : awayMap 𝕜 n F (MvPolynomial.X 0)
        = algebraMap (RatFunc 𝕜) (Localization.Away F) RatFunc.X := by
      rw [← tPoly_X 𝕜 n, awayMap_tPoly, RatFunc.algebraMap_X]
    have h2 : awayMap 𝕜 n G (MvPolynomial.X 0)
        = algebraMap (RatFunc 𝕜) (Localization.Away G) RatFunc.X := by
      rw [← tPoly_X 𝕜 n, awayMap_tPoly, RatFunc.algebraMap_X]
    rw [h1, h2, Φ.commutes]
  have hgtPoly : ∀ c : Polynomial 𝕜, g (tPoly 𝕜 n c)
      = algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') (tPoly 𝕜 n c) := by
    have h1 : (g.comp (tPoly 𝕜 n)) =
        (IsScalarTower.toAlgHom 𝕜 (MvPolynomial (Fin (n + 1)) 𝕜)
          (Localization.Away G')).comp (tPoly 𝕜 n) := by
      apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, AlgHom.comp_apply, tPoly_X, IsScalarTower.toAlgHom_apply]
      exact hgX0
    intro c
    have h2 := congrFun (congrArg DFunLike.coe h1) c
    rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] at h2
    exact h2
  have hC := C_eq_algebraMap_apply 𝕜 n cF0
  have hgF0 : g F₀ = algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')
      (tPoly 𝕜 n cF0) * wF := by
    apply hfbar_inj
    have hl : fbar (g F₀) = awayMap 𝕜 n G (tPoly 𝕜 n cF0) * yF := by
      have h := congrFun (congrArg DFunLike.coe hg) F₀
      rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
      have h' : fbar (g F₀) = Φ (awayMap 𝕜 n F F₀) := h
      have hsp : awayMap 𝕜 n F F₀ =
          algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away F)
            (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF0))
          * algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away F) F := by
        rw [awayMap_apply, hF₀, map_mul]
      have h1 : Φ (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away F)
          (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF0)))
          = awayMap 𝕜 n G (tPoly 𝕜 n cF0) := by
        rw [hC, ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (MvPolynomial (Fin n) (RatFunc 𝕜))
          (Localization.Away F) (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF0), Φ.commutes,
          ← awayMap_tPoly]
      have h2 : Φ (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜))
          (Localization.Away F) F) = yF := hyF.symm
      rw [h', hsp, map_mul, h1, h2]
    have hr : fbar (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')
        (tPoly 𝕜 n cF0) * wF) = awayMap 𝕜 n G (tPoly 𝕜 n cF0) * yF := by
      rw [map_mul, hfbar, hwF]
    exact hl.trans hr.symm
  have hunit_cF0 : IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')
      (tPoly 𝕜 n cF0)) := by
    rw [IsLocalization.algebraMap_isUnit_iff (Submonoid.powers G') (x := tPoly 𝕜 n cF0)]
    refine ⟨G', self_mem_powers G', ?_⟩
    exact (map_dvd (tPoly 𝕜 n) hcF0dvd).trans (by rw [hG']; exact dvd_mul_left _ _)
  have hunit_tCh : IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G')
      (tPoly 𝕜 n h)) := by
    rw [IsLocalization.algebraMap_isUnit_iff (Submonoid.powers G') (x := tPoly 𝕜 n h)]
    refine ⟨G', self_mem_powers G', ?_⟩
    rw [hG']
    exact dvd_mul_left _ _
  have hgF'_unit : IsUnit (g F') := by
    have h1 : g F' = g F₀ * g (tPoly 𝕜 n h) := by
      rw [hF', map_mul]
    rw [h1, hgF0, hgtPoly]
    exact (hunit_cF0.mul hwF_unit).mul hunit_tCh
  have hunit_g : ∀ v : Submonoid.powers F', IsUnit (g ↑v) := by
    intro v
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff ↑v F').mp v.2
    rw [← hk]
    simpa using hgF'_unit.pow k
  let ψ : Localization.Away F' →ₐ[𝕜] Localization.Away G' := IsLocalization.liftAlgHom (f := g) hunit_g
  have hres : ∀ x : MvPolynomial (Fin (n + 1)) 𝕜,
      fbar (ψ (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away F') x))
        = Φ (awayMap 𝕜 n F x) := by
    intro x
    have h1 : ψ (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away F') x) = g x := by
      rw [show ψ = IsLocalization.liftAlgHom (f := g) hunit_g from rfl,
        IsLocalization.liftAlgHom_apply]
      exact IsLocalization.lift_eq hunit_g x
    have h2 : fbar (g x) = Φ (awayMap 𝕜 n F x) := congrFun (congrArg DFunLike.coe hg) x
    rw [h1, h2]
  exact ⟨fbar, ψ, hfbar, hfbar_inj, hres⟩

/-- **`S1`, spreading out.**  Let `K = RatFunc 𝕜`, let `F`, `G ∈ K[x₁,…,xₙ]` be nonzero and let
`Φ : Localization.Away F ≃ₐ[K] Localization.Away G`.  Then `Φ` is the generic fibre of an
isomorphism of localisations over `𝕜`: there are nonzero `cF`, `cG ∈ 𝕜[t]` and nonzero
`F'`, `G' ∈ 𝕜[t,x₁,…,xₙ] = MvPolynomial (Fin (n+1)) 𝕜` with
`Work.MotA.spreadMap 𝕜 n F' = C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) * F` (and likewise for
`G'`, `G`, `cG`) and a `𝕜`-algebra isomorphism
`Localization.Away F' ≃ₐ[𝕜] Localization.Away G'`.

The equation `spreadMap 𝕜 n F' = C cF * F` is what makes the statement usable for the census: it
says that `F'` is obtained from `F ∈ K[x]` by clearing the denominators in `t` and multiplying by
the `t`-polynomial `cF`, so the prime factors of `F'` in the UFD `𝕜[t,x]` are the prime factors of
`F` over `K` together with the irreducible factors of `cF` in `𝕜[t]` (the "vertical" primes).

Route.  Write `B = MvPolynomial (Fin (n+1)) 𝕜 = 𝕜[t,x₁,…,xₙ]`, `A = MvPolynomial (Fin n) K`,
`f := Work.MotA.spreadMap 𝕜 n : B →ₐ[𝕜] A` (injective — prove
`Work.MotA.spreadMap_injective` as a helper in the same file, as the census needs it), so that `f`'s
image is the subring of `A` of polynomials whose coefficients lie in `𝕜[t]`, and `A` is generated
over `f(B)` by inverting `t` (since `K = 𝕜(t)`).

1. *Clearing denominators for `F`.*  Every element of `A` is a finite sum `Σ_μ F_μ(t)·x^μ` with
   `F_μ ∈ K`; a common multiple `cF ∈ 𝕜[t]` of the denominators of the finitely many `F_μ` gives
   `cF·F ∈ f(B)`, say `cF·F = f(F')` with `F' ∈ B` (unique by injectivity of `f`), nonzero since
   `A` is a domain.  Do the same for `G`.  Also record the helper `f (Polynomial-aeval-into-B c) =
   C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) c)`, i.e. `f` of the polynomial `c(t) ∈ B` is `C c`
   (`Work.MotA.spreadMap_C` for constants, plus `Polynomial.aeval`).
2. *Restriction of `Φ`.*  `Φ` is `K`-linear, so it fixes `K` and hence every `t`-polynomial, and
   `Φ(x_i) ∈ A_{(G)}` can be written with a common denominator.  Multiplying `cF`, `cG` (and
   correspondingly `F'`, `G'`) by further `t`-polynomials — note `f(F'·(c(t))) = f(F')·C c`, so the
   relation `f(F') = C cF·F` is preserved when `cF` and `F'` are both multiplied by the same
   `t`-polynomial — we may arrange that the image under `Φ` of each generator `t, x₁,…,xₙ` of
   `B_{F'}` lies in `B_{G'}` (i.e. clears the `t`-denominators of the numerators and inverts `F'` by
   making `G'` a multiple of the numerator of `Φ(F')`).  Then `Φ` restricts to a `𝕜`-algebra map
   `B_{F'} → B_{G'}` (the universal property of `IsLocalization.Away` applied to the composite
   `B → A → A_{(G)}`, once `G'` maps to a unit).  Applying the same to `Φ⁻¹` and multiplying the two
   choices of `F'` and of `G'` gives a two-sided inverse, hence an isomorphism.

Both `cF`, `cG` and `F'`, `G'` are allowed to be large: the statement is existential and the extra
vertical factors are harmless.  Also useful for the census (and provable here): `f` is injective,
`f` preserves the `𝕜[t]`-constants, and `t` is transcendental over `𝕜` inside `B` (so `B` is a UFD
and `cF ≠ 0` makes `F' ≠ 0`). -/
theorem exists_spread_awayAlgEquiv (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) (RatFunc 𝕜)) (hF : F ≠ 0) (hG : G ≠ 0)
    (Φ : Localization.Away F ≃ₐ[RatFunc 𝕜] Localization.Away G) :
    ∃ (cF cG : Polynomial 𝕜) (_ : cF ≠ 0) (_ : cG ≠ 0)
      (F' G' : MvPolynomial (Fin (n + 1)) 𝕜) (_ : F' ≠ 0) (_ : G' ≠ 0),
      Work.MotA.spreadMap 𝕜 n F'
          = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) * F ∧
      Work.MotA.spreadMap 𝕜 n G'
          = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG) * G ∧
      Nonempty (Localization.Away F' ≃ₐ[𝕜] Localization.Away G') := by
  -- ## 0. Clearing denominators
  obtain ⟨cF0, hcF0, F₀, hF₀⟩ := exists_clearing 𝕜 n F
  obtain ⟨cG0, hcG0, G₀, hG₀⟩ := exists_clearing 𝕜 n G
  have hF₀ne : F₀ ≠ 0 := by
    intro h
    have h1 : spreadMap 𝕜 n F₀ = 0 := by rw [h, map_zero]
    rw [hF₀] at h1
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (algebraMap_ne_zero hcF0)) hF h1
  have hG₀ne : G₀ ≠ 0 := by
    intro h
    have h1 : spreadMap 𝕜 n G₀ = 0 := by rw [h, map_zero]
    rw [hG₀] at h1
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (algebraMap_ne_zero hcG0)) hG h1
  -- ## 1. the elements whose denominators have to be cleared
  let yG : Fin (n + 1) → Localization.Away G :=
    fun j => Φ (awayMap 𝕜 n F (MvPolynomial.X j))
  let yGF : Localization.Away G := Φ (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜))
    (Localization.Away F) F)
  have hunitF : IsUnit (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away F) F) :=
    IsLocalization.map_units (Localization.Away F) ⟨F, self_mem_powers F⟩
  have hunitGF : IsUnit yGF := hunitF.map Φ
  let yGF' : Localization.Away G := ↑hunitGF.unit⁻¹
  let yF : Fin (n + 1) → Localization.Away F :=
    fun j => Φ.symm (awayMap 𝕜 n G (MvPolynomial.X j))
  let yFG : Localization.Away F := Φ.symm (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜))
    (Localization.Away G) G)
  have hunitG : IsUnit (algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G) G) :=
    IsLocalization.map_units (Localization.Away G) ⟨G, self_mem_powers G⟩
  have hunitFG : IsUnit yFG := hunitG.map Φ.symm
  let yFG' : Localization.Away F := ↑hunitFG.unit⁻¹
  -- ## 2. the denominators
  let dG : Fin (n + 1) → Polynomial 𝕜 :=
    fun j => Classical.choose (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ (yG j))
  have hdG : ∀ j, dG j ≠ 0 ∧ ∀ h : Polynomial 𝕜, dG j ∣ h →
      ∃ M b, yG j * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n G b :=
    fun j => Classical.choose_spec (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ (yG j))
  let dGF : Polynomial 𝕜 := Classical.choose (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ yGF)
  have hdGF : dGF ≠ 0 ∧ ∀ h : Polynomial 𝕜, dGF ∣ h →
      ∃ M b, yGF * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n G b :=
    Classical.choose_spec (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ yGF)
  let dGF' : Polynomial 𝕜 := Classical.choose (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ yGF')
  have hdGF' : dGF' ≠ 0 ∧ ∀ h : Polynomial 𝕜, dGF' ∣ h →
      ∃ M b, yGF' * (awayMap 𝕜 n G (G₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n G b :=
    Classical.choose_spec (exists_denom 𝕜 n G G₀ cG0 hcG0 hG₀ yGF')
  let dF : Fin (n + 1) → Polynomial 𝕜 :=
    fun j => Classical.choose (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ (yF j))
  have hdF : ∀ j, dF j ≠ 0 ∧ ∀ h : Polynomial 𝕜, dF j ∣ h →
      ∃ M b, yF j * (awayMap 𝕜 n F (F₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n F b :=
    fun j => Classical.choose_spec (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ (yF j))
  let dFG : Polynomial 𝕜 := Classical.choose (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ yFG)
  have hdFG : dFG ≠ 0 ∧ ∀ h : Polynomial 𝕜, dFG ∣ h →
      ∃ M b, yFG * (awayMap 𝕜 n F (F₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n F b :=
    Classical.choose_spec (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ yFG)
  let dFG' : Polynomial 𝕜 := Classical.choose (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ yFG')
  have hdFG' : dFG' ≠ 0 ∧ ∀ h : Polynomial 𝕜, dFG' ∣ h →
      ∃ M b, yFG' * (awayMap 𝕜 n F (F₀ * tPoly 𝕜 n h)) ^ M = awayMap 𝕜 n F b :=
    Classical.choose_spec (exists_denom 𝕜 n F F₀ cF0 hcF0 hF₀ yFG')
  -- ## 3. the common denominator, and the polynomials
  let h : Polynomial 𝕜 :=
    cF0 * cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dGF' * dFG * dFG'
  have hprodG : (∏ j, dG j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _; exact (hdG j).1
  have hprodF : (∏ j, dF j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro j _; exact (hdF j).1
  have hh : h ≠ 0 := by
    simp only [h]
    repeat' apply mul_ne_zero
    · exact hcF0
    · exact hcG0
    · exact hprodG
    · exact hprodF
    · exact hdGF.1
    · exact hdGF'.1
    · exact hdFG.1
    · exact hdFG'.1
  let F' : MvPolynomial (Fin (n + 1)) 𝕜 := F₀ * tPoly 𝕜 n h
  let G' : MvPolynomial (Fin (n + 1)) 𝕜 := G₀ * tPoly 𝕜 n h
  let cF : Polynomial 𝕜 := cF0 * h
  let cG : Polynomial 𝕜 := cG0 * h
  have hcF : cF ≠ 0 := mul_ne_zero hcF0 hh
  have hcG : cG ≠ 0 := mul_ne_zero hcG0 hh
  have keyF : (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cF0 * h)) :
      MvPolynomial (Fin n) (RatFunc 𝕜)) =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF0) *
        MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) h) := by
    rw [map_mul, MvPolynomial.C_mul]
  have keyG : (MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * h)) :
      MvPolynomial (Fin n) (RatFunc 𝕜)) =
      MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG0) *
        MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) h) := by
    rw [map_mul, MvPolynomial.C_mul]
  have hF'eq : spreadMap 𝕜 n F' = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cF) * F := by
    simp only [F', cF]
    rw [map_mul (spreadMap 𝕜 n), hF₀, spreadMap_tPoly, keyF]
    first | refl_ring1 | ring
  have hG'eq : spreadMap 𝕜 n G' = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) cG) * G := by
    simp only [G', cG]
    rw [map_mul (spreadMap 𝕜 n), hG₀, spreadMap_tPoly, keyG]
    first | refl_ring1 | ring
  have hF'ne : F' ≠ 0 := by
    intro h0
    have h1 : spreadMap 𝕜 n F' = 0 := by rw [h0, map_zero]
    rw [hF'eq] at h1
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (algebraMap_ne_zero hcF)) hF h1
  have hG'ne : G' ≠ 0 := by
    intro h0
    have h1 : spreadMap 𝕜 n G' = 0 := by rw [h0, map_zero]
    rw [hG'eq] at h1
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (algebraMap_ne_zero hcG)) hG h1
  -- ## 4. each chosen denominator divides the common one
  have hdG_dvd : ∀ j, dG j ∣ h := by
    intro j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j => dG j) (Finset.mem_univ j)
    refine ⟨cF0 * cG0 * q * (∏ j, dF j) * dGF * dGF' * dFG * dFG', ?_⟩
    simp only [h, hq]; ring
  have hdF_dvd : ∀ j, dF j ∣ h := by
    intro j
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j => dF j) (Finset.mem_univ j)
    refine ⟨cF0 * cG0 * (∏ j, dG j) * q * dGF * dGF' * dFG * dFG', ?_⟩
    simp only [h, hq]; ring
  have hdGF_dvd : dGF ∣ h := by
    refine ⟨cF0 * cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF' * dFG * dFG', ?_⟩
    simp only [h]; ring
  have hdGF'_dvd : dGF' ∣ h := by
    refine ⟨cF0 * cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dFG * dFG', ?_⟩
    simp only [h]; ring
  have hdFG_dvd : dFG ∣ h := by
    refine ⟨cF0 * cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dGF' * dFG', ?_⟩
    simp only [h]; ring
  have hdFG'_dvd : dFG' ∣ h := by
    refine ⟨cF0 * cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dGF' * dFG, ?_⟩
    simp only [h]; ring
  -- ## 5. the isomorphism of the two localisations
  have hcF0_dvd_h : cF0 ∣ h := by
    refine ⟨cG0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dGF' * dFG * dFG', ?_⟩
    simp only [h]; ring
  have hcG0_dvd_h : cG0 ∣ h := by
    refine ⟨cF0 * (∏ j, dG j) * (∏ j, dF j) * dGF * dGF' * dFG * dFG', ?_⟩
    simp only [h]; ring
  have hspreadG' : spreadMap 𝕜 n G'
      = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cG0 * h)) * G := by
    simp only [G']
    rw [map_mul (spreadMap 𝕜 n), hG₀, spreadMap_tPoly, keyG]
    first | refl_ring1 | ring
  have hspreadF' : spreadMap 𝕜 n F'
      = MvPolynomial.C (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) (cF0 * h)) * F := by
    simp only [F']
    rw [map_mul (spreadMap 𝕜 n), hF₀, spreadMap_tPoly, keyF]
    first | refl_ring1 | ring
  have hunitG'_AG : IsUnit (awayMap 𝕜 n G G') := by
    rw [show awayMap 𝕜 n G G' = algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away G)
      (spreadMap 𝕜 n G') from rfl, hspreadG', map_mul]
    exact (isUnit_algebraMap_C_away 𝕜 n G (cG0 * h) (mul_ne_zero hcG0 hh)).mul
      (isUnit_algebraMap_self _ _ G)
  have hunitF'_AF : IsUnit (awayMap 𝕜 n F F') := by
    rw [show awayMap 𝕜 n F F' = algebraMap (MvPolynomial (Fin n) (RatFunc 𝕜)) (Localization.Away F)
      (spreadMap 𝕜 n F') from rfl, hspreadF', map_mul]
    exact (isUnit_algebraMap_C_away 𝕜 n F (cF0 * h) (mul_ne_zero hcF0 hh)).mul
      (isUnit_algebraMap_self _ _ F)
  have hwGF_mul : yGF * yGF' = 1 := IsUnit.mul_val_inv hunitGF
  have hwFG_mul : yFG * yFG' = 1 := IsUnit.mul_val_inv hunitFG
  obtain ⟨fTbar, ψ, hfTbar, hfTbar_inj, hresT⟩ :=
    exists_spread_awayMap 𝕜 n F G hG Φ F₀ G₀ cF0 cG0 hF₀ hG₀ h hh F' G' rfl rfl hG'ne
      hunitG'_AG hcF0_dvd_h yG dG (fun j h' hd => (hdG j).2 h' hd) hdG_dvd (fun j => rfl)
      yGF dGF (fun h' hd => hdGF.2 h' hd) hdGF_dvd rfl yGF' dGF'
      (fun h' hd => hdGF'.2 h' hd) hdGF'_dvd hwGF_mul
  obtain ⟨fSbar, ψ', hfSbar, hfSbar_inj, hresF⟩ :=
    exists_spread_awayMap 𝕜 n G F hF Φ.symm G₀ F₀ cG0 cF0 hG₀ hF₀ h hh G' F' rfl rfl hF'ne
      hunitF'_AF hcG0_dvd_h yF dF (fun j h' hd => (hdF j).2 h' hd) hdF_dvd (fun j => rfl)
      yFG dFG (fun h' hd => hdFG.2 h' hd) hdFG_dvd rfl yFG' dFG'
      (fun h' hd => hdFG'.2 h' hd) hdFG'_dvd hwFG_mul
  have hcomp1 : fTbar.comp ψ = (Φ.restrictScalars 𝕜).toAlgHom.comp fSbar := by
    have key : ∀ b : MvPolynomial (Fin (n + 1)) 𝕜,
        (fTbar.comp ψ) (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away F') b)
          = ((Φ.restrictScalars 𝕜).toAlgHom.comp fSbar) (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜)
              (Localization.Away F') b) := by
      intro b
      change fTbar (ψ (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away F') b))
        = (Φ.restrictScalars 𝕜).toAlgHom (fSbar (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜)
            (Localization.Away F') b))
      rw [hresT b, hfSbar b]
      rfl
    have key2 : (fTbar.comp ψ).toRingHom = ((Φ.restrictScalars 𝕜).toAlgHom.comp fSbar).toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers F')
      exact RingHom.ext fun b => key b
    exact AlgHom.ext fun x => congrFun (congrArg DFunLike.coe key2) x
  have hcomp2 : fSbar.comp ψ' = ((Φ.restrictScalars 𝕜).symm).toAlgHom.comp fTbar := by
    have key : ∀ b : MvPolynomial (Fin (n + 1)) 𝕜,
        (fSbar.comp ψ') (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') b)
          = (((Φ.restrictScalars 𝕜).symm).toAlgHom.comp fTbar) (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜)
              (Localization.Away G') b) := by
      intro b
      change fSbar (ψ' (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜) (Localization.Away G') b))
        = ((Φ.restrictScalars 𝕜).symm).toAlgHom (fTbar (algebraMap (MvPolynomial (Fin (n + 1)) 𝕜)
            (Localization.Away G') b))
      rw [hresF b, hfTbar b]
      rfl
    have key2 : (fSbar.comp ψ').toRingHom = (((Φ.restrictScalars 𝕜).symm).toAlgHom.comp fTbar).toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers G')
      exact RingHom.ext fun b => key b
    exact AlgHom.ext fun x => congrFun (congrArg DFunLike.coe key2) x
  have hψψ' : ψ.comp ψ' = AlgHom.id 𝕜 (Localization.Away G') := by
    apply AlgHom.ext
    intro x
    apply hfTbar_inj
    have h1 : fTbar (ψ (ψ' x)) = Φ (fSbar (ψ' x)) := by
      show (fTbar.comp ψ) (ψ' x) = Φ (fSbar (ψ' x))
      rw [hcomp1]; rfl
    have h2 : fSbar (ψ' x) = (Φ.restrictScalars 𝕜).symm (fTbar x) := by
      show (fSbar.comp ψ') x = (Φ.restrictScalars 𝕜).symm (fTbar x)
      rw [hcomp2]; rfl
    show fTbar (ψ (ψ' x)) = fTbar x
    rw [h1, h2]
    exact (Φ.restrictScalars 𝕜).apply_symm_apply (fTbar x)
  have hψ'ψ : ψ'.comp ψ = AlgHom.id 𝕜 (Localization.Away F') := by
    apply AlgHom.ext
    intro x
    apply hfSbar_inj
    have h1 : fSbar (ψ' (ψ x)) = (Φ.restrictScalars 𝕜).symm (fTbar (ψ x)) := by
      show (fSbar.comp ψ') (ψ x) = (Φ.restrictScalars 𝕜).symm (fTbar (ψ x))
      rw [hcomp2]; rfl
    have h2 : fTbar (ψ x) = Φ (fSbar x) := by
      show (fTbar.comp ψ) x = Φ (fSbar x)
      rw [hcomp1]; rfl
    show fSbar (ψ' (ψ x)) = fSbar x
    rw [h1, h2]
    exact (Φ.restrictScalars 𝕜).symm_apply_apply (fSbar x)
  exact ⟨cF, cG, hcF, hcG, F', G', hF'ne, hG'ne, hF'eq, hG'eq,
    ⟨AlgEquiv.ofAlgHom ψ ψ' hψψ' hψ'ψ⟩⟩


end Work.MotA
