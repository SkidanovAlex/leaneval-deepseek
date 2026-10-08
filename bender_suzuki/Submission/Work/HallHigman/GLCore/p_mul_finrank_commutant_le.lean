import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.fourier_finrank
import Submission.Work.HallHigman.GLCore.orbit_transversal_card
import Submission.Work.HallHigman.GLCore.finrank_ker_monomial_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1200000

namespace Work.HallHigman.GLCore

open Finset

universe u v w

/-! ## Auxiliary lemmas for L9 of the GL-core design

The proof of `p_mul_finrank_commutant_le` proceeds as follows.

* Under the hypotheses of the Fourier lemma the action `σ` is *injective*: if `σ a = 1` then
  `σ ([a,f]) = 1` for all `f`, but `[a,f]` is central and the central character is injective,
  so `a` is central and `a = 1`.
* Hence `σ (α ^ p e) = X ^ p σ e X ^ (-p) = σ e` forces `α ^ p = 1`, and therefore the
  permutation `π` induced by `α` on `E ⧸ Z(E)` has order dividing `p`, with `Z(E)` as its only
  fixed point.
* Conjugation by `X` becomes, under the Fourier isomorphism `Θ` (L8), a monomial operator on
  the coordinates `E ⧸ Z(E) → End_E(V)`: it permutes the coordinates along the `π`-orbits and
  multiplies by scalars.  A fixed point is determined by its coordinates on one representative
  per orbit, and since there is exactly one trivial orbit and every other orbit has `p` elements,
  `p · dim C(X) ≤ (p + |E ⧸ Z(E)| - 1) · dim End_E(V)`. -/

/-- Conjugation by a unit is multiplicative (in a monoid). -/
private theorem unit_conj_mul {R : Type*} [Monoid R] (u : Rˣ) (x y : R) :
    ((↑u : R) * x * ↑u⁻¹) * ((↑u) * y * ↑u⁻¹) = (↑u) * (x * y) * ↑u⁻¹ := by
  have h : (↑u⁻¹ : R) * ↑u = 1 := by simp
  rw [show ((↑u : R) * x * ↑u⁻¹) * ((↑u) * y * ↑u⁻¹)
      = (↑u) * x * ((↑u⁻¹ * ↑u) * (y * ↑u⁻¹)) from by simp only [mul_assoc]]
  rw [h, one_mul]
  simp only [mul_assoc]

/-- **The action `σ` is injective.**  If `σ a = 1` then every commutator `[a,f]` is central and
dies under `σ`, hence is trivial by injectivity of the central character; so `a` is central and
`a = 1`. -/
private theorem injective_of_center_faithful {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {E : Type*} [Group E] (σ : E →* Module.End K V)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E) :
    Function.Injective σ := by
  have hker : ∀ x : E, σ x = 1 → x = 1 := by
    intro x hx
    have hxinv : σ x⁻¹ = 1 := by
      have h : σ x⁻¹ * σ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [hx, mul_one] at h
    have hcomm1 : ∀ f : E, x * f * x⁻¹ * f⁻¹ = 1 := by
      intro f
      refine hfaith _ (hcomm x f) ?_
      rw [map_mul, map_mul, map_mul, hx, hxinv, one_mul, mul_one, ← map_mul, mul_inv_cancel,
        map_one]
    have hcen : x ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro f
      have h := hcomm1 f
      have h' : x * f * x⁻¹ = f := by
        calc x * f * x⁻¹ = (x * f * x⁻¹ * f⁻¹) * f := by group
          _ = 1 * f := by rw [h]
          _ = f := one_mul f
      have h2 : x * f = f * x := by
        calc x * f = (x * f * x⁻¹) * x := by group
          _ = f * x := by rw [h']
      exact h2.symm
    exact hfaith x hcen hx
  intro a b hab
  have hb : σ (a⁻¹ * b) = 1 := by
    rw [map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
  exact inv_mul_eq_one.mp (hker _ hb)

/-- **The conjugating automorphism `α` has order dividing `p`.**  Indeed `σ (α^k e) =
X^k σ e X^{-k}` for all `k`, by induction, and `X ^ p = 1`, so `σ (α^p e) = σ e`; injectivity of
`σ` gives `α ^ p = 1`. -/
private theorem aut_pow_apply_eq_self {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {E : Type*} [Group E] (σ : E →* Module.End K V)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (α : E ≃* E) (X : (Module.End K V)ˣ) (hα : ∀ e, σ (α e) = X * σ e * X⁻¹)
    {p : ℕ} (hXp : X ^ p = 1) :
    ∀ e, (α ^ p) e = e := by
  have hinj := injective_of_center_faithful σ hfaith hcomm
  have hpow : ∀ k : ℕ, ∀ e : E,
      σ ((α ^ k) e) = (↑(X ^ k) : Module.End K V) * σ e * ↑((X⁻¹) ^ k) := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      have h1 : (α ^ (n + 1)) e = α ((α ^ n) e) := by rw [pow_succ']; rfl
      rw [h1, hα, ih e, pow_succ', pow_succ, Units.val_mul, Units.val_mul]
      noncomm_ring
  intro e
  refine hinj ?_
  rw [hpow p e, inv_pow, hXp, inv_one, Units.val_one]
  simp

/-- **The permutation induced by `α` on `E ⧸ Z(E)`.**  Since `α` fixes `Z(E)` pointwise it induces
a permutation `π` of the quotient, whose only fixed point is the identity coset (by the
fixed-point-free hypothesis) and whose order divides `p`. -/
private theorem exists_perm_quotient_center {E : Type*} [Group E]
    (α : E ≃* E) (hαZ : ∀ z ∈ Subgroup.center E, α z = z)
    (hfpf : ∀ e, α e * e⁻¹ ∈ Subgroup.center E → e ∈ Subgroup.center E)
    {p : ℕ} (hαp : ∀ e, (α ^ p) e = e) :
    ∃ πE : Equiv.Perm (E ⧸ Subgroup.center E),
      (∀ e, πE (QuotientGroup.mk e) = QuotientGroup.mk (α e)) ∧
      πE ^ p = 1 ∧ (∀ q, πE q = q ↔ q = 1) := by
  have hmap : Subgroup.map (α : E →* E) (Subgroup.center E) = Subgroup.center E := by
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (α : E →* E) x = x := hαZ x hx
      rwa [hx']
    · intro hy
      refine ⟨α.symm y, ?_, α.apply_symm_apply y⟩
      have h3 : α.symm y = y := by
        apply α.injective
        rw [α.apply_symm_apply, hαZ y hy]
      rw [h3]
      exact hy
  let πM : (E ⧸ Subgroup.center E) ≃* (E ⧸ Subgroup.center E) :=
    QuotientGroup.congr _ _ α hmap
  let πE : Equiv.Perm (E ⧸ Subgroup.center E) := πM.toEquiv
  have hπmk : ∀ e : E, πE (QuotientGroup.mk e) = QuotientGroup.mk (α e) := fun e =>
    QuotientGroup.congr_mk _ _ α hmap e
  have hiter : ∀ k : ℕ, ∀ e : E,
      (⇑πE)^[k] (QuotientGroup.mk e) = QuotientGroup.mk ((α ^ k) e) := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [Function.iterate_succ_apply', ih e, hπmk]
      congr 1
      rw [pow_succ']; rfl
  refine ⟨πE, hπmk, ?_, ?_⟩
  · refine Equiv.ext (fun q => ?_)
    rw [Equiv.Perm.coe_pow]
    conv_lhs => rw [← Quotient.out_eq' q]
    rw [hiter p (Quotient.out q), hαp]
    exact Quotient.out_eq' q
  · intro q
    constructor
    · intro h
      have hq : (QuotientGroup.mk (Quotient.out q) : E ⧸ Subgroup.center E) = q :=
        Quotient.out_eq' q
      have hmk : (QuotientGroup.mk (α (Quotient.out q)) : E ⧸ Subgroup.center E)
          = (QuotientGroup.mk (Quotient.out q) : E ⧸ Subgroup.center E) := by
        rw [← hπmk (Quotient.out q), hq, h]
      have hmem : (α (Quotient.out q))⁻¹ * (Quotient.out q) ∈ Subgroup.center E :=
        QuotientGroup.eq.mp hmk
      have hmem' : (Quotient.out q)⁻¹ * α (Quotient.out q) ∈ Subgroup.center E := by
        have := Subgroup.inv_mem _ hmem
        rwa [mul_inv_rev, inv_inv] at this
      have hmem'' : α (Quotient.out q) * (Quotient.out q)⁻¹ ∈ Subgroup.center E := by
        have hc := (inferInstance : (Subgroup.center E).Normal).conj_mem _
          hmem' (Quotient.out q)
        rwa [show (Quotient.out q) * ((Quotient.out q)⁻¹ * α (Quotient.out q))
          * (Quotient.out q)⁻¹ = α (Quotient.out q) * (Quotient.out q)⁻¹ from by group] at hc
      have hxZ : Quotient.out q ∈ Subgroup.center E := hfpf _ hmem''
      rw [← hq]
      exact (QuotientGroup.eq_one_iff (Quotient.out q)).mpr hxZ
    · intro h
      rw [h]
      simpa using hπmk 1

/-- **Conjugation by `X` preserves the commutant of `σ`.** -/
private theorem conj_mem_commutantOf {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {E : Type*} [Group E] (σ : E →* Module.End K V) (α : E ≃* E)
    (X : (Module.End K V)ˣ) (hα : ∀ e, σ (α e) = X * σ e * X⁻¹) :
    ∀ β ∈ commutantOf σ, (↑X : Module.End K V) * β * ↑X⁻¹ ∈ commutantOf σ := by
  intro β hβ
  rw [Work.HallHigman.mem_commutantOf_iff] at hβ ⊢
  intro e
  have he : σ e = (↑X : Module.End K V) * σ (α.symm e) * ↑X⁻¹ := by
    have h := hα (α.symm e)
    rwa [α.apply_symm_apply] at h
  have hA : σ e * ((↑X : Module.End K V) * β * ↑X⁻¹)
      = (↑X : Module.End K V) * (σ (α.symm e) * β) * ↑X⁻¹ := by
    rw [he, unit_conj_mul]
  have hB : ((↑X : Module.End K V) * β * ↑X⁻¹) * σ e
      = (↑X : Module.End K V) * (β * σ (α.symm e)) * ↑X⁻¹ := by
    rw [he, unit_conj_mul]
  rw [hA, hB, hβ (α.symm e)]


/-- **L9 of the GL-core design** (Step 4d of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): the upper bound on the dimension of the commutant of `X`.

Hypotheses: as in the Fourier lemma (L8, `fourier_finrank`: `Z(E)` acts by an injective scalar
character and all commutators are central, `|E|` invertible) together with an automorphism `α` of
`E` induced by conjugating the representation by a unit `X` of order `p`, which fixes `Z(E)` and
acts fixed-point-freely on `E ⧸ Z(E)`.

Under the Fourier decomposition `End V ≅ (E ⧸ Z(E) → End_E(V))` (`Θ`), conjugation by `X` becomes a
monomial map permuting the coordinates along the `⟨X⟩`-orbits on `E ⧸ Z(E)`: the identity coset and
`(|E ⧸ Z(E)| - 1) / p` free orbits of size `p`.  A fixed point of `Ad X` is determined by the
coordinates on one representative per orbit, whence the bound
`p · dim C(X) ≤ (p + |E ⧸ Z(E)| - 1) · dim End_E(V)`.

(The prover may re-derive the Fourier decomposition of L8 in its own file, or use
`Work.HallHigman.GLCore.fourier_finrank` to reduce to `dim End V = |E⧸Z| · dim End_E V`.) -/
lemma p_mul_finrank_commutant_le {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {E : Type*} [Group E] [Finite E]
    (σ : E →* Module.End K V)
    (hsc : ∀ z ∈ Subgroup.center E, ∃ c : K, σ z = algebraMap K (Module.End K V) c)
    (hfaith : ∀ z ∈ Subgroup.center E, σ z = 1 → z = 1)
    (hcomm : ∀ e f : E, e * f * e⁻¹ * f⁻¹ ∈ Subgroup.center E)
    (hE : (Nat.card E : K) ≠ 0)
    (α : E ≃* E) (X : (Module.End K V)ˣ) (hα : ∀ e, σ (α e) = X * σ e * X⁻¹)
    (hαZ : ∀ z ∈ Subgroup.center E, α z = z)
    (hfpf : ∀ e, α e * e⁻¹ ∈ Subgroup.center E → e ∈ Subgroup.center E)
    {p : ℕ} [Fact p.Prime] (hXp : X ^ p = 1) :
    p * Module.finrank K (Work.HallHigman.commutant (X : Module.End K V)) ≤
      (p + Nat.card (E ⧸ Subgroup.center E) - 1) *
        Module.finrank K (Work.HallHigman.commutantOf σ) := by
  classical
  have hp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hp.one_lt.le
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype ↥(Subgroup.center E) := Fintype.ofFinite _
  letI : Fintype (E ⧸ Subgroup.center E) := Fintype.ofFinite _
  -- Step 1: `σ` is injective and `α ^ p = 1`.
  have hαp : ∀ e, (α ^ p) e = e := aut_pow_apply_eq_self σ hfaith hcomm α X hα hXp
  -- Step 2: the permutation of `E ⧸ Z(E)` induced by `α`.
  obtain ⟨πE, hπmk, hπp, hπfix⟩ := exists_perm_quotient_center α hαZ hfpf hαp
  -- Step 3: the Fourier isomorphism `Θ`.
  have hbij : Function.Bijective (fourierTheta σ) :=
    ⟨fourierTheta_injective σ hsc hfaith hcomm hE,
      fourierTheta_surjective σ hsc hfaith hcomm hE⟩
  let Θ : ((E ⧸ Subgroup.center E) → ↥(commutantOf σ)) ≃ₗ[K] Module.End K V :=
    LinearEquiv.ofBijective (fourierTheta σ) hbij
  have hΘ_apply : ∀ β, Θ β = fourierTheta σ β := fun β => rfl
  -- Step 4: conjugation by `X` on `End V` and on `End_E(V)`.
  let ΦE : Module.End K V →ₗ[K] Module.End K V :=
    (LinearMap.mulLeft K (↑X)).comp (LinearMap.mulRight K (↑X⁻¹))
  have hΦE : ∀ Y : Module.End K V, ΦE Y = (↑X : Module.End K V) * Y * ↑X⁻¹ := fun Y => by
    simp only [ΦE, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      mul_assoc]
  let ΦB : ↥(commutantOf σ) →ₗ[K] ↥(commutantOf σ) :=
    LinearMap.codRestrict (commutantOf σ) (ΦE.comp (commutantOf σ).subtype) (fun β => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hΦE]
      exact conj_mem_commutantOf σ α X hα _ β.2)
  have hΦB : ∀ β : ↥(commutantOf σ), (↑(ΦB β) : Module.End K V) = ΦE ↑β := fun β =>
    LinearMap.codRestrict_apply _ _ _
  let T : ((E ⧸ Subgroup.center E) → ↥(commutantOf σ)) →ₗ[K]
      ((E ⧸ Subgroup.center E) → ↥(commutantOf σ)) :=
    Θ.symm.toLinearMap.comp (ΦE.comp Θ.toLinearMap)
  have hT_at : ∀ β, T β = Θ.symm (ΦE (Θ β)) := fun β => rfl
  have hTΘ : ∀ β, Θ (T β) = ΦE (Θ β) := fun β => by
    rw [hT_at β, LinearEquiv.apply_symm_apply]
  -- Step 5: the scalars giving the monomial structure.
  have hzq : ∀ q : E ⧸ Subgroup.center E,
      (Quotient.out (πE q))⁻¹ * α (Quotient.out q) ∈ Subgroup.center E := by
    intro q
    have hq : (QuotientGroup.mk (Quotient.out q) : E ⧸ Subgroup.center E) = q :=
      Quotient.out_eq' q
    have h1 : (QuotientGroup.mk (Quotient.out (πE q)) : E ⧸ Subgroup.center E) = πE q :=
      Quotient.out_eq' (πE q)
    have h2 : (QuotientGroup.mk (α (Quotient.out q)) : E ⧸ Subgroup.center E) = πE q := by
      rw [← hπmk (Quotient.out q), hq]
    exact QuotientGroup.eq.mp (h1.trans h2.symm)
  let cK : (E ⧸ Subgroup.center E) → K := fun q =>
    (centerUnit σ hsc ⟨(Quotient.out (πE q))⁻¹ * α (Quotient.out q), hzq q⟩ : Kˣ)
  have hcK : ∀ q, (σ (α (Quotient.out q)) : Module.End K V) =
      cK q • σ (Quotient.out (πE q)) := by
    intro q
    have h1 : α (Quotient.out q)
        = (Quotient.out (πE q)) * ((Quotient.out (πE q))⁻¹ * α (Quotient.out q)) := by group
    rw [h1, map_mul, centerUnit_spec σ hsc ⟨_, hzq q⟩, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one]
  -- Step 6: conjugation by `X` acts monomially on the Fourier coordinates.
  have hTform : ∀ (β : (E ⧸ Subgroup.center E) → ↥(commutantOf σ)) (q : E ⧸ Subgroup.center E),
      T β q = cK (πE.symm q) • ΦB (β (πE.symm q)) := by
    intro β
    have step1 : ∀ q, (↑X : Module.End K V) * (σ (Quotient.out q) * ↑(β q)) * ↑X⁻¹
        = cK q • (σ (Quotient.out (πE q)) * ↑(ΦB (β q))) := by
      intro q
      rw [← unit_conj_mul X (σ (Quotient.out q)) ↑(β q), ← hα (Quotient.out q),
        ← hΦE (↑(β q)), ← hΦB (β q), hcK q, smul_mul_assoc]
    have step2 : (∑ q, cK q • (σ (Quotient.out (πE q)) * ↑(ΦB (β q))))
        = ∑ q, σ (Quotient.out q) * (cK (πE.symm q) • ↑(ΦB (β (πE.symm q)))) := by
      rw [← Equiv.sum_comp πE.symm
        (fun q => cK q • (σ (Quotient.out (πE q)) * ↑(ΦB (β q))))]
      exact Finset.sum_congr rfl (fun q _ => by
        rw [Equiv.apply_symm_apply, mul_smul_comm])
    let βt : (E ⧸ Subgroup.center E) → ↥(commutantOf σ) :=
      fun q => cK (πE.symm q) • ΦB (β (πE.symm q))
    have hβt_coe : ∀ q, (↑(βt q) : Module.End K V) =
        cK (πE.symm q) • ↑(ΦB (β (πE.symm q))) := fun q => by
      simp only [βt, Submodule.coe_smul]
    have hβtilde : Θ βt = ΦE (Θ β) := by
      calc Θ βt = ∑ q, σ (Quotient.out q) * (cK (πE.symm q) • ↑(ΦB (β (πE.symm q)))) := by
            rw [hΘ_apply, fourierTheta_apply]
            exact Finset.sum_congr rfl (fun q _ => by rw [hβt_coe])
        _ = ∑ q, cK q • (σ (Quotient.out (πE q)) * ↑(ΦB (β q))) := step2.symm
        _ = ∑ q, (↑X : Module.End K V) * (σ (Quotient.out q) * ↑(β q)) * ↑X⁻¹ :=
            Finset.sum_congr rfl (fun q _ => (step1 q).symm)
        _ = ΦE (∑ q, σ (Quotient.out q) * ↑(β q)) := by
            rw [hΦE, Finset.mul_sum, Finset.sum_mul]
        _ = ΦE (Θ β) := by
            rw [hΘ_apply, fourierTheta_apply]
            rfl
    have hTβ : T β = βt := by
      rw [hT_at β, ← hβtilde, LinearEquiv.symm_apply_apply]
    intro q
    rw [hTβ]
  -- Step 7: the orbit transversal and the dimension bound for the monomial operator.
  have hpsymm : πE.symm ^ p = 1 := by
    rw [show πE.symm = πE⁻¹ from rfl, inv_pow, hπp, inv_one]
  have hz : ∀ q, πE.symm q = q ↔ q = 1 := fun q => by
    rw [← hπfix q]
    exact ⟨fun h => by
        calc πE q = πE (πE.symm q) := by rw [h]
          _ = q := Equiv.apply_symm_apply πE q,
      fun h => by
        calc πE.symm q = πE.symm (πE q) := by rw [h]
          _ = q := Equiv.symm_apply_apply πE q⟩
  obtain ⟨R, hR, hRcard⟩ := orbit_transversal_card πE.symm hp hpsymm hz
  have hbound : Module.finrank K (LinearMap.ker (T - 1)) ≤
      R.card * Module.finrank K ↥(commutantOf σ) :=
    finrank_ker_monomial_le πE.symm (fun q => cK (πE.symm q)) ΦB T hTform R hR
  -- Step 8: identify the fixed space of `T` with the commutant of `X`.
  have hcomm_eq : Work.HallHigman.commutant (X : Module.End K V) = LinearMap.ker (ΦE - 1) := by
    ext Y
    rw [Work.HallHigman.mem_commutant_iff, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      hΦE]
    constructor
    · intro h
      calc (↑X : Module.End K V) * Y * ↑X⁻¹ = (Y * ↑X) * ↑X⁻¹ := by rw [h]
        _ = Y := by rw [mul_assoc]; simp
    · intro h
      have hXi : (↑X⁻¹ : Module.End K V) * ↑X = 1 := by simp
      have hY : (↑X : Module.End K V) * Y = ((↑X : Module.End K V) * Y * ↑X⁻¹) * ↑X := by
        rw [show ((↑X : Module.End K V) * Y * ↑X⁻¹) * ↑X
              = ((↑X : Module.End K V) * Y) * (↑X⁻¹ * ↑X) from by simp only [mul_assoc],
          hXi, mul_one]
      have h2 : (↑X : Module.End K V) * Y * ↑X⁻¹ = Y := by
        rw [h]
        simp
      rw [hY, h2]
  have hfin : Module.finrank K (LinearMap.ker (ΦE - 1)) =
      Module.finrank K (LinearMap.ker (T - 1)) := by
    have hmem : ∀ x : (E ⧸ Subgroup.center E) → ↥(commutantOf σ),
        (x ∈ LinearMap.ker (T - 1) ↔ Θ x ∈ LinearMap.ker (ΦE - 1)) := by
      intro x
      have h1 : (T x = x) ↔ ((T - 1) x = 0) := by
        rw [LinearMap.sub_apply, sub_eq_zero]
        simp
      have h2 : (ΦE (Θ x) = Θ x) ↔ ((ΦE - 1) (Θ x) = 0) := by
        rw [LinearMap.sub_apply, sub_eq_zero]
        simp
      rw [LinearMap.mem_ker, LinearMap.mem_ker, ← h1, ← h2, ← hTΘ x]
      exact ⟨fun h => congrArg Θ h, fun h => Θ.injective h⟩
    have hmap : Submodule.map Θ.toLinearMap (LinearMap.ker (T - 1)) = LinearMap.ker (ΦE - 1) := by
      ext Y
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hmem x).mp hx
      · intro hY
        refine ⟨Θ.symm Y, (hmem _).mpr ?_, Θ.apply_symm_apply Y⟩
        rw [LinearEquiv.apply_symm_apply]
        exact hY
    calc Module.finrank K (LinearMap.ker (ΦE - 1))
        = Module.finrank K (Submodule.map Θ.toLinearMap (LinearMap.ker (T - 1))) := by rw [hmap]
      _ = Module.finrank K (LinearMap.ker (T - 1)) :=
          (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Θ.toLinearMap Θ.injective
            (LinearMap.ker (T - 1)))).symm
  -- Step 9: assembly.
  have hcardsub : Fintype.card (E ⧸ Subgroup.center E) = Nat.card (E ⧸ Subgroup.center E) :=
    Nat.card_eq_fintype_card.symm
  calc p * Module.finrank K (Work.HallHigman.commutant (X : Module.End K V))
      = p * Module.finrank K (LinearMap.ker (T - 1)) := by rw [hcomm_eq, hfin]
    _ ≤ p * (R.card * Module.finrank K ↥(commutantOf σ)) := Nat.mul_le_mul_left p hbound
    _ = (p * R.card) * Module.finrank K ↥(commutantOf σ) := by rw [mul_assoc]
    _ = (Fintype.card (E ⧸ Subgroup.center E) + p - 1) * Module.finrank K ↥(commutantOf σ) := by
        rw [hRcard]
    _ = (p + Nat.card (E ⧸ Subgroup.center E) - 1) * Module.finrank K ↥(commutantOf σ) := by
        congr 1
        rw [hcardsub]
        omega
