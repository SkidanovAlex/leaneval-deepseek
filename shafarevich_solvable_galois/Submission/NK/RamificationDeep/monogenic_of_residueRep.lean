import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Submission.NK.RamificationDeep.moduleFinite_inertiaField_comap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace NK.RamificationDeep

open Polynomial Submodule

/-- The algebra structure of an intermediate field over the ambient field is the inclusion. -/
theorem algebraMap_intermediateField_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (M : IntermediateField F E) (x : ↥M) : algebraMap ↥M E x = (x : E) := rfl

/-! ## Auxiliary: naturality of `eval₂` under a ring homomorphism -/

/-- Evaluating `p.map f` at `g x` is the image under `g` of the evaluation of `p` at `x`. -/
theorem eval₂_map_comp {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : S →+* T) (x : S) (p : Polynomial R) :
    g (Polynomial.eval₂ f x p) = Polynomial.eval₂ (g.comp f) (g x) p := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range]
  simp only [map_sum, map_mul, map_pow, RingHom.comp_apply]

/-! ## The module-theoretic core (Nakayama step) -/

/-- **Descent step.**  Let `R` be a local ring, `B` a finite `R`-algebra and `π : B`.  Assume

* `B = R + π B` (every element of `B` is a scalar plus a multiple of `π`), and
* some positive power of `π` is a multiple of a nonzero element of the maximal ideal of `R`.

Then every element of `B` is a polynomial in `π` with coefficients in `R`. -/
theorem eval₂RingHom_surjective_of_pow_mem_smul_maximalIdeal
    {R B : Type*} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (π : B)
    (hgen : ∀ b : B, ∃ r : R, ∃ c : B, b = algebraMap R B r + π * c)
    (hN : ∃ r ∈ IsLocalRing.maximalIdeal R, ∃ N : ℕ, 0 < N ∧ ∃ a : B, π ^ N = r • a) :
    Function.Surjective (Polynomial.eval₂RingHom (algebraMap R B) π) := by
  classical
  obtain ⟨r₀, hr₀, N, hNpos, a₀, ha₀⟩ := hN
  set ψ : Polynomial R →+* B := Polynomial.eval₂RingHom (algebraMap R B) π with hψ
  have hψC : ∀ r : R, ψ (Polynomial.C r) = algebraMap R B r := by
    intro r; rw [hψ]; exact Polynomial.eval₂_C _ _
  have hψX : ψ Polynomial.X = π := by
    rw [hψ]; exact Polynomial.eval₂_X _ _
  set S : Subring B := ψ.range with hS
  have hπS : π ∈ S := ⟨Polynomial.X, hψX⟩
  let Ssub : Submodule R B :=
    { carrier := S
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      smul_mem' := by
        rintro c x ⟨p, rfl⟩
        exact ⟨Polynomial.C c * p, by rw [map_mul, hψC, Algebra.smul_def]⟩ }
  -- (1) `B = S + π ^ (n+1) * B` for every `n`
  have hdecomp : ∀ n : ℕ, ∀ b : B, ∃ s ∈ S, ∃ y : B, b = s + π ^ (n + 1) * y := by
    intro n
    induction n with
    | zero =>
      intro b
      obtain ⟨c, d, hcd⟩ := hgen b
      exact ⟨algebraMap R B c, ⟨Polynomial.C c, hψC c⟩, d, by rw [hcd, pow_one]⟩
    | succ n ih =>
      intro b
      obtain ⟨s, hs, y, hy⟩ := ih b
      obtain ⟨c, d, hcd⟩ := hgen y
      refine ⟨s + π ^ (n + 1) * algebraMap R B c,
        S.add_mem hs (S.mul_mem (S.pow_mem hπS (n + 1)) ⟨Polynomial.C c, hψC c⟩), d, ?_⟩
      rw [hy, hcd, show π ^ (n + 2) = π ^ (n + 1) * π from by rw [pow_succ]]
      ring
  -- (2) the quotient of `B` by `S` is killed by the maximal ideal
  haveI : Module.Finite R (B ⧸ Ssub) := Module.Finite.quotient R Ssub
  have hle : (⊤ : Submodule R (B ⧸ Ssub)) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (B ⧸ Ssub)) := by
    intro m _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (p := Ssub) m
    obtain ⟨s, hs, y, hy⟩ := hdecomp (N - 1) b
    have hNs : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hNpos
    have hb : b = s + r₀ • (a₀ * y) := by
      rw [hy, hNs, ha₀, Algebra.smul_mul_assoc]
    have hmk : (Submodule.mkQ Ssub) b = r₀ • (Submodule.mkQ Ssub) (a₀ * y) := by
      rw [hb, map_add, map_smul]
      rw [show (Submodule.mkQ Ssub) s = 0 from by
        rw [Submodule.mkQ_apply]; exact (Quotient.mk_eq_zero Ssub).mpr hs, zero_add]
    show (Submodule.mkQ Ssub) b ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (B ⧸ Ssub))
    rw [hmk]
    exact Submodule.smul_mem_smul hr₀ Submodule.mem_top
  -- (3) Nakayama
  have hJ : IsLocalRing.maximalIdeal R ≤ (⊥ : Ideal R).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
  have hbot : (⊤ : Submodule R (B ⧸ Ssub)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top hle hJ
  have hStop : S = ⊤ := by
    have h := congrArg (Submodule.comap (Submodule.mkQ Ssub)) hbot
    rw [Submodule.comap_top, Submodule.comap_bot, Submodule.ker_mkQ] at h
    refine SetLike.ext fun x => ?_
    have hx : x ∈ Ssub := h.symm ▸ Submodule.mem_top
    exact ⟨fun _ => Subring.mem_top x, fun _ => hx⟩
  exact RingHom.range_eq_top.mp hStop

/-! ## The maximal ideal of `A` pulled back to `A ∩ E` -/

/-- If the image in `A` of an element `a` of `A ∩ E` is a unit of `A`, then `a` is a unit
of `A ∩ E`. -/
theorem isUnit_of_isUnit_comapHom {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) {a : ↥(A.comap (algebraMap E L))}
    (h : IsUnit (comapHom A a)) : IsUnit a := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists.mp h
  have ha0 : (a : E) ≠ 0 := by
    intro h0
    have h1 : comapHom A a = 0 := by ext; simp [h0]
    rw [h1, zero_mul] at hw
    exact zero_ne_one hw.1
  have hkey : algebraMap E L ((a : E)⁻¹) = algebraMap ↥A L w := by
    rw [map_inv₀]
    have h3 : algebraMap E L (a : E) = algebraMap ↥A L (comapHom A a) :=
      (coe_algebraMap_comap_apply A a).symm
    rw [h3, eq_comm]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hw.2, map_one])
  have hb : ((a : E)⁻¹) ∈ (A.comap (algebraMap E L) : ValuationSubring E) := by
    rw [ValuationSubring.mem_comap, hkey]
    exact w.2
  exact IsUnit.of_mul_eq_one (⟨(a : E)⁻¹, hb⟩ : ↥(A.comap (algebraMap E L))) (by
    ext
    exact mul_inv_cancel₀ ha0)

/-- The inclusion `A ∩ E ↪ A` is a local homomorphism: it pulls the maximal ideal of `A`
back to the maximal ideal of `A ∩ E`. -/
theorem comapHom_mem_maximalIdeal {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) {a : ↥(A.comap (algebraMap E L))}
    (ha : a ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L))) :
    comapHom A a ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal] at ha ⊢
  exact fun hu => ha (isUnit_of_isUnit_comapHom A hu)

/-! ## A uniformizer power is a multiple of an element of the maximal ideal of `A ∩ E` -/

/-- If the maximal ideal of `A ∩ E` is nonzero, then some positive power of the uniformizer
`π` of `A` is a multiple of a nonzero element of that maximal ideal. -/
theorem exists_pow_mem_smul_maximalIdeal {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (hbot : IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L)) ≠ ⊥) :
    ∃ r ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L)), ∃ N : ℕ, 0 < N ∧
      ∃ a : ↥A, π ^ N = r • a := by
  classical
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hπA : π ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [hπ]; exact Ideal.mem_span_singleton_self π
  have hπ0 : π ≠ 0 := by
    intro h0
    have hb : IsLocalRing.maximalIdeal ↥A = ⊥ := by
      rw [hπ, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField ↥A
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hb)
  have hrA : comapHom A r ∈ IsLocalRing.maximalIdeal ↥A := comapHom_mem_maximalIdeal A hr
  have hrA0 : comapHom A r ≠ 0 := by
    intro h
    exact hr0 (comapHom_injective A (by simpa using h))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, IsDiscreteValuationRing.addVal ↥A (comapHom A r) = ↑m := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp fun h =>
      hrA0 ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
    exact ⟨m, hm.symm⟩
  obtain ⟨l, hl⟩ : ∃ l : ℕ, IsDiscreteValuationRing.addVal ↥A π = ↑l := by
    obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp fun h =>
      hπ0 ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
    exact ⟨l, hl.symm⟩
  have hm0 : m ≠ 0 := by
    intro h0
    have hunit : IsUnit (comapHom A r) :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mp (by rw [hm, h0]; rfl)
    exact (IsLocalRing.mem_maximalIdeal (comapHom A r)).mp hrA hunit
  have hl0 : l ≠ 0 := by
    intro h0
    have hunit : IsUnit π :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mp (by rw [hl, h0]; rfl)
    exact (IsLocalRing.mem_maximalIdeal π).mp hπA hunit
  have hdvd : comapHom A r ∣ π ^ m := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, hm, hl]
    rw [nsmul_eq_mul]
    have hml : (m : ℕ∞) ≤ ((m * l : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hl0)
    simpa using hml
  obtain ⟨a, ha⟩ := hdvd
  exact ⟨r, hr, m, Nat.pos_of_ne_zero hm0, a, by rw [ha, Algebra.smul_def, algebraMap_comap_apply]⟩

/-! ## The monogenicity statement over an arbitrary subfield -/

/-- **Monogeneity of `A` over `A ∩ E` from the residue representation.**  Let `E ⊆ L` be a
subfield, `A` a discrete valuation ring of `L` with uniformizer `π`, and assume that every
element of `A` is congruent modulo `π` to an element of `A ∩ E` (`hres`).  If moreover `A` is a
finite module over `A ∩ E`, then `A = (A ∩ E)[π]`: every element of `A` is a polynomial in `π`
whose coefficients lie in `A ∩ E`. -/
theorem polynomial_rep_of_residueRep {E L : Type*} [Field E] [Field L] [Algebra E L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A] (π : A)
    (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    [Module.Finite ↥(A.comap (algebraMap E L)) ↥A]
    (hres : ∀ x : A, ∃ b : ↥(A.comap (algebraMap E L)),
      comapHom A b - x ∈ IsLocalRing.maximalIdeal A) :
    ∀ x : A, ∃ p : Polynomial E,
      (∀ j, algebraMap E L (p.coeff j) ∈ A) ∧
      p.eval₂ (algebraMap E L) (π : L) = (x : L) := by
  classical
  -- `A = (A ∩ E) + π A`
  have hgen : ∀ b : ↥A, ∃ r : ↥(A.comap (algebraMap E L)), ∃ c : ↥A,
      b = algebraMap ↥(A.comap (algebraMap E L)) ↥A r + π * c := by
    intro b
    obtain ⟨r, hr⟩ := hres b
    have hmem : comapHom A r - b ∈ Ideal.span ({π} : Set ↥A) := by rwa [← hπ]
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨r, -c, ?_⟩
    have hbc : b = comapHom A r - π * c := by
      rw [eq_sub_iff_add_eq, ← hc]; ring
    rw [hbc, algebraMap_comap_apply]
    ring
  -- a positive power of `π` is a multiple of an element of the maximal ideal of `A ∩ E`
  have hN : ∃ r ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L)), ∃ N : ℕ, 0 < N ∧
      ∃ a : ↥A, π ^ N = r • a := by
    by_cases hbot : IsLocalRing.maximalIdeal ↥(A.comap (algebraMap E L)) = ⊥
    · -- then `A ∩ E` would be a field and `A` finite over it, hence a field itself
      exfalso
      have hRf : IsField ↥(A.comap (algebraMap E L)) :=
        (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot
      letI : Field ↥(A.comap (algebraMap E L)) := IsField.toField hRf
      have hπA : π ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [hπ]; exact Ideal.mem_span_singleton_self π
      have hπ0 : π ≠ 0 := by
        intro h0
        have hb : IsLocalRing.maximalIdeal ↥A = ⊥ := by
          rw [hπ, h0, Ideal.span_singleton_eq_bot]
        exact IsDiscreteValuationRing.not_isField ↥A
          ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hb)
      haveI : FiniteDimensional ↥(A.comap (algebraMap E L)) ↥A := ‹Module.Finite _ _›
      have hinj : Function.Injective
          (LinearMap.mulLeft ↥(A.comap (algebraMap E L)) π) := by
        intro a b hab
        exact mul_left_cancel₀ hπ0 hab
      have hsurj : Function.Surjective
          (LinearMap.mulLeft ↥(A.comap (algebraMap E L)) π) :=
        LinearMap.surjective_of_injective hinj
      obtain ⟨c, hc⟩ := hsurj 1
      exact (IsLocalRing.mem_maximalIdeal π).mp hπA (IsUnit.of_mul_eq_one c hc)
    · exact exists_pow_mem_smul_maximalIdeal A π hπ hbot
  intro x
  obtain ⟨p, hp⟩ :=
    eval₂RingHom_surjective_of_pow_mem_smul_maximalIdeal
      (R := ↥(A.comap (algebraMap E L))) π hgen hN x
  refine ⟨p.map (Subring.subtype (A.comap (algebraMap E L)).toSubring), ?_, ?_⟩
  · intro j
    rw [Polynomial.coeff_map]
    exact (p.coeff j).2
  · rw [Polynomial.eval₂_map]
    have h2 : (algebraMap E L).comp (Subring.subtype (A.comap (algebraMap E L)).toSubring)
        = (algebraMap ↥A L).comp (algebraMap ↥(A.comap (algebraMap E L)) ↥A) := by
      ext r
      exact (coe_algebraMap_comap_apply A r).symm
    rw [h2]
    have hp' : Polynomial.eval₂ (algebraMap ↥(A.comap (algebraMap E L)) ↥A) π p = x := hp
    have hπcoe : (π : L) = algebraMap ↥A L π := rfl
    rw [hπcoe, ← eval₂_map_comp (f := algebraMap ↥(A.comap (algebraMap E L)) ↥A)
      (g := algebraMap ↥A L) (x := π) (p := p), hp']
    exact algebraMap_subtypeMem_apply A x

/-! ## The requested lemma -/

theorem monogenic_of_residueRep {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsGalois K L] [Finite ↥(A.decompositionSubgroup K)] (hA : A.decompositionSubgroup K = ⊤)
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (hres : ∀ x : A, ∃ b : ↥(NK.RamificationDeep.restrictRing A (NK.RamificationDeep.inertiaField (K := K) A)),
      NK.RamificationDeep.restrictRingToA A (NK.RamificationDeep.inertiaField (K := K) A) b - x ∈ IsLocalRing.maximalIdeal A) :
    ∀ x : A, ∃ p : Polynomial ↥(NK.RamificationDeep.inertiaField (K := K) A),
      (∀ j, ((p.coeff j : ↥(NK.RamificationDeep.inertiaField (K := K) A)) : L) ∈ A) ∧
      p.eval₂ (algebraMap ↥(NK.RamificationDeep.inertiaField (K := K) A) L) (π : L) = (x : L) := by
  classical
  haveI hfin : Module.Finite ↥(A.comap (algebraMap ↥(inertiaField (K := K) A) L)) ↥A :=
    moduleFinite_inertiaField_comap (K := K) A hA
  have hres' : ∀ x : A, ∃ b : ↥(A.comap (algebraMap ↥(inertiaField (K := K) A) L)),
      comapHom A b - x ∈ IsLocalRing.maximalIdeal A := by
    intro x
    obtain ⟨b, hb⟩ := hres x
    exact ⟨b, by
      simp only [comapHom, algebraMap_intermediateField_apply]
      exact hb⟩
  intro x
  obtain ⟨p, hp1, hp2⟩ :=
    polynomial_rep_of_residueRep (E := ↥(inertiaField (K := K) A)) A π hπ hres' x
  exact ⟨p, fun j => by simpa only [algebraMap_intermediateField_apply] using hp1 j, hp2⟩

end NK.RamificationDeep
