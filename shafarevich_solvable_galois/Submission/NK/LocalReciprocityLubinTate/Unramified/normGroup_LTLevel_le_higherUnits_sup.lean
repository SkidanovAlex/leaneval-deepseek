import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_valuation_extension_finite
import Submission.NK.LocalReciprocityLubinTate.LubinTate.norm_root_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Unramified.coeff_LTpolyEis_mem_span_lower
import Submission.NK.LocalReciprocityLubinTate.Unramified.norm_adjoinRoot_eq_resultant
import Submission.NK.LocalReciprocityLubinTate.Unramified.resultant_LTpolyEis_heart
import Submission.NK.LocalReciprocityLubinTate.Unramified.valuation_aeval_eq_zpow
import Submission.NK.LocalReciprocityLubinTate.Unramified.valuation_root_pow_eq

namespace NK.LocalReciprocityLubinTate.Unramified

open Polynomial
open scoped ValuativeRel

universe u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

noncomputable section

/-! ## Auxiliary lemmas for Honda's norm computation -/

/-- The Eisenstein factor is compatible with ring homomorphisms: mapping the coefficients of
`LTpolyEis P q n` along `φ` gives `LTpolyEis (φ P) q n`. -/
theorem LTpolyEis_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (P : A) (q m : ℕ) :
    (LTpolyEis P q m).map φ = LTpolyEis (φ P) q m := by
  have hiter : ∀ m : ℕ, (LTpolyIter P q m).map φ = LTpolyIter (φ P) q m := by
    intro m
    induction m with
    | zero => simp [LTpolyIter_zero]
    | succ k ih =>
        rw [LTpolyIter_succ, LTpolyIter_succ, Polynomial.map_comp, ih]
        congr 1
        simp only [LTpoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
          Polynomial.map_C, Polynomial.map_X]
  simp only [LTpolyEis, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_C, hiter]

/-- Every unit of `F` is, up to a power of the uniformiser, a unit of the ring of integers:
`Fˣ = ⟨π⟩ · 𝒪[F]ˣ`, with the exponent of `π` recorded. -/
theorem exists_content_decomposition (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (πu : Fˣ) (hπ : IsUniformizer F (πu : F)) (c : Fˣ) :
    ∃ k : ℤ, ∃ u : (↥(ValuativeRel.valuation F).integer)ˣ,
      c = πu ^ k * NK.LocalReciprocityLubinTate.Units.unitsIncl F u := by
  have hmem : c ∈ Subgroup.zpowers πu ⊔
      (NK.LocalReciprocityLubinTate.Units.unitsIncl F).range := by
    rw [NK.LocalReciprocityLubinTate.Units.sup_zpowers_range F πu hπ]
    exact Subgroup.mem_top c
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hb
  exact ⟨k, u, by rw [← hab, hk]⟩

/-- Every element of `AdjoinRoot E` has a representative of degree `< E.natDegree`. -/
theorem exists_rep_adjoinRoot {F : Type u} [Field F] (E : Polynomial F)
    (hmon : E.Monic) (hEne : E ≠ 1) (x : AdjoinRoot E) :
    ∃ g : Polynomial F, g.natDegree < E.natDegree ∧ x = AdjoinRoot.mk E g := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (g := E) x
  refine ⟨p %ₘ E, ?_, ?_⟩
  · exact Polynomial.natDegree_modByMonic_lt p hmon hEne
  · rw [← hp, AdjoinRoot.mk_eq_mk]
    refine ⟨p /ₘ E, ?_⟩
    have h := Polynomial.modByMonic_add_div p E
    calc p - p %ₘ E = (p %ₘ E + E * (p /ₘ E)) - p %ₘ E := by rw [h]
      _ = E * (p /ₘ E) := by ring

/-! ## The main computation -/

/-- **Honda's norm computation on the AdjoinRoot model.**

For the Lubin–Tate level `K_n = F(Λ_n)`, realised as `AdjoinRoot (LTpolyEis (πu:F) q (n-1))`,
the norm of every unit lies in `⟨πu⟩ · U^n`. -/
private theorem norm_units_adjoinRoot_le (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) (hn : 1 ≤ n)
    (z : (AdjoinRoot (LTpolyEis (πu : F) (residueCard F) (n - 1)))ˣ) :
    (Units.map (Algebra.norm F :
        AdjoinRoot (LTpolyEis (πu : F) (residueCard F) (n - 1)) →* F) z)
      ∈ (Subgroup.zpowers πu ⊔ higherUnits F n) := by
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  set A : Subring F := (ValuativeRel.valuation F).integer with hA
  let Em : Polynomial F := LTpolyEis (πu : F) (residueCard F) (n - 1)
  let d : ℕ := (residueCard F - 1) * residueCard F ^ (n - 1)
  have hd1 : 1 ≤ d := by
    simp only [d]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) _)
  obtain ⟨hEmon, hEdeg0, hEc0, _⟩ :=
    LubinTate.LTpolyEis_shape (πu : F) (residueCard F) (n - 1) hq2
  have hEdeg : Em.natDegree = d := hEdeg0
  have hEne : Em ≠ 1 := by
    intro h1
    have h2 : Em.natDegree = 0 := by rw [h1]; simp
    omega
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F πu hπ
  have hEirr : Irreducible Em := by
    have h1 : Em = LTpolyEis (P : F) (residueCard F) (n - 1) := by
      simp only [Em, ← hPcoe]
    rw [h1]
    exact irreducible_LTpolyEis F P hPirr (residueCard F) (n - 1) hq2
  haveI : Fact (Irreducible Em) := ⟨hEirr⟩
  haveI : Module.Finite F (AdjoinRoot Em) := hEmon.finite_adjoinRoot
  haveI : Algebra.IsIntegral F (AdjoinRoot Em) := Algebra.IsIntegral.of_finite F _
  haveI : Algebra.IsSeparable F (AdjoinRoot Em) := inferInstance
  obtain ⟨w, hw⟩ := Eval.exists_valuation_extension_finite F (AdjoinRoot Em)
  have hAinj : Function.Injective A.subtype := fun x y h => Subtype.ext h
  have hinj : Function.Injective (algebraMap F (AdjoinRoot Em)) := by
    rw [AdjoinRoot.algebraMap_eq]
    refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
    rw [Polynomial.degree_eq_natDegree hEmon.ne_zero]
    exact_mod_cast (by omega : Em.natDegree ≠ 0)
  have hEm_eq : Em = (LTpolyEis P (residueCard F) (n - 1)).map A.subtype := by
    have h1 := LTpolyEis_map A.subtype P (residueCard F) (n - 1)
    simp only [Em, Subring.coe_subtype] at *
    rw [h1, ← hPcoe]
  have hroot_zero : (aeval (AdjoinRoot.root Em)) Em = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  have hPval : w (algebraMap F (AdjoinRoot Em) (P : F)) < 1 :=
    (Valuation.HasExtension.val_map_lt_one_iff (ValuativeRel.valuation F) w (P : F)).mpr (by
      rw [hPcoe]
      exact Valuation.IsUniformizer.val_lt_one hπ)
  have hPne : (P : F) ≠ 0 := by rw [hPcoe]; exact Units.ne_zero πu
  have hcoeff : ∀ i, i < d → w ((Em.map (algebraMap F (AdjoinRoot Em))).coeff i) ≤
      w (algebraMap F (AdjoinRoot Em) (P : F)) := by
    intro i hi
    have hi' : i < (residueCard F - 1) * residueCard F ^ (n - 1) := by simpa only [d] using hi
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
      (coeff_LTpolyEis_mem_span_lower P (residueCard F) (n - 1) hq2 i hi')
    have hcoeffi : Em.coeff i = (P : F) * (b : F) := by
      rw [hEm_eq, Polynomial.coeff_map, hb]
      simp
    rw [Polynomial.coeff_map, hcoeffi, map_mul, Valuation.map_mul]
    have hble : w (algebraMap F (AdjoinRoot Em) ((b : A) : F)) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (ValuativeRel.valuation F) w ((b : A) : F)).mpr
        (show (ValuativeRel.valuation F) ((b : A) : F) ≤ 1 from b.2)
    calc w (algebraMap F (AdjoinRoot Em) (P : F)) *
          w (algebraMap F (AdjoinRoot Em) ((b : A) : F))
        ≤ w (algebraMap F (AdjoinRoot Em) (P : F)) * 1 := by gcongr
      _ = w (algebraMap F (AdjoinRoot Em) (P : F)) := mul_one _
  have hroot_pow : w (AdjoinRoot.root Em) ^ d = w (algebraMap F (AdjoinRoot Em) (P : F)) :=
    (valuation_root_pow_eq w (AdjoinRoot.root Em) (algebraMap F (AdjoinRoot Em) (P : F))
      (Em.map (algebraMap F (AdjoinRoot Em))) d hd1 (hEmon.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap F (AdjoinRoot Em)) hinj,
            hEdeg])
      (by rw [Polynomial.aeval_map_algebraMap]; exact hroot_zero) hPval
      (fun h0 => hPne (hinj (by rw [h0, map_zero])))
      (fun i hi => hcoeff i hi) (by rw [Polynomial.coeff_map, hEc0, hPcoe])).1
  have hroot_lt : w (AdjoinRoot.root Em) < 1 :=
    (valuation_root_pow_eq w (AdjoinRoot.root Em) (algebraMap F (AdjoinRoot Em) (P : F))
      (Em.map (algebraMap F (AdjoinRoot Em))) d hd1 (hEmon.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap F (AdjoinRoot Em)) hinj,
            hEdeg])
      (by rw [Polynomial.aeval_map_algebraMap]; exact hroot_zero) hPval
      (fun h0 => hPne (hinj (by rw [h0, map_zero])))
      (fun i hi => hcoeff i hi) (by rw [Polynomial.coeff_map, hEc0, hPcoe])).2
  have hβne : w (AdjoinRoot.root Em) ≠ 0 := (Valuation.ne_zero_iff w).mpr (by
    intro h0
    have h1 : w (algebraMap F (AdjoinRoot Em) (P : F)) = 0 := by
      rw [← hroot_pow, h0, map_zero, zero_pow (by omega : d ≠ 0)]
    have h2 : algebraMap F (AdjoinRoot Em) (P : F) = 0 := by
      by_contra hne
      exact (Valuation.ne_zero_iff w).mpr hne h1
    exact hPne (hinj (by rw [h2, map_zero])))
  have hroot_ne : AdjoinRoot.root Em ≠ 0 := (Valuation.ne_zero_iff w).mp hβne
  -- the content decomposition of the coefficients
  have hcontent : ∀ c : F, c ≠ 0 → ∃ k : ℤ, ∃ u : Aˣ,
      c = (((πu : Fˣ) ^ k * NK.LocalReciprocityLubinTate.Units.unitsIncl F u : Fˣ) : F) := by
    intro c hc
    obtain ⟨k, u, hku⟩ := exists_content_decomposition F πu hπ (Units.mk0 c hc)
    exact ⟨k, u, by rw [← hku]; simp⟩
  let K : Polynomial F → ℕ → ℤ := fun g i =>
    if h : g.coeff i = 0 then 0 else Classical.choose (hcontent (g.coeff i) h)
  let U : Polynomial F → ℕ → Aˣ := fun g i =>
    if h : g.coeff i = 0 then 1
    else Classical.choose (Classical.choose_spec (hcontent (g.coeff i) h))
  have hKU : ∀ (g : Polynomial F) (i : ℕ) (hi : g.coeff i ≠ 0), g.coeff i =
      (((πu : Fˣ) ^ (K g i) *
        NK.LocalReciprocityLubinTate.Units.unitsIncl F (U g i) : Fˣ) : F) := by
    intro g i hi
    simp only [K, U, dif_neg hi]
    exact Classical.choose_spec (Classical.choose_spec (hcontent (g.coeff i) hi))
  have hunit_val : ∀ u : Aˣ, w (algebraMap F (AdjoinRoot Em)
      (((NK.LocalReciprocityLubinTate.Units.unitsIncl F u : Fˣ)) : F)) = 1 := by
    intro u
    rw [show (1 : WithZero (Multiplicative ℤ)) =
      w (algebraMap F (AdjoinRoot Em) (1 : F)) from (map_one w).symm]
    refine (Valuation.HasExtension.val_map_eq_iff (ValuativeRel.valuation F) w _ 1).mpr ?_
    rw [map_one]
    have h1 : (ValuativeRel.valuation F) ((u : A) : F) ≤ 1 := (u : A).2
    have h2 : (ValuativeRel.valuation F) (((u⁻¹ : Aˣ) : A) : F) ≤ 1 := ((u⁻¹ : Aˣ) : A).2
    have h3 : (ValuativeRel.valuation F) ((u : A) : F) *
        (ValuativeRel.valuation F) (((u⁻¹ : Aˣ) : A) : F) = 1 := by
      rw [← Valuation.map_mul]
      have h : ((u : A) : F) * (((u⁻¹ : Aˣ) : A) : F) = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Subring.coe_one]
      rw [h, Valuation.map_one]
    have h4 : (1 : ValuativeRel.ValueGroupWithZero F) ≤
        (ValuativeRel.valuation F) ((u : A) : F) := by
      calc (1 : ValuativeRel.ValueGroupWithZero F) = (ValuativeRel.valuation F) ((u : A) : F) *
            (ValuativeRel.valuation F) (((u⁻¹ : Aˣ) : A) : F) := h3.symm
        _ ≤ (ValuativeRel.valuation F) ((u : A) : F) * 1 := by gcongr
        _ = (ValuativeRel.valuation F) ((u : A) : F) := mul_one _
    exact le_antisymm h1 h4
  -- the value hypothesis of the "ord" lemma, for a general polynomial `g`
  have hKval : ∀ (g : Polynomial F) (i : ℕ), i ∈ (g.map (algebraMap F (AdjoinRoot Em))).support →
      w ((g.map (algebraMap F (AdjoinRoot Em))).coeff i) =
        (w (algebraMap F (AdjoinRoot Em) (P : F))) ^ (K g i) := by
    intro g i hi
    have hgi : g.coeff i ≠ 0 := fun h0 =>
      (Polynomial.mem_support_iff.mp hi) (by rw [Polynomial.coeff_map, h0, map_zero])
    rw [Polynomial.coeff_map, hKU g i hgi]
    rw [show (((πu : Fˣ) ^ (K g i) *
          NK.LocalReciprocityLubinTate.Units.unitsIncl F (U g i) : Fˣ) : F) =
        (πu : F) ^ (K g i) *
          ((NK.LocalReciprocityLubinTate.Units.unitsIncl F (U g i) : Fˣ) : F)
      from by rw [Units.val_mul, Units.val_zpow_eq_zpow_val]]
    rw [map_mul, map_zpow₀ (algebraMap F (AdjoinRoot Em)) (πu : F) (K g i),
      Valuation.map_mul, map_zpow₀ w (algebraMap F (AdjoinRoot Em) (πu : F)) (K g i),
      show algebraMap F (AdjoinRoot Em) (πu : F) = algebraMap F (AdjoinRoot Em) (P : F)
        from by rw [hPcoe],
      hunit_val, mul_one]
  -- **the unit step**: an element of valuation `1` has a norm in `U^n`
  have key : ∀ x : AdjoinRoot Em, w x = 1 →
      ∃ u : Fˣ, u ∈ higherUnits F n ∧ (u : F) = Algebra.norm F x := by
    intro x hx1
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Valuation.map_zero] at hx1
      exact zero_ne_one hx1
    obtain ⟨g, hgnat, hgx⟩ := exists_rep_adjoinRoot Em hEmon hEne x
    have hgne : g ≠ 0 := by
      rintro rfl
      rw [show (AdjoinRoot.mk Em) (0 : Polynomial F) = 0 from map_zero _] at hgx
      exact hx0 hgx
    have hgdeg : (g.map (algebraMap F (AdjoinRoot Em))).natDegree < d := by
      rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap F (AdjoinRoot Em)) hinj,
        ← hEdeg]
      exact hgnat
    have hg0' : g.map (algebraMap F (AdjoinRoot Em)) ≠ 0 := by
      intro h
      exact hgne ((Polynomial.map_injective (algebraMap F (AdjoinRoot Em)) hinj) (by
        rw [h, Polynomial.map_zero]))
    obtain ⟨m, hmw, i₀, hi₀mem, hmi₀, hmin⟩ :=
      valuation_aeval_eq_zpow w (AdjoinRoot.root Em)
        (algebraMap F (AdjoinRoot Em) (P : F)) d hd1 hroot_lt hroot_ne
        hroot_pow.symm (g.map (algebraMap F (AdjoinRoot Em))) hg0' hgdeg (K g) (hKval g)
    have hxaeval : x = (aeval (AdjoinRoot.root Em)) (g.map (algebraMap F (AdjoinRoot Em))) := by
      rw [hgx, ← AdjoinRoot.aeval_eq,
        ← Polynomial.aeval_map_algebraMap (AdjoinRoot Em) (AdjoinRoot.root Em) g]
    have hw1 : (w (AdjoinRoot.root Em)) ^ m = 1 := by
      rw [← hmw, ← hxaeval, hx1]
    have hm0 : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := (zpow_right_strictAnti₀ (zero_lt_iff.mpr hβne) hroot_lt) hlt
        change (w (AdjoinRoot.root Em)) ^ (0 : ℤ) < (w (AdjoinRoot.root Em)) ^ m at h
        rw [zpow_zero, hw1] at h
        exact lt_irrefl 1 h
      · have h := (zpow_right_strictAnti₀ (zero_lt_iff.mpr hβne) hroot_lt) hgt
        change (w (AdjoinRoot.root Em)) ^ m < (w (AdjoinRoot.root Em)) ^ (0 : ℤ) at h
        rw [zpow_zero, hw1] at h
        exact lt_irrefl 1 h
    have hi₀mem' : i₀ ∈ g.support := by
      rwa [Polynomial.support_map_of_injective g hinj] at hi₀mem
    have hKnonneg : ∀ i ∈ g.support, 0 ≤ K g i := by
      intro i hi
      have hi' : i < d := by
        have hle : i ≤ g.natDegree := Polynomial.le_natDegree_of_mem_supp _ hi
        omega
      have h := hmin i (by rwa [Polynomial.support_map_of_injective g hinj])
      rw [hm0] at h
      by_contra hneg
      push_neg at hneg
      have hKle : K g i ≤ -1 := by omega
      have hdle : (d : ℤ) * K g i ≤ (d : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left hKle (by omega : (0 : ℤ) ≤ (d : ℤ))
      have hid : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi'
      have hsum : (d : ℤ) * K g i + (i : ℤ) < 0 := by linarith [hdle, hid]
      linarith [h, hsum]
    have hi₀0 : i₀ = 0 := by
      have h := hmi₀
      rw [hm0] at h
      have hle : i₀ ≤ g.natDegree := Polynomial.le_natDegree_of_mem_supp _ hi₀mem'
      have hlt : (i₀ : ℤ) < (d : ℤ) := by
        have h1 : (i₀ : ℤ) ≤ (g.natDegree : ℤ) := by exact_mod_cast hle
        have h2 : (g.natDegree : ℤ) < (d : ℤ) := by
          have hh := hgnat
          rw [hEdeg] at hh
          exact_mod_cast hh
        linarith
      have hdvd : (d : ℤ) ∣ (i₀ : ℤ) := ⟨-(K g i₀), by linarith⟩
      have hdvd' : d ∣ i₀ := by exact_mod_cast hdvd
      rcases Nat.eq_zero_or_pos i₀ with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 hdvd') (by omega)
    have hK0 : K g 0 = 0 := by
      have h := hmi₀
      rw [hm0, hi₀0] at h
      have hmul : (d : ℤ) * K g 0 = 0 := by omega
      exact (mul_eq_zero.mp hmul).resolve_left (by rw [Nat.cast_eq_zero]; omega)
    -- the polynomial over the ring of integers
    let h : Polynomial A := ∑ i ∈ g.support,
      Polynomial.C (P ^ (K g i).toNat * (U g i : A)) * Polynomial.X ^ i
    have hcoeff_formula : ∀ j : ℕ, h.coeff j =
        if j ∈ g.support then P ^ (K g j).toNat * (U g j : A) else 0 := by
      intro j
      simp only [h, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq g.support j (fun i => P ^ (K g i).toNat * (U g i : A))]
    have hmap : h.map A.subtype = g := by
      ext j
      rw [Polynomial.coeff_map, hcoeff_formula j]
      by_cases hj : j ∈ g.support
      · rw [if_pos hj, hKU g j (Polynomial.mem_support_iff.mp hj)]
        rw [show (((πu : Fˣ) ^ (K g j) *
              NK.LocalReciprocityLubinTate.Units.unitsIncl F (U g j) : Fˣ) : F) =
            (πu : F) ^ (K g j) *
              ((NK.LocalReciprocityLubinTate.Units.unitsIncl F (U g j) : Fˣ) : F)
            from by rw [Units.val_mul, Units.val_zpow_eq_zpow_val]]
        have h1 : A.subtype (P ^ (K g j).toNat) = (πu : F) ^ (K g j) := by
          rw [map_pow, Subring.coe_subtype, ← zpow_natCast,
            Int.toNat_of_nonneg (hKnonneg j hj), hPcoe]
        rw [map_mul, h1]
        rfl
      · rw [if_neg hj, map_zero]
        exact (Polynomial.notMem_support_iff.mp hj).symm
    have hunit0 : IsUnit (h.coeff 0) := by
      have h0mem : (0 : ℕ) ∈ g.support := by rw [← hi₀0]; exact hi₀mem'
      rw [hcoeff_formula 0, if_pos h0mem, hK0]
      simp
    -- the norm is the resultant of `h` and the Eisenstein factor
    have hnorm : Algebra.norm F x =
        A.subtype ((LTpolyEis P (residueCard F) (n - 1)).resultant h) := by
      rw [hgx, norm_adjoinRoot_eq_resultant Em hEmon hEirr g]
      conv_lhs => rw [hEm_eq, ← hmap]
      rw [show Polynomial.resultant ((LTpolyEis P (residueCard F) (n - 1)).map A.subtype)
            (h.map A.subtype) =
          A.subtype (Polynomial.resultant (LTpolyEis P (residueCard F) (n - 1)) h) from by
        rw [Polynomial.resultant_map_map,
          Polynomial.natDegree_map_eq_of_injective (f := A.subtype) hAinj,
          Polynomial.natDegree_map_eq_of_injective (f := A.subtype) hAinj]]
    have hheart : (LTpolyEis P (residueCard F) (n - 1)).resultant h - 1 ∈
        Ideal.span {P ^ n} :=
      resultant_LTpolyEis_heart P hPirr n hn h hunit0
    have hmem_m : (LTpolyEis P (residueCard F) (n - 1)).resultant h - 1 ∈
        (maximalIdealOfIntegers F) ^ n := by
      rw [show maximalIdealOfIntegers F =
          Ideal.span ({P} : Set ↥(ValuativeRel.valuation F).integer) from
            Irreducible.maximalIdeal_eq hPirr, Ideal.span_singleton_pow]
      exact hheart
    have hmem_max : (LTpolyEis P (residueCard F) (n - 1)).resultant h - 1 ∈
        IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer :=
      (Ideal.pow_le_self (by omega : n ≠ 0)) hmem_m
    have hunit_res : IsUnit ((LTpolyEis P (residueCard F) (n - 1)).resultant h) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem0
      have h1 : (1 : ↥(ValuativeRel.valuation F).integer) ∈
          IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer := by
        have h2 := sub_mem hmem0 hmem_max
        have h3 : (LTpolyEis P (residueCard F) (n - 1)).resultant h -
            ((LTpolyEis P (residueCard F) (n - 1)).resultant h - 1) = 1 := by
          rw [sub_sub_cancel]
        rw [h3] at h2
        exact h2
      exact absurd ((Ideal.eq_top_iff_one _).mpr h1)
        (IsLocalRing.maximalIdeal.isMaximal ↥(ValuativeRel.valuation F).integer).ne_top
    obtain ⟨u, hu⟩ := hunit_res
    refine ⟨NK.LocalReciprocityLubinTate.Units.unitsIncl F u, ?_, ?_⟩
    · refine Subgroup.mem_map_of_mem (Units.map A.subtype.toMonoidHom) ?_
      rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff, hu]
      exact hmem_m
    · rw [NK.LocalReciprocityLubinTate.Units.unitsIncl, Units.coe_map, hu]
      exact hnorm.symm
  -- **the general step**: `z = z' · (-root)^m`
  obtain ⟨g, hgnat, hgz⟩ := exists_rep_adjoinRoot Em hEmon hEne (z : AdjoinRoot Em)
  have hgne : g ≠ 0 := by
    rintro rfl
    rw [show (AdjoinRoot.mk Em) (0 : Polynomial F) = 0 from map_zero _] at hgz
    exact (Units.ne_zero z) hgz
  have hgdeg : (g.map (algebraMap F (AdjoinRoot Em))).natDegree < d := by
    rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap F (AdjoinRoot Em)) hinj,
      ← hEdeg]
    exact hgnat
  have hg0' : g.map (algebraMap F (AdjoinRoot Em)) ≠ 0 := by
    intro h
    exact hgne ((Polynomial.map_injective (algebraMap F (AdjoinRoot Em)) hinj) (by
      rw [h, Polynomial.map_zero]))
  obtain ⟨m, hmw, i₀, hi₀mem, hmi₀, hmin⟩ :=
    valuation_aeval_eq_zpow w (AdjoinRoot.root Em)
      (algebraMap F (AdjoinRoot Em) (P : F)) d hd1 hroot_lt hroot_ne
      hroot_pow.symm (g.map (algebraMap F (AdjoinRoot Em))) hg0' hgdeg (K g) (hKval g)
  have hzw : w (z : AdjoinRoot Em) = (w (AdjoinRoot.root Em)) ^ m := by
    rw [hgz, ← AdjoinRoot.aeval_eq,
      ← Polynomial.aeval_map_algebraMap (AdjoinRoot Em) (AdjoinRoot.root Em) g]
    exact hmw
  have hnorm_neg : Algebra.norm F (-(AdjoinRoot.root Em)) = (πu : F) := by
    have h1 : -(AdjoinRoot.root Em) =
        algebraMap F (AdjoinRoot Em) (-1) * AdjoinRoot.root Em := by
      rw [show algebraMap F (AdjoinRoot Em) (-1) = -(1 : AdjoinRoot Em) from by
        rw [map_neg (algebraMap F (AdjoinRoot Em)) 1, map_one], neg_one_mul]
    have hfd : Module.finrank F (AdjoinRoot Em) = d := by
      rw [← hEdeg]
      exact (PowerBasis.finrank (AdjoinRoot.powerBasis hEmon.ne_zero)).trans
        (AdjoinRoot.powerBasis_dim hEmon.ne_zero)
    have hrootnorm : Algebra.norm F (AdjoinRoot.root Em) = (-1 : F) ^ d * (πu : F) := by
      have h := LubinTate.norm_root_LTpolyEis F P hPirr (residueCard F) (n - 1) hq2
      rw [show LTpolyEis (↑P) (residueCard F) (n - 1) = Em from by simp only [Em, hPcoe]] at h
      rw [h, hPcoe]
    rw [h1, map_mul, Algebra.norm_algebraMap, hfd, hrootnorm]
    rw [← mul_assoc, ← pow_add]
    rw [show d + d = 2 * d from by ring, pow_mul, neg_one_sq, one_pow, one_mul]
  let v : (AdjoinRoot Em)ˣ := Units.mk0 (-(AdjoinRoot.root Em)) (neg_ne_zero.mpr hroot_ne)
  have hv_coe : (v : AdjoinRoot Em) = -(AdjoinRoot.root Em) := rfl
  have hv_w : w (v : AdjoinRoot Em) = w (AdjoinRoot.root Em) := by
    rw [hv_coe, Valuation.map_neg]
  have hv0 : (v : AdjoinRoot Em) ^ m ≠ 0 := by
    rw [hv_coe]
    exact zpow_ne_zero m (neg_ne_zero.mpr hroot_ne)
  have hvNm : (Units.map (Algebra.norm F : AdjoinRoot Em →* F)) v = πu := by
    refine Units.ext ?_
    rw [Units.coe_map, hv_coe]
    exact hnorm_neg
  have hzw' : w ((z : AdjoinRoot Em) * ((v : AdjoinRoot Em) ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_zpow₀, hv_w, hzw]
    exact mul_inv_cancel₀ (zpow_ne_zero m hβne)
  obtain ⟨u₁, hu₁mem, hu₁x⟩ := key _ hzw'
  have hnorm_eq : Algebra.norm F (z : AdjoinRoot Em) =
      (πu : F) ^ m * Algebra.norm F ((z : AdjoinRoot Em) * ((v : AdjoinRoot Em) ^ m)⁻¹) := by
    have hz_eq : (z : AdjoinRoot Em) = ((z : AdjoinRoot Em) * ((v : AdjoinRoot Em) ^ m)⁻¹) *
        (v : AdjoinRoot Em) ^ m := by
      rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one]
    conv_lhs => rw [hz_eq]
    rw [map_mul, mul_comm]
    congr 1
    rw [show (v : AdjoinRoot Em) ^ m = (↑(v ^ m) : AdjoinRoot Em) from
        (Units.val_zpow_eq_zpow_val v m).symm,
      ← Units.coe_map (Algebra.norm F : AdjoinRoot Em →* F),
      map_zpow (Units.map (Algebra.norm F : AdjoinRoot Em →* F)) v m, hvNm,
      Units.val_zpow_eq_zpow_val]
  refine Subgroup.mem_sup.mpr ⟨πu ^ m, Subgroup.zpow_mem (Subgroup.zpowers πu)
      (Subgroup.mem_zpowers πu) m, u₁, hu₁mem, ?_⟩
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hu₁x, Units.coe_map]
  exact hnorm_eq.symm

/-! ## The target -/

/-- Honda's norm computation, the hard `⊆` half: for a uniformiser `πu` of a char-0 nonarchimedean
local field `F` and `n ≥ 1`, the norm group of the Lubin-Tate level `K_n = LTLevel F πu (residueCard F) n`
is contained in `⟨πu⟩ · U^n`; equivalently `Nm(𝒪[K_n]ˣ) ⊆ 1 + 𝔪^n`.

Suggested route (elementary: resultants, residue-field Frobenius, Newton identities; no formal group
law and no power-series Coleman operator).  Take `P` irreducible in `𝒪[F]` with `(P:F) = (πu:F)`,
`q = residueCard F`, `f = LTpoly P q`, `E := LTpolyEis P q (n-1)` (monic Eisenstein of degree
`(q-1)q^{n-1}`, minimal polynomial of a primitive division point `y`, and `K_n = F(y)`).

Heart (useful auxiliary lemma, delegated separately as
`NK.LocalReciprocityLubinTate.Unramified.resultant_LTpolyEis_sub_one_mem_span`, import it if it is
already on disk): for `g` in `𝒪[F][X]` with `g.coeff 0` a unit one has
`Polynomial.resultant E g - 1 ∈ Ideal.span {P^n}`.  Its proof: the operator
`R(h)(Y) = Res_X(f(X)-Y, h(X))` satisfies `R(h) ≡ h` mod `P` (since mod `P` the roots of
`f(X)-Y` are those of `X^q - Y`, and the residue field is `𝔽_q`), and the gain
`h ≡ 1 mod P^k ⟹ R(h) ≡ 1 mod P^{k+1}` (Newton's identities: `Σ_{f(α)=Y} α^j ∈ P·𝒪[F][Y]` for
`j ≥ 1`); iterating on `h = R(g)·g⁻¹` and using `Res(f^{(i)}, g) = ∏_{Λ_i} g` together with
`f^{(n)} = E·f^{(n-1)}` gives the claim.

Then: `Algebra.norm F (aeval y g) = Polynomial.resultant E g` for `y` a primitive `π^n`-division
point (the conjugates of `y` are the roots of `E`), and `𝒪[F][y] = 𝒪[K_n]` (from `Nm(y) = P`,
`norm_root_LTpolyEis`), so `Nm(𝒪[K_n]ˣ) ⊆ U^n`; with `Nm(y) = P` and `K_nˣ = ⟨y⟩·𝒪[K_n]ˣ` this
gives `Nm(K_nˣ) ⊆ ⟨P⟩·U^n = ⟨πu⟩·U^n`. -/
theorem normGroup_LTLevel_le_higherUnits_sup (F : Type u) [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) (n : ℕ) (hn : 1 ≤ n) :
    NK.LocalReciprocity.normGroup F
        ↥(NK.LocalReciprocityLubinTate.LTLevel F (πu : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n) ≤
      Subgroup.zpowers πu ⊔ NK.LocalReciprocityLubinTate.higherUnits F n := by
  classical
  have hq2 : 2 ≤ residueCard F := two_le_residueCard F
  have hq1 : 1 ≤ residueCard F := by omega
  let Em : Polynomial F := LTpolyEis (πu : F) (residueCard F) (n - 1)
  obtain ⟨hEmon, hEdeg0, hEc0, _⟩ :=
    LubinTate.LTpolyEis_shape (πu : F) (residueCard F) (n - 1) hq2
  have hEdeg : Em.natDegree = (residueCard F - 1) * residueCard F ^ (n - 1) := hEdeg0
  obtain ⟨P, hPirr, hPcoe⟩ := exists_irreducible_natCast_of_isUniformizer F πu hπ
  have hEirr : Irreducible Em := by
    have h1 : Em = LTpolyEis (P : F) (residueCard F) (n - 1) := by
      simp only [Em, ← hPcoe]
    rw [h1]
    exact irreducible_LTpolyEis F P hPirr (residueCard F) (n - 1) hq2
  haveI : Fact (Irreducible Em) := ⟨hEirr⟩
  -- the primitive division point generating the level
  have hdegpos : Em.degree ≠ 0 := by
    have hpos : 0 < (residueCard F - 1) * residueCard F ^ (n - 1) :=
      Nat.mul_pos (by omega) (pow_pos (by omega) _)
    rw [Polynomial.degree_eq_natDegree hEmon.ne_zero]
    exact_mod_cast (by omega : Em.natDegree ≠ 0)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) Em hdegpos
  have hymem : y ∈ LTdivisionSet F (πu : F) (residueCard F) n := by
    have hstep : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [LTdivisionSet,
      Polynomial.mem_rootSet_of_ne (LTpolyIter_ne_zero (πu : F) (residueCard F) n hq2)]
    show (Polynomial.aeval y) (LTpolyIter (πu : F) (residueCard F) n) = 0
    rw [← hstep, LTpolyIter_succ_eq_mul (πu : F) (residueCard F) (n - 1) hq1,
      Polynomial.aeval_mul]
    show (Polynomial.aeval y) Em * (Polynomial.aeval y)
      (LTpolyIter (πu : F) (residueCard F) (n - 1)) = 0
    rw [hy, zero_mul]
  have hmin : minpoly F y = Em := (minpoly.eq_of_irreducible_of_monic hEirr hy hEmon).symm
  haveI : FiniteDimensional F ↥(LTLevel F (πu : F) (residueCard F) n) :=
    LubinTate.finiteDimensional_LTLevel F (πu : F) (residueCard F) n hq2
  have hspan : IntermediateField.adjoin F ({y} : Set (AlgebraicClosure F)) =
      LTLevel F (πu : F) (residueCard F) n := by
    refine IntermediateField.eq_of_le_of_finrank_eq
      (IntermediateField.adjoin_simple_le_iff.mpr
        (LTdivisionSet_subset_LTLevel F (πu : F) (residueCard F) n hymem)) ?_
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y), hmin, hEdeg,
      finrank_LTLevel_eq_of_isUniformizer F πu hπ n hn]
  have e : AdjoinRoot Em ≃ₐ[F] ↥(LTLevel F (πu : F) (residueCard F) n) :=
    (hmin ▸ IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsIntegral.isIntegral y)).trans
      (IntermediateField.equivOfEq hspan)
  have hmem : NK.LocalReciprocity.normGroup F (AdjoinRoot Em) ≤
      Subgroup.zpowers πu ⊔ higherUnits F n := by
    rw [NK.LocalReciprocity.normGroup_eq_range]
    rintro x ⟨z, rfl⟩
    exact norm_units_adjoinRoot_le F πu hπ n hn z
  rw [← NK.LocalReciprocity.normGroup_eq_of_algEquiv e]
  exact hmem

end

end NK.LocalReciprocityLubinTate.Unramified
