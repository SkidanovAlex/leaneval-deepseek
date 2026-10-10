import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.DVRMaximal
import Submission.Work.MotC2.DVRPrime.MemOrInvMem
import Submission.Work.MotC2.InfAux
import Submission.Work.MotC2.InfPlaceLocalization
import Submission.Work.MotC2.infPlace_nonunit_eq_infW_mul
import Submission.Work.MotC2Cls.Setup
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.algebraMap_smul_eq_aeval
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.ConjFunc
import Submission.Work.MotC2.NeTwoRatFuncSqMul
import Submission.Work.MotC2.NeTwoSquarefreeCubic
import Submission.Work.MotC2.CharTwoCrux
import Submission.Work.MotC2.EllipticCharTwoNonsingular
import Submission.Work.MotC2.CharTwoNormCrux
import Submission.Work.MotC2.NormNeTwoCrux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

variable {L : Type*} [Field L]

section Place

variable (E : WeierstrassCurve L) [E.IsElliptic]

/-- `infPlace E` is a discrete valuation ring (the local ring of the point at infinity). -/
theorem infPlace_isDiscreteValuationRing : IsDiscreteValuationRing ↥(infPlace E) := by
  haveI := InfLoc.instIsNoetherianRingInfLoc E
  haveI := InfLoc.instIsLocalRingInfLoc E
  refine (IsDiscreteValuationRing.TFAE ↥(infPlace E) (InfLoc.not_isField E)).out 5 1 |>.mp ?_
  -- the maximal ideal is principal: `u = 1/x` is a non-unit, hence a multiple of `w = y/x²`
  have hu : algebraMap (infCoordRing E) ↥(infPlace E) (InfLoc.u E) ∈
      IsLocalRing.maximalIdeal ↥(infPlace E) := InfLoc.algebraMap_u_mem_maximalIdeal E
  have hnonunit : ¬ ∃ g : Func E, g ∈ infPlace E ∧ infU E * g = 1 := by
    rintro ⟨g, hg, hg1⟩
    have hg1' : algebraMap (infCoordRing E) ↥(infPlace E) (InfLoc.u E) *
        (⟨g, hg⟩ : ↥(infPlace E)) = 1 := by
      apply Subtype.ext
      simpa [InfLoc.algebraMap_u_val] using hg1
    exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_iff_exists_inv.mpr ⟨_, hg1'⟩)) hu
  obtain ⟨g, hg, hug⟩ := infPlace_nonunit_eq_infW_mul L E (infU E)
    (InfAux.mem_infPlace_of_mem E (InfLoc.u E)) hnonunit
  have hug' : algebraMap (infCoordRing E) ↥(infPlace E) (InfLoc.u E) =
      algebraMap (infCoordRing E) ↥(infPlace E) (InfLoc.w E) * (⟨g, hg⟩ : ↥(infPlace E)) := by
    apply Subtype.ext
    simpa [InfLoc.algebraMap_u_val, InfLoc.algebraMap_w_val] using hug
  refine ⟨algebraMap (infCoordRing E) ↥(infPlace E) (InfLoc.w E), ?_⟩
  rw [InfLoc.maximalIdeal_eq_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [hug']
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    · exact Ideal.subset_span rfl
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- `f : L(E)` is a quotient of two elements of the local ring `infPlace E`. -/
private def IsFracO (f : Func E) : Prop :=
  ∃ a b : ↥(infPlace E), (b : Func E) ≠ 0 ∧ f * (b : Func E) = (a : Func E)

private lemma isFracO_algebraMap (c : L) :
    IsFracO E (algebraMap L (Func E) c) :=
  ⟨⟨algebraMap L (Func E) c, Subalgebra.algebraMap_mem (infPlace E) c⟩, 1, one_ne_zero,
    by show algebraMap L (Func E) c * 1 = algebraMap L (Func E) c
       rw [mul_one]⟩

private lemma isFracO_add {f g : Func E} (hf : IsFracO E f) (hg : IsFracO E g) :
    IsFracO E (f + g) := by
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := hf
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := hg
  have hb₁' : (b₁ : Func E) ≠ 0 := by simpa using hb₁
  have hb₂' : (b₂ : Func E) ≠ 0 := by simpa using hb₂
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, ?_, ?_⟩
  · show (b₁ : Func E) * (b₂ : Func E) ≠ 0
    exact mul_ne_zero hb₁' hb₂'
  · show (f + g) * ((b₁ : Func E) * (b₂ : Func E)) =
        (a₁ : Func E) * (b₂ : Func E) + (a₂ : Func E) * (b₁ : Func E)
    linear_combination (norm := refl_ring1) (b₂ : Func E) * h₁ + (b₁ : Func E) * h₂

private lemma isFracO_mul {f g : Func E} (hf : IsFracO E f) (hg : IsFracO E g) :
    IsFracO E (f * g) := by
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := hf
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := hg
  have hb₁' : (b₁ : Func E) ≠ 0 := by simpa using hb₁
  have hb₂' : (b₂ : Func E) ≠ 0 := by simpa using hb₂
  refine ⟨a₁ * a₂, b₁ * b₂, ?_, ?_⟩
  · show (b₁ : Func E) * (b₂ : Func E) ≠ 0
    exact mul_ne_zero hb₁' hb₂'
  · show (f * g) * ((b₁ : Func E) * (b₂ : Func E)) = (a₁ : Func E) * (a₂ : Func E)
    linear_combination (norm := refl_ring1) (g : Func E) * (b₂ : Func E) * h₁ + (a₁ : Func E) * h₂

private lemma isFracO_inv {g : Func E} (hg : IsFracO E g) (hg0 : g ≠ 0) :
    IsFracO E g⁻¹ := by
  obtain ⟨a, b, hb, hab⟩ := hg
  have hb' : (b : Func E) ≠ 0 := by simpa using hb
  have ha : (a : Func E) ≠ 0 := by
    intro h0
    have h3 : g * (b : Func E) = 0 := by rw [hab, h0]
    exact hg0 ((mul_eq_zero.mp h3).resolve_right hb')
  refine ⟨b, a, ?_, ?_⟩
  · simpa using ha
  · show g⁻¹ * (a : Func E) = (b : Func E)
    rw [← hab, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]

private lemma isFracO_div {f g : Func E} (hf : IsFracO E f) (hg : IsFracO E g) (hg0 : g ≠ 0) :
    IsFracO E (f / g) := by
  rw [div_eq_mul_inv]
  exact isFracO_mul E hf (isFracO_inv E hg hg0)

private lemma isFracO_infU : IsFracO E (infU E) :=
  ⟨⟨infU E, InfAux.mem_infPlace_of_mem E ⟨infU E, InfAux.infU_mem_infCoordRing E⟩⟩,
    1, one_ne_zero, by show infU E * 1 = infU E; rw [mul_one]⟩

private lemma isFracO_infW : IsFracO E (infW E) :=
  ⟨⟨infW E, InfAux.mem_infPlace_of_mem E ⟨infW E, InfAux.infW_mem_infCoordRing E⟩⟩,
    1, one_ne_zero, by show infW E * 1 = infW E; rw [mul_one]⟩

private lemma isFracO_inv_infU : IsFracO E ((infU E)⁻¹) :=
  ⟨1, ⟨infU E, InfAux.mem_infPlace_of_mem E ⟨infU E, InfAux.infU_mem_infCoordRing E⟩⟩,
    by show infU E ≠ 0; simpa [infU] using inv_ne_zero (genX_ne_zero E),
    by show (infU E)⁻¹ * infU E = 1
       rw [inv_mul_cancel₀ (show infU E ≠ 0 by
         simpa [infU] using inv_ne_zero (genX_ne_zero E))]⟩

private noncomputable def fracSub : Subalgebra L (Func E) where
  carrier := {f | IsFracO E f}
  mul_mem' := fun ha hb => isFracO_mul E ha hb
  one_mem' := by simpa using isFracO_algebraMap E (1 : L)
  add_mem' := fun ha hb => isFracO_add E ha hb
  zero_mem' := by simpa using isFracO_algebraMap E (0 : L)
  algebraMap_mem' := isFracO_algebraMap E

/-- `L(E)` is the fraction field of `infPlace E`. -/
theorem infPlace_isFractionRing :
    ∀ f : Func E, ∃ a b : ↥(infPlace E),
      (b : Func E) ≠ 0 ∧ f * (b : Func E) = (a : Func E) := by
  intro f
  have hS : Algebra.adjoin L ({infU E, infW E, (infU E)⁻¹} : Set (Func E)) ≤ fracSub E := by
    refine Algebra.adjoin_le_iff.mpr ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact isFracO_infU E
    · exact isFracO_infW E
    · exact isFracO_inv_infU E
  obtain ⟨r, s, hs0, hfs⟩ := IsFractionRing.div_surjective (Coord E) f
  have hr : IsFracO E (algebraMap (Coord E) (Func E) r) :=
    hS (InfLoc.algebraMap_coord_mem E r)
  have hs : IsFracO E (algebraMap (Coord E) (Func E) s) :=
    hS (InfLoc.algebraMap_coord_mem E s)
  have hs0' : (algebraMap (Coord E) (Func E) s : Func E) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs0
  have hdiv : IsFracO E (algebraMap (Coord E) (Func E) r / algebraMap (Coord E) (Func E) s) :=
    isFracO_div E hr hs hs0'
  rw [hfs] at hdiv
  exact hdiv

/-- Every non-zero element of `L(E)` or its inverse lies in `infPlace E`. -/
theorem infPlace_or_inv (f : Func E) (hf : f ≠ 0) :
    f ∈ infPlace E ∨ f⁻¹ ∈ infPlace E := by
  haveI : IsDiscreteValuationRing ↥(infPlace E) := infPlace_isDiscreteValuationRing E
  haveI : ValuationRing ↥(infPlace E) := inferInstance
  exact DVRPrime.MemOrInvMem (infPlace E) (infPlace_isFractionRing E) hf

/-- The point at infinity `O`, as a valuation subring of `L(E)`. -/
noncomputable def placeAtO : ValuationSubring (Func E) :=
  ValuationSubring.ofSubring (infPlace E).toSubring fun x => by
    by_cases hx : x = 0
    · exact Or.inl (by rw [hx]; exact (infPlace E).zero_mem)
    · rcases infPlace_or_inv E x hx with h | h
      · exact Or.inl (Subalgebra.mem_toSubring.mpr h)
      · exact Or.inr (Subalgebra.mem_toSubring.mpr h)

/-- `x = genX E` is not regular at the point at infinity: its pole there has order `2`. -/
theorem genX_notMem_infPlace : genX E ∉ infPlace E := by
  intro hx
  obtain ⟨a, b, hb, hab⟩ := (InfAux.infPlace_mem_iff E (genX E)).mp hx
  apply hb
  rw [← InfAux.mem_infIdealR_iff E b]
  have hb' : ((b : Func E)) = infU E * (a : Func E) := by
    calc (b : Func E) = (infU E * genX E) * (b : Func E) := by rw [infU_mul_genX E, one_mul]
      _ = infU E * (genX E * (b : Func E)) := by ring
      _ = infU E * (a : Func E) := by rw [hab]
  rw [hb']
  have hu : infU E ∈ infIdeal E := Submodule.subset_span (by simp)
  rw [show infU E * (a : Func E) = a • infU E from by
    rw [infCoordRing_smul_eq_mul, mul_comm]]
  exact Submodule.smul_mem _ a hu

/-- If a place of `L(E)/L` contains the local ring `O` of the point at infinity then it is `O`
itself, unless it is the whole field (which the second hypothesis excludes). -/
theorem eq_of_le_of_ne_top_infPlace (V : ValuationSubring (Func E))
    (hle : placeAtO E ≤ V) (hVtop : V ≠ ⊤) : V = placeAtO E := by
  haveI : IsDiscreteValuationRing ↥(infPlace E) := infPlace_isDiscreteValuationRing E
  have hle' : (infPlace E).toSubring ≤ V.toSubring := fun z hz => hle hz
  -- the contraction of the maximal ideal of `V` to `O` is a prime ideal of `O`
  set P : Ideal ↥(infPlace E) :=
    Ideal.comap (Subring.inclusion hle') (IsLocalRing.maximalIdeal ↥V) with hPdef
  have hPprime : P.IsPrime := Ideal.IsPrime.comap (Subring.inclusion hle')
  rcases dvr_prime_eq_bot_or_maximalIdeal P hPprime with hP | hP
  · -- every non-zero element of `O` is a unit of `V`, hence `L(E) = Frac O ⊆ V`
    exfalso
    have hunit : ∀ a : ↥(infPlace E), a ≠ 0 → IsUnit (⟨(a : Func E), hle' a.2⟩ : ↥V) := by
      intro a ha
      by_contra hnu
      have hmem : (⟨(a : Func E), hle' a.2⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hPmem : a ∈ P := Ideal.mem_comap.mpr hmem
      rw [hP] at hPmem
      exact ha (Ideal.mem_bot.mp hPmem)
    have hall : ∀ f : Func E, f ∈ V := by
      intro f
      by_cases hf : f = 0
      · rw [hf]; exact V.zero_mem
      obtain ⟨a, b, hb0, hbf⟩ := infPlace_isFractionRing E f
      have hbne : b ≠ 0 := by simpa using hb0
      obtain ⟨w, hw⟩ := (hunit b hbne).exists_right_inv
      have hbcoe : (b : Func E) * ((w : ↥V) : Func E) = 1 := by
        have h := congrArg (fun z : ↥V => (z : Func E)) hw
        simpa using h
      have hbinv : (b : Func E)⁻¹ ∈ V := by
        rw [inv_eq_of_mul_eq_one_right hbcoe]
        exact w.2
      have hfin : f = (a : Func E) * (b : Func E)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hb0]
        exact hbf
      rw [hfin]
      exact mul_mem (hle' a.2) hbinv
    exact hVtop (by
      apply ValuationSubring.ext
      intro x
      exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => hall x⟩)
  · -- `P = 𝔪_O`, so a `v ∈ V` with `v ∉ O` would have `v⁻¹ ∈ 𝔪_O ⊆ 𝔪_V`, a non-unit of `V`
    apply ValuationSubring.ext
    intro v
    refine ⟨fun hv => ?_, fun hv => hle' hv⟩
    by_contra hvO
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hvO (Subalgebra.mem_toSubring.mpr ((infPlace E).zero_mem))
    rcases infPlace_or_inv E v hv0 with h | h
    · exact hvO h
    · have hnotunit : ¬ IsUnit (⟨v⁻¹, h⟩ : ↥(infPlace E)) := by
        rintro hunit
        obtain ⟨w, hw⟩ := hunit.exists_right_inv
        apply hvO
        have h1 : v⁻¹ * (w : Func E) = 1 := by
          have h := congrArg (fun z : ↥(infPlace E) => (z : Func E)) hw
          simpa using h
        have h2 : v = (w : Func E) := by
          rw [← inv_inv v]
          exact inv_eq_of_mul_eq_one_right h1
        rw [h2]
        exact w.2
      have hmemO : (⟨v⁻¹, h⟩ : ↥(infPlace E)) ∈ IsLocalRing.maximalIdeal ↥(infPlace E) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnotunit
      have hmemV : (⟨v⁻¹, hle' h⟩ : ↥V) ∈ IsLocalRing.maximalIdeal ↥V := by
        have hPmem : (⟨v⁻¹, h⟩ : ↥(infPlace E)) ∈ P := by
          rw [hP]; exact hmemO
        exact Ideal.mem_comap.mp hPmem
      have hunitV : IsUnit (⟨v⁻¹, hle' h⟩ : ↥V) := by
        refine isUnit_iff_exists_inv.mpr ⟨⟨v, hv⟩, ?_⟩
        apply Subtype.ext
        change v⁻¹ * v = 1
        rw [inv_mul_cancel₀ hv0]
      exact (IsLocalRing.notMem_maximalIdeal.mpr hunitV) hmemV

end Place

/-! ## The family of places other than `O` -/

section Family

variable (E : WeierstrassCurve L) [E.IsElliptic]

/-- The `L`-subalgebra of `L(E)` carried by a valuation subring `V` containing `L`. -/
noncomputable def valSub (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) : Subalgebra L (Func E) where
  carrier := V.toSubring
  mul_mem' := fun ha hb => V.toSubring.mul_mem ha hb
  one_mem' := V.toSubring.one_mem
  add_mem' := fun ha hb => V.toSubring.add_mem ha hb
  zero_mem' := V.toSubring.zero_mem
  algebraMap_mem' := hL

/-- The places of `L(E)/L` other than the point at infinity `O` and other than the whole field. -/
def placeFamily : Set (Subalgebra L (Func E)) :=
  {W | ∃ (V : ValuationSubring (Func E)) (hL : ∀ c : L, algebraMap L (Func E) c ∈ V),
    V ≠ ⊤ ∧ V ≠ placeAtO E ∧ W = valSub E V hL}

/-- The intersection of all places of `L(E)/L` except the point at infinity. -/
noncomputable def placeInter : Subalgebra L (Func E) :=
  ⨅ W : {W : Subalgebra L (Func E) // W ∈ placeFamily E}, W.1

/-- If `genX E` is regular at the place `V`, then `genY E` is too. -/
theorem genY_mem_of_genX_mem (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hx : genX E ∈ V) : genY E ∈ V := by
  by_cases hy : genY E = 0
  · rw [hy]; exact V.zero_mem
  · rcases V.mem_or_inv_mem (genY E) with h | h
    · exact h
    · -- `y = (x³ + a₂x² + a₄x + a₆)·y⁻¹ - (a₁x + a₃)` follows from `y² + (a₁x+a₃)·y = x³+…`
      set C : Func E := (genX E) ^ 3 + algebraMap L (Func E) E.a₂ * (genX E) ^ 2 +
        algebraMap L (Func E) E.a₄ * genX E + algebraMap L (Func E) E.a₆ with hCdef
      set Ee : Func E := algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃
        with hEedef
      have hCmem : C ∈ V := by
        rw [hCdef]
        exact add_mem (add_mem (add_mem (pow_mem hx 3)
          (mul_mem (hL _) (pow_mem hx 2))) (mul_mem (hL _) hx)) (hL _)
      have hEmem : Ee ∈ V := by
        rw [hEedef]
        exact add_mem (mul_mem (hL _) hx) (hL _)
      have hy2 : genY E * genY E + Ee * genY E = C := by
        rw [hCdef, hEedef, ← genY_sq_relation E]
        refl_ring1
      have h1 : (C * (genY E)⁻¹ - Ee) * genY E = genY E * genY E := by
        rw [sub_mul, mul_assoc, inv_mul_cancel₀ hy, mul_one, ← hy2]
        refl_ring1
      rw [(mul_right_cancel₀ hy h1).symm]
      exact sub_mem (mul_mem hCmem h) hEmem

/-- If the place `V` does not contain `genX E`, then it contains the chart-at-infinity coordinate
ring `L[1/x, y/x²]`. -/
theorem infCoordRing_le_of_notMem_genX (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hx : genX E ∉ V) :
    infCoordRing E ≤ valSub E V hL := by
  have hu : infU E ∈ V := by
    rcases V.mem_or_inv_mem (genX E) with h | h
    · exact absurd h hx
    · simpa [infU] using h
  have hw : infW E ∈ V := by
    by_cases hw0 : infW E = 0
    · rw [hw0]; exact V.zero_mem
    · rcases V.mem_or_inv_mem (infW E) with h | h
      · exact h
      · -- `w = (u + a₂u² + a₄u³ + a₆u⁴)·w⁻¹ - (a₁u + a₃u²)` from the chart relation
        set A : Func E := infU E + algebraMap L (Func E) E.a₂ * (infU E) ^ 2 +
          algebraMap L (Func E) E.a₄ * (infU E) ^ 3 +
          algebraMap L (Func E) E.a₆ * (infU E) ^ 4 with hAdef
        set B : Func E := algebraMap L (Func E) E.a₁ * infU E +
          algebraMap L (Func E) E.a₃ * (infU E) ^ 2 with hBdef
        have hAmem : A ∈ V := by
          rw [hAdef]
          exact add_mem (add_mem (add_mem hu (mul_mem (hL _) (pow_mem hu 2)))
            (mul_mem (hL _) (pow_mem hu 3))) (mul_mem (hL _) (pow_mem hu 4))
        have hBmem : B ∈ V := by
          rw [hBdef]
          exact add_mem (mul_mem (hL _) hu) (mul_mem (hL _) (pow_mem hu 2))
        have hw2 : infW E * infW E + B * infW E = A := by
          rw [hAdef, hBdef, ← infW_sq_relation E]
          refl_ring1
        have h1 : (A * (infW E)⁻¹ - B) * infW E = infW E * infW E := by
          rw [sub_mul, mul_assoc, inv_mul_cancel₀ hw0, mul_one, ← hw2]
          refl_ring1
        rw [(mul_right_cancel₀ hw0 h1).symm]
        exact sub_mem (mul_mem hAmem h) hBmem
  rw [infCoordRing]
  refine Algebra.adjoin_le_iff.mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact hu
  · exact hw

/-- `w = infW E` is a non-unit at a place `V` that does not contain `x`. -/
private lemma infW_mem_nonunits_of_notMem_genX (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hx : genX E ∉ V) :
    infW E ∈ V.nonunits := by
  have hring_le : infCoordRing E ≤ valSub E V hL := infCoordRing_le_of_notMem_genX E V hL hx
  have hu : infU E ∈ V := by
    rcases V.mem_or_inv_mem (genX E) with h | h
    · exact absurd h hx
    · simpa [infU] using h
  have hw : infW E ∈ V := hring_le (Algebra.subset_adjoin (by simp))
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases hw0 : infW E = 0
  · exact Or.inl hw0
  · refine Or.inr fun hwinv => hx ?_
    set h₀ : Func E := 1 + algebraMap L (Func E) E.a₂ * infU E +
      algebraMap L (Func E) E.a₄ * (infU E) ^ 2 + algebraMap L (Func E) E.a₆ * (infU E) ^ 3 -
      (algebraMap L (Func E) E.a₁ + algebraMap L (Func E) E.a₃ * infU E) * infW E with h₀def
    have h₀mem : h₀ ∈ V := by
      rw [h₀def]
      exact sub_mem (add_mem (add_mem (add_mem V.one_mem
        (mul_mem (hL _) hu)) (mul_mem (hL _) (pow_mem hu 2)))
        (mul_mem (hL _) (pow_mem hu 3)))
        (mul_mem (add_mem (hL _) (mul_mem (hL _) hu)) hw)
    -- `u * h₀ = w²`
    have hsq : infU E * h₀ = infW E * infW E := by
      have hrel2 : infW E * infW E +
          (algebraMap L (Func E) E.a₁ * infU E + algebraMap L (Func E) E.a₃ * (infU E) ^ 2) *
            infW E = (infU E + algebraMap L (Func E) E.a₂ * (infU E) ^ 2 +
            algebraMap L (Func E) E.a₄ * (infU E) ^ 3 +
            algebraMap L (Func E) E.a₆ * (infU E) ^ 4) := by
        rw [← infW_sq_relation E]
        refl_ring1
      have h2 : infU E * h₀ = (infU E + algebraMap L (Func E) E.a₂ * (infU E) ^ 2 +
          algebraMap L (Func E) E.a₄ * (infU E) ^ 3 +
          algebraMap L (Func E) E.a₆ * (infU E) ^ 4) -
          (algebraMap L (Func E) E.a₁ * infU E + algebraMap L (Func E) E.a₃ * (infU E) ^ 2) *
            infW E := by
        rw [h₀def]; ring
      rw [h2, ← hrel2]
      refl_ring1
    -- hence `x = h₀ * (w⁻¹)²`
    have hxeq : genX E = h₀ * ((infW E)⁻¹) ^ 2 := by
      have h1 : h₀ = genX E * (infW E * infW E) := by
        calc h₀ = (infU E * genX E) * h₀ := by rw [infU_mul_genX E, one_mul]
          _ = genX E * (infU E * h₀) := by ring
          _ = genX E * (infW E * infW E) := by rw [hsq]
      rw [h1, mul_assoc]
      have h2 : (infW E * infW E) * ((infW E)⁻¹) ^ 2 = 1 := by
        have h3 : (infW E * infW E) * ((infW E)⁻¹ * (infW E)⁻¹) =
            (infW E * (infW E)⁻¹) * (infW E * (infW E)⁻¹) := by ring
        rw [pow_two, h3, mul_inv_cancel₀ hw0, mul_one]
      rw [h2, mul_one]
    rw [hxeq]
    exact mul_mem h₀mem (pow_mem hwinv 2)

/-- If the place `V` does not contain `genX E`, then the inverse of every element of the
chart-at-infinity coordinate ring outside `infIdeal E` lies in `V`. -/
theorem inv_mem_of_mem_infCoordRing_of_notMem_infIdeal (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hx : genX E ∉ V) {r : Func E}
    (hr : r ∈ infCoordRing E) (hnot : r ∉ infIdeal E) : r⁻¹ ∈ V := by
  have hring_le : infCoordRing E ≤ valSub E V hL := infCoordRing_le_of_notMem_genX E V hL hx
  have hring_le' : (infCoordRing E).toSubring ≤ V.toSubring := fun z hz => hring_le hz
  have hu : infU E ∈ V := by
    rcases V.mem_or_inv_mem (genX E) with h | h
    · exact absurd h hx
    · simpa [infU] using h
  have hw : infW E ∈ V := hring_le (Algebra.subset_adjoin (by simp))
  set inc : ↥(infCoordRing E) →+* ↥V := Subring.inclusion hring_le' with incdef
  have hu_nu : inc (⟨infU E, InfAux.infU_mem_infCoordRing E⟩ : ↥(infCoordRing E)) ∈
      IsLocalRing.maximalIdeal ↥V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    rw [ValuationSubring.mem_nonunits_iff_or]
    refine Or.inr fun h => hx ?_
    have h2 : genX E =
        (((inc (⟨infU E, InfAux.infU_mem_infCoordRing E⟩ : ↥(infCoordRing E))) : ↥V) :
          Func E)⁻¹ := by
      rw [show (((inc (⟨infU E, InfAux.infU_mem_infCoordRing E⟩ : ↥(infCoordRing E))) : ↥V) :
          Func E) = (genX E)⁻¹ from rfl]
      rw [inv_inv]
    rw [h2]
    exact h
  have hw_nu : inc (⟨infW E, InfAux.infW_mem_infCoordRing E⟩ : ↥(infCoordRing E)) ∈
      IsLocalRing.maximalIdeal ↥V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have h2 : (((inc (⟨infW E, InfAux.infW_mem_infCoordRing E⟩ : ↥(infCoordRing E))) : ↥V) :
        Func E) = infW E := rfl
    rw [h2]
    exact infW_mem_nonunits_of_notMem_genX E V hL hx
  have hleI : InfAux.infIdealR E ≤ Ideal.comap inc (IsLocalRing.maximalIdeal ↥V) := by
    intro y hy
    rw [InfAux.mem_infIdealR_iff'] at hy
    obtain ⟨a, b, hab⟩ := hy
    rw [Ideal.mem_comap, ← hab, map_add, map_mul, map_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu_nu) (Ideal.mul_mem_left _ _ hw_nu)
  have hcomap_ne : Ideal.comap inc (IsLocalRing.maximalIdeal ↥V) ≠ ⊤ := by
    intro htop
    have h2 : (1 : ↥(infCoordRing E)) ∈ Ideal.comap inc (IsLocalRing.maximalIdeal ↥V) := by
      rw [htop]; exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h2
    exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h2
  have hcomap : InfAux.infIdealR E = Ideal.comap inc (IsLocalRing.maximalIdeal ↥V) :=
    (InfAux.isMaximal_infIdealR E).eq_of_le hcomap_ne hleI
  have hrI : (⟨r, hr⟩ : ↥(infCoordRing E)) ∉ InfAux.infIdealR E := fun h =>
    hnot ((InfAux.mem_infIdealR_iff E ⟨r, hr⟩).mpr h)
  have hrm : inc (⟨r, hr⟩ : ↥(infCoordRing E)) ∉ IsLocalRing.maximalIdeal ↥V := fun hmem =>
    hrI (hcomap ▸ Ideal.mem_comap.mpr hmem)
  obtain ⟨u, hu'⟩ := (IsLocalRing.notMem_maximalIdeal.mp hrm).exists_right_inv
  have h1 : r * (u : Func E) = 1 := by
    have h := congrArg (fun z : ↥V => (z : Func E)) hu'
    have h3 : ((inc (⟨r, hr⟩ : ↥(infCoordRing E)) * u : ↥V) : Func E) =
        ((inc (⟨r, hr⟩ : ↥(infCoordRing E)) : ↥V) : Func E) * (u : Func E) := rfl
    have h4 : ((inc (⟨r, hr⟩ : ↥(infCoordRing E)) : ↥V) : Func E) = r := rfl
    rw [h3, h4] at h
    simpa using h
  rw [inv_eq_of_mul_eq_one_right h1]
  exact u.2

/-- If the place `V` does not contain `genX E`, then it contains the local ring of `O`. -/
theorem infPlace_le_of_notMem_genX (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hx : genX E ∉ V) :
    infPlace E ≤ valSub E V hL := by
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro z (hz | hz)
  · exact infCoordRing_le_of_notMem_genX E V hL hx hz
  · obtain ⟨r, ⟨hr, hrn⟩, rfl⟩ := hz
    exact inv_mem_of_mem_infCoordRing_of_notMem_infIdeal E V hL hx hr hrn

/-- If `V` is a place of `L(E)/L` different from `O`, then `genX E` is regular at `V`. -/
theorem genX_mem_of_valRing (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hVtop : V ≠ ⊤) (hVO : V ≠ placeAtO E) :
    genX E ∈ V := by
  by_cases hxV : genX E ∈ V
  · exact hxV
  · exfalso
    have hle : infPlace E ≤ valSub E V hL := infPlace_le_of_notMem_genX E V hL hxV
    have hle' : placeAtO E ≤ V := fun x hxmem => hle (Subalgebra.mem_toSubring.mp hxmem)
    exact hVO (eq_of_le_of_ne_top_infPlace E V hle' hVtop)

/-- A place of `L(E)/L` different from `O` contains the affine coordinate ring `L[x,y]`. -/
theorem affRing_le_of_valRing (V : ValuationSubring (Func E))
    (hL : ∀ c : L, algebraMap L (Func E) c ∈ V) (hVtop : V ≠ ⊤) (hVO : V ≠ placeAtO E) :
    affRing E ≤ valSub E V hL := by
  have hx : genX E ∈ V := genX_mem_of_valRing E V hL hVtop hVO
  have hy : genY E ∈ V := genY_mem_of_genX_mem E V hL hx
  rw [Work.MotC2.affRing_eq_adjoin]
  refine Algebra.adjoin_le_iff.mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

/-- Every place different from `O` contains the affine coordinate ring. -/
theorem affRing_le_placeInter : affRing E ≤ placeInter E := by
  refine le_iInf ?_
  rintro ⟨W, V, hL, hVtop, hVO, rfl⟩
  exact affRing_le_of_valRing E V hL hVtop hVO

end Family

section Main

variable (E : WeierstrassCurve L) [E.IsElliptic]

/-- `L[x] ⊆ affRing E`. -/
private lemma norm_ax_le_affRing : Ax E ≤ affRing E := by
  rw [Ax, affRing]
  refine Algebra.adjoin_le ?_
  rintro z (rfl : z = genX E)
  exact Algebra.subset_adjoin ⟨coordX E, rfl⟩

private lemma norm_genY_mem_affRing : genY E ∈ affRing E := by
  rw [affRing_eq_adjoin]
  exact Algebra.subset_adjoin (by simp)

/-- Every element of `affRing E` is of the form `P(x) + Q(x)·y`. -/
private lemma norm_affRingBasisForm :
    ∀ z : Func E, z ∈ affRing E →
      ∃ P Q : Polynomial L, z = xPhi E P + xPhi E Q * genY E := by
  intro z hz
  have hle : affRing E ≤ (IsScalarTower.toAlgHom L (Coord E) (Func E)).range := by
    rw [affRing]
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simpa using ha⟩
  obtain ⟨c, rfl⟩ := hle hz
  obtain ⟨P, Q, hPQ⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) c
  refine ⟨P, Q, ?_⟩
  rw [← hPQ, map_add]
  change algebraMap (Coord E) (Func E) (P • (1 : Coord E)) +
      algebraMap (Coord E) (Func E) (Q • CoordinateRing.mk E Polynomial.X) =
      xPhi E P + xPhi E Q * genY E
  rw [(algebraMap_smul_eq_aeval L E P).1, (algebraMap_smul_eq_aeval L E Q).2]
  simp only [xPhi]

private lemma norm_xPhi_linCoef : xPhi E (linCoef E) = eK E := by
  simp [linCoef, eK, xPhi]

private lemma norm_xPhi_cubCoef : xPhi E (cubCoef E) = cK E := by
  simp [cubCoef, cK, xPhi]

/-- The affine coordinate ring `L[x,y]` is integrally closed in `L(E)`.

Write `z ∈ L(E)` as `z = r/s` with `r, s ∈ affRing E`, put `D = s·σ(s) ∈ L[x]` (where `σ` is the
conjugation `y ↦ -y - (a₁x+a₃)`), and write `z = (P + Q·y)/D` with `P, Q ∈ L[X]`.  Then
`p = P/D`, `q = Q/D` lie in `L(x)` and the trace `z + σ z = 2p - q·e` and the norm
`z·σ z = p² - p·q·e - q²·c` both lie in `L[x]`; the two valuation cruxes `CharTwoNormCrux`
(characteristic two) and `NormNeTwoCrux` (characteristic `≠ 2`) then yield `p, q ∈ L[x]`, so
`z = p + q·y ∈ affRing E`. -/
theorem affRing_integrallyClosed : IsIntegrallyClosedIn ↥((affRing E).toSubring) (Func E) := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro z hz
  change z ∈ (affRing E : Subalgebra L (Func E))
  change IsIntegral ↥(affRing E) z at hz
  obtain ⟨σ, hσinv, hσfix, hσy, hσring⟩ := ConjFunc L E
  have hxPhi_mem : ∀ P : Polynomial L, xPhi E P ∈ Ax E := by
    intro P
    rw [← xPhi_range E]
    exact ⟨P, rfl⟩
  have hσ_ax : ∀ a ∈ Ax E, σ a = a := by
    intro a ha
    rw [← xPhi_range E] at ha
    obtain ⟨P, rfl⟩ := ha
    exact hσfix P
  have hσy' : σ (genY E) = -genY E - eK E := by
    rw [hσy]; rfl
  have hzA : IsIntegral ↥(Ax E) z := isIntegral_Ax_of_isIntegral_affRing E hz
  have hσ_int : IsIntegral ↥(affRing E) (σ z) := by
    let σ' : ↥(affRing E) →+* ↥(affRing E) :=
      { toFun := fun a => ⟨σ (a : Func E), (hσring (a : Func E)).mp a.2⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp
        map_zero' := by ext; simp
        map_add' := by intro a b; ext; simp }
    have hcomp : (algebraMap ↥(affRing E) (Func E)).comp σ' =
        σ.toRingEquiv.toRingHom.comp (algebraMap ↥(affRing E) (Func E)) := by
      ext a; rfl
    exact IsIntegral.map_of_comp_eq σ' σ.toRingEquiv.toRingHom hcomp hz
  have hσA : IsIntegral ↥(Ax E) (σ z) := isIntegral_Ax_of_isIntegral_affRing E hσ_int
  -- write `z = r / s` with `r, s ∈ affRing E`
  obtain ⟨a, b, hb, hzab⟩ := IsFractionRing.div_surjective (Coord E) z
  set r : Func E := algebraMap (Coord E) (Func E) a with hrdef
  set s : Func E := algebraMap (Coord E) (Func E) b with hsdef
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hsσ0 : σ s ≠ 0 := by
    intro h
    have h1 : s = 0 := by rw [← hσinv s, h, map_zero]
    exact hs0 h1
  have hr_mem : r ∈ affRing E := by
    rw [hrdef]
    exact Algebra.subset_adjoin ⟨a, rfl⟩
  have hs_mem : s ∈ affRing E := by
    rw [hsdef]
    exact Algebra.subset_adjoin ⟨b, rfl⟩
  have hzrs : r / s = z := hzab
  have hsσ_mem : σ s ∈ affRing E := (hσring s).mp hs_mem
  obtain ⟨P', Q', hP'Q'⟩ := norm_affRingBasisForm E s hs_mem
  -- `D = s·σ(s) ∈ L[x]` and `D ≠ 0`
  have hD_mem : s * σ s ∈ Ax E := by
    have hσs : σ s = xPhi E P' - xPhi E Q' * eK E - xPhi E Q' * genY E := by
      rw [hP'Q', map_add, map_mul, hσ_ax _ (hxPhi_mem P'), hσ_ax _ (hxPhi_mem Q'), hσy']
      refl_ring1
    have key : (xPhi E P' + xPhi E Q' * genY E) *
          (xPhi E P' - xPhi E Q' * eK E - xPhi E Q' * genY E)
        = xPhi E P' ^ 2 - xPhi E P' * xPhi E Q' * eK E - (xPhi E Q') ^ 2 * cK E := by
      have h := y_sq E
      linear_combination (norm := refl_ring1) (-(xPhi E Q') ^ 2) * h
    rw [hσs, hP'Q', key]
    exact sub_mem (sub_mem (pow_mem (hxPhi_mem P') 2)
      (mul_mem (mul_mem (hxPhi_mem P') (hxPhi_mem Q')) (eK_mem E)))
      (mul_mem (pow_mem (hxPhi_mem Q') 2) (cK_mem E))
  set D : Func E := s * σ s with hDdef
  have hD_mem' : D ∈ Ax E := by rw [hDdef]; exact hD_mem
  have hD0 : D ≠ 0 := by
    rw [hDdef]; exact mul_ne_zero hs0 hsσ0
  have hr'mem : r * σ s ∈ affRing E := mul_mem hr_mem hsσ_mem
  obtain ⟨Pt, Qt, hPt⟩ := norm_affRingBasisForm E (r * σ s) hr'mem
  have hz_eq : z = (xPhi E Pt + xPhi E Qt * genY E) / D := by
    have h1 : r / s = (r * σ s) / (s * σ s) := by
      rw [div_eq_div_iff hs0 (mul_ne_zero hs0 hsσ0)]
      refl_ring1
    rw [← hzrs, h1, hPt, hDdef]
  have hσz : σ z = (xPhi E Pt - xPhi E Qt * eK E - xPhi E Qt * genY E) / D := by
    have h1 : σ (xPhi E Pt + xPhi E Qt * genY E)
        = xPhi E Pt - xPhi E Qt * eK E - xPhi E Qt * genY E := by
      rw [map_add, map_mul, hσ_ax _ (hxPhi_mem Pt), hσ_ax _ (hxPhi_mem Qt), hσy']
      refl_ring1
    rw [hz_eq, map_div₀, h1, hσ_ax D hD_mem']
  set p : Func E := xPhi E Pt / D with hpdef
  set q : Func E := xPhi E Qt / D with hqdef
  have hz_pq : z = p + q * genY E := by
    rw [hz_eq, hpdef, hqdef]
    field_simp
  have hp_range : p ∈ Set.range (xPsi E) := by
    refine mem_range_xPsi_of_mul E (u := xPhi E Pt) (v := D) (hxPhi_mem Pt) hD_mem' hD0 ?_
    rw [hpdef, div_mul_cancel₀ _ hD0]
  have hq_range : q ∈ Set.range (xPsi E) := by
    refine mem_range_xPsi_of_mul E (u := xPhi E Qt) (v := D) (hxPhi_mem Qt) hD_mem' hD0 ?_
    rw [hqdef, div_mul_cancel₀ _ hD0]
  -- trace and norm
  have hT : z + σ z = 2 * p - q * eK E := by
    rw [hσz, hz_eq, hpdef, hqdef]
    field_simp
    refl_ring1
  have hN : z * σ z = p ^ 2 - p * (q * eK E) - q ^ 2 * cK E := by
    have hexp : (xPhi E Pt + xPhi E Qt * genY E) *
          (xPhi E Pt - xPhi E Qt * eK E - xPhi E Qt * genY E)
        = xPhi E Pt ^ 2 - xPhi E Pt * (xPhi E Qt * eK E) - (xPhi E Qt) ^ 2 * cK E := by
      have h := y_sq E
      linear_combination (norm := refl_ring1) (-(xPhi E Qt) ^ 2) * h
    rw [hσz, hz_eq, hpdef, hqdef, div_mul_div_comm, hexp]
    field_simp
  have hT_int : IsIntegral ↥(Ax E) (z + σ z) := IsIntegral.add hzA hσA
  have hN_int : IsIntegral ↥(Ax E) (z * σ z) := IsIntegral.mul hzA hσA
  have heK_range : eK E ∈ Set.range (xPsi E) :=
    ⟨algebraMap (Polynomial L) (RatFunc L) (linCoef E),
      by rw [xPsi_apply_algebraMap, norm_xPhi_linCoef]⟩
  have hcK_range : cK E ∈ Set.range (xPsi E) :=
    ⟨algebraMap (Polynomial L) (RatFunc L) (cubCoef E),
      by rw [xPsi_apply_algebraMap, norm_xPhi_cubCoef]⟩
  have hT_range : (z + σ z) ∈ Set.range (xPsi E) := by
    rw [hT]
    obtain ⟨u, hu⟩ := hp_range
    obtain ⟨v, hv⟩ := hq_range
    obtain ⟨w, hw⟩ := heK_range
    refine ⟨u + u - v * w, ?_⟩
    rw [map_sub, map_add, map_mul, hu, hv, hw]
    refl_ring1
  have hN_range : (z * σ z) ∈ Set.range (xPsi E) := by
    rw [hN]
    obtain ⟨u, hu⟩ := hp_range
    obtain ⟨v, hv⟩ := hq_range
    obtain ⟨w, hw⟩ := heK_range
    obtain ⟨x, hx⟩ := hcK_range
    refine ⟨u ^ 2 - u * (v * w) - v ^ 2 * x, ?_⟩
    simp only [map_sub, map_mul, map_pow]
    rw [hu, hv, hw, hx]
  have hT_mem : (z + σ z) ∈ Ax E := mem_Ax_of_isIntegral_of_mem_range_xPsi E hT_range hT_int
  have hN_mem : (z * σ z) ∈ Ax E := mem_Ax_of_isIntegral_of_mem_range_xPsi E hN_range hN_int
  have hpqAx : p ∈ Ax E ∧ q ∈ Ax E := by
    by_cases h2 : (2 : L) = 0
    · have h2K : (2 : Func E) = 0 := by
        rw [show (2 : Func E) = algebraMap L (Func E) (2 : L) from
          (map_ofNat (algebraMap L (Func E)) 2).symm]
        rw [h2, map_zero]
      haveI : CharP (Func E) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2K
      have h1 : 2 * p - q * eK E = q * eK E := by
        rw [h2K, zero_mul, zero_sub, CharTwo.neg_eq]
      have hqe : q * eK E ∈ Ax E := by
        rw [← h1, ← hT]
        exact hT_mem
      have h2'' : p ^ 2 - p * (q * eK E) - q ^ 2 * cK E
          = p ^ 2 + p * (q * eK E) + q ^ 2 * cK E := by
        rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
      have hN' : p ^ 2 + p * (q * eK E) + q ^ 2 * cK E ∈ Ax E := by
        rw [← h2'', ← hN]
        exact hN_mem
      exact CharTwoNormCrux L E h2 p q hp_range hq_range hqe hN'
    · have hT' : 2 * p - q * eK E ∈ Ax E := by rw [← hT]; exact hT_mem
      have hN' : p ^ 2 - p * (q * eK E) - q ^ 2 * cK E ∈ Ax E := by rw [← hN]; exact hN_mem
      exact NormNeTwoCrux L E h2 p q hp_range hq_range hT' hN'
  obtain ⟨hpAx, hqAx⟩ := hpqAx
  rw [hz_pq]
  exact add_mem (norm_ax_le_affRing E hpAx)
    (mul_mem (norm_ax_le_affRing E hqAx) (norm_genY_mem_affRing E))

/-- The intersection of all places except `O` is exactly the affine coordinate ring. -/
theorem placeInter_le_affRing : placeInter E ≤ affRing E := by
  intro f hf
  rw [placeInter, Algebra.mem_iInf] at hf
  by_contra hfR
  haveI := affRing_integrallyClosed E
  obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (K := Func E) (R := (affRing E).toSubring) hfR
  have hL : ∀ c : L, algebraMap L (Func E) c ∈ V := fun c =>
    hRV (Subalgebra.algebraMap_mem (affRing E) c)
  have hxaff : genX E ∈ affRing E := by
    rw [Work.MotC2.affRing_eq_adjoin]
    exact Algebra.subset_adjoin (by simp)
  have hVtop : V ≠ ⊤ := fun h => hfV (by rw [h]; exact ValuationSubring.mem_top (genX E))
  have hVO : V ≠ placeAtO E := by
    intro h
    have hxV : genX E ∈ V := hRV hxaff
    rw [h] at hxV
    exact genX_notMem_infPlace E (Subalgebra.mem_toSubring.mp hxV)
  have hmem : f ∈ valSub E V hL :=
    hf ⟨valSub E V hL, ⟨V, hL, hVtop, hVO, rfl⟩⟩
  exact hfV (by simpa [valSub] using hmem)

/-- The preimage of a place under an automorphism of `L(E)`. -/
noncomputable def preimVal (Θ : Func E ≃ₐ[L] Func E) (V : ValuationSubring (Func E)) :
    ValuationSubring (Func E) :=
  ValuationSubring.ofSubring (V.toSubring.comap Θ.toRingHom) fun x => by
    rcases V.mem_or_inv_mem (Θ x) with h | h
    · exact Or.inl (Subring.mem_comap.mpr h)
    · refine Or.inr (Subring.mem_comap.mpr ?_)
      rw [show Θ.toRingHom x⁻¹ = (Θ.toRingHom x)⁻¹ from map_inv₀ Θ.toRingHom x]
      exact h

/-- An automorphism of `L(E)` fixing the place at infinity preserves the intersection of all the
other places. -/
theorem mem_placeInter_map (Θ : Func E ≃ₐ[L] Func E)
    (hO : Subalgebra.map Θ.toAlgHom (infPlace E) = infPlace E)
    {f : Func E} (hf : f ∈ placeInter E) : Θ f ∈ placeInter E := by
  rw [placeInter, Algebra.mem_iInf] at hf ⊢
  intro W
  obtain ⟨V, hL, hVtop, hVO, hWeq⟩ := W.2
  rw [hWeq]
  have hL' : ∀ c : L, algebraMap L (Func E) c ∈ preimVal E Θ V := fun c => by
    rw [preimVal, ValuationSubring.mem_ofSubring, Subring.mem_comap]
    simpa using hL c
  have hPtop : preimVal E Θ V ≠ ⊤ := by
    intro htop
    apply hVtop
    apply ValuationSubring.ext
    intro y
    refine ⟨fun _ => ValuationSubring.mem_top y, fun _ => ?_⟩
    have h1 : Θ.symm y ∈ preimVal E Θ V := by
      rw [htop]; exact ValuationSubring.mem_top _
    rw [preimVal, ValuationSubring.mem_ofSubring, Subring.mem_comap] at h1
    simpa using h1
  have hPO : preimVal E Θ V ≠ placeAtO E := by
    intro hPeq
    apply hVO
    apply ValuationSubring.ext
    intro y
    constructor
    · intro hy
      have h1 : Θ.symm y ∈ preimVal E Θ V := by
        rw [preimVal, ValuationSubring.mem_ofSubring, Subring.mem_comap]; simpa using hy
      rw [hPeq, placeAtO, ValuationSubring.mem_ofSubring] at h1
      have h2 : Θ.symm y ∈ infPlace E := Subalgebra.mem_toSubring.mp h1
      have h3 : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) :=
        Subalgebra.mem_map.mpr ⟨Θ.symm y, h2, by simp⟩
      rwa [hO] at h3
    · intro hy
      have hy' : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) := by rw [hO]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.mp hy'
      have h1 : z ∈ preimVal E Θ V := by
        rw [hPeq, placeAtO, ValuationSubring.mem_ofSubring]
        exact Subalgebra.mem_toSubring.mpr hz
      rw [preimVal, ValuationSubring.mem_ofSubring, Subring.mem_comap] at h1
      rw [← hzy]
      simpa using h1
  have hgood : valSub E (preimVal E Θ V) hL' ∈ placeFamily E :=
    ⟨preimVal E Θ V, hL', hPtop, hPO, rfl⟩
  have hmem : f ∈ valSub E (preimVal E Θ V) hL' := hf ⟨_, hgood⟩
  change Θ f ∈ V.toSubring
  have h : f ∈ (preimVal E Θ V).toSubring := hmem
  rw [preimVal, ValuationSubring.ofSubring_toSubring, Subring.mem_comap] at h
  simpa using h

end Main

theorem CoordPreserved (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E)
    (hO : Subalgebra.map Θ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E) :
    Subalgebra.map Θ.toAlgHom (Work.MotC2.affRing E) = Work.MotC2.affRing E := by
  have hA : placeInter E = affRing E :=
    le_antisymm (placeInter_le_affRing E) (affRing_le_placeInter E)
  -- `Θ⁻¹` also fixes the place at infinity
  have hOsymm : Subalgebra.map Θ.symm.toAlgHom (infPlace E) = infPlace E := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx
      have hy' : y ∈ Subalgebra.map Θ.toAlgHom (infPlace E) := by rw [hO]; exact hy
      obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.mp hy'
      rw [← hzy] at hyx
      have hxz : x = z := by rw [← hyx]; simp
      rw [hxz]
      exact hz
    · intro x hx
      have hx' : Θ x ∈ Subalgebra.map Θ.toAlgHom (infPlace E) :=
        Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hO] at hx'
      exact Subalgebra.mem_map.mpr ⟨Θ x, hx', by simp⟩
  have hstab : ∀ f : Func E, f ∈ placeInter E → Θ f ∈ placeInter E :=
    fun f hf => mem_placeInter_map E Θ hO hf
  have hstab' : ∀ f : Func E, f ∈ placeInter E → Θ.symm f ∈ placeInter E :=
    fun f hf => mem_placeInter_map E Θ.symm hOsymm hf
  have hmap : Subalgebra.map Θ.toAlgHom (placeInter E) ≤ placeInter E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hx
    exact hstab y hy
  have hmap' : Subalgebra.map Θ.symm.toAlgHom (placeInter E) ≤ placeInter E := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subalgebra.mem_map.mp hx
    exact hstab' y hy
  have hle : Subalgebra.map Θ.toAlgHom (placeInter E) = placeInter E := by
    refine le_antisymm hmap ?_
    intro f hf
    have h1 : Θ.symm f ∈ placeInter E := hmap' (Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩)
    exact Subalgebra.mem_map.mpr ⟨Θ.symm f, h1, by simp⟩
  rw [hA] at hle
  exact hle

end Work.MotC2
